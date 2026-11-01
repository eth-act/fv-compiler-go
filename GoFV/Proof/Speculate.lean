import GoFV.Opt.SpecSafe
import GoFV.Proof.Eval

/-!
# Speculative execution is safe

`evalValue_specSafe`: a value whose op passes `specSafeOp` evaluates, in every frame where its
arguments have values, to some value: the semantics' pure ops are total (division by zero and
oversized shifts give `poison`, §4.2-4.3 of `docs/plans/semantics.md`), cannot panic and have no
effect. So a pass may execute such a value on a path where the input did not (branchelim's arms,
the right operand of a fused comparison), provided its arguments are defined there.

`canSpeculativelyExecute_spec`: what Go's syntactic check `canSpeculativelyExecute` gives per
value (no `Phi`, no side effects, no memory type, no memory argument except `InlMark`), and
`specSafe_of_canSpeculativelyExecute`: with the op-shape facts that calls and nil checks take a
memory argument and the memory-typed ops have a memory type (`MemShaped`), every value of a
block passing `canSpeculativelyExecute` that is not a parameter read is `specSafeOp`.
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt

theorem mapM_ofOption_ok {m : ID → String} {r : ID → Option Val} :
    ∀ {l : List ID}, (∀ a ∈ l, ∃ z, r a = some z) →
      ∃ L, l.mapM (fun a => Res.ofOption (m a) (r a)) = .ok L
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨z, hz⟩ := h a List.mem_cons_self
    obtain ⟨L, hL⟩ := mapM_ofOption_ok (l := l) fun b hb => h b (List.mem_cons_of_mem _ hb)
    refine ⟨z :: L, ?_⟩
    rw [List.mapM_cons, hz]
    change Res.bind (List.mapM (fun a => Res.ofOption (m a) (r a)) l) _ = _
    rw [hL]; rfl

/-- **A speculation-safe value evaluates** wherever its arguments have values. -/
theorem evalValue_specSafe {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    (hs : specSafeOp v.op = true) (hargs : ∀ a ∈ v.args, ∃ z, fr.regs[a]? = some (some z)) :
    ∃ y, evalValue env ctx fr v = .ok y := by
  unfold evalValue
  obtain ⟨L, hL⟩ := mapM_ofOption_ok (l := v.args.toList)
    (m := fun a => s!"v{v.id}: argument v{a} has no value") (r := fun a => (fr.regs[a]?).join)
    fun a ha => by
      obtain ⟨z, hz⟩ := hargs a (Array.mem_toList_iff.1 ha)
      exact ⟨z, by rw [hz]; rfl⟩
  rw [hL]
  simp only [bind, Res.bind]
  have hroot : isRoot v.op = false := by
    simp only [specSafeOp, Bool.and_eq_true, Bool.not_eq_true'] at hs; exact hs.1.1.1
  have hne : ∀ op, isRoot op = true → v.op ≠ op := fun op h he => by rw [he] at hroot; simp_all
  have hspec : v.op ≠ .Arg ∧ v.op ≠ .ArgIntReg := by
    simp only [specSafeOp, Bool.and_eq_true, bne_iff_ne, ne_eq] at hs
    exact ⟨hs.1.2, hs.2⟩
  suffices h : ∃ r, evalOp env ctx fr v L (ctx.tys[v.id]?.getD .other) = .ok r by
    obtain ⟨r, hr⟩ := h
    exact ⟨_, by rw [hr]; rfl⟩
  unfold evalOp
  split
  · exact ⟨_, rfl⟩
  · exact absurd ‹_› hspec.1
  · exact absurd ‹_› hspec.2
  all_goals first
    | exact absurd ‹v.op = _› (hne _ (by decide))
    | skip
  split
  · exact ⟨_, rfl⟩
  · rw [hroot]
    exact ⟨_, rfl⟩

/-- What `canSpeculativelyExecute` checks of each value of the block. -/
theorem canSpeculativelyExecute_spec {isMem : TypeRef → Bool} {f : Func} {b : ID}
    (h : canSpeculativelyExecute isMem f b = true) :
    ∀ id ∈ (f.getB b).values, (f.getV id).op ≠ .Phi ∧ (f.getV id).op.hasSideEffects = false ∧
      isMem (f.getV id).type = false ∧ isDivMod (f.getV id).op = false ∧
      isPtrArithmetic (f.getV id).op = false ∧
      ((f.getV id).op = .InlMark ∨ hasMemoryArg isMem f (f.getV id) = false) := by
  intro id hid
  unfold canSpeculativelyExecute at h
  have := (Array.all_eq_true'.1 h) id hid
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne,
    ne_eq, Bool.or_eq_true, beq_iff_eq] at this
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := this
  exact ⟨h1, h5, h4, h2, h3, h6.imp (fun x => x) (by simpa using ·)⟩

/-- Op-shape facts (true of the generic ops by their definitions in `genericOps.go`): a call or
nil check takes a memory argument, an op whose result is a memory has a memory type, and
`VarLive` is memory-typed. -/
def MemShaped (isMem : TypeRef → Bool) (f : Func) (v : Value) : Prop :=
  ((v.op.call || v.op.nilCheck) = true → hasMemoryArg isMem f v = true) ∧
  ((v.op.typ == "Mem" || v.op == .VarLive) = true → isMem v.type = true)

/-- **`canSpeculativelyExecute` admits only speculation-safe values** (on memory-shaped values
other than parameter reads). -/
theorem specSafe_of_canSpeculativelyExecute {isMem : TypeRef → Bool} {f : Func} {b : ID}
    (h : canSpeculativelyExecute isMem f b = true) {id : ID} (hid : id ∈ (f.getB b).values)
    (hshape : MemShaped isMem f (f.getV id)) (harg : (f.getV id).op ≠ .Arg)
    (hargr : (f.getV id).op ≠ .ArgIntReg) : specSafeOp (f.getV id).op = true := by
  obtain ⟨h1, h2, h3, -, -, h6⟩ := canSpeculativelyExecute_spec h id hid
  obtain ⟨hc, hm⟩ := hshape
  generalize f.getV id = v at *
  have hInl : v.op = .InlMark → isRoot v.op = false := fun he => by rw [he]; decide
  have hroot : isRoot v.op = false := by
    rcases h6 with he | hma
    · exact hInl he
    · unfold isRoot
      cases hcall : (v.op.call || v.op.nilCheck) with
      | true => rw [hc hcall] at hma; cases hma
      | false =>
        cases hmem : (v.op.typ == "Mem" || v.op == .VarLive) with
        | true => rw [hm hmem] at h3; cases h3
        | false =>
          simp only [Bool.or_eq_false_iff] at hcall hmem
          simp [h2, hmem.1, hmem.2]
  simp [specSafeOp, hroot, h1, harg, hargr]

end GoFV.Proof

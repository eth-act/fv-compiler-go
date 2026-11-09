import GoFV.Proof.Pass.FuseCmpSetup
import GoFV.Proof.Pass.DeadRel

variable [GoFV.SSA.Sem.Addrs]

/-!
# fuseComparisons: block `b` in the target

In `g`, block `b` holds `b`'s values and the new value `nv`, all speculation-safe and none a
`Phi`. `enter_b`: entering it in a frame `GT1` evaluates, against a reference frame `G` (the
source's frame after `b` when the source ran `b`, after `p` when the target speculates `b`),
every value: the values outside a free set `F` yield their `G` registers (`MixOK`), and the
target keeps its other registers. `evalValue_newOp`: `nv`'s result is the parallel `OrB`/`AndB`
of its arguments; `newOp_true`/`newOp_pass`: on the side `p` takes to `s` it is `p`'s control,
on `b`'s side it is `b`'s control.
-/

namespace GoFV.Proof.FuseCmp

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.Fuse GoFV.Opt.Fuse.Cmp GoFV.Proof
  Dom

theorem filterMapM_nophi {ctx : Ctx} {fr : Frame} {i : Nat} :
    ∀ {l : List ID}, (∀ z ∈ l, ∃ v, ctx.f.value? z = some v ∧ v.op ≠ .Phi) →
      l.filterMapM (phiStep ctx fr i) = .ok []
  | [], _ => rfl
  | z :: l, h => by
    obtain ⟨v, hv, hp⟩ := h z List.mem_cons_self
    have hz : phiStep ctx fr i z = .ok none := by unfold phiStep; rw [hv]; simp [hp]
    rw [List.filterMapM_cons, hz]
    simp only [bind, Res.bind]
    exact filterMapM_nophi fun y hy => h y (List.mem_cons_of_mem _ hy)

theorem specSafe_newOp (i : Nat) : specSafeOp (newOp i) = true := by
  unfold newOp; split <;> decide

theorem evalOp_newOp {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {i : Nat}
    (hop : v.op = newOp i) (args : List Val) (ty : Ty) :
    evalOp env ctx fr v args ty =
      .ok (if i = 0 then Cmp.orB args else Cmp.andB args) := by
  obtain ⟨id, op, type, auxInt, aux, pos, uses, vargs, block⟩ := v
  simp only at hop
  subst hop
  unfold newOp
  by_cases hi : i = 0
  · simp only [hi, beq_self_eq_true, ite_true]; rfl
  · simp only [show (i == 0) = false by simpa using hi, Bool.false_eq_true, ite_false, hi]; rfl

/-- **The new value's result**: the parallel `OrB`/`AndB` of its arguments' registers. -/
theorem evalValue_newOp {env : Env} {ctx : Ctx} {fr : Frame} {w : Value} {i : Nat}
    (hop : w.op = newOp i) {a1 a2 : ID} (hargs : w.args = #[a1, a2]) {x1 x2 : Val}
    (h1 : fr.regs[a1]? = some (some x1)) (h2 : fr.regs[a2]? = some (some x2)) :
    evalValue env ctx fr w = .ok ((if i = 0 then Cmp.orB [x1, x2] else Cmp.andB [x1, x2]).retype
      (ctx.tys[w.id]?.getD .other)) := by
  unfold evalValue
  rw [hargs]
  simp only [List.mapM_cons, List.mapM_nil, h1, h2, Option.join, Option.bind_some, id,
    Res.ofOption, bind, Res.bind, pure, evalOp_newOp hop]

/-- On the side `p` takes to `s`, the new value is `p`'s control. -/
theorem newOp_true {i : Nat} {c : Bool} (hk : (if c then 0 else 1) = i) (x : Val) :
    (if i = 0 then Cmp.orB [.bool c, x] else Cmp.andB [.bool c, x]) = .bool c := by
  cases c <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hk <;> subst hk <;>
    simp only [Nat.one_ne_zero, ite_false, ite_true] <;> cases x <;> rfl

/-- On `b`'s side, the new value is `b`'s control. -/
theorem newOp_pass {i : Nat} (hi : i < 2) {c : Bool} (hk : (if c then 0 else 1) = 1 - i) (c' : Bool) :
    (if i = 0 then Cmp.orB [.bool c, .bool c'] else Cmp.andB [.bool c, .bool c']) = .bool c' := by
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl <;> cases c <;> simp at hk <;> cases c' <;> rfl

variable {f g : Func} {st : Site}

namespace Base

variable (S : Base f g st)
include S

/-- Block `b` in `f` and `g`. -/
theorem gB : ∃ B B', f.block? st.b = some B ∧ g.block? st.b = some B' ∧ B.id = st.b ∧
    B'.id = st.b ∧ B'.values = B.values.push st.nv ∧ B'.kind = .If ∧ B'.controls = #[st.nv] ∧
    B'.succs = B.succs.map st.remapE ∧ (schedule g B').isSome := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨B, -, -, B', hB, -, -, hB', -, -, -, -, -, -, hk, -, -, -, -, -, -, -, -, -, -, hsch⟩ :=
    S.rel.shape
  obtain ⟨X, hX, hX'⟩ := S.rel.gblock (x := st.b) (by simp)
  rw [hB] at hX; cases hX
  rw [hB'] at hX'; cases hX'
  obtain ⟨b', hb', hid⟩ := hwf.blockId st.b S.inB
  rw [hB] at hb'; cases hb'
  refine ⟨B, _, hB, hB', hid, ?_, ?_, ?_, ?_, ?_, hsch⟩ <;> simp [Site.expect, hid, hk]

theorem inBg : st.b ∈ g.blocks := by rw [S.rel.blocks]; exact S.inB

/-- A value of `b` keeps what is read, is no `Phi` and is speculation-safe. -/
theorem bval {B : Block} (hB : f.block? st.b = some B) {x : ID} (hx : x ∈ B.values) :
    ∃ v w, f.value? x = some v ∧ g.value? x = some w ∧ SemEq (some v) (some w) ∧
      w.type = v.type ∧ w.op = v.op ∧ v.op ≠ .Phi ∧ specSafeOp v.op = true ∧ v.id = x ∧
      v.block = st.b := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨v, hv, hsp⟩ := S.rel.spec hB x hx
  obtain ⟨v', hv', hvid, hvb⟩ := hwf.valueId st.b B ⟨S.inB, hB⟩ x hx
  rw [hv] at hv'; cases hv'
  obtain ⟨-, hval⟩ := S.rel.value (S.mem_ne S.inB hB hx)
  obtain ⟨w, hw, hid, hty, haux, hai, hop, -, -, hsame⟩ := hval v hv
  have hnp : v.op ≠ .Phi := fun h => by simp [specSafeOp, h] at hsp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hsb, -⟩ := S.rel.shape
  have hargs := hsame fun h => hsb (hvb.symm.trans h.2).symm
  exact ⟨v, w, hv, hw, ⟨hid, hop, haux, hai, hargs⟩, hty, hop, hnp, hsp, hvid, hvb⟩

/-- The values of `b` in `g` are no `Phi`s and speculation-safe. -/
theorem gB_vals {B B' : Block} (hB : f.block? st.b = some B)
    (hvals : B'.values = B.values.push st.nv) :
    ∀ z ∈ B'.values, ∃ w, g.value? z = some w ∧ w.op ≠ .Phi ∧ specSafeOp w.op = true := by
  intro z hz
  rw [hvals, Array.mem_push] at hz
  rcases hz with hz | rfl
  · obtain ⟨v, w, -, hw, -, -, hop, hnp, hsp, -⟩ := S.bval hB hz
    exact ⟨w, hw, hop ▸ hnp, hop ▸ hsp⟩
  · obtain ⟨-, -, -, w, hw, -, hop, -⟩ := S.rel.newv
    refine ⟨w, hw, ?_, hop ▸ specSafe_newOp st.i⟩
    rw [hop]; unfold newOp; split <;> decide

end Base

namespace Setup

variable (S : Setup f g st)
include S

/-- **Entering `b` in the target** against a reference frame (see the module doc). -/
theorem enter_b {env : Env} {tabs : Tables} {B B' : Block} (hB : f.block? st.b = some B)
    (hB' : g.block? st.b = some B') (hvals : B'.values = B.values.push st.nv)
    (hid' : B'.id = st.b) (hsch : (schedule g B').isSome)
    {G GT1 : Frame} {F : ID → Prop} (hGs : G.regs.size = f.valueTab.size)
    (hg : GT1 = { G with regs := GT1.regs }) (hs : GT1.regs.size = G.regs.size)
    (hext : ∀ a, a ∉ B'.values → (∃ x ∈ B'.values, a ∈ argsF g x) →
      GT1.regs[a]? = G.regs[a]? ∧ ∃ z, G.regs[a]? = some (some z))
    (hmix : ∀ x ∈ B'.values, MixOK env (Ctx.make tabs g) G F [x]) :
    ∃ GT2, enterBlock env (Ctx.make tabs g) GT1 B' 0 = .ok GT2 ∧
      GT2 = { G with regs := GT2.regs } ∧ GT2.regs.size = G.regs.size ∧
      (∀ a ∈ B'.values, ¬ F a → GT2.regs[a]? = G.regs[a]?) ∧
      (∀ a ∈ B'.values, ∃ z, GT2.regs[a]? = some (some z)) ∧
      (∀ a, a ∉ B'.values → GT2.regs[a]? = GT1.regs[a]?) := by
  obtain ⟨ce, hwg⟩ := S.wg
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 hsch
  have hnp := S.gB_vals hB hvals
  obtain ⟨-, otopo, omem⟩ := schedule_topo (valuesOwn hwg S.inBg hB')
    (hwg.valuesNodup st.b B' ⟨S.inBg, hB'⟩) ho
  have hmem : ∀ x, x ∈ o.toList ↔ x ∈ B'.values := fun x => by
    rw [omem x]
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    obtain ⟨w, hw, hwp, -⟩ := hnp x h
    exact ⟨w, hw, hwp⟩
  have hps : B'.values.toList.filterMapM (phiStep (Ctx.make tabs g) GT1 0) = .ok [] :=
    filterMapM_nophi fun z hz => by
      obtain ⟨w, hw, hwp, -⟩ := hnp z (Array.mem_toList_iff.1 hz)
      exact ⟨w, hw, hwp⟩
  have hGs' : G.regs.size = (Ctx.make tabs g).f.valueTab.size := by
    rw [hGs]; exact S.gsize.symm
  obtain ⟨GT2, hev, hGT, hGTs, h4, h5, h6⟩ := evalAll_mix (F := F) hGs'
    (mixOK_of_single fun x hx => hmix x ((hmem x).1 hx))
    (S := fun a => a ∉ o.toList ∧ ∃ x ∈ o.toList, a ∈ argsF (Ctx.make tabs g).f x)
    (g := { GT1 with regs := setPhis [] GT1.regs })
    (Dead.refOK_of_topo otopo fun x hx a ha hna => ⟨hna, x, hx, ha⟩)
    (fun a ha _ => by
      obtain ⟨x, hx, hax⟩ := ha.2
      exact (hext a (fun h => ha.1 ((hmem a).2 h)) ⟨x, (hmem x).1 hx, hax⟩).1)
    (fun a ha => by
      obtain ⟨x, hx, hax⟩ := ha.2
      obtain ⟨h1, z, hz⟩ := hext a (fun h => ha.1 ((hmem a).2 h)) ⟨x, (hmem x).1 hx, hax⟩
      exact ⟨z, by show GT1.regs[a]? = _; rw [h1, hz]⟩)
    (by rw [hg]) (by show GT1.regs.size = _; exact hs)
  refine ⟨GT2, ?_, hGT, hGTs, fun a ha hF => h4 a (.inr ((hmem a).2 ha)) hF,
    fun a ha => h5 a (.inr ((hmem a).2 ha)), fun a ha => ?_⟩
  · rw [enterBlock_eq, hps]
    change (Res.ofOption _ ((Ctx.make tabs g).sched[B'.id]?).join).bind _ = _
    rw [hid', sched_of_block hB', ho]
    exact hev
  · rw [h6 a fun h => ha ((hmem a).1 h)]
    rfl

end Setup

end GoFV.Proof.FuseCmp

import GoFV.Opt.SccpCheck
import GoFV.Proof.Pass.KnownBitsInv

variable [GoFV.SSA.Sem.Addrs]

/-!
# The source-side invariant of sccp (issue #32)

`sccpOK_spec`: what sccp's checker establishes, as propositions. `sccpInv`: the invariant
`AtomSim.SrcInv` of a run of the source: every register `a` whose cell is constant holds
`poison` or that constant (`Claim`), while the source runs an executable block entered along an
executable edge. It holds at the entry (registers `poison`) and each step keeps it: a term by
the post-fixpoint condition (its arguments' constants evaluate to its own) and the monotonicity
of `evalPure`; an atom claims nothing (`fixOK` admits no constant atom but `Phi`); an edge is
executable by `reachOK` (a constant control picks the successor its constant picks) and each
constant `Phi` has its constant on that edge.
-/

namespace GoFV.Proof.Sccp

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.Sccp GoFV.Opt.RewriteCheck GoFV.Proof.Term
open GoFV.Proof.AtomSim

/-- What `sccpOK` checks. -/
structure Facts (tabs : Tables) (f g : Func) (C : Array (Option Lat)) (vis : Array Edge)
    (R : Array Bool) : Prop where
  atoms : atomsOK f g = true
  cf : closedOK f = true
  cg : closedOK g = true
  blocks : blocksOK tabs f g C = true
  reach : reachOK tabs f C vis R = true
  fix : ∀ x < f.valueTab.size, fixOK tabs f C vis x = true
  rep : ∀ x < f.valueTab.size, repOK tabs f g C x = true

theorem sccpOK_spec {tabs : Tables} {f g : Func} {C : Array (Option Lat)} {vis : Array Edge}
    {R : Array Bool} (h : sccpOK tabs f g C vis R = true) : Facts tabs f g C vis R := by
  unfold sccpOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, fun x hx => (h6 x hx).1, fun x hx => (h6 x hx).2⟩

/-! ## Scalars -/

theorem scalarEq_eq : ∀ {a b : Val}, scalarEq a b = true → a = b
  | .int w x, .int w' x', h => by
    simp only [scalarEq, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    rw [BitVec.eq_of_toNat_eq h]
  | .bool b, .bool b', h => by simp only [scalarEq, beq_iff_eq] at h; rw [h]
  | .int _ _, .bool _, h | .bool _, .int _ _, h => by simp [scalarEq] at h
  | .poison, _, h | .mem _, _, h | .tuple _, _, h | .ptr _, _, h | .agg _, _, h
  | .blob _, _, h | .empty, _, h => by simp [scalarEq] at h
  | .int _ _, .poison, h | .int _ _, .mem _, h | .int _ _, .tuple _, h | .int _ _, .ptr _, h
  | .int _ _, .agg _, h | .int _ _, .blob _, h | .int _ _, .empty, h => by simp [scalarEq] at h
  | .bool _, .poison, h | .bool _, .mem _, h | .bool _, .tuple _, h | .bool _, .ptr _, h
  | .bool _, .agg _, h | .bool _, .blob _, h | .bool _, .empty, h => by simp [scalarEq] at h

theorem scalar?_some {v c : Val} (h : scalar? v = some c) :
    c = v ∧ ((∃ w x, c = .int w x) ∨ ∃ b, c = .bool b) := by
  cases v <;> simp only [scalar?, Option.some.injEq, reduceCtorEq] at h <;> subst h
  · exact ⟨rfl, .inl ⟨_, _, rfl⟩⟩
  · exact ⟨rfl, .inr ⟨_, rfl⟩⟩

theorem cval_scalar {tabs : Tables} {f : Func} {C : Array (Option Lat)} {x : ID} {c : Val}
    (h : cval tabs f C x = some c) : (∃ w y, c = .int w y) ∨ ∃ b, c = .bool b := by
  unfold cval at h
  split at h
  · split at h
    · exact (scalar?_some h).2
    · cases h
  · cases h

/-- A value refining an integer or boolean is `poison` or that value. -/
theorem refines_scalar {y c : Val} (hc : (∃ w x, c = .int w x) ∨ ∃ b, c = .bool b)
    (h : Sem.Refines y c) : y = .poison ∨ y = c := by
  rcases hc with ⟨w, x, rfl⟩ | ⟨b, rfl⟩ <;> cases h <;> simp

theorem cval_value {tabs : Tables} {f : Func} {C : Array (Option Lat)} {x : ID} {c : Val}
    (h : cval tabs f C x = some c) : ∃ v, f.value? x = some v := by
  unfold cval at h
  split at h
  · rename_i v _ _; exact ⟨v, by assumption⟩
  · cases h

/-! ## The claim -/

/-- `y` is `poison` or the constant `a`'s cell claims. -/
def Claim (tabs : Tables) (f : Func) (C : Array (Option Lat)) (a : ID) (y : Val) : Prop :=
  ∀ c, cval tabs f C a = some c → Sem.Refines y c

theorem Claim.poison (tabs : Tables) (f : Func) (C : Array (Option Lat)) (a : ID) :
    Claim tabs f C a .poison := fun _ _ => .poison _

theorem refinesList_mapM {ρ : ID → Val} {g : ID → Option Val} :
    ∀ {l : List ID} {cs : List Val}, (∀ a ∈ l, ∀ c, g a = some c → Sem.Refines (ρ a) c) →
      l.mapM g = some cs → RefinesList (l.map ρ) cs
  | [], cs, _, h => by simp at h; subst h; exact .nil
  | a :: l, cs, hP, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨c, hc, cs', hcs, rfl⟩ := h
    exact .cons (hP a List.mem_cons_self c hc)
      (refinesList_mapM (fun b hb => hP b (List.mem_cons_of_mem _ hb)) hcs)

/-! ## Terminators -/

theorem control_ok {fr : Frame} {b : Block} {k : Nat} {y : Val} (h : Sem.control fr b k = .ok y) :
    ∃ c, b.controls[k]? = some c ∧ rv fr c = y := by
  unfold Sem.control at h
  cases hc : b.controls[k]? with
  | none => simp only [hc] at h; cases h
  | some c =>
    simp only [hc] at h
    refine ⟨c, rfl, ?_⟩
    cases hr : (fr.regs[c]?).join with
    | none => simp only [hr, Res.ofOption] at h; cases h
    | some y' => simp only [hr, Res.ofOption] at h; cases h; simp [rv, hr]

/-- The successor a terminator takes, by its kind and controls. -/
theorem stepTerm_goto {fr : Frame} {b : Block} {e : Edge} (h : stepTerm fr b = .ok (.goto e)) :
    ((b.kind = .Plain ∨ b.kind = .First ∨ b.kind = .Defer) ∧ b.succs[0]? = some e) ∨
    (b.kind = .If ∧ ∃ c t, b.controls[0]? = some c ∧ rv fr c = .bool t ∧
      b.succs[if t then 0 else 1]? = some e) ∨
    (b.kind = .JumpTable ∧ ∃ c w x, b.controls[0]? = some c ∧ rv fr c = .int w x ∧
      b.succs[(x : BitVec w.bits).toNat]? = some e) := by
  unfold stepTerm at h
  cases hb : b.kind <;> simp only [hb] at h
  all_goals first
    | (cases h; done)
    | exact .inl ⟨.inl rfl, KnownBits.succ_idx h⟩
    | exact .inl ⟨.inr (.inl rfl), KnownBits.succ_idx h⟩
    | exact .inl ⟨.inr (.inr rfl), KnownBits.succ_idx h⟩
    | (cases hc0 : Sem.control fr b 0 with
        | ok v =>
          rw [hc0] at h
          simp only [bind, Res.bind] at h
          obtain ⟨c, hc, hy⟩ := control_ok hc0
          split at h <;> first
            | (cases h; done)
            | exact .inr (.inl ⟨rfl, c, true, hc, hy, KnownBits.succ_idx h⟩)
            | exact .inr (.inl ⟨rfl, c, false, hc, hy, KnownBits.succ_idx h⟩)
            | exact .inr (.inr ⟨rfl, c, _, _, hc, hy, KnownBits.succ_idx h⟩)
            | (split at h <;> first
              | (cases h; done)
              | (split at h <;> cases h))
        | panic e m => rw [hc0] at h; cases h
        | stuck msg => rw [hc0] at h; cases h)

section
variable {tabs : Tables} {f : Func} {C : Array (Option Lat)}

/-- A terminator takes a successor its block may take. -/
theorem stepTerm_feasible {fr : Frame} {b : Block} {e : Edge}
    (hP : ∀ a, Claim tabs f C a (rv fr a)) (h : stepTerm fr b = .ok (.goto e)) :
    ∃ k, b.succs[k]? = some e ∧ feasible tabs f C b k = true := by
  rcases stepTerm_goto h with ⟨hk | hk | hk, he⟩ | ⟨hk, c, t, hc, hy, he⟩ | ⟨hk, c, w, x, hc, hy, he⟩
  · exact ⟨0, he, by simp [feasible, hk]⟩
  · exact ⟨0, he, by simp [feasible, hk]⟩
  · exact ⟨0, he, by simp [feasible, hk]⟩
  · refine ⟨_, he, ?_⟩
    simp only [feasible, hk, hc, Option.bind_some]
    split
    · rename_i t' ht
      have := hP c _ ht
      rw [hy] at this
      cases this; simp
    · rfl
  · refine ⟨_, he, ?_⟩
    simp only [feasible, hk, hc, Option.bind_some]
    split
    · rename_i w' x' hx
      have := hP c _ hx
      rw [hy] at this
      cases this; simp
    · rfl

end

/-! ## The invariant -/

section
variable {tabs : Tables} {f g : Func} {C : Array (Option Lat)} {vis : Array Edge} {R : Array Bool}
  {ce : CheckEnv} (hwf : WF ce f) (K : Facts tabs f g C vis R)
include hwf K

/-- A term node keeps the invariant. -/
theorem sc_term {x : ID} {v : Value} (hv : f.value? x = some v) (ht : termOp v.op = true)
    (ρ : ID → Val) (hρ : ∀ a ∈ v.args, Claim tabs f C a (ρ a)) :
    Claim tabs f C x ((GoFV.Proof.Rules.opVal tabs v.op (tabs.ty v.type) v.auxInt v.aux
      (v.args.toList.map ρ)).retype
      (tabs.ty v.type)) := by
  intro c hc
  have hfix := K.fix x (lt_of_value? hv)
  have hph : v.op ≠ .Phi := fun h => by rw [h, termOp_phi] at ht; cases ht
  simp only [fixOK, hc, hv, beq_iff_eq, hph, ite_false, ht, Bool.true_and] at hfix
  split at hfix
  · rename_i cs hcs
    rw [← scalarEq_eq hfix]
    exact retype_mono _ (GoFV.Proof.Rules.opVal_mono _ _ _ _ _ (refinesList_mapM
      (fun a ha c hc => hρ a (Array.mem_toList_iff.1 ha) c hc) hcs))
  · cases hfix

/-- An atom keeps the invariant: it claims nothing. -/
theorem sc_atom {x : ID} {v : Value} (hv : f.value? x = some v) (ht : termOp v.op = false)
    (hph : v.op ≠ .Phi) (y : Val) : Claim tabs f C x y := by
  intro c hc
  have hfix := K.fix x (lt_of_value? hv)
  simp only [fixOK, hc, hv, beq_iff_eq, hph, ite_false, ht, Bool.false_and] at hfix
  cases hfix

/-- An edge the source takes from an executable block is executable. -/
theorem sc_live {p : ID} {pb : Block} (hp : p ∈ f.blocks) (hpb : f.block? p = some pb)
    (hR : R.getD p false = true) {k : Nat} {e : Edge} (hk : pb.succs[k]? = some e)
    (hF : feasible tabs f C pb k = true) :
    e.b ∈ f.blocks ∧ R.getD e.b false = true ∧ live vis e.b e.i = true := by
  obtain ⟨hmem, -⟩ := hwf.succLink p pb ⟨hp, hpb⟩ k e hk
  have h := K.reach
  unfold reachOK at h
  simp only [Bool.and_eq_true, Array.all_eq_true'] at h
  have := h.2 p hp
  simp only [hR, Bool.not_true, Bool.false_or, hpb, List.all_eq_true, List.mem_range] at this
  have hlt : k < pb.succs.size := (Array.getElem?_eq_some_iff.1 hk).1
  have h2 := this k hlt
  rw [getElem!_pos pb.succs k hlt, (Array.getElem?_eq_some_iff.1 hk).2, hF] at h2
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at h2
  exact ⟨hmem, h2.2, h2.1⟩

/-- The `Phi`s of an executable edge keep the invariant. -/
theorem sc_phis {fr : Frame} {b : ID} {i : Nat} (hb : b ∈ f.blocks)
    (hlive : live vis b i = true) (hinv : ∀ a, Claim tabs f C a (rv fr a)) :
    PhisP tabs f (fun _ a y => Claim tabs f C a y) fr b i := by
  intro bb hbb z hz v hv hph a ha c hc
  have hfix := K.fix z (lt_of_value? hv)
  obtain ⟨v', hv', -, hvb⟩ := hwf.valueId b bb ⟨hb, hbb⟩ z hz
  rw [hv] at hv'; cases hv'
  simp only [fixOK, hc, hv, hph, beq_self_eq_true, ite_true, List.all_eq_true,
    List.mem_range] at hfix
  have hi : i < v.args.size := (Array.getElem?_eq_some_iff.1 ha).1
  have h1 := hfix i hi
  rw [hvb, hlive, getElem!_pos v.args i hi, (Array.getElem?_eq_some_iff.1 ha).2] at h1
  simp only [Bool.not_true, Bool.false_or] at h1
  split at h1
  · rename_i c' hc'
    rw [← scalarEq_eq h1]
    exact retype_mono _ (hinv a c' hc')
  · cases h1

end

/-- **The source-side invariant of sccp**: registers with a constant cell hold `poison` or the
constant, while the source runs an executable block entered along an executable edge. -/
def sccpInv {tabs : Tables} {f g : Func} {C : Array (Option Lat)} {vis : Array Edge}
    {R : Array Bool} {ce : CheckEnv} (hwf : WF ce f) (K : Facts tabs f g C vis R) :
    SrcInv tabs f where
  P _ a y := Claim tabs f C a y
  L b i := b ∈ f.blocks ∧ R.getD b false = true ∧ live vis b i = true
  start := by
    have h := K.reach
    unfold reachOK at h
    simp only [Bool.and_eq_true] at h
    exact ⟨⟨hwf.entry, h.1.1, h.1.2⟩, fun a => Claim.poison _ _ _ a⟩
  poisonAtom _ a _ := Claim.poison _ _ _ a
  Q _ _ := True
  qstart := trivial
  qpois _ _ _ _ _ := trivial
  edge p _ pb fr e _ hpb hL hinv _ _ _ _ _ _ hst := by
    obtain ⟨k, hk, hF⟩ := stepTerm_feasible hinv hst
    obtain ⟨hm, hR, hl⟩ := sc_live hwf K hL.1 hpb hL.2.1 hk hF
    exact ⟨⟨hm, hR, hl⟩, hinv, sc_phis hwf K hm hl hinv, fun _ _ _ _ => trivial⟩
  qstep _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := trivial
  term _ _ _ x _ v hv ht ρ hρ := sc_term hwf K hv ht ρ hρ
  atom _ _ _ x _ v hv ht hph y := sc_atom hwf K hv ht hph _

@[simp] theorem sccpInv_P {tabs : Tables} {f g : Func} {C : Array (Option Lat)}
    {vis : Array Edge} {R : Array Bool} {ce : CheckEnv} (hwf : WF ce f)
    (K : Facts tabs f g C vis R) (b a : ID) (y : Val) :
    (sccpInv hwf K).P b a y = Claim tabs f C a y := rfl

end GoFV.Proof.Sccp

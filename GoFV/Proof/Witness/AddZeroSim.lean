import GoFV.Proof.Witness.AddZero
import GoFV.Proof.AtomSim

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness of the atom simulation: `addZero` through `checkedRewrite`

On `addZero` the checked rewrite pass replaces `0 + n` by `n` (`addZero_checkedRewrite`). Every
atom of the result (`InitMem`, `Arg`, `MakeResult`) and the `Ret` control read only atoms, the
same as in the input, so the term premises of `AtomSim.atomSim_refines` hold by
`sameAtomArgs_sound` (a kernel-evaluated test); with the validator's atom and closure facts the
simulation gives the pass's refinement on this instance: `addZero(7) = 7` in the output too.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof GoFV.Proof.Term GoFV.Opt.RewriteCheck

/-- `x` is not a term node of `D`. -/
def atomB (D : ID → Option Value) (x : ID) : Bool :=
  match D x with
  | some v => !termOp v.op
  | none => true

theorem not_isTerm_of_atomB {D : ID → Option Value} {x : ID} (h : atomB D x = true) :
    ¬ IsTerm D x := by
  rintro ⟨v, hv, ht⟩
  simp [atomB, hv, ht] at h

/-- An atom of both sides refines itself as a term. -/
theorem termRef_atom {D E : ID → Option Value} {tabs : Tables} {x : ID} (hD : atomB D x = true)
    (hE : atomB E x = true) : TermRef D tabs x E tabs x := by
  intro n
  refine ⟨n, fun ρ ρ' hρ _ _ => ?_⟩
  cases n with
  | zero => exact .poison _
  | succ n =>
    rw [AtomSim.den_succ_atom (not_isTerm_of_atomB hD), AtomSim.den_succ_atom (not_isTerm_of_atomB hE)]
    exact hρ x

/-- The arguments `x` (of `f`) and `y` (of `g`) of an atom or control: the same atom of both,
or a pair `R x y` refined by other means. -/
def argOK (R : ID → ID → Bool) (f g : Func) (x y : ID) : Bool :=
  (x == y && atomB f.value? x && atomB (listedDefs g) y) || R x y

/-- Every listed atom of `g` is `f`'s with the same fields, the blocks keep their kind,
successors and ID, the controls are `f`'s, and their arguments are pairwise `argOK R`. -/
def sameAtomArgs (R : ID → ID → Bool) (f g : Func) : Bool :=
  g.blocks.all fun b =>
    match f.block? b, g.block? b with
    | some fb, some gb =>
      gb.kind == fb.kind && gb.succs == fb.succs && gb.id == fb.id &&
      fb.controls.size == gb.controls.size &&
      (List.range gb.controls.size).all (fun k => argOK R f g fb.controls[k]! gb.controls[k]!) &&
      gb.values.all fun a =>
        match g.value? a with
        | some u => termOp u.op ||
          match f.value? a with
          | some u' => u'.op == u.op && u'.type == u.type && u'.auxInt == u.auxInt &&
              u'.aux == u.aux && u'.args.size == u.args.size &&
              (List.range u.args.size).all (fun i => argOK R f g u'.args[i]! u.args[i]!)
          | none => false
        | none => true
    | _, _ => false

theorem termRef_of_argOK {R : ID → ID → Bool} {tabs : Tables} {f g : Func}
    (hR : ∀ x y, R x y = true → TermRef f.value? tabs x (listedDefs g) tabs y) {x y : ID}
    (h : argOK R f g x y = true) : TermRef f.value? tabs x (listedDefs g) tabs y := by
  unfold argOK at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨rfl, h1⟩, h2⟩ | h
  · exact termRef_atom h1 h2
  · exact hR x y h

theorem sameAtomArgs_sound {R : ID → ID → Bool} {tabs : Tables} {f g : Func}
    (hR : ∀ x y, R x y = true → TermRef f.value? tabs x (listedDefs g) tabs y)
    (h : sameAtomArgs R f g = true) : AtomArgsRef tabs f g ∧ TermStepRef tabs f g := by
  unfold sameAtomArgs at h
  have hb := Array.all_eq_true_iff_forall_mem.1 h
  constructor
  · intro b hbm gb hgb a ha u hu ht
    have hb := hb b hbm
    cases hfb : f.block? b with
    | none => simp [hfb, hgb] at hb
    | some fb =>
      simp only [hfb, hgb, Bool.and_eq_true] at hb
      have hv := Array.all_eq_true_iff_forall_mem.1 hb.2 a ha
      simp only [hu, ht, Bool.false_or] at hv
      cases hfa : f.value? a with
      | none => simp [hfa] at hv
      | some u' =>
        simp only [hfa, Bool.and_eq_true, beq_iff_eq] at hv
        obtain ⟨⟨⟨⟨⟨hop, hty⟩, hai⟩, hax⟩, hsz⟩, hall⟩ := hv
        refine ⟨u', rfl, hop, hty, hai, hax, hsz, fun i hi => ?_⟩
        exact termRef_of_argOK hR (List.all_eq_true.1 hall i (List.mem_range.2 hi))
  · refine ControlsRef.toTermStepRef (fun b hbm fb gb hfb hgb => ?_) fun b hbm fb gb hfb hgb => ?_
    · have hb := hb b hbm
      simp only [hfb, hgb, Bool.and_eq_true, beq_iff_eq] at hb
      obtain ⟨⟨⟨-, hc⟩, hcs⟩, -⟩ := hb
      exact ⟨hc, fun k hk => termRef_of_argOK hR (List.all_eq_true.1 hcs k (List.mem_range.2 hk))⟩
    · have hb := hb b hbm
      simp only [hfb, hgb, Bool.and_eq_true, beq_iff_eq] at hb
      exact ⟨hb.1.1.1.1.1, hb.1.1.1.1.2, hb.1.1.1.2⟩

/-- The rewritten argument: `v4 = Add64 (Const64 [0]) v2` of `addZero` is refined by the atom
`v2` at every fuel (`Add64` of `0` and an `int64` is that integer, anything else `poison`). -/
theorem addZero_den4 {E : ID → Option Value} (hE : atomB E 2 = true) {ρ ρ' : ID → Val}
    (hρ : ValRef ρ ρ') : ∀ n, Sem.Refines (den addZero.value? azTabs ρ n 4) (den E azTabs ρ' n 2)
  | 0 => .poison _
  | 1 => .poison _
  | k + 2 => by
    rw [AtomSim.den_succ_atom (not_isTerm_of_atomB hE)]
    have h : den addZero.value? azTabs ρ (k + 2) 4 =
        (Sem.Int.add .w64 [.int .w64 0, ρ 2]).retype (.int .w64) := rfl
    rw [h]
    have h2 := hρ 2
    generalize ρ 2 = v at h2 ⊢
    generalize ρ' 2 = v' at h2
    cases v with
    | int w x =>
      cases h2
      by_cases hw : w = .w64
      · subst hw
        simp [Sem.Int.add, Sem.int2, Val.asInt, Val.retype]
        exact .int _ _
      · simp [Sem.Int.add, Sem.int2, Val.asInt, hw]
        exact .poison _
    | _ => simp [Sem.Int.add, Sem.int2, Val.asInt]; exact .poison _

theorem addZero_termRef4 {E : ID → Option Value} (hE : atomB E 2 = true) :
    TermRef addZero.value? azTabs 4 E azTabs 2 :=
  fun n => ⟨n, fun _ _ hρ _ _ => addZero_den4 hE hρ n⟩

/-- The control `v5 = MakeResult v4 v1` of `addZero` is refined by `MakeResult v2 v1`. -/
theorem addZero_termRef5 {E : ID → Option Value} (hE : atomB E 2 = true) (h1 : atomB E 1 = true)
    (h5 : E 5 = some { (addZero.value? 5).get! with args := #[2, 1] }) :
    TermRef addZero.value? azTabs 5 E azTabs 5 := by
  intro n
  refine ⟨n, fun ρ ρ' hρ _ _ => ?_⟩
  match n with
  | 0 => exact .poison _
  | k + 1 =>
    rw [AtomSim.den_succ_term h5 rfl,
      AtomSim.den_succ_term (show addZero.value? 5 = some ((addZero.value? 5).get!) from rfl) rfl]
    refine retype_mono _ (GoFV.Proof.Rules.opVal_mono _ _ _ _ _ ?_)
    show RefinesList [den _ _ ρ k 4, den _ _ ρ k 1] [den _ _ ρ' k 2, den _ _ ρ' k 1]
    refine .cons (addZero_den4 hE hρ k) (.cons ?_ .nil)
    match k with
    | 0 => exact .poison _
    | j + 1 =>
      rw [AtomSim.den_succ_atom (not_isTerm_of_atomB h1),
        AtomSim.den_succ_atom (D := addZero.value?) (not_isTerm_of_atomB (by decide +kernel))]
      exact hρ 1

/-- The pairs that are not the same atom: `MakeResult`'s first argument `v4` → `v2`, and the
`Ret` control `v5` (a term: `MakeResult`). -/
def azR (x y : ID) : Bool := (x == 4 && y == 2) || (x == 5 && y == 5)

theorem addZero_sameAtomArgs :
    (checkedRewrite (Interp.Table.ofRuleSet azRules) azPassEnv addZero).toOption.map
      (fun o => (sameAtomArgs azR addZero o.func, atomB (listedDefs o.func) 2,
        atomB (listedDefs o.func) 1,
        listedDefs o.func 5 == some { (addZero.value? 5).get! with args := #[2, 1] })) =
      some (true, true, true, true) := by
  decide +kernel

/-- **Witness**: the checked rewrite pass changes `addZero` and, by `AtomSim.atomSim_refines`
(all premises discharged), its output refines it under monotone contracts: with `Env.p1`,
`addZero(7) = 7` gives a run of the output returning `7`. -/
theorem addZero_atomSim :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet azRules) azPassEnv addZero = .ok out ∧
      (out.func.value? 5).map (·.args) = some #[2, 1] ∧
      RefinesUnder Env.Mono out.tables out.func azTabs addZero ∧
      ∃ fuel m, run Env.p1 out.tables out.func [.i64 7] {} fuel = .returned [.i64 7] m := by
  obtain ⟨out, hc, ht, h5, ⟨log, hv⟩, hf, hg⟩ := addZero_checkedRewrite
  obtain ⟨hA, hcf, hcg⟩ := GoFV.Proof.Pass.Rewrite.validate_parts hv
  have hs := addZero_sameAtomArgs
  rw [hc] at hs
  simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
  have hR : ∀ x y, azR x y = true → TermRef addZero.value? azTabs x (listedDefs out.func) azTabs y := by
    intro x y hxy
    simp only [azR, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hxy
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact addZero_termRef4 hs.2.1
    · exact addZero_termRef5 hs.2.1 hs.2.2.1 (beq_iff_eq.1 hs.2.2.2)
  obtain ⟨h1, h2⟩ := sameAtomArgs_sound hR hs.1
  have hr : RefinesUnder Env.Mono out.tables out.func azTabs addZero := by
    rw [ht]; exact AtomSim.atomSim_refines hf hg hA hcf hcg h1 h2
  refine ⟨out, hc, h5, hr, ?_⟩
  obtain ⟨m, hm⟩ := returnsInt_iff.1 addZero_checks.2.2
  obtain ⟨fuel', ho⟩ := hr Env.p1 Env.p1_mono [.i64 7] {} 1 (by rw [hm]; trivial)
  rw [hm] at ho
  refine ⟨fuel', ?_⟩
  generalize run Env.p1 out.tables out.func [.i64 7] {} fuel' = o at ho ⊢
  cases ho with
  | returned hl =>
    cases hl with
    | cons h1 t =>
      cases t
      cases h1
      exact ⟨_, rfl⟩

end GoFV.Proof.Witness

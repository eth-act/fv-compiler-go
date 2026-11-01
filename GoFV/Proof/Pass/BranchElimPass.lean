import GoFV.Proof.Pass.BranchElimSim
import GoFV.Proof.Pass.NumberLines
import GoFV.Opt.BranchElim

/-!
# branchelim refines its input

`branchelim_refines`: on an input without `NilCheck`, the output of `branchelimPass`
refines the input. The pass runs its rewrite loop with every rewrite checked (`stepOK`: the
result passes `check` and is a diamond merge of the previous function, `DRel`); the loop keeps
`Inv` (refines the input, passes `check`, no `NilCheck`), each accepted rewrite by
`refines_of_step`. The input's `postorder` cache does not change runs (`eraseF_postorder`).
-/

namespace GoFV.Proof.BranchElim

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.BranchElim GoFV.Proof

theorem checkOK_sound {ce : CheckEnv} {f : Func} (h : checkOK ce f = true) : check ce f = .ok () := by
  unfold checkOK at h
  split at h
  · rename_i h'; exact h'
  · cases h

theorem diamondB_sound {f g : Func} {dom post : ID} (h : diamondB f g dom post = true) :
    ∃ s, DRel f g s := by
  unfold diamondB at h
  split at h
  · rename_i s hs
    obtain ⟨h1, h2, -⟩ := site_spec hs
    exact ⟨s, ⟨by rw [h1, h2]; exact hs, h⟩⟩
  · cases h

theorem stepOK_sound {ce : CheckEnv} {f g : Func} {dom : ID} (h : stepOK ce f g dom = true) :
    check ce g = .ok () ∧ ∃ s, DRel f g s := by
  unfold stepOK at h
  rw [Bool.and_eq_true, List.any_eq_true] at h
  obtain ⟨h1, post, -, h2⟩ := h
  exact ⟨checkOK_sound h1, diamondB_sound h2⟩

/-- A checked rewrite introduces no `NilCheck`. -/
theorem noNil_step {f g : Func} {s : Site} (h : DRel f g s) (hn : Dead.NoNil f) : Dead.NoNil g := by
  intro x gv hgv
  have hv := value_spec h x
  unfold Site.valueOK at hv
  cases hfv : f.value? x with
  | none => rw [hfv, hgv] at hv; cases hv
  | some fv =>
    rw [hfv, hgv] at hv
    simp only [Bool.and_eq_true, beq_iff_eq] at hv
    obtain ⟨-, hv⟩ := hv
    split at hv
    · simp only [Bool.and_eq_true, beq_iff_eq] at hv
      rw [hv.1]; decide
    · simp only [Bool.and_eq_true, beq_iff_eq] at hv
      rw [hv.1]; exact hn x fv hfv

/-- The loop invariant: refines the input, passes `check`, has no `NilCheck`. -/
def Inv (tabs : Tables) (f0 f : Func) : Prop :=
  Refines tabs f tabs f0 ∧ (∃ ce, check ce f = .ok ()) ∧ Dead.NoNil f

theorem Inv.step {tabs : Tables} {f0 f g : Func} {ce : CheckEnv} {dom : ID} (hI : Inv tabs f0 f)
    (h : stepOK ce f g dom = true) : Inv tabs f0 g := by
  obtain ⟨hr, ⟨cf, hcf⟩, hn⟩ := hI
  obtain ⟨hcg, s, hrel⟩ := stepOK_sound h
  have S : Setup f g s := ⟨⟨cf, check_wf hcf⟩, ⟨ce, check_wf hcg⟩,
    Dom.certOK_of_check (check_domCert hcf), hrel, hn⟩
  exact ⟨hr.trans S.refines_of_step, ⟨ce, hcg⟩, noNil_step hrel hn⟩

theorem filter_some {o : Option Func} {p : Func → Bool} {g : Func} (h : o.filter p = some g) :
    p g = true := by
  cases o with
  | none => cases h
  | some x =>
    simp only [Option.filter] at h
    split at h
    · cases h; assumption
    · cases h

theorem sweep_inv {tabs : Tables} {f0 : Func} {c : BranchElim.Ctx} {ce : CheckEnv} :
    ∀ (bs : List ID) (f : Func) (ch : Bool) (f' : Func) (ch' : Bool),
      sweep c ce bs f ch = .ok (f', ch') → Inv tabs f0 f → Inv tabs f0 f'
  | [], f, ch, f', ch', h, hI => by
    simp only [sweep, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact hI
  | b :: bs, f, ch, f', ch', h, hI => by
    simp only [sweep, bind, Except.bind] at h
    cases he1 : elimIf c f b with
    | error e => rw [he1] at h; cases h
    | ok r1 =>
      rw [he1] at h
      simp only at h
      cases hr1 : r1.filter (stepOK ce f · b) with
      | some g =>
        rw [hr1] at h
        exact sweep_inv bs g true f' ch' h (hI.step (filter_some hr1))
      | none =>
        rw [hr1] at h
        simp only at h
        cases he2 : elimIfElse c f b with
        | error e => rw [he2] at h; cases h
        | ok r2 =>
          rw [he2] at h
          simp only at h
          cases hr2 : r2.filter (stepOK ce f · b) with
          | some g =>
            rw [hr2] at h
            exact sweep_inv bs g true f' ch' h (hI.step (filter_some hr2))
          | none =>
            rw [hr2] at h
            exact sweep_inv bs f ch f' ch' h hI

theorem rounds_inv {tabs : Tables} {f0 : Func} {c : BranchElim.Ctx} {ce : CheckEnv} :
    ∀ (n : Nat) (f g : Func), rounds c ce n f = .ok g → Inv tabs f0 f → Inv tabs f0 g
  | 0, f, g, h, hI => by
    simp only [rounds, pure, Except.pure, Except.ok.injEq] at h
    rw [← h]; exact hI
  | n + 1, f, g, h, hI => by
    simp only [rounds, bind, Except.bind] at h
    cases hs : sweep c ce f.blocks.toList f false with
    | error e => rw [hs] at h; cases h
    | ok r =>
      rw [hs] at h
      obtain ⟨f', ch⟩ := r
      have hI' := sweep_inv _ _ _ _ _ hs hI
      simp only at h
      split at h
      · exact rounds_inv n f' g h hI'
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        rw [← h]; exact hI'

theorem noNil_postorder {f : Func} (h : Dead.NoNil f) : Dead.NoNil f.postorder.2 := by
  intro x v hv
  apply h x v
  revert hv
  unfold Func.postorder
  split <;> exact id

/-- **branchelim refines its input** (checked input, no `NilCheck`). -/
theorem branchelim_refines {penv : PassEnv} {f : Func} {out : PassOut}
    (h : branchelimPass penv f = .ok out) (hnn : Dead.NoNil f) :
    Refines out.tables out.func penv.tables f := by
  simp only [branchelimPass, Pass.ofFunc, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i g hg
    cases h
    -- the output is the input, its `postorder` caching, or the checked loop's result from it
    have hpo : Refines penv.tables f.postorder.2 penv.tables f :=
      Refines.of_eraseF (eraseF_postorder f)
    unfold branchelim at hg
    simp only [bind, Except.bind, pure, Except.pure] at hg
    cases hfl : penv.flag "havecondselect" with
    | error e => rw [hfl] at hg; cases hg
    | ok fl =>
      rw [hfl] at hg
      simp only at hg
      split at hg
      · cases hg; exact Refines.refl _ _
      · cases hc : ctxOf penv f.postorder.2 f.postorder.1 with
        | error e => rw [hc] at hg; cases hg
        | ok c =>
          rw [hc] at hg
          simp only at hg
          split at hg
          · cases hg; exact hpo
          · rename_i hck
            have hck' : checkOK { tabs := penv.tables, typs := penv.typs } f.postorder.2 = true := by
              simpa using hck
            exact (rounds_inv _ _ _ hg ⟨hpo, ⟨_, checkOK_sound hck'⟩, noNil_postorder hnn⟩).1

end GoFV.Proof.BranchElim

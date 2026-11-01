import GoFV.Proof.Pass.BranchElimSim
import GoFV.Proof.Pass.BranchElimPres
import GoFV.Proof.Pass.NumberLines
import GoFV.Opt.BranchElim

/-!
# branchelim refines its input

`branchelim_refines`: the output of `branchelimPass` refines its input. The pass checks its input
once (`check`, giving `Dom.WFDom`: well formed, uses dominated on paths) and runs its rewrite
loop with every rewrite checked (`stepOK`: the result is a diamond merge of the previous
function, `DRel`, with no `check` of the result); the loop keeps `Inv` (refines the input,
`WFDom`), each accepted rewrite by `refines_of_step`, `DRel.wf_pres` and `DRel.useDom_pres`.
The input's `postorder` cache does not change runs (`eraseF_postorder`).
-/

namespace GoFV.Proof.BranchElim

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.BranchElim GoFV.Proof Dom

theorem diamondB_sound {f g : Func} {dom post : ID} (h : diamondB f g dom post = true) :
    ∃ s, DRel f g s := by
  unfold diamondB at h
  split at h
  · rename_i s hs
    obtain ⟨h1, h2, -⟩ := site_spec hs
    exact ⟨s, ⟨by rw [h1, h2]; exact hs, h⟩⟩
  · cases h

theorem stepOK_sound {f g : Func} {dom : ID} (h : stepOK f g dom = true) : ∃ s, DRel f g s := by
  unfold stepOK at h
  rw [List.any_eq_true] at h
  obtain ⟨post, -, h2⟩ := h
  exact diamondB_sound h2

/-- The loop invariant: refines the input, well formed with uses dominated on paths. -/
def Inv (tabs : Tables) (f0 f : Func) : Prop :=
  Refines tabs f tabs f0 ∧ ∃ ce, WFDom ce f

theorem Inv.step {tabs : Tables} {f0 f g : Func} {dom : ID} (hI : Inv tabs f0 f)
    (h : stepOK f g dom = true) : Inv tabs f0 g := by
  obtain ⟨hr, ce, hwd⟩ := hI
  obtain ⟨s, hrel⟩ := stepOK_sound h
  have hwg := hrel.wf_pres hwd.wf
  have S : Setup f g s := ⟨⟨⟨ce, hwd.wf⟩, hrel⟩, ⟨ce, hwg⟩, hwd.dom⟩
  exact ⟨hr.trans S.refines_of_step, ce, hwg, hrel.useDom_pres hwd.wf hwd.dom⟩

theorem filter_some {o : Option Func} {p : Func → Bool} {g : Func} (h : o.filter p = some g) :
    p g = true := by
  cases o with
  | none => cases h
  | some x =>
    simp only [Option.filter] at h
    split at h
    · cases h; assumption
    · cases h

theorem sweep_inv {tabs : Tables} {f0 : Func} {c : BranchElim.Ctx} :
    ∀ (bs : List ID) (f : Func) (ch : Bool) (f' : Func) (ch' : Bool),
      sweep c bs f ch = .ok (f', ch') → Inv tabs f0 f → Inv tabs f0 f'
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
      cases hr1 : r1.filter (stepOK f · b) with
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
          cases hr2 : r2.filter (stepOK f · b) with
          | some g =>
            rw [hr2] at h
            exact sweep_inv bs g true f' ch' h (hI.step (filter_some hr2))
          | none =>
            rw [hr2] at h
            exact sweep_inv bs f ch f' ch' h hI

theorem rounds_inv {tabs : Tables} {f0 : Func} {c : BranchElim.Ctx} :
    ∀ (n : Nat) (f g : Func), rounds c n f = .ok g → Inv tabs f0 f → Inv tabs f0 g
  | 0, f, g, h, hI => by
    simp only [rounds, pure, Except.pure, Except.ok.injEq] at h
    rw [← h]; exact hI
  | n + 1, f, g, h, hI => by
    simp only [rounds, bind, Except.bind] at h
    cases hs : sweep c f.blocks.toList f false with
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

/-- **branchelim refines its input.** -/
theorem branchelim_refines {penv : PassEnv} {f : Func} {out : PassOut}
    (h : branchelimPass penv f = .ok out) :
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
            exact (rounds_inv _ _ _ hg ⟨hpo, _, WFDom.of_check (checkOK_sound hck')⟩).1

end GoFV.Proof.BranchElim

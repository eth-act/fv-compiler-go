import GoFV.Proof.Pass.MoveL
import GoFV.Proof.Low.TabsAgreeL
import GoFV.Opt.PairCheck
import GoFV.Opt.Pair

variable [GoFV.SSA.Sem.Addrs]

/-!
# `pair` refines its input on `runL` (issue #385)

`pair_refinesL`: `pair` keeps the CFG; it makes two loads of adjacent elements the selectors of a
pair load and two adjacent stores a pair store and a memory `Copy`. For an input and output that
pass `check` and that the `pair` validator `PairCheck.pairB` accepts (translation validation:
the tables agree for the input, `tabsAgreeL`, and the value-motion validator with `pair`'s cases,
`pairMoveB`, accepts the pair in the output's tables), the output refines the input under
`runL`: `refinesL_of_moveWith` with `pr` in the output's tables, then the input in its own
tables (`Low.runL_tabsAgreeL`).
-/

namespace GoFV.Proof.MoveL

open GoFV.SSA GoFV.Opt GoFV.Proof.Dom

/-- **pair refines its input on `runL`.** -/
theorem pair_refinesL {penv : PassEnv} {f : Func} {out : PassOut} {ce ce' : CheckEnv}
    (_h : pairPass penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ())
    (hv : PairCheck.pairB penv.tables out.tables f out.func = true) :
    RefinesL out.tables out.func penv.tables f := by
  unfold PairCheck.pairB pairMoveB at hv
  simp only [Bool.and_eq_true] at hv
  obtain ⟨hta, hsel, hmv⟩ := hv
  have h1 : RefinesL out.tables out.func out.tables f :=
    refinesL_of_moveWith (pr := true) ⟨⟨ce, check_wf hf⟩, ⟨ce', check_wf hg⟩,
      certOK_of_check (check_domCert hf), certOK_of_check (check_domCert hg), hmv⟩ fun _ => hsel
  exact RefinesL.trans (RefinesL.of_runL_eq fun env args mem fuel =>
    Low.runL_tabsAgreeL hta env args mem fuel) h1

end GoFV.Proof.MoveL

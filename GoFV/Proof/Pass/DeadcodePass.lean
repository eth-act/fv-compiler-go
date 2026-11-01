import GoFV.Proof.Pass.DeadSim
import GoFV.Proof.Pass.DeadFrag
import GoFV.Proof.Pass.DeadChain
import GoFV.Opt.Deadcode

/-!
# deadcode refines its input (all five instances)

`deadcode_refines`: for an input and output that pass `check`, with the input in the fragment
`DeadFrag`, the output of `deadcodePass` refines its input (`refines_of_deadRel`).

`DeadFrag tabs f`: deadcode's output `g` keeps blocks, values and edges of `f` (`DeadRel`: the
removed edges, unreachable blocks and dead values are dropped, a reachable `First` block becomes
`Plain`, and the kept values are unchanged; checked on the output by `deadRelB`, a translation
validation of the static part of the pass), the side-effecting roots of the kept blocks of `f`
are chained, and `f` has no `NilCheck`. `deadFragB` is a sufficient condition for checked
inputs (`deadFrag_of`; `chainedB` searches the dependencies `Chained` needs);
`lake exe deadcode-probe` counts the corpus sections that satisfy it. Outside
it: inputs where the copyelim step of deadcode changes a kept value (a copy argument, or a `Phi`
of a reachable block that loses its arguments from unreachable predecessors and becomes a copy);
#83 has the plan to cover them by carrying copyelim's relation (`CopyRel`).
-/

namespace GoFV.Proof.Dead

open GoFV.SSA GoFV.Opt GoFV.Proof

/-- deadcode's input fragment (see the module doc). -/
def DeadFrag (tabs : Tables) (f : Func) : Prop :=
  ∀ g, deadcode tabs f = .ok g → DeadRel f g ∧ Chained f (· ∈ g.blocks) ∧ NoNil f

/-- A sufficient condition for `DeadFrag`, for checked inputs (`deadFrag_of`). -/
def deadFragB (tabs : Tables) (f : Func) : Bool :=
  match deadcode tabs f with
  | .ok g => deadRelB f g && chainedB f g.blocks && noNilB f
  | .error _ => true

theorem deadFrag_of {ce : CheckEnv} {tabs : Tables} {f : Func} (hf : check ce f = .ok ())
    (h : deadFragB tabs f = true) : DeadFrag tabs f := by
  intro g hg
  unfold deadFragB at h
  rw [hg] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨deadRelB_sound h1, chained_of (check_wf hf) (deadRelB_blocks h1) h2, noNil_of h3⟩

/-- **deadcode refines its input** (`early`, `pre-opt`, `opt`, `gcse` and `generic deadcode`). -/
theorem deadcode_refines {penv : PassEnv} {f : Func} {out : PassOut} {ce ce' : CheckEnv}
    (h : deadcodePass penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) (hfrag : DeadFrag penv.tables f) :
    Refines out.tables out.func penv.tables f := by
  simp only [deadcodePass, Pass.ofFunc, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i g hd
    cases h
    obtain ⟨hrel, hch, hnn⟩ := hfrag g hd
    exact refines_of_deadRel ⟨⟨ce, check_wf hf⟩, ⟨ce', check_wf hg⟩, hrel, hch, hnn⟩

end GoFV.Proof.Dead

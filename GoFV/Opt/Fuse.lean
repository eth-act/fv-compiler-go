import GoFV.Opt.Pass
import GoFV.Opt.Fuse.Basic
import GoFV.Opt.Fuse.PlainCheck
import GoFV.Opt.Fuse.ComparisonsCheck
import GoFV.Opt.Fuse.IfCheck
import GoFV.Opt.Fuse.BranchRedirectCheck

/-!
# early fuse and late fuse (`fuseEarly`, `fuseLate`, `fuse.go:13-18`)

- `fuseEarly`: `fuse(f, fuseTypePlain | fuseTypeIntInRange | fuseTypeSingleBitDifference |
  fuseTypeNanCheck)`: per block (backwards over `f.Blocks`), `fuseIntInRange`,
  `fuseSingleBitDifference`, `fuseNanCheck`, then `fuseBlockPlain`, each on the same `b`.
- `fuseLate`: `fuse(f, fuseTypePlain | fuseTypeIf | fuseTypeBranchRedirect)`: per block
  `fuseBlockIf` then `fuseBlockPlain`; after each sweep `fuseBranchRedirect` (prove's facts
  table).

`fuseBlockPlain` runs checked in place (`Plain.fuseBlockPlainChecked`, proof
`GoFV.Proof.FusePlain.fuseBlockPlainChecked_refines`): a rewrite the checker rejects is an
error, and the pass then returns its input unchanged (`orInput`; never on the corpus). Early
fuse's comparison fusions run checked too (`Cmp.fuseComparisonsChecked`, proof
`GoFV.Proof.FuseCmp.fuseComparisonsChecked_refines`; a rejected rewrite is skipped). The step
checkers need no `check` of their results (issue #147): both passes run the slim input check
`wfDomCheck` once, on their input, and return a function that fails it unchanged (every corpus
input passes); the refinement theorems are `GoFV.Proof.FuseEarly.fuseEarly_refines` and
`GoFV.Proof.FuseLate.fuseLate_refines`. Late fuse's `fuseBlockIf` runs checked
(`fuseBlockIfChecked`, proof `GoFV.Proof.FuseIf.fuseBlockIfChecked_refines`): its rare rewrites
(1,586 on the full corpus) are checked with `check`, a rejected one is skipped (never on the
corpus). Its branch redirects run checked (`fuseBranchRedirectChecked`: prove's validator
decides each redirected branch, `Redir.stepOK`; proof
`GoFV.Proof.FuseRedirect.fuseBranchRedirectChecked_ok`); a rejected redirect is skipped (never on
the corpus).
-/

namespace GoFV.Opt

open GoFV.SSA GoFV.Opt.Fuse

namespace Fuse

/-- The early fuse per-block step: the three comparison fusions, then `fuseBlockPlain`, each
checked. -/
def earlyStep (isMem : TypeRef → Bool) (f : Func) (b : ID) :
    Except String (Func × Bool) := do
  let (f, c1) := Cmp.fuseComparisonsChecked isMem canOptIntInRange f b
  let (f, c2) := Cmp.fuseComparisonsChecked isMem canOptSingleBitDifference f b
  let (f, c3) := Cmp.fuseComparisonsChecked isMem canOptNanCheck f b
  let (f, c4) ← Plain.fuseBlockPlainChecked f b
  pure (f, c1 || c2 || c3 || c4)

/-- The late fuse per-block step: `fuseBlockIf`, then `fuseBlockPlain`. -/
def lateStep (ce : CheckEnv) (tv : TypeView) (f : Func) (b : ID) :
    Except String (Func × Bool) := do
  let (f, c1) ← fuseBlockIfChecked ce tv f b
  let (f, c2) ← Plain.fuseBlockPlainChecked f b
  pure (f, c1 || c2)

/-- The fuse type queries from the pass environment. -/
def typeView (env : PassEnv) : Except String TypeView := do
  let some mem := env.typ? "Mem" | throw "fuse: no typ Mem"
  let some void := env.typ? "Void" | throw "fuse: no typ Void"
  return { tabs := env.tables, mem, void }

end Fuse

/-- `fuseEarly(f)`, every rewrite checked; the step checkers' proofs assume a well-formed input
with dominated uses (`wfDomCheck`), so a function that fails it is returned unchanged. -/
def fuseEarly (tv : TypeView) (f : Func) : Except String Func :=
  if !wfDomOK f then .ok f else
  orInput f (fuseLoop (Fuse.earlyStep tv.isMem) none roundFuel f)

/-- The `early fuse` pass. -/
def fuseEarlyPass : Pass := Pass.ofFunc fun env f => do
  fuseEarly (← Fuse.typeView env) f

/-- `fuseLate(f)`, every rewrite checked; the step checkers' proofs assume a well-formed input
with dominated uses (`wfDomCheck`), so a function that fails it is returned unchanged. -/
def fuseLate (ce : CheckEnv) (tv : TypeView) (pv : Prove.Prover) (f : Func) :
    Except String Func :=
  if !wfDomOK f then .ok f else
  orInput f (fuseLoop (Fuse.lateStep ce tv) (some (fuseBranchRedirectChecked pv ce.tabs))
    roundFuel f)

/-- The `late fuse` pass. -/
def fuseLatePass : Pass := Pass.ofFunc fun env f => do
  fuseLate { tabs := env.tables, typs := env.typs } (← Fuse.typeView env)
    (← Prove.Prover.ofEnv env) f

end GoFV.Opt

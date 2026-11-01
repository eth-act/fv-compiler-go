import GoFV.Opt.Pass
import GoFV.Opt.Fuse.Basic
import GoFV.Opt.Fuse.PlainCheck
import GoFV.Opt.Fuse.ComparisonsCheck
import GoFV.Opt.Fuse.If
import GoFV.Opt.Fuse.BranchRedirect

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
checkers need no `check` of their results (issue #147): early fuse runs `check` once, on its
input, and returns a function that fails it unchanged (every corpus input passes); its
refinement theorem is `GoFV.Proof.FuseEarly.fuseEarly_refines`.
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
def lateStep (tv : TypeView) (f : Func) (b : ID) : Except String (Func × Bool) := do
  let (f, c1) ← fuseBlockIf tv f b
  let (f, c2) ← Plain.fuseBlockPlainChecked f b
  pure (f, c1 || c2)

/-- The fuse type queries from the pass environment. -/
def typeView (env : PassEnv) : Except String TypeView := do
  let some mem := env.typ? "Mem" | throw "fuse: no typ Mem"
  let some void := env.typ? "Void" | throw "fuse: no typ Void"
  return { tabs := env.tables, mem, void }

end Fuse

/-- `fuseEarly(f)`, every rewrite checked; the step checkers' proofs assume an input that passes
`check`, so a function that fails it is returned unchanged. -/
def fuseEarly (ce : CheckEnv) (tv : TypeView) (f : Func) : Except String Func :=
  if !checkOK ce f then .ok f else
  orInput f (fuseLoop (Fuse.earlyStep tv.isMem) none roundFuel f)

/-- The `early fuse` pass. -/
def fuseEarlyPass : Pass := Pass.ofFunc fun env f => do
  fuseEarly { tabs := env.tables, typs := env.typs } (← Fuse.typeView env) f

/-- `fuseLate(f)`. -/
def fuseLate (ce : CheckEnv) (tv : TypeView) (pv : Prove.Prover) (f : Func) :
    Except String Func :=
  orInput f (fuseLoop (Fuse.lateStep tv) (some (fuseBranchRedirect pv)) roundFuel f)

/-- The `late fuse` pass. -/
def fuseLatePass : Pass := Pass.ofFunc fun env f => do
  fuseLate { tabs := env.tables, typs := env.typs } (← Fuse.typeView env)
    (← Prove.Prover.ofEnv env) f

end GoFV.Opt

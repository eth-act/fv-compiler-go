import GoFV.Opt.Pass
import GoFV.Opt.Fuse.Basic
import GoFV.Opt.Fuse.Plain
import GoFV.Opt.Fuse.If
import GoFV.Opt.Fuse.Comparisons
import GoFV.SSA.TypePred

/-!
# early fuse (`fuseEarly`, `fuse.go:13`)

`fuse(f, fuseTypePlain | fuseTypeIntInRange | fuseTypeSingleBitDifference | fuseTypeNanCheck)`:
per block (backwards over `f.Blocks`), `fuseIntInRange`, `fuseSingleBitDifference`,
`fuseNanCheck`, then `fuseBlockPlain`, each on the same `b`.
-/

namespace GoFV.Opt

open GoFV.SSA GoFV.Opt.Fuse

namespace Fuse

/-- The early fuse per-block step. -/
def earlyStep (isMem : TypeRef → Bool) (f : Func) (b : ID) : Except String (Func × Bool) :=
  let (f, c1) := fuseComparisons isMem canOptIntInRange f b
  let (f, c2) := fuseComparisons isMem canOptSingleBitDifference f b
  let (f, c3) := fuseComparisons isMem canOptNanCheck f b
  let (f, c4) := fuseBlockPlain f b
  pure (f, c1 || c2 || c3 || c4)

/-- The fuse type queries from the pass environment. -/
def typeView (env : PassEnv) : Except String TypeView := do
  let some mem := env.typ? "Mem" | throw "fuse: no typ Mem"
  let some void := env.typ? "Void" | throw "fuse: no typ Void"
  return { isMem := env.tables.isMemory mem, void }

end Fuse

/-- `fuseEarly(f)`. -/
def fuseEarly (tv : TypeView) (f : Func) : Except String Func :=
  fuseLoop (Fuse.earlyStep tv.isMem) none roundFuel f

/-- The `early fuse` pass. -/
def fuseEarlyPass : Pass := Pass.ofFunc fun env f => do fuseEarly (← Fuse.typeView env) f

end GoFV.Opt

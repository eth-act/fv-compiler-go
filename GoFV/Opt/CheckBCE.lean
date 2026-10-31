import GoFV.Opt.Pass

/-!
# check bce (`checkbce.go`)

`checkbce` only emits diagnostics (`f.Warnl` with `-d=ssa/check_bce/debug>0`, `logopt` with
`-json`); it never mutates the function in any configuration (`docs/PASSES.md`, check bce).
-/

namespace GoFV.Opt

open GoFV.SSA

/-- `checkbce(f)`: the SSA is unchanged. -/
def checkbce (f : Func) : Func := f

theorem checkbce_eq (f : Func) : checkbce f = f := rfl

/-- The `check bce` pass. -/
def checkbcePass : Pass := Pass.ofFunc fun _ f => pure (checkbce f)

end GoFV.Opt

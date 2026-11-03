import GoFV.Opt.CSE

/-!
# lowered cse (`cse.go`)

The `generic cse` port run on lowered ARM64 SSA (docs/PASSES2.md, lowered cse; issue #393),
without the translation validator: `CSE.crel`'s semantics covers generic ops only.
-/

namespace GoFV.Opt

/-- The `lowered cse` pass. -/
def loweredCsePass : Pass := Pass.ofFunc fun env f => do cse (← cseCtx env) f

end GoFV.Opt

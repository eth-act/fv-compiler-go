import GoFV.Opt.CSE

/-!
# lowered cse (`cse.go`)

The `generic cse` port run on lowered ARM64 SSA (docs/PASSES2.md, lowered cse; issue #393),
unvalidated, as Go runs it. `GoFV.Proof.CSEL.loweredCse_refinesL` proves it refines its input
under `runL` when the lowered checker accepts its result (`CSEL.frag`, `GoFV.Opt.LoweredCSECheck`).
-/

namespace GoFV.Opt

/-- The `lowered cse` pass. -/
def loweredCsePass : Pass := Pass.ofFunc fun env f => do cse (← cseCtx env) f

end GoFV.Opt

import GoFV.Opt.NumberLines
import GoFV.Opt.CheckBCE
import GoFV.Opt.SoftFloat
import GoFV.Opt.ReschedChecks
import GoFV.Opt.CpuFeatures
import GoFV.Opt.CopyElim
import GoFV.Opt.ZCSE
import GoFV.Opt.Deadcode
import GoFV.Opt.ShortCircuit
import GoFV.Opt.Fuse

/-!
# Registered Lean passes

One `PassEntry` per ported stock pass function, with the stock names of its pipeline instances
(`compile.go` `passes`). `pass-parity` checks every entry it selects; add a line here when a
port lands.
-/

namespace GoFVTest.Parity

open GoFV.Opt

def registry : Array PassEntry := #[
  { fn := "numberLines", names := #["number lines"], run := numberLinesPass },
  { fn := "copyelim", names := #["early phielim and copyelim"], run := copyelimPass },
  { fn := "deadcode", run := deadcodePass,
    names := #["early deadcode", "pre-opt deadcode", "opt deadcode", "gcse deadcode",
               "generic deadcode"] },
  { fn := "zcse", names := #["zero arg cse"], run := zcsePass },
  { fn := "shortcircuit", names := #["short circuit"], run := shortcircuitPass },
  { fn := "fuseEarly", names := #["early fuse"], run := fuseEarlyPass },
  { fn := "softfloat", names := #["softfloat"], run := softfloatPass },
  { fn := "checkbce", names := #["check bce"], run := checkbcePass },
  { fn := "insertLoopReschedChecks", names := #["insert resched checks"],
    run := reschedChecksPass, disabled := reschedChecksDisabled },
  { fn := "cpufeatures", names := #["cpufeatures"], run := cpufeaturesPass,
    disabled := simdDisabled },
  { fn := "rewriteTern", names := #["rewrite tern"], run := rewriteTernPass,
    disabled := simdDisabled }
]

end GoFVTest.Parity

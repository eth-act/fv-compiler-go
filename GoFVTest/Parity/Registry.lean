import GoFV.Opt.ExpandCalls
import GoFV.Opt.WriteBarrier
import GoFV.Opt.NilCheck
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
import GoFV.Opt.ElimDeadAutos
import GoFV.Opt.DeadStore
import GoFV.Opt.MemCombine
import GoFV.Opt.KnownBits
import GoFV.Opt.PhiOpt
import GoFV.Opt.BranchElim
import GoFV.Opt.Opt
import GoFV.Opt.CSE
import GoFV.Opt.Prove.Pass
import GoFV.Opt.Decompose

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
  { fn := "opt", names := #["opt", "middle opt", "late opt"], run := opt },
  { fn := "divisible", names := #["divisible"], run := divisible },
  { fn := "divmod", names := #["divmod"], run := divmod },
  { fn := "zcse", names := #["zero arg cse"], run := zcsePass },
  { fn := "shortcircuit", names := #["short circuit"], run := shortcircuitPass },
  { fn := "fuseEarly", names := #["early fuse"], run := fuseEarlyPass },
  { fn := "nilcheckelim", names := #["nilcheckelim"], run := nilcheckelimPass },
  { fn := "expandCalls", names := #["expand calls"], run := expandCallsPass },
  { fn := "fuseLate", names := #["late fuse"], run := fuseLatePass },
  { fn := "softfloat", names := #["softfloat"], run := softfloatPass },
  { fn := "checkbce", names := #["check bce"], run := checkbcePass },
  { fn := "elimDeadAutosGeneric", names := #["dead auto elim"], run := elimDeadAutosPass },
  { fn := "dse", names := #["dse"], run := dsePass },
  { fn := "memcombine", names := #["memcombine"], run := memcombinePass },
  { fn := "writebarrier", names := #["writebarrier"], run := writebarrierPass },
  { fn := "insertLoopReschedChecks", names := #["insert resched checks"],
    run := reschedChecksPass, disabled := reschedChecksDisabled },
  { fn := "cpufeatures", names := #["cpufeatures"], run := cpufeaturesPass,
    disabled := simdDisabled },
  { fn := "rewriteTern", names := #["rewrite tern"], run := rewriteTernPass,
    disabled := simdDisabled },
  { fn := "knownBits", names := #["known bits"], run := knownBitsPass },
  { fn := "phiopt", names := #["phiopt"], run := phioptPass },
  { fn := "branchelim", names := #["branchelim"], run := branchelimPass },
  { fn := "cse", names := #["generic cse"], run := csePass },
  { fn := "prove", names := #["prove"], run := provePass },
  { fn := "decomposeUser", names := #["decompose user"], run := Decompose.decomposeUserPass },
  { fn := "postExpandCallsDecompose", names := #["decompose builtin"],
    run := Decompose.postExpandCallsDecomposePass }
]

end GoFVTest.Parity

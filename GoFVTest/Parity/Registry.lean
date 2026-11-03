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
import GoFV.Opt.KnownBitsCheck
import GoFV.Opt.PhiOpt
import GoFV.Opt.PhiOptCheck
import GoFV.Opt.BranchElim
import GoFV.Opt.Opt
import GoFV.Opt.CSE
import GoFV.Opt.Prove.Pass
import GoFV.Opt.Decompose
import GoFV.Opt.SccpReplay
import GoFV.Opt.SccpCheck
import GoFV.Opt.Lower
import GoFV.Opt.CheckLower
import GoFV.Opt.ElimUnreadAutos
import GoFV.Opt.TupleSelectors
import GoFV.Opt.Pair
import GoFV.Opt.LoweredCSE
import GoFV.Opt.Schedule
import GoFV.Opt.NilCheckLate
import GoFV.Opt.FlagAlloc
import GoFV.Opt.LoopRotate
import GoFV.Opt.Trim
import GoFV.Opt.Licm
import GoFV.Opt.Tighten
import GoFV.Opt.Critical
import GoFV.Opt.LikelyAdjust
import GoFV.Opt.Layout

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
  { fn := "copyelim", names := #["early phielim and copyelim", "late phielim and copyelim"],
    run := copyelimPass },
  { fn := "deadcode", run := deadcodePass,
    names := #["early deadcode", "pre-opt deadcode", "opt deadcode", "gcse deadcode",
               "generic deadcode", "lowered deadcode for cse", "lowered deadcode",
               "late deadcode"] },
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
  { fn := "sccp", names := #["sccp"], run := sccpChecked, replay := some sccpReplay },
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
    run := Decompose.postExpandCallsDecomposePass },
  { fn := "lower", names := #["lower"], run := lower },
  { fn := "lateLower", names := #["late lower"], run := lateLower },
  { fn := "addressingModes", names := #["addressing modes"], run := addressingModesPass },
  { fn := "pair", names := #["pair"], run := pairPass },
  { fn := "cse", names := #["lowered cse"], run := loweredCsePass },
  { fn := "elimUnreadAutos", names := #["elim unread autos"], run := elimUnreadAutosPass },
  { fn := "tightenTupleSelectors", names := #["tighten tuple selectors"],
    run := tightenTupleSelectorsPass },
  { fn := "checkLower", names := #["checkLower"], run := checkLowerPass },
  { fn := "licm", names := #["loop invariant"], run := licmPass },
  { fn := "tighten", names := #["tighten"], run := tightenPass },
  { fn := "critical", names := #["critical"], run := criticalPass },
  { fn := "phiTighten", names := #["phi tighten"], run := phiTightenPass },
  { fn := "likelyadjust", names := #["likelyadjust"], run := likelyadjustPass },
  { fn := "layout", names := #["layout"], run := layoutPass },
  { fn := "schedule", names := #["schedule"], run := schedulePass },
  { fn := "nilcheckelim2", names := #["late nilcheck"], run := nilcheckelim2Pass },
  { fn := "flagalloc", names := #["flagalloc"], run := flagallocPass },
  { fn := "loopRotate", names := #["loop rotate"], run := loopRotatePass },
  { fn := "trim", names := #["trim"], run := trimPass }
]

end GoFVTest.Parity

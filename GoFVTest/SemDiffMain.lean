import GoFVTest.SemDiff

/-! Entry point of `sem-difftest` (`GoFVTest/SemDiff.lean`), kept apart so that other tools can
import the difftest's value builder and printer. -/

open scoped GoFV.SSA.Sem.Fixed

def main (args : List String) : IO UInt32 := GoFVTest.SemDiff.run args

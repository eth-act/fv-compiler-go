import GoFV.SSA.Parse
import GoFV.SSA.Check

/-!
# `check-bench`: where `check` spends its time

For every section of every `.ssa` file under the arguments, the time of `check` and of its
parts: `checkGo` (Go's `checkFunc`), `DomCert.check`, `checkArgShapes`, and inside `checkGo`
the dominator tree (`postorder` + `dominators` + `newSparseTree`), the loop nest and `memCheck`.
-/

open GoFV.SSA

namespace GoFVTest.CheckBench

def main (args : List String) : IO UInt32 := do
  let mut files := #[]
  for a in args do
    let p : System.FilePath := a
    if ← p.isDir then
      files := files ++ ((← p.walkDir).filter (·.extension == some "ssa"))
    else files := files.push p
  let names := #["check", "checkGo", "DomCert.check", "checkArgShapes", "dom tree", "loopnest",
    "memCheck"]
  let mut t : Array Nat := Array.replicate names.size 0
  let mut n := 0
  let mut bad := 0
  for path in files do
    let data ← IO.FS.readBinFile path
    let .ok ex := parseExport data | continue
    let typs := ((ex.sections[0]?).bind (·.typs)).getD #[]
    let mut tables : Tables := {}
    for h : si in [0:ex.sections.size] do
      let s := ex.sections[si]
      tables := tables.addAll s.defs
      let ce : CheckEnv := { tabs := tables, typs }
      let f := s.func
      n := n + 1
      let ok (r : Except String Unit) : Bool := match r with | .ok () => true | .error _ => false
      let t0 ← IO.monoNanosNow
      let r0 ← IO.lazyPure fun _ => ok (check ce f)
      let t1 ← IO.monoNanosNow
      let _ ← IO.lazyPure fun _ => ok (checkGo ce f)
      let t2 ← IO.monoNanosNow
      let _ ← IO.lazyPure fun _ => ok (DomCert.check f)
      let t3 ← IO.monoNanosNow
      let _ ← IO.lazyPure fun _ => ok (checkArgShapes ce f)
      let t4 ← IO.monoNanosNow
      let po ← IO.lazyPure fun _ => Analysis.postorder f
      let tr ← IO.lazyPure fun _ =>
        Analysis.newSparseTree (f.bidLast + 1) f.entry po (Analysis.dominators f)
      let t5 ← IO.monoNanosNow
      let _ ← IO.lazyPure fun _ => (Analysis.loopnest f po tr).toBool
      let t6 ← IO.monoNanosNow
      let _ ← IO.lazyPure fun _ => ok (Check.memCheck ce f)
      let t7 ← IO.monoNanosNow
      if !r0 then bad := bad + 1
      t := #[t[0]! + (t1 - t0), t[1]! + (t2 - t1), t[2]! + (t3 - t2), t[3]! + (t4 - t3),
        t[4]! + (t5 - t4), t[5]! + (t6 - t5), t[6]! + (t7 - t6)]
  IO.println s!"sections {n}, check fails {bad}"
  for h : k in [0:names.size] do
    IO.println s!"{names[k]}: {(t[k]! / 1000000 : Nat)} ms"
  return 0

end GoFVTest.CheckBench

def main (args : List String) : IO UInt32 := GoFVTest.CheckBench.main args

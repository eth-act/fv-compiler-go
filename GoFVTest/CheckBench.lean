import GoFV.SSA.Parse
import GoFV.SSA.Check
import GoFV.SSA.WFCheck

/-!
# `check-bench`: where `check` spends its time

For every section of every `.ssa` file under the arguments, the time of `check` and of its
parts: `checkGo` (Go's `checkFunc`), `DomCert.check`, `checkArgShapes`, and inside `checkGo`
the dominator tree (`postorder` + `dominators` + `newSparseTree`), the loop nest and `memCheck`;
then the slim input check of the checked CFG passes (`wfDomCheck`), its structural part
(`wfCheck`), the certificate construction (`DomCert.make`; Go's `Analysis.dominators` alone for
comparison) and the four certificate tests. `wfDomCheck` must accept every section `check`
accepts, and the certificate's tree must be Go's. `--pass NAME` times only the inputs of pass
`NAME`'s sections (the functions that pass's input guard sees).
-/

open GoFV.SSA

namespace GoFVTest.CheckBench

partial def parseArgs : List String → Option String → Array String → Option String × Array String
  | "--pass" :: p :: rest, _, ps => parseArgs rest (some p) ps
  | a :: rest, sel, ps => parseArgs rest sel (ps.push a)
  | [], sel, ps => (sel, ps)

def main (args : List String) : IO UInt32 := do
  let (sel, paths) := parseArgs args none #[]
  let mut files := #[]
  for a in paths do
    let p : System.FilePath := a
    if ← p.isDir then
      files := files ++ ((← p.walkDir).filter (·.extension == some "ssa"))
    else files := files.push p
  let names := #["check", "checkGo", "DomCert.check", "checkArgShapes", "dom tree", "loopnest",
    "memCheck", "wfDomCheck", "wfCheck", "DomCert.make", "Analysis.dominators", "parentsOK",
    "edgesOK", "rootedOK", "usesOK"]
  let mut t : Array Nat := Array.replicate names.size 0
  let mut n := 0
  let mut bad := 0
  let mut wfBad := 0
  let mut idomDiff := 0
  for path in files do
    let data ← IO.FS.readBinFile path
    let .ok ex := parseExport data | continue
    let typs := ((ex.sections[0]?).bind (·.typs)).getD #[]
    let mut tables : Tables := {}
    for h : si in [0:ex.sections.size] do
      let s := ex.sections[si]
      tables := tables.addAll s.defs
      if let some p := sel then
        if (ex.sections[si + 1]?).map (·.pass.toStringLossy) != some p then continue
      let ce : CheckEnv := { tabs := tables, typs }
      let f := s.func
      n := n + 1
      let ok (r : Except String Unit) : Bool := match r with | .ok () => true | .error _ => false
      let mut ts : Array Nat := #[← IO.monoNanosNow]
      let r0 ← IO.lazyPure fun _ => ok (check ce f)
      ts := ts.push (← IO.monoNanosNow)
      let _ ← IO.lazyPure fun _ => ok (checkGo ce f)
      ts := ts.push (← IO.monoNanosNow)
      let _ ← IO.lazyPure fun _ => ok (DomCert.check f)
      ts := ts.push (← IO.monoNanosNow)
      let _ ← IO.lazyPure fun _ => ok (checkArgShapes ce f)
      ts := ts.push (← IO.monoNanosNow)
      let po ← IO.lazyPure fun _ => Analysis.postorder f
      let tr ← IO.lazyPure fun _ =>
        Analysis.newSparseTree (f.bidLast + 1) f.entry po (Analysis.dominators f)
      ts := ts.push (← IO.monoNanosNow)
      let _ ← IO.lazyPure fun _ => (Analysis.loopnest f po tr).toBool
      ts := ts.push (← IO.monoNanosNow)
      let _ ← IO.lazyPure fun _ => ok (Check.memCheck ce f)
      ts := ts.push (← IO.monoNanosNow)
      let r8 ← IO.lazyPure fun _ => ok (wfDomCheck f)
      ts := ts.push (← IO.monoNanosNow)
      let _ ← IO.lazyPure fun _ => ok (wfCheck f)
      ts := ts.push (← IO.monoNanosNow)
      let c ← IO.lazyPure fun _ => DomCert.make f
      ts := ts.push (← IO.monoNanosNow)
      let goIdom ← IO.lazyPure fun _ => Analysis.dominators f
      ts := ts.push (← IO.monoNanosNow)
      let _ ← IO.lazyPure fun _ => DomCert.parentsOK c f.entry
      ts := ts.push (← IO.monoNanosNow)
      let _ ← IO.lazyPure fun _ => DomCert.edgesOK c f
      ts := ts.push (← IO.monoNanosNow)
      let _ ← IO.lazyPure fun _ => DomCert.rootedOK c f
      ts := ts.push (← IO.monoNanosNow)
      let _ ← IO.lazyPure fun _ => DomCert.usesOK c f
      ts := ts.push (← IO.monoNanosNow)
      if !r0 then bad := bad + 1
      if r0 && !r8 then wfBad := wfBad + 1
      if c.idom != goIdom then idomDiff := idomDiff + 1
      t := (List.range names.size).toArray.map fun k => t[k]! + (ts[k + 1]! - ts[k]!)
  IO.println s!"sections {n}, check fails {bad}, wfDomCheck fails where check passes {wfBad}, certificate tree differs from Analysis.dominators {idomDiff}"
  for h : k in [0:names.size] do
    IO.println s!"{names[k]}: {(t[k]! / 1000000 : Nat)} ms"
  return 0

end GoFVTest.CheckBench

def main (args : List String) : IO UInt32 := GoFVTest.CheckBench.main args

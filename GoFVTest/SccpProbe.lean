import GoFV.SSA.Parse
import GoFV.SSA.Check
import GoFV.Opt.SccpCheck

/-!
# `sccp-probe`: does sccp's checker ever reject?

Runs sccp's analysis and `replaceConst` (insertion order) on the input of every `sccp` section
of the given export files that passes `check`, and counts the inputs it changes and those where
`Sccp.sccpOK` rejects the result (first failing condition; `blocks`: `replaceConst` removed
edges); lists the smallest accepted changed inputs (witness candidates).
-/

open GoFV.SSA GoFV.Rules GoFV.Opt GoFV.Opt.Sccp

namespace GoFVTest.SccpProbe

def why (tabs : Tables) (f g : Func) (C : Array (Option Lat)) (vis : Array Edge) (R : Array Bool) :
    String := Id.run do
  if !KnownBits.blocksOK f g then return "blocks"
  if !RewriteCheck.atomsOK f g then return "atoms"
  if !RewriteCheck.closedOK f then return "closedF"
  if !RewriteCheck.closedOK g then return "closedG"
  if !reachOK tabs f C vis R then return "reach"
  for x in List.range f.valueTab.size do
    if !fixOK tabs f C vis x then
      let d := (f.value? x).map fun v =>
        let args := v.args.toList.map fun a => (a, (cval tabs f C a).map repr)
        s!"{v.op.name} {(cval tabs f C x).map repr} args {args}"
      return s!"fix v{x} {d}"
    if !repOK tabs f g C x then
      return s!"rep v{x} {(f.value? x).map (·.op.name)} → {(g.value? x).map (·.op.name)}"
  return "?"

def main (args : List String) : IO UInt32 := do
  let mut files := #[]
  for a in args do
    let p : System.FilePath := a
    if ← p.isDir then
      files := files ++ ((← p.walkDir).filter (·.extension == some "ssa"))
    else files := files.push p
  let mut inputs := 0
  let mut checked := 0
  let mut changed := 0
  let mut rejected := 0
  let mut errs := 0
  let mut shown := 0
  let mut whys : Std.HashMap String Nat := {}
  let mut cands : Array (Nat × Nat × String) := #[]
  for path in files do
    let .ok data ← (IO.FS.readBinFile path).toBaseIO | continue
    let .ok e := parseExport data | continue
    let typs := ((e.sections[0]?).bind (·.typs)).getD #[]
    let mut tables : Tables := {}
    for h : j in [0:e.sections.size] do
      let s := e.sections[j]
      let prev := tables
      tables := tables.addAll s.defs
      if s.pass.toStringLossy != "sccp" || j == 0 then continue
      let f := e.sections[j-1]!.func
      inputs := inputs + 1
      let env : PassEnv :=
        { passName := "sccp", pkg := e.pkg, funcName := e.name, abi := e.abi,
          nosplit := e.nosplit, pgohot := e.pgohot, config := e.config, typs,
          typeOrder := default, tables := prev }
      if (check { tabs := prev, typs } f).toBool == false then continue
      checked := checked + 1
      let .ok rw := RwEnv.ofPassEnv env | errs := errs + 1; continue
      let .ok a := analyze rw prev f | errs := errs + 1; continue
      let g := replace a a.keys
      if g == f then continue
      changed := changed + 1
      if sccpOK prev f g a.cells a.visited a.visitedBlock then
        let nv := f.blocks.foldl (fun n b => n + ((f.block? b).map (·.values.size)).getD 0) 0
        cands := cands.push (nv, f.blocks.size, s!"{path} {s.index}")
      else
        rejected := rejected + 1
        let w := why prev f g a.cells a.visited a.visitedBlock
        let key := (w.splitOn " ").head!
        whys := whys.insert key (whys.getD key 0 + 1)
        if shown < 40 then
          IO.println s!"REJECT {path} {s.index}: {w}"
          shown := shown + 1
  IO.println s!"sccp inputs {inputs}, passing check {checked}: changes {changed}, rejects {rejected}, errors {errs}"
  IO.println s!"rejections by first failing condition: {whys.toList}"
  IO.println "witness candidates (accepted changed inputs; values, blocks), smallest first:"
  for (nv, nb, s) in (cands.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)).toList.take 15 do
    IO.println s!"  {nv} {nb} {s}"
  return 0

end GoFVTest.SccpProbe

def main (args : List String) : IO UInt32 := GoFVTest.SccpProbe.main args

import GoFV.SSA.Parse
import GoFV.SSA.Check
import GoFV.Opt.KnownBitsCheck

/-!
# `knownbits-probe`: does known bits' checker ever reject?

Runs `knownBitsWith` on every section of the given export files whose input passes `check`
(`--inst`: only the inputs of the `known bits` pass) and counts the sections it changes and
those where `KnownBits.kbOK` rejects the result (first failing condition); lists the smallest
accepted changed inputs (witness candidates).
-/

open GoFV.SSA GoFV.Opt GoFV.Opt.KnownBits

namespace GoFVTest.KnownBitsProbe

/-- The first condition of `kbOK` that fails. -/
def hx (r : BB) : String := s!"({r.1.toHex}, {r.2.toHex})"

def why (tabs : Tables) (f g : Func) (E : Array (Int64 × Int64)) (R : Array Bool) : String := Id.run do
  if !RewriteCheck.atomsOK f g then return "atoms"
  if !RewriteCheck.closedOK f then return "closedF"
  if !RewriteCheck.closedOK g then return "closedG"
  if !blocksOK f g then return "blocks"
  if !reachOK f R then return "reach"
  for x in List.range f.valueTab.size do
    if !fixOK tabs f R E x then
      let d := (f.value? x).map fun v =>
        let args := v.args.toList.map fun a => (a, hx (ent E a), (f.value? a).map (·.op.name))
        s!"{v.op.name} auxInt {v.auxInt} entry {hx (ent E x)} args {args}"
      return s!"fix v{x} {d}"
    if !repOK tabs f g E x then
      return s!"rep v{x} {(f.value? x).map (·.op.name)} → {(g.value? x).map (·.op.name)}"
  return "?"

def main (args : List String) : IO UInt32 := do
  let instOnly := args.head? == some "--inst"
  let args := if instOnly then args.tail else args
  let mut files := #[]
  for a in args do
    let p : System.FilePath := a
    if ← p.isDir then
      files := files ++ ((← p.walkDir).filter (·.extension == some "ssa"))
    else files := files.push p
  let mut secs := 0
  let mut changed := 0
  let mut rejected := 0
  let mut inst := 0
  let mut instChanged := 0
  let mut instRejected := 0
  let mut errs := 0
  let mut shown := 0
  let mut whys : Std.HashMap String Nat := {}
  let mut cands : Array (Nat × Nat × String) := #[]
  for path in files do
    let data ← IO.FS.readBinFile path
    let .ok ex := parseExport data | continue
    let typs := (ex.sections[0]?.bind (·.typs)).getD #[]
    let mut tabs : Tables := {}
    for h : j in [0:ex.sections.size] do
      let s := ex.sections[j]
      tabs := tabs.addAll s.defs
      let f := s.func
      let isInst := (ex.sections[j + 1]?.map (·.pass.toStringLossy)) == some "known bits"
      if instOnly && !isInst then continue
      if (check { tabs, typs } f).toBool == false then continue
      secs := secs + 1
      if isInst then inst := inst + 1
      let order := TypeOrder.ofGroups ex.typeOrder ex.typeCmp
      let .ok (g, E, R) := knownBitsWith tabs order f | errs := errs + 1; continue
      let ok := kbOK tabs f g E R
      if g != f then
        changed := changed + 1
        if isInst then
          instChanged := instChanged + 1
          if ok then
            let nv := f.blocks.foldl (fun n b => n + ((f.block? b).map (·.values.size)).getD 0) 0
            cands := cands.push (nv, f.blocks.size, s!"{path} {s.index}")
      if !ok then
        rejected := rejected + 1
        if isInst then instRejected := instRejected + 1
        let w := why tabs f g E R
        let key := (w.splitOn " ").head!
        whys := whys.insert key (whys.getD key 0 + 1)
        if isInst || shown < 10 then
          IO.println s!"REJECT {path} {s.index} ({s.pass.toStringLossy}) changed={g != f}: {w}"
          shown := shown + 1
  IO.println s!"sections {secs}: known bits changes {changed}, checker rejects {rejected}, errors {errs}"
  IO.println s!"known bits inputs {inst}: changes {instChanged}, rejects {instRejected}"
  IO.println s!"rejections by first failing condition: {whys.toList}"
  IO.println "witness candidates (accepted changed inputs; values, blocks), smallest first:"
  for (nv, nb, s) in (cands.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)).toList.take 15 do
    IO.println s!"  {nv} {nb} {s}"
  return 0

end GoFVTest.KnownBitsProbe

def main (args : List String) : IO UInt32 := GoFVTest.KnownBitsProbe.main args

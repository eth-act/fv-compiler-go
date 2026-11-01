import GoFV.SSA.Parse
import GoFV.SSA.Check
import GoFV.Opt.ZCSE

/-!
# `zcse-probe`: does zcse's checker ever reject?

Runs `zcse` on every section of the given export files whose input passes `check` (not only
the inputs of `zero arg cse`) and counts the sections where `ZCSE.zrel` rejects the result,
with the first failing condition, and the sections zcse changes; separately for the inputs of
the `zero arg cse` instances (a rejection there would cost parity).
-/

open GoFV.SSA GoFV.Opt GoFV.Opt.ZCSE

namespace GoFVTest.ZcseProbe

/-- The first condition of `zrel` that fails. -/
def why (tabs : Tables) (f g : Func) : String := Id.run do
  if DomCert.cfgView g != DomCert.cfgView f then return "cfg"
  if g.ownAux != f.ownAux then return "ownAux"
  if g.valueTab.size != f.valueTab.size then return "size"
  for bid in f.blocks do
    if !blockOK f g bid then return s!"block b{bid}"
  for x in ((g.block? g.entry).map (·.values)).getD #[] do
    if entryArgless g x && !(g.value? x).any (safe tabs (params tabs g)) then
      return s!"unsafe v{x} {((g.value? x).map (·.op.name)).getD "?"}"
    if entryArgless g x && !rootStays f g x then
      return s!"moved-root v{x} {((g.value? x).map (·.op.name)).getD "?"}"
  for x in List.range f.valueTab.size do
    if !valueOK f g x then return s!"value v{x}"
  return "?"

def main (args : List String) : IO UInt32 := do
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
  let mut shown := 0
  let mut whys : Std.HashMap String Nat := {}
  for path in files do
    let data ← IO.FS.readBinFile path
    let .ok ex := parseExport data | continue
    let typs := (ex.sections[0]?.bind (·.typs)).getD #[]
    let mut tabs : Tables := {}
    for h : j in [0:ex.sections.size] do
      let s := ex.sections[j]
      tabs := tabs.addAll s.defs
      let f := s.func
      if (check { tabs, typs } f).toBool == false then continue
      secs := secs + 1
      -- the input of a `zero arg cse` instance is the section before its output
      let isInst := (ex.sections[j + 1]?.map (·.pass.toStringLossy)) == some "zero arg cse"
      if isInst then inst := inst + 1
      let g := zcse f
      if g != f then
        changed := changed + 1
        if isInst then instChanged := instChanged + 1
      if !zrel tabs f g then
        rejected := rejected + 1
        if isInst then instRejected := instRejected + 1
        let w := why tabs f g
        let key := (w.splitOn " ").head!
        whys := whys.insert key (whys.getD key 0 + 1)
        if shown < 20 then
          IO.println s!"REJECT {path} {s.index} ({s.pass.toStringLossy}): {w}"
          shown := shown + 1
  IO.println s!"sections {secs}: zcse changes {changed}, checker rejects {rejected}"
  IO.println s!"zero arg cse inputs {inst}: zcse changes {instChanged}, rejects {instRejected}"
  IO.println s!"rejections by first failing condition: {whys.toList}"
  return 0

end GoFVTest.ZcseProbe

def main (args : List String) : IO UInt32 := GoFVTest.ZcseProbe.main args

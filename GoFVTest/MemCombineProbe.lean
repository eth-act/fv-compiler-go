import GoFV.SSA.Parse
import GoFV.SSA.Check
import GoFV.Opt.MemCombine.Check

/-!
# `memcombine-probe`: what memcombine's checker accepts

Runs `memcombine` (stock), the variant without store-of-load combining and `memcombineChecked`
on the inputs of the `memcombine` sections of the given export files that pass `check`.
Counts the inputs the stock pass changes, those the variant changes, those `mcOK` accepts (the
checked pass then equals the variant), and those whose checked result equals the stock output;
names the first failing condition of each rejection (`--dump`: every rejection) and lists the
smallest accepted inputs (witness candidates).
-/

open GoFV.SSA GoFV.Opt GoFV.Opt.MemCombine GoFV.Opt.MemCombine.Check

namespace GoFVTest.MemCombineProbe

/-- The first condition of `mcOK` that fails. -/
def why (tabs : Tables) (f g : Func) : String := Id.run do
  if !mcAtomsOK f g then return "atoms"
  if !RewriteCheck.closedOK f then return "closedF"
  if !RewriteCheck.closedOK g then return "closedG"
  if !KnownBits.blocksOK f g then return "blocks"
  let R := reachMarks g
  if !reachOK g R then return "reach"
  for x in List.range g.valueTab.size do
    if !valOK tabs f g R x then
      let d := match listedD f x, listedD g x with
        | some u, some w => s!"{u.op.name} → {w.op.name}"
        | none, some w => s!"new {w.op.name}"
        | _, _ => "?"
      let kind := match listedD f x, listedD g x with
        | some u, some w =>
          if RewriteCheck.termOp w.op then
            if rootOK tabs f g x u w then "root?" else "root"
          else if changedStore u w then "store" else "atom"
        | _, _ => "new"
      return s!"{kind} v{x} {d}"
  return "?"

def main (args : List String) : IO UInt32 := do
  let dump := args.head? == some "--dump"
  let args := if dump then args.tail else args
  let mut files := #[]
  for a in args do
    let p : System.FilePath := a
    if ← p.isDir then
      files := files ++ ((← p.walkDir).filter (·.extension == some "ssa"))
    else files := files.push p
  let mut inputs := 0
  let mut checked := 0
  let mut stockCh := 0
  let mut varCh := 0
  let mut accepted := 0
  let mut atStock := 0
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
      if s.pass.toStringLossy != "memcombine" || j == 0 then continue
      let f := e.sections[j-1]!.func
      inputs := inputs + 1
      let env : PassEnv :=
        { passName := "memcombine", pkg := e.pkg, funcName := e.name, abi := e.abi,
          nosplit := e.nosplit, pgohot := e.pgohot, config := e.config, typs,
          typeOrder := TypeOrder.ofGroups e.typeOrder e.typeCmp, tables := prev }
      if (check { tabs := prev, typs } f).toBool == false then continue
      checked := checked + 1
      let .ok (c, u) := memcombineCfg env | errs := errs + 1; continue
      let .ok (gs, _) := memcombine c u prev f | errs := errs + 1; continue
      let .ok (g, tabs) := memcombine { c with loadSource := false } u prev f
        | errs := errs + 1; continue
      if gs != f then stockCh := stockCh + 1
      if g == f then continue
      varCh := varCh + 1
      let .ok o := memcombineChecked env f | errs := errs + 1; continue
      if o.func != f then
        accepted := accepted + 1
        if o.func == gs then atStock := atStock + 1
        let nv := f.blocks.foldl (fun n b => n + ((f.block? b).map (·.values.size)).getD 0) 0
        cands := cands.push (nv, f.blocks.size, s!"{path} {s.index}")
      else
        rejected := rejected + 1
        let w := if tabsAgree prev tabs f then why tabs f g else "tabsAgree"
        let key := (w.splitOn " ").head!
        whys := whys.insert key (whys.getD key 0 + 1)
        if dump || shown < 20 then
          IO.println s!"REJECT {path} {s.index}: {w}"
          shown := shown + 1
  IO.println s!"memcombine inputs {inputs}, passing check {checked}: stock changes {stockCh}, \
    variant changes {varCh}, accepted {accepted} (at stock {atStock}), rejected {rejected}, \
    errors {errs}"
  IO.println s!"rejections by first failing condition: {whys.toList}"
  IO.println "witness candidates (accepted inputs; values, blocks), smallest first:"
  for (nv, nb, s) in (cands.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)).toList.take 20 do
    IO.println s!"  {nv} {nb} {s}"
  return 0

end GoFVTest.MemCombineProbe

def main (args : List String) : IO UInt32 := GoFVTest.MemCombineProbe.main args

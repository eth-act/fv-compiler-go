import GoFV.SSA.Parse
import GoFV.SSA.Check
import GoFV.Opt.MemCombine.Check

open scoped GoFV.SSA.Sem.Fixed

/-!
# `memcombine-probe`: what memcombine's checker accepts

Runs `memcombine` (stock) and `memcombineChecked` on the inputs of the `memcombine` sections of
the given export files that pass `check`. Counts the inputs the stock pass changes and those
whose checked result equals the stock output (accepted); names the first failing condition of
each rejection (`--dump`: every rejection) and lists the smallest accepted inputs that combine
stores (witness candidates).
-/

open GoFV.SSA GoFV.Opt GoFV.Opt.MemCombine GoFV.Opt.MemCombine.Check

namespace GoFVTest.MemCombineProbe

/-- The first condition of `storeOK` that fails. -/
def storeWhy (tabs : Tables) (f g : Func) (M : Array Bool) (x : ID) (u w : Value) : String :=
  Id.run do
  if !(u.op == .Store && w.op == .Store && u.args.size == 3 && w.args.size == 3) then
    return "shape"
  let D := f.value?
  let m0 := w.args[2]!
  let pw := w.args[0]!
  if !M.getD m0 false then return "mem∉M"
  if !M.getD pw false then return "ptr∉M"
  let some S := chainTo D m0 9 x | return "chain"
  if S.length < 2 then return "chain1"
  let some recs := storeRecs tabs D S
    | let bad := S.filter fun s => match D s with
        | some sv => (storedBytes tabs D sv).isNone
        | none => true
      let d := bad.map fun s => match D s with
        | some sv => match D sv.args[1]! with
          | some xv => s!"{xv.op.name}"
          | none => "?"
        | none => "?"
      return s!"bytes {d}"
  let some (_, (b0, i0, o0), _) := recs.find? (·.1 == pw) | return "ptr∉chain"
  if !ptrTyped tabs D b0 then return "base"
  if !recs.all (fun r => r.2.1.1 == b0 && r.2.1.2.1 == i0) then return "bases"
  match Sem.auxTy tabs w.aux, listedD g w.args[1]! with
  | .int ww, some sv =>
    if intW (tabs.ty sv.type) != some ww then return "svType"
    match symOf tabs (listedD g) true false tgtFuel w.args[1]! with
    | some (bt, sg) =>
      if bt.length != ww.bytes then return "btLen"
      if !bt.all (vbWidthOK tabs (listedD g)) then return "btWidth"
      if !leavesIn M bt sg then return "leaves∉M"
      if !tileOK recs o0 ww.bytes bt sg then
        return s!"tile {sv.op.name} {repr bt} vs {repr (recs.map (·.2.2.1))}"
      return "?"
    | _ => return s!"svDesc {sv.op.name}"
  | _, _ => return "wType"

/-- The first condition of `mcOK` that fails. -/
def why (tabs : Tables) (f g : Func) : String := Id.run do
  if !RewriteCheck.atomsXOK f g then return "atoms"
  if !RewriteCheck.closedOK f then return "closedF"
  if !RewriteCheck.closedOK g then return "closedG"
  if !KnownBits.blocksOK f g then return "blocks"
  let R := reachMarks g
  if !reachOK g R then return "reach"
  let M := relMarks f g R
  for x in List.range g.valueTab.size do
    if !valOK tabs f g R M x then
      match listedD f x, listedD g x with
      | some u, some w =>
        if RewriteCheck.termOp w.op then return s!"root v{x} {u.op.name} → {w.op.name}"
        else return s!"store v{x}: {storeWhy tabs f g M x u w}"
      | none, some w => return s!"new v{x} {w.op.name}"
      | _, _ => return "?"
  return "?"

/-- `g` combines stores of `f`: a `Store` of `f` is listed in `g` as another op. -/
def combinesStores (f g : Func) : Bool :=
  f.blocks.any fun b => ((f.block? b).map fun fb => fb.values.any fun x =>
    match f.value? x, listedD g x with
    | some u, some w => u.op == .Store && w.op != .Store
    | _, _ => false).getD false

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
  let mut stockSt := 0
  let mut accepted := 0
  let mut acceptedSt := 0
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
      let .ok (gs, ts) := memcombine c u prev f | errs := errs + 1; continue
      if gs == f then continue
      stockCh := stockCh + 1
      let st := combinesStores f gs
      if st then stockSt := stockSt + 1
      let .ok o := memcombineChecked env f | errs := errs + 1; continue
      if o.func == gs then
        accepted := accepted + 1
        if st then
          acceptedSt := acceptedSt + 1
          let nv := f.blocks.foldl (fun n b => n + ((f.block? b).map (·.values.size)).getD 0) 0
          cands := cands.push (nv, f.blocks.size, s!"{path} {s.index}")
      else
        rejected := rejected + 1
        let w := if !tabsAgree prev ts f then "tabsAgree" else why ts f gs
        let key := String.intercalate " " ((w.splitOn " ").take 1 ++
          (if w.startsWith "store" then ((w.splitOn ": ").drop 1).take 1 |>.map
            (fun r => (r.splitOn " ").head!) else []))
        whys := whys.insert key (whys.getD key 0 + 1)
        if dump || shown < 20 then
          IO.println s!"REJECT {path} {s.index}: {w}"
          shown := shown + 1
  IO.println s!"memcombine inputs {inputs}, passing check {checked}: stock changes {stockCh} \
    (combining stores {stockSt}), accepted {accepted} (combining stores {acceptedSt}), \
    rejected {rejected}, errors {errs}"
  IO.println s!"rejections by first failing condition: {whys.toList}"
  IO.println "witness candidates (accepted inputs combining stores; values, blocks), smallest first:"
  for (nv, nb, s) in (cands.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)).toList.take 20 do
    IO.println s!"  {nv} {nb} {s}"
  return 0

end GoFVTest.MemCombineProbe

def main (args : List String) : IO UInt32 := GoFVTest.MemCombineProbe.main args

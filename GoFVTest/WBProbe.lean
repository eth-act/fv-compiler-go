import GoFV.SSA.Parse
import GoFV.SSA.Check
import GoFV.Opt.WriteBarrierCheck

/-!
# `wb-probe`: what writebarrier's checker accepts (issue #36)

Runs `writebarrier` (stock) and `writebarrierChecked` on the inputs of the `writebarrier`
sections of the given export files that pass `check`. Counts the inputs the pass changes, those
with `wbZero`/`wbMove` calls, those that store to
`runtime.writeBarrier` directly, the accepted ones and whether they equal the stock output,
names the first failing condition of each rejection and lists the smallest accepted inputs
(witness candidates).
-/

open GoFV.SSA GoFV.Opt GoFV.Opt.WBCheck

namespace GoFVTest.WBProbe

/-- `g` calls `runtime.wbZero`/`runtime.wbMove`. -/
def hasWbCall (tabs : Tables) (g : Func) : Bool :=
  g.blocks.any fun b => (vals g b).any fun x => match g.value? x with
    | some v => v.op == .StaticCall &&
        (match v.aux.bind tabs.callee? with
          | some n => n == "runtime.wbZero" || n == "runtime.wbMove"
          | none => false)
    | none => false

/-- `f` writes through `Addr {runtime.writeBarrier}` directly. -/
def storesFlag (tabs : Tables) (f : Func) : Bool :=
  f.blocks.any fun b => (vals f b).any fun x => match f.value? x with
    | some v =>
      (Sem.isRoot v.op && !v.op.call) && v.args.any fun a => match f.value? a with
        | some w => w.op == .Addr && symName? tabs w.aux == some "runtime.writeBarrier" &&
            v.op != .NilCheck
        | none => false
    | none => false

/-- The first condition of `wbOK` that fails. -/
def why (tabs : Tables) (f g : Func) : String := Id.run do
  if !(g.entry == f.entry && g.ownAux == f.ownAux) then return "entry"
  if !memTyOK tabs f then
    let bad := f.blocks.toList.flatMap fun b => (vals f b).toList.filterMap fun x =>
      match f.value? x with
      | some v => if v.op != .WB && v.op != .WBend && v.op != .StoreWB && v.op != .MoveWB &&
          v.op != .ZeroWB && (memFree (tabs.ty v.type) || memOpOK v.op) then none
          else some v.op.name
      | none => some "?"
    return s!"memTy {bad.eraseDups}"
  let some c := ctxOf tabs f g | Id.run do
    for b in f.blocks do
      if (chainRuns? f g b).isNone then
        let ch := chainOf f g (g.blocks.size + 1) b
        return s!"lazy chain b{b} {ch.isSome} {ch.map fun (ss, _) => ss.map (runOf? f g · |>.isSome)}"
    let splits := f.blocks.toList.flatMap fun b =>
      ((chainRuns? f g b).map fun (rs, _) => rs.map (·.sp)).getD []
    let ws := splits.map fun s => (s.wbaddr, s.const0, (g.value? s.wbaddr).map (·.op.name),
      (g.value? s.const0).map (·.op.name), (vals g g.entry).contains s.wbaddr,
      (vals g g.entry).contains s.const0)
    return s!"lazy fields {ws.eraseDups}"
  for b in f.blocks do
    if c.blockOK b then continue
    let some B := f.block? b | return s!"block b{b}"
    let some (rs, _) := chainRuns? f g b | return s!"chain b{b}"
    let segs := segsOf b rs
    if !(segs ++ rs.map (·.sp.t)).Nodup then return s!"nodup b{b}"
    for (r, j) in rs.zipIdx do
      if !c.runOK b B segs rs j r then
        let bad := ((g.block? r.sp.t).map (·.values.toList)).getD [] |>.filter
          (!c.roleOK b B segs rs true j ·)
        let bad := bad.map fun x => (x, (g.value? x).map (·.op.name), repr (c.roleOf rs x))
        return s!"run b{b} j{j} then-bad={bad}"
    for x in B.values do
      if !(if c.K.getD x false then segs.any fun s => (vals g s).contains x
          else rs.any (fun r => r.src.contains x) || rs.any (fun r => r.nc == some x)) then
        return s!"unclassified b{b} v{x} {(f.getV x).op.name} kept={c.K.getD x false}"
    for (s, j) in segs.zipIdx do
      for x in vals g s do
        if !c.roleOK b B segs rs false j x then
          return s!"role b{b} seg{j} v{x} {(g.getV x).op.name} {repr (c.roleOf rs x)}"
    if !c.npOK B rs segs then return s!"np b{b}"
    return s!"ends b{b}"
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
  let mut changed := 0
  let mut wbCalls := 0
  let mut flagStores := 0
  let mut accepted := 0
  let mut atStock := 0
  let mut rejected := 0
  let mut errs := 0
  let mut shown := 0
  let mut whys : Std.HashMap String Nat := {}
  let mut cands : Array (Nat × Nat × String) := #[]
  let mut callCands : Array (Nat × Nat × String) := #[]
  for path in files do
    let .ok data ← (IO.FS.readBinFile path).toBaseIO | continue
    let .ok e := parseExport data | continue
    let typs := ((e.sections[0]?).bind (·.typs)).getD #[]
    let mut tables : Tables := {}
    for h : j in [0:e.sections.size] do
      let s := e.sections[j]
      let prev := tables
      tables := tables.addAll s.defs
      if s.pass.toStringLossy != "writebarrier" || j == 0 then continue
      let f := e.sections[j-1]!.func
      inputs := inputs + 1
      let env : PassEnv :=
        { passName := "writebarrier", pkg := e.pkg, funcName := e.name, abi := e.abi,
          nosplit := e.nosplit, pgohot := e.pgohot, config := e.config, typs,
          typeOrder := TypeOrder.ofGroups e.typeOrder e.typeCmp, tables := prev,
          frontend := e.frontendTables }
      if (check { tabs := prev, typs } f).toBool == false then continue
      checked := checked + 1
      if storesFlag prev f then flagStores := flagStores + 1
      let .ok out := writebarrier env f | errs := errs + 1; continue
      if out.func == f then continue
      changed := changed + 1
      let calls := hasWbCall out.tables out.func
      if calls then wbCalls := wbCalls + 1
      match writebarrierChecked env f with
      | .ok o =>
        accepted := accepted + 1
        if o.func == out.func then atStock := atStock + 1
        let nv := f.blocks.foldl (fun n b => n + (vals f b).size) 0
        cands := cands.push (nv, f.blocks.size, s!"{path} {s.index}")
        if calls then callCands := callCands.push (nv, f.blocks.size, s!"{path} {s.index}")
      | .error _ =>
        rejected := rejected + 1
        let w := if tabsAgree prev out.tables f then why out.tables f out.func else "tabsAgree"
        let key := (w.splitOn " ").head!
        whys := whys.insert key (whys.getD key 0 + 1)
        if dump || shown < 20 then
          IO.println s!"REJECT {path} {s.index} {e.pkg}.{e.name}: {w}"
          shown := shown + 1
  IO.println s!"writebarrier inputs {inputs}, passing check {checked}: changed {changed} \
    (with wbZero/wbMove calls {wbCalls}), accepted {accepted} (at stock {atStock}), \
    rejected {rejected}, errors {errs}; storing to runtime.writeBarrier {flagStores}"
  IO.println s!"rejections by first failing condition: {whys.toList}"
  let smallest (a : Array (Nat × Nat × String)) :=
    (a.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)).toList.take 20
  IO.println "witness candidates (accepted inputs; values, blocks), smallest first:"
  for (nv, nb, s) in smallest cands do
    IO.println s!"  {nv} {nb} {s}"
  IO.println "with wbZero/wbMove calls:"
  for (nv, nb, s) in smallest callCands do
    IO.println s!"  {nv} {nb} {s}"
  return 0

end GoFVTest.WBProbe

def main (args : List String) : IO UInt32 := GoFVTest.WBProbe.main args

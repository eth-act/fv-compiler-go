import GoFV.SSA.Parse
import GoFV.SSA.Check
import GoFV.Opt.WriteBarrierCheck

/-!
# `wb-probe`: what writebarrier's checker accepts (issue #36)

Runs `writebarrier` (stock) and `writebarrierChecked` on the inputs of the `writebarrier`
sections of the given export files that pass `check`. Counts the inputs the pass changes, those
with `wbZero`/`wbMove` calls (outside the checker's scope), those that store to
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
  if !memTyOK tabs f then return "memTy"
  let K := keptMarks f g
  let mut Lst := Array.replicate g.valueTab.size false
  let mut lazy : Option (ID × ID) := none
  for b in f.blocks do
    let some (splits, _) := chainOf f g (g.blocks.size + 1) b | return s!"chain b{b}"
    for s in splits do
      lazy := some (s.wbaddr, s.const0)
      match runOf? f g s with
      | some r => Lst := Lst.set! r.last true
      | none => return s!"run b{b}"
  let (wbaddr, const0) := lazy.getD (0, 0)
  let c : Ctx := { tabs, f, g, K, Lst, wbaddr, const0 }
  for b in f.blocks do
    if c.blockOK b then continue
    let some (splits, _) := chainOf f g (g.blocks.size + 1) b | return "chain"
    let some runs := splits.mapM (runOf? f g) | return "run"
    let segs := b :: splits.map (·.e)
    for (r, i) in runs.zipIdx do
      if !c.flagOK r.sp then return s!"flag b{b}"
      if !c.endOK r then return s!"end b{b}"
      if !c.thenOK b segs i r then return s!"then b{b}"
      if let some n := r.nc then
        if !(K.getD n false) then
          if !(vals f b).contains n then return s!"ncOut b{b}"
      if !r.src.all (fun x => (vals f b).contains x && !K.getD x false) then return s!"src b{b}"
    if !c.npOK b runs segs then
      let src := npSeq f b
      let ks := segs.map fun s => (npSeq g s, c.keptNP s)
      let rs := runs.map fun r => (r.nc, r.src, r.tgt, r.last)
      return s!"np b{b} src={src} segs={segs} ks={ks} runs={rs}"
    let B := f.getB b
    for x in B.values do
      if !((K.getD x false && (segs.filter fun s => (vals g s).contains x).length == 1) ||
          runs.any (fun r => r.src.contains x) || runs.any (fun r => r.nc == some x)) then
        return s!"values b{b} unclassified v{x} {(f.getV x).op.name} kept={K.getD x false} \
          in={segs.filter fun s => (vals g s).contains x} g={(g.value? x).map (·.op.name)}"
    for (s, j) in segs.zipIdx do
      for x in vals g s do
        if K.getD x false then
          let u := f.getV x
          let bad := u.args.filter fun a => !c.availIn b segs j a
          if !(B.values.contains x) || (u.op == .Phi && j != 0) || (u.op != .Phi && !bad.isEmpty) then
            return s!"values b{b} kept v{x} {u.op.name} seg {j} bad args {bad} \
              held={bad.map c.held}"
        else if !c.newOK b runs j x then
          return s!"values b{b} new v{x} {(g.getV x).op.name} seg {j}"
    let some (_, last) := chainOf f g (g.blocks.size + 1) b | return "chain"
    let L := g.getB last
    let C0 := g.getB b
    return s!"values b{b} ? c0pre={C0.preds == B.preds} kind={L.kind == B.kind} \
      ctl={L.controls == B.controls} succ={L.succs == B.succs} held={B.controls.all c.held} \
      ids={C0.id == b && L.id == last}"
  if lazy.isSome then return "lazy"
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
      if hasWbCall out.tables out.func then
        wbCalls := wbCalls + 1
        continue
      match writebarrierChecked env f with
      | .ok o =>
        accepted := accepted + 1
        if o.func == out.func then atStock := atStock + 1
        let nv := f.blocks.foldl (fun n b => n + (vals f b).size) 0
        cands := cands.push (nv, f.blocks.size, s!"{path} {s.index}")
      | .error _ =>
        rejected := rejected + 1
        let w := if tabsAgree prev out.tables f then why out.tables f out.func else "tabsAgree"
        let key := (w.splitOn " ").head!
        whys := whys.insert key (whys.getD key 0 + 1)
        if dump || shown < 20 then
          IO.println s!"REJECT {path} {s.index} {e.pkg}.{e.name}: {w}"
          shown := shown + 1
  IO.println s!"writebarrier inputs {inputs}, passing check {checked}: changed {changed}, \
    with wbZero/wbMove calls {wbCalls}, others accepted {accepted} (at stock {atStock}), \
    rejected {rejected}, errors {errs}; storing to runtime.writeBarrier {flagStores}"
  IO.println s!"rejections by first failing condition: {whys.toList}"
  IO.println "witness candidates (accepted inputs; values, blocks), smallest first:"
  for (nv, nb, s) in (cands.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1 < b.2.1)).toList.take 20 do
    IO.println s!"  {nv} {nb} {s}"
  return 0

end GoFVTest.WBProbe

def main (args : List String) : IO UInt32 := GoFVTest.WBProbe.main args

import GoFV.SSA.Parse
import GoFV.Opt.ShortCircuit
import GoFV.Opt.ZCSE

/-!
# `lake exe shortcirc-probe <dir>...`: what short circuit rewrites on the corpus (issue #16)

For every `short circuit` section (input: the previous section), replays the pass with an
instrumented copy of `constPhiArgs` and `shortcircuitBlock` (each result is compared with the
pass's own) and counts:

- `constPhiArgs`: phi arguments replaced (edge 0 / edge 1), constants created / reused;
- `shortcircuitBlock`: rewrites by `shortcircuitPhiPlan` shape (none: no other phi), the length
  of the control chain, negations, `fixPhi` calls, moved phis (`afterMove`: `phielimValue` or
  `resetValue .Invalid`), the final resets of unused values of `b`, `b` becoming `Invalid`, the
  control phi becoming a `Copy`;
- whether the values left in `b` are read outside `b`'s non-`Phi`s and controls in the result
  (`bvalOut`), and the cost of a whole-function scan per rewrite (values summed over rewrites).
-/

open GoFV.SSA GoFV.Opt GoFV.Opt.Fuse GoFV.Opt.ShortCircuit

namespace GoFVTest.ShortCircProbe
structure Counts where
  fns : Nat := 0
  selfRef : Nat := 0
  argInRegion : Nat := 0
  cpaTypeNe : Nat := 0
  cpaNotBoolShape : Nat := 0
  cpaNotEntry : Nat := 0
  cpaGrow : Nat := 0
  cpaZrelRej : Nat := 0
  cpaArgs0 : Nat := 0
  cpaArgs1 : Nat := 0
  cpaNew : Nat := 0
  cpaReused : Nat := 0
  cpaFns : Nat := 0
  sc : Nat := 0
  planNone : Nat := 0
  planMerge : Nat := 0
  planUIntoT : Nat := 0
  planTIntoU : Nat := 0
  planTExits : Nat := 0
  planUExits : Nat := 0
  nOther1 : Nat := 0
  nOther2 : Nat := 0
  nOther3 : Nat := 0
  chain1 : Nat := 0
  chain2 : Nat := 0
  chain3 : Nat := 0
  swaps : Nat := 0
  fixPhis : Nat := 0
  fixPhiUnused : Nat := 0
  moved : Nat := 0
  movedElim : Nat := 0
  movedInvalid : Nat := 0
  afterMoveSetArg : Nat := 0
  finalReset : Nat := 0
  bInvalid : Nat := 0
  ctlCopy : Nat := 0
  tPhis : Nat := 0
  bvalOut : Nat := 0
  scanCost : Nat := 0
  maxPerFn : Nat := 0
  mismatch : Nat := 0
  /-- checker accepts / rejects by plan shape: none, merge, uIntoT, tIntoU, tExits, uExits -/
  acc : Array Nat := #[0, 0, 0, 0, 0, 0]
  rej : Array Nat := #[0, 0, 0, 0, 0, 0]
  /-- rejections whose only failing block check is the schedule order (weak order holds) -/
  schedWeak : Nat := 0
  /-- checked blocks summed over rewrites -/
  kBlocks : Nat := 0
  grows : Nat := 0
  growsB : Nat := 0
  rejShown : Array String := #[]
  shown : Array String := #[]
  deriving Inhabited

def show1 (k : Counts) (s : String) : Counts :=
  if k.shown.size < 20 then { k with shown := k.shown.push s } else k

/-! ## Instrumented copies -/

def afterMoveI (f : Func) (phi : ID) (k : Counts) : Func × Counts := Id.run do
  let mut f := f
  let mut k := k
  for v in (f.getB (f.getV phi).block).values do
    let x := f.getV v
    if x.op != .Phi || v == phi then continue
    for j in [0:x.args.size] do
      if (f.getV v).args[j]! == phi then
        f := f.setArg v j (f.getV phi).args[j]!
        k := { k with afterMoveSetArg := k.afterMoveSetArg + 1 }
  if (f.getV phi).uses != 0 then return ((f.phielimValue phi).1, { k with movedElim := k.movedElim + 1 })
  return (f.resetValue phi .Invalid, { k with movedInvalid := k.movedInvalid + 1 })

def fixOtherPhisI (plan : Plan) (cidx : Nat) (b ctl : ID) : Nat → Func → Nat → Counts →
    Func × Counts
  | 0, f, _, k => (f, k)
  | fuel + 1, f, i, k =>
    let vals := (f.getB b).values
    if h : i < vals.size then
      let phi := vals[i]
      let x := f.getV phi
      if x.uses == 0 || phi == ctl || x.op != .Phi then
        let k := if x.op == .Phi && phi != ctl then { k with fixPhiUnused := k.fixPhiUnused + 1 } else k
        fixOtherPhisI plan cidx b ctl fuel f (i + 1) k
      else
        let f := fixPhi plan cidx f phi i
        let k := { k with fixPhis := k.fixPhis + 1 }
        if (f.getV phi).block == b then fixOtherPhisI plan cidx b ctl fuel f (i + 1) k
        else
          let (f, k) := afterMoveI f phi { k with moved := k.moved + 1 }
          fixOtherPhisI plan cidx b ctl fuel f i k
    else (f, k)

/-- `shortcircuitBlock` with counters; `none` if it does not fire. -/
def scBlockI (f : Func) (b : ID) (k : Counts) : Option (Func × Counts × List ID) := Id.run do
  let bb := f.getB b
  if bb.kind != .If then return none
  let (ctl, nval, swap) := unwrapControl f b (bb.values.size + 1) bb.controls[0]! 1 0
  let cx := f.getV ctl
  if cx.op != .Phi || cx.block != b || cx.uses != 1 then return none
  let isPhi (w : ID) : Bool := (f.getV w).op == .Phi
  let nOtherPhi := bb.values.countP fun w => isPhi w && w != ctl
  if nOtherPhi > 0 && bb.preds.size != 2 then return none
  if bb.values.size != nval + nOtherPhi then return none
  if nOtherPhi > 0 then
    for v in bb.values do
      if !isPhi v then continue
      for a in (f.getV v).args do
        if a != v && isPhi a && bb.values.contains a then return none
  let some cidx := cx.args.findIdx? fun a => (f.getV a).op == .ConstBool | return none
  let pe := bb.preds[cidx]!
  let p := pe.b
  let pi := pe.i
  let ti := (1 ^^^ (f.getV cx.args[cidx]!).auxInt ^^^ swap.toInt64).toInt.toNat
  let te := bb.succs[ti]!
  let t := te.b
  if p == b || t == b then return none
  let mut plan : Option Plan := none
  if nOtherPhi > 0 then
    match phiPlan f b ti with
    | some pl => plan := some pl
    | none => return none
  let mut k := k
  if let some pl := plan then
    let region : Array ID := match pl with
      | .merge t m vis => #[t, m] ++ vis
      | .uIntoT t vis => #[t] ++ vis
      | .tIntoU t u => #[t, u]
      | .tExits t u => #[t, u]
      | .uExits t u => #[t, u]
    let region := region.push bb.succs[1 - ti]!.b
    for v in bb.values do
      let x := f.getV v
      if x.op != .Phi || v == ctl then continue
      if x.args.contains v then k := { k with selfRef := k.selfRef + 1 }
      if x.args.any fun a => region.contains (f.getV a).block || (f.getV a).block == b then
        k := { k with argInRegion := k.argInRegion + 1 }
        let kind := match pl with
          | .merge .. => "merge" | .uIntoT .. => "uIntoT" | .tIntoU .. => "tIntoU"
          | .tExits .. => "tExits" | .uExits .. => "uExits"
        let roles := (List.range x.args.size).map fun j =>
          let a := x.args[j]!
          let ab := (f.getV a).block
          let role := if ab == b then "b" else if ab == bb.succs[ti]!.b then "t"
            else if ab == bb.succs[1 - ti]!.b then "u" else if region.contains ab then "R" else "-"
          s!"{if j == cidx then "P" else "Q"}:v{a}@b{ab}({role},{(f.getV a).op.name})"
        k := show1 k s!"b{b} {kind}: phi v{v} args {roles}"
  k := { k with sc := k.sc + 1 }
  k := match plan with
    | none => { k with planNone := k.planNone + 1 }
    | some (.merge ..) => { k with planMerge := k.planMerge + 1 }
    | some (.uIntoT ..) => { k with planUIntoT := k.planUIntoT + 1 }
    | some (.tIntoU ..) => { k with planTIntoU := k.planTIntoU + 1 }
    | some (.tExits ..) => { k with planTExits := k.planTExits + 1 }
    | some (.uExits ..) => { k with planUExits := k.planUExits + 1 }
  k := if nOtherPhi == 0 then k else if nOtherPhi == 1 then { k with nOther1 := k.nOther1 + 1 }
    else if nOtherPhi == 2 then { k with nOther2 := k.nOther2 + 1 } else { k with nOther3 := k.nOther3 + 1 }
  k := if nval == 1 then { k with chain1 := k.chain1 + 1 } else if nval == 2 then
    { k with chain2 := k.chain2 + 1 } else { k with chain3 := k.chain3 + 1 }
  if swap == 1 then k := { k with swaps := k.swaps + 1 }
  let mut f := (f.removePred b cidx).removePhiArg b ctl cidx
  let tn := (f.getB t).preds.size
  f := f.modB p fun x => { x with succs := x.succs.set! pi ⟨t, tn⟩ }
  f := f.modB t fun x => { x with preds := x.preds.push ⟨p, pi⟩ }
  for v in (f.getB t).values do
    let x := f.getV v
    if x.op != .Phi then continue
    k := { k with tPhis := k.tPhis + 1 }
    f := f.addArg v x.args[te.i]!
  if let some pl := plan then
    let n := (f.getB b).values.size
    let (f', k') := fixOtherPhisI pl cidx b ctl (2 * n + 2) f 0 k
    f := f'; k := k'
    for v in (f.getB b).values do
      if (f.getV v).uses == 0 then
        f := f.resetValue v .Invalid
        k := { k with finalReset := k.finalReset + 1 }
  if (f.getB b).preds.size == 0 then
    f := f.modB b fun x => { x with kind := .Invalid }
    k := { k with bInvalid := k.bInvalid + 1 }
  let (f2, ch) := f.phielimValue ctl
  if ch then k := { k with ctlCopy := k.ctlCopy + 1 }
  return some (f2, k, (bb.values.toList))

/-- Values of block `b` of `g` (still listed there, not `Invalid`) read outside `b`'s non-`Phi`s
and controls. -/
def bvalOutside (g : Func) (b : ID) : Bool := Id.run do
  let bv := (g.getB b).values.filter fun v => (g.getV v).op != .Invalid
  if bv.isEmpty then return false
  for y in g.blocks do
    let Y := g.getB y
    for v in Y.values do
      let x := g.getV v
      if y == b && x.op != .Phi then continue
      if x.args.any bv.contains then return true
    if y != b && Y.controls.any bv.contains then return true
  return false

def constPhiArgsI (tabs : Tables) (isBool : TypeRef → Bool) (sameType : TypeRef → TypeRef → Bool)
    (boolT : TypeRef) (f : Func) (k : Counts) : Func × Counts := Id.run do
  let mut f := f
  let mut k := k
  let mut ct : Option ID := none
  let mut cf : Option ID := none
  let mut any := false
  for b in f.blocks do
    for v in (f.getB b).values do
      let x := f.getV v
      if x.op != .Phi || !isBool x.type then continue
      for i in [0:x.args.size] do
        let a := (f.getV v).args[i]!
        let e := (f.getB b).preds[i]!
        let pb := f.getB e.b
        if pb.kind != .If || pb.controls[0]! != a then continue
        any := true
        let isNew (f f' : Func) := f'.vidLast != f.vidLast || f'.freeValues.length != f.freeValues.length
        if e.i == 0 then
          k := { k with cpaArgs0 := k.cpaArgs0 + 1 }
          if ct.isNone then
            let (f', c) := f.constBool sameType boolT true
            k := if isNew f f' then { k with cpaNew := k.cpaNew + 1 } else
              { k with cpaReused := k.cpaReused + 1 }
            f := f'; ct := some c
        else
          k := { k with cpaArgs1 := k.cpaArgs1 + 1 }
          if cf.isNone then
            let (f', c) := f.constBool sameType boolT false
            k := if isNew f f' then { k with cpaNew := k.cpaNew + 1 } else
              { k with cpaReused := k.cpaReused + 1 }
            f := f'; cf := some c
        let c := (if e.i == 0 then ct else cf).get!
        if (f.getV c).type != x.type then k := { k with cpaTypeNe := k.cpaTypeNe + 1 }
        if (match tabs.ty (f.getV c).type with | .bool => false | _ => true) then
          k := { k with cpaNotBoolShape := k.cpaNotBoolShape + 1 }
        if (f.getV c).block != f.entry || !(f.getB f.entry).values.contains c then
          k := { k with cpaNotEntry := k.cpaNotEntry + 1 }
        f := f.setArg v i c
  if any then k := { k with cpaFns := k.cpaFns + 1 }
  return (f, k)

def nvals (f : Func) : Nat := f.blocks.foldl (fun n b => n + (f.getB b).values.size) 0

def planIdx : Option Plan → Nat
  | none => 0
  | some (.merge ..) => 1
  | some (.uIntoT ..) => 2
  | some (.tIntoU ..) => 3
  | some (.tExits ..) => 4
  | some (.uExits ..) => 5

/-- The weak schedule order: every source non-phi the target lists before a source root, the
source lists before it. -/
def schedWeakOK (f g : Func) (fB gB : Block) : Bool :=
  match Sem.schedule f fB, Sem.schedule g gB with
  | some oS, some oT =>
    let nS := Info.nodesOf f fB
    let pos (x : ID) : Nat := (oS.toList.idxOf? x).getD 0
    let src := oT.toList.filter (nS.contains ·)
    (List.range src.length).all fun j =>
      let r := src[j]!
      Sem.prio (f.getV r).op == 0 || (src.take j).all fun y => pos y < pos r
  | _, _ => false

/-- Which parts of `scOK` fail. -/
def diag (tabs : Tables) (f g : Func) (s : Site) : List String := Id.run do
  let I := infoOf tabs f g s
  let T := I.factTab f g
  let mut out : List String := [s!"b{s.b} p{s.p} t{I.t} region {I.region} K {I.K} T {T.toList.map fun (B, pin, o) => (B, pin, o)} dflt {I.dflt}"]
  for B in I.region do
    let gB := g.getB B
    let phis := gB.values.toList.filter (isPhiIn g ·) |>.map fun z => (z, (g.getV z).args.toList)
    out := s!"R b{B}: gpreds {gB.preds.toList.map (·.b)} has54 {gB.values.contains 54} phis {phis} succs {gB.succs.toList.map (·.b)}" :: out
  if !I.preOK f then out := "preOK" :: out
  if !wfDomOK g then out := "wfDomOK" :: out
  if !(g.blocks == f.blocks && g.entry == f.entry && g.ownAux == f.ownAux &&
      g.valueTab.size == f.valueTab.size && g.blockTab.size == f.blockTab.size) then out := "blocks/entry/sizes" :: out
  if !I.redirOK f g then out := "redirOK" :: out
  if !I.regionOK g then out := "regionOK" :: out
  if !I.frameOK f g then out := "frameOK" :: out
  if !I.exitOK g T then out := "exitOK" :: out
  if !I.scanOK g then out := "scanOK" :: out
  for B in I.K do
    if I.blockOK f g T B then continue
    match f.block? B, g.block? B with
    | some fB, some gB =>
      let (pin, out') := I.factsOf T B
      let inR := I.region.contains B
      let mut parts : List String := []
      if !(gB.kind == fB.kind && gB.controls.size == fB.controls.size) then parts := "kind/ctrl" :: parts
      if !(inR || B == I.s.b || (pin == I.dflt && out' == I.dflt)) then parts := "dflt" :: parts
      if !I.newOK f fB gB then parts := "new" :: parts
      if !I.nodesOK f g fB gB pin out' (inR || B == I.s.b) then
        let nT := Info.nodesOf g gB
        let nS := Info.nodesOf f fB
        let home := I.home f g fB out'
        let bad1 := nS.toList.filter fun y => !(nT.contains y && home y == some y)
        let bad2 := nT.toList.filter fun x => !I.nodeOK f g fB gB pin out' (inR || B == I.s.b) x
        let showV (h : Func) (x : ID) : String :=
          let v := h.getV x
          s!"v{x}={v.op.name}{v.args.toList}@b{v.block}"
        parts := s!"nodes(srcMissing {bad1.map (showV f)}, bad {bad2.map fun x => (showV g x, showV f x, home x)}, pin {pin}, out {out'}, vs {I.vs}, bvals {I.bvals})" :: parts
      if !Info.schedOK f g fB gB then
        parts := (if schedWeakOK f g fB gB then "sched(weak ok)" else "sched") :: parts
      if !I.outOK f g fB gB pin out' then parts := "out" :: parts
      if !I.succOK fB gB B then parts := "succ" :: parts
      if !(gB.controls.zip fB.controls).all (fun (c', c) => I.argRel f g fB gB pin out' c' c) then parts := "ctrlRel" :: parts
      for iT in List.range (max 1 gB.preds.size) do
        let (iS, E) := I.edgeIn f T B gB iT
        if !(I.redir B iT || fB.preds[iS]? == gB.preds[iT]?) then parts := s!"pred{iT}" :: parts
        if !I.phisOK f g fB gB pin iT iS E inR then parts := s!"phis{iT}(pin {pin} E {E})" :: parts
      let role := if B == I.s.b then "b" else if B == I.t then "t" else if B == I.s.p then "p"
        else if inR then "R" else "K"
      out := s!"block b{B}({role}) gpreds {gB.preds.toList.map (·.b)} fpreds {fB.preds.toList.map (·.b)}: {parts}" :: out
    | _, _ => out := s!"block b{B}: missing" :: out
  return out

def step (tabs : Tables) (name : String) (f : Func) (b : ID) (k : Counts) : Except String (Func × Bool × Counts) := do
  let (f, c1) ← Fuse.Plain.fuseBlockPlainChecked f b
  let (g, c2) := shortcircuitBlock f b
  let mut k := k
  if let some s := siteOf f b then
    let i := planIdx s.plan
    let g1 := applySite f s
    k := { k with kBlocks := k.kBlocks + (infoOf tabs f g1 s).K.size }
    if g1.valueTab.size != f.valueTab.size then k := { k with grows := k.grows + 1 }
    if g1.blockTab.size != f.blockTab.size then k := { k with growsB := k.growsB + 1 }
    if scOK tabs f g1 s then k := { k with acc := k.acc.modify i (· + 1) }
    else
      let d := diag tabs f g1 s
      k := { k with rej := k.rej.modify i (· + 1) }
      if d.all (fun x => (x.splitOn "sched(weak ok)").length > 1 || (x.splitOn ":").length == 1 && false) then
        k := { k with schedWeak := k.schedWeak + 1 }
      if k.rejShown.size < 30 then
        k := { k with rejShown := k.rejShown.push s!"{name} b{b} plan {i}: {d}" }
  match scBlockI f b k with
  | none => if c2 then k := show1 { k with mismatch := k.mismatch + 1 } s!"{name} b{b}: fired, copy did not"
  | some (g', k', _) =>
    k := k'
    if !c2 || g' != g then k := show1 { k with mismatch := k.mismatch + 1 } s!"{name} b{b}: copy differs"
    k := { k with scanCost := k.scanCost + nvals g }
    if bvalOutside g b then k := show1 { k with bvalOut := k.bvalOut + 1 } s!"{name} b{b}: b value read outside"
  pure (g, c2 || c1, k)

def sweep (tabs : Tables) (name : String) (f : Func) (k : Counts) : Except String (Func × Bool × Counts) := do
  let blocks := f.blocks
  let mut f := f
  let mut ch := false
  let mut k := k
  for i in [0:blocks.size] do
    let (f', c, k') ← step tabs name f blocks[blocks.size - 1 - i]! k
    f := f'; k := k'; ch := c || ch
  return (f, ch, k)

def loop (tabs : Tables) (name : String) : Nat → Func → Counts → Except String (Func × Counts)
  | 0, _, _ => throw "round bound"
  | n + 1, f, k => do
    let (f, ch, k) ← sweep tabs name f k
    if ch then loop tabs name n f.invalidateCFG k else return (f, k)

def main (args : List String) : IO UInt32 := do
  let mut files := #[]
  for a in args do
    let p : System.FilePath := a
    if ← p.isDir then
      files := files ++ ((← p.walkDir).filter (·.extension == some "ssa"))
    else files := files.push p
  let mut k : Counts := {}
  let mut errs := 0
  for path in files do
    let .ok data ← (IO.FS.readBinFile path).toBaseIO | continue
    let .ok e := parseExport data | continue
    let typs := ((e.sections[0]?).bind (·.typs)).getD #[]
    let mut tables : Tables := {}
    for h : j in [0:e.sections.size] do
      let s := e.sections[j]
      let prev := tables
      tables := tables.addAll s.defs
      if s.pass.toStringLossy != "short circuit" || j == 0 then continue
      let f0 := e.sections[j-1]!.func
      let env : PassEnv :=
        { passName := "short circuit", pkg := e.pkg, funcName := e.name, abi := e.abi,
          nosplit := e.nosplit, pgohot := e.pgohot, config := e.config, typs,
          typeOrder := default, tables := prev }
      let some boolT := env.typ? "Bool" | errs := errs + 1; continue
      let isBool (t : TypeRef) : Bool := (env.type? t).map (·.kind) == some .BOOL
      let (f1, k1) := constPhiArgsI prev isBool env.typeOrder.eq boolT f0 { k with fns := k.fns + 1 }
      if f1 != ShortCircuit.constPhiArgs isBool env.typeOrder.eq boolT f0 then
        errs := errs + 1
      let mut k1 := k1
      if f1.valueTab.size != f0.valueTab.size then k1 := { k1 with cpaGrow := k1.cpaGrow + 1 }
      -- `f1` with `f0`'s arguments back: only the new constants differ
      let restore (x : Nat) (o : Option Value) : Option Value :=
        match o, f0.value? x with
        | some gv, some fv => some { gv with args := fv.args }
        | o, _ => o
      let mid : Func := { f1 with valueTab := f1.valueTab.mapIdx restore }
      if f1 != f0 && !GoFV.Opt.ZCSE.zrel prev f0 mid then
        k1 := show1 { k1 with cpaZrelRej := k1.cpaZrelRej + 1 } s!"{path}: zrel rejects constPhiArgs' constants"
      let sc0 := k1.sc
      match loop prev s!"{path}" roundFuel f1 k1 with
      | .ok (_, k') => k := { k' with maxPerFn := max k'.maxPerFn (k'.sc - sc0) }
      | .error _ => errs := errs + 1; k := k1
  IO.println s!"functions {k.fns}, errors {errs}"
  IO.println s!"constPhiArgs: functions {k.cpaFns}, args replaced edge0 {k.cpaArgs0} edge1 {k.cpaArgs1}; consts created {k.cpaNew}, reused {k.cpaReused}; const type ≠ phi type {k.cpaTypeNe}; const shape not bool {k.cpaNotBoolShape}; const not listed in entry {k.cpaNotEntry}; value table grows {k.cpaGrow}; zrel rejects {k.cpaZrelRej}"
  IO.println s!"shortcircuitBlock: rewrites {k.sc} (max per function {k.maxPerFn}); plan none {k.planNone}, merge {k.planMerge}, uIntoT {k.planUIntoT}, tIntoU {k.planTIntoU}, tExits {k.planTExits}, uExits {k.planUExits}"
  IO.println s!"  nOtherPhi 1: {k.nOther1}, 2: {k.nOther2}, ≥3: {k.nOther3}; chain length 1: {k.chain1}, 2: {k.chain2}, ≥3: {k.chain3}; negated {k.swaps}; t phis extended {k.tPhis}"
  IO.println s!"  fixPhi {k.fixPhis} (unused other phis skipped {k.fixPhiUnused}); moved {k.moved} (afterMove setArg {k.afterMoveSetArg}, phielimValue {k.movedElim}, reset Invalid {k.movedInvalid}); final resets {k.finalReset}; b Invalid {k.bInvalid}; ctl → Copy {k.ctlCopy}"
  IO.println s!"  b values read outside b's non-phis/controls {k.bvalOut}; scan cost (values) {k.scanCost}; copy mismatches {k.mismatch}"
  IO.println s!"  plan phis: self-referencing {k.selfRef}, an argument defined in b or the plan's blocks {k.argInRegion}"
  IO.println s!"  checker (scOK) accepts by plan [none, merge, uIntoT, tIntoU, tExits, uExits]: {k.acc}; rejects: {k.rej}; checked blocks {k.kBlocks}; value table grows {k.grows}, block table {k.growsB}"
  for s in k.shown do IO.println s!"  {s}"
  for s in k.rejShown do IO.println s!"  reject: {s}"
  return 0

end GoFVTest.ShortCircProbe

def main (args : List String) : IO UInt32 := GoFVTest.ShortCircProbe.main args

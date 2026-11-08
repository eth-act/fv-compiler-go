import GoFV.Opt.Opt
import GoFV.SSA.Edges

variable [GoFV.SSA.Sem.Addrs]

/-!
# sccp (`sccp.go`)

Wegman–Zadeck sparse conditional constant propagation, ported verbatim (`docs/PASSES.md`,
sccp). The analysis (`analyze`) is deterministic: the edge and use worklists are FIFO, built in
`f.Blocks` × `b.Values` × `Args` and `b.Succs` order; `visited`, `defUse` and `defBlock` are
only looked up (`visited` is an array by block ID rather than a `Std.HashSet`, which the kernel
cannot evaluate, so witnesses can run the analysis by `decide +kernel`). Each fold attempt
(`computeLattice`) appends a temporary value to `f.Entry.Values` (a dead constant, or
`OpInvalid` when no folding rule applies), folded by the generic rules
(`Interp.rewriteValue genericTable`, Go's `rewriteValuegeneric`).

`replaceConst` ranges over the Go map `latticeCells`, so the order in which it rewires blocks
is Go's random map order. `replace a order` takes that order as a parameter; `sccp` uses the
insertion order of `latticeCells` (`Analysis.keys`). Only the relative order of values whose
rewiring removes edges into a common block is observable (the `Preds` and phi-argument order
of that block, `docs/PARITY.md`); `GoFV.Opt.SccpReplay` recovers it from the stock output.
-/

namespace GoFV.Opt

open GoFV.SSA GoFV.Rules

namespace Sccp

/-- `lt.tag` (`top < constant < bottom`). -/
def Lat.tag : Lat → Nat
  | .top => 0 | .const .. => 1 | .bottom => 2

/-- `lattice{lt.tag, nil}` for a non-constant lattice. -/
def Lat.untagged : Lat → Lat
  | .bottom => .bottom
  | _ => .top

/-- `equals(a, b)`: same tag, and constants with the same `Op` and `AuxInt`. -/
def Lat.equals : Lat → Lat → Bool
  | .top, .top | .bottom, .bottom => true
  | .const _ o a, .const _ o' a' => o == o' && a == a'
  | _, _ => false

/-- The 1-input ops `visitValue` folds. -/
def unaryOp : Op → Bool
  | .Neg8 | .Neg16 | .Neg32 | .Neg64 | .Neg32F | .Neg64F
  | .Com8 | .Com16 | .Com32 | .Com64
  | .Floor | .Ceil | .Trunc | .RoundToEven | .Sqrt
  | .Trunc16to8 | .Trunc32to8 | .Trunc32to16 | .Trunc64to8
  | .Trunc64to16 | .Trunc64to32 | .Cvt32to32F | .Cvt32to64F
  | .Cvt64to32F | .Cvt64to64F | .Cvt32Fto32 | .Cvt32Fto64
  | .Cvt64Fto32 | .Cvt64Fto64 | .Cvt32Fto64F | .Cvt64Fto32F
  | .CvtBoolToUint8
  | .ZeroExt8to16 | .ZeroExt8to32 | .ZeroExt8to64 | .ZeroExt16to32
  | .ZeroExt16to64 | .ZeroExt32to64 | .SignExt8to16 | .SignExt8to32
  | .SignExt8to64 | .SignExt16to32 | .SignExt16to64 | .SignExt32to64
  | .Ctz8 | .Ctz16 | .Ctz32 | .Ctz64
  | .Slicemask
  | .IsNonNil
  | .Not => true
  | _ => false

/-- The 2-input ops `visitValue` folds. -/
def binaryOp : Op → Bool
  | .Add64 | .Add32 | .Add16 | .Add8 | .Add32F | .Add64F
  | .Sub64 | .Sub32 | .Sub16 | .Sub8 | .Sub32F | .Sub64F
  | .Mul64 | .Mul32 | .Mul16 | .Mul8 | .Mul32F | .Mul64F
  | .Div32F | .Div64F
  | .Div8 | .Div16 | .Div32 | .Div64
  | .Div8u | .Div16u | .Div32u | .Div64u
  | .Mod8 | .Mod16 | .Mod32 | .Mod64
  | .Mod8u | .Mod16u | .Mod32u | .Mod64u
  | .Eq64 | .Eq32 | .Eq16 | .Eq8 | .Eq32F | .Eq64F
  | .Less64 | .Less32 | .Less16 | .Less8
  | .Less64U | .Less32U | .Less16U | .Less8U
  | .Less32F | .Less64F
  | .Leq64 | .Leq32 | .Leq16 | .Leq8
  | .Leq64U | .Leq32U | .Leq16U | .Leq8U
  | .Leq32F | .Leq64F
  | .EqB | .NeqB
  | .Lsh64x64 | .Rsh64x64 | .Rsh64Ux64 | .Lsh32x64
  | .Rsh32x64 | .Rsh32Ux64 | .Lsh16x64 | .Rsh16x64
  | .Rsh16Ux64 | .Lsh8x64 | .Rsh8x64 | .Rsh8Ux64
  | .IsInBounds | .IsSliceInBounds
  | .And8 | .And16 | .And32 | .And64
  | .Or8 | .Or16 | .Or32 | .Or64
  | .Xor8 | .Xor16 | .Xor32 | .Xor64 => true
  | _ => false

/-- `possibleConst(v)`. -/
def possibleConst (o : Op) : Bool :=
  isConst o || o == .Copy || o == .Phi || unaryOp o || binaryOp o

/-- The `worklist` (`f` lives in the rewrite state). Maps keyed by value or block ID are
arrays indexed by ID. -/
structure Work where
  edges : Array Edge := #[]
  /-- `t.edges = t.edges[1:]`: the next unread index. -/
  eHead : Nat := 0
  uses : Array ID := #[]
  uHead : Nat := 0
  /-- `inUses` (membership only). -/
  inUses : Array Bool
  /-- The executable edges (`visited`): by target block ID, their predecessor indices. -/
  visited : Array (List Nat)
  /-- `latticeCells` by value ID (`none`: no entry). -/
  cells : Array (Option Lat)
  /-- The keys of `latticeCells`, in insertion order. -/
  keys : Array ID := #[]
  defUse : Array (Array ID)
  defBlock : Array (Array ID)
  visitedBlock : Array Bool

/-- `t.visited[e]`. -/
def Work.seen (w : Work) (e : Edge) : Bool := (w.visited.getD e.b []).contains e.i

/-- The edges of `visited`, by target block ID. -/
def edgesOf (vis : Array (List Nat)) : Array Edge :=
  (List.range vis.size).foldl (fun r b => (vis.getD b []).foldl (fun r i => r.push ⟨b, i⟩) r) #[]

/-- The pass monad: the worklist over the rewrite monad (which holds the function). -/
abbrev M := StateT Work RwM

/-- `buildDefUses()`. -/
def buildDefUses (f : Func) (w : Work) : Work := Id.run do
  let mut defUse := w.defUse
  let mut defBlock := w.defBlock
  for b in f.blocks do
    let blk := f.getB b
    for v in blk.values do
      let x := f.getV v
      for a in x.args do
        if possibleConst (f.getV a).op && possibleConst x.op then
          if a == v then continue
          defUse := defUse.modify a (·.push v)
    for c in blk.controls do
      if possibleConst (f.getV c).op then
        defBlock := defBlock.modify c (·.push b)
  return { w with defUse, defBlock }

/-- `getLatticeCell(v)`. -/
def getLatticeCell (x : Value) : M Lat := do
  if !possibleConst x.op then return .bottom
  return ((← get).cells[x.id]?.join).getD .top

/-- `t.latticeCells[v] = lt`. -/
def setCell (v : ID) (lt : Lat) : M Unit :=
  modify fun w =>
    let keys := if (w.cells[v]?.join).isSome then w.keys else w.keys.push v
    { w with cells := Func.tabPut w.cells v lt, keys }

@[inline] def cell (v : ID) : M Lat := do getLatticeCell (← RwM.val v)

/-- `propagate(block)`. -/
def propagate (b : ID) : M Unit := do
  let blk ← RwM.blk b
  match blk.kind with
  | .Exit | .Ret | .RetJmp | .Invalid => pure ()
  | .Defer => modify fun w => { w with edges := w.edges ++ blk.succs }
  | .First | .Plain => modify fun w => { w with edges := w.edges.push blk.succs[0]! }
  | .If | .JumpTable =>
    match ← cell blk.controls[0]! with
    | .bottom => modify fun w => { w with edges := w.edges ++ blk.succs }
    | .const _ _ ai =>
      let idx : Int := if blk.kind == .If then 1 - ai.toInt else ai.toInt
      if blk.kind == .JumpTable && (idx < 0 || idx ≥ blk.succs.size) then return
      let some e := blk.succs[idx.toNat]? | throw s!"sccp: b{b}: no successor {idx}"
      modify fun w => { w with edges := w.edges.push e }
    | .top => pure ()
  | _ => throw s!"sccp: b{b}: All kind of block should be processed above."

/-- `addUses(v)`. -/
def addUses (v : ID) : M Unit := do
  -- read the chains first: holding the whole worklist across the loop would copy it
  let us := (← get).defUse[v]!
  let bs := (← get).defBlock[v]!
  for u in us do
    if (← cell u).tag == 2 then continue
    if !(← get).inUses[u]! then
      modify fun w => { w with inUses := w.inUses.set! u true, uses := w.uses.push u }
  for b in bs do
    if (← get).visitedBlock[b]! then propagate b

/-- `meet(phi)`. -/
def meet (x : Value) : M Lat := do
  let mut opt : Lat := .top
  for h : i in [0:x.args.size] do
    if (← get).seen ⟨x.block, i⟩ then
      let lt ← cell x.args[i]
      match lt with
      | .const .. =>
        if opt.tag == 0 then opt := lt
        else if !opt.equals lt then return .bottom
      | .bottom => return .bottom
      | .top => pure ()
  return opt

/-- `computeLattice(f, val, args...)`: fold a temporary copy of `val` over the constant
arguments with the generic rules. The temporary stays at the end of `f.Entry.Values`. -/
def computeLattice (x : Value) (args : Array ID) : M Lat := do
  let t ← RwM.modFGet fun f => f.newValue x.op x.type f.entry x.pos
  RwM.modF (·.addArgs t args)
  let matched ← Interp.rewriteValue genericTable t
  let y ← RwM.val t
  if matched && isConst y.op then return .const t y.op y.auxInt
  RwM.modF (·.resetValue t .Invalid)
  return .bottom

/-- `visitValue(val)`. -/
def visitValue (v : ID) : M Unit := do
  let x ← RwM.val v
  if !possibleConst x.op then return
  let old ← getLatticeCell x
  if old.tag == 2 then return
  if isConst x.op then setCell v (.const v x.op x.auxInt)
  else if x.op == .Copy then setCell v (← cell x.args[0]!)
  else if x.op == .Phi then setCell v (← meet x)
  else if unaryOp x.op then
    match ← cell x.args[0]! with
    | .const a .. => setCell v (← computeLattice x #[a])
    | lt1 => setCell v lt1.untagged
  else if binaryOp x.op then
    let lt1 ← cell x.args[0]!
    let lt2 ← cell x.args[1]!
    match lt1, lt2 with
    | .const a .., .const b .. => setCell v (← computeLattice x #[a, b])
    | _, _ => setCell v (if lt1.tag == 2 || lt2.tag == 2 then .bottom else .top)
  -- the deferred check
  let new ← getLatticeCell x
  if !new.equals old then
    if old.tag > new.tag then throw "Must lower lattice"
    addUses v

/-- The worklist loop. Each iteration consumes one queued edge or use; `fuel` bounds both
queues' total length (`sccpFuel`). -/
def loop : Nat → M Unit
  | 0 => throw "sccp: worklist fuel exhausted"
  | n + 1 => do
    let w ← get
    if h : w.eHead < w.edges.size then
      let e := w.edges[w.eHead]
      let seen := w.seen e
      let destVisited := w.visitedBlock[e.b]!
      set { w with eHead := w.eHead + 1 }
      if !seen then
        let dest := e.b
        modify fun w => { w with visited := w.visited.modify e.b (e.i :: ·),
                                 visitedBlock := w.visitedBlock.set! dest true }
        for v in (← RwM.blk dest).values do
          if (← RwM.val v).op == .Phi || !destVisited then visitValue v
        if !destVisited then propagate dest
      loop n
    else if h : w.uHead < w.uses.size then
      let u := w.uses[w.uHead]
      set { w with uHead := w.uHead + 1, inUses := w.inUses.set! u false }
      visitValue u
      loop n
    else return

/-- A bound on the worklist iterations: every lattice cell is lowered at most twice, so each
block is propagated at most `1 + 2·#controls` times and each value queued at most twice per
`defUse` entry (generously over-approximated). -/
def sccpFuel (f : Func) : Nat :=
  f.blocks.foldl (init := 16) fun n b =>
    let blk := f.getB b
    let args := blk.values.foldl (init := 0) fun k v => k + (f.getV v).args.size
    n + 4 * (blk.succs.size + 1) * (blk.controls.size + 1) + 4 * (args + 1)

/-- The analysis result: the function with the fold temporaries, the tables, the lattice and
the blocks each value controls. -/
structure Analysis where
  f : Func
  tables : Tables
  cells : Array (Option Lat)
  /-- `latticeCells` keys in insertion order. -/
  keys : Array ID
  defBlock : Array (Array ID)
  /-- The executable edges (`visited`) and blocks (`visitedBlock`). -/
  visited : Array Edge
  visitedBlock : Array Bool

/-- The lattice cell of `v` (`none`: no entry). -/
def Analysis.cell? (a : Analysis) (v : ID) : Option Lat := a.cells[v]?.join

/-- The analysis phase of `sccp(f)`: `buildDefUses` and the worklist loop. -/
def analyze (rw : RwEnv) (tables : Tables) (f : Func) : Except String Analysis :=
  let nv := f.vidLast + 1
  let w : Work := { inUses := Array.replicate nv false, cells := Array.replicate nv none,
                    defUse := Array.replicate nv #[], defBlock := Array.replicate nv #[],
                    visitedBlock := Array.replicate (f.bidLast + 1) false,
                    visited := Array.replicate (f.bidLast + 1) [],
                    edges := #[⟨f.entry, 0⟩] }
  let w := buildDefUses f w
  let st : RwState := { f, tables, pending := XPosMap.ofCache f.cache.lineStarts }
  match ((loop (sccpFuel f)).run w |>.run rw).run st with
  | .ok ((), w) s => .ok { f := s.f, tables := s.tables, cells := w.cells, keys := w.keys,
                           defBlock := w.defBlock, visited := edgesOf w.visited,
                           visitedBlock := w.visitedBlock }
  | .error e _ => .error e

/-- `rewireSuccessor(block, constVal)` with `rm` removing edges; true if the block was rewired.
-/
def rewireWith (rm : Func → ID → Nat → Func) (f : Func) (b : ID) (ai : Int64) : Func × Bool :=
  let blk := f.getB b
  let plain (f : Func) : Func :=
    (f.modB b fun x => { x with kind := .Plain, likely := .unknown }).resetControls b
  match blk.kind with
  | .If => (plain (rm f b ai.toInt.toNat), true)
  | .JumpTable =>
    let idx := ai.toInt
    if idx < 0 || idx ≥ blk.succs.size then (f, false) else
    let f := f.swapSuccessorsByIdx b 0 idx.toNat
    let f := (List.range (blk.succs.size - 1)).foldl (fun f _ => rm f b 1) f
    (plain f, true)
  | _ => (f, false)

/-- `rewireSuccessor(block, constVal)`; true if the block was rewired. -/
def rewireSuccessor : Func → ID → Int64 → Func × Bool := rewireWith Func.removeEdge

/-- `replaceConst()`, ranging over `latticeCells` in `order` (a permutation of `a.keys`), with
`rewire` for `rewireSuccessor` (the checker's intermediate function uses another,
`GoFV.Opt.Sccp.rewireFirst`). -/
def replace (a : Analysis) (order : Array ID)
    (rewire : Func → ID → Int64 → Func × Bool := rewireSuccessor) : Func := Id.run do
  let mut f := a.f
  for v in order do
    if let some (.const _ op ai) := a.cell? v then
      if !isConst (f.getV v).op then
        f := (f.resetValue v op).modV v fun x => { x with auxInt := ai }
      for b in a.defBlock[v]! do
        f := (rewire f b ai).1
  return f

end Sccp

/-- `sccp(f)` with `replaceConst` ranging over `latticeCells` in `order a` (default: insertion
order). -/
def sccpWith (order : Sccp.Analysis → Array ID) : Pass := fun env f => do
  let rw ← RwEnv.ofPassEnv env
  let a ← Sccp.analyze rw env.tables f
  return { func := Sccp.replace a (order a), tables := a.tables }

/-- The `sccp` pass. -/
def sccpPass : Pass := sccpWith (·.keys)

end GoFV.Opt

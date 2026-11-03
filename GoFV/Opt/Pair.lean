import GoFV.Opt.Pass
import GoFV.SSA.Alloc
import GoFV.SSA.TypeNew
import GoFV.SSA.TypePred
import GoFV.Util.PdqSort
import GoFV.Util.PdqSortM
import Std.Data.HashMap

/-!
# pair (`pair.go`)

ARM64 load/store pairing (docs/PASSES2.md, pair; issue #391). `offsetOk` returns true
unconditionally in this pin, so every pairable op qualifies.

1. `pairLoads`, per block: the pairable loads (`MOVDload`, `MOVWUload`, `MOVWload`,
   `FMOVDload`, `FMOVSload`) in `b.Values` order, sorted (`slices.SortFunc`) by Go opcode
   number, pointer ID, memory ID, aux (nil first, then by an aux number the comparator assigns
   on first sight: `PdqSortM` with the numbering as state), offset (wrapping `int64`
   differences). Adjacent loads with equal op/pointer/memory/aux, offsets one width apart,
   become `Select0`/`Select1` of a new pair load appended to the block (at the first load's
   position, with type `NewTuple`); the second is skipped.
2. Cross-block: for each block that is not a write-barrier test (`NZW` of a `MOVWUload` of
   `runtime.writeBarrier`), the pairable loads of its single-predecessor successors keyed by
   `(op, ptr, mem, offset, aux)` (last wins); scanning the block's values backwards, at most 4
   loads pair with a successor load at `offset + width` (tried first) or `offset - width`: a
   pair load appended to the block, the block's load becomes its selector, the successor load
   a `Copy` of a new selector appended to the block (at the successor load's position).
3. `pairStores`, per block: from the first store that no same-block memory op uses, walk the
   memory chain backwards (stopping at `InitMem`, `Phi` or a memory argument from another
   block), collecting stores of known width (`MOVD`/`FMOVD` 8, `MOVW`/`FMOVS` 4, `MOVH` 2, `MOVB`
   1) with one base pointer and aux and disjoint ranges, at most 100; a flush sorts them by
   offset and turns adjacent equal-op stores one width apart into the pair store (the lower
   one, rewritten in place) and a memory `Copy` (the upper one).
-/

namespace GoFV.Opt

open GoFV.SSA

namespace Pair

/-- `pairableLoads[op]`: element width and pair op. -/
def loadInfo : Op → Option (Int64 × Op)
  | .ARM64MOVDload => some (8, .ARM64LDP)
  | .ARM64MOVWUload => some (4, .ARM64LDPW)
  | .ARM64MOVWload => some (4, .ARM64LDPSW)
  | .ARM64FMOVDload => some (8, .ARM64FLDPD)
  | .ARM64FMOVSload => some (4, .ARM64FLDPS)
  | _ => none

/-- `pairableStores[op]`: element width and pair op. -/
def storeInfo : Op → Option (Int64 × Op)
  | .ARM64MOVDstore => some (8, .ARM64STP)
  | .ARM64MOVWstore => some (4, .ARM64STPW)
  | .ARM64FMOVDstore => some (8, .ARM64FSTPD)
  | .ARM64FMOVSstore => some (4, .ARM64FSTPS)
  | _ => none

/-- `storeWidth(op)` of `pairStores`: 0 for stores the pass does not understand. -/
def storeWidth : Op → Int64
  | .ARM64MOVDstore | .ARM64FMOVDstore => 8
  | .ARM64MOVWstore | .ARM64FMOVSstore => 4
  | .ARM64MOVHstore => 2
  | .ARM64MOVBstore => 1
  | _ => 0

/-- `overlap(offset1, size1, offset2, size2)` on Go `int64`s (wrapping sums). -/
def overlap (o1 s1 o2 s2 : Int64) : Bool :=
  (o1 ≥ o2 && o2 + s2 > o1) || (o2 ≥ o1 && o1 + s1 > o2)

/-- What the pass reads besides the function. -/
structure Ctx where
  isMem : TypeRef → Bool
  /-- Fresh type numbers start here (`NewTuple`). -/
  floor : Nat

/-- The state: the function and the tables (new tuple types). -/
structure St where
  f : Func
  tabs : Tables

/-- `b.NewValue2IA(pos, op, NewTuple(t0, t1), auxInt, aux, ptr, mem)`. -/
def newPairLoad (c : Ctx) (s : St) (b : ID) (pos : Pos) (op : Op) (t0 t1 : TypeRef)
    (auxInt : Int64) (aux : Option AuxRef) (ptr mem : ID) : Except String (St × ID) := do
  let (t, tabs) ← s.tabs.newTuple c.floor t0 t1
  let (f, load) := s.f.newValueArgs b pos op t auxInt aux #[ptr, mem]
  return ({ f, tabs }, load)

/-- `x.reset(op); x.SetArgs1(a)`. -/
def resetTo (f : Func) (x : ID) (op : Op) (a : ID) : Func := (f.resetValue x op).setArgs1 x a

/-- The load sort's comparator (`pair.go:155-180`); the state numbers auxes on first sight. -/
def cmpLoad (f : Func) (x y : ID) : StateM (Std.HashMap AuxRef Int) Int := do
  let x := f.getV x
  let y := f.getV y
  if x.op != y.op then return (x.op.goNum : Int) - y.op.goNum
  let (x0, y0) := (x.args[0]!, y.args[0]!)
  if x0 != y0 then return (x0 : Int) - y0
  let (x1, y1) := (x.args[1]!, y.args[1]!)
  if x1 != y1 then return (x1 : Int) - y1
  match x.aux, y.aux with
  | some xa, some ya =>
    let a ← auxID xa
    let b ← auxID ya
    if a != b then return a - b
  | some _, none => return 1
  | none, some _ => return -1
  | none, none => pure ()
  return (x.auxInt - y.auxInt).toInt
where
  auxID (a : AuxRef) : StateM (Std.HashMap AuxRef Int) Int := do
    let m ← get
    match m[a]? with
    | some i => return i
    | none =>
      let i : Int := m.size
      set (m.insert a i)
      return i

/-- The first loop of `pairLoads`: pairs within each block. -/
def pairLoadsLocal (c : Ctx) (s : St) : Except String St := do
  let mut s := s
  for b in s.f.blocks do
    let loads := (s.f.getB b).values.filter fun v => (loadInfo (s.f.getV v).op).isSome
    if loads.size < 2 then continue
    let f := s.f
    let loads := (GoFV.Util.PdqSortM.sortFunc (cmpLoad f) loads |>.run' {}).run
    let mut i := 0
    -- each iteration advances `i`
    for _ in [0:loads.size] do
      if i + 1 ≥ loads.size then break
      let x := s.f.getV loads[i]!
      let y := s.f.getV loads[i + 1]!
      i := i + 1
      if x.op != y.op || x.args[0]! != y.args[0]! || x.args[1]! != y.args[1]! then continue
      if x.aux != y.aux then continue
      let some (w, pairOp) := loadInfo x.op | continue
      if x.auxInt + w != y.auxInt then continue
      let (s', load) ← newPairLoad c s b x.pos pairOp x.type y.type x.auxInt x.aux
        x.args[0]! x.args[1]!
      let f := resetTo s'.f x.id .Select0 load
      s := { s' with f := resetTo f y.id .Select1 load }
      i := i + 1
  return s

/-- `memoryBarrierTest(b)`. -/
def memoryBarrierTest (tabs : Tables) (f : Func) (b : ID) : Bool :=
  let blk := f.getB b
  blk.kind == .ARM64NZW &&
    match blk.controls[0]? with
    | none => false
    | some c =>
      let x := f.getV c
      x.op == .ARM64MOVWUload &&
        match (x.aux.bind tabs.aux?).map (·.kind) with
        | some (AuxKind.sym n ..) => n == GoStr.ofString "runtime.writeBarrier"
        | _ => false

/-- `nextBlockKey`: op, pointer, memory, offset, aux. -/
abbrev Key := Op × ID × ID × Int64 × Option AuxRef

/-- The second loop of `pairLoads`: pairs with loads of single-predecessor successors. -/
def pairLoadsNext (c : Ctx) (s : St) : Except String St := do
  let mut s := s
  for b in s.f.blocks do
    if memoryBarrierTest s.tabs s.f b then continue
    let mut next : Std.HashMap Key ID := {}
    for e in (s.f.getB b).succs do
      let sb := s.f.getB e.b
      if sb.preds.size > 1 then continue
      for v in sb.values do
        let x := s.f.getV v
        if (loadInfo x.op).isNone then continue
        next := next.insert (x.op, x.args[0]!, x.args[1]!, x.auxInt, x.aux) v
    if next.isEmpty then continue
    let vals := (s.f.getB b).values
    let mut nMoved := 0
    for k in [0:vals.size] do
      if nMoved ≥ 4 then break
      let x := s.f.getV vals[vals.size - 1 - k]!
      let some (w, pairOp) := loadInfo x.op | continue
      let key : Key := (x.op, x.args[0]!, x.args[1]!, x.auxInt + w, x.aux)
      if let some yid := next[key]? then
        next := next.erase key
        let y := s.f.getV yid
        let (s', load) ← newPairLoad c s b x.pos pairOp x.type y.type x.auxInt x.aux
          x.args[0]! x.args[1]!
        let f := resetTo s'.f x.id .Select0 load
        let f := f.resetValue yid .Copy
        let (f, sel) := f.newValueArgs b y.pos .Select1 y.type 0 none #[load]
        s := { s' with f := f.setArgs1 yid sel }
        nMoved := nMoved + 1
        continue
      let key : Key := (x.op, x.args[0]!, x.args[1]!, x.auxInt - w, x.aux)
      if let some yid := next[key]? then
        next := next.erase key
        let y := s.f.getV yid
        let (s', load) ← newPairLoad c s b x.pos pairOp y.type x.type y.auxInt x.aux
          x.args[0]! x.args[1]!
        let f := resetTo s'.f x.id .Select1 load
        let f := f.resetValue yid .Copy
        let (f, sel) := f.newValueArgs b y.pos .Select0 y.type 0 none #[load]
        s := { s' with f := f.setArgs1 yid sel }
        nMoved := nMoved + 1
  return s

/-- `v.MemoryArg()`; nil is fatal here (Go would dereference it). -/
def memoryArg (c : Ctx) (f : Func) (v : ID) : Except String ID := do
  let x := f.getV v
  if x.op == .Phi then throw s!"v{v}: MemoryArg on Phi"
  match x.args.back? with
  | some m => if c.isMem (f.getV m).type then return m
  | none => pure ()
  throw s!"v{v}: no memory argument"

/-- `prevStore(v)`: the memory argument if it is in `v`'s block. -/
def prevStore (c : Ctx) (f : Func) (v : ID) : Except String (Option ID) := do
  let x := f.getV v
  if x.op == .InitMem || x.op == .Phi then return none
  let m ← memoryArg c f v
  return if (f.getV m).block != x.block then none else some m

/-- `flushMemChain()`: pair adjacent stores of the chain sorted by offset. -/
def flush (c : Ctx) (f : Func) (chain : Array ID) : Except String Func := do
  if chain.size < 2 then return f
  let chain := GoFV.Util.PdqSort.sortFunc
    (fun x y => ((f.getV x).auxInt - (f.getV y).auxInt).toInt) chain
  let mut f := f
  let mut i := 0
  for _ in [0:chain.size] do
    if i + 1 ≥ chain.size then break
    let v := f.getV chain[i]!
    let w := f.getV chain[i + 1]!
    i := i + 1
    let mem ← memoryArg c f v.id
    let wmem ← memoryArg c f w.id
    let some (width, pairOp) := storeInfo v.op | continue
    if w.op == v.op && w.auxInt == v.auxInt + width then
      let args := #[v.args[0]!, v.args[1]!, w.args[1]!, mem]
      f := (f.resetValue v.id pairOp).addArgs v.id args
      f := f.modV v.id fun x => { x with aux := v.aux, auxInt := v.auxInt, pos := v.pos }
      f := resetTo f w.id .Copy wmem
      i := i + 1
  return f

/-- `pairStores(f)`. -/
def pairStores (c : Ctx) (f : Func) : Except String Func := do
  let limit := 100
  let mut f := f
  let mut last : Array Bool := Array.replicate (f.vidLast + 1) false
  for b in f.blocks do
    let vals := (f.getB b).values
    for v in vals do
      if c.isMem (f.getV v).type then last := last.set! v true
    for v in vals do
      if c.isMem (f.getV v).type then
        if let some m ← prevStore c f v then last := last.set! m false
    let some lastMem := vals.find? (last[·]!) | continue
    let mut chain : Array ID := #[]
    let mut cur := some lastMem
    -- the memory chain within the block is acyclic: at most `vals.size` steps
    for _ in [0:vals.size + 1] do
      let some v := cur | break
      let x := f.getV v
      let writeSize := storeWidth x.op
      if writeSize == 0 then
        f ← flush c f chain
        chain := #[]
      else
        let reset := chain.size > 0 &&
          let head := f.getV chain[0]!
          (x.uses != 1 || x.args[0]! != head.args[0]! || x.aux != head.aux)
        if reset || chain.size == limit then
          f ← flush c f chain
          chain := #[]
        for w in chain do
          let w := f.getV w
          if overlap w.auxInt (storeWidth w.op) x.auxInt writeSize then
            f ← flush c f chain
            chain := #[]
            break
        chain := chain.push v
      cur ← prevStore c f v
    f ← flush c f chain
  return f

end Pair

/-- `pair(f)` on arm64 with the tables (new tuple types); `floor` is the first fresh type
number. -/
def pair (tabs : Tables) (isMem : TypeRef → Bool) (floor : Nat) (f : Func) :
    Except String (Func × Tables) := do
  let c : Pair.Ctx := { isMem, floor }
  let s ← Pair.pairLoadsLocal c { f, tabs }
  let s ← Pair.pairLoadsNext c s
  return (← Pair.pairStores c s.f, s.tabs)

/-- The `pair` pass (arm64 only, as Go's arch switch). -/
def pairPass : Pass := fun env f => do
  match env.config? "arch" with
  | some #[.word "arm64"] => pure ()
  | _ => throw "pair: only arm64 is ported"
  let some mem := env.typ? "Mem" | throw "typs: no Mem"
  let floor := max env.tables.types.size env.typeOrder.rank.size
  let (f, tables) ← pair env.tables (env.tables.isMemory mem) floor f
  return { func := f, tables }

end GoFV.Opt

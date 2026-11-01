import GoFV.Opt.MemCombine.Base
import GoFV.Util.PdqSort
import GoFV.Util.SparseSet

/-!
# memcombine: stores (`memcombine.go:333-755`)

`memcombineStores` visits, per block, the in-block `Store` chains from their last store
backwards; `combineStores(root)` gathers up to 8 chained stores to one base (cumulative size
≤ `RegSize`), picks the largest prefix of total size 8, 4 or 2 whose stores are sequential in
memory, and rewrites `root` into one wide store of a constant, of a widened load, or of a
shifted/truncated/byte-swapped base value; the other stores are clobbered and retyped `bool`.
-/

namespace GoFV.Opt.MemCombine

open GoFV.SSA GoFV.Util

/-- A `StoreRecord`. -/
structure StoreRecord where
  store : ID
  offset : Int64
  size : Int64
  deriving Inhabited

@[inline] def isTrunc (o : Op) : Bool :=
  o == .Trunc64to8 || o == .Trunc64to16 || o == .Trunc64to32 || o == .Trunc32to8 ||
  o == .Trunc32to16 || o == .Trunc16to8

@[inline] def isRshU (o : Op) : Bool := o == .Rsh64Ux64 || o == .Rsh32Ux64 || o == .Rsh16Ux64

/-- `getShiftBase(a)`. -/
def getShiftBase (f : Func) (a : Array StoreRecord) : Option ID := do
  let x := (f.getV a[0]!.store).args[1]!
  let y := (f.getV a[1]!.store).args[1]!
  let xv := f.getV x
  let yv := f.getV y
  if !isTrunc xv.op then none
  if !isTrunc yv.op then none
  let x := xv.args[0]!
  let y := yv.args[0]!
  let xv := f.getV x
  let yv := f.getV y
  let x2 := if isRshU xv.op then some xv.args[0]! else none
  let y2 := if isRshU yv.op then some yv.args[0]! else none
  if y2 == some x then return x
  if x2 == some y then return y
  if x2 == y2 then x2 else none

/-- `isShiftBase(v, base)`. -/
def isShiftBase (f : Func) (v base : ID) : Bool :=
  let val := f.getV (f.getV v).args[1]!
  if !isTrunc val.op then false else
  let w := val.args[0]!
  if w == base then true else
  let wv := f.getV w
  isRshU wv.op && wv.args[0]! == base

/-- `shift(v, base)`. -/
def shiftOf (f : Func) (v base : ID) : Int64 :=
  let val := f.getV (f.getV v).args[1]!
  if !isTrunc val.op then -1 else
  let w := val.args[0]!
  if w == base then 0 else
  let wv := f.getV w
  if !isRshU wv.op then -1 else
  let s := f.getV wv.args[1]!
  if s.op != .Const64 then -1 else s.auxInt

/-- Go's `x << s` on `int64` (`s ≥ 0`): 0 once `s ≥ 64`. -/
@[inline] def goShl (x s : Int64) : Int64 :=
  if s ≥ 64 then 0 else x <<< s

/-- Rewrite `root` to store `sv` at `ptr` on `mem` with position `pos`; clobber the other
stores of `a` and retype them `bool`. -/
def install (root : ID) (a : Array StoreRecord) (ptr sv mem : ID) (pos : Pos) : M Unit := do
  let ta ← typeAux (← val sv).type
  let boolT := (← read).bool
  for r in a do
    let v := r.store
    if v == root then
      modF fun f =>
        let f := f.modV v fun x => { x with aux := some ta, pos }
        ((f.setArg v 0 ptr).setArg v 1 sv).setArg v 2 mem
    else
      clobber v
      modF (·.modV v fun x => { x with type := boolT })

/-- Gather the stores chained below `root` (`allMergeable`). -/
def gather (root : ID) (rbase : BaseAddress) (roff : Int64) : M (Array StoreRecord) := do
  let rx ← val root
  let rsize ← auxSize root
  let maxRegSize := (← read).regSize
  let mut all := #[{ store := root, offset := roff, size := rsize : StoreRecord }]
  let mut allSize := rsize
  let mut x := rx.args[2]!
  for _ in [1:8] do
    let xv ← val x
    if xv.op != .Store then break
    if xv.block != rx.block then break
    if xv.uses != 1 then break
    let xSize ← auxSize x
    if xSize == 0 then break
    if xSize > maxRegSize - allSize then break
    let (base, off) ← split xv.args[0]!
    if base != rbase then break
    all := all.push { store := x, offset := off, size := xSize }
    allSize := allSize + xSize
    x := xv.args[2]!
  return all

/-- The consecutive-loads check: the common memory argument of the loads that are the stored
values, if they are single-use pointer-free loads from consecutive offsets of one base. -/
def loadSource (a : Array StoreRecord) : M (Option ID) := do
  let mut first : Option (ID × BaseAddress × Int64) := none
  for r in a do
    let load ← arg r.store 1
    let lx ← val load
    if lx.op != .Load then return none
    if lx.uses != 1 then return none
    let hp ← match GoFV.Rules.Ty.hasPointers (← get).tabs lx.type with
      | .ok b => pure b
      | .error e => throw e
    if hp then return none
    let lmem := lx.args[1]!
    let (base, idx) ← split lx.args[0]!
    match first with
    | none => first := some (lmem, base, idx)
    | some (m, loadBase, loadIdx) =>
      if base != loadBase || lmem != m then return none
      if idx != loadIdx + (r.offset - a[0]!.offset) then return none
  return first.map (·.1)

/-- `combineStores(root)`. -/
def combineStores (root : ID) : M Unit := do
  let rx ← val root
  let (rbase, roff) ← split rx.args[0]!
  if (← read).s390x && (← op rbase.ptr) == .Addr then return
  let all ← gather root rbase roff
  if all.size ≤ 1 then return
  -- fit the combined total size to one of the register sizes
  let mut mergeableSet : Array (Int64 × Array StoreRecord) := #[]
  let mut sz : Int64 := 0
  for i in [0:all.size] do
    sz := sz + all[i]!.size
    if sz == 8 || sz == 4 || sz == 2 then
      mergeableSet := mergeableSet.push (sz, all.extract 0 (i + 1))
  let mut a : Array StoreRecord := #[]
  let mut aTotalSize : Int64 := 0
  let mut mem : ID := 0
  let mut pos := Pos.none
  -- pick the largest mergeable set
  for s in [(8 : Int64), 4, 2] do
    let candidate := ((mergeableSet.find? (·.1 == s)).map (·.2)).getD #[]
    if candidate.size ≥ 2 then
      let lastStore ← val candidate[candidate.size - 1]!.store
      mem := lastStore.args[2]!
      pos := lastStore.pos
      let candidate := PdqSort.sortFunc (fun x y => if x.offset < y.offset then -1
        else if x.offset > y.offset then 1 else 0) candidate
      let sequential := (List.range (candidate.size - 1)).all fun i =>
        candidate[i + 1]!.offset == candidate[i]!.offset + candidate[i]!.size
      if sequential then
        a := candidate
        aTotalSize := s
        break
  if a.size ≤ 1 then return
  let c ← read
  -- memory location to write at (the lowest one)
  let ptr := (← val a[0]!.store).args[0]!
  -- constant stores
  let mut isConst := true
  for r in a do
    match (← val (← arg r.store 1)).op with
    | .Const32 | .Const16 | .Const8 | .ConstBool => pure ()
    | _ => isConst := false
    if !isConst then break
  if isConst then
    let mut cst : Int64 := 0
    for r in a do
      let mask := goShl 1 ((8 : Int64) * r.size) - 1
      let mut s : Int64 := (r.offset - (a[0]!).offset) * 8
      if c.bigEndian then s := (aTotalSize - r.size) * 8 - s
      cst := cst ||| goShl ((← val (← arg r.store 1)).auxInt &&& mask) s
    let cv ← match aTotalSize.toInt with
      | 2 => constInt .Const16 c.u16 cst.toInt16.toInt64
      | 4 => constInt .Const32 c.u32 cst.toInt32.toInt64
      | _ => constInt .Const64 c.u64 cst
    install root a ptr cv mem pos
    return
  -- consecutive loads as the source of the stores
  let loadMem ← loadSource a
  if loadMem.isSome then
    if !c.loadSource then return
    -- widen the first load
    let load ← arg a[0]!.store 1
    let t := if aTotalSize == 2 then c.u16 else if aTotalSize == 4 then c.u32 else c.u64
    modF (·.modV load fun x => { x with type := t })
    install root a ptr load mem pos
    return
  -- all the shift/trunc are of the same base value
  let f ← getF
  let some shiftBase := getShiftBase f a | return
  if !a.all (fun r => isShiftBase f r.store shiftBase) then return
  -- writes in little- or big-endian order
  let shift0 := shiftOf f a[0]!.store shiftBase
  let isLittleEndian := (List.range a.size).all fun i =>
    i == 0 || shiftOf f a[i]!.store shiftBase == shift0 + (a[i]!.offset - a[0]!.offset) * 8
  let mut isBigEndian := true
  let mut shiftedSize : Int64 := 0
  for i in [1:a.size] do
    shiftedSize := shiftedSize + a[i]!.size
    if shiftOf f a[i]!.store shiftBase != shift0 - shiftedSize * 8 then
      isBigEndian := false
      break
  if !isLittleEndian && !isBigEndian then return
  let needSwap := isLittleEndian && c.bigEndian || isBigEndian && !c.bigEndian
  if needSwap && (Int64.ofNat a.size != aTotalSize || !(← haveByteSwap aTotalSize)) then return
  -- commit point
  let b := rx.block
  let rpos := rx.pos
  let mut sv := shiftBase
  if isLittleEndian && shift0 != 0 then sv ← shiftBy true b rpos sv shift0
  let bigShift := shift0 - (aTotalSize - a[0]!.size) * 8
  if isBigEndian && bigShift != 0 then sv ← shiftBy true b rpos sv bigShift
  let svSize ← size (← val sv).type
  if svSize > aTotalSize then sv ← truncate b rpos sv svSize aTotalSize
  if needSwap then sv ← byteSwap b rpos sv
  install root a ptr sv mem pos

/-- `memcombineStores(f)`. -/
def memcombineStores : M Unit := do
  let f ← getF
  let mut mark := SparseSet.new (f.vidLast + 1)
  for b in f.blocks do
    let f ← getF
    let vals := (f.getB b).values
    -- mark all stores which are not last in a store sequence
    mark := mark.clear
    for v in vals do
      let x := f.getV v
      if x.op == .Store then mark := mark.add x.args.back!
    -- later stores come earlier in the order
    let mut order : Array ID := #[]
    for v in vals do
      let x := f.getV v
      if x.op != .Store then continue
      if mark.contains v then continue
      let mut w := v
      for _ in [0:vals.size + 1] do
        order := order.push w
        w := (f.getV w).args[2]!
        let wx := f.getV w
        if wx.block != b || wx.op != .Store then break
    -- combining opportunities at each store in queue order
    for v in order do
      if (← op v) != .Store then continue
      let size ← auxSize v
      if size ≥ (← read).regSize || size == 0 then continue
      combineStores v

end GoFV.Opt.MemCombine

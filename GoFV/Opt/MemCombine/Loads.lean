import GoFV.Opt.MemCombine.Base
import GoFV.Rules.Helpers.MergePoint
import GoFV.Util.PdqSort
import GoFV.Util.SparseSet

/-!
# memcombine: loads (`memcombine.go:29-86,130-331`)

`memcombineLoads` finds the roots of `Or16/32/64` trees per block (in `b.Values` order, BFS
of each tree) and tries `combineLoads(v, n)` for n = max, max/2, …, 2; `combineLoads` matches n
leaves `[Lsh const](ZeroExt(Load ptr mem))` at contiguous offsets from one base, in little- or
big-endian shift order, and replaces the root by `Copy` of one wide load (plus `Bswap`,
`ZeroExt`, `Lsh` as needed) placed at `mergePoint` of the loads.
-/

namespace GoFV.Opt.MemCombine

open GoFV.SSA GoFV.Util

@[inline] def isOr (o : Op) : Bool := o == .Or16 || o == .Or32 || o == .Or64

/-- A `LoadRecord`. -/
structure LoadRecord where
  load : ID
  offset : Int64
  shift : Int64
  deriving Inhabited

/-- Collect the `n` leaves of the `orOp` tree at `root` (`a[i] = v.Args[0]; a = append(a,
v.Args[1]); i--`): `none` if a non-root node has other uses or there are fewer leaves. Each
step either grows `a` (at most `n` times) or advances `i`, so `2n + 1` steps suffice. -/
def orLeaves (root : ID) (orOp : Op) (n : Nat) : M (Option (Array ID)) := do
  let mut a := #[root]
  let mut i := 0
  for _ in [0:2 * n + 1] do
    if !(i < a.size && a.size < n) then break
    let v := a[i]!
    let x ← val v
    if x.uses != 1 && v != root then return none
    if x.op == orOp then
      a := (a.set! i x.args[0]!).push x.args[1]!
    else
      i := i + 1
  return if a.size == n then some a else none

/-- The zero extension op the leaves must use, from the first leaf. -/
def extOpFor (orOp o : Op) : Option Op :=
  if orOp == .Or64 && (o == .ZeroExt8to64 || o == .ZeroExt16to64 || o == .ZeroExt32to64) ||
     orOp == .Or32 && (o == .ZeroExt8to32 || o == .ZeroExt16to32) ||
     orOp == .Or16 && o == .ZeroExt8to16 then some o else none

/-- `combineLoads(root, n)`. -/
def combineLoads (root : ID) (n : Int64) : M Bool := do
  let rx ← val root
  let orOp := rx.op
  let some shiftOp := (match orOp with
    | .Or64 => some Op.Lsh64x64 | .Or32 => some .Lsh32x64 | .Or16 => some .Lsh16x64
    | _ => none) | return false
  let some a ← orLeaves root orOp n.toNatClampNeg | return false
  -- the first entry decides the ops we're looking for
  let mut v := a[0]!
  if (← op v) == shiftOp then v ← arg v 0
  let some extOp := extOpFor orOp (← op v) | return false
  v ← arg v 0
  if (← op v) != .Load then return false
  let (base, _) ← split (← arg v 0)
  let mem ← arg v 1
  let size ← size (← val v).type
  if (← read).s390x && (← op base.ptr) == .Addr then return false
  -- check all the entries
  let mut recs : Array LoadRecord := #[]
  for i in [0:a.size] do
    let mut w := a[i]!
    if (← val w).uses != 1 then return false
    let mut shift : Int64 := 0
    if (← op w) == shiftOp then
      let s ← val (← arg w 1)
      if s.op != .Const64 then return false
      shift := s.auxInt
      w ← arg w 0
      if (← val w).uses != 1 then return false
    if (← op w) != extOp then return false
    let load ← arg w 0
    let lx ← val load
    if lx.op != .Load then return false
    if lx.uses != 1 then return false
    if lx.args[1]! != mem then return false
    let (p, off) ← split lx.args[0]!
    if p != base then return false
    recs := recs.push { load, offset := off, shift }
  -- sort in memory address order
  let r := PdqSort.sortFunc (fun x y => if x.offset < y.offset then -1
    else if x.offset > y.offset then 1 else 0) recs
  -- contiguous offsets
  let r0 := r[0]!
  for i in [0:r.size] do
    if r[i]!.offset != r0.offset + Int64.ofNat i * size then return false
  -- little- or big-endian order
  let shift0 := r0.shift
  let isLittleEndian := (List.range r.size).all fun i =>
    r[i]!.shift == shift0 + Int64.ofNat i * size * 8
  let isBigEndian := (List.range r.size).all fun i =>
    r[i]!.shift == shift0 - Int64.ofNat i * size * 8
  if !isLittleEndian && !isBigEndian then return false
  -- where to put the new load
  let loads := r.map (·.load)
  let some loadBlock ← (do
      match GoFV.Rules.mergePoint (← getF) rx.block loads with
      | .ok b => pure b
      | .error e => throw e) | return false
  let mut pos := Pos.none
  for l in loads do
    let lx ← val l
    if lx.block == loadBlock then
      pos := lx.pos
      break
  if pos == Pos.none then return false
  let c ← read
  let needSwap := isLittleEndian && c.bigEndian || isBigEndian && !c.bigEndian
  if needSwap && (size != 1 || !(← haveByteSwap n)) then return false
  -- commit point
  v ← newValue loadBlock pos .Load (← sizeType (n * size)) #[← arg r0.load 0, mem]
  if needSwap then v ← byteSwap loadBlock pos v
  let rsize ← GoFV.Opt.MemCombine.size rx.type
  if n * size < rsize then v ← zeroExtend loadBlock pos v (n * size) rsize
  if isLittleEndian && shift0 != 0 then v ← shiftBy false loadBlock pos v shift0
  let sh := shift0 - (n - 1) * size * 8
  if isBigEndian && sh != 0 then v ← shiftBy false loadBlock pos v sh
  -- install with (Copy v)
  modF fun f => (f.resetValue root .Copy).addArg root v
  for x in r do clobber x.load
  return true

/-- `memcombineLoads(f)`. -/
def memcombineLoads : M Unit := do
  let f ← getF
  -- mark all values that are the argument of an OR
  let mut mark := SparseSet.new (f.vidLast + 1)
  for b in f.blocks do
    for v in (f.getB b).values do
      let x := f.getV v
      if isOr x.op then mark := (mark.add x.args[0]!).add x.args[1]!
  for b in f.blocks do
    let f ← getF
    let mut order : Array ID := #[]
    for v in (f.getB b).values do
      let x := f.getV v
      if !isOr x.op then continue
      if mark.contains v then continue
      -- BFS of the OR tree rooted at v
      let mut i := order.size
      order := order.push v
      for _ in [0:f.vidLast + 1] do
        if h : i < order.size then
          let y := f.getV order[i]
          for j in [0:2] do
            let a := y.args[j]!
            if isOr (f.getV a).op then order := order.push a
          i := i + 1
        else break
      if i < order.size then throw s!"memcombineLoads: OR tree at v{v} too large"
    for v in order do
      let o ← op v
      if !isOr o then continue
      let regSize := (← read).regSize
      let max : Int64 := if o == .Or64 then regSize else if o == .Or32 then 4 else 2
      let mut n := max
      for _ in [0:64] do
        if n ≤ 1 then break
        if ← combineLoads v n then break
        n := n / 2

end GoFV.Opt.MemCombine

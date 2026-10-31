import GoFV.SSA.TypePred
import GoFV.Util.PdqSort
import Std.Data.HashSet.Basic

/-!
# `storeOrder`

Port of `storeOrder` (`ssa/schedule.go:397-560`, go1.27.3), used by `nilcheckelim` and
`writebarrier` to put a block's values in store order: stores by their memory chain, each
followed by the nil checks and then the other values that depend on it (store numbers `3i`,
`3i+1`, `3i+2`), placed by a counting sort that keeps `b.Values` order within a bin; runs of
nil checks are then sorted by position with Go's unstable `slices.SortFunc` (ties possible:
exact port in `GoFV.Util.PdqSort`). In `nilcheckelim` a block without nil checks is left as is
(`f.pass.name`, docs/PASSES.md §1.8).

`storeNumber` is the caller's scratch slice (indexed by value ID); Go never clears it, so values
numbered by an earlier call keep their numbers, and the port threads it through. The `sset`
scratch set is cleared by `storeOrder` itself and is local here. `Except.error` is Go's
`Fatalf` or a nil dereference on malformed input.
-/

namespace GoFV.SSA

namespace StoreOrder

/-- `valuePosCmp(a, b)`: −1 if `a.Pos.Before(b.Pos)`, +1 if after, else 0. -/
def valuePosCmp (f : Func) (a b : ID) : Int :=
  let pa := ((f.value? a).map (·.pos)).getD default
  let pb := ((f.value? b).map (·.pos)).getD default
  if pa.before pb then -1 else if pa.after pb then 1 else 0

end StoreOrder

open StoreOrder in
/-- `storeOrder(values, sset, storeNumber)` in pass `passName`, with `isMem = t.IsMemory()`:
the reordered values and the updated `storeNumber`. -/
def storeOrder (f : Func) (isMem : TypeRef → Bool) (passName : String) (values : Array ID)
    (storeNumber : Array Int) : Except String (Array ID × Array Int) := do
  if values.isEmpty then return (values, storeNumber)
  let getV (id : ID) : Value := (f.value? id).getD default
  -- `v.MemoryArg()` (`none` for Go's nil; never called on a Phi here)
  let memArg (v : Value) : Option ID :=
    match v.args.back? with
    | some m => if isMem (getV m).type then some m else none
    | none => none
  -- find all stores
  let mut stores : Array ID := #[]
  let mut hasNilCheck := false
  let mut sset : Std.HashSet ID := {}
  for v in values do
    let x := getV v
    if isMem x.type then
      stores := stores.push v
      if x.op == .InitMem || x.op == .Phi then continue
      let some m := memArg x | throw s!"storeOrder: v{v} has no memory argument"
      sset := sset.insert m
    if x.op == .NilCheck then hasNilCheck := true
  if stores.isEmpty || (!hasNilCheck && passName == "nilcheckelim") then
    return (values, storeNumber)
  -- find the last store, the one not used by other stores
  let mut last : Option ID := none
  for v in stores do
    if !sset.contains v then
      if let some l := last then throw s!"two stores live simultaneously: v{v} and v{l}"
      last := some v
  let mut storeNumber := storeNumber
  let mut count : Array Int := Array.replicate (3 * (stores.size + 1)) 0
  sset := {}
  let mut w := last
  for k in [0:stores.size] do
    let n := stores.size - k
    let some wv := w | throw "storeOrder: nil store in the memory chain"
    storeNumber := storeNumber.set! wv (3 * n)
    count := count.modify (3 * n) (· + 1)
    sset := sset.insert wv
    let x := getV wv
    if x.op == .InitMem || x.op == .Phi then
      if n != 1 then throw s!"store order is wrong: there are stores before v{wv}"
      break
    w := memArg x
  -- assign the other values their numbers in DFS order
  for v in values do
    if sset.contains v then continue
    let mut stack : Array ID := #[v]
    sset := sset.insert v
    -- every value is pushed once (sset) and every iteration pushes or pops
    for _ in [0:2 * values.size + 1] do
      let some wv := stack.back? | break
      if storeNumber.getD wv 0 != 0 then
        stack := stack.pop
        continue
      let x := getV wv
      if x.op == .Phi then
        storeNumber := storeNumber.set! wv 2
        count := count.modify 2 (· + 1)
        stack := stack.pop
        continue
      let mut max : Int := 0
      let mut argsdone := true
      for a in x.args do
        if (getV a).block != x.block then continue
        if !sset.contains a then
          stack := stack.push a
          sset := sset.insert a
          argsdone := false
          break
        let sa := storeNumber.getD a 0 / 3
        if sa > max then max := sa
      if !argsdone then continue
      let n := if x.op == .NilCheck then 3 * max + 1 else 3 * max + 2
      storeNumber := storeNumber.set! wv n
      count := count.modify n.toNat (· + 1)
      stack := stack.pop
  -- prefix sums
  for i in [1:count.size] do
    count := count.set! i (count[i]! + count[i - 1]!)
  if count.back? != some (values.size : Int) then
    throw s!"storeOrder: value is missing, total count = {count.back?.getD 0}"
  -- place values in count-indexed bins
  let mut order : Array ID := Array.replicate values.size 0
  for v in values do
    let s := storeNumber.getD v 0
    if s < 1 then throw s!"storeOrder: v{v} has no store number"
    let j := (s - 1).toNat
    order := order.set! (count[j]!).toNat v
    count := count.modify j (· + 1)
  -- order nil checks in source order
  if hasNilCheck then
    let sortRange (o : Array ID) (a b : Nat) : Array ID :=
      let s := GoFV.Util.PdqSort.sortFunc (valuePosCmp f) (o.extract a b)
      s.foldl (init := (o, a)) (fun (o, i) x => (o.set! i x, i + 1)) |>.1
    let mut start : Option Nat := none
    for i in [0:order.size] do
      if (getV order[i]!).op == .NilCheck then
        if start.isNone then start := some i
      else if let some s := start then
        order := sortRange order s i
        start := none
    if let some s := start then order := sortRange order s order.size
  return (order, storeNumber)

end GoFV.SSA

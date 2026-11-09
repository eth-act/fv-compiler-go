import GoFV.Opt.Sccp

variable [GoFV.SSA.Sem.Addrs]

/-!
# sccp: replaying Go's map order from the stock output

`replaceConst` ranges over the Go map `latticeCells`, whose iteration order is random. Its
only order-dependent effect is `removeEdge`: removing predecessor edges of a block `c`
swap-removes them from `c.Preds` and from the arguments of `c`'s phis, so when the rewiring of
two or more *different* values removes edges into `c`, the final order of `c.Preds` (and, by
the same permutation, of the arguments of `c`'s surviving phis) depends on the order in which
those values are visited. Everything else commutes: value resets, the back indices fixed by the
swaps, rewires of different blocks, phis turned into copies or constants (`docs/PARITY.md`).

So a stock result is reachable iff some order Go can range over the map in reproduces, for
every block `c`, the order in which edges were removed from `c.Preds`. Go's orders
(`smallMapOrders`): with at most 8 keys, the rotations of the insertion order; with more, any
order. `replayOrder` recovers one: per block `c` with removals from at least two values, it
simulates the swap-removes on `c`'s initial predecessor list and compares with the stock
`c.Preds`; for a small map it tries each rotation, for a large one it tries every relative
order of each block's values, picks one candidate per block such that all are consistent with
one global order, and extends that to an order of all keys (insertion order otherwise).
`sccpReplay` runs `replaceConst` in that order; the parity harness compares its result with
the stock output exactly.
-/

namespace GoFV.Opt.Sccp

open GoFV.SSA

/-- The edges a rewiring value removes: `(target block c, position of the edge in c's
initial Preds)`, in removal order. -/
abbrev Removals := Array (ID × Nat)

/-- The blocks `rewireSuccessor` rewires for `v` (in `defBlock` order), with the edges each
removal takes away (`f` is the input function: a block's successors change only through its
own rewiring) and the index of the successor it keeps. -/
def rewires (a : Analysis) (f : Func) (v : ID) : Array (ID × Removals × Nat) := Id.run do
  let some (.const _ _ ai) := a.cell? v | return #[]
  let mut out := #[]
  for b in a.defBlock[v]! do
    let blk := f.getB b
    let ss := blk.succs
    match blk.kind with
    | .If =>
      let r := ai.toInt.toNat
      out := out.push (b, #[(ss[r]!.b, ss[r]!.i)], 1 - r)
    | .JumpTable =>
      let idx := ai.toInt
      if idx < 0 || idx ≥ ss.size then continue
      -- `swapSuccessorsByIdx(0, idx)`, then `removeEdge(1)` until one successor is left
      let mut l := ((List.range ss.size).toArray.swapIfInBounds 0 idx.toNat)
      let mut rs : Removals := #[]
      while h : 1 < l.size do
        let k := l[1]
        rs := rs.push (ss[k]!.b, ss[k]!.i)
        l := (l.set 1 l[l.size - 1]).pop
      out := out.push (b, rs, idx.toNat)
    | _ => pure ()
  return out

/-- Swap-remove the edges `rs` (initial positions) from the list `ps`. -/
def removeAll (ps : Array Nat) (rs : Array Nat) : Array Nat :=
  rs.foldl (init := ps) fun ps p =>
    match ps.idxOf? p with
    | some j => (ps.set! j ps[ps.size - 1]!).pop
    | none => ps

/-- All orders of `xs` (`xs` has few elements: the values removing edges into one block). -/
partial def perms (xs : List ID) : List (List ID) :=
  match xs with
  | [] => [[]]
  | _ => xs.flatMap fun x => (perms (xs.erase x)).map (x :: ·)

/-- Whether the precedence pairs `cs` (`a` before `b`) are acyclic. -/
def acyclic (nodes : List ID) (cs : List (ID × ID)) : Bool := Id.run do
  -- Kahn: repeatedly drop nodes without incoming constraints
  let mut left := nodes
  let mut cs := cs
  for _ in nodes do
    match left.find? (fun n => !cs.any (·.2 == n)) with
    | some n =>
      left := left.erase n
      cs := cs.filter (·.1 != n)
    | none => return false
  return true

/-- Pick one candidate order per block, consistent with one global order (backtracking,
bounded by `budget` steps). -/
partial def choose (nodes : List ID) (cands : List (List (List ID))) (acc : List (ID × ID))
    (budget : Nat) : Option (List (ID × ID)) × Nat :=
  match cands with
  | [] => (some acc, budget)
  | opts :: rest => Id.run do
    let mut budget := budget
    for o in opts do
      if budget == 0 then return (none, 0)
      budget := budget - 1
      let acc' := acc ++ o.zip o.tail
      if acyclic nodes acc' then
        let (r, b) := choose nodes rest acc' budget
        budget := b
        if r.isSome then return (r, budget)
    return (none, budget)

/-- Values per block with removals from at least two of them; the default order already
determines the others. -/
def contested (a : Analysis) (f : Func) : Array (ID × Array (ID × Array Nat)) := Id.run do
  -- per target block: (value, positions it removes, in order)
  let mut byTarget : Array (ID × Array (ID × Array Nat)) := #[]
  for v in a.keys do
    for (_, rs, _) in rewires a f v do
      for (c, p) in rs do
        match byTarget.findIdx? (·.1 == c) with
        | some i =>
          byTarget := byTarget.modify i fun (c, gs) =>
            match gs.findIdx? (·.1 == v) with
            | some j => (c, gs.modify j fun (v, ps) => (v, ps.push p))
            | none => (c, gs.push (v, #[p]))
        | none => byTarget := byTarget.push (c, #[(v, #[p])])
  return byTarget.filter (·.2.size ≥ 2)

/-- `abi.MapGroupSlots`: a Go map with at most this many entries is one group ("small"). -/
def mapGroupSlots : Nat := 8

/-- The orders in which Go can range over `latticeCells` (`internal/runtime/maps`): a small
map fills its group's slots in insertion order (no deletions) and `Iter` starts at a random
slot and wraps around, so its orders are the rotations of the insertion order; a larger map's
order follows hashes of the keys' addresses under a random seed: any order. -/
def smallMapOrders (keys : Array ID) : Option (List (Array ID)) :=
  if keys.size > mapGroupSlots then none
  else some ((List.range keys.size).map fun r => keys.extract r keys.size ++ keys.extract 0 r)

/-- The `latticeCells` order that reproduces `stock`'s predecessor order, if Go can range
over the map in such an order; `none` if no such order does (or the search bound is hit). `f`
is the pass input. -/
def replayOrder (a : Analysis) (f stock : Func) : Option (Array ID) := Id.run do
  let cs := contested a f
  if cs.isEmpty then return some a.keys
  -- the kept successor of each rewired block: maps stock Preds entries to initial edges
  let mut kept : Array (ID × Nat) := #[]
  for v in a.keys do
    for (b, _, k) in rewires a f v do kept := kept.push (b, k)
  -- per contested block: does this relative order of its values give the stock Preds?
  let mut checks : Array (Array ID → Bool) := #[]
  for (c, gs) in cs do
    let init := (List.range (f.getB c).preds.size).toArray
    let want := (stock.getB c).preds.map fun e =>
      let k := ((kept.find? (·.1 == e.b)).map (·.2)).getD e.i
      ((f.getB e.b).succs[k]?.map (·.i)).getD (f.getB c).preds.size
    checks := checks.push fun o =>
      let o := o.filter fun v => gs.any (·.1 == v)
      removeAll init (o.flatMap fun v => ((gs.find? (·.1 == v)).map (·.2)).getD #[]) == want
  if let some rots := smallMapOrders a.keys then
    return rots.find? fun o => checks.all (· o)
  -- large map: every order; search the relative orders per contested block
  let mut cands : List (List (List ID)) := []
  for h : i in [0:cs.size] do
    let gs := cs[i].2
    if gs.size > 8 then return none
    let ok := (perms (gs.map (·.1)).toList).filter fun o => checks[i]! o.toArray
    if ok.isEmpty then return none
    cands := cands ++ [ok]
  let nodes := (cs.flatMap (·.2.map (·.1))).toList.eraseDups
  let (some cons, _) := choose nodes cands [] 100000 | return none
  -- linear extension of the constraints, otherwise insertion order
  let mut out := #[]
  let mut left := a.keys.toList
  let mut cons := cons
  for _ in a.keys do
    let some n := left.find? (fun n => !cons.any (·.2 == n)) | return none
    out := out.push n
    left := left.erase n
    cons := cons.filter (·.1 != n)
  return some out

end GoFV.Opt.Sccp

namespace GoFV.Opt

open GoFV.SSA GoFV.Rules

/-- `sccp` with the `latticeCells` order recovered from the stock output `stock`
(`Sccp.replayOrder`; insertion order if none reproduces it). -/
def sccpReplay (env : PassEnv) (f stock : Func) : Except String PassOut := do
  let rw ← RwEnv.ofPassEnv env
  let a ← Sccp.analyze rw env.tables f
  let order := (Sccp.replayOrder a f stock).getD a.keys
  return { func := Sccp.replace a order, tables := a.tables }

end GoFV.Opt

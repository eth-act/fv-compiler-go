import Std.Data.HashMap.Basic
import Std.Data.HashSet.Basic

/-!
# prove: partially ordered sets of SSA values (`poset.go`)

A verbatim port of `poset`: a forest of DAGs of nodes with at most two children (extra nodes
for fan-out, side chosen by `(i1^i2)&1`), values mapped to nodes (aliases share a node),
non-equality facts keyed by node index, and an undo stack. The answers of `Ordered`/`Equal`/
`NonEqual` and the success bit of the `Set*` operations depend on the order facts were added
(`docs/PASSES.md`, prove, "Poset is history-dependent"), so the structure is replicated
exactly. Values are their IDs. Differences from Go that are not observable:

- `values` is a hash map; `aliasnodes` pushes its `undoAliasNode` records in hash order instead
  of Go's random map order (each record restores a distinct key, so the order is irrelevant);
- `noneq` (Go: a bitset per larger index) is the set of pairs `(larger, smaller)`;
- Go's `panic`s on misuse are not replicated (prove never triggers them).
-/

namespace GoFV.Opt.Prove

/-- `posetEdge`: target node index `<< 1 | strict`; `0` is the empty edge. -/
abbrev PEdge := Nat

@[inline] def newedge (t : Nat) (strict : Bool) : PEdge := t * 2 + (if strict then 1 else 0)
@[inline] def PEdge.target (e : PEdge) : Nat := e / 2
@[inline] def PEdge.strict (e : PEdge) : Bool := e % 2 == 1

/-- `posetNode`. -/
structure PNode where
  l : PEdge := 0
  r : PEdge := 0
  deriving Inhabited, Repr, DecidableEq

/-- `posetUndo`, one constructor per `undoType`. -/
inductive PUndo where
  | checkpoint
  | setChl (idx : Nat) (e : PEdge)
  | setChr (idx : Nat) (e : PEdge)
  /-- Forget that node `i1` (the larger index) is non-equal to `i2`. -/
  | nonEqual (i1 i2 : Nat)
  /-- Remove the last node, created for value `id` (`0`: an extra node). -/
  | newNode (id idx : Nat)
  /-- Point value `id` back at node `prev` (`0`: it was born as an alias, delete it). -/
  | aliasNode (id prev : Nat)
  | newRoot (idx : Nat)
  | changeRoot (idx : Nat) (e : PEdge)
  | mergeRoot (idx : Nat)
  deriving Inhabited, Repr

/-- `poset`. -/
structure Poset where
  lastidx : Nat := 0
  values : Std.HashMap Nat Nat := {}
  nodes : Array PNode := #[{}]
  roots : Array Nat := #[]
  noneq : Std.HashSet (Nat × Nat) := {}
  undo : Array PUndo := #[]
  deriving Inhabited

namespace Poset

@[inline] def node (po : Poset) (i : Nat) : PNode := po.nodes[i]?.getD {}
@[inline] def setchl (po : Poset) (i : Nat) (e : PEdge) : Poset :=
  { po with nodes := po.nodes.modify i fun n => { n with l := e } }
@[inline] def setchr (po : Poset) (i : Nat) (e : PEdge) : Poset :=
  { po with nodes := po.nodes.modify i fun n => { n with r := e } }
@[inline] def upush (po : Poset) (u : PUndo) : Poset := { po with undo := po.undo.push u }

/-- `po.lookup(n)`. -/
@[inline] def lookup (po : Poset) (n : Nat) : Option Nat := po.values.get? n

/-- `po.newnode(n)` (`n = none`: an extra node). -/
def newnode (po : Poset) (n : Option Nat) : Poset × Nat :=
  let i := po.lastidx + 1
  let po := { po with lastidx := i, nodes := po.nodes.push {} }
  match n with
  | some id => ({ po with values := po.values.insert id i }.upush (.newNode id i), i)
  | none => (po.upush (.newNode 0 i), i)

/-- `po.addchild(i1, i2, strict)`. -/
def addchild (po : Poset) (i1 i2 : Nat) (strict : Bool) : Poset :=
  let n := po.node i1
  let e2 := newedge i2 strict
  if n.l == 0 then (po.setchl i1 e2).upush (.setChl i1 0)
  else if n.r == 0 then (po.setchr i1 e2).upush (.setChr i1 0)
  else
    let (po, extra) := po.newnode none
    if (i1 ^^^ i2) &&& 1 != 0 then
      let po := (po.setchl extra n.r).setchr extra e2
      (po.setchr i1 (newedge extra false)).upush (.setChr i1 n.r)
    else
      let po := (po.setchl extra n.l).setchr extra e2
      (po.setchl i1 (newedge extra false)).upush (.setChl i1 n.l)

/-- `po.aliasnewnode(n1, n2)`. -/
def aliasnewnode (po : Poset) (n1 n2 : Nat) : Poset :=
  let i1 := (po.lookup n1).getD 0
  { po with values := po.values.insert n2 i1 }.upush (.aliasNode n2 0)

/-- `po.aliasnodes(n1, i2s)`. -/
def aliasnodes (po : Poset) (n1 : Nat) (i2s : Array Bool) : Poset := Id.run do
  let i1 := (po.lookup n1).getD 0
  let test (i : Nat) : Bool := i2s[i]?.getD false
  let mut po := po
  for idx in [0:po.nodes.size] do
    if idx == i1 then continue
    let n := po.node idx
    let l := n.l
    let r := n.r
    if test l.target then
      po := (po.setchl idx (newedge i1 l.strict)).upush (.setChl idx l)
    if test r.target then
      po := (po.setchr idx (newedge i1 r.strict)).upush (.setChr idx r)
    if test idx then
      if l != 0 && !test l.target then po := po.addchild i1 l.target l.strict
      if r != 0 && !test r.target then po := po.addchild i1 r.target r.strict
      po := ((po.setchl idx 0).setchr idx 0).upush (.setChl idx l) |>.upush (.setChr idx r)
  let moved := po.values.fold (init := #[]) fun acc k v => if test v then acc.push (k, v) else acc
  for (k, v) in moved do
    po := { po with values := po.values.insert k i1 }.upush (.aliasNode k v)
  return po

def isroot (po : Poset) (r : Nat) : Bool := po.roots.contains r

def changeroot (po : Poset) (oldr newr : Nat) : Poset :=
  match po.roots.idxOf? oldr with
  | some i => { po with roots := po.roots.set! i newr }
  | none => po

def removeroot (po : Poset) (r : Nat) : Poset :=
  match po.roots.idxOf? r with
  | some i => { po with roots := po.roots.eraseIdx! i }
  | none => po

/-- `po.reaches(i1, i2, strict)`: `po.dfs(i1, strict, n == i2)`. -/
def reaches (po : Poset) (i1 i2 : Nat) (strict : Bool) : Bool := Id.run do
  let n := po.lastidx + 1
  let bound := 4 * n + 4
  let mut closed := Array.replicate n false
  let mut opn : Array Nat := #[i1]
  if strict then
    let mut next : Array Nat := #[]
    for _ in [0:bound] do
      if opn.isEmpty then break
      let i := opn.back!
      opn := opn.pop
      if closed[i]! then continue
      closed := closed.set! i true
      let nd := po.node i
      if nd.l != 0 then
        if nd.l.strict then next := next.push nd.l.target else opn := opn.push nd.l.target
      if nd.r != 0 then
        if nd.r.strict then next := next.push nd.r.target else opn := opn.push nd.r.target
    opn := next
    closed := Array.replicate n false
  for _ in [0:bound] do
    if opn.isEmpty then break
    let i := opn.back!
    opn := opn.pop
    if closed[i]! then continue
    if i == i2 then return true
    closed := closed.set! i true
    let nd := po.node i
    if nd.l != 0 then opn := opn.push nd.l.target
    if nd.r != 0 then opn := opn.push nd.r.target
  return false

/-- `po.findroot(i)` (`0` where Go panics). -/
def findroot (po : Poset) (i : Nat) : Nat :=
  (po.roots.find? fun r => po.reaches r i false).getD 0

/-- `po.mergeroot(r1, r2)`. -/
def mergeroot (po : Poset) (r1 r2 : Nat) : Poset :=
  let (po, r) := po.newnode none
  let po := (po.setchl r (newedge r1 false)).setchr r (newedge r2 false)
  ((po.changeroot r1 r).removeroot r2).upush (.mergeRoot r)

/-- `po.findpaths1(cur, dst, seen, path)`; `fuel` bounds the depth (each call marks a new node
seen). -/
def findpaths1 (po : Poset) (dst : Nat) : Nat → Nat → Array Bool → Array Bool →
    Array Bool × Array Bool
  | 0, _, seen, path => (seen, path)
  | fuel + 1, cur, seen, path =>
    if cur == dst then (seen, path) else
    let seen := seen.set! cur true
    let l := (po.node cur).l.target
    let r := (po.node cur).r.target
    let (seen, path) := if !seen[l]! then findpaths1 po dst fuel l seen path else (seen, path)
    let (seen, path) := if !seen[r]! then findpaths1 po dst fuel r seen path else (seen, path)
    let path := if path[l]! || path[r]! then path.set! cur true else path
    (seen, path)

/-- `po.findpaths(cur, dst)`. -/
def findpaths (po : Poset) (cur dst : Nat) : Array Bool :=
  let n := po.lastidx + 1
  let path := (Array.replicate n false).set! dst true
  (findpaths1 po dst (n + 1) cur (Array.replicate n false) path).2

/-- `po.collapsepath(n1, n2)`. -/
def collapsepath (po : Poset) (n1 n2 : Nat) : Bool × Poset :=
  let i1 := (po.lookup n1).getD 0
  let i2 := (po.lookup n2).getD 0
  if po.reaches i1 i2 true then (false, po) else
  let paths := (po.findpaths i1 i2).set! i1 false
  (true, po.aliasnodes n1 paths)

/-- `po.isnoneq(i1, i2)`. -/
def isnoneq (po : Poset) (i1 i2 : Nat) : Bool :=
  if i1 == i2 then false else
  if i1 < i2 then po.noneq.contains (i2, i1) else po.noneq.contains (i1, i2)

/-- `po.setnoneq(n1, n2)`. -/
def setnoneq (po : Poset) (n1 n2 : Nat) : Poset :=
  let (po, i1) := match po.lookup n1 with
    | some i => (po, i)
    | none => let (po, i) := po.newnode (some n1)
              ({ po with roots := po.roots.push i }.upush (.newRoot i), i)
  let (po, i2) := match po.lookup n2 with
    | some i => (po, i)
    | none => let (po, i) := po.newnode (some n2)
              ({ po with roots := po.roots.push i }.upush (.newRoot i), i)
  let (i1, i2) := if i1 < i2 then (i2, i1) else (i1, i2)
  if po.noneq.contains (i1, i2) then po else
  { po with noneq := po.noneq.insert (i1, i2) }.upush (.nonEqual i1 i2)

/-- `po.Ordered(n1, n2)`: `n1 < n2` is known. -/
def ordered (po : Poset) (n1 n2 : Nat) : Bool :=
  match po.lookup n1, po.lookup n2 with
  | some i1, some i2 => i1 != i2 && po.reaches i1 i2 true
  | _, _ => false

/-- `po.OrderedOrEqual(n1, n2)`: `n1 <= n2` is known. -/
def orderedOrEqual (po : Poset) (n1 n2 : Nat) : Bool :=
  match po.lookup n1, po.lookup n2 with
  | some i1, some i2 => i1 == i2 || po.reaches i1 i2 false
  | _, _ => false

/-- `po.Equal(n1, n2)`. -/
def equal (po : Poset) (n1 n2 : Nat) : Bool :=
  match po.lookup n1, po.lookup n2 with
  | some i1, some i2 => i1 == i2
  | _, _ => false

/-- `po.NonEqual(n1, n2)`. -/
def nonEqual (po : Poset) (n1 n2 : Nat) : Bool :=
  match po.lookup n1, po.lookup n2 with
  | some i1, some i2 => po.isnoneq i1 i2 || po.ordered n1 n2 || po.ordered n2 n1
  | _, _ => false

/-- `po.setOrder(n1, n2, strict)`. -/
def setOrder (po : Poset) (n1 n2 : Nat) (strict : Bool) : Bool × Poset :=
  match po.lookup n1, po.lookup n2 with
  | none, none =>
    let (po, i1) := po.newnode (some n1)
    let (po, i2) := po.newnode (some n2)
    let po := { po with roots := po.roots.push i1 }.upush (.newRoot i1)
    (true, po.addchild i1 i2 strict)
  | some i1, none =>
    let (po, i2) := po.newnode (some n2)
    (true, po.addchild i1 i2 strict)
  | none, some i2 =>
    let (po, i1) := po.newnode (some n1)
    if po.isroot i2 then
      let po := (po.changeroot i2 i1).upush (.changeRoot i1 (newedge i2 strict))
      (true, po.addchild i1 i2 strict)
    else
      let r := po.findroot i2
      let (po, extra) := po.newnode none
      let po := (po.changeroot r extra).upush (.changeRoot extra (newedge r false))
      let po := po.addchild extra r false
      let po := po.addchild extra i1 false
      (true, po.addchild i1 i2 strict)
  | some i1, some i2 =>
    if i1 == i2 then (!strict, po) else
    let strict := strict || po.isnoneq i1 i2
    if po.reaches i1 i2 false then
      if strict && !po.reaches i1 i2 true then (true, po.addchild i1 i2 true)
      else (true, po)
    else if po.reaches i2 i1 false then
      if strict then (false, po) else po.collapsepath n2 n1
    else
      let r1 := po.findroot i1
      let r2 := po.findroot i2
      let po := if r1 != r2 then po.mergeroot r1 r2 else po
      (true, po.addchild i1 i2 strict)

/-- `po.SetOrder(n1, n2)`: record `n1 < n2`; `false` on contradiction. -/
@[inline] def setOrderLt (po : Poset) (n1 n2 : Nat) : Bool × Poset := po.setOrder n1 n2 true
/-- `po.SetOrderOrEqual(n1, n2)`: record `n1 <= n2`. -/
@[inline] def setOrderOrEqual (po : Poset) (n1 n2 : Nat) : Bool × Poset :=
  po.setOrder n1 n2 false

/-- `po.SetEqual(n1, n2)`. -/
def setEqual (po : Poset) (n1 n2 : Nat) : Bool × Poset :=
  match po.lookup n1, po.lookup n2 with
  | none, none =>
    let (po, i1) := po.newnode (some n1)
    let po := { po with roots := po.roots.push i1 }.upush (.newRoot i1)
    (true, po.aliasnewnode n1 n2)
  | some _, none => (true, po.aliasnewnode n1 n2)
  | none, some _ => (true, po.aliasnewnode n2 n1)
  | some i1, some i2 =>
    if i1 == i2 then (true, po) else
    if po.isnoneq i1 i2 then (false, po) else
    if po.reaches i1 i2 false then po.collapsepath n1 n2 else
    if po.reaches i2 i1 false then po.collapsepath n2 n1 else
    let r1 := po.findroot i1
    let r2 := po.findroot i2
    let po := if r1 != r2 then po.mergeroot r1 r2 else po
    let i2s := (Array.replicate (po.lastidx + 1) false).set! i2 true
    (true, po.aliasnodes n1 i2s)

/-- `po.SetNonEqual(n1, n2)`. -/
def setNonEqual (po : Poset) (n1 n2 : Nat) : Bool × Poset :=
  match po.lookup n1, po.lookup n2 with
  | some i1, some i2 =>
    if po.isnoneq i1 i2 then (true, po) else
    if po.equal n1 n2 then (false, po) else
    let po := po.setnoneq n1 n2
    let po := if po.reaches i1 i2 false && !po.reaches i1 i2 true then po.addchild i1 i2 true
      else po
    let po := if po.reaches i2 i1 false && !po.reaches i2 i1 true then po.addchild i2 i1 true
      else po
    (true, po)
  | _, _ => (true, po.setnoneq n1 n2)

/-- `po.Checkpoint()`. -/
@[inline] def checkpoint (po : Poset) : Poset := po.upush .checkpoint

/-- `po.Undo()`: undo up to and including the last checkpoint. -/
def undoAll (po : Poset) : Poset := Id.run do
  let mut po := po
  for _ in [0:po.undo.size] do
    let some u := po.undo.back? | break
    po := { po with undo := po.undo.pop }
    match u with
    | .checkpoint => break
    | .setChl idx e => po := po.setchl idx e
    | .setChr idx e => po := po.setchr idx e
    | .nonEqual i1 i2 => po := { po with noneq := po.noneq.erase (i1, i2) }
    | .newNode id idx =>
      if id != 0 then po := { po with values := po.values.erase id }
      po := { po with nodes := po.nodes.extract 0 idx, lastidx := po.lastidx - 1 }
    | .aliasNode id prev =>
      if prev == 0 then po := { po with values := po.values.erase id }
      else po := { po with values := po.values.insert id prev }
    | .newRoot idx => po := po.removeroot idx
    | .changeRoot idx e => po := po.changeroot idx e.target
    | .mergeRoot idx =>
      let n := po.node idx
      po := po.changeroot idx n.l.target
      po := { po with roots := po.roots.push n.r.target }
  return po

end Poset

end GoFV.Opt.Prove

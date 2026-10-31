import GoFV.SSA.Func

/-!
# Sparse (dominator) tree

Port of `ssa/sparsetree.go` (go1.27.3). `newSparseTree(f, parentOf)` scans the postorder
(`f.postorder()`, i.e. the possibly stale cached one, docs/PASSES.md §1.3) and prepends each
block to its parent's child list, so children end up in reverse postorder; `numberBlock` then
assigns entry/exit numbers by a walk of that child/sibling order. Nodes are `SdomNode`
(`GoFV.SSA.Func`), indexed by block ID; blocks outside the tree keep the zero node.
-/

namespace GoFV.SSA.Analysis

/-- `SparseTree`: one node per block ID. -/
abbrev SparseTree := Array SdomNode

/-- `t.numberBlock` over a sibling chain: numbers `c`, its subtree, then its siblings, starting
at the first free number `n`; returns the next free number. `fuel` bounds the depth of the
child/sibling walk (one step per block). -/
def numberChain : Nat → SparseTree → Option ID → Int → SparseTree × Int
  | 0, t, _, n => (t, n)
  | _ + 1, t, none, n => (t, n)
  | fuel + 1, t, some b, n =>
    -- reserve n for entry-1, assign n+1 to entry; n+2 reserved, n+3 next free
    let t := t.modify b fun x => { x with entry := n + 1 }
    let (t, n) := numberChain fuel t (t[b]?.bind (·.child)) (n + 3)
    -- reserve n for exit-1, assign n+1 to exit; n+2 reserved, n+3 next free
    let t := t.modify b fun x => { x with exit := n + 1 }
    numberChain fuel t (t[b]?.bind (·.sibling)) (n + 3)

/-- `t.numberBlock(b, n)`: numbers `b` and its subtree (not its siblings). -/
def numberBlock (t : SparseTree) (b : ID) (n : Int) : SparseTree × Int :=
  let t := t.modify b fun x => { x with entry := n + 1 }
  let (t, n) := numberChain (t.size + 1) t (t[b]?.bind (·.child)) (n + 3)
  let t := t.modify b fun x => { x with exit := n + 1 }
  (t, n + 3)

/-- `newSparseTree(f, parentOf)` with `po = f.postorder()` passed explicitly (the caller decides
whether it is the cached one) and `nb = f.NumBlocks()`. -/
def newSparseTree (nb : Nat) (entry : ID) (po : Array ID) (parentOf : Array (Option ID)) :
    SparseTree :=
  let t : SparseTree := po.foldl (init := Array.replicate nb default) fun t b =>
    match parentOf[b]?.join with
    | some p =>
      let sib := t[p]?.bind (·.child)
      let t := t.modify b fun x => { x with parent := some p, sibling := sib }
      t.modify p fun x => { x with child := some b }
    | none => t
  (numberBlock t entry 1).1

namespace SparseTree

/-- `t.Child(x)`. -/
@[inline] def child (t : SparseTree) (x : ID) : Option ID := t[x]?.bind (·.child)
/-- `t.Sibling(x)`. -/
@[inline] def sibling (t : SparseTree) (x : ID) : Option ID := t[x]?.bind (·.sibling)
/-- `t.Parent(x)`. -/
@[inline] def parent (t : SparseTree) (x : ID) : Option ID := t[x]?.bind (·.parent)
/-- `t.domorder(x)`: the entry number. -/
@[inline] def domorder (t : SparseTree) (x : ID) : Int := (t[x]?.map (·.entry)).getD 0

/-- `t.IsAncestorEq(x, y)`: `x` dominates `y` (reflexively). -/
def isAncestorEq (t : SparseTree) (x y : ID) : Bool :=
  x == y ||
    let xx := t[x]?.getD default
    let yy := t[y]?.getD default
    xx.entry ≤ yy.entry && yy.exit ≤ xx.exit

/-- `t.isAncestor(x, y)`: `x` strictly dominates `y`. -/
def isAncestor (t : SparseTree) (x y : ID) : Bool :=
  x != y &&
    let xx := t[x]?.getD default
    let yy := t[y]?.getD default
    xx.entry < yy.entry && yy.exit < xx.exit

end SparseTree

end GoFV.SSA.Analysis

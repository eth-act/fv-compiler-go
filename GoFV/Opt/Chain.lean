import GoFV.SSA.Sem.Run

/-!
# Chained roots (decision procedure)

`chainedB f B` checks, in every block of `B`, that every two side-effecting roots (priority 2)
are ordered by dependency: it computes the ancestors of each root inside the block
(`ancOf`, a worklist walk over the arguments that are nodes of the block) and checks that of
every two roots one is an ancestor of the other. Its soundness (`GoFV.Proof.Dead.chained_of`)
is in `GoFV.Proof.Pass.DeadChain`; checked passes run it on the blocks they merge.
-/

namespace GoFV.Opt

open GoFV.SSA GoFV.SSA.Sem

/-- `x` is a non-`Phi` value of the block (a node of its schedule, `nodeB_sound`). -/
def nodeB (f : Func) (fb : Block) (x : ID) : Bool :=
  fb.values.contains x && (f.value? x).any (·.op != .Phi)

/-- The arguments of value `x`. -/
def argsV (f : Func) (x : ID) : List ID := ((f.value? x).map (·.args.toList)).getD []

/-- The ancestor walk: `fuel`, the stack, the nodes found so far. -/
def ancW (f : Func) (fb : Block) : Nat → List ID → List ID → List ID
  | 0, _, vis => vis
  | _, [], vis => vis
  | n + 1, y :: st, vis =>
    let new := (argsV f y).filter fun a => nodeB f fb a && !vis.contains a
    ancW f fb n (new ++ st) (new ++ vis)

/-- Nodes of the block that root `r` depends on (found within `|values| + 1` steps per value). -/
def ancOf (f : Func) (fb : Block) (r : ID) : List ID :=
  ancW f fb ((fb.values.size + 1) * (fb.values.size + 1)) [r] []

/-- The priority-2 roots of a block. -/
def roots2 (f : Func) (fb : Block) : List ID :=
  ((schedNodes f fb).toList.filter (·.prio == 2)).map (·.id)

/-- Decides `Chained` (for well-formed `f`, `chained_of`). -/
def chainedB (f : Func) (B : Array ID) : Bool :=
  B.all fun bid =>
    match f.block? bid with
    | none => true
    | some fb =>
      let ancs := (roots2 f fb).map fun r => (r, ancOf f fb r)
      ancs.all fun (y, ay) => ancs.all fun (x, ax) => x == y || ay.contains x || ax.contains y

end GoFV.Opt

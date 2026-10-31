import GoFV.SSA.Func
import GoFV.SSA.Analysis.Dom
import GoFV.SSA.Analysis.Postorder

/-!
# Dominator certificate (the last step of `GoFV.SSA.check`)

Go's `checkFunc` trusts its Lengauer–Tarjan dominators (`Analysis.dominators`). Proving that
algorithm is out of reach, so `check` validates its output instead, by local checks that need
no path reasoning to use:

* a depth for every block of the tree (`Cert.depth`, computed along the reverse postorder, not
  trusted): the entry has depth 0, every other block of depth `k + 1` has an immediate dominator
  of depth `k` (`parentsOK`); `Cert.anc a b` (`a` is `b` or one of its tree ancestors) walks the
  immediate dominators from `b` down to `a`'s depth;
* every successor of a tree block is a tree block other than the entry, and its immediate
  dominator is an ancestor of the edge's source (`edgesOK`) — so the ancestors of a block lie on
  every path to it (`GoFV.Proof.DomCert`);
* every tree block other than the entry has a tree predecessor it is not an ancestor of
  (`rootedOK`);
* every argument (of a `Phi`: argument `i` against predecessor `i`, if that is a tree block) and
  every control of a tree block is defined in an ancestor of the using block (`usesOK`).

These hold for any correct dominator tree, so the certificate never rejects what Go accepts
(`lake exe ssa-check` on the corpus, `docs/contracts/check.md`).
-/

namespace GoFV.SSA.DomCert

/-- Immediate dominators and depths by block ID (`none`: not in the tree). -/
structure Cert where
  idom : Array (Option ID)
  depth : Array (Option Nat)

namespace Cert

/-- The immediate dominator of `b` (`b` itself if none). -/
@[inline] def up (c : Cert) (b : ID) : ID := (c.idom[b]?.join).getD b

/-- `k` steps up the tree from `b`. -/
def walk (c : Cert) : Nat → ID → ID
  | 0, b => b
  | k + 1, b => c.walk k (c.up b)

@[inline] def depthOf (c : Cert) (b : ID) : Option Nat := c.depth[b]?.join

/-- `b` is in the tree. -/
@[inline] def inTree (c : Cert) (b : ID) : Bool := (c.depthOf b).isSome

/-- `a` is `b` or a tree ancestor of `b`. -/
def anc (c : Cert) (a b : ID) : Bool :=
  match c.depthOf a, c.depthOf b with
  | some da, some db => da ≤ db && c.walk (db - da) b == a
  | _, _ => false

end Cert

/-- The certificate of `f`: Go's immediate dominators and depths along the reverse postorder
(a dominator precedes the blocks it dominates). -/
def make (f : Func) : Cert := Id.run do
  let idom := Analysis.dominators f
  let mut depth : Array (Option Nat) := (Array.replicate (f.bidLast + 1) none).set! f.entry (some 0)
  for b in (Analysis.postorder f).reverse do
    if b == f.entry then continue
    match idom[b]?.join with
    | some d => depth := depth.set! b ((depth[d]?.join).map (· + 1))
    | none => pure ()
  return { idom, depth }

/-- The block a value is defined in (0, never a block, if it is not in the function). -/
@[inline] def blockOf (f : Func) (a : ID) : ID := ((f.value? a).map (·.block)).getD 0

/-- The entry is the root; every other tree block's immediate dominator is one level up. -/
def parentsOK (c : Cert) (entry : ID) : Bool :=
  c.depthOf entry == some 0 &&
  (List.range c.depth.size).all fun b =>
    match c.depthOf b with
    | none => true
    | some 0 => b == entry
    | some (k + 1) =>
      match c.idom[b]?.join with
      | some d => c.depthOf d == some k
      | none => false

/-- Successors of tree blocks are tree blocks other than the entry, whose immediate dominator
is an ancestor of the edge's source. -/
def edgesOK (c : Cert) (f : Func) : Bool :=
  f.blocks.all fun bid =>
    !c.inTree bid ||
    match f.block? bid with
    | none => false
    | some b => b.succs.all fun e => e.b != f.entry && c.inTree e.b && c.anc (c.up e.b) bid

/-- Every tree block other than the entry has a tree predecessor it is not an ancestor of. -/
def rootedOK (c : Cert) (f : Func) : Bool :=
  f.blocks.all fun bid =>
    !c.inTree bid || bid == f.entry ||
    match f.block? bid with
    | none => false
    | some b => b.preds.any fun e => c.inTree e.b && !c.anc bid e.b

/-- Uses in tree blocks are dominated by their definitions. -/
def usesOK (c : Cert) (f : Func) : Bool :=
  f.blocks.all fun bid =>
    !c.inTree bid ||
    match f.block? bid with
    | none => false
    | some b =>
      b.values.all (fun vid =>
        match f.value? vid with
        | none => false
        | some v =>
          if v.op == .Phi then
            (v.args.zip b.preds).all fun (a, e) => !c.inTree e.b || c.anc (blockOf f a) e.b
          else v.args.all fun a => c.anc (blockOf f a) bid) &&
      b.controls.all fun x => c.anc (blockOf f x) bid

@[inline] def ensure (ok : Bool) (msg : String) : Except String Unit :=
  if ok then pure () else throw msg

/-- Validate the dominator tree of `f` and every use against it. -/
def check (f : Func) : Except String Unit := do
  let c := make f
  ensure (parentsOK c f.entry) "domcert: dominator tree depths inconsistent"
  ensure (edgesOK c f) "domcert: an edge's target has an immediate dominator not above its source"
  ensure (rootedOK c f) "domcert: a block dominates all its predecessors"
  ensure (usesOK c f) "domcert: a use is not dominated by its definition"

end GoFV.SSA.DomCert

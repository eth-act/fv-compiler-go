import GoFV.SSA.Func
import GoFV.SSA.Analysis.Dom
import GoFV.SSA.Analysis.Postorder

/-!
# Dominator certificate (the last step of `GoFV.SSA.check`)

Go's `checkFunc` trusts its Lengauer–Tarjan dominators (`Analysis.dominators`). Proving that
algorithm is out of reach, so `check` validates its output instead, by local checks that need
no path reasoning to use:

* a depth for every block of the tree (`Cert.depth`, computed along the DFS preorder, not
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

The certificate's immediate dominators come from the textbook Lengauer–Tarjan algorithm
(`ltIdom`: Go's `dominatorsLTOrig`, but each bucket is emptied after use; Go never empties
them and rescans them once per DFS child of their block, which made `Analysis.dominators` the
largest part of the certificate on big functions, issue #147). Any correct algorithm gives the
same tree, and the checks above validate it, so nothing about it is proven. Compiled code skips
the `cfgView` copy (`make_eq_ofView`) and checks the non-`Phi` uses of a block against one
ancestor path shared along the block list (`usesOK_eq_usesOKFast`) instead of walking the tree
per use.
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

/-- The control-flow graph of `f` alone (entry, block list, edges): what the dominator tree
depends on, so functions with the same graph get the same certificate. -/
def cfgView (f : Func) : Func :=
  { (default : Func) with
    entry := f.entry, bidLast := f.bidLast, blocks := f.blocks
    blockTab := f.blockTab.map (Option.map fun b =>
      { (default : Block) with id := b.id, succs := b.succs, preds := b.preds }) }

/-- The successor edges of block `b` (none if `b` is not a block). -/
@[inline] def cfgSuccs (f : Func) (b : ID) : Array Edge := ((f.block? b).map (·.succs)).getD #[]

/-- The predecessor edges of block `b` (none if `b` is not a block). -/
@[inline] def cfgPreds (f : Func) (b : ID) : Array Edge := ((f.block? b).map (·.preds)).getD #[]

/-- Go's `dfsOrig` over the successor function `succs` (blocks `< nb`, `edges` successor edges
in all): numbers the reachable blocks 1..n in DFS preorder. Returns `(n, semi, vertex, parent)`:
`semi[v]` is `v`'s number (0: unreached), `vertex[i]` the block numbered `i`, `parent` the DFS
tree parent. -/
def dfs (nb entry edges : Nat) (succs : ID → Array Edge) :
    Nat × Array Nat × Array Nat × Array Nat := Id.run do
  let mut semi := Array.replicate nb 0
  let mut vertex := Array.replicate (nb + 1) 0
  let mut parent := Array.replicate nb 0
  let mut n := 0
  let mut s : Array ID := #[entry]
  -- a block is pushed once per incoming edge from a newly numbered block, plus the entry
  for _ in [0:edges + 2] do
    let some v := s.back? | break
    s := s.pop
    if semi.getD v 1 != 0 then continue
    n := n + 1
    semi := semi.set! v n
    vertex := vertex.set! n v
    for e in succs v do
      if semi.getD e.b 1 == 0 then
        s := s.push e.b
        parent := parent.set! e.b v
  return (n, semi, vertex, parent)

/-- Lengauer–Tarjan, simple version, as in Go's `dominatorsLTOrig` except that a bucket is
emptied once processed. Returns the immediate dominators by block ID (`none`: the entry or
unreachable), the DFS preorder `vertex` and the number `n` of reachable blocks. -/
def ltIdom (nb entry edges : Nat) (succs preds : ID → Array Edge) :
    Array (Option ID) × Array Nat × Nat := Id.run do
  let (n, semi, vertex, parent) := dfs nb entry edges succs
  let mut semi := semi
  let mut label := Array.range nb
  let mut ancestor := Array.replicate nb 0
  let mut bucketHead := Array.replicate nb 0
  let mut bucketLink := Array.replicate nb 0
  let mut idom : Array (Option ID) := Array.replicate nb none
  for k in [0:n - 1] do
    let i := n - k
    let w := vertex[i]!
    -- step 2
    for e in preds w do
      let v := e.b
      if semi.getD v 0 == 0 then continue
      let (u, a, l) := Analysis.evalOrig nb semi v ancestor label
      ancestor := a
      label := l
      if semi[u]! < semi[w]! then semi := semi.set! w semi[u]!
    -- add w to bucket[vertex[semi[w]]]
    let vsw := vertex[semi[w]!]!
    bucketLink := bucketLink.set! w bucketHead[vsw]!
    bucketHead := bucketHead.set! vsw w
    -- link(parent[w], w)
    let pw := parent[w]!
    ancestor := ancestor.set! w pw
    -- step 3: each block is added to one bucket once, so `nb` steps suffice
    let mut v := bucketHead[pw]!
    for _ in [0:nb] do
      if v == 0 then break
      let (u, a, l) := Analysis.evalOrig nb semi v ancestor label
      ancestor := a
      label := l
      idom := idom.set! v (some (if semi[u]! < semi[v]! then u else pw))
      v := bucketLink[v]!
    bucketHead := bucketHead.set! pw 0
  -- step 4
  for i in [2:n + 1] do
    let w := vertex[i]!
    let d := (idom[w]!).getD 0
    if d != vertex[semi[w]!]! then idom := idom.set! w idom[d]!
  return (idom, vertex, n)

/-- The certificate of a control-flow graph (blocks `< nb`, block list `blocks`): `ltIdom`'s
immediate dominators and depths along its DFS preorder (an immediate dominator is a DFS tree
ancestor, so it is numbered first). -/
def ofCfg (nb entry : Nat) (blocks : Array ID) (succs preds : ID → Array Edge) : Cert := Id.run do
  let edges := blocks.foldl (fun n b => n + (succs b).size) 0
  let (idom, vertex, n) := ltIdom nb entry edges succs preds
  let mut depth : Array (Option Nat) := (Array.replicate nb none).set! entry (some 0)
  for i in [2:n + 1] do
    let b := vertex[i]!
    match idom[b]?.join with
    | some d => depth := depth.set! b ((depth[d]?.join).map (· + 1))
    | none => pure ()
  return { idom, depth }

/-- The certificate of the control-flow graph of `v`. -/
def ofView (v : Func) : Cert := ofCfg (v.bidLast + 1) v.entry v.blocks (cfgSuccs v) (cfgPreds v)

/-- The certificate of `f`. -/
def make (f : Func) : Cert := ofView (cfgView f)

private theorem block?_cfgView (f : Func) (b : ID) :
    (cfgView f).block? b = (f.block? b).map fun x =>
      { (default : Block) with id := x.id, succs := x.succs, preds := x.preds } := by
  simp only [cfgView, Func.block?, Array.getElem?_map]
  cases f.blockTab[b]? with
  | none => rfl
  | some o => cases o <;> rfl

private theorem cfgSuccs_cfgView (f : Func) : cfgSuccs (cfgView f) = cfgSuccs f := by
  funext b
  simp only [cfgSuccs, block?_cfgView, Option.map_map]
  rfl

private theorem cfgPreds_cfgView (f : Func) : cfgPreds (cfgView f) = cfgPreds f := by
  funext b
  simp only [cfgPreds, block?_cfgView, Option.map_map]
  rfl

/-- Compiled, `make` reads `f`'s graph in place, without the `cfgView` copy. -/
@[csimp] theorem make_eq_ofView : @make = @ofView := by
  funext f
  unfold make ofView
  rw [cfgSuccs_cfgView, cfgPreds_cfgView]
  rfl

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

/-! ### `usesOK` with a shared ancestor path (compiled form) -/

/-- The uses of block `b` of `f`, `anc a` deciding that `a` is an ancestor of `b` (`usesOK`'s
test for one tree block). -/
@[inline] def blockUsesOK (c : Cert) (f : Func) (anc : ID → Bool) (b : Block) : Bool :=
  b.values.all (fun vid =>
    match f.value? vid with
    | none => false
    | some v =>
      if v.op == .Phi then
        (v.args.zip b.preds).all fun (a, e) => !c.inTree e.b || c.anc (blockOf f a) e.b
      else v.args.all fun a => anc (blockOf f a)) &&
  b.controls.all fun x => anc (blockOf f x)

/-- Writes `x, c.up x, c.up² x, …` into `p` at `k, k - 1, …, 0`, stopping early at the first
position below `lim` that already holds the value to write (`p` holds an ancestor path up to
`lim`, so the rest of it agrees too). -/
def fixPath (c : Cert) (lim : Nat) : Nat → ID → Array ID → Array ID
  | 0, x, p => if 0 < lim && p.getD 0 0 == x then p else p.set! 0 x
  | k + 1, x, p =>
    if k + 1 < lim && p.getD (k + 1) 0 == x then p else fixPath c lim k (c.up x) (p.set! (k + 1) x)

/-- `usesOK` over the blocks `l`; `p` holds an ancestor path at positions `< lim`
(`PathOK`). The ancestor test of a tree block of depth `d` reads its path, which `fixPath`
builds from the previous block's path. -/
def usesGo (c : Cert) (f : Func) : List ID → Array ID → Nat → Bool
  | [], _, _ => true
  | bid :: bs, p, lim =>
    match c.depthOf bid with
    | none => usesGo c f bs p lim
    | some d =>
      match f.block? bid with
      | none => false
      | some b =>
        if d < p.size then
          let p := fixPath c lim d bid p
          blockUsesOK c f (fun a => match c.depthOf a with
              | some da => da ≤ d && p.getD da 0 == a
              | none => false) b &&
            usesGo c f bs p (d + 1)
        else blockUsesOK c f (fun a => c.anc a bid) b && usesGo c f bs p lim

/-- `usesOK`, the ancestor tests of non-`Phi` uses reading one shared path; functions with few
blocks (shallow trees) keep the per-use walk, which needs no path array. -/
def usesOKFast (c : Cert) (f : Func) : Bool :=
  if f.blocks.size < 32 then usesOK c f
  else usesGo c f f.blocks.toList (Array.replicate c.depth.size 0) 0

namespace Cert

private theorem walk_succ' (c : Cert) : ∀ (k : Nat) (b : ID), c.walk (k + 1) b = c.up (c.walk k b)
  | 0, _ => rfl
  | k + 1, b => walk_succ' c k (c.up b)

private theorem walk_add' (c : Cert) (k : Nat) : ∀ (j : Nat) (b : ID), c.walk (k + j) b = c.walk k (c.walk j b)
  | 0, _ => rfl
  | j + 1, b => walk_add' c k j (c.up b)

end Cert

/-- `p` holds `x`'s ancestor path of depth `d` below `lim`. -/
def PathOK (c : Cert) (p : Array ID) (lim : Nat) : Prop :=
  ∃ d x, lim ≤ d + 1 ∧ ∀ j < lim, p[j]? = some (c.walk (d - j) x)

private theorem fixPath_spec (c : Cert) {lim d : Nat} {x0 : ID} (hlim : lim ≤ d + 1) :
    ∀ (k : Nat) (x : ID) (p : Array ID), (∀ j < lim, j ≤ k → p[j]? = some (c.walk (d - j) x0)) →
      k < p.size →
      (fixPath c lim k x p).size = p.size ∧
      (∀ j ≤ k, (fixPath c lim k x p)[j]? = some (c.walk (k - j) x)) ∧
      (∀ j, k < j → (fixPath c lim k x p)[j]? = p[j]?)
  | 0, x, p, hp, hk => by
    rw [fixPath.eq_1]
    by_cases hc : (decide (0 < lim) && p.getD 0 0 == x) = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      obtain ⟨hl, hx⟩ := hc
      have hx0 := hp 0 hl (Nat.le_refl _)
      rw [Array.getD_eq_getD_getElem?, hx0, Option.getD_some] at hx
      subst hx
      refine ⟨rfl, fun j hj => ?_, fun _ _ => rfl⟩
      obtain rfl : j = 0 := by omega
      exact hx0
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
      refine ⟨by simp, fun j hj => ?_, fun j hj => ?_⟩
      · obtain rfl : j = 0 := by omega
        simp [Array.set!, hk]; rfl
      · simp only [Array.set!]
        rw [Array.getElem?_setIfInBounds_ne (by omega)]
  | k + 1, x, p, hp, hk => by
    rw [fixPath.eq_2]
    by_cases hc : (decide (k + 1 < lim) && p.getD (k + 1) 0 == x) = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      obtain ⟨hl, hx⟩ := hc
      have hx0 := hp (k + 1) hl (Nat.le_refl _)
      rw [Array.getD_eq_getD_getElem?, hx0, Option.getD_some] at hx
      subst hx
      refine ⟨rfl, fun j hj => ?_, fun _ _ => rfl⟩
      rw [hp j (by omega) hj, ← Cert.walk_add', show k + 1 - j + (d - (k + 1)) = d - j by omega]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
      have hp' : ∀ j < lim, j ≤ k → (p.set! (k + 1) x)[j]? = some (c.walk (d - j) x0) := by
        intro j hj hjk
        simp only [Array.set!]
        rw [Array.getElem?_setIfInBounds_ne (by omega)]
        exact hp j hj (by omega)
      obtain ⟨h1, h2, h3⟩ := fixPath_spec c hlim k (c.up x) (p.set! (k + 1) x) hp'
        (by simp; omega)
      refine ⟨by rw [h1]; simp, fun j hj => ?_, fun j hj => ?_⟩
      · rcases Nat.lt_or_ge k j with hkj | hkj
        · obtain rfl : j = k + 1 := by omega
          rw [h3 _ hkj]
          simp [Array.set!, hk]; rfl
        · rw [h2 j hkj, show k + 1 - j = (k - j) + 1 by omega]
          rfl
      · rw [h3 j (by omega)]
        simp only [Array.set!]
        rw [Array.getElem?_setIfInBounds_ne (by omega)]

private theorem usesGo_eq (c : Cert) (f : Func) : ∀ (l : List ID) (p : Array ID) (lim : Nat),
    PathOK c p lim → usesGo c f l p lim = l.all fun bid =>
      !c.inTree bid ||
      match f.block? bid with
      | none => false
      | some b => blockUsesOK c f (fun a => c.anc a bid) b
  | [], _, _, _ => rfl
  | bid :: bs, p, lim, hp => by
    rw [List.all_cons]
    unfold usesGo
    cases hd : c.depthOf bid with
    | none =>
      simp only [Cert.inTree, hd, Option.isSome_none, Bool.not_false, Bool.true_or, Bool.true_and]
      exact usesGo_eq c f bs p lim hp
    | some d =>
      simp only [Cert.inTree, hd, Option.isSome_some, Bool.not_true, Bool.false_or]
      cases f.block? bid with
      | none => rfl
      | some b =>
        simp only
        split
        · rename_i hds
          obtain ⟨d0, x0, hl, hp0⟩ := hp
          obtain ⟨h1, h2, -⟩ := fixPath_spec c hl d bid p
            (fun j hj _ => hp0 j hj) hds
          have hanc : (fun a => match c.depthOf a with
              | some da => da ≤ d && (fixPath c lim d bid p).getD da 0 == a
              | none => false) = fun a => c.anc a bid := by
            funext a
            unfold Cert.anc
            rw [hd]
            cases c.depthOf a with
            | none => rfl
            | some da =>
              simp only
              by_cases hda : da ≤ d
              · rw [Array.getD_eq_getD_getElem?, h2 da hda, Option.getD_some]
              · simp [hda]
          rw [hanc, usesGo_eq c f bs _ (d + 1) ⟨d, bid, Nat.le_refl _, fun j hj => h2 j (by omega)⟩]
          rfl
        · rw [usesGo_eq c f bs p lim hp]
          rfl

/-- Compiled, `usesOK` reads one ancestor path per block instead of walking the tree per use. -/
@[csimp] theorem usesOK_eq_usesOKFast : @usesOK = @usesOKFast := by
  funext c f
  unfold usesOKFast
  split
  · rfl
  · rw [usesGo_eq c f _ _ 0 ⟨0, 0, Nat.zero_le _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩,
      Array.all_toList]
    rfl

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

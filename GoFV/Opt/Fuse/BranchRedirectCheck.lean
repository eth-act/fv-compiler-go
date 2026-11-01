import GoFV.Opt.Fuse.BranchRedirect
import GoFV.Opt.Fuse.ComparisonsCheck
import GoFV.Opt.ProveCheck.Decide

/-!
# fuseBranchRedirect, checked

`Redir.relB tabs f g st` validates one redirect of `fuseBranchRedirect` (`redirect f b k out`)
at the site `st` (`siteOf`): predecessor `k` of the `If` block `b` is the edge `p → b` (`p`'s
successor `pi`, `p` an `If` block with control `cp`), and `p` now jumps to `child = b.Succs[out]`
directly.

- **The decision** (`decideOK`): prove's validator (`ProveCheck.decides`) decides that `b`'s
  control `ctl` is `.bool (out == 0)` under the path fact `(cp, pi == 0)` (what `p`'s control
  holds when `p` leaves along `pi`), and the same fact on `ctl` if `ctl` is the same term as `cp`
  (`sameTerm`). The term nodes the decision reads (`termClosure` of `cp` and `ctl`) are listed with
  their term arguments after them (`topoOK`), so their values are their registers' (the proof's
  induction).
- **The shape** (`shapeOK`): `b` holds no values, or only `ctl`, a term (not a `Phi`) that does
  not read itself and that no value and no other block's control reads (`unreadOK`); `child` is
  neither `b` nor the entry.
- **The result**: every block table entry is `expect`ed: every successor edge goes through `r`
  (`p → b` becomes `p → child` at `child`'s new last index `cn`; `b`'s last predecessor edge
  takes index `k`), `b` loses predecessor `k` by swap-removal, `child` gains `⟨p, pi⟩`; the
  untouched entries are compared by pointer first (`tabEq`). Every `Phi` of `child` gains its
  argument along `b → child` (index `ai`); every other value keeps what is read (`sameW`).

No `check` of the result is needed (issue #147): the proof derives well-formedness and use
dominance from the relation. `fuseBranchRedirectChecked` is `fuseBranchRedirect` with every
redirect checked (a rejected one is skipped) and with structural loops; the soundness proof is
`GoFV.Proof.FuseRedirect.fuseBranchRedirectChecked_ok`.
-/

namespace GoFV.Opt.Fuse

open GoFV.SSA GoFV.Opt.Prove

namespace Redir

/-- Depth of the range analysis and of `Not` nesting in the redirect decision. -/
def fuel : Nat := 4

/-- A redirect site (see the module doc). -/
structure Site where
  b : ID
  k : Nat
  out : Nat
  p : ID
  pi : Nat
  child : ID
  ai : Nat
  /-- the last predecessor index of `b` -/
  n : Nat
  /-- the source of `b`'s last predecessor edge -/
  q : ID
  /-- `child`'s predecessor count in `f` (the index of the new edge) -/
  cn : Nat
  cp : ID
  ctl : ID
  deriving Inhabited

/-- The site of `redirect f b k out`. -/
def siteOf (f : Func) (b : ID) (k out : Nat) : Site :=
  let B := f.getB b
  let pk := B.preds[k]!
  let se := B.succs[out]!
  { b, k, out, p := pk.b, pi := pk.i, child := se.b, ai := se.i, n := B.preds.size - 1,
    q := B.preds[B.preds.size - 1]!.b, cn := (f.getB se.b).preds.size,
    cp := (f.getB pk.b).controls[0]!, ctl := B.controls[0]! }

namespace Site

variable (st : Site)

/-- The edges after the redirect: `p → b` (at `k`) goes to `child` at `cn`; `b`'s last edge
moves to `k`. -/
def r (e : Edge) : Edge :=
  if e.b == st.b && e.i == st.k then ⟨st.child, st.cn⟩
  else if e.b == st.b && e.i == st.n then ⟨st.b, st.k⟩ else e

/-- The block table entry of `x` in `g`, from its entry `X` in `f`. -/
def expect (x : ID) (X : Block) : Block :=
  let X := { X with succs := X.succs.map st.r }
  let X := if x == st.b then { X with preds := Cmp.swapRemove X.preds st.k } else X
  if x == st.child then { X with preds := X.preds.push ⟨st.p, st.pi⟩ } else X

/-- The blocks whose table entries the redirect replaces. -/
def touched (x : ID) : Bool := x == st.b || x == st.p || x == st.child || x == st.q

/-- Block `x`'s entry in `g` is `expect`ed. -/
def blockOK (f g : Func) (x : ID) : Bool :=
  match f.block? x, g.block? x with
  | some X, some X' => X' == st.expect x X
  | _, _ => false

/-- `b`'s control, when it is `b`'s value: a term that does not read itself. -/
def ctlOK (f : Func) : Bool :=
  match f.value? st.ctl with
  | some v => v.id == st.ctl && RewriteCheck.termOp v.op && !v.args.contains st.ctl
  | none => false

/-- The shape of `b`, `p` and `child` in `f`. -/
def shapeOK (f : Func) : Bool :=
  match f.block? st.b, f.block? st.p, f.block? st.child with
  | some B, some P, some C =>
    f.blocks.contains st.b && st.p != st.b && st.child != st.b && st.child != f.entry &&
      st.out < 2 && st.k ≤ st.n &&
      B.kind == .If && B.controls == #[st.ctl] && B.succs.size == 2 &&
      B.succs[st.out]? == some ⟨st.child, st.ai⟩ && B.preds.size == st.n + 1 &&
      B.preds[st.k]? == some ⟨st.p, st.pi⟩ && B.preds[st.n]?.map (·.b) == some st.q &&
      P.kind == .If && P.controls == #[st.cp] && C.preds.size == st.cn &&
      (B.values.isEmpty || (B.values == #[st.ctl] && st.ctlOK f))
  | _, _, _ => false

/-- No listed value reads `ctl`, and no block but `b` has it as a control (when `ctl` is `b`'s
value: the target may skip evaluating it). -/
def unreadOK (f : Func) : Bool :=
  (valsOf f st.b).isEmpty ||
  f.blocks.all fun y => match f.block? y with
    | some Y =>
      Y.values.all (fun x => (f.value? x).all fun v => !v.args.contains st.ctl) &&
        (y == st.b || !Y.controls.contains st.ctl)
    | none => true

/-- A `Phi` of `child`. -/
def cPhi (v : Value) : Bool := v.op == .Phi && v.block == st.child

/-- Value table entries: a `Phi` of `child` gains its argument along `b → child`; any other value
keeps what is read (`sameW`). -/
def entryOK (o o' : Option Value) : Bool :=
  match o, o' with
  | some v, some w =>
    if st.cPhi v then st.ai < v.args.size && Cmp.sameW { v with args := v.args.push v.args[st.ai]! } w
    else Cmp.sameW v w
  | none, none => true
  | _, _ => false

/-- The entry is no `Phi` of `child`. -/
def noCPhi (o : Option Value) : Bool :=
  match o with
  | some v => !st.cPhi v
  | none => true

theorem entryOK_refl {o : Option Value} (h : st.noCPhi o = true) : st.entryOK o o = true := by
  cases o with
  | none => rfl
  | some v =>
    simp only [noCPhi, Bool.not_eq_true'] at h
    simp [entryOK, h, Cmp.sameW_refl]

/-- `entryOK`, by pointer first where it is reflexive. -/
def entryFast (o o' : Option Value) : Bool :=
  if h : st.noCPhi o = true then
    withPtrEq o o' (fun _ => st.entryOK o o') (fun he => by subst he; exact st.entryOK_refl h)
  else st.entryOK o o'

/-- Every value table entry passes `entryOK`. -/
def valTabOK (f g : Func) : Bool :=
  f.valueTab.size == g.valueTab.size && Nat.all f.valueTab.size fun x _ =>
    st.entryFast f.valueTab[x]! g.valueTab[x]!

end Site

/-! ## The decision -/

/-- `x` is a term node of `f`. -/
def isTerm (f : Func) (x : ID) : Bool := (f.value? x).any fun v => RewriteCheck.termOp v.op

/-- The arguments of value `x`. -/
def argsOf (f : Func) (x : ID) : Array ID := ((f.value? x).map (·.args)).getD #[]

/-- Add the term nodes reachable from `x` through term nodes, each before its arguments
(`fuel` bounds the depth; a node beyond it is left out, and `topoOK` then fails). -/
def visit (f : Func) : Nat → List ID → ID → List ID
  | 0, acc, _ => acc
  | fuel + 1, acc, x =>
    if acc.contains x || !isTerm f x then acc
    else x :: (argsOf f x).foldl (visit f fuel) acc

/-- The term nodes reachable from `xs`. -/
def termClosure (f : Func) (xs : List ID) : List ID := xs.foldl (visit f 64) []

/-- Every term node's term arguments are listed after it. -/
def topoOK (f : Func) : List ID → Bool
  | [] => true
  | x :: rest => (argsOf f x).all (fun a => !isTerm f a || rest.contains a) && topoOK f rest

/-- `u` and `w` are the same term (same op, type, auxints and arguments). -/
def sameTerm (f : Func) (u w : ID) : Bool :=
  match f.value? u, f.value? w with
  | some a, some c =>
    RewriteCheck.termOp a.op && a.op == c.op && a.type == c.type && a.auxInt == c.auxInt &&
      a.aux == c.aux && a.args == c.args
  | _, _ => false

/-- The path facts along `p → b`: `p`'s control holds `pv`, and so does `ctl` if it is the
same term. -/
def asm (f : Func) (cp ctl : ID) (pv : Bool) : ProveCheck.Asm :=
  { facts := (cp, pv) :: (if sameTerm f cp ctl then [(ctl, pv)] else []) }

/-- `ctl` is an (in)equality `a ⋈ b` at width `w` whose sides' signed ranges are disjoint, so
it is `.bool v` (the signed reading complements `ProveCheck.rangeDecides`, which separates
equalities by unsigned ranges). -/
def eqDisjoint (tabs : Tables) (f : Func) (A : ProveCheck.Asm) (ctl : ID) (v : Bool) : Bool :=
  match f.value? ctl with
  | some cv =>
    RewriteCheck.termOp cv.op &&
    match cv.args.toList, ProveCheck.cTab.lookup cv.op with
    | [a, b], some (.eq w isEq) =>
      v == !isEq &&
        (let rx := ProveCheck.rng f.value? tabs A fuel w a
         let ry := ProveCheck.rng f.value? tabs A fuel w b
         decide (rx.shi < ry.slo) || decide (ry.shi < rx.slo))
    | _, _ => false
  | none => false

/-- **The decision**: under the path facts along `p → b`, `ctl` is decided to be `.bool v`, and
the term nodes the decision reads are listed in a dependency order. -/
def decideOK (tabs : Tables) (f : Func) (cp : ID) (pv : Bool) (ctl : ID) (v : Bool) : Bool :=
  let T := termClosure f [cp, ctl]
  let A := asm f cp ctl pv
  (ProveCheck.decides f.value? tabs A fuel fuel ctl v || eqDisjoint tabs f A ctl v) &&
    topoOK f T && (!isTerm f cp || T.contains cp) && (!isTerm f ctl || T.contains ctl)

/-! ## The relation -/

/-- **One redirect** at site `st`, checked (see the module doc). -/
def relB (tabs : Tables) (f g : Func) (st : Site) : Bool :=
  st.shapeOK f && st.unreadOK f && decideOK tabs f st.cp (st.pi == 0) st.ctl (st.out == 0) &&
    st.valTabOK f g && [st.b, st.p, st.child, st.q].all (st.blockOK f g) &&
    tabEq f.blockTab g.blockTab st.touched && tabEq g.blocks f.blocks (fun _ => false) &&
    g.entry == f.entry && g.ownAux == f.ownAux

/-- **A checked redirect**: `g` is `f` with predecessor `k` of `b` redirected to `b.Succs[out]`. -/
def stepOK (tabs : Tables) (f g : Func) (b : ID) (k out : Nat) : Bool :=
  relB tabs f g (siteOf f b k out)

end Redir

/-! ## `fuseBranchRedirect`, checked -/

/-- `predLoop` with every redirect checked; a rejected one is skipped. -/
def predLoopC (pv : Prover) (tabs : Tables) (b : ID) : Nat → Func → FactsTable → Nat → Bool →
    Func × FactsTable × Bool
  | 0, f, ft, _, changed => (f, ft, changed)
  | fuel + 1, f, ft, k, changed =>
    if k < (f.getB b).preds.size then
      match tryPredOut pv f ft b k with
      | (ft, some out) =>
        let g := redirect f b k out
        if Redir.stepOK tabs f g b k out then predLoopC pv tabs b fuel g ft k true
        else predLoopC pv tabs b fuel f ft (k + 1) changed
      | (ft, none) => predLoopC pv tabs b fuel f ft (k + 1) changed
    else (f, ft, changed)

/-- A block without predecessors that is not the entry becomes `Invalid`. -/
def markDead (f : Func) (b : ID) : Func :=
  if (f.getB b).preds.size == 0 && b != f.entry then
    f.modB b fun x => { x with kind := .Invalid }
  else f

/-- One block of `fuseBranchRedirect`'s sweep. -/
def redirectBlock (pv : Prover) (tabs : Tables) (f : Func) (ft : FactsTable) (b : ID) :
    Func × FactsTable × Bool :=
  let bb := f.getB b
  if bb.kind != .If then (f, ft, false) else
  let ctl := f.getV bb.controls[0]!
  if (ctl.block != b && bb.values.size != 0) ||
      ((bb.values.size != 1 || ctl.uses != 1) && ctl.block == b) then (f, ft, false) else
  let (f, ft, c) := predLoopC pv tabs b (2 * bb.preds.size + 2) f ft 0 false
  (markDead f b, ft, c)

/-- The sweep over `blocks[k-1] … blocks[0]`. -/
def redirectSweep (pv : Prover) (tabs : Tables) (blocks : Array ID) :
    Nat → Func → FactsTable → Bool → Func × FactsTable × Bool
  | 0, f, ft, changed => (f, ft, changed)
  | k + 1, f, ft, changed =>
    let (f, ft, c) := redirectBlock pv tabs f ft blocks[k]!
    redirectSweep pv tabs blocks k f ft (c || changed)

/-- **`fuseBranchRedirect`, checked**: every redirect is validated (`Redir.stepOK`). -/
def fuseBranchRedirectChecked (pv : Prover) (tabs : Tables) (f : Func) :
    Except String (Func × Bool) :=
  let (g, ft, changed) :=
    redirectSweep pv tabs f.blocks f.blocks.size f (FactsTable.new pv.cx f).checkpoint false
  match ft.err with
  | some e => throw e
  | none => pure (g, changed)

end GoFV.Opt.Fuse

import GoFV.Opt.Fuse.Comparisons
import GoFV.Opt.Checked
import GoFV.Opt.SpecSafe

variable [GoFV.SSA.Sem.Addrs]

/-!
# fuseComparisons, checked

`Cmp.relB f g b` validates one `fuseComparisons` rewrite at `b` of `f` into `g` (`site`: `b`'s
only predecessor `p`, the side `i` both share, their common successor `s`, the controls `pc` and
`bc`, the new value `nv`, the source `q` of `s`'s last predecessor edge):

- in `f`: `p` and `b` are `If` blocks, `b`'s only predecessor is `p` along `p`'s other side,
  both reach `s` along side `i` (`s` is neither `p` nor `b`); every value of `b` is
  speculation-safe (`specSafeBlock`);
- in `g`: `b` holds its values and `nv` and branches on `nv` to its old successors, `p` is
  `Plain` and jumps to `b` (`expect`); the edge `p → s` is gone: `s`'s last predecessor took its
  index (`remapE` on every successor list, `swapRemove` on `s`'s predecessors), every other block
  table entry is unchanged; `nv` is `OrB pc bc` (side 0) or `AndB pc bc` (side 1) of the type of
  `pc` and `bc` (neither a `Phi`) in block `b`, at a free ID of `f`'s table; every `Phi` of `s`
  has the same argument along `p`'s and `b`'s edges and loses `p`'s by swap-removal; every other
  value keeps what the semantics and well-formedness read (`sameW`: all but positions and use
  counts); `b`'s values are schedulable.

The value and block tables are compared entry by entry with the untouched entries compared by
pointer first (`entryFast`, `tabEq`), so no `check` of `g` is needed and the check costs about
one pointer comparison per table entry (issue #147). The soundness proof is
`GoFV.Proof.FuseCmp.fuseComparisonsChecked_refines`.
-/

namespace GoFV.Opt.Fuse

open GoFV.SSA

namespace Cmp

/-- The site of a comparison fusion at `b` (see the module doc). -/
structure Site where
  b : ID
  p : ID
  /-- `b`'s edge index in `p`'s successors -/
  kp : Nat
  /-- the shared side (`1 - kp`) -/
  i : Nat
  s : ID
  /-- `p`'s and `b`'s edge indices in `s`'s predecessors -/
  jp : Nat
  jb : Nat
  /-- the last predecessor index of `s` in `f` -/
  n : Nat
  /-- the source of `s`'s last predecessor edge -/
  q : ID
  pc : ID
  bc : ID
  nv : ID

/-- The site the rewrite of `f` into `g` at `b` would have. -/
def site (f g : Func) (b : ID) : Site :=
  let B := f.getB b
  let e := B.preds[0]!
  let P := f.getB e.b
  let i := 1 - e.i
  let es := P.succs[i]!
  let S := f.getB es.b
  { b, p := e.b, kp := e.i, i, s := es.b, jp := es.i, jb := B.succs[i]!.i,
    n := S.preds.size - 1, q := S.preds[S.preds.size - 1]!.b, pc := P.controls[0]!,
    bc := B.controls[0]!, nv := (g.getB b).controls[0]! }

/-- The new control's op on side `i`. -/
def newOp (i : Nat) : Op := if i == 0 then .OrB else .AndB

/-- Go's swap-removal of index `j` (`removePred`, `removePhiArg`). -/
def swapRemove {α : Type} [Inhabited α] (a : Array α) (j : Nat) : Array α :=
  (a.set! j a[a.size - 1]!).pop

/-- What the semantics and well-formedness read of a value: all but its position and use
count. -/
def sameW (v w : Value) : Bool :=
  w.id == v.id && w.type == v.type && w.aux == v.aux && w.auxInt == v.auxInt && w.op == v.op &&
    w.args == v.args && w.block == v.block

theorem sameW_refl (v : Value) : sameW v v = true := by simp [sameW]

namespace Site

variable (st : Site)

/-- An edge after `p → s` is removed: `s`'s last predecessor moves to `p`'s index. -/
def remapE (e : Edge) : Edge := if e.b == st.s && e.i == st.n then { e with i := st.jp } else e

/-- The block table entry of `x` in `g`, from its entry `X` in `f`. -/
def expect (x : ID) (X : Block) : Block :=
  if x == st.b then
    { X with values := X.values.push st.nv, controls := #[st.nv], succs := X.succs.map st.remapE,
             preds := #[⟨st.p, 0⟩] }
  else if x == st.p then
    { X with kind := .Plain, likely := .unknown, controls := #[], succs := #[⟨st.b, 0⟩] }
  else if x == st.s then
    { X with preds := swapRemove X.preds st.jp, succs := X.succs.map st.remapE }
  else { X with succs := X.succs.map st.remapE }

/-- The blocks whose table entries the rewrite replaces. -/
def touched (x : ID) : Bool := x == st.p || x == st.b || x == st.s || x == st.q

/-- Block `x`'s entry in `g` is `expect`ed. -/
def blockOK (f g : Func) (x : ID) : Bool :=
  match f.block? x, g.block? x with
  | some X, some X' => X' == st.expect x X
  | _, _ => false

/-- The shape of `p`, `b` and `s` in `f`, and the schedulability of `b` in `g`. -/
def shapeOK (f g : Func) : Bool :=
  match f.block? st.b, f.block? st.p, f.block? st.s, g.block? st.b with
  | some B, some P, some S, some B' =>
    f.blocks.contains st.b && st.kp < 2 && st.i == 1 - st.kp && st.p != st.b && st.s != st.b &&
      st.s != st.p &&
      B.kind == .If && P.kind == .If && B.preds == #[⟨st.p, st.kp⟩] &&
      B.controls == #[st.bc] && P.controls == #[st.pc] && B.succs.size == 2 &&
      P.succs.size == 2 && P.succs[st.i]? == some ⟨st.s, st.jp⟩ &&
      B.succs[st.i]? == some ⟨st.s, st.jb⟩ && S.preds.size == st.n + 1 &&
      S.preds[st.n]?.map (·.b) == some st.q && (Sem.schedule g B').isSome
  | _, _, _, _ => false

/-- A control of the rewrite: listed in `f`, not a `Phi`, of type `t`. -/
def ctrlOK (f : Func) (c : ID) (t : TypeRef) : Bool :=
  match f.value? c with
  | some v => v.op != .Phi && v.type == t
  | none => false

/-- The new value: a free ID of `f`'s table, `newOp i` of `pc` and `bc` in block `b`, of their
type. -/
def newOK (f g : Func) : Bool :=
  g.valueTab.size == f.valueTab.size && st.nv < f.valueTab.size && (f.value? st.nv).isNone &&
    match g.value? st.nv with
    | some w => w.id == st.nv && w.op == newOp st.i && w.args == #[st.pc, st.bc] &&
        w.block == st.b && ctrlOK f st.pc w.type && ctrlOK f st.bc w.type
    | none => false

/-- A `Phi` of `s`. -/
def sPhi (v : Value) : Bool := v.op == .Phi && v.block == st.s

/-- Value table entries: a `Phi` of `s` agrees along `p`'s and `b`'s edges and loses `p`'s
argument by swap-removal; any other value keeps what is read (`sameW`). -/
def entryOK (o o' : Option Value) : Bool :=
  match o, o' with
  | some v, some w =>
    if st.sPhi v then
      v.args[st.jp]? == v.args[st.jb]? && sameW { v with args := swapRemove v.args st.jp } w
    else sameW v w
  | none, none => true
  | _, _ => false

/-- The entry is no `Phi` of `s`. -/
def noSPhi (o : Option Value) : Bool :=
  match o with
  | some v => !st.sPhi v
  | none => true

theorem entryOK_refl {o : Option Value} (h : st.noSPhi o = true) : st.entryOK o o = true := by
  cases o with
  | none => rfl
  | some v =>
    simp only [noSPhi, Bool.not_eq_true'] at h
    simp [entryOK, h, sameW_refl]

/-- `entryOK`, by pointer first where it is reflexive. -/
def entryFast (o o' : Option Value) : Bool :=
  if h : st.noSPhi o = true then
    withPtrEq o o' (fun _ => st.entryOK o o') (fun he => by subst he; exact st.entryOK_refl h)
  else st.entryOK o o'

/-- Every value table entry but `nv`'s passes `entryOK`. -/
def valTabOK (f g : Func) : Bool :=
  f.valueTab.size == g.valueTab.size && Nat.all f.valueTab.size fun x _ =>
    x == st.nv || st.entryFast f.valueTab[x]! g.valueTab[x]!

end Site

/-- **One `fuseComparisons` rewrite** at `b`, checked (see the module doc). -/
def relB (f g : Func) (b : ID) : Bool :=
  let st := site f g b
  st.shapeOK f g && st.newOK f g && specSafeBlock f b && st.valTabOK f g &&
    [st.p, st.b, st.s, st.q].all (st.blockOK f g) &&
    tabEq f.blockTab g.blockTab st.touched && tabEq g.blocks f.blocks (fun _ => false) &&
    g.entry == f.entry && g.ownAux == f.ownAux

/-- **A checked `fuseComparisons` step** at `b`: `g` is the rewrite of `f`. -/
def stepOK (f g : Func) (b : ID) : Bool := relB f g b

/-- **`fuseComparisons`, checked**: the rewrite is kept only if `stepOK` accepts it. -/
def fuseComparisonsChecked (isMem : TypeRef → Bool)
    (canOpt : Func → Value → Value → Op → Bool) (f : Func) (b : ID) : Func × Bool :=
  let (g, ch) := fuseComparisons isMem canOpt f b
  if ch && stepOK f g b then (g, true) else (f, false)

end Cmp

end GoFV.Opt.Fuse

import GoFV.Opt.Fuse.Comparisons
import GoFV.Opt.Fuse.PlainCheck
import GoFV.Opt.SpecSafe
import GoFV.SSA.DomCert

/-!
# fuseComparisons, checked

`Cmp.relB f g b` validates one `fuseComparisons` rewrite at `b` of `f` into `g` (`site`: `b`'s
only predecessor `p`, the side `i` both share, their common successor `s`, the controls `pc` and
`bc`, the new value `nv`):

- in `f`: `p` and `b` are `If` blocks, `b`'s only predecessor is `p` along `p`'s other side,
  both reach `s` along side `i` (`s` is neither `p` nor `b`); every value of `b` is
  speculation-safe (`specSafeBlock`); every `Phi` of `s` has the same argument along `p`'s and
  `b`'s edges;
- in `g`: `b` holds its values and `nv` (`OrB pc bc` for side 0, `AndB pc bc` for side 1, a free
  ID of `f`'s table) and branches on `nv` to its old successors; `p` keeps its values and jumps
  to `b`; the edge `p → s` is gone: `s`'s last predecessor took its index (`remapE` on every
  successor list, the `Phi`s of `s` lose that argument by swap-removal, `swapRemove`); all else
  is unchanged; `b`'s values are schedulable.

The soundness proof is `GoFV.Proof.FuseCmp.refines_of_step`.
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
  { b, p := e.b, kp := e.i, i, s := es.b, jp := es.i, jb := B.succs[i]!.i,
    n := (f.getB es.b).preds.size - 1, pc := P.controls[0]!, bc := B.controls[0]!,
    nv := (g.getB b).controls[0]! }

/-- The new control's op on side `i`. -/
def newOp (i : Nat) : Op := if i == 0 then .OrB else .AndB

/-- Go's swap-removal of index `j` (`removePred`, `removePhiArg`). -/
def swapRemove (a : Array ID) (j : Nat) : Array ID := (a.set! j a[a.size - 1]!).pop

namespace Site

variable (st : Site)

/-- An edge after `p → s` is removed: `s`'s last predecessor moves to `p`'s index. -/
def remapE (e : Edge) : Edge := if e.b == st.s && e.i == st.n then { e with i := st.jp } else e

/-- The shape of `p`, `b` and `s` in `f` and of `p` and `b` in `g`. -/
def shapeOK (f g : Func) : Bool :=
  match f.block? st.b, f.block? st.p, f.block? st.s, g.block? st.b, g.block? st.p with
  | some B, some P, some S, some B', some P' =>
    st.kp < 2 && st.i == 1 - st.kp && st.p != st.b && st.s != st.b && st.s != st.p &&
      B.kind == .If && P.kind == .If && B.preds == #[⟨st.p, st.kp⟩] &&
      B.controls == #[st.bc] && P.controls == #[st.pc] && B.succs.size == 2 &&
      P.succs.size == 2 && P.succs[st.i]? == some ⟨st.s, st.jp⟩ &&
      B.succs[st.i]? == some ⟨st.s, st.jb⟩ && S.preds.size == st.n + 1 &&
      B'.id == st.b && B'.values == B.values.push st.nv && B'.kind == .If &&
      B'.controls == #[st.nv] && B'.succs == B.succs.map st.remapE &&
      (Sem.schedule g B').isSome &&
      P'.id == st.p && P'.values == P.values && P'.kind == .Plain &&
      P'.succs[0]? == some ⟨st.b, 0⟩
  | _, _, _, _, _ => false

/-- The new value: a free ID of `f`'s table, `newOp i` of `pc` and `bc` in `g`. -/
def newOK (f g : Func) : Bool :=
  g.valueTab.size == f.valueTab.size && st.nv < f.valueTab.size && (f.value? st.nv).isNone &&
    match g.value? st.nv with
    | some w => w.id == st.nv && w.op == newOp st.i && w.args == #[st.pc, st.bc]
    | none => false

/-- Value `x` (not `nv`): a `Phi` of `s` agrees along `p`'s and `b`'s edges and loses `p`'s
argument by swap-removal; any other value is unchanged. -/
def valueOK (f g : Func) (x : ID) : Bool :=
  match f.value? x with
  | some v =>
    if v.op == .Phi && (valsOf f st.s).contains x then
      v.args[st.jp]? == v.args[st.jb]? &&
        match g.value? x with
        | some w => w.id == v.id && w.type == v.type && w.aux == v.aux && w.auxInt == v.auxInt &&
            w.op == v.op && w.args == swapRemove v.args st.jp
        | none => false
    else Plain.valueOK f g x
  | none => Plain.valueOK f g x

/-- `p` and `b` are listed and `b` is no ancestor of `p` in `f`'s dominator certificate. -/
def placeOK (f : Func) : Bool :=
  f.blocks.contains st.b && f.blocks.contains st.p && !(DomCert.make f).anc st.b st.p

/-- A block other than `p` and `b`: unchanged but for `remapE` on its successors. -/
def blockOK (f g : Func) (x : ID) : Bool :=
  match f.block? x, g.block? x with
  | some fb, some gb => gb.id == fb.id && gb.values == fb.values && gb.kind == fb.kind &&
      gb.controls == fb.controls && gb.succs == fb.succs.map st.remapE
  | _, _ => false

end Site

/-- **One `fuseComparisons` rewrite** at `b`, checked (see the module doc). -/
def relB (f g : Func) (b : ID) : Bool :=
  let st := site f g b
  st.shapeOK f g && st.newOK f g && st.placeOK f && specSafeBlock f b &&
    (List.range f.valueTab.size).all (fun x => x == st.nv || st.valueOK f g x) &&
    f.blocks.all (fun x => x == st.p || x == st.b || st.blockOK f g x) &&
    g.blocks == f.blocks && g.entry == f.entry && g.ownAux == f.ownAux

/-- **A checked `fuseComparisons` step** at `b`: `g` passes `check` and is the rewrite. -/
def stepOK (ce : CheckEnv) (f g : Func) (b : ID) : Bool := checkOK ce g && relB f g b

/-- **`fuseComparisons`, checked**: the rewrite is kept only if `stepOK` accepts it. -/
def fuseComparisonsChecked (ce : CheckEnv) (isMem : TypeRef → Bool)
    (canOpt : Func → Value → Value → Op → Bool) (f : Func) (b : ID) : Func × Bool :=
  let (g, ch) := fuseComparisons isMem canOpt f b
  if ch && stepOK ce f g b then (g, true) else (f, false)

end Cmp

end GoFV.Opt.Fuse

import GoFV.Opt.Checked
import GoFV.Opt.ZCSE

/-!
# short circuit, checked (issue #16)

`cpaOK tabs f g` checks step 1 of short circuit (`constPhiArgs`): `g` is `f` with

- the same blocks and control-flow graph; the entry block gains values at the end of its list
  (the new constants), every other block table entry is unchanged;
- every value of `f` unchanged but for its use count and its arguments; a changed argument `k`
  is one of a `Phi` whose predecessor along edge `k` is an `If` with that argument as its
  control, and it became a `ConstBool` of `g`'s entry (of the boolean shape) holding the value
  the control has on that edge (`true` on the `If`'s first successor);
- each new value a `ConstBool` without arguments in the entry block;
- the argument-free values of `g`'s entry evaluate in every frame (`ZCSE.safe`), so that
  adding the constants to the entry is zcse's relation (`GoFV.Proof.ZCSE.ZRel`).

It runs once per pass on the whole function (unchanged table entries are compared by pointer
first, `tabEq`). The proof is `GoFV.Proof.ShortCirc.cpaOK_refines`.
-/

namespace GoFV.Opt.ShortCircuit

open GoFV.SSA

/-- `c` is a `ConstBool` value of `g`'s entry, without arguments, of the boolean shape, holding
`d`. -/
def constB (tabs : Tables) (g : Func) (c : ID) (d : Bool) : Bool :=
  (valsOf g g.entry).contains c &&
    match g.value? c with
    | some w => w.op == .ConstBool && w.args.isEmpty && w.id == c && w.block == g.entry &&
        (w.auxInt != 0) == d && (match tabs.ty w.type with | .bool => true | _ => false)
    | none => false

/-- Argument `k` of value `fv` of `f` is `fa`, and `ga` in `g`: the same, or `fv` is a `Phi`
whose predecessor along edge `k` is an `If` on `fa`, and `ga` is the constant `fa` holds on
that edge. -/
def argOK (tabs : Tables) (f g : Func) (fv : Value) (k : Nat) (fa ga : ID) : Bool :=
  fa == ga || (fv.op == .Phi &&
    match f.block? fv.block with
    | some Y =>
      match Y.preds[k]? with
      | some e =>
        match f.block? e.b with
        | some P => P.kind == .If && P.controls[0]? == some fa && constB tabs g ga (e.i == 0)
        | none => false
      | none => false
    | none => false)

/-- A value of `f` unchanged in `g` but for its use count and arguments (`argOK`); a new value
of `g` is a `ConstBool` without arguments of the entry. -/
def cpaValOK (tabs : Tables) (f g : Func) (x : ID) : Bool :=
  match f.value? x, g.value? x with
  | some fv, some gv =>
    { gv with args := fv.args, uses := fv.uses } == fv && gv.args.size == fv.args.size &&
      (List.range fv.args.size).all fun k => argOK tabs f g fv k fv.args[k]! gv.args[k]!
  | some _, none => false
  | none, _ => true

theorem argOK_self (tabs : Tables) (f g : Func) (fv : Value) (k : Nat) (a : ID) :
    argOK tabs f g fv k a a = true := by simp [argOK]

/-- Entries that are the same object pass `cpaValOK`. -/
theorem cpaValOK_of_eq {tabs : Tables} {f g : Func} {x : ID} (hx : x < f.valueTab.size)
    (h : f.valueTab[x]! = g.valueTab[x]!) : cpaValOK tabs f g x = true := by
  unfold cpaValOK Func.value?
  rw [getElem!_pos f.valueTab x hx] at h
  rw [Array.getElem?_eq_getElem hx]
  rcases Nat.lt_or_ge x g.valueTab.size with hg | hg
  · rw [getElem!_pos g.valueTab x hg] at h
    rw [Array.getElem?_eq_getElem hg, ← h]
    cases f.valueTab[x] with
    | none => rfl
    | some fv => simp [argOK_self]
  · rw [getElem!_neg g.valueTab x (by omega)] at h
    rw [h]; rfl

/-- A new value of `g`'s entry: a `ConstBool` without arguments, with its ID, block and a `Bool`
auxint. -/
def newConstOK (f g : Func) (x : ID) : Bool :=
  f.value? x == none &&
    match g.value? x with
    | some w => w.op == .ConstBool && w.args.isEmpty && w.id == x && w.block == g.entry &&
        (w.auxInt == 0 || w.auxInt == 1)
    | none => false

/-- **The checker of `constPhiArgs`** (see the module doc). -/
def cpaOK (tabs : Tables) (f g : Func) : Bool :=
  g.blocks == f.blocks && g.entry == f.entry && g.ownAux == f.ownAux && g.bidLast == f.bidLast &&
    g.valueTab.size == f.valueTab.size &&
    tabEq g.blockTab f.blockTab (· == f.entry) &&
    (match f.block? f.entry, g.block? g.entry with
      | some fE, some gE =>
        { gE with values := fE.values } == fE &&
          gE.values.extract 0 fE.values.size == fE.values &&
          (gE.values.extract fE.values.size).all (newConstOK f g) &&
          decide (gE.values.extract fE.values.size).toList.Nodup &&
          gE.values.all fun x => match g.value? x with
            | some w => !ZCSE.argless w || ZCSE.safe tabs (ZCSE.params tabs g) w
            | none => true
      | _, _ => false) &&
    Nat.all f.valueTab.size fun x hx =>
      withPtrEq f.valueTab[x]! g.valueTab[x]! (fun _ => cpaValOK tabs f g x) (cpaValOK_of_eq hx)

end GoFV.Opt.ShortCircuit

import GoFV.Proof.DomCert
import GoFV.Proof.Pass.CopyFrag

/-!
# What copyelim changes: the static relation `CopyRel`

`CopyRel tabs f g` relates copyelim's input `f` and output `g` on the blocks of `f`'s dominator
tree (the only blocks a run can reach): same control-flow graph and block contents; every
argument or control `a` of `f` becomes `a` itself or, if `a` is a copy in `g`, the copy's
argument (`ArgRel`); every value keeps its op, aux and type, except that a `Phi` may become a
`Copy` of a value every one of its arguments is related to (phielim), and a value of a zero-size
aggregate type may become `Empty`. The argument of a copy of `g` in a tree block keeps its
value at the copy's shape (`RetypeInto`), or is an `Addr` (a global pointer or `poison`) under a
word-shaped copy (`CopyArgOK`; a `Phi <uintptr>` of `Addr`s turned copy, issue #17).

Checked on the corpus: copyelim's output satisfies `CopyRel` on every section
(`lake exe copyrel-probe`). `copyelim_refines_of_rel` (`GoFV.Proof.Pass.CopyElim`) derives the
refinement from it.
-/

namespace GoFV.Proof.CopyElim

open GoFV.SSA GoFV.SSA.DomCert GoFV.Opt

/-- `w` is `a`, or `a` is a `Copy` of `w` in `g`. -/
def ArgRel (g : Func) (a w : ID) : Prop :=
  a = w ∨ ∃ u, g.value? a = some u ∧ u.op = .Copy ∧ u.args = #[w]

/-- What copyelim does to a value `fv` of a tree block (its result `gv`). -/
inductive ValRel (tabs : Tables) (g : Func) (fv gv : Value) : Prop where
  /-- Same op, aux and auxint; arguments related. -/
  | same : gv.op = fv.op → gv.aux = fv.aux → gv.auxInt = fv.auxInt →
      gv.args.size = fv.args.size →
      (∀ (k : Nat) (a : ID), fv.args[k]? = some a → ∃ w, gv.args[k]? = some w ∧ ArgRel g a w) →
      ValRel tabs g fv gv
  /-- phielim: a `Phi` all of whose arguments are related to `w` becomes `Copy w`. -/
  | phi (w : ID) : fv.op = .Phi → gv.op = .Copy → gv.args = #[w] →
      (∀ a ∈ fv.args, ArgRel g a w) → ValRel tabs g fv gv
  /-- A value of a zero-size struct or array type becomes `Empty` (without arguments). -/
  | empty : zeroSizeAggregate tabs fv.type = .ok true → gv.op = .Empty → gv.args = #[] →
      ValRel tabs g fv gv

/-- What a copy `x` of shape `t` needs of its argument `wv`: values of `wv`'s shape keep their
value at `t` (`RetypeInto`), or `x` was a `Phi` (`fx`: its input value), `wv` is an `Addr` (it
evaluates to a global pointer or `poison`, `GlobalOrPoison`) and `t` a word shape. -/
def CopyArgOK (tabs : Tables) (fx : Option Value) (wv : Value) (t : Sem.Ty) : Prop :=
  RetypeInto (tabs.ty wv.type) t ∨
    (wv.op = .Addr ∧ wordShape t = true ∧ ∀ fv, fx = some fv → fv.op = .Phi)

/-- The argument's register `y` (fixed at its shape, and a global pointer or `poison` when it is
an `Addr`'s) keeps its value at the copy's shape. -/
theorem CopyArgOK.apply {tabs : Tables} {fx : Option Value} {wv : Value} {t : Sem.Ty}
    (h : CopyArgOK tabs fx wv t) {y : Sem.Val}
    (hy : y.retype (tabs.ty wv.type) = y) (ha : wv.op = .Addr → GlobalOrPoison y) :
    y.retype t = y :=
  h.elim (fun h => h.apply hy) (fun ⟨hop, ht, _⟩ => (ha hop).retype_word ht)

/-- The static relation between copyelim's input `f` and output `g`. -/
structure CopyRel (tabs : Tables) (f g : Func) : Prop where
  cfg : cfgView g = cfgView f
  ownAux : g.ownAux = f.ownAux
  vsize : g.valueTab.size = f.valueTab.size
  block : ∀ bid ∈ f.blocks, ((make f).depthOf bid).isSome → ∀ fb, f.block? bid = some fb →
    ∃ gb, g.block? bid = some gb ∧ gb.kind = fb.kind ∧ gb.values = fb.values ∧
      gb.controls.size = fb.controls.size ∧
      ∀ (k : Nat) (c : ID), fb.controls[k]? = some c →
        ∃ c', gb.controls[k]? = some c' ∧ ArgRel g c c'
  value : ∀ bid ∈ f.blocks, ((make f).depthOf bid).isSome → ∀ fb, f.block? bid = some fb →
    ∀ x ∈ fb.values, ∀ fv, f.value? x = some fv →
      ∃ gv, g.value? x = some gv ∧ gv.block = fv.block ∧ gv.type = fv.type ∧ ValRel tabs g fv gv
  copyShape : ∀ bid ∈ f.blocks, ((make f).depthOf bid).isSome → ∀ fb, f.block? bid = some fb →
    ∀ x ∈ fb.values, ∀ gv w, g.value? x = some gv → gv.op = .Copy → gv.args = #[w] →
      ∃ wv, g.value? w = some wv ∧ CopyArgOK tabs (f.value? x) wv (tabs.ty gv.type)

end GoFV.Proof.CopyElim

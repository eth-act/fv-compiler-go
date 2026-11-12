import GoFV.Opt.CopyElim
import GoFV.Opt.RewriteCheck
import GoFV.SSA.Check
import GoFV.Proof.Pass.CopyElimSim

variable [GoFV.SSA.Sem.Addrs]

/-!
# copyelim on zero-size values: a checked second fragment (issue #69)

`copyelim_refines`' fragment `EmptyFrag` admits only zero-size values that already evaluate to
`.empty` without arguments (`Empty`, `Arg` at offset 0). `phielim` also resets zero-size `Load`s,
copies and selections to `Empty`, dropping their arguments; a target `Empty` then no longer
depends on, say, the `NilCheck` its source `Load` read, which the simulation's schedule argument
(equal frames, the roots' dependencies kept) cannot follow.

`zeroGuard` validates such an input in two steps. `zeroReset tabs f` is `f` with every zero-size
term value of shape `empty` reset to `Empty` (use counts recounted). `f` to `zeroReset tabs f` is
checked as a rewrite by the atom simulation: the same atoms, the roots in the same order
(`RewriteCheck.atomsOK`), and every value as a term refined (a value of shape `empty` is `.empty`
or `poison`, `Empty` is `.empty`). `zeroReset tabs f` to copyelim's output `g` is copyelim's
relation (`CopyElim.CopyRel`), decided on the output by `copyRelB`, with the old fragment
`EmptyFrag` on `zeroReset tabs f`. The proofs are in `GoFV.Proof.Pass.CopyZero`.
-/

namespace GoFV.Opt.CopyZero

open GoFV.SSA GoFV.Proof.CopyElim

/-- `v` is reset by `zeroReset`: a term (`RewriteCheck.termOp`) of a zero-size struct or array
type with shape `empty`. -/
def resetB (tabs : Tables) (v : Value) : Bool :=
  zeroSizeB tabs v.type && (match tabs.ty v.type with | .empty => true | _ => false) &&
    RewriteCheck.termOp v.op

/-- `v` reset to `Empty` when `resetB`. -/
def zr (tabs : Tables) (v : Value) : Value :=
  if resetB tabs v then { v with op := .Empty, args := #[], auxInt := 0, aux := none } else v

/-- The use counts `check` expects: each argument of a listed value and each control. -/
def useTab (f : Func) : Array Nat := Id.run do
  let mut uses : Array Nat := Array.replicate f.valueTab.size 0
  for b in f.blocks.filterMap f.block? do
    for vid in b.values do
      let some v := f.value? vid | continue
      for a in v.args do
        uses := uses.modify a (· + 1)
    for c in b.controls do
      uses := uses.modify c (· + 1)
  return uses

/-- `f` with its zero-size term values reset to `Empty` (`zr`), use counts recounted. -/
def zeroReset (tabs : Tables) (f : Func) : Func :=
  let f1 := { f with valueTab := f.valueTab.map (·.map (zr tabs)) }
  let u := useTab f1
  { f1 with valueTab := f1.valueTab.mapIdx fun i o => o.map fun v => { v with uses := u[i]! } }

/-- Decides `CopyElim.ArgRel g a w`. -/
def argRelB (g : Func) (a w : ID) : Bool :=
  a == w || (g.value? a).any fun u => u.op == .Copy && u.args == #[w]

/-- Decides `CopyElim.ValRel tabs g kv gv`. -/
def valRelB (tabs : Tables) (g : Func) (kv gv : Value) : Bool :=
  (gv.op == kv.op && gv.aux == kv.aux && gv.auxInt == kv.auxInt &&
    gv.args.size == kv.args.size &&
    (List.range kv.args.size).all fun i => argRelB g kv.args[i]! gv.args[i]!) ||
  (kv.op == .Phi && gv.op == .Copy && gv.args.size == 1 && kv.args.all (argRelB g · gv.args[0]!)) ||
  (zeroSizeB tabs kv.type && gv.op == .Empty && gv.args.isEmpty)

/-- The checks of value `x` of a tree block: related as `ValRel`, and a copy of `g` retypes like
its argument. -/
def valueRelB (tabs : Tables) (k g : Func) (x : ID) : Bool :=
  (match k.value? x, g.value? x with
    | some kv, some gv => gv.block == kv.block && gv.type == kv.type && valRelB tabs g kv gv
    | some _, none => false
    | none, _ => true) &&
  (g.value? x).all fun gv => gv.op != .Copy || gv.args.size != 1 ||
    (g.value? gv.args[0]!).any fun wv => retypeIntoB (tabs.ty wv.type) (tabs.ty gv.type)

/-- Decides `CopyElim.CopyRel tabs k g` (`GoFV.Proof.Pass.CopyZero.copyRelB_sound`). -/
def copyRelB (tabs : Tables) (k g : Func) : Bool :=
  let C := DomCert.make k
  DomCert.cfgView g == DomCert.cfgView k && g.ownAux == k.ownAux &&
  g.valueTab.size == k.valueTab.size &&
  k.blocks.all fun b =>
    !C.inTree b ||
    match k.block? b, g.block? b with
    | some kb, some gb =>
      gb.kind == kb.kind && gb.values == kb.values && gb.controls.size == kb.controls.size &&
      ((List.range kb.controls.size).all fun i => argRelB g kb.controls[i]! gb.controls[i]!) &&
      kb.values.all (valueRelB tabs k g)
    | some _, none => false
    | none, _ => true

/-- The second fragment of `early phielim and copyelim` (`copyelim_refines_zero`). -/
def zeroGuard (env : PassEnv) (f : Func) : Bool :=
  let tabs := env.tables
  let k := zeroReset tabs f
  match copyelim tabs f with
  | .ok g =>
    (check { tabs, typs := env.typs } k).toBool && emptyFragB tabs k &&
      RewriteCheck.atomsOK f k && RewriteCheck.closedOK f && RewriteCheck.closedOK k &&
      copyRelB tabs k g
  | .error _ => false

end GoFV.Opt.CopyZero

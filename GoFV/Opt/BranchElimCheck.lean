import GoFV.Opt.SpecSafe
import GoFV.Opt.Chain
import GoFV.SSA.Check

/-!
# branchelim, checked: one rewrite at a time

`diamondB f g dom post` validates one `elimIf`/`elimIfElse` rewrite of `f` into `g`: the `If`
block `dom` has two sides, each an edge to `post` or a speculation-safe `Plain` arm whose only
predecessor is `dom` and whose successor is `post` (`sideOf`); in `g`, `dom` holds the values
of `dom`, the arms and `post`, takes `post`'s kind, controls and successors, and `post`'s `Phi`s
are `CondSelect`s of `dom`'s control over the arguments of the two sides; every other value
and block is unchanged in what the semantics reads. Side conditions that make the merged
block evaluate as the source's path does:

- arm values are speculation-safe (`specSafeOp`), are read only by their own arm and, along
  their side, by `post`'s `Phi`s, and read nothing of `post` or the other arm;
- `dom`'s non-`Phi` values and its control read nothing of `post`; `post`'s `Phi`s read nothing
  of `post`; `post`'s other values are no parameter reads;
- the merged block has a schedule and its side-effecting roots are chained, as are those of
  `dom` and `post` in `f` (`chainedB`).

The soundness proof is `GoFV.Proof.BranchElim.refines_of_step`.
-/

namespace GoFV.Opt.BranchElim

open GoFV.SSA

/-- The values of block `b` (none if `b` is not a block). -/
def valsOf (f : Func) (b : ID) : Array ID := ((f.block? b).map (·.values)).getD #[]

/-- One side of the diamond at `dom`, along successor `k` (edge `e`): the arm block (`none`:
the edge enters `post` directly) and the predecessor index of `post` the side enters by. -/
def sideOf (f : Func) (dom post : ID) (k : Nat) (e : Edge) : Option (Option ID × Nat) :=
  if e.b == post then some (none, e.i) else
  match f.block? e.b with
  | some a =>
    if a.kind == .Plain && a.preds == #[⟨dom, k⟩] && a.succs.size == 1 &&
        (a.succs[0]?.map (·.b)) == some post && e.b != dom then
      some (some e.b, (a.succs[0]?.map (·.i)).getD 0)
    else none
  | none => none

/-- A diamond: the `If` block, the join block, `dom`'s control, the arms and the predecessor
indices of `post` by side. -/
structure Site where
  dom : ID
  post : ID
  c : ID
  arm0 : Option ID
  arm1 : Option ID
  j0 : Nat
  j1 : Nat

/-- The diamond at `dom` joining at `post`, if `f` has that shape. -/
def site? (f : Func) (dom post : ID) : Option Site :=
  match f.block? dom with
  | none => none
  | some D =>
    if D.kind == .If && D.controls.size == 1 && D.succs.size == 2 && post != dom then
      match sideOf f dom post 0 D.succs[0]!, sideOf f dom post 1 D.succs[1]! with
      | some (a0, j0), some (a1, j1) => some ⟨dom, post, D.controls[0]!, a0, a1, j0, j1⟩
      | _, _ => none
    else none

namespace Site

variable (s : Site) (f : Func)

/-- `x` is a value of arm `a?`. -/
def inArm (a? : Option ID) (x : ID) : Bool := a?.any fun a => (valsOf f a).contains x

/-- `x` is a value of an arm. -/
def armVal (x : ID) : Bool := inArm f s.arm0 x || inArm f s.arm1 x

/-- `x` is a value of `post`. -/
def postVal (x : ID) : Bool := (valsOf f s.post).contains x

/-- `x` is a value of the merged blocks. -/
def regionVal (x : ID) : Bool := (valsOf f s.dom).contains x || s.armVal f x || s.postVal f x

/-- `b` is one of the merged blocks. -/
def regionBlock (b : ID) : Bool := b == s.dom || b == s.post || s.arm0 == some b || s.arm1 == some b

/-- The arguments of an arm's value: no value of `post` or of the other arm. -/
def armArgsOK (own other : Option ID) (v : Value) : Bool :=
  v.args.all fun a => !s.postVal f a && !inArm f other a

/-- Arm `own`: speculation-safe values reading nothing of `post` or the other arm. -/
def armOK (own other : Option ID) : Bool :=
  match own with
  | none => true
  | some a => (valsOf f a).all fun x => match f.value? x with
    | some v => specSafeOp v.op && s.armArgsOK f own other v
    | none => false

/-- A use of argument `k` of value `y` (listed in block `bid`): an arm value is read only by its
own arm, or by `post`'s `Phi`s along its side. -/
def useOK (bid : ID) (yv : Value) (k : Nat) (a : ID) : Bool :=
  (!inArm f s.arm0 a || s.arm0 == some bid || (bid == s.post && yv.op == .Phi && k == s.j0)) &&
  (!inArm f s.arm1 a || s.arm1 == some bid || (bid == s.post && yv.op == .Phi && k == s.j1))

/-- Every use of an arm value in `f` is allowed, and no control is an arm value. -/
def usesOK : Bool :=
  f.blocks.all fun bid => match f.block? bid with
    | none => true
    | some B =>
      B.values.all (fun y => match f.value? y with
        | some yv => (List.range yv.args.size).all fun k => s.useOK f bid yv k yv.args[k]!
        | none => true) &&
      B.controls.all fun c => !s.armVal f c

/-- `dom`'s non-`Phi` values and its control read nothing of `post`. -/
def domOK : Bool :=
  (valsOf f s.dom).all (fun x => match f.value? x with
    | some v => v.op == .Phi || v.args.all fun a => !s.postVal f a
    | none => false) &&
  !s.postVal f s.c

/-- `post`'s `Phi`s have two arguments, none a value of `post`; its other values are no
parameter reads. -/
def postOK : Bool :=
  (valsOf f s.post).all fun x => match f.value? x with
    | some v =>
      if v.op == .Phi then v.args.size == 2 && v.args.all fun a => !s.postVal f a
      else v.op != .Arg && v.op != .ArgIntReg
    | none => false

/-- The shape of `f` around the diamond. -/
def shapeOK : Bool :=
  match f.block? s.post with
  | none => false
  | some P =>
    P.preds.size == 2 && s.j0 != s.j1 && s.j0 < 2 && s.j1 < 2 &&
    (match s.arm0, s.arm1 with
      | some a, some b => a != b
      | _, _ => true) &&
    s.armOK f s.arm0 s.arm1 && s.armOK f s.arm1 s.arm0 && s.usesOK f && s.domOK f && s.postOK f

/-- The target version of value `x`: `post`'s `Phi`s become `CondSelect`s of `dom`'s control
over their arguments along sides 0 and 1; every other value is unchanged in its ID, op, type,
aux, auxint and arguments. -/
def valueOK (g : Func) (x : ID) : Bool :=
  match f.value? x, g.value? x with
  | some fv, some gv =>
    gv.id == fv.id && gv.type == fv.type && gv.aux == fv.aux && gv.auxInt == fv.auxInt &&
    if s.postVal f x && fv.op == .Phi then
      gv.op == .CondSelect && gv.args == #[fv.args[s.j0]!, fv.args[s.j1]!, s.c]
    else gv.op == fv.op && gv.args == fv.args
  | none, none => true
  | _, _ => false

/-- Block `bid` (outside the diamond) is unchanged in what entering it and its terminator read. -/
def blockOK (g : Func) (bid : ID) : Bool :=
  s.regionBlock bid ||
  match f.block? bid, g.block? bid with
  | some fb, some gb => gb.id == fb.id && gb.values == fb.values && gb.kind == fb.kind &&
      gb.controls == fb.controls && gb.succs == fb.succs
  | _, _ => false

/-- The merged block of `g`. -/
def mergedOK (g : Func) : Bool :=
  match f.block? s.dom, f.block? s.post, g.block? s.dom with
  | some D, some P, some D' =>
    D'.id == s.dom && D'.kind == P.kind && D'.controls == P.controls && D'.succs == P.succs &&
    D'.values.all (s.regionVal f) &&
    D.values.all D'.values.contains && P.values.all D'.values.contains &&
    (match s.arm0 with | some a => (valsOf f a).all D'.values.contains | none => true) &&
    (match s.arm1 with | some a => (valsOf f a).all D'.values.contains | none => true) &&
    (Sem.schedule g D').isSome && chainedB g #[s.dom] && chainedB f #[s.dom, s.post]
  | _, _, _ => false

/-- **One branchelim rewrite**, checked (see the module doc). -/
def relB (g : Func) : Bool :=
  s.shapeOK f && f.blocks.contains s.dom && g.entry == f.entry && g.ownAux == f.ownAux &&
  g.valueTab.size == f.valueTab.size && g.blocks == f.blocks &&
  s.mergedOK f g && (List.range f.valueTab.size).all (s.valueOK f g) && f.blocks.all (s.blockOK f g)

end Site

/-- `g` is `f` with the diamond at `dom` joining at `post` merged. -/
def diamondB (f g : Func) (dom post : ID) : Bool :=
  match site? f dom post with
  | some s => s.relB f g
  | none => false

/-- The join block candidates of a diamond at `dom`: its successors and theirs. -/
def postCandidates (f : Func) (dom : ID) : List ID :=
  match f.block? dom with
  | some D => (D.succs.toList.map (·.b)) ++
      D.succs.toList.filterMap fun e => (f.block? e.b).bind fun B => B.succs[0]?.map (·.b)
  | none => []

/-- `f` passes `check`. -/
def checkOK (ce : CheckEnv) (f : Func) : Bool :=
  match check ce f with
  | .ok () => true
  | .error _ => false

/-- **A checked branchelim step**: `g` (the rewrite at `dom`) passes `check` and is a diamond
merge of `f`. -/
def stepOK (ce : CheckEnv) (f g : Func) (dom : ID) : Bool :=
  checkOK ce g && (postCandidates f dom).any (diamondB f g dom)

end GoFV.Opt.BranchElim

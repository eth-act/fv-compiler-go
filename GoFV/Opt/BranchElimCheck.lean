import GoFV.Opt.SpecSafe
import GoFV.Opt.Checked

/-!
# branchelim, checked: one rewrite at a time

`diamondB f g dom post` validates one `elimIf`/`elimIfElse` rewrite of `f` into `g`: the `If`
block `dom` has two sides, each an edge to `post` or a speculation-safe `Plain` arm whose only
predecessor is `dom` and whose successor is `post` (`sideOf`); in `g`, `dom` holds the values
of `dom`, the arms and `post` (in this order), takes `post`'s kind, controls and successors,
keeps its predecessors (an edge from `post` now from `dom`), and `post`'s `Phi`s are
`CondSelect`s of `dom`'s control over the arguments of the two sides (`mergedOK`); the arms
and `post` are emptied (`deadOK`); a successor of `post` is unchanged but for its predecessor
edges from `post`, now from `dom` (`targetOK`); the values of these blocks and `dom`'s control
are unchanged in what the semantics reads and lie in `dom` (or their block) (`movedOK`); every
other value and block table entry is unchanged (`tabEq`, pointer first, so the check costs
about the size of the diamond plus a pointer comparison per table entry; issue #147). Side
conditions that make the merged block evaluate as the source's path does:

- arm values are speculation-safe (`specSafeOp`), are read only by their own arm and, along
  their side, by `post`'s `Phi`s, and read nothing of `post` or the other arm;
- `dom`'s non-`Phi` values and its control read nothing of `post`; `post`'s `Phi`s read nothing
  of `post`; `post`'s other values are no parameter reads;
- the merged block has a schedule that lists the non-pure nodes (priority ≠ 0) of `dom` and
  `post` in the sequence `dom`'s and then `post`'s schedule lists them (`npSeqOK`).

No `check` of `g`: the soundness proof is `GoFV.Proof.BranchElim.refines_of_step`, with the
well-formedness and use dominance of `g` from `GoFV.Proof.BranchElim.DRel.wf_pres` and
`DRel.useDom_pres`.
-/

namespace GoFV.Opt.BranchElim

open GoFV.SSA

/-- The merged block `D'` of `g` has a schedule listing the non-pure nodes of `D` and `P` (in
`f`) in the sequence `D`'s schedule and then `P`'s lists them. -/
def npSeqOK (f g : Func) (D P D' : Block) : Bool :=
  match Sem.schedule f D, Sem.schedule f P, Sem.schedule g D' with
  | some oD, some oP, some oT =>
    oT.toList.filter (fun x => npOf f D x || npOf f P x) ==
      oD.toList.filter (npOf f D) ++ oP.toList.filter (npOf f P)
  | _, _, _ => false

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

/-- The values of arm `a?` (none without an arm). -/
def armVals (a? : Option ID) : Array ID := match a? with
  | some a => valsOf f a
  | none => #[]

/-- Edge `e` of `f`, redirected to `dom` if it leaves `post` (the merged block takes over
`post`'s successor edges). -/
def redir (e : Edge) : Edge := if e.b == s.post then { e with b := s.dom } else e

/-- The successors of `post` in `f`: their predecessor edges from `post` now leave `dom`. -/
def tgts : Array ID := ((f.block? s.post).map fun P => P.succs.map (·.b)).getD #[]

/-- Block `b` is changed by the rewrite: a block of the diamond or a successor of `post`. -/
def changed (b : ID) : Bool := s.regionBlock b || (s.tgts f).contains b

/-- Value `x` is compared one by one (`movedOK`), not by `tabEq`: `dom`'s control (its use count
changes), or a value listed in a changed block, by its block field. -/
def skipV (x : ID) : Bool :=
  x == s.c || match f.value? x with
    | some v => s.changed f v.block && (valsOf f v.block).contains x
    | none => false

/-- Value `x` is `valueOK` and lies in block `blk` of `g` (positions and use counts may
differ). -/
def movedOK (g : Func) (blk x : ID) : Bool :=
  s.valueOK f g x && (g.value? x).any (·.block == blk)

/-- Block `b` (an arm or `post`) is emptied in `g`. -/
def deadOK (g : Func) (b : ID) : Bool :=
  match g.block? b with
  | some B' => B'.id == b && B'.values.isEmpty && B'.preds.isEmpty && B'.succs.isEmpty &&
      B'.controls.isEmpty
  | none => false

/-- Arm `a?`, if any, is emptied in `g`. -/
def armDeadOK (g : Func) (a? : Option ID) : Bool := a?.all (deadOK g)

/-- A successor `t` of `post` other than `dom` lies outside the diamond and is unchanged in `g`
but for its predecessor edges from `post`, which leave `dom` (and its position). -/
def targetOK (g : Func) (t : ID) : Bool :=
  t == s.dom ||
  (!s.regionBlock t && match f.block? t, g.block? t with
    | some T, some T' => T' == { T with preds := T.preds.map s.redir, pos := T'.pos }
    | _, _ => false)

/-- The merged block of `g`: `dom` with the values of the arms (side 0, then side 1) and of
`post` appended, `post`'s kind, controls and successors, `dom`'s predecessors (an edge from
`post` now from `dom`), and a schedule (`npSeqOK`). -/
def mergedOK (g : Func) : Bool :=
  match f.block? s.dom, f.block? s.post, g.block? s.dom with
  | some D, some P, some D' =>
    D'.id == s.dom && D'.kind == P.kind && D'.controls == P.controls && D'.succs == P.succs &&
    D'.preds == D.preds.map s.redir &&
    D'.values == D.values ++ armVals f s.arm0 ++ armVals f s.arm1 ++ P.values &&
    (Sem.schedule g D').isSome && npSeqOK f g D P D'
  | _, _, _ => false

/-- **One branchelim rewrite**, checked (see the module doc). The unchanged table entries are
compared with `tabEq` (pointer first), so the check costs about the size of the diamond and
the successors of `post`, plus a pointer comparison per table entry (issue #147). -/
def relB (g : Func) : Bool :=
  s.shapeOK f && f.blocks.contains s.dom && g.entry == f.entry && g.ownAux == f.ownAux &&
  tabEq g.blocks f.blocks (fun _ => false) &&
  s.mergedOK f g && deadOK g s.post && armDeadOK g s.arm0 && armDeadOK g s.arm1 &&
  (s.tgts f).all (s.targetOK f g) &&
  (valsOf f s.post).all (fun x => (f.value? x).any (·.block == s.post)) &&
  (valsOf f s.dom).all (s.movedOK f g s.dom) && (armVals f s.arm0).all (s.movedOK f g s.dom) &&
  (armVals f s.arm1).all (s.movedOK f g s.dom) && (valsOf f s.post).all (s.movedOK f g s.dom) &&
  (s.tgts f).all (fun t => t == s.dom || (valsOf f t).all (s.movedOK f g t)) &&
  s.movedOK f g (((f.value? s.c).map (·.block)).getD 0) s.c &&
  tabEq f.valueTab g.valueTab (s.skipV f) &&
  tabEq f.blockTab g.blockTab (s.changed f)

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

/-- **A checked branchelim step**: `g` (the rewrite at `dom`) is a diamond merge of `f`. No
`check` of `g`: the soundness proof derives its well-formedness and use dominance from the
relation (`GoFV.Proof.BranchElim.wf_pres`, `useDom_pres`). -/
def stepOK (f g : Func) (dom : ID) : Bool :=
  (postCandidates f dom).any (diamondB f g dom)

end GoFV.Opt.BranchElim

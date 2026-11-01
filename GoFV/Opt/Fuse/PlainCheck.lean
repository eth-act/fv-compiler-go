import GoFV.Opt.Fuse.Plain
import GoFV.Opt.Checked

/-!
# fuseBlockPlain, checked

`Plain.relB f g run` validates one `fuseBlockPlain` rewrite of `f` into `g` that fuses the run
`b₀ … c` (`plainRun`):

- in `f`, `b₀` is listed and consecutive blocks of the run are linked alone: each but `c` is
  `Plain` with the next as its only successor, which has it as its only predecessor
  (`chainOK`); the blocks after `b₀` are not the entry and hold no `Phi` and no parameter read
  (`laterOK`); a non-`Phi` reads no value of a later block of the run (`readsAllOK`);
- in `g`, every value of the run is unchanged in what the semantics reads and moved to `c`
  (`movedOK`), every other value table entry is unchanged; block `c` holds the run's values in
  run order, `b₀`'s predecessors, `c`'s kind and controls, and `c`'s successors with edges into
  `b₀` redirected to `c` (`redirect`); its schedule lists the non-pure nodes of the run block by
  block, each in its source sequence (`mergedOK`); the other blocks of the run are emptied
  (`deadOK`); a predecessor of `b₀` outside the run is unchanged but for the same redirection
  (`predOK`); every other block table entry is unchanged; the entry moves from `b₀` to `c`.

The unchanged table entries are compared with `tabEq` (pointer first), so the check costs about
the size of the run, not of the function (issue #147). No `check` of `g` is needed: the
soundness proof (`GoFV.Proof.FusePlain.refines_of_step`) derives the well-formedness and use
dominance of `g` from the relation (`GoFV.Proof.FusePlain.wf_pres`, `useDom_pres`).
-/

namespace GoFV.Opt.Fuse

open GoFV.SSA

/-- The run `fuseBlockPlain f b` fuses (`b₀ … c`), if it fires. -/
def plainRun (f : Func) (b : ID) : Option (List ID) :=
  let bb := f.getB b
  if bb.kind != .Plain then none else
  let c := bb.succs[0]!.b
  if (f.getB c).preds.size != 1 || c == b then none else
  let fuel := f.blocks.size + 1
  let b := runStart f c fuel b
  let c := runEnd f b fuel c
  some (runBlocks f c fuel b #[]).toList

namespace Plain

/-- Edge `e`, redirected to `c` if it enters `b0`. -/
def redirect (b0 c : ID) (e : Edge) : Edge := if e.b == b0 then { e with b := c } else e

/-- `x` is `Plain` with the only successor `y`, whose only predecessor is `x`. -/
def linkOK (f : Func) (x y : ID) : Bool :=
  match f.block? x, f.block? y with
  | some X, some Y => X.kind == .Plain && X.succs == #[⟨y, 0⟩] && Y.preds == #[⟨x, 0⟩]
  | _, _ => false

/-- Consecutive blocks are linked alone. -/
def chainOK (f : Func) : List ID → Bool
  | x :: y :: rest => linkOK f x y && chainOK f (y :: rest)
  | _ => true

/-- A later block of the run: not the entry, no `Phi` and no parameter read. -/
def laterOK (f : Func) (y : ID) : Bool :=
  y != f.entry && (valsOf f y).all fun x => match f.value? x with
    | some v => v.op != .Phi && v.op != .Arg && v.op != .ArgIntReg
    | none => false

/-- The non-`Phi`s of block `x` read no value of the blocks `later`. -/
def readsOK (f : Func) (x : ID) (later : List ID) : Bool :=
  (valsOf f x).all fun v => match f.value? v with
    | some fv => fv.op == .Phi || fv.args.all fun a => later.all fun y => !(valsOf f y).contains a
    | none => false

/-- `readsOK` for every block of the run against the blocks after it. -/
def readsAllOK (f : Func) : List ID → Bool
  | [] => true
  | x :: rest => readsOK f x rest && readsAllOK f rest

/-- Two table entries the semantics reads alike (blocks and positions may differ). -/
def sameV (fv gv : Value) : Bool :=
  gv.id == fv.id && gv.type == fv.type && gv.aux == fv.aux && gv.auxInt == fv.auxInt &&
    gv.op == fv.op && gv.args == fv.args

/-- Value `x` of the run: unchanged in what the semantics reads, and moved to block `c`. -/
def movedOK (f g : Func) (c x : ID) : Bool :=
  match f.value? x, g.value? x with
  | some fv, some gv => sameV fv gv && gv.block == c
  | _, _ => false

/-- `p` is a predecessor of `b0` in `f`. -/
def isPredOf (f : Func) (b0 p : ID) : Bool :=
  match f.block? b0 with
  | some B0 => B0.preds.any (·.b == p)
  | none => false

/-- The predecessors of `b0` in `f`. -/
def predsOf (f : Func) (b0 : ID) : Array Edge := ((f.block? b0).map (·.preds)).getD #[]

/-- Block `p` (a predecessor of `b0` outside the run) is unchanged but for edges into `b0`,
redirected to `c`. -/
def predOK (f g : Func) (b0 c p : ID) : Bool :=
  match f.block? p, g.block? p with
  | some P, some P' => P' == { P with succs := P.succs.map (redirect b0 c) }
  | _, _ => false

/-- Block `y` (of the run, before `c`) is emptied in `g`. -/
def deadOK (g : Func) (y : ID) : Bool :=
  match g.block? y with
  | some Y' => Y'.id == y && Y'.values.isEmpty && Y'.preds.isEmpty && Y'.succs.isEmpty &&
      Y'.controls.isEmpty
  | none => false

/-- The schedule of block `x` of `f`. -/
def schedOf (f : Func) (x : ID) : Option (Array ID) := (f.block? x).bind (Sem.schedule f)

/-- `y` is a non-pure node of block `x` of `f`. -/
def npAt (f : Func) (x y : ID) : Bool :=
  match f.block? x with
  | some B => npOf f B y
  | none => false

/-- The non-pure nodes of the run, block by block in their schedules' sequence. -/
def npSeq (f : Func) (run : List ID) : List ID :=
  run.flatMap fun x => ((schedOf f x).getD #[]).toList.filter (npAt f x)

/-- The fused block `c` of `g` (see the module doc). -/
def mergedOK (f g : Func) (run : List ID) (b0 c : ID) : Bool :=
  match f.block? c, g.block? c with
  | some C, some C' =>
    C'.id == c && C'.values.toList == run.flatMap (fun x => (valsOf f x).toList) &&
    C'.kind == C.kind && C'.controls == C.controls && C'.succs == C.succs.map (redirect b0 c) &&
    C'.preds == predsOf f b0 && run.all (fun x => (schedOf f x).isSome) &&
    match Sem.schedule g C' with
    | some oT => oT.toList.filter (fun y => run.any (npAt f · y)) == npSeq f run
    | none => false
  | _, _ => false

/-- **One `fuseBlockPlain` rewrite** of the run `run`, checked (see the module doc). -/
def relB (f g : Func) (run : List ID) : Bool :=
  match run.head?, run.getLast? with
  | some b0, some c =>
    b0 != c && decide run.Nodup && f.blocks.contains b0 && chainOK f run &&
      run.tail.all (laterOK f) && readsAllOK f run &&
      tabEq g.blocks f.blocks (fun _ => false) && g.entry == (if f.entry == b0 then c else f.entry) &&
      g.ownAux == f.ownAux &&
      tabEq f.valueTab g.valueTab (fun x => run.any fun y => (valsOf f y).contains x) &&
      run.all (fun y => (valsOf f y).all (movedOK f g c)) &&
      tabEq f.blockTab g.blockTab (fun bid => run.contains bid || isPredOf f b0 bid) &&
      (predsOf f b0).all (fun e => run.contains e.b || predOK f g b0 c e.b) &&
      run.dropLast.all (deadOK g) &&
      mergedOK f g run b0 c
  | _, _ => false

/-- **A checked `fuseBlockPlain` step** at `b`: `g` fuses `plainRun f b`. -/
def stepOK (f g : Func) (b : ID) : Bool :=
  match plainRun f b with
  | some run => relB f g run
  | none => false

/-- **`fuseBlockPlain`, checked**: the rewrite is kept only if `stepOK` accepts it. -/
def fuseBlockPlainChecked (f : Func) (b : ID) : Func × Bool :=
  let (g, ch) := fuseBlockPlain f b
  if ch && stepOK f g b then (g, true) else (f, false)

end Plain

end GoFV.Opt.Fuse

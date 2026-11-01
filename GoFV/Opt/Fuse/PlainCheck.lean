import GoFV.Opt.Fuse.Plain
import GoFV.Opt.Checked

/-!
# fuseBlockPlain, checked

`Plain.relB f g run` validates one `fuseBlockPlain` rewrite of `f` into `g` that fuses the run
`b₀ … c` (`plainRun`):

- in `f`, consecutive blocks of the run are linked alone: each but `c` is `Plain` with the next
  as its only successor, which has it as its only predecessor (`chainOK`); the blocks after `b₀`
  are not the entry and hold no `Phi` and no parameter read (`laterOK`); a non-`Phi` reads no
  value of a later block of the run (`readsAllOK`);
- in `g`, block `c` holds the run's values in run order, `c`'s kind and controls, and `c`'s
  successors with edges into `b₀` redirected to `c` (`redirect`); its schedule lists the
  non-pure nodes of the run block by block, each in its source sequence (`mergedOK`); every
  block outside the run is unchanged but for the same redirection (`blockOK`); every value
  is unchanged in what the semantics reads (`valueOK`); the entry moves from `b₀` to `c`.

The soundness proof is `GoFV.Proof.FusePlain.refines_of_step`.
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

/-- Value `x` is unchanged. -/
def valueOK (f g : Func) (x : ID) : Bool :=
  match f.value? x, g.value? x with
  | some fv, some gv => sameV fv gv
  | none, none => true
  | _, _ => false

/-- Block `bid` (outside the run) is unchanged but for edges into `b0`, redirected to `c`. -/
def blockOK (f g : Func) (b0 c bid : ID) : Bool :=
  match f.block? bid, g.block? bid with
  | some fb, some gb => gb.id == fb.id && gb.values == fb.values && gb.kind == fb.kind &&
      gb.controls == fb.controls && gb.succs == fb.succs.map (redirect b0 c)
  | _, _ => false

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
    run.all (fun x => (schedOf f x).isSome) &&
    match Sem.schedule g C' with
    | some oT => oT.toList.filter (fun y => run.any (npAt f · y)) == npSeq f run
    | none => false
  | _, _ => false

/-- **One `fuseBlockPlain` rewrite** of the run `run`, checked (see the module doc). -/
def relB (f g : Func) (run : List ID) : Bool :=
  match run.head?, run.getLast? with
  | some b0, some c =>
    b0 != c && decide run.Nodup && run.all f.blocks.contains && chainOK f run &&
      run.tail.all (laterOK f) && readsAllOK f run &&
      g.blocks == f.blocks && g.entry == (if f.entry == b0 then c else f.entry) &&
      g.ownAux == f.ownAux && g.valueTab.size == f.valueTab.size &&
      (List.range f.valueTab.size).all (valueOK f g) &&
      f.blocks.all (fun bid => run.contains bid || blockOK f g b0 c bid) &&
      mergedOK f g run b0 c
  | _, _ => false

/-- **A checked `fuseBlockPlain` step** at `b`: `g` passes `check` and fuses `plainRun f b`. -/
def stepOK (ce : CheckEnv) (f g : Func) (b : ID) : Bool :=
  checkOK ce g && match plainRun f b with
    | some run => relB f g run
    | none => false

/-- **`fuseBlockPlain`, checked**: the rewrite is kept only if `stepOK` accepts it. -/
def fuseBlockPlainChecked (ce : CheckEnv) (f : Func) (b : ID) : Func × Bool :=
  let (g, ch) := fuseBlockPlain f b
  if ch && stepOK ce f g b then (g, true) else (f, false)

end Plain

end GoFV.Opt.Fuse

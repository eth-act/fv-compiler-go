import GoFV.Opt.Fuse.Plain
import GoFV.Opt.Checked
import GoFV.Opt.SchedFast

/-!
# fuseBlockPlain, checked in place

`fuseBlockPlainChecked f b` validates one `fuseBlockPlain` rewrite of `f` that fuses the run
`b₀ … c` (`plainRunOf`) without keeping `f` (issue #147):

- before the rewrite, `snapOf f b` checks `f`: `b₀` is listed and consecutive blocks of the run
  are linked alone: each but `c` is `Plain` with the next as its only successor, which has it
  as its only predecessor (`chainOK`); the blocks after `b₀` are not the entry and hold no `Phi`
  and no parameter read (`laterOK`); a non-`Phi` reads no value of a later block of the run
  (`readsAllOK`). It keeps what the check of the result compares against: the run's values with
  their entries, `b₀`'s predecessors with the blocks of those outside the run, block `c`, and the
  run's non-pure nodes block by block in their schedules' sequence;
- `fuseBlockPlain` then rewrites `f` in place (the snapshot holds no reference to the tables);
- `postOK` checks the result `g`: every value of the run is unchanged in what the semantics
  reads and moved to `c`; block `c` holds the run's values in run order, `b₀`'s predecessors,
  `c`'s kind and controls, and `c`'s successors with edges into `b₀` redirected to `c`
  (`redirect`); its schedule lists the run's non-pure nodes in the snapshot's sequence; the
  other blocks of the run are emptied (`deadOK`); a predecessor of `b₀` outside the run is
  unchanged but for the same redirection; the entry moves from `b₀` to `c`.

Every other table entry is unchanged by a proven frame lemma of `fuseRun`
(`GoFV.Proof.FusePlain.fuseRun_frame`), so the check costs about the size of the run. A rejected
rewrite is an error: `f` is gone, and the passes fall back to their input. No `check` of `g` is
needed: the soundness proof derives its well-formedness and use dominance from the relation
(`GoFV.Proof.FusePlain.PRel.wf_pres`, `useDom_pres`).
-/

namespace GoFV.Opt.Fuse

open GoFV.SSA

/-- The run `fuseBlockPlain f b` fuses (`b₀ … c`), if it fires. -/
def plainRun (f : Func) (b : ID) : Option (List ID) :=
  (plainRunOf f b).map fun (_, _, run) => run.toList

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

/-- The non-`Phi`s of block `x` read no value of the blocks `later` (for well-formed `f`, the
block of a listed value is `blockOf`). -/
def readsOK (f : Func) (x : ID) (later : List ID) : Bool :=
  (valsOf f x).all fun v => match f.value? v with
    | some fv => fv.op == .Phi || fv.args.all fun a => !later.contains (DomCert.blockOf f a)
    | none => false

/-- `readsOK` for every block of the run against the blocks after it. -/
def readsAllOK (f : Func) : List ID → Bool
  | [] => true
  | x :: rest => readsOK f x rest && readsAllOK f rest

/-- Two table entries the semantics reads alike (blocks and positions may differ). -/
def sameV (fv gv : Value) : Bool :=
  gv.id == fv.id && gv.type == fv.type && gv.aux == fv.aux && gv.auxInt == fv.auxInt &&
    gv.op == fv.op && gv.args == fv.args

/-- `p` is a predecessor of `b0` in `f`. -/
def isPredOf (f : Func) (b0 p : ID) : Bool :=
  match f.block? b0 with
  | some B0 => B0.preds.any (·.b == p)
  | none => false

/-- The predecessors of `b0` in `f`. -/
def predsOf (f : Func) (b0 : ID) : Array Edge := ((f.block? b0).map (·.preds)).getD #[]

/-- `x` is a non-pure value of `f`: a non-`Phi` value of priority ≠ 0. -/
def npV (f : Func) (x : ID) : Bool :=
  match f.value? x with
  | some v => v.op != .Phi && Sem.prio v.op != 0
  | none => false

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

/-- The fused block `c` of `g`, as the proof states it (`postOK` checks it against the
snapshot). -/
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

/-- What `fuseBlockPlainChecked` keeps of `f` before the rewrite (see the module doc). -/
structure Snap where
  run : List ID
  b0 : ID
  c : ID
  entry : ID
  /-- The run's values in run order, with their entries. -/
  vEnt : List (ID × Option Value)
  preds : Array Edge
  /-- The predecessors of `b₀` outside the run, with their blocks. -/
  pEnt : List (ID × Option Block)
  C : Block
  /-- The run's non-pure nodes, block by block in their schedules' sequence. -/
  npS : List ID

/-- The schedule of block `x` of `f` as the checker computes it (`SchedFast.schedFast`: over
block-local IDs; the same non-pure sequence as `Sem.schedule`, `schedFast_filter`). -/
def fastOf (f : Func) (x : ID) : Option (Array ID) := (f.block? x).bind (SchedFast.schedFast f)

/-- The pre-check of `f` and its snapshot (`none`: the rewrite does not fire or is skipped). -/
@[noinline] def snapOf (f : Func) (b : ID) : Option Snap :=
  match plainRunOf f b with
  | none => none
  | some (b0', c', runA) =>
    let run := runA.toList
    match run.head?, run.getLast? with
    | some b0, some c =>
      if !(b0 == b0' && c == c' && b0 != c && decide run.Nodup && f.blocks.contains b0 &&
          chainOK f run && run.tail.all (laterOK f) && readsAllOK f run) then none else
      let scheds := run.map (fastOf f)
      match f.block? c with
      | some C =>
        if !scheds.all (·.isSome) then none else
        let preds := predsOf f b0
        some {
          run, b0, c, entry := f.entry, preds, C
          vEnt := run.flatMap fun y => (valsOf f y).toList.map fun x => (x, f.value? x)
          pEnt := preds.toList.filterMap fun e =>
            if run.contains e.b then none else some (e.b, f.block? e.b)
          npS := scheds.flatMap fun o => (o.getD #[]).toList.filter (npV f) }
      | none => none
    | _, _ => none

/-- The check of the result `g` against the snapshot (see the module doc). -/
def postOK (s : Snap) (g : Func) : Bool :=
  s.vEnt.all (fun (x, fv?) => match fv?, g.value? x with
      | some fv, some gv => sameV fv gv && gv.block == s.c
      | _, _ => false) &&
    s.pEnt.all (fun (p, P?) => match P? with
      | some P => g.block? p == some { P with succs := P.succs.map (redirect s.b0 s.c) }
      | none => false) &&
    s.run.dropLast.all (deadOK g) &&
    g.entry == (if s.entry == s.b0 then s.c else s.entry) &&
    match g.block? s.c with
    | some C' => C'.id == s.c && C'.values.toList == s.vEnt.map (·.1) && C'.kind == s.C.kind &&
        C'.controls == s.C.controls && C'.succs == s.C.succs.map (redirect s.b0 s.c) &&
        C'.preds == s.preds &&
        match SchedFast.schedFast g C' with
        | some oT => oT.toList.filter (npV g) == s.npS
        | none => false
    | none => false

/-- **`fuseBlockPlain`, checked in place**: `.ok (f, false)` if the rewrite does not fire (or the
pre-check skips it), the rewrite if `postOK` accepts it, an error otherwise. -/
def fuseBlockPlainChecked (f : Func) (b : ID) : Except String (Func × Bool) :=
  match snapOf f b with
  | none => .ok (f, false)
  | some s =>
    let (g, ch) := fuseBlockPlain f b
    if ch && postOK s g then .ok (g, true) else .error "fuse: plain rewrite rejected"

end Plain

end GoFV.Opt.Fuse

import GoFV.SSA.Sem.RunSched
import GoFV.SSA.Sem.RunLoc
import GoFV.SSA.Sem.TyEq
import GoFV.SSA.Analysis.Postorder
import Std.Data.HashMap

/-!
# The regalloc checker (`docs/plans/regalloc-check.md`)

Translation validation of `regalloc` (L1 → L2, `docs/plans/semantics2.md` §7): `checkRA tabs f g`
compares the scheduled function `f` (the input of `regalloc`, run by `runSched`) with the
allocated function `g` (its output, run by `runLoc`), both in the tables `tabs` of `g`'s
section. The allocator itself (`GoFV.Opt.Regalloc`) is not trusted.

**Facts.** A fact `(l, o)` says that location `l` (a register, a stack slot, the memory, the
flags) holds the value the source run gave to `o` (a source value ID, or component `j` of a
tuple-valued one). Facts about a *frame constant* (`isKVal`: `MOVDconst`, `FMOVSconst`,
`FMOVDconst`, `LoweredGetCallerPC`, `SP`, `SB`, `MOVDaddr` of `SP`/`SB`, the values `regalloc`
rematerialises) hold unconditionally; the others hold whenever the source run has a value for
`o` (before `o` runs they say nothing).

**Walk.** `g`'s blocks are `f`'s, with the same kinds and successors; in each block `g`'s values
are `f`'s values in `f`'s order (*kept*: same ID, op, aux, auxint and type; arguments may be
other values), interleaved with moves (`Copy`, `LoadReg`, `StoreReg`: the facts of the source
location are copied to the destination) and rematerialised frame constants (new IDs, the op,
aux, auxint and arguments of a source constant). A source frame constant may be missing
(`regalloc` issues it only at its uses). Per value, as `stepLoc`:

1. every argument is read from its home and the home holds the source argument (`argOK`; a
   selector reads only its component; `ZERO` reads the zero constant);
2. the clobbers of the op (`regInfo.clobbers`, `clobbersArg0/1`, `tempRegs`, `clobberFlags`)
   lose their facts (`clobberFacts`);
3. for a kept value, every fact about its ID is dropped (the source value changes);
4. the locations written lose their facts and get the value's (`writeLocs`; a slot write kills
   the overlapping slots, as `LocState.setSlot`).

Phis are resolved on the edges (`phiEdge`): at the end of a predecessor, the home of every phi
of the successor holds the phi's argument for that edge. Block entry states are a certificate
(`Cert.ins`, computed by `certify`, an untrusted fixpoint); the check verifies them on every
edge, so soundness needs no fixpoint theory.
-/

namespace GoFV.Opt.RegallocCheck

open GoFV.SSA GoFV.SSA.Sem

/-! ## Facts -/

/-- A location of the `runLoc` state. -/
inductive Loc where
  | reg (r : Nat)
  | slot (k : SlotKey)
  | mem
  | flags
  /-- Not a location: `(avail, v)` says that the source run's value of the pure value `v` is
  its op applied to the current values of its arguments. -/
  | avail
  deriving DecidableEq, Inhabited, Repr, Hashable

/-- A source value (`comp = none`) or component `j` of a tuple-valued source value. A fact
`(l, o)` is *exact* (`weak = false`) when `l` holds the source value of `o` itself, *weak* when
`l` read at the shape of `o` gives it (a phi of a narrower integer type than its argument, in
the argument's register). -/
structure Orig where
  id : ID
  comp : Option Nat
  weak : Bool
  deriving DecidableEq, Inhabited, Repr, Hashable

abbrev Fact := Loc × Orig
abbrev Facts := List Fact

/-- The exact fact that `l` holds `id` (component `comp`). -/
@[inline] def exactF (l : Loc) (id : ID) (comp : Option Nat := none) : Fact := (l, ⟨id, comp, false⟩)

/-- `l` holds `id` (component `comp`), exactly or weakly. -/
def Facts.holds (S : Facts) (l : Loc) (id : ID) (comp : Option Nat := none) : Bool :=
  S.contains (l, ⟨id, comp, false⟩) || S.contains (l, ⟨id, comp, true⟩)

/-- `l` holds `id` exactly. -/
def Facts.holdsExact (S : Facts) (l : Loc) (id : ID) : Bool := S.contains (l, ⟨id, none, false⟩)

/-- The check's view of the two functions: the source `f` with `runSched`'s context, the target
`g` with `runLoc`'s, both in the tables `tabs`. -/
structure Cx where
  tabs : Tables
  f : Func
  g : Func
  sc : Ctx
  lc : LocCtx
  /-- For each source frame constant, a representative among the source constants with the same
  op, aux, auxint, type and arguments (untrusted: `Cx.canon` checks it). -/
  krep : Array ID

/-- The key of a frame constant for `constReps`' table (the op by name). -/
def constKey (v : Value) : String × Option AuxRef × Int64 × TypeRef × List ID :=
  (v.op.name, v.aux, v.auxInt, v.type, v.args.toList)

/-- `x` and `v` agree on everything a frame constant's value depends on. -/
def sameConst (x v : Value) : Bool :=
  x.op == v.op && x.aux == v.aux && x.auxInt == v.auxInt && x.type == v.type && x.args == v.args

/-- The shape of source value `id`. -/
def Cx.fty (cx : Cx) (id : ID) : Ty := cx.sc.tys[id]?.getD .other

/-- The shape of target value `id`. -/
def Cx.gty (cx : Cx) (id : ID) : Ty := cx.lc.ty id

/-- The ops of frame constants: their value depends on the activation only. -/
def kOp : Op → Bool
  | .ARM64MOVDconst | .ARM64FMOVSconst | .ARM64FMOVDconst | .ARM64LoweredGetCallerPC
  | .ARM64MOVDaddr | .ARM64ZERO | .SP | .SB => true
  | _ => false

/-- `v` is a frame constant of `f`: a frame-constant op whose arguments are `SP`/`SB`. -/
def isKVal (f : Func) (v : Value) : Bool :=
  kOp v.op && v.args.all fun a => match f.value? a with
    | some u => (u.op == .SP || u.op == .SB) && u.args.isEmpty
    | none => false

def Cx.isK (cx : Cx) (id : ID) : Bool := match cx.f.value? id with
  | some v => isKVal cx.f v
  | none => false

/-- The representatives of the frame constants of `f` (the first with each key, in value-table
order). -/
def constReps (f : Func) : Array ID := Id.run do
  let mut m : Std.HashMap (String × Option AuxRef × Int64 × TypeRef × List ID) ID := {}
  let mut out := (List.range f.valueTab.size).toArray
  for o in f.valueTab do
    if let some v := o then
      if isKVal f v then
        match m[constKey v]? with
        | some r => out := out.set! v.id r
        | none => m := m.insert (constKey v) v.id
  return out

def Cx.make (tabs : Tables) (f g : Func) : Cx :=
  { tabs, f, g, sc := Ctx.makeSched tabs f, lc := LocCtx.make tabs g, krep := constReps f }

/-- Frame constants with the same op, aux, auxint, type and arguments have the same value: facts
name them by one representative. -/
def Cx.canon (cx : Cx) (u : ID) : ID :=
  match cx.krep[u]?, cx.f.value? u with
  | some r, some v =>
    match cx.f.value? r with
    | some x => if r != u && isKVal cx.f v && isKVal cx.f x && sameConst x v then r else u
    | none => u
  | _, _ => u

/-- The word shapes (`int64` and pointers), which have the same values (`Val.hasTy`). -/
def isWord : Ty → Bool
  | .ptr _ | .int .w64 => true
  | _ => false

/-- Shapes with the same values (`Val.hasTy`): equal, or both words. -/
def shapeEq (t t' : Ty) : Bool :=
  (isWord t && isWord t') || Ty.beq t t'

/-- Reading at shape `t'` and then at `t` is reading at `t` (`LMode.retype`): equal shapes, or an
integer `t` no wider than the integer `t'` (a phi or move of a narrower type takes the low
bits). -/
def composes (t t' : Ty) : Bool :=
  shapeEq t t' ||
    match t, t' with
    | .int w, .int w' => decide (w.bits ≤ w'.bits)
    | _, _ => false

/-- Source value `id` is a zero constant (`MOVDconst [0]`, `ZERO`), which `regalloc` homes in
`ZERO`. -/
def Cx.isZeroConst (cx : Cx) (id : ID) : Bool := match cx.f.value? id with
  | some v => (v.op == .ARM64ZERO || (v.op == .ARM64MOVDconst && v.auxInt == 0)) && v.args.isEmpty
  | none => false

/-- The shape of a fact's origin. -/
def Cx.origTy (cx : Cx) (o : Orig) : Ty :=
  match o.comp, cx.fty o.id with
  | none, t => t
  | some j, .tuple ts => ts.getD j .other
  | some _, _ => .other

/-! ## Locations read and written (mirroring `LocState.read`/`write`) -/

/-- Register `r` as a location (`ZERO` and numbers beyond the register file hold no value). -/
def regLoc (r : Nat) : Option Loc :=
  if r == zeroReg || r ≥ ARM64.registers.size then none else some (.reg r)

/-- The locations of the components of a tuple of shapes `ts` in registers `rs`, from component
`j` on (`LocState.writeParts`/`readParts`). -/
def compLocs : List Ty → List (Option Nat) → Nat → List (Loc × Nat)
  | [], _, _ => []
  | t :: ts, rs, j =>
    match t with
    | .mem => (.mem, j) :: compLocs ts rs (j + 1)
    | t =>
      if t.isFlags then (.flags, j) :: compLocs ts rs (j + 1)
      else match rs with
        | some r :: rs => ((regLoc r).toList.map (·, j)) ++ compLocs ts rs (j + 1)
        | none :: rs => compLocs ts rs (j + 1)
        | [] => compLocs ts [] (j + 1)

/-- Where a value of home `h` and shape `t` is read from. -/
inductive RLoc where
  | loc (l : Loc)
  /-- `ZERO`: the zero of the reader's shape. -/
  | zero
  /-- A tuple: the location of each component that has one. -/
  | tuple (ls : List (Loc × Nat))
  /-- A value read as `poison` (a pair home of a non-tuple, a register beyond the file). -/
  | poison
  deriving Inhabited

/-- `LocState.read` of a value of home `h` and shape `t` (`none`: `stuck`). -/
def readLoc (h : Option Location) (t : Ty) : Option RLoc :=
  match h, t with
  | some (.slot k), _ => some (.loc (.slot k))
  | some h, .tuple ts => some (.tuple (compLocs ts h.regList 0))
  | some (.reg r), _ =>
    if r == zeroReg then some .zero
    else match regLoc r with
      | some l => some (.loc l)
      | none => some .poison
  | some _, _ => some .poison
  | none, .tuple ts => some (.tuple (compLocs ts [] 0))
  | none, .mem => some (.loc .mem)
  | none, t => if t.isFlags then some (.loc .flags) else none

/-- The locations `LocState.write` gives a value of home `h` and shape `t` (with the tuple
component each holds). -/
def writeLocs (h : Option Location) (t : Ty) : List (Loc × Option Nat) :=
  match h, t with
  | some (.slot k), _ => [(.slot k, none)]
  | h, .tuple ts => (compLocs ts ((h.map Location.regList).getD []) 0).map fun (l, j) => (l, some j)
  | some (.reg r), _ => (regLoc r).toList.map (·, none)
  | _, .mem => [(.mem, none)]
  | _, t => if t.isFlags then [(.flags, none)] else []

/-- The locations a write of a value of home `h` and shape `t` changes (a result that is not a
tuple writes `poison` to every component, `Val.partsOf`). -/
def killLocs (h : Option Location) (t : Ty) : List Loc := (writeLocs h t).map (·.1)

/-- Slot `k'` overlaps slot `k` (`LocState.setSlot`: same variable, overlapping bytes; a slot of
unknown size overlaps every slot of its variable). -/
def slotOverlaps (tabs : Tables) (k k' : SlotKey) : Bool :=
  let size (k : SlotKey) : Option Int := (typeSize? tabs k.type).map Int.ofNat
  k'.name == k.name &&
    match size k, size k' with
    | some n, some n' => decide (k.off < k'.off + n') && decide (k'.off < k.off + n)
    | _, _ => true

/-- A write of `l` changes `l'`. -/
def clashes (tabs : Tables) (l l' : Loc) : Bool :=
  match l, l' with
  | .slot k, .slot k' => k' == k || slotOverlaps tabs k k'
  | l, l' => l == l'

/-- The facts that survive a write of `l`. -/
def killLoc (tabs : Tables) (l : Loc) (S : Facts) : Facts :=
  S.filter fun (l', _) => !clashes tabs l l'

/-- The facts that survive the clobbers of target value `w` (`LocState.clobber`). -/
def clobberFacts (cx : Cx) (S : Facts) (w : Value) : Facts :=
  let ri := w.op.regInfo
  let S := if ri.clobbers.isEmpty then S else
    S.filter fun (l, _) => match l with
      | .reg r => !ri.clobbers.hasReg r
      | _ => true
  let killR (r : Nat) (S : Facts) : Facts := S.filter (·.1 != .reg r)
  let arg (b : Bool) (i : Nat) (S : Facts) : Facts :=
    if !b then S else
    match w.args[i]?.bind cx.lc.regOf with
    | some r => killR r S
    | none => S
  let S := arg ri.clobbersArg0 0 (arg ri.clobbersArg1 1 S)
  let S := match (cx.lc.temps[w.id]?).join with
    | some r => killR r S
    | none => S
  if w.op.clobberFlags then S.filter (·.1 != .flags) else S

/-- The facts after target value `w`'s result, with origin `id`, is written. -/
def writeFacts (cx : Cx) (S : Facts) (w : Value) (id : ID) : Facts :=
  let h := cx.lc.home w.id
  let t := cx.gty w.id
  let S := (killLocs h t).foldl (fun S l => killLoc cx.tabs l S) S
  (writeLocs h t).map (fun (l, j) => exactF l id j) ++ S

/-! ## Reads -/

/-- Target value `a'` read from its home holds the source value `a` (component `sel` only, for a
selector). -/
def argOK (cx : Cx) (S : Facts) (a' a : ID) (sel : Option Nat) : Except String Unit :=
  match readLoc (cx.lc.home a') (cx.gty a') with
  | none => throw s!"stuck-read v{a'} has no home"
  | some .poison => throw s!"poison-read v{a'} is read as poison"
  | some .zero =>
    if cx.isZeroConst a && shapeEq (cx.gty a') (cx.fty a) then pure ()
    else throw s!"zero-read v{a'} in ZERO for v{a}"
  | some (.loc l) =>
    if S.holds l (cx.canon a) && shapeEq (cx.gty a') (cx.fty a) then pure ()
    else throw s!"missing v{a'} ({repr l}) does not hold v{a}"
  | some (.tuple ls) =>
    match sel with
    | none => throw s!"tuple-read v{a'} read whole"
    | some i =>
      if !shapeEq (cx.gty a') (cx.fty a) then throw s!"tuple-shape v{a'} v{a}" else
      match ls.find? (·.2 == i) with
      | some (l, _) =>
        if S.holds l a (some i) then pure ()
        else throw s!"missing v{a'}.{i} ({repr l}) does not hold v{a}.{i}"
      | none => throw s!"missing v{a'}.{i} has no location"

/-- The component a selector reads of its argument. -/
def selIndex (v : Value) : Option Nat :=
  match v.op with
  | .Select0 => some 0
  | .Select1 => some 1
  | .SelectN => if v.auxInt.toInt < 0 then none else some v.auxInt.toInt.toNat
  | _ => none

/-- The arguments of kept value `w` (source value `u`) hold `u`'s arguments. -/
def argsOK (cx : Cx) (S : Facts) (w u : Value) : Except String Unit := do
  if w.args.size != u.args.size then throw s!"arity v{w.id}"
  for h : j in [0:w.args.size] do
    let sel := if j == 0 then selIndex u else none
    argOK cx S w.args[j] (u.args[j]!) sel

/-! ## Values -/

/-- Source and target value agree on everything `evalOpL` reads besides the arguments. -/
def sameOp (u w : Value) : Bool :=
  u.op == w.op && u.aux == w.aux && u.auxInt == w.auxInt && u.type == w.type &&
    u.args.size == w.args.size

/-- `MOVDreg`/`MOVDnop` read whether their argument's register is sign-extended: under
`runSched` from the producer's op (`arm64Op`), under `runLoc` from the register's producer
(`LocCtx.signOf`); the two must agree. -/
def signOK (cx : Cx) (w u : Value) : Bool :=
  if w.op == .ARM64MOVDreg || w.op == .ARM64MOVDnop then
    let src := (u.args[0]?.bind cx.f.value?).map (Arm64.signExtendsIn cx.f.value?)
    let tgt := (w.args[0]?.map (cx.lc.signOf cx.g.valueTab.size)).getD false
    src.getD false == tgt
  else true

/-- The arm64 ops `evalOpL` evaluates with `Arm64.evalPure` alone (their result is a function of
the arguments, the shape, the auxint and the aux): not a root and not one of `arm64Op`'s. -/
def pureArm64 (op : Op) : Bool :=
  !op.generic && !isRoot op &&
    match op with
    | .ARM64MOVBload | .ARM64MOVBUload | .ARM64MOVHload | .ARM64MOVHUload | .ARM64MOVWload
    | .ARM64MOVWUload | .ARM64MOVDload | .ARM64FMOVSload | .ARM64FMOVDload | .ARM64FMOVQload
    | .ARM64LDP | .ARM64LDPW | .ARM64LDPSW | .ARM64FLDPD | .ARM64FLDPS | .ARM64FLDPQ
    | .ARM64MOVDaddr | .ARM64MOVDreg | .ARM64MOVDnop | .ARM64LoweredGetClosurePtr
    | .ARM64LoweredGetCallerSP | .ARM64LoweredMemEq | .ARM64LDAR | .ARM64LDARB | .ARM64LDARW
    | .ARM64LoweredZero | .ARM64LoweredZeroLoop | .ARM64LoweredMove | .ARM64LoweredMoveLoop =>
      false
    | _ => true

/-- Source value `v` reads source value `u`. -/
def Cx.reads (cx : Cx) (v u : ID) : Bool := ((cx.f.value? v).map (·.args.contains u)).getD false

/-- The facts after source value `u` takes a new value: none about `u`, and `v` is no longer
available when it reads `u`. A frame constant takes the value it had (`isKVal`). -/
def Cx.redefine (cx : Cx) (S : Facts) (u : ID) : Facts :=
  if cx.isK u then S else
  S.filter fun (l, o) => o.id != u && !(l == .avail && cx.reads o.id u)

/-- A kept value: target value `w` is source value `u` (same ID). An available source value with
the op, aux, auxint, type and arguments of `u` has `u`'s new value: the locations `u` is written
to hold it too. -/
def keptStep (cx : Cx) (S : Facts) (w u : Value) : Except String Facts := do
  argsOK cx S w u
  if !signOK cx w u then throw s!"sign v{w.id}: MOVDreg argument changes its producer"
  if !shapeEq (cx.gty w.id) (cx.fty u.id) then throw s!"shape v{w.id}"
  let pure' := pureArm64 u.op && !u.args.contains u.id
  let eqs : List ID := if !pure' then [] else S.filterMap fun (l, o) =>
    if l == .avail && o.comp.isNone && o.id != u.id &&
        ((cx.f.value? o.id).map (sameConst · u)).getD false then some o.id else none
  let S := clobberFacts cx S w
  let S := cx.redefine S u.id
  let S ← if u.op == .MakeResult then
    -- the components are the arguments, read from the locations they are written to: those
    -- locations hold the arguments exactly afterwards
    let h := cx.lc.home w.id
    let t := cx.gty w.id
    let ts := match t with | .tuple ts => ts | _ => []
    let same (l : Loc) (j : Nat) : Bool :=
      match w.args[j]?, u.args[j]? with
      | some a', some a =>
        (match readLoc (cx.lc.home a') (cx.gty a') with
          | some (.loc l') => l' == l
          | _ => false) &&
        S.holds l (cx.canon a) && shapeEq (ts.getD j .other) (cx.fty a) &&
          shapeEq (cx.gty a') (cx.fty a)
      | _, _ => false
    let ws := writeLocs h t
    let isTup := match t with | .tuple _ => true | _ => false
    if isTup && ws.all (fun (l, j) => match j with | some j => same l j | none => false) then
      let S := (killLocs h t).foldl (fun S l => killLoc cx.tabs l S) S
      pure ((ws.flatMap fun (l, j) => match j.bind (u.args[·]?) with
        | some a => [exactF l u.id j, exactF l (cx.canon a)]
        | none => []) ++ S)
    else pure (writeFacts cx S w (cx.canon u.id))
  else pure (writeFacts cx S w (cx.canon u.id))
  let written := (writeLocs (cx.lc.home w.id) (cx.gty w.id)).flatMap fun (l, j) =>
    eqs.map fun v => exactF l v j
  pure (written ++ (if pure' then [exactF .avail u.id] else []) ++ S)

/-- `regalloc` turns a `KeepAlive x mem` whose `x` is in a register or rematerialisable into
`Copy mem`, or into `VarLive {name} mem` when `x` is the address of a stack object
(`regalloc.go`, `OpKeepAlive`): all three are the memory. -/
def isKeepAliveCopy (u w : Value) : Bool :=
  u.op == .KeepAlive && (w.op == .Copy || w.op == .VarLive) && u.type == w.type &&
    u.args.size == 2 && w.args.size == 1

/-- A kept `KeepAlive` that became `Copy mem` or `VarLive mem`. -/
def keepAliveStep (cx : Cx) (S : Facts) (w u : Value) : Except String Facts := do
  let (some a', some a) := (w.args[0]?, u.args[1]?) | throw s!"keepalive v{w.id}"
  argOK cx S a' a none
  if !shapeEq (cx.gty w.id) (cx.fty u.id) then throw s!"shape v{w.id}"
  let S := cx.redefine (clobberFacts cx S w) u.id
  pure (writeFacts cx S w u.id)

/-- A move (`Copy`, `LoadReg`, `StoreReg`): the facts of the argument's location, at the value's
shape, are copied to the destination. A move out of `ZERO` holds the zero constant `zo` (the
source constant the argument is, if any). -/
def moveStep (cx : Cx) (S : Facts) (w : Value) (zo : Option ID) : Except String Facts := do
  let some a' := w.args[0]? | throw s!"move v{w.id} without argument"
  if w.args.size != 1 then throw s!"move v{w.id} arity"
  let t := cx.gty w.id
  let src : List Orig ← match readLoc (cx.lc.home a') (cx.gty a') with
    | none => throw s!"stuck-read v{a'} has no home"
    | some (.loc l) =>
      pure (S.filterMap fun (l', o) =>
        if l' == l && shapeEq (cx.origTy o) t && composes (cx.origTy o) (cx.gty a') then
          some { o with weak := false }
        else none)
    | some .zero =>
      pure (match zo with
        | some u =>
          if cx.isZeroConst u && shapeEq (cx.gty a') t && shapeEq (cx.fty u) t then
            [⟨cx.canon u, none, false⟩]
          else []
        | none => [])
    | some _ => pure []
  let S := clobberFacts cx S w
  let h := cx.lc.home w.id
  let S := (killLocs h t).foldl (fun S l => killLoc cx.tabs l S) S
  let new := (writeLocs h t).flatMap fun (l, j) => match j with
    | none => src.map (l, ·)
    | some _ => []
  pure (new ++ S)

/-- A rematerialised frame constant: target value `w` recomputes source constant `u`. -/
def rematStep (cx : Cx) (S : Facts) (w u : Value) : Except String Facts := do
  if !isKVal cx.f u then throw s!"remat v{w.id}: v{u.id} is not a frame constant"
  if !sameOp u w then throw s!"remat v{w.id}: differs from v{u.id}"
  if !shapeEq (cx.gty w.id) (cx.fty u.id) then throw s!"shape v{w.id}"
  argsOK cx S w u
  pure (writeFacts cx (clobberFacts cx S w) w (cx.canon u.id))

/-- The certificate: each block's entry facts (after its phis), and for each new target value the
source constant it rematerialises. -/
structure Cert where
  ins : Array Facts
  remat : Array (Option ID)
  deriving Inhabited

/-- The source constant target value `a'` is: itself if kept, else its rematerialisation hint. -/
def constOf (cx : Cx) (cert : Cert) (a' : ID) : Option ID :=
  match cx.g.value? a', cx.f.value? a' with
  | some x, some y => if sameOp y x then some a' else (cert.remat[a']?).join
  | _, _ => (cert.remat[a']?).join

/-- A new target value (not a source value): a move or a rematerialised constant. -/
def newStep (cx : Cx) (cert : Cert) (S : Facts) (w : Value) : Except String Facts := do
  if w.op == .Copy || w.op == .LoadReg || w.op == .StoreReg then
    moveStep cx S w (w.args[0]?.bind (constOf cx cert))
  else
    let some u := ((cert.remat[w.id]?).join <|> some w.id).bind cx.f.value?
      | throw s!"new v{w.id} ({w.op.name}) has no source"
    rematStep cx S w u

/-- Run target value `d` against the source order `os`: the facts after it and the source
values left. -/
def stepValue (cx : Cx) (cert : Cert) (S : Facts) (d : ID) (os : List ID) :
    Except String (Facts × List ID) := do
  let some w := cx.g.value? d | throw s!"stuck v{d} is not in the target"
  if w.op == .Phi then
    if w.args.all (cx.lc.home · == cx.lc.home d) then pure (S, os)
    else throw s!"phi v{d}: an argument has another home"
  else
    match cx.f.value? d with
    | some u =>
      if os.contains d then
        if !sameOp u w && !isKeepAliveCopy u w then throw s!"kept v{d} differs from the source"
        -- the source frame constants the target does not issue before `d`
        let pre := os.takeWhile (· != d)
        if !pre.all cx.isK then
          throw s!"order v{d}: source values {pre.filter (!cx.isK ·)} skipped"
        let S ← if sameOp u w then keptStep cx S w u else keepAliveStep cx S w u
        pure (S, (os.dropWhile (· != d)).drop 1)
      else pure (← newStep cx cert S w, os)
    | none => pure (← newStep cx cert S w, os)

/-- Run the target values `ds` of a block against the source order `os`; the facts at the end
and the source values left (frame constants the target does not issue). -/
def walk (cx : Cx) (cert : Cert) : Facts → List ID → List ID → Except String (Facts × List ID)
  | S, [], os => pure (S, os)
  | S, d :: ds, os => do
    let (S, os) ← stepValue cx cert S d os
    walk cx cert S ds os

/-- The facts at the entry of block `s` along its `i`th incoming edge, from the facts `S` at the
end of the predecessor: every phi's home holds its `i`th argument; then the phis take their
values. -/
def phiEdge (cx : Cx) (S : Facts) (s : ID) (i : Nat) : Except String Facts := do
  let some sb := cx.f.block? s | throw s!"edge to b{s}, which is not in the source"
  let phis := sb.values.toList.filterMap fun id => match cx.f.value? id with
    | some p => if p.op == .Phi then some p else none
    | none => none
  let mut new : Facts := []
  for p in phis do
    let some a := p.args[i]? | throw s!"phi v{p.id}: no argument {i}"
    match readLoc (cx.lc.home p.id) (cx.fty p.id) with
    | some (.loc l) =>
      let a := cx.canon a
      let tp := cx.fty p.id
      let ta := cx.fty a
      -- exact: the phi is its argument at the phi's shape, which reading `l` at that shape
      -- gives; weak: only when that composes with the argument's shape
      if S.holdsExact l a then
        new := (l, ⟨p.id, none, !shapeEq tp ta⟩) :: new
      else if S.holds l a then
        if !composes tp ta then throw s!"phi-shape v{p.id} v{a}"
        new := (l, ⟨p.id, none, true⟩) :: new
      else
        throw s!"phi-edge v{p.id} ({repr l}) does not hold v{a} at the end of b{sb.preds[i]?.map (·.b)}"
    | _ => throw s!"phi-home v{p.id} has no single location"
  let ids := phis.map (·.id)
  pure (new ++ S.filter fun (l, o) =>
    !ids.contains o.id && !(l == .avail && ids.any (cx.reads o.id ·)))

/-- Facts `T` hold whenever facts `S` do (a weak fact follows from the exact one). -/
def sub (T S : Facts) : Bool :=
  T.all fun (l, o) => S.contains (l, o) || (o.weak && S.contains (l, { o with weak := false }))

/-- `stepTermL` reads control `j` of a block of kind `k` (control 0 of an arm64 kind, `If`,
`JumpTable`, `Ret`). -/
def readsControl (k : BlockKind) (j : Nat) : Bool :=
  j == 0 && (k.isArm64 || k == .If || k == .JumpTable || k == .Ret)

/-- Target value `a'` can be read (`LocState.read` is not `stuck`). -/
def readable (cx : Cx) (a' : ID) : Bool := (readLoc (cx.lc.home a') (cx.gty a')).isSome

/-- The terminators of source block `b` and target block `b'` agree on everything `stepTermL`
reads, and the target's controls that it reads hold the source's (the others are read from
their homes by `stepTermLoc` and must not be `stuck`). -/
def termOK (cx : Cx) (S : Facts) (b b' : Block) : Except String Unit := do
  if !(b.kind == b'.kind && b.auxInt == b'.auxInt && b.aux == b'.aux && b.succs == b'.succs &&
      b.controls.size == b'.controls.size) then
    throw s!"block b{b.id} differs from the source"
  for h : j in [0:b.controls.size] do
    let c := b.controls[j]
    let c' := b'.controls[j]!
    match cx.f.value? c, cx.g.value? c' with
    | some u, some w =>
      if w.op == .MakeResult then
        if readsControl b.kind j then
          if c' != c || !sameOp u w then throw s!"control b{b.id}: MakeResult differs"
          for h : k in [0:w.args.size] do argOK cx S w.args[k] (u.args[k]!) none
        else if !w.args.all (readable cx) then throw s!"stuck-read control b{b.id}"
      else if readsControl b.kind j then argOK cx S c' c none
      else if !readable cx c' then throw s!"stuck-read control b{b.id}"
    | _, _ => throw s!"control b{b.id}: v{c}/v{c'} missing"

/-- Check block `bid` from its certified entry facts: values, terminator, outgoing edges. -/
def checkBlock (cx : Cx) (cert : Cert) (bid : ID) : Except String Unit := do
  let some b := cx.f.block? bid | throw s!"b{bid} is not in the source"
  let some b' := cx.g.block? bid | throw s!"b{bid} is not in the target"
  -- a block whose source order is not a schedule is stuck in the source
  let some order := (cx.sc.sched[bid]?).join | pure ()
  let S0 := cert.ins.getD bid []
  let (S, rest) ← walk cx cert S0 b'.values.toList order.toList
  if !rest.all cx.isK then throw s!"order b{bid}: source values {rest.filter (!cx.isK ·)} missing"
  termOK cx S b b'
  for e in b.succs do
    let E ← phiEdge cx S e.b e.i
    if !sub (cert.ins.getD e.b []) E then throw s!"cert b{bid}->b{e.b}: entry facts not implied"

/-- The whole check against a certificate. -/
def checkWith (cx : Cx) (cert : Cert) : Except String Unit := do
  if cx.f.lowered != cx.g.lowered then throw "lowered: source and target differ in Func.lowered"
  if cx.g.entry != cx.f.entry || cx.g.ownAux != cx.f.ownAux then throw "entry or signature differs"
  if !(cert.ins.getD cx.f.entry []).isEmpty then throw "cert: entry facts"
  for bid in cx.f.blocks do checkBlock cx cert bid

/-! ## The untrusted certificate -/

/-- The facts in both lists. -/
def inter (S T : Facts) : Facts := S.filterMap fun (l, o) =>
  if T.contains (l, o) then some (l, o)
  else if T.contains (l, { o with weak := !o.weak }) then some (l, { o with weak := true })
  else none

/-- Rematerialisation hints: every new target value whose op, aux, auxint, type and arguments
are those of a source frame constant. -/
def rematHints (f g : Func) : Array (Option ID) := Id.run do
  let key (v : Value) : String × Option AuxRef × Int64 × TypeRef × List ID :=
    (v.op.name, v.aux, v.auxInt, v.type, v.args.toList)
  let mut m : Std.HashMap (String × Option AuxRef × Int64 × TypeRef × List ID) ID := {}
  for o in f.valueTab do
    if let some v := o then
      if isKVal f v && !m.contains (key v) then m := m.insert (key v) v.id
  let mut out := Array.replicate g.valueTab.size none
  for o in g.valueTab do
    if let some w := o then
      if kOp w.op then
        if let some u := m[key w]? then
          if u != w.id then out := out.set! w.id (some u)
  return out

/-- The block entry facts, by forward iteration from the entry (no facts) with intersection at
merges, until stable or `passes` rounds have run. -/
def certify (cx : Cx) (passes : Nat := 64) : Cert := Id.run do
  let remat := rematHints cx.f cx.g
  let nb := cx.f.blockTab.size
  let rpo := (GoFV.SSA.Analysis.postorder cx.f).reverse
  let mut ins : Array (Option Facts) := (Array.replicate nb none).set! cx.f.entry (some [])
  for _ in [0:passes] do
    let mut changed := false
    for bid in rpo do
      let some S0 := (ins[bid]?).join | continue
      let cert : Cert := { ins := ins.map (·.getD []), remat }
      let some b := cx.f.block? bid | continue
      let some b' := cx.g.block? bid | continue
      let some order := (cx.sc.sched[bid]?).join | continue
      let S := match walk cx cert S0 b'.values.toList order.toList with
        | .ok (S, _) => S
        | .error _ => []
      for e in b.succs do
        let E := match phiEdge cx S e.b e.i with
          | .ok E => E
          | .error _ => []
        let old := (ins[e.b]?).join
        let new := match old with
          | none => E
          | some T => inter T E
        if old != some new then
          ins := ins.set! e.b (some new)
          changed := true
    if !changed then break
  return { ins := ins.map (·.getD []), remat }

/-- The regalloc check with its own certificate (`.ok ()`: `g` refines `f`). -/
def checkRA (tabs : Tables) (f g : Func) : Except String Unit :=
  let cx := Cx.make tabs f g
  checkWith cx (certify cx)

end GoFV.Opt.RegallocCheck

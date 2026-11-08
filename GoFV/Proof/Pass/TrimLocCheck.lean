import GoFV.Proof.SimLocSign

variable [GoFV.SSA.Sem.Addrs]

/-!
# `trimRelB`: the decided relation of `trim`'s input and output over `runLoc`

`trim` (#412) splices `Plain` blocks into their successor. Under `runLoc` a `Phi` does nothing
(it only checks that its arguments share its home), so a block is its non-`Phi` values and its
terminator; an entry of a kept block `t` of the output `g` along an edge `p → t` corresponds to
the entry of the edge's old target `x` in the input `f`, from which `f` runs through the removed
blocks `x → … → t` (each `Plain`, without controls) and then `t`. `chaseLoc f g n x` follows that
chain (fuel `n`) and returns `t` and the non-`Phi` values `f` runs on the way, including `t`'s.

`trimRelB f g` holds when:

* **ctx**: `f` and `g` have the same entry, `ownAux`, homes (`low.regAlloc`), temporary
  registers (`low.tempRegs`), value-table size and `lowered`;
* **values**: every value of `g` is a value of `f` with the same op and type, and a non-`Phi`
  one equal up to position, use count and block;
* **entry**: the entry of `f` is an entry point (`entryLocB`) of the entry of `g`;
* **kept**: every block of `g` is a block of `f` with the same kind, controls and aux (up to
  position and prediction) and as many successors, and each successor of `f`'s block is an
  entry point of the corresponding successor of `g`'s;
* **closed**: the non-`Phi` values of `g`'s blocks, their arguments and the controls (and a
  `MakeResult` control's arguments) are values of `g`;
* **phis**: every `Phi` of a block of `g` has its arguments' home (so it never gets stuck);
* **signs**: `f` and `g` have the same `signView` at every ID (a dropped `Phi` and an absent value
  look alike), so `runLoc`'s `MOVDreg`/`MOVDnop` read the same upper bits (`LocCtx.signOf`).

`trim_refinesLoc` (`GoFV.Proof.Pass.TrimLoc`) proves that `trimRelB f g = true` makes `g`
refine `f` under `runLoc`.
-/

namespace GoFV.Proof.TrimLoc

open GoFV.SSA GoFV.SSA.Sem

/-- The values among `ids` that are not `Phi`s of `f` (IDs that are not values are kept). -/
def npLoc (f : Func) (ids : List ID) : List ID :=
  ids.filter fun id => !((f.value? id).any (·.op == .Phi))

/-- From the entry of `f`'s block `x`: the first block of `g` reached through blocks `g` does not
have (each `Plain` without controls), and the non-`Phi` values `f` runs up to the end of that
block. -/
def chaseLoc (f g : Func) : Nat → ID → Option (ID × List ID)
  | 0, _ => none
  | n + 1, x =>
    match f.block? x with
    | none => none
    | some c =>
      if (g.block? x).isSome then some (x, npLoc f c.values.toList)
      else if c.kind == .Plain && c.controls.isEmpty then
        match c.succs[0]? with
        | some e => (chaseLoc f g n e.b).map fun r => (r.1, npLoc f c.values.toList ++ r.2)
        | none => none
      else none

/-- The fuel of `chaseLoc`: a chain visits each block of `f` at most once. -/
def chaseFuel (f : Func) : Nat := f.blockTab.size + 1

/-- Entering `f` at `x` is entering `g` at `t`: the chain from `x` ends at `t`, and the non-`Phi`
values of `g`'s block `t` are those `f` runs on the way. -/
def entryLocB (f g : Func) (x t : ID) : Bool :=
  match chaseLoc f g (chaseFuel f) x with
  | some (t', code) =>
    t' == t && match g.block? t with
      | some T => npLoc g T.values.toList == code
      | none => false
  | none => false

/-- A block without the fields `trim` may change (or `runLoc` does not read). -/
def eraseBT (b : Block) : Block :=
  { b with pos := default, likely := .unknown, values := #[], succs := #[], preds := #[] }

/-- A value without the fields `trim` may change on a non-`Phi` (or `runLoc` does not read). -/
def eraseVT (v : Value) : Value := { v with pos := default, uses := 0, block := 0 }

/-- The homes of `f`'s values by ID (`LocCtx.make`'s). -/
def locHomes (f : Func) : Array (Option Location) :=
  let n := f.valueTab.size
  let none' : Array (Option Location) := Array.replicate n none
  match f.low.regAlloc with
  | some (_, es) => es.foldl (fun a (id, l) => if id < n then a.set! id (some l) else a) none'
  | none => none'

/-- **ctx** -/
def ctxLocB (f g : Func) : Bool :=
  f.entry == g.entry && f.ownAux == g.ownAux && f.low.regAlloc == g.low.regAlloc &&
    f.low.tempRegs == g.low.tempRegs && f.valueTab.size == g.valueTab.size &&
    f.lowered == g.lowered

/-- **values**, for value `id`; a `Select0`/`Select1` of `g` also has its arguments in `g` (a
`MOVDreg` of it reads whether it selects from `LDPSW`, `Arm64.signExtendsIn`). -/
def valLocB (f g : Func) (id : ID) : Bool :=
  match g.value? id with
  | none => true
  | some v' =>
    match f.value? id with
    | none => false
    | some v => v'.id == id && v.op == v'.op && v.type == v'.type &&
      (v'.op == .Phi || eraseVT v == eraseVT v') &&
      (!(v'.op == .Select0 || v'.op == .Select1) || v'.args.all fun a => (g.value? a).isSome)

/-- **kept**, for block `K'` of `g`. -/
def keptLocB (f g : Func) (K' : Block) : Bool :=
  match f.block? K'.id with
  | none => false
  | some Kf =>
    eraseBT K' == eraseBT Kf && K'.succs.size == Kf.succs.size &&
      (List.range Kf.succs.size).all fun i =>
        match Kf.succs[i]?, K'.succs[i]? with
        | some e, some e' => entryLocB f g e.b e'.b
        | _, _ => false

/-- `id` is a value of `g`. -/
def hasV (g : Func) (id : ID) : Bool := (g.value? id).isSome

/-- **closed**, for block `K'` of `g`. -/
def closedLocB (g : Func) (K' : Block) : Bool :=
  (npLoc g K'.values.toList).all (fun id =>
    match g.value? id with
    | some v => v.args.all (hasV g)
    | none => false) &&
  K'.controls.all fun c =>
    match g.value? c with
    | some v => v.op != .MakeResult || v.args.all (hasV g)
    | none => false

/-- **phis**, for block `K'` of `g` with homes `hs`. -/
def phisLocB (g : Func) (hs : Array (Option Location)) (K' : Block) : Bool :=
  K'.values.all fun id =>
    match g.value? id with
    | some v => v.op != .Phi || v.args.all fun a => (hs[a]?).join == (hs[id]?).join
    | none => true

/-- The blocks of `g`, with their table index. -/
def blocksIdx (g : Func) : List (ID × Block) :=
  (List.range g.blockTab.size).filterMap fun i => (g.block? i).map (i, ·)

/-- **signs**: `f` and `g` have the same `signView` at every ID (what `runLoc`'s `MOVDreg`
reads of the function, `LocCtx.signOf`). -/
def signsLocB (f g : Func) : Bool :=
  (List.range f.valueTab.size).all fun id =>
    signView f.value? (f.value? id) == signView g.value? (g.value? id)

/-- **`trimRelB f g`**: see the module comment. -/
def trimRelB (f g : Func) : Bool :=
  let hs := locHomes g
  ctxLocB f g &&
    (List.range g.valueTab.size).all (valLocB f g) &&
    entryLocB f g f.entry g.entry &&
    (blocksIdx g).all (fun (i, K') =>
      K'.id == i && keptLocB f g K' && closedLocB g K' && phisLocB g hs K') &&
    signsLocB f g

end GoFV.Proof.TrimLoc

import GoFV.Opt.DeadStore
import GoFV.Opt.CSE

/-!
# dse's checker

`DSE.drel tabs f g` accepts `g` as a result of `dse` on `f` when `g` has `f`'s control-flow
graph, blocks and values except for eliminated stores (`elimV`: a `Store`/`Zero`/`Move` became
`Copy mem`), and the bytes every eliminated store writes are overwritten before anything reads
them. The second part is checked forward along the memory chains with a *pending set* per memory
value (`pend`): the byte ranges (an allocation named by an `Addr`/`LocalAddr` base, offsets
`[lo, hi)`) where the source's memory may differ from the target's at that value.

* An eliminated store adds its range (its pointer an `OffPtr` chain from an `Addr`/`LocalAddr`
  base, `ptrLoc`); a kept `Store`/`Zero`/`Move` removes the range it writes (`sub`), a kept
  `VarDef` its variable; a kept `Move` must read an allocation with no pending range; any other
  op has an empty pending set (`pendStep`).
* A value with pending ranges is used only in its block, by no `Phi` and no control, as the
  memory argument (last, once) of a `Store`/`Zero`/`Move`/`VarDef`, or by an op that ignores
  its arguments' values (`LocalAddr`, `InlMark`) (`usesOK`).
* Every block's schedule in `g` lists the roots of `g` in `f`'s order (`schedOK`).

`pendArr` computes the pending sets along each block's source schedule; the checker then
verifies `pendStep` at every value, so the proof uses only the local equations.
`GoFV.Proof.DSE.dse_refines` proves that an accepted result refines its input.
-/

namespace GoFV.Opt

open GoFV.SSA

namespace DSE

/-- A pending byte range: an allocation and the offsets `[lo, hi)`. -/
abbrev Iv := CSE.Alloc × Int × Int

/-- The number of bytes a `Store` (its aux type's shape), `Zero` or `Move` (its auxint) writes. -/
def wsize (tabs : Tables) (x : Value) : Nat :=
  if x.op == .Store then (Sem.auxTy tabs x.aux).size else x.auxInt.toInt.toNat

/-- The allocation pointer `p` points into: its `OffPtr` chain's `Addr`/`LocalAddr` base. -/
def ptrAlloc (tabs : Tables) (f : Func) (p : ID) : Option CSE.Alloc :=
  CSE.allocOf tabs f (CSE.baseOff tabs f 64 p 0).1

/-- The allocation and offset pointer `p` points to, the offset in `[0, 2^63)`. -/
def ptrLoc (tabs : Tables) (f : Func) (p : ID) : Option (CSE.Alloc × Int) :=
  match ptrAlloc tabs f p with
  | some a =>
    let o := (CSE.baseOff tabs f 64 p 0).2
    if 0 ≤ o ∧ o < 2 ^ 63 then some (a, o) else none
  | none => none

/-- The byte range a `Store`/`Zero`/`Move` writes, if its pointer has a `ptrLoc`. -/
def range? (tabs : Tables) (f : Func) (x : Value) : Option Iv :=
  match x.args[0]? with
  | some p => (ptrLoc tabs f p).map fun (a, o) => (a, o, o + wsize tabs x)
  | none => none

/-- `iv` without the bytes of `r`. -/
def sub (r iv : Iv) : List Iv :=
  if iv.1 = r.1 then
    (if iv.2.1 < min iv.2.2 r.2.1 then [(iv.1, iv.2.1, min iv.2.2 r.2.1)] else []) ++
      (if max iv.2.1 r.2.2 < iv.2.2 then [(iv.1, max iv.2.1 r.2.2, iv.2.2)] else [])
  else [iv]

/-- The ops dse eliminates. -/
def elimOp (op : Op) : Bool := op == .Store || op == .Zero || op == .Move

/-- `gv` is the eliminated store `fv`: `Copy` of its memory argument. -/
def elimV (fv gv : Value) : Bool :=
  elimOp fv.op && gv.op == .Copy && gv.aux == none && gv.auxInt == 0 && gv.id == fv.id &&
    gv.type == fv.type && gv.block == fv.block &&
    match fv.args.back? with
    | some m => gv.args == #[m]
    | none => false

/-- `gv` is `fv` (as far as `run` reads it). -/
def sameV (fv gv : Value) : Bool :=
  gv.id == fv.id && gv.op == fv.op && gv.aux == fv.aux && gv.auxInt == fv.auxInt &&
    gv.type == fv.type && gv.block == fv.block && gv.args == fv.args

/-- The pending set of value `x` from those of its arguments (`none`: not allowed). -/
def pendStep (tabs : Tables) (f g : Func) (P : ID → List Iv) (x : ID) : Option (List Iv) :=
  match f.value? x, g.value? x with
  | some fv, some gv =>
    let pm := match fv.args.back? with
      | some m => P m
      | none => []
    if elimV fv gv then
      (range? tabs f fv).map fun iv => if iv.2.1 < iv.2.2 then pm ++ [iv] else pm
    else if fv.op == .Store || fv.op == .Zero then
      some (match range? tabs f fv with
        | some r => pm.flatMap (sub r)
        | none => pm)
    else if fv.op == .Move then
      if pm.isEmpty then some []
      else
        match fv.args[1]? with
        | some s =>
          match ptrAlloc tabs f s with
          | some a =>
            if pm.all (·.1 != a) then
              some (match range? tabs f fv with
                | some r => pm.flatMap (sub r)
                | none => pm)
            else none
          | none => none
        | none => none
    else if fv.op == .VarDef then
      some (match fv.aux with
        | some n => pm.filter (·.1 != .local n)
        | none => pm)
    else some []
  | _, _ => some []

/-- The ops that write memory along a chain (their memory argument is the last). -/
def chainOp (op : Op) : Bool := op == .Store || op == .Zero || op == .Move || op == .VarDef

/-- Ops whose value does not depend on their arguments' values. -/
def blindOp (op : Op) : Bool := op == .LocalAddr || op == .InlMark

/-- Every argument of `x` with pending ranges is from `x`'s block and is read by `x` only as the
memory argument of a chain op, or `x` ignores it. -/
def usesOK (f : Func) (P : ID → List Iv) (x : ID) : Bool :=
  match f.value? x with
  | some fv =>
    fv.args.all fun a => (P a).isEmpty ||
      (fv.op != .Phi && (f.value? a).map (·.block) == some fv.block &&
        (blindOp fv.op || (chainOp fv.op && fv.args.back? == some a && !fv.args.pop.contains a)))
  | none => true

/-- The pending sets along each block's source schedule. -/
def pendArr (tabs : Tables) (f g : Func) : Array (List Iv) := Id.run do
  let mut A : Array (List Iv) := Array.replicate f.valueTab.size []
  for b in f.blocks do
    match f.block? b with
    | some fb =>
      match Sem.schedule f fb with
      | some o =>
        for x in o do
          A := A.set! x ((pendStep tabs f g (fun a => A.getD a []) x).getD [])
      | none => pure ()
    | none => pure ()
  return A

/-- Value `x`: kept or an eliminated store. -/
def valueOK (f g : Func) (x : ID) : Bool :=
  match f.value? x with
  | none => true
  | some fv =>
    match g.value? x with
    | some gv => sameV fv gv || elimV fv gv
    | none => false

/-- Block `bid`: the same kind, values and controls, no control with pending ranges. -/
def blockOK (f g : Func) (P : ID → List Iv) (bid : ID) : Bool :=
  match f.block? bid, g.block? bid with
  | some fb, some gb =>
    gb.kind == fb.kind && gb.values == fb.values && gb.controls == fb.controls &&
      fb.controls.all fun c => (P c).isEmpty
  | _, _ => false

/-- Block `bid`: if `f`'s block has a schedule, `g`'s has one listing `g`'s roots in the same
order. -/
def schedOK (f g : Func) (bid : ID) : Bool :=
  match f.block? bid, g.block? bid with
  | some fb, some gb =>
    match Sem.schedule f fb with
    | none => true
    | some oS =>
      match Sem.schedule g gb with
      | some oT => oT.toList.filter (CSE.rootNode g) == oS.toList.filter (CSE.rootNode g)
      | none => false
  | _, _ => false

/-- **dse's output relation** (see the module comment). -/
def drel (tabs : Tables) (f g : Func) : Bool :=
  let A := pendArr tabs f g
  let P := fun x => A.getD x []
  DomCert.cfgView g == DomCert.cfgView f && g.ownAux == f.ownAux &&
  g.valueTab.size == f.valueTab.size &&
  f.blocks.all (blockOK f g P) &&
  (List.range f.valueTab.size).all (fun x =>
    valueOK f g x && decide (pendStep tabs f g P x = some (P x)) && usesOK f P x) &&
  f.blocks.all (schedOK f g)

end DSE

/-- `dse_refines`' fragment: dse fails or the checker accepts its result. -/
def dseFrag (env : PassEnv) (f : Func) : Bool :=
  match env.typ? "Mem" with
  | some mem =>
    match dse env.tables mem f with
    | .ok g => DSE.drel env.tables f g
    | .error _ => true
  | none => true

end GoFV.Opt

import GoFV.Opt.ElimDeadAutos
import GoFV.Opt.DeadStoreCheck
import GoFV.Opt.NilCheckRel

/-!
# dead auto elim's checker

`DAE.arel tabs f g` accepts `g` as a result of `dead auto elim` on `f` when `g` has `f`'s
control-flow graph, blocks and values except for eliminated writes (`elimV`: a `Store`/`Zero`/
`Move`/`VarDef` became `Copy mem`), every eliminated write goes to a frame variable of the set
`E` (`names`), and the address of a variable of `E` is used only as the destination of eliminated
writes. Then the source's and the target's memories differ only in the variables of `E`, which
nothing reads (`#31`).

* `tag x`: the variable whose `LocalAddr` the pointer-typed `x` is, through `OffPtr`/`AddPtr`/
  `PtrIndex`/`Copy` (argument 0); checked locally at every value (`tagOK`). `x` is *tainted* when
  its tag is in `E`.
* A tainted argument is allowed only as argument 0 of a tainted pointer op (`OffPtr`, `AddPtr`,
  `PtrIndex`, `Copy`), as the destination (argument 0) of an eliminated `Store`/`Zero`/`Move`, or
  as the source (argument 1) of an eliminated `Move`; no control is tainted (`usesOK`).
* Every variable of `E` is a frame variable whose address the program cannot rebuild from an
  integer (`unforgeable`: a `PAUTO` whose address is not taken, `Blk.temp`) and is not an
  open-coded defer slot.
* Every block's schedule in `g` lists the roots of `g` in `f`'s order (`DSE.schedOK`).
* Every kept value with a memory- or tuple-shaped argument (shape `mem`/`tuple`) has it last
  and an op of `memOps` (or is a `Phi`), and every kept value whose shape may hold a pointer, a
  blob or a memory has an op of `ptrOps` (`opOK`): the proof treats these ops one by one; any
  other value reads equal arguments in source and target, and its result holds no pointer into
  an eliminated variable.
-/

namespace GoFV.Opt

open GoFV.SSA

namespace DAE

/-- The ops dead auto elim eliminates. -/
def elimOp (op : Op) : Bool := op == .Store || op == .Zero || op == .Move || op == .VarDef

/-- `gv` is the eliminated write `fv`: `Copy` of its memory argument. -/
def elimV (fv gv : Value) : Bool :=
  elimOp fv.op && gv.op == .Copy && gv.aux == none && gv.auxInt == 0 && gv.id == fv.id &&
    gv.type == fv.type && gv.block == fv.block &&
    match fv.args.back? with
    | some m => gv.args == #[m]
    | none => false

/-- Ops whose pointer value points into the allocation of their argument 0. -/
def propOp (op : Op) : Bool := op == .OffPtr || op == .AddPtr || op == .PtrIndex || op == .Copy

/-- The tag of value `fv` from the tags of its arguments. -/
def tagStep (tabs : Tables) (T : ID → Option AuxRef) (fv : Value) : Option AuxRef :=
  if !NilCheck.ptrShaped tabs fv.type then none
  else if fv.op == .LocalAddr then fv.aux
  else if propOp fv.op then (fv.args[0]?).bind T
  else none

/-- The tags, by rounds over the values (checked by `tagOK`). -/
def tagArr (tabs : Tables) (f : Func) : Array (Option AuxRef) := Id.run do
  let mut A : Array (Option AuxRef) := Array.replicate f.valueTab.size none
  for _ in [0:4] do
    for x in List.range f.valueTab.size do
      match f.value? x with
      | some fv => A := A.set! x (tagStep tabs (fun a => A.getD a none) fv)
      | none => pure ()
  return A

/-- The variable an eliminated write writes: `VarDef`'s aux, the tag of the destination
otherwise. -/
def nameOf (T : ID → Option AuxRef) (fv : Value) : Option AuxRef :=
  if fv.op == .VarDef then fv.aux else (fv.args[0]?).bind T

/-- The eliminated variables. -/
def names (f g : Func) (T : ID → Option AuxRef) : List AuxRef :=
  (List.range f.valueTab.size).foldl (fun E x =>
    match f.value? x, g.value? x with
    | some fv, some gv =>
      if elimV fv gv then
        match nameOf T fv with
        | some n => if E.contains n then E else E ++ [n]
        | none => E
      else E
    | _, _ => E) []

/-- A frame variable whose address no integer conversion reaches (`Blk.temp`: not
`Tables.forgeable`), and not an open-coded defer slot. -/
def unforgeable (tabs : Tables) (n : AuxRef) : Bool :=
  !tabs.forgeable n &&
    match tabs.aux? n with
    | some { kind := .name _ _ _ _ _ fl _, .. } => !fl.opendeferslot
    | _ => false

/-- Value `x`: kept or an eliminated write to a variable of `E`. -/
def valueOK (f g : Func) (T : ID → Option AuxRef) (E : List AuxRef) (x : ID) : Bool :=
  match f.value? x with
  | none => true
  | some fv =>
    match g.value? x with
    | some gv =>
      DSE.sameV fv gv || (elimV fv gv && (nameOf T fv).any E.contains)
    | none => false

/-- The uses of tainted values by `x`. -/
def usesOK (f g : Func) (T : ID → Option AuxRef) (E : List AuxRef) (x : ID) : Bool :=
  match f.value? x with
  | none => true
  | some fv =>
    let tainted := fun a => (T a).any E.contains
    let el := match g.value? x with
      | some gv => elimV fv gv
      | none => false
    (List.range fv.args.size).all fun i =>
      match fv.args[i]? with
      | none => true
      | some a =>
        !tainted a ||
          (i == 0 && propOp fv.op && T x == T a) ||
          (el && i == 0 && fv.op != .VarDef) ||
          (el && i == 1 && fv.op == .Move)

/-- Ops whose last argument may be memory- or tuple-shaped (the proof handles them). -/
def memOps : List Op :=
  [.Copy, .LocalAddr, .Convert, .InlMark, .GetG, .GetCallerSP, .Select0, .Select1, .SelectN,
    .MakeResult, .Load, .AtomicLoad32, .AtomicLoad64, .AtomicLoadPtr, .MemEq, .Store, .Zero, .Move,
    .VarDef, .VarLive, .KeepAlive, .NilCheck, .PanicBounds, .StaticCall, .InterCall, .ClosureCall,
    .AtomicStore32, .AtomicStore64, .AtomicAdd32, .AtomicAdd32Variant, .AtomicAdd64,
    .AtomicCompareAndSwap32, .AtomicCompareAndSwap32Variant, .AtomicCompareAndSwap64,
    .AtomicCompareAndSwap64Variant]

/-- Ops whose pointer-, blob- or memory-shaped results the proof handles. -/
def ptrOps : List Op :=
  [.Phi, .Copy, .OffPtr, .AddPtr, .PtrIndex, .LocalAddr, .Addr, .ConstNil, .Convert, .CondSelect,
    .GetG, .GetClosurePtr, .Arg, .ArgIntReg, .InitMem, .Select0, .Select1, .SelectN, .MakeResult,
    .Load, .AtomicLoad32, .AtomicLoad64, .AtomicLoadPtr, .Store, .Zero, .Move, .VarDef, .VarLive,
    .KeepAlive, .NilCheck, .PanicBounds, .StaticCall, .InterCall, .ClosureCall, .AtomicStore32,
    .AtomicStore64, .AtomicAdd32, .AtomicAdd32Variant, .AtomicAdd64, .AtomicCompareAndSwap32,
    .AtomicCompareAndSwap32Variant, .AtomicCompareAndSwap64, .AtomicCompareAndSwap64Variant]

mutual
/-- A shape whose values hold no pointer, blob or memory: integers (a 64-bit one holds at most
an address-less global), booleans, zero-sized, opaque and unknown shapes, composites of
those. -/
def noPtrTy : Sem.Ty → Bool
  | .int _ | .bool | .empty | .opaque _ | .other => true
  | .agg fs _ => noPtrFields fs
  | _ => false
def noPtrFields : List (Nat × Sem.Ty) → Bool
  | [] => true
  | (_, t) :: fs => noPtrTy t && noPtrFields fs
end

/-- A memory or tuple shape. -/
def memTy : Sem.Ty → Bool
  | .mem | .tuple _ => true
  | _ => false

/-- An argument that is not memory- or tuple-shaped. -/
def plainArg (tabs : Tables) (f : Func) (a : ID) : Bool :=
  match f.value? a with
  | some av => !memTy (tabs.ty av.type)
  | none => true

/-- Kept value `fv`: a memory- or tuple-shaped argument only last and only for `memOps` (any
for a `Phi`), a result shape that may hold a pointer only for `ptrOps`. -/
def opOK (tabs : Tables) (f : Func) (fv : Value) : Bool :=
  (fv.op == .Phi || fv.args.all (plainArg tabs f) ||
      (memOps.contains fv.op && fv.args.pop.all (plainArg tabs f))) &&
    (ptrOps.contains fv.op || noPtrTy (tabs.ty fv.type))

/-- Value `x`: eliminated, or a kept value with `opOK`. -/
def keptOK (tabs : Tables) (f g : Func) (x : ID) : Bool :=
  match f.value? x, g.value? x with
  | some fv, some gv => elimV fv gv || opOK tabs f fv
  | _, _ => true

/-- Block `bid`: the same kind, values and controls, no tainted control. -/
def blockOK (f g : Func) (T : ID → Option AuxRef) (E : List AuxRef) (bid : ID) : Bool :=
  match f.block? bid, g.block? bid with
  | some fb, some gb =>
    gb.kind == fb.kind && gb.values == fb.values && gb.controls == fb.controls &&
      fb.controls.all fun c => !(T c).any E.contains
  | _, _ => false

/-- **dead auto elim's output relation** (see the module comment). -/
def arel (tabs : Tables) (f g : Func) : Bool :=
  let A := tagArr tabs f
  let T := fun x => A.getD x none
  let E := names f g T
  DomCert.cfgView g == DomCert.cfgView f && g.ownAux == f.ownAux &&
  g.valueTab.size == f.valueTab.size &&
  E.all (unforgeable tabs) &&
  f.blocks.all (blockOK f g T E) &&
  (List.range f.valueTab.size).all (fun x =>
    valueOK f g T E x && usesOK f g T E x && keptOK tabs f g x &&
      match f.value? x with
      | some fv => tagStep tabs T fv == T x
      | none => T x == none) &&
  f.blocks.all (DSE.schedOK f g)

end DAE

/-- `dead_auto_elim_refines`' fragment: the pass fails or the checker accepts its result. -/
def daeFrag (env : PassEnv) (f : Func) : Bool :=
  match env.typ? "Mem", env.typ? "Flags" with
  | some mem, some flags =>
    match elimDeadAutosGeneric env.tables mem flags (env.abi == 1) f with
    | .ok g => DAE.arel env.tables f g
    | .error _ => true
  | _, _ => true

end GoFV.Opt

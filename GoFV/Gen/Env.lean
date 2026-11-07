import GoFV.Asm.Prog
import GoFV.SSA.RegARM64
import Std.Data.HashMap.Basic

/-!
# What the Phase 3 ports read

The input of the ports of `AllocFrame` … `defframe` (`docs/PASSES3.md` A1–C7, I3 #549): the
function after `trim` (the last section of its `gofv-ssa` file, with the file's definition
tables) and what the companion `gofv-prog 3` file records about the frontend at the two cut
points before `genssa`: `Dcl` when `AllocFrame` starts (`frame` section, `in` lines, with the
names' type facts) and the `genin` section (`curfn.Pos()`, defer state, the wrapped function,
the open-coded defer slots, `f.RegArgs`, the text symbol's `FuncInfo` header). The outputs
(`frame` `out`/`opt`/`merge`/`stack`, `prog0`, the metadata symbols of `asm`) are never read.

Names (`*ir.Name`s of `Dcl`) are identified by their `.prog` number `n<k>`; the `name`
definition links each one to the `.ssa` aux object of the same `*ir.Name` (`NameDef.aux`).
Registers are obj register numbers (`REG_R0 = 8192`, …) as `v.Reg()` returns them.
-/

namespace GoFV.Gen

open GoFV.SSA
open GoFV.Asm (NameDef DclEntry GenIn RegArg)

/-- A `Dcl` name: its `.prog` definition and type facts, and (when the `.ssa` file references
the same object) its aux number and the `.ssa` type with full structure. -/
structure NameInfo where
  n : Nat
  d : NameDef
  /-- The `.prog` type facts (size, alignment, pointer data, pointer mask, `String()`). -/
  ty : GoFV.Asm.TypeDef
  /-- The `.ssa` type of the aux object (`AuxKind.name`'s type), with kind and structure. -/
  ssaType : Option TypeRef
  deriving Inhabited

namespace NameInfo

def cls (x : NameInfo) : String := x.d.cls
def size (x : NameInfo) : Except String Int :=
  match x.ty.size with | some s => pure s | none => throw s!"name n{x.n}: size not calculated"
def align (x : NameInfo) : Except String Int :=
  match x.ty.align with | some s => pure s | none => throw s!"name n{x.n}: alignment not calculated"
def ptrdata (x : NameInfo) : Except String Int :=
  match x.ty.ptrdata with | some s => pure s | none => throw s!"name n{x.n}: ptrdata not calculated"
def hasPointers (x : NameInfo) : Except String Bool :=
  match x.ty.hasPtr with | some b => pure b | none => throw s!"name n{x.n}: hasptr not calculated"

end NameInfo

/-- `AllocFrame`'s result (A1, A2): `curfn.Dcl` after it (frame offsets and flags), the
truncated tail (`FuncDebug.OptDcl`), the MergeLocals partitions (leader, followers in order;
leaders in `Dcl` order) and the frame sizes — the `frame` section's `out`, `opt`, `merge` and
`stack` lines. -/
structure FrameOut where
  dcl : Array DclEntry
  optDcl : Array DclEntry
  merges : Array (Nat × Array Nat)
  stksize : Int
  stkptrsize : Int
  stkalign : Int
  deriving Inhabited

/-- An `ssa.Spill` of `f.RegArgs` (A3, `buildssa` tail): obj register, frame offset, and the
`.ssa` type of the register piece. -/
structure RegSpill where
  reg : Int
  off : Int
  type : TypeRef
  deriving DecidableEq, Inhabited, Repr

/-- The ports' input (see the module doc). -/
structure Env where
  /-- The `.ssa` file (header and `config` lines). -/
  file : ExportFile
  /-- The function after `trim`. -/
  f : Func
  /-- The definition tables of the whole `.ssa` file plus its `frontend` block. -/
  tabs : Tables
  /-- The `.prog` file's `config` lines (`docs/contracts/export.md`, "gofv-prog 3"). -/
  progConfig : Array (String × Token)
  /-- `Dcl` names by `.prog` number (`none`: not a name number). -/
  names : Array (Option NameInfo)
  /-- `.ssa` aux number → `.prog` name number, for the names of `Dcl`. -/
  auxName : Std.HashMap AuxRef Nat
  /-- `Dcl` when `AllocFrame` starts, in order (`frame` `in` lines). -/
  dclIn : Array DclEntry
  /-- The `Dcl` flags when `AllocFrame` starts, by name number (static ones such as `outregs`
  are read from here). -/
  inFlags : Std.HashMap Nat GoFV.Asm.NameFlags
  genin : GenIn
  /-- `.prog` symbol numbers of the input sections (`frame`, `genin`): name and ABI. -/
  inSyms : Std.HashMap Nat (GoStr × Nat)
  /-- `f.RegAlloc` by value ID. -/
  locs : Array (Option Location)
  /-- `f.tempRegs` by value ID (dense register numbers). -/
  temps : Array (Option Nat)

namespace Env

def name? (e : Env) (n : Nat) : Option NameInfo := (e.names[n]?).join

def name (e : Env) (n : Nat) : Except String NameInfo :=
  match e.name? n with | some x => pure x | none => throw s!"no name n{n}"

def value (e : Env) (id : ID) : Except String Value :=
  match e.f.value? id with | some v => pure v | none => throw s!"no value v{id}"

def block (e : Env) (id : ID) : Except String Block :=
  match e.f.block? id with | some b => pure b | none => throw s!"no block b{id}"

def typeDef (e : Env) (t : TypeRef) : Except String TypeDef :=
  match e.tabs.type? t with | some d => pure d | none => throw s!"no type t{t}"

def auxDef (e : Env) (a : AuxRef) : Except String AuxDef :=
  match e.tabs.aux? a with | some d => pure d | none => throw s!"no aux a{a}"

/-- The `.prog` name of an `*ir.Name` aux object (`none`: not a `Dcl` name). -/
def nameOfAux? (e : Env) (a : AuxRef) : Option Nat := e.auxName[a]?

/-- `config <key>` of the `.ssa` file. -/
def config? (e : Env) (key : String) : Option (Array Token) :=
  (e.file.config.find? (·.1 == key)).map (·.2)

/-- `config <key>` of the `.prog` file. -/
def progConfig? (e : Env) (key : String) : Option Token :=
  (e.progConfig.find? (·.1 == key)).map (·.2)

private def wordNat? : Token → Option Nat
  | .word w => w.toNat?
  | _ => none

/-- A natural-number `.prog` config value (`0`/`1` flags included). -/
def progConfigNat (e : Env) (key : String) : Except String Nat :=
  match (e.progConfig? key).bind wordNat? with
  | some n => pure n
  | none => throw s!"prog config {key}: missing or not a number"

/-- `base.Flag.N` (`-N`): 0 for the corpus. -/
def flagN (e : Env) : Except String Nat := e.progConfigNat "flagN"

/-- `base.Flag.CompilingRuntime`. -/
def compilingRuntime (e : Env) : Except String Bool := (· != 0) <$> e.progConfigNat "compilingruntime"

/-- `base.Debug.MergeLocals`. -/
def mergeLocals (e : Env) : Except String Nat := e.progConfigNat "mergelocals"

/-- `base.Ctxt.Flag_linkshared`. -/
def linkshared (e : Env) : Except String Bool := (· != 0) <$> e.progConfigNat "flaglinkshared"

/-- `base.Ctxt.Flag_locationlists`. -/
def locationlists (e : Env) : Except String Bool := (· != 0) <$> e.progConfigNat "locationlists"

/-- `f.RegAlloc[v.ID]`. -/
def loc? (e : Env) (v : ID) : Option Location := (e.locs[v]?).join

/-- The obj register number of dense register `r` (`Register.objNum`). -/
def objReg (r : Nat) : Except String Int :=
  match ARM64.registers[r]? with
  | some x => pure x.objNum
  | none => throw s!"no register {r}"

/-- `v.Reg()`: the obj register of `f.RegAlloc[v.ID]`, which must be a register. -/
def reg (e : Env) (v : ID) : Except String Int :=
  match e.loc? v with
  | some (.reg r) => objReg r
  | some l => throw s!"v{v}: location {repr l} is not a register"
  | none => throw s!"v{v}: no location"

/-- `v.Reg0()`: the first register of a `LocPair` (0 when nil? no: Go panics on a nil entry). -/
def reg0 (e : Env) (v : ID) : Except String Int :=
  match e.loc? v with
  | some (.pair (some r) _) => objReg r
  | l => throw s!"v{v}: Reg0 of {repr l}"

/-- `v.Reg1()`. -/
def reg1 (e : Env) (v : ID) : Except String Int :=
  match e.loc? v with
  | some (.pair _ (some r)) => objReg r
  | l => throw s!"v{v}: Reg1 of {repr l}"

/-- `v.RegTmp()`: the obj register of `f.tempRegs[v.ID]`. -/
def regTmp (e : Env) (v : ID) : Except String Int :=
  match (e.temps[v]?).join with
  | some r => objReg r
  | none => throw s!"v{v}: no temp register"

/-- `v.Type.IsTuple()`. -/
def isTuple (e : Env) (t : TypeRef) : Except String Bool := do
  return (← e.typeDef t).kind == .TUPLE

/-- `v.ResultReg()`: `Reg0()` for tuple-typed values, else `Reg()`. -/
def resultReg (e : Env) (v : Value) : Except String Int := do
  if ← e.isTuple v.type then e.reg0 v.id else e.reg v.id

/-- The symbol name and ABI of an `*obj.LSym` aux. -/
def lsymOf (e : Env) (a : AuxRef) : Except String (GoStr × Nat) := do
  match (← e.auxDef a).kind with
  | .sym name abi .. => pure (name, abi)
  | _ => throw s!"aux a{a} is not a symbol"

/-- The symbol of an `*obj.LSym` aux, or the callee symbol of an `*AuxCall` (`AddAux`). -/
def lsym (e : Env) (a : AuxRef) : Except String (GoStr × Nat) := do
  match (← e.auxDef a).kind with
  | .sym name abi .. => pure (name, abi)
  | .call (some fn) _ => e.lsymOf fn
  | _ => throw s!"aux a{a} is not a symbol"

/-- Builds the input from a parsed `.ssa` file and its companion `.prog` file (only the
`config`, `frame` input and `genin` parts of the latter are read). -/
def load (file : ExportFile) (pf : GoFV.Asm.ProgFile) : Except String Env := do
  let some sec := file.sections.back? | throw "no section"
  if sec.pass.toStringLossy != "trim" then throw s!"last section is {sec.pass.toStringLossy}, not trim"
  let tabs := file.frontendTables
  let defs := pf.frame.defs ++ pf.genin.defs
  let mut ptypes : Std.HashMap Nat GoFV.Asm.TypeDef := {}
  let mut syms : Std.HashMap Nat (GoStr × Nat) := {}
  for d in defs do
    match d with
    | .type k t => ptypes := ptypes.insert k t
    | .sym k s abi => syms := syms.insert k (s, abi)
    | _ => pure ()
  let mut names : Array (Option NameInfo) := #[]
  let mut auxName : Std.HashMap AuxRef Nat := {}
  for d in defs do
    if let .name k nd := d then
      let ty ← match nd.type.bind (ptypes[·]?) with
        | some t => pure t
        | none => throw s!"name n{k}: no type"
      let ssaType ← match nd.aux with
        | none => pure none
        | some a =>
          match tabs.aux? a with
          | some { kind := .name sym _ t .., .. } =>
            if sym != nd.sym then throw s!"name n{k}: aux a{a} is {sym.toStringLossy}"
            pure (some t)
          | _ => throw s!"name n{k}: aux a{a} is not a name"
      if names.size ≤ k then names := names ++ Array.replicate (k + 1 - names.size) none
      names := names.set! k (some { n := k, d := nd, ty, ssaType })
      if let some a := nd.aux then auxName := auxName.insert a k
  let f := sec.func
  let nv := f.valueTab.size
  let mut locs : Array (Option Location) := Array.replicate nv none
  if let some (_, es) := f.low.regAlloc then
    for (id, l) in es do
      if id < nv then locs := locs.set! id (some l)
  let mut temps : Array (Option Nat) := Array.replicate nv none
  if let some es := f.low.tempRegs then
    for (id, r) in es do
      if id < nv then temps := temps.set! id (some r)
  let inFlags := pf.frame.dclIn.foldl (fun m d => m.insert d.name d.flags) {}
  return { file, f, tabs, progConfig := pf.config, names, auxName, dclIn := pf.frame.dclIn,
           inFlags, genin := pf.genin, inSyms := syms, locs, temps }

end Env

end GoFV.Gen

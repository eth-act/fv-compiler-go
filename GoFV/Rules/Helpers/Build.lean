import GoFV.Rules.Env
import GoFV.Rules.Helpers.Sym
import GoFV.Opt.Pass
import GoFV.SSA.TypeNew

/-!
# Helpers that build values or objects (`rewrite.go`)

`rewriteStructStore`, `rewriteStructLoad`, `imakeOfStructMake`, `devirtLECall`,
`rewriteFixedLoad`, `needRaceCleanup`, `clobber`, `resetCopy`, and the object constructors
they and the rule results need: `t.PtrTo()`, `typeToAux(t)`, symbols by name
(`fe.StringData`, relocation targets, `ir.Syms.Zerobase`).

New types and aux objects get fresh table numbers (`docs/contracts/export.md`, "Objects first
created by pass `k`"); an existing object of the same identity is reused, as Go's pointer
caches do (`t.PtrTo()` is cached in `t`, `base.Ctxt.Lookup` interns symbols by name, a
`*types.Type` aux is the type itself).
-/

namespace GoFV.Rules

open GoFV.SSA

namespace RwM

/-- Add a type definition at a fresh number. -/
def addType (d : TypeDef) : RwM TypeRef := do
  let s ← get
  let n := max s.tables.types.size 1
  set { s with tables := s.tables.add (.type n d) }
  return n

/-- Add an aux definition at a fresh number. -/
def addAux (d : AuxDef) : RwM AuxRef := do
  let s ← get
  let n := max s.tables.auxes.size 1
  set { s with tables := s.tables.add (.aux n d) }
  return n

/-- The frontend type `t` (a file number) in the tables: the input tables are a prefix of the
file's, so a defined number is the same type; otherwise it is copied (with its components) to a
fresh number. -/
partial def importType (t : TypeRef) : RwM TypeRef := do
  if ((← get).tables.type? t).isSome then return t
  if let some n := (← get).imported[t]? then return n
  let some d := (← read).frontend.type? t | throw s!"frontend type t{t} not defined"
  let n ← addType d
  modify fun s => { s with imported := s.imported.insert t n }
  let fld (x : GoFV.SSA.Field) : RwM GoFV.SSA.Field := do return { x with type := ← importType x.type }
  let tail ← match d.tail with
    | .elem e => pure (.elem (← importType e))
    | .array e k => pure (.array (← importType e) k)
    | .struct fs => pure (.struct (← fs.mapM fld))
    | .func r p q fs => pure (.func r p q (← fs.mapM fld))
    | .tuple a b => pure (.tuple (← importType a) (← importType b))
    | .results ts => pure (.results (← ts.mapM importType))
    | .none => pure .none
  modify fun s => { s with tables := s.tables.add (.type n { d with tail }) }
  return n

/-- Redefine aux `a` (an object the pass mutates in place). -/
def setAux (a : AuxRef) (d : AuxDef) : RwM Unit :=
  modify fun s => { s with tables := s.tables.add (.aux a d) }

/-- `t.PtrTo()`: the unnamed pointer type to `t` (`types.NewPtr`, cached per element). -/
def ptrTo (t : TypeRef) : RwM TypeRef := do
  let env ← read
  let s ← get
  -- new types go past both the tables and the file's `typeorder` (`GoFV.SSA.TypeNew`)
  let floor := max s.tables.types.size env.typeOrder.rank.size
  let (p, tabs) ← liftE (s.tables.ptrTo floor env.ptrSize t)
  set { s with tables := tabs }
  return p

/-- `typeToAux(t)` (`Ty.typeAux`). -/
def typeAux (t : TypeRef) : RwM AuxRef := do
  let (tabs, a) ← liftE (Ty.typeAux (← tables) t)
  modify fun s => { s with tables := tabs }
  return a

/-- The `*obj.LSym` named `name` (`base.Ctxt.Lookup`): an existing symbol aux; else the
frontend's symbol (`PassEnv.frontend`, its types copied over); else a new one made by `mk`. -/
def symAux (name : GoStr) (abi : Option Nat) (mk : Unit → AuxDef) : RwM AuxRef := do
  if let some (i, _) := GoFV.Opt.PassEnv.findSym? (← tables) name abi then return i
  match GoFV.Opt.PassEnv.findSym? (← read).frontend name abi with
  | some (_, d) =>
    match d.kind with
    | .sym n a k sz fl ti ii dat rel rt =>
      let ti ← ti.mapM importType
      let ii ← ii.mapM importType
      addAux { d with kind := .sym n a k sz fl ti ii dat rel rt }
    | _ => addAux d
  | none => addAux (mk ())

/-- A symbol the port knows only by name (not read-only data, as exported for symbols whose
contents the passes do not read). -/
def plainSym (name : GoStr) (abi : Nat := 0) : Unit → AuxDef := fun _ =>
  { fmt := name, kind := .sym name abi "-" 0 {} none none none #[] none }

/-- `fe.StringData(s)`: the `go:string.…` symbol of string `s` (its name is in the string aux
the value came from). -/
def stringData (s : ByteArray) : RwM AuxRef := do
  let tabs ← tables
  -- the symbol name is recorded in any `str` aux of the same string
  let mut name? : Option GoStr := none
  for d? in tabs.auxes do
    if let some d := d? then
      if let .str t dn := d.kind then
        if t.bytes == s then name? := some dn; break
  let some name := name? | throw "fe.StringData: no string aux for the string"
  symAux name (some 0) fun _ =>
    { fmt := name,
      kind := .sym name 0 "SRODATA" s.size { dupok := true, «local» := true,
                                             contentaddressable := true }
        none none (if s.size == 0 then none else some s) #[] none }

/-- `b.NewValue…(pos, op, t, auxint, aux, args...)` in block `b`. -/
@[inline] def newValue (b : ID) (pos : Pos) (op : Op) (t : TypeRef) (auxInt : Int64 := 0)
    (aux : Option AuxRef := none) (args : Array ID := #[]) : RwM ID :=
  modFGet fun f => f.newValueArgs b pos op t auxInt aux args

@[inline] def reset (v : ID) (op : Op) : RwM Unit := modF fun f => f.resetValue v op
@[inline] def addArg (v w : ID) : RwM Unit := modF fun f => f.addArg v w
@[inline] def copyOf (v w : ID) : RwM Unit := modF fun f => f.copyOf v w

end RwM

namespace Helpers

open RwM

/-- `clobber(vv...)`: reset each value to `OpInvalid`; true. -/
def clobber (vs : List ID) : RwM Bool := do
  for v in vs do reset v .Invalid
  return true

/-- `resetCopy(v, arg)`: true. -/
def resetCopy (v arg : ID) : RwM Bool := do
  reset v .Copy; addArg v arg; return true

/-- `rewriteStructStore(v)`: a `Store` of a `StructMake` becomes a chain of field stores;
returns the last memory. -/
def rewriteStructStore (v : ID) : RwM ID := do
  let x ← val v
  let b := x.block
  let dst := x.args[0]!
  let sm ← val x.args[1]!
  if sm.op != .StructMake then throw s!"invalid struct store: v{sm.id}"
  let mut mem := x.args[2]!
  let t := sm.type
  let tmem ← typ "Mem"
  for i in [0:sm.args.size] do
    let ft ← ty (Ty.fieldType · t i)
    let pt ← ptrTo ft
    let off ← ty (Ty.fieldOff · t i)
    let addr ← newValue b x.pos .OffPtr pt (Int64.ofInt off) none #[dst]
    let fa ← typeAux ft
    mem ← newValue b x.pos .Store tmem 0 (some fa) #[addr, sm.args[i]!, mem]
  return mem

/-- `rewriteStructLoad(v)`: a `Load` of a struct becomes a `StructMake` of field loads. -/
def rewriteStructLoad (v : ID) : RwM ID := do
  let x ← val v
  let b := x.block
  let ptr := x.args[0]!
  let mem := x.args[1]!
  let t := x.type
  let n ← ty (Ty.numFields · t)
  let mut args : Array ID := #[]
  for i in [0:n] do
    let ft ← ty (Ty.fieldType · t i)
    let pt ← ptrTo ft
    let off ← ty (Ty.fieldOff · t i)
    let addr ← newValue b x.pos .OffPtr pt (Int64.ofInt off) none #[ptr]
    args := args.push (← newValue b x.pos .Load ft 0 none #[addr, mem])
  reset v .StructMake
  modF fun f => f.addArgs v args
  return v

/-- `imakeOfStructMake(v)`: `(IMake typ (StructMake ...))` → `(IMake typ arg)` with the first
argument of non-zero size. -/
def imakeOfStructMake (v : ID) : RwM ID := do
  let x ← val v
  let sm ← val x.args[1]!
  let mut arg? : Option ID := none
  for a in sm.args do
    if (← ty (Ty.size · (← val a).type)) > 0 then arg? := some a; break
  let some arg := arg? | throw "imakeOfStructMake: no argument of non-zero size"
  newValue x.block x.pos .IMake x.type 0 none #[x.args[0]!, arg]

/-- `devirtLECall(v, sym)`: `v` becomes a `StaticLECall` of `sym` (its shared `*AuxCall` is
mutated, i.e. redefined) without its first argument. -/
def devirtLECall (v : ID) (sym : Option AuxRef) : RwM ID := do
  let x ← val v
  let some a := x.aux | throw "devirtLECall: no aux"
  let d ← liftE (Sym.auxDef (← tables) a)
  let .call _ abi := d.kind | throw "devirtLECall: aux is not an *AuxCall"
  let name ← match sym with
    | some s => pure (← liftE (Sym.lsym (← tables) (some s))).name
    | none => throw "devirtLECall: nil symbol"
  setAux a { fmt := ⟨"AuxCall{".toUTF8 ++ name.bytes ++ "}".toUTF8⟩, kind := .call sym abi }
  let a0 := x.args[0]!
  modF fun f =>
    let f := f.modV v fun y => { y with op := .StaticLECall, args := y.args.extract 1 y.args.size }
    f.decUses a0
  return v

/-- `needRaceCleanup(sym, v)`. -/
def needRaceCleanup (sym : Option AuxRef) (v : ID) : RwM Bool := do
  if !(← read).race then return false
  let tabs ← tables
  let enter := "runtime.racefuncenter".toUTF8
  let exit := "runtime.racefuncexit".toUTF8
  if !(← liftE (Sym.isSameCall tabs sym enter)) && !(← liftE (Sym.isSameCall tabs sym exit)) then
    return false
  let f ← getF
  for b in f.blocks do
    for w in (f.getB b).values do
      let y := f.getV w
      match y.op with
      | .StaticCall | .StaticLECall =>
        let s ← liftE (Sym.callFnName tabs y.aux)
        let s := (s.map (·.bytes)).getD ByteArray.empty
        let ok := [enter, exit, "runtime.panicdivide".toUTF8, "runtime.panicwrap".toUTF8,
          "runtime.panicshift".toUTF8].any (· == s)
        if !ok then return false
      | .ClosureCall | .InterCall | .ClosureLECall | .InterLECall => return false
      | _ => pure ()
  if ← liftE (Sym.isSameCall tabs sym enter) then
    let x ← val v
    let a0 ← val x.args[0]!
    if a0.op != .Store then
      return x.op == .StaticLECall
    let mem := a0.args[2]!
    reset a0.id .Copy
    addArg a0.id mem
  return true

end Helpers

end GoFV.Rules

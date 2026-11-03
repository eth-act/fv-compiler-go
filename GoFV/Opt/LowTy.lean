import GoFV.Opt.Pass
import GoFV.SSA.Alloc
import GoFV.SSA.TypePred

/-!
# Type predicates of the scheduled passes

The `*types.Type` predicates `schedule`, `late nilcheck` and `flagalloc` ask of value types
(`types/type.go`): `IsMemory`, `IsFlags` (the object `types.TypeFlags`), `IsTuple` and a
tuple's `FieldType(0/1)`, over the export's type tables and the `typs` pseudo-types.
-/

namespace GoFV.Opt

open GoFV.SSA

/-- The type tables and the `Mem`, `Flags` and `Void` pseudo-types (`typs`). -/
structure LowTy where
  tabs : Tables
  mem : TypeRef
  flags : TypeRef
  void : TypeRef

namespace LowTy

/-- From a pass environment; error if `typs` lacks a pseudo-type. -/
def ofEnv (env : PassEnv) : Except String LowTy := do
  let some mem := env.typ? "Mem" | throw "typs: no Mem"
  let some flags := env.typ? "Flags" | throw "typs: no Flags"
  let some void := env.typ? "Void" | throw "typs: no Void"
  return { tabs := env.tables, mem, flags, void }

/-- `t.IsMemory()`. -/
@[inline] def isMemory (e : LowTy) (t : TypeRef) : Bool := e.tabs.isMemory e.mem t

/-- `t.IsFlags()`. -/
@[inline] def isFlags (e : LowTy) (t : TypeRef) : Bool := t == e.flags

/-- The components of a `TUPLE` type, `none` for any other kind (`t.IsTuple()`). -/
@[inline] def tuple? (e : LowTy) (t : TypeRef) : Option (TypeRef × TypeRef) :=
  match (e.tabs.type? t).map (·.tail) with
  | some (TypeTail.tuple a b) => some (a, b)
  | _ => none

/-- `t.IsTuple()`. -/
@[inline] def isTuple (e : LowTy) (t : TypeRef) : Bool := (e.tuple? t).isSome

/-- `v.MemoryArg()` (`value.go`): the last argument if it has memory type; `none` for Go's nil
(no arguments, or a non-memory last argument). Go's `Fatalf` on a `Phi` is the caller's. -/
@[inline] def memoryArg (e : LowTy) (f : Func) (v : Value) : Option ID :=
  match v.args.back? with
  | some m => if e.isMemory (f.getV m).type then some m else none
  | none => none

end LowTy

end GoFV.Opt

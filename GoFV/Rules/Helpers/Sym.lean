import GoFV.SSA.Alloc
import GoFV.Rules.Helpers.Types

/-!
# Symbol and call helpers (`rewrite.go`)

Helpers that inspect `Aux` values: `*obj.LSym` (`symIsRO`, `symIsROZero`, `read8..64`,
`isFixedLoad`), `*AuxCall` (`isSameCall`, `isMalloc`), `*ir.Name` (`isDictArgSym`), and
`copyCompatibleType`, which `isFixedLoad` uses. Only `SRODATA` symbols carry kind, data and
relocations in the export (`docs/contracts/export.md`), which is all these helpers read.
-/

namespace GoFV.Rules.Sym

open GoFV.SSA

/-- The definition of aux `a`. -/
def auxDef (tabs : Tables) (a : AuxRef) : Except String AuxDef :=
  match tabs.aux? a with
  | some d => .ok d
  | none => .error s!"aux a{a} not defined"

/-- The contents of an `*obj.LSym` (`sym.(*obj.LSym)`, panicking otherwise). -/
structure LSym where
  name : GoStr
  abi : Nat
  kind : String
  data : ByteArray
  relocs : Array Reloc
  typeInfo : Option TypeRef
  itabInfo : Option TypeRef
  rtype : Option RType

def lsym (tabs : Tables) (a : Option AuxRef) : Except String LSym := do
  let some a := a | throw "nil Sym asserted to *obj.LSym"
  match (← auxDef tabs a).kind with
  | .sym name abi kind _ _ ti ii data relocs rt =>
    return { name, abi, kind, data := data.getD ByteArray.empty, relocs, typeInfo := ti,
             itabInfo := ii, rtype := rt }
  | _ => throw s!"aux a{a} is not an *obj.LSym"

/-- `symIsRO(sym)`. -/
def symIsRO (tabs : Tables) (a : Option AuxRef) : Except String Bool := do
  let s ← lsym tabs a
  return s.kind == "SRODATA" && s.relocs.size == 0

/-- `symIsROZero(sym)`. -/
def symIsROZero (tabs : Tables) (a : Option AuxRef) : Except String Bool := do
  let s ← lsym tabs a
  if s.kind != "SRODATA" || s.relocs.size != 0 then return false
  return s.data.data.all (· == 0)

/-- `read8(sym, off)`: 0 outside the data. -/
def read8 (tabs : Tables) (a : Option AuxRef) (off : Int) : Except String Nat := do
  let s ← lsym tabs a
  if off < 0 || off ≥ s.data.size then return 0
  return s.data[off.toNat]!.toNat

/-- `readN(sym, off, byteorder)` for `n` bytes: bytes past the data read as 0. -/
def readN (tabs : Tables) (a : Option AuxRef) (off : Int) (n : Nat) (bigEndian : Bool) :
    Except String Nat := do
  let s ← lsym tabs a
  let byte (i : Nat) : Nat :=
    if 0 ≤ off && off < s.data.size then
      let j := off.toNat + i
      if j < s.data.size then s.data[j]!.toNat else 0
    else 0
  let mut r := 0
  for i in [0:n] do
    let k := if bigEndian then n - 1 - i else i
    r := r + byte i * 2 ^ (8 * k)
  return r

/-- The `Fn` symbol name of an `*AuxCall` (`aux.(*AuxCall).Fn`), `none` if `Fn` is nil. -/
def callFnName (tabs : Tables) (a : Option AuxRef) : Except String (Option GoStr) := do
  let some a := a | throw "nil Aux asserted to *AuxCall"
  match (← auxDef tabs a).kind with
  | .call none _ => return none
  | .call (some fn) _ => return some (← lsym tabs (some fn)).name
  | _ => throw s!"aux a{a} is not an *AuxCall"

/-- `isSameCall(aux, name)`. -/
def isSameCall (tabs : Tables) (a : Option AuxRef) (name : ByteArray) : Except String Bool := do
  match ← callFnName tabs a with
  | some n => return n.bytes == name
  | none => return false

def startsWith (s p : ByteArray) : Bool :=
  p.size ≤ s.size && (List.range p.size).all fun i => s[i]! == p[i]!

/-- `isMalloc(aux)`: `runtime.newobject` or a specialised small-size malloc. -/
def isMalloc (tabs : Tables) (a : Option AuxRef) : Except String Bool := do
  match ← callFnName tabs a with
  | none => return false
  | some n =>
    let n := n.bytes
    return n == "runtime.newobject".toUTF8 ||
      startsWith n "runtime.mallocgcSmallNoScanSC".toUTF8 ||
      startsWith n "runtime.mallocgcSmallScanNoHeaderSC".toUTF8 ||
      startsWith n "runtime.mallocgcTinySC".toUTF8

/-- `isDictArgSym(sym)`: `sym.(*ir.Name).Sym().Name == ".dict"`. -/
def isDictArgSym (tabs : Tables) (a : Option AuxRef) : Except String Bool := do
  let some a := a | throw "nil Sym asserted to *ir.Name"
  match (← auxDef tabs a).kind with
  | .name sym .. => return sym.bytes == ".dict".toUTF8
  | _ => throw s!"aux a{a} is not an *ir.Name"

/-- `copyCompatibleType(t1, t2)`; `cmpEq` is `Compare == CMPeq`. -/
def copyCompatibleType (tabs : Tables) (cmpEq : TypeRef → TypeRef → Bool) (t1 t2 : TypeRef) :
    Except String Bool := do
  if (← Ty.size tabs t1) != (← Ty.size tabs t2) then return false
  if ← Ty.isInteger tabs t1 then return ← Ty.isInteger tabs t2
  if ← Ty.isPtrShaped tabs t1 then return ← Ty.isPtrShaped tabs t2
  return cmpEq t1 t2

/-- A field of the runtime type descriptor (`config rttype.<name> <offset>:<kind>:<size>`). -/
structure RtField where
  name : String
  offset : Int
  kind : TypeKind
  size : Int
  deriving Inhabited

/-- `copyCompatibleType(t, f.Type)` for a runtime descriptor field known by kind and size: the
field types are integers or pointers, so `Compare` is never reached. -/
def compatWithField (tabs : Tables) (t : TypeRef) (fld : RtField) : Except String Bool := do
  if (← Ty.size tabs t) != fld.size then return false
  if ← Ty.isInteger tabs t then return Ty.isIntegerKind fld.kind
  if ← Ty.isPtrShaped tabs t then return Ty.isPtrShapedKind fld.kind
  -- Go: `t1.Compare(t2) == CMPeq`; a non-integer, non-pointer type never equals one
  return false

/-- `objabi.R_WEAKADDR` (`R_WEAK | R_ADDR`) as the export spells it: `RelocType.String()` has
no name for it. -/
def weakAddr : String := "RelocType(-32767)"

/-- What `isFixedLoad`/`rewriteFixedLoad` resolve a load to. -/
inductive FixedLoad where
  /-- `Addr {sym}` of a relocation target (name and ABI). -/
  | addr (name : GoStr) (abi : Nat)
  /-- A pointer-sized constant (`Size_`, `PtrBytes`). -/
  | constPtr (c : Int)
  | const32 (c : Int)
  | const8 (c : Int)
  /-- `Addr` of a symbol known by name only (`GCData`, the `Elem` of a pointer type). -/
  | addrName (name : GoStr)

/-- The shared decision of `isFixedLoad(v, sym, off)` and `rewriteFixedLoad`: `none` when the
load is not fixed. `fields` are the exported descriptor fields, `elemOff` the offset of
`PtrType.Elem`. -/
def fixedLoad (tabs : Tables) (vty : TypeRef) (a : Option AuxRef) (off : Int)
    (fields : Array RtField) (elemOff : Int) : Except String (Option FixedLoad) := do
  let s ← lsym tabs a
  if ((← Ty.isPtrShaped tabs vty) || (← Ty.isKind .UINTPTR tabs vty)) && s.kind == "SRODATA" then
    for r in s.relocs do
      if (r.type == "R_ADDR" || r.type == weakAddr) && r.off == off && r.add == 0 then
        return some (.addr r.target r.targetAbi.toNat)
    return none
  let some t := s.typeInfo | return none
  for fld in fields do
    if fld.offset == off && (← compatWithField tabs vty fld) then
      let some rt := s.rtype | throw s!"fixedLoad: no rtype for {s.name}"
      let need {α} (x : Option α) : Except String α :=
        match x with | some y => .ok y | none => .error s!"fixedLoad: {s.name}.{fld.name} unknown"
      match fld.name with
      | "Size_" => return some (.constPtr (← need rt.size))
      | "PtrBytes" => return some (.constPtr (← need rt.ptrdata))
      | "Hash" => return some (.const32 (← need rt.hash))
      | "Kind_" => return some (.const8 (← need rt.abiKind))
      | "GCData" => return some (.addrName rt.gcdata)
      | _ => return none
  if (← Ty.isKind .PTR tabs t) && off == elemOff then
    let some rt := s.rtype | throw s!"fixedLoad: no rtype for {s.name}"
    return some (.addrName rt.elemSym)
  return none

end GoFV.Rules.Sym

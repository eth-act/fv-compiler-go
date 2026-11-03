import GoFV.SSA.Export
import GoFV.SSA.Sem.Mem
import GoFV.SSA.Sem.Flags

/-!
# Type shapes (`docs/plans/semantics.md` §3.1)

The shape (`Ty`) of an exported type: integer width (from the exported size), `bool`,
pointer-shaped types (with the element size of `*T`), SSA-able composites as fields at their
exported offsets (string, slice, interface, struct, `[1]T`, complex), larger arrays as byte
blobs, zero-sized types, and memory/tuples. Floats are their IEEE bit patterns: `float32` and
`float64` have the integer shapes of their size (`Sem/Float.lean`), `complex64`/`complex128`
are pairs of them. Sizes are exported, never recomputed: a type whose size the export does
not have is `other`.
-/

namespace GoFV.SSA.Sem

open GoFV.SSA

/-- The exported size of `t`, if known and non-negative. -/
def typeSize? (tabs : Tables) (t : TypeRef) : Option Nat :=
  match (tabs.type? t).bind (·.size) with
  | some s => if s ≥ 0 then some s.toNat else none
  | none => none

/-- The shape of type `t` in `tabs` (`fuel` bounds the nesting of struct fields and arrays;
pointers do not recurse). Strings and slices have their own shapes (`Ty.str`, `Ty.slice`),
whose values have valid lengths. -/
def tyOf (tabs : Tables) : Nat → TypeRef → Ty
  | 0, _ => .other
  | fuel + 1, t =>
    match tabs.type? t with
    | none => .other
    | some d =>
      let size := typeSize? tabs t
      match d.kind with
      | .INT8 | .UINT8 | .INT16 | .UINT16 | .INT32 | .UINT32 | .INT64 | .UINT64 | .INT | .UINT
      | .UINTPTR =>
        match d.size.bind Width.ofSize? with
        | some w => .int w
        | none => .other
      | .BOOL => .bool
      | .PTR | .UNSAFEPTR | .MAP | .CHAN | .FUNC =>
        .ptr (match d.tail with
          | .elem e => typeSize? tabs e
          | _ => none)
      | .STRING => .str
      | .SLICE =>
        .slice (match d.tail with
          | .elem e => typeSize? tabs e
          | _ => none)
      -- the itab/type word is a `uintptr` and the data word a `*uint8`, as Go decomposes an
      -- interface (`ITab`/`IData`, `expand_calls.go`, `dec.rules`)
      | .INTER => .agg [(0, .int .w64), (8, .ptr (some 1))] 16
      | .STRUCT =>
        match size, d.tail with
        | some 0, _ => .empty
        | some n, .struct fields =>
          match fields.toList.mapM fun f => f.offset.map fun o => (o.toNat, f.type) with
          | some fs => .agg (fs.map fun (o, ft) => (o, tyOf tabs fuel ft)) n
          | none => .opaque n
        | _, _ => .other
      | .ARRAY =>
        match size, d.tail with
        | some 0, _ => .empty
        | some n, .array e 1 => .agg [(0, tyOf tabs fuel e)] n
        | some n, _ => .blob n
        | none, _ => .other
      | .FLOAT32 | .FLOAT64 =>
        match d.size.bind Width.ofSize? with
        | some w => .int w
        | none => .other
      | .COMPLEX64 | .COMPLEX128 =>
        match size with
        | some 8 => .agg [(0, .int .w32), (4, .int .w32)] 8
        | some 16 => .agg [(0, .int .w64), (8, .int .w64)] 16
        | _ => .other
      -- lowered SSA (Phase 2): `flags` as `Ty.flags`, a `Vec128` register as its 16 bytes
      | .SSA =>
        if d.str == GoStr.ofString "mem" then .mem
        else if d.str == GoStr.ofString "flags" then Ty.flags
        else if d.str == GoStr.ofString "vec128" then .blob 16
        else .other
      | .TUPLE =>
        match d.tail with
        | .tuple a b => .tuple [tyOf tabs fuel a, tyOf tabs fuel b]
        | _ => .other
      | .RESULTS =>
        match d.tail with
        | .results ts => .tuple (ts.toList.map (tyOf tabs fuel))
        | _ => .other
      | _ => .other

/-- The shape of `t`. -/
def _root_.GoFV.SSA.Tables.ty (tabs : Tables) (t : TypeRef) : Ty := tyOf tabs 32 t

/-- `Val.retype` at a pointer shape (`Val.retype_ptr`): the string and slice pointers. A 64-bit
integer keeps its word (§3.3: the pointer at that concrete address, `Val.asPtrWord`), a narrower
one or a boolean is zero-extended (as at `.int .w64`); a pointer becomes its word (`Ptr.word`: its
address if it converts back to itself). -/
def Val.retypePtr : Val → Val
  | .int _ a => .int .w64 (a.setWidth 64)
  | .bool b => .int .w64 (if b then 1 else 0)
  | .ptr p => p.word
  | _ => .poison

/-- `Val.retype` at `.int .w64` (`Val.retype_i64`): the string and slice lengths. -/
def Val.retypeI64 : Val → Val
  | .int _ x => .int .w64 (x.setWidth 64)
  | .bool b => .int .w64 (if b then 1 else 0)
  | .ptr p => p.word
  | _ => .poison

mutual
/-- A value as a value of type shape `t` (§3.2). Go types a value by its `Type`, not by its
op: rules build e.g. `(Rsh64x64 <t> …)` with `t` = `int32` (`divmod.rules`), whose meaning is
the low 32 bits of the 64-bit shift. An integer narrower than the op keeps the low bits. A
narrower integer or a boolean at an integer shape is zero-extended: generic code never has one
(its values have their type's width), and lowered code has them exactly where a rule dropped an
extension of a producer whose upper register bits are zero (`ARM64latelower.rules`:
`ZeroUpper32Bits`, the boolean-generating instructions; `CvtBoolToUint8 => Copy`;
`docs/plans/semantics2.md` §3). The two word shapes (`.int .w64`
and pointers) retype alike (§3.2, #290): a 64-bit integer keeps its word, and a pointer becomes
its word (`Ptr.word`): its concrete address if it converts back to itself
(`Ptr.convertible`), else the pointer (a global, which has no concrete address, a frame
temporary, whose address no integer converts back to). So every register holds a pointer that
has an integer form in that form, pointer consumers read it as the pointer at that address
(`Val.asPtrWord`), and a word copied between a `uintptr` and a pointer type (an itab word after
`decompose builtin`, `Convert`, a phi elimination's `Copy`) is unchanged. Composites are retyped
componentwise (a call's tuple
keeps its components beyond the type's). Every other mismatch of value and shape is `poison`,
so `(v.retype t).hasTy t` always holds (#108). A string or slice whose length or capacity
is not a valid signed `int` (`Val.strOK`, `Val.sliceOK`: `0 ≤ len ≤ cap`) is `poison`. -/
def Val.retype : Ty → Val → Val
  | _, .poison => .poison
  | .int w', .int _ x => .int w' (x.setWidth w'.bits)
  | .int w', .bool b => .int w' (if b then 1 else 0)
  | .int .w64, .ptr p => p.word
  | .ptr _, .int _ a => .int .w64 (a.setWidth 64)
  | .ptr _, .bool b => .int .w64 (if b then 1 else 0)
  | .ptr _, .ptr p => p.word
  | .bool, .bool b => .bool b
  | .mem, .mem m => .mem m
  | .tuple ts, .tuple vs => match Val.retypePre ts vs with
    | some vs' => .tuple vs'
    | none => .poison
  | .agg fs _, .agg vs => match Val.retypeFields fs vs with
    | some vs' => .agg vs'
    | none => .poison
  | .str, .agg [p, l] => Val.ofStr [p.retypePtr, l.retypeI64]
  | .slice _, .agg [p, l, c] => Val.ofSlice [p.retypePtr, l.retypeI64, c.retypeI64]
  | .blob n, .blob bs => if bs.length == n then .blob bs else .poison
  | .empty, .empty => .empty
  | _, _ => .poison
def Val.retypePre : List Ty → List Val → Option (List Val)
  | [], vs => some vs
  | t :: ts, v :: vs => (Val.retypePre ts vs).map (Val.retype t v :: ·)
  | _ :: _, [] => none
def Val.retypeFields : List (Nat × Ty) → List Val → Option (List Val)
  | [], [] => some []
  | (_, t) :: fs, v :: vs => (Val.retypeFields fs vs).map (Val.retype t v :: ·)
  | _, _ => none
end

mutual
/-- `v` has shape `t` (`poison` has every shape; the two word shapes have the same values: a
64-bit integer and a pointer that does not convert to an integer, `Val.retype`; a string or
slice has valid lengths, `Val.strOK`/`Val.sliceOK`). -/
def Val.hasTy : Val → Ty → Bool
  | .poison, _ => true
  | .int w _, .int w' => w == w'
  | .bool _, .bool => true
  | .mem _, .mem => true
  | .tuple vs, .tuple ts => Val.hasTyPre vs ts
  -- a word: a 64-bit integer (a pointer that converts to an integer is held as its address,
  -- `Ptr.word`; a `uintptr` copied to a pointer type; concrete bytes loaded at a pointer type,
  -- §3.3) or a pointer without an integer form (a global, a frame temporary)
  | .ptr p, .ptr _ => !p.convertible
  | .int .w64 _, .ptr _ => true
  | .ptr p, .int .w64 => !p.convertible
  | .agg vs, .agg fs _ => Val.hasTyList vs (fs.map (·.2))
  | .agg vs, .str => Val.strOK vs && vs.head?.all Val.isPtrWord
  | .agg vs, .slice _ => Val.sliceOK vs && vs.head?.all Val.isPtrWord
  | .blob bs, .blob n => bs.length == n
  | .empty, .empty => true
  | _, _ => false
def Val.hasTyList : List Val → List Ty → Bool
  | [], [] => true
  | v :: vs, t :: ts => Val.hasTy v t && Val.hasTyList vs ts
  | _, _ => false
/-- The first components of `vs` have the shapes `ts` (a call's tuple carries its results'
addresses after the components of its type, §5). -/
def Val.hasTyPre : List Val → List Ty → Bool
  | _, [] => true
  | v :: vs, t :: ts => Val.hasTy v t && Val.hasTyPre vs ts
  | [], _ :: _ => false
end

end GoFV.SSA.Sem

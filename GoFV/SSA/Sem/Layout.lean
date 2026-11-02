import GoFV.SSA.Export
import GoFV.SSA.Sem.Mem

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
      | .SSA => if d.str == GoStr.ofString "mem" then .mem else .other
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
integer keeps its word (§3.3: the pointer at that concrete address, `Val.asPtrWord`). -/
def Val.retypePtr : Val → Val
  | .int .w64 a => .int .w64 a
  | .ptr p => .ptr p
  | _ => .poison

/-- `Val.retype` at `.int .w64` (`Val.retype_i64`): the string and slice lengths. -/
def Val.retypeI64 : Val → Val
  | .int w x => if Width.w64.bits ≤ w.bits then .int .w64 (x.setWidth 64) else .poison
  | .ptr p => match p.addr? with
    | some a => .int .w64 a
    | none => .ptr p
  | _ => .poison

mutual
/-- A value as a value of type shape `t` (§3.2). Go types a value by its `Type`, not by its
op: rules build e.g. `(Rsh64x64 <t> …)` with `t` = `int32` (`divmod.rules`), whose meaning is
the low 32 bits of the 64-bit shift. An integer narrower than the op keeps the low bits; a
wider type would expose undefined high bits and is `poison`. A `uintptr`-typed value that
holds a pointer (`ConstNil <uintptr>`, `Convert`) becomes its concrete address; a global, which
has no concrete address, stays a pointer at an integer type. A 64-bit integer typed as a
pointer keeps its word: pointer consumers read it as the pointer at that address
(`Val.asPtrWord`, §3.3), so a `uintptr` word copied to a pointer-typed value (an itab word
after `decompose builtin`) is unchanged. Composites are retyped componentwise (a call's tuple
keeps its components beyond the type's). Every other mismatch of value and shape is `poison`,
so `(v.retype t).hasTy t` always holds (#108). A string or slice whose length or capacity
is not a valid signed `int` (`Val.strOK`, `Val.sliceOK`: `0 ≤ len ≤ cap`) is `poison`. -/
def Val.retype : Ty → Val → Val
  | _, .poison => .poison
  | .int w', .int w x => if w'.bits ≤ w.bits then .int w' (x.setWidth w'.bits) else .poison
  | .int .w64, .ptr p => match p.addr? with
    | some a => .int .w64 a
    | none => .ptr p
  | .ptr _, .int .w64 a => .int .w64 a
  | .ptr _, .ptr p => .ptr p
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
/-- `v` has shape `t` (`poison` has every shape; an address-less pointer has the 64-bit integer
shape too, and a 64-bit integer the pointer shape; a string or slice has valid lengths,
`Val.strOK`/`Val.sliceOK`). -/
def Val.hasTy : Val → Ty → Bool
  | .poison, _ => true
  | .int w _, .int w' => w == w'
  | .bool _, .bool => true
  | .mem _, .mem => true
  | .tuple vs, .tuple ts => Val.hasTyPre vs ts
  | .ptr _, .ptr _ => true
  -- a pointer word may be a concrete address (a `uintptr` copied to a pointer type, concrete
  -- bytes loaded at a pointer type, §3.3)
  | .int .w64 _, .ptr _ => true
  -- a `uintptr`/`int64` may hold a pointer without a concrete address (a global: code
  -- pointers of closures, `unsafe.Pointer` ↔ `uintptr`)
  | .ptr p, .int .w64 => p.addr?.isNone
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

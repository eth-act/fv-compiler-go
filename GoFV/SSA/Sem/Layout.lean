import GoFV.SSA.Export
import GoFV.SSA.Sem.Mem

/-!
# Type shapes (`docs/plans/semantics.md` §3.1)

The shape (`Ty`) of an exported type: integer width (from the exported size), `bool`,
pointer-shaped types (with the element size of `*T`), SSA-able composites as fields at their
exported offsets (string, slice, interface, struct, `[1]T`), larger arrays as byte blobs,
zero-sized types, and memory/tuples. Sizes are exported, never recomputed: a type whose size
the export does not have is `other`.
-/

namespace GoFV.SSA.Sem

open GoFV.SSA

/-- The exported size of `t`, if known and non-negative. -/
def typeSize? (tabs : Tables) (t : TypeRef) : Option Nat :=
  match (tabs.type? t).bind (·.size) with
  | some s => if s ≥ 0 then some s.toNat else none
  | none => none

/-- The shape of type `t` in `tabs` (`fuel` bounds the nesting of struct fields and arrays;
pointers do not recurse). -/
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
      | .STRING => .agg [(0, .ptr (some 1)), (8, .int .w64)] 16
      | .SLICE =>
        let e := match d.tail with
          | .elem e => typeSize? tabs e
          | _ => none
        .agg [(0, .ptr e), (8, .int .w64), (16, .int .w64)] 24
      | .INTER => .agg [(0, .ptr none), (8, .ptr none)] 16
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
      | .FLOAT32 | .FLOAT64 | .COMPLEX64 | .COMPLEX128 =>
        match size with
        | some n => .opaque n
        | none => .other
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

/-- A value as a value of type shape `t` (§3.2). Go types a value by its `Type`, not by its
op: rules build e.g. `(Rsh64x64 <t> …)` with `t` = `int32` (`divmod.rules`), whose meaning is
the low 32 bits of the 64-bit shift. An integer narrower than the op keeps the low bits; a
wider type would expose undefined high bits and is `poison`. A `uintptr`-typed value that
holds a pointer (`ConstNil <uintptr>`, `Convert`) becomes its concrete address, an integer
typed as a pointer the pointer at that address (§3.3); a global, which has no concrete
address, stays a pointer. A `bool`-typed value that is not a boolean is `poison` (so a
register of a `bool`-typed value is a boolean or `poison`). Other shapes are unchanged. -/
def Val.retype : Ty → Val → Val
  | .int w', .int w x => if w'.bits ≤ w.bits then .int w' (x.setWidth w'.bits) else .poison
  | .ptr _, .int .w64 a => .ptr (Ptr.ofAddr a)
  | .int .w64, .ptr p => match p.addr? with
    | some a => .int .w64 a
    | none => .ptr p
  | .bool, .bool b => .bool b
  | .bool, _ => .poison
  | _, v => v

mutual
/-- `v` has shape `t` (`poison` has every shape). -/
def Val.hasTy : Val → Ty → Bool
  | .poison, _ => true
  | .int w _, .int w' => w == w'
  | .bool _, .bool => true
  | .mem _, .mem => true
  | .tuple vs, .tuple ts => Val.hasTyList vs ts
  | .ptr _, .ptr _ => true
  | .agg vs, .agg fs _ => Val.hasTyList vs (fs.map (·.2))
  | .blob bs, .blob n => bs.length == n
  | .empty, .empty => true
  | _, _ => false
def Val.hasTyList : List Val → List Ty → Bool
  | [], [] => true
  | v :: vs, t :: ts => Val.hasTy v t && Val.hasTyList vs ts
  | _, _ => false
end

end GoFV.SSA.Sem

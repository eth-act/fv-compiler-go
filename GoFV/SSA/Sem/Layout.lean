import GoFV.SSA.Export
import GoFV.SSA.Sem.Val

/-!
# Type shapes (`docs/plans/semantics.md` §3.1)

P1 needs only the shape of a value's type: integer width (from the exported size), `bool`,
memory, tuples. Later phases add field layouts and ABI pieces here.
-/

namespace GoFV.SSA.Sem

open GoFV.SSA

/-- The shape of type `t` in `tabs` (`TUPLE`/`RESULTS` nest at most once; `fuel` bounds the
lookup anyway). -/
def tyOf (tabs : Tables) : Nat → TypeRef → Ty
  | 0, _ => .other
  | fuel + 1, t =>
    match tabs.type? t with
    | none => .other
    | some d =>
      match d.kind with
      | .INT8 | .UINT8 | .INT16 | .UINT16 | .INT32 | .UINT32 | .INT64 | .UINT64 | .INT | .UINT
      | .UINTPTR =>
        match d.size.bind Width.ofSize? with
        | some w => .int w
        | none => .other
      | .BOOL => .bool
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

/-- The shape of `t` (`TUPLE` and `RESULTS` components are never tuples themselves). -/
def _root_.GoFV.SSA.Tables.ty (tabs : Tables) (t : TypeRef) : Ty := tyOf tabs 3 t

/-- A value as a value of type shape `t` (§3.2). Go types a value by its `Type`, not by its
op: rules build e.g. `(Rsh64x64 <t> …)` with `t` = `int32` (`divmod.rules`), whose meaning is
the low 32 bits of the 64-bit shift. An integer narrower than the op keeps the low bits; a
wider type would expose undefined high bits and is `poison`. Other shapes are unchanged. -/
def Val.retype : Ty → Val → Val
  | .int w', .int w x => if w'.bits ≤ w.bits then .int w' (x.setWidth w'.bits) else .poison
  | _, v => v

mutual
/-- `v` has shape `t` (`poison` has every shape). -/
def Val.hasTy : Val → Ty → Bool
  | .poison, _ => true
  | .int w _, .int w' => w == w'
  | .bool _, .bool => true
  | .mem _, .mem => true
  | .tuple vs, .tuple ts => Val.hasTyList vs ts
  | _, _ => false
def Val.hasTyList : List Val → List Ty → Bool
  | [], [] => true
  | v :: vs, t :: ts => Val.hasTy v t && Val.hasTyList vs ts
  | _, _ => false
end

end GoFV.SSA.Sem

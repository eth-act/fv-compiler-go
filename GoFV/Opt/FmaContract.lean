import GoFV.SSA.Func

/-!
# Floating-point contraction at the `useFMA` shapes (decision on #384, issue #385)

`lower` fuses a float add or subtract of a product into one fused multiply-add
(`_gen/ARM64.rules:1798-1809`, `useFMA` is always true with the default `base.FmaHash == nil`),
which rounds once where the source rounds twice. The Go spec allows it ("An implementation may
combine multiple floating-point operations into a single fused operation", `doc/go_spec.html`),
so the `lower` theorem holds up to a *contraction* of the source (`docs/plans/semantics2.md`
§2.1): `contractAt f C` is `f` with each value of `C` that has one of the twelve rule shapes on
the generic ops (`fmaOf`) replaced by the fused arm64 op of the rule's right-hand side, with the
rule's arguments; the multiply stays (it may have other uses). On the generic ops the shapes
are, for each width (`D`: 64-bit, `S`: 32-bit), with `P = Mul x y` and `N = Neg (Mul x y)` or
`Mul (Neg x) y` (`FNMUL x y` after lowering, `ARM64.rules:1789-1792`):

| source | fused |
| --- | --- |
| `Add a P`, `Add P a` | `FMADD a x y` |
| `Add a N`, `Add N a` | `FMSUB a x y` |
| `Sub a P` | `FMSUB a x y` |
| `Sub a N` | `FMADD a x y` |
| `Sub P a` | `FNMSUB a x y` |
| `Sub N a` | `FNMADD a x y` |

An explicit conversion, which the spec says prevents fusion, leaves a `Round32F`/`Round64F`
between the multiply and the add, so no shape matches it.
-/

namespace GoFV.Opt.FmaContract

open GoFV.SSA

/-- The product `m` is: `Mul x y` (`false`), or `Neg (Mul x y)` / `Mul (Neg x) y` (`true`), at
width 64 (`d`) or 32. -/
def mulOf (f : Func) (d : Bool) (m : ID) : Option (ID × ID × Bool) :=
  let mul : Op := if d then .Mul64F else .Mul32F
  let neg : Op := if d then .Neg64F else .Neg32F
  match f.value? m with
  | some u =>
    if u.op == mul && u.args.size == 2 then
      match f.value? u.args[0]! with
      | some n => if n.op == neg && n.args.size == 1 then some (n.args[0]!, u.args[1]!, true)
                  else some (u.args[0]!, u.args[1]!, false)
      | none => some (u.args[0]!, u.args[1]!, false)
    else if u.op == neg && u.args.size == 1 then
      match f.value? u.args[0]! with
      | some p => if p.op == mul && p.args.size == 2 then some (p.args[0]!, p.args[1]!, true) else none
      | none => none
    else none
  | none => none

/-- The fused ops of width 64 (`d`) or 32: `FMADD`, `FMSUB`, `FNMADD`, `FNMSUB`. -/
def fmadd (d : Bool) : Op := if d then .ARM64FMADDD else .ARM64FMADDS
def fmsub (d : Bool) : Op := if d then .ARM64FMSUBD else .ARM64FMSUBS
def fnmadd (d : Bool) : Op := if d then .ARM64FNMADDD else .ARM64FNMADDS
def fnmsub (d : Bool) : Op := if d then .ARM64FNMSUBD else .ARM64FNMSUBS

/-- The fused value of `v` (module doc), if `v` has one of the twelve shapes. -/
def fmaOf (f : Func) (v : Value) : Option Value :=
  let fused (op : Op) (a x y : ID) : Option Value :=
    some { v with op, args := #[a, x, y], auxInt := 0, aux := none }
  let d? : Option Bool := match v.op with
    | .Add64F | .Sub64F => some true
    | .Add32F | .Sub32F => some false
    | _ => none
  match d?, v.args.toList with
  | some d, [l, r] =>
    if v.op == .Add64F || v.op == .Add32F then
      match mulOf f d r, mulOf f d l with
      | some (x, y, neg), _ => fused (if neg then fmsub d else fmadd d) l x y
      | none, some (x, y, neg) => fused (if neg then fmsub d else fmadd d) r x y
      | none, none => none
    else
      match mulOf f d r, mulOf f d l with
      | some (x, y, neg), _ => fused (if neg then fmadd d else fmsub d) l x y
      | none, some (x, y, neg) => fused (if neg then fnmadd d else fnmsub d) r x y
      | none, none => none
  | _, _ => none

/-- `f` with the values of `C` that have an FMA shape contracted (`fmaOf`). -/
def contractAt (f : Func) (C : List ID) : Func :=
  { f with valueTab := f.valueTab.mapIdx fun i o =>
      match o with
      | some v => if C.contains i then (fmaOf f v).getD v else some v
      | none => none }

/-- The values of `f` with an FMA shape. -/
def fmaValues (f : Func) : List ID :=
  (List.range f.valueTab.size).filter fun i => ((f.value? i).bind (fmaOf f)).isSome

/-- `f` with every FMA shape contracted. -/
def contractAll (f : Func) : Func := contractAt f (fmaValues f)

end GoFV.Opt.FmaContract

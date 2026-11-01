import GoFV.Proof.Pass.ECRel
import GoFV.Opt.ExpandCallsCheck

/-!
# The conversion of `expand calls` (issue #28)

The parameters of `CvRel` for `expand calls` (`GoFV.Opt.ECCheck.ecCheck`): the conversion `ecCv`
(identity, except for calls and `MakeResult`s: a tuple of Go-typed results becomes the register
pieces of its register-assigned results, `convTuple`, at the shapes of the target's register
types), the new values (`isNewB`: IDs the source does not define) and the source values a
value's obligation reads (`ecFront`: its arguments).
-/

namespace GoFV.Proof.EC

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.ECCheck GoFV.Proof.ABI

/-- The register pieces of the results `outs` of a tuple `(results…, rest…)`, followed by the
rest (memory, result addresses). -/
def convTuple (tabs : Tables) (outs : List ABIParam) : Val → Val
  | .tuple vs =>
    .tuple ((outs.zip vs).flatMap (fun (p, v) => leafVals (tabs.ty p.type) v) ++ vs.drop outs.length)
  | _ => .poison

/-- **The conversion of `expand calls`.** -/
def ecCv (tabs : Tables) (f g : Func) : Cv := fun x y =>
  match f.value? x with
  | some u =>
    if (callOpMap u.op).isSome then
      (convTuple tabs (callOuts tabs u.aux) y).retype (shapeOf (typeShapes tabs) g x)
    else if u.op == .MakeResult then
      (convTuple tabs (ownOuts tabs f) y).retype (shapeOf (typeShapes tabs) g x)
    else y
  | none => y

/-- The source values the obligation of `x` reads: its arguments. -/
def ecFront (f : Func) (x : ID) : List ID := ((f.value? x).map (·.args.toList)).getD []

theorem ecCv_of_not_converted {tabs : Tables} {f g : Func} {x : ID} (h : converted f x = false)
    (y : Val) : ecCv tabs f g x y = y := by
  unfold ecCv
  unfold converted at h
  cases hx : f.value? x with
  | none => rfl
  | some u =>
    rw [hx] at h
    simp only [Bool.or_eq_false_iff] at h
    simp only [h.1, h.2]
    rfl

end GoFV.Proof.EC

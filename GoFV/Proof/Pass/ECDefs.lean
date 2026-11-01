import GoFV.Proof.Pass.ECRel
import GoFV.Opt.ExpandCallsCheck

/-!
# The conversion of `expand calls` (issue #28)

The parameters of `CvRel` for `expand calls` (`GoFV.Opt.ECCheck.ecCheck`): the conversion `ecCv`
(identity, except for calls and `MakeResult`s, whose tuple of Go-typed results becomes the
register pieces of the results, `convTuple`, at the shape of the target's register types, and
for the values the pass invalidated, which become `poison`), the new values (`isNewB`: IDs the
source does not define), the source values a value's obligation reads (`ecFront`: its arguments
in the source and its non-new arguments in the target) and the relation of `Ret` outcomes
(`ecRR`: the target returns the register pieces of the source's results, at register shapes).
-/

namespace GoFV.Proof.EC

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.ECCheck GoFV.Proof.ABI GoFV.Proof.Order GoFV.Proof.AtomSim

/-- The register pieces of the results `outs` of a tuple `(results…, rest…)`, followed by the
rest (memory, result addresses). -/
def convTuple (tabs : Tables) (outs : List ABIParam) : Val → Val
  | .tuple vs =>
    .tuple ((outs.zip vs).flatMap (fun (p, v) => leafVals (tabs.ty p.type) v) ++ vs.drop outs.length)
  | _ => .poison

/-- **The conversion of `expand calls`.** -/
def ecCv (tabs : Tables) (f g : Func) : Cv := fun x y =>
  if invalidated g x then .poison else
  match f.value? x with
  | some u =>
    if (callOpMap u.op).isSome then
      (convTuple tabs (callOuts tabs u.aux) y).retype (shapeOf (typeShapes tabs) g x)
    else if u.op == .MakeResult then
      (convTuple tabs (ownOuts tabs f) y).retype (shapeOf (typeShapes tabs) g x)
    else y
  | none => y

/-- The source values the obligation of `x` reads: its arguments in the source and its
arguments in the target that the source defines. -/
def ecFront (f g : Func) (x : ID) : List ID :=
  ((f.value? x).map (·.args.toList)).getD [] ++
    (((g.value? x).map (·.args.toList)).getD []).filter (fun a => !isNewB f a)

/-- **The relation of `Ret` outcomes**: the source's results, one per result of the function,
each of its result's shape; the target's refine the register pieces of the source's, each
retyped at the shape of a register that holds its leaf without loss (`regShapeOK`: the leaf's
shape, or a pointer register for a pointer or 64-bit integer leaf); the memories refine. -/
def ecRR (tabs : Tables) (f : Func) (rs : List Val) (m : Mem) (rs' : List Val) (m' : Mem) : Prop :=
  List.Forall₂ (fun (p : ABIParam) (r : Val) => r.hasTy (tabs.ty p.type) = true) (ownOuts tabs f) rs ∧
    ∃ rts : List Ty,
      List.Forall₂ (fun lt rt => regShapeOK rt lt = true) (leafTys tabs (ownOuts tabs f)) rts ∧
      RefinesList (List.zipWith Val.retype rts
        (((ownOuts tabs f).zip rs).flatMap fun (p, r) => leafVals (tabs.ty p.type) r)) rs' ∧
      Mem.Refines m m'

/-- What `blockOK`'s `imkArgOK` gives for an argument `a` of a converted value `x` of block `fb`
whose node in `g` is an `IMake` (the `IMake` data shortcut, `ECCheck.imakeData`): the source
mode (`a` is the same interface-shaped `IMake` in `f` with an unconverted data operand of the
same constructor shape in both, and `x` depends on `a` in `gb` when `a` is a value of `fb`) or
the target mode (`a` is interface-shaped in `g`, and `a` and its data operand are each a node of
`gb` that `x` depends on or placed in a strict dominator of `gb` in `g`: `HeldT`). -/
def EcImkOK (tabs : Tables) (f g : Func) (fb gb : Block) (x a : ID) : Prop :=
  ∀ aw, g.value? a = some aw → aw.op = .IMake → aw.args.size = 2 ∧
    ((∃ au, f.value? a = some au ∧ au.op = .IMake ∧ au.args.size = 2 ∧
        au.args[1]! = aw.args[1]! ∧ ifaceShape (shapeOf (typeShapes tabs) f a) = true ∧
        special f g aw.args[1]! = false ∧
        ((∃ e e', shapeOf (typeShapes tabs) f aw.args[1]! = .ptr e ∧
            shapeOf (typeShapes tabs) g aw.args[1]! = .ptr e') ∨
          (∃ fs n fs' n', shapeOf (typeShapes tabs) f aw.args[1]! = .agg fs n ∧
            shapeOf (typeShapes tabs) g aw.args[1]! = .agg fs' n')) ∧
        (a ∈ fb.values →
          Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList) a x)) ∨
      (ifaceShape (shapeOf (typeShapes tabs) g a) = true ∧ HeldT g gb x a ∧ HeldT g gb x aw.args[1]!))

theorem ecCv_of_not_special {tabs : Tables} {f g : Func} {x : ID} (h : special f g x = false)
    (y : Val) : ecCv tabs f g x y = y := by
  unfold special at h
  simp only [Bool.or_eq_false_iff] at h
  unfold ecCv
  rw [h.2]
  unfold converted at h
  cases hx : f.value? x with
  | none => rfl
  | some u =>
    have h1 := h.1
    rw [hx] at h1
    simp only [Bool.or_eq_false_iff] at h1
    simp only [Bool.false_eq_true, ite_false, h1.1, h1.2]

end GoFV.Proof.EC

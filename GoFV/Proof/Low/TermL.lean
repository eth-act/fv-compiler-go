import GoFV.Proof.TermStep
import GoFV.Opt.LowerCheck

/-!
# Lowered values as terms over atoms (issue #385)

Phase 1's `GoFV.Proof.Term` for `runL`: a value whose `termVL` holds is a term over the *atoms*
(phis, roots, activation-dependent values): `denL low D tabs ρ n x` evaluates `x`'s definition in
`D` recursively with fuel `n` as `runL` does in mode `low` (`Sem.evalValueL`: `opValL` at the
value's shape `shp low`, then `rty low`), reading atoms (and values `D` does not define) from
`ρ`. `low` is the function's `Func.lowered` (`runL` reads a lowered function's values as
registers, `Val.retypeL`, at the lowered shapes, `Sem.tyOfL`).

`TermRefL lowD D x lowE E y`: for every fuel on the left there is one on the right such that for
valuations `ρ ⊑ ρ'` whose atom values are fixed by `rty` at their shapes (`TypedL`),
`denL lowD D … x ⊑ denL lowE E … y`. `AtomArgsRefL` and `TermStepRefL` are the premises of the
atom simulation (`GoFV.Proof.Low.atomSimL_refines`) that the validator (`GoFV.Opt.LowerCheck.validateL`)
establishes (`GoFV.Proof.Low.validateL_termRef`).
-/

namespace GoFV.Proof.Low

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.LowerCheck GoFV.Proof.Term

/-- `x` is a term node of `D`. -/
def IsTermL (tabs : Tables) (D : ID → Option Value) (x : ID) : Prop :=
  ∃ v, D x = some v ∧ termVL tabs v = true

/-- The shape of `x`'s type in `D` in mode `low` (`other` if undefined). -/
def shapeL (low : Bool) (D : ID → Option Value) (tabs : Tables) (x : ID) : Ty :=
  ((D x).map fun v => shp low tabs v.type).getD .other

/-- The value of `x` as a term over the atoms, in mode `low`, with fuel `n` (`poison` when
exhausted). -/
def denL (low : Bool) (D : ID → Option Value) (tabs : Tables) (ρ : ID → Val) : Nat → ID → Val
  | 0, _ => .poison
  | n + 1, x =>
    match D x with
    | some v =>
      if termVL tabs v then
        rty low (shp low tabs v.type)
          (opValL tabs v.op (shp low tabs v.type) v.auxInt v.aux
            (v.args.toList.map (denL low D tabs ρ n)))
      else ρ x
    | none => ρ x

/-- The atoms `D` defines hold values fixed by `rty low` at their shapes (as `runL`'s registers
do). -/
def TypedL (low : Bool) (D : ID → Option Value) (tabs : Tables) (ρ : ID → Val) : Prop :=
  ∀ a, ¬ IsTermL tabs D a → (D a).isSome → rty low (shapeL low D tabs a) (ρ a) = ρ a

/-- `y` in `E` (mode `lowE`) refines `x` in `D` (mode `lowD`) as a term over the atoms. -/
def TermRefL (lowD : Bool) (D : ID → Option Value) (tabs : Tables) (x : ID) (lowE : Bool)
    (E : ID → Option Value) (tabs' : Tables) (y : ID) : Prop :=
  ∀ n, ∃ m, ∀ ρ ρ', ValRef ρ ρ' → TypedL lowD D tabs ρ → TypedL lowE E tabs' ρ' →
    Sem.Refines (denL lowD D tabs ρ n x) (denL lowE E tabs' ρ' m y)

/-- The arguments of every atom listed in `g` refine, as terms, those of the atom of `f` it
corresponds to (`atomPair`: the same ID and fields, a renamed op, or a lowered store). -/
def AtomArgsRefL (tabs : Tables) (f g : Func) : Prop :=
  ∀ b ∈ g.blocks, ∀ gb, g.block? b = some gb → ∀ a ∈ gb.values, ∀ u, g.value? a = some u →
    termVL tabs u = false →
    ∃ u', f.value? a = some u' ∧ atomPair tabs u' u = true ∧
      ∀ i < u.args.size,
        TermRefL f.lowered f.value? tabs u'.args[i]! g.lowered (listedDefs g) tabs u.args[i]!

/-- The terminator of `b` (`Sem.stepTermL`) on the control values `cs`. -/
def stepValsL (b : Block) (cs : List Val) : Res Next :=
  if b.kind.isArm64 then
    match b.kind with
    | .ARM64JUMPTABLE => do
      match Arm64.reg (← ctlV b cs 0) with
      | some x => succ b x.toNat
      | none => .stuck s!"b{b.id}: JUMPTABLE on poison or non-int"
    | k => do
      match Arm64.taken k b.auxInt (← ctlV b cs 0) with
      | some true => succ b 0
      | some false => succ b 1
      | none => .stuck s!"b{b.id}: {k.name} on poison or an ill-typed control"
  else stepVals b cs

/-- The terminator of every block of `g`, as a function of its controls' terms over the atoms,
refines that of `f`'s block, and the successors of `f`'s block are successors of `g`'s. -/
def TermStepRefL (tabs : Tables) (f g : Func) : Prop :=
  ∀ b ∈ g.blocks, ∀ fb gb, f.block? b = some fb → g.block? b = some gb →
    (∀ e ∈ fb.succs, e ∈ gb.succs) ∧
    ∀ n, ∃ m, ∀ ρ ρ', ValRef ρ ρ' → TypedL f.lowered f.value? tabs ρ →
      TypedL g.lowered (listedDefs g) tabs ρ' →
      Res.Rel Next.Refines (stepValsL fb (fb.controls.toList.map (denL f.lowered f.value? tabs ρ n)))
        (stepValsL gb (gb.controls.toList.map (denL g.lowered (listedDefs g) tabs ρ' m)))

end GoFV.Proof.Low

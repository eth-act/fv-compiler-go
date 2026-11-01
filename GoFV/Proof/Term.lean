import GoFV.Proof.PureMono
import GoFV.Opt.RewriteCheck

/-!
# Values as terms over atoms (issue #113)

A value whose op is a term op (`RewriteCheck.termOp`: evaluated by `evalPure`) is a term over
the *atoms* (phis, roots, frame-dependent values): `den D tabs ρ n x` evaluates `x`'s definition
in `D` recursively with fuel `n`, reading atoms (and values `D` does not define) from `ρ`, as
`evalValue` does (`evalPure` at the shape of the value's type, then `Val.retype`).

`TermRef D x E y`: for every fuel on the left there is one on the right such that, for any
valuations `ρ ⊑ ρ'` whose atom values are fixed by `retype` at their shapes (registers are,
`Typed`), `den D … x ⊑ den E … y`. It is the obligation the rewrite validator establishes for
the arguments of atoms and for controls (`GoFV.Proof.Pass.Rewrite`), and the premise of the
atom simulation.
-/

namespace GoFV.Proof.Term

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck

/-- The shape of `x`'s type in `D` (`other` if undefined). -/
def shape (D : ID → Option Value) (tabs : Tables) (x : ID) : Ty :=
  ((D x).map fun v => tabs.ty v.type).getD .other

/-- `x` is a term node of `D`. -/
def IsTerm (D : ID → Option Value) (x : ID) : Prop := ∃ v, D x = some v ∧ termOp v.op = true

/-- The value of `x` as a term over the atoms, with fuel `n` (`poison` when exhausted). -/
def den (D : ID → Option Value) (tabs : Tables) (ρ : ID → Val) : Nat → ID → Val
  | 0, _ => .poison
  | n + 1, x =>
    match D x with
    | some v =>
      if termOp v.op then
        (evalPure v.op (tabs.ty v.type) v.auxInt v.aux (v.args.toList.map (den D tabs ρ n))).retype
          (tabs.ty v.type)
      else ρ x
    | none => ρ x

/-- Pointwise refinement of valuations. -/
def ValRef (ρ ρ' : ID → Val) : Prop := ∀ a, Refines (ρ a) (ρ' a)

/-- The atoms of `D` hold values fixed by `retype` at their shapes (as registers do). -/
def Typed (D : ID → Option Value) (tabs : Tables) (ρ : ID → Val) : Prop :=
  ∀ a, ¬ IsTerm D a → (ρ a).retype (shape D tabs a) = ρ a

/-- `y` in `E` refines `x` in `D` as a term over the atoms. -/
def TermRef (D : ID → Option Value) (tabs : Tables) (x : ID) (E : ID → Option Value)
    (tabs' : Tables) (y : ID) : Prop :=
  ∀ n, ∃ m, ∀ ρ ρ', ValRef ρ ρ' → Typed D tabs ρ → Typed E tabs' ρ' →
    Refines (den D tabs ρ n x) (den E tabs' ρ' m y)

end GoFV.Proof.Term

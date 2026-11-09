import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values07

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `Neq` of two constants (`generic.rules:585`)

`(Neq<N> (Const<N> [c]) (Const<N> [d])) => (ConstBool [c != d])`. `rule_auto` leaves
`BitVec.ofInt N c ≠ BitVec.ofInt N d` from `c ≠ d` with both auxints in the signed `N`-bit range
(the `Eq` fold `:584` needs only the other direction); `ofInt_ne_of_range` closes it.
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

/-- `BitVec.ofInt w` is injective on the signed `w`-bit range. -/
theorem ofInt_ne_of_range {w : Nat} {c d : Int} (h1 : -(((2 ^ w : Nat) : Int) / 2) ≤ c)
    (h2 : c < (((2 ^ w : Nat) : Int) + 1) / 2) (h3 : -(((2 ^ w : Nat) : Int) / 2) ≤ d)
    (h4 : d < (((2 ^ w : Nat) : Int) + 1) / 2) (h : ¬c = d) :
    ¬BitVec.ofInt w c = BitVec.ofInt w d := fun he => h (by
  have := congrArg BitVec.toInt he
  rwa [toInt_ofInt_of_range h1 h2, toInt_ofInt_of_range h3 h4] at this)

/-- `rule_auto` up to `rule_close`'s normal form, then `rule_close` or `ofInt_ne_of_range`. -/
macro "neqc_auto" : tactic => `(tactic| (
  rule_unfold
  (try rule_ands)
  (try rule_clear_oracle)
  (try rule_norm)
  (try rule_ands)
  all_goals (repeat rule_split1)
  all_goals (try rule_widths)
  all_goals (repeat rule_gen1)
  all_goals (try simp only [GoFV.Proof.Rules.DV.int.injEq, GoFV.Proof.Rules.DV.bool.injEq] at *)
  all_goals (try rule_ands)
  all_goals (try rule_subst)
  all_goals (try rule_norm)
  all_goals (try simp_all only [rule_arith, rule_close_s])
  all_goals first
    | done
    | rule_close
    | (apply ofInt_ne_of_range <;> first | assumption | omega)))

/-- `generic.rules:585`: `(Neq16 (Const16 [c]) (Const16 [d])) => (ConstBool [c != d])` -/
theorem r_generic_585_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_585 := by
  neqc_auto

/-- `generic.rules:585`: `(Neq32 (Const32 [c]) (Const32 [d])) => (ConstBool [c != d])` -/
theorem r_generic_585_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_585_2 := by
  neqc_auto

/-- `generic.rules:585`: `(Neq64 (Const64 [c]) (Const64 [d])) => (ConstBool [c != d])` -/
theorem r_generic_585_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_585_3 := by
  neqc_auto

/-- `generic.rules:585`: `(Neq8 (Const8 [c]) (Const8 [d])) => (ConstBool [c != d])` -/
theorem r_generic_585_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_585_4 := by
  neqc_auto

end GoFV.Proof.Rules

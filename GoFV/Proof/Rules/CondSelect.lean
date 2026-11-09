import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values02

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `CondSelect` of equal or constant arms (`generic.rules:293`, `:294`)

After `rule_auto`'s splits the goals are `Refines y y` and `Refines (bif b then x else x) x`,
which `rule_close` (`rfl` up to reducible unfolding) does not close: `Sem.Refines.refl`, after a
case split on the condition for `:294`.
-/

namespace GoFV.Proof.Rules

/-- `rule_auto`'s unfolding and splits, then reflexivity of `Refines` (after a case split on
the one boolean in context) or `rule_close`. -/
macro "rule_refl" : tactic => `(tactic| (
  rule_unfold
  (try rule_ands)
  (try rule_clear_oracle)
  (try rule_norm)
  (try rule_ands)
  all_goals (repeat rule_split1)
  all_goals (try rule_widths)
  all_goals first
    | exact GoFV.SSA.Sem.Refines.refl _
    | (cases ‹Bool› <;> exact GoFV.SSA.Sem.Refines.refl _)
    | rule_close))

/-- `generic.rules:292`: `(CondSelect x _ (ConstBool [true ])) => x` -/
theorem r_generic_292_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_292 := by
  rule_refl

/-- `generic.rules:293`: `(CondSelect _ y (ConstBool [false])) => y` -/
theorem r_generic_293_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_293 := by
  rule_refl

/-- `generic.rules:294`: `(CondSelect x x _) => x` -/
theorem r_generic_294_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_294 := by
  rule_refl

end GoFV.Proof.Rules

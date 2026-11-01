import Lean

/-!
# Simp set of `rule_unfold_getd` (`TacticCond.lean`)

`rule_cond_ds`: `rule_unfold_ds` without `Option.getD` (the condition's evaluation with its
fallbacks to the oracle left folded). A separate module: `register_simp_attr` cannot be used in
the module that declares it, and adding it to `Attr.lean` rebuilds every rule module.
-/

register_simp_attr rule_cond_ds
register_simp_attr rule_cond_s

import GoFV.Rules.Generated.ARM64

/-!
# The proven-only `ARM64.rules` rule set (issue #385)

`ARM64.rules` restricted to the rules with a merged lowered obligation (`ArmRule.Sound`,
`ArmRule.SetOp`, `ArmRule.Rename`, `BlockRuleL.Sound`; `GoFV/Proof/Low/ProvenARM64.lean`), in
matching order: the rule set of the checked `lower` (`GoFV.Opt.lowerChecked`).
-/

namespace GoFV.Rules.ProvenARM64

open GoFV.Rules

/-- `ARM64.rules` restricted to its proven rules. -/
def lower : RuleSet where
  name := "ARM64"
  values := []
  blocks := []

end GoFV.Rules.ProvenARM64

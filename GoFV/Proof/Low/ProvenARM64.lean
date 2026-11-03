import GoFV.Proof.Low.RuleL
import GoFV.Rules.ProvenARM64

/-!
# The proven `ARM64.rules` rule set is sound (issue #385)

`arm64_allSound`: every rule of `GoFV.Rules.ProvenARM64.lower` has its lowered obligation
(`ArmRuleSet.AllSound`), from the rule lemmas of `GoFV/Proof/Low/Rules/*`.
-/

namespace GoFV.Proof.Low

open GoFV.Rules GoFV.Proof.Rules

/-- Every rule of `ProvenARM64.lower` is sound. -/
theorem arm64_allSound : ArmRuleSet.AllSound ProvenARM64.lower :=
  ⟨trivial, trivial, rfl, rfl, rfl, rfl, rfl, rfl⟩

end GoFV.Proof.Low

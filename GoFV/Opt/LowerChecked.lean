import GoFV.Opt.LowerCheck
import GoFV.Rules.ProvenARM64
import GoFV.Opt.FmaContract

/-!
# The checked `lower` (issue #385)

`lowerChecked`: the input with its fused multiply-add shapes contracted
(`GoFV.Opt.FmaContract.contractAll`, the `useFMA` rules of `ARM64.rules:1798-1809` applied to the
source, decision on #384), then `applyRewrite` with the proven `ARM64.rules`
(`GoFV.Rules.ProvenARM64.lower`) and its log, kept if `GoFV.Opt.LowerCheck.validateL` accepts it,
else the contracted input (`GoFV.Proof.Low.lower_refines`).
-/

namespace GoFV.Opt

/-- The proven `ARM64.rules` rules, indexed by op and block kind. -/
def lowerProvenTable : GoFV.Rules.Interp.Table :=
  GoFV.Rules.Interp.Table.ofRuleSet GoFV.Rules.ProvenARM64.lower

/-- **The checked `lower`.** -/
def lowerChecked : Pass := fun env f =>
  LowerCheck.checkedLowerWith lowerProvenTable env (FmaContract.contractAll f)

end GoFV.Opt

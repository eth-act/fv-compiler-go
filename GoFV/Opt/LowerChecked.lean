import GoFV.Opt.LowerCheck
import GoFV.Rules.ProvenARM64

/-!
# The checked `lower` (issue #385)

`lowerChecked`: `applyRewrite` with the proven `ARM64.rules` (`GoFV.Rules.ProvenARM64.lower`) and
its log, kept if `GoFV.Opt.LowerCheck.validateL` accepts it, else the input
(`GoFV.Proof.Low.lower_refines`).
-/

namespace GoFV.Opt

/-- The proven `ARM64.rules` rules, indexed by op and block kind. -/
def lowerProvenTable : GoFV.Rules.Interp.Table :=
  GoFV.Rules.Interp.Table.ofRuleSet GoFV.Rules.ProvenARM64.lower

/-- **The checked `lower`.** -/
def lowerChecked : Pass := LowerCheck.checkedLowerWith lowerProvenTable

end GoFV.Opt

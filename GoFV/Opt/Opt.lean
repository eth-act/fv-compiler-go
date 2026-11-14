import GoFV.Rules.Run
import GoFV.Rules.Generated.Generic
import GoFV.Rules.Generated.Divisible
import GoFV.Rules.Generated.Divmod
import GoFV.Rules.Proven
import GoFV.Opt.RewriteCheck

variable [GoFV.SSA.Sem.Addrs]

/-!
# opt, middle opt, late opt, divisible, divmod (`opt.go`)

`opt` = `applyRewrite(f, rewriteBlockgeneric, rewriteValuegeneric, removeDeadValues)`, run as
`opt`, `middle opt` and `late opt` (the pass name is visible to the rules);
`divisible`/`divmod` likewise with their rule files (docs/PASSES.md, issues #7, #25).

The proven-only passes (`optProven`, `divisibleProven`, `divmodProven`) fire only the rules
with a merged `Rule.Sound` lemma (`GoFV.Rules.Proven`, issue #113), like clifv's
`--opt-proven-only`. The checked passes (`optChecked`, …) are the proven-only passes validated
against their logs (`GoFV.Opt.RewriteCheck`): the passes the theorems are about.
-/

namespace GoFV.Opt

open GoFV.Rules

/-- The generic rules, indexed by op. -/
def genericTable : Interp.Table := Interp.Table.ofRuleSet Generated.Generic.ruleSet
def divisibleTable : Interp.Table := Interp.Table.ofRuleSet Generated.Divisible.ruleSet
def divmodTable : Interp.Table := Interp.Table.ofRuleSet Generated.Divmod.ruleSet

/-- `opt` (also `middle opt`, `late opt`). -/
def opt : Pass := rewritePass genericTable true

/-- `divisible`. -/
def divisible : Pass := rewritePass divisibleTable true

/-- `divmod`. -/
def divmod : Pass := rewritePass divmodTable true

/-- The proven-only rule tables. `divmod`'s is `guarded` (`Interp.checkedGuard`: `:136`–`:148`
fire only on a dividend `isNonNegative` shows nonnegative, as the validator requires). -/
def genericProvenTable : Interp.Table := Interp.Table.ofRuleSet Proven.generic
def divisibleProvenTable : Interp.Table := Interp.Table.ofRuleSet Proven.divisible
def divmodProvenTable : Interp.Table := { Interp.Table.ofRuleSet Proven.divmod with guarded := true }

/-- `opt` firing only proven rules. -/
def optProven : Pass := rewritePass genericProvenTable true

/-- `divisible` firing only proven rules. -/
def divisibleProven : Pass := rewritePass divisibleProvenTable true

/-- `divmod` firing only proven rules. -/
def divmodProven : Pass := rewritePass divmodProvenTable true

/-- `opt` firing only proven rules, validated. -/
def optChecked : Pass := checkedRewrite genericProvenTable

/-- `divisible` firing only proven rules, validated. -/
def divisibleChecked : Pass := checkedRewrite divisibleProvenTable

/-- `divmod` firing only proven rules, validated. -/
def divmodChecked : Pass := checkedRewrite divmodProvenTable

end GoFV.Opt

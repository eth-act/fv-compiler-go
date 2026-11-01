import GoFV.Proof.Rules.Tactic
import GoFV.Proof.Rules.Block
import GoFV.Rules.Generated.Generic.Blocks

/-!
# Block rule lemmas: `If` rules

`BlockRule.Sound` (`GoFV/Proof/Rules/Block.lean`) of the block rules of `generic.rules`: each is
an `If` rule whose control rule (`BlockRule.ctrlRule`, written out here as a constant so that
`rule_auto` can unfold it; `rfl` checks it) satisfies `Rule.Sound`.
-/

namespace GoFV.Proof.Rules

open GoFV.Rules GoFV.Rules.Generated.Generic

/-- The control rule of `generic.rules:1064`: `(Not cond) => (Not cond)`. -/
def r_generic_1064_ctrl : Rule where
  loc := ⟨"generic", 1064⟩
  op := .Not
  vars := [⟨"cond", .value, (.named "*Value")⟩]
  pat := (.op .Not none .any .any .any .fixed [(.bind 0)] false)
  cond := none
  block := none
  result := .build [{ op := .Not, ty := none, auxInt := none, aux := none, args := [.var 0] }]
  pos := []

/-- The control rule of `generic.rules:1065`: `(ConstBool [c]) && c => (ConstBool [true])`. -/
def r_generic_1065_ctrl : Rule where
  loc := ⟨"generic", 1065⟩
  op := .ConstBool
  vars := [⟨"c", .auxInt, .bool⟩]
  pat := (.op .ConstBool none .any (.bind 0) .any .fixed [] false)
  cond := (some (.var 0))
  block := none
  result := .build
    [{ op := .ConstBool, ty := none, auxInt := some (.lit .bool (.bool true)), aux := none, args := [] }]
  pos := []

/-- The control rule of `generic.rules:1066`: `(ConstBool [c]) && !c => (ConstBool [false])`. -/
def r_generic_1066_ctrl : Rule where
  loc := ⟨"generic", 1066⟩
  op := .ConstBool
  vars := [⟨"c", .auxInt, .bool⟩]
  pat := (.op .ConstBool none .any (.bind 0) .any .fixed [] false)
  cond := (some (.unop .not (.var 0) .bool))
  block := none
  result := .build
    [{ op := .ConstBool, ty := none, auxInt := some (.lit .bool (.bool false)), aux := none, args := [] }]
  pos := []

theorem r_generic_1064_ctrlRule : BlockRule.ctrlRule r_generic_1064 = some r_generic_1064_ctrl := rfl
theorem r_generic_1065_ctrlRule : BlockRule.ctrlRule r_generic_1065 = some r_generic_1065_ctrl := rfl
theorem r_generic_1066_ctrlRule : BlockRule.ctrlRule r_generic_1066 = some r_generic_1066_ctrl := rfl

theorem r_generic_1064_ctrl_sound : Rule.Sound r_generic_1064_ctrl := by rule_auto
theorem r_generic_1065_ctrl_sound : Rule.Sound r_generic_1065_ctrl := by rule_auto
theorem r_generic_1066_ctrl_sound : Rule.Sound r_generic_1066_ctrl := by rule_auto

/-- `generic.rules:1064`: `(If (Not cond) yes no) => (If cond no yes)` -/
theorem r_generic_1064_sound : BlockRule.Sound r_generic_1064 :=
  ⟨_, r_generic_1064_ctrlRule, r_generic_1064_ctrl_sound⟩

/-- `generic.rules:1065`: `(If (ConstBool [c]) yes no) && c => (First yes no)` -/
theorem r_generic_1065_sound : BlockRule.Sound r_generic_1065 :=
  ⟨_, r_generic_1065_ctrlRule, r_generic_1065_ctrl_sound⟩

/-- `generic.rules:1066`: `(If (ConstBool [c]) yes no) && !c => (First no yes)` -/
theorem r_generic_1066_sound : BlockRule.Sound r_generic_1066 :=
  ⟨_, r_generic_1066_ctrlRule, r_generic_1066_ctrl_sound⟩

end GoFV.Proof.Rules

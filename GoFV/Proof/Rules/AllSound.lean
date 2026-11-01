import GoFV.Proof.Rules.Block

/-!
# Sound rule sets

`RuleSet.AllSound s`: every value rule of `s` satisfies `Rule.Sound` (`Den.lean`), every block
rule `BlockRule.Sound` (`Block.lean`). The rewrite
passes' theorems (issue #113) take it as the hypothesis on their rule set; the proven-only rule
sets satisfy it (`GoFV/Proof/Rules/Proven.lean`, generated).
-/

namespace GoFV.Proof.Rules

open GoFV.Rules

/-- `P` holds for every element of the list (one conjunct per element). -/
def ForallL {α : Type} (P : α → Prop) : List α → Prop
  | [] => True
  | a :: l => P a ∧ ForallL P l

theorem ForallL.mem {α : Type} {P : α → Prop} : ∀ {l : List α}, ForallL P l → ∀ a ∈ l, P a
  | _ :: _, ⟨h, _⟩, _, .head _ => h
  | _ :: _, ⟨_, t⟩, a, .tail _ hm => ForallL.mem t a hm

/-- Every value rule of `s` satisfies `Rule.Sound`, every block rule `BlockRule.Sound`. -/
def _root_.GoFV.Rules.RuleSet.AllSound (s : RuleSet) : Prop :=
  (∀ p ∈ s.values, ∀ r ∈ p.2, Rule.Sound r) ∧ ∀ p ∈ s.blocks, ∀ br ∈ p.2, BlockRule.Sound br

theorem RuleSet.allSound_of {s : RuleSet}
    (h : ForallL (fun p : SSA.Op × List Rule => ForallL Rule.Sound p.2) s.values)
    (hb : ForallL (fun p : SSA.BlockKind × List BlockRule => ForallL BlockRule.Sound p.2)
      s.blocks) : s.AllSound :=
  ⟨fun p hp r hr => ForallL.mem (ForallL.mem h p hp) r hr,
   fun p hp r hr => ForallL.mem (ForallL.mem hb p hp) r hr⟩

end GoFV.Proof.Rules

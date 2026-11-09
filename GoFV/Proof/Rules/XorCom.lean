import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values13
import GoFV.Rules.Generated.Generic.Values14

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `Xor` with all ones (`generic.rules:657`)

`(Xor<N> (Const<N> [-1]) x) => (Com<N> x)`: after `rule_auto`'s splits the goal is
`BitVec.ofInt N (-1) ^^^ x = ~~~x`, which none of `rule_close`'s closers proves; the constant is
`BitVec.allOnes N` (`decide`) and `BitVec.allOnes_xor` closes it.
-/

namespace GoFV.Proof.Rules

/-- `rule_auto`'s unfolding and splits, then `rule_close` or the all-ones rewrite. -/
macro "rule_xor_ones" : tactic => `(tactic| (
  rule_unfold
  (try rule_ands)
  (try rule_clear_oracle)
  (try rule_norm)
  (try rule_ands)
  all_goals (repeat rule_split1)
  all_goals (try rule_widths)
  all_goals first
    | rule_close
    | (rw [show BitVec.ofInt 8 (-1) = BitVec.allOnes 8 from by decide]; exact BitVec.allOnes_xor)
    | (rw [show BitVec.ofInt 16 (-1) = BitVec.allOnes 16 from by decide]; exact BitVec.allOnes_xor)
    | (rw [show BitVec.ofInt 32 (-1) = BitVec.allOnes 32 from by decide]; exact BitVec.allOnes_xor)
    | (rw [show BitVec.ofInt 64 (-1) = BitVec.allOnes 64 from by decide]; exact BitVec.allOnes_xor)))

/-- `generic.rules:657`: `(Xor16 (Const16 [-1]) x) => (Com16 x)` -/
theorem r_generic_657_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_657 := by
  rule_xor_ones

/-- `generic.rules:657`: `(Xor32 (Const32 [-1]) x) => (Com32 x)` -/
theorem r_generic_657_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_657_2 := by
  rule_xor_ones

/-- `generic.rules:657`: `(Xor64 (Const64 [-1]) x) => (Com64 x)` -/
theorem r_generic_657_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_657_3 := by
  rule_xor_ones

/-- `generic.rules:657`: `(Xor8 (Const8 [-1]) x) => (Com8 x)` -/
theorem r_generic_657_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_657_4 := by
  rule_xor_ones

end GoFV.Proof.Rules

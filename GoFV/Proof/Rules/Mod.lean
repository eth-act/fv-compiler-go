import GoFV.Proof.Rules.Tactic
import GoFV.Proof.Rules.NonNeg
import GoFV.Proof.Rules.DivmodSPow2
import GoFV.Rules.Generated.Generic.Values06

/-!
# Rule lemmas: `Mod` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Mod` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:216`: `(Mod16 (Const16 [c]) (Const16 [d])) && d != 0 => (Const16 [c % d])` -/
theorem r_generic_216_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_216 := by rule_auto

/-- `generic.rules:1142`: `(Mod16 <t> n (Const16 [c])) && c < 0 && c != -1<<15 => (Mod16 <t> n (Const16 <t> [-c]))` -/
theorem r_generic_1142_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1142 := by rule_auto

/-- `generic.rules:1152`: `(Mod16 <t> x (Const16 [c])) && x.Op != OpConst16 && (c > 0 || c == -1<<15) => (Sub16 x (Mul16 <t> (Div16 <t> x (Const16 <t> [c])) (Const16 <t> [c])))` -/
theorem r_generic_1152_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1152 := by rule_auto

/-- `generic.rules:221`: `(Mod16u (Const16 [c]) (Const16 [d])) && d != 0 => (Const16 [int16(uint16(c) % uint16(d))])` -/
theorem r_generic_221_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_221 := by rule_auto

/-- `generic.rules:1160`: `(Mod16u <t> x (Const16 [c])) && x.Op != OpConst16 && c != 0 => (Sub16 x (Mul16 <t> (Div16u <t> x (Const16 <t> [c])) (Const16 <t> [c])))` -/
theorem r_generic_1160_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1160 := by rule_auto

/-- `generic.rules:217`: `(Mod32 (Const32 [c]) (Const32 [d])) && d != 0 => (Const32 [c % d])` -/
theorem r_generic_217_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_217 := by rule_auto

/-- `generic.rules:1143`: `(Mod32 <t> n (Const32 [c])) && c < 0 && c != -1<<31 => (Mod32 <t> n (Const32 <t> [-c]))` -/
theorem r_generic_1143_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1143 := by rule_auto

/-- `generic.rules:1154`: `(Mod32 <t> x (Const32 [c])) && x.Op != OpConst32 && (c > 0 || c == -1<<31) => (Sub32 x (Mul32 <t> (Div32 <t> x (Const32 <t> [c])) (Const32 <t> [c])))` -/
theorem r_generic_1154_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1154 := by rule_auto

/-- `generic.rules:222`: `(Mod32u (Const32 [c]) (Const32 [d])) && d != 0 => (Const32 [int32(uint32(c) % uint32(d))])` -/
theorem r_generic_222_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_222 := by rule_auto

/-- `generic.rules:1162`: `(Mod32u <t> x (Const32 [c])) && x.Op != OpConst32 && c != 0 => (Sub32 x (Mul32 <t> (Div32u <t> x (Const32 <t> [c])) (Const32 <t> [c])))` -/
theorem r_generic_1162_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1162 := by rule_auto

/-- `generic.rules:1134`: `(Mod8 <t> n (Const8 [c])) && isNonNegative(n) && isPowerOfTwo(c) => (And8 n (Const8 <t> [c-1]))` -/
theorem r_generic_1134_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1134 := by
  rule_unfold
  (try rule_ands)
  (try rule_clear_oracle)
  (try rule_norm)
  (try rule_ands)
  all_goals (repeat rule_split1)
  all_goals (try rule_widths)
  all_goals mods_pow2

/-- `generic.rules:1135`: `(Mod16 <t> n (Const16 [c])) && isNonNegative(n) && isPowerOfTwo(c) => (And16 n (Const16 <t> [c-1]))` -/
theorem r_generic_1135_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1135 := by
  rule_unfold
  (try rule_ands)
  (try rule_clear_oracle)
  (try rule_norm)
  (try rule_ands)
  all_goals (repeat rule_split1)
  all_goals (try rule_widths)
  all_goals mods_pow2

/-- `generic.rules:1136`: `(Mod32 <t> n (Const32 [c])) && isNonNegative(n) && isPowerOfTwo(c) => (And32 n (Const32 <t> [c-1]))` -/
theorem r_generic_1136_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1136 := by
  rule_unfold
  (try rule_ands)
  (try rule_clear_oracle)
  (try rule_norm)
  (try rule_ands)
  all_goals (repeat rule_split1)
  all_goals (try rule_widths)
  all_goals mods_pow2

/-- `generic.rules:1137`: `(Mod64 <t> n (Const64 [c])) && isNonNegative(n) && isPowerOfTwo(c) => (And64 n (Const64 <t> [c-1]))` -/
theorem r_generic_1137_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1137 := by
  rule_unfold
  (try rule_ands)
  (try rule_clear_oracle)
  (try rule_norm)
  (try rule_ands)
  all_goals (repeat rule_split1)
  all_goals (try rule_widths)
  all_goals mods_pow2

/-- `generic.rules:1138`: `(Mod64 n (Const64 [-1<<63])) && isNonNegative(n) => n` -/
theorem r_generic_1138_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1138 := by
  rule_unfold
  (try rule_ands)
  (try rule_clear_oracle)
  (try rule_norm)
  (try rule_ands)
  all_goals (repeat rule_split1)
  all_goals (try rule_widths)
  all_goals first
    | exact NonNegCmp.srem_intMin64_of_msb _ ‹_›
    | rule_close

end GoFV.Proof.Rules

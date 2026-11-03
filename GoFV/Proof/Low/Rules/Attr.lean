import Lean

/-!
# Simp set of the lowering rule lemmas (issue #385)

`arm_sem`: the arm64 op families (`Sem/Arm64/*`) and register facts the rule lemmas of
`GoFV/Proof/Low/Rules/*` normalize with (`arm_norm`, `GoFV/Proof/Low/Rules/Tactic.lean`).
-/

register_simp_attr arm_sem

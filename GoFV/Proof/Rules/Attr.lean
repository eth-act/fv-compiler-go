import Lean

/-!
# Simp sets of the rule lemmas (`GoFV/Proof/Rules/Lemmas.lean`, `Names.lean`)

- `rule_helper`: `Helper.ofName "<name>" = …` and `typShape "<name>" = …` for the names the
  rules use (the kernel compares strings slowly; these are proved once).
- `rule_sem`: the op families as `Option.elim` chains over `Val.asInt`/`Val.asBool`, value and
  refinement facts, and the `BitVec` forms of shifts, rotations and constants.
- `rule_arith`: pushing auxint arithmetic (`Int`) into `BitVec` for the closing step.
- `rule_bits`: all-ones constants as `BitVec.allOnes` (bitwise identities per bit).
- `rule_amt`: amounts and conditions as `Nat`/`Int` arithmetic with remainders by constants
  (`omega` form; rotation amounts, constant shifts, comparisons with constants).
- `rule_cmp`: `BitVec` comparisons and equations as `Nat`/`Int` ones on `toNat` (`omega` form).
- `rule_unfold_ds`, `rule_unfold_s`, `rule_norm_s`, `rule_close_s`, `rule_eval`: the lemma
  lists of the tactics (`Tactic.lean`, `NonVacuous.lean`). A long list inside a tactic macro's
  quotation compiles to code building its syntax: 3.9 MB of `.olean` for `Tactic.lean`.
-/

register_simp_attr rule_helper
register_simp_attr rule_sem
register_simp_attr rule_arith
register_simp_attr rule_bits
register_simp_attr rule_amt
register_simp_attr rule_cmp
register_simp_attr rule_unfold_ds
register_simp_attr rule_unfold_s
register_simp_attr rule_norm_s
register_simp_attr rule_close_s
register_simp_attr rule_eval

/-- `rule_norm` (`Tactic.lean`) with `decide := true`: `rule_auto`'s fallback for the proofs that
need it. -/
register_option gofv.ruleNorm.decide : Bool := {
  defValue := false
  descr := "rule_norm: simp_all with decide := true (rule_auto's fallback)" }

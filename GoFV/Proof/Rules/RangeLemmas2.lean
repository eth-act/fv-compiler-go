import GoFV.Proof.Rules.RangeLemmas

/-!
# The signed range-check identities with `c + 1`/`d + 1` (`generic.rules:325–328`, `349–352`)

See `RangeLemmas.lean`; a separate module for the size of the `omega` proofs.
-/

namespace GoFV.Proof.Rules

theorem range_and_s1 {w : Nat} (x c d : BitVec w) (h : c.toInt + 1 ≤ d.toInt) :
    (x - (c + 1#w)).ult (d - c - 1#w) = (c.slt x && x.slt d) := by
  range_lemma x c d

theorem range_and_s1_le {w : Nat} (x c d : BitVec w) (h : c.toInt + 1 ≤ d.toInt) :
    (x - (c + 1#w)).ule (d - c - 1#w) = (c.slt x && x.sle d) := by
  range_lemma x c d

theorem range_or_s1 {w : Nat} (x c d : BitVec w) (h : d.toInt + 1 ≤ c.toInt) :
    (c - d - 1#w).ult (x - (d + 1#w)) = (c.slt x || x.sle d) := by
  range_lemma x c d

theorem range_or_s1_le {w : Nat} (x c d : BitVec w) (h : d.toInt + 1 ≤ c.toInt) :
    (c - d - 1#w).ule (x - (d + 1#w)) = (c.sle x || x.sle d) := by
  range_lemma x c d

end GoFV.Proof.Rules

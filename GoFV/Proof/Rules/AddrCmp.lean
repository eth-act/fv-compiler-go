import GoFV.Proof.Rules.AllSound
import GoFV.Rules.Generated.Generic.Values03
import GoFV.Rules.Generated.Generic.Values08

/-!
# Rule lemmas: comparisons of symbol addresses (issue #69)

`(EqPtr (Addr {x} _) (Addr {y} _)) => (ConstBool [x == y])` (`generic.rules:1648`) and
`(NeqPtr (Addr {x} _) (Addr {y} _)) => (ConstBool [x != y])` (`:1651`) compare the two symbols,
which the denotation leaves to the oracle. The obligation is `Rule.AddrCmp` (`addrCmpShape`), and
the checked rewrite validates each instance (`GoFV.Opt.RewriteCheck.addrCmpOK`; refinement:
`GoFV.Proof.Pass.Rewrite.ACFacts.step`: an `Addr` denotes offset 0 of the global block its symbol
names, so two of them are equal iff the names are).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:1648`: `(EqPtr (Addr {x} _) (Addr {y} _)) => (ConstBool [x == y])` -/
theorem r_generic_1648_sound : Rule.AddrCmp GoFV.Rules.Generated.Generic.r_generic_1648 := rfl

/-- `generic.rules:1651`: `(NeqPtr (Addr {x} _) (Addr {y} _)) => (ConstBool [x != y])` -/
theorem r_generic_1651_sound : Rule.AddrCmp GoFV.Rules.Generated.Generic.r_generic_1651 := rfl

/-- The shape is not vacuous: `generic.rules:1649` (`(EqPtr (Addr {x} _) (OffPtr [o] (Addr {y}
_))) => (ConstBool [x == y && o == 0])`) has an `OffPtr` operand. -/
example : ¬ Rule.AddrCmp GoFV.Rules.Generated.Generic.r_generic_1649 := by
  unfold Rule.AddrCmp; decide

end GoFV.Proof.Rules

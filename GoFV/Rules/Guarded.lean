import GoFV.Rules.Generated.Generic.Values02

/-!
# Guarded rules (issue #290)

Generated rules that the proven-only rule sets (`GoFV.Rules.Proven`) carry under a stronger
condition, because only that restriction is a refinement. Each is the generated rule with its
condition replaced (written out, so that the rule tactics unfold it as a generated rule; the
`_eq` theorems check that everything else is the generated rule's). Stock Go fires
the rule in more places, which the proven-only passes leave off stock.
-/

namespace GoFV.Rules.Guarded

open GoFV.Rules

/-- `generic.rules:1072` `(Convert (Convert ptr mem) mem) => ptr` at an integer type only
(`!v.Type.IsPtrShaped()`): the round trip `uintptr → unsafe.Pointer → uintptr`, where the
semantics' `Convert`s give back the leaf's word. The pointer round trip is not a `Sem.Refines`
refinement: the source is the integer `addr p` (a pointer-shaped integer word), the target the
pointer `p` (docs/proofs/rules.md "Findings", #290). -/
def r_generic_1072 : Rule where
  loc := ⟨"generic", 1072⟩
  op := .Convert
  vars := [⟨"mem", .value, (.named "*Value")⟩, ⟨"ptr", .value, (.named "*Value")⟩]
  pat := (.op .Convert none .any .any .any .fixed [(.op .Convert none .any .any .any .fixed [(.bind 1), (.bind 0)] false), (.same 0)] false)
  cond := some (.unop .not (.method (.field (.rsv .v) "Type" (.named "*types.Type"))
    "IsPtrShaped" [] .bool) .bool)
  block := none
  result := .copy (.var 1)
  pos := []

/-- The guarded rule is the generated one but for its condition. -/
theorem r_generic_1072_eq : { r_generic_1072 with cond := none } = Generated.Generic.r_generic_1072 :=
  rfl

/-- The guarded rules (their generated forms stay unproven). -/
def all : List Rule := [r_generic_1072]

end GoFV.Rules.Guarded

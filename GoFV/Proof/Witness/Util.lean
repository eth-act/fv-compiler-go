/-!
# Shared witness helpers

Small lemmas that several witness modules need. They live here, once, so that every
`GoFV.Proof` module can be imported together (issue #133, `GoFVTest/Proof/AllProof.lean`).
-/

namespace GoFV.Proof.Witness

/-- A `Unit`-valued check that `toBool` accepts succeeded. -/
theorem ok_of_toBool {ε : Type} {e : Except ε Unit} (h : e.toBool = true) : e = .ok () := by
  revert h; cases e <;> simp [Except.toBool]

/-- An `Except` value that `toBool` accepts is `.ok` of something. -/
theorem exists_ok_of_toBool {ε α : Type} {x : Except ε α} (h : x.toBool = true) :
    ∃ a, x = .ok a := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl⟩

example : ok_of_toBool (e := (.ok () : Except String Unit)) rfl = rfl := rfl
example : exists_ok_of_toBool (x := (.ok 3 : Except String Nat)) rfl = ⟨3, rfl⟩ := rfl

end GoFV.Proof.Witness

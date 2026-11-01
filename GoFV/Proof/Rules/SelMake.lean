import GoFV.Proof.Rules.Dec
import GoFV.Rules.Generated.Generic.Values01
import GoFV.Rules.Generated.Generic.Values12

/-!
# Rule lemmas: generic selections of a `Make`

`Rule.Sound` of the generic rules that select a component of a `Make`, as the dec rules in
`Dec.lean` (`dec_unfold` keeps the `Make`'s argument shapes `makeArgOk`; `sel_make2`,
`sel_make3`, `select_retype_make`): `(ArraySelect (ArrayMake1 x)) => x` (`:992`, the same rule
as `dec.rules:126`) and the constant lengths `(StringLen (StringMake _ (Const64 <t> [c])))`,
`(SliceLen (SliceMake _ (Const64 <t> [c]) _))`, `(SliceCap (SliceMake _ _ (Const64 <t> [c])))`
`=> (Const64 <t> [c])` (`:1012`, `:1031`, `:1032`): the selected argument is the result
(`Int64.ofInt c.toInt = c`). The 32-bit forms `:1033`/`:1034` and the selections of selections
`:1035–1038` are not proved: the latter retype the inner selection at the inner and at the
outer type, which agree only up to a lemma about composite retypes not written yet.
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

/-- `generic.rules:992`: `(ArraySelect (ArrayMake1 x)) => x` -/
theorem r_generic_992_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_992 := by
  dec_unfold GoFV.Rules.Generated.Generic.r_generic_992
  unfold Comp.selectAux
  split
  · exact .poison _
  · have h := select_retype_make (e.ty [0]) (e.auxInt []).toInt.toNat [e.leaf [0, 0]] [e.ty [0, 0]]
      (fun i v t h1 h2 => by
        match i with
        | 0 => simp at h1 h2; subst h1 h2; exact ⟨hlt, hat⟩
        | _ + 1 => simp at h1) rfl
    generalize (e.auxInt []).toInt.toNat = k at h ⊢
    cases k with
    | zero => exact h
    | succ k =>
      have h' : Refines (Comp.select (k + 1) [Val.retype (e.ty [0]) (Comp.make [e.leaf [0, 0]])])
          .poison := by simpa using h
      rw [eq_poison_of_refines h']
      exact .poison _

/-- `generic.rules:1012`: `(StringLen (StringMake _ (Const64 <t> [c]))) => (Const64 <t> [c])` -/
theorem r_generic_1012_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1012 := by
  dec_unfold GoFV.Rules.Generated.Generic.r_generic_1012
  rw [Int64.ofInt_toInt]
  exact sel_make2 hlt (Val.retype_hasTy _ _) hat.1 hat.2 1

/-- `generic.rules:1031`: `(SliceLen (SliceMake _ (Const64 <t> [c]) _)) => (Const64 <t> [c])` -/
theorem r_generic_1031_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1031 := by
  dec_unfold GoFV.Rules.Generated.Generic.r_generic_1031
  rw [Int64.ofInt_toInt]
  exact sel_make3 hlt.1 (Val.retype_hasTy _ _) hlt.2 hat.1 hat.2.1 hat.2.2 1

/-- `generic.rules:1032`: `(SliceCap (SliceMake _ _ (Const64 <t> [c]))) => (Const64 <t> [c])` -/
theorem r_generic_1032_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1032 := by
  dec_unfold GoFV.Rules.Generated.Generic.r_generic_1032
  rw [Int64.ofInt_toInt]
  exact sel_make3 hlt.1 hlt.2 (Val.retype_hasTy _ _) hat.1 hat.2.1 hat.2.2 2

end GoFV.Proof.Rules

import GoFV.Proof.Rules.Tactic
import GoFV.Proof.Rules.DecShape
import GoFV.Rules.Generated.Dec.Values00

/-!
# Rule lemmas: `dec` rules, selections (`dec.rules`, issue #17)

`Rule.Sound` of the dec rules that select a component of a `Make` (`(StringPtr (StringMake ptr
_)) => ptr`, …) or of a pointer-shaped value (`(StructSelect x) && x.Type.IsPtrShaped() => x`).

A selection of a `Make` retyped at its type's shape gives the argument back when the argument
has the component's shape (`select_retype_make`): `Pat.argsOK` of the `Make` (`makeArgOk`,
issue #17) with the leaf's shape (`Pat.typed`). A selection of a pointer-shaped value is
`poison` (`Comp.select` reads only aggregates).

Not provable under `Rule.Sound` (`docs/proofs/rules.md`, "Dec rules"):

- `dec.rules:119`/`:120` (`(ArrayMake1 x)`/`(StructMake x) && x.Type.IsPtrShaped() => x`):
  false under the semantics. A one-field aggregate of a pointer is `.agg [p]` at the shape
  `.agg [(0, .ptr _)] 8`; Go represents it as the bare pointer. Model gap, not a Go bug
  (agreed with agent Semantics4; `docs/plans/semantics.md` §10). Their obligation is
  `Rule.Drop` (`DecMakeSel.lean`): the checked rewrite keeps the `Make`.
- `dec.rules:125` (`(IMake _typ (ArrayMake1 val)) => (IMake _typ val)`): correct only at the
  interface shape, which the obligation does not fix (an `IMake` typed with an aggregate data
  word). `:103`/`:104`/`:127` (`StructSelect`/`ArraySelect` of `IData x`) are proven in
  `IDataSel.lean` (`argShapeOk` fixes an `IData` operand's shape, `idataArgOk`).
- `dec.rules:102` (`imakeOfStructMake(v)`), `:106` (`StructSelect [i] (StructMake ___)`,
  variadic, `x.Args[i]`): no `Rule.Sound` form (`Pat.arityOk`, custom result).
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

/-- Unfold `Rule.Sound r` of a dec rule, keeping the argument shapes `hat` (`makeArgOk`). -/
syntax "dec_unfold " ident : tactic

set_option hygiene false in
macro_rules
  | `(tactic| dec_unfold $r:ident) => `(tactic| (
    refine ⟨rfl, ?_⟩
    intro e or hbt
    dsimp only [$r:ident, rule_unfold_ds]
    simp only [rule_helper, rule_unfold_s]
    intro hwf hc hcond hty hlt hat hnn
    clear hnn
    try simp only [Pat.argsOK, Pat.argsOKs, reduceArgShapeOk, Bool.and_eq_true, Bool.true_and,
      Bool.and_true, Nat.zero_add, Nat.reduceAdd] at hat
    try dsimp only [condHolds, rule_unfold_ds] at hcond
    try simp only [rule_helper, rule_unfold_s] at hcond))

/-- Two arguments of a `Make`. -/
theorem sel_make2 {T : Ty} {a b : Val} {ta tb : Ty} (ha : a.hasTy ta = true) (hb : b.hasTy tb = true)
    (hma : makeArgOk T 0 ta = true) (hmb : makeArgOk T 1 tb = true) (k : Nat) :
    Refines (Comp.select k [(Comp.make [a, b]).retype T]) ([a, b].getD k .poison) :=
  select_retype_make T k [a, b] [ta, tb] (fun i v t h1 h2 => by
    match i with
    | 0 => simp at h1 h2; subst h1 h2; exact ⟨ha, hma⟩
    | 1 => simp at h1 h2; subst h1 h2; exact ⟨hb, hmb⟩
    | _ + 2 => simp at h1) rfl

/-- Three arguments of a `Make`. -/
theorem sel_make3 {T : Ty} {a b c : Val} {ta tb tc : Ty} (ha : a.hasTy ta = true)
    (hb : b.hasTy tb = true) (hc : c.hasTy tc = true) (hma : makeArgOk T 0 ta = true)
    (hmb : makeArgOk T 1 tb = true) (hmc : makeArgOk T 2 tc = true) (k : Nat) :
    Refines (Comp.select k [(Comp.make [a, b, c]).retype T]) ([a, b, c].getD k .poison) :=
  select_retype_make T k [a, b, c] [ta, tb, tc] (fun i v t h1 h2 => by
    match i with
    | 0 => simp at h1 h2; subst h1 h2; exact ⟨ha, hma⟩
    | 1 => simp at h1 h2; subst h1 h2; exact ⟨hb, hmb⟩
    | 2 => simp at h1 h2; subst h1 h2; exact ⟨hc, hmc⟩
    | _ + 3 => simp at h1) rfl

/-- `Refines a poison` only for `a = poison`. -/
theorem eq_poison_of_refines {a : Val} (h : Refines a .poison) : a = .poison := by
  cases h; rfl

/-- A selection of a non-aggregate is `poison`. -/
theorem select_nonAgg {k : Nat} {v : Val} (h : ∀ vs, v ≠ .agg vs) : Comp.select k [v] = .poison := by
  cases v <;> first | rfl | exact absurd rfl (h _)

theorem selectAux_nonAgg {ai : Int64} {v : Val} (h : ∀ vs, v ≠ .agg vs) :
    Comp.selectAux ai [v] = .poison := by
  unfold Comp.selectAux
  split
  · rfl
  · exact select_nonAgg h

/-- A value of a pointer shape or of `.other` is no aggregate. -/
theorem nonAgg_of_hasTy {v : Val} {t : Ty} (hv : v.hasTy t = true)
    (ht : (∃ e, t = .ptr e) ∨ t = .other) : ∀ vs, v ≠ .agg vs := by
  intro vs h
  subst h
  rcases ht with ⟨e, rfl⟩ | rfl <;> simp [Val.hasTy] at hv

/-- The condition `x.Type.IsPtrShaped()` holds only at a pointer shape or `.other`, where the
selection is `poison`. -/
syntax "ptr_shaped_cond" : tactic

set_option hygiene false in
macro_rules
  | `(tactic| ptr_shaped_cond) => `(tactic| (
    have hsh : (∃ el, e.ty [0] = .ptr el) ∨ e.ty [0] = .other := by
      revert hcond
      generalize e.ty [0] = t
      cases t <;> simp [kindDV, kindE]
    rw [selectAux_nonAgg (nonAgg_of_hasTy hlt hsh)]
    exact .poison _))

/-- `dec.rules:13`: `(ComplexReal (ComplexMake real _ )) => real` -/
theorem r_dec_13_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_13 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_13
  exact sel_make2 hlt.1 hlt.2 hat.1 hat.2 0

/-- `dec.rules:14`: `(ComplexImag (ComplexMake _ imag )) => imag` -/
theorem r_dec_14_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_14 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_14
  exact sel_make2 hlt.1 hlt.2 hat.1 hat.2 1

/-- `dec.rules:42`: `(StringPtr (StringMake ptr _)) => ptr` -/
theorem r_dec_42_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_42 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_42
  exact sel_make2 hlt.1 hlt.2 hat.1 hat.2 0

/-- `dec.rules:43`: `(StringLen (StringMake _ len)) => len` -/
theorem r_dec_43_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_43 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_43
  exact sel_make2 hlt.1 hlt.2 hat.1 hat.2 1

/-- `dec.rules:58`: `(SlicePtr (SliceMake ptr _ _ )) => ptr` -/
theorem r_dec_58_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_58 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_58
  exact sel_make3 hlt.1 hlt.2.1 hlt.2.2 hat.2.1.2 hat.2.2.1.2 hat.2.2.2.2 0

/-- `dec.rules:59`: `(SliceLen (SliceMake _ len _)) => len` -/
theorem r_dec_59_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_59 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_59
  exact sel_make3 hlt.1 hlt.2.1 hlt.2.2 hat.2.1.2 hat.2.2.1.2 hat.2.2.2.2 1

/-- `dec.rules:60`: `(SliceCap (SliceMake _ _ cap)) => cap` -/
theorem r_dec_60_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_60 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_60
  exact sel_make3 hlt.1 hlt.2.1 hlt.2.2 hat.2.1.2 hat.2.2.1.2 hat.2.2.2.2 2

/-- `dec.rules:61`: `(SlicePtrUnchecked (SliceMake ptr _ _ )) => ptr` -/
theorem r_dec_61_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_61 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_61
  exact sel_make3 hlt.1 hlt.2.1 hlt.2.2 hat.1.2 hat.2.1.2 hat.2.2.2 0

/-- `dec.rules:82`: `(ITab (IMake itab _)) => itab` -/
theorem r_dec_82_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_82 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_82
  exact sel_make2 hlt.1 hlt.2 hat.1 hat.2 0

/-- `dec.rules:83`: `(IData (IMake _ data)) && data.Op != OpStructMake && data.Op != OpArrayMake1 => data` -/
theorem r_dec_83_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_83 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_83
  exact sel_make2 hlt.1 hlt.2 hat.2.1 hat.2.2 1

/-- `dec.rules:115`: `(StructSelect x) && x.Type.IsPtrShaped() => x` -/
theorem r_dec_115_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_115 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_115
  ptr_shaped_cond

/-- `dec.rules:116`: `(ArraySelect [0] x) && x.Type.IsPtrShaped() => x` -/
theorem r_dec_116_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_116 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_116
  ptr_shaped_cond

/-- `dec.rules:126`: `(ArraySelect (ArrayMake1 x)) => x` -/
theorem r_dec_126_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_126 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_126
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

end GoFV.Proof.Rules

import GoFV.Proof.Rules.Dec
import GoFV.Rules.Generated.Generic.Values01
import GoFV.Rules.Generated.Generic.Values12

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: selections of an interface's data word (issue #69)

`(StructSelect (IData x)) && v.Type.Size() > 0 => (IData x)` (`generic.rules:982`,
`dec.rules:103`), its `Size() == 0` form `=> (Empty)` (`:983`, `dec.rules:104`) and
`(ArraySelect [0] (IData x)) => (IData x)` (`:1001`, `dec.rules:127`). `argShapeOk` gives an
`IData` operand a shape whose second component is a word (`idataArgOk`: the interface shape), so
`IData x` is a word retyped, never an aggregate (`retype_ne_agg`), and the selection of it is
`poison` (`selectAux_nonAgg`): the source is `poison`. Go puts a one-field struct or array of a
pointer into a direct interface as the bare pointer; the model keeps it as `.agg [p]`, so a
selection of the data word reads nothing (as for `generic.rules:981`, `IMFacts.step`).
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

/-- A value of a word shape is no aggregate. -/
theorem hasTy_word_ne_agg {v : Val} {f : Ty} (hf : (isPtrTy f || isInt64Ty f) = true)
    (hv : v.hasTy f = true) (vs : List Val) : v ≠ .agg vs := by
  rintro rfl
  cases f with
  | ptr _ => simp [Val.hasTy] at hv
  | int w => cases w <;> simp [Val.hasTy, isPtrTy, isInt64Ty] at hv hf
  | _ => simp [isPtrTy, isInt64Ty] at hf

/-- A component of a list of values with shapes. -/
theorem hasTyList_getElem? : ∀ {vs : List Val} {ts : List Ty}, Val.hasTyList vs ts = true →
    ∀ (i : Nat) (t : Ty), ts[i]? = some t → ∃ v, vs[i]? = some v ∧ v.hasTy t = true
  | [], [], _, _, _, h => by simp at h
  | v :: vs, t' :: ts, h, i, t, ht => by
    simp only [Val.hasTyList, Bool.and_eq_true] at h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ht
      subst ht
      exact ⟨v, rfl, h.1⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at ht ⊢
      exact hasTyList_getElem? h.2 i t ht
  | [], _ :: _, h, _, _, _ => by simp [Val.hasTyList] at h
  | _ :: _, [], h, _, _, _ => by simp [Val.hasTyList] at h

/-- The data word of a value of a shape `idataArgOk` accepts is no aggregate. -/
theorem idata_select_ne_agg {x : Val} {t : Ty} (hx : x.hasTy t = true)
    (ht : idataArgOk t = true) (ws : List Val) : Comp.select 1 [x] ≠ .agg ws := by
  cases t with
  | agg fs n =>
    rcases h1 : fs[1]? with _ | ⟨o, f⟩
    · simp [idataArgOk, h1] at ht
    · have hw : (isPtrTy f || isInt64Ty f) = true := by simpa [idataArgOk, h1] using ht
      cases x with
      | poison => simp [Comp.select]
      | agg vs =>
        simp only [Val.hasTy] at hx
        obtain ⟨v, hv, hvt⟩ := hasTyList_getElem? hx 1 f (by simp [h1])
        simp only [Comp.select, List.getD_eq_getElem?_getD, hv, Option.getD_some]
        exact hasTy_word_ne_agg hw hvt ws
      | _ => simp [Val.hasTy] at hx
  | _ => simp [idataArgOk] at ht

/-- A non-aggregate retyped is no aggregate. -/
theorem retype_ne_agg {v : Val} (hv : ∀ vs, v ≠ .agg vs) (t : Ty) (ws : List Val) :
    v.retype t ≠ .agg ws := by
  have hw : ∀ p : Ptr, p.word ≠ .agg ws := fun p h => by
    unfold Ptr.word at h; split at h <;> (try split at h) <;> cases h
  intro h
  unfold Val.retype at h
  split at h
  all_goals first
    | exact hv _ rfl
    | exact hw _ h
    | cases h
    | (split at h <;> cases h)

/-- The selection of an `IData` of an operand of a shape `idataArgOk` accepts is `poison`. -/
theorem selectAux_idata {ai : Int64} {x : Val} {t T : Ty} (hx : x.hasTy t = true)
    (ht : idataArgOk t = true) :
    Comp.selectAux ai [(Comp.select 1 [x]).retype T] = .poison :=
  selectAux_nonAgg (retype_ne_agg (idata_select_ne_agg hx ht) T)

/-- `generic.rules:982`: `(StructSelect (IData x)) && v.Type.Size() > 0 => (IData x)` -/
theorem r_generic_982_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_982 := by
  dec_unfold GoFV.Rules.Generated.Generic.r_generic_982
  rw [selectAux_idata hlt hat]
  exact .poison _

/-- `generic.rules:983`: `(StructSelect (IData x)) && v.Type.Size() == 0 => (Empty)` -/
theorem r_generic_983_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_983 := by
  dec_unfold GoFV.Rules.Generated.Generic.r_generic_983
  rw [selectAux_idata hlt hat]
  exact .poison _

/-- `generic.rules:1001`: `(ArraySelect [0] (IData x)) => (IData x)` -/
theorem r_generic_1001_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1001 := by
  dec_unfold GoFV.Rules.Generated.Generic.r_generic_1001
  rw [selectAux_idata hlt hat]
  exact .poison _

/-- `dec.rules:103`: `(StructSelect (IData x)) && v.Type.Size() > 0 => (IData x)` -/
theorem r_dec_103_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_103 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_103
  rw [selectAux_idata hlt hat]
  exact .poison _

/-- `dec.rules:104`: `(StructSelect (IData x)) && v.Type.Size() == 0 => (Empty)` -/
theorem r_dec_104_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_104 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_104
  rw [selectAux_idata hlt hat]
  exact .poison _

/-- `dec.rules:127`: `(ArraySelect [0] (IData x)) => (IData x)` -/
theorem r_dec_127_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_127 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_127
  rw [selectAux_idata hlt hat]
  exact .poison _

end GoFV.Proof.Rules

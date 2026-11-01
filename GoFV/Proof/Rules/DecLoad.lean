import GoFV.Proof.Rules.Dec
import GoFV.Proof.Pass.StructLoadMem
import GoFV.Proof.ValRefine
import GoFV.Proof.PureMono

/-!
# Rule lemmas: `dec` rules, `Load` splits (`dec.rules`, issue #17)

`(Load <t> ptr mem) && t.IsString() => (StringMake (Load <typ.BytePtr> ptr mem) (Load <typ.Int>
(OffPtr <typ.IntPtr> [config.PtrSize] ptr) mem))` (`:45`), and the slice (`:63`) and interface
(`:87`) forms: a `Load` of a composite is refined by the `Make` of its components' `Load`s.
The condition fixes the shape (`kindE`: false at every shape but the kind's; at `.other` the
`Load` is `poison`); there it is a `rewriteStructLoad` expansion whose first component is read at
the pointer itself (`loadSplit_ref`, from `StructLoad.structLoad_ref`: a valid read of the
composite's bytes reads each component's bytes at its offset, inside the block's window).
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules
open GoFV.Proof.Pass.StructLoad (Fields fieldVal structLoad_ref)

/-- A `Load` of an aggregate whose first field is at offset 0 is refined by the `Make` of the
`Load` of the first field at the pointer itself and the field `Load`s at `OffPtr`s. -/
theorem loadSplit_ref {t0 : Ty} {fs : List (Nat × Ty)} {n : Nat}
    (hl : GoFV.Opt.RewriteCheck.layoutsOK n ((0, t0) :: fs) = true)
    (ho : ∀ f ∈ (0, t0) :: fs, f.1 < n) (P Mv : Val) {vs : List Val}
    (hvs : Fields (fun v f => ∃ e, v = fieldVal P Mv f.1 (.ptr e) f.2) vs fs) :
    Refines ((loadOp (.agg ((0, t0) :: fs) n) [P, Mv]).retype (.agg ((0, t0) :: fs) n))
      ((Comp.make ((loadOp t0 [P, Mv]).retype t0 :: vs)).retype (.agg ((0, t0) :: fs) n)) := by
  cases P with
  | ptr p =>
    have h := structLoad_ref hl ho (.ptr p) Mv
      (vs := fieldVal (.ptr p) Mv 0 (.ptr none) t0 :: vs) ⟨⟨none, rfl⟩, hvs⟩
    refine h.trans (retype_mono _ (.agg (.cons ?_ (RefinesList.refl vs))))
    unfold fieldVal
    have hq : PtrOps.offPtr (Int64.ofNat 0) [.ptr p] = PtrOps.ptrRes p := by
      show PtrOps.ptrRes (p.add _) = _
      congr 1
      cases p
      simp [Ptr.add]
    rw [hq]
    unfold PtrOps.ptrRes
    split
    · exact Refines.refl _
    · show Refines ((loadOp t0 [Val.poison.retype (.ptr none), Mv]).retype t0) _
      rw [retype_poison]
      exact retype_mono _ (.poison _)
  | _ =>
    show Refines (Val.poison.retype _) _
    rw [retype_poison]
    exact .poison _

/-- `kindDV` of a type value refutes the condition only at `some false`. -/
theorem kindDV_ty (k : KindPred) (t : Ty) : kindDV k (DV.ty t) = (kindE k t).map DV.bool := rfl

/-- Only `poison` has the shape `.other`. -/
theorem eq_poison_of_other {v : Val} (h : v.hasTy .other = true) : v = .poison := by
  cases v <;> simp_all [Val.hasTy]

theorem strShape_eq {t : Ty} (h : strShape t = true) :
    t = .agg [(0, .ptr (some 1)), (8, .int .w64)] 16 := by
  unfold strShape at h; split at h <;> first | rfl | cases h

theorem sliceShape_eq {t : Ty} (h : sliceShape t = true) :
    ∃ e, t = .agg [(0, .ptr e), (8, .int .w64), (16, .int .w64)] 24 := by
  unfold sliceShape at h; split at h <;> first | exact ⟨_, rfl⟩ | cases h

theorem interShape_eq {t : Ty} (h : interShape t = true) :
    t = .agg [(0, .int .w64), (8, .ptr (some 1))] 16 := by
  unfold interShape at h; split at h <;> first | rfl | cases h

/-- `dec.rules:45`: `(Load <t> ptr mem) && t.IsString() => (StringMake (Load <typ.BytePtr> ptr mem) (Load <typ.Int> (OffPtr <typ.IntPtr> [config.PtrSize] ptr) mem))` -/
theorem r_dec_45_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_45 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_45
  have hk : kindE .string (e.ty []) ≠ some false := by
    intro hk; simp [kindDV_ty, hk] at hcond
  rw [← Val.retype_of_hasTy hty]
  rcases kindE_string hk with hs | ho
  · rw [strShape_eq hs]
    exact loadSplit_ref (by decide) (by decide) _ _ ⟨⟨some 8, rfl⟩, trivial⟩
  · rw [ho] at hty ⊢
    rw [Val.retype_of_hasTy hty, eq_poison_of_other hty]
    exact .poison _

/-- `dec.rules:63`: `(Load <t> ptr mem) && t.IsSlice() => (SliceMake (Load <t.Elem().PtrTo()> ptr mem) (Load <typ.Int> (OffPtr <typ.IntPtr> [config.PtrSize] ptr) mem) (Load <typ.Int> (OffPtr <typ.IntPtr> [2*config.PtrSize] ptr) mem))` -/
theorem r_dec_63_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_63 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_63
  have hk : kindE .slice (e.ty []) ≠ some false := by
    intro hk; simp [kindDV_ty, hk] at hcond
  rw [← Val.retype_of_hasTy hty]
  rcases kindE_slice hk with hs | ho
  · obtain ⟨el, he⟩ := sliceShape_eq hs
    rw [he]
    dsimp only [strctField, List.find?]
    exact loadSplit_ref
      (by simp [GoFV.Opt.RewriteCheck.layoutsOK, GoFV.Opt.RewriteCheck.layoutOK, Sem.Ty.size]
          <;> decide)
      (by simp) _ _ ⟨⟨some 8, rfl⟩, ⟨some 8, rfl⟩, trivial⟩
  · rw [ho] at hty ⊢
    rw [Val.retype_of_hasTy hty, eq_poison_of_other hty]
    exact .poison _

/-- `dec.rules:87`: `(Load <t> ptr mem) && t.IsInterface() => (IMake (Load <typ.Uintptr> ptr mem) (Load <typ.BytePtr> (OffPtr <typ.BytePtrPtr> [config.PtrSize] ptr) mem))` -/
theorem r_dec_87_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_87 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_87
  have hk : kindE .inter (e.ty []) ≠ some false := by
    intro hk; simp [kindDV_ty, hk] at hcond
  rw [← Val.retype_of_hasTy hty]
  rcases kindE_inter hk with hs | ho
  · rw [interShape_eq hs]
    exact loadSplit_ref (by decide) (by decide) _ _ ⟨⟨some 8, rfl⟩, trivial⟩
  · rw [ho] at hty ⊢
    rw [Val.retype_of_hasTy hty, eq_poison_of_other hty]
    exact .poison _

/-! ## Extractors of a `Load` (`dec.rules:135`–`:154`)

`(StringPtr x:(Load <t> ptr mem)) && t.IsString() => @x.Block (Load <typ.BytePtr> ptr mem)` and
the other components of strings, slices and interfaces: component `k` of a `Load` of an aggregate
is refined by the `Load` of field `k` at its offset (`selLoad_ref`, from `structLoad_ref`; at
offset 0 at the pointer itself, `selLoad0_ref`). The `@x.Block` placement is the validator's
(`RewriteCheck.blockTopOK`); the obligation is `Rule.Sound` of the result tree. -/

/-- The struct-load fields of `fs`: each field's `Load` at its offset. -/
theorem fields_map (P Mv : Val) : ∀ fs : List (Nat × Ty),
    Fields (fun v f => ∃ e, v = fieldVal P Mv f.1 (.ptr e) f.2)
      (fs.map fun f => fieldVal P Mv f.1 (.ptr none) f.2) fs
  | [] => trivial
  | _ :: fs => ⟨⟨none, rfl⟩, fields_map P Mv fs⟩

/-- **Component `k` of a `Load` of an aggregate** is refined by the `Load` of field `k` at its
offset (`OffPtr`), when the fields lie inside the aggregate at offsets below its size. -/
theorem selLoad_ref {fs : List (Nat × Ty)} {n : Nat} (hl : GoFV.Opt.RewriteCheck.layoutsOK n fs = true)
    (ho : ∀ f ∈ fs, f.1 < n) (P Mv : Val) {k o : Nat} {t : Ty} (hk : fs[k]? = some (o, t))
    (e : Option Nat) :
    Refines (Comp.select k [(loadOp (.agg fs n) [P, Mv]).retype (.agg fs n)])
      (fieldVal P Mv o (.ptr e) t) := by
  have h1 := Comp.select_mono k
    (.cons (structLoad_ref hl ho P Mv (fields_map P Mv fs)) .nil)
  refine h1.trans ?_
  rcases select_retype_make_get (.agg fs n) k (fs.map fun f => fieldVal P Mv f.1 (.ptr none) f.2)
    with h | ⟨f, v, hf, hv, he⟩
  · rw [h]; exact .poison _
  · rw [he]
    simp only [fieldShape?, hk, Option.map_some, Option.some.injEq] at hf
    subst hf
    simp only [List.getElem?_map, hk, Option.map_some, Option.some.injEq] at hv
    subst hv
    unfold fieldVal
    have hpe : ∀ z : Val, z.retype (.ptr none) = z.retype (.ptr e) := by
      intro z
      cases z with
      | int w _ => cases w <;> rfl
      | _ => rfl
    rw [Val.retype_idem, hpe]
    exact Refines.refl _

/-- Component `k` of a `Load` of an aggregate whose field `k` is at offset 0 is refined by the
`Load` of the field at the pointer itself. -/
theorem selLoad0_ref {fs : List (Nat × Ty)} {n : Nat} (hl : GoFV.Opt.RewriteCheck.layoutsOK n fs = true)
    (ho : ∀ f ∈ fs, f.1 < n) (P Mv : Val) {k : Nat} {t : Ty} (hk : fs[k]? = some (0, t)) :
    Refines (Comp.select k [(loadOp (.agg fs n) [P, Mv]).retype (.agg fs n)])
      ((loadOp t [P, Mv]).retype t) := by
  cases P with
  | ptr p =>
    refine (selLoad_ref hl ho (.ptr p) Mv hk none).trans ?_
    unfold fieldVal
    have hq : PtrOps.offPtr (Int64.ofNat 0) [.ptr p] = PtrOps.ptrRes p := by
      show PtrOps.ptrRes (p.add _) = _
      congr 1
      cases p
      simp [Ptr.add]
    rw [hq]
    unfold PtrOps.ptrRes
    split
    · exact Refines.refl _
    · show Refines ((loadOp t [Val.poison.retype (.ptr none), Mv]).retype t) _
      rw [retype_poison]
      exact retype_mono _ (.poison _)
  | _ =>
    show Refines (Comp.select k [Val.poison.retype _]) _
    rw [retype_poison]
    exact .poison _

/-- Only `poison` has the shape `.other`: `retype` there is `poison`. -/
theorem retype_other (v : Val) : v.retype .other = .poison := by
  cases v <;> simp [Val.retype]

/-- A selection of a `Load` at `.other` is `poison`. -/
theorem selLoad_other (k : Nat) (vs : List Val) (r : Val) :
    Refines (Comp.select k [(loadOp .other vs).retype .other]) r := by
  rw [retype_other]; exact .poison _

/-- `dec.rules:135`: `(StringPtr x:(Load <t> ptr mem)) && t.IsString() => @x.Block (Load <typ.BytePtr> ptr mem)` -/
theorem r_dec_135_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_135 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_135
  have hk : kindE .string (e.ty [0]) ≠ some false := by
    intro hk; simp [kindDV_ty, hk] at hcond
  rcases kindE_string hk with hs | ho
  · rw [strShape_eq hs]
    exact selLoad0_ref (by decide) (by decide) _ _ rfl
  · rw [ho]; exact selLoad_other _ _ _

/-- `dec.rules:136`: `(StringLen x:(Load <t> ptr mem)) && t.IsString() => @x.Block (Load <typ.Int> (OffPtr <typ.IntPtr> [config.PtrSize] ptr) mem)` -/
theorem r_dec_136_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_136 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_136
  have hk : kindE .string (e.ty [0]) ≠ some false := by
    intro hk; simp [kindDV_ty, hk] at hcond
  rcases kindE_string hk with hs | ho
  · rw [strShape_eq hs]
    exact selLoad_ref (by decide) (by decide) _ _ rfl (some 8)
  · rw [ho]; exact selLoad_other _ _ _

/-- `dec.rules:144`: `(ITab x:(Load <t> ptr mem)) && t.IsInterface() => @x.Block (Load <typ.Uintptr> ptr mem)` -/
theorem r_dec_144_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_144 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_144
  have hk : kindE .inter (e.ty [0]) ≠ some false := by
    intro hk; simp [kindDV_ty, hk] at hcond
  rcases kindE_inter hk with hs | ho
  · rw [interShape_eq hs]
    exact selLoad0_ref (by decide) (by decide) _ _ rfl
  · rw [ho]; exact selLoad_other _ _ _

/-- `dec.rules:146`: `(IData x:(Load <t> ptr mem)) && t.IsInterface() => @x.Block (Load <typ.BytePtr> (OffPtr <typ.BytePtrPtr> [config.PtrSize] ptr) mem)` -/
theorem r_dec_146_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_146 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_146
  have hk : kindE .inter (e.ty [0]) ≠ some false := by
    intro hk; simp [kindDV_ty, hk] at hcond
  rcases kindE_inter hk with hs | ho
  · rw [interShape_eq hs]
    exact selLoad_ref (by decide) (by decide) _ _ rfl (some 8)
  · rw [ho]; exact selLoad_other _ _ _

/-- `dec.rules:150`: `(SlicePtr x:(Load <t> ptr mem)) && t.IsSlice() => @x.Block (Load <t.Elem().PtrTo()> ptr mem)` -/
theorem r_dec_150_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_150 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_150
  have hk : kindE .slice (e.ty [0]) ≠ some false := by
    intro hk; simp [kindDV_ty, hk] at hcond
  rcases kindE_slice hk with hs | ho
  · obtain ⟨el, he⟩ := sliceShape_eq hs
    rw [he]
    dsimp only [strctField, List.find?]
    exact selLoad0_ref
      (by simp [GoFV.Opt.RewriteCheck.layoutsOK, GoFV.Opt.RewriteCheck.layoutOK, Sem.Ty.size]
          <;> decide)
      (by simp) _ _ rfl
  · rw [ho]; exact selLoad_other _ _ _

/-- `dec.rules:151`: `(SliceLen x:(Load <t> ptr mem)) && t.IsSlice() => @x.Block (Load <typ.Int> (OffPtr <typ.IntPtr> [config.PtrSize] ptr) mem)` -/
theorem r_dec_151_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_151 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_151
  have hk : kindE .slice (e.ty [0]) ≠ some false := by
    intro hk; simp [kindDV_ty, hk] at hcond
  rcases kindE_slice hk with hs | ho
  · obtain ⟨el, he⟩ := sliceShape_eq hs
    rw [he]
    exact selLoad_ref
      (by simp [GoFV.Opt.RewriteCheck.layoutsOK, GoFV.Opt.RewriteCheck.layoutOK, Sem.Ty.size]
          <;> decide)
      (by simp) _ _ rfl (some 8)
  · rw [ho]; exact selLoad_other _ _ _

/-- `dec.rules:154`: `(SliceCap x:(Load <t> ptr mem)) && t.IsSlice() => @x.Block (Load <typ.Int> (OffPtr <typ.IntPtr> [2*config.PtrSize] ptr) mem)` -/
theorem r_dec_154_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_154 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_154
  have hk : kindE .slice (e.ty [0]) ≠ some false := by
    intro hk; simp [kindDV_ty, hk] at hcond
  rcases kindE_slice hk with hs | ho
  · obtain ⟨el, he⟩ := sliceShape_eq hs
    rw [he]
    exact selLoad_ref
      (by simp [GoFV.Opt.RewriteCheck.layoutsOK, GoFV.Opt.RewriteCheck.layoutOK, Sem.Ty.size]
          <;> decide)
      (by simp) _ _ rfl (some 8)
  · rw [ho]; exact selLoad_other _ _ _

end GoFV.Proof.Rules

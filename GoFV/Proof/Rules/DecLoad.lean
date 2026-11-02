import GoFV.Proof.Rules.Dec
import GoFV.Proof.Pass.StructLoadMem
import GoFV.Proof.ValRefine
import GoFV.Proof.Rules.SelLoad

/-!
# Rule lemmas: `dec` rules, `Load` splits (`dec.rules`, issue #17)

`(Load <t> ptr mem) && t.IsString() => (StringMake (Load <typ.BytePtr> ptr mem) (Load <typ.Int>
(OffPtr <typ.IntPtr> [config.PtrSize] ptr) mem))` (`:45`), and the slice (`:63`), interface
(`:87`) and complex (`:16`, `:28`) forms: a `Load` of a composite is refined by the `Make` of its
components' `Load`s. The condition fixes the shape (`kindE`: false at every shape but the kind's;
at `.other` the `Load` is `poison`; a complex rule's `t.Size()` conjunct is false at the other
complex shape, `shapeSize`); there it is a `rewriteStructLoad` expansion whose first component is
read at the pointer itself (`loadSplit_ref`, from `StructLoad.structLoad_ref`: a valid read of
the composite's bytes reads each component's bytes at its offset, inside the block's window).
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules
open GoFV.Proof.Pass.StructLoad (Fields fieldVal structLoad_ref)

/-- A `Load` at a string or slice shape is the load at its aggregate layout, length-checked. -/
theorem loadOp_asAgg (t : Ty) (args : List Val) :
    loadOp t args = Val.checkLen t (loadOp t.asAgg args) := by
  unfold loadOp
  split
  · exact load_asAgg _ _ _
  · exact (Val.checkLen_poison t).symm

/-- Component `k` of a length-checked string or slice: refined by whatever refines component `k`
of the aggregate layout (the check keeps the value or makes it `poison`). -/
theorem select_checkLen_ref {t : Ty} {k : Nat} {L X : Val}
    (h : Refines (Comp.select k [L.retype t.asAgg]) X) :
    Refines (Comp.select k [(Val.checkLen t L).retype t]) X := by
  have h2 : (Val.checkLen t L).retype t = L.retype t.asAgg ∨
      (Val.checkLen t L).retype t = .poison := by
    rcases Val.checkLen_eq_or t L with h1 | h1 <;> rw [h1]
    · rw [retype_asAgg]; exact Val.checkLen_eq_or _ _
    · right; cases t <;> rfl
  rcases h2 with h2 | h2 <;> rw [h2]
  · exact h
  · exact .poison _

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

theorem strShape_eq {t : Ty} (h : strShape t = true) : t = .str := by
  unfold strShape at h; split at h <;> first | rfl | cases h

theorem sliceShape_eq {t : Ty} (h : sliceShape t = true) : ∃ e, t = .slice e := by
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
  · rw [strShape_eq hs, loadOp_asAgg]
    exact retype_checkLen_refines
      (loadSplit_ref (by decide) (by decide) _ _ ⟨⟨some 8, rfl⟩, trivial⟩)
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
    rw [he, loadOp_asAgg]
    dsimp only [strctField, List.find?]
    refine retype_checkLen_refines ?_
    simp only [Ty.asAgg, Ty.sliceAgg]
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

theorem complexShape_eq {t : Ty} (h : complexShape t = true) :
    t = .agg [(0, .int .w32), (4, .int .w32)] 8 ∨ t = .agg [(0, .int .w64), (8, .int .w64)] 16 := by
  unfold complexShape at h; split at h <;> first | exact .inl rfl | exact .inr rfl | cases h

/-- `dec.rules:16`: `(Load <t> ptr mem) && t.IsComplex() && t.Size() == 8 => (ComplexMake (Load <typ.Float32> ptr mem) (Load <typ.Float32> (OffPtr <typ.Float32Ptr> [4] ptr) mem) )` -/
theorem r_dec_16_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_16 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_16
  have hk : kindE .complex (e.ty []) ≠ some false := by
    intro hk; simp [kindDV_ty, hk, binE_land_bool] at hcond
  rw [← Val.retype_of_hasTy hty]
  rcases kindE_complex hk with hs | ho
  · rcases complexShape_eq hs with h8 | h16
    · rw [h8]
      exact loadSplit_ref (by decide) (by decide) _ _ ⟨⟨some 4, rfl⟩, trivial⟩
    · obtain ⟨b, hb⟩ := hbt ((Expr.var 0).method "IsComplex" [] GoTy.bool) rfl
      simp [kindDV_ty, h16, kindE, complexShape, shapeSize, hb, binE_land_bool] at hcond
  · rw [ho] at hty ⊢
    rw [Val.retype_of_hasTy hty, eq_poison_of_other hty]
    exact .poison _

/-- `dec.rules:28`: `(Load <t> ptr mem) && t.IsComplex() && t.Size() == 16 => (ComplexMake (Load <typ.Float64> ptr mem) (Load <typ.Float64> (OffPtr <typ.Float64Ptr> [8] ptr) mem) )` -/
theorem r_dec_28_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_28 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_28
  have hk : kindE .complex (e.ty []) ≠ some false := by
    intro hk; simp [kindDV_ty, hk, binE_land_bool] at hcond
  rw [← Val.retype_of_hasTy hty]
  rcases kindE_complex hk with hs | ho
  · rcases complexShape_eq hs with h8 | h16
    · obtain ⟨b, hb⟩ := hbt ((Expr.var 0).method "IsComplex" [] GoTy.bool) rfl
      simp [kindDV_ty, h8, kindE, complexShape, shapeSize, hb, binE_land_bool] at hcond
    · rw [h16]
      exact loadSplit_ref (by decide) (by decide) _ _ ⟨⟨some 8, rfl⟩, trivial⟩
  · rw [ho] at hty ⊢
    rw [Val.retype_of_hasTy hty, eq_poison_of_other hty]
    exact .poison _

/-! ## Extractors of a `Load` (`dec.rules:135`–`:154`)

`(StringPtr x:(Load <t> ptr mem)) && t.IsString() => @x.Block (Load <typ.BytePtr> ptr mem)` and
the other components of strings, slices and interfaces: component `k` of a `Load` of an aggregate
is refined by the `Load` of field `k` at its offset (`selLoad_ref`, from `structLoad_ref`; at
offset 0 at the pointer itself, `selLoad0_ref`; `SelLoad.lean`). The `@x.Block` placement is the
validator's (`RewriteCheck.blockTopOK`); the obligation is `Rule.Sound` of the result tree. -/

/-- `dec.rules:135`: `(StringPtr x:(Load <t> ptr mem)) && t.IsString() => @x.Block (Load <typ.BytePtr> ptr mem)` -/
theorem r_dec_135_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_135 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_135
  have hk : kindE .string (e.ty [0]) ≠ some false := by
    intro hk; simp [kindDV_ty, hk] at hcond
  rcases kindE_string hk with hs | ho
  · rw [strShape_eq hs, loadOp_asAgg .str]
    refine select_checkLen_ref ?_
    simp only [Ty.asAgg, Ty.strAgg]
    exact selLoad0_ref (by decide) (by decide) _ _ rfl
  · rw [ho]; exact selLoad_other _ _ _

/-- `dec.rules:136`: `(StringLen x:(Load <t> ptr mem)) && t.IsString() => @x.Block (Load <typ.Int> (OffPtr <typ.IntPtr> [config.PtrSize] ptr) mem)` -/
theorem r_dec_136_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_136 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_136
  have hk : kindE .string (e.ty [0]) ≠ some false := by
    intro hk; simp [kindDV_ty, hk] at hcond
  rcases kindE_string hk with hs | ho
  · rw [strShape_eq hs, loadOp_asAgg .str]
    refine select_checkLen_ref ?_
    simp only [Ty.asAgg, Ty.strAgg]
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

/-- `dec.rules:158`: `(ComplexReal x:(Load <t> ptr mem)) && t.IsComplex() && t.Size() == 8 => @x.Block (Load <typ.Float32> ptr mem)` -/
theorem r_dec_158_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_158 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_158
  have hk : kindE .complex (e.ty [0]) ≠ some false := by
    intro hk; simp [kindDV_ty, hk, binE_land_bool] at hcond
  rcases kindE_complex hk with hs | ho
  · rcases complexShape_eq hs with h8 | h16
    · rw [h8]; exact selLoad0_ref (by decide) (by decide) _ _ rfl
    · obtain ⟨b, hb⟩ := hbt ((Expr.var 0).method "IsComplex" [] GoTy.bool) rfl
      simp [kindDV_ty, h16, kindE, complexShape, shapeSize, hb, binE_land_bool] at hcond
  · rw [ho]; exact selLoad_other _ _ _

/-- `dec.rules:159`: `(ComplexImag x:(Load <t> ptr mem)) && t.IsComplex() && t.Size() == 8 => @x.Block (Load <typ.Float32> (OffPtr <typ.Float32Ptr> [4] ptr) mem)` -/
theorem r_dec_159_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_159 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_159
  have hk : kindE .complex (e.ty [0]) ≠ some false := by
    intro hk; simp [kindDV_ty, hk, binE_land_bool] at hcond
  rcases kindE_complex hk with hs | ho
  · rcases complexShape_eq hs with h8 | h16
    · rw [h8]; exact selLoad_ref (by decide) (by decide) _ _ rfl (some 4)
    · obtain ⟨b, hb⟩ := hbt ((Expr.var 0).method "IsComplex" [] GoTy.bool) rfl
      simp [kindDV_ty, h16, kindE, complexShape, shapeSize, hb, binE_land_bool] at hcond
  · rw [ho]; exact selLoad_other _ _ _

/-- `dec.rules:163`: `(ComplexReal x:(Load <t> ptr mem)) && t.IsComplex() && t.Size() == 16 => @x.Block (Load <typ.Float64> ptr mem)` -/
theorem r_dec_163_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_163 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_163
  have hk : kindE .complex (e.ty [0]) ≠ some false := by
    intro hk; simp [kindDV_ty, hk, binE_land_bool] at hcond
  rcases kindE_complex hk with hs | ho
  · rcases complexShape_eq hs with h8 | h16
    · obtain ⟨b, hb⟩ := hbt ((Expr.var 0).method "IsComplex" [] GoTy.bool) rfl
      simp [kindDV_ty, h8, kindE, complexShape, shapeSize, hb, binE_land_bool] at hcond
    · rw [h16]; exact selLoad0_ref (by decide) (by decide) _ _ rfl
  · rw [ho]; exact selLoad_other _ _ _

/-- `dec.rules:164`: `(ComplexImag x:(Load <t> ptr mem)) && t.IsComplex() && t.Size() == 16 => @x.Block (Load <typ.Float64> (OffPtr <typ.Float64Ptr> [8] ptr) mem)` -/
theorem r_dec_164_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_164 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_164
  have hk : kindE .complex (e.ty [0]) ≠ some false := by
    intro hk; simp [kindDV_ty, hk, binE_land_bool] at hcond
  rcases kindE_complex hk with hs | ho
  · rcases complexShape_eq hs with h8 | h16
    · obtain ⟨b, hb⟩ := hbt ((Expr.var 0).method "IsComplex" [] GoTy.bool) rfl
      simp [kindDV_ty, h8, kindE, complexShape, shapeSize, hb, binE_land_bool] at hcond
    · rw [h16]; exact selLoad_ref (by decide) (by decide) _ _ rfl (some 8)
  · rw [ho]; exact selLoad_other _ _ _

/-- `dec.rules:150`: `(SlicePtr x:(Load <t> ptr mem)) && t.IsSlice() => @x.Block (Load <t.Elem().PtrTo()> ptr mem)` -/
theorem r_dec_150_sound : Rule.Sound GoFV.Rules.Generated.Dec.r_dec_150 := by
  dec_unfold GoFV.Rules.Generated.Dec.r_dec_150
  have hk : kindE .slice (e.ty [0]) ≠ some false := by
    intro hk; simp [kindDV_ty, hk] at hcond
  rcases kindE_slice hk with hs | ho
  · obtain ⟨el, he⟩ := sliceShape_eq hs
    rw [he, loadOp_asAgg (.slice el)]
    refine select_checkLen_ref ?_
    simp only [Ty.asAgg, Ty.sliceAgg]
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
    rw [he, loadOp_asAgg (.slice el)]
    refine select_checkLen_ref ?_
    simp only [Ty.asAgg, Ty.sliceAgg]
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
    rw [he, loadOp_asAgg (.slice el)]
    refine select_checkLen_ref ?_
    simp only [Ty.asAgg, Ty.sliceAgg]
    exact selLoad_ref
      (by simp [GoFV.Opt.RewriteCheck.layoutsOK, GoFV.Opt.RewriteCheck.layoutOK, Sem.Ty.size]
          <;> decide)
      (by simp) _ _ rfl (some 8)
  · rw [ho]; exact selLoad_other _ _ _

end GoFV.Proof.Rules

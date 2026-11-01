import GoFV.Proof.Rules.Dec
import GoFV.Proof.Pass.StructLoadMem
import GoFV.Proof.ValRefine

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

end GoFV.Proof.Rules

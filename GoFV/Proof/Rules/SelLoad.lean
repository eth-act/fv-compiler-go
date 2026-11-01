import GoFV.Proof.Pass.StructLoadMem
import GoFV.Proof.Rules.DecShape
import GoFV.Proof.PureMono

/-!
# Selections of a `Load` (issue #17)

Component `k` of a `Load` of an aggregate is refined by the `Load` of field `k` at its offset
(`selLoad_ref`, from `StructLoad.structLoad_ref`: a valid read of the aggregate's bytes reads
the field's bytes at its offset, inside the block's window); at offset 0 by the `Load` at the
pointer itself (`selLoad0_ref`). Used by the extractor rule lemmas (`DecLoad.lean`,
`dec.rules:135`–`:154`) and the per-instance selections of a `Load`
(`GoFV/Proof/Pass/RewriteLoadSel.lean`, `dec.rules:132`, `:141`).
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem
open GoFV.Proof.Pass.StructLoad (Fields fieldVal structLoad_ref)

private theorem retype_poison_sl (t : Ty) : Val.poison.retype t = .poison := by cases t <;> rfl

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
    simp only [fieldShape?, Ty.asAgg, hk, Option.map_some, Option.some.injEq] at hf
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
      rw [retype_poison_sl]
      exact retype_mono _ (.poison _)
  | _ =>
    show Refines (Comp.select k [Val.poison.retype _]) _
    rw [retype_poison_sl]
    exact .poison _

/-- Only `poison` has the shape `.other`: `retype` there is `poison`. -/
theorem retype_other (v : Val) : v.retype .other = .poison := by
  cases v <;> simp [Val.retype]

/-- A selection of a `Load` at `.other` is `poison`. -/
theorem selLoad_other (k : Nat) (vs : List Val) (r : Val) :
    Refines (Comp.select k [(loadOp .other vs).retype .other]) r := by
  rw [retype_other]; exact .poison _

end GoFV.Proof.Rules

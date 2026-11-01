import GoFV.Proof.FinishMono
import GoFV.Proof.Retype

/-!
# Register pieces of ABI values: shapes, Make-trees and selector chains (#28)

The definitions behind the ABI round trip of `expand calls`: well-formed register shapes
(`wf`: fields in order, disjoint, within the size; no blobs, tuples, memories or `other`
inside), the value a Make-tree builds from register pieces (`build`) and the pieces selector
chains compute (`leafVals`). Here the facts that need no bytes: lengths and shapes of the
pieces (`leafVals_length`, `leafVals_hasTy`), monotonicity (`leafVals_mono`, `build_mono`),
`build` undoes `leafVals` (`build_leafVals`) and `decode` (`build_decode`), and the order of a
well-formed shape's leaves (`leaves_wfFields`). `GoFV.Proof.ABI` relates them to `ofPieces`,
`toPieces`, `encode` and `decode`.
-/

namespace GoFV.Proof.ABI

open GoFV.SSA.Sem

/-- `R` holds pairwise between the elements of two lists of equal length (core has no
`List.Forall₂`; this one lives in `GoFV.Proof.ABI`). -/
inductive List.Forall₂ {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : List.Forall₂ R [] []
  | cons {a : α} {b : β} {l : List α} {l' : List β} : R a b → List.Forall₂ R l l' →
      List.Forall₂ R (a :: l) (b :: l')

mutual
/-- Fields in order, disjoint, within the size; no blobs, tuples, memory or `other` inside. -/
def wf : Ty → Bool
  | .agg fs n => wfFields fs n 0
  | .int _ | .bool | .ptr _ | .opaque _ | .empty => true
  | _ => false
def wfFields : List (Nat × Ty) → Nat → Nat → Bool
  | [], n, start => start ≤ n
  | (o, t) :: fs, n, start => start ≤ o && wf t && wfFields fs n (o + t.size)
end

mutual
/-- A value of shape `t` built from its register pieces (in `leaves t` order), as the Make-trees
of `expand calls` build it. -/
def build : Ty → List Val → Val
  | .agg fs _, ps => .agg (buildFields fs ps)
  | .empty, _ => .empty
  | _, ps => ps.headD .poison
def buildFields : List (Nat × Ty) → List Val → List Val
  | [], _ => []
  | (_, t) :: fs, ps =>
    build t (ps.take (leaves t).length) :: buildFields fs (ps.drop (leaves t).length)
end

mutual
/-- The register pieces of `v` at shape `t` as selector chains (`StructSelect`, `SlicePtr`, …,
each retyped at its field's shape) compute them. -/
def leafVals : Ty → Val → List Val
  | .agg fs _, .agg vs => leafValsFields fs vs
  | .agg fs n, _ => (leaves (.agg fs n)).map fun _ => .poison
  | .empty, _ => []
  | t, v => [v.retype t]
def leafValsFields : List (Nat × Ty) → List Val → List Val
  | [], _ => []
  | (_, t) :: fs, vs => leafVals t ((vs.headD .poison).retype t) ++ leafValsFields fs vs.tail
end

/-- The shapes of register pieces: a leaf of a well-formed shape is one of these. -/
def atom : Ty → Bool
  | .int _ | .bool | .ptr _ | .opaque _ => true
  | _ => false

/-! ## Equations -/

theorem leaves_agg (fs : List (Nat × Ty)) (n : Nat) :
    leaves (.agg fs n) = leaves.leavesFields fs := (rfl)

theorem leavesFields_nil : leaves.leavesFields [] = [] := (rfl)

theorem leavesFields_cons (o : Nat) (t : Ty) (fs : List (Nat × Ty)) :
    leaves.leavesFields ((o, t) :: fs) =
      (leaves t).map (fun x => (o + x.1, x.2)) ++ leaves.leavesFields fs := (rfl)

theorem leaves_atom {t : Ty} (h : atom t = true) : leaves t = [(0, t)] := by
  cases t <;> first | rfl | cases h

theorem build_atom {t : Ty} (h : atom t = true) (ps : List Val) : build t ps = ps.headD .poison := by
  cases t <;> first | rfl | cases h

theorem leafVals_atom {t : Ty} (h : atom t = true) (v : Val) : leafVals t v = [v.retype t] := by
  cases t <;> first | rfl | cases h

theorem leafVals_agg_of_ne {fs : List (Nat × Ty)} {n : Nat} {v : Val} (h : ∀ vs, v ≠ .agg vs) :
    leafVals (.agg fs n) v = (leaves (.agg fs n)).map fun _ => .poison := by
  cases v <;> first | rfl | exact absurd rfl (h _)

theorem leafValsFields_cons (o : Nat) (t : Ty) (fs : List (Nat × Ty)) (v : Val) (vs : List Val) :
    leafValsFields ((o, t) :: fs) (v :: vs) = leafVals t (v.retype t) ++ leafValsFields fs vs :=
  (rfl)

theorem wf_atom {t : Ty} (h : atom t = true) : wf t = true := by
  cases t <;> first | rfl | cases h

/-! ## `List.Forall₂` -/

theorem List.Forall₂.length_eq {α β : Type} {R : α → β → Prop} :
    {l : List α} → {l' : List β} → List.Forall₂ R l l' → l.length = l'.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => congrArg (· + 1) h.length_eq

theorem List.Forall₂.append {α β : Type} {R : α → β → Prop} :
    {l₁ l₂ : List α} → {l₁' l₂' : List β} → List.Forall₂ R l₁ l₁' → List.Forall₂ R l₂ l₂' →
      List.Forall₂ R (l₁ ++ l₂) (l₁' ++ l₂')
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons r h, h' => .cons r (h.append h')

theorem List.Forall₂.map_right {α β : Type} {R : α → β → Prop} (f : β → β)
    (hf : ∀ a b, R a b → R a (f b)) :
    {l : List α} → {l' : List β} → List.Forall₂ R l l' → List.Forall₂ R l (l'.map f)
  | _, _, .nil => .nil
  | _, _, .cons r h => .cons (hf _ _ r) (h.map_right f hf)

/-! ## Well-formed field lists -/

theorem wfFields_le : {fs : List (Nat × Ty)} → {n s : Nat} → wfFields fs n s = true → s ≤ n
  | [], _, _, h => by simpa [wfFields] using h
  | (o, t) :: fs, _, _, h => by
    simp only [wfFields, Bool.and_eq_true, decide_eq_true_eq] at h
    have := wfFields_le h.2
    omega

theorem wfFields_of_le : {fs : List (Nat × Ty)} → {n s s' : Nat} → s ≤ s' →
    wfFields fs n s' = true → wfFields fs n s = true
  | [], _, _, _, hs, h => by simp only [wfFields, decide_eq_true_eq] at h ⊢; omega
  | (o, t) :: fs, _, _, _, hs, h => by
    simp only [wfFields, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨⟨by omega, h.1.2⟩, h.2⟩

theorem wfFields_mem : {fs : List (Nat × Ty)} → {n s : Nat} → wfFields fs n s = true →
    ∀ x ∈ fs, s ≤ x.1 ∧ x.1 + x.2.size ≤ n ∧ wf x.2 = true
  | [], _, _, _, _, hx => absurd hx List.not_mem_nil
  | (o, t) :: fs, _, _, h, x, hx => by
    simp only [wfFields, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨h.1.1, wfFields_le h.2, h.1.2⟩
    · have := wfFields_mem h.2 x hx
      exact ⟨by omega, this.2⟩

/-! ## Leaves of a well-formed shape -/

mutual
theorem mem_leaves_atom : (t : Ty) → wf t = true → ∀ x ∈ leaves t, atom x.2 = true
  | .int _, _, x, hx | .bool, _, x, hx | .ptr _, _, x, hx | .opaque _, _, x, hx => by
    rw [leaves_atom rfl, List.mem_singleton] at hx; subst hx; rfl
  | .empty, _, _, hx => absurd hx List.not_mem_nil
  | .agg fs n, h, x, hx => mem_leavesFields_atom fs n 0 h x hx
  | .blob _, h, _, _ | .mem, h, _, _ | .tuple _, h, _, _ | .other, h, _, _ => nomatch h
theorem mem_leavesFields_atom : (fs : List (Nat × Ty)) → (n s : Nat) → wfFields fs n s = true →
    ∀ x ∈ leaves.leavesFields fs, atom x.2 = true
  | [], _, _, _, _, hx => absurd hx List.not_mem_nil
  | (o, t) :: fs, n, s, h, x, hx => by
    simp only [wfFields, Bool.and_eq_true] at h
    rw [leavesFields_cons, List.mem_append, List.mem_map] at hx
    rcases hx with ⟨y, hy, rfl⟩ | hx
    · exact mem_leaves_atom t h.1.2 y hy
    · exact mem_leavesFields_atom fs n _ h.2 x hx
end

mutual
theorem leaves_ord : (t : Ty) → (o start n : Nat) → (rest : List (Nat × Ty)) → wf t = true →
    start ≤ o → wfFields rest n (o + t.size) = true →
    wfFields ((leaves t).map (fun x => (o + x.1, x.2)) ++ rest) n start = true
  | .int _, o, start, n, rest, h, hs, hr | .bool, o, start, n, rest, h, hs, hr
  | .ptr _, o, start, n, rest, h, hs, hr | .opaque _, o, start, n, rest, h, hs, hr => by
    rw [leaves_atom rfl]
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, wfFields,
      Nat.add_zero, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hs, h⟩, hr⟩
  | .empty, o, start, n, rest, _, hs, hr =>
    (wfFields_of_le hs (by simpa [Ty.size] using hr) : wfFields rest n start = true)
  | .agg fs m, o, start, n, rest, h, hs, hr =>
    leavesFields_ord fs m 0 o start n rest h (by omega) hr
  | .blob _, _, _, _, _, h, _, _ | .mem, _, _, _, _, h, _, _ | .tuple _, _, _, _, _, h, _, _
  | .other, _, _, _, _, h, _, _ => nomatch h
theorem leavesFields_ord : (fs : List (Nat × Ty)) → (m s o start n : Nat) →
    (rest : List (Nat × Ty)) → wfFields fs m s = true → start ≤ o + s →
    wfFields rest n (o + m) = true →
    wfFields ((leaves.leavesFields fs).map (fun x => (o + x.1, x.2)) ++ rest) n start = true
  | [], m, s, o, start, n, rest, h, hs, hr => by
    have : s ≤ m := wfFields_le h
    exact wfFields_of_le (by omega) hr
  | (fo, ft) :: fs, m, s, o, start, n, rest, h, hs, hr => by
    simp only [wfFields, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [leavesFields_cons, List.map_append, List.map_map, List.append_assoc]
    have e : ((fun x : Nat × Ty => (o + x.1, x.2)) ∘ fun x : Nat × Ty => (fo + x.1, x.2)) =
        fun x : Nat × Ty => (o + fo + x.1, x.2) := by
      funext x; simp [Nat.add_assoc]
    rw [e]
    exact leaves_ord ft (o + fo) start n _ h.1.2 (by omega)
      (leavesFields_ord fs m (fo + ft.size) o _ n rest h.2 (by omega) hr)
end

/-- The leaves of a well-formed shape are in order, disjoint and within its size. -/
theorem leaves_wfFields {t : Ty} (h : wf t = true) : wfFields (leaves t) t.size 0 = true := by
  have := leaves_ord t 0 0 t.size [] h (Nat.le_refl _) (by simp [wfFields])
  simpa using this

/-- Each leaf of a well-formed shape is an `atom` within its size. -/
theorem mem_leaves {t : Ty} (h : wf t = true) {x : Nat × Ty} (hx : x ∈ leaves t) :
    x.1 + x.2.size ≤ t.size ∧ atom x.2 = true :=
  ⟨(wfFields_mem (leaves_wfFields h) x hx).2.1, mem_leaves_atom t h x hx⟩

/-! ## Lengths and shapes of the pieces -/

mutual
theorem leafVals_length_aux : (t : Ty) → (v : Val) → wf t = true →
    (leafVals t v).length = (leaves t).length
  | .int _, _, _ | .bool, _, _ | .ptr _, _, _ | .opaque _, _, _ | .empty, _, _ => rfl
  | .agg fs n, v, h => by
    by_cases hv : ∃ vs, v = .agg vs
    · obtain ⟨vs, rfl⟩ := hv
      exact leafValsFields_length fs vs n 0 h
    · rw [leafVals_agg_of_ne fun vs e => hv ⟨vs, e⟩, List.length_map]
  | .blob _, _, h | .mem, _, h | .tuple _, _, h | .other, _, h => nomatch h
theorem leafValsFields_length : (fs : List (Nat × Ty)) → (vs : List Val) → (n s : Nat) →
    wfFields fs n s = true → (leafValsFields fs vs).length = (leaves.leavesFields fs).length
  | [], _, _, _, _ => rfl
  | (o, t) :: fs, vs, n, s, h => by
    simp only [wfFields, Bool.and_eq_true] at h
    show (leafVals t _ ++ leafValsFields fs vs.tail).length = _
    rw [leavesFields_cons, List.length_append, List.length_append, List.length_map,
      leafVals_length_aux t _ h.1.2, leafValsFields_length fs vs.tail n _ h.2]
end

theorem leafVals_length {t : Ty} {v : Val} (h : wf t = true) :
    (leafVals t v).length = (leaves t).length :=
  leafVals_length_aux t v h

theorem forall₂_poison {α : Type} (f : α → Ty) :
    (l : List α) → List.Forall₂ (fun p x => Val.hasTy p (f x) = true) (l.map fun _ => .poison) l
  | [] => .nil
  | _ :: l => .cons rfl (forall₂_poison f l)

mutual
theorem leafVals_hasTy_aux : (t : Ty) → (v : Val) → wf t = true →
    List.Forall₂ (fun p (l : Nat × Ty) => p.hasTy l.2 = true) (leafVals t v) (leaves t)
  | .int _, v, _ | .bool, v, _ | .ptr _, v, _ | .opaque _, v, _ => by
    rw [leafVals_atom rfl, leaves_atom rfl]
    exact .cons (Val.retype_hasTy _ v) .nil
  | .empty, _, _ => .nil
  | .agg fs n, v, h => by
    by_cases hv : ∃ vs, v = .agg vs
    · obtain ⟨vs, rfl⟩ := hv
      exact leafValsFields_hasTy fs vs n 0 h
    · rw [leafVals_agg_of_ne fun vs e => hv ⟨vs, e⟩]
      exact forall₂_poison (fun x : Nat × Ty => x.2) _
  | .blob _, _, h | .mem, _, h | .tuple _, _, h | .other, _, h => nomatch h
theorem leafValsFields_hasTy : (fs : List (Nat × Ty)) → (vs : List Val) → (n s : Nat) →
    wfFields fs n s = true →
    List.Forall₂ (fun p (l : Nat × Ty) => p.hasTy l.2 = true) (leafValsFields fs vs)
      (leaves.leavesFields fs)
  | [], _, _, _, _ => .nil
  | (o, t) :: fs, vs, n, s, h => by
    simp only [wfFields, Bool.and_eq_true] at h
    rw [leavesFields_cons]
    exact List.Forall₂.append
      ((leafVals_hasTy_aux t _ h.1.2).map_right (fun x : Nat × Ty => (o + x.1, x.2))
        fun _ _ r => r)
      (leafValsFields_hasTy fs vs.tail n _ h.2)
end

theorem leafVals_hasTy {t : Ty} {v : Val} (h : wf t = true) :
    List.Forall₂ (fun p (l : Nat × Ty) => p.hasTy l.2 = true) (leafVals t v) (leaves t) :=
  leafVals_hasTy_aux t v h

/-! ## Monotonicity -/

theorem refinesList_poison {α : Type} :
    (l : List α) → (l' : List Val) → l.length = l'.length →
      RefinesList (l.map fun _ => .poison) l'
  | [], [], _ => .nil
  | _ :: l, _ :: l', h => .cons (.poison _) (refinesList_poison l l' (by simpa using h))

theorem refinesList_append : {as bs cs ds : List Val} → RefinesList as bs → RefinesList cs ds →
    RefinesList (as ++ cs) (bs ++ ds)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons r h, h' => .cons r (refinesList_append h h')

theorem refinesList_headD {ps ps' : List Val} (h : RefinesList ps ps') :
    Refines (ps.headD .poison) (ps'.headD .poison) := by
  cases h with
  | nil => exact .poison _
  | cons h _ => exact h

mutual
theorem leafVals_mono_aux : (t : Ty) → wf t = true → {v v' : Val} → Refines v v' →
    RefinesList (leafVals t v) (leafVals t v')
  | .int _, _, _, _, h | .bool, _, _, _, h | .ptr _, _, _, _, h | .opaque _, _, _, _, h => by
    rw [leafVals_atom rfl, leafVals_atom rfl]
    exact .cons (retype_mono _ h) .nil
  | .empty, _, _, _, _ => .nil
  | .agg fs n, hw, v, v', h => by
    by_cases hv : ∃ vs, v = .agg vs
    · obtain ⟨vs, rfl⟩ := hv
      cases h with
      | agg h => exact leafValsFields_mono fs n 0 hw h
    · rw [leafVals_agg_of_ne fun vs e => hv ⟨vs, e⟩]
      exact refinesList_poison _ _ (leafVals_length hw).symm
  | .blob _, h, _, _, _ | .mem, h, _, _, _ | .tuple _, h, _, _, _ | .other, h, _, _, _ => nomatch h
theorem leafValsFields_mono : (fs : List (Nat × Ty)) → (n s : Nat) → wfFields fs n s = true →
    {vs vs' : List Val} → RefinesList vs vs' →
    RefinesList (leafValsFields fs vs) (leafValsFields fs vs')
  | [], _, _, _, _, _, _ => .nil
  | (o, t) :: fs, n, s, hw, vs, vs', h => by
    simp only [wfFields, Bool.and_eq_true] at hw
    show RefinesList (leafVals t _ ++ leafValsFields fs vs.tail)
      (leafVals t _ ++ leafValsFields fs vs'.tail)
    refine refinesList_append (leafVals_mono_aux t hw.1.2 (retype_mono t (refinesList_headD h))) ?_
    cases h with
    | nil => exact RefinesList.refl _
    | cons _ h => exact leafValsFields_mono fs n _ hw.2 h
end

theorem leafVals_mono {t : Ty} {v v' : Val} (hw : wf t = true) (h : Refines v v') :
    RefinesList (leafVals t v) (leafVals t v') :=
  leafVals_mono_aux t hw h

mutual
theorem build_mono_aux : (t : Ty) → {ps ps' : List Val} → RefinesList ps ps' →
    Refines (build t ps) (build t ps')
  | .agg fs _, _, _, h => .agg (buildFields_mono fs h)
  | .empty, _, _, _ => .empty
  | .int _, _, _, h | .bool, _, _, h | .ptr _, _, _, h | .opaque _, _, _, h | .mem, _, _, h
  | .tuple _, _, _, h | .other, _, _, h | .blob _, _, _, h => refinesList_headD h
theorem buildFields_mono : (fs : List (Nat × Ty)) → {ps ps' : List Val} → RefinesList ps ps' →
    RefinesList (buildFields fs ps) (buildFields fs ps')
  | [], _, _, _ => .nil
  | (_, t) :: fs, _, _, h =>
    .cons (build_mono_aux t (h.take _)) (buildFields_mono fs (h.drop _))
end

theorem build_mono {t : Ty} {ps ps' : List Val} (h : RefinesList ps ps') :
    Refines (build t ps) (build t ps') :=
  build_mono_aux t h

/-! ## `build` undoes `leafVals` -/

mutual
theorem build_leafVals_aux : (t : Ty) → (v : Val) → wf t = true → v.hasTy t = true →
    Refines v (build t (leafVals t v))
  | .int _, v, _, hv | .bool, v, _, hv | .ptr _, v, _, hv | .opaque _, v, _, hv => by
    rw [leafVals_atom rfl, build_atom rfl, List.headD_cons, Val.retype_of_hasTy hv]
    exact Refines.refl v
  | .empty, v, _, hv => by
    cases v <;> first | exact .poison _ | exact .empty | cases hv
  | .agg fs n, v, hw, hv => by
    cases v with
    | poison => exact .poison _
    | agg vs => exact .agg (buildFields_leafValsFields fs vs n 0 hw hv)
    | _ => cases hv
  | .blob _, _, h, _ | .mem, _, h, _ | .tuple _, _, h, _ | .other, _, h, _ => nomatch h
theorem buildFields_leafValsFields : (fs : List (Nat × Ty)) → (vs : List Val) → (n s : Nat) →
    wfFields fs n s = true → Val.hasTyList vs (fs.map (·.2)) = true →
    RefinesList vs (buildFields fs (leafValsFields fs vs))
  | [], [], _, _, _, _ => .nil
  | (o, t) :: fs, v :: vs, n, s, hw, hv => by
    simp only [wfFields, Bool.and_eq_true] at hw
    simp only [List.map_cons, Val.hasTyList, Bool.and_eq_true] at hv
    rw [leafValsFields_cons, Val.retype_of_hasTy hv.1]
    show RefinesList (v :: vs) (build t _ :: buildFields fs _)
    rw [List.take_left' (leafVals_length hw.1.2), List.drop_left' (leafVals_length hw.1.2)]
    exact .cons (build_leafVals_aux t v hw.1.2 hv.1)
      (buildFields_leafValsFields fs vs n _ hw.2 hv.2)
  | [], _ :: _, _, _, _, hv | _ :: _, [], _, _, _, hv => nomatch hv
end

theorem build_leafVals {t : Ty} {v : Val} (hw : wf t = true) (hv : v.hasTy t = true) :
    Refines v (build t (leafVals t v)) :=
  build_leafVals_aux t v hw hv

/-! ## `build` undoes `decode` -/

mutual
theorem build_decode_aux : (t : Ty) → (buf : Array Byte) → (b : Nat) → wf t = true →
    build t ((leaves t).map fun x => decode buf (b + x.1) x.2) = decode buf b t
  | .int _, buf, b, _ | .bool, buf, b, _ | .ptr _, buf, b, _ | .opaque _, buf, b, _ => by
    rw [leaves_atom rfl, build_atom rfl]; rfl
  | .empty, _, _, _ => rfl
  | .agg fs n, buf, b, h => by
    rw [leaves_agg, build, decode, buildFields_decode fs buf b n 0 h]
  | .blob _, _, _, h | .mem, _, _, h | .tuple _, _, _, h | .other, _, _, h => nomatch h
theorem buildFields_decode : (fs : List (Nat × Ty)) → (buf : Array Byte) → (b n s : Nat) →
    wfFields fs n s = true →
    buildFields fs ((leaves.leavesFields fs).map fun x => decode buf (b + x.1) x.2) =
      decodeFields buf b fs
  | [], _, _, _, _, _ => rfl
  | (o, t) :: fs, buf, b, n, s, h => by
    simp only [wfFields, Bool.and_eq_true] at h
    rw [leavesFields_cons, List.map_append, List.map_map]
    have e : ((fun x : Nat × Ty => decode buf (b + x.1) x.2) ∘ fun x : Nat × Ty => (o + x.1, x.2)) =
        fun x : Nat × Ty => decode buf (b + o + x.1) x.2 := by
      funext x; simp [Nat.add_assoc]
    rw [e]
    show build t _ :: buildFields fs _ = decode buf (b + o) t :: decodeFields buf b fs
    have hl : ((leaves t).map fun x => decode buf (b + o + x.1) x.2).length = (leaves t).length :=
      List.length_map ..
    rw [List.take_left' hl, List.drop_left' hl, build_decode_aux t buf (b + o) h.1.2,
      buildFields_decode fs buf b n _ h.2]
end

theorem build_decode {t : Ty} {buf : Array Byte} {b : Nat} (h : wf t = true) :
    build t ((leaves t).map fun (o, lt) => decode buf (b + o) lt) = decode buf b t :=
  build_decode_aux t buf b h

end GoFV.Proof.ABI

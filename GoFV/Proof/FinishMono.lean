import GoFV.SSA.Sem.Run
import GoFV.Proof.ValRefine

variable [GoFV.SSA.Sem.Addrs]

/-!
# `goResults`, `Mem.freeFrame` and `Mem.dropFrames` are monotone in refinement

`Res.Rel R`: results related by `R`, panics alike with refined memories, a stuck source
related to anything. `goResults_mono`: Go-typed results of poison-free refined `MakeResult`
components in refined memories are refined (`finish_refines` in `Proof/Refine`). A poison-free
value is refined only by poison-free values of the same shapes (`Refines.noPoison`).
-/

namespace GoFV.SSA.Sem

open GoFV.SSA

/-! ## Results -/

/-- Results related by `R`; the same panic with refined memories; a stuck source is related to
anything. -/
inductive Res.Rel {α β : Type} (R : α → β → Prop) : Res α → Res β → Prop where
  | ok {a : α} {b : β} : R a b → Res.Rel R (.ok a) (.ok b)
  | panic (e : Panic) {m m' : Mem} : Mem.Refines m m' → Res.Rel R (.panic e m) (.panic e m')
  | stuck (msg : String) (r : Res β) : Res.Rel R (.stuck msg) r

theorem Res.Rel.bind {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop} {x : Res α}
    {x' : Res β} {f : α → Res γ} {g : β → Res δ} (h : Res.Rel R x x')
    (hf : ∀ a b, R a b → Res.Rel S (f a) (g b)) : Res.Rel S (x >>= f) (x' >>= g) := by
  cases h with
  | ok h => exact hf _ _ h
  | panic e hm => exact .panic e hm
  | stuck msg r => exact .stuck msg _

theorem Res.Rel.ofOption {α : Type} (msg msg' : String) (o : Option α) :
    Res.Rel (· = ·) (Res.ofOption msg o) (Res.ofOption msg' o) := by
  cases o
  · exact .stuck _ _
  · exact .ok rfl

/-! ## Poison-free values -/

theorem Val.any_hasPoison (l : List Val) : l.any Val.hasPoison = Val.anyPoison l := by
  induction l with
  | nil => rfl
  | cons v l ih => simp only [List.any_cons, Val.anyPoison, ih]

private theorem np_cases {a b : Val} (h : Refines a b) (hp : a.hasPoison = false) :
    a.isPtrWord = b.isPtrWord ∧ (∀ x : BitVec 64, a = .int .w64 x ↔ b = .int .w64 x) := by
  cases h <;> simp_all [Val.hasPoison, Val.isPtrWord]

/-- Poison-free refined components have the same string and slice shapes. -/
private theorem np_lens {as bs : List Val} (hl : RefinesList as bs) (h : Val.anyPoison as = false) :
    (∀ t, t = .str ∨ (∃ e, t = .slice e) → Val.hasTy (.agg as) t = Val.hasTy (.agg bs) t) := by
  rintro t (rfl | ⟨e, rfl⟩) <;> rw [Bool.eq_iff_iff]
  all_goals first | rw [Val.hasTy_agg_str, Val.hasTy_agg_str] | rw [Val.hasTy_agg_slice, Val.hasTy_agg_slice]
  all_goals
    rcases hl with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | ⟨h4, t⟩⟩⟩⟩ <;>
      simp only [Val.anyPoison, Bool.or_eq_false_iff] at h <;> simp
  case inl.cons.cons.nil =>
    have c1 := np_cases h1 h.1
    have c2 := np_cases h2 h.2.1
    simp only [c2.2]
    constructor <;> rintro ⟨p, l, ⟨rfl, hb⟩, hp, hl⟩
    · exact ⟨_, l, ⟨rfl, hb⟩, by rw [← c1.1]; exact hp, hl⟩
    · exact ⟨_, l, ⟨rfl, hb⟩, by rw [c1.1]; exact hp, hl⟩
  case inr.cons.cons.cons.nil =>
    have c1 := np_cases h1 h.1
    have c2 := np_cases h2 h.2.1
    have c3 := np_cases h3 h.2.2.1
    simp only [c2.2, c3.2]
    constructor <;> rintro ⟨p, l, c, ⟨rfl, hb⟩, hp, hl⟩
    · exact ⟨_, l, c, ⟨rfl, hb⟩, by rw [← c1.1]; exact hp, hl⟩
    · exact ⟨_, l, c, ⟨rfl, hb⟩, by rw [c1.1]; exact hp, hl⟩

mutual
/-- A poison-free value is refined only by poison-free values of the same shapes. -/
theorem Refines.noPoison : {a b : Val} → Refines a b → a.hasPoison = false →
    b.hasPoison = false ∧ ∀ t, a.hasTy t = b.hasTy t
  | _, _, .poison _, h => by simp [Val.hasPoison] at h
  | _, _, .int _ _, h => ⟨h, fun _ => rfl⟩
  | _, _, .bool _, h => ⟨h, fun _ => rfl⟩
  | _, _, .mem _, _ => ⟨rfl, fun t => by cases t <;> rfl⟩
  | _, _, .ptr _, h => ⟨h, fun _ => rfl⟩
  | _, _, .empty, h => ⟨h, fun _ => rfl⟩
  | _, _, .blob hb, h => by
    have he := BytesRefine.eq hb fun x hx hx' => by
      subst hx'; simp [Val.hasPoison] at h; exact h hx
    subst he; exact ⟨h, fun _ => rfl⟩
  | _, _, .tuple hl, h => by
    have := RefinesList.noPoison hl (by simpa [Val.hasPoison] using h)
    exact ⟨by simpa [Val.hasPoison] using this.1,
      fun t => by cases t <;> simp [Val.hasTy, this.2.2]⟩
  | _, _, .agg hl, h => by
    have := RefinesList.noPoison hl (by simpa [Val.hasPoison] using h)
    exact ⟨by simpa [Val.hasPoison] using this.1,
      fun t => by
        cases t
        case str => exact np_lens hl (by simpa [Val.hasPoison] using h) _ (.inl rfl)
        case slice e => exact np_lens hl (by simpa [Val.hasPoison] using h) _ (.inr ⟨e, rfl⟩)
        all_goals simp [Val.hasTy, this.2.1]⟩
theorem RefinesList.noPoison : {as bs : List Val} → RefinesList as bs → Val.anyPoison as = false →
    Val.anyPoison bs = false ∧ (∀ ts, Val.hasTyList as ts = Val.hasTyList bs ts) ∧
      ∀ ts, Val.hasTyPre as ts = Val.hasTyPre bs ts
  | _, _, .nil, _ => ⟨rfl, fun _ => rfl, fun _ => rfl⟩
  | _, _, .cons h t, hp => by
    simp only [Val.anyPoison, Bool.or_eq_false_iff] at hp
    have h1 := Refines.noPoison h hp.1
    have h2 := RefinesList.noPoison t hp.2
    refine ⟨by simp [Val.anyPoison, h1.1, h2.1], fun ts => ?_, fun ts => ?_⟩
    · cases ts <;> simp [Val.hasTyList, h1.2, h2.2.1]
    · cases ts <;> simp [Val.hasTyPre, h1.2, h2.2.2]
end

theorem RefinesList.length_eq : {as bs : List Val} → RefinesList as bs → as.length = bs.length
  | _, _, .nil => rfl
  | _, _, .cons _ t => by simp [RefinesList.length_eq t]

theorem RefinesList.take : ∀ (n : Nat) {as bs : List Val}, RefinesList as bs →
    RefinesList (as.take n) (bs.take n)
  | 0, _, _, _ => .nil
  | _ + 1, _, _, .nil => .nil
  | n + 1, _, _, .cons h t => .cons h (RefinesList.take n t)

theorem RefinesList.drop : ∀ (n : Nat) {as bs : List Val}, RefinesList as bs →
    RefinesList (as.drop n) (bs.drop n)
  | 0, _, _, h => h
  | _ + 1, _, _, .nil => .nil
  | n + 1, _, _, .cons _ t => RefinesList.drop n t

/-! ## Memories -/

theorem Mem.Refines.read_none {m m' : Mem} (h : Mem.Refines m m') {p : Ptr} {n : Nat}
    (hr : m.read p n = none) : m'.read p n = none := by
  unfold Mem.read at hr ⊢
  by_cases hn : (n == 0) = true
  · simp [hn] at hr
  · simp only [hn, Bool.false_eq_true, ite_false] at hr ⊢
    rcases h.find? p.blk with ⟨h1, h2⟩ | ⟨a, a', h1, h2, ha⟩
    · rw [h2]; rfl
    · rw [h1] at hr; rw [h2]
      dsimp only [bind, Option.bind] at hr ⊢
      rw [← ha.size_eq]
      split at hr
      · cases hr
      · next hle => simp [hle]

theorem Mem.Refines.read_getD {m m' : Mem} (h : Mem.Refines m m') (p : Ptr) (n : Nat)
    (d : Array Byte) : BytesRefineA ((m.read p n).getD d) ((m'.read p n).getD d) := by
  cases hr : m.read p n with
  | none => rw [h.read_none hr]; exact BytesRefineA.refl _
  | some bs =>
    obtain ⟨bs', hr', hb⟩ := h.read hr
    rw [hr']; exact hb

theorem AllocsRefine.filter_fst (q : Blk × Alloc → Bool) (hq : ∀ b a a', q (b, a) = q (b, a')) :
    {l l' : List (Blk × Alloc)} → AllocsRefine l l' → AllocsRefine (l.filter q) (l'.filter q)
  | _, _, .nil => .nil
  | _, _, .cons b (a := a) (a' := a') h t => by
    rw [List.filter_cons, List.filter_cons, ← hq b a a']
    split
    · exact .cons b h (AllocsRefine.filter_fst q hq t)
    · exact AllocsRefine.filter_fst q hq t

theorem Mem.Refines.freeFrame {m m' : Mem} (h : Mem.Refines m m') (act : Nat) :
    Mem.Refines (m.freeFrame act) (m'.freeFrame act) := by
  rcases m with ⟨⟨l⟩, n, k⟩; rcases m' with ⟨⟨l'⟩, n', k'⟩
  obtain ⟨hn, hk, hl⟩ := h
  refine ⟨hn, hk, ?_⟩
  simp only [Mem.freeFrame, List.filter_toArray]
  exact AllocsRefine.filter_fst _ (fun _ _ _ => rfl) hl

theorem Mem.Refines.dropFrames {m m' : Mem} (h : Mem.Refines m m') (act : Nat) :
    Mem.Refines (m.dropFrames act) (m'.dropFrames act) := by
  rcases m with ⟨⟨l⟩, n, k⟩; rcases m' with ⟨⟨l'⟩, n', k'⟩
  obtain ⟨hn, hk, hl⟩ := h
  refine ⟨hn, hk, ?_⟩
  simp only [Mem.dropFrames, List.filter_toArray]
  exact AllocsRefine.filter_fst _ (fun _ _ _ => rfl) hl

/-! ## `goResults` -/

/-- Lists of byte arrays refined pointwise. -/
inductive ArrsRefine : List (Array Byte) → List (Array Byte) → Prop where
  | nil : ArrsRefine [] []
  | cons {a b : Array Byte} {as bs : List (Array Byte)} : BytesRefineA a b → ArrsRefine as bs →
      ArrsRefine (a :: as) (b :: bs)

theorem putBytes_fold_mono : ∀ {pieces pieces' : List Val}, RefinesList pieces pieces' →
    ∀ (ls : List (Nat × Ty)) {buf buf' : Array Byte}, BytesRefineA buf buf' →
      BytesRefineA ((ls.zip pieces).foldl (fun buf ((o, lt), v) => putBytes buf o (encode lt v)) buf)
        ((ls.zip pieces').foldl (fun buf ((o, lt), v) => putBytes buf o (encode lt v)) buf')
  | _, _, .nil, ls, _, _, hb => by simpa using hb
  | _, _, .cons _ _, [], _, _, hb => by simpa using hb
  | _, _, .cons h t, _ :: ls, _, _, hb => by
    simp only [List.zip_cons_cons, List.foldl_cons]
    exact putBytes_fold_mono t ls (putBytes_mono hb (encode_mono _ h) _)

theorem goResults_post_mono {act : Nat} {m m' : Mem} (hm : Mem.Refines m m') :
    ∀ (os : List (Option AuxRef × Ty × Nat)) {pieces pieces' : List Val},
      RefinesList pieces pieces' →
      Res.Rel ArrsRefine (goResults.post act m pieces os) (goResults.post act m' pieces' os)
  | [], pieces, pieces', hp => by
    unfold goResults.post
    rw [show pieces.isEmpty = pieces'.isEmpty by
      cases hp <;> rfl]
    split
    · exact .ok .nil
    · exact .stuck _ _
  | (name, t, k) :: os, pieces, pieces', hp => by
    unfold goResults.post
    split
    · refine Res.Rel.bind (Res.Rel.ofOption _ _ name) fun n _ hn => ?_
      subst hn
      refine Res.Rel.bind (goResults_post_mono hm os hp) fun bs bs' hb => ?_
      exact .ok (.cons (hm.read_getD _ _ _) hb)
    · rw [← hp.length_eq]
      dsimp only
      split
      · exact .stuck _ _
      · refine Res.Rel.bind (goResults_post_mono hm os (hp.drop k)) fun bs bs' hb => ?_
        exact .ok (.cons (putBytes_fold_mono (hp.take k) _ (BytesRefineA.refl _)) hb)

theorem decode_zip_mono : ∀ {bs bs' : List (Array Byte)}, ArrsRefine bs bs' →
    ∀ (os : List (Option AuxRef × Ty × Nat)),
      RefinesList ((bs.zip os).map fun (b, (_, t, _)) => decode b 0 t)
        ((bs'.zip os).map fun (b, (_, t, _)) => decode b 0 t)
  | _, _, .nil, _ => .nil
  | _, _, .cons _ _, [] => .nil
  | _, _, .cons h t, _ :: os => .cons (decode_mono h 0 _) (decode_zip_mono t os)

theorem encode_zip_mono : ∀ {rs rs' : List Val}, RefinesList rs rs' →
    ∀ (os : List (Option AuxRef × Ty × Nat)),
      ArrsRefine ((rs.zip os).map fun (v, (_, t, _)) => encode t v)
        ((rs'.zip os).map fun (v, (_, t, _)) => encode t v)
  | _, _, .nil, _ => .nil
  | _, _, .cons _ _, [] => .nil
  | _, _, .cons h t, _ :: os => .cons (encode_mono _ h) (encode_zip_mono t os)

theorem hasTy_zip_eq : ∀ {rs rs' : List Val}, RefinesList rs rs' → Val.anyPoison rs = false →
    ∀ (os : List (Option AuxRef × Ty × Nat)),
      ((rs.zip os).all fun (v, (_, t, _)) => v.hasTy t) =
        ((rs'.zip os).all fun (v, (_, t, _)) => v.hasTy t)
  | _, _, .nil, _, _ => rfl
  | _, _, .cons _ _, _, [] => rfl
  | _, _, .cons h t, hp, _ :: os => by
    simp only [Val.anyPoison, Bool.or_eq_false_iff] at hp
    simp only [List.zip_cons_cons, List.all_cons, (h.noPoison hp.1).2, hasTy_zip_eq t hp.2 os]

/-- **`goResults` is monotone** on poison-free `MakeResult` components. -/
theorem goResults_mono {outs : Array (Option AuxRef × Ty × Nat)} {act : Nat} {rs rs' : List Val}
    {m m' : Mem} (hp : Val.anyPoison rs = false) (hr : RefinesList rs rs')
    (hm : Mem.Refines m m') :
    Res.Rel RefinesList (goResults outs act rs m) (goResults outs act rs' m') := by
  have hjp : ∀ bs bs', ArrsRefine bs bs' →
      Res.Rel RefinesList
        (let vals := (bs.zip outs.toList).map fun (b, (_, t, _)) => decode b 0 t
         if vals.any Val.hasPoison = true then Res.stuck "poison result" else Res.ok vals)
        (let vals := (bs'.zip outs.toList).map fun (b, (_, t, _)) => decode b 0 t
         if vals.any Val.hasPoison = true then Res.stuck "poison result" else Res.ok vals) := by
    intro bs bs' hb
    have hv := decode_zip_mono hb outs.toList
    simp only [Val.any_hasPoison]
    split
    · exact .stuck _ _
    · next hn =>
      have h' := (hv.noPoison (by simpa using hn)).1
      simp only [h', Bool.false_eq_true, ↓reduceIte]
      exact .ok hv
  unfold goResults
  simp only [hr.length_eq, hasTy_zip_eq hr hp]
  split
  · exact Res.Rel.bind (.ok (encode_zip_mono hr _)) hjp
  · exact Res.Rel.bind (goResults_post_mono hm _ hr) hjp

end GoFV.SSA.Sem

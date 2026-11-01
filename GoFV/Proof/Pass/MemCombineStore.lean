import GoFV.Proof.Pass.MemCombineRef

/-!
# memcombine: a combined store writes what its chain wrote (issue #35)

`store_chgRef`: a combined store `storeOK` accepts satisfies the atom simulation's changed-store
obligation (`AtomSim.ChgRefP`).

- The source (`chain_den`): the root's write succeeds on its arguments' terms, so (by `MemAtoms`)
  each store of the chain down to the target's memory `m0` holds the write of its arguments'
  terms; at every large fuel the chain's writes (`stStep`) applied to `m0`'s memory succeed with a
  memory refining the root's.
- Each store writes, through its pointer `base + idx + off` (`splitP_sound`, one base and index
  for the chain), the encoding of its value, which is `poison` or the bytes of its description
  (`recBytes`: `symOf_sound`, or the byte of a `ConstBool`); the offsets tile the target's width
  from the target's pointer, so the writes are one write of their bytes (`write_tiling`).
- The target writes at that pointer (a pointer of the chain, refined by `mc_ref`) on a memory
  refining `m0`'s the bytes of its value: if some stored value has defined bytes, the target's
  description reads only values each stored value reads, so its bytes are defined
  (`vbWidthOK`, its loads covered: `covered_loadOK`) and its value is their integer
  (`symOf_complete`), byte for byte the stored bytes; otherwise every stored byte is `poison`.
  `Mem.Refines.write` gives the refined memory.
-/

namespace GoFV.Proof.MemCombine

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.MemCombine.Check GoFV.Opt.RewriteCheck GoFV.Proof.Term
open GoFV.Proof.AtomSim

/-! ## Helpers -/

theorem retype_eq_mem' {t : Ty} {v : Val} {M : Mem} (h : v.retype t = .mem M) : v = .mem M := by
  unfold Val.retype at h
  split at h <;> (try unfold Val.ofStr at h) <;> (try unfold Val.ofSlice at h) <;>
    (repeat' split at h) <;> simp_all

theorem args_three {α : Type} {a : Array ID} (h : a.size = 3) (F : ID → α) :
    a.toList.map F = [F a[0]!, F a[1]!, F a[2]!] := by
  rcases a with ⟨_ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨t, l⟩⟩⟩⟩⟩ <;> simp_all

/-- A `Store`'s write: a pointer, a memory and the written memory. -/
theorem memDef_store_spec {tabs : Tables} {s : Value} (hs : s.op = .Store)
    {a b c y : Val} (h : memDef tabs s [a, b, c] = some y) :
    ∃ q m0 M', a = .ptr q ∧ c = .mem m0 ∧ m0.write q (encode (auxTy tabs s.aux) b) = some M' ∧
      y = .mem M' := by
  cases a <;> try (simp [memDef, hs] at h; done)
  cases c <;> try (simp [memDef, hs] at h; done)
  rename_i q m0
  simp only [memDef, hs, Option.map_eq_some_iff] at h
  obtain ⟨M', hw, rfl⟩ := h
  exact ⟨q, m0, M', rfl, rfl, hw, rfl⟩

theorem memDef_store_eq {tabs : Tables} {s : Value} (hs : s.op = .Store) (q : Ptr) (b : Val)
    (m : Mem) : memDef tabs s [.ptr q, b, .mem m] = (m.write q (encode (auxTy tabs s.aux) b)).map .mem := by
  simp [memDef, hs]

theorem refines_mem_inv {M : Mem} {v : Val} (h : Sem.Refines (.mem M) v) :
    ∃ M', v = .mem M' ∧ Mem.Refines M M' := by
  cases h with
  | mem hm => exact ⟨_, rfl, hm⟩

/-! ## The source's chain -/

/-- `chainTo`'s step. -/
theorem chainTo_succ {D : ID → Option Value} {m0 : ID} {n : Nat} {z : ID} {S : List ID}
    (h : chainTo D m0 (n + 1) z = some S) :
    (z = m0 ∧ S = []) ∨ (z ≠ m0 ∧ ∃ v S', D z = some v ∧ v.op = .Store ∧ v.args.size = 3 ∧
      chainTo D m0 n v.args[2]! = some S' ∧ S = z :: S') := by
  unfold chainTo at h
  by_cases hz : z = m0
  · subst hz; simp at h; exact .inl ⟨rfl, h⟩
  · right
    simp only [beq_iff_eq, hz, ite_false] at h
    refine ⟨hz, ?_⟩
    cases hD : D z with
    | none => rw [hD] at h; cases h
    | some v =>
      rw [hD] at h
      simp only at h
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨S', hS', rfl⟩ := Option.map_eq_some_iff.1 h
        exact ⟨v, S', rfl, hc.1, hc.2, hS', rfl⟩
      · cases h

/-- The elements of a chain are `Store`s with three arguments. -/
theorem chainTo_mem {D : ID → Option Value} {m0 : ID} : ∀ {n : Nat} {z : ID} {S : List ID},
    chainTo D m0 n z = some S → ∀ s ∈ S, ∃ v, D s = some v ∧ v.op = .Store ∧ v.args.size = 3
  | 0, _, _, h, _, _ => by cases h
  | n + 1, z, S, h, s, hs => by
    rcases chainTo_succ h with ⟨-, rfl⟩ | ⟨-, v, S', hv, hop, hsz, hS', rfl⟩
    · cases hs
    · rcases List.mem_cons.1 hs with rfl | hs
      · exact ⟨v, hv, hop, hsz⟩
      · exact chainTo_mem hS' s hs

/-- One store of a chain at fuel `K`, on the memory `m`. -/
def stStep (tabs : Tables) (D : ID → Option Value) (ρ : ID → Val) (K : Nat) (m : Mem) (s : ID) :
    Option Mem :=
  match D s with
  | some v =>
    match memDef tabs v [den D tabs ρ K v.args[0]!, den D tabs ρ K v.args[1]!, .mem m] with
    | some (.mem m') => some m'
    | _ => none
  | none => none

section Chain
variable {tabs : Tables} {D : ID → Option Value} {ρ : ID → Val} (hMA : MemAtoms D tabs ρ)
include hMA

/-- **The source's chain**: a chain element whose value is a memory is, at every large fuel, a
memory refined by the chain's writes on `m0`'s memory. -/
theorem chain_den {m0 : ID} : ∀ (N : Nat) (z : ID) (S : List ID), chainTo D m0 N z = some S →
    ∀ (k : Nat) (Mz : Mem), den D tabs ρ k z = .mem Mz →
    ∃ K0, ∀ K, K0 ≤ K → ∃ M0 Mz', den D tabs ρ K m0 = .mem M0 ∧
      S.reverse.foldlM (stStep tabs D ρ K) M0 = some Mz' ∧ Mem.Refines Mz Mz'
  | 0, _, _, h, _, _, _ => by cases h
  | N + 1, z, S, h, k, Mz, hz => by
    rcases chainTo_succ h with ⟨rfl, rfl⟩ | ⟨hne, v, S', hv, hop, hsz, hS', rfl⟩
    · refine ⟨k, fun K hK => ?_⟩
      have hm := den_fuel_mono D tabs ρ k K z hK
      rw [hz] at hm
      obtain ⟨M', hM', hr⟩ := refines_mem_inv hm
      exact ⟨M', M', hM', rfl, hr⟩
    · have hat : ¬ IsTerm D z := fun ⟨w, hw, ht⟩ => by
        rw [hv] at hw; cases hw; rw [hop] at ht; cases ht
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by
        cases k with
        | zero => simp [den] at hz
        | succ k' => exact ⟨k', rfl⟩
      rw [den_succ_atom hat] at hz
      obtain ⟨N0, hN0⟩ := hMA z v hv (by rw [hop]; rfl) (by rw [hz]; simp)
      obtain ⟨y, hy, hyr⟩ := hN0 N0 (Nat.le_refl _)
      rw [hz] at hyr
      have hy' : y = .mem Mz := retype_eq_mem' hyr.symm
      rw [args_three hsz, hy'] at hy
      obtain ⟨q, mp, M', hq, hmp, hw, hM⟩ := memDef_store_spec hop hy
      cases hM
      obtain ⟨K1, hK1⟩ := chain_den N v.args[2]! S' hS' N0 mp hmp
      refine ⟨max K1 N0, fun K hK => ?_⟩
      obtain ⟨M0, Mp', h0, hf, hr⟩ := hK1 K ((Nat.max_le.1 hK).1)
      have hl : RefinesList [den D tabs ρ N0 v.args[0]!, den D tabs ρ N0 v.args[1]!, .mem mp]
          [den D tabs ρ K v.args[0]!, den D tabs ρ K v.args[1]!, .mem Mp'] :=
        .cons (den_fuel_mono D tabs ρ N0 K _ ((Nat.max_le.1 hK).2))
          (.cons (den_fuel_mono D tabs ρ N0 K _ ((Nat.max_le.1 hK).2)) (.cons (.mem hr) .nil))
      obtain ⟨y'', hy'', hyy⟩ := memDef_store_mono hop hl
        (by rw [hq, memDef_store_eq hop, hw]; rfl)
      obtain ⟨Mz', rfl, hMM⟩ := refines_mem_inv hyy
      refine ⟨M0, Mz', h0, ?_, hMM⟩
      rw [List.reverse_cons, List.foldlM_append, hf]
      simp [stStep, hv, hy'']

end Chain

/-! ## Lists and bytes -/

theorem bytesRefine_of_get : ∀ {a b : List Byte}, a.length = b.length →
    (∀ i (ha : i < a.length) (hb : i < b.length), Byte.Refines a[i] b[i]) → BytesRefine a b
  | [], [], _, _ => .nil
  | x :: a, y :: b, hl, h =>
    .cons (h 0 (by simp) (by simp)) (bytesRefine_of_get (by simpa using hl) fun i ha hb =>
      h (i + 1) (by simp; omega) (by simp; omega))
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem bytesRefineA_of_get {a b : Array Byte} (hs : a.size = b.size)
    (h : ∀ i (ha : i < a.size) (hb : i < b.size), Byte.Refines a[i] b[i]) : BytesRefineA a b :=
  bytesRefine_of_get (by simpa using hs) fun i ha hb => by
    simpa using h i (by simpa using ha) (by simpa using hb)

/-- Elements of a list each predicate `P k` (`k < W`) holds of at most once are pairwise apart. -/
theorem pairwise_of_count {α : Type} (P : Nat → α → Bool) (W : Nat) :
    ∀ l : List α, (∀ k < W, (l.filter (P k)).length ≤ 1) →
      l.Pairwise (fun a b => ∀ k < W, ¬ (P k a = true ∧ P k b = true))
  | [], _ => .nil
  | a :: l, h => by
    refine List.Pairwise.cons (fun b hb k hk ⟨h1, h2⟩ => ?_) (pairwise_of_count P W l fun k hk => ?_)
    · have := h k hk
      rw [List.filter_cons_of_pos h1] at this
      have h0 : (l.filter (P k)).length = 0 := by simp only [List.length_cons] at this; omega
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff] at h0
      exact h0 b hb h2
    · have := h k hk
      by_cases h1 : P k a = true
      · rw [List.filter_cons_of_pos h1] at this; simp only [List.length_cons] at this; omega
      · rw [List.filter_cons_of_neg h1] at this; exact this

/-- A store of a chain and its record (`storeRecs`). -/
def StRel (tabs : Tables) (D : ID → Option Value) (s : ID) (r : StoreRec) : Prop :=
  ∃ v, D s = some v ∧ v.args.size = 3 ∧ r.1 = v.args[0]! ∧
    r.2.1 = splitP tabs D 64 v.args[0]! none 0 ∧ storedBytes tabs D v = some r.2.2

/-- Two lists related elementwise. -/
inductive Pairs {α β : Type} (Rel : α → β → Prop) : List α → List β → Prop where
  | nil : Pairs Rel [] []
  | cons {a : α} {b : β} {l : List α} {l' : List β} : Rel a b → Pairs Rel l l' →
      Pairs Rel (a :: l) (b :: l')

theorem mapM_some_cons {α β : Type} {F : α → Option β} {a : α} {l : List α} {out : List β}
    (h : (a :: l).mapM F = some out) : ∃ b bs, F a = some b ∧ l.mapM F = some bs ∧ out = b :: bs := by
  rw [List.mapM_cons] at h
  cases ha : F a with
  | none => simp [ha] at h
  | some b =>
    cases hl : l.mapM F with
    | none => simp [ha, hl] at h
    | some bs => simp [ha, hl] at h; exact ⟨b, bs, rfl, rfl, h.symm⟩

theorem storeRecs_rel {tabs : Tables} {D : ID → Option Value} :
    ∀ {S : List ID} {recs : List StoreRec}, storeRecs tabs D S = some recs →
      Pairs (StRel tabs D) S recs
  | [], recs, h => by simp [storeRecs] at h; subst h; exact .nil
  | s :: S, recs, h => by
    obtain ⟨r, rs, hr, hrs, rfl⟩ := mapM_some_cons h
    refine .cons ?_ (storeRecs_rel hrs)
    cases hs : D s with
    | none => rw [hs] at hr; cases hr
    | some v =>
      rw [hs] at hr
      simp only [Option.bind_some] at hr
      split at hr
      · rename_i h3
        simp only [beq_iff_eq] at h3
        obtain ⟨r', hb, rfl⟩ := Option.map_eq_some_iff.1 hr
        exact ⟨v, hs, h3, rfl, rfl, hb⟩
      · cases hr

theorem pairs_mem {α β : Type} {Rel : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, Pairs Rel l l' → ∀ a ∈ l, ∃ b ∈ l', Rel a b
  | _, _, .nil, _, h => absurd h List.not_mem_nil
  | _, _, .cons hr t, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨b, hb, hr'⟩ := pairs_mem t a h
      exact ⟨b, List.mem_cons_of_mem _ hb, hr'⟩

/-! ## A stored value's bytes -/

theorem encode_int_poison (w : Width) : encode (.int w) .poison = Array.replicate w.bytes .poison := by
  simp [encode, Ty.size]

/-- **The bytes a store writes**: `poison`, or its description's (defined) bytes, whose loads are
valid. -/
theorem recBytes {tabs : Tables} {D : ID → Option Value} {ρ : ID → Val} (hT : Term.Typed D tabs ρ)
    {v : Value} {r : Desc} (hsb : storedBytes tabs D v = some r) (K : Nat) :
    (encode (auxTy tabs v.aux) (den D tabs ρ K v.args[1]!)).size = r.1.length ∧
    ((∀ t < r.1.length, (encode (auxTy tabs v.aux) (den D tabs ρ K v.args[1]!))[t]? = some .poison) ∨
      ∃ C, semL (den D tabs ρ K) r.1 = some C ∧ (∀ l ∈ r.2, LoadOK (den D tabs ρ K) l) ∧
        ∀ t < r.1.length, ∃ c, C[t]? = some c ∧
          (encode (auxTy tabs v.aux) (den D tabs ρ K v.args[1]!))[t]? = some (.b c)) := by
  unfold storedBytes at hsb
  dsimp only at hsb
  cases hx : D v.args[1]! with
  | none => rw [hx] at hsb; cases hsb
  | some xv =>
    rw [hx] at hsb
    simp only at hsb
    have hty := den_hasTy hT hx K
    split at hsb
    · rename_i w w' ha ht
      split at hsb
      · rename_i hww
        obtain ⟨rfl, h8⟩ := hww
        cases hs : symOf tabs D false false srcFuel v.args[1]! with
        | none => rw [hs] at hsb; cases hsb
        | some r' =>
          rw [hs] at hsb
          simp only at hsb
          split at hsb
          · rename_i hlen
            cases hsb
            rw [ha]
            rw [ht] at hty
            generalize hd : den D tabs ρ K v.args[1]! = d at hty ⊢
            cases d with
            | poison =>
              rw [encode_int_poison]
              exact ⟨by simp [hlen], .inl fun t htl => by rw [hlen] at htl; simp [htl]⟩
            | int w0 X =>
              simp only [Val.hasTy, beq_iff_eq] at hty
              subst hty
              have hsd := symOf_sound hT srcFuel K v.args[1]! r w0 X hs hd
              rw [encode_int_bytes]
              refine ⟨by simp [hlen], .inr ⟨_, hsd.1, hsd.2, fun t htl => ?_⟩⟩
              rw [hlen] at htl
              refine ⟨byteOf X.toNat t, ?_, ?_⟩
              · simp [bytesOf, htl]
              · simp [htl]
            | ptr p =>
              exfalso
              cases w <;> simp [Val.hasTy] at hty <;> revert h8 <;> decide
            | _ => simp [Val.hasTy] at hty
          · cases hsb
      · cases hsb
    · rename_i ha ht
      split at hsb
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        cases hsb
        rw [ha]
        cases K with
        | zero =>
          refine ⟨rfl, .inl fun t htl => ?_⟩
          simp at htl; subst htl; simp [den, encode, Ty.size]
        | succ k =>
          have hcb : evalPure .ConstBool Ty.bool xv.auxInt xv.aux
              (xv.args.toList.map (den D tabs ρ k)) = .bool (xv.auxInt != 0) := rfl
          have hv : den D tabs ρ (k + 1) v.args[1]! = .bool (xv.auxInt != 0) := by
            rw [den_term hx (by rw [hc.1]; rfl) (by rw [hc.1]; rfl), hc.1, ht, hcb]
            rfl
          rw [hv]
          refine ⟨rfl, .inr ⟨[if (xv.auxInt != 0) = true then 1 else 0], rfl,
            fun l hl => (List.not_mem_nil hl).elim, fun t htl => ?_⟩⟩
          simp only [List.length_cons, List.length_nil] at htl
          obtain rfl : t = 0 := by omega
          cases (xv.auxInt != 0) <;> exact ⟨_, rfl, rfl⟩
      · cases hsb
    · cases hsb

/-! ## What the checker says -/

theorem tileOK_spec {recs : List StoreRec} {o0 : Int} {W : Nat} {bt : List SB} {sg : List LoadRec}
    (h : tileOK recs o0 W bt sg = true) :
    (∀ r ∈ recs, o0 ≤ r.2.1.2.2 ∧ (r.2.1.2.2 - o0).toNat + r.2.2.1.length ≤ W ∧
      (∀ k < r.2.2.1.length, bt[(r.2.1.2.2 - o0).toNat + k]? = r.2.2.1[k]?) ∧
      (∀ y ∈ vbIds bt, y ∈ vbIds r.2.2.1) ∧ ∀ t ∈ sg, coveredOK r.2.2.2 t = true) ∧
    ∀ k < W, (recs.filter (covers o0 k)).length = 1 := by
  unfold tileOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq, List.mem_range,
    List.contains_iff_mem] at h
  exact ⟨fun r hr => by
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h.1 r hr
    exact ⟨h1, h2, h3, h4, h5⟩, h.2⟩

theorem storeOK_spec {tabs : Tables} {f g : Func} {M : Array Bool} {x : ID} {u w : Value}
    (h : storeOK tabs f g M x u w = true) :
    u.op = .Store ∧ w.op = .Store ∧ u.args.size = 3 ∧ w.args.size = 3 ∧
    M.getD w.args[2]! false = true ∧ M.getD w.args[0]! false = true ∧
    ∃ S recs b0 i0 o0 r0 ww sv bt sg,
      chainTo f.value? w.args[2]! 9 x = some S ∧ 2 ≤ S.length ∧
      storeRecs tabs f.value? S = some recs ∧ (w.args[0]!, (b0, i0, o0), r0) ∈ recs ∧
      ptrTyped tabs f.value? b0 = true ∧ (∀ r ∈ recs, r.2.1.1 = b0 ∧ r.2.1.2.1 = i0) ∧
      auxTy tabs w.aux = .int ww ∧ listedD g w.args[1]! = some sv ∧
      intW (tabs.ty sv.type) = some ww ∧
      symOf tabs (listedD g) true false tgtFuel w.args[1]! = some (bt, sg) ∧
      bt.length = ww.bytes ∧ (∀ s ∈ bt, vbWidthOK tabs (listedD g) s = true) ∧
      leavesIn M bt sg = true ∧ tileOK recs o0 ww.bytes bt sg = true := by
  unfold storeOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hu, hw⟩, hu3⟩, hw3⟩, ⟨hm0, hpw⟩, h⟩ := h
  refine ⟨hu, hw, hu3, hw3, hm0, hpw, ?_⟩
  split at h
  · cases h
  rename_i S hS
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlen, h⟩ := h
  split at h
  · cases h
  rename_i recs hrecs
  split at h
  · cases h
  rename_i p b0 i0 o0 r0 hfind
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hb0, hbase⟩, h⟩ := h
  have hp := List.find?_some hfind
  simp only [beq_iff_eq] at hp
  subst hp
  have hmem := List.mem_of_find?_eq_some hfind
  split at h
  · rename_i ww sv haux hsv
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hsvw, h⟩ := h
    split at h
    · rename_i bt sg hbt
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
      obtain ⟨⟨⟨hbtl, hvbw⟩, hleaves⟩, htile⟩ := h
      exact ⟨S, recs, b0, i0, o0, r0, ww, sv, bt, sg, hS, hlen, hrecs, hmem, hb0, hbase, haux, hsv,
        hsvw, hbt, hbtl, hvbw, hleaves, htile⟩
    · cases h
  · cases h

/-! ## Lists -/

theorem pairs_mem' {α β : Type} {Rel : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, Pairs Rel l l' → ∀ b ∈ l', ∃ a ∈ l, Rel a b
  | _, _, .nil, _, h => absurd h List.not_mem_nil
  | _, _, .cons hr t, b, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨a, ha, hr'⟩ := pairs_mem' t b h
      exact ⟨a, List.mem_cons_of_mem _ ha, hr'⟩

theorem pairs_map {α β γ : Type} {Rel : α → β → Prop} {F : α → γ} {G : β → γ}
    (hFG : ∀ a b, Rel a b → F a = G b) :
    ∀ {l : List α} {l' : List β}, Pairs Rel l l' → l.map F = l'.map G
  | _, _, .nil => rfl
  | _, _, .cons hr t => by simp only [List.map_cons, hFG _ _ hr, pairs_map hFG t]

theorem foldlM_some_mem {α β : Type} {F : α → β → Option α} :
    ∀ {l : List β} {a b : α}, l.foldlM F a = some b → ∀ x ∈ l, ∃ m m', F m x = some m'
  | [], _, _, _, x, hx => absurd hx List.not_mem_nil
  | y :: l, a, b, h, x, hx => by
    rw [List.foldlM_cons] at h
    cases hy : F a y with
    | none => rw [hy] at h; cases h
    | some a' =>
      rw [hy] at h
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨a, a', hy⟩
      · exact foldlM_some_mem h x hx

theorem foldlM_congr_map {α β γ : Type} {F : α → β → Option α} {G : α → γ → Option α}
    {H : β → γ} : ∀ (l : List β) (a : α), (∀ x ∈ l, ∀ m, F m x = G m (H x)) →
      l.foldlM F a = (l.map H).foldlM G a
  | [], _, _ => rfl
  | y :: l, a, h => by
    rw [List.foldlM_cons, List.map_cons, List.foldlM_cons, h y List.mem_cons_self a]
    cases G a (H y) with
    | none => rfl
    | some a' => exact foldlM_congr_map l a' fun x hx m => h x (List.mem_cons_of_mem _ hx) m

theorem ptrAt_zero (P : Ptr) : ptrAt P 0 0 = P := by
  cases P; simp [ptrAt]

theorem semL_mem {V : ID → Val} {l : List SB} {C : List (BitVec 8)} (h : semL V l = some C)
    {s : SB} (hs : s ∈ l) : ∃ c, s.sem V = some c := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hs
  obtain ⟨c, hc, -⟩ := semL_getElem? h k _ (List.getElem?_eq_getElem hk)
  exact ⟨c, hc⟩

theorem byte?_some {v : Val} {k : Nat} {c : BitVec 8} (h : byte? v k = some c) :
    ∃ w X, v = .int w X ∧ k < w.bytes := by
  unfold byte? at h
  split at h
  · rename_i w X
    split at h
    · exact ⟨w, X, rfl, by assumption⟩
    · cases h
  · cases h

theorem mem_vbIds {bs : List SB} {y : ID} : y ∈ vbIds bs ↔ ∃ k, SB.vb y k ∈ bs := by
  unfold vbIds
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨s, hs, hy⟩
    cases s <;> simp [SB.vbId?] at hy
    subst hy; exact ⟨_, hs⟩
  · rintro ⟨k, hk⟩
    exact ⟨_, hk, rfl⟩

theorem storedBytes_pos {tabs : Tables} {D : ID → Option Value} {v : Value} {r : Desc}
    (h : storedBytes tabs D v = some r) : 0 < r.1.length := by
  unfold storedBytes at h
  dsimp only at h
  split at h
  · split at h
    · split at h
      · split at h
        · split at h
          · rename_i hl; cases h; rw [hl]; exact bytes_pos _
          · cases h
        · cases h
      · cases h
    · split at h
      · cases h; simp
      · cases h
    · cases h
  · cases h

theorem recs_pos {tabs : Tables} {D : ID → Option Value} {S : List ID} {recs : List StoreRec}
    (h : Pairs (StRel tabs D) S recs) : ∀ r ∈ recs, 0 < r.2.2.1.length := fun r hr => by
  obtain ⟨s, -, v, -, -, -, -, hsb⟩ := pairs_mem' h r hr
  exact storedBytes_pos hsb

/-- The offset (from `o0`) a store of a chain writes at. -/
def tileD (tabs : Tables) (D : ID → Option Value) (o0 : Int) (s : ID) : Nat :=
  match D s with
  | some v => ((splitP tabs D 64 v.args[0]! none 0).2.2 - o0).toNat
  | none => 0

/-- The bytes a store of a chain writes at fuel `F`. -/
def tileE (tabs : Tables) (D : ID → Option Value) (ρ : ID → Val) (F : Nat) (s : ID) : Array Byte :=
  match D s with
  | some v => encode (auxTy tabs v.aux) (den D tabs ρ F v.args[1]!)
  | none => #[]

/-- A record's place: its offset from `o0` and its length. -/
def tileOf (o0 : Int) (r : StoreRec) : Nat × Nat := ((r.2.1.2.2 - o0).toNat, r.2.2.1.length)

section
variable {tabs : Tables} {f g : Func} {R : Array Bool} {ce ce' : CheckEnv}
  (hwf : WF ce f) (hwg : WF ce' g) (K : McFacts tabs f g R)
include hwf hwg K

/-- **The target's write** refines the chain's writes at fuel `F`. -/
theorem tile_target {ρ ρ' : ID → Val} (hρ : ValRef ρ ρ') (hTf : Term.Typed f.value? tabs ρ)
    (hTg : Term.Typed (listedDefs g) tabs ρ') {w : Value} (hws : w.op = .Store)
    (hw3 : w.args.size = 3) (hm0M : (relMarks f g R).getD w.args[2]! false = true)
    (hpwM : (relMarks f g R).getD w.args[0]! false = true) {S : List ID} {recs : List StoreRec}
    {b0 : ID} {i0 : Option ID} {o0 : Int} {r0 : Desc} {ww : Width} {sv : Value} {bt : List SB}
    {sg : List LoadRec} (hrecs : storeRecs tabs f.value? S = some recs)
    (hSt : ∀ s ∈ S, ∃ v, f.value? s = some v ∧ v.op = .Store ∧ v.args.size = 3)
    (hr0 : (w.args[0]!, (b0, i0, o0), r0) ∈ recs) (hb0 : ptrTyped tabs f.value? b0 = true)
    (hbase : ∀ r ∈ recs, r.2.1.1 = b0 ∧ r.2.1.2.1 = i0) (haux : auxTy tabs w.aux = .int ww)
    (hsv : listedD g w.args[1]! = some sv)
    (hbt : symOf tabs (listedD g) true false tgtFuel w.args[1]! = some (bt, sg))
    (hbtl : bt.length = ww.bytes) (hvbw : ∀ s ∈ bt, vbWidthOK tabs (listedD g) s = true)
    (hleaves : leavesIn (relMarks f g R) bt sg = true) (htile : tileOK recs o0 ww.bytes bt sg = true)
    {F : Nat} {M0 Mt : Mem} (h0 : den f.value? tabs ρ F w.args[2]! = .mem M0)
    (hfold : S.reverse.foldlM (stStep tabs f.value? ρ F) M0 = some Mt) :
    ∃ m y', memDef tabs w (w.args.toList.map (den (listedDefs g) tabs ρ' m)) = some y' ∧
      Sem.Refines (.mem Mt) y' := by
  classical
  have hM : ∀ y, (relMarks f g R).getD y false = true →
      Sem.Refines (den f.value? tabs ρ F y) (den (listedDefs g) tabs ρ' (tgtFuel * F) y) :=
    fun y hy => mc_ref hwf hwg K hρ hTf hTg F y (relMarks_getD hy)
  obtain ⟨hrec, hcount⟩ := tileOK_spec htile
  have hrel := storeRecs_rel hrecs
  unfold leavesIn at hleaves
  simp only [Bool.and_eq_true, List.all_eq_true] at hleaves
  obtain ⟨hlb, hls⟩ := hleaves
  have hstore : ∀ s ∈ S, ∀ v, f.value? s = some v → v.op = .Store := fun s hs v hv => by
    obtain ⟨v', hv', hop, -⟩ := hSt s hs; rw [hv] at hv'; cases hv'; exact hop
  -- every store of the chain writes through a pointer
  have hptr : ∀ s ∈ S, ∀ v, f.value? s = some v → ∃ P, den f.value? tabs ρ F v.args[0]! = .ptr P := by
    intro s hs v hv
    obtain ⟨m, m', hm⟩ := foldlM_some_mem hfold s (List.mem_reverse.2 hs)
    simp only [stStep, hv] at hm
    split at hm
    · rename_i m'' hd
      obtain ⟨q, -, -, hq, -⟩ := memDef_store_spec (hstore s hs v hv) hd
      exact ⟨q, hq⟩
    · cases hm
  -- the chain's base and index, and the target's pointer `Q`
  obtain ⟨s0, hs0, v0, hv0, -, hp0, hsp0, -⟩ := pairs_mem' hrel _ hr0
  simp only at hp0 hsp0
  obtain ⟨P0, hP0⟩ := hptr s0 hs0 v0 hv0
  obtain ⟨P, I, hPb, hI, hPQ0⟩ := splitP_sound hTf (m := F) 64 F v0.args[0]! none 0 (Nat.le_refl _)
    hsp0.symm hb0 hP0 rfl
  rw [ptrAt_zero] at hPQ0
  have hQ : den f.value? tabs ρ F w.args[0]! = .ptr (ptrAt P I o0) := by rw [hp0, hP0, hPQ0]
  have hPs : ∀ s ∈ S, ∀ v, f.value? s = some v → ∃ r ∈ recs, StRel tabs f.value? s r ∧
      den f.value? tabs ρ F v.args[0]! = .ptr (ptrAt P I r.2.1.2.2) := by
    intro s hs v hv
    obtain ⟨⟨rp, ⟨rb, ri, ro⟩, rd⟩, hr, hsr⟩ := pairs_mem hrel s hs
    obtain ⟨v', hv', h3', hr1, hsp, hsb'⟩ := hsr
    rw [hv] at hv'; cases hv'
    obtain ⟨Ps, hPs⟩ := hptr s hs v hv
    obtain ⟨hb, hi⟩ := hbase _ hr
    simp only at hb hi hsp
    subst hb hi
    obtain ⟨P', I', hP', hI', hPs'⟩ := splitP_sound hTf (m := F) 64 F _ none 0 (Nat.le_refl _)
      hsp.symm hb0 hPs rfl
    rw [hPb] at hP'; cases hP'; rw [hI] at hI'; cases hI'
    rw [ptrAt_zero] at hPs'
    exact ⟨_, hr, ⟨v, hv, h3', hr1, hsp, hsb'⟩, by rw [hPs, hPs']⟩
  -- the chain's writes are a tiling from `Q`
  have hstep : ∀ s ∈ S, ∀ m, stStep tabs f.value? ρ F m s =
      m.write ((ptrAt P I o0).add (BitVec.ofNat 64 (tileD tabs f.value? o0 s)))
        (tileE tabs f.value? ρ F s) := by
    intro s hs m
    obtain ⟨v, hv, hop, -⟩ := hSt s hs
    obtain ⟨⟨rp, ⟨rb, ri, ro⟩, rd⟩, hr, ⟨v', hv', -, -, hsp, -⟩, hPs⟩ := hPs s hs v hv
    rw [hv] at hv'; cases hv'
    simp only at hsp hPs
    have hro : o0 ≤ ro := (hrec _ hr).1
    simp only [tileD, tileE, stStep, hv, ← hsp]
    rw [hPs, memDef_store_eq hop, ptrAt_le hro]
    cases m.write _ _ <;> rfl
  have hfold' := hfold
  rw [foldlM_congr_map (H := fun s => (tileD tabs f.value? o0 s, tileE tabs f.value? ρ F s))
    (G := fun m (p : Nat × Array Byte) => m.write ((ptrAt P I o0).add (BitVec.ofNat 64 p.1)) p.2)
    _ _ (fun s hs m => hstep s (List.mem_reverse.1 hs) m)] at hfold'
  generalize hws' : S.reverse.map (fun s => (tileD tabs f.value? o0 s, tileE tabs f.value? ρ F s)) = ws
    at hfold'
  have hshape : ws.map (fun p => (p.1, p.2.size)) = (recs.map (tileOf o0)).reverse := by
    rw [← hws', List.map_map, List.map_reverse]
    congr 1
    refine pairs_map (fun s r hsr => ?_) hrel
    obtain ⟨v, hv, -, -, hsp, hsb⟩ := hsr
    simp only [Function.comp, tileD, tileE, tileOf, hv, ← hsp, (recBytes hTf hsb F).1]
  have hmemws : ∀ p ∈ ws, ∃ r ∈ recs, tileOf o0 r = (p.1, p.2.size) := fun p hp => by
    have := List.mem_map_of_mem (f := fun p : Nat × Array Byte => (p.1, p.2.size)) hp
    rw [hshape, List.mem_reverse, List.mem_map] at this
    exact this
  have hin : ∀ p ∈ ws, p.1 + p.2.size ≤ ww.bytes := fun p hp => by
    obtain ⟨r, hr, he⟩ := hmemws p hp
    simp only [tileOf, Prod.mk.injEq] at he
    rw [← he.1, ← he.2]; exact (hrec r hr).2.1
  have hcov : ∀ k < ww.bytes, ∃ p ∈ ws, p.1 ≤ k ∧ k < p.1 + p.2.size := fun k hk => by
    obtain ⟨r, hr⟩ := List.length_pos_iff_exists_mem.1 (by rw [hcount k hk]; exact Nat.one_pos)
    rw [List.mem_filter] at hr
    obtain ⟨hr, hc⟩ := hr
    have hro := (hrec r hr).1
    have : tileOf o0 r ∈ ws.map (fun p => (p.1, p.2.size)) := by
      rw [hshape, List.mem_reverse]; exact List.mem_map_of_mem hr
    obtain ⟨p, hp, he⟩ := List.mem_map.1 this
    simp only [tileOf, Prod.mk.injEq] at he
    unfold covers at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    refine ⟨p, hp, ?_, ?_⟩ <;> rw [he.1] <;> try rw [he.2]
    all_goals omega
  have hdis : ws.Pairwise fun p q => p.1 + p.2.size ≤ q.1 ∨ q.1 + q.2.size ≤ p.1 := by
    have key : (ws.map (fun p : Nat × Array Byte => (p.1, p.2.size))).Pairwise
        (fun a b : Nat × Nat => a.1 + a.2 ≤ b.1 ∨ b.1 + b.2 ≤ a.1) := by
      rw [hshape, List.pairwise_reverse, List.pairwise_map]
      have hp := pairwise_of_count (covers o0) ww.bytes recs fun k hk => Nat.le_of_eq (hcount k hk)
      refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) hp
      have ha' := hrec a ha
      have hb' := hrec b hb
      have hla := recs_pos hrel a ha
      have hlb := recs_pos hrel b hb
      simp only [tileOf]
      refine Classical.byContradiction fun hne => ?_
      refine hab (max (a.2.1.2.2 - o0).toNat (b.2.1.2.2 - o0).toNat) ?_ ⟨?_, ?_⟩
      · omega
      all_goals unfold covers; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
    exact List.pairwise_map.1 key
  obtain ⟨Sb, hSz, hSb, hwr⟩ := write_tiling ws hin hcov hdis hfold'
  -- each byte of `Sb` is a byte of a store of the chain
  have hbyte : ∀ i < ww.bytes, ∃ s ∈ S, ∃ v r, f.value? s = some v ∧ StRel tabs f.value? s r ∧
      storedBytes tabs f.value? v = some r.2.2 ∧
      tileD tabs f.value? o0 s = (r.2.1.2.2 - o0).toNat ∧
      tileD tabs f.value? o0 s ≤ i ∧ i - tileD tabs f.value? o0 s < r.2.2.1.length ∧ r ∈ recs ∧
      Sb[i]? = (tileE tabs f.value? ρ F s)[i - tileD tabs f.value? o0 s]? := by
    intro i hi
    obtain ⟨p, hp, h1, h2⟩ := hcov i hi
    have hp' := hp
    rw [← hws', List.mem_map] at hp'
    obtain ⟨s, hs, rfl⟩ := hp'
    rw [List.mem_reverse] at hs
    obtain ⟨v, hv, -⟩ := hSt s hs
    obtain ⟨r, hr, hsr⟩ := pairs_mem hrel s hs
    obtain ⟨v', hv', h3, hr1, hsp, hsb⟩ := hsr
    rw [hv] at hv'; cases hv'
    have hsz := (recBytes hTf hsb F).1
    have htd : tileD tabs f.value? o0 s = (r.2.1.2.2 - o0).toNat := by simp [tileD, hv, ← hsp]
    simp only at h1 h2
    have hte : (tileE tabs f.value? ρ F s).size = r.2.2.1.length := by simp [tileE, hv, hsz]
    refine ⟨s, hs, v, r, hv, ⟨v, hv, h3, hr1, hsp, hsb⟩, hsb, htd, h1, by omega, hr, ?_⟩
    have := hSb _ _ hp (i - tileD tabs f.value? o0 s) (by omega)
    rwa [Nat.add_sub_cancel' h1] at this
  -- the target's pointer and memory
  have hQ' := hM _ hpwM
  rw [hQ] at hQ'
  have hQT := refines_ptr hQ'
  have hm0' := hM _ hm0M
  rw [h0] at hm0'
  obtain ⟨M0', hM0', hMM0⟩ := refines_mem_inv hm0'
  -- the target writes bytes refining `Sb` at `Q`
  have fin : ∀ mt, tgtFuel * F ≤ mt →
      BytesRefineA Sb (encode (.int ww) (den (listedDefs g) tabs ρ' mt w.args[1]!)) →
      ∃ m y', memDef tabs w (w.args.toList.map (den (listedDefs g) tabs ρ' m)) = some y' ∧
        Sem.Refines (.mem Mt) y' := by
    intro mt hmt hST
    have hpT := den_fuel_mono (listedDefs g) tabs ρ' _ mt w.args[0]! hmt
    rw [hQT] at hpT
    have hmT := den_fuel_mono (listedDefs g) tabs ρ' _ mt w.args[2]! hmt
    rw [hM0'] at hmT
    obtain ⟨M0'', hM0'', hMM0'⟩ := refines_mem_inv hmT
    obtain ⟨Mt', hwT, hMt⟩ := (hMM0.trans hMM0').write hST hwr
    refine ⟨mt, .mem Mt', ?_, .mem hMt⟩
    rw [args_three hw3, refines_ptr hpT, hM0'', memDef_store_eq hws, haux, hwT]
    rfl
  by_cases hdef : ∃ s ∈ S, ∃ v r C, f.value? s = some v ∧ storedBytes tabs f.value? v = some r ∧
      semL (den f.value? tabs ρ F) r.1 = some C ∧ ∀ l ∈ r.2, LoadOK (den f.value? tabs ρ F) l
  · -- some stored value has defined bytes: so has the target's
    obtain ⟨s1, hs1, v1, r1, C1, hv1, hsb1, hC1, hL1⟩ := hdef
    obtain ⟨rr, hrr, hsrr⟩ := pairs_mem hrel s1 hs1
    obtain ⟨v', hv', -, -, -, hsb'⟩ := hsrr
    rw [hv1] at hv'; cases hv'
    rw [hsb1] at hsb'; cases hsb'
    obtain ⟨-, -, -, hvb1, hcov1⟩ := hrec rr hrr
    have hLT : ∀ t ∈ sg, LoadOK (den (listedDefs g) tabs ρ' (tgtFuel * F)) t := fun t ht =>
      covered_loadOK hL1 (hcov1 t ht) fun y hy => hM y (hls t ht y hy)
    have hbk := symOf_backed hbt
    have hvbT : ∀ y k, SB.vb y k ∈ bt →
        ∃ c, byte? (den (listedDefs g) tabs ρ' (tgtFuel * F) y) k = some c := by
      intro y k hk
      obtain ⟨k', hk'⟩ := mem_vbIds.1 (hvb1 y (mem_vbIds.2 ⟨k, hk⟩))
      obtain ⟨c', hc'⟩ := semL_mem hC1 hk'
      obtain ⟨w1, X1, hX1, -⟩ := byte?_some hc'
      have hyM := hM y (hlb _ hk y (by simp [SB.ids]))
      rw [hX1] at hyM
      have hX1' := refines_int hyM
      have hw := hvbw _ hk
      simp only [vbWidthOK] at hw
      cases hy : listedD g y with
      | none => rw [hy] at hw; cases hw
      | some vy =>
        rw [hy] at hw
        simp only at hw
        cases hwy : intW (tabs.ty vy.type) with
        | none => rw [hwy] at hw; cases hw
        | some wy =>
          rw [hwy] at hw
          simp only [Option.any_some, decide_eq_true_eq] at hw
          have hty := den_hasTy hTg (by rw [← listedD_eq]; exact hy) (tgtFuel * F)
          rw [intW_eq hwy, hX1'] at hty
          simp only [Val.hasTy, beq_iff_eq] at hty
          subst hty
          exact ⟨byteOf X1.toNat k, by simp [byte?, hX1', hw]⟩
    obtain ⟨B, hB⟩ := semL_of_backed hvbT hbk hLT
    rw [listedD_eq] at hbt
    obtain ⟨w1, Y, hY, hYb⟩ := symOf_complete hTg (tgtFuel * F) tgtFuel _ (bt, sg) B hbt hB hLT
    have hw1 : w1 = ww := width_eq_of_bytes (by
      have := congrArg List.length hYb
      rw [bytesOf_length, semL_length hB, hbtl] at this
      exact this)
    subst w1
    refine fin (tgtFuel * F + tgtFuel) (Nat.le_add_right _ _) ?_
    rw [hY, encode_int_bytes]
    refine bytesRefineA_of_get (by simp [hSz]) fun i hi0 _ => ?_
    have hi : i < ww.bytes := hSz ▸ hi0
    obtain ⟨s, hs, v, r, hv, -, hsb, htd, hle, hlt, hr, hSi⟩ := hbyte i hi
    obtain ⟨-, -, hbtr, -, -⟩ := hrec r hr
    have hSi' : Sb[i]? = some Sb[i] := Array.getElem?_eq_getElem hi0
    rw [hSi'] at hSi
    rcases (recBytes hTf hsb F).2 with hp | ⟨C, hC, -, hc⟩
    · have := hp (i - tileD tabs f.value? o0 s) hlt
      simp only [tileE, hv] at hSi
      rw [this] at hSi
      rw [Option.some.inj hSi]
      exact .poison _
    · obtain ⟨c, hCc, hEc⟩ := hc _ hlt
      simp only [tileE, hv] at hSi
      rw [hEc] at hSi
      rw [Option.some.inj hSi]
      -- the target's byte `i` is `c`
      have hbi := hbtr _ hlt
      rw [← htd, Nat.add_sub_cancel' hle] at hbi
      obtain ⟨sb, hsbi⟩ : ∃ sb, r.2.2.1[i - tileD tabs f.value? o0 s]? = some sb :=
        ⟨_, List.getElem?_eq_getElem hlt⟩
      obtain ⟨c0, hc0, hCc0⟩ := semL_getElem? hC _ _ hsbi
      rw [hCc] at hCc0; cases hCc0
      rw [hsbi] at hbi
      have hT1 := sem_mono' (fun y hy => hM y (hlb sb (List.mem_of_getElem? hbi) y hy)) hc0
      obtain ⟨c1, hc1, hBc1⟩ := semL_getElem? hB _ _ hbi
      rw [hT1] at hc1; cases hc1
      have hBi : B[i]? = some (byteOf Y.toNat i) := by
        rw [← hYb]; simp [bytesOf, hi]
      rw [hBc1] at hBi; cases hBi
      simp [hi]
      exact .refl _
  · -- every stored byte is `poison`
    refine fin _ (Nat.le_refl _) (bytesRefineA_of_get (by simp [hSz, encode_size, Ty.size]) ?_)
    intro i hi0 _
    have hi : i < ww.bytes := hSz ▸ hi0
    obtain ⟨s, hs, v, r, hv, -, hsb, -, -, hlt, -, hSi⟩ := hbyte i hi
    rw [Array.getElem?_eq_getElem hi0] at hSi
    rcases (recBytes hTf hsb F).2 with hp | ⟨C, hC, hL, -⟩
    · simp only [tileE, hv] at hSi
      rw [hp _ hlt] at hSi
      rw [Option.some.inj hSi]
      exact .poison _
    · exact absurd ⟨s, hs, v, r.2.2, C, hv, hsb, hC, hL⟩ hdef

/-- **A combined store** writes a memory refining the one its chain of stores wrote. -/
theorem store_chgRef {x : ID} {u w : Value} (hu : f.value? x = some u)
    (hs : storeOK tabs f g (relMarks f g R) x u w = true) :
    ChgRefP f.value? tabs u (listedDefs g) w := by
  intro ρ ρ' hρ hTf hTg hMA n y hy
  obtain ⟨hus, hws, hu3, hw3, hm0M, hpwM, S, recs, b0, i0, o0, r0, ww, svv, bt, sg, hS, hSlen,
    hrecs, hr0, hb0, hbase, haux, hsv, hsvw, hbt, hbtl, hvbw, hleaves, htile⟩ := storeOK_spec hs
  rw [args_three hu3] at hy
  obtain ⟨Pk, Mk1, Mtop, hpk, hmk, hwk, rfl⟩ := memDef_store_spec hus hy
  obtain ⟨S', hS', rfl⟩ : ∃ S', chainTo f.value? w.args[2]! 8 u.args[2]! = some S' ∧
      S = x :: S' := by
    rcases chainTo_succ hS with ⟨-, rfl⟩ | ⟨-, v, S', hv, -, -, hS', rfl⟩
    · simp at hSlen
    · rw [hu] at hv; cases hv; exact ⟨S', hS', rfl⟩
  obtain ⟨K1, hK1⟩ := chain_den hMA 8 u.args[2]! S' hS' n Mk1 hmk
  obtain ⟨M0, Mk1', h0, hf, hr1⟩ := hK1 (max K1 n) (Nat.le_max_left _ _)
  have hnK : n ≤ max K1 n := Nat.le_max_right _ _
  have hl : RefinesList [den f.value? tabs ρ n u.args[0]!, den f.value? tabs ρ n u.args[1]!,
      .mem Mk1] [den f.value? tabs ρ (max K1 n) u.args[0]!, den f.value? tabs ρ (max K1 n) u.args[1]!,
      .mem Mk1'] :=
    .cons (den_fuel_mono _ _ _ _ _ _ hnK) (.cons (den_fuel_mono _ _ _ _ _ _ hnK)
      (.cons (.mem hr1) .nil))
  obtain ⟨y'', hy'', hyy⟩ := memDef_store_mono hus hl
    (by rw [hpk, memDef_store_eq hus, hwk]; rfl)
  obtain ⟨Mtop', rfl, hMM⟩ := refines_mem_inv hyy
  have hfold : (x :: S').reverse.foldlM (stStep tabs f.value? ρ (max K1 n)) M0 = some Mtop' := by
    rw [List.reverse_cons, List.foldlM_append, hf]; simp [stStep, hu, hy'']
  obtain ⟨m, y', h1, h2⟩ := tile_target hwf hwg K hρ hTf hTg hws hw3 hm0M hpwM hrecs
    (chainTo_mem hS) hr0 hb0 hbase
    haux hsv hbt hbtl hvbw hleaves htile h0 hfold
  exact ⟨m, y', h1, (Sem.Refines.mem hMM).trans h2⟩

end

end GoFV.Proof.MemCombine

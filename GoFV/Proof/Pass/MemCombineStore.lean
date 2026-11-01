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
  split at h <;> (repeat' split at h) <;> simp_all

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

theorem storeRecs_rel {tabs : Tables} {D : ID → Option Value} :
    ∀ {S : List ID} {recs : List StoreRec}, storeRecs tabs D S = some recs →
      List.Forall₂ (StRel tabs D) S recs
  | [], recs, h => by simp [storeRecs] at h; subst h; exact .nil
  | s :: S, recs, h => by
    unfold storeRecs at h
    rw [List.mapM_cons] at h
    cases hs : D s with
    | none => simp [hs] at h
    | some v =>
      by_cases h3 : v.args.size = 3
      · cases hb : storedBytes tabs D v with
        | none => simp [hs, h3, hb] at h
        | some r =>
          cases hr : List.mapM (fun s => (D s).bind fun sv =>
              if sv.args.size == 3 then (storedBytes tabs D sv).map fun r =>
                (sv.args[0]!, splitP tabs D 64 sv.args[0]! none 0, r) else none) S with
          | none => simp [hs, h3, hb, hr] at h
          | some rs =>
            simp [hs, h3, hb, hr] at h
            subst h
            exact .cons ⟨v, hs, h3, rfl, rfl, hb⟩ (storeRecs_rel hr)
      · simp [hs, h3] at h

theorem forall₂_mem {α β : Type} {Rel : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ Rel l l' → ∀ a ∈ l, ∃ b ∈ l', Rel a b
  | _, _, .nil, _, h => absurd h List.not_mem_nil
  | _, _, .cons hr t, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨b, hb, hr'⟩ := forall₂_mem t a h
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
        cases hs : symOf tabs D false srcFuel v.args[1]! with
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
              exact ⟨by simp [hlen], .inl fun t htl => by simp [hlen] at htl ⊢; omega⟩
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
              cases w0 : w <;> simp [w0, Width.bytes] at h8 <;> simp [Val.hasTy, w0] at hty
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
          rw [den_term hx (by rw [hc.1]; rfl) (by rw [hc.1]; rfl), hc.1, ht]
          refine ⟨rfl, .inr ⟨_, rfl, fun l hl => by cases hl, fun t htl => ?_⟩⟩
          simp at htl; subst htl
          simp [semL, SB.sem, evalPure, Conv.constBool, Val.retype, encode]
      · cases hsb
    · cases hsb

section
variable {tabs : Tables} {f g : Func} {R : Array Bool} {ce ce' : CheckEnv}
  (hwf : WF ce f) (hwg : WF ce' g) (K : McFacts tabs f g R)
include hwf hwg K

/-- **A combined store** writes a memory refining the one its chain of stores wrote. -/
theorem store_chgRef {x : ID} {u w : Value} (hu : f.value? x = some u)
    (hs : storeOK tabs f g (relMarks f g R) x u w = true) :
    ChgRefP f.value? tabs u (listedDefs g) w := by
  sorry

end

end GoFV.Proof.MemCombine

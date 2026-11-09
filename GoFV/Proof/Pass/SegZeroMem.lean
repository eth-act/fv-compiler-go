import GoFV.Proof.MemRefine
import GoFV.Proof.Pass.MemCombineBytes

variable [GoFV.SSA.Sem.Addrs]

/-!
# Segments: stores tiling a zeroed region (issue #151)

`generic.rules` drops a `Zero [n] p mem` under stores that overwrite all of its bytes
(`Store op1 d1 (Store op2 d2 (Store op3 d3 (Zero [n] p mem)))` with the stores tiling `[0, n)`
becomes the same stores over `mem`). `writes P m ws` applies stores `(offset, bytes)` at
`P + offset` in order; `Tiles 0 n ws` says they tile `[0, n)`. Over a zeroed region they give
exactly the memory they give over the original one (`writes_over_zero_eq`: the zero write is
valid, so every store is, and every zero byte is overwritten), and hence a refinement of the
original memory gives a refinement of the result (`writes_over_zero`).
-/

namespace GoFV.Proof.Seg

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof.MemCombine GoFV.Proof.CSE.Mem GoFV.Proof.DSE

/-- Writes `ws` (offset, bytes) at `P + offset`, in order. -/
def writes (P : Ptr) : Mem → List (Nat × Array Byte) → Option Mem
  | m, [] => some m
  | m, (o, bs) :: ws => (m.write (P.add (BitVec.ofNat 64 o)) bs).bind (writes P · ws)

/-- `ws` tiles `[lo, n)` with consecutive non-empty pieces in increasing order. -/
def Tiles : Nat → Nat → List (Nat × Array Byte) → Prop
  | lo, n, [] => lo = n
  | lo, n, (o, bs) :: ws => o = lo ∧ 0 < bs.size ∧ Tiles (lo + bs.size) n ws

/-- `writes` is memcombine's tiling fold. -/
theorem writes_eq_foldlM (P : Ptr) (ws : List (Nat × Array Byte)) :
    ∀ m : Mem, writes P m ws = ws.foldlM (tileStep P) m := by
  induction ws with
  | nil => intro m; rfl
  | cons p ws ih =>
    intro m
    obtain ⟨o, bs⟩ := p
    simp only [writes, List.foldlM_cons, ih]
    rfl

/-- **Refinement through writes:** the same writes over a refining memory succeed and refine. -/
theorem writes_mono {P : Ptr} : ∀ {m m' W : Mem} {ws : List (Nat × Array Byte)},
    Mem.Refines m m' → writes P m ws = some W → ∃ W', writes P m' ws = some W' ∧ Mem.Refines W W'
  | _, _, _, [], hm, hw => by cases hw; exact ⟨_, rfl, hm⟩
  | m, m', W, (o, bs) :: ws, hm, hw => by
    cases h1 : m.write (P.add (BitVec.ofNat 64 o)) bs with
    | none => rw [writes, h1] at hw; cases hw
    | some m1 =>
      rw [writes, h1] at hw
      obtain ⟨m1', h1', hr⟩ := hm.write (BytesRefineA.refl bs) h1
      obtain ⟨W', hw', hW⟩ := writes_mono hr hw
      exact ⟨W', by rw [writes, h1']; exact hw', hW⟩

/-! ## Tilings -/

theorem Tiles.bounds : ∀ {lo n : Nat} {ws : List (Nat × Array Byte)}, Tiles lo n ws →
    lo ≤ n ∧ ∀ p ∈ ws, lo ≤ p.1 ∧ p.1 + p.2.size ≤ n
  | lo, n, [], h => by
    have h' : lo = n := h
    exact ⟨by omega, fun _ hp => absurd hp List.not_mem_nil⟩
  | lo, n, (o, bs) :: ws, ⟨ho, _, ht⟩ => by
    obtain ⟨h1, h2⟩ := Tiles.bounds ht
    refine ⟨by omega, fun p hp => ?_⟩
    rcases List.mem_cons.1 hp with rfl | hp
    · simp only; omega
    · have := h2 p hp; omega

theorem Tiles.pairwise : ∀ {lo n : Nat} {ws : List (Nat × Array Byte)}, Tiles lo n ws →
    ws.Pairwise fun p q => p.1 + p.2.size ≤ q.1 ∨ q.1 + q.2.size ≤ p.1
  | _, _, [], _ => List.Pairwise.nil
  | _, _, (_, _) :: _, ⟨ho, _, ht⟩ =>
    List.Pairwise.cons (fun q hq => Or.inl (by have := (Tiles.bounds ht).2 q hq; simp only; omega))
      (Tiles.pairwise ht)

theorem Tiles.cover : ∀ {lo n : Nat} {ws : List (Nat × Array Byte)}, Tiles lo n ws →
    ∀ k, lo ≤ k → k < n → ∃ p ∈ ws, p.1 ≤ k ∧ k < p.1 + p.2.size
  | lo, n, [], h, k, h1, h2 => by
    have h' : lo = n := h
    exact (by omega : False).elim
  | lo, n, (o, bs) :: ws, ⟨ho, _, ht⟩, k, h1, h2 => by
    by_cases hk : k < lo + bs.size
    · exact ⟨(o, bs), List.mem_cons_self, by simp only; omega, by simp only; omega⟩
    · obtain ⟨p, hp, hp1, hp2⟩ := Tiles.cover ht k (by omega) h2
      exact ⟨p, List.mem_cons_of_mem _ hp, hp1, hp2⟩

/-! ## Writes over a zeroed region -/

/-- Stores valid in block `Q.blk` of `m` all succeed. -/
private theorem fold_ok (Q : Ptr) : ∀ (ws : List (Nat × Array Byte)) (m : Mem) (a : Alloc),
    m.find? Q.blk = some a → a.writable = true →
    (∀ p ∈ ws, 0 < p.2.size → Q.blk.writableFrom ≤ tileOff Q p ∧
      tileOff Q p + p.2.size ≤ a.data.size ∧ tileOff Q p + p.2.size < 2 ^ 64 ∧
      Q.blk.endsInWindow (tileOff Q p + p.2.size) = true) →
    ∃ mr, ws.foldlM (tileStep Q) m = some mr
  | [], m, _, _, _, _ => ⟨m, rfl⟩
  | p :: ws, m, a, hm, hwr, hv => by
    rw [List.foldlM_cons]
    by_cases hp : 0 < p.2.size
    · obtain ⟨h0, h1, h2, h3⟩ := hv p List.mem_cons_self hp
      have ho : (Q.add (BitVec.ofNat 64 p.1)).off.toNat = tileOff Q p := by
        rw [Ptr.add_off, toNat_add_ofNat]; rfl
      have hs := write_of_valid (p := Q.add (BitVec.ofNat 64 p.1)) (bs := p.2) hm hp hwr
        (by rw [Ptr.add_blk, ho]; exact h0) (by rw [ho]; exact h1) (by rw [ho]; exact h2)
        (by rw [Ptr.add_blk, ho]; exact h3)
      rw [Ptr.add_blk, ho] at hs
      change tileStep Q m p = _ at hs
      rw [hs]
      exact fold_ok Q ws _
        { a with data := (List.range p.2.size).foldl (fun d i => d.set! (tileOff Q p + i) p.2[i]!) a.data }
        (by rw [find?_set, ite_eq_left rfl]) hwr
        (fun q hq hq0 => by simpa only [foldl_set_size] using hv q (List.mem_cons_of_mem _ hq) hq0)
    · have hs : tileStep Q m p = some m := by
        unfold tileStep Mem.write
        simp [Array.isEmpty_iff_size_eq_zero.2 (by omega : p.2.size = 0)]
      rw [hs]
      exact fold_ok Q ws m a hm hwr fun q hq hq0 => hv q (List.mem_cons_of_mem _ hq) hq0

/-- **Stores tiling a zeroed region** give exactly the memory they give without the zeroing. -/
theorem writes_over_zero_eq {m Z W : Mem} {P : Ptr} {n : Nat} {ws : List (Nat × Array Byte)}
    (hz : m.write P (Array.replicate n (.b 0)) = some Z) (hw : writes P Z ws = some W)
    (ht : Tiles 0 n ws) : writes P m ws = some W := by
  have hb := ht.bounds
  by_cases hn : n = 0
  · subst hn
    rcases ws with _ | ⟨⟨o, bs⟩, ws⟩
    · have hZ : Z = m := by
        unfold Mem.write at hz
        simp only [Array.isEmpty_replicate, ite_true] at hz
        exact (Option.some.inj hz).symm
      subst hZ
      exact hw
    · have := hb.2 (o, bs) List.mem_cons_self
      have h0 : 0 < bs.size := ht.2.1
      exact (by simp only at this; omega : False).elim
  have hrs : (Array.replicate n (Byte.b 0)).size = n := Array.size_replicate
  obtain ⟨a0, ha0⟩ := write_find hz (by omega)
  obtain ⟨hZ, hv⟩ := write_spec ha0 hz
  obtain ⟨hwr, hv0, hv1, hv2, hv3⟩ := hv (by omega)
  rw [hrs] at hv1 hv2 hv3
  -- the zeroed data: unchanged outside `[off, off + n)`
  obtain ⟨Dz, rfl, hDzs, hDzu⟩ : ∃ Dz : Array Byte, Z = m.set P.blk { a0 with data := Dz } ∧
      Dz.size = a0.data.size ∧
      ∀ j, ¬ (P.off.toNat ≤ j ∧ j < P.off.toNat + n) → Dz[j]? = a0.data[j]? := by
    refine ⟨_, hZ, foldl_set_size _ _ _ _, fun j hj => ?_⟩
    rw [foldl_set_getElem? _ _ _ _ (Nat.le_refl _) (by rw [hrs]; exact hv1) j, hrs, ite_eq_right hj]
  have hnw : ∀ p ∈ ws, P.off.toNat + p.1 + p.2.size < 2 ^ 64 := fun p hp => by
    have := (hb.2 p hp).2; omega
  have hdis := ht.pairwise
  rw [writes_eq_foldlM] at hw ⊢
  obtain ⟨D, rfl, hDs, hDu, hDw⟩ := fold_data P ws _ W { a0 with data := Dz }
    (by rw [find?_set, ite_eq_left rfl]) hw hnw hdis
  have hoff : ∀ p ∈ ws, tileOff P p = P.off.toNat + p.1 := fun p hp => by
    have := hnw p hp
    unfold tileOff; rw [Nat.mod_eq_of_lt (by omega)]
  obtain ⟨W2, hW2⟩ := fold_ok P ws m a0 ha0 hwr fun p hp _ => by
    have := (hb.2 p hp).2
    rw [hoff p hp]
    exact ⟨by omega, by omega, by omega, endsInWindow_mono hv3 (by omega)⟩
  obtain ⟨D2, rfl, hD2s, hD2u, hD2w⟩ := fold_data P ws m W2 a0 ha0 hW2 hnw hdis
  rw [hW2, set_set]
  have hD : D = D2 := by
    apply Array.ext_getElem?
    intro j
    by_cases hj : ∃ p ∈ ws, P.off.toNat + p.1 ≤ j ∧ j < P.off.toNat + p.1 + p.2.size
    · obtain ⟨p, hp, h1, h2⟩ := hj
      have hj' : j = P.off.toNat + p.1 + (j - (P.off.toNat + p.1)) := by omega
      rw [hj', hDw p hp _ (by omega), hD2w p hp _ (by omega)]
    · have hj' : ∀ p ∈ ws, ¬ (P.off.toNat + p.1 ≤ j ∧ j < P.off.toNat + p.1 + p.2.size) :=
        fun p hp h => hj ⟨p, hp, h⟩
      rw [hDu j hj', hD2u j hj']
      refine hDzu j fun ⟨h1, h2⟩ => ?_
      obtain ⟨p, hp, hp1, hp2⟩ := ht.cover (j - P.off.toNat) (by omega) (by omega)
      exact hj' p hp ⟨by omega, by omega⟩
  rw [hD]

/-- **Stores tiling a zeroed region, refined:** the same stores over a refinement of the
original memory succeed and refine the result. -/
theorem writes_over_zero {m m' Z W : Mem} {P : Ptr} {n : Nat} {ws : List (Nat × Array Byte)}
    (hz : m.write P (Array.replicate n (.b 0)) = some Z) (hw : writes P Z ws = some W)
    (ht : Tiles 0 n ws) (hm : Mem.Refines m m') :
    ∃ W', writes P m' ws = some W' ∧ Mem.Refines W W' :=
  writes_mono hm (writes_over_zero_eq hz hw ht)

/-! ## Non-vacuity: a 16-byte heap allocation, zeroed, then two 8-byte stores -/

private def m0 : Mem := { blocks := #[(.heap 0, { data := Array.replicate 16 .poison })], nextHeap := 1 }
private def P0 : Ptr := ⟨.heap 0, 0⟩
private def ws0 : List (Nat × Array Byte) :=
  [(0, Array.replicate 8 (.b 1)), (8, Array.replicate 8 (.b 2))]

example : ∃ Z W, m0.write P0 (Array.replicate 16 (.b 0)) = some Z ∧ writes P0 Z ws0 = some W ∧
    Tiles 0 16 ws0 ∧ Mem.Refines m0 m0 := by
  have h : ((m0.write P0 (Array.replicate 16 (.b 0))).bind (writes P0 · ws0)).isSome = true := by
    decide +kernel
  obtain ⟨W, hW⟩ := Option.isSome_iff_exists.1 h
  cases hZ : m0.write P0 (Array.replicate 16 (.b 0)) with
  | none => rw [hZ] at hW; cases hW
  | some Z =>
    rw [hZ] at hW
    exact ⟨Z, W, rfl, hW, ⟨rfl, by decide, rfl, by decide, rfl⟩, Mem.Refines.refl _⟩

end GoFV.Proof.Seg

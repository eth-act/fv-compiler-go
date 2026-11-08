import GoFV.Proof.Pass.MemCombineBytes
import GoFV.SSA.Sem.RunL

variable [GoFV.SSA.Sem.Addrs]

/-!
# Disjoint writes commute (`pair`'s reversed adjacent stores)

`pair` merges two adjacent stores of one width `w` into a pair store even when the store at the
higher offset comes first. The two writes then happen in the other order; they commute because
their ranges are disjoint (`write_comm`). Two `symAddr`s at offsets `k` and `k + w` of one base
are in different blocks or `w` bytes apart (`symAddr_adj`): on a symbol or pointer base by the
offsets, on an integer base by `Ptr.ofAddr`'s windows (`ofAddr_adj`).
-/

namespace GoFV.Proof.MoveL

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof GoFV.Proof.DSE GoFV.Proof.CSE.Mem GoFV.Proof.MemCombine

/-! ## Writes -/

private theorem setL_comm {b b' : Blk} (a a' : Alloc) (hne : b ≠ b') :
    ∀ l : List (Blk × Alloc), (∃ e ∈ l, e.1 = b) →
      setL b a (setL b' a' l) = setL b' a' (setL b a l)
  | [], ⟨_, he, _⟩ => absurd he List.not_mem_nil
  | e :: l, ⟨e', he', hb⟩ => by
    by_cases h1 : e.1 = b
    · have h3 : (b == b') = false := by simp [hne]
      simp [setL, h1, h3]
    · have hl : ∃ e ∈ l, e.1 = b := by
        rcases List.mem_cons.1 he' with rfl | h
        · exact absurd hb h1
        · exact ⟨e', h, hb⟩
      by_cases h2 : e.1 = b'
      · have h4 : (b' == b) = false := by simp [hne.symm]
        simp [setL, h2, h4]
      · simp [setL, h1, h2, setL_comm a a' hne l hl]

/-- `Mem.set`s of two blocks commute when one of them has an allocation. -/
private theorem set_comm {m : Mem} {b b' : Blk} {a0 : Alloc} (a a' : Alloc) (hne : b ≠ b')
    (hf : m.find? b = some a0) : (m.set b' a').set b a = (m.set b a).set b' a' := by
  have hl : ∃ e ∈ m.blocks.toList, e.1 = b := by
    rw [find?_toList, Option.map_eq_some_iff] at hf
    obtain ⟨e, he, -⟩ := hf
    exact ⟨e, List.mem_of_find?_eq_some he, by simpa using List.find?_some he⟩
  exact Mem.ext' (by rw [set_toList, set_toList, set_toList, set_toList, setL_comm a a' hne _ hl])
    (by simp only [set_nextHeap]) (by simp only [set_nextAct])

/-- The byte loops of two writes to disjoint ranges commute. -/
private theorem fold_comm (op oq : Nat) (bp bq d : Array Byte) (hp : op + bp.size ≤ d.size)
    (hq : oq + bq.size ≤ d.size) (hd : op + bp.size ≤ oq ∨ oq + bq.size ≤ op) :
    (List.range bq.size).foldl (fun d i => d.set! (oq + i) bq[i]!)
        ((List.range bp.size).foldl (fun d i => d.set! (op + i) bp[i]!) d) =
      (List.range bp.size).foldl (fun d i => d.set! (op + i) bp[i]!)
        ((List.range bq.size).foldl (fun d i => d.set! (oq + i) bq[i]!) d) := by
  apply Array.ext_getElem?
  intro j
  rw [foldl_set_getElem? oq bq _ _ (Nat.le_refl _) (by rw [foldl_set_size]; exact hq),
    foldl_set_getElem? op bp _ _ (Nat.le_refl _) hp,
    foldl_set_getElem? op bp _ _ (Nat.le_refl _) (by rw [foldl_set_size]; exact hp),
    foldl_set_getElem? oq bq _ _ (Nat.le_refl _) hq]
  by_cases h1 : oq ≤ j ∧ j < oq + bq.size
  · have h2 : ¬(op ≤ j ∧ j < op + bp.size) := by omega
    simp only [h1, h2, and_self, ite_true, ite_false]
  · simp only [h1, ite_false]

/-- **Writes to disjoint ranges commute**: two writes that succeed in one order succeed in the
other with the same result. -/
theorem write_comm {m m1 m2 : Mem} {p q : Ptr} {bp bq : Array Byte}
    (h1 : m.write q bq = some m1) (h2 : m1.write p bp = some m2)
    (hd : p.blk ≠ q.blk ∨ p.off.toNat + bp.size ≤ q.off.toNat ∨
      q.off.toNat + bq.size ≤ p.off.toNat) :
    ∃ m1', m.write p bp = some m1' ∧ m1'.write q bq = some m2 := by
  by_cases hq0 : bq.size = 0
  · have he : bq.isEmpty = true := Array.isEmpty_iff_size_eq_zero.2 hq0
    have e1 : m1 = m := by unfold Mem.write at h1; simp only [he, ite_true] at h1; cases h1; rfl
    subst e1
    refine ⟨m2, h2, ?_⟩
    unfold Mem.write; simp [he]
  by_cases hp0 : bp.size = 0
  · have he : bp.isEmpty = true := Array.isEmpty_iff_size_eq_zero.2 hp0
    have e2 : m2 = m1 := by unfold Mem.write at h2; simp only [he, ite_true] at h2; cases h2; rfl
    subst e2
    refine ⟨m, ?_, h1⟩
    unfold Mem.write; simp [he]
  obtain ⟨aq, haq⟩ := write_find h1 (by omega)
  obtain ⟨e1, wq⟩ := write_spec haq h1
  obtain ⟨wq, hq1, hq2, hq3⟩ := wq (by omega)
  subst e1
  obtain ⟨ap, hap⟩ := write_find h2 (by omega)
  obtain ⟨e2, wp⟩ := write_spec hap h2
  obtain ⟨wp, hp1, hp2, hp3⟩ := wp (by omega)
  subst e2
  rw [find?_set] at hap
  by_cases hb : q.blk = p.blk
  · simp only [hb, ite_true] at hap
    cases hap
    rw [hb] at haq
    simp only at wp hp1
    rw [foldl_set_size] at hp1
    have hd' : p.off.toNat + bp.size ≤ q.off.toNat ∨ q.off.toNat + bq.size ≤ p.off.toNat := by
      rcases hd with hd | hd
      · exact absurd hb.symm hd
      · exact hd
    refine ⟨_, write_of_valid haq (by omega) wp hp1 hp2 hp3, ?_⟩
    rw [write_of_valid (a := { aq with data := ((List.range bp.size).foldl
        (fun d i => d.set! (p.off.toNat + i) bp[i]!) aq.data) }) (by rw [find?_set, hb]; simp)
        (by omega) wq (by rw [foldl_set_size]; exact hq1) hq2 (hb ▸ hq3)]
    rw [hb, set_set, set_set, fold_comm _ _ _ _ _ hp1 hq1 hd']
  · simp only [hb, ite_false] at hap
    refine ⟨_, write_of_valid hap (by omega) wp hp1 hp2 hp3, ?_⟩
    have hpq : p.blk ≠ q.blk := Ne.symm hb
    rw [write_of_valid (a := aq) (by rw [find?_set]; simp only [hpq, ite_false]; exact haq)
      (by omega) wq hq1 hq2 hq3]
    exact congrArg some (set_comm _ _ hb haq)

/-- A non-empty write that succeeds ends below `2^64`. -/
theorem write_end {m m' : Mem} {p : Ptr} {bs : Array Byte} (h : m.write p bs = some m')
    (hpos : 0 < bs.size) : p.off.toNat + bs.size < 2 ^ 64 := by
  obtain ⟨a, ha⟩ := write_find h hpos
  exact ((write_spec ha h).2 hpos).2.2.1

/-! ## Adjacent addresses -/

private theorem off_add (k : Int64) (w : Nat) :
    BitVec.ofInt 64 (k + Int64.ofNat w).toInt = BitVec.ofInt 64 k.toInt + BitVec.ofNat 64 w := by
  rw [← Int64.toInt_toBitVec, ← Int64.toInt_toBitVec, BitVec.ofInt_toInt, BitVec.ofInt_toInt,
    Int64.toBitVec_add]
  rfl

/-- The pointers at two concrete addresses `w` apart are in different blocks or `w` bytes apart
(both have their address, `Ptr.addr?_ofAddr`). -/
theorem ofAddr_adj (y : BitVec 64) {w : Nat} (hw : w < 2 ^ 22) :
    (Ptr.ofAddr y).blk ≠ (Ptr.ofAddr (y + BitVec.ofNat 64 w)).blk ∨
      (Ptr.ofAddr (y + BitVec.ofNat 64 w)).off = (Ptr.ofAddr y).off + BitVec.ofNat 64 w := by
  by_cases hb : (Ptr.ofAddr y).blk = (Ptr.ofAddr (y + BitVec.ofNat 64 w)).blk
  · refine .inr ?_
    have h1 := Ptr.addr?_ofAddr y
    have h2 := Ptr.addr?_ofAddr (y + BitVec.ofNat 64 w)
    unfold Ptr.addr? at h1 h2
    rw [← hb] at h2
    cases hn : (Ptr.ofAddr y).blk.base? with
    | none => rw [hn] at h1; cases h1
    | some n =>
      rw [hn] at h1 h2
      simp only [Option.map_some, Option.some.injEq] at h1 h2
      rw [← h1] at h2
      bv_omega
  · exact .inl hb

/-- **Adjacent `symAddr`s**: the addresses at offsets `k` and `k + w` of one base are in
different blocks or `w` bytes apart. -/
theorem symAddr_adj {ctx : Ctx} {v : Value} {a : Val} {P Q : Ptr} {w : Nat} (hw : w < 2 ^ 22)
    (hP : symAddr ctx v a = some P)
    (hQ : symAddr ctx { v with auxInt := v.auxInt + Int64.ofNat w } a = some Q) :
    P.blk ≠ Q.blk ∨ Q.off = P.off + BitVec.ofNat 64 w := by
  unfold symAddr at hP hQ
  dsimp only at hP hQ
  rw [off_add] at hQ
  split at hP
  · rename_i n hn
    rw [hn] at hQ
    dsimp only at hQ
    split at hP
    · rename_i hk; rw [hk] at hQ; cases hP; cases hQ; exact .inr rfl
    · rename_i hk; rw [hk] at hQ; cases hP; cases hQ; exact .inr rfl
    · cases hP
  · rename_i hn
    rw [hn] at hQ
    dsimp only at hQ
    unfold Arm64.addr at hP hQ
    cases a with
    | ptr p =>
      cases hP; cases hQ; right
      simp only [Ptr.add, BitVec.add_assoc]
    | _ =>
      simp only [Option.map_eq_some_iff] at hP hQ
      obtain ⟨x, hx, rfl⟩ := hP
      obtain ⟨x', hx', rfl⟩ := hQ
      rw [hx] at hx'; cases hx'
      rw [← BitVec.add_assoc]
      exact ofAddr_adj _ hw

/-- **Adjacent writes commute**: writes of `w` bytes at adjacent `symAddr`s `Q` (offset
`k + w`) and then `P` (offset `k`) give what the writes at `P` and then `Q` give. -/
theorem write_adj_comm {ctx : Ctx} {v : Value} {a : Val} {P Q : Ptr} {w : Nat} (hw0 : 0 < w)
    (hw : w < 2 ^ 22)
    (hP : symAddr ctx v a = some P)
    (hQ : symAddr ctx { v with auxInt := v.auxInt + Int64.ofNat w } a = some Q)
    {m m1 m2 : Mem} {bp bq : Array Byte} (hbp : bp.size = w) (hbq : bq.size = w)
    (h1 : m.write Q bq = some m1) (h2 : m1.write P bp = some m2) :
    ∃ m1', m.write P bp = some m1' ∧ m1'.write Q bq = some m2 := by
  refine write_comm h1 h2 ?_
  rcases symAddr_adj hw hP hQ with hb | ho
  · exact .inl hb
  · have he := write_end h2 (by omega)
    refine .inr (.inl ?_)
    rw [ho, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := w) (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega

end GoFV.Proof.MoveL

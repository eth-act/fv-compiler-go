import GoFV.Proof.Gen.Value
import GoFV.Arm64.State

/-!
# Loads and stores of slice G1 under `MemInj` (`docs/plans/proofs3.md` §3)

Under `AddrAgree` the pointer words `MemInj` allows (`BytesRel`'s `W`) hold their own Phase 1
address, so every byte of a live block is related to its machine byte by `ByteRel`
(`memInj_byteRel`). An 8-byte load (`Mem.load` at `int64`, `MOVD off(Rn), Rd`) then reads a value
related to the machine word (`lo_load`); an 8-byte store (`Mem.write` of `storeBytes 8`,
`MOVD Rs, off(Rn)`) keeps `MemInj` (`memInj_store`) when the block keys are distinct (otherwise a
second entry of the written block would keep its old bytes while the machine's change).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64

variable {ι : Blk → Option (BitVec 64)}

/-- The block keys of a memory are distinct. -/
def KeysNodup (m : Mem) : Prop := (m.blocks.toList.map (·.1)).Nodup

/-! ## Bytes of the machine memory and of Phase 1 encodings -/

private theorem extract_extract (V : BitVec n) (j k : Nat) (h : j < k) :
    (V.extractLsb' 8 (8 * k)).extractLsb' (8 * j) 8 = V.extractLsb' (8 * (j + 1)) 8 := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_extractLsb']
  have : 8 * j + i < 8 * k := by omega
  simp only [this, decide_true, Bool.true_and]
  congr 1; omega

theorem addr_off (a o : BitVec 64) (j : Nat) :
    a + BitVec.ofNat 64 (o.toNat + j) = a + o + BitVec.ofNat 64 j := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem addr_succ (A : BitVec 64) (j : Nat) :
    A + 1 + BitVec.ofNat 64 j = A + BitVec.ofNat 64 (j + 1) := by
  rw [BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega

private theorem readMem_succ_toNat (mm : Memory) (A : BitVec 64) (k : Nat) :
    (readMem mm A (k + 1)).toNat = (readMem mm (A + 1) k).toNat * 256 + (mm A).toNat := by
  simp only [readMem, BitVec.toNat_cast, BitVec.toNat_append]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (mm A).isLt, Nat.shiftLeft_eq]

theorem readMem_byte (mm : Memory) : ∀ (k : Nat) (A : BitVec 64) (j : Nat), j < k →
    (readMem mm A k).toNat / 256 ^ j % 256 = (mm (A + BitVec.ofNat 64 j)).toNat
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, A, 0, _ => by
    have := (mm A).isLt
    rw [readMem_succ_toNat]; simp only [Nat.pow_zero, Nat.div_one, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero]; omega
  | k + 1, A, j + 1, h => by
    have := (mm A).isLt
    rw [readMem_succ_toNat, Nat.pow_succ', ← Nat.div_div_eq_div_mul,
      show ((readMem mm (A + 1) k).toNat * 256 + (mm A).toNat) / 256 = (readMem mm (A + 1) k).toNat
        by omega, readMem_byte mm k (A + 1) j (by omega), addr_succ]

theorem readMem_of_bytes (mm : Memory) : ∀ (k : Nat) (A : BitVec 64) (n : Nat), n < 256 ^ k →
    (∀ j, j < k → (mm (A + BitVec.ofNat 64 j)).toNat = n / 256 ^ j % 256) →
    (readMem mm A k).toNat = n
  | 0, _, n, hn, _ => by simp only [Nat.pow_zero] at hn; rw [show n = 0 by omega]; rfl
  | k + 1, A, n, hn, h => by
    have h0 := h 0 (by omega)
    simp only [Nat.pow_zero, Nat.div_one, BitVec.add_zero] at h0
    rw [readMem_succ_toNat, readMem_of_bytes mm k (A + 1) (n / 256) ?_ ?_, h0]
    · omega
    · rw [Nat.pow_succ] at hn; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hn)
    · intro j hj
      rw [addr_succ, h (j + 1) (by omega), Nat.pow_succ', Nat.div_div_eq_div_mul]

theorem writeMem_other : ∀ (k : Nat) (mm : Memory) (A : BitVec 64) (V : BitVec (8 * k))
    (y : BitVec 64), (∀ j, j < k → y ≠ A + BitVec.ofNat 64 j) → writeMem mm A k V y = mm y
  | 0, _, _, _, _, _ => rfl
  | k + 1, mm, A, V, y, h => by
    simp only [writeMem]
    rw [writeMem_other k _ (A + 1) _ y (fun j hj => by rw [addr_succ]; exact h (j + 1) (by omega))]
    have := h 0 (by omega)
    simp only [BitVec.add_zero] at this
    simp only [this, ↓reduceIte]

theorem writeMem_at : ∀ (k : Nat) (mm : Memory) (A : BitVec 64) (V : BitVec (8 * k))
    (j : Nat), j < k → k ≤ 8 → writeMem mm A k V (A + BitVec.ofNat 64 j) = V.extractLsb' (8 * j) 8
  | 0, _, _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | k + 1, mm, A, V, 0, _, hk => by
    simp only [writeMem]
    rw [writeMem_other k _ (A + 1) _ _ (fun j hj => ?_)]
    · simp
    · rw [addr_succ]; intro he
      have := congrArg BitVec.toNat he
      simp [BitVec.toNat_add] at this; omega
  | k + 1, mm, A, V, j + 1, h, hk => by
    simp only [writeMem]
    rw [← addr_succ, writeMem_at k _ (A + 1) _ j (by omega) (by omega), extract_extract V j k (by omega)]

/-- `bytesNat?` on a list. -/
private def bnat : List Byte → Option Nat
  | [] => some 0
  | .b x :: l => (bnat l).map (x.toNat + 256 * ·)
  | _ :: _ => none

private theorem bytesNat?_eq (bs : Array Byte) : bytesNat? bs = bnat bs.toList := by
  unfold bytesNat?
  rw [← Array.foldr_toList]
  induction bs.toList with
  | nil => rfl
  | cons c l ih =>
    simp only [List.foldr_cons, ih]
    cases c <;> simp only [bnat]
    cases bnat l <;> rfl

private theorem bnat_some : ∀ (l : List Byte) (n : Nat), bnat l = some n →
    n < 256 ^ l.length ∧ ∀ j (hj : j < l.length), l[j] = .b (BitVec.ofNat 8 (n / 256 ^ j))
  | [], n, h => by
    simp only [bnat, Option.some.injEq] at h; subst h
    exact ⟨by simp, fun j hj => absurd hj (by simp)⟩
  | .b x :: l, n, h => by
    simp only [bnat, Option.map_eq_some_iff] at h
    obtain ⟨n', hn', rfl⟩ := h
    obtain ⟨h1, h2⟩ := bnat_some l n' hn'
    have := x.isLt
    refine ⟨?_, fun j hj => ?_⟩
    · simp only [List.length_cons, Nat.pow_succ]; omega
    · cases j with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.pow_zero, Nat.div_one, Byte.b.injEq]
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
      | succ j =>
        simp only [List.getElem_cons_succ, List.length_cons] at hj ⊢
        rw [h2 j (by omega), Nat.pow_succ', ← Nat.div_div_eq_div_mul,
          show (x.toNat + 256 * n') / 256 = n' by omega]
  | .frag _ _ :: _, _, h => by simp [bnat] at h
  | .poison :: _, _, h => by simp [bnat] at h

private theorem bytesPtr?_some {bs : Array Byte} {q : Ptr} (h : bytesPtr? bs = some q) :
    bs.size = 8 ∧ ∀ j (hj : j < bs.size), bs[j] = .frag q j := by
  unfold bytesPtr? at h
  split at h
  · rename_i p hp
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h; subst h
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hc
      refine ⟨hc.1, fun j hj => ?_⟩
      have := hc.2 j (by omega)
      rw [Array.getElem?_eq_getElem hj] at this
      exact Option.some.inj this
    · cases h
  · cases h

/-- 8 bytes related to the machine bytes at `A` decode (as an `int64`) to a value related to the
machine word there. -/
private theorem lo_decode (hA : AddrAgree ι) {mm : Memory} {A : BitVec 64} {bs : Array Byte}
    (hs : bs.size = 8) (hb : ∀ j (hj : j < bs.size), ByteRel ι bs[j] (mm (A + BitVec.ofNat 64 j))) :
    Lo ι 64 (decodeInt .w64 bs) ((readMem mm A 8).setWidth 64) := by
  unfold decodeInt
  cases hn : bytesNat? bs with
  | some n =>
    rw [bytesNat?_eq] at hn
    obtain ⟨h1, h2⟩ := bnat_some _ n hn
    simp only [Array.length_toList, hs] at h1 h2
    have hr : (readMem mm A 8).toNat = n := by
      refine readMem_of_bytes mm 8 A n h1 fun j hj => ?_
      have := hb j (by omega)
      rw [← Array.getElem_toList, h2 j (by simpa [hs] using hj)] at this
      simp only [ByteRel] at this
      rw [← this, BitVec.toNat_ofNat]
    show (BitVec.ofNat 64 n).setWidth 64 = ((readMem mm A 8).setWidth 64).setWidth 64
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, hr]
  | none =>
    cases hq : bytesPtr? bs with
    | none => trivial
    | some q =>
      obtain ⟨-, hq⟩ := bytesPtr?_some hq
      have h0 := hb 0 (by omega)
      rw [hq] at h0
      obtain ⟨aq, haq, -⟩ := h0
      have hr : (readMem mm A 8).toNat = (aq + q.off).toNat := by
        refine readMem_of_bytes mm 8 A _ (by have := (aq + q.off).isLt; simpa using this)
          fun j hj => ?_
        have := hb j (by omega)
        rw [hq] at this
        obtain ⟨aq', haq', he⟩ := this
        rw [haq] at haq'; cases haq'
        rw [he, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_mul]
      have hp : PtrRel ι q ((readMem mm A 8).setWidth 64) := by
        refine ⟨aq, haq, ?_⟩
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_setWidth, hr, Nat.mod_eq_of_lt (aq + q.off).isLt]
      show Lo ι 64 q.word _
      unfold Ptr.word
      split
      · rename_i ad hc had
        show ad.setWidth 64 = _
        rw [ptrRel_addr hA hp had (notTemp_of_convertible hc)]
      · exact Or.inr hp

private theorem find?_mem {m : Mem} {b : Blk} {al : Alloc} (h : m.find? b = some al) :
    (b, al) ∈ m.blocks := by
  unfold Mem.find? at h
  cases hf : m.blocks.find? (·.1 == b) with
  | none => rw [hf] at h; cases h
  | some e =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    have h1 := Array.mem_of_find?_eq_some hf
    have h2 := Array.find?_some hf
    obtain ⟨b', al'⟩ := e
    simp only [beq_iff_eq] at h2
    subst h2
    exact h1

private theorem read_some {m : Mem} {p : Ptr} {n : Nat} {bs : Array Byte} (hn : 0 < n)
    (h : m.read p n = some bs) : ∃ al, m.find? p.blk = some al ∧ p.off.toNat + n ≤ al.data.size ∧
      bs = al.data.extract p.off.toNat (p.off.toNat + n) := by
  unfold Mem.read at h
  cases hf : m.find? p.blk with
  | none => simp [hf] at h; omega
  | some al =>
    simp [hf] at h
    have hn0 : n ≠ 0 := by omega
    simp only [hn0, ↓reduceIte] at h
    split at h
    · rename_i hc
      cases h
      exact ⟨al, rfl, hc.1, rfl⟩
    · cases h

private theorem canWrite_some {m : Mem} {p : Ptr} {n : Nat} (hn : 0 < n)
    (h : m.canWrite p n = true) : ∃ al, m.find? p.blk = some al ∧ p.off.toNat + n ≤ al.data.size := by
  unfold Mem.canWrite at h
  cases hf : m.find? p.blk with
  | none => simp [hf] at h; omega
  | some al =>
    simp [hf] at h
    rcases h with h | ⟨⟨⟨-, h⟩, -⟩, -⟩
    · omega
    · exact ⟨al, rfl, h⟩

/-! ## The lemmas -/

/-- Under `AddrAgree`, every byte of a live block is related to its machine byte. -/
theorem memInj_byteRel (hA : AddrAgree ι) {m : Mem} {mm : Memory} (h : MemInj ι m mm)
    {b : Blk} {al : Alloc} {a : BitVec 64} (hb : (b, al) ∈ m.blocks) (ha : ι b = some a)
    {i : Nat} (hi : i < al.data.size) : ByteRel ι al.data[i] (mm (a + BitVec.ofNat 64 i)) := by
  obtain ⟨W, hW⟩ := h.bytes
  obtain ⟨hw1, -, hw3⟩ := hW b al a hb ha
  by_cases hin : ∃ o, W b o ∧ o ≤ i ∧ i < o + 8
  · obtain ⟨o, ho, hoi, hio⟩ := hin
    obtain ⟨q, hq, hrel⟩ := hw1 o ho
    unfold ptrWordAt? at hq
    split at hq
    · rename_i hsz
      split at hq
      · rename_i n hn
        have hq' : Ptr.ofAddr (BitVec.ofNat 64 n) = q := by
          by_cases hnil : (Ptr.ofAddr (BitVec.ofNat 64 n)).blk = .nil
          · simp [hnil] at hq
          · simpa [hnil] using hq
        subst hq'
        have hw := ptrRel_addr hA hrel (Ptr.addr?_ofAddr _) (notTemp_ofAddr _)
        rw [bytesNat?_eq] at hn
        obtain ⟨h1, h2⟩ := bnat_some _ n hn
        have hlen : (al.data.extract o (o + 8)).toList.length = 8 := by simp; omega
        rw [hlen] at h1
        have hr : (readMem mm (a + BitVec.ofNat 64 o) 8).toNat = n := by
          have := congrArg BitVec.toNat hw
          simp only [memWord, BitVec.toNat_cast, BitVec.toNat_ofNat] at this
          rw [this]; exact Nat.mod_eq_of_lt (by simpa using h1)
        have he := h2 (i - o) (by omega)
        rw [Array.getElem_toList, Array.getElem_extract] at he
        simp only [Nat.add_sub_cancel' hoi] at he
        rw [he]
        show BitVec.ofNat 8 (n / 256 ^ (i - o)) = _
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, ← hr, readMem_byte mm 8 _ (i - o) (by omega), BitVec.add_assoc,
          BitVec.ofNat_add_ofNat, Nat.add_sub_cancel' hoi]
      · cases hq
    · cases hq
  · exact hw3 i hi fun o ho ⟨h1, h2⟩ => hin ⟨o, ho, h1, h2⟩

/-- The address of an access: a 64-bit base related to `X` (a pointer or a pointer word) moved
by `off`, into a live block, is that block's injected address plus the offset; outside the nil
page when the access of `n > 0` bytes is valid. -/
theorem addr_rel (hA : AddrAgree ι) {m : Mem} {mm : Memory} (h : MemInj ι m mm) {base : Val}
    {X off : BitVec 64} {p : Ptr} {n : Nat} (hx : ValRel ι base X) (hf : Fits 64 base)
    (hp : Arm64.addr base off = some p) (hn : 0 < n) (hv : m.canWrite p n = true ∨ (m.read p n).isSome) :
    ∃ a, ι p.blk = some a ∧ X + off = a + p.off ∧ nilPage (a + p.off) = false := by
  obtain ⟨al, hfa, hsz⟩ : ∃ al, m.find? p.blk = some al ∧ p.off.toNat + n ≤ al.data.size := by
    rcases hv with hv | hv
    · exact canWrite_some hn hv
    · obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.1 hv
      obtain ⟨al, h1, h2, -⟩ := read_some hn hbs
      exact ⟨al, h1, h2⟩
  obtain ⟨a, ha, hlo, hhi⟩ := h.mapped _ _ (find?_mem hfa)
  refine ⟨a, ha, ?_, ?_⟩
  · cases base with
    | ptr q =>
      simp only [Arm64.addr, Option.some.injEq] at hp
      subst hp
      obtain ⟨aq, haq, rfl⟩ := hx
      simp only [Ptr.add] at ha ⊢
      rw [ha] at haq; cases haq
      rw [BitVec.add_assoc]
    | int w y =>
      cases w <;> simp [Fits, Width.bits] at hf
      have hX := valRel_i64 hA hx
      subst hX
      simp only [Arm64.addr, Arm64.reg, Option.map_some, Option.some.injEq, BitVec.setWidth_eq] at hp
      subst hp
      have hd := Ptr.addr?_ofAddr (X + off)
      unfold Ptr.addr? at hd
      cases hb : (Ptr.ofAddr (X + off)).blk.base? with
      | none => rw [hb] at hd; cases hd
      | some nb =>
        rw [hb] at hd
        simp only [Option.map_some, Option.some.injEq] at hd
        rw [hA _ _ _ hb ha (notTemp_ofAddr _), hd]
    | bool => simp [Fits] at hf
    | poison => simp [Arm64.addr, Arm64.reg] at hp
    | _ => simp [Fits] at hf
  · have h4 := hlo (by omega)
    simp only [nilPage, decide_eq_false_iff_not, Nat.not_lt]
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    omega

/-- An 8-byte load at a valid address reads a value related to the machine word there. -/
theorem lo_load (hA : AddrAgree ι) {m : Mem} {mm : Memory} (h : MemInj ι m mm) {p : Ptr}
    {a : BitVec 64} {bs : Array Byte} (ha : ι p.blk = some a) (hr : m.read p 8 = some bs) :
    Lo ι 64 (m.load (.int .w64) p) ((readMem mm (a + p.off) 8).setWidth 64) := by
  obtain ⟨al, hfa, hsz, hbs⟩ := read_some (by omega) hr
  have hmem := find?_mem hfa
  have hl : m.load (.int .w64) p = decodeInt .w64 (bs.extract 0 (0 + 8)) := by
    simp only [Mem.load, Ty.size, Width.bytes, Width.bits, Nat.reduceDiv, hr, decodeLoad, Sem.decode]
  rw [hl]
  subst hbs
  apply lo_decode hA
  · simp; omega
  · intro j hj
    have hj8 : j < 8 := by simp at hj; omega
    simp only [Array.getElem_extract]
    rw [← addr_off]
    have := memInj_byteRel hA h hmem ha (i := p.off.toNat + (0 + j)) (by omega)
    simpa using this

private theorem intBytes_rel (Xs : BitVec 64) (j : Nat) (hj : j < 8) :
    ByteRel ι (intBytes 8 Xs.toNat)[j]! (Xs.extractLsb' (8 * j) 8) := by
  rw [getElem!_pos _ _ (by simp [intBytes]; omega)]
  simp only [intBytes, Array.getElem_map, List.getElem_toArray, List.getElem_range, ByteRel]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

private theorem storeBytes_rel (hA : AddrAgree ι) {x : Val} {Xs : BitVec 64} (hx : ValRel ι x Xs)
    (hf : Fits 64 x ∨ Fits 1 x) : (Arm64.storeBytes 8 x).size = 8 ∧
    ∀ j, j < 8 → ByteRel ι (Arm64.storeBytes 8 x)[j]! (Xs.extractLsb' (8 * j) 8) := by
  cases x with
  | poison =>
    have : Arm64.storeBytes 8 .poison = Array.replicate 8 .poison := rfl
    rw [this]
    refine ⟨rfl, fun j hj => ?_⟩
    rw [getElem!_pos _ _ (by simp; omega), Array.getElem_replicate]
    trivial
  | int w y =>
    have hw : w = .w64 := by
      cases w <;> rcases hf with hf | hf <;> simp [Fits, Width.bits] at hf ⊢
    subst hw
    have hX := valRel_i64 hA hx
    subst hX
    have : Arm64.storeBytes 8 (.int .w64 Xs) = intBytes 8 Xs.toNat := by
      simp [Arm64.storeBytes, Arm64.reg]
    rw [this]
    exact ⟨by simp [intBytes], fun j hj => intBytes_rel Xs j hj⟩
  | bool b =>
    have : Arm64.storeBytes 8 (.bool b) = intBytes 8 Xs.toNat := by
      simp only [ValRel] at hx
      subst hx
      simp [Arm64.storeBytes, Arm64.reg]
    rw [this]
    exact ⟨by simp [intBytes], fun j hj => intBytes_rel Xs j hj⟩
  | ptr q =>
    obtain ⟨aq, haq, rfl⟩ := hx
    have : Arm64.storeBytes 8 (.ptr q) = ptrBytes q := rfl
    rw [this]
    refine ⟨by simp [ptrBytes], fun j hj => ?_⟩
    rw [getElem!_pos _ _ (by simp [ptrBytes]; omega)]
    simp only [ptrBytes, Array.getElem_map, List.getElem_toArray, List.getElem_range]
    exact ⟨aq, haq, rfl⟩
  | _ => rcases hf with hf | hf <;> simp [Fits] at hf

private theorem fold_set (bs : Array Byte) (off : Nat) : ∀ (n : Nat) (d : Array Byte),
    ((List.range n).foldl (fun d i => d.set! (off + i) bs[i]!) d).size = d.size ∧
    ∀ i, i < d.size → ((List.range n).foldl (fun d i => d.set! (off + i) bs[i]!) d)[i]? =
      if off ≤ i ∧ i < off + n then some bs[i - off]! else d[i]?
  | 0, d => ⟨rfl, fun i _ => by simp only [show ¬(off ≤ i ∧ i < off + 0) by omega, ↓reduceIte]; rfl⟩
  | n + 1, d => by
    obtain ⟨h1, h2⟩ := fold_set bs off n d
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
    refine ⟨h1, fun i hi => ?_⟩
    rw [Array.getElem?_setIfInBounds]
    by_cases he : off + n = i
    · subst he
      simp only [↓reduceIte, h1, hi, show off ≤ off + n ∧ off + n < off + (n + 1) by omega,
        Nat.add_sub_cancel_left, and_self]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false he), h2 i hi]
      split <;> split <;> first | rfl | (exfalso; omega)

private theorem nodup_unique : ∀ {l : List (Blk × Alloc)} {k : Blk} {v w : Alloc},
    (l.map (·.1)).Nodup → (k, v) ∈ l → (k, w) ∈ l → v = w
  | [], _, _, _, _, h, _ => by cases h
  | e :: l, k, v, w, hn, hv, hw => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 hv with hv' | hv' <;> rcases List.mem_cons.1 hw with hw' | hw'
    · subst hv'; cases hw'; rfl
    · subst hv'; exact absurd (List.mem_map.2 ⟨(k, w), hw', rfl⟩ : k ∈ l.map (·.1)) hn.1
    · subst hw'; exact absurd (List.mem_map.2 ⟨(k, v), hv', rfl⟩ : k ∈ l.map (·.1)) hn.1
    · exact nodup_unique hn.2 hv' hw'

/-- An 8-byte store of a 64-bit or boolean register content related to `Xs` keeps `MemInj` with
the machine's `writeMem` of `Xs`, and the keys distinct; the blocks keep their sizes, and the
machine bytes change only in the 8 bytes of the access, inside the window of its block. -/
theorem memInj_store (hA : AddrAgree ι) {m m' : Mem} {mm : Memory} (h : MemInj ι m mm)
    (hk : KeysNodup m) {p : Ptr} {a : BitVec 64} {x : Val} {Xs : BitVec 64}
    (ha : ι p.blk = some a) (hx : ValRel ι x Xs) (hf : Fits 64 x ∨ Fits 1 x)
    (hw : m.write p (Arm64.storeBytes 8 x) = some m') :
    MemInj ι m' (writeMem mm (a + p.off) 8 (BitVec.ofNat (8 * 8) (Xs.toNat % 2 ^ (8 * 8)))) ∧
      KeysNodup m' ∧
      (∀ b al2, (b, al2) ∈ m'.blocks → ∃ al1, (b, al1) ∈ m.blocks ∧ al1.data.size = al2.data.size) ∧
      ∃ al, (p.blk, al) ∈ m.blocks ∧ p.off.toNat + 8 ≤ al.data.size ∧
        ∀ y : BitVec 64, (∀ j, j < 8 → y.toNat ≠ a.toNat + p.off.toNat + j) →
          writeMem mm (a + p.off) 8 (BitVec.ofNat (8 * 8) (Xs.toNat % 2 ^ (8 * 8))) y = mm y := by
  obtain ⟨hsz, hbyte⟩ := storeBytes_rel hA hx hf
  generalize Arm64.storeBytes 8 x = bsW at hsz hbyte hw
  unfold Mem.write at hw
  have hne : bsW.isEmpty = false := by simp [Array.isEmpty, hsz]
  simp only [hne, Bool.false_eq_true, ↓reduceIte] at hw
  cases hfa : m.find? p.blk with
  | none => simp [hfa] at hw
  | some al =>
  simp only [hfa, hsz, Option.bind_eq_bind, Option.bind_some] at hw
  split at hw
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    have hoff : p.off.toNat + 8 ≤ al.data.size := hc.1.1.2
    simp only [Option.some.injEq] at hw
    have hfs := fold_set bsW p.off.toNat 8 al.data
    generalize List.foldl (fun d i => d.set! (p.off.toNat + i) bsW[i]!) al.data (List.range 8) = D
      at hw hfs
    obtain ⟨hDsz, hDget⟩ := hfs
    have hmem := find?_mem hfa
    unfold Mem.set at hw
    cases hi : m.blocks.findIdx? (·.1 == p.blk) with
    | none =>
      have := Array.findIdx?_eq_none_iff.1 hi _ hmem
      simp at this
    | some idx =>
    rw [hi] at hw
    obtain ⟨hidx, hkey, -⟩ := Array.findIdx?_eq_some_iff_getElem.1 hi
    simp only [beq_iff_eq] at hkey
    generalize hal' : ({ data := D, writable := al.writable } : Alloc) = al' at hw
    have hm' : m'.blocks = m.blocks.set! idx (p.blk, al') := by rw [← hw]
    have hlist : m'.blocks.toList = m.blocks.toList.set idx (p.blk, al') := by
      rw [hm', Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
    have hk' : KeysNodup m' := by
      unfold KeysNodup at hk ⊢
      rw [hlist, List.map_set]
      have hl : idx < (m.blocks.toList.map (·.1)).length := by simp [hidx]
      have := List.set_getElem_self hl
      rw [List.getElem_map, Array.getElem_toList, hkey] at this
      rw [this]; exact hk
    have hnew : (p.blk, al') ∈ m'.blocks := by
      rw [Array.mem_def, hlist]
      have hl : idx < (m.blocks.toList.set idx (p.blk, al')).length := by simp [hidx]
      have := List.getElem_mem hl
      rwa [List.getElem_set_self] at this
    have hcases : ∀ b al2, (b, al2) ∈ m'.blocks →
        (b = p.blk ∧ al2 = al') ∨ (b ≠ p.blk ∧ (b, al2) ∈ m.blocks) := by
      intro b al2 hb
      by_cases hbp : b = p.blk
      · subst hbp
        exact Or.inl ⟨rfl, nodup_unique hk' (Array.mem_def.1 hb) (Array.mem_def.1 hnew)⟩
      · refine Or.inr ⟨hbp, ?_⟩
        rw [Array.mem_def, hlist] at hb
        rcases List.mem_or_eq_of_mem_set hb with hb | hb
        · exact Array.mem_def.2 hb
        · exact absurd (congrArg Prod.fst hb) hbp
    subst hal'
    obtain ⟨a0, ha0, hlo, hhi⟩ := h.mapped _ _ hmem
    obtain rfl : a = a0 := Option.some.inj (ha.symm.trans ha0)
    have ha4 := hlo (by omega)
    have hV : (BitVec.ofNat (8 * 8) (Xs.toNat % 2 ^ (8 * 8)) : BitVec 64) = Xs := by
      apply BitVec.eq_of_toNat_eq; simpa using Xs.isLt
    rw [hV]
    have hback : ∀ b al2, (b, al2) ∈ m'.blocks →
        ∃ al1, (b, al1) ∈ m.blocks ∧ al1.data.size = al2.data.size := by
      intro b al2 hb
      rcases hcases b al2 hb with ⟨rfl, rfl⟩ | ⟨-, hb⟩
      · exact ⟨al, hmem, hDsz.symm⟩
      · exact ⟨al2, hb, rfl⟩
    have hout : ∀ y : BitVec 64, (∀ j, j < 8 → y.toNat ≠ a.toNat + p.off.toNat + j) →
        writeMem mm (a + p.off) 8 Xs y = mm y := by
      intro y hy
      apply writeMem_other
      intro j hj he
      apply hy j hj
      rw [he]; simp [BitVec.toNat_add]; omega
    refine ⟨⟨h.nil, ?_, ?_, ⟨fun _ _ => False, ?_⟩⟩, hk', hback, al, hmem, hoff, hout⟩
    · intro b al2 hb
      obtain ⟨al1, hb1, hs⟩ := hback b al2 hb
      rw [← hs]; exact h.mapped b al1 hb1
    · intro b al2 b' al2' a2 a2' hb hb' hne h1 h2
      obtain ⟨al1, hb1, hs⟩ := hback b al2 hb
      obtain ⟨al1', hb1', hs'⟩ := hback b' al2' hb'
      rw [← hs, ← hs']; exact h.inj b al1 b' al1' a2 a2' hb1 hb1' hne h1 h2
    · intro b al2 a2 hb hι
      refine ⟨fun o ho => ho.elim, fun o _ ho => ho.elim, fun i hi _ => ?_⟩
      rcases hcases b al2 hb with ⟨rfl, rfl⟩ | ⟨hne, hb⟩
      · obtain rfl : a = a2 := Option.some.inj (ha.symm.trans hι)
        have hiD : i < al.data.size := by rw [← hDsz]; exact hi
        have hg := hDget i hiD
        rw [Array.getElem?_eq_getElem hi] at hg
        show ByteRel ι D[i] _
        by_cases hin : p.off.toNat ≤ i ∧ i < p.off.toNat + 8
        · rw [ite_eq_left hin] at hg
          rw [Option.some.inj hg, show a + BitVec.ofNat 64 i =
              a + p.off + BitVec.ofNat 64 (i - p.off.toNat) by rw [← addr_off, Nat.add_sub_cancel' hin.1],
            writeMem_at 8 mm _ Xs _ (by omega) (Nat.le_refl 8)]
          exact hbyte _ (by omega)
        · rw [ite_eq_right hin, Array.getElem?_eq_getElem hiD] at hg
          rw [Option.some.inj hg, hout _ ?_]
          · exact memInj_byteRel hA h hmem ha hiD
          · intro j hj; simp [BitVec.toNat_add]; omega
      · obtain ⟨a2', h2', -, hhi2⟩ := h.mapped _ _ hb
        obtain rfl : a2 = a2' := Option.some.inj (hι.symm.trans h2')
        have := h.inj b al2 p.blk al a2 a hb hmem hne hι ha
        rw [hout _ ?_]
        · exact memInj_byteRel hA h hb hι hi
        · intro j hj; simp [BitVec.toNat_add]; omega
  · cases hw

end GoFV.Proof.Gen

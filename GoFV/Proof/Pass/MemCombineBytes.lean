import GoFV.Opt.MemCombine.Sym
import GoFV.Proof.Pass.DSEMem

/-!
# memcombine: bytes of integers and of memory (issue #35)

The facts the proof of memcombine's checker (`GoFV.Opt.MemCombine.Check`) reads its symbolic
bytes with.

* Integers by bytes (`byteOf`): an integer is determined by its bytes (`bitvec_eq_of_bytes`);
  the bytes of `|||`, `<<<`/`>>>` by multiples of 8, `setWidth`, `bswapNat` and of constants
  (`litBytes`); `decodeInt` of concrete bytes and `encode` of an integer by bytes.
* Memory: adjacent reads concatenate (`read_append`), a read's sub-range reads its slice
  (`read_extract`), reads covering a range make the whole range readable (`read_cover`), and
  writes tiling a range are one write of the tiled bytes (`write_tiling`).
-/

namespace GoFV.Proof.MemCombine

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.MemCombine.Check GoFV.Proof.CSE.Mem GoFV.Proof.DSE

/-! ## Bytes by bits -/

theorem byteOf_getLsbD (x k i : Nat) :
    (byteOf x k).getLsbD i = (decide (i < 8) && x.testBit (8 * k + i)) := by
  rw [byteOf, BitVec.getLsbD_ofNat, Nat.testBit_div_two_pow, Nat.add_comm i]

/-- Two bytes are equal if their bits are. -/
theorem byteOf_ext {x y k l : Nat} (h : ∀ i < 8, x.testBit (8 * k + i) = y.testBit (8 * l + i)) :
    byteOf x k = byteOf y l := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [byteOf_getLsbD, byteOf_getLsbD, h i hi]

theorem byteOf_ext_iff {x y k l : Nat} :
    byteOf x k = byteOf y l ↔ ∀ i < 8, x.testBit (8 * k + i) = y.testBit (8 * l + i) := by
  refine ⟨fun h i hi => ?_, byteOf_ext⟩
  have := congrArg (BitVec.getLsbD · i) h
  simp only [byteOf_getLsbD, hi, decide_true, Bool.true_and] at this
  exact this

theorem byteOf_zero_of_bits {x k : Nat} (h : ∀ i < 8, x.testBit (8 * k + i) = false) :
    byteOf x k = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [byteOf_getLsbD, h i hi]
  simp

theorem testBit_byteOf {x k i : Nat} (hi : i < 8) : (byteOf x k).toNat.testBit i = x.testBit (8 * k + i) := by
  rw [BitVec.testBit_toNat, byteOf_getLsbD]
  simp [hi]

theorem width_bits_eq (w : Width) : w.bits = 8 * w.bytes := by
  cases w <;> rfl

/-! ## Integers by bytes -/

/-- Two `n`-bit vectors with the same bytes below `n` are equal. -/
theorem bitvec_eq_of_bytes' {n : Nat} {x y : BitVec n}
    (h : ∀ k, 8 * k < n → byteOf x.toNat k = byteOf y.toNat k) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hb := byteOf_ext_iff.1 (h (j / 8) (by omega)) (j % 8) (by omega)
  rw [← BitVec.testBit_toNat, ← BitVec.testBit_toNat]
  have hj' : 8 * (j / 8) + j % 8 = j := by omega
  rwa [hj'] at hb

theorem bitvec_eq_of_bytes {w : Width} {x y : BitVec w.bits}
    (h : ∀ k < w.bytes, byteOf x.toNat k = byteOf y.toNat k) : x = y :=
  bitvec_eq_of_bytes' fun k hk => h k (by have := width_bits_eq w; omega)

theorem byteOf_or {n : Nat} (x y : BitVec n) (k : Nat) :
    byteOf (x ||| y).toNat k = byteOf x.toNat k ||| byteOf y.toNat k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, byteOf_getLsbD, BitVec.toNat_or, Nat.testBit_or, hi,
    decide_true, Bool.true_and]

theorem byteOf_shl {n : Nat} (x : BitVec n) (j k : Nat) (hk : 8 * k < n) (h8 : n % 8 = 0) :
    byteOf (x <<< (8 * j)).toNat k = if k < j then 0 else byteOf x.toNat (k - j) := by
  split
  · apply byteOf_zero_of_bits
    intro i hi
    rw [BitVec.testBit_toNat, BitVec.getLsbD_shiftLeft]
    simp only [show 8 * k + i < 8 * j by omega, decide_true, Bool.not_true, Bool.and_false,
      Bool.false_and]
  · apply byteOf_ext
    intro i hi
    rw [BitVec.testBit_toNat, BitVec.testBit_toNat, BitVec.getLsbD_shiftLeft]
    simp only [show 8 * k + i < n by omega, show ¬ 8 * k + i < 8 * j by omega, decide_true,
      decide_false, Bool.not_false, Bool.true_and]
    congr 1
    omega

theorem byteOf_ushr {n : Nat} (x : BitVec n) (j k : Nat) (h8 : n % 8 = 0) :
    byteOf (x >>> (8 * j)).toNat k = if 8 * (k + j) < n then byteOf x.toNat (k + j) else 0 := by
  split
  · apply byteOf_ext
    intro i hi
    rw [BitVec.testBit_toNat, BitVec.testBit_toNat, BitVec.getLsbD_ushiftRight]
    congr 1
    omega
  · apply byteOf_zero_of_bits
    intro i hi
    rw [BitVec.testBit_toNat, BitVec.getLsbD_ushiftRight]
    exact BitVec.getLsbD_of_ge _ _ (by omega)

theorem byteOf_setWidth {n : Nat} (x : BitVec n) (m k : Nat) (hk : 8 * k + 8 ≤ m) :
    byteOf (x.setWidth m).toNat k = byteOf x.toNat k := by
  apply byteOf_ext
  intro i hi
  rw [BitVec.testBit_toNat, BitVec.testBit_toNat, BitVec.getLsbD_setWidth]
  simp [show 8 * k + i < m by omega]

theorem byteOf_high {n : Nat} (x : BitVec n) (k : Nat) (hk : n ≤ 8 * k) : byteOf x.toNat k = 0 := by
  apply byteOf_zero_of_bits
  intro i hi
  rw [BitVec.testBit_toNat]
  exact BitVec.getLsbD_of_ge _ _ (by omega)

/-! ## Byte swaps -/

theorem pow256 (n : Nat) : 256 ^ n = 2 ^ (8 * n) := by
  rw [Nat.pow_mul]

theorem bswapNat_lt (nb x : Nat) : Int.bswapNat nb x < 256 ^ nb := by
  induction nb generalizing x with
  | zero => simp [Int.bswapNat]
  | succ nb ih =>
    rw [Int.bswapNat, Nat.pow_succ]
    have h1 := ih (x / 256)
    have h2 : x % 256 * 256 ^ nb ≤ 255 * 256 ^ nb :=
      Nat.mul_le_mul_right _ (by omega)
    omega

theorem bswapNat_succ (nb x : Nat) :
    Int.bswapNat (nb + 1) x = 2 ^ (8 * nb) * (x % 2 ^ 8) + Int.bswapNat nb (x / 2 ^ 8) := by
  rw [Int.bswapNat, ← pow256, Nat.mul_comm]

theorem byteOf_bswapNat (nb x k : Nat) (hk : k < nb) :
    byteOf (Int.bswapNat nb x) k = byteOf x (nb - 1 - k) := by
  induction nb generalizing x k with
  | zero => omega
  | succ nb ih =>
    have hlt : Int.bswapNat nb (x / 2 ^ 8) < 2 ^ (8 * nb) := by
      rw [← pow256]; exact bswapNat_lt _ _
    apply byteOf_ext
    intro i hi
    rw [bswapNat_succ, Nat.testBit_two_pow_mul_add _ hlt]
    by_cases hkn : k < nb
    · rw [ite_eq_left (by omega)]
      have := byteOf_ext_iff.1 (ih (x / 2 ^ 8) k hkn) i hi
      rw [this, Nat.testBit_div_two_pow]
      congr 1
      omega
    · rw [ite_eq_right (by omega), Nat.testBit_mod_two_pow]
      simp only [show 8 * k + i - 8 * nb < 8 by omega, decide_true, Bool.true_and]
      congr 1
      omega

/-! ## Constants -/

theorem litBytes_getElem? {n : Nat} (c : _root_.Int) {k : Nat} (hk : k < n) :
    (litBytes n c)[k]? = some (.lit (byteOf (BitVec.ofInt (8 * n) c).toNat k)) := by
  simp [litBytes, List.getElem?_range hk]

theorem byteOf_ofInt_eq (w : Width) (c : _root_.Int) (k : Nat) :
    byteOf (BitVec.ofInt w.bits c).toNat k = byteOf (BitVec.ofInt (8 * w.bytes) c).toNat k :=
  congrArg (fun n => byteOf (BitVec.ofInt n c).toNat k) (width_bits_eq w)

/-! ## Decoding and encoding -/

/-- The little-endian value of a list of bytes. -/
def natOfBytes : List (BitVec 8) → Nat
  | [] => 0
  | x :: xs => x.toNat + 256 * natOfBytes xs

theorem bytesNat?_map {bs : Array Byte} {xs : List (BitVec 8)} (h : bs.toList = xs.map .b) :
    bytesNat? bs = some (natOfBytes xs) := by
  rw [bytesNat?, ← Array.foldr_toList, h]
  clear h
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, List.foldr_cons, ih]
    rfl

theorem byteOf_zero (x : Nat) : byteOf x 0 = BitVec.ofNat 8 x := by
  simp [byteOf]

theorem byteOf_succ (x k : Nat) : byteOf x (k + 1) = byteOf (x / 256) k := by
  unfold byteOf
  rw [Nat.div_div_eq_div_mul, Nat.mul_succ, Nat.pow_add, Nat.mul_comm]

theorem byteOf_natOfBytes : ∀ (xs : List (BitVec 8)) (k : Nat) (hk : k < xs.length),
    byteOf (natOfBytes xs) k = xs[k]
  | x :: xs, 0, _ => by
    rw [byteOf_zero, natOfBytes]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    have := x.isLt
    simp only [List.getElem_cons_zero]
    omega
  | x :: xs, k + 1, hk => by
    rw [byteOf_succ, natOfBytes]
    have := x.isLt
    rw [show (x.toNat + 256 * natOfBytes xs) / 256 = natOfBytes xs by omega]
    exact byteOf_natOfBytes xs k (by simp at hk; omega)

theorem byteOf_mod_two_pow {x n k : Nat} (hk : 8 * k + 8 ≤ n) :
    byteOf (x % 2 ^ n) k = byteOf x k := by
  apply byteOf_ext
  intro i hi
  rw [Nat.testBit_mod_two_pow]
  simp [show 8 * k + i < n by omega]

theorem decodeInt_concrete {w : Width} {bs : Array Byte} {xs : List (BitVec 8)}
    (hsz : bs.toList = xs.map .b) (hn : xs.length = w.bytes) :
    ∃ X : BitVec w.bits, decodeInt w bs = .int w X ∧
      ∀ k (hk : k < w.bytes), byteOf X.toNat k = xs[k]'(by omega) := by
  refine ⟨BitVec.ofNat w.bits (natOfBytes xs), ?_, fun k hk => ?_⟩
  · unfold decodeInt
    rw [bytesNat?_map hsz]
  · rw [BitVec.toNat_ofNat, byteOf_mod_two_pow (by have := width_bits_eq w; omega)]
    exact byteOf_natOfBytes xs k _

theorem encode_int_bytes (w : Width) (X : BitVec w.bits) :
    encode (.int w) (.int w X) = (List.range w.bytes).toArray.map fun k => Byte.b (byteOf X.toNat k) := by
  rw [encode]
  simp only [beq_self_eq_true, ite_true]
  rfl

/-! ## Reads -/

theorem read_eq_some {m : Mem} {p : Ptr} {n : Nat} {bs : Array Byte} (hn : n ≠ 0) :
    m.read p n = some bs ↔ ∃ a, m.find? p.blk = some a ∧ p.off.toNat + n ≤ a.data.size ∧
      p.off.toNat + n < 2 ^ 64 ∧ bs = a.data.extract p.off.toNat (p.off.toNat + n) := by
  unfold Mem.read
  simp only [beq_iff_eq, hn, ite_false]
  cases m.find? p.blk with
  | none => simp
  | some a =>
    simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq, exists_eq_left']
    split
    · rename_i h
      simp only [Option.some.injEq, h, true_and]
      exact eq_comm
    · rename_i h
      simp only [reduceCtorEq, false_iff]
      exact fun ⟨h1, h2, _⟩ => h ⟨h1, h2⟩

theorem toNat_add_ofNat (o : BitVec 64) (d : Nat) :
    (o + BitVec.ofNat 64 d).toNat = (o.toNat + d) % 2 ^ 64 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod]

theorem Ptr.add_blk (p : Ptr) (k : BitVec 64) : (p.add k).blk = p.blk := rfl

theorem Ptr.add_off (p : Ptr) (k : BitVec 64) : (p.add k).off = p.off + k := rfl

theorem Ptr.add_zero (p : Ptr) : p.add (BitVec.ofNat 64 0) = p := by
  cases p
  simp [Ptr.add]

theorem read_zero (m : Mem) (p : Ptr) : m.read p 0 = some #[] := rfl

/-- Adjacent reads concatenate. -/
theorem read_append {m : Mem} {p : Ptr} {a b : Nat} {x y : Array Byte}
    (ha : m.read p a = some x) (hb : m.read (p.add (BitVec.ofNat 64 a)) b = some y) :
    m.read p (a + b) = some (x ++ y) := by
  by_cases ha0 : a = 0
  · subst ha0
    rw [read_zero] at ha
    cases ha
    rw [Ptr.add_zero] at hb
    rw [Nat.zero_add, hb, Array.empty_append]
  by_cases hb0 : b = 0
  · subst hb0
    rw [read_zero] at hb
    cases hb
    rw [Nat.add_zero, ha, Array.append_empty]
  obtain ⟨al, hf, h1, h2, rfl⟩ := (read_eq_some ha0).1 ha
  obtain ⟨al', hf', h1', h2', rfl⟩ := (read_eq_some hb0).1 hb
  rw [Ptr.add_blk, hf, Option.some.injEq] at hf'
  subst hf'
  rw [Ptr.add_off, toNat_add_ofNat, Nat.mod_eq_of_lt (by omega)] at h1' h2' ⊢
  refine (read_eq_some (by omega)).2 ⟨al, hf, by omega, by omega, ?_⟩
  rw [Array.extract_append_extract, Nat.min_eq_left (by omega), Nat.max_eq_right (by omega),
    Nat.add_assoc]

/-- A sub-range of a read reads its slice. -/
theorem read_extract {m : Mem} {p : Ptr} {n : Nat} {bs : Array Byte} (h : m.read p n = some bs)
    {j k : Nat} (hjk : j + k ≤ n) :
    m.read (p.add (BitVec.ofNat 64 j)) k = some (bs.extract j (j + k)) := by
  by_cases hk0 : k = 0
  · subst hk0
    rw [read_zero]
    simp [Nat.min_le_left]
  obtain ⟨al, hf, h1, h2, rfl⟩ := (read_eq_some (n := n) (by omega)).1 h
  refine (read_eq_some hk0).2 ⟨al, hf, ?_⟩
  rw [Ptr.add_off, toNat_add_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨by omega, by omega, ?_⟩
  rw [Array.extract_extract, Nat.min_eq_left (by omega), Nat.add_assoc]

/-- Ranges `[off + d, off + d + s)` that are each valid (modulo `2^64`, as a `Ptr.add` offset)
and cover `[0, n)` from `off` lie below `size` and `2^64`. -/
theorem cover_bound {off size n : Nat} (P : List (Nat × Nat)) (hoff : off < 2 ^ 64)
    (hv : ∀ r ∈ P, 0 < r.2 → (off + r.1) % 2 ^ 64 + r.2 ≤ size ∧ (off + r.1) % 2 ^ 64 + r.2 < 2 ^ 64)
    (hc : ∀ k < n, ∃ r ∈ P, r.1 ≤ k ∧ k < r.1 + r.2) :
    ∀ k < n, off + k + 1 ≤ size ∧ off + k + 1 < 2 ^ 64 := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro hk
    obtain ⟨r, hr, h1, h2⟩ := hc k hk
    obtain ⟨v1, v2⟩ := hv r hr (by omega)
    have hnw : off + r.1 < 2 ^ 64 := by
      by_cases h0 : r.1 = 0
      · omega
      · have := ih (r.1 - 1) (by omega) (by omega)
        omega
    rw [Nat.mod_eq_of_lt hnw] at v1 v2
    omega

/-- Reads covering `[0, n)` from `Q` make the whole range readable. -/
theorem read_cover {m : Mem} {Q : Ptr} {n : Nat} (hn : 0 < n) (rs : List (Nat × Nat))
    (hv : ∀ r ∈ rs, ∃ bs, m.read (Q.add (BitVec.ofNat 64 r.1)) r.2 = some bs)
    (hc : ∀ k < n, ∃ r ∈ rs, r.1 ≤ k ∧ k < r.1 + r.2) :
    ∃ bs, m.read Q n = some bs := by
  obtain ⟨r0, hr0, h01, h02⟩ := hc 0 hn
  obtain ⟨bs0, hb0⟩ := hv r0 hr0
  obtain ⟨al, hf, -⟩ := (read_eq_some (by omega)).1 hb0
  rw [Ptr.add_blk] at hf
  have hb := cover_bound (size := al.data.size) rs Q.off.isLt (fun r hr hpos => by
    obtain ⟨bs, hbs⟩ := hv r hr
    obtain ⟨al', hf', h1, h2, -⟩ := (read_eq_some (by omega)).1 hbs
    rw [Ptr.add_blk, hf, Option.some.injEq] at hf'
    subst hf'
    rw [Ptr.add_off, toNat_add_ofNat] at h1 h2
    exact ⟨h1, h2⟩) hc (n - 1) (by omega)
  exact ⟨_, (read_eq_some (by omega)).2 ⟨al, hf, by omega, by omega, rfl⟩⟩

/-! ## Writes -/

/-- `Mem.set` of a block twice is the second `set`. -/
theorem setL_setL (b : Blk) (a a' : Alloc) :
    ∀ l : List (Blk × Alloc), setL b a' (setL b a l) = setL b a' l
  | [] => by simp [setL]
  | e :: l => by
    unfold setL
    by_cases hb : (e.1 == b) = true
    · simp [hb, setL]
    · simp only [hb, Bool.false_eq_true, ite_false, setL, setL_setL b a a' l]

theorem Mem.ext' {m m' : Mem} (h1 : m.blocks.toList = m'.blocks.toList)
    (h2 : m.nextHeap = m'.nextHeap) (h3 : m.nextAct = m'.nextAct) : m = m' := by
  obtain ⟨⟨l⟩, nh, na⟩ := m
  obtain ⟨⟨l'⟩, nh', na'⟩ := m'
  simp only at h1 h2 h3
  rw [h1, h2, h3]

theorem set_set (m : Mem) (b : Blk) (a a' : Alloc) : (m.set b a).set b a' = m.set b a' :=
  Mem.ext' (by rw [set_toList, set_toList, set_toList, setL_setL])
    (by rw [set_nextHeap, set_nextHeap, set_nextHeap])
    (by rw [set_nextAct, set_nextAct, set_nextAct])

/-- The bytes after `Mem.write`'s byte loop. -/
theorem foldl_set_getElem? (off : Nat) (bs d : Array Byte) :
    ∀ n ≤ bs.size, off + n ≤ d.size → ∀ j,
      ((List.range n).foldl (fun d i => d.set! (off + i) bs[i]!) d)[j]? =
        if off ≤ j ∧ j < off + n then bs[j - off]? else d[j]?
  | 0, _, _, j => by
    rw [ite_eq_right (by omega)]
    rfl
  | n + 1, hn, hd, j => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds,
      foldl_set_getElem? off bs d n (by omega) (by omega) j, foldl_set_size]
    by_cases hj : off + n = j
    · subst hj
      simp only [show off + n < d.size by omega, ite_true, true_and,
        show off ≤ off + n ∧ off + n < off + (n + 1) from ⟨by omega, by omega⟩,
        Nat.add_sub_cancel_left, getElem!_pos bs n (by omega), getElem?_pos bs n (by omega)]
    · simp only [hj, ite_false]
      congr 1
      apply propext
      omega

/-- A successful `Mem.write`: the block's data after the byte loop; a non-empty write was
valid. -/
theorem write_spec {m m1 : Mem} {p : Ptr} {bs : Array Byte} {a : Alloc}
    (hm : m.find? p.blk = some a) (hw : m.write p bs = some m1) :
    m1 = m.set p.blk { a with data :=
        (List.range bs.size).foldl (fun d i => d.set! (p.off.toNat + i) bs[i]!) a.data } ∧
      (0 < bs.size → a.writable = true ∧ p.off.toNat + bs.size ≤ a.data.size ∧
        p.off.toNat + bs.size < 2 ^ 64) := by
  unfold Mem.write at hw
  by_cases he : bs.isEmpty = true
  · have hsz : bs.size = 0 := Array.isEmpty_iff_size_eq_zero.1 he
    simp only [he, ite_true] at hw
    cases hw
    rw [hsz]
    refine ⟨?_, fun h => absurd h (by omega)⟩
    exact (set_self (a := a) hm).symm
  · simp only [he, Bool.false_eq_true, ite_false, hm, Option.bind_eq_bind, Option.bind_some] at hw
    split at hw
    · rename_i hc
      cases hw
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact ⟨rfl, fun _ => ⟨hc.1.1, hc.1.2, hc.2⟩⟩
    · cases hw

theorem write_find {m m1 : Mem} {p : Ptr} {bs : Array Byte} (hw : m.write p bs = some m1)
    (hpos : 0 < bs.size) : ∃ a, m.find? p.blk = some a := by
  cases h : m.find? p.blk with
  | some a => exact ⟨a, rfl⟩
  | none =>
    unfold Mem.write at hw
    have he : bs.isEmpty = false := by
      rw [Bool.eq_false_iff]
      intro h'
      have := Array.isEmpty_iff_size_eq_zero.1 h'
      omega
    simp [he, h] at hw

theorem write_of_valid {m : Mem} {p : Ptr} {bs : Array Byte} {a : Alloc}
    (hm : m.find? p.blk = some a) (hpos : 0 < bs.size) (hw : a.writable = true)
    (h1 : p.off.toNat + bs.size ≤ a.data.size) (h2 : p.off.toNat + bs.size < 2 ^ 64) :
    m.write p bs = some (m.set p.blk { a with
      data := (List.range bs.size).foldl (fun d i => d.set! (p.off.toNat + i) bs[i]!) a.data })
    := by
  unfold Mem.write
  have he : bs.isEmpty = false := by
    rw [Bool.eq_false_iff]
    intro h'
    have := Array.isEmpty_iff_size_eq_zero.1 h'
    omega
  simp only [he, Bool.false_eq_true, ite_false, hm, Option.bind_eq_bind, Option.bind_some, hw,
    Bool.and_eq_true, decide_eq_true_eq, h1, h2, and_self, ite_true]

section Tiling

variable (Q : Ptr)

/-- One store of a tiling: `p.2` at `Q + p.1`. -/
def tileStep (m : Mem) (p : Nat × Array Byte) : Option Mem := m.write (Q.add (BitVec.ofNat 64 p.1)) p.2

/-- The offset of a store of a tiling in its block. -/
def tileOff (p : Nat × Array Byte) : Nat := (Q.off.toNat + p.1) % 2 ^ 64

theorem tileStep_spec {m m1 : Mem} {p : Nat × Array Byte} {a : Alloc}
    (hm : m.find? Q.blk = some a) (hw : tileStep Q m p = some m1) :
    m1 = m.set Q.blk { a with data :=
        (List.range p.2.size).foldl (fun d i => d.set! (tileOff Q p + i) p.2[i]!) a.data } ∧
      (0 < p.2.size → a.writable = true ∧ tileOff Q p + p.2.size ≤ a.data.size ∧
        tileOff Q p + p.2.size < 2 ^ 64) := by
  have := write_spec (p := Q.add (BitVec.ofNat 64 p.1)) hm hw
  rwa [Ptr.add_off, toNat_add_ofNat] at this

theorem fold_find : ∀ (ws : List (Nat × Array Byte)) (m mr : Mem),
    ws.foldlM (tileStep Q) m = some mr → (∃ p ∈ ws, 0 < p.2.size) → ∃ a, m.find? Q.blk = some a
  | [], _, _, _, ⟨_, h, _⟩ => absurd h List.not_mem_nil
  | p :: ws, m, mr, hf, ⟨q, hq, hpos⟩ => by
    rw [List.foldlM_cons] at hf
    cases h1 : tileStep Q m p with
    | none => rw [h1] at hf; cases hf
    | some m1 =>
      rw [h1] at hf
      by_cases hp : 0 < p.2.size
      · exact write_find (p := Q.add (BitVec.ofNat 64 p.1)) (bs := p.2) h1 hp
      · rcases List.mem_cons.1 hq with rfl | hq
        · exact absurd hpos hp
        · obtain ⟨a1, ha1⟩ := fold_find ws m1 mr hf ⟨q, hq, hpos⟩
          have hs : p.2.size = 0 := by omega
          unfold tileStep Mem.write at h1
          simp [Array.isEmpty_iff_size_eq_zero.2 hs] at h1
          exact ⟨a1, h1 ▸ ha1⟩

/-- Every non-empty store of a successful tiling is valid in the starting block. -/
theorem fold_valid : ∀ (ws : List (Nat × Array Byte)) (m mr : Mem) (a : Alloc),
    m.find? Q.blk = some a → ws.foldlM (tileStep Q) m = some mr →
    ∀ p ∈ ws, 0 < p.2.size → a.writable = true ∧ tileOff Q p + p.2.size ≤ a.data.size ∧
      tileOff Q p + p.2.size < 2 ^ 64
  | [], _, _, _, _, _, _, h, _ => absurd h List.not_mem_nil
  | p :: ws, m, mr, a, hm, hf, q, hq, hpos => by
    rw [List.foldlM_cons] at hf
    cases h1 : tileStep Q m p with
    | none => rw [h1] at hf; cases hf
    | some m1 =>
      rw [h1] at hf
      obtain ⟨rfl, hv⟩ := tileStep_spec Q hm h1
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hv hpos
      · have h := fold_valid ws _ mr _ (by rw [find?_set, ite_eq_left rfl]) hf q hq hpos
        simpa only [foldl_set_size] using h

/-- The data after a tiling whose stores do not wrap around and are pairwise disjoint. -/
theorem fold_data : ∀ (ws : List (Nat × Array Byte)) (m mr : Mem) (a : Alloc),
    m.find? Q.blk = some a → ws.foldlM (tileStep Q) m = some mr →
    (∀ p ∈ ws, Q.off.toNat + p.1 + p.2.size < 2 ^ 64) →
    ws.Pairwise (fun p q => p.1 + p.2.size ≤ q.1 ∨ q.1 + q.2.size ≤ p.1) →
    ∃ D : Array Byte, mr = m.set Q.blk { a with data := D } ∧ D.size = a.data.size ∧
      (∀ j, (∀ p ∈ ws, ¬ (Q.off.toNat + p.1 ≤ j ∧ j < Q.off.toNat + p.1 + p.2.size)) →
        D[j]? = a.data[j]?) ∧
      (∀ p ∈ ws, ∀ t < p.2.size, D[Q.off.toNat + p.1 + t]? = p.2[t]?)
  | [], m, mr, a, hm, hf, _, _ => by
    cases hf
    refine ⟨a.data, (set_self hm).symm, rfl, fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil⟩
  | p :: ws, m, mr, a, hm, hf, hnw, hdis => by
    rw [List.foldlM_cons] at hf
    cases h1 : tileStep Q m p with
    | none => rw [h1] at hf; cases hf
    | some m1 =>
      rw [h1] at hf
      obtain ⟨rfl, hv⟩ := tileStep_spec Q hm h1
      have ho : tileOff Q p = Q.off.toNat + p.1 := by
        have := hnw p List.mem_cons_self
        unfold tileOff; rw [Nat.mod_eq_of_lt (by omega)]
      rw [ho] at hv
      generalize hD1 : (List.range p.2.size).foldl
        (fun d i => d.set! (tileOff Q p + i) p.2[i]!) a.data = D1 at hf
      have hD1g : ∀ j, D1[j]? = if Q.off.toNat + p.1 ≤ j ∧ j < Q.off.toNat + p.1 + p.2.size
          then p.2[j - (Q.off.toNat + p.1)]? else a.data[j]? := by
        intro j
        rw [← hD1, ho]
        by_cases hpos : 0 < p.2.size
        · exact foldl_set_getElem? _ _ _ _ (Nat.le_refl _) (hv hpos).2.1 j
        · have hs : p.2.size = 0 := by omega
          rw [hs, ite_eq_right (by omega)]
          rfl
      have hD1s : D1.size = a.data.size := by rw [← hD1, foldl_set_size]
      obtain ⟨D, rfl, hDs, hDu, hDw⟩ := fold_data ws _ mr { a with data := D1 }
        (by rw [find?_set, ite_eq_left rfl]) hf (fun q hq => hnw q (List.mem_cons_of_mem _ hq))
        (List.pairwise_cons.1 hdis).2
      refine ⟨D, set_set _ _ _ _, hDs.trans hD1s, fun j hj => ?_, fun q hq t ht => ?_⟩
      · rw [hDu j (fun q hq => hj q (List.mem_cons_of_mem _ hq)), hD1g j,
          ite_eq_right (hj p List.mem_cons_self)]
      · rcases List.mem_cons.1 hq with rfl | hq
        · rw [hDu _ (fun r hr => ?_), hD1g, ite_eq_left ⟨by omega, by omega⟩]
          · congr 1; omega
          · have := (List.pairwise_cons.1 hdis).1 r hr
            omega
        · exact hDw q hq t ht

end Tiling

/-- **Store tiling.** Writes whose ranges `[d, d + E.size)` are pairwise disjoint and tile
`[0, W)` from `Q`, applied in order, are one write at `Q` of their bytes. -/
theorem write_tiling {m0 mr : Mem} {Q : Ptr} {W : Nat} (ws : List (Nat × Array Byte))
    (hin : ∀ p ∈ ws, p.1 + p.2.size ≤ W)
    (hcov : ∀ k < W, ∃ p ∈ ws, p.1 ≤ k ∧ k < p.1 + p.2.size)
    (hdis : ws.Pairwise fun p q => p.1 + p.2.size ≤ q.1 ∨ q.1 + q.2.size ≤ p.1)
    (hw : ws.foldlM (fun m (p : Nat × Array Byte) => m.write (Q.add (BitVec.ofNat 64 p.1)) p.2) m0 =
      some mr) :
    ∃ S : Array Byte, S.size = W ∧ (∀ d E, (d, E) ∈ ws → ∀ t < E.size, S[d + t]? = E[t]?) ∧
      m0.write Q S = some mr := by
  change ws.foldlM (tileStep Q) m0 = some mr at hw
  by_cases hW : W = 0
  · subst hW
    refine ⟨#[], rfl, fun d E h t ht => ?_, ?_⟩
    · have := hin _ h
      simp only at this
      omega
    have : ∀ (l : List (Nat × Array Byte)) (m : Mem), (∀ p ∈ l, p.1 + p.2.size ≤ 0) →
        l.foldlM (tileStep Q) m = some m := by
      intro l
      induction l with
      | nil => intro m _; rfl
      | cons p l ih =>
        intro m hl
        have hs : p.2.size = 0 := by have := hl p List.mem_cons_self; omega
        rw [List.foldlM_cons]
        unfold tileStep Mem.write
        simp only [Array.isEmpty_iff_size_eq_zero.2 hs, ite_true]
        exact ih m fun q hq => hl q (List.mem_cons_of_mem _ hq)
    rw [this ws m0 hin] at hw
    cases hw
    rfl
  obtain ⟨p0, hp0, h01, h02⟩ := hcov 0 (by omega)
  obtain ⟨a0, ha0⟩ := fold_find Q ws m0 mr hw ⟨p0, hp0, by omega⟩
  have hv := fold_valid Q ws m0 mr a0 ha0 hw
  have hb := cover_bound (size := a0.data.size) (ws.map fun p => (p.1, p.2.size)) Q.off.isLt
    (fun r hr hpos => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
      have := hv p hp hpos
      exact ⟨this.2.1, this.2.2⟩)
    (fun k hk => by
      obtain ⟨p, hp, h1, h2⟩ := hcov k hk
      exact ⟨_, List.mem_map_of_mem hp, h1, h2⟩) (W - 1) (by omega)
  obtain ⟨D, rfl, hDs, hDu, hDw⟩ := fold_data Q ws m0 mr a0 ha0 hw
    (fun p hp => by have := hin p hp; omega) hdis
  have hwr := (hv p0 hp0 (by omega)).1
  have hSs : (D.extract Q.off.toNat (Q.off.toNat + W)).size = W := by
    simp only [Array.size_extract]; omega
  refine ⟨D.extract Q.off.toNat (Q.off.toNat + W), hSs, fun d E h t ht => ?_, ?_⟩
  · have := hin _ h
    rw [Array.getElem?_extract, ite_eq_left (by simp at this ⊢; omega), ← Nat.add_assoc]
    exact hDw _ h t ht
  · rw [write_of_valid ha0 (by omega) hwr (by omega) (by omega)]
    refine congrArg (fun d => some (m0.set Q.blk { a0 with data := d })) ?_
    apply Array.ext_getElem?
    intro j
    rw [foldl_set_getElem? Q.off.toNat (D.extract Q.off.toNat (Q.off.toNat + W)) a0.data _
      (Nat.le_refl _) (by omega) j]
    split
    · rename_i hj
      rw [Array.getElem?_extract, ite_eq_left (by omega)]
      congr 1; omega
    · rename_i hj
      rw [hDu j fun p hp hr => hj (by have := hin p hp; omega)]

end GoFV.Proof.MemCombine

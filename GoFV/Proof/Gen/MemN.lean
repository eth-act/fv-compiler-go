import GoFV.Proof.Gen.Mem

/-!
# Narrow loads and stores of slice G3 under `MemInj` (`docs/plans/proofs3.md` §3)

The narrow counterparts of `lo_load` and `memInj_store` (`Mem.lean`). Every byte of a live block
is related to its machine byte (`memInj_byteRel`), so:

* an `n`-byte load (`MOV{B,H,W}{,U}`, `Arm64.loadN`, `n ∈ {1, 2, 4, 8}`) reads a value related to
  the machine's bytes zero- or sign-extended (`lo_loadN`): a narrow Phase 1 load that yields an
  integer read concrete bytes, which are the machine's; otherwise it is `poison`. At the boolean
  shape, a stored byte 0 or 1 reads back related to the machine's byte (`valRel_loadBool`);
* an `n`-byte store (`MOV{B,H,W}`, `Arm64.storeBytes n`) of a register content of class at least
  `8n` (or a boolean) writes the low `n` bytes of the machine register and keeps `MemInj`
  (`memInj_storeN`; a pointer with a register is its address under `AddrAgree`);
* the address of a valid access is outside the nil page and does not wrap (`access_nil`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64

variable {ι : Blk → Option (BitVec 64)}

/-! ## Helpers (private copies of `Mem.lean`'s) -/

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

/-! ## Narrow accesses (slice G3) -/

/-- The bytes of a valid read of `n > 0` bytes are related to the machine bytes at the injected
address of the access. -/
private theorem read_rel (hA : AddrAgree ι) {m : Mem} {mm : Memory} (h : MemInj ι m mm)
    {p : Ptr} {a : BitVec 64} {n : Nat} {bs : Array Byte} (hn : 0 < n) (ha : ι p.blk = some a)
    (hr : m.read p n = some bs) :
    bs.size = n ∧ ∀ j (hj : j < bs.size), ByteRel ι bs[j] (mm (a + p.off + BitVec.ofNat 64 j)) := by
  obtain ⟨al, hfa, hsz, rfl⟩ := read_some hn hr
  refine ⟨by simp; omega, fun j hj => ?_⟩
  simp only [Array.size_extract] at hj
  simp only [Array.getElem_extract]
  rw [← addr_off]
  exact memInj_byteRel hA h (find?_mem hfa) ha (by omega)

/-- Concrete bytes related to the machine bytes at `A` are the number the machine reads there. -/
private theorem readMem_nat {mm : Memory} {A : BitVec 64} {bs : Array Byte} {k : Nat}
    (hb : ∀ j (hj : j < bs.size), ByteRel ι bs[j] (mm (A + BitVec.ofNat 64 j)))
    (hk : bytesNat? bs = some k) : (readMem mm A bs.size).toNat = k := by
  rw [bytesNat?_eq] at hk
  obtain ⟨h1, h2⟩ := bnat_some _ k hk
  simp only [Array.length_toList] at h1 h2
  refine readMem_of_bytes mm _ A k h1 fun j hj => ?_
  have := hb j hj
  rw [← Array.getElem_toList, h2 j hj] at this
  simp only [ByteRel] at this
  rw [← this, BitVec.toNat_ofNat]

/-- A narrow integer load at a valid address: `poison`, or the number the machine reads there. -/
private theorem load_narrow (hA : AddrAgree ι) {m : Mem} {mm : Memory} (h : MemInj ι m mm)
    {p : Ptr} {a : BitVec 64} {bs : Array Byte} (ha : ι p.blk = some a) {w : Width} {n : Nat}
    (hw : w ≠ .w64) (hwn : w.bytes = n) (hr : m.read p n = some bs) :
    m.load (.int w) p = .poison ∨ ∃ k, m.load (.int w) p = .int w (BitVec.ofNat w.bits k) ∧
      (readMem mm (a + p.off) n).toNat = k := by
  subst hwn
  have hl : m.load (.int w) p = decodeInt w (bs.extract 0 (0 + w.bytes)) := by
    simp only [Mem.load, Ty.size, hr, decodeLoad, Sem.decode]
  obtain ⟨hs, hb⟩ := read_rel hA h (by cases w <;> decide) ha hr
  rw [hl, Nat.zero_add, ← hs, Array.extract_size]
  unfold decodeInt
  cases hk : bytesNat? bs with
  | some k => exact Or.inr ⟨k, rfl, readMem_nat hb hk⟩
  | none => cases w <;> first | exact absurd rfl hw | exact Or.inl rfl

private theorem res_int {t : Ty} (ht : t ≠ .bool) (r : BitVec 64) :
    Arm64.res t r = .int .w64 r := by
  cases t <;> first | rfl | exact absurd rfl ht

/-- The machine's `n`-byte read zero-extended, from the number it holds. -/
private theorem sw_readMem {mm : Memory} {A : BitVec 64} {n v k : Nat} (hv : v = 8 * n)
    (hk : (readMem mm A n).toNat = k) :
    (BitVec.ofNat v k).setWidth 64 = (readMem mm A n).setWidth 64 := by
  subst hk hv
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `lo_loadN` at a narrow width `w` of `n` bytes, given `Arm64.loadN`'s narrow case. -/
private theorem lo_narrow (hA : AddrAgree ι) {m : Mem} {mm : Memory} (h : MemInj ι m mm)
    {p : Ptr} {a : BitVec 64} {bs : Array Byte} {t : Ty} {sg : Bool} {w : Width} {n : Nat}
    (ht : t ≠ .bool) (ha : ι p.blk = some a) (hw : w ≠ .w64) (hwn : w.bytes = n)
    (hbits : w.bits = 8 * n) (hr : m.read p n = some bs)
    (hl : Arm64.loadN t n sg m p = match m.load (.int w) p with
      | .int _ x => Arm64.res t (if sg then Arm64.sext (8 * n) (x.setWidth 64) else x.setWidth 64)
      | _ => .poison) :
    Lo ι 64 (Arm64.loadN t n sg m p)
      (if sg then ProgOp.sextTo64 n ((readMem mm (a + p.off) n).setWidth 64)
       else (readMem mm (a + p.off) n).setWidth 64) := by
  rcases load_narrow hA h ha hw hwn hr with hp | ⟨k, hk, hR⟩
  · rw [hl, hp]; trivial
  · rw [hl, hk]
    dsimp only
    rw [res_int ht]
    show BitVec.setWidth 64 _ = BitVec.setWidth 64 _
    rw [sw_readMem hbits hR]; rfl

/-- An `n`-byte load (`1, 2, 4, 8`) at a valid address reads a value related, on all 64 bits, to
the register the machine's load writes: the bytes there zero-extended, or for a signed narrow load
(`MOVB`, `MOVH`, `MOVW`) sign-extended. -/
theorem lo_loadN (hA : AddrAgree ι) {m : Mem} {mm : Memory} (h : MemInj ι m mm) {p : Ptr}
    {a : BitVec 64} {n : Nat} {bs : Array Byte} {t : Ty} {sg : Bool}
    (hn : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8) (hsg : n = 8 → sg = false) (ht : t ≠ .bool)
    (ha : ι p.blk = some a) (hr : m.read p n = some bs) :
    Lo ι 64 (Arm64.loadN t n sg m p)
      (if sg then ProgOp.sextTo64 n ((readMem mm (a + p.off) n).setWidth 64)
       else (readMem mm (a + p.off) n).setWidth 64) := by
  rcases hn with rfl | rfl | rfl | rfl
  · exact lo_narrow hA h ht ha (w := .w8) (by decide) rfl rfl hr rfl
  · exact lo_narrow hA h ht ha (w := .w16) (by decide) rfl rfl hr rfl
  · exact lo_narrow hA h ht ha (w := .w32) (by decide) rfl rfl hr rfl
  · obtain rfl := hsg rfl
    have := lo_load hA h ha hr
    have hl : Arm64.loadN t 8 false m p = match m.load (.int .w64) p with
        | .int .w64 x => Arm64.res t x
        | v => v := rfl
    rw [hl]
    split
    · rename_i x hx
      rw [hx] at this
      rw [res_int ht]; exact this
    · exact this

/-- The 1-byte unsigned load (`MOVBU`) at the boolean shape, of a stored byte 0 or 1, is related
to the machine's zero-extended byte. -/
theorem valRel_loadBool (hA : AddrAgree ι) {m : Mem} {mm : Memory} (h : MemInj ι m mm) {p : Ptr}
    {a : BitVec 64} {bs : Array Byte} (ha : ι p.blk = some a) (hr : m.read p 1 = some bs)
    (h01 : ∀ x, m.load (.int .w8) p = .int .w8 x → x.toNat < 2) :
    ValRel ι ((Arm64.loadN .bool 1 false m p).retypeL .bool) ((readMem mm (a + p.off) 1).setWidth 64) := by
  have hl : Arm64.loadN .bool 1 false m p = match m.load (.int .w8) p with
      | .int _ x => Arm64.res .bool (x.setWidth 64)
      | _ => .poison := rfl
  rcases load_narrow hA h ha (w := .w8) (n := 1) (by decide) rfl hr with hp | ⟨k, hk, hR⟩
  · rw [hl, hp]; trivial
  · have h2 := h01 _ hk
    have hR' := (readMem mm (a + p.off) 1).isLt
    rw [hl, hk]
    simp only [BitVec.toNat_ofNat, Width.bits, Nat.reducePow] at h2
    have hk2 : k < 2 := by simp at hR'; omega
    have hR0 : (readMem mm (a + p.off) 1).setWidth 64 = BitVec.ofNat 64 k := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, hR]
    rw [hR0]
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> rfl

/-- The `n` little-endian bytes of a register `Y` agreeing with `Xs` on the low `8n` bits are the
bytes of the machine's `n`-byte store of `Xs`. -/
private theorem intBytes_relN {Y Xs : BitVec 64} {n j : Nat} (hj : j < n)
    (hY : Y.toNat % 2 ^ (8 * n) = Xs.toNat % 2 ^ (8 * n)) :
    ByteRel ι (intBytes n Y.toNat)[j]!
      ((BitVec.ofNat (8 * n) (Xs.toNat % 2 ^ (8 * n))).extractLsb' (8 * j) 8) := by
  rw [getElem!_pos _ _ (by simp [intBytes]; omega)]
  simp only [intBytes, Array.getElem_map, List.getElem_toArray, List.getElem_range, ByteRel]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.mod_mod,
    ← hY]
  rw [show 2 ^ (8 * n) = 2 ^ (8 * j) * 2 ^ (8 * (n - j)) by rw [← Nat.pow_add]; congr 1; omega,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : 8 ≤ 8 * (n - j)))]

/-- The bytes of an `n`-byte store (`1, 2, 4, 8`) of a register content of class `c ≥ 8n` (or a
boolean) related to `Xs` are related to the bytes of the machine's store of `Xs`. -/
theorem storeBytes_relN (hA : AddrAgree ι) {n c : Nat} {x : Val} {Xs : BitVec 64}
    (hn : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8) (hx : ValRel ι x Xs) (hf : Fits c x)
    (hc : 8 * n ≤ c ∨ c = 1) : (Arm64.storeBytes n x).size = n ∧ ∀ j, j < n →
      ByteRel ι (Arm64.storeBytes n x)[j]!
        ((BitVec.ofNat (8 * n) (Xs.toNat % 2 ^ (8 * n))).extractLsb' (8 * j) 8) := by
  have hn8 : n ≤ 8 := by omega
  by_cases hp : n = 8 ∧ ∃ q, x = .ptr q
  · obtain ⟨rfl, q, rfl⟩ := hp
    obtain ⟨aq, haq, rfl⟩ := hx
    have hV : (BitVec.ofNat (8 * 8) ((aq + q.off).toNat % 2 ^ (8 * 8)) : BitVec 64) = aq + q.off := by
      apply BitVec.eq_of_toNat_eq; simp
    have : Arm64.storeBytes 8 (.ptr q) = ptrBytes q := rfl
    rw [this, hV]
    refine ⟨by simp [ptrBytes], fun j hj => ?_⟩
    rw [getElem!_pos _ _ (by simp [ptrBytes]; omega)]
    simp only [ptrBytes, Array.getElem_map, List.getElem_toArray, List.getElem_range]
    exact ⟨aq, haq, rfl⟩
  have hs : Arm64.storeBytes n x = match Arm64.reg x with
      | some r => intBytes n r.toNat
      | none => Array.replicate n .poison := by
    unfold Arm64.storeBytes
    split
    · exact absurd ⟨rfl, _, rfl⟩ hp
    · exact absurd hf id
    · cases Arm64.reg x <;> simp only [hn8, ↓reduceIte]
  rw [hs]
  cases hr : Arm64.reg x with
  | none =>
    refine ⟨by simp, fun j hj => ?_⟩
    rw [getElem!_pos _ _ (by simp; omega), Array.getElem_replicate]
    trivial
  | some r =>
    refine ⟨by simp [intBytes], fun j hj => intBytes_relN hj ?_⟩
    rcases hc with hc | rfl
    · have hl := congrArg BitVec.toNat (reg_low hA hx hf hr)
      simp only [BitVec.toNat_setWidth] at hl
      rw [← Nat.mod_mod_of_dvd r.toNat (Nat.pow_dvd_pow 2 hc), hl,
        Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hc)]
    · cases x with
      | bool b =>
        have hr' : (if b then (1 : BitVec 64) else 0) = r := Option.some.inj hr
        have hx' : Xs = if b then 1 else 0 := hx
        rw [hx', hr']
      | int w v => cases w <;> simp [Fits, Width.bits] at hf
      | ptr q => simp [Fits] at hf
      | poison => cases hr
      | _ => exact absurd hf id

/-- A write of `0 < n ≤ 8` bytes, each related to the corresponding byte of the machine's `V`,
keeps `MemInj` with the machine's `writeMem` of `V` (`memInj_storeN`'s conclusion). -/
private theorem memInj_write (hA : AddrAgree ι) {m m' : Mem} {mm : Memory} (h : MemInj ι m mm)
    (hk : KeysNodup m) {p : Ptr} {a : BitVec 64} {n : Nat} {bsW : Array Byte}
    {V : BitVec (8 * n)} (hn0 : 0 < n) (hn : n ≤ 8) (ha : ι p.blk = some a) (hsz : bsW.size = n)
    (hbyte : ∀ j, j < n → ByteRel ι bsW[j]! (V.extractLsb' (8 * j) 8))
    (hw : m.write p bsW = some m') :
    MemInj ι m' (writeMem mm (a + p.off) n V) ∧ KeysNodup m' ∧
      (∀ b al2, (b, al2) ∈ m'.blocks → ∃ al1, (b, al1) ∈ m.blocks ∧ al1.data.size = al2.data.size) ∧
      ∃ al, (p.blk, al) ∈ m.blocks ∧ p.off.toNat + n ≤ al.data.size ∧
        ∀ y : BitVec 64, (∀ j, j < n → y.toNat ≠ a.toNat + p.off.toNat + j) →
          writeMem mm (a + p.off) n V y = mm y := by
  unfold Mem.write at hw
  have hne : bsW.isEmpty = false := by
    rw [Array.isEmpty_eq_false_iff, ← Array.size_pos_iff, hsz]; exact hn0
  simp only [hne, Bool.false_eq_true, ↓reduceIte] at hw
  cases hfa : m.find? p.blk with
  | none => simp [hfa] at hw
  | some al =>
  simp only [hfa, hsz, Option.bind_eq_bind, Option.bind_some] at hw
  split at hw
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    have hoff : p.off.toNat + n ≤ al.data.size := hc.1.1.2
    simp only [Option.some.injEq] at hw
    have hfs := fold_set bsW p.off.toNat n al.data
    generalize List.foldl (fun d i => d.set! (p.off.toNat + i) bsW[i]!) al.data (List.range n) = D
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
    have hback : ∀ b al2, (b, al2) ∈ m'.blocks →
        ∃ al1, (b, al1) ∈ m.blocks ∧ al1.data.size = al2.data.size := by
      intro b al2 hb
      rcases hcases b al2 hb with ⟨rfl, rfl⟩ | ⟨-, hb⟩
      · exact ⟨al, hmem, hDsz.symm⟩
      · exact ⟨al2, hb, rfl⟩
    have hout : ∀ y : BitVec 64, (∀ j, j < n → y.toNat ≠ a.toNat + p.off.toNat + j) →
        writeMem mm (a + p.off) n V y = mm y := by
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
        by_cases hin : p.off.toNat ≤ i ∧ i < p.off.toNat + n
        · rw [ite_eq_left hin] at hg
          rw [Option.some.inj hg, show a + BitVec.ofNat 64 i =
              a + p.off + BitVec.ofNat 64 (i - p.off.toNat) by rw [← addr_off, Nat.add_sub_cancel' hin.1],
            writeMem_at n mm _ V _ (by omega) hn]
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

/-- An `n`-byte store (`1, 2, 4, 8`) of a register content of class `c` related to `Xs`, with
`8n ≤ c` or a boolean (`c = 1`), keeps `MemInj` with the machine's `writeMem` of the low `n`
bytes of `Xs`, and the keys distinct; the blocks keep their sizes, and the machine bytes change
only in the `n` bytes of the access, inside the window of its block. -/
theorem memInj_storeN (hA : AddrAgree ι) {m m' : Mem} {mm : Memory} (h : MemInj ι m mm)
    (hk : KeysNodup m) {p : Ptr} {a : BitVec 64} {x : Val} {Xs : BitVec 64} {n c : Nat}
    (hn : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8) (ha : ι p.blk = some a) (hx : ValRel ι x Xs)
    (hf : Fits c x) (hc : 8 * n ≤ c ∨ c = 1)
    (hw : m.write p (Arm64.storeBytes n x) = some m') :
    MemInj ι m' (writeMem mm (a + p.off) n (BitVec.ofNat (8 * n) (Xs.toNat % 2 ^ (8 * n)))) ∧
      KeysNodup m' ∧
      (∀ b al2, (b, al2) ∈ m'.blocks → ∃ al1, (b, al1) ∈ m.blocks ∧ al1.data.size = al2.data.size) ∧
      ∃ al, (p.blk, al) ∈ m.blocks ∧ p.off.toNat + n ≤ al.data.size ∧
        ∀ y : BitVec 64, (∀ j, j < n → y.toNat ≠ a.toNat + p.off.toNat + j) →
          writeMem mm (a + p.off) n (BitVec.ofNat (8 * n) (Xs.toNat % 2 ^ (8 * n))) y = mm y :=
  have hb := storeBytes_relN hA hn hx hf hc
  memInj_write hA h hk (by omega) (by omega) ha hb.1 hb.2 hw

/-- The address of a valid access of `n > 0` bytes into a live block is outside the nil page, and
the block's injected address plus the offset does not wrap around. -/
theorem access_nil {m : Mem} {mm : Memory} (h : MemInj ι m mm) {p : Ptr} {a : BitVec 64} {n : Nat}
    (ha : ι p.blk = some a) (hn : 0 < n) (hv : m.canWrite p n = true ∨ (m.read p n).isSome) :
    nilPage (a + p.off) = false ∧ (a + p.off).toNat = a.toNat + p.off.toNat := by
  obtain ⟨al, hfa, hsz⟩ : ∃ al, m.find? p.blk = some al ∧ p.off.toNat + n ≤ al.data.size := by
    rcases hv with hv | hv
    · exact canWrite_some hn hv
    · obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.1 hv
      obtain ⟨al, h1, h2, -⟩ := read_some hn hbs
      exact ⟨al, h1, h2⟩
  obtain ⟨a0, ha0, hlo, hhi⟩ := h.mapped _ _ (find?_mem hfa)
  obtain rfl : a = a0 := Option.some.inj (ha.symm.trans ha0)
  have h4 := hlo (by omega)
  have ht : (a + p.off).toNat = a.toNat + p.off.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  refine ⟨?_, ht⟩
  simp only [nilPage, decide_eq_false_iff_not, Nat.not_lt, ht]
  omega

end GoFV.Proof.Gen

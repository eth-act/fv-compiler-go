import GoFV.Proof.Gen.Mem

variable [GoFV.SSA.Sem.Addrs]

/-!
# `runtime.memequal`'s answer on the machine and in Phase 1 (slice G28, #733)

`runtime·memequal` (`internal/bytealg/equal_arm64.s`) compares the `R2` machine bytes at `R0` and
`R1` (`MachBytesEq`) and returns 1 or 0 in `R0` (`MemEqRes`): the trusted contract `MemEqSpec`
(`G28.lean`) states only that. `memEq` (Phase 1, `Sem/Ptr.lean`) compares `Byte`s, which keep a
pointer fragment's provenance: two fragments of different pointers differ in Phase 1 even where
their injected addresses coincide (two zero-size blocks at one address, `InjectiveOnLive`), and a
fragment differs from a concrete byte. Under `AddrAgree` and `MemInj` equal `Byte`s are equal
machine bytes (`memEq_res`); different ones are different machine bytes where they differ
visibly (`DiffAt`): at two different concrete bytes, or at two different pointers stored whole,
each into a nonempty live allocation before its end (`LiveWordAt`: as fragments or as the
concrete word of its Phase 1 address; distinct live blocks have disjoint windows), or at such a
pointer against nil. `MemEqPre`, a premise on the Phase 1 run (not trusted, as `CmpPre`), asks
that much of every `LoweredMemEq` whose bytes `memEq` finds different.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64

variable {ι : Blk → Option (BitVec 64)}

/-! ## Definitions -/

/-- The `n` machine bytes at `x` and at `y` agree (what `runtime.memequal` compares). -/
def MachBytesEq (M : Memory) (x y n : BitVec 64) : Prop :=
  ∀ j, j < n.toNat → M (x + BitVec.ofNat 64 j) = M (y + BitVec.ofNat 64 j)

/-- `runtime.memequal`'s result in `m'` from its entry state `m` (`equal_arm64.s`): `X0` is 1 if
the `X2` machine bytes at `X0` and at `X1` agree, 0 if not. -/
def MemEqRes (m m' : MState) : Prop :=
  (MachBytesEq m.mem (m.x 0) (m.x 1) (m.x 2) → m'.x 0 = 1) ∧
    (¬ MachBytesEq m.mem (m.x 0) (m.x 1) (m.x 2) → m'.x 0 = 0)

/-- The word at `j` of `bs` addresses `r`, which points into a nonempty live allocation of `mm`
before its end: `r`'s eight fragments, or the concrete bytes of `r`'s Phase 1 address. -/
def LiveWordAt (mm : Mem) (bs : Array Byte) (j : Nat) (r : Ptr) : Prop :=
  (bs.extract j (j + 8) = ptrBytes r ∨
    ∃ y : BitVec 64, bs.extract j (j + 8) = intBytes 8 y.toNat ∧ Ptr.ofAddr y = r) ∧
  ∃ al, (r.blk, al) ∈ mm.blocks ∧ r.off.toNat < al.data.size

/-- `bs` and `cs` differ at `j` where the machine sees it: two different concrete bytes; two
different pointers into nonempty live allocations, before their ends (`LiveWordAt`); or such a
pointer against nil (eight zero bytes). -/
def DiffAt (mm : Mem) (bs cs : Array Byte) (j : Nat) : Prop :=
  (∃ x y, bs[j]? = some (.b x) ∧ cs[j]? = some (.b y) ∧ x ≠ y) ∨
  (∃ r r', LiveWordAt mm bs j r ∧ LiveWordAt mm cs j r' ∧ r ≠ r') ∨
  (∃ r, LiveWordAt mm bs j r ∧ cs.extract j (j + 8) = intBytes 8 0) ∨
  (∃ r, bs.extract j (j + 8) = intBytes 8 0 ∧ LiveWordAt mm cs j r)

/-- The bytes `memEq [x0, x1, x2, .mem mm]` compares, when they hold no `poison` and differ,
differ where the machine sees it (`DiffAt`). -/
def MemEqDiff (mm : Mem) (x0 x1 x2 : Val) : Prop :=
  ∀ p q (w : Width) (n : BitVec w.bits) bs cs, x0.asPtrWord = some p → x1.asPtrWord = some q →
    x2 = .int w n → mm.read p n.toNat = some bs → mm.read q n.toNat = some cs →
    bs.any (· == .poison) = false → cs.any (· == .poison) = false → bs ≠ cs →
    ∃ j, DiffAt mm bs cs j

/-- **The Phase 1 premise of a `LoweredMemEq`** (G28; a premise on the run, not trusted, as
`CmpPre`): the bytes `memEq` compares from `s` differ, if at all, where the machine sees it
(`MemEqDiff`). -/
def MemEqPre (lc : LocCtx) (s : LocState) (v : Value) : Prop :=
  v.op = .ARM64LoweredMemEq → ∀ a0 a1 a2 x0 x1 x2 mm, v.args[0]? = some a0 →
    v.args[1]? = some a1 → v.args[2]? = some a2 → s.read lc a0 = .ok x0 →
    s.read lc a1 = .ok x1 → s.read lc a2 = .ok x2 → s.mem = .mem mm → MemEqDiff mm x0 x1 x2

/-! ## Helpers (private copies of `Mem.lean`'s) -/

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

private theorem read_zero {m : Mem} {p : Ptr} {bs : Array Byte} (h : m.read p 0 = some bs) :
    bs = #[] := by
  unfold Mem.read at h
  simp only [BEq.rfl, ↓reduceIte] at h
  exact (Option.some.inj h).symm

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

/-! ## Machine bytes -/

/-- A related byte other than `poison` determines its machine byte. -/
private theorem byteRel_fun {b : Byte} {y y' : BitVec 8} (h : ByteRel ι b y) (h' : ByteRel ι b y')
    (hb : b ≠ .poison) : y = y' := by
  cases b with
  | b x => exact h.symm.trans h'
  | frag p i =>
    obtain ⟨a, ha, rfl⟩ := h
    obtain ⟨a', ha', rfl⟩ := h'
    rw [ha] at ha'; cases ha'; rfl
  | poison => exact absurd rfl hb

/-- A 64-bit word is its eight bytes. -/
private theorem word_eq_of_bytes {x y : BitVec 64}
    (h : ∀ i, i < 8 → x.extractLsb' (8 * i) 8 = y.extractLsb' (8 * i) 8) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have := congrArg (fun z => z.getLsbD (k % 8)) (h (k / 8) (by omega))
  have hk8 : k % 8 < 8 := Nat.mod_lt _ (by decide)
  simp only [BitVec.getLsbD_extractLsb', hk8, decide_true, Bool.true_and] at this
  rwa [show 8 * (k / 8) + k % 8 = k by omega] at this

/-- Byte `i` of `intBytes` of a word is that byte of the word. -/
private theorem intBytes_byte (y : BitVec 64) (i : Nat) :
    BitVec.ofNat 8 (y.toNat / 2 ^ (8 * i)) = y.extractLsb' (8 * i) 8 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

private theorem extract_size {bs : Array Byte} {j : Nat} {e : Array Byte}
    (h : bs.extract j (j + 8) = e) (he : e.size = 8) : j + 8 ≤ bs.size := by
  have := congrArg Array.size h
  simp only [Array.size_extract, he] at this
  omega

private theorem extract_get {bs : Array Byte} {j : Nat} {e : Array Byte}
    (h : bs.extract j (j + 8) = e) (he : e.size = 8) {i : Nat} (hi : i < 8) :
    bs[j + i]? = e[i]? := by
  have hs := extract_size h he
  have hi' : i < (bs.extract j (j + 8)).size := by simp only [Array.size_extract]; omega
  rw [← h, Array.getElem?_eq_getElem hi', Array.getElem_extract,
    Array.getElem?_eq_getElem (by omega)]

private theorem ptrBytes_size (r : Ptr) : (ptrBytes r).size = 8 := by simp [ptrBytes]

private theorem intBytes_size (x : Nat) : (intBytes 8 x).size = 8 := by simp [intBytes]

private theorem ptrBytes_get (r : Ptr) {i : Nat} (hi : i < 8) :
    (ptrBytes r)[i]? = some (.frag r i) := by
  simp [ptrBytes, hi]

private theorem intBytes_get (x : Nat) {i : Nat} (hi : i < 8) :
    (intBytes 8 x)[i]? = some (.b (BitVec.ofNat 8 (x / 2 ^ (8 * i)))) := by
  simp [intBytes, hi]

/-- The machine bytes of a concrete word stored at `j` of a read are the word's. -/
private theorem mach_int (hA : AddrAgree ι) {m : Mem} {M : Memory} (h : MemInj ι m M)
    {p : Ptr} {a : BitVec 64} {n : Nat} {bs : Array Byte} (hn : 0 < n) (ha : ι p.blk = some a)
    (hr : m.read p n = some bs) {j : Nat} {y : BitVec 64}
    (hw : bs.extract j (j + 8) = intBytes 8 y.toNat) {i : Nat} (hi : i < 8) :
    M (a + p.off + BitVec.ofNat 64 (j + i)) = y.extractLsb' (8 * i) 8 := by
  obtain ⟨-, hb⟩ := read_rel hA h hn ha hr
  have hs := extract_size hw (intBytes_size _)
  have hg := extract_get hw (intBytes_size _) hi
  rw [intBytes_get _ hi, Array.getElem?_eq_getElem (by omega), Option.some.injEq] at hg
  have := hb (j + i) (by omega)
  rw [hg] at this
  exact this.symm.trans (intBytes_byte y i)

/-- The machine bytes of a word at `j` of a read that addresses a live `r` (`LiveWordAt`) are
those of `r`'s injected address. -/
private theorem mach_live (hA : AddrAgree ι) {m : Mem} {M : Memory} (h : MemInj ι m M)
    {p : Ptr} {a : BitVec 64} {n : Nat} {bs : Array Byte} (hn : 0 < n) (ha : ι p.blk = some a)
    (hr : m.read p n = some bs) {j : Nat} {r : Ptr} (hw : LiveWordAt m bs j r) :
    ∃ ar, ι r.blk = some ar ∧ ∀ i, i < 8 →
      M (a + p.off + BitVec.ofNat 64 (j + i)) = (ar + r.off).extractLsb' (8 * i) 8 := by
  obtain ⟨hw, al, hal, -⟩ := hw
  obtain ⟨ar, har, -⟩ := h.mapped _ _ hal
  refine ⟨ar, har, fun i hi => ?_⟩
  rcases hw with hw | ⟨y, hw, rfl⟩
  · obtain ⟨hsz, hb⟩ := read_rel hA h hn ha hr
    have hs := extract_size hw (ptrBytes_size _)
    have hg := extract_get hw (ptrBytes_size _) hi
    rw [ptrBytes_get _ hi, Array.getElem?_eq_getElem (by omega), Option.some.injEq] at hg
    have := hb (j + i) (by omega)
    rw [hg] at this
    obtain ⟨a', ha', hy⟩ := this
    rw [har] at ha'; cases ha'
    exact hy
  · rw [mach_int hA h hn ha hr hw hi,
      ptrRel_addr hA ⟨ar, har, rfl⟩ (Ptr.addr?_ofAddr y) (notTemp_ofAddr y)]

/-- Two different pointers into nonempty live allocations, before their ends, have different
injected addresses. -/
private theorem live_ne {m : Mem} {M : Memory} (h : MemInj ι m M) {r r' : Ptr}
    {al al' : Alloc} (hal : (r.blk, al) ∈ m.blocks) (hro : r.off.toNat < al.data.size)
    (hal' : (r'.blk, al') ∈ m.blocks) (hro' : r'.off.toNat < al'.data.size) (hne : r ≠ r')
    {ar ar' : BitVec 64} (har : ι r.blk = some ar) (har' : ι r'.blk = some ar') :
    ar + r.off ≠ ar' + r'.off := by
  intro he
  by_cases hb : r.blk = r'.blk
  · have hae : ar = ar' := by
      rw [hb, har'] at har; exact (Option.some.inj har).symm
    subst hae
    have ho : r.off = r'.off := (BitVec.add_right_inj ar).1 he
    exact hne (by cases r; cases r'; simp_all)
  · obtain ⟨a1, ha1, -, hhi1⟩ := h.mapped _ _ hal
    obtain ⟨a2, ha2, -, hhi2⟩ := h.mapped _ _ hal'
    rw [har] at ha1; cases ha1
    rw [har'] at ha2; cases ha2
    have hd := h.inj _ _ _ _ _ _ hal hal' hb har har'
    have h1 : (ar + r.off).toNat = ar.toNat + r.off.toNat := by
      rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have h2 : (ar' + r'.off).toNat = ar'.toNat + r'.off.toNat := by
      rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have := congrArg BitVec.toNat he
    omega

/-- A pointer into a nonempty live allocation, before its end, is not nil on the machine. -/
private theorem live_ne_zero {m : Mem} {M : Memory} (h : MemInj ι m M) {r : Ptr} {al : Alloc}
    (hal : (r.blk, al) ∈ m.blocks) (hro : r.off.toNat < al.data.size) {ar : BitVec 64}
    (har : ι r.blk = some ar) : ar + r.off ≠ 0 := by
  intro he
  obtain ⟨a1, ha1, hlo, hhi⟩ := h.mapped _ _ hal
  rw [har] at ha1; cases ha1
  have h1 : (ar + r.off).toNat = ar.toNat + r.off.toNat := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have h0 : (ar + r.off).toNat = 0 := by rw [he]; rfl
  have := hlo (by omega)
  omega

/-- A pointer-shaped register content of class 64 addresses, at offset 0, the pointer it reads
as (`Val.asPtrWord`). -/
private theorem addr_of_asPtrWord' {x : Val} {p : Ptr} (hf : Fits 64 x)
    (h : x.asPtrWord = some p) :
    Arm64.addr x 0 = some p := by
  cases x with
  | ptr q =>
    simp only [Val.asPtrWord, Option.some.injEq] at h
    subst h
    simp [Arm64.addr, Ptr.add]
  | int w y =>
    cases w <;> simp [Fits, Width.bits] at hf
    simp only [Val.asPtrWord, Option.some.injEq] at h
    subst h
    simp [Arm64.addr, Arm64.reg]
  | _ => simp [Val.asPtrWord] at h

/-! ## Phase 1's answer is the machine's -/

/-- **`memEq` against the machine** (G28): under `AddrAgree` and `MemInj`, with `p`, `q`, `n`
related to `X0`, `X1`, `X2` at class 64, a word `R` that is 1 if the `X2` machine bytes at `X0`
and `X1` agree and 0 if not (`runtime.memequal`'s result, `MemEqRes`) is related to `memEq`'s
answer when the bytes it compares differ, if at all, where the machine sees it (`MemEqDiff`). -/
theorem memEq_res (hA : AddrAgree ι) {mm : Mem} {M : Memory} (h : MemInj ι mm M)
    {x0 x1 x2 : Val} {X0 X1 X2 : BitVec 64} (h0 : ValRel ι x0 X0) (h1 : ValRel ι x1 X1)
    (h2 : ValRel ι x2 X2) (hf0 : Fits 64 x0) (hf1 : Fits 64 x1) (hf2 : Fits 64 x2)
    (hd : MemEqDiff mm x0 x1 x2) {R : BitVec 64}
    (hr : (MachBytesEq M X0 X1 X2 → R = 1) ∧ (¬ MachBytesEq M X0 X1 X2 → R = 0)) :
    ValRel ι (memEq [x0, x1, x2, .mem mm]) R := by
  cases x2
  case int w n =>
    cases w <;> simp [Fits, Width.bits] at hf2
    have hX2 : X2 = n := valRel_i64 hA h2
    subst hX2
    cases hp : x0.asPtrWord with
    | none => simp only [memEq, hp]; trivial
    | some p =>
    cases hq : x1.asPtrWord with
    | none => simp only [memEq, hp, hq]; trivial
    | some q =>
    cases hra : mm.read p X2.toNat with
    | none => simp only [memEq, hp, hq, hra]; trivial
    | some bs =>
    cases hrb : mm.read q X2.toNat with
    | none => simp only [memEq, hp, hq, hra, hrb]; trivial
    | some cs =>
    simp only [memEq, hp, hq, hra, hrb]
    split
    · trivial
    rename_i hpo
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hpo
    obtain ⟨hpa, hpb⟩ := hpo
    show R = if (bs == cs) = true then 1 else 0
    by_cases hz : X2.toNat = 0
    · rw [hz] at hra hrb
      rw [read_zero hra, read_zero hrb]
      exact hr.1 fun j hj => absurd hj (by omega)
    have hn : 0 < X2.toNat := by omega
    obtain ⟨a, ha, hX0, -⟩ := addr_rel hA h h0 hf0 (addr_of_asPtrWord' hf0 hp) hn
      (Or.inr (by rw [hra]; rfl))
    obtain ⟨b, hb, hX1, -⟩ := addr_rel hA h h1 hf1 (addr_of_asPtrWord' hf1 hq) hn
      (Or.inr (by rw [hrb]; rfl))
    have hX0' : X0 = a + p.off := by simpa using hX0
    have hX1' : X1 = b + q.off := by simpa using hX1
    subst hX0' hX1'
    obtain ⟨hsa, hba⟩ := read_rel hA h hn ha hra
    obtain ⟨hsb, hbb⟩ := read_rel hA h hn hb hrb
    have hnpa : ∀ j (hj : j < bs.size), bs[j] ≠ .poison := by
      intro j hj he
      have := Array.any_eq_false.1 hpa j hj
      simp [he] at this
    by_cases hab : bs = cs
    · subst hab
      simp only [beq_self_eq_true, ↓reduceIte]
      refine hr.1 fun j hj => ?_
      have hj' : j < bs.size := by omega
      exact byteRel_fun (hba j hj') (hbb j hj') (hnpa j hj')
    · simp only [beq_false_of_ne hab, Bool.false_eq_true, ↓reduceIte]
      refine hr.2 fun hme => ?_
      obtain ⟨j, hdj⟩ := hd p q .w64 X2 bs cs hp hq rfl hra hrb hpa hpb hab
      have hword : ∀ {W W' : BitVec 64} (k : Nat), k + 8 ≤ X2.toNat →
          (∀ i, i < 8 → M (a + p.off + BitVec.ofNat 64 (k + i)) = W.extractLsb' (8 * i) 8) →
          (∀ i, i < 8 → M (b + q.off + BitVec.ofNat 64 (k + i)) = W'.extractLsb' (8 * i) 8) →
          W = W' := by
        intro W W' k hk hW hW'
        exact word_eq_of_bytes fun i hi => by
          rw [← hW i hi, ← hW' i hi]; exact hme (k + i) (by omega)
      rcases hdj with ⟨x, y, hx, hy, hxy⟩ | ⟨r, r', hr1, hr2, hne⟩ | ⟨r, hr1, hz2⟩ | ⟨r, hz1, hr2⟩
      · have hj : j < bs.size := by
          rcases Nat.lt_or_ge j bs.size with hc | hc
          · exact hc
          · rw [Array.getElem?_eq_none hc] at hx; cases hx
        have hj' : j < cs.size := by omega
        rw [Array.getElem?_eq_getElem hj, Option.some.injEq] at hx
        rw [Array.getElem?_eq_getElem hj', Option.some.injEq] at hy
        have e1 := hba j hj
        have e2 := hbb j hj'
        rw [hx] at e1; rw [hy] at e2
        exact hxy (e1.trans ((hme j (by omega)).trans e2.symm))
      · have hk : j + 8 ≤ X2.toNat := by
          rw [← hsa]
          rcases hr1.1 with e | ⟨_, e, _⟩
          · exact extract_size e (ptrBytes_size _)
          · exact extract_size e (intBytes_size _)
        obtain ⟨ar, har, hW⟩ := mach_live hA h hn ha hra hr1
        obtain ⟨ar', har', hW'⟩ := mach_live hA h hn hb hrb hr2
        obtain ⟨-, al, hal, hro⟩ := hr1
        obtain ⟨-, al', hal', hro'⟩ := hr2
        exact live_ne h hal hro hal' hro' hne har har' (hword j hk hW hW')
      · have hk : j + 8 ≤ X2.toNat := by rw [← hsb]; exact extract_size hz2 (intBytes_size _)
        obtain ⟨ar, har, hW⟩ := mach_live hA h hn ha hra hr1
        have hW' := fun i (hi : i < 8) => mach_int hA h hn hb hrb (y := 0) (by simpa using hz2) hi
        obtain ⟨-, al, hal, hro⟩ := hr1
        exact live_ne_zero h hal hro har (hword j hk hW hW')
      · have hk : j + 8 ≤ X2.toNat := by rw [← hsa]; exact extract_size hz1 (intBytes_size _)
        obtain ⟨ar, har, hW'⟩ := mach_live hA h hn hb hrb hr2
        have hW := fun i (hi : i < 8) => mach_int hA h hn ha hra (y := 0) (by simpa using hz1) hi
        obtain ⟨-, al, hal, hro⟩ := hr2
        exact live_ne_zero h hal hro har (hword j hk hW hW').symm
  all_goals (simp only [memEq]; trivial)

/-- Bytes `memEq` finds equal satisfy `MemEqDiff` (they do not differ). -/
theorem memEqDiff_of_true {mm : Mem} {x0 x1 x2 : Val}
    (h : memEq [x0, x1, x2, .mem mm] = .bool true) : MemEqDiff mm x0 x1 x2 := by
  intro p q w n bs cs hp hq hn hra hrb hpa hpb hne
  subst hn
  simp only [memEq, hp, hq, hra, hrb, hpa, hpb, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
    Val.bool.injEq, beq_iff_eq] at h
  exact absurd h hne

end GoFV.Proof.Gen

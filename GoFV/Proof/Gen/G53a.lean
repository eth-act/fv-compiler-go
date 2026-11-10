import GoFV.Proof.Gen.G50
import GoFV.Proof.Gen.Spec53a

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G53, group A: `LoweredMove` (`docs/plans/proofs3.md` §4)

`vkind53a` (`GoFV/Gen/Check53a.lean`) accepts `LoweredMove [n] dst src mem`; `VK53a`
(`Spec53a.lean`) says what it accepted. `runLoc` runs it as the op's clobbers (`R25`, `F16`, `F17`
hold `poison`, `clobber_move`), then `Arm64.move`: the `n` bytes read at `src` written at `dst`, or
`poison` if either access is invalid (`stepLoc_lmove`).

Genssa emits nothing when `dst` and `src` share their register, else `moveTail`'s chunks, each a
load of 32, 16 or 8 bytes off `src` into the temporaries (`FLDPQ` into `V16`, `V17`; `FMOVQ` into
`V16`; `MOVD` into `X25`) and a store of them at the same offset off `dst` (`chunk_run`). A chunk
copies the bytes of its window (`cpW`, `wr_get`); the machine runs the chunks in order
(`move_run`) and changes nothing else but `X25`, `V16`, `V17` (`Keeps53`). The machine copies in
chunks while `Arm64.move` reads all `n` bytes before it writes, so the two agree when the source and
the destination are the same bytes or disjoint (`cpMem_get`); then every byte at `dst` is the
machine byte that was at `src`, related to the byte `runLoc` copied, and every other byte is
unchanged, which keeps `MemInj` (`memInj_writeAny`); the copied bytes lie inside a live block, away
from the frame (`SepFrom`), so the saved words and the spill slots keep their bytes.

The run premise `Pre53a` states exactly that: both accesses are valid (Go copies memory it owns)
and the two byte ranges are equal or disjoint (Go's `Move` never copies between partially
overlapping ranges). It is a property of the run, checkable on the state, not a trusted hook. The
registers the op clobbers are `poison` in `runLoc`'s state, related to anything; no other register
changes on either side. `LoweredMove` is in no upper-bit keep or entry table: after it the table
is empty (`uStep35_53a`). `vk53a_step` is one value.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The premise -/

/-- `LoweredMove [n] dst src mem` reads `n` valid bytes at `src` and writes them at `dst` (Go
copies memory it owns), and the two byte ranges are equal or disjoint (Go's `Move` never copies
between partially overlapping ones). -/
def Pre53a (lc : LocCtx) (s : LocState) (v : Value) : Prop :=
  v.op = .ARM64LoweredMove → ∀ d x a y, v.args[0]? = some d → s.read lc d = .ok x →
    v.args[1]? = some a → s.read lc a = .ok y →
    ∃ pd ps mm bs mm', Arm64.addr x 0 = some pd ∧ Arm64.addr y 0 = some ps ∧ s.mem = .mem mm ∧
      mm.read ps v.auxInt.toInt.toNat = some bs ∧ mm.write pd bs = some mm' ∧
      (pd = ps ∨ pd.blk ≠ ps.blk ∨ pd.off.toNat + v.auxInt.toInt.toNat ≤ ps.off.toNat ∨
        ps.off.toNat + v.auxInt.toInt.toNat ≤ pd.off.toNat)

/-! ## `stepLoc` of `LoweredMove` -/

/-- After `LoweredMove` the upper-bit table is empty. -/
private theorem uStep35_53a {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value}
    (hop : v.op = .ARM64LoweredMove) : uStep35 lc L v = [] := by
  simp [uStep35, ldEntry35, loadOp?, narrowLoad?, pairOp35, uStep34, keep34, keep31, keepOp31,
    keepOp34, uStepL, uEntry, narrowLd?, loadIdxOp?, hop]

private theorem move_noArg0 : Op.ARM64LoweredMove.regInfo.clobbersArg0 = false := by decide

private theorem move_noArg1 : Op.ARM64LoweredMove.regInfo.clobbersArg1 = false := by decide

private theorem move_mask_ne : Op.ARM64LoweredMove.regInfo.clobbers.isEmpty = false := by decide

private theorem move_flags : Op.ARM64LoweredMove.clobberFlags = false := by decide

private theorem move_mask24 : Op.ARM64LoweredMove.regInfo.clobbers.hasReg 24 = true := by decide

private theorem move_mask47 : Op.ARM64LoweredMove.regInfo.clobbers.hasReg 47 = true := by decide

private theorem move_mask48 : Op.ARM64LoweredMove.regInfo.clobbers.hasReg 48 = true := by decide

section Step

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

/-- `LoweredMove`'s clobbers: its mask (`R25`, `F16`, `F17`); no argument, temporary or flags. -/
private theorem clobber_move (hop : v.op = .ARM64LoweredMove)
    (ht : (lc.temps[v.id]?).join = none) :
    s.clobber lc v = s.clobberMask Op.ARM64LoweredMove.regInfo.clobbers := by
  unfold LocState.clobber
  simp only [hop, move_noArg0, move_noArg1, ht, move_flags, Bool.not_false, Bool.false_eq_true,
    ↓reduceIte]

/-- `clobberMask` keeps the slots, the flags and the memory. -/
private theorem clobberMask_keeps (s : LocState) (msk : RegMask) :
    (s.clobberMask msk).slots = s.slots ∧ (s.clobberMask msk).flags = s.flags ∧
      (s.clobberMask msk).mem = s.mem := by
  unfold LocState.clobberMask; split <;> exact ⟨rfl, rfl, rfl⟩

/-- A register after `LoweredMove`'s clobbers: `poison`, or kept and none of `R25`, `F16`,
`F17`. -/
private theorem clobberMask_move {r : Nat} {x : Val}
    (h : (s.clobberMask Op.ARM64LoweredMove.regInfo.clobbers).regs[r]? = some x) :
    x = .poison ∨ (s.regs[r]? = some x ∧ r ≠ 24 ∧ r ≠ 47 ∧ r ≠ 48) := by
  simp only [LocState.clobberMask, move_mask_ne, Bool.false_eq_true, ↓reduceIte,
    Array.getElem?_mapIdx] at h
  cases hr : s.regs[r]? with
  | none => rw [hr] at h; cases h
  | some y =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq] at h
    by_cases hm : Op.ARM64LoweredMove.regInfo.clobbers.hasReg r = true
    · left; rw [if_pos hm] at h; exact h.symm
    · right
      rw [if_neg hm] at h
      refine ⟨by rw [h], ?_, ?_, ?_⟩ <;> rintro rfl
      · exact hm move_mask24
      · exact hm move_mask47
      · exact hm move_mask48

/-- `LoweredMove [n] dst src mem`: its clobbers, then `Arm64.move` of its arguments (the memory
after the copy, or `poison`) as the memory. -/
private theorem stepLoc_lmove (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .ARM64LoweredMove) {d a mem : ID} (ha : v.args = #[d, a, mem]) {mm : Mem}
    (hmem : s.read lc mem = .ok (.mem mm)) (h : stepLoc env lc s v = .ok s') :
    ∃ x y, s.read lc d = .ok x ∧ s.read lc a = .ok y ∧
      s' = (s.clobberMask Op.ARM64LoweredMove.regInfo.clobbers).write lc v.id
        ((Arm64.move v.auxInt [x, y, .mem mm]).retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, hmv, hr, rfl⟩ := stepLoc_ok_eval (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) h
  rw [ha] at hmv
  change ((s.read lc d).bind fun x => (s.read lc a).bind fun y => (s.read lc mem).bind
    fun z => .ok [x, y, z]) = .ok argv at hmv
  cases hx : s.read lc d with
  | panic e m0 => rw [hx] at hmv; cases hmv
  | stuck msg => rw [hx] at hmv; cases hmv
  | ok x =>
  cases hy : s.read lc a with
  | panic e m0 => rw [hx, hy] at hmv; cases hmv
  | stuck msg => rw [hx, hy] at hmv; cases hmv
  | ok y =>
    rw [hx, hy, hmem] at hmv
    cases hmv
    refine ⟨x, y, rfl, rfl, ?_⟩
    rw [clobber_move hop ht, lmode_retype hl]
    cases hnf : nilFaults true lc.ctx v [x, y, .mem mm] with
    | some m0 =>
      have he : evalOpL true env lc.ctx s.fr v [x, y, .mem mm] (lc.ty v.id) =
          .panic .nilDeref m0 := by
        unfold evalOpL arm64Op
        simp only [hop, hnf]
        rfl
      rw [he] at hr
      cases hr
    | none =>
      have he : evalOpL true env lc.ctx s.fr v [x, y, .mem mm] (lc.ty v.id) =
          .ok (Arm64.move v.auxInt [x, y, .mem mm]) := by
        unfold evalOpL arm64Op
        simp only [hop, hnf]
        rfl
      rw [he] at hr
      cases hr
      rfl

end Step

/-! ## Registers -/

/-- A Go register other than `R25` has no X register `X25`. -/
theorem objX?_ne25 {r : Nat} {k : Reg} (h : objX? r = some k) (hr : r ≠ 24) :
    k ≠ 25 := by
  intro he
  subst he
  unfold objX? at h
  split at h
  · have := congrArg BitVec.toNat (Option.some.inj h); simp at this; omega
  · split at h
    · have := congrArg BitVec.toNat (Option.some.inj h); simp at this; omega
    · split at h
      · have := congrArg BitVec.toNat (Option.some.inj h); simp at this; omega
      · cases h

/-- A Go register other than `F16`, `F17` has neither `V16` nor `V17`. -/
theorem objV?_ne1617 {r : Nat} {k : Reg} (h : objV? r = some k) (h47 : r ≠ 47)
    (h48 : r ≠ 48) : k ≠ 16 ∧ k ≠ 17 := by
  obtain ⟨h1, h2, rfl⟩ := objV?_some h
  constructor <;> intro he <;> have := congrArg BitVec.toNat he <;> simp at this <;> omega

/-! ## Machine bytes -/

theorem extract_extract53 {k : Nat} (V : BitVec (8 * (k + 1))) (t : Nat) (h1 : 1 ≤ t)
    (h2 : t ≤ k) :
    (V.extractLsb' 8 (8 * k)).extractLsb' (8 * (t - 1)) 8 = V.extractLsb' (8 * t) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb']
  have e : 8 + (8 * (t - 1) + i) = 8 * t + i := by omega
  simp [hi, e, show 8 * (t - 1) + i < 8 * k by omega]

/-- The byte at `y` after an `k`-byte write at `A`: byte `y - A` of the value inside the window,
the old byte elsewhere. -/
theorem writeMem_get : ∀ (k : Nat) (M : Memory) (A : BitVec 64) (V : BitVec (8 * k))
    (y : BitVec 64), k < 2 ^ 64 →
    writeMem M A k V y = if (y - A).toNat < k then V.extractLsb' (8 * (y - A).toNat) 8 else M y
  | 0, M, A, V, y, _ => by simp [writeMem]
  | k + 1, M, A, V, y, hk => by
    rw [writeMem, writeMem_get k _ (A + 1) _ y (by omega)]
    by_cases h0 : y = A
    · subst h0
      have h1 : ¬ (y - (y + 1)).toNat < k := by bv_omega
      simp only [h1, ↓reduceIte]
      simp
    · have hne : (y - A).toNat ≠ 0 := by bv_omega
      have he : (y - (A + 1)).toNat = (y - A).toNat - 1 := by bv_omega
      rw [he]
      by_cases ht : (y - A).toNat - 1 < k
      · rw [if_pos ht, if_pos (by omega), extract_extract53 V _ (by omega) (by omega)]
      · have ht' : ¬ (y - A).toNat < k + 1 := by omega
        rw [if_neg ht, if_neg ht']
        exact if_neg h0

/-- Byte `j` of a `k`-byte read at `A` is the byte at `A + j`. -/
theorem readMem_get (M : Memory) (A : BitVec 64) {k j : Nat} (hj : j < k) :
    (readMem M A k).extractLsb' (8 * j) 8 = M (A + BitVec.ofNat 64 j) := by
  apply BitVec.eq_of_toNat_eq
  rw [← readMem_byte M k A j hj, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

/-- The `k` bytes of a `k`-byte read, stored from a register of at least `8k` bits. -/
theorem ofNat_rd {k w : Nat} (B : BitVec (8 * k)) (h : 8 * k ≤ w) :
    BitVec.ofNat (8 * k) ((B.setWidth w).toNat % 2 ^ (8 * k)) = B := by
  apply BitVec.eq_of_toNat_eq
  have hB := B.isLt
  have hp : 2 ^ (8 * k) ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) h
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (by omega : B.toNat < 2 ^ w), Nat.mod_mod, Nat.mod_eq_of_lt hB]

/-- The machine memory after a chunk copies the `w` bytes at offset `o` from `S` to `D`. -/
def cpW (S D : BitVec 64) (M : Memory) (o w : Nat) : Memory := fun y =>
  if o ≤ (y - D).toNat ∧ (y - D).toNat < o + w then M (S + (y - D)) else M y

/-- The machine memory after the chunks `cs` (kind, offset) copy from `S` to `D`, in order. -/
def cpMem (S D : BitVec 64) (M : Memory) (cs : List (Nat × Nat)) : Memory :=
  cs.foldl (fun M c => cpW S D M c.2 (moveW c.1)) M

/-- A `w`-byte write at `D + o` of the `w` bytes read at `S + o` in `M`: inside the window, the
byte of `M` at the same distance from `S`. -/
theorem wr_get {M M' : Memory} {S D y : BitVec 64} {o w : Nat} (hw : o + w < 2 ^ 64) :
    writeMem M' (D + BitVec.ofNat 64 o) w (readMem M (S + BitVec.ofNat 64 o) w) y =
      if o ≤ (y - D).toNat ∧ (y - D).toNat < o + w then M (S + (y - D)) else M' y := by
  rw [writeMem_get w M' _ _ y (by omega)]
  have ht : (y - (D + BitVec.ofNat 64 o)).toNat < w ↔
      o ≤ (y - D).toNat ∧ (y - D).toNat < o + w := by bv_omega
  by_cases hc : o ≤ (y - D).toNat ∧ (y - D).toNat < o + w
  · rw [if_pos (ht.2 hc), if_pos hc, readMem_get _ _ (ht.2 hc)]
    congr 1
    bv_omega
  · rw [if_neg (fun h => hc (ht.1 h)), if_neg hc]

/-- The chunks copy: when the source and the destination are the same bytes or the source lies
outside the `n` bytes at `D`, and every chunk lies inside the `n` bytes, a byte some chunk covers
is the byte at the same distance from `S`, and every other byte is unchanged. -/
theorem cpMem_get {S D : BitVec 64} {n : Nat}
    (hsd : S = D ∨ ∀ k, k < n → n ≤ (S + BitVec.ofNat 64 k - D).toNat) :
    ∀ (cs : List (Nat × Nat)) (M : Memory), (∀ c ∈ cs, c.2 + moveW c.1 ≤ n) → ∀ y,
      cpMem S D M cs y = if ∃ c ∈ cs, c.2 ≤ (y - D).toNat ∧ (y - D).toNat < c.2 + moveW c.1
        then M (S + (y - D)) else M y
  | [], M, _, y => by simp [cpMem]
  | c :: rest, M, hcs, y => by
    have ih := cpMem_get hsd rest (cpW S D M c.2 (moveW c.1))
      (fun c' h => hcs c' (List.mem_cons_of_mem _ h)) y
    unfold cpMem at ih ⊢
    rw [List.foldl_cons, ih]
    by_cases hr : ∃ c' ∈ rest, c'.2 ≤ (y - D).toNat ∧ (y - D).toNat < c'.2 + moveW c'.1
    · obtain ⟨c', hc'm, hc'⟩ := hr
      have hc'n := hcs c' (List.mem_cons_of_mem _ hc'm)
      rw [if_pos ⟨c', hc'm, hc'⟩, if_pos ⟨c', List.mem_cons_of_mem _ hc'm, hc'⟩]
      unfold cpW
      rcases hsd with rfl | hsd
      · have hy : S + (y - S) = y := by bv_omega
        split <;> simp only [hy]
      · have hk := hsd (y - D).toNat (by omega)
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hk
        have hcn := hcs c List.mem_cons_self
        rw [if_neg (by omega)]
    · rw [if_neg hr]
      unfold cpW
      by_cases hcy : c.2 ≤ (y - D).toNat ∧ (y - D).toNat < c.2 + moveW c.1
      · rw [if_pos hcy, if_pos ⟨c, List.mem_cons_self, hcy⟩]
      · rw [if_neg hcy, if_neg]
        rintro ⟨c', hm, hc'⟩
        rcases List.mem_cons.1 hm with rfl | hm
        · exact hcy hc'
        · exact hr ⟨c', hm, hc'⟩

/-! ## The machine's chunks -/

/-- `m'` is `m` but for `X25`, `V16`, `V17`, the memory and the PC. -/
def Keeps53 (m m' : MState) : Prop :=
  m'.sp = m.sp ∧ m'.nzcv = m.nzcv ∧ (∀ q : Reg, q ≠ 25 → m'.x q = m.x q) ∧
    ∀ q : Reg, q ≠ 16 → q ≠ 17 → m'.v q = m.v q

theorem Keeps53.trans {m m' m'' : MState} (h : Keeps53 m m') (h' : Keeps53 m' m'') :
    Keeps53 m m'' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, fun q hq => (h'.2.2.1 q hq).trans (h.2.2.1 q hq),
    fun q h16 h17 => (h'.2.2.2 q h16 h17).trans (h.2.2.2 q h16 h17)⟩

theorem Keeps53.rX {m m' : MState} (h : Keeps53 m m') {r : Reg} (hr : r ≠ 25) :
    m'.rX r = m.rX r := by
  unfold MState.rX
  split
  · rfl
  · exact h.2.2.1 r hr

theorem reg_ne25 {k : Nat} (hk : k < 32) (h : k ≠ 25) : (BitVec.ofNat 5 k : Reg) ≠ 25 := by
  intro he
  have := congrArg BitVec.toNat he
  simp at this
  omega

theorem ofInt_nat (o : Nat) : BitVec.ofInt 64 (o : Int) = BitVec.ofNat 64 o := by
  apply BitVec.eq_of_toNat_eq; simp

theorem eff_wV16 {e : Eff} {val : BitVec 128} :
    e.wV f16A val = .ok { e with v := (16, val) :: e.v } := eff_wV_f0 (k := 16) (by decide)

theorem eff_wV17 {e : Eff} {val : BitVec 128} :
    e.wV f17A val = .ok { e with v := (17, val) :: e.v } := eff_wV_f0 (k := 17) (by decide)

theorem ctx_v16 {c : ProgCtx} : c.v f16A = .ok (c.s.v (BitVec.ofNat 5 16)) :=
  ctx_v_f0 (k := 16) (by decide)

theorem ctx_v17 {c : ProgCtx} : c.v f17A = .ok (c.s.v (BitVec.ofNat 5 17)) :=
  ctx_v_f0 (k := 17) (by decide)

/-- `FLDPQ` at the address `A` of its operand: the 16 bytes at `A` into `V16`, the 16 above into
`V17`. -/
private theorem eff_fldpq {c : ProgCtx} {A : BitVec 64} (has : c.p.as = .FLDPQ)
    (hma : c.mem c.p.from_ = .ok (A, none)) (ht : c.p.to = pairA f16A f17A) :
    progEffect c = .ok
      { v := [(17, (readMem c.s.mem (A + BitVec.ofNat 64 16) 16).setWidth 128),
              (16, (readMem c.s.mem A 16).setWidth 128)],
        loads := [(A + BitVec.ofNat 64 16, 16), (A, 16)] } := by
  have hname : As.name .FLDPQ = "FLDPQ" := rfl
  unfold progEffect
  simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
    ProgOp.movMem, ProgOp.pairOp, ht, pairA, hma, Eff.ld, eff_wV16, eff_wV17]
  rfl

/-- `FSTPQ (F16, F17)` at the address `A` of its operand: the 16 bytes of `V16` at `A`, then those
of `V17` 16 bytes above. -/
private theorem eff_fstpq {c : ProgCtx} {A : BitVec 64} (has : c.p.as = .FSTPQ)
    (hf : c.p.from_ = pairA f16A f17A) (hma : c.mem c.p.to = .ok (A, none)) :
    progEffect c = .ok
      { stores := [(A, 16, (c.s.v (BitVec.ofNat 5 16)).toNat % 2 ^ (8 * 16)),
        (A + BitVec.ofNat 64 16, 16, (c.s.v (BitVec.ofNat 5 17)).toNat % 2 ^ (8 * 16))] } := by
  have hname : As.name .FSTPQ = "FSTPQ" := rfl
  unfold progEffect
  simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
    ProgOp.movMem, ProgOp.pairOp, hf, pairA, hma, ctx_v16, ctx_v17]
  rfl

section Machine

variable {L : Link} {p : Prog} {s : MState} {next : BitVec 64}

/-- `FLDPQ off(Rn), (F16, F17)`, both addresses outside the nil page. -/
private theorem progStep_fldpq {kn : Nat} {off : Int} (hkn : kn < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .FLDPQ)
    (hf : p.from_ = memA (REG_R0 + kn) off) (hsc : p.scond = 0) (ht : p.to = pairA f16A f17A)
    (hnil : nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off) = false)
    (hnil16 : nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off + BitVec.ofNat 64 16) =
      false) :
    progStep L p s = .ok { (s.wV (BitVec.ofNat 5 16)
        ((readMem s.mem (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off) 16).setWidth 128)).wV
        (BitVec.ofNat 5 17)
        ((readMem s.mem (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off + BitVec.ofNat 64 16)
          16).setWidth 128) with
      pc := next } := by
  have hma := ctx_mem_reg (c := ⟨L, s, p⟩) hkn hsc (off := off)
  rw [← hf] at hma
  have he := eff_fldpq (c := ⟨L, s, p⟩) has hma ht
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
    (by simp [Eff.nilAccess?, List.find?, hnil, hnil16])]
  simp only [Eff.apply, List.foldr]
  rfl

/-- `FSTPQ (F16, F17), off(Rn)`, both addresses outside the nil page. -/
private theorem progStep_fstpq {kn : Nat} {off : Int} (hkn : kn < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .FSTPQ) (hf : p.from_ = pairA f16A f17A)
    (hsc : p.scond = 0) (ht : p.to = memA (REG_R0 + kn) off)
    (hnil : nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off) = false)
    (hnil16 : nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off + BitVec.ofNat 64 16) =
      false) :
    progStep L p s = .ok { s with
      mem := writeMem (writeMem s.mem (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off) 16
          (BitVec.ofNat (8 * 16) ((s.v (BitVec.ofNat 5 16)).toNat % 2 ^ (8 * 16))))
        (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off + BitVec.ofNat 64 16) 16
          (BitVec.ofNat (8 * 16) ((s.v (BitVec.ofNat 5 17)).toNat % 2 ^ (8 * 16))),
      pc := next } := by
  have hma := ctx_mem_reg (c := ⟨L, s, p⟩) hkn hsc (off := off)
  rw [← ht] at hma
  have he := eff_fstpq (c := ⟨L, s, p⟩) has hf hma
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
    (by simp [Eff.nilAccess?, List.find?, hnil, hnil16])]
  rfl

end Machine

theorem wX_fields {m : MState} {r : Reg} {val : BitVec 64} :
    (m.wX r val).mem = m.mem ∧ (m.wX r val).sp = m.sp ∧ (m.wX r val).nzcv = m.nzcv ∧
      (m.wX r val).v = m.v := by
  unfold MState.wX; split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem wX_x_of_ne {m : MState} {r q : Reg} {val : BitVec 64} (h : q ≠ r) :
    (m.wX r val).x q = m.x q := by
  unfold MState.wX
  split
  · rfl
  · simp [h]

theorem nil_of {A : BitVec 64} {d : Nat} (h1 : 4096 ≤ A.toNat)
    (h2 : A.toNat + d < 2 ^ 64) : nilPage (A + BitVec.ofNat 64 d) = false := by
  simp only [nilPage, decide_eq_false_iff_not, Nat.not_lt]
  bv_omega

section Run

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64}

/-- One chunk, its load off `X ks` (holding `S`) then its store off `X kd` (holding `D`): the
machine copies the chunk's bytes and changes only `X25`, `V16`, `V17`. -/
theorem chunk_run (hnd : (psA.toList.map (·.id)).Nodup)
    (hlt : ∀ p ∈ psA.toList, p.id < 2 ^ 32)
    (hret : ∀ p ∈ psA.toList, (Link.byId sym text az ez psA.toList).addr p.id ≠ some ret)
    {ks kd : Nat} (hks : ks < 32) (hkd : kd < 32) (hkd25 : kd ≠ 25) {S D : BitVec 64}
    {c : Nat × Nat} {j k j' : Nat} {m : MState}
    (h1 : OneAt2 psA j (moveLd (REG_R0 + ks) c) k) (h2 : OneAt2 psA k (moveSt (REG_R0 + kd) c) j')
    (hS : m.rX (BitVec.ofNat 5 ks) = S) (hD : m.rX (BitVec.ofNat 5 kd) = D)
    (hSb : 4096 ≤ S.toNat ∧ S.toNat + c.2 + moveW c.1 ≤ 2 ^ 64)
    (hDb : 4096 ≤ D.toNat ∧ D.toNat + c.2 + moveW c.1 ≤ 2 ^ 64) :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret
        { m with pc := pcAt text psA.toList j } m' ∧
      m'.pc = pcAt text psA.toList j' ∧ m'.mem = cpW S D m.mem c.2 (moveW c.1) ∧ Keeps53 m m' := by
  obtain ⟨w, o⟩ := c
  dsimp only at h1 h2 hSb hDb ⊢
  have hkd' := reg_ne25 hkd hkd25
  obtain ⟨k0, rfl, hk0, hok0, hst0⟩ := pstar_oneAt2 (H := H) hnd hlt hret h1 m
  by_cases h32 : w = 32
  · subst h32
    simp only [moveLd, moveSt, ↓reduceIte] at hok0 h2
    simp only [moveW, ↓reduceIte] at hSb hDb ⊢
    obtain ⟨has0, hf0, -, ht0, hsc0⟩ := Shape.ok_eq hok0
    have hstep0 := progStep_fldpq (L := Link.byId sym text az ez psA.toList)
      (s := { m with pc := pcAt text psA.toList k0 }) hks (nextAddr_pcAt hnd hk0) has0 hf0 hsc0
      ht0 (by show nilPage (m.rX (BitVec.ofNat 5 ks) + _) = false
              rw [hS, ofInt_nat]; exact nil_of hSb.1 (by omega))
      (by show nilPage (m.rX (BitVec.ofNat 5 ks) + _ + _) = false
          rw [hS, ofInt_nat, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
          exact nil_of hSb.1 (by omega))
    let m1 : MState := (m.wV (BitVec.ofNat 5 16)
        ((readMem m.mem (m.rX (BitVec.ofNat 5 ks) + BitVec.ofInt 64 o) 16).setWidth 128)).wV
        (BitVec.ofNat 5 17)
        ((readMem m.mem (m.rX (BitVec.ofNat 5 ks) + BitVec.ofInt 64 o + BitVec.ofNat 64 16)
          16).setWidth 128)
    obtain ⟨k1, rfl, hk1, hok1, hst1⟩ := pstar_oneAt2 (H := H) hnd hlt hret h2 m1
    obtain ⟨has1, hf1, -, ht1, hsc1⟩ := Shape.ok_eq hok1
    have hm1D : m1.rX (BitVec.ofNat 5 kd) = D := hD
    have hstep1 := progStep_fstpq (L := Link.byId sym text az ez psA.toList)
      (s := { m1 with pc := pcAt text psA.toList k1 }) hkd (nextAddr_pcAt hnd hk1) has1 hf1 hsc1
      ht1 (by show nilPage (m1.rX (BitVec.ofNat 5 kd) + _) = false
              rw [hm1D, ofInt_nat]; exact nil_of hDb.1 (by omega))
      (by show nilPage (m1.rX (BitVec.ofNat 5 kd) + _ + _) = false
          rw [hm1D, ofInt_nat, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
          exact nil_of hDb.1 (by omega))
    refine ⟨_, ((hst0.tail (pstep_at hnd hlt hret hk0 rfl hstep0)).trans hst1).tail
      (pstep_at hnd hlt hret hk1 rfl hstep1), rfl, ?_, ⟨rfl, rfl, fun _ _ => rfl, fun q h16 h17 => ?_⟩⟩
    · funext y
      show writeMem (writeMem m.mem (m1.rX (BitVec.ofNat 5 kd) + BitVec.ofInt 64 o) 16
          (BitVec.ofNat (8 * 16) ((m1.v (BitVec.ofNat 5 16)).toNat % 2 ^ (8 * 16))))
        (m1.rX (BitVec.ofNat 5 kd) + BitVec.ofInt 64 o + BitVec.ofNat 64 16) 16
          (BitVec.ofNat (8 * 16) ((m1.v (BitVec.ofNat 5 17)).toNat % 2 ^ (8 * 16))) y = _
      have hv16 : m1.v (BitVec.ofNat 5 16) =
          (readMem m.mem (S + BitVec.ofNat 64 o) 16).setWidth 128 := by
        simp [m1, MState.wV, hS, ofInt_nat]
      have hv17 : m1.v (BitVec.ofNat 5 17) =
          (readMem m.mem (S + BitVec.ofNat 64 (o + 16)) 16).setWidth 128 := by
        simp [m1, MState.wV, hS, ofInt_nat, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      rw [hv16, hv17, hm1D, ofInt_nat, ofNat_rd _ (by decide), ofNat_rd _ (by decide),
        BitVec.add_assoc, BitVec.ofNat_add_ofNat, wr_get (by omega), wr_get (by omega)]
      unfold cpW
      by_cases ha : o + 16 ≤ (y - D).toNat ∧ (y - D).toNat < o + 16 + 16
      · rw [if_pos ha, if_pos (by omega)]
      · rw [if_neg ha]
        by_cases hb : o ≤ (y - D).toNat ∧ (y - D).toNat < o + 16
        · rw [if_pos hb, if_pos (by omega)]
        · rw [if_neg hb, if_neg (by omega)]
    · show (if q = BitVec.ofNat 5 17 then _ else
        (if q = BitVec.ofNat 5 16 then _ else m.v q)) = m.v q
      rw [if_neg (show ¬ q = BitVec.ofNat 5 17 from h17),
        if_neg (show ¬ q = BitVec.ofNat 5 16 from h16)]
  by_cases h16 : w = 16
  · subst h16
    simp only [moveLd, moveSt, ↓reduceIte, show (16 : Nat) ≠ 32 by decide] at hok0 h2
    simp only [moveW, ↓reduceIte, show (16 : Nat) ≠ 32 by decide] at hSb hDb ⊢
    obtain ⟨has0, hf0, -, ht0, hsc0⟩ := Shape.ok_eq hok0
    dsimp only at has0 hf0 ht0
    have hma0 := ctx_mem_reg (c := ⟨Link.byId sym text az ez psA.toList,
      { m with pc := pcAt text psA.toList k0 }, psA.toList[k0]⟩) hks hsc0 (off := o)
    rw [← hf0] at hma0
    have hstep0 := progStep_floadAt (n := 16) (kd := 16) (by decide) (nextAddr_pcAt hnd hk0)
      (by rw [has0]; rfl) (by rw [hf0]; rfl) hma0 (by rw [ht0]; rfl)
      (by show nilPage (m.rX (BitVec.ofNat 5 ks) + _) = false
          rw [hS, ofInt_nat]; exact nil_of hSb.1 (by omega))
    let m1 : MState := m.wV (BitVec.ofNat 5 16)
      ((readMem m.mem (m.rX (BitVec.ofNat 5 ks) + BitVec.ofInt 64 o) 16).setWidth 128)
    obtain ⟨k1, rfl, hk1, hok1, hst1⟩ := pstar_oneAt2 (H := H) hnd hlt hret h2 m1
    obtain ⟨has1, hf1, -, ht1, hsc1⟩ := Shape.ok_eq hok1
    dsimp only at has1 hf1 ht1
    have hm1D : m1.rX (BitVec.ofNat 5 kd) = D := hD
    have hma1 := ctx_mem_reg (c := ⟨Link.byId sym text az ez psA.toList,
      { m1 with pc := pcAt text psA.toList k1 }, psA.toList[k1]⟩) hkd hsc1 (off := o)
    rw [← ht1] at hma1
    have hstep1 := progStep_fstoreAt (n := 16) (ks := 16) (by decide) (nextAddr_pcAt hnd hk1)
      (by rw [has1]; rfl) (by rw [hf1]; rfl) (by rw [ht1]; rfl) hma1
      (by show nilPage (m1.rX (BitVec.ofNat 5 kd) + _) = false
          rw [hm1D, ofInt_nat]; exact nil_of hDb.1 (by omega))
    refine ⟨_, ((hst0.tail (pstep_at hnd hlt hret hk0 rfl hstep0)).trans hst1).tail
      (pstep_at hnd hlt hret hk1 rfl hstep1), rfl, ?_, ⟨rfl, rfl, fun _ _ => rfl, fun q h16 _ => ?_⟩⟩
    · funext y
      show writeMem m.mem (m1.rX (BitVec.ofNat 5 kd) + BitVec.ofInt 64 o) 16
          (BitVec.ofNat (8 * 16) ((m1.v (BitVec.ofNat 5 16)).toNat % 2 ^ (8 * 16))) y = _
      have hv16 : m1.v (BitVec.ofNat 5 16) =
          (readMem m.mem (S + BitVec.ofNat 64 o) 16).setWidth 128 := by
        simp [m1, MState.wV, hS, ofInt_nat]
      rw [hv16, hm1D, ofInt_nat, ofNat_rd _ (by decide), wr_get (by omega)]
      rfl
    · show (if q = BitVec.ofNat 5 16 then _ else m.v q) = m.v q
      rw [if_neg (show ¬ q = BitVec.ofNat 5 16 from h16)]
  · simp only [moveLd, moveSt, h32, h16, ↓reduceIte] at hok0 h2
    simp only [moveW, h32, h16, ↓reduceIte] at hSb hDb ⊢
    obtain ⟨has0, hf0, -, ht0, hsc0⟩ := Shape.ok_eq hok0
    have hstep0 := progStep_load (L := Link.byId sym text az ez psA.toList)
      (s := { m with pc := pcAt text psA.toList k0 }) hks (kd := 25) (by decide)
      (nextAddr_pcAt hnd hk0) has0 hf0 hsc0 (by rw [ht0]; rfl)
      (by show nilPage (m.rX (BitVec.ofNat 5 ks) + _) = false
          rw [hS, ofInt_nat]; exact nil_of hSb.1 (by omega))
    let m1 : MState := m.wX (BitVec.ofNat 5 25)
      ((readMem m.mem (m.rX (BitVec.ofNat 5 ks) + BitVec.ofInt 64 o) 8).setWidth 64)
    have e0 : progStep (Link.byId sym text az ez psA.toList) psA.toList[k0]
        { m with pc := pcAt text psA.toList k0 } =
        .ok { m1 with pc := pcAt text psA.toList (k0 + 1) } := by
      rw [hstep0]
      rfl
    obtain ⟨k1, rfl, hk1, hok1, hst1⟩ := pstar_oneAt2 (H := H) hnd hlt hret h2 m1
    obtain ⟨has1, hf1, -, ht1, hsc1⟩ := Shape.ok_eq hok1
    obtain ⟨hm1mem, hm1sp, hm1nz, hm1v⟩ := wX_fields (m := m) (r := BitVec.ofNat 5 25)
      (val := (readMem m.mem (m.rX (BitVec.ofNat 5 ks) + BitVec.ofInt 64 o) 8).setWidth 64)
    have hm1D : m1.rX (BitVec.ofNat 5 kd) = D := by
      rw [← hD]; unfold MState.rX; split
      · rfl
      · exact wX_x_of_ne hkd'
    have hrx25 : ∀ val : BitVec 64,
        (m.wX (BitVec.ofNat 5 25) val).rX (BitVec.ofNat 5 25) = val := fun val => by
      simp [MState.rX, MState.wX]
    have hm1R : m1.rX (BitVec.ofNat 5 25) =
        (readMem m.mem (S + BitVec.ofNat 64 o) 8).setWidth 64 := by
      show (m.wX _ _).rX _ = _
      rw [hrx25, hS, ofInt_nat]
    have hstep1 := progStep_store (L := Link.byId sym text az ez psA.toList)
      (s := { m1 with pc := pcAt text psA.toList k1 }) hkd (ks := 25) (by decide)
      (nextAddr_pcAt hnd hk1) has1 (by rw [hf1]; rfl) hsc1 ht1
      (by show nilPage (m1.rX (BitVec.ofNat 5 kd) + _) = false
          rw [hm1D, ofInt_nat]; exact nil_of hDb.1 (by omega))
    refine ⟨_, ((hst0.tail (pstep_at hnd hlt hret hk0 rfl e0)).trans hst1).tail
      (pstep_at hnd hlt hret hk1 rfl hstep1), rfl, ?_,
      ⟨hm1sp, hm1nz, fun q hq => wX_x_of_ne hq, fun q _ _ => by rw [hm1v]⟩⟩
    funext y
    show writeMem m1.mem (m1.rX (BitVec.ofNat 5 kd) + BitVec.ofInt 64 o) 8
        (BitVec.ofNat (8 * 8) ((m1.rX (BitVec.ofNat 5 25)).toNat % 2 ^ (8 * 8))) y = _
    rw [hm1mem, hm1R, hm1D, ofInt_nat, ofNat_rd _ (by decide), wr_get (by omega)]
    rfl

/-- The chunks `cs` off `X ks` (holding `S`) and `X kd` (holding `D`), from index `j` to `j'`. -/
theorem move_run (hnd : (psA.toList.map (·.id)).Nodup)
    (hlt : ∀ p ∈ psA.toList, p.id < 2 ^ 32)
    (hret : ∀ p ∈ psA.toList, (Link.byId sym text az ez psA.toList).addr p.id ≠ some ret)
    {ks kd : Nat} (hks : ks < 32) (hkd : kd < 32) (hks25 : ks ≠ 25) (hkd25 : kd ≠ 25)
    {S D : BitVec 64} :
    ∀ (cs : List (Nat × Nat)) (j j' : Nat) (m : MState),
      ManyAt2 psA j (cs.flatMap (movePats (REG_R0 + ks) (REG_R0 + kd))) j' →
      m.rX (BitVec.ofNat 5 ks) = S → m.rX (BitVec.ofNat 5 kd) = D →
      (∀ c ∈ cs, 4096 ≤ S.toNat ∧ S.toNat + c.2 + moveW c.1 ≤ 2 ^ 64 ∧
        4096 ≤ D.toNat ∧ D.toNat + c.2 + moveW c.1 ≤ 2 ^ 64) →
      ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret
          { m with pc := pcAt text psA.toList j } m' ∧
        m'.pc = pcAt text psA.toList j' ∧ m'.mem = cpMem S D m.mem cs ∧ Keeps53 m m'
  | [], j, j', m, h, _, _, _ => by
    simp only [List.flatMap_nil, ManyAt2] at h
    subst h
    exact ⟨_, .refl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩
  | c :: rest, j, j', m, h, hS, hD, hb => by
    simp only [List.flatMap_cons, movePats, List.cons_append, List.nil_append] at h
    obtain ⟨k, h1, k', h2, h3⟩ := h
    have hc := hb c List.mem_cons_self
    obtain ⟨m1, hst1, hpc1, hmem1, hk1⟩ := chunk_run (H := H) hnd hlt hret hks hkd hkd25 h1 h2 hS hD
      ⟨hc.1, hc.2.1⟩ ⟨hc.2.2.1, hc.2.2.2⟩
    obtain ⟨m2, hst2, hpc2, hmem2, hk2⟩ := move_run hnd hlt hret hks hkd hks25 hkd25 rest k' j' m1
      h3 (by rw [hk1.rX (reg_ne25 hks hks25), hS]) (by rw [hk1.rX (reg_ne25 hkd hkd25), hD])
      (fun c' h' => hb c' (List.mem_cons_of_mem _ h'))
    have heta : ({ m1 with pc := pcAt text psA.toList k' } : MState) = m1 := by
      rw [← hpc1]
    rw [heta] at hst2
    refine ⟨m2, hst1.trans hst2, hpc2, ?_, hk1.trans hk2⟩
    rw [hmem2, hmem1]
    rfl

end Run

/-! ## The bytes `runLoc` copies -/

theorem find?_mem53 {m : Mem} {b : Blk} {al : Alloc} (h : m.find? b = some al) :
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

theorem read_some53 {m : Mem} {p : Ptr} {n : Nat} {bs : Array Byte} (hn : 0 < n)
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

/-! ## The value -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K : KMap}

/-- `LoweredMove [n] dst src mem`: the chunks copy the `n` bytes at `src`'s injected address to
`dst`'s, inside a live block and away from the frame; `R25`, `F16`, `F17` are `poison`. -/
private theorem g53a_move (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size = 8)
    (hm : LocMatch E s b i m) (hinv : G3Inv E lc K s osp) (hR : KRead lc v K.get)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {rd rs : Int} (hop : v.op = .ARM64LoweredMove) (hsz3 : v.args.size = 3)
    (hmt : memTy (lc.ty v.id) = true) (hhn : lc.home v.id = none)
    (hdo : argObj lc v 0 = .ok (64, rd)) (hso : argObj lc v 1 = .ok (64, rs))
    (hma : memArg lc v 2 = .ok ()) (h16 : 16 ≤ v.auxInt.toInt) (hrd : rd ≠ r25A)
    (hrs : rs ≠ r25A)
    (hcov : moveCovers v.auxInt.toInt.toNat (moveOffs v.auxInt.toInt.toNat) = true)
    (hvs : ManyAt2 psA j (if rd == rs then [] else
      (moveOffs v.auxInt.toInt.toNat).flatMap (movePats rs rd)) j')
    (hpre : Pre53a lc s v)
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ G3Inv E lc K s' osp := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hdo
  obtain ⟨kd, hkd, rfl, hkkd⟩ := objOf?_some hor0
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hso
  obtain ⟨ks, hks, rfl, hkks⟩ := objOf?_some hor1
  have hkd25 : kd ≠ 25 := fun h => hrd (by rw [h]; rfl)
  have hks25 : ks ≠ 25 := fun h => hrs (by rw [h]; rfl)
  obtain ⟨a2, ha2, hamt, hah2⟩ := memArg_spec hma
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨xv, hxr, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv.core hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkd
  obtain ⟨yv, hyr, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv.core hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkks
  obtain ⟨x, y, hx, hy, rfl⟩ :=
    stepLoc_lmove hl htemp hop (arr3 hsz3 ha0 ha1 ha2) (read_mem hl hah2 hamt hmm) hs
  rw [hxr] at hx
  cases hx
  rw [hyr] at hy
  cases hy
  obtain ⟨pd, ps, mm1, bs, mm', hpd, hps, hmm1, hrd', hwr, hdisj⟩ :=
    hpre hop a0 xv a1 yv ha0 hxr ha1 hyr
  rw [hmm] at hmm1
  cases hmm1
  have hmove : Arm64.move v.auxInt [xv, yv, .mem mm] = .mem mm' := by
    simp only [Arm64.move, hpd, hps, hrd', hwr]
  rw [hmove, write_mem hhn hmt, memTy_eq hmt, retypeL_mem]
  obtain ⟨hcsl, hcfl, -⟩ := clobberMask_keeps s Op.ARM64LoweredMove.regInfo.clobbers
  obtain ⟨mm0, hmm0, hk0, hsep0⟩ := hinv.core.mem
  rw [hmm] at hmm0
  cases hmm0
  generalize hn : v.auxInt.toInt.toNat = n at hcov hvs hrd' hdisj
  have hn16 : 16 ≤ n := by omega
  -- the source bytes
  obtain ⟨als, hfs, hoffs, rfl⟩ := read_some53 (by omega) hrd'
  have hbs : (als.data.extract ps.off.toNat (ps.off.toNat + n)).size = n := by
    simp only [Array.size_extract]; omega
  have hals := find?_mem53 hfs
  -- the destination
  obtain ⟨ald, hald, hoffd⟩ := write_inside hwr (by rw [hbs]; omega)
  rw [hbs] at hoffd
  have hcan : mm.canWrite pd n = true := by
    have := canWrite_of_write hwr (by rw [hbs]; omega)
    rwa [hbs] at this
  obtain ⟨ad, had, hDeq, -⟩ := addr_rel hA hMI hxv hxf hpd (by omega : 0 < n) (Or.inl hcan)
  obtain ⟨as, has, hSeq, -⟩ := addr_rel hA hMI hyv hyf hps (by omega : 0 < n)
    (Or.inr (by rw [hrd']; rfl))
  obtain ⟨ad', had', hlod, hhid⟩ := hMI.mapped _ _ hald
  obtain rfl : ad = ad' := Option.some.inj (had.symm.trans had')
  obtain ⟨as', has', hlos, hhis⟩ := hMI.mapped _ _ hals
  obtain rfl : as = as' := Option.some.inj (has.symm.trans has')
  have hlod' := hlod (by omega)
  have hlos' := hlos (by omega)
  have hDt : (ad + pd.off).toNat = ad.toNat + pd.off.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hSt : (as + ps.off).toNat = as.toNat + ps.off.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hXD : m.rX (BitVec.ofNat 5 kd) = ad + pd.off := by simpa using hDeq
  have hXS : m.rX (BitVec.ofNat 5 ks) = as + ps.off := by simpa using hSeq
  -- the source bytes are related to the machine's
  have hsrc : ∀ j, j < n → ByteRel E.ι (als.data.extract ps.off.toNat (ps.off.toNat + n))[j]!
      (m.mem (as + ps.off + BitVec.ofNat 64 j)) := by
    intro j hj
    rw [getElem!_pos _ _ (by rw [hbs]; exact hj), Array.getElem_extract, ← addr_off]
    exact memInj_byteRel hA hMI hals has (by omega)
  -- the machine: the copy, or nothing when both are in the same register
  obtain ⟨m', hrun, hpc', hcp, hout, hkeep⟩ : ∃ m', PStar H (Link.byId sym text az ez psA.toList)
      psA.toList ret m m' ∧ m'.pc = pcAt text psA.toList j' ∧
      (∀ j, j < n → m'.mem (ad + pd.off + BitVec.ofNat 64 j) = m.mem (as + ps.off + BitVec.ofNat 64 j)) ∧
      (∀ y : BitVec 64, (∀ j, j < n → y.toNat ≠ ad.toNat + pd.off.toNat + j) → m'.mem y = m.mem y) ∧
      Keeps53 m m' := by
    by_cases hrr : (REG_R0 + (kd : Int)) = REG_R0 + (ks : Int)
    · have hkk : kd = ks := by omega
      subst hkk
      simp only [hrr, beq_self_eq_true, ↓reduceIte, ManyAt2] at hvs
      subst hvs
      refine ⟨m, .refl, by rw [hm.pc, hj], fun j _ => ?_, fun _ _ => rfl,
        rfl, rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩
      rw [← hXD, ← hXS]
    · simp only [beq_iff_eq, hrr, ↓reduceIte] at hvs
      obtain ⟨hin, hcovj⟩ := moveCovers_spec hcov
      have hsd : as + ps.off = ad + pd.off ∨
          ∀ k, k < n → n ≤ (as + ps.off + BitVec.ofNat 64 k - (ad + pd.off)).toNat := by
        have hsep : (as + ps.off).toNat + n ≤ (ad + pd.off).toNat ∨
            (ad + pd.off).toNat + n ≤ (as + ps.off).toNat → ∀ k, k < n →
              n ≤ (as + ps.off + BitVec.ofNat 64 k - (ad + pd.off)).toNat := by
          intro h k hk
          rw [hDt, hSt] at h
          have h64 : (as + ps.off + BitVec.ofNat 64 k).toNat = as.toNat + ps.off.toNat + k := by
            rw [BitVec.toNat_add, hSt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
              Nat.mod_eq_of_lt (by omega)]
          rw [BitVec.toNat_sub, h64, hDt]
          omega
        rcases hdisj with rfl | hne | hlt | hlt
        · left
          obtain rfl : as = ad := Option.some.inj (has.symm.trans had)
          rfl
        · right
          apply hsep
          rcases hMI.inj _ _ _ _ _ _ hald hals hne had has with h | h <;> omega
        · right
          apply hsep
          by_cases hb : pd.blk = ps.blk
          · rw [hb, has] at had; cases had; omega
          · rcases hMI.inj _ _ _ _ _ _ hald hals hb had has with h | h <;> omega
        · right
          apply hsep
          by_cases hb : pd.blk = ps.blk
          · rw [hb, has] at had; cases had; omega
          · rcases hMI.inj _ _ _ _ _ _ hald hals hb had has with h | h <;> omega
      obtain ⟨m', hst, hpc', hmem', hkeep⟩ := move_run (H := H) F.nodup F.lt F.ret hks hkd hks25
        hkd25 (moveOffs n) j j' m hvs hXS hXD (fun c hc => by
          have := hin c hc
          exact ⟨by rw [hSt]; omega, by rw [hSt]; omega, by rw [hDt]; omega, by rw [hDt]; omega⟩)
      rw [pc_eta hm hj] at hst
      have hget := cpMem_get hsd (moveOffs n) m.mem hin
      refine ⟨m', hst, hpc', fun j hj => ?_, fun y hy => ?_, hkeep⟩
      · rw [hmem', hget]
        have hsub : ad + pd.off + BitVec.ofNat 64 j - (ad + pd.off) = BitVec.ofNat 64 j := by
          bv_omega
        have hjt : (ad + pd.off + BitVec.ofNat 64 j - (ad + pd.off)).toNat = j := by
          rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        rw [if_pos ?_, hsub]
        obtain ⟨c, hc, hcj⟩ := hcovj j hj
        exact ⟨c, hc, by rw [hjt]; exact hcj⟩
      · rw [hmem', hget, if_neg]
        rintro ⟨c, hc, hc1, hc2⟩
        have := hin c hc
        apply hy ((y - (ad + pd.off)).toNat) (by omega)
        rw [BitVec.toNat_sub] at hc1 hc2 ⊢
        have hy64 := y.isLt
        rw [hDt] at hc1 hc2 ⊢
        omega
  -- `MemInj`, the separation and the frame
  obtain ⟨hMI', hk', hback, -⟩ := memInj_writeAny hA hMI hk0 (by omega : 0 < n) had hbs
    (M := m'.mem) (fun j hj => by rw [hcp j hj]; exact hsrc j hj) hout hwr
  have hsep' : SepAt osp E.ι (StkAt E) mm' := hsep0.write hk0 hwr
  have hwf := write_wf hwr (by rw [hbs]; omega)
  have hP : ∀ y, StkAt E y → m'.mem y = m.mem y := fun y hy =>
    hout y fun j hj he => hsep0.not_mem hald had hy (by omega) (by omega)
  obtain ⟨hslots, hframe⟩ := stk_slots_frame (E' := E) (m' := m') hm hF hsz rfl
    (fun _ _ h => h) hP hkeep.1 (hkeep.2.2.1 _ (by decide)) (hkeep.2.2.1 _ (by decide))
    (fun _ => hkeep.2.2.1 _ (by decide))
  refine ⟨m', hrun, ⟨fun r x h => ?_, ?_, ?_, ⟨mm', rfl, hMI'⟩, hframe, by rw [hpc', hj']⟩,
    ⟨⟨fun r x c hrz h hc => ?_, mm', rfl, hk', hsep'⟩, fun k v hk => hinv.slots k v ?_⟩⟩
  · rcases clobberMask_move h with rfl | ⟨h2, h24, h47, h48⟩
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
    · obtain ⟨hx1, hv1⟩ := hm.regs r x h2
      refine ⟨fun q hq => ?_, fun q hq => ?_⟩
      · rw [hkeep.2.2.1 q (objX?_ne25 hq h24)]
        exact hx1 q hq
      · obtain ⟨hq16, hq17⟩ := objV?_ne1617 hq h47 h48
        rw [hkeep.2.2.2 q hq16 hq17]
        exact hv1 q hq
  · show FlagsRel (s.clobberMask _).flags m'.nzcv
    rw [hcfl, hkeep.2.1]
    exact hm.flags
  · show ∀ k v, (s.clobberMask _).slots.lookup k = some v → _
    rw [hcsl]
    exact hslots
  · rcases clobberMask_move h with rfl | ⟨h2, -, -, -⟩
    · trivial
    · exact hinv.core.regs r x c hrz h2 hc
  · rw [← hcsl]; exact hk

end Cases

/-! ## One value -/

/-- One value of G53's group A, under `Pre53a`: the machine runs its Progs, the states match after
it, the invariant holds with the class table `kStep`, and the upper-bit table after it is empty. -/
theorem vk53a_step {env : Env} {H : Hooks} {lc : LocCtx} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)}
    (F : Facts lc sym text az ez ps.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size = 8)
    (hVK : VK53a lc v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s osp) (hpre : Pre53a lc s v)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E s' bid (i + 1) m' ∧ G3Inv E lc (kStep lc K v) s' osp ∧ UOKL m'
      (uStep35 lc L v) := by
  cases hVK with
  | move hop hsz3 hmt hhn hdo hso hma h16 hrd hrs hcov =>
    have hK : kStep lc K v = K := by
      simp only [kStep, hop, hhn]
      rfl
    obtain ⟨m', h1, h2, h3⟩ := g53a_move (H := H) F hF hsz hm hinv (kread_of_reads hreads) hj hj'
      hop hsz3 hmt hhn hdo hso hma h16 hrd hrs hcov hvs hpre htemp hs
    refine ⟨m', h1, h2, by rw [hK]; exact h3, ?_⟩
    rw [uStep35_53a hop]
    exact fun e he => by cases he

end GoFV.Proof.Gen

import GoFV.Proof.Gen.G54a

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G54, `LoweredMoveLoop` (`docs/plans/proofs3.md` §4)

`vkind54a` (`GoFV/Gen/Check54a.lean`) accepts `LoweredMoveLoop [n] dst src mem`; `VK54a.move`
(`Spec54a.lean`) says what it accepted. `runLoc` runs it as its clobbers (`R24`, `R25`, `F16`,
`F17` and the registers of `dst` and `src` hold `poison`) then `Arm64.move`: the `n` bytes read at
`src` written at `dst`, or `poison` if either access is invalid (`stepLoc_mloop`).

Genssa emits nothing when `dst` and `src` share their register, else `MOVD $n/64, R24`, a body of
two `FLDPQ.P 32(Rsrc), (F16, F17)`; `FSTPQ.P (F16, F17), 32(Rdst)` pairs, `SUB $1, R24` and
`CBNZ R24` back to the body, then `moveTail`'s chunks of the `n mod 64` bytes left off the advanced
pointers. A pair copies 32 bytes (`cpP_one`: `cpW` at the pointers' offset from the start,
`cpW_shift`); the loop (`mloop_run`) by induction over the `n / 64` iterations (invariant: after
`i` iterations both pointers are advanced by `64 i`, `R24` holds `n / 64 - i`, the memory is
`cpMem` of the chunks so far, `mloopChunks`), then G53's `move_run` of the tail at the advanced
pointers. As for `LoweredMove` (`G53a.lean`), the machine copies chunk by chunk while `Arm64.move`
reads all bytes first; they agree when the two ranges are the same bytes or disjoint (`cpMem_get`),
which the run premise `Pre54b` states. On the machine only the two pointers, `X24`, `X25`, `V16`,
`V17` change, the registers `runLoc` sets to `poison`. `vk54b_move` is one value.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The premise -/

/-- `LoweredMoveLoop [n] dst src mem` reads `n` valid bytes at `src` and writes them at `dst`, and
the two byte ranges are equal or disjoint (Go's `Move` never copies between partially overlapping
ones). -/
def Pre54b (lc : LocCtx) (s : LocState) (v : Value) : Prop :=
  v.op = .ARM64LoweredMoveLoop → ∀ d x a y, v.args[0]? = some d → s.read lc d = .ok x →
    v.args[1]? = some a → s.read lc a = .ok y →
    ∃ pd ps mm bs mm', Arm64.addr x 0 = some pd ∧ Arm64.addr y 0 = some ps ∧ s.mem = .mem mm ∧
      mm.read ps v.auxInt.toInt.toNat = some bs ∧ mm.write pd bs = some mm' ∧
      (pd = ps ∨ pd.blk ≠ ps.blk ∨ pd.off.toNat + v.auxInt.toInt.toNat ≤ ps.off.toNat ∨
        ps.off.toNat + v.auxInt.toInt.toNat ≤ pd.off.toNat)

/-! ## `stepLoc` -/

section Step

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

/-- `LoweredMoveLoop [n] dst src mem`: its clobbers, then `Arm64.move` of its arguments as the
memory. -/
theorem stepLoc_mloop (hl : lc.ctx.f.lowered = true) (hop : v.op = .ARM64LoweredMoveLoop)
    {d a mem : ID} (ha : v.args = #[d, a, mem]) {mm : Mem}
    (hmem : s.read lc mem = .ok (.mem mm)) (h : stepLoc env lc s v = .ok s') :
    ∃ x y, s.read lc d = .ok x ∧ s.read lc a = .ok y ∧
      s' = (s.clobber lc v).write lc v.id ((Arm64.move v.auxInt [x, y, .mem mm]).retypeL (lc.ty v.id)) := by
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
    rw [lmode_retype hl]
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

/-! ## The machine's copies -/

/-- The chunks of the first `i` iterations: 32 bytes at each multiple of 32 below `64 i`. -/
def mloopChunks (i : Nat) : List (Nat × Nat) := (List.range' 0 (2 * i) 32).map fun o => (32, o)

theorem mloopChunks_succ (i : Nat) :
    mloopChunks (i + 1) = mloopChunks i ++ [(32, 64 * i), (32, 64 * i + 32)] := by
  unfold mloopChunks
  rw [show 2 * (i + 1) = 2 * i + 2 by omega, ← List.range'_append, List.map_append]
  congr 1
  simp only [List.range', List.map_cons, List.map_nil]
  rw [show 0 + 32 * (2 * i) = 64 * i by omega]

theorem mem_mloopChunks {i : Nat} {c : Nat × Nat} (h : c ∈ mloopChunks i) :
    c.1 = 32 ∧ c.2 + 32 ≤ 64 * i := by
  simp only [mloopChunks, List.mem_map, List.mem_range'] at h
  obtain ⟨o, ⟨k, hk, rfl⟩, rfl⟩ := h
  exact ⟨rfl, by omega⟩

theorem mloopChunks_cover {i j : Nat} (hj : j < 64 * i) :
    ∃ c ∈ mloopChunks i, c.2 ≤ j ∧ j < c.2 + moveW c.1 := by
  refine ⟨(32, 32 * (j / 32)), ?_, ?_⟩
  · simp only [mloopChunks, List.mem_map, List.mem_range', Prod.mk.injEq, true_and]
    exact ⟨32 * (j / 32), ⟨j / 32, by omega, by omega⟩, rfl⟩
  · simp only [moveW, ↓reduceIte]
    omega

theorem cpMem_append (S D : BitVec 64) (M : Memory) (a b : List (Nat × Nat)) :
    cpMem S D M (a ++ b) = cpMem S D (cpMem S D M a) b := List.foldl_append

/-- A copy window off pointers advanced by `c` is the window `c` further off the start. -/
theorem cpW_shift (S D : BitVec 64) (M : Memory) {c o w : Nat} (h : c + o + w ≤ 2 ^ 64) :
    cpW (S + BitVec.ofNat 64 c) (D + BitVec.ofNat 64 c) M o w = cpW S D M (c + o) w := by
  funext y
  unfold cpW
  have hs : S + BitVec.ofNat 64 c + (y - (D + BitVec.ofNat 64 c)) = S + (y - D) := by grind
  rw [hs]
  have he : (o ≤ (y - (D + BitVec.ofNat 64 c)).toNat ∧ (y - (D + BitVec.ofNat 64 c)).toNat < o + w) ↔
      (c + o ≤ (y - D).toNat ∧ (y - D).toNat < c + o + w) := by
    have hc : c < 2 ^ 64 ∨ (o = 0 ∧ w = 0 ∧ c = 2 ^ 64) := by omega
    rcases hc with hc | ⟨rfl, rfl, rfl⟩
    · have hsub : (y - (D + BitVec.ofNat 64 c)).toNat =
          ((y - D).toNat + (2 ^ 64 - c)) % 2 ^ 64 := by
        rw [show y - (D + BitVec.ofNat 64 c) = (y - D) - BitVec.ofNat 64 c by grind,
          BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]
        omega
      rw [hsub]
      have hd := (y - D).isLt
      by_cases hdc : c ≤ (y - D).toNat
      · rw [show (y - D).toNat + (2 ^ 64 - c) = ((y - D).toNat - c) + 2 ^ 64 by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        omega
      · rw [Nat.mod_eq_of_lt (by omega)]
        omega
    · omega
  by_cases hc1 : c + o ≤ (y - D).toNat ∧ (y - D).toNat < c + o + w
  · rw [if_pos (he.2 hc1), if_pos hc1]
  · rw [if_neg (fun h => hc1 (he.1 h)), if_neg hc1]

theorem cpMem_shift (S D : BitVec 64) {c : Nat} (cs : List (Nat × Nat))
    (h : ∀ x ∈ cs, c + x.2 + moveW x.1 ≤ 2 ^ 64) :
    ∀ M : Memory, cpMem (S + BitVec.ofNat 64 c) (D + BitVec.ofNat 64 c) M cs =
      cpMem S D M (cs.map fun x => (x.1, c + x.2)) := by
  induction cs with
  | nil => intro M; simp only [cpMem, List.foldl_nil, List.map_nil]
  | cons x rest ih =>
    intro M
    simp only [cpMem, List.foldl_cons, List.map_cons] at ih ⊢
    rw [cpW_shift S D M (h x List.mem_cons_self)]
    exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) _

section Run

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64}

/-- `FLDPQ.P 32(Rsrc), (F16, F17)`; `FSTPQ.P (F16, F17), 32(Rdst)` with `X ks = S + c`,
`X kd = D + c`: the 32 bytes at `S + c` copied to `D + c` (`cpW`), both pointers advanced by 32. -/
theorem cpP_one (hnd : (psA.toList.map (·.id)).Nodup) (hlt : ∀ p ∈ psA.toList, p.id < 2 ^ 32)
    (hret : ∀ p ∈ psA.toList, (Link.byId sym text az ez psA.toList).addr p.id ≠ some ret)
    {ks kd : Nat} (hks : ks < 31) (hkd : kd < 31) (hne : ks ≠ kd) {S D : BitVec 64} {c : Nat}
    {j k j' : Nat} (h1 : OneAt2 psA j (fldpqPPat (REG_R0 + ks)) k)
    (h2 : OneAt2 psA k (fstpqPPat (REG_R0 + kd)) j') (m : MState)
    (hS : m.x (BitVec.ofNat 5 ks) = S + BitVec.ofNat 64 c)
    (hD : m.x (BitVec.ofNat 5 kd) = D + BitVec.ofNat 64 c)
    (hSb : 4096 ≤ S.toNat ∧ S.toNat + c + 32 ≤ 2 ^ 64)
    (hDb : 4096 ≤ D.toNat ∧ D.toNat + c + 32 ≤ 2 ^ 64) :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret
        { m with pc := pcAt text psA.toList j } m' ∧
      m'.pc = pcAt text psA.toList j' ∧
      m'.x (BitVec.ofNat 5 ks) = S + BitVec.ofNat 64 (c + 32) ∧
      m'.x (BitVec.ofNat 5 kd) = D + BitVec.ofNat 64 (c + 32) ∧
      Keeps54 [BitVec.ofNat 5 ks, BitVec.ofNat 5 kd] [BitVec.ofNat 5 16, BitVec.ofNat 5 17] m m' ∧
      m'.mem = cpW S D m.mem c 32 := by
  have hksd : (BitVec.ofNat 5 kd : Reg) ≠ BitVec.ofNat 5 ks := by
    intro h; have := congrArg BitVec.toNat h; simp at this; omega
  have hS' : m.rX (BitVec.ofNat 5 ks) = S + BitVec.ofNat 64 c := by rw [rX_of_lt hks, hS]
  -- the load
  let m1 : MState := ((m.wX (BitVec.ofNat 5 ks) (S + BitVec.ofNat 64 c + BitVec.ofNat 64 32)).wV
    (BitVec.ofNat 5 16) ((readMem m.mem (S + BitVec.ofNat 64 c) 16).setWidth 128)).wV
    (BitVec.ofNat 5 17) ((readMem m.mem (S + BitVec.ofNat 64 c + BitVec.ofNat 64 16) 16).setWidth 128)
  have hs1 := pstar_one54 (H := H) hnd hlt hret h1 m m1 (fun k hk hok => by
    have hr : ({ m with pc := pcAt text psA.toList k } : MState).rX (BitVec.ofNat 5 ks) =
        S + BitVec.ofNat 64 c := hS'
    rw [progStep_fldpqP hks (nextAddr_pcAt hnd hk) hok
      (by rw [hr]; exact nil_of hSb.1 (by omega))
      (by rw [hr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; exact nil_of hSb.1 (by omega)), hr]
    simp only [wX_pc]
    rfl)
  have hm1D : m1.rX (BitVec.ofNat 5 kd) = D + BitVec.ofNat 64 c := by
    rw [rX_of_lt hkd]
    show (m.wX _ _).x _ = _
    rw [wX_x_of_ne hksd, hD]
  have hm1mem : m1.mem = m.mem := (wX_fields).1
  -- the store
  let m2 : MState := { m1.wX (BitVec.ofNat 5 kd) (D + BitVec.ofNat 64 c + BitVec.ofNat 64 32) with
    mem := writeMem (writeMem m1.mem (D + BitVec.ofNat 64 c) 16
        (BitVec.ofNat (8 * 16) ((m1.v (BitVec.ofNat 5 16)).toNat % 2 ^ (8 * 16))))
      (D + BitVec.ofNat 64 c + BitVec.ofNat 64 16) 16
        (BitVec.ofNat (8 * 16) ((m1.v (BitVec.ofNat 5 17)).toNat % 2 ^ (8 * 16))) }
  have hs2 := pstar_one54 (H := H) hnd hlt hret h2 m1 m2 (fun k hk hok => by
    have hr : ({ m1 with pc := pcAt text psA.toList k } : MState).rX (BitVec.ofNat 5 kd) =
        D + BitVec.ofNat 64 c := hm1D
    rw [progStep_fstpqP hkd (nextAddr_pcAt hnd hk) hok
      (by rw [hr]; exact nil_of hDb.1 (by omega))
      (by rw [hr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; exact nil_of hDb.1 (by omega)), hr]
    simp only [wX_pc]
    rfl)
  have hv16 : m1.v (BitVec.ofNat 5 16) = (readMem m.mem (S + BitVec.ofNat 64 c) 16).setWidth 128 := by
    simp [m1, MState.wV]
  have hv17 : m1.v (BitVec.ofNat 5 17) =
      (readMem m.mem (S + BitVec.ofNat 64 (c + 16)) 16).setWidth 128 := by
    simp [m1, MState.wV, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  refine ⟨_, hs1.trans hs2, rfl, ?_, ?_, ?_, ?_⟩
  · show (m1.wX _ _).x _ = _
    rw [wX_x_of_ne hksd.symm]
    show (m.wX _ _).x _ = _
    rw [wX_x_self54 hks, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  · show (m1.wX _ _).x _ = _
    rw [wX_x_self54 hkd, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  · have hk1 : Keeps54 [BitVec.ofNat 5 ks, BitVec.ofNat 5 kd] [BitVec.ofNat 5 16, BitVec.ofNat 5 17]
        m m1 :=
      (keeps54_wX (by simp)).trans ((keeps54_wV (by simp)).trans (keeps54_wV (by simp)))
    have hk2 : Keeps54 [BitVec.ofNat 5 ks, BitVec.ofNat 5 kd]
        [BitVec.ofNat 5 16, BitVec.ofNat 5 17] m1 m2 :=
      keeps54_mem (keeps54_wX (by simp)) _
    exact keeps54_pc (hk1.trans hk2) _
  · funext y
    show writeMem (writeMem m1.mem _ 16 _) _ 16 _ y = _
    rw [hv16, hv17, hm1mem, ofNat_rd _ (by decide), ofNat_rd _ (by decide),
      BitVec.add_assoc D, BitVec.ofNat_add_ofNat, wr_get (by omega), wr_get (by omega)]
    unfold cpW
    by_cases ha : c + 16 ≤ (y - D).toNat ∧ (y - D).toNat < c + 16 + 16
    · rw [if_pos ha, if_pos (by omega)]
    · rw [if_neg ha]
      by_cases hb : c ≤ (y - D).toNat ∧ (y - D).toNat < c + 16
      · rw [if_pos hb, if_pos (by omega)]
      · rw [if_neg hb, if_neg (by omega)]

/-- The move loop, from its `MOVD` at index `j`: the machine reaches the Prog after the `CBNZ`
(`ke`, where the tail starts) with both pointers advanced by `64 N` (`N = n / 64`), `X24` and the
temporaries changed, the memory `cpMem` of the loop's chunks (`mloopChunks N`). -/
theorem mloop_run (hnd : (psA.toList.map (·.id)).Nodup) (hlt : ∀ p ∈ psA.toList, p.id < 2 ^ 32)
    (hret : ∀ p ∈ psA.toList, (Link.byId sym text az ez psA.toList).addr p.id ≠ some ret)
    {ks kd : Nat} (hks : ks < 31) (hkd : kd < 31) (hne : ks ≠ kd) (hs24 : ks ≠ 24)
    (hd24 : kd ≠ 24) {n : Int} {tail : List Pat} {j j' : Nat}
    (hvs : ManyAt2 psA j (loopPats r24A n (moveBody (REG_R0 + ks) (REG_R0 + kd)) ++ tail) j')
    (hloop : loopTgt psA j = true) (h64 : 64 ≤ n) {S D : BitVec 64} (m : MState)
    (hS : m.x (BitVec.ofNat 5 ks) = S) (hD : m.x (BitVec.ofNat 5 kd) = D)
    (hSb : 4096 ≤ S.toNat ∧ S.toNat + n.toNat ≤ 2 ^ 64)
    (hDb : 4096 ≤ D.toNat ∧ D.toNat + n.toNat ≤ 2 ^ 64) :
    ∃ ke m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret
        { m with pc := pcAt text psA.toList j } m' ∧
      m'.pc = pcAt text psA.toList ke ∧ ManyAt2 psA ke tail j' ∧
      m'.x (BitVec.ofNat 5 ks) = S + BitVec.ofNat 64 (64 * (n.toNat / 64)) ∧
      m'.x (BitVec.ofNat 5 kd) = D + BitVec.ofNat 64 (64 * (n.toNat / 64)) ∧
      Keeps54 [BitVec.ofNat 5 ks, BitVec.ofNat 5 kd, BitVec.ofNat 5 24]
        [BitVec.ofNat 5 16, BitVec.ofNat 5 17] m m' ∧
      m'.mem = cpMem S D m.mem (mloopChunks (n.toNat / 64)) := by
  obtain ⟨k1, kb, ks', ke, hmv, hbody, hsub, hcb, htl, hk1, hke, hbr⟩ :=
    loopTgt_spec hvs (fldpqPPat_code _) (fstpqPPat_code _) (fldpqPPat_code _) (fstpqPPat_code _)
      hloop
  generalize hN : n.toNat / 64 = N
  have hN1 : 1 ≤ N := by omega
  have hNlt : N < 2 ^ 64 := by omega
  have hn64 : n / 64 = (N : Int) := by omega
  have hne' : ∀ a b : Nat, a < 31 → b < 31 → a ≠ b → (BitVec.ofNat 5 a : Reg) ≠ BitVec.ofNat 5 b :=
    fun a b ha hb hab h => by have := congrArg BitVec.toNat h; simp at this; omega
  -- the counter's `MOVD $N, R24`
  let m0 : MState := m.wX (BitVec.ofNat 5 24) (BitVec.ofNat 64 N)
  have hs0 := pstar_one54 (H := H) hnd hlt hret hmv m m0 (fun k hk hok => by
    obtain ⟨has, hf, -, ht, -⟩ := Shape.ok_eq hok
    rw [progStep_movConst (kd := 24) (by omega) (nextAddr_pcAt hnd hk) has hf ht, hn64, ofInt_nat]
    simp only [wX_pc]
    rfl)
  let I : Nat → MState → Prop := fun i m' =>
    Keeps54 [BitVec.ofNat 5 ks, BitVec.ofNat 5 kd, BitVec.ofNat 5 24]
        [BitVec.ofNat 5 16, BitVec.ofNat 5 17] m m' ∧
      m'.x (BitVec.ofNat 5 ks) = S + BitVec.ofNat 64 (64 * i) ∧
      m'.x (BitVec.ofNat 5 kd) = D + BitVec.ofNat 64 (64 * i) ∧
      m'.x (BitVec.ofNat 5 24) = BitVec.ofNat 64 (N - i) ∧
      m'.mem = cpMem S D m.mem (mloopChunks i)
  have hI0 : I 0 { m0 with pc := pcAt text psA.toList k1 } := by
    refine ⟨keeps54_pc (keeps54_wX (by simp)) _, ?_, ?_, ?_, ?_⟩
    · show (m.wX (BitVec.ofNat 5 24) (BitVec.ofNat 64 N)).x (BitVec.ofNat 5 ks) = _
      rw [wX_x_of_ne (hne' _ _ hks (by omega) hs24), hS]; simp
    · show (m.wX (BitVec.ofNat 5 24) (BitVec.ofNat 64 N)).x (BitVec.ofNat 5 kd) = _
      rw [wX_x_of_ne (hne' _ _ hkd (by omega) hd24), hD]; simp
    · show (m.wX (BitVec.ofNat 5 24) (BitVec.ofNat 64 N)).x (BitVec.ofNat 5 24) = _
      rw [wX_x_self54 (by omega : 24 < 31)]; simp
    · show (m.wX (BitVec.ofNat 5 24) (BitVec.ofNat 64 N)).mem = _
      rw [(wX_fields).1]; rfl
  have hstep : ∀ i m1, i < N → I i m1 → m1.pc = pcAt text psA.toList k1 →
      ∃ m2, PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m1 m2 ∧ I (i + 1) m2 ∧
        m2.pc = if i + 1 = N then pcAt text psA.toList ke else pcAt text psA.toList k1 := by
    intro i m1 hi ⟨hk1', hs1, hd1, hc1, hmem1⟩ hpc1
    have heta : ({ m1 with pc := pcAt text psA.toList k1 } : MState) = m1 := by rw [← hpc1]
    obtain ⟨ka, ha1, kb1, ha2, kc1, ha3, kb', ha4, rfl⟩ := hbody
    -- the first pair
    obtain ⟨m2, hst2, hpc2, hs2, hd2, hk2, hmem2⟩ := cpP_one (H := H) hnd hlt hret hks hkd hne
      ha1 ha2 m1 hs1 hd1 ⟨hSb.1, by omega⟩ ⟨hDb.1, by omega⟩
    rw [heta] at hst2
    have heta2 : ({ m2 with pc := pcAt text psA.toList kb1 } : MState) = m2 := by rw [← hpc2]
    -- the second pair
    obtain ⟨m3, hst3, hpc3, hs3, hd3, hk3, hmem3⟩ := cpP_one (H := H) hnd hlt hret hks hkd hne
      ha3 ha4 m2 hs2 hd2 ⟨hSb.1, by omega⟩ ⟨hDb.1, by omega⟩
    rw [heta2] at hst3
    have heta3 : ({ m3 with pc := pcAt text psA.toList kb } : MState) = m3 := by rw [← hpc3]
    -- the counter
    obtain ⟨m4, hst4, hx4, hk4, hmem4, hpc4⟩ := count_run (H := H) hnd hlt hret
      (kc := 24) (by omega) hsub hcb hk1 hke hbr m3
    rw [heta3] at hst4
    have hc3 : m3.x (BitVec.ofNat 5 24) = BitVec.ofNat 64 (N - i) := by
      rw [hk3.2.2.1 _ (by simp [hne' _ _ (by omega) hks (Ne.symm hs24),
        hne' _ _ (by omega) hkd (Ne.symm hd24)]), hk2.2.2.1 _ (by simp [hne' _ _ (by omega) hks
        (Ne.symm hs24), hne' _ _ (by omega) hkd (Ne.symm hd24)]), hc1]
    have hcnt : BitVec.ofNat 64 (N - i) - 1 = BitVec.ofNat 64 (N - (i + 1)) := by
      rw [show N - i = N - (i + 1) + 1 by omega, ← BitVec.ofNat_add_ofNat]
      exact BitVec.add_sub_cancel _ _
    have hn24s : BitVec.ofNat 5 ks ∉ [(BitVec.ofNat 5 24 : Reg)] := by
      simp [hne' _ _ hks (by omega) hs24]
    have hn24d : BitVec.ofNat 5 kd ∉ [(BitVec.ofNat 5 24 : Reg)] := by
      simp [hne' _ _ hkd (by omega) hd24]
    refine ⟨m4, (hst2.trans hst3).trans hst4, ⟨hk1'.trans ((hk2.mono (by simp) (by simp)).trans
      ((hk3.mono (by simp) (by simp)).trans (hk4.mono (by simp) (by simp)))), ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [hk4.2.2.1 _ hn24s, hs3, show 64 * i + 32 + 32 = 64 * (i + 1) by omega]
    · rw [hk4.2.2.1 _ hn24d, hd3, show 64 * i + 32 + 32 = 64 * (i + 1) by omega]
    · rw [hx4, hc3, hcnt]
    · rw [hmem4, hmem3, hmem2, hmem1, mloopChunks_succ, cpMem_append]
      rfl
    · rw [hpc4, hc3, hcnt]
      by_cases he : i + 1 = N
      · rw [if_pos he, if_pos (by rw [show N - (i + 1) = 0 by omega]; rfl)]
      · rw [if_neg he, if_neg]
        intro h0
        have := congrArg BitVec.toNat h0
        rw [BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl] at this
        omega
  obtain ⟨mN, hsN, ⟨hkN, hsN', hdN, -, hmemN⟩, hpcN⟩ :=
    loop_run hstep N 0 _ (by omega) (by omega) hI0 rfl
  exact ⟨ke, mN, hs0.trans hsN, hpcN, htl, hsN', hdN, hkN, hmemN⟩

end Run

/-! ## The value -/

private theorem mloop_arg0 : Op.ARM64LoweredMoveLoop.regInfo.clobbersArg0 = true := by decide

private theorem mloop_arg1 : Op.ARM64LoweredMoveLoop.regInfo.clobbersArg1 = true := by decide

private theorem mloop_flags : Op.ARM64LoweredMoveLoop.clobberFlags = false := by decide

private theorem mloop_m23 : Op.ARM64LoweredMoveLoop.regInfo.clobbers.hasReg 23 = true := by decide

private theorem mloop_m24 : Op.ARM64LoweredMoveLoop.regInfo.clobbers.hasReg 24 = true := by decide

private theorem mloop_m47 : Op.ARM64LoweredMoveLoop.regInfo.clobbers.hasReg 47 = true := by decide

private theorem mloop_m48 : Op.ARM64LoweredMoveLoop.regInfo.clobbers.hasReg 48 = true := by decide

/-- The upper-bit table is empty after `LoweredMoveLoop`. -/
theorem uStep35_54b {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value}
    (hop : v.op = .ARM64LoweredMoveLoop) : uStep35 lc L v = [] := by
  simp [uStep35, ldEntry35, loadOp?, narrowLoad?, pairOp35, uStep34, keep34, keep31, keepOp31,
    keepOp34, uStepL, uEntry, narrowLd?, loadIdxOp?, hop]

theorem keeps54_of_53 {m m' : MState} (h : Keeps53 m m') :
    Keeps54 [BitVec.ofNat 5 25] [BitVec.ofNat 5 16, BitVec.ofNat 5 17] m m' :=
  ⟨h.1, h.2.1, fun q hq => h.2.2.1 q (by simpa using hq), fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    exact h.2.2.2 q hq.1 hq.2⟩

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K : KMap}

/-- `LoweredMoveLoop [n] dst src mem`: the loop and the tail copy the `n` bytes at `src`'s
injected address to `dst`'s, inside a live block and away from the frame; the registers the
machine changes are `poison` in `runLoc`. -/
theorem g54b_move (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size = 8)
    (hm : LocMatch E s b i m) (hinv : G3Inv E lc K s) (hR : KRead lc v K.get)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {rd rs : Int} (hop : v.op = .ARM64LoweredMoveLoop) (hsz3 : v.args.size = 3)
    (hmt : memTy (lc.ty v.id) = true) (hhn : lc.home v.id = none)
    (hdo : argObj lc v 0 = .ok (64, rd)) (hso : argObj lc v 1 = .ok (64, rs))
    (hma : memArg lc v 2 = .ok ()) (h64 : 64 ≤ v.auxInt.toInt) (hd0 : argDest lc v 0 = true)
    (hd1 : argDest lc v 1 = true) (h24d : rd ≠ r24A) (h24s : rs ≠ r24A) (h25d : rd ≠ r25A)
    (h25s : rs ≠ r25A)
    (hcov : moveCovers (v.auxInt.toInt.toNat % 64) (moveOffs (v.auxInt.toInt.toNat % 64)) = true)
    (hvs : ManyAt2 psA j (if rd == rs then [] else
      loopPats r24A v.auxInt.toInt (moveBody rs rd) ++
        (moveOffs (v.auxInt.toInt.toNat % 64)).flatMap (movePats rs rd)) j')
    (hloop : loopOp lc v = true → loopTgt psA j = true)
    (hpre : Pre54b lc s v) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ G3Inv E lc K s' := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hdo
  obtain ⟨a0', r0', ha0', hah0', hr0⟩ := argDest_spec hd0
  rw [ha0] at ha0'; cases ha0'; rw [hah0] at hah0'; cases hah0'
  obtain ⟨kd, hkd, rfl, hkkd⟩ := objOf?_some hor0
  have hkd' : kd < 31 ∧ objX? r0 = some (BitVec.ofNat 5 kd) := by
    rcases hkkd with ⟨h, -⟩ | h
    · exact absurd h (by unfold zeroReg; omega)
    · exact h
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hso
  obtain ⟨a1', r1', ha1', hah1', hr1⟩ := argDest_spec hd1
  rw [ha1] at ha1'; cases ha1'; rw [hah1] at hah1'; cases hah1'
  obtain ⟨ks, hks, rfl, hkks⟩ := objOf?_some hor1
  have hks' : ks < 31 ∧ objX? r1 = some (BitVec.ofNat 5 ks) := by
    rcases hkks with ⟨h, -⟩ | h
    · exact absurd h (by unfold zeroReg; omega)
    · exact h
  have hkd25 : kd ≠ 25 := fun h => h25d (by rw [h]; rfl)
  have hks25 : ks ≠ 25 := fun h => h25s (by rw [h]; rfl)
  have hkd24 : kd ≠ 24 := fun h => h24d (by rw [h]; rfl)
  have hks24 : ks ≠ 24 := fun h => h24s (by rw [h]; rfl)
  have hd27 := objX?_lt27 hkd'.2 hr0
  have hs27 := objX?_lt27 hks'.2 hr1
  simp only [BitVec.toNat_ofNat] at hd27 hs27
  obtain ⟨a2, ha2, hamt, hah2⟩ := memArg_spec hma
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨xv, hxr, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv.core hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkd
  obtain ⟨yv, hyr, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv.core hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkks
  obtain ⟨x, y, hx, hy, rfl⟩ :=
    stepLoc_mloop hl hop (arr3 hsz3 ha0 ha1 ha2) (read_mem hl hah2 hamt hmm) hs
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
  obtain ⟨hcsl, hcfl, -⟩ := clobber_keeps54 (lc := lc) (v := v) s (by rw [hop]; exact mloop_flags)
  obtain ⟨mm0, hmm0, hk0, hsep0⟩ := hinv.core.mem
  rw [hmm] at hmm0
  cases hmm0
  generalize hn : v.auxInt.toInt.toNat = n at hcov hvs hrd' hdisj
  have hn64 : 64 ≤ n := by omega
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
  have hXD : m.x (BitVec.ofNat 5 kd) = ad + pd.off := by
    rw [← rX_of_lt hkd'.1]; simpa using hDeq
  have hXS : m.x (BitVec.ofNat 5 ks) = as + ps.off := by
    rw [← rX_of_lt hks'.1]; simpa using hSeq
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
      Keeps54 [BitVec.ofNat 5 ks, BitVec.ofNat 5 kd, BitVec.ofNat 5 24, BitVec.ofNat 5 25]
        [BitVec.ofNat 5 16, BitVec.ofNat 5 17] m m' := by
    by_cases hrr : (REG_R0 + (kd : Int)) = REG_R0 + ks
    · have hkk : kd = ks := by omega
      subst hkk
      simp only [hrr, beq_self_eq_true, ↓reduceIte, ManyAt2] at hvs
      subst hvs
      refine ⟨m, .refl, by rw [hm.pc, hj], fun j _ => ?_, fun _ _ => rfl, Keeps54.refl _⟩
      rw [← hXD, ← hXS]
    · simp only [beq_iff_eq, hrr, ↓reduceIte] at hvs
      have hr01 : r0 ≠ r1 := by
        rintro rfl
        exact hrr (by rw [Option.some.inj (hor0.symm.trans hor1)])
      have hlp : loopOp lc v = true := by
        simp only [loopOp, hop, beq_self_eq_true, Bool.true_and, Bool.or_eq_true, beq_iff_eq,
          reduceCtorEq, false_or, bne_iff_ne, ne_eq, ha0, ha1, Option.bind_some]
        rw [regHome?_eq.2 hah0, regHome?_eq.2 hah1]
        simpa using hr01
      obtain ⟨hin, hcovj⟩ := moveCovers_spec hcov
      generalize hN : n / 64 = N
      have hN64 : 64 * N ≤ n := by omega
      have hsd : as + ps.off = ad + pd.off ∨
          ∀ k, k < n → n ≤ (as + ps.off + BitVec.ofNat 64 k - (ad + pd.off)).toNat := by
        have hsep : (as + ps.off).toNat + n ≤ (ad + pd.off).toNat ∨
            (ad + pd.off).toNat + n ≤ (as + ps.off).toNat → ∀ k, k < n →
              n ≤ (as + ps.off + BitVec.ofNat 64 k - (ad + pd.off)).toNat := by
          intro h k hk
          rw [hDt, hSt] at h
          have h64' : (as + ps.off + BitVec.ofNat 64 k).toNat = as.toNat + ps.off.toNat + k := by
            rw [BitVec.toNat_add, hSt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
              Nat.mod_eq_of_lt (by omega)]
          rw [BitVec.toNat_sub, h64', hDt]
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
      -- the loop
      obtain ⟨ke, mN, hrunL, hpcN, htl, hsN, hdN, hkN, hmemN⟩ := mloop_run (H := H) F.nodup F.lt
        F.ret hks'.1 hkd'.1 (fun h => hrr (by rw [h])) hks24 hkd24 hvs (hloop hlp) h64 m hXS hXD
        ⟨by omega, by rw [hn]; omega⟩ ⟨by omega, by rw [hn]; omega⟩
      rw [pc_eta hm hj] at hrunL
      rw [hn, hN] at hsN hdN hmemN
      -- the tail
      obtain ⟨mT, hrunT, hpcT, hmemT, hkT⟩ := move_run (H := H) F.nodup F.lt F.ret (by omega : ks < 32)
        (by omega : kd < 32) hks25 hkd25 (S := as + ps.off + BitVec.ofNat 64 (64 * N))
        (D := ad + pd.off + BitVec.ofNat 64 (64 * N)) (moveOffs (n % 64)) ke j' mN htl
        (by rw [rX_of_lt hks'.1, hsN]) (by rw [rX_of_lt hkd'.1, hdN]) (fun c hc => by
          have := hin c hc
          have hw8 : 8 ≤ moveW c.1 := by
            unfold moveW; split
            · omega
            · split <;> omega
          have hSn : as.toNat + ps.off.toNat + n ≤ 2 ^ 64 := by omega
          have hDn : ad.toNat + pd.off.toNat + n ≤ 2 ^ 64 := by omega
          have hNn : 64 * N + 8 ≤ n := by omega
          have h1 : (as + ps.off + BitVec.ofNat 64 (64 * N)).toNat = as.toNat + ps.off.toNat + 64 * N := by
            rw [BitVec.toNat_add, hSt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
              Nat.mod_eq_of_lt (by omega)]
          have h2 : (ad + pd.off + BitVec.ofNat 64 (64 * N)).toNat = ad.toNat + pd.off.toNat + 64 * N := by
            rw [BitVec.toNat_add, hDt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
              Nat.mod_eq_of_lt (by omega)]
          rw [h1, h2]
          omega)
      have hetaN : ({ mN with pc := pcAt text psA.toList ke } : MState) = mN := by rw [← hpcN]
      rw [hetaN] at hrunT
      -- all the chunks, from the start
      let allC : List (Nat × Nat) :=
        mloopChunks N ++ (moveOffs (n % 64)).map fun c => (c.1, 64 * N + c.2)
      have hinA : ∀ c ∈ allC, c.2 + moveW c.1 ≤ n := by
        intro c hc
        rcases List.mem_append.1 hc with h | h
        · obtain ⟨h1, h2⟩ := mem_mloopChunks h
          rw [h1]; simp only [moveW, ↓reduceIte]; omega
        · obtain ⟨c0, h0, rfl⟩ := List.mem_map.1 h
          have := hin c0 h0
          simp only
          omega
      have hcovA : ∀ j, j < n → ∃ c ∈ allC, c.2 ≤ j ∧ j < c.2 + moveW c.1 := by
        intro j hj
        by_cases hjN : j < 64 * N
        · obtain ⟨c, hc, hcj⟩ := mloopChunks_cover hjN
          exact ⟨c, List.mem_append_left _ hc, hcj⟩
        · obtain ⟨c, hc, hcj⟩ := hcovj (j - 64 * N) (by omega)
          exact ⟨(c.1, 64 * N + c.2), List.mem_append_right _ (List.mem_map_of_mem hc),
            by simp only; omega⟩
      have hmemA : mT.mem = cpMem (as + ps.off) (ad + pd.off) m.mem allC := by
        rw [hmemT, cpMem_shift _ _ _ (fun c hc => by have := hin c hc; omega), hmemN,
          ← cpMem_append]
      have hget := cpMem_get hsd allC m.mem hinA
      refine ⟨mT, hrunL.trans hrunT, hpcT, fun j hj => ?_, fun y hy => ?_,
        ((hkN.mono (by simp) (by simp)).trans ((keeps54_of_53 hkT).mono (by simp) (by simp)))⟩
      · rw [hmemA, hget]
        have hsub : ad + pd.off + BitVec.ofNat 64 j - (ad + pd.off) = BitVec.ofNat 64 j := by
          grind
        have hjt : (ad + pd.off + BitVec.ofNat 64 j - (ad + pd.off)).toNat = j := by
          rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        rw [if_pos ?_, hsub]
        obtain ⟨c, hc, hcj⟩ := hcovA j hj
        exact ⟨c, hc, by rw [hjt]; exact hcj⟩
      · rw [hmemA, hget, if_neg]
        rintro ⟨c, hc, hc1, hc2⟩
        have := hinA c hc
        apply hy ((y - (ad + pd.off)).toNat) (by omega)
        rw [BitVec.toNat_sub] at hc1 hc2 ⊢
        have hy64 := y.isLt
        rw [hDt] at hc1 hc2 ⊢
        omega
  -- `MemInj`, the separation and the frame
  obtain ⟨hMI', hk', hback, -⟩ := memInj_writeAny hA hMI hk0 (by omega : 0 < n) had hbs
    (M := m'.mem) (fun j hj => by rw [hcp j hj]; exact hsrc j hj) hout hwr
  have hsep' : SepFrom E.ι (StkAt E) mm' := by
    intro b2 al2 a2 hb hι w hw'
    obtain ⟨al0, hb0, hs0⟩ := hback b2 al2 hb
    rw [← hs0]; exact hsep0 b2 al0 a2 hb0 hι w hw'
  have hP : ∀ y, StkAt E y → m'.mem y = m.mem y := fun y hy =>
    hout y fun j hj he => hsep0 _ _ _ hald had y hy ⟨by omega, by omega⟩
  have hq : ∀ q : Nat, 27 ≤ q → q < 32 → m'.x (BitVec.ofNat 5 q) = m.x (BitVec.ofNat 5 q) := by
    intro q hq1 hq2
    refine hkeep.2.2.1 _ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro he <;> have := congrArg BitVec.toNat he <;> simp at this <;>
      omega
  obtain ⟨hslots, hframe⟩ := stk_slots_frame (E' := E) (m' := m') hm hF hsz rfl
    (fun _ _ h => h) hP hkeep.1 (hq 28 (by omega) (by omega)) (hq 29 (by omega) (by omega))
    (fun _ => hq 30 (by omega) (by omega))
  -- the registers `runLoc` keeps are not the machine's changed ones
  have hreg : ∀ r x, (s.clobber lc v).regs[r]? = some x → x = .poison ∨
      (s.regs[r]? = some x ∧ (∀ q, objX? r = some q → m'.x q = m.x q) ∧
        ∀ q, objV? r = some q → m'.v q = m.v q) := by
    intro r x h
    rcases clobber_get54 h with rfl | ⟨h2, hmask, h0, h1, -⟩
    · exact .inl rfl
    rw [hop] at hmask h0 h1
    have hr23 : r ≠ 23 := by rintro rfl; rw [mloop_m23] at hmask; cases hmask
    have hr24 : r ≠ 24 := by rintro rfl; rw [mloop_m24] at hmask; cases hmask
    have hr47 : r ≠ 47 := by rintro rfl; rw [mloop_m47] at hmask; cases hmask
    have hr48 : r ≠ 48 := by rintro rfl; rw [mloop_m48] at hmask; cases hmask
    refine .inr ⟨h2, fun q hq => hkeep.2.2.1 q ?_, fun q hq => hkeep.2.2.2 q ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rintro rfl
        have := objX?_inj hq hks'.2
        subst this
        have := h1 mloop_arg1 (by simp [ha1, LocCtx.regOf, hah1])
        unfold zeroReg at this; omega
      · rintro rfl
        have := objX?_inj hq hkd'.2
        subst this
        have := h0 mloop_arg0 (by simp [ha0, LocCtx.regOf, hah0])
        unfold zeroReg at this; omega
      · rintro rfl
        exact hr23 (objX?_inj hq rfl)
      · rintro rfl
        exact hr24 (objX?_inj hq rfl)
    · obtain ⟨h16, h17⟩ := objV?_ne1617 hq hr47 hr48
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨h16, h17⟩
  refine ⟨m', hrun, ⟨fun r x h => ?_, ?_, ?_, ⟨mm', rfl, hMI'⟩, hframe, ?_⟩,
    ⟨⟨fun r x c hrz h hc => ?_, mm', rfl, hk', hsep'⟩, fun k y hk => hinv.slots k y ?_⟩⟩
  · rcases hreg r x h with rfl | ⟨h2, hx, hv⟩
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
    · obtain ⟨hx1, hv1⟩ := hm.regs r x h2
      exact ⟨fun q hq => by rw [hx q hq]; exact hx1 q hq, fun q hq => by rw [hv q hq]; exact hv1 q hq⟩
  · show FlagsRel (s.clobber lc v).flags m'.nzcv
    rw [hcfl, hkeep.2.1]
    exact hm.flags
  · show ∀ k y, (s.clobber lc v).slots.lookup k = some y → _
    rw [hcsl]
    exact hslots
  · show m'.pc = E.pcOf b (i + 1)
    rw [hpc', hj']
  · rcases clobber_get54 h with rfl | ⟨h2, -⟩
    · trivial
    · exact hinv.core.regs r x c hrz h2 hc
  · rw [← hcsl]; exact hk

end Cases

end GoFV.Proof.Gen

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

end GoFV.Proof.Gen

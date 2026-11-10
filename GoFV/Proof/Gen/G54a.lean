import GoFV.Proof.Gen.G54L

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G54, `LoweredZeroLoop` (`docs/plans/proofs3.md` §4)

`vkind54a` (`GoFV/Gen/Check54a.lean`) accepts `LoweredZeroLoop [n] p mem` with its temporary as
the loop counter; `VK54a.zero` (`Spec54a.lean`) says what it accepted. `runLoc` runs it as its
clobbers (`p`'s register and the temporary hold `poison`) then `Arm64.zero`: `n` zero bytes at `p`,
or `poison` if the write is invalid (`stepLoc_zloop`), which the run premise `Pre54a` excludes.

Genssa emits `MOVD $n/64, Rc`, a body of four `STP.P (ZR, ZR), 16(Rp)`, `SUB $1, Rc` and
`CBNZ Rc` back to the body, then `zeroTail`'s stores of the `n mod 64` bytes left off the advanced
`Rp`. The machine (`zloop_run`): the counter's `MOVD`, then by induction over the `n / 64`
iterations (`loop_run`, invariant: after `i` iterations `Rp` holds `p + 64 i`, `Rc` holds
`n / 64 - i`, the bytes below `p + 64 i` are 0, `zloopStores`), each the body (`stpP_run`) and the
counter (`count_run`); then `zero_run` of the tail at `p + 64 (n / 64)`. Every byte of the `n` is
covered (`zcover`) and nothing outside is written, so the bytes at the write's injected address are
the zeros `runLoc` wrote, which keeps `MemInj` (`memInj_writeAny`); they lie inside a live block,
away from the frame. On the machine only `Rp` and `Rc` change, the registers `runLoc` sets to
`poison`. `vk54a_zero` is one value.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The premise -/

/-- `LoweredZeroLoop [n] p mem` writes its `n` zero bytes at a valid address (Go zeroes memory it
owns). -/
def Pre54a (lc : LocCtx) (s : LocState) (v : Value) : Prop :=
  v.op = .ARM64LoweredZeroLoop → ∀ a x, v.args[0]? = some a → s.read lc a = .ok x →
    ∃ p mm mm', Arm64.addr x 0 = some p ∧ s.mem = .mem mm ∧
      mm.write p (Array.replicate v.auxInt.toInt.toNat (.b 0)) = some mm'

/-! ## `stepLoc` -/

section Step

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

/-- `LoweredZeroLoop [n] p mem`: its clobbers, then `Arm64.zero` of its arguments as the memory. -/
theorem stepLoc_zloop (hl : lc.ctx.f.lowered = true) (hop : v.op = .ARM64LoweredZeroLoop)
    {a mem : ID} (ha : v.args = #[a, mem]) {mm : Mem} (hmem : s.read lc mem = .ok (.mem mm))
    (h : stepLoc env lc s v = .ok s') :
    ∃ x, s.read lc a = .ok x ∧
      s' = (s.clobber lc v).write lc v.id ((Arm64.zero v.auxInt [x, .mem mm]).retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, hmv, hr, rfl⟩ := stepLoc_ok_eval (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) h
  rw [ha] at hmv
  change ((s.read lc a).bind fun x => (s.read lc mem).bind fun y => .ok [x, y]) = .ok argv at hmv
  cases hx : s.read lc a with
  | panic e m0 => rw [hx] at hmv; cases hmv
  | stuck msg => rw [hx] at hmv; cases hmv
  | ok x =>
    rw [hx, hmem] at hmv
    cases hmv
    refine ⟨x, rfl, ?_⟩
    rw [lmode_retype hl]
    cases hnf : nilFaults true lc.ctx v [x, .mem mm] with
    | some m0 =>
      have he : evalOpL true env lc.ctx s.fr v [x, .mem mm] (lc.ty v.id) = .panic .nilDeref m0 := by
        unfold evalOpL arm64Op
        simp only [hop, hnf]
        rfl
      rw [he] at hr
      cases hr
    | none =>
      have he : evalOpL true env lc.ctx s.fr v [x, .mem mm] (lc.ty v.id) =
          .ok (Arm64.zero v.auxInt [x, .mem mm]) := by
        unfold evalOpL arm64Op
        simp only [hop, hnf]
        rfl
      rw [he] at hr
      cases hr
      rfl

end Step

/-! ## The machine's stores -/

/-- The stores of the first `i` iterations: an `STP` of 16 zero bytes at each multiple of 16 below
`64 i`. -/
def zloopStores (i : Nat) : List (Bool × Nat) := (List.range' 0 (4 * i) 16).map fun o => (true, o)

theorem zeroStore_shift (A : BitVec 64) (c : Nat) (M : Memory) (st : Bool × Nat) :
    zeroStore (A + BitVec.ofNat 64 c) M st = zeroStore A M (st.1, c + st.2) := by
  obtain ⟨pr, o⟩ := st
  have h : A + BitVec.ofNat 64 c + BitVec.ofNat 64 o = A + BitVec.ofNat 64 (c + o) := by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  simp only [zeroStore, h]

theorem zeroMem_shift (A : BitVec 64) (c : Nat) (offs : List (Bool × Nat)) :
    ∀ (M : Memory),
      zeroMem (A + BitVec.ofNat 64 c) M offs = zeroMem A M (offs.map fun st => (st.1, c + st.2)) := by
  induction offs with
  | nil => intro M; simp only [zeroMem, List.foldl_nil, List.map_nil]
  | cons st rest ih =>
    intro M
    simp only [zeroMem, List.foldl_cons, List.map_cons] at ih ⊢
    rw [zeroStore_shift]
    exact ih _

theorem zeroMem_append (A : BitVec 64) (M : Memory) (a b : List (Bool × Nat)) :
    zeroMem A M (a ++ b) = zeroMem A (zeroMem A M a) b := List.foldl_append

theorem zloopStores_succ (i : Nat) :
    zloopStores (i + 1) = zloopStores i ++ (List.range' (64 * i) 4 16).map fun o => (true, o) := by
  unfold zloopStores
  rw [← List.map_append, show 4 * (i + 1) = 4 * i + 4 by omega, ← List.range'_append]
  congr 3
  omega

theorem mem_zloopStores {i : Nat} {st : Bool × Nat} (h : st ∈ zloopStores i) :
    st.1 = true ∧ st.2 + 16 ≤ 64 * i := by
  simp only [zloopStores, List.mem_map, List.mem_range'] at h
  obtain ⟨o, ⟨k, hk, rfl⟩, rfl⟩ := h
  exact ⟨rfl, by omega⟩

theorem zloopStores_cover {i j : Nat} (hj : j < 64 * i) :
    ∃ st ∈ zloopStores i, st.2 ≤ j ∧ j < st.2 + zeroW st.1 := by
  refine ⟨(true, 16 * (j / 16)), ?_, ?_⟩
  · simp only [zloopStores, List.mem_map, List.mem_range', Prod.mk.injEq, true_and]
    exact ⟨16 * (j / 16), ⟨j / 16, by omega, by omega⟩, rfl⟩
  · simp only [zeroW, ↓reduceIte]
    omega

section Run

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64}

/-- `n` `STP.P (ZR, ZR), 16(Rn)` from `X kn = A + c`: 16 zero bytes at each of `A + c`,
`A + c + 16`, …; `X kn` ends at `A + c + 16 n`. -/
theorem stpP_run (hnd : (psA.toList.map (·.id)).Nodup) (hlt : ∀ p ∈ psA.toList, p.id < 2 ^ 32)
    (hret : ∀ p ∈ psA.toList, (Link.byId sym text az ez psA.toList).addr p.id ≠ some ret)
    {kn : Nat} (hkn : kn < 31) {A : BitVec 64} :
    ∀ (n c j j' : Nat) (m : MState),
      ManyAt2 psA j (List.replicate n (stpPPat (REG_R0 + kn))) j' →
      m.x (BitVec.ofNat 5 kn) = A + BitVec.ofNat 64 c →
      (∀ h, h < n → nilPage (A + BitVec.ofNat 64 (c + 16 * h)) = false ∧
        nilPage (A + BitVec.ofNat 64 (c + 16 * h + 8)) = false) →
      ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret
          { m with pc := pcAt text psA.toList j } m' ∧
        m'.pc = pcAt text psA.toList j' ∧
        m'.x (BitVec.ofNat 5 kn) = A + BitVec.ofNat 64 (c + 16 * n) ∧
        Keeps54 [BitVec.ofNat 5 kn] [] m m' ∧
        m'.mem = zeroMem A m.mem ((List.range' c n 16).map fun o => (true, o))
  | 0, c, j, j', m, h, hx, _ => by
    simp only [List.replicate, ManyAt2] at h
    subst h
    exact ⟨_, .refl, rfl, by simpa using hx, Keeps54.refl _, rfl⟩
  | n + 1, c, j, j', m, h, hx, hnil => by
    obtain ⟨k, h1, h2⟩ := h
    let m1 : MState := { m.wX (BitVec.ofNat 5 kn) (A + BitVec.ofNat 64 c + BitVec.ofNat 64 16) with
      mem := zeroStore (A + BitVec.ofNat 64 c) m.mem (true, 0) }
    have hn0 := hnil 0 (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at hn0
    have hs1 := pstar_one54 (H := H) hnd hlt hret h1 m m1 (fun k hk hok => by
      have hr : ({ m with pc := pcAt text psA.toList k } : MState).rX (BitVec.ofNat 5 kn) =
          A + BitVec.ofNat 64 c := by
        show m.rX _ = _; rw [rX_of_lt hkn, hx]
      rw [progStep_stpP hkn (nextAddr_pcAt hnd hk) hok (by rw [hr]; exact hn0.1)
        (by rw [hr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; exact hn0.2), hr]
      simp only [wX_pc]
      rfl)
    have hx1 : m1.x (BitVec.ofNat 5 kn) = A + BitVec.ofNat 64 (c + 16) := by
      show (m.wX _ _).x _ = _
      rw [wX_x_self54 hkn, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    obtain ⟨m2, hs2, hpc2, hx2, hk2, hmem2⟩ := stpP_run hnd hlt hret hkn n (c + 16) k j' m1 h2 hx1
      (fun h hh => by
        have := hnil (h + 1) (by omega)
        rwa [show c + 16 * (h + 1) = c + 16 + 16 * h by omega] at this)
    refine ⟨m2, hs1.trans hs2, hpc2, by rw [hx2]; congr 2; omega,
      (keeps54_mem (keeps54_wX (List.mem_singleton.2 rfl)) _).trans hk2, ?_⟩
    rw [hmem2]
    show zeroMem A (zeroStore (A + BitVec.ofNat 64 c) m.mem (true, 0)) _ =
      zeroMem A (zeroStore A m.mem (true, c)) _
    rw [zeroStore_shift]
    rfl

/-- The zero loop, from its `MOVD` at index `j`: the machine reaches the Prog after the `CBNZ`
(`ke`, where the tail starts) with `X kp` advanced by `64 N` (`N = n / 64`), `X kc` and the memory
changed only by the zeros below `A + 64 N` (`zloopStores N`). -/
theorem zloop_run (hnd : (psA.toList.map (·.id)).Nodup) (hlt : ∀ p ∈ psA.toList, p.id < 2 ^ 32)
    (hret : ∀ p ∈ psA.toList, (Link.byId sym text az ez psA.toList).addr p.id ≠ some ret)
    {kp kc : Nat} (hkp : kp < 31) (hkc : kc < 31) (hne : kp ≠ kc) {n : Int} {tail : List Pat}
    {j j' : Nat}
    (hvs : ManyAt2 psA j (loopPats (REG_R0 + kc) n (zeroBody (REG_R0 + kp)) ++ tail) j')
    (hloop : loopTgt psA j = true) (h64 : 64 ≤ n) {A : BitVec 64} (m : MState)
    (hA : m.x (BitVec.ofNat 5 kp) = A) (hA1 : 4096 ≤ A.toNat) (hA2 : A.toNat + n.toNat ≤ 2 ^ 64) :
    ∃ ke m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret
        { m with pc := pcAt text psA.toList j } m' ∧
      m'.pc = pcAt text psA.toList ke ∧ ManyAt2 psA ke tail j' ∧
      m'.x (BitVec.ofNat 5 kp) = A + BitVec.ofNat 64 (64 * (n.toNat / 64)) ∧
      Keeps54 [BitVec.ofNat 5 kp, BitVec.ofNat 5 kc] [] m m' ∧
      m'.mem = zeroMem A m.mem (zloopStores (n.toNat / 64)) := by
  obtain ⟨k1, kb, ks, ke, hmv, hbody, hsub, hcb, htl, hk1, hke, hbr⟩ :=
    loopTgt_spec hvs (stpPPat_code _) (stpPPat_code _) (stpPPat_code _) (stpPPat_code _) hloop
  generalize hN : n.toNat / 64 = N
  have hN1 : 1 ≤ N := by omega
  have hNlt : N < 2 ^ 64 := by omega
  have hn64 : n / 64 = (N : Int) := by omega
  have hkpc : (BitVec.ofNat 5 kp : Reg) ≠ BitVec.ofNat 5 kc := by
    intro h; have := congrArg BitVec.toNat h; simp at this; omega
  -- the counter's `MOVD $N, Rc`
  let m0 : MState := m.wX (BitVec.ofNat 5 kc) (BitVec.ofNat 64 N)
  have hs0 := pstar_one54 (H := H) hnd hlt hret hmv m m0 (fun k hk hok => by
    obtain ⟨has, hf, -, ht, -⟩ := Shape.ok_eq hok
    rw [progStep_movConst (by omega : kc < 32) (nextAddr_pcAt hnd hk) has hf ht, hn64, ofInt_nat]
    simp only [wX_pc]
    rfl)
  -- the invariant after `i` iterations
  let I : Nat → MState → Prop := fun i m' =>
    Keeps54 [BitVec.ofNat 5 kp, BitVec.ofNat 5 kc] [] m m' ∧
      m'.x (BitVec.ofNat 5 kp) = A + BitVec.ofNat 64 (64 * i) ∧
      m'.x (BitVec.ofNat 5 kc) = BitVec.ofNat 64 (N - i) ∧
      m'.mem = zeroMem A m.mem (zloopStores i)
  have hI0 : I 0 { m0 with pc := pcAt text psA.toList k1 } := by
    refine ⟨keeps54_pc (keeps54_wX (by simp)) _, ?_, ?_, ?_⟩
    · show (m.wX _ _).x _ = _
      rw [wX_x_of_ne hkpc, hA]; simp
    · show (m.wX _ _).x _ = _
      rw [wX_x_self54 hkc]; simp
    · show (m.wX _ _).mem = _
      rw [(wX_fields).1]; rfl
  have hstep : ∀ i m1, i < N → I i m1 → m1.pc = pcAt text psA.toList k1 →
      ∃ m2, PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m1 m2 ∧ I (i + 1) m2 ∧
        m2.pc = if i + 1 = N then pcAt text psA.toList ke else pcAt text psA.toList k1 := by
    intro i m1 hi ⟨hk1', hx1, hc1, hmem1⟩ hpc1
    have heta : ({ m1 with pc := pcAt text psA.toList k1 } : MState) = m1 := by rw [← hpc1]
    -- the body
    obtain ⟨m2, hs2, hpc2, hx2, hk2, hmem2⟩ := stpP_run (H := H) hnd hlt hret hkp 4 (64 * i) k1 kb
      m1 hbody hx1 (fun h hh => by
        constructor
        · exact nil_of hA1 (by omega)
        · exact nil_of hA1 (by omega))
    rw [heta] at hs2
    have heta2 : ({ m2 with pc := pcAt text psA.toList kb } : MState) = m2 := by rw [← hpc2]
    -- the counter
    obtain ⟨m3, hs3, hx3, hk3, hmem3, hpc3⟩ := count_run (H := H) hnd hlt hret hkc hsub hcb hk1
      hke hbr m2
    rw [heta2] at hs3
    have hc2 : m2.x (BitVec.ofNat 5 kc) = BitVec.ofNat 64 (N - i) := by
      rw [hk2.2.2.1 _ (by simpa using hkpc.symm), hc1]
    have hcnt : BitVec.ofNat 64 (N - i) - 1 = BitVec.ofNat 64 (N - (i + 1)) := by
      rw [show N - i = N - (i + 1) + 1 by omega, ← BitVec.ofNat_add_ofNat]
      exact BitVec.add_sub_cancel _ _
    refine ⟨m3, hs2.trans hs3, ⟨hk1'.trans ((hk2.mono (by simp) (by simp)).trans
      (hk3.mono (by simp) (by simp))), ?_, ?_, ?_⟩, ?_⟩
    · rw [hk3.2.2.1 _ (by simpa using hkpc), hx2, show 64 * i + 16 * 4 = 64 * (i + 1) by omega]
    · rw [hx3, hc2, hcnt]
    · rw [hmem3, hmem2, hmem1, ← zeroMem_append, zloopStores_succ]
    · rw [hpc3, hc2, hcnt]
      by_cases he : i + 1 = N
      · rw [if_pos he, if_pos (by rw [show N - (i + 1) = 0 by omega]; rfl)]
      · rw [if_neg he, if_neg]
        intro h0
        have := congrArg BitVec.toNat h0
        rw [BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl] at this
        omega
  obtain ⟨mN, hsN, ⟨hkN, hxN, -, hmemN⟩, hpcN⟩ := loop_run hstep N 0 _ (by omega) (by omega) hI0 rfl
  exact ⟨ke, mN, hs0.trans hsN, hpcN, htl, hxN, hkN, hmemN⟩

end Run

/-! ## The value -/

private theorem zloop_arg0 : Op.ARM64LoweredZeroLoop.regInfo.clobbersArg0 = true := by decide

private theorem zloop_flags : Op.ARM64LoweredZeroLoop.clobberFlags = false := by decide

/-- The upper-bit table is empty after `LoweredZeroLoop`. -/
theorem uStep35_54a {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value}
    (hop : v.op = .ARM64LoweredZeroLoop) : uStep35 lc L v = [] := by
  simp [uStep35, ldEntry35, loadOp?, narrowLoad?, pairOp35, uStep34, keep34, keep31, keepOp31,
    keepOp34, uStepL, uEntry, narrowLd?, loadIdxOp?, hop]

/-- A Go register `r < 26` with X register `k`: `k < 27` (not `g`, `FP`, `LR`). -/
theorem objX?_lt27 {r : Nat} {k : Reg} (h : objX? r = some k) (hr : r < 26) : k.toNat < 27 := by
  obtain ⟨-, hk⟩ := objX?_some h
  rw [hk]
  split <;> omega

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K : KMap}

/-- `LoweredZeroLoop [n] p mem`: the loop and the tail zero the `n` bytes at `p`'s injected
address, inside a live block and away from the frame; `p`'s register and the temporary are
`poison` in `runLoc`, the only X registers the machine changes. -/
theorem g54a_zero (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size = 8)
    (hm : LocMatch E s b i m) (hinv : G3Inv E lc K s osp) (hR : KRead lc v K.get)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {t : Nat} {rp rc : Int} (hop : v.op = .ARM64LoweredZeroLoop)
    (ht : (lc.temps[v.id]?).join = some t) (hsz2 : v.args.size = 2)
    (hmt : memTy (lc.ty v.id) = true) (hhn : lc.home v.id = none)
    (hao : argObj lc v 0 = .ok (64, rp)) (hma : memArg lc v 1 = .ok ())
    (hrc : objOf? t = some rc) (h64 : 64 ≤ v.auxInt.toInt) (hdst : argDest lc v 0 = true)
    (ht26 : t < 26) (hne : rc ≠ rp)
    (hcov : zeroCovers (v.auxInt.toInt.toNat % 64) (zeroOffs (v.auxInt.toInt.toNat % 64)) = true)
    (hvs : ManyAt2 psA j (loopPats rc v.auxInt.toInt (zeroBody rp) ++
      (zeroOffs (v.auxInt.toInt.toNat % 64)).map (zeroPat rp)) j')
    (hloop : loopTgt psA j = true) (hpre : Pre54a lc s v) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ G3Inv E lc K s' osp := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  -- the registers
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨a0', r0', ha0', hah0', hr26⟩ := argDest_spec hdst
  rw [ha0] at ha0'
  cases ha0'
  rw [hah0] at hah0'
  cases hah0'
  obtain ⟨kp, hkp, rfl, hkkp⟩ := objOf?_some hor0
  have hkp' : kp < 31 ∧ objX? r0 = some (BitVec.ofNat 5 kp) := by
    rcases hkkp with ⟨h, -⟩ | h
    · exact absurd h (by unfold zeroReg; omega)
    · exact h
  obtain ⟨kc, hkc, rfl, hkkc⟩ := objOf?_some hrc
  have hkc' : kc < 31 ∧ objX? t = some (BitVec.ofNat 5 kc) := by
    rcases hkkc with ⟨h, -⟩ | h
    · exact absurd h (by unfold zeroReg; omega)
    · exact h
  have hpc' : kp ≠ kc := fun h => hne (by rw [h])
  have hp27 := objX?_lt27 hkp'.2 hr26
  have hc27 := objX?_lt27 hkc'.2 ht26
  simp only [BitVec.toNat_ofNat] at hp27 hc27
  obtain ⟨a1, ha1, hamt, hah1⟩ := memArg_spec hma
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨xv, hxr, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv.core hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkp
  obtain ⟨x, hx, rfl⟩ :=
    stepLoc_zloop hl hop (arr2 hsz2 ha0 ha1) (read_mem hl hah1 hamt hmm) hs
  rw [hxr] at hx
  cases hx
  obtain ⟨p, mm1, mm', hp, hmm1, hw⟩ := hpre hop a0 xv ha0 hxr
  rw [hmm] at hmm1
  cases hmm1
  have hz : Arm64.zero v.auxInt [xv, .mem mm] = .mem mm' := by
    simp only [Arm64.zero, hp, hw]
  rw [hz, write_mem hhn hmt, memTy_eq hmt, retypeL_mem]
  obtain ⟨hcsl, hcfl, -⟩ := clobber_keeps54 (lc := lc) (v := v) s (by rw [hop]; exact zloop_flags)
  obtain ⟨mm0, hmm0, hk0, hsep0⟩ := hinv.core.mem
  rw [hmm] at hmm0
  cases hmm0
  generalize hn : v.auxInt.toInt.toNat = n at hcov hvs hw
  have hn64 : 64 ≤ n := by omega
  have hbs : (Array.replicate n (Byte.b 0)).size = n := Array.size_replicate
  obtain ⟨al, hal, hoff⟩ := write_inside hw (by rw [hbs]; omega)
  rw [hbs] at hoff
  have hcan : mm.canWrite p n = true := by
    have := canWrite_of_write hw (by rw [hbs]; omega)
    rwa [hbs] at this
  obtain ⟨a, hpa, haeq, -⟩ := addr_rel hA hMI hxv hxf hp (by omega : 0 < n) (Or.inl hcan)
  obtain ⟨a', ha', hlo, hhi⟩ := hMI.mapped _ _ hal
  obtain rfl : a = a' := Option.some.inj (hpa.symm.trans ha')
  have h4 := hlo (by omega)
  have hAt : (a + p.off).toNat = a.toNat + p.off.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hX : m.x (BitVec.ofNat 5 kp) = a + p.off := by
    rw [← rX_of_lt hkp'.1]; simpa using haeq
  -- the loop, then the tail at `a + p.off + 64 N`
  obtain ⟨ke, mN, hrunL, hpcN, htl, hxN, hkN, hmemN⟩ := zloop_run (H := H) F.nodup F.lt F.ret
    hkp'.1 hkc'.1 hpc' hvs hloop h64 m hX (by omega) (by rw [hn]; omega)
  rw [pc_eta hm hj] at hrunL
  rw [hn] at hxN hmemN
  generalize hN : n / 64 = N at hxN hmemN
  have hN64 : 64 * N ≤ n := by omega
  obtain ⟨hin, hcovd⟩ := zeroCovers_spec hcov
  have hw8 : ∀ pr : Bool, 8 ≤ zeroW pr := fun pr => by unfold zeroW; split <;> omega
  have hnilT : ∀ st ∈ zeroOffs (n % 64),
      nilPage (a + p.off + BitVec.ofNat 64 (64 * N) + BitVec.ofNat 64 st.2) = false ∧
      (st.1 = true →
        nilPage (a + p.off + BitVec.ofNat 64 (64 * N) + BitVec.ofNat 64 st.2 + 8) = false) := by
    intro st hst
    have hi := hin st hst
    have h8 := hw8 st.1
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    refine ⟨nil_of (by omega) (by omega), fun hpr => ?_⟩
    rw [hpr] at hi
    simp only [zeroW, ↓reduceIte] at hi
    rw [BitVec.add_assoc, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat]
    exact nil_of (by omega) (by omega)
  have hrunT := zero_run (H := H) F.nodup F.lt F.ret (by omega : kp < 32) (zeroOffs (n % 64)) ke
    j' mN htl hnilT (by rw [rX_of_lt hkp'.1, hxN])
  have hetaN : ({ mN with pc := pcAt text psA.toList ke } : MState) = mN := by rw [← hpcN]
  rw [hetaN] at hrunT
  let MT : Memory :=
    zeroMem (a + p.off + BitVec.ofNat 64 (64 * N)) mN.mem (zeroOffs (n % 64))
  let m' : MState := { mN with mem := MT, pc := pcAt text psA.toList j' }
  -- every store, from `a + p.off`
  let allSt : List (Bool × Nat) :=
    zloopStores N ++ (zeroOffs (n % 64)).map fun st => (st.1, 64 * N + st.2)
  have hmem' : m'.mem = zeroMem (a + p.off) m.mem allSt := by
    show zeroMem _ mN.mem _ = _
    rw [hmemN, zeroMem_shift, zeroMem_append]
  have hinA : ∀ st ∈ allSt, st.2 + zeroW st.1 ≤ n := by
    intro st hst
    rcases List.mem_append.1 hst with h | h
    · obtain ⟨h1, h2⟩ := mem_zloopStores h
      rw [h1]; simp only [zeroW, ↓reduceIte]; omega
    · obtain ⟨st0, h0, rfl⟩ := List.mem_map.1 h
      have := hin st0 h0
      simp only
      omega
  have hcovA : ∀ j, j < n → ∃ st ∈ allSt, st.2 ≤ j ∧ j < st.2 + zeroW st.1 := by
    intro j hj
    by_cases hjN : j < 64 * N
    · obtain ⟨st, hst, hc⟩ := zloopStores_cover hjN
      exact ⟨st, List.mem_append_left _ hst, hc⟩
    · obtain ⟨st, hst, hc⟩ := hcovd (j - 64 * N) (by omega)
      exact ⟨(st.1, 64 * N + st.2), List.mem_append_right _ (List.mem_map_of_mem hst),
        by simp only; omega⟩
  have hbnd : ∀ st ∈ allSt, (a + p.off).toNat + st.2 + zeroW st.1 ≤ 2 ^ 64 := by
    intro st hst; have := hinA st hst; omega
  have hMout : ∀ y : BitVec 64, (∀ j, j < n → y.toNat ≠ a.toNat + p.off.toNat + j) →
      m'.mem y = m.mem y := by
    intro y hy
    rw [hmem']
    refine zeroMem_out allSt m.mem hbnd fun st hst hc => ?_
    have hi := hinA st hst
    have h8 := hw8 st.1
    unfold Covers at hc
    exact hy (y.toNat - (a.toNat + p.off.toNat)) (by omega) (by omega)
  obtain ⟨hMI', hk', hback, -⟩ := memInj_writeAny hA hMI hk0 (by omega) hpa hbs (M := m'.mem)
    (fun j hj => by
      obtain ⟨st, hst, hc⟩ := hcovA j hj
      have hi := hinA st hst
      have hy : (a + p.off + BitVec.ofNat 64 j).toNat = a.toNat + p.off.toNat + j := by
        rw [BitVec.toNat_add, hAt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : j < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega)]
      rw [hmem', zeroMem_cov allSt m.mem hbnd ⟨st, hst, by unfold Covers; rw [hy, hAt]; omega⟩]
      rw [getElem!_pos _ _ (by rw [hbs]; exact hj), Array.getElem_replicate]
      rfl)
    hMout hw
  have hsep' : SepAt osp E.ι (StkAt E) mm' := hsep0.write hk0 hw
  have hwf := write_wf hw (by rw [hbs]; omega)
  have hP : ∀ y, StkAt E y → m'.mem y = m.mem y := fun y hy =>
    hMout y fun j hj he => hsep0.not_mem hal hpa hy (by omega) (by omega)
  have hkeep : Keeps54 [BitVec.ofNat 5 kp, BitVec.ofNat 5 kc] [] m m' := hkN
  have hq : ∀ q : Nat, 27 ≤ q → q < 32 → m'.x (BitVec.ofNat 5 q) = m.x (BitVec.ofNat 5 q) := by
    intro q hq1 hq2
    refine hkeep.2.2.1 _ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    constructor <;> intro he <;> have := congrArg BitVec.toNat he <;> simp at this <;> omega
  obtain ⟨hslots, hframe⟩ := stk_slots_frame (E' := E) (m' := m') hm hF hsz rfl
    (fun _ _ h => h) hP hkeep.1 (hq 28 (by omega) (by omega)) (hq 29 (by omega) (by omega))
    (fun _ => hq 30 (by omega) (by omega))
  -- the registers `runLoc` keeps are not the machine's changed ones
  have hreg : ∀ r x, (s.clobber lc v).regs[r]? = some x → x = .poison ∨
      (s.regs[r]? = some x ∧ ∀ q, objX? r = some q → m'.x q = m.x q) := by
    intro r x h
    rcases clobber_get54 h with rfl | ⟨h2, -, h0, -, htp⟩
    · exact .inl rfl
    refine .inr ⟨h2, fun q hq => hkeep.2.2.1 q ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    constructor
    · rintro rfl
      have hr0 := objX?_inj hq hkp'.2
      subst hr0
      have := h0 (by rw [hop]; exact zloop_arg0) (by simp [ha0, LocCtx.regOf, hah0])
      unfold zeroReg at this; omega
    · rintro rfl
      have hrt := objX?_inj hq hkc'.2
      subst hrt
      have := htp ht
      unfold zeroReg at this; omega
  refine ⟨m', hrunL.trans hrunT, ⟨fun r x h => ?_, ?_, ?_, ⟨mm', rfl, hMI'⟩, hframe, ?_⟩,
    ⟨⟨fun r x c hrz h hc => ?_, mm', rfl, hk', hsep'⟩, fun k v hk => hinv.slots k v ?_⟩⟩
  · rcases hreg r x h with rfl | ⟨h2, hx⟩
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
    · obtain ⟨hx1, hv1⟩ := hm.regs r x h2
      refine ⟨fun q hq => ?_, fun q hq => ?_⟩
      · rw [hx q hq]; exact hx1 q hq
      · rw [hkeep.2.2.2 q (by simp)]; exact hv1 q hq
  · show FlagsRel (s.clobber lc v).flags m'.nzcv
    rw [hcfl, hkeep.2.1]
    exact hm.flags
  · show ∀ k y, (s.clobber lc v).slots.lookup k = some y → _
    rw [hcsl]
    exact hslots
  · show m'.pc = E.pcOf b (i + 1)
    rw [hj']
  · rcases clobber_get54 h with rfl | ⟨h2, -⟩
    · trivial
    · exact hinv.core.regs r x c hrz h2 hc
  · rw [← hcsl]; exact hk

end Cases

end GoFV.Proof.Gen

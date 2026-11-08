import GoFV.Proof.Gen.G7
import GoFV.Proof.Gen.Spec8

variable [GoFV.SSA.Sem.Addrs]

/-!
# Soundness of the genssa validator's slice G8: write barriers (`docs/plans/proofs3.md` §4)

`g8_value`, `g8_term`, `g8_nilPanic`: `g7_value`'s, `g7_term`'s and `g7_nilPanic`'s statements over
`checkG8`, under the activation `G8Env` (G6's, and no write barrier in a frameless function: its
`CALL` overwrites `X30`), with the trusted write-barrier contract `WbOK` as a premise of
`g8_value` next to `CallOK`.

A write-barrier request `LoweredWB [n] mem` runs under `runLoc` as `wbOp` (Phase 1's `WB`): a
fresh buffer block `wbuf` of `8n` poison bytes (`Mem.wbAlloc`) and the pointer to it, written to
the pair home `(R25, -)`, after the op's clobbers (`R16`, `R17`, `R30`, the `F` registers and the
flags hold `poison`). On the machine its Prog `CALL runtime.gcWriteBarrier<n>(SB)` puts the return
address in `X30` and enters the runtime hook (semantics3 §6, `wbHook`). What the hook does is the
trusted contract `WbOK`/`WbSpec` (listed in `docs/proofs/STATUS.md` Assumptions), which mirrors
`wbHook`: it returns to `X30` with `SP` and every register but `X25` and `X27` kept and the
memory unchanged, `X25` the address of the buffer under an injection that extends `ι` and puts the
buffer apart from the live blocks and the frame (`g8_wb`). The selections of the request are no
code: `Select0` (the buffer pointer, homed in `R25`) rereads the register (`g8_sel0`), `Select1`
(the memory) changes nothing (`g8_sel1`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm

/-! ## The premises -/

/-- **The write-barrier hook's contract** (trusted, semantics3 §6, mirroring `wbHook`;
`docs/proofs/STATUS.md` Assumptions): from the machine state `m` at the entry of
`runtime.gcWriteBarrier<n>`, if the memory injects `runLoc`'s memory `mm` (distinct keys, the live
blocks away from the frame), the hook returns to `X30` with `SP`, the memory and every register but
`X25` and `X27` kept, and an extension of `ι` that still puts Phase 1's blocks at their addresses
maps the buffer block `wbuf` to `X25` and injects `mm` with a fresh `8n`-byte buffer
(`Mem.wbAlloc`), the live blocks again away from the frame. -/
def WbSpec (H : Hooks) (E : MatchEnv) (n : Nat) (mm : Mem) (m : MState) : Prop :=
  MemInj E.ι mm m.mem → KeysNodup mm → SepFrom E.ι (StkAt E) mm →
  ∃ ι' m', H.call m = some (.ret m') ∧ (∀ b a, E.ι b = some a → ι' b = some a) ∧
    AddrAgree ι' ∧ m'.pc = m.x 30 ∧ m'.sp = m.sp ∧
    (∀ k : Reg, k ≠ 25 → k ≠ 27 → m'.x k = m.x k) ∧ m'.mem = m.mem ∧
    ι' .wbuf = some (m'.x 25) ∧ MemInj ι' (mm.wbAlloc n) m'.mem ∧ KeysNodup (mm.wbAlloc n) ∧
    SepFrom ι' (StkAt E) (mm.wbAlloc n)

/-- The write-barrier contract (`WbSpec`) at the request `v` from `s`, at every machine state at
the symbol of `runtime.gcWriteBarrier<n>` that is `m` but for `X30`. -/
def WbOK (H : Hooks) (E : MatchEnv) (g : G2In) (L : Link) (lc : LocCtx) (s : LocState)
    (v : Value) (m : MState) : Prop :=
  v.op = .ARM64LoweredWB → ∀ y mm (m₁ : MState), g.syms[y]? = some (wbSym v.auxInt.toInt) →
    s.mem = .mem mm → m₁.pc = L.sym y → m₁.sp = m.sp → m₁.v = m.v → m₁.nzcv = m.nzcv →
    m₁.mem = m.mem → (∀ k, k ≠ 30 → m₁.x k = m.x k) → WbSpec H E v.auxInt.toInt.toNat mm m₁

/-- The activation of a function `checkG8` accepted: G6's, and a function with a write barrier
has a frame (the `CALL` overwrites `X30`). -/
structure G8Env (lc : LocCtx) (g : G2In) (L : Link) (ps : Array Prog) (ret : BitVec 64)
    (tab : PcTab) (E : MatchEnv) : Prop where
  env : G6Env lc g L ps ret tab E
  wbs : E.framed = false → ∀ id v, lc.ctx.f.value? id = some v → v.op ≠ .ARM64LoweredWB

/-! ## `stepLoc` of a write-barrier request and of its selections -/

section Step

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

theorem wb_noArg0 : Op.ARM64LoweredWB.regInfo.clobbersArg0 = false := by decide

theorem wb_noArg1 : Op.ARM64LoweredWB.regInfo.clobbersArg1 = false := by decide

theorem wb_mask_ne : Op.ARM64LoweredWB.regInfo.clobbers.isEmpty = false := by decide

theorem wb_flags : Op.ARM64LoweredWB.clobberFlags = true := by decide

private theorem wb_keeps64 : ∀ i, i < 64 → Op.ARM64LoweredWB.regInfo.clobbers.hasReg i = false →
    i < 16 ∨ (18 ≤ i ∧ i ≤ 27) ∨ i = 29 ∨ i = 30 ∨ i = 63 := by decide

/-- The registers a write barrier keeps: `R0`–`R15`, `R19`–`R26`, `g`, `R29`, `ZERO`, `SP` and
those past the `F` registers (it clobbers `R16`, `R17`, `R30` and `F0`–`F31`). -/
theorem wb_keeps {i : Nat} (h : Op.ARM64LoweredWB.regInfo.clobbers.hasReg i = false) :
    i < 16 ∨ (18 ≤ i ∧ i ≤ 27) ∨ i = 29 ∨ i = 30 ∨ 63 ≤ i := by
  by_cases hi : i < 64
  · rcases wb_keeps64 i hi h with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by omega))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by omega))))

theorem clobber_wb (hop : v.op = .ARM64LoweredWB) (ht : (lc.temps[v.id]?).join = none) :
    s.clobber lc v =
      { s.clobberMask Op.ARM64LoweredWB.regInfo.clobbers with flags := .poison } := by
  unfold LocState.clobber
  simp only [hop, wb_noArg0, wb_noArg1, ht, wb_flags, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]

/-- A register after a write barrier's clobbers: `poison`, or kept and one it keeps. -/
theorem clobberMask_wb {r : Nat} {x : Val}
    (h : (s.clobberMask Op.ARM64LoweredWB.regInfo.clobbers).regs[r]? = some x) :
    x = .poison ∨
      (s.regs[r]? = some x ∧ (r < 16 ∨ (18 ≤ r ∧ r ≤ 27) ∨ r = 29 ∨ r = 30 ∨ 63 ≤ r)) := by
  simp only [LocState.clobberMask, wb_mask_ne, Bool.false_eq_true, ↓reduceIte,
    Array.getElem?_mapIdx] at h
  cases hr : s.regs[r]? with
  | none => rw [hr] at h; cases h
  | some y =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq] at h
    by_cases hm : Op.ARM64LoweredWB.regInfo.clobbers.hasReg r = true
    · left; rw [if_pos hm] at h; exact h.symm
    · right
      rw [if_neg hm] at h
      exact ⟨by rw [h], wb_keeps (by simpa using hm)⟩

/-- A register after `setReg r x`: `x` at `r`, or the old content (at another register, or at
`ZERO`, which `setReg` does not write). -/
theorem setReg_get {r q : Nat} {x y : Val} (h : (s.setReg r x).regs[q]? = some y) :
    (q = r ∧ y = x) ∨ ((q ≠ r ∨ r = zeroReg) ∧ s.regs[q]? = some y) := by
  simp only [LocState.setReg] at h
  by_cases hq : q = r
  · subst hq
    split at h
    · rename_i hlt
      simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hlt
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hlt.1] at h
      exact Or.inl ⟨rfl, (Option.some.inj h).symm⟩
    · rename_i hlt
      simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_and,
        Decidable.not_not] at hlt
      exact Or.inr ⟨Or.inr (hlt (Array.getElem?_eq_some_iff.1 h).1), h⟩
  · split at h
    · rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm hq)] at h
      exact Or.inr ⟨Or.inl hq, h⟩
    · exact Or.inr ⟨Or.inl hq, h⟩

theorem wbTy_spec {t : Ty} (h : wbTy t = true) : ∃ e, t = .tuple [.ptr e, .mem] := by
  unfold wbTy at h
  split at h
  · exact ⟨_, rfl⟩
  · cases h

theorem wbArg_spec {c : ID} (h : wbArg lc c = true) :
    (lc.ctx.f.value? c).map (·.op) = some .ARM64LoweredWB ∧
      lc.home c = some (.pair (some wbReg) none) ∧ wbTy (lc.ty c) = true := by
  simp only [wbArg, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- `LoweredWB [n] mem`: the op's clobbers, then the buffer pointer in `R25` and the memory with a
fresh buffer (`wbOp`). -/
theorem stepLoc_wb (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .ARM64LoweredWB) {a : ID} (ha : v.args = #[a]) {mm : Mem}
    (hm : s.read lc a = .ok (.mem mm)) {e : Option Nat} (hty : lc.ty v.id = .tuple [.ptr e, .mem])
    (hh : lc.home v.id = some (.pair (some wbReg) none)) (h : stepLoc env lc s v = .ok s') :
    s' = { ({ s.clobberMask Op.ARM64LoweredWB.regInfo.clobbers with flags := .poison } :
        LocState).setReg wbReg (.ptr ⟨.wbuf, 0⟩) with
      mem := .mem (mm.wbAlloc v.auxInt.toInt.toNat) } := by
  obtain ⟨argv, r, hmv, hr, rfl⟩ := stepLoc_ok_eval (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) h
  rw [ha] at hmv
  change ((s.read lc a).bind fun x => Res.ok [x]) = _ at hmv
  rw [hm] at hmv
  cases hmv
  have he : evalOpL true env lc.ctx s.fr v [.mem mm] (lc.ty v.id) =
      .ok (wbOp v.auxInt [.mem mm]) := by
    unfold evalOpL
    rw [hop]
    rfl
  rw [he] at hr
  cases hr
  rw [lmode_retype hl, clobber_wb hop ht]
  unfold LocState.write
  rw [hh, hty]
  rfl

/-- A write-barrier request read from its home `(Rr, -)`: the register at the pointer shape and the
memory. -/
theorem read_wb {c : ID} {r : Nat} {e : Option Nat} (hl : lc.ctx.f.lowered = true)
    (hh : lc.home c = some (.pair (some r) none)) (hty : lc.ty c = .tuple [.ptr e, .mem]) :
    s.read lc c = .ok (.tuple [(s.reg (.ptr e) r).retypeL (.ptr e), s.mem.retypeL .mem]) := by
  have hraw : s.raw lc c = .ok (.tuple [s.reg (.ptr e) r, s.mem]) := by
    unfold LocState.raw
    simp only [hh, hty, Location.regList]
    rfl
  unfold LocState.read
  rw [hraw]
  simp only [lmode_retype hl, hty, retypeL_pair]
  rfl

end Step

/-! ## Registers and classes -/

/-- A Go register a write barrier keeps, other than `R25`, is none of `X25`, `X27`, `X30`. -/
theorem objX?_kept {r : Nat} {k : Reg} (h : objX? r = some k) (hr : r ≠ wbReg)
    (hk : r < 16 ∨ (18 ≤ r ∧ r ≤ 27) ∨ r = 29 ∨ r = 30 ∨ 63 ≤ r) :
    k ≠ 25 ∧ k ≠ 27 ∧ k ≠ 30 := by
  unfold wbReg at hr
  refine ⟨fun he => ?_, objX?_ne27 h, fun he => ?_⟩ <;> subst he <;> unfold objX? at h
  · split at h
    · have := congrArg BitVec.toNat (Option.some.inj h); simp at this; omega
    · split at h
      · have := congrArg BitVec.toNat (Option.some.inj h); simp at this; omega
      · split at h
        · have := congrArg BitVec.toNat (Option.some.inj h); simp at this; omega
        · cases h
  · split at h
    · have := congrArg BitVec.toNat (Option.some.inj h); simp at this; omega
    · split at h
      · have := congrArg BitVec.toNat (Option.some.inj h); simp at this; omega
      · split at h
        · have := congrArg BitVec.toNat (Option.some.inj h); simp at this; omega
        · cases h

/-- A Go register a write barrier keeps is no `F` register. -/
theorem objV?_kept {r : Nat} (hk : r < 16 ∨ (18 ≤ r ∧ r ≤ 27) ∨ r = 29 ∨ r = 30 ∨ 63 ≤ r) :
    objV? r = none := by
  unfold objV?
  split
  · omega
  · rfl

theorem objX?_wbReg : objX? wbReg = some 25 := rfl

/-- The class table follows a write-barrier request (`kStep`): `R25` holds a pointer. -/
theorem kwb_kStep {lc : LocCtx} {K : KMap} {v : Value} {e : Option Nat} (hop : v.op ≠ .Phi)
    (hh : lc.home v.id = some (.pair (some wbReg) none))
    (hty : lc.ty v.id = .tuple [.ptr e, .mem]) :
    KLe (kStep lc K v).get (kSet K.get wbReg (some 64)) := by
  intro r c _ hc
  rw [kStep_get] at hc
  simp only [hop, ↓reduceIte, hh, hty, tupleTys, List.zip_cons_cons, List.zip_nil_right] at hc
  have hnd : ([(Ty.ptr e, some wbReg), (Ty.mem, (none : Option Nat))].filterMap (·.2)).Nodup := by
    simp
  unfold kSet
  by_cases hr : r = wbReg
  · subst hr
    simp only [↓reduceIte]
    by_cases hsz : wbReg < K.size
    · rw [kResults_get_of_mem (t := .ptr e) hnd (by simp) hsz] at hc; exact hc
    · rw [KMap.get_ge (by rw [kResults_size]; omega)] at hc; cases hc
  · simp only [hr, ↓reduceIte]
    rw [kResults_get_of_not_mem (by simp [hr])] at hc
    exact hc

/-- `R25`, which a `Select0` of a write-barrier request reads (`kReads`), holds a pointer. -/
theorem ksel8_of_reads {lc : LocCtx} {v : Value} {K : KMap} {c : ID}
    (h : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2) (hop : v.op = .Select0)
    (hc0 : v.args[0]? = some c) (hw : wbArg lc c = true) : K.get wbReg = some 64 := by
  obtain ⟨-, hhc, hty⟩ := wbArg_spec hw
  obtain ⟨e, hte⟩ := wbTy_spec hty
  apply h (wbReg, 64)
  simp [kReads, hop, hc0, hhc, hte, tupleTys, Gen.Check.cls]

/-! ## One value of G8's own kinds -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {g : G2In} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- A write-barrier request: `CALL runtime.gcWriteBarrier<n>(SB)` with the return address in
`X30`, the hook by the trusted contract (`WbOK`): the buffer pointer in `R25`, the memory with the
fresh buffer. The injection grows by the buffer. -/
theorem g8_wb (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E) (hlc : E.lc = lc)
    (hcf : checkFrame lc g = .ok ()) (hframed : E.framed = true)
    (hsyms : ∀ y, (Link.byId sym text az ez psA.toList).sym y ≠ ret ∧ ∀ p ∈ psA.toList,
      (Link.byId sym text az ez psA.toList).addr p.id ≠
        some ((Link.byId sym text az ez psA.toList).sym y))
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hK : KLe K' (kSet K wbReg (some 64)))
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    (hop : v.op = .ARM64LoweredWB) (hsz1 : v.args.size = 1)
    (hh : lc.home v.id = some (.pair (some wbReg) none)) (hty : wbTy (lc.ty v.id) = true)
    (hma : memArg lc v 0 = .ok ()) (hvs : OneAt2 psA j (wbPat g v.auxInt.toInt) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s')
    (hok : WbOK H E g (Link.byId sym text az ez psA.toList) lc s v m) :
    ∃ ι', (∀ b a, E.ι b = some a → ι' b = some a) ∧ AddrAgree ι' ∧ ∃ m',
      PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch { E with ι := ι' } s' b (i + 1) m' ∧
      CoreInv ι' (StkAt { E with ι := ι' }) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  obtain ⟨e, hte⟩ := wbTy_spec hty
  obtain ⟨a0, ha0, hamt, hah0⟩ := memArg_spec hma
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨mm0, hmm0, hkn, hsep⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  have hs' := stepLoc_wb hl htemp hop (arr1 hsz1 ha0) (read_mem hl hah0 hamt hmm) hte hh hs
  -- the machine: no-ops, then the `CALL`
  obtain ⟨k, rfl, hk, hokp, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
  rw [pc_eta hm hj] at hstar
  obtain ⟨has, -, -, -, -, -, ht1, ht2, ht3, y, hy1, hy⟩ := wbPat_spec hokp
  let m₁ : MState :=
    { m with x := (fun q => if q = 30 then pcAt text psA.toList (k + 1) else m.x q),
             pc := (Link.byId sym text az ez psA.toList).sym y }
  have hm1x : ∀ q, q ≠ 30 → m₁.x q = m.x q := fun q hq => by
    show (if q = 30 then _ else m.x q) = m.x q
    exact ite_eq_right_iff.2 fun h => absurd h hq
  have hcstep : progStep (Link.byId sym text az ez psA.toList) psA.toList[k]
      { m with pc := pcAt text psA.toList k } = .ok m₁ := by
    rw [progStep_callSym (nextAddr_pcAt F.nodup hk) has ht1 ht2 ht3 hy1, wX_pc]
    simp only [MState.wX, show ¬ ((30 : Reg) = 31) by decide, ↓reduceIte]
    rfl
  obtain ⟨ι', m', hcallH, hext, hA', hpc', hsp', hx', hmem', hbuf, hMI', hkn', hsep'⟩ :=
    hok hop y mm m₁ hy hmm rfl rfl rfl rfl rfl hm1x hMI hkn hsep
  have hstep2 : PStep H (Link.byId sym text az ez psA.toList) psA.toList ret m₁ m' :=
    .hook (hsyms y).1 (progAt?_none (hsyms y).2) hcallH
  have hstar' := (hstar.tail (pstep_at F.nodup F.lt F.ret hk rfl hcstep)).tail hstep2
  -- `runLoc`'s state after the request
  have hsl' : s'.slots = s.slots := by
    rw [hs']
    simp [LocState.setReg, LocState.clobberMask, wb_mask_ne]
  have hreg : ∀ r x, s'.regs[r]? = some x →
      (r = wbReg ∧ x = .ptr ⟨.wbuf, 0⟩) ∨ x = .poison ∨
        (s.regs[r]? = some x ∧ r ≠ wbReg ∧
          (r < 16 ∨ (18 ≤ r ∧ r ≤ 27) ∨ r = 29 ∨ r = 30 ∨ 63 ≤ r)) := by
    intro r x h
    rw [hs'] at h
    rcases setReg_get h with ⟨rfl, rfl⟩ | ⟨hne, h2⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · have hne' : r ≠ wbReg := by
        rcases hne with hne | hne
        · exact hne
        · exact absurd hne (by decide)
      rcases clobberMask_wb h2 with rfl | ⟨h3, hk3⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨h3, hne', hk3⟩)
  -- the frame and the slots under the larger injection
  obtain ⟨hslots', hframe'⟩ := stk_slots_frame (E' := { E with ι := ι' }) (m' := m') hm hF
    (slot_sizes hlc hcf hsi) rfl hext (fun q _ => by rw [hmem']) hsp'
    ((hx' 28 (by decide) (by decide)).trans (hm1x 28 (by decide)))
    ((hx' 29 (by decide) (by decide)).trans (hm1x 29 (by decide)))
    (fun hf => by rw [hframed] at hf; cases hf)
  refine ⟨ι', hext, hA', m', hstar', ⟨fun r x h => ?_, by rw [hs']; exact trivial,
    by rw [hsl']; exact hslots', ⟨_, by rw [hs'], hMI'⟩, hframe', ?_⟩,
    ⟨fun r x c hrz h hc => ?_, _, by rw [hs'], hkn', hsep'⟩, fun k v hk => hsi k v (hsl' ▸ hk)⟩
  · rcases hreg r x h with ⟨rfl, rfl⟩ | rfl | ⟨h2, hne, hk2⟩
    · refine ⟨fun q hq => ?_, fun q hq => by rw [objV?_kept (by decide)] at hq; cases hq⟩
      obtain rfl := Option.some.inj (objX?_wbReg.symm.trans hq)
      exact (⟨m'.x 25, hbuf, by simp⟩ : PtrRel ι' ⟨.wbuf, 0⟩ (m'.x 25))
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
    · obtain ⟨hx1, -⟩ := hm.regs r x h2
      refine ⟨fun q hq => ?_, fun q hq => by rw [objV?_kept hk2] at hq; cases hq⟩
      obtain ⟨h25, h27, h30⟩ := objX?_kept hq hne hk2
      rw [hx' q h25 h27, hm1x q h30]
      exact valRel_mono hext (hx1 q hq)
  · show m'.pc = E.pcOf b (i + 1)
    rw [hpc', hj']
    simp [m₁]
  · have hc' := hK r c hrz hc
    rcases hreg r x h with ⟨rfl, rfl⟩ | rfl | ⟨h2, hne, -⟩
    · simp only [kSet, ↓reduceIte, Option.some.injEq] at hc'
      subst hc'
      exact (rfl : (64 : Nat) = 64)
    · trivial
    · simp only [kSet, hne, ↓reduceIte] at hc'
      exact hinv.regs r x c hrz h2 hc'

/-- `Select0` of a write-barrier request, homed in `R25` like the request's pointer: no code;
`R25` is reread at the value's shape. -/
theorem g8_sel0 (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {c : ID} (hop : v.op = .Select0) (hsz1 : v.args.size = 1) (hc0 : v.args[0]? = some c)
    (hw : wbArg lc c = true) (hvh : lc.home v.id = some (.reg wbReg))
    (hcv : cls (lc.ty v.id) = some 64) (hKr : K wbReg = some 64)
    (hvs : j' = j) (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  obtain ⟨-, hhc, hty⟩ := wbArg_spec hw
  obtain ⟨e, hte⟩ := wbTy_spec hty
  obtain ⟨x, hx, rfl⟩ := stepLoc_select hl htemp (Or.inl ⟨hop, rfl⟩) (arr1 hsz1 hc0) hs
  rw [read_wb hl hhc hte] at hx
  cases hx
  have hsel : Tuple.select 0
      [.tuple [(s.reg (.ptr e) wbReg).retypeL (.ptr e), s.mem.retypeL .mem]] =
      (s.reg (.ptr e) wbReg).retypeL (.ptr e) := rfl
  rw [hsel, write_reg hvh hcv]
  have hrel : ValRel E.ι (((s.reg (.ptr e) wbReg).retypeL (.ptr e)).retypeL (lc.ty v.id))
      (m.rX (BitVec.ofNat 5 25)) := by
    rw [rX_lt (by decide)]
    simp only [LocState.reg, show (wbReg == zeroReg) = false by decide, Bool.false_eq_true,
      ↓reduceIte]
    cases hv : s.regs[wbReg]? with
    | none => simp only [Option.getD_none, retypeL_poison]; trivial
    | some raw =>
      simp only [Option.getD_some]
      have hfit := hinv.regs wbReg raw 64 (by decide) hv hKr
      have h1' := valRel_retypeL hA (rfl : cls (Ty.ptr e) = some 64) hfit
        ((hm.regs wbReg raw hv).1 _ objX?_wbReg)
      exact valRel_retypeL hA hcv (fits_retypeL rfl _) h1'
  obtain ⟨hlm, hinv'⟩ := finish_reg hm hinv (by decide : destOK wbReg = true)
    (by decide : 25 < 32) (by decide : objOf? wbReg = some (ARM64.REG_R0 + 25)) hrel
    (fits_retypeL hcv _) (b' := b) (i' := i + 1)
  rw [wX_rX_self, hj', hvs, ← hj, ← hm.pc] at hlm
  exact ⟨m, .refl, hlm, hinv'.mono (knext_set hK (by rw [hop]; nofun) hvh hcv), hsi⟩

/-- `Select1` of a write-barrier request, the memory with no home: no code, no change. -/
theorem g8_sel1 (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {c : ID} (hop : v.op = .Select1) (hsz1 : v.args.size = 1) (hc0 : v.args[0]? = some c)
    (hw : wbArg lc c = true) (hmt : memTy (lc.ty v.id) = true) (hhn : lc.home v.id = none)
    (hvs : j' = j) (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  obtain ⟨-, hhc, hty⟩ := wbArg_spec hw
  obtain ⟨e, hte⟩ := wbTy_spec hty
  obtain ⟨x, hx, rfl⟩ := stepLoc_select hl htemp (Or.inr ⟨hop, rfl⟩) (arr1 hsz1 hc0) hs
  rw [read_wb hl hhc hte] at hx
  cases hx
  obtain ⟨mm, hmm, -⟩ := hm.mem
  have ht' : lc.ty v.id = .mem := by cases h : lc.ty v.id <;> simp_all [memTy]
  have hmem : (s.mem.retypeL .mem).retypeL .mem = s.mem := by rw [hmm]; rfl
  have hs' : s.write lc v.id ((Tuple.select 1
      [.tuple [(s.reg (.ptr e) wbReg).retypeL (.ptr e), s.mem.retypeL .mem]]).retypeL
        (lc.ty v.id)) = s := by
    unfold LocState.write
    rw [hhn, ht']
    show { s with mem := (s.mem.retypeL .mem).retypeL .mem } = s
    rw [hmem]
  rw [hs']
  obtain ⟨m', h1, h2, h3, -⟩ := op_none (H := H) (sym := sym) (text := text) (az := az) (ez := ez)
    (psA := psA) (ret := ret) hm hinv rfl (by rw [hj', hvs, hj])
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun))
  exact ⟨m', h1, h2, h3, hsi⟩

end Cases

/-! ## The theorems -/

/-- `G8Env` under an activation that extends the injection. -/
theorem G8Env.extend {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog} {ret : BitVec 64}
    {tab : PcTab} {E E' : MatchEnv} (hE : G8Env lc g L ps ret tab E) (hx : E.Extends E')
    (hE' : G2Env lc g L ps ret tab E') : G8Env lc g L ps ret tab E' where
  env := ⟨hE', hE.env.vars.extend hx⟩
  wbs := fun hf => hE.wbs (by rw [hx.1] at hf; exact hf)

/-- One value of G8's kinds (`VK8`) emitted at the Progs from `j` to `j'`: `vk7_step`'s statement
for G8's values under `G8Env`, with the write-barrier contract `WbOK`. -/
theorem vk8_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2}
    (hE : G8Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hns : CallsNotSlot lc)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK8 lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s) (hpre : G7Pre lc s v)
    (hcall : CallOK H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hwb : WbOK H E g (Link.byId sym text az ez ps.toList) lc s v m)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G8Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' := by
  have hE8 := hE
  obtain ⟨⟨hE2, hvars⟩, hwbs⟩ := hE
  have hE0 := hE2
  obtain ⟨hlcE, -, -, -, -, -, hsyms, -, -, -, hF⟩ := hE2
  have same : ∀ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E s' bid (i + 1) m' ∧ CoreInv E.ι (StkAt E) (kStep lc K v).get s' ∧
      SlotInv lc s' →
      ∃ E' m', E.Extends E' ∧ G8Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
        PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
        LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' :=
    fun m' ⟨h1, h2, h3, h4⟩ => ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE8, h1, h2, ⟨h3, h4⟩⟩
  cases hVK with
  | g7 hVK7 =>
    obtain ⟨E', m', hx, hE', h⟩ :=
      vk7_step ⟨hE0, hvars⟩ F hns hcf hv hVK7 hvs htemp hj hj' hreads hm hinv hpre hcall hs
    exact ⟨E', m', hx, hE8.extend hx hE'.env, h⟩
  | wb hop _ _ hsz1 hh hty hma =>
    have hframed : E.framed = true := by
      cases hfr : E.framed
      · exact absurd hop (hwbs hfr id v hv)
      · rfl
    obtain ⟨e, hte⟩ := wbTy_spec hty
    obtain ⟨ι', hext', hA', m', hstar, hlm, hcore', hsl'⟩ := g8_wb (H := H) F hF hlcE hcf hframed
      hsyms hm hinv.core hinv.slots (kwb_kStep (by rw [hop]; nofun) hh hte) hj hj' hop hsz1 hh hty
      hma hvs htemp hs hwb
    exact ⟨_, m', ⟨rfl, hext'⟩, hE8.extend ⟨rfl, hext'⟩ (hE0.extend hext' hA'), hstar, hlm,
      ⟨hcore', hsl'⟩⟩
  | sel0 hop hsz1 hc0 hw hvh hcv =>
    obtain ⟨m', h⟩ := g8_sel0 (H := H) F hm hinv.core hinv.slots
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz1 hc0 hw hvh hcv
      (ksel8_of_reads hreads hop hc0 hw) hvs htemp hs
    exact same m' h
  | sel1 hop hsz1 hc0 hw hmt hhn =>
    obtain ⟨m', h⟩ := g8_sel1 (H := H) F hm hinv.core hinv.slots
      (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hop hsz1 hc0 hw hmt hhn hvs htemp hs
    exact same m' h

/-- **G8, values.** `g7_value`'s statement over `checkG8`, under `G8Env`, with the trusted
write-barrier contract `WbOK` next to `CallOK`: a value (not an entry value) of an accepted
function run by `runLoc` is matched by `runProg` steps of genssa's P0 Progs to a state related
before the next value, with the registers at the classes before the next value, under an activation
that extends `E`'s injection (by the callee's at a call, by the buffer at a write barrier) and is
again a `G8Env`. -/
theorem g8_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG8 lc ps bstart g = .ok (tab, kt)) (hE : G8Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp3 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hpre : G7Pre lc s v)
    (hcall : CallOK H E g L lc s s' v m) (hwb : WbOK H E g L lc s v m)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G8Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' := by
  have hE0 := hE
  obtain ⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome4, hcf, hk, hlt, hnd, hblocks⟩ := checkG8_spec hc
  obtain ⟨b, j, js, e, next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk] at hkd
  obtain ⟨htemp, hVK⟩ := vkind8_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home4 hhome4, hnd, hlt, hret, hA⟩
  rw [kAt_succ hi hv]
  exact vk8_step hE0 F (call_not_slot4 hhome4) hcf hv hVK hvs htemp hj hj' hreads hm hinv hpre
    hcall hwb hs

/-- **G8, nil panics.** `g7_nilPanic`'s statement over `checkG8`. -/
theorem g8_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState} {m : MState}
    {e : Panic} {mm' : Mem}
    (hc : checkG8 lc ps bstart g = .ok (tab, kt)) (hE : G8Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  obtain ⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome4, -, hk, hlt, hnd, hblocks⟩ := checkG8_spec hc
  obtain ⟨b, j, js, e', next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk] at hkd
  obtain ⟨-, hVK⟩ := vkind8_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home4 hhome4, hnd, hlt, hret, hA⟩
  cases hVK with
  | g7 hVK7 =>
    cases hVK7 with
    | g6 hne _ => exact absurd hop hne
    | nil _ hsz2 _ _ hao hma =>
      exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma hvs hs
  | wb hop' => rw [hop] at hop'; cases hop'
  | sel0 hop' => rw [hop] at hop'; cases hop'
  | sel1 hop' => rw [hop] at hop'; cases hop'

/-- **G8, terminators.** `g7_term`'s statement over `checkG8`, under `G8Env`. -/
theorem g8_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG8 lc ps bstart g = .ok (tab, kt)) (hE : G8Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList := by
  obtain ⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome4, -, hk, hlt, hnd, hblocks⟩ := checkG8_spec hc
  exact termK_step hpcOf ⟨hl, clsReg_of_home4 hhome4, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb
    hm hinv hpre ht

end GoFV.Proof.Gen

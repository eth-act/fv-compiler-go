import GoFV.Proof.Gen.G53a
import GoFV.Proof.Gen.Spec54a

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G54: the machine's loops (`docs/plans/proofs3.md` §4)

The Progs of `LoweredZeroLoop`/`LoweredMoveLoop` (`GoFV/Gen/Check54a.lean`) under `runProg`: the
post-indexed `STP.P (ZR, ZR), 16(Rn)` (`progStep_stpP`), `FLDPQ.P 32(Rn), (F16, F17)`
(`progStep_fldpqP`) and `FSTPQ.P (F16, F17), 32(Rn)` (`progStep_fstpqP`), each writing its base
register advanced; the counter's `MOVD $k, Rc` and `SUB $1, Rc` (`progStep_subOne`); the
`CBNZ Rc` back to the head (`count_run`: `SUB`, then `CBNZ` to the head while the counter is not
zero, else on). `loop_run` runs a loop to its exit by induction on the iterations left, from a
per-iteration step that keeps an invariant. `Keeps54 xs vs m m'`: `m'` is `m` but for the X
registers `xs`, the V registers `vs`, the memory and the PC.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## Unchanged registers -/

/-- `m'` is `m` but for the X registers `xs`, the V registers `vs`, the memory and the PC. -/
def Keeps54 (xs vs : List Reg) (m m' : MState) : Prop :=
  m'.sp = m.sp ∧ m'.nzcv = m.nzcv ∧ (∀ q, q ∉ xs → m'.x q = m.x q) ∧
    ∀ q, q ∉ vs → m'.v q = m.v q

theorem Keeps54.refl {xs vs : List Reg} (m : MState) : Keeps54 xs vs m m :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem Keeps54.trans {xs vs : List Reg} {m m' m'' : MState} (h : Keeps54 xs vs m m')
    (h' : Keeps54 xs vs m' m'') : Keeps54 xs vs m m'' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, fun q hq => (h'.2.2.1 q hq).trans (h.2.2.1 q hq),
    fun q hq => (h'.2.2.2 q hq).trans (h.2.2.2 q hq)⟩

theorem Keeps54.mono {xs vs xs' vs' : List Reg} {m m' : MState} (h : Keeps54 xs vs m m')
    (hx : ∀ q ∈ xs, q ∈ xs') (hv : ∀ q ∈ vs, q ∈ vs') : Keeps54 xs' vs' m m' :=
  ⟨h.1, h.2.1, fun q hq => h.2.2.1 q (fun h' => hq (hx q h')),
    fun q hq => h.2.2.2 q (fun h' => hq (hv q h'))⟩

/-- Writing an X register of `xs` keeps the others. -/
theorem keeps54_wX {xs vs : List Reg} {m : MState} {r : Reg} {val : BitVec 64} (hr : r ∈ xs) :
    Keeps54 xs vs m (m.wX r val) := by
  obtain ⟨hmem, hsp, hnz, hv⟩ := wX_fields (m := m) (r := r) (val := val)
  exact ⟨hsp, hnz, fun q hq => wX_x_of_ne (fun (h : q = r) => hq (h ▸ hr)), fun q _ => by rw [hv]⟩

/-- Writing a V register of `vs` keeps the others. -/
theorem keeps54_wV {xs vs : List Reg} {m : MState} {r : Reg} {val : BitVec 128} (hr : r ∈ vs) :
    Keeps54 xs vs m (m.wV r val) :=
  ⟨rfl, rfl, fun _ _ => rfl, fun q hq => by
    show (if q = r then val else m.v q) = m.v q
    rw [if_neg (fun (h : q = r) => hq (h ▸ hr))]⟩

theorem keeps54_pc {xs vs : List Reg} {m m' : MState} (h : Keeps54 xs vs m m') (pc : BitVec 64) :
    Keeps54 xs vs m { m' with pc } := h

theorem keeps54_mem {xs vs : List Reg} {m m' : MState} (h : Keeps54 xs vs m m') (M : Memory) :
    Keeps54 xs vs m { m' with mem := M } := h

theorem wX_x_self54 {m : MState} {k : Nat} (hk : k < 31) {val : BitVec 64} :
    (m.wX (BitVec.ofNat 5 k) val).x (BitVec.ofNat 5 k) = val := by
  have h31 : (BitVec.ofNat 5 k : Reg) ≠ 31 := by
    intro h; have := congrArg BitVec.toNat h; simp at this; omega
  unfold MState.wX
  rw [if_neg h31]
  simp

theorem rX_of_lt {m : MState} {k : Nat} (hk : k < 31) :
    m.rX (BitVec.ofNat 5 k) = m.x (BitVec.ofNat 5 k) := rX_lt hk

/-! ## Operands and steps -/

/-- A post-indexed memory operand off `X kn`: the address `X kn`, then `X kn + off` written back. -/
theorem ctx_mem_post {c : ProgCtx} {kn : Nat} {off : Int} (hkn : kn < 32)
    (hsc : c.p.scond = C_XPOST.toNat) :
    c.mem (memA (REG_R0 + kn) off) = .ok (c.s.rX (BitVec.ofNat 5 kn),
      some (REG_R0 + kn, c.s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off)) := by
  simp (config := { decide := true }) only [ProgCtx.mem, memA, ctx_x_r0 hkn, hsc, C_XPRE,
    C_XPOST]
  rfl

private theorem ctx_zr {c : ProgCtx} : c.x zrA = .ok 0 := by
  have := ctx_x_r0 (c := c) (k := 31) (by decide)
  rw [rX_31] at this
  exact this

private theorem ok_bind54 {α β : Type} (a : α) (f : α → Except String β) :
    (Except.ok a >>= f) = f a := rfl

private theorem eff_stpP {c : ProgCtx} {kn : Nat} {A : BitVec 64} (hkn : kn < 31)
    (has : c.p.as = .STP) (hf : c.p.from_ = pairA zrA zrA)
    (hma : c.mem c.p.to = .ok (A, some (REG_R0 + kn, A + BitVec.ofInt 64 16))) :
    progEffect c = .ok
      { x := [(kn, A + BitVec.ofInt 64 16)],
        stores := [(A, 8, (0 : BitVec 64).toNat % 2 ^ (8 * 8)),
          (A + BitVec.ofNat 64 8, 8, (0 : BitVec 64).toNat % 2 ^ (8 * 8))] } := by
  have hname : As.name .STP = "STP" := rfl
  unfold progEffect
  simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
    ProgOp.movMem, ProgOp.pairOp, hf, pairA, hma, ok_bind54, eff_wX_r0 hkn, ctx_zr]
  rfl

private theorem eff_fldpqP {c : ProgCtx} {kn : Nat} {A : BitVec 64} (hkn : kn < 31)
    (has : c.p.as = .FLDPQ)
    (hma : c.mem c.p.from_ = .ok (A, some (REG_R0 + kn, A + BitVec.ofInt 64 32)))
    (ht : c.p.to = pairA f16A f17A) :
    progEffect c = .ok
      { x := [(kn, A + BitVec.ofInt 64 32)],
        v := [(17, (readMem c.s.mem (A + BitVec.ofNat 64 16) 16).setWidth 128),
              (16, (readMem c.s.mem A 16).setWidth 128)],
        loads := [(A + BitVec.ofNat 64 16, 16), (A, 16)] } := by
  have hname : As.name .FLDPQ = "FLDPQ" := rfl
  unfold progEffect
  simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
    ProgOp.movMem, ProgOp.pairOp, ht, pairA, hma, ok_bind54, Eff.ld, eff_wX_r0 hkn, eff_wV16,
    eff_wV17]

private theorem eff_fstpqP {c : ProgCtx} {kn : Nat} {A : BitVec 64} (hkn : kn < 31)
    (has : c.p.as = .FSTPQ) (hf : c.p.from_ = pairA f16A f17A)
    (hma : c.mem c.p.to = .ok (A, some (REG_R0 + kn, A + BitVec.ofInt 64 32))) :
    progEffect c = .ok
      { x := [(kn, A + BitVec.ofInt 64 32)],
        stores := [(A, 16, (c.s.v (BitVec.ofNat 5 16)).toNat % 2 ^ (8 * 16)),
          (A + BitVec.ofNat 64 16, 16, (c.s.v (BitVec.ofNat 5 17)).toNat % 2 ^ (8 * 16))] } := by
  have hname : As.name .FSTPQ = "FSTPQ" := rfl
  unfold progEffect
  simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
    ProgOp.movMem, ProgOp.pairOp, hf, pairA, hma, ok_bind54, eff_wX_r0 hkn, ctx_v16, ctx_v17]
  rfl

private theorem ofInt_lit (k : Nat) : BitVec.ofInt 64 (k : Int) = BitVec.ofNat 64 k := ofInt_nat k

section Steps

variable {L : Link} {p : Prog} {s : MState} {next : BitVec 64}

/-- `STP.P (ZR, ZR), 16(Rn)`, both addresses outside the nil page: 16 zero bytes at `X kn`, which
advances by 16. -/
theorem progStep_stpP {kn : Nat} (hkn : kn < 31) (hn : L.nextAddr p.id = some next)
    (hok : (stpPPat (REG_R0 + kn)).ok p = true)
    (hnil : nilPage (s.rX (BitVec.ofNat 5 kn)) = false)
    (hnil8 : nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofNat 64 8) = false) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kn) (s.rX (BitVec.ofNat 5 kn) + BitVec.ofNat 64 16)
      with mem := zeroStore (s.rX (BitVec.ofNat 5 kn)) s.mem (true, 0), pc := next } := by
  simp only [stpPPat, Shape.okP, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨has, hf⟩, -⟩, ht⟩, hsc⟩, -⟩, -⟩ := hok
  have hma := ctx_mem_post (c := ⟨L, s, p⟩) (kn := kn) (off := 16) (by omega) hsc
  rw [← ht] at hma
  have he := eff_stpP (c := ⟨L, s, p⟩) hkn has hf hma
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
    (by simp [Eff.nilAccess?, List.find?, hnil, hnil8])]
  have hw := (wX_fields (m := s) (r := BitVec.ofNat 5 kn)
    (val := s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 16)).1
  simp only [Eff.apply, List.foldr, List.foldl, Option.getD, hw, zeroStore, ↓reduceIte,
    ofInt_lit 16]
  have h0 : s.rX (BitVec.ofNat 5 kn) + BitVec.ofNat 64 0 = s.rX (BitVec.ofNat 5 kn) := by simp
  rw [h0]
  rfl

/-- `FLDPQ.P 32(Rn), (F16, F17)`, both addresses outside the nil page: the 16 bytes at `X kn` into
`V16`, the 16 above into `V17`; `X kn` advances by 32. -/
theorem progStep_fldpqP {kn : Nat} (hkn : kn < 31) (hn : L.nextAddr p.id = some next)
    (hok : (fldpqPPat (REG_R0 + kn)).ok p = true)
    (hnil : nilPage (s.rX (BitVec.ofNat 5 kn)) = false)
    (hnil16 : nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofNat 64 16) = false) :
    progStep L p s = .ok { ((s.wX (BitVec.ofNat 5 kn)
        (s.rX (BitVec.ofNat 5 kn) + BitVec.ofNat 64 32)).wV (BitVec.ofNat 5 16)
        ((readMem s.mem (s.rX (BitVec.ofNat 5 kn)) 16).setWidth 128)).wV (BitVec.ofNat 5 17)
        ((readMem s.mem (s.rX (BitVec.ofNat 5 kn) + BitVec.ofNat 64 16) 16).setWidth 128) with
      pc := next } := by
  simp only [fldpqPPat, Shape.okP, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨has, hf⟩, -⟩, ht⟩, hsc⟩, -⟩, -⟩ := hok
  have hma := ctx_mem_post (c := ⟨L, s, p⟩) (kn := kn) (off := 32) (by omega) hsc
  rw [← hf] at hma
  have he := eff_fldpqP (c := ⟨L, s, p⟩) hkn has hma ht
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
    (by simp [Eff.nilAccess?, List.find?, hnil, hnil16])]
  simp only [Eff.apply, List.foldr, Option.getD, ofInt_lit 32]
  rfl

/-- `FSTPQ.P (F16, F17), 32(Rn)`, both addresses outside the nil page: `V16`'s 16 bytes at `X kn`,
then `V17`'s; `X kn` advances by 32. -/
theorem progStep_fstpqP {kn : Nat} (hkn : kn < 31) (hn : L.nextAddr p.id = some next)
    (hok : (fstpqPPat (REG_R0 + kn)).ok p = true)
    (hnil : nilPage (s.rX (BitVec.ofNat 5 kn)) = false)
    (hnil16 : nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofNat 64 16) = false) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kn) (s.rX (BitVec.ofNat 5 kn) + BitVec.ofNat 64 32)
      with
      mem := writeMem (writeMem s.mem (s.rX (BitVec.ofNat 5 kn)) 16
          (BitVec.ofNat (8 * 16) ((s.v (BitVec.ofNat 5 16)).toNat % 2 ^ (8 * 16))))
        (s.rX (BitVec.ofNat 5 kn) + BitVec.ofNat 64 16) 16
          (BitVec.ofNat (8 * 16) ((s.v (BitVec.ofNat 5 17)).toNat % 2 ^ (8 * 16))),
      pc := next } := by
  simp only [fstpqPPat, Shape.okP, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨has, hf⟩, -⟩, ht⟩, hsc⟩, -⟩, -⟩ := hok
  have hma := ctx_mem_post (c := ⟨L, s, p⟩) (kn := kn) (off := 32) (by omega) hsc
  rw [← ht] at hma
  have he := eff_fstpqP (c := ⟨L, s, p⟩) hkn has hf hma
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
    (by simp [Eff.nilAccess?, List.find?, hnil, hnil16])]
  have hw := (wX_fields (m := s) (r := BitVec.ofNat 5 kn)
    (val := s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 32)).1
  simp only [Eff.apply, List.foldr, List.foldl, Option.getD, hw, ofInt_lit 32]
  rfl

/-- `SUB $1, Rc` (`Rc` also the first operand): `X kc` decremented. -/
theorem progStep_subOne {kc : Nat} (hkc : kc < 32) (hn : L.nextAddr p.id = some next)
    (hok : (Pat.ofShape { as := .SUB, from_ := constA 1, to := regA (REG_R0 + kc) }).ok p = true) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kc) (s.rX (BitVec.ofNat 5 kc) - 1) with
      pc := next } := by
  obtain ⟨has, hf, hr, ht, -⟩ := Shape.ok_eq hok
  have hrn : ProgCtx.rn ⟨L, s, p⟩ = REG_R0 + kc := by
    simp [ProgCtx.rn, hr, ht, regA]
  have hname : As.name .SUB = "SUB" := rfl
  have he : progEffect ⟨L, s, p⟩ =
      .ok (effWd {} kc (s.rX (BitVec.ofNat 5 kc) - BitVec.ofInt 64 1)) := by
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, hf, ht, hrn, regA, constA,
      ProgOp.baseOf, ↓reduceIte, ProgOp.binNames, ctx_src_reg hkc, ctx_src_const, ProgOp.binOp,
      addSub_sub]
    simp only [eff_wX_dest hkc]
    by_cases h : kc = 31 <;> simp [effWd, h] <;> rfl
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
    (by by_cases h : kc = 31 <;> simp [effWd, h, Eff.nilAccess?]), wd_apply hkc]
  rfl

end Steps

/-! ## Runs -/

section Run

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64}

/-- One Prog matching `pat` after no-ops, whose step from any state `m` at its address is `m'` at
the next address: the machine reaches `m'` with the PC at `j'`. -/
theorem pstar_one54 (hnd : (psA.toList.map (·.id)).Nodup) (hlt : ∀ p ∈ psA.toList, p.id < 2 ^ 32)
    (hret : ∀ p ∈ psA.toList, (Link.byId sym text az ez psA.toList).addr p.id ≠ some ret)
    {j j' : Nat} {pat : Pat} (h : OneAt2 psA j pat j') (m m' : MState)
    (hf : ∀ k (hk : k < psA.toList.length), pat.ok psA.toList[k] = true →
      progStep (Link.byId sym text az ez psA.toList) psA.toList[k]
        { m with pc := pcAt text psA.toList k } = .ok { m' with pc := pcAt text psA.toList (k + 1) }) :
    PStar H (Link.byId sym text az ez psA.toList) psA.toList ret
      { m with pc := pcAt text psA.toList j } { m' with pc := pcAt text psA.toList j' } := by
  obtain ⟨k, rfl, hk, hok, hst⟩ := pstar_oneAt2 (H := H) hnd hlt hret h m
  exact hst.tail (pstep_at hnd hlt hret hk rfl (hf k hk hok))

/-- The counter's `SUB $1, Rc` then `CBNZ Rc` whose target is the Prog at `k1`: `X kc` is `c - 1`,
and the machine is at the head `k1` unless it is 0, else after the `CBNZ`. -/
theorem count_run (hnd : (psA.toList.map (·.id)).Nodup) (hlt : ∀ p ∈ psA.toList, p.id < 2 ^ 32)
    (hret : ∀ p ∈ psA.toList, (Link.byId sym text az ez psA.toList).addr p.id ≠ some ret)
    {kc : Nat} (hkc : kc < 31) {kb ks ke k1 : Nat}
    (hsub : OneAt2 psA kb (.ofShape { as := .SUB, from_ := constA 1, to := regA (REG_R0 + kc) }) ks)
    (hcb : OneAt2 psA ks (cbnzPat (REG_R0 + kc)) ke) (hk1 : k1 < psA.size) (hke : ke - 1 < psA.size)
    (hbr : psA[ke - 1].to = brA psA[k1].id) (m : MState) :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret
        { m with pc := pcAt text psA.toList kb } m' ∧
      m'.x (BitVec.ofNat 5 kc) = m.x (BitVec.ofNat 5 kc) - 1 ∧
      Keeps54 [BitVec.ofNat 5 kc] [] m m' ∧ m'.mem = m.mem ∧
      m'.pc = if m.x (BitVec.ofNat 5 kc) - 1 = 0 then pcAt text psA.toList ke
        else pcAt text psA.toList k1 := by
  have hs1 := pstar_one54 (H := H) hnd hlt hret hsub m
    (m.wX (BitVec.ofNat 5 kc) (m.rX (BitVec.ofNat 5 kc) - 1)) (fun k hk hok => by
      rw [progStep_subOne (by omega) (nextAddr_pcAt hnd hk) hok]
      simp only [wX_pc]
      rfl)
  let m1 := m.wX (BitVec.ofNat 5 kc) (m.rX (BitVec.ofNat 5 kc) - 1)
  obtain ⟨k, rfl, hk, hok, hst⟩ := pstar_oneAt2 (H := H) hnd hlt hret hcb m1
  have hk' : k < psA.size := by simpa using hk
  simp only [cbnzPat, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨has, hf⟩, -⟩, -⟩, -⟩, -⟩ := hok
  have hto : psA.toList[k].to = brA psA.toList[k1].id := by
    simpa using hbr
  have hL := addr_pcAt (sym := sym) (text := text) (az := az) (ez := ez)
    (ps := psA.toList) (j := k1) (by simpa using hk1)
  have hstep := progStep_cbz (s := { m1 with pc := pcAt text psA.toList k })
    (by omega : kc < 32) (nextAddr_pcAt hnd hk) (Or.inr has) hf hto hL
  have hx1 : m1.x (BitVec.ofNat 5 kc) = m.x (BitVec.ofNat 5 kc) - 1 := by
    simp only [m1]; rw [wX_x_self54 hkc, rX_of_lt hkc]
  have hrx : ({ m1 with pc := pcAt text psA.toList k } : MState).rX (BitVec.ofNat 5 kc) =
      m.x (BitVec.ofNat 5 kc) - 1 := by
    show m1.rX _ = _; rw [rX_of_lt hkc, hx1]
  rw [hrx, has] at hstep
  refine ⟨_, (hs1.trans hst).tail (pstep_at hnd hlt hret hk rfl hstep), hx1,
    keeps54_pc (keeps54_wX (List.mem_singleton.2 rfl)) _, (wX_fields).1, ?_⟩
  show (if ((m.x (BitVec.ofNat 5 kc) - 1 == 0) = (As.CBNZ == As.CBZ)) then _ else _) = _
  have hb : (As.CBNZ == As.CBZ) = false := by decide
  rw [hb]
  by_cases hz : m.x (BitVec.ofNat 5 kc) - 1 = 0
  · rw [if_pos hz, hz]; rfl
  · rw [if_neg hz, if_pos (by simpa using hz)]

/-- A loop of `N` iterations, each from the head (`head`) under the invariant `I i` reaching
`I (i + 1)` at the head or, after the last, at `exit`: from `I 0` at the head the machine reaches
`I N` at `exit`. -/
theorem loop_run {N : Nat} {I : Nat → MState → Prop} {head exit : BitVec 64}
    (hstep : ∀ i m, i < N → I i m → m.pc = head →
      ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧ I (i + 1) m' ∧
        m'.pc = if i + 1 = N then exit else head) :
    ∀ d i m, i + d = N → i < N → I i m → m.pc = head →
      ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧ I N m' ∧
        m'.pc = exit
  | 0, i, _, hd, hi, _, _ => by omega
  | d + 1, i, m, hd, hi, hI, hpc => by
    obtain ⟨m1, hs1, hI1, hpc1⟩ := hstep i m hi hI hpc
    by_cases hN : i + 1 = N
    · subst hN
      exact ⟨m1, hs1, hI1, by rw [hpc1, if_pos rfl]⟩
    · rw [if_neg hN] at hpc1
      obtain ⟨m2, hs2, hI2, hpc2⟩ := loop_run hstep d (i + 1) m1 (by omega) (by omega) hI1 hpc1
      exact ⟨m2, hs1.trans hs2, hI2, hpc2⟩

end Run

/-! ## `runLoc`'s clobbers -/

section Clobber

variable {lc : LocCtx} {v : Value}

/-- A register after `setReg r0 poison`: `poison`, or the old content at a register other than
`r0` (or `r0` is `ZERO`, which `setReg` does not write). -/
theorem setReg_poison_get {s : LocState} {r0 q : Nat} {y : Val}
    (h : (s.setReg r0 .poison).regs[q]? = some y) :
    y = .poison ∨ (s.regs[q]? = some y ∧ (q ≠ r0 ∨ r0 = zeroReg)) := by
  rcases setReg_get h with ⟨-, rfl⟩ | ⟨h1, h2⟩
  · exact .inl rfl
  · exact .inr ⟨h2, h1⟩

/-- A register after `clobberMask msk`: `poison`, or the old content at a register not in `msk`. -/
theorem clobberMask_get {s : LocState} {msk : RegMask} {q : Nat} {y : Val}
    (h : (s.clobberMask msk).regs[q]? = some y) :
    y = .poison ∨ (s.regs[q]? = some y ∧ msk.hasReg q = false) := by
  unfold LocState.clobberMask at h
  split at h
  · rename_i he
    refine .inr ⟨h, ?_⟩
    cases hm : msk.hasReg q with
    | false => rfl
    | true =>
      exfalso
      simp only [RegMask.isEmpty, RegMask.hasReg, Bool.and_eq_true, beq_iff_eq] at he hm
      split at hm <;> simp_all
  · simp only [Array.getElem?_mapIdx] at h
    cases hr : s.regs[q]? with
    | none => rw [hr] at h; cases h
    | some z =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq] at h
      by_cases hm : msk.hasReg q = true
      · left; rw [if_pos hm] at h; exact h.symm
      · right; rw [if_neg hm] at h; exact ⟨by rw [h], by simpa using hm⟩

/-- One argument's clobber of `LocState.clobber`. -/
def clobArg54 (lc : LocCtx) (v : Value) (b : Bool) (i : Nat) (s : LocState) : LocState :=
  if !b then s else match v.args[i]?.bind lc.regOf with
    | some r => s.setReg r .poison
    | none => s

/-- The temporary's clobber of `LocState.clobber`. -/
def clobTemp54 (lc : LocCtx) (v : Value) (s : LocState) : LocState :=
  match (lc.temps[v.id]?).join with
  | some r => s.setReg r .poison
  | none => s

/-- `LocState.clobber` as its steps. -/
theorem clobber_eq54 (s : LocState) :
    s.clobber lc v =
      if v.op.clobberFlags then
        { clobTemp54 lc v (clobArg54 lc v v.op.regInfo.clobbersArg0 0
          (clobArg54 lc v v.op.regInfo.clobbersArg1 1 (s.clobberMask v.op.regInfo.clobbers)))
          with flags := .poison }
      else clobTemp54 lc v (clobArg54 lc v v.op.regInfo.clobbersArg0 0
          (clobArg54 lc v v.op.regInfo.clobbersArg1 1 (s.clobberMask v.op.regInfo.clobbers))) := by
  unfold LocState.clobber clobArg54 clobTemp54
  rfl

private theorem clobArg_get (b : Bool) (i : Nat) (s : LocState) {q : Nat} {y : Val}
    (h : (clobArg54 lc v b i s).regs[q]? = some y) :
    y = .poison ∨ (s.regs[q]? = some y ∧
      (b = true → v.args[i]?.bind lc.regOf = some q → q = zeroReg)) := by
  unfold clobArg54 at h
  cases b with
  | false => exact .inr ⟨h, fun h => by cases h⟩
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    cases hr : v.args[i]?.bind lc.regOf with
    | none => rw [hr] at h; exact .inr ⟨h, fun _ h => by cases h⟩
    | some r0 =>
      rw [hr] at h
      rcases setReg_poison_get h with rfl | ⟨h1, h2⟩
      · exact .inl rfl
      · refine .inr ⟨h1, fun _ he => ?_⟩
        cases he
        rcases h2 with h2 | h2
        · exact absurd rfl h2
        · exact h2

private theorem clobTemp_get (s : LocState) {q : Nat} {y : Val}
    (h : (clobTemp54 lc v s).regs[q]? = some y) :
    y = .poison ∨ (s.regs[q]? = some y ∧ ((lc.temps[v.id]?).join = some q → q = zeroReg)) := by
  unfold clobTemp54 at h
  cases ht : (lc.temps[v.id]?).join with
  | none => rw [ht] at h; exact .inr ⟨h, fun h => by cases h⟩
  | some t =>
    rw [ht] at h
    rcases setReg_poison_get h with rfl | ⟨h1, h2⟩
    · exact .inl rfl
    · refine .inr ⟨h1, fun he => ?_⟩
      cases he
      rcases h2 with h2 | h2
      · exact absurd rfl h2
      · exact h2

/-- A register after `LocState.clobber lc s v`: `poison`, or the old content at a register outside
the op's mask, not an argument register it clobbers and not its temporary (`ZERO` excepted). -/
theorem clobber_get54 {s : LocState} {r : Nat} {x : Val} (h : (s.clobber lc v).regs[r]? = some x) :
    x = .poison ∨ (s.regs[r]? = some x ∧ v.op.regInfo.clobbers.hasReg r = false ∧
      (v.op.regInfo.clobbersArg0 = true → v.args[0]?.bind lc.regOf = some r → r = zeroReg) ∧
      (v.op.regInfo.clobbersArg1 = true → v.args[1]?.bind lc.regOf = some r → r = zeroReg) ∧
      ((lc.temps[v.id]?).join = some r → r = zeroReg)) := by
  rw [clobber_eq54] at h
  have h4 : (clobTemp54 lc v (clobArg54 lc v v.op.regInfo.clobbersArg0 0
      (clobArg54 lc v v.op.regInfo.clobbersArg1 1 (s.clobberMask v.op.regInfo.clobbers)))).regs[r]? =
      some x := by
    split at h <;> exact h
  rcases clobTemp_get _ h4 with rfl | ⟨h3, ht⟩
  · exact .inl rfl
  rcases clobArg_get _ 0 _ h3 with rfl | ⟨h2, ha0⟩
  · exact .inl rfl
  rcases clobArg_get _ 1 _ h2 with rfl | ⟨h1, ha1⟩
  · exact .inl rfl
  rcases clobberMask_get h1 with rfl | ⟨h0, hm⟩
  · exact .inl rfl
  exact .inr ⟨h0, hm, ha0, ha1, ht⟩

/-- `LocState.clobber` keeps the slots and the memory, and the flags of an op that keeps them. -/
theorem clobber_keeps54 (s : LocState) (hf : v.op.clobberFlags = false) :
    (s.clobber lc v).slots = s.slots ∧ (s.clobber lc v).flags = s.flags ∧
      (s.clobber lc v).mem = s.mem := by
  have hA : ∀ (b : Bool) (i : Nat) (s : LocState), (clobArg54 lc v b i s).slots = s.slots ∧
      (clobArg54 lc v b i s).flags = s.flags ∧ (clobArg54 lc v b i s).mem = s.mem := by
    intro b i s
    unfold clobArg54
    split
    · exact ⟨rfl, rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl, rfl⟩
  have hT : ∀ s : LocState, (clobTemp54 lc v s).slots = s.slots ∧
      (clobTemp54 lc v s).flags = s.flags ∧ (clobTemp54 lc v s).mem = s.mem := by
    intro s; unfold clobTemp54; split <;> exact ⟨rfl, rfl, rfl⟩
  have hM : ∀ msk : RegMask, (s.clobberMask msk).slots = s.slots ∧
      (s.clobberMask msk).flags = s.flags ∧ (s.clobberMask msk).mem = s.mem := by
    intro msk; unfold LocState.clobberMask; split <;> exact ⟨rfl, rfl, rfl⟩
  rw [clobber_eq54, hf, if_neg (by simp)]
  obtain ⟨h1, h2, h3⟩ := hM v.op.regInfo.clobbers
  obtain ⟨h4, h5, h6⟩ := hA v.op.regInfo.clobbersArg1 1 (s.clobberMask v.op.regInfo.clobbers)
  obtain ⟨h7, h8, h9⟩ := hA v.op.regInfo.clobbersArg0 0
    (clobArg54 lc v v.op.regInfo.clobbersArg1 1 (s.clobberMask v.op.regInfo.clobbers))
  obtain ⟨h10, h11, h12⟩ := hT (clobArg54 lc v v.op.regInfo.clobbersArg0 0
    (clobArg54 lc v v.op.regInfo.clobbersArg1 1 (s.clobberMask v.op.regInfo.clobbers)))
  exact ⟨h10.trans (h7.trans (h4.trans h1)), h11.trans (h8.trans (h5.trans h2)),
    h12.trans (h9.trans (h6.trans h3))⟩

end Clobber

end GoFV.Proof.Gen

import GoFV.Proof.Gen.G61a

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G61, group A: the load-exclusive compare-and-swap (`docs/plans/proofs3.md` §4)

`LoweredAtomicCas{64,32}` (`cas`, `GoFV/Gen/Check61a.lean`): `LDAXR (Rp), R27`; `CMP`/`CMPW Ro,
R27`; `BNE L`; `STLXR Rn, (Rp), R27`; `CBNZ R27`; `L: CSET EQ, Rd`. The machine's run
(`cas_run`): the compare's zero flag says whether the location's low bytes equal `Ro`'s
(`cmpF61c_z`); if so the `BNE` falls through, the store-exclusive stores `Rn`'s low bytes and
leaves `R27 = 0`, the `CBNZ R27` falls through and the `CSET` gives 1; else the `BNE` branches to
the `CSET` (`atomTgt`), which gives 0, and the memory is unchanged. `g61_cas` relates it to
`runLoc`'s `Atomic.cas` (`stepLoc_cas61`) through `atom_finish`: the location's integer
(`old_rel61`) and the fitted `old` (`fit_asInt61`) are the compared low bits, the boolean result
is the `CSET`'s 0 or 1.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## Runs -/

section Runs

/-- The flags of the compare-and-swap's `CMP` (`n = 8`) or `CMPW` (`n = 4`) of `a` with `b`. -/
def cmpF61c (n : Nat) (a b : BitVec 64) : GoFV.SSA.Sem.Flags :=
  if n = 8 then (GoFV.SSA.Sem.Arm64.subFlags a b).2
  else (GoFV.SSA.Sem.Arm64.subFlags (a.setWidth 32) (b.setWidth 32)).2

/-- The zero flag of `cmpF61c`: the low bits of the location's width are equal. -/
theorem cmpF61c_z {n : Nat} (hn : n = 8 ∨ n = 4) (a b : BitVec 64) :
    (cmpF61c n a b).z = (a.setWidth (widthN n).bits == b.setWidth (widthN n).bits) := by
  rcases hn with rfl | rfl
  · show (GoFV.SSA.Sem.Arm64.subFlags a b).2.z = (a.setWidth 64 == b.setWidth 64)
    rw [subFlags_z64, BitVec.setWidth_eq, BitVec.setWidth_eq]
  · exact subFlags_z32 _ _

theorem cmpPat_code61c {n : Nat} {ro : Int} : (cmp61Pat n ro).Code := fun _ h => by
  unfold cmp61Pat at h
  exact shape_noop (by split <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> nofun) h

theorem bnePat_code61c : bnePat.Code := fun p h => by
  simp only [bnePat, Bool.and_eq_true, beq_iff_eq] at h
  have has := h.1.1.1.1.1.1
  exact noop_of_as (by simp [Prog.isSkip, has]) (by rw [has]; nofun)

theorem csetEqPat_code61c {rd : Int} : (csetEqPat rd).Code := fun _ h =>
  shape_noop (by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> nofun) h

variable {L : Link} {p : Prog} {next t : BitVec 64}

/-- `CMP`/`CMPW Ro, R27`: the flags `cmpF61c` of `X27` and `X ko`. -/
theorem cmp_step61c {n ko : Nat} (hn : n = 8 ∨ n = 4) (hko : ko < 32)
    (hnx : L.nextAddr p.id = some next) (hok : (cmp61Pat n (REG_R0 + ko)).ok p = true)
    (s : MState) :
    progStep L p s = .ok { s with
      nzcv := cmpF61c n (s.rX (BitVec.ofNat 5 27)) (s.rX (BitVec.ofNat 5 ko)), pc := next } := by
  rcases hn with rfl | rfl
  · simp only [cmp61Pat, Pat.ofShape, Shape.ok, Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨⟨⟨⟨⟨has, hf⟩, hr⟩, -⟩, -⟩, -⟩, -⟩ := hok
    rw [progStep_cmp (kn := 27) (by omega) hnx (by rw [has]; rfl)
      (by rw [hf]; exact ctx_src_reg hko) (hr.trans rfl)]
    rfl
  · simp only [cmp61Pat, Pat.ofShape, Shape.ok, Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨⟨⟨⟨⟨has, hf⟩, hr⟩, -⟩, -⟩, -⟩, -⟩ := hok
    rw [progStep_cmpwReg (kn := 27) (by omega) hko hnx (by rw [has]; rfl) hf (hr.trans rfl)]
    rfl

/-- `BNE` with the zero flag set: the fall-through. -/
theorem bne_fall61c {tid : Nat} (hnx : L.nextAddr p.id = some next) (hok : bnePat.ok p = true)
    (ht : p.to = brA tid) (hL : L.addr tid = some t) {s : MState} (hz : s.nzcv.z = true) :
    progStep L p s = .ok { s with pc := next } := by
  simp only [bnePat, Bool.and_eq_true, beq_iff_eq] at hok
  have has := hok.1.1.1.1.1.1
  rw [progStep_bcond (c := .ne) hnx (by rw [has]; rfl) ht hL]
  show Except.ok { s with pc := if (!s.nzcv.z) = true then t else next } = _
  rw [hz]
  rfl

/-- `BNE` with the zero flag clear: the target. -/
theorem bne_taken61c {tid : Nat} (hnx : L.nextAddr p.id = some next) (hok : bnePat.ok p = true)
    (ht : p.to = brA tid) (hL : L.addr tid = some t) {s : MState} (hz : s.nzcv.z = false) :
    progStep L p s = .ok { s with pc := t } := by
  simp only [bnePat, Bool.and_eq_true, beq_iff_eq] at hok
  have has := hok.1.1.1.1.1.1
  rw [progStep_bcond (c := .ne) hnx (by rw [has]; rfl) ht hL]
  show Except.ok { s with pc := if (!s.nzcv.z) = true then t else next } = _
  rw [hz]
  rfl

/-- `CSET EQ, Rd`: the zero flag as 0 or 1 in `X kd`. -/
theorem csetEq_step61c {kd : Nat} (hkd : kd < 32) (hnx : L.nextAddr p.id = some next)
    (hok : (csetEqPat (REG_R0 + kd)).ok p = true) {s : MState} {z : Bool} (hz : s.nzcv.z = z) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd) (if z then 1 else 0) with pc := next } := by
  simp only [csetEqPat, Pat.ofShape, Shape.ok, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨has, hf⟩, -⟩, ht⟩, -⟩, -⟩, -⟩ := hok
  have hc : condOf (BitVec.ofInt 4 (SPOP_EQ - SPOP_EQ)) = .eq := by decide
  rw [progStep_cset hkd hnx has hf (by decide) ht]
  simp only [MState.holds, hc]
  rw [← hz]
  rfl

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64}

omit [GoFV.SSA.Sem.Addrs] in
private theorem pstar_trans61c {L : Link} {ps : List Prog} {a b c : MState}
    (h1 : PStar H L ps ret a b) (h2 : PStar H L ps ret b c) : PStar H L ps ret a c := by
  induction h2 with
  | refl => exact h1
  | tail _ hs ih => exact ih.tail hs

/-- The compare-and-swap's run: `LDAXR` loads the `n` bytes at `A` into `X27`, `CMP`/`CMPW`
compares them with `X ko` (`z`: their low `8n` bits are equal); if `z`, the `BNE` falls through,
`STLXR` stores the low `n` bytes of `X kn` at `A` and sets `X27 = 0`, the `CBNZ R27` falls
through and `CSET EQ` puts 1 in `X kd`; else the `BNE` branches to the `CSET`, which puts 0
there. Only `X27` and `X kd` change among the X registers. -/
theorem cas_run (hnd : (psA.toList.map (·.id)).Nodup) (hlt : ∀ p ∈ psA.toList, p.id < 2 ^ 32)
    (hret : ∀ p ∈ psA.toList, (Link.byId sym text az ez psA.toList).addr p.id ≠ some ret)
    {n kp ko kn kd : Nat} (hn : n = 8 ∨ n = 4) (hkp : kp < 31) (hko : ko < 32) (hkn : kn < 32)
    (hkd : kd < 31) (hp27 : kp ≠ 27) (ho27 : ko ≠ 27) (hn27 : kn ≠ 27) {j j' : Nat}
    (hvs : ManyAt2 psA j (atomPats61 .cas n (REG_R0 + kp) (REG_R0 + ko) (REG_R0 + kn)
      (REG_R0 + kd) 0) j')
    (htgt : atomTgt .cas psA j = true) (m : MState) {A : BitVec 64}
    (hA : m.rX (BitVec.ofNat 5 kp) = A) (hnil : nilPage A = false) {z : Bool}
    (hz : (((readMem m.mem A n).setWidth 64).setWidth (widthN n).bits ==
      (m.rX (BitVec.ofNat 5 ko)).setWidth (widthN n).bits) = z) :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret
        { m with pc := pcAt text psA.toList j } m' ∧
      m'.x (BitVec.ofNat 5 kd) = (if z then 1 else 0) ∧
      (∀ q : Reg, q ≠ BitVec.ofNat 5 kd → q ≠ BitVec.ofNat 5 27 → m'.x q = m.x q) ∧
      m'.mem = (if z then writeMem m.mem A n
        (BitVec.ofNat (8 * n) ((m.rX (BitVec.ofNat 5 kn)).toNat % 2 ^ (8 * n))) else m.mem) ∧
      m'.v = m.v ∧ m'.sp = m.sp ∧ m'.pc = pcAt text psA.toList j' := by
  have hn' : n = 8 ∨ n = 4 ∨ n = 1 := by omega
  simp only [atomPats61] at hvs
  obtain ⟨k1, h1, k2, h2, k3, h3, k4, h4, k5, h5, k6, h6, hj'⟩ := hvs
  simp only [ManyAt2] at hj'
  subst hj'
  -- the branches' targets
  have e1 := oneAt2_next h1 ldaxPat_code
  have e2 := oneAt2_next h2 cmpPat_code61c
  have e3 := oneAt2_next h3 bnePat_code61c
  have e4 := oneAt2_next h4 stlxPat_code
  have e5 := oneAt2_next h5 (fun _ hp => cbnzPat_noop hp)
  have e6 := oneAt2_next h6 csetEqPat_code61c
  simp only [atomTgt, brTo, nexts, Bool.and_eq_true] at htgt
  rw [← e1, ← e2, ← e3, ← e4, ← e5, ← e6] at htgt
  obtain ⟨hk1, -⟩ : ∃ hk1 : k1 - 1 < psA.size, True := by
    obtain ⟨k, -, rfl, hk, -⟩ := h1; exact ⟨by omega, trivial⟩
  obtain ⟨hk3, -⟩ : ∃ hk3 : k3 - 1 < psA.size, True := by
    obtain ⟨k, -, rfl, hk, -⟩ := h3; exact ⟨by omega, trivial⟩
  obtain ⟨hk5, -⟩ : ∃ hk5 : k5 - 1 < psA.size, True := by
    obtain ⟨k, -, rfl, hk, -⟩ := h5; exact ⟨by omega, trivial⟩
  obtain ⟨hk6, hj1⟩ : ∃ hk6 : j' - 1 < psA.size, 1 ≤ j' := by
    obtain ⟨k, -, rfl, hk, -⟩ := h6; exact ⟨by omega, by omega⟩
  rw [Array.getElem?_eq_getElem hk3, Array.getElem?_eq_getElem hk6,
    Array.getElem?_eq_getElem hk5, Array.getElem?_eq_getElem hk1] at htgt
  simp only [beq_iff_eq] at htgt
  obtain ⟨htB, htC⟩ := htgt
  have hL1 : (Link.byId sym text az ez psA.toList).addr psA[k1 - 1].id =
      some (pcAt text psA.toList (k1 - 1)) := by
    have := addr_pcAt (sym := sym) (text := text) (az := az) (ez := ez) (ps := psA.toList)
      (j := k1 - 1) (by simpa using hk1)
    simpa using this
  have hL6 : (Link.byId sym text az ez psA.toList).addr psA[j' - 1].id =
      some (pcAt text psA.toList (j' - 1)) := by
    have := addr_pcAt (sym := sym) (text := text) (az := az) (ez := ez) (ps := psA.toList)
      (j := j' - 1) (by simpa using hk6)
    simpa using this
  -- `LDAXR`
  let old : BitVec 64 := (readMem m.mem A n).setWidth 64
  obtain ⟨k, hk1', hs1⟩ := step1 (H := H) hnd hlt hret h1 m
    (f := fun k => { m.wX (BitVec.ofNat 5 27) old with pc := pcAt text psA.toList (k + 1) })
    (fun k hk hok _ => by
      simp only [ldaxPat, Pat.ofShape, Shape.ok, Bool.and_eq_true, beq_iff_eq] at hok
      obtain ⟨⟨⟨⟨⟨⟨has, hf⟩, -⟩, ht⟩, hsc⟩, -⟩, -⟩ := hok
      have hma : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
          { m with pc := pcAt text psA.toList k } psA.toList[k]).mem psA.toList[k].from_ =
          .ok (A, none) := by
        rw [hf, ctx_mem_reg (by omega) hsc]
        show Except.ok (m.rX (BitVec.ofNat 5 kp) + BitVec.ofInt 64 0, none) = _
        rw [hA]; simp
      rw [progStep_ldaxr hn' (kd := 27) (by omega) (nextAddr_pcAt hnd hk) has hma (ht.trans rfl)
        hnil, wX_pc])
  rw [← hk1'] at hs1
  let m1 : MState := m.wX (BitVec.ofNat 5 27) old
  have h27 : m1.rX (BitVec.ofNat 5 27) = old := rX_wX_self61 (by omega) old
  have hko' : m1.rX (BitVec.ofNat 5 ko) = m.rX (BitVec.ofNat 5 ko) :=
    rX_wX61 (by omega) hko ho27 old
  -- `CMP`
  let m2 : MState := { m1 with nzcv := cmpF61c n old (m.rX (BitVec.ofNat 5 ko)) }
  obtain ⟨k', hk2', hs2⟩ := step1 (H := H) hnd hlt hret h2 m1
    (f := fun k => { m2 with pc := pcAt text psA.toList (k + 1) })
    (fun k hk hok _ => by
      rw [cmp_step61c hn hko (nextAddr_pcAt hnd hk) hok]
      have e27 : ({ m1 with pc := pcAt text psA.toList k } : MState).rX (BitVec.ofNat 5 27) =
          old := h27
      have eko : ({ m1 with pc := pcAt text psA.toList k } : MState).rX (BitVec.ofNat 5 ko) =
          m.rX (BitVec.ofNat 5 ko) := hko'
      rw [e27, eko])
  rw [← hk2'] at hs2
  have hm2z : m2.nzcv.z = z := by
    show (cmpF61c n old (m.rX (BitVec.ofNat 5 ko))).z = z
    rw [cmpF61c_z hn]; exact hz
  have hfr2 : ∀ q : Reg, q ≠ BitVec.ofNat 5 27 → m2.x q = m.x q := fun q hq =>
    show (m.wX (BitVec.ofNat 5 27) old).x q = m.x q from wX_x_of_ne hq
  have hmem2 : m2.mem = m.mem := show (m.wX _ _).mem = _ from wX_fields.1
  have hsp2 : m2.sp = m.sp := show (m.wX _ _).sp = _ from wX_fields.2.1
  have hv2 : m2.v = m.v := show (m.wX _ _).v = _ from wX_fields.2.2.2
  cases z with
  | false =>
    -- `BNE`, taken
    obtain ⟨k'', hk3', hs3⟩ := step1 (H := H) hnd hlt hret h3 m2
      (f := fun _ => { m2 with pc := pcAt text psA.toList (j' - 1) })
      (fun k hk hok hk3e => by
        have hkk : k = k3 - 1 := by omega
        subst hkk
        have ht : psA.toList[k3 - 1].to = brA psA[j' - 1].id := by simpa using htB
        exact bne_taken61c (nextAddr_pcAt hnd hk) hok ht hL6 hm2z)
    -- `CSET`
    have h6' : OneAt2 psA (j' - 1) (csetEqPat (REG_R0 + kd)) j' := by
      obtain ⟨k, -, hkj, hk, hok, -⟩ := h6
      exact ⟨k, by omega, hkj, hk, hok, fun l _ h1 h2 => absurd h2 (by omega)⟩
    obtain ⟨k''', hk6', hs6⟩ := step1 (H := H) hnd hlt hret h6' m2
      (f := fun k => { m2.wX (BitVec.ofNat 5 kd) (if false then 1 else 0) with
        pc := pcAt text psA.toList (k + 1) })
      (fun k hk hok _ => by
        rw [csetEq_step61c (s := { m2 with pc := pcAt text psA.toList k }) (by omega)
          (nextAddr_pcAt hnd hk) hok hm2z, wX_pc])
    rw [← hk6'] at hs6
    refine ⟨_, pstar_trans61c hs1 (pstar_trans61c hs2 (pstar_trans61c hs3 hs6)),
      wX_x_self54 hkd, fun q h1 h2 => ?_, ?_, ?_, ?_, rfl⟩
    · show (m2.wX _ _).x q = _
      rw [wX_x_of_ne h1, hfr2 q h2]
    · show (m2.wX _ _).mem = _
      rw [wX_fields.1, hmem2]; rfl
    · show (m2.wX _ _).v = _
      rw [wX_fields.2.2.2, hv2]
    · show (m2.wX _ _).sp = _
      rw [wX_fields.2.1, hsp2]
  | true =>
    -- `BNE`, the fall-through
    obtain ⟨k'', hk3', hs3⟩ := step1 (H := H) hnd hlt hret h3 m2
      (f := fun k => { m2 with pc := pcAt text psA.toList (k + 1) })
      (fun k hk hok hk3e => by
        have hkk : k = k3 - 1 := by omega
        subst hkk
        have ht : psA.toList[k3 - 1].to = brA psA[j' - 1].id := by simpa using htB
        exact bne_fall61c (nextAddr_pcAt hnd hk) hok ht hL6 hm2z)
    rw [← hk3'] at hs3
    -- `STLXR`
    let M' : Memory := writeMem m.mem A n
      (BitVec.ofNat (8 * n) ((m.rX (BitVec.ofNat 5 kn)).toNat % 2 ^ (8 * n)))
    obtain ⟨k4', hk4', hs4⟩ := step1 (H := H) hnd hlt hret h4 m2
      (f := fun k => { m2.wX (BitVec.ofNat 5 27) 0 with
        mem := M', pc := pcAt text psA.toList (k + 1) })
      (fun k hk hok _ => by
        simp only [stlxPat, Shape.okT, Bool.and_eq_true, beq_iff_eq] at hok
        obtain ⟨⟨⟨⟨⟨⟨has, hf⟩, -⟩, ht⟩, hsc⟩, -⟩, ht2⟩ := hok
        have hma : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
            { m2 with pc := pcAt text psA.toList k } psA.toList[k]).mem psA.toList[k].to =
            .ok (A, none) := by
          rw [ht, ctx_mem_reg (by omega) hsc]
          show Except.ok ((m.wX (BitVec.ofNat 5 27) old).rX (BitVec.ofNat 5 kp) +
            BitVec.ofInt 64 0, none) = _
          rw [rX_wX61 (by omega) (by omega) hp27, hA]; simp
        rw [progStep_stlxr hn' hkn (nextAddr_pcAt hnd hk) has hf hma ht2 hnil]
        have hv : ({ m2 with pc := pcAt text psA.toList k } : MState).rX (BitVec.ofNat 5 kn) =
            m.rX (BitVec.ofNat 5 kn) := by
          show (m.wX (BitVec.ofNat 5 27) old).rX (BitVec.ofNat 5 kn) = _
          exact rX_wX61 (by omega) (by omega) hn27 old
        have hmm : ({ m2 with pc := pcAt text psA.toList k } : MState).mem = m.mem := hmem2
        rw [wX_pc, hv, hmm])
    rw [← hk4'] at hs4
    -- `CBNZ R27`
    let m4 : MState := { m2.wX (BitVec.ofNat 5 27) 0 with mem := M' }
    obtain ⟨k5', hk5', hs5⟩ := step1 (H := H) hnd hlt hret h5 m4
      (f := fun k => { m4 with pc := pcAt text psA.toList (k + 1) })
      (fun k hk hok hk5e => by
        have hkk : k = k5 - 1 := by omega
        subst hkk
        have ht : psA.toList[k5 - 1].to = brA psA[k1 - 1].id := by simpa using htC
        rw [cbnz27_step hk hnd hok ht hL1]
        show (m2.wX (BitVec.ofNat 5 27) 0).rX (BitVec.ofNat 5 27) = 0
        exact rX_wX_self61 (by omega) 0)
    rw [← hk5'] at hs5
    -- `CSET`
    have hm4z : m4.nzcv.z = true := by
      show (m2.wX (BitVec.ofNat 5 27) 0).nzcv.z = true
      rw [wX_fields.2.2.1]; exact hm2z
    obtain ⟨k6', hk6', hs6⟩ := step1 (H := H) hnd hlt hret h6 m4
      (f := fun k => { m4.wX (BitVec.ofNat 5 kd) (if true then 1 else 0) with
        pc := pcAt text psA.toList (k + 1) })
      (fun k hk hok _ => by
        rw [csetEq_step61c (s := { m4 with pc := pcAt text psA.toList k }) (by omega)
          (nextAddr_pcAt hnd hk) hok hm4z, wX_pc])
    rw [← hk6'] at hs6
    refine ⟨_, pstar_trans61c hs1 (pstar_trans61c hs2 (pstar_trans61c hs3
      (pstar_trans61c hs4 (pstar_trans61c hs5 hs6)))),
      wX_x_self54 hkd, fun q h1 h2 => ?_, ?_, ?_, ?_, rfl⟩
    · show (m4.wX _ _).x q = _
      rw [wX_x_of_ne h1]
      show (m2.wX (BitVec.ofNat 5 27) 0).x q = _
      rw [wX_x_of_ne h2, hfr2 q h2]
    · show (m4.wX _ _).mem = _
      rw [wX_fields.1]; rfl
    · show (m4.wX _ _).v = _
      rw [wX_fields.2.2.2]
      show (m2.wX (BitVec.ofNat 5 27) 0).v = _
      rw [wX_fields.2.2.2, hv2]
    · show (m4.wX _ _).sp = _
      rw [wX_fields.2.1]
      show (m2.wX (BitVec.ofNat 5 27) 0).sp = _
      rw [wX_fields.2.1, hsp2]

end Runs

/-! ## The case -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K : Nat → Option Nat}

/-- A load that reads as an integer read its bytes. -/
theorem load_read61c {mm : Mem} {w : Width} {p : Ptr} {c : BitVec w.bits}
    (h : (mm.load (.int w) p).asInt w = some c) : ∃ bs, mm.read p (Ty.int w).size = some bs := by
  unfold Mem.load at h
  cases hr : mm.read p (Ty.int w).size with
  | none => simp only [hr] at h; simp [Val.asInt] at h
  | some bs => exact ⟨bs, rfl⟩

/-- `LoweredAtomicCas{64,32} p old new mem`: the loop compares the location with `old`, stores
`new` when they are equal, and puts whether they were in `Rd`. -/
theorem g61_cas (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size ≤ 8)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hj : E.pcOf b i = pcAt text psA.toList j)
    (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {n : Nat} {t0 : Ty} {rp ro rn rd : Int} {r : Nat}
    (hop : atom61? v.op = some (.cas, n)) (htemp : (lc.temps[v.id]?).join = none)
    (hsz4 : v.args.size = 4) (hty : lc.ty v.id = .tuple [t0, .mem]) (hc0 : cls t0 = some 1)
    (hap : argObj lc v 0 = .ok (64, rp)) (hpr : rp ≠ r27A) (hpz : rp ≠ ARM64.REGZERO)
    (hao : argObj lc v 1 = .ok (8 * n, ro)) (hor27 : ro ≠ r27A)
    (han : argObj lc v 2 = .ok (8 * n, rn)) (hnr : rn ≠ r27A) (hma : memArg lc v 3 = .ok ())
    (hh : lc.home v.id = some (.pair (some r) none)) (hrz : r ≠ zeroReg) (hd : destOK r = true)
    (hor : objOf? r = some rd) (hvs : ManyAt2 psA j (atomPats61 .cas n rp ro rn rd 0) j')
    (htgt : atomTgt .cas psA j = true) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) (kSet K r (some 1)) s' osp ∧
      SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  obtain ⟨hnp, -, -, -, -, -, -, -, hcf, -, -, -, hn, hwb, -, hn1, -⟩ := atom61?_facts hop
  have hn84 : n = 8 ∨ n = 4 := by
    rcases hn with h | h | h
    · exact .inl h
    · exact .inr h
    · exact absurd h (hn1 (.inl rfl))
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hap
  obtain ⟨kp, hkp, rfl, hkkp⟩ := objOf?_some hor0
  have hkp31 := objOf?_lt31 hkp hkkp hpz
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hao
  obtain ⟨ko, hko, rfl, hkko⟩ := objOf?_some hor1
  obtain ⟨a2, r2, ha2, hah2, hor2, hca2⟩ := argObj_spec han
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor2
  obtain ⟨a3, ha3, hamt, hah3⟩ := memArg_spec hma
  obtain ⟨kd, hkd, rfl, hkkd⟩ := objOf?_some hor
  obtain ⟨hkd31, hk27⟩ : kd < 31 ∧ kd ≠ 27 := by
    rcases hkkd with ⟨h, -⟩ | ⟨h, ho⟩
    · exact absurd h hrz
    · exact ⟨h, fun he => objX?_ne27 ho (by rw [he])⟩
  have hp27 : kp ≠ 27 := fun h => hpr (by subst h; rfl)
  have ho27 : ko ≠ 27 := fun h => hor27 (by subst h; rfl)
  have hn27 : kn ≠ 27 := fun h => hnr (by subst h; rfl)
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨mm0, hmm0, hk0, hsep0⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  obtain ⟨X, hX, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkp
  obtain ⟨Yo, hYo, hyov, hyof⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkko
  obtain ⟨Yn, hYn, hynv, hynf⟩ :=
    arg_rel hA hl hm hinv hah2 hca2 (kread_arg hR hnp ha2 hah2 hca2) hkkn
  obtain ⟨x, yo, yn, p, cur, old, hx, hyo, hyn, hpw, hal, hcur, hold, hcase⟩ :=
    stepLoc_cas61 hl hop (.inl rfl) (arr4 hsz4 ha0 ha1 ha2 ha3) (read_mem hl hah3 hamt hmm) hs
  have ex := hx.symm.trans hX
  injection ex with ex
  subst ex
  have eyo := hyo.symm.trans hYo
  injection eyo with eyo
  subst eyo
  have eyn := hyn.symm.trans hYn
  injection eyn with eyn
  subst eyn
  have hsz' : (Ty.int (widthN n)).size = n := by rcases hn with rfl | rfl | rfl <;> rfl
  obtain ⟨bs, hbs⟩ := load_read61c hcur
  rw [hsz'] at hbs
  obtain ⟨a, hpa, haeq, hnil⟩ :=
    addr_rel hA hMI hxv hxf (addr_asPtrWord hpw) (by omega : 0 < n) (.inr (by rw [hbs]; rfl))
  have haeq' : m.rX (BitVec.ofNat 5 kp) = a + p.off := by simpa using haeq
  rw [hwb] at hal
  have hcur' := old_rel61 hA hMI hn hpa hal ⟨bs, hbs⟩ cur hcur
  have hfo : Fits (widthN n).bits yo := by rw [widthN_bits hn]; exact hyof
  have hold' := fit_asInt61 hA hyov hfo old hold
  have hfr : ∀ z : Bool, Fits 1 ((Val.bool z).retypeL t0) := fun z => fits_retypeL hc0 _
  have hrel : ∀ z : Bool, ValRel E.ι ((Val.bool z).retypeL t0) (if z then 1 else 0) := fun z =>
    valRel_retypeL hA hc0 (by cases z <;> rfl) (by cases z <;> rfl)
  have hpc0 := pc_eta hm hj
  have hfl : v.op.clobberFlags = false → False := fun h => absurd (hcf.symm.trans h) (by decide)
  rcases hcase with ⟨heq, mm', hw, rfl⟩ | ⟨hne, rfl⟩
  · -- the location held `old`: `new` stored, `true`
    have hz : (((readMem m.mem (a + p.off) n).setWidth 64).setWidth (widthN n).bits ==
        (m.rX (BitVec.ofNat 5 ko)).setWidth (widthN n).bits) = true := by
      rw [hcur', hold', heq, beq_self_eq_true]
    obtain ⟨m', hrun, hxd, hxq, hmem', hv', hsp', hpc'⟩ := cas_run (H := H) F.nodup F.lt F.ret
      hn84 hkp31 hko hkn hkd31 hp27 ho27 hn27 hvs htgt m haeq' hnil hz
    rw [hpc0] at hrun
    have hfn : Fits (widthN n).bits yn := by rw [widthN_bits hn]; exact hynf
    rw [encode_storeBytes hfn, hwb] at hw
    obtain ⟨hM', hk', hsep', hP⟩ := atom_store61 hA hMI hk0 hsep0 hn hpa hynv hynf hw
    rw [hty, retypeL_pair, retypeL_mem, write_atom61 hh hty (by rw [hc0]; rfl)]
    simp only [↓reduceIte] at hxd hmem'
    obtain ⟨hlm, hcore, hsl⟩ := atom_finish (m' := m') hF hsz hm hinv hsi hkd hor hd hrz
      (hfr true) (by rw [hxd]; exact hrel true) (by rw [hmem']; exact hM') hk' hsep'
      (fun y hy => by rw [hmem']; exact hP y hy) (fun t ht => by rw [htemp] at ht; cases ht)
      (fun q h1 h2 _ => hxq q h1 h2) hv' hsp' (fun h => (hfl h).elim) (hpc'.trans hj'.symm)
    exact ⟨_, hrun, hlm, hcore, hsl⟩
  · -- the location did not: memory kept, `false`
    have hz : (((readMem m.mem (a + p.off) n).setWidth 64).setWidth (widthN n).bits ==
        (m.rX (BitVec.ofNat 5 ko)).setWidth (widthN n).bits) = false := by
      rw [hcur', hold', beq_eq_false_iff_ne]; exact hne
    obtain ⟨m', hrun, hxd, hxq, hmem', hv', hsp', hpc'⟩ := cas_run (H := H) F.nodup F.lt F.ret
      hn84 hkp31 hko hkn hkd31 hp27 ho27 hn27 hvs htgt m haeq' hnil hz
    rw [hpc0] at hrun
    rw [hty, retypeL_pair, retypeL_mem, write_atom61 hh hty (by rw [hc0]; rfl)]
    simp only [Bool.false_eq_true, ↓reduceIte] at hxd hmem'
    obtain ⟨hlm, hcore, hsl⟩ := atom_finish (m' := m') hF hsz hm hinv hsi hkd hor hd hrz
      (hfr false) (by rw [hxd]; exact hrel false) (by rw [hmem']; exact hMI) hk0 hsep0
      (fun y _ => by rw [hmem']) (fun t ht => by rw [htemp] at ht; cases ht)
      (fun q h1 h2 _ => hxq q h1 h2) hv' hsp' (fun h => (hfl h).elim) (hpc'.trans hj'.symm)
    exact ⟨_, hrun, hlm, hcore, hsl⟩

end Cases

end GoFV.Proof.Gen

import GoFV.Proof.Gen.G61V

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G61, group A: the atomic read-modify-writes (`docs/plans/proofs3.md` §4)

`vkind61a` (`GoFV/Gen/Check61a.lean`) accepts the lowered atomics and their components; `VK61a`
(`Spec61a.lean`) says what it accepted. One value of each family, from `runLoc`'s step
(`Step61.lean`) to the machine's run of its Progs (`Progs61.lean`), related by `atom_finish`
(`G61V.lean`):

* the load-exclusive/store-exclusive loops: `LDAXR` loads the location's `n` bytes (`old_rel61`,
  `res_rel61`), the store-exclusive stores the new value and leaves `R27 = 0`, so the `CBNZ R27`
  back to the `LDAXR` (`atomTgt`) falls through: the loop runs once (`xchg_run`, `add_run`,
  `logic_run`; the compare-and-swap `cas_run`, whose `BNE` skips the store to the `CSET` when the
  location does not hold `old`);
* the LSE forms: one instruction (`progStep_lse`, `progStep_casal`), with `ADD`, `MVN`, `MOV`,
  `CMP`, `CSET` around it.

The stores keep `MemInj` (`atom_store61`, `memInj_storeN`) at the address `addr_rel` gives;
`runLoc`'s result tuple is the component in `Rd` and the new memory (`write_atom61`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## Runs -/

section Runs

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64}

private theorem pstar_trans61 {L : Link} {ps : List Prog} {a b c : MState}
    (h1 : PStar H L ps ret a b) (h2 : PStar H L ps ret b c) : PStar H L ps ret a c := by
  induction h2 with
  | refl => exact h1
  | tail _ hs ih => exact ih.tail hs

/-- One Prog matching `pat` after no-ops, stepping to `f k` from its index `k`. -/
theorem step1 (hnd : (psA.toList.map (·.id)).Nodup) (hlt : ∀ p ∈ psA.toList, p.id < 2 ^ 32)
    (hret : ∀ p ∈ psA.toList, (Link.byId sym text az ez psA.toList).addr p.id ≠ some ret)
    {pat : Pat} {j j' : Nat} (h : OneAt2 psA j pat j') (m : MState) {f : Nat → MState}
    (hs : ∀ k (hk : k < psA.toList.length), pat.ok psA.toList[k] = true → j' = k + 1 →
      progStep (Link.byId sym text az ez psA.toList) psA.toList[k]
        { m with pc := pcAt text psA.toList k } = .ok (f k)) :
    ∃ k, j' = k + 1 ∧ PStar H (Link.byId sym text az ez psA.toList) psA.toList ret
      { m with pc := pcAt text psA.toList j } (f k) := by
  obtain ⟨k, hk1, hk, hok, hstar⟩ := pstar_oneAt2 (H := H) hnd hlt hret h m
  exact ⟨k, hk1, hstar.tail (pstep_at hnd hlt hret hk rfl (hs k hk hok hk1))⟩

theorem rX_wX61 {m : MState} {k q : Nat} (hk : k < 32) (hq : q < 32) (hkq : q ≠ k)
    (val : BitVec 64) : (m.wX (BitVec.ofNat 5 k) val).rX (BitVec.ofNat 5 q) = m.rX (BitVec.ofNat 5 q) := by
  simp only [MState.rX, wX_x_ne hk hq hkq]

theorem rX_wX_self61 {m : MState} {k : Nat} (hk : k < 31) (val : BitVec 64) :
    (m.wX (BitVec.ofNat 5 k) val).rX (BitVec.ofNat 5 k) = val := by
  rw [rX_of_lt hk, wX_x_self54 hk]

theorem mem_wX61 {m : MState} {r : Reg} {val : BitVec 64} : (m.wX r val).mem = m.mem :=
  wX_fields.1

/-- The Prog at the `k`-th index after no-ops of a `ManyAt2` chain (the indices `nexts`). -/
theorem oneAt2_idx {ps : Array Prog} {j j' : Nat} {pat : Pat} (h : OneAt2 ps j pat j')
    (hc : pat.Code) : j' = nextIdx ps j := oneAt2_next h hc


theorem llsc61_cases (n : Nat) : llsc61 n = (.LDAXR, .STLXR) ∨ llsc61 n = (.LDAXRW, .STLXRW) ∨
    llsc61 n = (.LDAXRB, .STLXRB) := by
  unfold llsc61; split <;> (try split) <;> simp

theorem ldaxPat_code {n : Nat} {rp rd : Int} : (ldaxPat n rp rd).Code := fun _ h => by
  rcases llsc61_cases n with hc | hc | hc <;> simp only [ldaxPat, hc] at h <;>
    exact shape_noop (by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> nofun) h

theorem stlxPat_code {n : Nat} {rs rp : Int} : (stlxPat n rs rp).Code := fun p h => by
  simp only [stlxPat, Shape.okT, Bool.and_eq_true, beq_iff_eq] at h
  have has := h.1.1.1.1.1.1
  rcases llsc61_cases n with hc | hc | hc <;> rw [hc] at has <;>
    exact noop_of_as (by simp [Prog.isSkip, has]) (by rw [has]; nofun)

/-- `CBNZ R27` after a store-exclusive (`R27 = 0`) to a target in the list: the fall-through. -/
theorem cbnz27_step {k tid : Nat} (hk : k < psA.toList.length)
    (hnd : (psA.toList.map (·.id)).Nodup) (hok : (cbnzPat r27A).ok psA.toList[k] = true)
    (ht : psA.toList[k].to = brA tid) {t : BitVec 64}
    (hL : (Link.byId sym text az ez psA.toList).addr tid = some t) {s : MState}
    (h0 : s.rX (BitVec.ofNat 5 27) = 0) :
    progStep (Link.byId sym text az ez psA.toList) psA.toList[k] s =
      .ok { s with pc := pcAt text psA.toList (k + 1) } := by
  simp only [cbnzPat, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨has, hf⟩, -⟩, -⟩, -⟩, -⟩ := hok
  rw [progStep_cbz (k := 27) (by omega) (nextAddr_pcAt hnd hk) (.inr has)
    (by rw [hf]; rfl) ht hL, h0, has]
  rfl

/-- The load-exclusive/store-exclusive loop of an exchange: `LDAXR` loads the `n` bytes at `A`
into `X kd`, `STLXR` stores the low `n` bytes of `X kv` there and sets `X27 = 0`, and the `CBNZ R27`
(to the `LDAXR`) falls through. -/
theorem xchg_run (hnd : (psA.toList.map (·.id)).Nodup) (hlt : ∀ p ∈ psA.toList, p.id < 2 ^ 32)
    (hret : ∀ p ∈ psA.toList, (Link.byId sym text az ez psA.toList).addr p.id ≠ some ret)
    {n kp kv kd : Nat} (hn : n = 8 ∨ n = 4 ∨ n = 1) (hkp : kp < 31) (hkv : kv < 32)
    (hkd : kd < 31) (hpd : kp ≠ kd) (hvd : kv ≠ kd) {j j' : Nat}
    (hvs : ManyAt2 psA j (atomPats61 .xchg n (REG_R0 + kp) (REG_R0 + kv) (REG_R0 + kv)
      (REG_R0 + kd) 0) j')
    (htgt : atomTgt .xchg psA j = true) (m : MState) {A : BitVec 64}
    (hA : m.rX (BitVec.ofNat 5 kp) = A) (hnil : nilPage A = false) :
    PStar H (Link.byId sym text az ez psA.toList) psA.toList ret
      { m with pc := pcAt text psA.toList j }
      { (m.wX (BitVec.ofNat 5 kd) ((readMem m.mem A n).setWidth 64)).wX (BitVec.ofNat 5 27) 0 with
        mem := writeMem m.mem A n
          (BitVec.ofNat (8 * n) ((m.rX (BitVec.ofNat 5 kv)).toNat % 2 ^ (8 * n))),
        pc := pcAt text psA.toList j' } := by
  simp only [atomPats61] at hvs
  obtain ⟨k1, h1, k2, h2, k3, h3, hj'⟩ := hvs
  simp only [ManyAt2] at hj'
  subst hj'
  -- the `CBNZ`'s target
  have e1 := oneAt2_next h1 ldaxPat_code
  have e2 := oneAt2_next h2 stlxPat_code
  have e3 := oneAt2_next h3 (fun _ hp => cbnzPat_noop hp)
  simp only [atomTgt, brTo, nexts] at htgt
  rw [← e1, ← e2, ← e3] at htgt
  obtain ⟨hk1, hkk1⟩ : ∃ hk1 : k1 - 1 < psA.size, True := by
    obtain ⟨k, -, rfl, hk, -⟩ := h1; exact ⟨by omega, trivial⟩
  obtain ⟨hk3, -⟩ : ∃ hk3 : j' - 1 < psA.size, True := by
    obtain ⟨k, -, rfl, hk, -⟩ := h3; exact ⟨by omega, trivial⟩
  rw [Array.getElem?_eq_getElem hk3, Array.getElem?_eq_getElem hk1] at htgt
  simp only [beq_iff_eq] at htgt
  have hL : (Link.byId sym text az ez psA.toList).addr psA[k1 - 1].id =
      some (pcAt text psA.toList (k1 - 1)) := by
    have := addr_pcAt (sym := sym) (text := text) (az := az) (ez := ez) (ps := psA.toList)
      (j := k1 - 1) (by simpa using hk1)
    simpa using this
  -- `LDAXR`
  let old : BitVec 64 := (readMem m.mem A n).setWidth 64
  obtain ⟨k, hk1', hs1⟩ := step1 (H := H) hnd hlt hret h1 m
    (f := fun k => { m.wX (BitVec.ofNat 5 kd) old with pc := pcAt text psA.toList (k + 1) })
    (fun k hk hok _ => by
      simp only [ldaxPat, Pat.ofShape, Shape.ok, Bool.and_eq_true, beq_iff_eq] at hok
      obtain ⟨⟨⟨⟨⟨⟨has, hf⟩, -⟩, ht⟩, hsc⟩, -⟩, -⟩ := hok
      have hma : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
          { m with pc := pcAt text psA.toList k } psA.toList[k]).mem psA.toList[k].from_ =
          .ok (A, none) := by
        rw [hf, ctx_mem_reg (by omega) hsc]
        show Except.ok (m.rX (BitVec.ofNat 5 kp) + BitVec.ofInt 64 0, none) = _
        rw [hA]; simp
      rw [progStep_ldaxr hn (by omega) (nextAddr_pcAt hnd hk) has hma ht hnil, wX_pc])
  rw [← hk1'] at hs1
  -- `STLXR`
  let m1 : MState := m.wX (BitVec.ofNat 5 kd) old
  let M' : Memory := writeMem m.mem A n
    (BitVec.ofNat (8 * n) ((m.rX (BitVec.ofNat 5 kv)).toNat % 2 ^ (8 * n)))
  obtain ⟨k', hk2', hs2⟩ := step1 (H := H) hnd hlt hret h2 m1
    (f := fun k => { m1.wX (BitVec.ofNat 5 27) 0 with mem := M', pc := pcAt text psA.toList (k + 1) })
    (fun k hk hok _ => by
      simp only [stlxPat, Shape.okT, Bool.and_eq_true, beq_iff_eq] at hok
      obtain ⟨⟨⟨⟨⟨⟨has, hf⟩, -⟩, ht⟩, hsc⟩, -⟩, ht2⟩ := hok
      have hma : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
          { m1 with pc := pcAt text psA.toList k } psA.toList[k]).mem psA.toList[k].to =
          .ok (A, none) := by
        rw [ht, ctx_mem_reg (by omega) hsc]
        show Except.ok ((m.wX (BitVec.ofNat 5 kd) old).rX (BitVec.ofNat 5 kp) +
          BitVec.ofInt 64 0, none) = _
        rw [rX_wX61 (by omega) (by omega) hpd, hA]; simp
      rw [progStep_stlxr hn hkv (nextAddr_pcAt hnd hk) has hf hma ht2 hnil]
      have hv : ({ m1 with pc := pcAt text psA.toList k } : MState).rX (BitVec.ofNat 5 kv) =
          m.rX (BitVec.ofNat 5 kv) := by
        show (m.wX (BitVec.ofNat 5 kd) old).rX (BitVec.ofNat 5 kv) = _
        exact rX_wX61 (by omega) (by omega) hvd old
      rw [hv, wX_pc]
      simp only [M', m1, mem_wX61])
  rw [← hk2'] at hs2
  -- `CBNZ R27`
  obtain ⟨k'', hk3', hs3⟩ := step1 (H := H) hnd hlt hret h3
    ({ m1.wX (BitVec.ofNat 5 27) 0 with mem := M' })
    (f := fun k => { m1.wX (BitVec.ofNat 5 27) 0 with mem := M', pc := pcAt text psA.toList (k + 1) })
    (fun k hk hok hk3e => by
      have hkk : k = j' - 1 := by omega
      subst hkk
      have ht : psA.toList[j' - 1].to = brA psA[k1 - 1].id := by simpa using htgt
      rw [cbnz27_step hk hnd hok ht hL]
      show (m1.wX (BitVec.ofNat 5 27) 0).rX (BitVec.ofNat 5 27) = 0
      exact rX_wX_self61 (by omega) 0)
  rw [← hk3'] at hs3
  exact pstar_trans61 hs1 (pstar_trans61 hs2 hs3)

end Runs

/-! ## The cases -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K : Nat → Option Nat}

/-- The store of an atomic of group A: `runLoc` writes `storeBytes n z` at `p`, the machine the low
`n` bytes of a register `Z` related to `z` at `p`'s injected address; outside the frame. -/
theorem atom_store61 (hA : AddrAgree E.ι) {mm mm' : Mem} {M : Memory} (hMI : MemInj E.ι mm M)
    (hk : KeysNodup mm) (hsep : SepAt osp E.ι (StkAt E) mm) {p : Ptr} {a : BitVec 64} {n : Nat}
    (hn : n = 8 ∨ n = 4 ∨ n = 1) (ha : E.ι p.blk = some a) {z : Val} {Z : BitVec 64}
    (hz : ValRel E.ι z Z) (hf : Fits (8 * n) z)
    (hw : mm.write p (Arm64.storeBytes n z) = some mm') :
    MemInj E.ι mm' (writeMem M (a + p.off) n (BitVec.ofNat (8 * n) (Z.toNat % 2 ^ (8 * n)))) ∧
      KeysNodup mm' ∧ SepAt osp E.ι (StkAt E) mm' ∧
      ∀ y, StkAt E y → writeMem M (a + p.off) n (BitVec.ofNat (8 * n) (Z.toNat % 2 ^ (8 * n))) y =
        M y := by
  have hc : 8 * n ≤ 8 * n ∨ 8 * n = 1 := .inl (Nat.le_refl _)
  obtain ⟨hM', hk', -, al, hal, hoff, hout⟩ := memInj_storeN hA hMI hk (by omega) ha hz hf hc hw
  have hbs := (storeBytes_relN hA (by omega) hz hf hc).1
  have hwf := write_wf hw (by rw [hbs]; omega)
  exact ⟨hM', hk', hsep.write hk hw,
    fun y hy => hout y fun j hj he => hsep.not_mem hal ha hy (by omega) (by omega)⟩

/-- An operand register other than `ZERO` is `X k` with `k < 31`. -/
theorem objOf?_lt31 {r : Nat} {k : Nat} (hk : k < 32)
    (h : (r = zeroReg ∧ k = 31) ∨ (k < 31 ∧ objX? r = some (BitVec.ofNat 5 k)))
    (hz : REG_R0 + (k : Int) ≠ ARM64.REGZERO) : k < 31 := by
  rcases h with ⟨-, rfl⟩ | ⟨h, -⟩
  · exact absurd rfl hz
  · exact h

/-- `LoweredAtomicExchange{64,32,8} p x mem`: the loop loads the location's old value into `Rd`,
stores `x` and runs once. -/
theorem g61_xchg (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size = 8)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hj : E.pcOf b i = pcAt text psA.toList j)
    (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {n : Nat} {t0 : Ty} {rp rv rd : Int} {r : Nat}
    (hop : atom61? v.op = some (.xchg, n)) (hsz3 : v.args.size = 3)
    (hty : lc.ty v.id = .tuple [t0, .mem]) (hc0 : cls t0 = some (8 * n))
    (hap : argObj lc v 0 = .ok (64, rp)) (hpz : rp ≠ ARM64.REGZERO)
    (hav : argObj lc v 1 = .ok (8 * n, rv)) (hma : memArg lc v 2 = .ok ())
    (hh : lc.home v.id = some (.pair (some r) none)) (hrz : r ≠ zeroReg) (hd : destOK r = true)
    (hor : objOf? r = some rd) (hdp : rd ≠ rp) (hdv : rd ≠ rv)
    (htemp : (lc.temps[v.id]?).join = none)
    (hvs : ManyAt2 psA j (atomPats61 .xchg n rp rv rv rd 0) j')
    (htgt : atomTgt .xchg psA j = true) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) (kSet K r (some (8 * n))) s' osp ∧
      SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  obtain ⟨hnp, -, -, -, -, -, -, -, hcf, -, -, -, hn, hwb, -⟩ := atom61?_facts hop
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hap
  obtain ⟨kp, hkp, rfl, hkkp⟩ := objOf?_some hor0
  have hkp31 := objOf?_lt31 hkp hkkp hpz
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hav
  obtain ⟨kv, hkv, rfl, hkkv⟩ := objOf?_some hor1
  obtain ⟨a2, ha2, hamt, hah2⟩ := memArg_spec hma
  obtain ⟨kd, hkd, rfl, hkkd⟩ := objOf?_some hor
  obtain ⟨hkd31, hk27⟩ : kd < 31 ∧ kd ≠ 27 := by
    rcases hkkd with ⟨h, -⟩ | ⟨h, ho⟩
    · exact absurd h hrz
    · exact ⟨h, fun he => objX?_ne27 ho (by rw [he])⟩
  have hpd : kp ≠ kd := fun h => hdp (by rw [h])
  have hvd : kv ≠ kd := fun h => hdv (by rw [h])
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨mm0, hmm0, hk0, hsep0⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  obtain ⟨X, hX, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkp
  obtain ⟨Y, hY, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkkv
  obtain ⟨x, y, p, mm', hx, hy, hpw, hal, hw, rfl⟩ := stepLoc_rmw61 hl hop nofun nofun
    (arr3 hsz3 ha0 ha1 ha2) (read_mem hl hah2 hamt hmm) hs
  rw [hx] at hX; cases hX
  rw [hy] at hY; cases hY
  simp only [kindF, Atomic.step] at hw ⊢
  have hfy : Fits (widthN n).bits Y := by rw [widthN_bits hn]; exact hyf
  rw [encode_storeBytes hfy, hwb] at hw
  have hbs := (storeBytes_relN hA (by omega) hyv hyf (.inl (Nat.le_refl _))).1
  have hcan : mm.canWrite p n = true := by
    have := canWrite_of_write hw (by rw [hbs]; omega)
    rwa [hbs] at this
  obtain ⟨a, hpa, haeq, hnil⟩ :=
    addr_rel hA hMI hxv hxf (addr_asPtrWord hpw) (by omega : 0 < n) (.inl hcan)
  have haeq' : m.rX (BitVec.ofNat 5 kp) = a + p.off := by simpa using haeq
  obtain ⟨hM', hk', hsep', hP⟩ := atom_store61 hA hMI hk0 hsep0 hn hpa hyv hyf hw
  have hrun := xchg_run (H := H) F.nodup F.lt F.ret hn hkp31 hkv hkd31 hpd hvd hvs htgt m
    haeq' hnil
  rw [pc_eta hm hj] at hrun
  have hsz' : (Ty.int (widthN n)).size = n := by rcases hn with rfl | rfl | rfl <;> rfl
  rw [hsz'] at hal
  have hold := res_rel61 hA hMI hn hc0 hpa hal (read_of_canWrite hcan (by omega))
  simp only [Atomic.result]
  rw [hty, retypeL_pair, retypeL_mem, write_atom61 hh hty (by rw [hc0]; rfl)]
  obtain ⟨hlm, hcore, hsl⟩ := atom_finish (m' := { (m.wX (BitVec.ofNat 5 kd)
      ((readMem m.mem (a + p.off) n).setWidth 64)).wX (BitVec.ofNat 5 27) 0 with
        mem := writeMem m.mem (a + p.off) n
          (BitVec.ofNat (8 * n) ((m.rX (BitVec.ofNat 5 kv)).toNat % 2 ^ (8 * n))),
        pc := pcAt text psA.toList j' })
    hF hsz hm hinv hsi hkd hor hd hrz (fits_retypeL hc0 _)
    (by
      show ValRel E.ι _ (((m.wX (BitVec.ofNat 5 kd) _).wX (BitVec.ofNat 5 27) 0).x _)
      rw [wX_x_ne (by omega) hkd hk27, wX_x_self54 hkd31]
      exact hold)
    hM' hk' hsep' hP (fun t ht => by rw [htemp] at ht; cases ht)
    (fun q h1 h2 _ => by
      show ((m.wX (BitVec.ofNat 5 kd) _).wX (BitVec.ofNat 5 27) 0).x q = m.x q
      rw [wX_x_of_ne h2, wX_x_of_ne h1])
    (by show ((m.wX _ _).wX _ _).v = m.v; rw [wX_fields.2.2.2, wX_fields.2.2.2])
    (by show ((m.wX _ _).wX _ _).sp = m.sp; rw [wX_fields.2.1, wX_fields.2.1])
    (fun _ => by show ((m.wX _ _).wX _ _).nzcv = m.nzcv; rw [wX_fields.2.2.1, wX_fields.2.2.1])
    hj'.symm
  exact ⟨_, hrun, hlm, hcore, hsl⟩

end Cases

end GoFV.Proof.Gen

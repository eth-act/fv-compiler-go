import GoFV.Proof.Obj.MemPanic

variable [GoFV.SSA.Sem.Addrs]

/-!
# Atomics of slice G61 that fault on a nil pointer (`docs/plans/proofs3.md` §6, §9)

A lowered atomic of G61's group A (`atom61?`: the exchanges, adds, compare-and-swaps, ands and
ors, as load-exclusive/store-exclusive loops or LSE instructions) whose `runLoc` step panics: the
only panic of an atomic is `nilFaults`' (the generic atomic, `atomicRoot`, never panics), on its
pointer, argument 0 with no symbol (`nilFaults_atom61`), so the pointer is nil
(`stepLoc_atom61_panic`) and the register that holds it the machine word 0 (`nil_fault_page`).
What `vkind64` accepts of an atomic is `vkind62`'s (`vkind64_eq63`, `vkind63_eq62`: no op of
G64's, no spill or reload), so `vkind61`'s (`vkind62_eq61`) and so `vkind61a`'s (`vkind61_atom`); its Progs (`atomPats61`)
access the location first by `LDAXR*` (the loops), by the LSE instruction (`SWPAL*`, `LDADDAL*`,
`LDORAL*`), or, after `MVN Rv, R27` (`LDCLRAL*`) or `MOV Rold, R27` (`CASAL*`), by the LSE
instruction, and each of these faults in the nil page (`progStep_ldaxr_nil`, `progStep_lse_nil`,
`progStep_casal_nil`; `atom_nil_run`). So `runProg` panics with `nilDeref` as `runLoc` does
(`g64_atomPanic`), and so does `runMach` (`g64_obj_atomPanic`, `obj_panic`).
-/

namespace GoFV.Proof.Obj

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64 GoFV.Asm.CheckObj
open GoFV.Proof.Gen

/-! ## `runLoc`: the step of an atomic that panics -/

section Step

variable {env : Env} {lc : LocCtx} {s : LocState} {v : Value}

/-- The nil fault of an atomic of group A: its pointer (argument 0) is nil, in the nil page. -/
theorem nilFaults_atom61 {ctx : GoFV.SSA.Sem.Ctx} {f : AtomF61} {n : Nat}
    (hop : atom61? v.op = some (f, n)) {argv : List Val} {m : Mem}
    (h : nilFaults true ctx v argv = some m) :
    ∃ x b, argv.head? = some x ∧ Arm64.addr x 0 = some b ∧ b.isNil = true ∧
      b.nilFault = true := by
  unfold nilFaults at h
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · split at h
    · rename_i hany
      simp only [nilAccesses] at hany
      generalize v.op = o at hop hany
      unfold atom61? at hop
      split at hop
      all_goals cases hop
      all_goals (
        simp (config := { decide := true }) only [↓reduceIte, Option.toList,
          List.append_nil] at hany
        cases hx : argv.head? with
        | none => simp [hx] at hany
        | some x =>
          cases hb : Arm64.addr x 0#64 with
          | none => simp [hx, hb] at hany
          | some b =>
            simp [hx, hb] at hany
            exact ⟨x, b, rfl, hb, hany.1, hany.2⟩)
    · cases h
  · cases h

/-- **An atomic of group A whose step panics**: with `nilDeref`, its pointer (argument 0, offset
0) read as a nil pointer in the nil page. -/
theorem stepLoc_atom61_panic {f : AtomF61} {n : Nat} (hop : atom61? v.op = some (f, n))
    {e : Panic} {mm : Mem} (h : stepLoc env lc s v = .panic e mm) :
    e = .nilDeref ∧ ∃ a0 x b, v.args[0]? = some a0 ∧ s.read lc a0 = .ok x ∧
      Arm64.addr x 0 = some b ∧ b.isNil = true ∧ b.nilFault = true := by
  obtain ⟨h1, h2, h3, h4, h5, -, -, -, -, -, -, -, -, -, -, -, g, hg, -⟩ := atom61?_facts hop
  obtain ⟨argv, hmap, hev⟩ := stepLoc_panic_eval h1 h2 h3 h4 h5 h
  rw [evalOpL_atom61 hop] at hev
  cases hnf : nilFaults true lc.ctx v argv with
  | none =>
    rw [arm64Op_atom61 hop hg hnf] at hev
    exact absurd hev atomicRoot_ne_panic
  | some m =>
    have hp : arm64Op true env lc.ctx s.fr v argv (lc.ty v.id) = .panic .nilDeref m := by
      unfold arm64Op; rw [hnf]
    rw [hp] at hev
    cases hev
    refine ⟨rfl, ?_⟩
    obtain ⟨x, b, hxh, hb, hbn, hbf⟩ := nilFaults_atom61 hop hnf
    cases ha : v.args.toList.head? with
    | none =>
      obtain ⟨hlen, -⟩ := mapM_res hmap
      have hl : v.args.toList = [] := by
        cases hl : v.args.toList with
        | nil => rfl
        | cons a l => rw [hl] at ha; cases ha
      rw [hl] at hlen
      cases argv with
      | nil => cases hxh
      | cons _ _ => simp at hlen
    | some a0 =>
      obtain ⟨x', hx, hxh'⟩ := mapM_read_head hmap ha
      rw [hxh] at hxh'
      cases hxh'
      have h0 : v.args.toList[0]? = some a0 := by rw [← List.head?_eq_getElem?]; exact ha
      exact ⟨a0, x, b, by simpa using h0, hx, hb, hbn, hbf⟩

end Step

/-! ## The machine: the first access of an atomic's Progs faults -/

section Machine

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64}

/-- A Prog matching `pat` after no-ops whose step faults in the nil page: `runProg` panics there
with `nilDeref`. -/
theorem oneAt2_fault (hnd : (psA.toList.map (·.id)).Nodup) (hlt : ∀ p ∈ psA.toList, p.id < 2 ^ 32)
    (hret : ∀ p ∈ psA.toList, (Link.byId sym text az ez psA.toList).addr p.id ≠ some ret)
    {pat : Pat} {j j' : Nat} (h : OneAt2 psA j pat j') (m : MState)
    (hf : ∀ k (hk : k < psA.toList.length), pat.ok psA.toList[k] = true →
      ∃ a, progStep (Link.byId sym text az ez psA.toList) psA.toList[k]
        { m with pc := pcAt text psA.toList k } = .error (.nilPage a)) :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret
        { m with pc := pcAt text psA.toList j } m' ∧
      PPanics H (Link.byId sym text az ez psA.toList) psA.toList ret m' .nilDeref := by
  obtain ⟨k, -, hk, hok, hstar⟩ := pstar_oneAt2 (H := H) hnd hlt hret h m
  obtain ⟨a, ha⟩ := hf k hk hok
  refine ⟨_, hstar, fun hr => hret _ (List.getElem_mem hk) ?_, .inl ⟨_, a,
    progAt?_pcAt hnd hlt hk, ha, rfl⟩⟩
  rw [addr_pcAt hk]
  exact congrArg some hr

/-- The Progs of an atomic of group A of family `f` (`atomPats61`, the pointer in `X kp`, the
operands in `X kv`, `X kn`, the result in `X kd`) with the pointer in the nil page: they run to
their first access, which faults (`PPanics`). -/
theorem atom_nil_run (hnd : (psA.toList.map (·.id)).Nodup)
    (hlt : ∀ p ∈ psA.toList, p.id < 2 ^ 32)
    (hret : ∀ p ∈ psA.toList, (Link.byId sym text az ez psA.toList).addr p.id ≠ some ret)
    {f : AtomF61} {n kp kv kn kd : Nat} {rt : Int} (hn : n = 8 ∨ n = 4 ∨ n = 1)
    (hadd : f = .addV → n ≠ 1) (hcas : (f = .cas ∨ f = .casV ∨ f = .add) → n ≠ 1)
    (hkp : kp < 31) (hp27 : kp ≠ 27) (hkv : kv < 32) (hkn : kn < 32) (hkd : kd < 32) {j j' : Nat}
    (hvs : ManyAt2 psA j (atomPats61 f n (REG_R0 + kp) (REG_R0 + kv) (REG_R0 + kn) (REG_R0 + kd)
      rt) j')
    (m : MState) (hnil : nilPage (m.rX (BitVec.ofNat 5 kp) + BitVec.ofInt 64 0) = true) :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret
        { m with pc := pcAt text psA.toList j } m' ∧
      PPanics H (Link.byId sym text az ez psA.toList) psA.toList ret m' .nilDeref := by
  -- `LDAXR* (Rp), Rd` first
  have ldax : ∀ {j1 kd' : Nat}, kd' < 32 →
      OneAt2 psA j (ldaxPat n (REG_R0 + kp) (REG_R0 + kd')) j1 →
      ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret
          { m with pc := pcAt text psA.toList j } m' ∧
        PPanics H (Link.byId sym text az ez psA.toList) psA.toList ret m' .nilDeref :=
    fun hkd' h1 => oneAt2_fault (H := H) hnd hlt hret h1 m fun k hk hok => by
      simp only [ldaxPat, Pat.ofShape, Shape.ok, Bool.and_eq_true, beq_iff_eq] at hok
      obtain ⟨⟨⟨⟨⟨⟨has, hf⟩, -⟩, ht⟩, hsc⟩, -⟩, -⟩ := hok
      exact ⟨_, progStep_ldaxr_nil hn hkd' (nextAddr_pcAt hnd hk) has
        (by rw [hf]; exact ctx_mem_reg (by omega) hsc) ht hnil⟩
  -- an LSE instruction `op Rs, (Rp), Rt` of family `g`, from a state `q` with `q`'s pointer
  have lse : ∀ {g : AtomF61} {j0 j1 ks kt : Nat} (q : MState),
      (g = .xchgV ∧ (n = 8 ∨ n = 4 ∨ n = 1) ∨ g = .addV ∧ (n = 8 ∨ n = 4) ∨
        g = .andV ∧ (n = 8 ∨ n = 4 ∨ n = 1) ∨ g = .orV ∧ (n = 8 ∨ n = 4 ∨ n = 1)) →
      ks < 32 → kt < 32 → q.rX (BitVec.ofNat 5 kp) = m.rX (BitVec.ofNat 5 kp) →
      OneAt2 psA j0 (lsePat (lse61 g n) (REG_R0 + ks) (REG_R0 + kp) (REG_R0 + kt)) j1 →
      ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret
          { q with pc := pcAt text psA.toList j0 } m' ∧
        PPanics H (Link.byId sym text az ez psA.toList) psA.toList ret m' .nilDeref :=
    fun q hg hks hkt hq h1 => oneAt2_fault (H := H) hnd hlt hret h1 q fun k hk hok => by
      simp only [lsePat, Shape.okT, Bool.and_eq_true, beq_iff_eq] at hok
      obtain ⟨⟨⟨⟨⟨⟨has, hf⟩, -⟩, ht⟩, hsc⟩, -⟩, ht2⟩ := hok
      refine ⟨_, progStep_lse_nil hg hks hkt (nextAddr_pcAt hnd hk) has hf
        (by rw [ht]; exact ctx_mem_reg (by omega) hsc) ht2 ?_⟩
      show nilPage (q.rX (BitVec.ofNat 5 kp) + BitVec.ofInt 64 0) = true
      rw [hq]; exact hnil
  cases f with
  | xchg | add | andL | orL | cas =>
    simp only [atomPats61] at hvs
    obtain ⟨k1, h1, -⟩ := hvs
    first
      | exact ldax hkd h1
      | exact ldax (kd' := 27) (by omega) h1
  | xchgV =>
    simp only [atomPats61] at hvs
    obtain ⟨k1, h1, -⟩ := hvs
    exact lse m (.inl ⟨rfl, hn⟩) hkv hkd rfl h1
  | addV =>
    simp only [atomPats61] at hvs
    obtain ⟨k1, h1, -⟩ := hvs
    have hn' : n = 8 ∨ n = 4 := by have := hadd rfl; omega
    exact lse m (.inr (.inl ⟨rfl, hn'⟩)) hkv hkd rfl h1
  | orV =>
    simp only [atomPats61] at hvs
    obtain ⟨k1, h1, -⟩ := hvs
    exact lse m (.inr (.inr (.inr ⟨rfl, hn⟩))) hkv hkd rfl h1
  | andV =>
    -- `MVN Rv, R27`; `LDCLRAL R27, (Rp), Rd`
    simp only [atomPats61] at hvs
    obtain ⟨k1, h1, k2, h2, -⟩ := hvs
    obtain ⟨k, hk', hs1⟩ := step1 (H := H) hnd hlt hret h1 m
      (f := fun k => { m.wX (BitVec.ofNat 5 27) (~~~(m.rX (BitVec.ofNat 5 kv))) with
        pc := pcAt text psA.toList (k + 1) })
      (fun k hk hok _ => by
        simp only [Pat.ofShape, Shape.ok, Bool.and_eq_true, beq_iff_eq] at hok
        obtain ⟨⟨⟨⟨⟨⟨has, hf⟩, -⟩, ht⟩, -⟩, -⟩, -⟩ := hok
        rw [progStep_un32 (op := .ARM64MVN) (kd := 27) rfl hkv (by omega) (nextAddr_pcAt hnd hk)
          has hf (by rw [ht]; rfl), wX_pc]
        rfl)
    rw [← hk'] at hs1
    obtain ⟨m', hs2, hp⟩ := lse (m.wX (BitVec.ofNat 5 27) (~~~(m.rX (BitVec.ofNat 5 kv))))
      (.inr (.inr (.inl ⟨rfl, hn⟩))) (ks := 27) (by omega) hkd
      (rX_wX61 (by omega) (by omega) hp27 _) h2
    exact ⟨m', pstar_trans61d hs1 hs2, hp⟩
  | casV =>
    -- `MOVD`/`MOVW Ro, R27`; `CASAL R27, (Rp), Rn`
    simp only [atomPats61] at hvs
    obtain ⟨k1, h1, k2, h2, -⟩ := hvs
    have hn' : n = 8 ∨ n = 4 := by have := hcas (.inr (.inl rfl)); omega
    obtain ⟨W, hs1⟩ : ∃ W : BitVec 64,
        PStar H (Link.byId sym text az ez psA.toList) psA.toList ret
          { m with pc := pcAt text psA.toList j }
          { m.wX (BitVec.ofNat 5 27) W with pc := pcAt text psA.toList k1 } := by
      rcases hn' with rfl | rfl
      · obtain ⟨k, hk', hs⟩ := step1 (H := H) hnd hlt hret h1 m
          (f := fun k => { m.wX (BitVec.ofNat 5 27) (m.rX (BitVec.ofNat 5 kv)) with
            pc := pcAt text psA.toList (k + 1) })
          (fun k hk hok _ => by
            simp only [Pat.ofShape, Shape.ok, Bool.and_eq_true, beq_iff_eq, ↓reduceIte] at hok
            obtain ⟨⟨⟨⟨⟨⟨has, hf⟩, -⟩, ht⟩, -⟩, -⟩, -⟩ := hok
            rw [progStep_movReg (kd := 27) hkv (by omega) (nextAddr_pcAt hnd hk) has hf
              (by rw [ht]; rfl), wX_pc]
            rfl)
        rw [← hk'] at hs
        exact ⟨_, hs⟩
      · obtain ⟨k, hk', hs⟩ := step1 (H := H) hnd hlt hret h1 m
          (f := fun k => { m.wX (BitVec.ofNat 5 27)
              (ProgOp.sextTo64 4 (m.rX (BitVec.ofNat 5 kv))) with
            pc := pcAt text psA.toList (k + 1) })
          (fun k hk hok _ => by
            simp only [Pat.ofShape, Shape.ok, Bool.and_eq_true, beq_iff_eq] at hok
            obtain ⟨⟨⟨⟨⟨⟨has, hf⟩, -⟩, ht⟩, -⟩, -⟩, -⟩ := hok
            rw [progStep_ext (n := 4) (sg := true) (kd := 27) hkv (by omega)
              (nextAddr_pcAt hnd hk) (by rw [has]; rfl) hf (by rw [ht]; rfl), wX_pc]
            rfl)
        rw [← hk'] at hs
        exact ⟨_, hs⟩
    obtain ⟨m', hs2, hp⟩ := oneAt2_fault (H := H) hnd hlt hret h2 (m.wX (BitVec.ofNat 5 27) W)
      fun k hk hok => by
        simp only [lsePat, Shape.okT, Bool.and_eq_true, beq_iff_eq] at hok
        obtain ⟨⟨⟨⟨⟨⟨has, hf⟩, -⟩, ht⟩, hsc⟩, -⟩, ht2⟩ := hok
        refine ⟨_, progStep_casal_nil hn' (ks := 27) (by omega) hkn (nextAddr_pcAt hnd hk) has
          (by rw [hf]; rfl) (by rw [ht]; exact ctx_mem_reg (by omega) hsc) ht2 ?_⟩
        show nilPage ((m.wX (BitVec.ofNat 5 27) W).rX (BitVec.ofNat 5 kp) + BitVec.ofInt 64 0) =
          true
        rw [rX_wX61 (by omega) (by omega) hp27]; exact hnil
    exact ⟨m', pstar_trans61d hs1 hs2, hp⟩

end Machine

/-! ## Slice G64 -/

/-- **An atomic of slice G64 that faults**: from a `LocMatch`ed P0 state, an atomic of group A
whose `runLoc` step panics (with `nilDeref`, `stepLoc_atom61_panic`) is matched by its Progs up to
their first access, which faults in the nil page (`PPanics`). -/
theorem g64_atomPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm : Mem} {osp : Bool}
    (hc : checkG64L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : (atom61? v.op).isSome = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s osp) (hs : stepLoc env lc s v = .panic e mm) :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  obtain ⟨⟨f, n⟩, hop⟩ := Option.isSome_iff_exists.1 hop
  obtain ⟨rfl, a0, x, b0, ha0, hx, hb0, hbn, hpf⟩ := stepLoc_atom61_panic hop hs
  obtain ⟨hnp, -, -, -, -, -, -, -, -, -, -, hen, hn, -, hadd, hcas, -⟩ := atom61?_facts hop
  refine ⟨rfl, ?_⟩
  cases hl0 : lc.ctx.f.lowered with
  | false =>
    rcases nl30_ops (checkNL30_of_64L hl0 hc) hbid hb hi hv hen with h | h | h | h <;>
      rw [h] at hop <;> cases hop
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, -⟩ :=
    checkG64L_spec hl0 hc
  obtain ⟨b, j, js, e', next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk, vkind64_eq63 (by
      cases h : qop64 v.op
      · rfl
      · simp only [qop64, Bool.or_eq_true, beq_iff_eq] at h
        rcases h with ((((h | h) | h) | h) | h) | h <;> rw [h] at hop <;> simp [atom61?] at hop),
    vkind63_eq62 (fun h => by rw [h] at hop; simp [atom61?] at hop)
      (fun h => by rw [h] at hop; simp [atom61?] at hop),
    vkind62_eq61 fun h => by rw [h] at hop; simp [atom61?] at hop] at hkd
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have hR : KRead c.cx.lc v (kAt c.cx.lc kt bid blk i).get := kread_of_reads hreads
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  obtain ⟨mm0, -, hMI⟩ := hm.mem
  -- the pointer, nil in a register `X kp`: the machine word 0, in the nil page
  have hptr : ∀ {rp : Int}, argObj c.cx.lc v 0 = .ok (64, rp) → rp ≠ ARM64.REGZERO →
      rp ≠ r27A → ∃ kp : Nat, kp < 31 ∧ kp ≠ 27 ∧ rp = REG_R0 + kp ∧
        nilPage (m.rX (BitVec.ofNat 5 kp) + BitVec.ofInt 64 0) = true := by
    intro rp hap hpz hp27
    obtain ⟨a0', r0, ha0', hah0, hor0, hca0⟩ := argObj_spec hap
    rw [ha0] at ha0'
    cases ha0'
    obtain ⟨kp, hkp, rfl, hkkp⟩ := objOf?_some hor0
    obtain ⟨X, hX, hxv, hxf⟩ :=
      arg_rel hA hl hm hinv.core hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkp
    rw [hx] at hX
    cases hX
    refine ⟨kp, objOf?_lt31 hkp hkkp hpz, fun h => hp27 (by rw [h]; rfl), rfl,
      nil_fault_page hMI.nil hxv hxf hb0 hbn hb0 hpf⟩
  have hreg : ∀ {i' c' : Nat} {r : Int}, argObj c.cx.lc v i' = .ok (c', r) →
      ∃ k : Nat, k < 32 ∧ r = REG_R0 + k := fun h => by
    obtain ⟨_, _, _, _, hor', _⟩ := argObj_spec h
    obtain ⟨k, hk, rfl, -⟩ := objOf?_some hor'
    exact ⟨k, hk, rfl⟩
  cases vkind61_atom hop hkd with
  | rmw hop' _ _ _ _ _ _ hap hpr hpz hav _ _ _ _ _ hor =>
    rw [hop] at hop'
    cases hop'
    obtain ⟨kp, hkp, hp27, rfl, hnil⟩ := hptr hap hpz hpr
    obtain ⟨kv, hkv, rfl⟩ := hreg hav
    obtain ⟨kd, hkd32, rfl, -⟩ := objOf?_some hor
    obtain ⟨m', hstar, hpp⟩ := atom_nil_run (H := H) F.nodup F.lt F.ret hn hadd hcas hkp hp27
      hkv hkv hkd32 hvs m hnil
    rw [pc_eta hm hj] at hstar
    exact ⟨m', hstar, hpp⟩
  | cas hop' _ _ _ _ _ _ hap hpr hpz hao _ han _ _ _ _ _ hor =>
    rw [hop] at hop'
    cases hop'
    obtain ⟨kp, hkp, hp27, rfl, hnil⟩ := hptr hap hpz hpr
    obtain ⟨ko, hko, rfl⟩ := hreg hao
    obtain ⟨kn, hkn, rfl⟩ := hreg han
    obtain ⟨kd, hkd32, rfl, -⟩ := objOf?_some hor
    obtain ⟨m', hstar, hpp⟩ := atom_nil_run (H := H) F.nodup F.lt F.ret hn hadd hcas hkp hp27
      hko hkn hkd32 hvs m hnil
    rw [pc_eta hm hj] at hstar
    exact ⟨m', hstar, hpp⟩
  | sel0 _ h => rw [h] at hop; cases hop
  | sel1 _ h => rw [h] at hop; cases hop

/-- **An atomic of slice G64 that faults, down to the machine words**: machine steps of the
linked code to a state that panics with `nilDeref` (the first access's nil-page fault,
`MPanics`). -/
theorem g64_obj_atomPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState} {m : MState}
    {e : Panic} {mm : Mem} {osp : Bool} {spills : Array Spill} {o : ObjIn} {otab : Tab}
    {base : BitVec 64} {code : Code} {retM : BitVec 64} {t : MState}
    (hc : checkG64L lc ps bstart g = .ok (tab, kt))
    (hE : G28Env lc g L ps (endP L.text ps.toList) tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : (atom61? v.op).isSome = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s osp) (hs : stepLoc env lc s v = .panic e mm)
    (hO : ObjEnv ps spills o otab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hHP : HookPanicMap H L ps.toList (ObjEnv.map otab ps L base))
    (hR : ObjRel (ObjEnv.map otab ps L base) m t) (hX : X27At otab L ps.toList m t)
    (hic : ∀ u, PStar H L ps.toList (endP L.text ps.toList) m u → ICallOut L ps.toList u) :
    e = .nilDeref ∧ ∃ t', MStar H code retM t t' ∧ MPanics H code retM t' e := by
  obtain ⟨he, m', hp, hpp⟩ := g64_atomPanic (H := H) hc hE hbid hb hi hv hop hm hinv hs
  obtain ⟨t1, ht1, hR1, hI1, hX1⟩ :=
    obj_star hO hH hp hR hX (locMatch_inv hE.env.env.env.env hm) hic
  obtain ⟨t2, ht2, hpan⟩ := obj_panic hO hHP hR1 hX1 (hI1.resolve_right hpp.1) hpp
  exact ⟨he, t2, mstar_trans ht1 ht2, hpan⟩

end GoFV.Proof.Obj

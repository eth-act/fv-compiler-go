import GoFV.Proof.Gen.G48a
import GoFV.Proof.Gen.G53S
import GoFV.Proof.Gen.G57
import GoFV.Proof.Gen.Spec48

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G48 of the genssa validator: stack arguments and stack results
(`docs/plans/proofs3.md` §8, item 7)

`checkG48 lc` (`GoFV/Gen/Check48.lean`) is G57 with the static calls whose ABI assigns inputs or
outputs to the stack (`callRegsS`) and the accesses off `SP` at `[8, outargsSize)` that pass those
values through the outgoing area. They exist only when the activation's `outargs` block sits at
`SP` (`MatchEnv.outSP`, G48b): the theorems here hold in that mode (`hosp : E.outSP = true`), in
the separation `SepFromW` (`G3Inv … E.outSP`), and keep `SPInv` (`G53S.lean`).

* An access off `SP` is G48a's lemma for its shape (`g48_spStore`, `g48_spLoad`, `g48_spStp`,
  `g48_spStpw`, `g48_spFstpd`, `g48_spFStore`, `g48_spFLoad`). Its base is an `SP` value homed in
  the Go register `SP` at a 64-bit shape (`spBase48`), whose read `SPInv` relates to the machine's
  `SP` (`sp_base48`). A load reads valid bytes (G3's premise in `G54Pre`, which G57 takes:
  `G3Pre`'s, `FLoadPre`).
* A static call with stack inputs or outputs is G2's (`g2_callAt`) on the ABI without them
  (`callRegsS`), with the callee contract `CallOKStk` (trusted, next to `CallOKS`; STATUS
  Assumptions): `CallSpecS` at the register arguments and results `callRegsS` gives. The caller
  has stored the stack arguments at `SP + off` (`off ≥ 8`, the accesses above) before the call;
  the callee reads them and writes its stack results there (Phase 1's `decodeArgs` /
  `encodeResults` on `outargs`), where the caller loads them after the call.
* The upper-bit table (`UOKL`): a store keeps the X registers (`m'.x = m.x`) and the table drops
  at most entries (`uokl_x48`); an integer load writes its register's X register (`uokl_spLoad48`,
  G35's `ld_uokl` for a narrow load with an entry); a float load writes no X register.

`g48_value` takes G57's premise `G54Pre`, the contracts of the mode `true` through `E.outSP`, and
`CallOKStk`; `g48_initMem`, `g48_term` keep `SPInv` (the function homes only `SP` values in the Go
register `SP`: `spHomes48`, the checker's form of `SPHomes`); `g48_nilPanic`, `g48_boundsPanic`
are G57's statements over `checkG48`.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The contract -/

/-- **The callee contract at a static call with stack arguments or results** (trusted,
semantics3 §6; `docs/proofs/STATUS.md` Assumptions; a function whose `outargs` block sits at `SP`):
`CallAtM true` (`CallSpecS`) at the register arguments and results of the ABI without its
stack-assigned inputs and outputs (`callRegsS`). Go's arm64 ABI places those at their
`ABIParam.offset` in the caller's outgoing area, above the fixed frame word (`FixedFrameSize = 8`,
`cmd/compile/internal/abi/abiutils.go`); the callee reads its stack arguments and writes its stack
results there, at `SP + off` of its caller's `SP` (`runtime/asm_arm64.s`, `cmd/internal/obj/arm64/
obj7.go`'s prologue saves `LR` at the callee's own frame, below that `SP`). -/
def CallOKStk (H : Hooks) (E : MatchEnv) (g : G2In) (L : Link) (lc : LocCtx) (s s' : LocState)
    (v : Value) (m : MState) : Prop :=
  v.op = .ARM64CALLstatic → ∀ name abi cabi ins outs,
    callOf? lc.ctx.tabs v.aux = some (name, abi, cabi) →
    callRegsS cabi = .ok (ins, outs) → CallAtM true H E g L lc s s' v m name abi ins outs

/-! ## The base of an access off `SP` -/

/-- The read of an access's base homed in the Go register `SP` at a 64-bit shape (`spBase48`)
relates to the machine's `SP` when the `outargs` block sits at `SP` (`SPInv`), and fits 64 bits. -/
theorem sp_base48 {E : MatchEnv} {lc : LocCtx} {s : LocState} {v : Value}
    {K : Nat → Option Nat} (hl : lc.ctx.f.lowered = true) (hA : AddrAgree E.ι)
    (hsp : SPInv E s) (hosp : E.outSP = true)
    (hregs : ∀ r x c, r ≠ zeroReg → s.regs[r]? = some x → K r = some c → Fits c x)
    (hR : KRead lc v K) (hnp : v.op ≠ .Phi) (hb : spBase48 lc v = true) :
    ∀ a x, v.args[0]? = some a → s.read lc a = .ok x → ValRel E.ι x E.sp ∧ Fits 64 x := by
  obtain ⟨a0, ha0, hh, hc⟩ := spBase48_spec hb
  intro a x ha hx
  rw [ha0] at ha
  cases ha
  rw [read_reg hl hh hc] at hx
  cases hx
  have hz : spReg ≠ zeroReg := by decide
  have hK : K spReg = some 64 := kread_arg hR hnp ha0 hh hc hz
  have hreg : s.reg (lc.ty a0) spReg = s.regs[spReg]?.getD .poison := by
    simp [LocState.reg, spReg, zeroReg]
  refine ⟨?_, fits_retypeL hc _⟩
  rw [hreg]
  cases hy : s.regs[spReg]? with
  | none => exact valRel_retypeL hA hc trivial trivial
  | some y => exact valRel_retypeL hA hc (hregs _ _ _ hz hy hK) ((hsp hosp).2 y hy)

/-! ## The upper-bit table -/

/-- The ops of G48's stores and float loads: none writes an X register. -/
def opsX48 : List Op :=
  [.ARM64MOVDstore, .ARM64MOVWstore, .ARM64MOVHstore, .ARM64MOVBstore, .ARM64STP, .ARM64STPW,
    .ARM64FSTPD, .ARM64FMOVSstore, .ARM64FMOVDstore, .ARM64FMOVSload, .ARM64FMOVDload]

/-- Across a value of `opsX48` that keeps the X registers, the table keeps at most its entries. -/
theorem uokl_x48 {lc : LocCtx} {v : Value} {m m' : MState} {L : List (Nat × Nat × Bool)}
    (hop : v.op ∈ opsX48) (hx : m'.x = m.x) (hL : UOKL m L) : UOKL m' (uStep35 lc L v) := by
  have h := List.all_eq_true.1 (show opsX48.all (fun o => (loadOp? o).isNone &&
    (loadIdxOp? o).isNone && o != .ARM64LDP && o != .Select0 && o != .Select1 &&
    o != .ARM64MOVDnop && o != .ARM64MOVDreg) = true by decide) _ hop
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hl, hi⟩, hp1⟩, hp2⟩, hp3⟩, h1⟩, h2⟩ := h
  have hp : pairOp35 lc v = false := by
    simp only [opsX48, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with h | h | h | h | h | h | h | h | h | h | h <;> simp [pairOp35, h]
  intro e he
  rw [uStep35_other (ldEntry35_none hl) hp] at he
  unfold uStep34 at he
  split at he
  · exact uok_of_x hx (hL e (List.mem_filter.1 he).1)
  · have hue : uEntry lc v = none := by simp [uEntry, narrowLd?, hl, hi]
    rw [uStepL_other hue h1 h2] at he
    cases he

/-- Across an integer load without an aux that writes the zero or sign extension of its bytes to
the X register of its home, the table: G35's `ld_uokl` for a narrow load with an entry, else the
entries of the other registers or none. -/
theorem uokl_spLoad48 {lc : LocCtx} {v : Value} {m m' : MState} {L : List (Nat × Nat × Bool)}
    {as : As} {n : Nat} {sg : Bool} {c : Nat} {rd : Int} {kd : Nat} {Y : BitVec (8 * n)}
    (hop : loadOp? v.op = some (as, n, sg)) (haux : v.aux = none)
    (hro : resObj lc v = .ok (c, rd)) (hrd : rd = GoFV.Asm.ARM64.REG_R0 + kd)
    (hx : m'.x = (m.wX (BitVec.ofNat 5 kd)
      (if sg then ProgOp.sextTo64 n (Y.setWidth 64) else Y.setWidth 64)).x)
    (hL : UOKL m L) : UOKL m' (uStep35 lc L v) := by
  by_cases h0 : ldEntry35 lc v = none
  · obtain ⟨r, hvh, -, hor, -⟩ := resObj_spec hro
    rw [hrd] at hor
    have hk := keepsX_wX hor hx
    have hr := regHome?_eq.2 hvh
    have hops : v.op ≠ .ARM64LDP ∧ v.op ≠ .Select0 ∧ v.op ≠ .Select1 ∧
        v.op ≠ .ARM64MOVDnop ∧ v.op ≠ .ARM64MOVDreg := by
      rcases loadOp?_op hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
        rw [h] <;> exact ⟨nofun, nofun, nofun, nofun, nofun⟩
    obtain ⟨hp1, hp2, hp3, h1, h2⟩ := hops
    have hp : pairOp35 lc v = false := by
      rcases loadOp?_op hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
        simp [pairOp35, h]
    rw [uStep35_other h0 hp]
    unfold uStep34
    split
    · intro e he
      obtain ⟨heL, hne⟩ := List.mem_filter.1 he
      rw [hr] at hne
      refine uokl_filter hL hk e (List.mem_filter.2 ⟨heL, ?_⟩)
      simp only [bne_iff_ne, ne_eq, Option.some.injEq] at hne
      exact bne_iff_ne.2 fun h => hne h.symm
    · have hue : uEntry lc v = none := by
        by_cases has : as = .MOVD
        · simp [uEntry, narrowLd?, hop, has]
        · have hn : narrowLd? lc v = some (n, sg) := by simp [narrowLd?, hop, has, haux]
          have has' : (as != .MOVD) = true := bne_iff_ne.2 has
          unfold ldEntry35 at h0
          unfold uEntry
          rw [hop, hr] at h0
          rw [hn, hr]
          cases hc : cls (lc.ty v.id) with
          | none => rfl
          | some c' =>
            rw [hc] at h0
            simp only [has', Bool.true_and] at h0 ⊢
            split at h0
            · cases h0
            · rename_i hcond
              exact ite_eq_right hcond
      rw [uStepL_other hue h1 h2]
      intro e he
      cases he
  · exact ld_uokl (.inr h0) hop hro hrd hx hL

/-! ## One value -/

/-- One access off `SP` (`VKsp48`), its base homed in the Go register `SP` (`spBase48`), in a
function whose `outargs` block sits at `SP` (`SPInv`, `hosp`): G48a's lemma for its shape, the
class table after it, the upper-bit table after it. -/
theorem vk48_sp {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)} {osp : Bool}
    (hE : G49Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hcf : checkFrame lc g = .ok ())
    (hax : v.aux = none) (hb : spBase48 lc v = true) (hVK : VKsp48 lc v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s osp) (hL : UOKL m L)
    (hpre : G53Pre lc s v) (hsp : SPInv E s) (hosp : E.outSP = true)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E s' bid (i + 1) m' ∧ G3Inv E lc (kStep lc K v) s' osp ∧
      UOKL m' (uStep35 lc L v) := by
  obtain ⟨hlcE, -, -, -, -, -, -, -, -, -, hF⟩ := hE.env.env.env.env.env
  have hsz := slot_sizes hlcE hcf hinv.slots
  have hR := kread_of_reads hreads
  obtain ⟨mm, hmm, hkn, hsep⟩ := hinv.core.mem
  have hbase := fun hnp => sp_base48 F.lowered F.addr hsp hosp hinv.core.regs hR hnp hb
  have hpre3 : G3Pre lc s v := hpre.1.1.1.1.1.1.1.1.1.1.1.1
  have hfl : FLoadPre lc s v := hpre.1.1.1.1.1.2
  -- a store: the memory only, the X registers kept
  have store : ∀ m' mm', lc.home v.id = none → v.op ∈ opsX48 →
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' →
      LocMatch E s' bid (i + 1) m' → s' = { s with mem := .mem mm' } → KeysNodup mm' →
      SepAt osp E.ι (StkAt E) mm' → m'.x = m.x →
      ∃ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
        LocMatch E s' bid (i + 1) m' ∧ G3Inv E lc (kStep lc K v) s' osp ∧
        UOKL m' (uStep35 lc L v) := by
    intro m' mm' hhn hops h1 h2 h3 h4 h5 h6
    subst h3
    refine ⟨m', h1, h2, ⟨(⟨hinv.core.regs, ⟨mm', rfl, h4, h5⟩⟩ :
      CoreInv E.ι (StkAt E) K.get { s with mem := .mem mm' } osp).mono
        (knext_same (knext_kStep fun _ => (hs_none hhn).noRegs)
          (Or.inr fun _ _ => by rw [hhn]; nofun)), hinv.slots⟩, uokl_x48 hops h6 hL⟩
  -- a load: the memory and the slots kept
  have load : ∀ m', s'.mem = s.mem → s'.slots = s.slots →
      (∀ r x c, r ≠ zeroReg → s'.regs[r]? = some x → (kStep lc K v).get r = some c → Fits c x) →
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' →
      LocMatch E s' bid (i + 1) m' → UOKL m' (uStep35 lc L v) →
      ∃ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
        LocMatch E s' bid (i + 1) m' ∧ G3Inv E lc (kStep lc K v) s' osp ∧
        UOKL m' (uStep35 lc L v) := by
    intro m' hmem hsl hregs h1 h2 h3
    refine ⟨m', h1, h2, ⟨⟨hregs, ⟨mm, hmem.trans hmm, hkn, hsep⟩⟩, fun k y hy => ?_⟩, h3⟩
    rw [hsl] at hy
    exact hinv.slots k y hy
  cases hVK with
  | load hop hsz2 _ hma hro hc =>
    obtain ⟨m', h1, h2, hmem, hsl, hregs, kd', Y, hrd, hx⟩ := g48_spLoad (H := H) F hm hmm hkn
      hinv.core.regs (knext_kStep (K := K) fun _ => (hs_res hro).noRegs)
      (hbase (loadOp?_ne_phi hop)) hj hj'
      (fun a x ha hx => by
        obtain ⟨p, mm2, bs, hsym, hmm2, hr, h01⟩ := hpre3.2.1 _ _ _ hop a x ha hx
        rw [hmm] at hmm2
        cases hmm2
        refine ⟨p, bs, ?_, hr, h01⟩
        rw [← hsym]; unfold symAddr; rw [hax])
      hop hsz2 hax hma hro hc
      (fun p hp => by
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := plain_spec hp
        exact ⟨h1, beq_iff_eq.mp h2, h3, beq_iff_eq.mp h4, h5, h6, h7⟩)
      hvs htemp hs
    exact load m' hmem hsl hregs h1 h2 (uokl_spLoad48 hop hax hro hrd hx hL)
  | store hop hsz3 hmt hhn _ hso hma hc =>
    obtain ⟨m', mm', h1, h2, h3, h4, h5, h6⟩ := g48_spStore (H := H) F hF hsz hm hmm hkn hsep
      hinv.core.regs hR (hbase (storeOp?_ne_phi hop)) hj hj' hop hsz3 hax hmt hhn hso hma hc
      (fun p hp => by
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := plain_spec hp
        exact ⟨h1, beq_iff_eq.mp h2, h3, beq_iff_eq.mp h4, h5, h6, h7⟩)
      hvs htemp hs
    refine store m' mm' hhn ?_ h1 h2 h3 h4 h5 h6
    rcases storeOp?_op hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide
  | stp hop hsz4 hmt hhn _ hxo hyo hma =>
    obtain ⟨m', mm', h1, h2, h3, h4, h5, h6⟩ := g48_spStp (H := H) F hF hsz hm hmm hkn hsep
      hinv.core.regs hR (hbase (by rw [hop]; nofun)) hj hj' hop hsz4 hax hmt hhn hxo hyo hma hvs
      htemp hs
    exact store m' mm' hhn (by rw [hop]; decide) h1 h2 h3 h4 h5 h6
  | stpw hop hsz4 hmt hhn _ hxo hyo hcx hcy hma =>
    obtain ⟨m', mm', h1, h2, h3, h4, h5, h6⟩ := g48_spStpw (H := H) F hF hsz hm hmm hkn hsep
      hinv.core.regs hR (hbase (by rw [hop]; nofun)) hj hj' hop hsz4 hax hmt hhn hxo hyo hcx hcy
      hma hvs htemp hs
    exact store m' mm' hhn (by rw [hop]; decide) h1 h2 h3 h4 h5 h6
  | fstpd hop hsz4 hmt hhn _ hxo hyo hma =>
    obtain ⟨m', mm', h1, h2, h3, h4, h5, h6⟩ := g48_spFstpd (H := H) F hF hsz hm hmm hkn hsep
      hinv.core.regs hR (hbase (by rw [hop]; nofun)) hj hj' hop hsz4 hax hmt hhn hxo hyo hma hvs
      htemp hs
    exact store m' mm' hhn (by rw [hop]; decide) h1 h2 h3 h4 h5 h6
  | fload hop hsz2 _ hma hro hc =>
    have hnp : v.op ≠ .Phi := by rcases hop with h | h <;> rw [h] <;> nofun
    obtain ⟨r, hvh, -⟩ := fresObj_spec hro
    obtain ⟨m', h1, h2, hmem, hsl, hregs, hx⟩ := g48_spFLoad (H := H) F hm hmm hkn
      hinv.core.regs (knext_kStep (K := K) fun _ => (hs_reg hvh).noRegs) (hbase hnp) hj hj' hop
      (fun a x ha hx => by
        obtain ⟨p, mm2, bs, hsym, hmm2, hr, hnq⟩ := hfl hop a x ha hx
        rw [hmm] at hmm2
        cases hmm2
        refine ⟨p, bs, ?_, hr, hnq⟩
        rw [← hsym]; unfold symAddr; rw [hax])
      hsz2 hax hma hro hc hvs htemp hs
    exact load m' hmem hsl hregs h1 h2
      (uokl_x48 (by rcases hop with h | h <;> rw [h] <;> decide) hx hL)
  | fstore hop hsz3 hmt hhn _ hso hma hc =>
    obtain ⟨m', mm', h1, h2, h3, h4, h5, h6⟩ := g48_spFStore (H := H) F hF hsz hm hmm hkn hsep
      hinv.core.regs hR (hbase (by rcases hop with h | h <;> rw [h] <;> nofun)) hj hj' hop hsz3
      hax hmt hhn hso hma hc hvs htemp hs
    exact store m' mm' hhn (by rcases hop with h | h <;> rw [h] <;> decide) h1 h2 h3 h4 h5 h6

/-- One value of G48's kinds, in a function whose `outargs` block sits at `SP` (`SPInv`, `hosp`):
`vk57_step`'s statement in the mode `true`, with the contract `CallOKStk` of the static calls with
stack arguments or results. -/
theorem vk48_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)}
    (hE : G49Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK48 lc g v kd)
    (hvs : VStep2 ps kd j j') (hloop : loopOp lc v = true → loopTgt ps j = true)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s true) (hL : UOKL m L)
    (hmem : ∀ x, (v.op = .ARM64MOVDnop ∨ v.op = .ARM64MOVDreg) → v.args[0]? = some x →
      ∃ r c, regHome? lc x = some r ∧ cls (lc.ty x) = some c ∧
        (r, c, lc.signOf lc.ctx.f.valueTab.size x) ∈ L)
    (hpre : G54Pre lc s v) (hsp : SPInv E s) (hosp : E.outSP = true)
    (hcall : CallOKAt true H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hcallz : CallOKZAt true H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hicall : ICallOKAt true H E (Link.byId sym text az ez ps.toList) ret lc s s' v m)
    (hwb : WbOKAt true H E g (Link.byId sym text az ez ps.toList) lc s v m) (hclo : CloOK E s v m)
    (hgetg : GetGOK E v)
    (hmeq : MemEqOKAt true H E g (Link.byId sym text az ez ps.toList) lc s v m)
    (hcallk : CallOKStk H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' true ∧
      UOKL m' (uStep35 lc L v) := by
  cases hVK with
  | g57 hVK57 =>
    exact vk57_step hE F hhome hcf hv hVK57 hvs hloop hj hj' hreads hm hinv hL hmem hpre hcall
      hcallz hicall hwb hclo hgetg hmeq hs
  | call htemp hop hcall' hcr hnd _ _ _ h16 hlen hargs hfa hres hct =>
    have hR := kread_of_reads hreads
    have hE28 := hE.env
    have hE0 := hE28.env.env.env.env
    obtain ⟨hlcE, -, -, -, -, -, hsyms, hcalls, -, -, hF⟩ := hE28.env.env.env.env
    have hframed : E.framed = true := by
      cases hfr : E.framed
      · exact absurd hop (hcalls hfr id v hv)
      · rfl
    have hnp : v.op ≠ .Phi := by rw [hop]; nofun
    obtain ⟨ι', hext', hA', m', hstar, hlm, hcore', hsl'⟩ := g2_callAt (H := H) F hF hlcE hcf
      hframed hsyms hm hinv.core hinv.slots hR hj hj' hop h16 hlen hargs
      (argsV F hm hinv.core hR hnp (fun a ha => List.dropLast_subset _ ha) hargs hfa) hres
      hct (kcall_kStep hnp hres hnd (callTy_len hct)) (fun _ hp => callPat_spec hp) hvs htemp hs
      (hcallk hop _ _ _ _ _ hcall' hcr)
    have hx : E.Extends { E with ι := ι' } := ⟨rfl, hext'⟩
    refine ⟨_, m', hx, ⟨hE28.extend hx (hE28.env.extend hx (hE28.env.env.extend hx
      (hE0.extend hext' hA'))), hE.vars.extend hx⟩, hstar, hlm, ⟨hcore', hsl'⟩, ?_⟩
    rw [uStep35_call47 (.inl hop)]
    intro e he
    cases he
  | sp htemp hax _ hb hVK =>
    obtain ⟨m', h1, h2, h3, h4⟩ := vk48_sp (H := H) hE F hcf hax hb hVK hvs htemp hj hj' hreads
      hm hinv hL hpre.1 hsp hosp hs
    exact ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, h3, h4⟩

/-- The ops of an access off `SP`. -/
theorem _root_.GoFV.Gen.Check.VKsp48.ops {lc : LocCtx} {v : Value} {kd : VKind2}
    (h : VKsp48 lc v kd) :
    (∃ x, loadOp? v.op = some x) ∨ (∃ x, storeOp? v.op = some x) ∨ v.op = .ARM64STP ∨
      v.op = .ARM64STPW ∨ v.op = .ARM64FSTPD ∨ v.op = .ARM64FMOVSload ∨
      v.op = .ARM64FMOVDload ∨ v.op = .ARM64FMOVSstore ∨ v.op = .ARM64FMOVDstore := by
  cases h with
  | load hop => exact .inl ⟨_, hop⟩
  | store hop => exact .inr (.inl ⟨_, hop⟩)
  | stp hop => exact .inr (.inr (.inl hop))
  | stpw hop => exact .inr (.inr (.inr (.inl hop)))
  | fstpd hop => exact .inr (.inr (.inr (.inr (.inl hop))))
  | fload hop =>
    rcases hop with h | h
    · exact .inr (.inr (.inr (.inr (.inr (.inl h)))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))
  | fstore hop =>
    rcases hop with h | h
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr h)))))))

/-- A nil check of G48's kinds is G7's. -/
theorem vk48_nil {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK48 lc g v kd)
    (hop : v.op = .ARM64LoweredNilCheck) : VK7 lc g v kd := by
  cases h with
  | g57 h => exact vk57_nil h hop
  | call _ hop' => rw [hop] at hop'; cases hop'
  | sp _ _ _ _ h =>
    exfalso
    rcases h.ops with ⟨x, hx⟩ | ⟨x, hx⟩ | ho | ho | ho | ho | ho | ho | ho
    · rw [hop] at hx; simp [loadOp?, narrowLoad?] at hx
    · rw [hop] at hx; simp [storeOp?, narrowStore?] at hx
    all_goals rw [hop] at ho; cases ho

/-- A bounds check of G48's kinds is G28's. -/
theorem vk48_pb {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK48 lc g v kd)
    (hop : pbOp v.op = true) : VK28 lc g v kd := by
  cases h with
  | g57 h => exact vk57_pb h hop
  | call _ hop' => rw [hop'] at hop; cases hop
  | sp _ _ _ _ h =>
    exfalso
    rcases pbOp_cases hop with hp | hp | hp | hp <;>
    rcases h.ops with ⟨x, hx⟩ | ⟨x, hx⟩ | ho | ho | ho | ho | ho | ho | ho
    all_goals first
      | (rw [hp] at hx; simp [loadOp?, narrowLoad?, storeOp?, narrowStore?] at hx; done)
      | (rw [hp] at ho; cases ho)

/-! ## The theorems on G48's check -/

/-- G57's values and G48's calls and accesses off `SP` under G48's check, in a function whose
`outargs` block sits at `SP` (`hosp`, `SPInv`), keeping `SPInv`. -/
theorem g48L_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState}
    (hc : checkG48L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
    (hl : lc.ctx.f.lowered = true)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s E.outSP) (hsp : SPInv E s)
    (hosp : E.outSP = true) (hu : UOKL m (uL35 lc (uIn35 lc bid) blk i))
    (hpre : G54Pre lc s v)
    (hcall : CallOKAt E.outSP H E g L lc s s' v m)
    (hcallz : CallOKZAt E.outSP H E g L lc s s' v m)
    (hicall : ICallOKAt E.outSP H E L ret lc s s' v m)
    (hwb : WbOKAt E.outSP H E g L lc s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hmeq : MemEqOKAt E.outSP H E g L lc s v m) (hcallk : CallOKStk H E g L lc s s' v m)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' E.outSP ∧
      SPInv E' s' ∧ UOKL m' (uL35 lc (uIn35 lc bid) blk (i + 1)) := by
  have hsh : spHomes48 lc = true := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := checkG48L_spec hl hc
    exact h
  suffices key : ∃ E' m', E.Extends E' ∧ G49Env lc g L ps ret tab E' ∧
      PStar H L ps.toList ret m m' ∧ LocMatch E' s' bid (i + 1) m' ∧
      G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' E.outSP ∧
      UOKL m' (uL35 lc (uIn35 lc bid) blk (i + 1)) by
    obtain ⟨E', m', hx, hE', h1, h2, h3, h4⟩ := key
    exact ⟨E', m', hx, hE', h1, h2, h3, spInv_step hE'.env.env.env.env.env.addr hx
      hE.env.env.env.env.env.lcEq (fun _ => ⟨hl, spHomes48_spec hsh⟩) hv hsp hs, h4⟩
  rw [hosp] at hinv hcall hcallz hicall hwb hmeq ⊢
  rw [uL35_succ hl hi hv]
  have hE0 := hE
  obtain ⟨⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, hcf, hk, hlt, hnd, hblocks, -, hmovd, -, hlp,
    -⟩ := checkG48L_spec hl hc
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
  have hVK := vkind48_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  have hloop : loopOp c.cx.lc v = true → loopTgt c.cx.ps ((js ++ [e]).getD i 0) = true :=
    fun hop => loopOK_spec hlp hrow hb hi hv hop
  rw [kAt_succ hi hv]
  exact vk48_step hE0 F hhome hcf hv hVK hvs hloop hj hj' hreads hm hinv hu
    (fun x hop hx => movdOK35_spec hmovd hbid hb hi hv hop hx)
    hpre hsp hosp hcall hcallz hicall hwb hclo hgetg hmeq hcallk hs

/-- `InitMem` under G48's check: `g53L_initMemS`'s statement over `checkG48L`, `SPInv` kept by
`spHomes48`. -/
theorem g48L_initMem {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState}
    (hc : checkG48L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
    (hl : lc.ctx.f.lowered = true)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .InitMem) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s E.outSP) (hsp : SPInv E s) (hpre : MemInit s)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' E.outSP ∧
      SPInv E' s' ∧ UOKL m' (uL35 lc (uIn35 lc bid) blk (i + 1)) := by
  have hsh : spHomes48 lc = true := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := checkG48L_spec hl hc
    exact h
  have hsp' := spInv_step (s' := s') hE.env.env.env.env.env.addr ⟨rfl, fun _ _ h => h⟩
    hE.env.env.env.env.env.lcEq (fun _ => ⟨hl, spHomes48_spec hsh⟩) hv hsp hs
  have hE0 := hE
  obtain ⟨⟨⟨⟨⟨⟨-, hlink, hpcOf, -, -, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, -, -, -, -, -, -, hblocks, -, -, -, -, -⟩ :=
    checkG48L_spec hl hc
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
  have hkd := vkind48_initMem hop hkd
  rw [vkind57_initMem hop, vkind55_initMem hop, vkind54_initMem hop, vkind53_initMem hop,
    vkind52_initMem hop] at hkd
  have hkd := vkind49_initMem hop hkd
  rw [vkind51_initMem hop, vkind50_initMem hop, vkind47_initMem hop, vkind46_initMem hop,
    vkind45_initMem hop, vkind44_initMem hop] at hkd
  obtain ⟨-, -, ht, -, hh, hmt, rfl⟩ := vkind43_initMem hkd hop
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hpc : E.pcOf bid (i + 1) = E.pcOf bid i := by rw [hj', hj, hvs]
  have hss : s' = s := by
    rw [stepLoc_initMem hl ht hop hh hmt hs]
    exact congrArg (fun x => { s with mem := x }) hpre.symm
  subst hss
  have hK : kAt c.cx.lc kt bid blk (i + 1) = kAt c.cx.lc kt bid blk i := by
    rw [kAt_succ hi hv, kStep_none (by rw [hh]; nofun) (by rw [hh]; nofun) (by rw [hh]; nofun)]
  refine ⟨E, m, ⟨rfl, fun _ _ h => h⟩, hE0, .refl, locMatch_pc hm (hpc.trans hm.pc.symm),
    hK ▸ hinv, hsp', ?_⟩
  rw [uL35_succ hl hi hv, uStep35_initMem hop]
  intro e he
  cases he

/-- G38's nil panics under G48's check. -/
theorem g48L_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG48L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s osp) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  cases hl : lc.ctx.f.lowered with
  | false => exact g33_nilPanic (checkG33_of_48L hl hc) hE.env hbid hb hi hv hop hm hinv hs
  | true =>
  obtain ⟨⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, -, -, -⟩ :=
    checkG48L_spec hl hc
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
  have hVK := vkind48_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases vk48_nil hVK hop with
  | g6 hne _ => exact absurd hop hne
  | nil _ hsz2 _ _ hao hma =>
    exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma hvs hs

/-- G38's bounds panics under G48's check. -/
theorem g48L_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG48L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s osp) (hbok : BoundsOK H g L ps.toList)
    (hs : stepLoc env lc s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    exact g33_boundsPanic (checkG33_of_48L hl hc) hE.env hbid hb hi hv hop hm hinv hbok hs
  | true =>
  obtain ⟨⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, hsyms, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, hpb, -, -, -, -⟩ :=
    checkG48L_spec hl hc
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
  have hen : entryOp24 v.op = false := by
    rcases pbOp_cases hop with h | h | h | h <;> rw [h] <;> rfl
  have hVK := vkind48_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  exact vk28_boundsPanic F hsyms hpb hrow hb hi hv (vk48_pb hVK hop) hvs hj hreads hop hm hinv
    hbok hs

/-- G38's terminators under G48's check, keeping `SPInv`. -/
theorem g48L_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG48L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s E.outSP) (hsp : SPInv E s)
    (hpre : G1TermPre lc s blk) (hu : UOKL m (uL35 lc (uIn35 lc bid) blk blk.values.size))
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧
      G3Inv E lc (kt.at e.b) s' E.outSP ∧ SPInv E s' ∧ e.b ∈ lc.ctx.f.blocks.toList ∧
      UOKL m' (uIn35 lc e.b) := by
  suffices key : ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧
      G3Inv E lc (kt.at e.b) s' E.outSP ∧ e.b ∈ lc.ctx.f.blocks.toList ∧
      UOKL m' (uIn35 lc e.b) by
    obtain ⟨m', h1, h2, h3, h4, h5⟩ := key
    exact ⟨m', h1, h2, h3, spInv_term hsp ht, h4, h5⟩
  cases hl : lc.ctx.f.lowered with
  | false =>
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g33_term (checkG33_of_48L hl hc) hE.env hbid hb hm hinv hpre
      (by rw [uL31_nl hl]; intro e he; cases he) ht
    refine ⟨m', h1, h2, h3, h4, ?_⟩
    rw [uIn35_nl hl]
    intro e he
    cases he
  | true =>
  obtain ⟨⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, hedges, -, -⟩ :=
    checkG48L_spec hl hc
  obtain ⟨m', h1, h2, h3, h4, he, hx⟩ := termK_stepX hpcOf
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb hm hinv hpre ht
  refine ⟨m', h1, h2, h3, h4, fun x hxin => ?_⟩
  exact uok_of_x hx (hu x (uEdgesOK35_edge hedges hbid hb he x hxin))

/-! ## The slice: the theorems on `checkG48 lc`, on `liveCtx lc` -/

/-- **G48, values.** A value of a lowered function `checkG48` accepted, in an activation whose
`outargs` block sits at `SP` (`hosp`, `SPInv`): G57's values (`g57_value`'s statement), the
static calls with stack arguments or results under the trusted contract `CallOKStk`, and the
accesses off `SP` at `[8, outargsSize)`, keeping `SPInv`. -/
theorem g48_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState}
    (hc : checkG48 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
    (hl : lc.ctx.f.lowered = true)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s E.outSP) (hsp : SPInv E s)
    (hosp : E.outSP = true)
    (hu : UOKL m (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk i))
    (hpre : G54Pre (liveCtx lc) s v)
    (hcall : CallOKAt E.outSP H E g L (liveCtx lc) s s' v m)
    (hcallz : CallOKZAt E.outSP H E g L (liveCtx lc) s s' v m)
    (hicall : ICallOKAt E.outSP H E L ret (liveCtx lc) s s' v m)
    (hwb : WbOKAt E.outSP H E g L (liveCtx lc) s v m) (hclo : CloOK E s v m)
    (hgetg : GetGOK E v) (hmeq : MemEqOKAt E.outSP H E g L (liveCtx lc) s v m)
    (hcallk : CallOKStk H E g L (liveCtx lc) s s' v m)
    (hs : stepLoc env (liveCtx lc) s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env (liveCtx lc) g L ps ret tab E' ∧
      PStar H L ps.toList ret m m' ∧ LocMatch E' s' bid (i + 1) m' ∧
      G3Inv E' (liveCtx lc) (kAt (liveCtx lc) kt bid blk (i + 1)) s' E.outSP ∧ SPInv E' s' ∧
      UOKL m' (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk (i + 1)) :=
  g48L_value (checkG48_spec hc).2 hE hl hbid hb hi hv hen hm hinv hsp hosp hu hpre hcall hcallz
    hicall hwb hclo hgetg hmeq hcallk hs

/-- **G48, `InitMem`.** `g53_initMemS`'s statement over `checkG48`, `SPInv` kept by the checker's
`spHomes48`. -/
theorem g48_initMem {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState}
    (hc : checkG48 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
    (hl : lc.ctx.f.lowered = true)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .InitMem) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s E.outSP) (hsp : SPInv E s)
    (hpre : MemInit s) (hs : stepLoc env (liveCtx lc) s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env (liveCtx lc) g L ps ret tab E' ∧
      PStar H L ps.toList ret m m' ∧ LocMatch E' s' bid (i + 1) m' ∧
      G3Inv E' (liveCtx lc) (kAt (liveCtx lc) kt bid blk (i + 1)) s' E.outSP ∧ SPInv E' s' ∧
      UOKL m' (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk (i + 1)) :=
  g48L_initMem (checkG48_spec hc).2 hE hl hbid hb hi hv hop hm hinv hsp hpre hs

/-- **G48, nil panics.** `g57_nilPanic`'s statement over `checkG48`. -/
theorem g48_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG48 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s osp)
    (hs : stepLoc env (liveCtx lc) s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e :=
  g48L_nilPanic (checkG48_spec hc).2 hE hbid hb hi hv hop hm hinv hs

/-- **G48, bounds panics.** `g57_boundsPanic`'s statement over `checkG48`. -/
theorem g48_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG48 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s osp)
    (hbok : BoundsOK H g L ps.toList) (hs : stepLoc env (liveCtx lc) s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' :=
  g48L_boundsPanic (checkG48_spec hc).2 hE hbid hb hi hv hop hm hinv hbok hs

/-- **G48, terminators.** `g53_termS`'s statement over `checkG48`. -/
theorem g48_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG48 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk blk.values.size) s E.outSP)
    (hsp : SPInv E s) (hpre : G1TermPre (liveCtx lc) s blk)
    (hu : UOKL m (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk blk.values.size))
    (ht : stepTermLoc (liveCtx lc) s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧
      G3Inv E (liveCtx lc) (kt.at e.b) s' E.outSP ∧ SPInv E s' ∧ e.b ∈ lc.ctx.f.blocks.toList ∧
      UOKL m' (uIn35 (liveCtx lc) e.b) :=
  g48L_term (checkG48_spec hc).2 hE hbid hb hm hinv hsp hpre hu ht

end GoFV.Proof.Gen

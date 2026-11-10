import GoFV.Gen.Check59
import GoFV.Proof.Gen.G59
import GoFV.Proof.Witness.GenG48
import GoFV.Proof.Witness.GenG59p

/-!
# Witness: slice G59 (`checkG59`, `g59_value`) on `main.init.func33` (`test/zerodivide`)

`test/zerodivide/main/init.func33` (quick-v10), loaded as in `GenG59p.lean` (its embedded
`.ssa`/`.prog`, `lc0`, `ps`, `bs`, `g`, the state `s0` with `main.d = complex(1.5, 2.5)`). G58's
check rejects it (`v24: pair load shape`, its `FLDPD main.d(SB), (F2, F3)`); `checkG59` accepts it
with the PC table `tab59` and the class table `kt59`, and `g59_value` relates `v24`'s run to the
machine's `FLDPD`. The activation `E59` is G48's mode: its `outargs` block sits at `SP` (`outSP`,
`SPInv`; `SP` is `GenG48.spO`), `.autotmp_1`'s block at `SP + 40` as in `GenG59p`, with the
check's PC table.
-/

open scoped GoFV.SSA.Sem.Fixed

namespace GoFV.Proof.Witness.GenG59

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen
open GoFV.Proof.Witness.GenG59p

/-- The PC table `checkG59` computes: `b2`'s values from Prog 3 on (`v24` at index 3, Prog 3; the
value after it at Prog 4), then `b1` and `b3`. -/
def tab59 : PcTab :=
  [(2, [3, 3, 3, 3, 4, 4, 4, 5, 5, 5, 7, 7, 7, 7, 8, 9, 10, 11, 11, 11, 11, 13, 14, 15]),
    (1, [17, 18, 19, 19, 19, 20]), (3, [20, 20, 21, 21, 21])]

/-- The class table `checkG59` computes. -/
def kt59 : KTab :=
  let kin := kFlow lc (65 * lc.ctx.f.blocks.size + 2)
  lc.ctx.f.blocks.toList.map fun b => (b, (kin[b]?).getD KMap.bot)

/-- `b2`, the block of `v24`. -/
def blk : Block := (lc.ctx.f.block? 2).getD default

/-- `ι`: `GenG48.ι48` (the globals at `symA`, `outargs 0` at `SP`), and `.autotmp_1`'s block (aux
7, a `temp` block of activation 0) at `SP + 40`. -/
def ι59s (b : Blk) : Option (BitVec 64) :=
  if b = .temp 0 7 then some (GenG48.spO + 40) else GenG48.ι48 b

/-- A framed activation whose `outargs` block sits at `SP` (`SP = GenG48.spO`), with the PC table
`tab59`. -/
def E59 : MatchEnv :=
  { lc, ι := ι59s, sp := GenG48.spO, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab59, outSP := true }

/-- `GenG59p.m0` at `E59`'s `SP` and at `v24`'s PC under `tab59`. -/
def m59 : MState :=
  { x := fun k => if k = 28 then 0x9000 else if k = 29 then GenG48.spO - 8 else 0,
    sp := GenG48.spO, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E59.pcOf 2 3, mem := MD }

/-- What compiled evaluation checks on `main.init.func33` beyond `GenG59p.gFacts`: `checkG58`
rejects it, `checkG59` accepts it with `tab59` and `kt59`; `b2` is a block of it holding `v24` at
index 3; G35's table before `v24` is empty. -/
def gFacts : Bool :=
  (checkG58 lc0 ps bs g).toOption.isNone && (checkG59 lc0 ps bs g).toOption == some (tab59, kt59) &&
    lc.ctx.f.blocks.toList.contains 2 && (lc.ctx.f.block? 2).isSome && blk.values[3]? == some 24 &&
    uL35 lc (uIn35 lc 2) blk 3 == []

theorem g59_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    (checkG58 lc0 ps bs g).toOption = none ∧ checkG59 lc0 ps bs g = .ok (tab59, kt59) ∧
      2 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 2 = some blk ∧ blk.values[3]? = some 24 ∧
      uL35 lc (uIn35 lc 2) blk 3 = [] := by
  have hf := g59_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Option.isNone_iff_eq_none] at hf
  obtain ⟨h58, hres, hm2, hbs, hi, hu⟩ := hf
  refine ⟨h58, ?_, hm2, ?_, hi, hu⟩
  · revert hres; cases checkG59 lc0 ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk, hb]

theorem ι59s_temp : ι59s (.temp 0 7) = some (GenG48.spO + 40) := by simp [ι59s]

theorem ι59s_ne {b : Blk} (h : b ≠ .temp 0 7) : ι59s b = GenG48.ι48 b := by simp [ι59s, h]

theorem ι59s_glob (name : String) : ι59s (.global name) = some GenG2.symA := by
  simp [ι59s, GenG48.ι48]

theorem addrAgree59s : AddrAgree ι59s := by
  intro b n a hb ha hnt
  rw [ι59s_ne (hnt 0 7)] at ha
  exact GenG48.addrAgree48 b n a hb ha hnt

/-- `GenG59p.env59` at `E59`. -/
theorem env59' (hlt : ∀ p ∈ ps.toList, p.id < 2 ^ 32) (hav : accessedVars lc = [7])
    (hvo : varOp g 7 = some (.AUTO, -16)) (hfg : lc.ctx.tabs.forgeable 7 = false)
    (hact : lc.ctx.act = 0) (hsl : (homeSlots lc).isEmpty = true)
    (hoff : frameOff L .AUTO (-16) = 40) : G49Env lc g L ps 0 tab59 E59 where
  env := {
    env := {
      env := {
        env := {
          env := {
            lcEq := rfl
            link := rfl
            pcOf := rfl
            retOut := fun p hp => GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
            addr := addrAgree59s
            glob := fun _ name _ _ => ι59s_glob name.toStringLossy
            syms := by
              intro y
              have hs : L.sym y = GenG2.symA := rfl
              rw [hs]
              refine ⟨by decide, fun p hp => ?_⟩
              exact GenG2.prog_addr_ne (hlt p hp) hp (Or.inr (by decide)) (by decide)
            calls := fun h => by cases h
            slot := fun k hk => by simp [List.isEmpty_iff.1 hsl] at hk
            extra := by decide
            frame := ⟨by decide, by decide, fun k off h => by cases h⟩ }
          vars := by
            intro x hx o ho _
            rw [hav, List.mem_singleton] at hx
            subst hx
            rw [hvo] at ho
            cases ho
            rw [hact, hoff]
            show ι59s (.temp 0 7) = some (GenG48.spO + BitVec.ofInt 64 40)
            rw [ι59s_temp]
            rfl }
        wbs := fun h => by cases h }
      icalls := fun h => by cases h }
    memeqs := fun h => by cases h }
  vars := by
    intro x hx nc o ho _ hf
    rw [hav, List.mem_singleton] at hx
    subst hx
    rw [hfg] at hf
    cases hf

/-- `GenG59p.memInjD` under `ι59s`: `main.d`'s bytes at `symA`. -/
theorem memInjDs : MemInj ι59s memD MD where
  nil := by simp [ι59s, GenG48.ι48]
  mapped := by
    intro b al h
    obtain ⟨rfl, rfl⟩ := memD_blocks h
    exact ⟨GenG2.symA, ι59s_glob _, fun _ => by decide, by simp [bytesD, GenG2.symA]⟩
  inj := by
    intro b al b' al' a a' h h' hne
    obtain ⟨rfl, -⟩ := memD_blocks h
    obtain ⟨rfl, -⟩ := memD_blocks h'
    exact absurd rfl hne
  bytes := by
    refine ⟨fun _ _ => False, fun b al a h ha => ?_⟩
    obtain ⟨rfl, rfl⟩ := memD_blocks h
    rw [ι59s_glob] at ha
    cases ha
    refine ⟨fun o h => h.elim, fun o _ h => h.elim, fun i hi _ => ?_⟩
    have hi' : i < 16 := by simpa [bytesD] using hi
    have hd : (GenG2.symA + BitVec.ofNat 64 i - GenG2.symA).toNat = i := by
      rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
      omega
    simp [ByteRel, MD, hd, hi', bytesD]

theorem sep59 : SepFrom ι59s (StkAt E59) memD := by
  intro b al a h ha y hy
  obtain ⟨rfl, rfl⟩ := memD_blocks h
  rw [ι59s_glob] at ha
  cases ha
  have hsp : E59.sp.toNat = 0x4000000000000000 := rfl
  have hA : GenG2.symA.toNat = 0x10000000000 := rfl
  simp only [hA, bytesD, Array.size_ofFn]
  rcases hy with ⟨-, h1, -⟩ | ⟨k, off, hk, -, h2⟩
  · rw [hsp] at h1
    omega
  · simp [E59] at hk

/-- `GenG59p.locMatch0` under `tab59`. -/
theorem locMatch59 : LocMatch E59 s0 2 3 m59 where
  regs := by
    intro r v hv
    rw [s0_regs hv]
    exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨memD, rfl, memInjDs⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m59, MD, E59]; decide,
    by simp only [MState.word, readMem, m59, MD, E59]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

/-- `GenG59p.inv0` in the mode `outSP` for any class map (every register of `s0` is `poison`). -/
theorem inv59 {K : KMap} : G3Inv E59 lc K s0 E59.outSP where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, memD, rfl, keysD, sep59.w⟩
    rw [s0_regs hv]
    trivial
  slots := by intro k v h; simp [s0] at h

/-- `SPInv`: `outargs 0` at `SP`; the Go register `SP` holds `poison`. -/
theorem spInv59 (hact : lc.ctx.act = 0) : SPInv E59 s0 := by
  refine fun _ => ⟨?_, fun x hx => ?_⟩
  · show ι59s (.outargs lc.ctx.act) = some GenG48.spO
    rw [hact]
    rfl
  · rw [s0_regs hx]
    trivial

/-- G54's premises on `v24` (`FLDPD`): G50's `PairPre50` (`GenG59p.pre24`); none of the others
applies. -/
theorem pre24' (hid : (val 24).id = 24) (hop : (val 24).op = .ARM64FLDPD)
    (hty : lc.ty 24 = .tuple [.int .w64, .int .w64])
    (hsy : ((val 24).aux.bind (symOf? lc.ctx.tabs ·)).map (·.1.toStringLossy) = some "main.d")
    (hoff : (val 24).auxInt.toInt = 0)
    (hr0 : (memD.read pD 8).isSome = true) (hr1 : (memD.read pD8 8).isSome = true)
    (hl0 : (Arm64.loadN (.int .w64) 8 false memD pD).retypeL (.int .w64) = .int .w64 c0)
    (hl1 : (Arm64.loadN (.int .w64) 8 false memD pD8).retypeL (.int .w64) = .int .w64 c1) :
    G54Pre lc s0 (val 24) := by
  have hne : ∀ o : Op, o ≠ .ARM64FLDPD → (val 24).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩,
    ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro _ _ _ hl; rw [hop] at hl; cases hl
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro _ _ _ _ hl; rw [hop] at hl; cases hl
  · intro _ _ hl; rw [hop] at hl; cases hl
  · intro h; rcases h with h | h | h <;> exact absurd h (hne _ (by decide))
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro _ _ hl; rw [hop] at hl; cases hl
  · intro _ _ _ hl; rw [hop] at hl; simp [fp2Of] at hl
  · intro _ _ _ _ hl; rw [hop] at hl; simp [fp3Of] at hl
  · exact pre24 hid hop hty hsy hoff hr0 hr1 hl0 hl1
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))

/-- **G59 on `main.init.func33`** (`test/zerodivide`; `GenG59p.genG59p_witness`'s function and
state, through the slice's theorem): `checkG58` rejects the function (`v24: pair load shape`) and
`checkG59` accepts it. In an activation whose `outargs` block sits at `SP` (`outSP`, `SPInv`), from
`s0`, with `main.d = complex(1.5, 2.5)`, `stepLoc` runs `v24` (`FLDPD {main.d} [0] v3 v1`) to `c0`
(the bits of `1.5`) in `F2` and `c1` (the bits of `2.5`) in `F3`, and `g59_value` relates it to a
machine state after `FLDPD main.d(SB), (F2, F3)` (Prog 3) whose `V2` and `V3` hold `c0` and `c1` in
their low 64 bits, under an activation extending `E59` that is again a `G49Env`. -/
theorem genG59_witness :
    (checkG58 lc0 ps bs g).toOption = none ∧ checkG59 lc0 ps bs g = .ok (tab59, kt59) ∧
      ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 24) = .ok s1 ∧
        s1.regs[33]? = some (.int .w64 c0) ∧ s1.regs[34]? = some (.int .w64 c1) ∧
        E59.Extends E1 ∧ G49Env lc g L ps 0 tab59 E1 ∧ PStar GenG2.H0 L ps.toList 0 m59 m1 ∧
        LocMatch E1 s1 2 4 m1 ∧ (m1.v 2).setWidth 64 = c0 ∧ (m1.v 3).setWidth 64 = c1 := by
  obtain ⟨hl, -, -, -, hlt, -, -, -, hv, hid, hop, hty, hsy, hoff, hr0, hr1, hl0, hl1, hav, hvo,
    hfg, hact, hsl, hfo, -, hrun⟩ := GenG59p.facts
  obtain ⟨h58, hc, hm2, hb, hi, hu⟩ := facts
  obtain ⟨s1, hs1, hr⟩ := GenG1.okThen_spec hrun
  simp only [Bool.and_eq_true] at hr
  have hr33 := isI64_spec hr.1
  have hr34 := isI64_spec hr.2
  have hE := env59' hlt hav hvo hfg hact hsl hfo
  have hne : ∀ o : Op, o ≠ .ARM64FLDPD → (val 24).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  -- `g59_value` reads the blocks and values of `lc0`: rewrite rather than unfold (the kernel
  -- would evaluate `lc0`).
  have hl0' : lc0.ctx.f.lowered = true := by rw [← liveCtx_ctx (lc := lc0)]; exact hl
  have hm0 : 2 ∈ lc0.ctx.f.blocks.toList := by rw [← liveCtx_ctx (lc := lc0)]; exact hm2
  have hb0 : lc0.ctx.f.block? 2 = some blk := by rw [← liveCtx_ctx (lc := lc0)]; exact hb
  have hv0 : lc0.ctx.f.value? 24 = some (val 24) := by rw [← liveCtx_ctx (lc := lc0)]; exact hv
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1, -, -, -⟩ := g59_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hl0' hm0 hb0 hi hv0 (by rw [hop]; rfl) locMatch59 inv59 (spInv59 hact) rfl
    (by
      change UOKL m59 (uL35 lc (uIn35 lc 2) blk 3)
      rw [hu]
      intro e he
      cases he)
    (pre24' hid hop hty hsy hoff hr0 hr1 hl0 hl1)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun _ _ _ _ _ _ _ _ _ _ hn => by rw [hop] at hn; cases hn)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) hs1
  exact ⟨h58, hc, s1, E1, m1, hs1, hr33, hr34, hx1, hE1, hp1, hm1,
    (hm1.regs 33 _ hr33).2 _ rfl, (hm1.regs 34 _ hr34).2 _ rfl⟩

end GoFV.Proof.Witness.GenG59

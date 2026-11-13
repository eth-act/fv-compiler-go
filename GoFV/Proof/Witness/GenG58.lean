import GoFV.Proof.Gen.G58
import GoFV.Proof.Witness.GenG48
import GoFV.Proof.Witness.GenG58a

/-!
# Witness: slice G58 (`checkG58`, `g58_value`) on `math/bits.ReverseBytes16`

`std/std/math/bits/ReverseBytes16` (quick-v10), loaded as in `GenG58a.lean` (its embedded
`.ssa`/`.prog`, `lc0`, `ps`, `bs`, `g`, the state `s0`). G48's check (on G57) rejects it only for
its `REV16W` (`v11: REV16W widths`); `checkG58` accepts it with the PC table `tab58` and the class
table `kt58`, and `g58_value` relates `v11`'s run to the machine's `REV16W R0, R0`. The activation
`E58` is G48's mode: its `outargs` block sits at `SP` (`outSP`, `SPInv`; `ι` and `SP` are
`GenG48`'s), with the check's PC table (`v11` starts at the no-op Prog before its `REV16W`).
-/

open scoped GoFV.SSA.Sem.Fixed

namespace GoFV.Proof.Witness.GenG58

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen
open GoFV.Proof.Witness.GenG58a

/-- The PC table `checkG58` computes: `b1`'s values `v6`, `v1`, `v11` start at Prog 5, `v12` and the
terminator at Prog 7. -/
def tab58 : PcTab := [(1, [5, 5, 5, 7, 7])]

/-- The class table `checkG58` computes. -/
def kt58 : KTab :=
  let kin := kFlow lc (65 * lc.ctx.f.blocks.size + 2)
  lc.ctx.f.blocks.toList.map fun b => (b, (kin[b]?).getD KMap.bot)

/-- A framed activation whose `outargs` block sits at `SP` (`GenG48.ι48`, `SP = GenG48.spO`), with
the PC table `tab58`. -/
def E58 : MatchEnv :=
  { lc, ι := GenG48.ι48, sp := GenG48.spO, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab58, outSP := true }

/-- `GenG58a.m0` at `E58`'s `SP` and at `v11`'s PC under `tab58`. -/
def m58 : MState :=
  { x := fun k => if k = 0 then 0x1234 else if k = 28 then 0x9000
      else if k = 29 then GenG48.spO - 8 else 0,
    sp := GenG48.spO, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E58.pcOf 1 2, mem := fun _ => 0 }

/-- What compiled evaluation checks on `math/bits.ReverseBytes16` beyond `GenG58a.gFacts`:
`checkG48` rejects it, `checkG58` accepts it with `tab58` and `kt58`; its activation is `0`; `b1` is
a block of it; the class table before `v11` (index 2 of `b1`) holds `R0` at 16 bits, and G35's table
there is empty. -/
def gFacts : Bool :=
  (checkG48 lc0 ps bs g).toOption.isNone && (checkG58 lc0 ps bs g).toOption == some (tab58, kt58) &&
    lc.ctx.act == 0 && lc.ctx.f.blocks.toList.contains 1 && (lc.ctx.f.block? 1).isSome &&
    (kAt lc kt58 1 blk 2).get 0 == some 16 && uL35 lc (uIn35 lc 1) blk 2 == []

theorem g58_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    (checkG48 lc0 ps bs g).toOption = none ∧ checkG58 lc0 ps bs g = .ok (tab58, kt58) ∧
      lc.ctx.act = 0 ∧ 1 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 1 = some blk ∧
      (kAt lc kt58 1 blk 2).get 0 = some 16 ∧ uL35 lc (uIn35 lc 1) blk 2 = [] := by
  have hf := g58_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Option.isNone_iff_eq_none] at hf
  obtain ⟨h48, hres, hact, hm1, hbs, hk, hu⟩ := hf
  refine ⟨h48, ?_, hact, hm1, ?_, hk, hu⟩
  · revert hres; cases checkG58 lc0 ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk, hb]

/-- `GenG58a.env58` at `E58`. -/
theorem env58' (hlt : ∀ p ∈ ps.toList, p.id < 2 ^ 32) (hav : (accessedVars lc).isEmpty = true)
    (hsl : (homeSlots lc).isEmpty = true) : G49Env lc g L ps 0 tab58 E58 where
  env := {
    env := {
      env := {
        env := {
          env := {
            lcEq := rfl
            link := rfl
            pcOf := rfl
            retOut := fun p hp => GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
            addr := GenG48.addrAgree48
            glob := fun _ _ _ _ => rfl
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
            intro x hx
            simp [List.isEmpty_iff.1 hav] at hx }
        wbs := fun h => by cases h }
      icalls := fun h => by cases h }
    memeqs := fun h => by cases h }
  vars := by
    intro x hx
    simp [List.isEmpty_iff.1 hav] at hx

/-- `GenG58a.locMatch0` at `E58` and `m58`. -/
theorem locMatch58 : LocMatch E58 s0 1 2 m58 where
  regs := by
    intro r v hv
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      show (m58.x _).setWidth _ = _; simp only [m58]; decide
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨GenG2.mem0, rfl, GenG2.memInj0 rfl _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m58, E58]; decide,
    by simp only [MState.word, readMem, m58, E58]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

/-- `GenG58a.inv0` in the mode `outSP` (`SepFromW` of the empty memory), for any class map with
`R0` at 16 bits. -/
theorem inv58 {K : KMap} (hk0 : K.get 0 = some 16) : G3Inv E58 lc K s0 E58.outSP where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, GenG2.mem0, rfl, by simp [KeysNodup, GenG2.mem0],
      fun b al a h => by simp [GenG2.mem0] at h⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · rw [hk0] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- `SPInv`: `outargs 0` at `SP`; the Go register `SP` holds `poison`. -/
theorem spInv58 (hact : lc.ctx.act = 0) : SPInv E58 s0 := by
  refine fun _ => ⟨?_, fun x hx => ?_⟩
  · show GenG48.ι48 (.outargs lc.ctx.act) = some GenG48.spO
    rw [hact]
    rfl
  · rcases s0_regs hx with ⟨h, -⟩ | rfl
    · simp [spReg] at h
    · trivial

/-- None of G54's premises applies to `REV16W`. -/
theorem pre11 {s : LocState} (hop : (val 11).op = .ARM64REV16W) : G54Pre lc s (val 11) := by
  have hne : ∀ o : Op, o ≠ .ARM64REV16W → (val 11).op ≠ o := fun o h h' =>
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
  · intro _ _ _ _ hpo; rw [hop] at hpo; simp [pairOp50] at hpo
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))

/-- **G58 on `math/bits.ReverseBytes16`** (`GenG58a.genG58a_witness`'s function and state, through
the slice's theorem): `checkG48` rejects the function (`v11: REV16W widths`) and `checkG58` accepts
it. In an activation whose `outargs` block sits at `SP` (`outSP`, `SPInv`), from `s0`, with
`x = 0x1234` in `R0`, `stepLoc` runs `v11` to `0x3412`, and `g58_value` relates it to a machine
state after the no-op Prog 5 and `REV16W R0, R0` (Prog 6) whose `X0` has the low halfword
`0x3412`, under an activation extending `E58` that is again a `G49Env`, `SPInv` kept. -/
theorem genG58_witness :
    (checkG48 lc0 ps bs g).toOption = none ∧ checkG58 lc0 ps bs g = .ok (tab58, kt58) ∧
      ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 11) = .ok s1 ∧
        s1.regs[0]? = some (.int .w16 0x3412) ∧
        E58.Extends E1 ∧ G49Env lc g L ps 0 tab58 E1 ∧ PStar GenG2.H0 L ps.toList 0 m58 m1 ∧
        LocMatch E1 s1 1 3 m1 ∧ SPInv E1 s1 ∧ (m1.x 0).setWidth 16 = 0x3412 := by
  obtain ⟨hl, -, -, hlt, -, -, -, hv, hi, hop, hav, hsl, -, -, hrun⟩ := GenG58a.facts
  obtain ⟨h48, hc, hact, hm1, hb, hk, hu⟩ := facts
  obtain ⟨s1, hs1, hr⟩ := GenG1.okThen_spec hrun
  have hr1 := isRes_spec hr
  have hE := env58' hlt hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64REV16W → (val 11).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  -- `g58_value` reads the blocks and values of `lc0`: rewrite rather than unfold (the kernel
  -- would evaluate `lc0`).
  have hl0 : lc0.ctx.f.lowered = true := by rw [← liveCtx_ctx (lc := lc0)]; exact hl
  have hm0 : 1 ∈ lc0.ctx.f.blocks.toList := by rw [← liveCtx_ctx (lc := lc0)]; exact hm1
  have hb0 : lc0.ctx.f.block? 1 = some blk := by rw [← liveCtx_ctx (lc := lc0)]; exact hb
  have hv0 : lc0.ctx.f.value? 11 = some (val 11) := by rw [← liveCtx_ctx (lc := lc0)]; exact hv
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, hsp1, -⟩ := g58_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hl0 hm0 hb0 hi hv0 (by rw [hop]; rfl) locMatch58 (inv58 hk)
    (fun _ => spInv58 hact) (fun _ => rfl) (fun _ => rfl)
    (by
      change UOKL m58 (uL35 lc (uIn35 lc 1) blk 2)
      rw [hu]
      intro e he
      cases he)
    (pre11 hop)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun _ _ _ _ _ _ _ _ _ _ hn => by rw [hop] at hn; cases hn)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun _ h => absurd h (hne _ (by decide))) hs1
  exact ⟨h48, hc, s1, E1, m1, hs1, hr1, hx1, hE1, hp1, hm1', hsp1 rfl,
    (hm1'.regs 0 _ hr1).1 _ (by simp [objX?])⟩

end GoFV.Proof.Witness.GenG58

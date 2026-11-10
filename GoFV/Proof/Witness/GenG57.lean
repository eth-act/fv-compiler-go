import GoFV.Proof.Gen.G57
import GoFV.Proof.Witness.GenG10
import GoFV.Proof.Witness.GenG57a

/-!
# Witness: slice G57 (`checkG57`, `g57_value`) on `main.grow`

`examples/structs/main.grow` (quick-v10), loaded as in `GenG57a.lean` (its embedded `.ssa`/`.prog`,
`lc0`, `ps`, `bs`, `g`, the activation `E`, the states `s0`/`m0`). G55's check rejects it only for
its `STPW` (`v12`); `checkG57` accepts it with `GenG57a`'s PC and class tables, and `g57_value`
relates `v12`'s run to the machine's `STPW (R2, R3), 8(R0)`.
-/

open scoped GoFV.SSA.Sem.Fixed

namespace GoFV.Proof.Witness.GenG57

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen
open GoFV.Proof.Witness.GenG57a

/-- What compiled evaluation checks on `main.grow` beyond `GenG57a.gFacts`: `checkG57` accepts it
with `GenG57a`'s `tab` and `kt`; `b1` is a block of it, and G35's table before `v12` (index 14 of
`b1`) is empty. -/
def gFacts : Bool :=
  (checkG57 lc0 ps bs g).toOption == some (tab, kt) &&
    lc.ctx.f.blocks.toList.contains 1 && (lc.ctx.f.block? 1).isSome &&
    uL35 lc (uIn35 lc 1) blk 14 == []

theorem g57_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    checkG57 lc0 ps bs g = .ok (tab, kt) ∧ 1 ∈ lc.ctx.f.blocks.toList ∧
      lc.ctx.f.block? 1 = some blk ∧ uL35 lc (uIn35 lc 1) blk 14 = [] := by
  have hf := g57_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc] at hf
  obtain ⟨hres, hm1, hbs, hu⟩ := hf
  refine ⟨?_, hm1, ?_, hu⟩
  · revert hres; cases checkG57 lc0 ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk, hb]

/-- None of G54's premises applies to `STPW`. -/
theorem pre12 {s : LocState} (hop : (val 12).op = .ARM64STPW) : G54Pre lc s (val 12) := by
  have hne : ∀ o : Op, o ≠ .ARM64STPW → (val 12).op ≠ o := fun o h h' =>
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

/-- **G57 on `main.grow`** (`GenG57a.genG57a_witness`'s function and states, through the slice's
theorem): `checkG55` rejects the function (`v12: op STPW`) and `checkG57` accepts it. From `s0`,
with `heap 1` (32 poison bytes) in `R0`, `x = 0x11223344` in `R2` and `y = 0x55` in `R3`,
`stepLoc` runs `v12` (`STPW [8] v7 v37 v44 v31`), and `g57_value` relates it to a machine state
after Prog 15 (`STPW (R2, R3), 8(R0)`) whose memory holds `x`'s low byte `0x44` at `A + 8`
although `X2`'s upper half is not zero, under an activation extending `E` that is again a
`G49Env`. -/
theorem genG57_witness :
    (checkG55 lc0 ps bs g).toOption = none ∧ checkG57 lc0 ps bs g = .ok (tab, kt) ∧
      ∃ s1 mm E1 m1, stepLoc GenG2.env lc s0 (val 12) = .ok s1 ∧ s1.mem = .mem mm ∧
        E.Extends E1 ∧ G49Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
        LocMatch E1 s1 1 15 m1 ∧ m1.mem (A + BitVec.ofNat 64 8) = 0x44 := by
  obtain ⟨-, h55, -, -, -, hav, hsl, hlt, -, -, hv, hi, hop, -, -, hk0, hk2, hk3, hrun⟩ :=
    GenG57a.facts
  obtain ⟨hc, hm1, hb, hu⟩ := facts
  obtain ⟨s1, hs1, hd⟩ := GenG1.okThen_spec hrun
  obtain ⟨mm, al, hmm, hal, hal8, hpw⟩ := memIs_spec hd
  have hE := g57aEnv hlt hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64STPW → (val 12).op ≠ o := fun o h h' => h (h'.symm.trans hop)
  -- `g57_value` reads the blocks and values of `lc0`: rewrite rather than unfold (the kernel
  -- would evaluate `lc0`).
  have hm0 : 1 ∈ lc0.ctx.f.blocks.toList := by rw [← liveCtx_ctx (lc := lc0)]; exact hm1
  have hb0 : lc0.ctx.f.block? 1 = some blk := by rw [← liveCtx_ctx (lc := lc0)]; exact hb
  have hv0 : lc0.ctx.f.value? 12 = some (val 12) := by rw [← liveCtx_ctx (lc := lc0)]; exact hv
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -⟩ := g57_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hm0 hb0 hi hv0 (by rw [hop]; rfl) locMatch0 (g57aInv0 hk0 hk2 hk3)
    (by change UOKL m0 (uL35 lc (uIn35 lc 1) blk 14); rw [hu]; intro e he; cases he)
    (pre12 hop)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide))) hs1
  -- Byte 8 of `heap 1` after the store, read through `MemInj`: no pointer word covers it.
  have hA : m1.mem (A + BitVec.ofNat 64 8) = 0x44 := by
    obtain ⟨mm1, hmm1, hinj⟩ := hm1'.mem
    rw [hmm] at hmm1
    cases hmm1
    obtain ⟨W, hW⟩ := hinj.bytes
    obtain ⟨hw, -, hby⟩ := hW _ _ _ hal (hx1.2 (.heap 1) A rfl)
    obtain ⟨h8, hd8⟩ := Array.getElem?_eq_some_iff.1 hal8
    have hr := hby 8 h8 (fun o ho ho' => by
      obtain ⟨p, hp, -⟩ := hw o ho
      rw [hpw o (by omega)] at hp
      cases hp)
    rw [hd8] at hr
    exact hr.symm
  exact ⟨h55, hc, s1, mm, E1, m1, hs1, hmm, hx1, hE1, hp1, hm1', hA⟩

end GoFV.Proof.Witness.GenG57

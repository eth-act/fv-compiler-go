import GoFV.Gen.Check57
import GoFV.Proof.Gen.G58a
import GoFV.Proof.Witness.GenG57b

open scoped GoFV.SSA.Sem.Fixed

/-!
`LoweredRound32F` of G58's group A on `main.init.func95.1` (`test/gcgort`), the function, layout,
activation and states of `GenG57b` (`GoFV/Proof/Witness/GenG57b.lean`), one value earlier.
-/

namespace GoFV.Proof.Witness.GenG58a5

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen GoFV.Proof.Witness.GenG57b

/-- A value check's answer: no code. -/
def isNoCode : Option (Except String VKind2) → Bool
  | some (.ok .none) => true
  | _ => false

theorem isNoCode_spec {o : Option (Except String VKind2)} (h : isNoCode o = true) :
    o = some (.ok .none) := by
  unfold isNoCode at h
  split at h
  · rfl
  · cases h

/-- The register value `.int .w32 xv`. -/
def isXv : Option Val → Bool
  | some (.int .w32 x) => x == xv
  | _ => false

theorem isXv_spec {o : Option Val} (h : isXv o = true) : o = some (.int .w32 xv) := by
  unfold isXv at h
  split at h
  · rename_i x; rw [beq_iff_eq.1 h]
  · cases h

/-- What compiled evaluation checks on `main.init.func95.1` beyond `GenG57b.facts`: G57's value
check `vkind57` rejects `v13` (`op LoweredRound32F`), which `vkind58a` accepts with no code; `b1`
holds `v13` at index 7; `K0` holds `v13`'s reads; and `stepLoc` runs `v13` from `s0` to `F0`
(Go register 31) holding the same `float32` `xv`. -/
def gFacts : Bool :=
  (vkind57 lc g (val 13)).toOption.isNone && isNoCode (vkind58a lc g (val 13)) &&
    (lc.ctx.f.value? 13).isSome && blk.values[7]? == some 13 &&
    (val 13).op == .ARM64LoweredRound32F &&
    (kReads lc (val 13)).all (fun rc => K0.get rc.1 == some rc.2) &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 13)) (fun s1 => isXv s1.regs[31]?)

theorem g58a5_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts5 :
    (vkind57 lc g (val 13)).toOption = none ∧ isNoCode (vkind58a lc g (val 13)) = true ∧
      lc.ctx.f.value? 13 = some (val 13) ∧ blk.values[7]? = some 13 ∧
      (val 13).op = .ARM64LoweredRound32F ∧
      (∀ rc ∈ kReads lc (val 13), K0.get rc.1 = some rc.2) ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 13))
        (fun s1 => isXv s1.regs[31]?) = true := by
  have hf := g58a5_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, and_assoc, Option.isNone_iff_eq_none,
    List.all_eq_true] at hf
  obtain ⟨h57, hvk, hvs, hi, hop, hrd, hrun⟩ := hf
  refine ⟨h57, hvk, ?_, hi, hop, hrd, hrun⟩
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
  simp [val, hv]

/-- `GenG57b`'s match, one value earlier (`v13`, at the same PC: it has no code). -/
theorem locMatch7 : LocMatch E s0 1 7 m0 where
  regs := locMatch0.regs
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := locMatch0.mem
  frame := locMatch0.frame
  pc := rfl

/-- **G58, group A, on `main.init.func95.1`** (`test/gcgort`: `ch <- complex(float32(i),
float32(i))`, where `float32(i)` is `v9 = SCVTFS` and `v13 = LoweredRound32F v9`, no code, the
result in `v9`'s `F0`): `vkind57` rejects `v13` (`op LoweredRound32F`) and `vkind58a` accepts it.
From `GenG57b.s0`, with `float32(1.5)` in `F0`, `stepLoc` runs `v13` to `F0` holding the same
float, and `vk58a_step` relates it to a machine state (no Prog runs) with `V0`'s low word that
float, under an activation extending `E` that is again a `G49Env`. -/
theorem genG58a5_witness :
    (vkind57 lc g (val 13)).toOption = none ∧
      ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 13) = .ok s1 ∧ s1.regs[31]? = some (.int .w32 xv) ∧
        E.Extends E1 ∧ G49Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
        LocMatch E1 s1 1 8 m1 ∧ (m1.v 0).setWidth 32 = xv := by
  obtain ⟨hl, -, -, -, hlt, hnd, hhome, hcf, -, -, -, -, hav, hvo, hfg, hact, hsl, hoff, -, hk31,
    -⟩ := facts
  obtain ⟨h57, hvk, hv, -, -, hrd, hrun⟩ := facts5
  obtain ⟨s1, hs1, hr⟩ := GenG1.okThen_spec hrun
  have hr1 := isXv_spec hr
  have hE := g57bEnv hlt hav hvo hfg hact hsl hoff
  obtain ⟨htemp, hVK⟩ := vkind58a_spec (isNoCode_spec hvk)
  have F : Facts lc (fun _ => GenG2.symA) GenG2.text 32 8 ps.toList 0 E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt,
      fun p hp => GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp), addrAgree57⟩
  have hj : E.pcOf 1 7 = pcAt GenG2.text ps.toList jF := rfl
  have hj' : E.pcOf 1 (7 + 1) = pcAt GenG2.text ps.toList jF := rfl
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1, -, -⟩ := vk58a_step (H := GenG2.H0) (L := []) (bid := 1)
    (i := 7) (j := jF) (j' := jF) hE F hcf hv hVK rfl htemp hj hj' hrd locMatch7
    (g57bInv0 hk31) (fun e he => by cases he) hs1
  refine ⟨h57, s1, E1, m1, hs1, hr1, hx1, hE1, hp1, hm1, ?_⟩
  exact (hm1.regs 31 _ hr1).2 _ (by simp [objV?])

end GoFV.Proof.Witness.GenG58a5

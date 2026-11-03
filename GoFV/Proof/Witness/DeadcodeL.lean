import GoFV.Proof.Pass.DeadcodePassL
import GoFV.Proof.Witness.ClampL
import GoFV.Proof.Witness.Deadcode

/-!
# Non-vacuity witness: deadcode on lowered code

`deadL`: lowered `clamp` (`GoFV.Proof.Witness.ClampL`) with a dead arm64 value
`v23 = MOVDconst [7]` in `b1`. It passes `check`, is lowered, and returns `clamp(5, 0, 10) = 5`
under `runL`. deadcode's tail (`deadTail`, liveness and freeing) removes `v23`; the output passes
`check`, so `refinesL_of_deadRel` (with `deadTail_rel`, `deadTail_relL`) applies and the output
returns 5 under `runL` too (`deadTailL_witness`). The whole pass (`lowered deadcode`) accepts
`deadL`, which is in `DeadFrag` and `DeadFragL`, and its output passes `check`, is lowered and
lists fewer values (all by kernel evaluation), so `deadcode_refinesL` applies
(`deadcodeL_witness`).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof GoFV.Proof.Dead

/-- The check environment of lowered `clamp`. -/
def clampLCheckEnv : CheckEnv :=
  { tabs := clampLTabs, typs := #[("Bool", 4), ("Int", 2), ("Uintptr", 15), ("Mem", 28)] }

/-- `clampL`'s values and a dead `v23 = MOVDconst [7]` in `b1`. -/
def deadLValues : Array (Option Value) :=
  clampLValues.set! 23 (some (mkVI 23 .ARM64MOVDconst 2 7 none (pos 2 22 7 0) 0 #[] 1))

/-- `clampL`'s blocks, `b1` listing `v23`. -/
def deadLBlocks : Array (Option Block) := clampLBlocks.set! 1
  (some (mkB 1 .ARM64GT (pos 2 22 7 0) #[22] #[⟨3, 0⟩, ⟨2, 0⟩] #[] #[1, 8, 9, 10, 23, 22]))

/-- Lowered `clamp` with a dead arm64 value. -/
def deadL : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 24
  bidLast := 5
  blocks := #[1, 2, 3, 4, 5]
  blockTab := deadLBlocks
  valueTab := deadLValues
  names := #[(1, #[8]), (2, #[9]), (3, #[10])]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := [18, 13, 12, 19, 20, 17, 16, 11, 7, 6, 5, 4, 3, 2]
  freeBlocks := []
  cache := { postorder := some #[3, 5, 4, 2, 1], lineStarts := some #[] }

theorem deadL_facts :
    (check clampLCheckEnv deadL).toBool = true ∧ deadL.lowered = true ∧
    deadL.valueTab.size ≤ deadL.vidLast + 1 ∧
    returnsInt (runL Env.p1 clampLTabs deadL (clampArgs 5) {} 3) 5 = true ∧
    ((deadTail clampLTabs deadL.reachableBlocks deadL).toOption.map fun g =>
      (check clampLCheckEnv g).toBool && g.lowered && decide (listedValues g < listedValues deadL)) =
      some true := by
  decide +kernel

private theorem check_ok_of_toBool {ce : CheckEnv} {f : Func} (h : (check ce f).toBool = true) :
    check ce f = .ok () := by
  revert h; cases check ce f <;> simp [Except.toBool]

/-- **`refinesL_of_deadRel` is not vacuous**: deadcode's tail removes `deadL`'s dead arm64 value,
and the output returns `clamp(5, 0, 10) = 5` under `runL`, as `deadL` does. -/
theorem deadTailL_witness :
    ∃ g, deadTail clampLTabs deadL.reachableBlocks deadL = .ok g ∧
      listedValues g < listedValues deadL ∧
      ∃ fuel m, runL Env.p1 clampLTabs g (clampArgs 5) {} fuel = .returned [.i64 5] m := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := deadL_facts
  obtain ⟨m, hm⟩ := returnsInt_iff.1 h4
  cases hc : deadTail clampLTabs deadL.reachableBlocks deadL with
  | error e => rw [hc] at h5; cases h5
  | ok g =>
    rw [hc] at h5
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Bool.and_eq_true,
      decide_eq_true_eq] at h5
    obtain ⟨⟨hgc, hgl⟩, hv⟩ := h5
    have hwf := check_wf (check_ok_of_toBool h1)
    have hwg := check_wf (check_ok_of_toBool hgc)
    refine ⟨g, rfl, hv, ?_⟩
    obtain ⟨fuel, m', h⟩ := RefinesL.returned_int
      (refinesL_of_deadRel ⟨⟨_, hwf⟩, ⟨_, hwg⟩, deadTail_rel hwg h3 hc⟩ (deadTail_relL h3 hc)
        (by rw [hgl, h2])) hm
    exact ⟨fuel, m', h⟩

/-- A pass environment for `deadL`. -/
def deadLPassEnv : PassEnv where
  passName := "lowered deadcode"
  pkg := GoStr.ofString "main"
  funcName := GoStr.ofString "clamp"
  abi := 1
  nosplit := false
  pgohot := false
  config := #[]
  typs := #[]
  typeOrder := default
  tables := clampLTabs

theorem deadL_pass_facts :
    deadFragB clampLTabs deadL = true ∧ deadFragLB clampLTabs deadL = true ∧
    ((deadcode clampLTabs deadL).toOption.map fun g =>
      (check clampLCheckEnv g).toBool && g.lowered && decide (listedValues g < listedValues deadL)) =
      some true := by
  decide +kernel

/-- **`deadcode_refinesL` is not vacuous**: `lowered deadcode` removes `deadL`'s dead arm64
value, and the output returns `clamp(5, 0, 10) = 5` under `runL`, as `deadL` does. -/
theorem deadcodeL_witness :
    ∃ out, deadcodePass deadLPassEnv deadL = .ok out ∧ out.func.lowered = true ∧
      listedValues out.func < listedValues deadL ∧
      ∃ fuel m, runL Env.p1 out.tables out.func (clampArgs 5) {} fuel = .returned [.i64 5] m := by
  obtain ⟨h1, h2, -, h4, -⟩ := deadL_facts
  obtain ⟨hd, hdL, h5⟩ := deadL_pass_facts
  obtain ⟨m, hm⟩ := returnsInt_iff.1 h4
  cases hc : deadcode clampLTabs deadL with
  | error e => rw [hc] at h5; cases h5
  | ok g =>
    rw [hc] at h5
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Bool.and_eq_true,
      decide_eq_true_eq] at h5
    obtain ⟨⟨hgc, hgl⟩, hv⟩ := h5
    have hp : deadcodePass deadLPassEnv deadL = .ok { func := g, tables := clampLTabs } := by
      simp only [deadcodePass, Pass.ofFunc, deadLPassEnv]
      rw [hc]; rfl
    refine ⟨_, hp, hgl, hv, ?_⟩
    obtain ⟨fuel, m', h⟩ := RefinesL.returned_int
      (deadcode_refinesL hp (check_ok_of_toBool h1) (ce' := clampLCheckEnv)
        (check_ok_of_toBool hgc) (deadFrag_of hd) (by rw [hgl, h2]) (deadFragL_of hdL)) hm
    exact ⟨fuel, m', h⟩

end GoFV.Proof.Witness

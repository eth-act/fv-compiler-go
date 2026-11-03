import GoFV.Proof.Pass.LowCong
import GoFV.Proof.Witness.ClampL

/-!
# Non-vacuity witnesses: `checkLower`, `likelyadjust`, `layout` on lowered `clamp`

Each pass accepts `clampL` (by kernel evaluation); `likelyadjust` predicts `b1`'s branch
`unlikely` (as Go does in section 49) and `layout` reorders the blocks to `b1 b3 b2 b5 b4` (on
`clampL` itself, without `likelyadjust`'s prediction). By the pass theorems the outputs return
`clamp(5, 0, 10) = 5` under `runL`, as the source does (`clampL_run5`).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof

/-- A pass environment for lowered `clamp` (configuration: `hasgreg 1`). -/
def clampLPassEnv (passName : String) : PassEnv where
  passName := passName
  pkg := GoStr.ofString "main"
  funcName := GoStr.ofString "clamp"
  abi := 1
  nosplit := false
  pgohot := false
  config := #[("arch", #[.word "arm64"]), ("hasgreg", #[.word "1"])]
  typs := #[]
  typeOrder := default
  tables := clampLTabs

/-- A successful pass result, read off a kernel-evaluated `Option`. -/
theorem ok_of_toOption {p : Except String PassOut} {P : PassOut → Prop} [DecidablePred P]
    (h : (p.toOption.map fun o => decide (P o)) = some true) :
    ∃ out, p = .ok out ∧ P out := by
  cases p with
  | error e => cases h
  | ok out =>
    simp only [Except.toOption, Option.map_some, Option.some.injEq, decide_eq_true_eq] at h
    exact ⟨out, rfl, h⟩

theorem checkLower_witness :
    ∃ out, checkLowerPass (clampLPassEnv "checkLower") clampL = .ok out ∧
      ∃ fuel m, runL Env.p1 out.tables out.func (clampArgs 5) {} fuel = .returned [.i64 5] m := by
  obtain ⟨m, hm⟩ := clampL_run5
  obtain ⟨out, hp, -⟩ := ok_of_toOption (P := fun _ => True)
    (p := checkLowerPass (clampLPassEnv "checkLower") clampL) (by decide +kernel)
  refine ⟨out, hp, ?_⟩
  obtain ⟨fuel, m', h⟩ := RefinesL.returned_int (checkLower_refinesL hp) hm
  exact ⟨fuel, m', h⟩

theorem likelyadjust_witness :
    ∃ out, likelyadjustPass (clampLPassEnv "likelyadjust") clampL = .ok out ∧
      (out.func.block? 1).map (·.likely) = some .unlikely ∧
      ∃ fuel m, runL Env.p1 out.tables out.func (clampArgs 5) {} fuel = .returned [.i64 5] m := by
  obtain ⟨m, hm⟩ := clampL_run5
  obtain ⟨out, hp, hl⟩ := ok_of_toOption
    (P := fun o => (o.func.block? 1).map (·.likely) = some .unlikely)
    (p := likelyadjustPass (clampLPassEnv "likelyadjust") clampL) (by decide +kernel)
  refine ⟨out, hp, hl, ?_⟩
  obtain ⟨fuel, m', h⟩ := RefinesL.returned_int (likelyadjust_refinesL hp) hm
  exact ⟨fuel, m', h⟩

theorem layout_witness :
    ∃ out, layoutPass (clampLPassEnv "layout") clampL = .ok out ∧
      out.func.blocks = #[1, 3, 2, 5, 4] ∧
      ∃ fuel m, runL Env.p1 out.tables out.func (clampArgs 5) {} fuel = .returned [.i64 5] m := by
  obtain ⟨m, hm⟩ := clampL_run5
  obtain ⟨out, hp, hb⟩ := ok_of_toOption (P := fun o => o.func.blocks = #[1, 3, 2, 5, 4])
    (p := layoutPass (clampLPassEnv "layout") clampL) (by decide +kernel)
  refine ⟨out, hp, hb, ?_⟩
  obtain ⟨fuel, m', h⟩ := RefinesL.returned_int (layout_refinesL hp) hm
  exact ⟨fuel, m', h⟩

end GoFV.Proof.Witness

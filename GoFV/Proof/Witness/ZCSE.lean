import GoFV.Proof.Pass.ZCSE
import GoFV.Proof.Witness.DecodedLen

/-!
# Non-vacuity witness: zero arg cse on `decodedLen`

zcse changes `decodedLen` (the `Const64 [4]` `v28` is merged into the entry's `v13`: `v23`
becomes `Mul64 v12 v13`), its checker accepts the result, and input and output pass `check`
(all by kernel evaluation), so `zcse_refines` applies: the output returns
`decodedLen(10, NoPadding) = 7`, as the source does.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof GoFV.Proof.ZCSE

def dlCheckEnv : CheckEnv :=
  { tabs := dlTabs, typs := #[("Int", 2), ("Mem", 29), ("Bool", 4)] }

def dlPassEnv : PassEnv where
  passName := "zero arg cse"
  pkg := GoStr.ofString "encoding/base64"
  funcName := GoStr.ofString "decodedLen"
  abi := 1
  nosplit := false
  pgohot := false
  config := #[("softfloat", #[.word "0"])]
  typs := #[]
  typeOrder := default
  tables := dlTabs

theorem decodedLen_checks :
    (check dlCheckEnv decodedLen).toBool = true ∧
    ZCSE.zrel dlTabs decodedLen (zcse decodedLen) = true ∧
    (check dlCheckEnv (zcse decodedLen)).toBool = true ∧
    ((zcse decodedLen).value? 23).map (·.args) = some #[12, 13] ∧
    ((zcse decodedLen).value? 12).map (·.args) = some #[7, 13] := by
  decide +kernel

theorem zcse_witness :
    ∃ out, zcsePass dlPassEnv decodedLen = .ok out ∧
      (out.func.value? 23).map (·.args) = some #[12, 13] ∧
      ∃ fuel m, run Env.p1 out.tables out.func dlArgs {} fuel = .returned [.i64 7] m := by
  obtain ⟨h1, h2, h3, h4, -⟩ := decodedLen_checks
  obtain ⟨m, hm⟩ := returnsInt_iff.1 decodedLen_run
  have hf : check dlCheckEnv decodedLen = .ok () := by
    revert h1; cases check dlCheckEnv decodedLen <;> simp [Except.toBool]
  have hz : zcseChecked dlTabs decodedLen = zcse decodedLen := by
    simp only [zcseChecked, h2, ite_true]
  have hg : check dlCheckEnv (zcseChecked dlTabs decodedLen) = .ok () := by
    rw [hz]; revert h3; cases check dlCheckEnv (zcse decodedLen) <;> simp [Except.toBool]
  have hp : zcsePass dlPassEnv decodedLen =
      .ok { func := zcseChecked dlTabs decodedLen, tables := dlTabs } := rfl
  refine ⟨_, hp, by rw [hz]; exact h4, ?_⟩
  obtain ⟨fuel, h⟩ := Refines.returned_int (zcse_refines hp hf hg) hm
  exact ⟨fuel, m, h⟩

end GoFV.Proof.Witness

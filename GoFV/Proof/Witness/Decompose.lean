import GoFV.Proof.Pass.Decompose
import GoFV.Proof.Witness.DecPhis
import GoFV.Proof.Witness.TabsAgreeMod

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witnesses: decompose user and decompose builtin

decompose user on `pair` (a struct `Phi`) and decompose builtin on `strconv.FormatBool` (a
string `Phi`): by kernel evaluation, the checked stages accept the phi stage's outputs
(`pairOut`, `formatBoolOut`; the dec rules fire nowhere in `formatBoolOut`, so its rewrite is
itself with an empty log), so `refinesFrom_of_decUserOK`/`refinesFrom_of_decBuiltinStagesOK`
apply. That the passes compute these outputs and that `decUserFrag`/`decBuiltinFrag` accept the
inputs is checked by running them (`GoFVTest/Proof/DecomposeFrag.lean`; the passes' state
uses `Std.HashMap`, which the kernel does not evaluate). `DecPre` holds of `Env.p1` and inputs
without pointers (`decPre_p1`).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.Decompose GoFV.Proof GoFV.Proof.Decompose

/-- decompose user's output on `pair`. -/
def pairDecOut : PassOut := { func := pairOut, tables := pairTabs }

/-- decompose builtin's output on `formatBool`. -/
def formatBoolDecOut : PassOut := { func := formatBoolOut, tables := formatBoolTabs }

theorem pair_decUserOK :
    (check { tabs := pairTabs, typs := fbTyps } pair).toBool = true ∧
      (check { tabs := pairTabs, typs := fbTyps } pairOut).toBool = true ∧
      decUserOK (fbPassEnv "decompose user" pairTabs) pair pairDecOut = true := by
  decide +kernel

theorem formatBool_decBuiltinStagesOK :
    (check { tabs := formatBoolTabs, typs := fbTyps } formatBool).toBool = true ∧
      decBuiltinStagesOK (fbPassEnv "decompose builtin" formatBoolTabs) formatBool formatBoolOut
        formatBoolOut #[] formatBoolDecOut = true := by
  decide +kernel

/-- **Non-vacuity of `decomposeUser_refines`'s checked stages**: `pair`'s struct `Phi` `v11`
becomes a `StructMake`, and the output refines the input for `DecPre`. -/
theorem decomposeUser_witness :
    (pair.value? 11).map (·.op) = some .Phi ∧ (pairOut.value? 11).map (·.op) = some .StructMake ∧
      RefinesFrom DecPre pairTabs pairOut pairTabs pair := by
  obtain ⟨hcf, hcg, hok⟩ := pair_decUserOK
  have r := refinesFrom_of_decUserOK hok (ok_of_toBool hcf) (ok_of_toBool hcg)
  rw [show pairDecOut.tables = pairTabs from rfl, show pairDecOut.func = pairOut from rfl,
    show (fbPassEnv "decompose user" pairTabs).tables = pairTabs from rfl] at r
  exact ⟨decPhis_pair_witness.1, decPhis_pair_witness.2.1, r⟩

/-- **Non-vacuity of `decomposeBuiltin_refines`'s checked stages**: `FormatBool`'s string
`Phi` `v11` becomes a `StringMake`, and the output refines the input for `DecPre`. -/
theorem decomposeBuiltin_witness :
    (formatBool.value? 11).map (·.op) = some .Phi ∧
      (formatBoolOut.value? 11).map (·.op) = some .StringMake ∧
      RefinesFrom DecPre formatBoolTabs formatBoolOut formatBoolTabs formatBool := by
  obtain ⟨hcf, hok⟩ := formatBool_decBuiltinStagesOK
  have r := refinesFrom_of_decBuiltinStagesOK hok (ok_of_toBool hcf)
  rw [show formatBoolDecOut.tables = formatBoolTabs from rfl,
    show formatBoolDecOut.func = formatBoolOut from rfl,
    show (fbPassEnv "decompose builtin" formatBoolTabs).tables = formatBoolTabs from rfl] at r
  exact ⟨decPhis_formatBool_witness.1, decPhis_formatBool_witness.2.1, r⟩

/-- `DecPre` is satisfiable: `Env.p1` with `clamp`'s integer arguments and the empty memory. -/
theorem decPre_p1 (x : BitVec 64) : DecPre Env.p1 (clampArgs x) {} :=
  ⟨Env.p1_mono, p1_tempOblivious, clampArgs_initAvoids x⟩

end GoFV.Proof.Witness

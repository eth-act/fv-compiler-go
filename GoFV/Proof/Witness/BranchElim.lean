import GoFV.Proof.Pass.BranchElimPass
import GoFV.Proof.Witness.Max3

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: branchelim on `max3`

branchelim merges both if-triangles of `max3` (each rewrite accepted by the step checker; the
function becomes one `Ret` block, by kernel evaluation), so by `branchelim_refines` the output
returns `max3(1, 7, 4) = 7`, as the source does. `branchelim_pres_witness`: a rewrite of `max3`
accepted by the step checker, from a checked input, satisfies the hypotheses of `DRel.wf_pres`
and `DRel.useDom_pres`.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof GoFV.Proof.BranchElim

def max3PassEnv : PassEnv where
  passName := "branchelim"
  pkg := GoStr.ofString "main"
  funcName := GoStr.ofString "max3"
  abi := 1
  nosplit := false
  pgohot := false
  config := #[("arch", #[.word "arm64"]), ("regsize", #[.word "8"]),
    ("havecondselect", #[.word "1"])]
  typs := #[("Bool", 3), ("Int", 2), ("Uintptr", 15), ("Mem", 28), ("Void", 30)]
  typeOrder := default
  tables := max3Tabs

/-- branchelim turns `max3` into one `Ret` block whose two `Phi`s are `CondSelect`s. -/
theorem max3_branchelim :
    (match branchelimPass max3PassEnv max3 with
      | .ok out => decide ((out.func.block? 1).map (·.kind) = some .Ret) &&
          decide ((out.func.value? 15).map (·.op) = some .CondSelect) &&
          decide ((out.func.value? 18).map (·.op) = some .CondSelect)
      | .error _ => false) = true := by
  decide +kernel

theorem branchelim_witness :
    ∃ out, branchelimPass max3PassEnv max3 = .ok out ∧
      (out.func.block? 1).map (·.kind) = some .Ret ∧
      ∃ fuel m, run Env.p1 out.tables out.func max3Args {} fuel = .returned [.i64 7] m := by
  have h1 := max3_branchelim
  obtain ⟨m, hm⟩ := returnsInt_iff.1 max3_run
  cases hp : branchelimPass max3PassEnv max3 with
  | error e => rw [hp] at h1; cases h1
  | ok out =>
    rw [hp] at h1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    obtain ⟨fuel, m', h⟩ := Refines.returned_int (branchelim_refines hp) hm
    exact ⟨out, rfl, h1.1.1, fuel, m', h⟩

def max3CE : CheckEnv := { tabs := max3PassEnv.tables, typs := max3PassEnv.typs }

/-- `max3` (with its cached postorder) passes `check`, and `elimIf` at one of its blocks
proposes a rewrite the step checker accepts (kernel evaluation). -/
theorem max3_step :
    (checkOK max3CE max3.postorder.2 &&
      match GoFV.Opt.BranchElim.ctxOf max3PassEnv max3.postorder.2 max3.postorder.1 with
      | .ok c => max3.postorder.2.blocks.toList.any fun b =>
          match GoFV.Opt.BranchElim.elimIf c max3.postorder.2 b with
          | .ok (some g) => GoFV.Opt.BranchElim.stepOK max3.postorder.2 g b
          | _ => false
      | .error _ => false) = true := by
  decide +kernel

theorem branchelim_pres_witness :
    ∃ (f g : Func) (s : GoFV.Opt.BranchElim.Site) (ce : CheckEnv),
      DRel f g s ∧ Dom.WFDom ce f ∧ WF ce g ∧ Dom.UseDom g := by
  have h := max3_step
  rw [Bool.and_eq_true] at h
  obtain ⟨hck, h⟩ := h
  split at h
  · obtain ⟨b, -, hb⟩ := List.any_eq_true.1 h
    split at hb
    · rename_i g _
      obtain ⟨s, hrel⟩ := stepOK_sound hb
      have hwd := Dom.WFDom.of_check (checkOK_sound hck)
      exact ⟨_, g, s, _, hrel, hwd, hrel.wf_pres hwd.wf, hrel.useDom_pres hwd.wf hwd.dom⟩
    · cases hb
  · cases h

end GoFV.Proof.Witness

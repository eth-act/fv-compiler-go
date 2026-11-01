import GoFV.Proof.Pass.PhiOpt
import GoFV.Proof.Witness.TraceFP

/-!
# Non-vacuity witness: phiopt on `tracefpunwindoff`

phiopt changes `tracefpunwindoff` (the `Phi` `v11` of `true` and `false` becomes `Copy v10`,
the control of the entry's `If`), its checker accepts the result, and input and output pass
`check` (all by kernel evaluation), so `phiopt_refines` applies: the output returns `true`
when `debug.tracefpunwindoff = 1`, as the source does.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof GoFV.Proof.PhiOpt

def tfCheckEnv : CheckEnv :=
  { tabs := tfTabs, typs := #[("Bool", 2), ("Int32", 5), ("UInt8", 7), ("Uintptr", 15),
      ("Mem", 28)] }

def tfPassEnv : PassEnv where
  passName := "phiopt"
  pkg := GoStr.ofString "runtime"
  funcName := GoStr.ofString "tracefpunwindoff"
  abi := 1
  nosplit := false
  pgohot := false
  config := #[("softfloat", #[.word "0"])]
  typs := #[("UInt8", 7)]
  typeOrder := default
  tables := tfTabs

theorem tracefp_checks :
    (check tfCheckEnv tracefp).toBool = true ∧
    (phiopt tfTabs 7 tracefp).toOption.map (PhiOpt.prel tfTabs tracefp) = some true ∧
    (phiopt tfTabs 7 tracefp).toOption.map (fun g => (check tfCheckEnv g).toBool) = some true ∧
    (phiopt tfTabs 7 tracefp).toOption.map (fun g => (g.value? 11).map fun v => (v.op, v.args)) =
      some (some (.Copy, #[10])) := by
  decide +kernel

theorem phiopt_witness :
    ∃ out, phioptPass tfPassEnv tracefp = .ok out ∧
      (out.func.value? 11).map (fun v => (v.op, v.args)) = some (.Copy, #[10]) ∧
      ∃ fuel m, run Env.p1 out.tables out.func [] (tfMem 1) fuel = .returned [.bool true] m := by
  obtain ⟨h1, h2, h3, h4⟩ := tracefp_checks
  obtain ⟨m, hm⟩ := returnsBool_iff.1 tracefp_run.1
  have hf : check tfCheckEnv tracefp = .ok () := by
    revert h1; cases check tfCheckEnv tracefp <;> simp [Except.toBool]
  cases hp : phiopt tfTabs 7 tracefp with
  | error e => rw [hp] at h2; cases h2
  | ok g =>
    rw [hp] at h2 h3 h4
    simp only [Except.toOption, Option.map_some, Option.some.injEq] at h2 h3 h4
    have hc : phioptChecked tfTabs 7 tracefp = .ok g := by
      simp only [phioptChecked, hp, bind, Except.bind, h2, ite_true, pure, Except.pure]
    have hg : check tfCheckEnv g = .ok () := by
      revert h3; cases check tfCheckEnv g <;> simp [Except.toBool]
    have hpass : phioptPass tfPassEnv tracefp = .ok { func := g, tables := tfTabs } := by
      have hu : tfPassEnv.typ? "UInt8" = some 7 := rfl
      have ht : tfPassEnv.tables = tfTabs := rfl
      simp only [phioptPass, Pass.ofFunc, hu, ht, hc, bind, Except.bind, pure, Except.pure]
    refine ⟨_, hpass, by simpa using h4, ?_⟩
    have hr := phiopt_refines hpass hf (ce' := tfCheckEnv) hg
    have hm' : run Env.p1 tfPassEnv.tables tracefp [] (tfMem 1) 2 = .returned [.bool true] m := hm
    obtain ⟨fuel', ho⟩ := hr Env.p1 [] (tfMem 1) 2 (by rw [hm']; trivial)
    rw [hm'] at ho
    refine ⟨fuel', ?_⟩
    generalize run Env.p1 tfTabs g [] (tfMem 1) fuel' = o at ho ⊢
    cases ho with
    | returned hl =>
      cases hl with
      | cons h1 t =>
        cases t
        cases h1
        exact ⟨_, rfl⟩

end GoFV.Proof.Witness

import GoFV.Proof.Pass.DeadSim
import GoFV.Proof.Pass.DeadFrag
import GoFV.Proof.Pass.DeadTail
import GoFV.Proof.Pass.CopyElimWF

variable [GoFV.SSA.Sem.Addrs]

/-!
# deadcode refines its input (all five instances)

`deadcode = edges ; copyelim ; deadTail` (`deadcode_eq`, `edgesG_true`). With `f1' = edgesG false f`
(deadcode's edge removal where `Phi`s only lose arguments), `f1 = edgesG true f` (the real one)
and `f2 = copyelim f1`, the output `g` refines `f` by three refinements:

1. `f1'` refines `f` (`refines_of_deadRel`): `f1'` is well formed and keeps the reachable blocks
   of `f`, their values and the edges a run takes (`ei_edgesG`, `wf_of_ei`, `deadRel_of_ei`);
2. `f2` refines `f1'` (copyelim's `refines_of_rel`): `f1` is a state of copyelim's sweeps
   started at `f1'` (`j_edgesG`, `inv_of_j`), so `copyelim_rel_of_inv` relates `f1'` and `f2`,
   and `copyelim_wf_of_inv` makes `f2` well formed;
3. `g` refines `f2` (`refines_of_deadRel` with `deadTail_rel`).

`deadcode_refines` assumes `check` on input and output and the input fragment `DeadFrag`
(conditions on the input only, decided by `deadFragB`).
-/

namespace GoFV.Proof.Dead

open GoFV.SSA GoFV.Opt GoFV.Proof GoFV.Proof.CopyElim

/-- **deadcode refines its input** (`early`, `pre-opt`, `opt`, `gcse` and `generic deadcode`). -/
theorem deadcode_refines {penv : PassEnv} {f : Func} {out : PassOut} {ce ce' : CheckEnv}
    (h : deadcodePass penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) (hfrag : DeadFrag penv.tables f) :
    Refines out.tables out.func penv.tables f := by
  simp only [deadcodePass, Pass.ofFunc, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i g hd
    cases h
    rw [deadcode_eq, ← edgesG_true] at hd
    cases hc : copyelim penv.tables (edgesG true f) with
    | error e => rw [hc] at hd; cases hd
    | ok f2 =>
    rw [hc] at hd
    have hwf := check_wf hf
    have hwg := check_wf hg
    have hE := ei_edgesG hwf hfrag.firstTwo
    have hwf1 := wf_of_ei hwf hE
    have hI := inv_of_j hwf hE (j_edgesG hwf hfrag.firstTwo) hfrag.copy2
    obtain ⟨hwf2, hsz, hvl⟩ := copyelim_wf_of_inv hwf1 hfrag.copy1 hI hc
    have r1 : Refines penv.tables (edgesG false f) penv.tables f :=
      refines_of_deadRel ⟨⟨ce, hwf⟩, ⟨ce, hwf1⟩, deadRel_of_ei hwf hfrag.bid hE⟩
    have r2 : Refines penv.tables f2 penv.tables (edgesG false f) :=
      refines_of_rel ⟨⟨ce, hwf1⟩, ⟨ce, hwf2⟩, hfrag.cert1, hfrag.cert2 f2 hc,
        copyelim_rel_of_inv hwf1 hfrag.copy1 hI hc, hfrag.empty⟩
    have hs2 : f2.valueTab.size ≤ f2.vidLast + 1 := by rw [hsz, hvl]; exact hfrag.copy1.size
    have r3 : Refines penv.tables g penv.tables f2 :=
      refines_of_deadRel ⟨⟨ce, hwf2⟩, ⟨ce', hwg⟩, deadTail_rel hwg hs2 hd⟩
    exact r1.trans (r2.trans r3)

end GoFV.Proof.Dead

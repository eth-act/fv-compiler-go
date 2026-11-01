import GoFV.Opt.DecomposeCheck
import GoFV.Proof.Pass.DecPhiSim
import GoFV.Proof.Pass.Rewrite
import GoFV.Proof.Rules.Proven
import GoFV.Proof.TabsAgreeMod

/-!
# decompose user, decompose builtin refine their input (issue #17)

On inputs in the checked fragment (`decUserFrag`/`decBuiltinFrag`, GoFV/Opt/DecomposeCheck.lean)
each pass is a chain of checked stages, all read in the output tables `T`:

1. the input `f` in its own tables is `f` in `T` (`refinesFrom_of_tabsAgreeMod`: `T` only
   adds frame temporaries for the split names, which `f` cannot reach; for environments whose
   contracts ignore such temporaries and inputs holding no pointer into a frame temporary);
2. the phi splits refine `f` (`decPhis_refines`);
3. decompose builtin: the dec-rule rewrite with the proven dec rules refines the phi stage
   (`validate_refines` with `dec_allSound`);
4. the names stage only changes `f.Names`/`NamedValues`/the canonical splits, which the
   semantics never reads (`run_stripNames`).
-/

namespace GoFV.Proof.Decompose

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.Decompose GoFV.Proof

/-- The semantics never reads the name bookkeeping. -/
theorem run_stripNames (env : Env) (tabs : Tables) (f : Func) (args : List Val) (mem : Mem)
    (fuel : Nat) : run env tabs (stripNames f) args mem fuel = run env tabs f args mem fuel := by
  have hv : ∀ id, ((stripNames f).value? id).map eraseV = (f.value? id).map eraseV :=
    fun _ => rfl
  have hc : CtxEq (Ctx.make tabs (stripNames f)) (Ctx.make tabs f) :=
    ⟨rfl, rfl, sched_make tabs hv rfl, rfl, rfl, rfl, rfl, rfl, hv, fun _ => rfl⟩
  show runCtx env (Ctx.make tabs (stripNames f)) args mem fuel = runCtx env (Ctx.make tabs f) args mem fuel
  unfold runCtx
  rw [hc.params]
  split
  · rfl
  · rw [runLoop_congr hc, hc.outs, hc.act, entryFrame_ctx hc rfl]
    rfl

/-- Functions with the same code have the same runs. -/
theorem refines_of_sameCode {tabs : Tables} {f g : Func} (h : sameCode f g = true) :
    Refines tabs g tabs f :=
  Refines.of_run_eq fun env args mem fuel => by
    rw [← run_stripNames env tabs g, ← run_stripNames env tabs f]
    exact run_congr (of_decide_eq_true h).symm env tabs args mem fuel

theorem check_of_isOk {ce : CheckEnv} {f : Func} (h : (check ce f).isOk = true) :
    check ce f = .ok () := by
  cases hc : check ce f with
  | ok u => rfl
  | error e => rw [hc] at h; cases h

/-- The environments and inputs of the decompose theorems: monotone contracts that ignore
frame temporaries they are given no pointer into, and inputs holding no pointer into a frame
temporary. -/
def DecPre (env : Env) (args : List Val) (mem : Mem) : Prop :=
  env.Mono ∧ env.TempOblivious ∧ InitAvoids env args mem

theorem decPre_tabs : ∀ env args mem, DecPre env args mem → env.TempOblivious ∧ InitAvoids env args mem :=
  fun _ _ _ h => h.2

theorem decPre_mono {tabs tabs' : Tables} {f g : Func} (h : RefinesUnder Env.Mono tabs' g tabs f) :
    RefinesFrom DecPre tabs' g tabs f :=
  RefinesFrom.mono (fun _ _ _ hp => hp.1) h.from

/-- **decompose user refines its input** (on inputs in `decUserFrag`). -/
theorem decomposeUser_refines {penv : PassEnv} {f : Func} {out : PassOut} {ce ce' : CheckEnv}
    (h : decomposeUserPass penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) (hfrag : decUserFrag penv f = true) :
    RefinesFrom DecPre out.tables out.func penv.tables f := by
  unfold decUserFrag at hfrag
  rw [h] at hfrag
  simp only [decUserOK, Bool.and_eq_true] at hfrag
  exact refinesFrom_of_tabsAgreeMod decPre_tabs hfrag.1 hf
    (decPre_mono (DecPhi.decPhis_refines hfrag.2 hf hg))

/-- **decompose builtin refines its input** (on inputs in `decBuiltinFrag`). -/
theorem decomposeBuiltin_refines {penv : PassEnv} {f : Func} {out : PassOut} {ce ce' : CheckEnv}
    (h : postExpandCallsDecomposePass penv f = .ok out) (hf : check ce f = .ok ())
    (_hg : check ce' out.func = .ok ()) (hfrag : decBuiltinFrag penv f = true) :
    RefinesFrom DecPre out.tables out.func penv.tables f := by
  unfold decBuiltinFrag at hfrag
  rw [h] at hfrag
  unfold decBuiltinOK at hfrag
  split at hfrag
  · cases hfrag
  · rename_i t1 g1 _
    split at hfrag
    · cases hfrag
    · rename_i o2 n log _
      simp only [Bool.and_eq_true] at hfrag
      obtain ⟨⟨⟨⟨⟨⟨hta, hphi⟩, hc1⟩, hc2⟩, hagree⟩, hv⟩, hsame⟩ := hfrag
      have hg1 := check_of_isOk hc1
      have hg2 := check_of_isOk hc2
      have r1 := DecPhi.decPhis_refines hphi hf hg1
      have r2 := Pass.Rewrite.validate_refines Rules.dec_allSound hv hagree hg1 hg2
      have r3 : Refines out.tables out.func out.tables o2.func := refines_of_sameCode hsame
      exact refinesFrom_of_tabsAgreeMod decPre_tabs hta hf
        (decPre_mono ((r1.trans r2).trans (r3.under _)))

end GoFV.Proof.Decompose

import GoFV.Opt.DecomposeCheck
import GoFV.Proof.Pass.DecPhiSim
import GoFV.Proof.Pass.CopyRelCheck
import GoFV.Proof.Pass.CopyElim
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
   (`Pass.Rewrite.layersOK_refines` with `dec_allSound`: its value-rule `Load` expansions, its
   `Store` splits (`StructStore.ss_refines`, in place for the builtin `Make`s), then the
   validator with the other events); with phi eliminations in the log, in segments between them
   (`decSegsOK`, as `RewriteCheck.segsOK`): each segment refines, and at each elimination the
   function with the `Phi` turned copy refines the logged one by copyelim's simulation
   (`CopyRelCheck.copyOK_spec`, `CopyElim.refines_of_rel`);
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

/-- An output `decUserOK` accepts refines the input. -/
theorem refinesFrom_of_decUserOK {penv : PassEnv} {f : Func} {out : PassOut} {ce ce' : CheckEnv}
    (hok : decUserOK penv f out = true) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) :
    RefinesFrom DecPre out.tables out.func penv.tables f := by
  simp only [decUserOK, Bool.and_eq_true] at hok
  exact refinesFrom_of_tabsAgreeMod decPre_tabs hok.1 hf
    (decPre_mono (DecPhi.decPhis_refines hok.2 hf hg))

/-- The segments of the decompose rewrite's log refine (`decSegsOK`, as `Pass.Rewrite.segs_refines`
with the decompose layers under `Env.Mono`). -/
theorem refines_of_decSegsOK {penv : PassEnv} {T : Tables} {f0 g2 : Func}
    (hg2 : check (decCheckEnv penv T) g2 = .ok ()) :
    ∀ (evs : List Rules.RwEvent) (f : Func) (seg : Array Rules.RwEvent) {ce : CheckEnv},
      check ce f = .ok () → decSegsOK penv T f0 g2 f seg evs = true →
      RefinesUnder Env.Mono T g2 T f
  | [], f, seg, _, hf, h =>
    Pass.Rewrite.layersOK_refines (out := { func := g2, tables := T }) Rules.dec_allSound
      hg2 RewriteCheck.decLayers (by simp [RewriteCheck.decLayers]) f seg hf h
  | ev :: evs, f, seg, _, hf, h => by
    cases ev with
    | phielim v d pre =>
      simp only [decSegsOK, Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
      have hh := checkOK_sound h2
      have hh' := checkOK_sound h4
      obtain ⟨hrel, hfr⟩ := CopyRelCheck.copyOK_spec h3
      have R2 := CopyElim.refines_of_rel (tabs := T)
        ⟨⟨_, check_wf hh⟩, ⟨_, check_wf hh'⟩, Dom.certOK_of_check (check_domCert hh),
          Dom.certOK_of_check (check_domCert hh'), hrel, hfr⟩
      exact ((Pass.Rewrite.layersOK_refines (out := { func := RewriteCheck.dropInvalid pre, tables := T })
        Rules.dec_allSound hh RewriteCheck.decLayers (by simp [RewriteCheck.decLayers]) f seg hf
        h1).trans (R2.under _)).trans (refines_of_decSegsOK hg2 evs _ #[] hh' h5)
    | _ =>
      simp only [decSegsOK] at h
      exact refines_of_decSegsOK hg2 evs f _ hf h

/-- The rewrite stage refines its input (`decRewriteOK`). -/
theorem refines_of_decRewriteOK {penv : PassEnv} {T : Tables} {g1 g2 : Func}
    {log : Array Rules.RwEvent} {ce : CheckEnv} (hok : decRewriteOK penv T g1 g2 log = true)
    (hg1 : check ce g1 = .ok ()) (hg2 : check (decCheckEnv penv T) g2 = .ok ()) :
    RefinesUnder Env.Mono T g2 T g1 :=
  refines_of_decSegsOK hg2 log.toList g1 #[] hg1 hok

/-- Checked stages of decompose builtin refine the input. -/
theorem refinesFrom_of_decBuiltinStagesOK {penv : PassEnv} {f g1 g2 : Func}
    {log : Array Rules.RwEvent}
    {out : PassOut} {ce : CheckEnv} (hok : decBuiltinStagesOK penv f g1 g2 log out = true)
    (hf : check ce f = .ok ()) :
    RefinesFrom DecPre out.tables out.func penv.tables f := by
  simp only [decBuiltinStagesOK, Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨hta, hphi⟩, hc1⟩, hc2⟩, hv⟩, hsame⟩ := hok
  have hg1 := check_of_isOk hc1
  have hg2 := check_of_isOk hc2
  have r1 := DecPhi.decPhis_refines hphi hf hg1
  have r2 : RefinesUnder Env.Mono out.tables g2 out.tables g1 := refines_of_decRewriteOK hv hg1 hg2
  have r3 : Refines out.tables out.func out.tables g2 := refines_of_sameCode hsame
  exact refinesFrom_of_tabsAgreeMod decPre_tabs hta hf
    (decPre_mono ((r1.trans r2).trans (r3.under _)))

/-- **decompose user refines its input** (on inputs in `decUserFrag`). -/
theorem decomposeUser_refines {penv : PassEnv} {f : Func} {out : PassOut} {ce ce' : CheckEnv}
    (h : decomposeUserPass penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) (hfrag : decUserFrag penv f = true) :
    RefinesFrom DecPre out.tables out.func penv.tables f := by
  simp only [decUserFrag, h] at hfrag
  exact refinesFrom_of_decUserOK hfrag hf hg

/-- **decompose builtin refines its input** (on inputs in `decBuiltinFrag`). -/
theorem decomposeBuiltin_refines {penv : PassEnv} {f : Func} {out : PassOut} {ce ce' : CheckEnv}
    (h : postExpandCallsDecomposePass penv f = .ok out) (hf : check ce f = .ok ())
    (_hg : check ce' out.func = .ok ()) (hfrag : decBuiltinFrag penv f = true) :
    RefinesFrom DecPre out.tables out.func penv.tables f := by
  simp only [decBuiltinFrag, h, decBuiltinOK] at hfrag
  cases hs : phiStage penv true f with
  | error e => rw [hs] at hfrag; cases hfrag
  | ok p =>
    obtain ⟨t1, g1⟩ := p
    rw [hs] at hfrag
    simp only at hfrag
    cases hr : Rules.rewriteRun decProvenTable false true { penv with tables := t1 } g1 with
    | error e => rw [hr] at hfrag; cases hfrag
    | ok q =>
      obtain ⟨o2, n, log⟩ := q
      rw [hr] at hfrag
      exact refinesFrom_of_decBuiltinStagesOK hfrag hf

end GoFV.Proof.Decompose

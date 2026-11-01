import GoFV.Proof.Pass.DSEVal

/-!
# dse: one value's step

`step_ok`: a value the source evaluates evaluates in the target to a related register (see
`GoFV.Proof.Pass.DSEVal`); `step_panic`: a panicking value panics alike in the target.
-/

namespace GoFV.Proof.DSE

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.DSE GoFV.Proof.CSE GoFV.Proof.CSE.Mem

variable {env : Env} {tabs : Tables} {f g : Func} {P : ID → List Iv}

theorem ctx_facts (hrel : DRel tabs f g P) :
    (Ctx.make tabs g).tabs = (Ctx.make tabs f).tabs ∧
      (Ctx.make tabs g).params = (Ctx.make tabs f).params ∧
      (Ctx.make tabs g).act = (Ctx.make tabs f).act := by
  refine ⟨rfl, ?_, rfl⟩
  simp only [Ctx.make, abiParams, hrel.ownAux]

theorem chain_ne_copy {op : Op} (h : chainOp op = true) : op ≠ .Copy := by
  rintro rfl; exact absurd h (by decide)

theorem chain_not_blind {op : Op} (h : chainOp op = true) : blindOp op = false := by
  unfold chainOp at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((h | h) | h) | h <;> (rw [h]; rfl)

/-- The argument registers when every argument without pending ranges is equal. -/
theorem argVals_same {S T : Frame} {as : Array ID}
    (h : ∀ a ∈ as, ∃ vS vT, S.regs[a]? = some (some vS) ∧ T.regs[a]? = some (some vT) ∧ vT = vS) :
    argVals T as = argVals S as :=
  argVals_eq rfl fun k a ha => by
    obtain ⟨vS, vT, h1, h2, he⟩ := h a (Array.mem_of_getElem? ha)
    exact ⟨a, vS, ha, h1, he ▸ h2⟩

/-- **One value the source evaluates.** -/
theorem step_ok (hrel : DRel tabs f g P) {S T : Frame} {A : ID → Prop}
    (H : Avail env tabs f S A) (hT : T = { S with regs := T.regs })
    {x : ID} {fv gv : Value} (hfv : f.value? x = some fv) (hgv : g.value? x = some gv)
    (hid : fv.id = x) (hA : ∀ a ∈ fv.args, A a)
    (hargs : ∀ a ∈ gv.args, ∃ vS vT, S.regs[a]? = some (some vS) ∧
      T.regs[a]? = some (some vT) ∧ VRel (IvQ (P a)) vS vT)
    {y : Val} (hy : evalValue env (Ctx.make tabs f) S fv = .ok y) :
    ∃ y', evalValue env (Ctx.make tabs g) T gv = .ok y' ∧ VRel (IvQ (P x)) y y' := by
  have hx := lt_of_value? hfv
  have hpend := hrel.pend x hx
  obtain ⟨htabs, hpar, hact⟩ := ctx_facts hrel
  obtain ⟨vs, hvs⟩ := argVals_of_eval (env := env) (ctx := Ctx.make tabs f)
    (fun msg h => by rw [hy] at h; cases h)
  rw [evalValue_of_argVals hvs] at hy
  obtain ⟨r, hr, rfl⟩ := bind_ok hy
  obtain ⟨gv', hgv', hsv⟩ := hrel.value x fv hfv
  rw [hgv] at hgv'; cases hgv'
  -- the source argument registers `vs` and `x`'s arguments
  have hP0 : ∀ (Q : Ptr) (L : List Val), vs = .ptr Q :: L → ∀ p, fv.args[0]? = some p →
      S.regs[p]? = some (some (.ptr Q)) := by
    intro Q L hvsE p hp
    obtain ⟨v, hv, hr'⟩ := argVals_get hvs hp
    rw [hvsE] at hv; simp at hv; subst hv; exact hr'
  rcases hsv with hs | he
  · -- a kept value
    obtain ⟨hgid, hgop, hgax, hgai, hgty, -, hgargs⟩ := sameV_spec hs
    rw [hgargs] at hargs
    have htyG : (Ctx.make tabs g).tys[gv.id]? = (Ctx.make tabs f).tys[fv.id]? := by
      rw [hgid, hid, tys_of_value hgv, tys_of_value hfv, hgty]
    have hevT : ∀ vs', argVals T gv.args = some vs' →
        evalValue env (Ctx.make tabs g) T gv =
          (evalOp env (Ctx.make tabs f) S fv vs' ((Ctx.make tabs f).tys[fv.id]?.getD .other)).bind
            fun r => .ok (r.retype ((Ctx.make tabs f).tys[fv.id]?.getD .other)) := by
      intro vs' h'
      rw [evalValue_of_argVals h', htyG, hT, evalOp_frame,
        evalOp_congr hgop hgax hgai hgid htabs hpar hact]
    by_cases hall : ∀ a ∈ fv.args, P a = []
    · -- every argument is equal
      have hvsT : argVals T gv.args = some vs := by
        rw [hgargs, ← hvs]
        refine argVals_same fun a ha => ?_
        obtain ⟨vS, vT, h1, h2, h3⟩ := hargs a ha
        rw [hall a ha] at h3
        exact ⟨vS, vT, h1, h2, h3.eq_nil⟩
      rw [hevT vs hvsT, hr]
      exact ⟨_, rfl, .inl rfl⟩
    have hex : ∃ a ∈ fv.args, P a ≠ [] := Classical.byContradiction fun hn =>
      hall fun a ha => Classical.byContradiction fun hp => hn ⟨a, ha, hp⟩
    obtain ⟨a, ha, hpa⟩ := hex
    obtain ⟨-, -, hkind⟩ := uses_spec hfv (hrel.uses x hx) ha hpa
    rcases hkind with hb | ⟨hc, hback, hnot⟩
    · -- `LocalAddr`/`InlMark`
      obtain ⟨vs', hvs'⟩ := argVals_some (fr := T) (as := gv.args) fun a ha => by
        rw [hgargs] at ha
        obtain ⟨_, vT, -, h, -⟩ := hargs a ha
        exact ⟨vT, h⟩
      rw [hevT vs' hvs', evalOp_blind hb vs' vs, hr]
      exact ⟨_, rfl, .inl rfl⟩
    -- a kept memory op after pending ranges
    have hne : elimV fv gv = false := elimV_false_of_sameV hs (chain_ne_copy hc)
    have hpop : ∀ a' ∈ fv.args.pop, T.regs[a']? = S.regs[a']? := by
      intro a' ha'
      have ha'm := mem_of_mem_pop ha'
      by_cases hp' : P a' = []
      · obtain ⟨vS, vT, h1, h2, h3⟩ := hargs a' ha'm
        rw [hp'] at h3
        rw [h1, h2, h3.eq_nil]
      · obtain ⟨-, -, hk'⟩ := uses_spec hfv (hrel.uses x hx) ha'm hp'
        rcases hk' with hb' | ⟨-, hb', hn'⟩
        · rw [chain_not_blind hc] at hb'; cases hb'
        · rw [hback] at hb'; cases hb'; exact absurd ha' hn'
    obtain ⟨vS, vT, hSa, hTa, hVa⟩ := hargs a ha
    have hpm : pm P fv = P a := by unfold pm; rw [hback]
    unfold chainOp at hc
    simp only [Bool.or_eq_true, beq_iff_eq] at hc
    have hop4 : fv.op = .Store ∨ fv.op = .Zero ∨ fv.op = .Move ∨ fv.op = .VarDef := by
      rcases hc with ((h | h) | h) | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr h))
    rw [evalOp_chain hop4] at hr
    rcases hc with ((hop | hop) | hop) | hop
    rotate_right
    · -- `VarDef`
      obtain ⟨M, n, rfl, hax, rfl, htgt⟩ := varDef_shape hop hr
      have hSM : S.regs[a]? = some (some (.mem M)) :=
        argVals_back (L := []) (by simpa using hvs) hback
      rw [hSa] at hSM; cases hSM
      obtain ⟨MT, rfl, hMem⟩ := hVa.mem
      have hvsT : argVals T gv.args = some ([] ++ [.mem MT]) := by
        rw [hgargs]; exact argVals_last (L := []) (by simpa using hvs) hback hpop hTa
      refine ⟨_, by rw [hevT _ hvsT, evalOp_chain hop4]; simp only [List.nil_append, htgt]; rfl,
        VRel.retype_mem _ ((hMem.poison _).mono ?_)⟩
      intro b k ⟨hq, hb⟩
      rw [pend_varDef hfv hgv hne hop hpend, hax, hpm]
      exact ivQ_filter hq hb
    all_goals
      have hop3 : fv.op = .Store ∨ fv.op = .Zero ∨ fv.op = .Move := by simp [hop]
      obtain ⟨p, L, M, bs, M1, hvsE, hw, rfl, hbs, -, htgt⟩ := write_shape hop3 hr
      have hvs2 : argVals S fv.args = some ((.ptr p :: L) ++ [.mem M]) := by rw [hvs, hvsE]; rfl
      have hSM := argVals_back hvs2 hback
      rw [hSa] at hSM; cases hSM
      obtain ⟨MT, rfl, hMem⟩ := hVa.mem
      have hvsT : argVals T gv.args = some ((.ptr p :: L) ++ [.mem MT]) := by
        rw [hgargs]; exact argVals_last hvs2 hback hpop hTa
      have hrd : ∀ s, fv.op = .Move → L = [.ptr s] → MT.read s bs.size = M.read s bs.size := by
        intro s hm hL
        obtain ⟨sid, al, hs1, hal, hall', -⟩ :=
          pend_move hfv hgv hne hm (by rw [hpm]; exact hpa) hpend
        have hsv : S.regs[sid]? = some (some (.ptr s)) := by
          obtain ⟨v, hv, hr'⟩ := argVals_get hvs hs1
          rw [hvsE, hL] at hv; simp at hv; subst hv; exact hr'
        have hblk := (ptrAlloc_val H (hA sid (Array.mem_of_getElem? hs1)) hal hsv).1
        refine hMem.read s _ fun k => ?_
        rw [hblk, ← hpm]
        exact ivQ_not_alloc hall' k
      obtain ⟨M1', hw', hM1⟩ := hMem.write hw
      refine ⟨_, by rw [hevT _ hvsT, evalOp_chain hop4, List.cons_append, htgt MT M1' hrd hw']; rfl,
        VRel.retype_mem _ (hM1.mono ?_)⟩
      intro b k ⟨hq, hnr⟩
      have hPx : P x = match range? tabs f fv with
          | some r => (pm P fv).flatMap (sub r)
          | none => pm P fv := by
        first
          | exact pend_store hfv hgv hne (.inl hop) hpend
          | exact pend_store hfv hgv hne (.inr hop) hpend
          | (obtain ⟨-, -, -, -, -, h⟩ := pend_move hfv hgv hne hop (by rw [hpm]; exact hpa) hpend
             exact h)
      rw [hPx, hpm]
      cases hrr : range? tabs f fv with
      | none => exact hq
      | some rg =>
        refine ivQ_sub hq fun hreg => hnr ?_
        rw [hbs]
        exact (region_range hrr H hA (hP0 p (L ++ [.mem M]) hvsE)).2 hreg
  · -- an eliminated store
    obtain ⟨hop, hgc, -, -, hgid, hgty, -, m, hback, hgargs⟩ := elimV_spec he
    obtain ⟨iv, hrr, hPx⟩ := pend_elim hfv hgv he hpend
    have hop4 : fv.op = .Store ∨ fv.op = .Zero ∨ fv.op = .Move ∨ fv.op = .VarDef := by
      rcases hop with h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
    rw [evalOp_chain hop4] at hr
    obtain ⟨p, L, M, bs, M1, hvsE, hw, rfl, hbs, -, -⟩ := write_shape hop hr
    have hvs2 : argVals S fv.args = some ((.ptr p :: L) ++ [.mem M]) := by rw [hvs, hvsE]; rfl
    have hSM := argVals_back hvs2 hback
    obtain ⟨vS, vT, hSa, hTa, hVa⟩ := hargs m (by rw [hgargs]; simp)
    rw [hSa] at hSM; cases hSM
    obtain ⟨MT, rfl, hMem⟩ := hVa.mem
    have htyG : (Ctx.make tabs g).tys[gv.id]? = (Ctx.make tabs f).tys[fv.id]? := by
      rw [hgid, hid, tys_of_value hgv, tys_of_value hfv, hgty]
    refine ⟨_, evalValue_copy hgc hgargs hTa, ?_⟩
    rw [htyG]
    refine VRel.retype_mem _ ((hMem.write_left hw).mono ?_)
    have hpm : pm P fv = P m := by unfold pm; rw [hback]
    intro b k hbk
    rw [hPx, hpm]
    have hreg : Region p bs.size b k → b = blkOf iv.1 ∧ iv.2.1 ≤ (k : Int) ∧ (k : Int) < iv.2.2 :=
      fun h => by rw [hbs] at h; exact (region_range hrr H hA (hP0 p (L ++ [.mem M]) hvsE)).1 h
    by_cases hlt : iv.2.1 < iv.2.2
    · simp only [hlt, ↓reduceIte]
      rcases hbk with h | h
      · exact ivQ_append (.inl h)
      · exact ivQ_append (.inr (hreg h))
    · simp only [hlt, ↓reduceIte]
      rcases hbk with h | h
      · exact h
      · obtain ⟨-, h1, h2⟩ := hreg h; exact absurd (Int.lt_of_le_of_lt h1 h2) hlt

/-- **A panicking value** reads arguments without pending ranges and panics alike. -/
theorem step_panic (hrel : DRel tabs f g P) {S T : Frame} (hT : T = { S with regs := T.regs })
    {x : ID} {fv gv : Value} (hfv : f.value? x = some fv) (hgv : g.value? x = some gv)
    (hid : fv.id = x)
    (hargs : ∀ a ∈ gv.args, ∃ vS vT, S.regs[a]? = some (some vS) ∧
      T.regs[a]? = some (some vT) ∧ VRel (IvQ (P a)) vS vT)
    {e : Panic} {mm : Mem} (hy : evalValue env (Ctx.make tabs f) S fv = .panic e mm) :
    evalValue env (Ctx.make tabs g) T gv = .panic e mm := by
  have hx := lt_of_value? hfv
  obtain ⟨htabs, hpar, hact⟩ := ctx_facts hrel
  have hop := evalValue_panic_op hy
  obtain ⟨gv', hgv', hsv⟩ := hrel.value x fv hfv
  rw [hgv] at hgv'; cases hgv'
  have hs : sameV fv gv = true := by
    rcases hsv with h | h
    · exact h
    · obtain ⟨h1, -⟩ := elimV_spec h
      rcases h1 with h1 | h1 | h1 <;> rw [h1] at hop <;> rcases hop with h2 | h2 <;>
        exact absurd h2 (by decide)
  obtain ⟨hgid, hgop, hgax, hgai, hgty, -, hgargs⟩ := sameV_spec hs
  rw [hgargs] at hargs
  have hall : ∀ a ∈ fv.args, P a = [] := by
    intro a ha
    refine Classical.byContradiction fun hp => ?_
    obtain ⟨-, -, hk⟩ := uses_spec hfv (hrel.uses x hx) ha hp
    rcases hk with hb | ⟨hc, -⟩
    · unfold blindOp at hb
      simp only [Bool.or_eq_true, beq_iff_eq] at hb
      rcases hb with h | h <;> rw [h] at hop <;> rcases hop with h2 | h2 <;>
        exact absurd h2 (by decide)
    · unfold chainOp at hc
      simp only [Bool.or_eq_true, beq_iff_eq] at hc
      rcases hc with ((h | h) | h) | h <;> rw [h] at hop <;> rcases hop with h2 | h2 <;>
        exact absurd h2 (by decide)
  obtain ⟨vs, hvs⟩ := argVals_some (fr := S) (as := fv.args) fun a ha => by
    obtain ⟨vS, -, h, -⟩ := hargs a ha
    exact ⟨vS, h⟩
  have hvsT : argVals T gv.args = some vs := by
    rw [hgargs, ← hvs]
    refine argVals_same fun a ha => ?_
    obtain ⟨vS, vT, h1, h2, h3⟩ := hargs a ha
    rw [hall a ha] at h3
    exact ⟨vS, vT, h1, h2, h3.eq_nil⟩
  rw [evalValue_rel hgop hgax hgai hgid
    (by rw [hgid, hid, tys_of_value hgv, tys_of_value hfv, hgty]) htabs hpar hact hT hvs
    (.inl hvsT)]
  exact hy

end GoFV.Proof.DSE

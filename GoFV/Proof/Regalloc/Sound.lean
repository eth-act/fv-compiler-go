import GoFV.Proof.Regalloc.Block

/-!
# Regalloc checker soundness, stage 5: the loop and `checkRA_sound`

`docs/plans/regalloc-check.md` §4–§5. Block entries correspond one to one: at the entry of a
block (after the source's `Phi`s) the certificate's facts hold (`EntryInv`); a block's values
(`walk_sim`), its terminator (`term_sim`) and the edge to the next block (`phiEdge_sim`,
`sub_sound`) keep it, so by induction on fuel `runLoopLoc` of the target equals `runLoopL` of the
source whenever the source's outcome is defined (`loop_sim`), and `finish` is the same function
of it on both sides.

**`checkRA_sound`**: when `checkRA tabs f g` accepts, the allocated `g` refines the scheduled `f`
(`RefinesLS`, `GoFV/Proof/RefineLoc.lean`), both in the tables `tabs`: every returning or
panicking `runSched` of `f` is a `runLoc` of `g` with the same outcome and fuel.
-/

namespace GoFV.Proof.RA

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RegallocCheck GoFV.Proof.Low.Sim

variable {tabs : Tables} {f g : Func}

/-! ## What the check accepted -/

theorem block?_lt {F : Func} {d : ID} {b : Block} (h : F.block? d = some b) :
    d < F.blockTab.size := by
  unfold Func.block? at h
  cases hd : F.blockTab[d]? with
  | none => rw [hd] at h; cases h
  | some _ => exact (Array.getElem?_eq_some_iff.1 hd).1

theorem edgesOK_spec {cx : Cx} {cert : Cert} {bid : ID} {S : Facts} :
    ∀ {es : List Edge}, edgesOK cx cert bid S es = .ok () → ∀ e ∈ es,
      ∃ E, phiEdge cx S e.b e.i = .ok E ∧ sub (cert.ins.getD e.b []) E = true
  | [], _, _, he => absurd he List.not_mem_nil
  | e :: es, h, e', he' => by
    simp only [edgesOK, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i E hE
      split at h
      · cases h
      · rename_i hsub
        rcases List.mem_cons.1 he' with rfl | he'
        · exact ⟨E, hE, by simpa using hsub⟩
        · exact edgesOK_spec h e' he'
      all_goals sorry

theorem checkBlocks_spec {cx : Cx} {cert : Cert} :
    ∀ {bids : List ID}, checkBlocks cx cert bids = .ok () → ∀ bid ∈ bids,
      checkBlock cx cert bid = .ok ()
  | [], _, _, h => absurd h List.not_mem_nil
  | b :: bids, h, bid, hb => by
    simp only [checkBlocks, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i r hr
      rcases List.mem_cons.1 hb with rfl | hb
      · cases r; exact hr
      · exact checkBlocks_spec h bid hb

theorem checkBlock_spec {cx : Cx} {cert : Cert} {bid : ID} (h : checkBlock cx cert bid = .ok ())
    {b : Block} (hb : cx.f.block? bid = some b) :
    b.id = bid ∧ ∃ b', cx.g.block? bid = some b' ∧ ∀ order,
      (cx.sc.sched[bid]?).join = some order → ∃ S rest,
        walk cx cert (cert.ins.getD bid []) b'.values.toList order.toList = .ok (S, rest) ∧
        (∀ x ∈ rest, cx.isK x = true) ∧ termOK cx S b b' = .ok () ∧
        edgesOK cx cert bid S b.succs.toList = .ok () := by
  sorry

theorem checkWith_spec {cx : Cx} {cert : Cert} (h : checkWith cx cert = .ok ()) :
    cx.f.lowered = cx.g.lowered ∧ cx.g.entry = cx.f.entry ∧ cx.g.ownAux = cx.f.ownAux ∧
      cert.ins.getD cx.f.entry [] = [] ∧
      checkBlocks cx cert (List.range cx.f.blockTab.size) = .ok () := by
  sorry

/-! ## The target's frame -/

theorem stepLoc_fr {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}
    (h : stepLoc env lc s v = .ok s') : s'.fr = s.fr := by
  sorry

theorem enterListLoc_fr {env : Env} {lc : LocCtx} :
    ∀ {s s' : LocState} {l : List ID}, enterListLoc env lc s l = .ok s' → s'.fr = s.fr
  | s, s', [], h => by cases h; rfl
  | s, s', id :: ids, h => by
    simp only [enterListLoc] at h
    split at h
    · cases h
    · split at h
      · rename_i s1 hs1
        rw [enterListLoc_fr h, stepLoc_fr hs1]
      · cases h
      · cases h

/-! ## The loop -/

/-- At the entry of block `bid` along edge `i`: after the source's `Phi`s, the certificate's
facts hold. -/
def EntryInv (tabs : Tables) (f g : Func) (cert : Cert) (env : Env) (frA : Frame) (bid : ID)
    (i : Nat) (fr : Frame) (s : LocState) : Prop :=
  s.fr.regs.size = g.valueTab.size ∧
  ∀ b ps, f.block? bid = some b →
    b.values.toList.filterMapM (phiStepL (Cx.make tabs f g).md (Cx.make tabs f g).sc fr i) =
      .ok ps →
    Match (Cx.make tabs f g) env frA (cert.ins.getD bid []) { fr with regs := setPhis ps fr.regs } s

/-- **The loop**: from related block entries, the target's run is the source's when the source's
is defined. -/
theorem loop_sim {cert : Cert} (hc : checkWith (Cx.make tabs f g) cert = .ok ()) {env : Env}
    {frA : Frame} :
    ∀ (fuel : Nat) (fr : Frame) (s : LocState) (bid : ID) (i : Nat),
      EntryInv tabs f g cert env frA bid i fr s →
      (runLoopL (Cx.make tabs f g).md env (Cx.make tabs f g).sc fuel fr bid i).Defined →
      runLoopLoc env (Cx.make tabs f g).lc fuel s bid =
        runLoopL (Cx.make tabs f g).md env (Cx.make tabs f g).sc fuel fr bid i
  | 0, _, _, _, _, _, _ => rfl
  | fuel + 1, fr, s, bid, i, ⟨hsz, hinv⟩, hd => by
    obtain ⟨hlow, -, hown, -, hcb⟩ := checkWith_spec hc
    have hlow' : f.lowered = g.lowered := hlow
    have hown' : f.ownAux = g.ownAux := hown.symm
    rw [runLoopL_succ] at hd ⊢
    rw [runLoopLoc_succ]
    rw [sc_f] at hd ⊢
    cases hb : f.block? bid with
    | none => rw [hb] at hd; exact hd.elim
    | some b =>
      rw [hb] at hd ⊢
      dsimp only at hd ⊢
      obtain ⟨hbid, b', hb', hrest⟩ :=
        checkBlock_spec (checkBlocks_spec hcb bid (List.mem_range.2 (block?_lt hb))) hb
      have hb'' : g.block? bid = some b' := hb'
      rw [lc_f, hb'']
      dsimp only
      rw [enterBlockLoc_eq]
      cases hps : b.values.toList.filterMapM
          (phiStepL (Cx.make tabs f g).md (Cx.make tabs f g).sc fr i) with
      | panic e m => exact absurd hps filterMapM_phiL_not_panic
      | stuck msg =>
        rw [enterBlockL_eq, hps] at hd
        exact hd.elim
      | ok ps =>
        have hM := hinv b ps hb hps
        cases ho : ((Cx.make tabs f g).sc.sched[b.id]?).join with
        | none =>
          rw [enterBlockL_eq, hps] at hd
          change match Res.bind (Res.ofOption _ ((Cx.make tabs f g).sc.sched[b.id]?).join) _ with
            | _ => _ at hd
          rw [ho] at hd
          exact hd.elim
        | some order =>
          have hord : ((Cx.make tabs f g).sc.sched[bid]?).join = some order := by
            rw [← hbid]; exact ho
          obtain ⟨S, rest, hw, hK, ht, hed⟩ := hrest order hord
          have hsim := walk_sim (env := env) (frA := frA) hlow' hown' b'.values.toList _ _ S rest
            { fr with regs := setPhis ps fr.regs } s hw hK hM
          have henter : enterBlockL (Cx.make tabs f g).md env (Cx.make tabs f g).sc fr b i =
              evalAllL (Cx.make tabs f g).md env (Cx.make tabs f g).sc
                { fr with regs := setPhis ps fr.regs } order.toList := by
            rw [enterBlockL_eq, hps]
            show Res.bind (Res.ofOption _ ((Cx.make tabs f g).sc.sched[b.id]?).join) _ = _
            rw [ho]
            rfl
          rw [henter] at hd ⊢
          revert hsim hd
          cases evalAllL (Cx.make tabs f g).md env (Cx.make tabs f g).sc
              { fr with regs := setPhis ps fr.regs } order.toList with
          | stuck msg => intro _ hd; exact hd.elim
          | panic e m => intro hsim _; simp only [SimRes] at hsim; rw [hsim]
          | ok fr2 =>
            intro ⟨s2, hs2, hM2⟩ hd
            rw [hs2]
            dsimp only at hd ⊢
            have hsz2 : s2.fr.regs.size = g.valueTab.size := by rw [enterListLoc_fr hs2]; exact hsz
            cases hn : stepTermL fr2 b with
            | panic e m => exact absurd hn Dead.stepTermL_not_panic
            | stuck msg => rw [hn] at hd; exact hd.elim
            | ok n =>
              obtain ⟨s3, hs3, hM3, hsz3⟩ := term_sim hM2 hlow' hsz2 ht hn
              rw [hs3]
              rw [hn] at hd
              cases n with
              | ret rs m => rfl
              | goto e =>
                dsimp only at hd ⊢
                refine loop_sim hc fuel fr2 s3 e.b e.i ⟨hsz3, ?_⟩ hd
                intro b2 ps2 hb2 hps2
                have he : e ∈ b.succs := Dead.stepTermL_goto_mem hn
                obtain ⟨E, hE, hsubE⟩ := edgesOK_spec hed e (Array.mem_toList_iff.2 he)
                exact sub_sound (phiEdge_sim hM3 hE hb2 hps2) hsubE

/-! ## The theorem -/

theorem checkWith_sound {cert : Cert} (h : checkWith (Cx.make tabs f g) cert = .ok ()) :
    RefinesLS tabs g tabs f := by
  obtain ⟨hlow, hent, hown, hins, -⟩ := checkWith_spec h
  have hown' : f.ownAux = g.ownAux := hown.symm
  have hctx := ctxL_eq (tabs := tabs) hown'
  intro env args mem fuel hd
  refine ⟨fuel, ?_⟩
  suffices hq : runLoc env tabs g args mem fuel = runSched env tabs f args mem fuel by
    rw [hq]; exact OutcomeRefines.refl hd
  unfold runLoc runSched at *
  rw [runCtxLoc_eq]
  unfold runCtxL at hd ⊢
  have hp : (LocCtx.make tabs g).ctx.params = (Ctx.makeSched tabs f).params := params_eq hown'
  by_cases hl : (args.length != (Ctx.makeSched tabs f).params.size) = true
  · simp only [hl, ite_true] at hd; exact hd.elim
  · rw [if_neg (by rw [hp]; exact hl), if_neg hl]
    rw [if_neg hl] at hd
    have hdl := finish_defined hd
    have houts : (LocCtx.make tabs g).ctx.outs = (Ctx.makeSched tabs f).outs := by
      show (Ctx.makeL tabs g).outs = (Ctx.makeL tabs f).outs; rw [hctx]
    have hdef : (LocCtx.make tabs g).ctx.defers = (Ctx.makeSched tabs f).defers := by
      show (Ctx.makeL tabs g).defers = (Ctx.makeL tabs f).defers; rw [hctx]
    have hact : (LocCtx.make tabs g).ctx.act = (Ctx.makeSched tabs f).act := by
      show (Ctx.makeL tabs g).act = (Ctx.makeL tabs f).act; rw [hctx]
    have hentry : (LocCtx.make tabs g).ctx.f.entry = (Ctx.makeSched tabs f).f.entry := by
      rw [show (LocCtx.make tabs g).ctx.f = g from lc_f (f := f), sc_f (g := g)]; exact hent
    rw [houts, hdef, hact, hentry]
    congr 1
    let frA := entryFrame env (Ctx.makeSched tabs f) args mem
    have hs0 : (initLoc env (LocCtx.make tabs g) args mem).fr =
        { frA with regs := (initLoc env (LocCtx.make tabs g) args mem).fr.regs } := by
      show entryFrame env (Ctx.makeL tabs g) args mem = _
      rw [entryFrameL_eq hown']
      rfl
    have hfr0 : frA.regs = Array.replicate f.valueTab.size none := by
      show Array.replicate (Ctx.makeSched tabs f).f.valueTab.size none = _
      rw [sc_f (g := g)]
    have hM0 : Match (Cx.make tabs f g) env frA [] frA (initLoc env (LocCtx.make tabs g) args mem) :=
      { facts := fun F hF => absurd hF List.not_mem_nil
        fr_eq := rfl
        s_fr := hs0
        shaped := fun id x hx => by rw [hfr0] at hx; simp [Array.getElem?_replicate] at hx
        kinv := fun id x _ hx => by rw [hfr0] at hx; simp [Array.getElem?_replicate] at hx
        regs := by simp [RegsOK, initLoc]
        fsize := by rw [hfr0]; simp }
    refine loop_sim h fuel frA _ _ 0 ⟨?_, ?_⟩ hdl
    · show (entryFrame env (Ctx.makeL tabs g) args mem).regs.size = _
      rw [entryFrameL_eq hown']
      simp
    · intro b ps hb hps
      rw [show (Ctx.makeSched tabs f).f.entry = f.entry from by rw [sc_f (g := g)]] at hb
      rw [show cert.ins.getD (Ctx.makeSched tabs f).f.entry [] = [] from by
        rw [show (Ctx.makeSched tabs f).f.entry = f.entry from by rw [sc_f (g := g)]]; exact hins]
      exact phis_match hM0 hps fun F hF => absurd hF List.not_mem_nil

/-- **The regalloc checker is sound**: when `checkRA tabs f g` accepts the allocated `g` of the
scheduled `f`, `g` refines `f`. -/
theorem checkRA_sound (h : checkRA tabs f g = .ok ()) : RefinesLS tabs g tabs f :=
  checkWith_sound h

end GoFV.Proof.RA

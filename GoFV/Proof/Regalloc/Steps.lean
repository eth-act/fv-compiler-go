import GoFV.Proof.Regalloc.Value

variable [GoFV.SSA.Sem.Addrs]

/-!
# Regalloc checker soundness, stage 3: `KeepAlive`, moves, rematerialisations

* `keepAlive_sim`: a kept `KeepAlive x m` that became `Copy m`/`VarLive m` is its memory;
* `move_sim`: a move (`Copy`, `LoadReg`, `StoreReg`) copies the facts of its argument's location
  at its shape (`moveSrc`), or the zero constant out of `ZERO`;
* `remat_sim`: a rematerialised frame constant holds its source constant.

The source does not run moves and rematerialisations: its frame is unchanged.
-/

namespace GoFV.Proof.RA

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RegallocCheck

variable {tabs : Tables} {f g : Func}

/-! ## Zero constants -/

theorem zero_kval {env : Env} {frA : Frame} {a : ID}
    (hz : (Cx.make tabs f g).isZeroConst a = true) :
    (Cx.make tabs f g).md.low = true ∧ (Cx.make tabs f g).isK a = true ∧
      kval (Cx.make tabs f g) env frA a =
        (Arm64.res ((Cx.make tabs f g).fty a) 0).retypeL ((Cx.make tabs f g).fty a) := by
  unfold Cx.isZeroConst at hz
  split at hz
  · rename_i v hv
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Array.isEmpty_iff] at hz
    obtain ⟨⟨hk, hop⟩, hargs⟩ := hz
    have hgen : v.op.generic = false := by
      rcases hop with hop | ⟨hop, -⟩ <;> rw [hop] <;> decide
    have hlowf : f.lowered = true := by
      cases hl : f.lowered with
      | true => rfl
      | false => rw [Func.generic_of_lowered hl hv] at hgen; cases hgen
    have hmdl : (Cx.make tabs f g).md.low = true := hlowf
    obtain ⟨v', hv', -, hkv⟩ := isK_spec hk
    rw [hv] at hv'
    cases hv'
    refine ⟨hmdl, hk, ?_⟩
    rw [kval_eq _ env frA hv hkv, hargs]
    have hkr : ∀ ty, kRes (Cx.make tabs f g).sc v [] ty = Arm64.res ty 0 := by
      intro ty
      rcases hop with hop | ⟨hop, hai⟩
      · simp only [kRes, hop]; rfl
      · simp only [kRes, hop]
        show Arm64.res ty (Arm64.imm v.auxInt) = _
        rw [hai]; rfl
    simp only [Array.toList_empty, List.map_nil, hkr]
    unfold LMode.retype
    simp only [hmdl, ite_true]
  · cases hz

theorem zero_retypeL {t t' : Ty} (h : shapeEq t t' = true) :
    (Arm64.res t 0).retypeL t = (Arm64.res t' 0).retypeL t' := by
  have := retype_shapeEq ⟨true, true⟩ h (Arm64.res t 0)
  unfold LMode.retype at this
  simp only [ite_true] at this
  rw [this, res_zero_shapeEq h]

/-! ## Helpers -/

theorem factOK_at {cx : Cx} {env : Env} {frA fr : Frame} {s s' : LocState} {F : Fact}
    (h : FactOK cx env frA fr s F) (hat : F.1 ≠ .avail → s'.at F.1 = s.at F.1) :
    FactOK cx env frA fr s' F := by
  obtain ⟨l, o⟩ := F
  by_cases hl : l = .avail
  · subst hl; exact h
  · rw [factOK_loc hl] at h ⊢
    rw [hat hl]; exact h

theorem evalValueL_shaped {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {y : Val}
    (h : evalValueL md env ctx fr v = .ok y) :
    md.retype (ctx.tys[v.id]?.getD .other) y = y := by
  obtain ⟨argv, hargv⟩ := evalValueL_regsAre (fun msg h' => by rw [h] at h'; cases h')
  rw [evalValueL_eq hargv] at h
  cases hr : evalOpL md.faulting env ctx fr v argv (ctx.tys[v.id]?.getD .other) with
  | ok r => rw [hr] at h; cases h; exact LMode.retype_idem _ _ _
  | panic e m => rw [hr] at h; cases h
  | stuck msg => rw [hr] at h; cases h

/-- The source value of `d` after it took `y`. -/
theorem srcVal_upd_self {env : Env} {frA : Frame} {S : Facts} {fr : Frame} {s : LocState}
    (h : Match (Cx.make tabs f g) env frA S fr s) {d : ID} {u : Value} {y : Val}
    (hu : f.value? d = some u)
    (hy : evalValueL (Cx.make tabs f g).md env (Cx.make tabs f g).sc fr u = .ok y) :
    srcVal (Cx.make tabs f g) env frA (upd fr d y) d = some y := by
  have hlt : d < fr.regs.size := by rw [h.fsize]; exact value?_lt hu
  unfold srcVal
  split
  · rename_i hk; rw [eval_kval h hk hu hy]
  · rw [upd_self' hlt]; rfl

/-- The target state after `w` wrote `y` (origin `o`) and the source value `d` took `y`. -/
theorem write_match {env : Env} {frA : Frame} {S : Facts} {fr : Frame} {s : LocState}
    (h : Match (Cx.make tabs f g) env frA S fr s) {d : ID} {u w : Value}
    (hu : f.value? d = some u) (hud : u.id = d) (hwd : w.id = d)
    (hnd : writesNodup ((Cx.make tabs f g).lc.home d) ((Cx.make tabs f g).gty d) = true)
    {y r : Val} (hev : evalValueL (Cx.make tabs f g).md env (Cx.make tabs f g).sc fr u = .ok y)
    (hval : (LMode.loc (Cx.make tabs f g).lc.ctx.f).retype ((Cx.make tabs f g).lc.ty w.id) r = y)
    {o : ID} (ho : srcVal (Cx.make tabs f g) env frA (upd fr d y) o = some y) :
    Match (Cx.make tabs f g) env frA
      (writeFacts (Cx.make tabs f g) ((Cx.make tabs f g).redefine (clobberFacts (Cx.make tabs f g) S w) d) w o)
      (upd fr d y) (putRes (Cx.make tabs f g).lc s w r) := by
  have hlt : d < fr.regs.size := by rw [h.fsize]; exact value?_lt hu
  have hnd' : writesNodup ((Cx.make tabs f g).lc.home w.id) ((Cx.make tabs f g).lc.ty w.id) = true := by
    rw [hwd]; exact hnd
  have hys : (Cx.make tabs f g).md.retype ((Cx.make tabs f g).fty d) y = y := by
    have := evalValueL_shaped hev
    rw [hud] at this; exact this
  refine { facts := ?_, fr_eq := upd_fr_eq h.fr_eq d y,
           s_fr := by rw [putRes_fr]; exact h.s_fr, shaped := ?_, kinv := ?_,
           regs := putRes_regs h.regs w r, fsize := by rw [upd_size]; exact h.fsize }
  · intro F hF
    unfold writeFacts at hF
    rcases List.mem_append.1 hF with hF | hF
    · rw [List.mem_map] at hF
      obtain ⟨⟨l, j⟩, hl, rfl⟩ := hF
      refine (factOK_loc (writeLocs_ne hl)).2 fun x hx => ?_
      simp only [exactF] at hx
      rw [ho] at hx; cases hx
      simp only [exactF, Bool.false_eq_true, ite_false]
      rw [putRes_at_write h.regs hnd' hl, hval]
    · obtain ⟨hF1, hcl⟩ := mem_killAll hF
      have hF2 := (mem_redefine hF1).1
      refine factOK_keep h hu hud hev (redefine_mono (fun F hF => (at_clobber hF s).1) hF1) ?_
      intro _
      unfold putRes
      rw [at_write_other (regsOK_clobber h.regs w) (fun l hl => by rw [lc_tabs]; exact hcl l hl)]
      exact (at_clobber hF2 s).2
  · intro id x hx
    by_cases hid : id = d
    · subst hid
      rw [upd_self' hlt] at hx
      cases hx
      exact hys
    · rw [upd_ne hid] at hx; exact h.shaped id x hx
  · intro id x hk hx
    by_cases hid : id = d
    · subst hid
      rw [upd_self' hlt] at hx
      cases hx
      exact eval_kval h hk hu hev
    · rw [upd_ne hid] at hx; exact h.kinv id x hk hx

/-! ## `KeepAlive` -/

theorem keepAliveChecks_spec {cx : Cx} {S : Facts} {w u : Value}
    (h : keepAliveChecks cx S w u = .ok ()) :
    ∃ a' a, w.args[0]? = some a' ∧ u.args[1]? = some a ∧ argOK cx S a' a none = .ok () ∧
      shapeEq (cx.gty w.id) (cx.fty u.id) = true := by
  unfold keepAliveChecks at h
  split at h
  · rename_i a' a ha' ha
    split at h
    · cases h
    · rename_i hok
      split at h
      · cases h
      · rename_i hsh
        exact ⟨a', a, ha', ha, hok, by simpa using hsh⟩
  · cases h

theorem keepAlive_sim {env : Env} {frA : Frame} {S : Facts} {fr : Frame} {s : LocState}
    (h : Match (Cx.make tabs f g) env frA S fr s) (hlow : f.lowered = g.lowered)
    {d : ID} {u w : Value} (hu : f.value? d = some u) (hw : g.value? d = some w)
    (hud : u.id = d) (hwd : w.id = d) (hka : isKeepAliveCopy u w = true)
    (hnd : writesNodup ((Cx.make tabs f g).lc.home d) ((Cx.make tabs f g).gty d) = true)
    (hchk : keepAliveChecks (Cx.make tabs f g) S w u = .ok ()) :
    match evalValueL (Cx.make tabs f g).md env (Cx.make tabs f g).sc fr u with
    | .ok y => ∃ s', stepLoc env (Cx.make tabs f g).lc s w = .ok s' ∧
        Match (Cx.make tabs f g) env frA
          (writeFacts (Cx.make tabs f g)
            ((Cx.make tabs f g).redefine (clobberFacts (Cx.make tabs f g) S w) u.id) w u.id)
          (upd fr d y) s'
    | .panic e m => stepLoc env (Cx.make tabs f g).lc s w = .panic e m
    | .stuck _ => True := by
  unfold isKeepAliveCopy at hka
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hka
  obtain ⟨⟨⟨⟨hku, hwop⟩, hty⟩, hus⟩, hws⟩ := hka
  obtain ⟨a', a, ha', ha, hok, -⟩ := keepAliveChecks_spec hchk
  split
  · rename_i y hev
    obtain ⟨argv, hargv⟩ := evalValueL_regsAre (fun msg h' => by rw [hev] at h'; cases h')
    have hev' := hev
    rw [evalValueL_eq hargv] at hev'
    cases hr : evalOpL (Cx.make tabs f g).md.faulting env (Cx.make tabs f g).sc fr u argv
        ((Cx.make tabs f g).sc.tys[u.id]?.getD .other) with
    | panic e m => rw [hr] at hev'; cases hev'
    | stuck msg => rw [hr] at hev'; cases hev'
    | ok r0 =>
      rw [hr] at hev'
      cases hev'
      obtain ⟨x, m, rfl, rfl⟩ := evalOpL_keepAlive hku hr
      -- the memory argument
      have hua : u.args.toList[1]? = some a := by simpa using ha
      obtain ⟨M, hM, hMr⟩ := regsAre_get hargv hua
      cases hM
      obtain ⟨M', hM', hrel⟩ := argOK_read h hlow hok (srcVal_of_reg h hMr)
      simp only [ArgRel] at hrel
      subst hrel
      have hwa : w.args.toList = [a'] := by
        match hl : w.args.toList, hws with
        | [b], _ =>
          have : w.args[0]? = some b := by
            rw [← Array.getElem?_toList, hl]; rfl
          rw [ha'] at this; cases this; rfl
        | [], h0 => simp [← Array.length_toList, hl] at h0
        | _ :: _ :: _, h0 => simp [← Array.length_toList, hl] at h0
      have hmap : w.args.toList.mapM (s.read (Cx.make tabs f g).lc) = .ok [.mem m] := by
        rw [hwa, List.mapM_cons, hM']; rfl
      have hstep : stepLoc env (Cx.make tabs f g).lc s w =
          .ok (putRes (Cx.make tabs f g).lc s w (.mem m)) := by
        rcases hwop with hc | hc
        · rw [stepLoc_op (by rw [hc]; decide) (by rw [hc]; decide) (by rw [hc]; decide)
            (by rw [hc]; decide) (by rw [hc]; decide) hmap, evalOpL_copy hc]
          rfl
        · rw [stepLoc_op (by rw [hc]; decide) (by rw [hc]; decide) (by rw [hc]; decide)
            (by rw [hc]; decide) (by rw [hc]; decide) hmap, evalOpL_varLive hc]
          rfl
      refine ⟨_, hstep, ?_⟩
      have hgf : (Cx.make tabs f g).gty d = (Cx.make tabs f g).fty d :=
        gty_eq_fty hlow hu hw hty
      subst hud
      refine write_match h hu rfl hwd hnd hev ?_ (srcVal_upd_self h hu hev)
      rw [loc_md hlow, hwd]
      exact congrArg (fun t => (Cx.make tabs f g).md.retype t (.mem m)) hgf
  · rename_i e m hev
    exfalso
    obtain ⟨argv, hargv⟩ := evalValueL_regsAre (fun msg h' => by rw [hev] at h'; cases h')
    rw [evalValueL_eq hargv] at hev
    cases hr : evalOpL (Cx.make tabs f g).md.faulting env (Cx.make tabs f g).sc fr u argv
        ((Cx.make tabs f g).sc.tys[u.id]?.getD .other) with
    | panic e' m' => exact evalOpL_keepAlive_panic hku hr
    | ok r0 => rw [hr] at hev; cases hev
    | stuck msg => rw [hr] at hev; cases hev
  · trivial

/-! ## Moves -/

theorem compOK_shaped {cx : Cx} {env : Env} {frA : Frame} {S : Facts} {fr : Frame}
    {s : LocState} (h : Match cx env frA S fr s) {o : Orig} (hc : cx.compOK o = true) {x : Val}
    (hx : srcVal cx env frA fr o.id = some x) :
    cx.md.retype (cx.origTy o) (comp o.comp x) = comp o.comp x := by
  have hsh := srcVal_shaped h hx
  unfold Cx.compOK at hc
  unfold Cx.origTy
  split at hc
  · rename_i hn; rw [hn]; exact hsh
  · rename_i j ts hj ht
    rw [hj]
    simp only [decide_eq_true_eq] at hc
    rw [ht] at hsh
    have := comp_shaped _ hsh hc
    simpa [List.getD_eq_getElem?_getD, hc] using this
  · cases hc

/-- A move's destination, written at the move's shape `t` from the argument's read `x0`, holds
every source value `moveSrc` gives it. -/
theorem moveSrc_ok {env : Env} {frA : Frame} {S : Facts} {fr : Frame} {s : LocState}
    (h : Match (Cx.make tabs f g) env frA S fr s) {a' : ID} {t : Ty} {zo : Option ID}
    {x0 : Val} (hraw : s.raw (Cx.make tabs f g).lc a' = .ok x0)
    {o' : Orig} (ho : o' ∈ moveSrc (Cx.make tabs f g) S a' t zo) {x : Val}
    (hx : srcVal (Cx.make tabs f g) env frA fr o'.id = some x) :
    o'.weak = false ∧ (Cx.make tabs f g).md.retype t
      ((Cx.make tabs f g).md.retype ((Cx.make tabs f g).gty a') x0) = comp o'.comp x := by
  unfold moveSrc at ho
  split at ho
  · rename_i l0 hr0
    rw [raw_loc hr0] at hraw
    cases hraw
    rw [List.mem_filterMap] at ho
    obtain ⟨⟨l', o⟩, hF, he⟩ := ho
    dsimp only at he
    cases hw : o.weak
    · simp only [hw, Bool.false_eq_true, ite_false, Option.ite_none_right_eq_some,
        Option.some.injEq] at he
      obtain ⟨hcond, rfl⟩ := he
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      obtain ⟨⟨⟨rfl, hco⟩, hsh⟩, hcmp⟩ := hcond
      refine ⟨rfl, ?_⟩
      have hfo := (factOK_loc (readLoc_loc_ne hr0)).1 (h.facts _ hF) x hx
      simp only [hw, Bool.false_eq_true, ite_false] at hfo
      rw [← retype_shapeEq _ hsh, hfo]
      exact retype_composesAt hcmp (compOK_shaped h hco hx)
    · simp only [hw, ite_true, Option.ite_none_right_eq_some, Option.some.injEq] at he
      obtain ⟨hcond, rfl⟩ := he
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      obtain ⟨⟨⟨rfl, hco⟩, hsh⟩, hcmp⟩ := hcond
      refine ⟨rfl, ?_⟩
      have hfo := (factOK_loc (readLoc_loc_ne hr0)).1 (h.facts _ hF) x hx
      simp only [hw, ite_true] at hfo
      rw [← retype_shapeEq _ hsh, retype_composes hcmp]
      exact hfo
  · rename_i hr0
    rw [raw_zero hr0] at hraw
    cases hraw
    split at ho
    · rename_i u0
      split at ho
      · rename_i hc
        simp only [List.mem_singleton] at ho
        subst ho
        simp only [Bool.and_eq_true] at hc
        obtain ⟨⟨hz, hsa⟩, hsu⟩ := hc
        obtain ⟨hlowt, hk, hkv⟩ := zero_kval (env := env) (frA := frA) hz
        have hsv : srcVal (Cx.make tabs f g) env frA fr u0 = some (kval (Cx.make tabs f g) env frA u0) := by
          unfold srcVal; rw [if_pos hk]
        rw [(srcVal_canon hsv).1] at hx
        cases hx
        refine ⟨rfl, ?_⟩
        simp only [comp]
        rw [hkv]
        unfold LMode.retype
        simp only [hlowt, ite_true]
        rw [show (Cx.make tabs f g).lc.ty a' = (Cx.make tabs f g).gty a' from rfl,
          Val.retypeL_idem, zero_retypeL hsa, Val.retypeL_idem, zero_retypeL hsu]
      · simp at ho
    · simp at ho
  · simp at ho

theorem move_sim {env : Env} {frA : Frame} {S S' : Facts} {fr : Frame} {s : LocState}
    (h : Match (Cx.make tabs f g) env frA S fr s) (hlow : f.lowered = g.lowered)
    {w : Value} {zo : Option ID}
    (hmv : w.op = .Copy ∨ w.op = .LoadReg ∨ w.op = .StoreReg)
    (hnd : writesNodup ((Cx.make tabs f g).lc.home w.id) ((Cx.make tabs f g).gty w.id) = true)
    (hok : moveStep (Cx.make tabs f g) S w zo = .ok S') :
    ∃ s', stepLoc env (Cx.make tabs f g).lc s w = .ok s' ∧ Match (Cx.make tabs f g) env frA S' fr s' := by
  unfold moveStep at hok
  split at hok
  · rename_i a' hargs
    split at hok
    · cases hok
    · rename_i hrd
      cases hok
      obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 (by simpa using hrd)
      obtain ⟨x0, hraw⟩ := raw_ok (s := s) hr
      have hrd' := read_eq hraw
      have hmap : w.args.toList.mapM (s.read (Cx.make tabs f g).lc) =
          .ok [(LMode.loc (Cx.make tabs f g).lc.ctx.f).retype ((Cx.make tabs f g).lc.ty a') x0] := by
        rw [hargs, List.mapM_cons, hrd']; rfl
      have hstep : stepLoc env (Cx.make tabs f g).lc s w = .ok (putRes (Cx.make tabs f g).lc s w
          ((LMode.loc (Cx.make tabs f g).lc.ctx.f).retype ((Cx.make tabs f g).lc.ty a') x0)) := by
        rcases hmv with hc | hc | hc
        · rw [stepLoc_op (by rw [hc]; decide) (by rw [hc]; decide) (by rw [hc]; decide)
            (by rw [hc]; decide) (by rw [hc]; decide) hmap, evalOpL_copy hc]
          rfl
        · exact stepLoc_move (.inl hc) hmap
        · exact stepLoc_move (.inr hc) hmap
      refine ⟨_, hstep, ?_⟩
      refine { facts := ?_, fr_eq := h.fr_eq, s_fr := by rw [putRes_fr]; exact h.s_fr,
               shaped := h.shaped, kinv := h.kinv, regs := putRes_regs h.regs w _,
               fsize := h.fsize }
      intro F hF
      unfold moveFacts at hF
      rcases List.mem_append.1 hF with hF | hF
      · rw [List.mem_flatMap] at hF
        obtain ⟨⟨l, j⟩, hl, hF⟩ := hF
        cases j with
        | some _ => simp at hF
        | none =>
          rw [List.mem_map] at hF
          obtain ⟨o', ho', rfl⟩ := hF
          refine (factOK_loc (writeLocs_ne hl)).2 fun x hx => ?_
          obtain ⟨hw, hv⟩ := moveSrc_ok h hraw ho' hx
          simp only [hw, Bool.false_eq_true, ite_false]
          rw [putRes_at_write h.regs hnd hl, loc_md hlow]
          exact hv
      · obtain ⟨hFS, hat⟩ := putRes_at_kill h.regs hF
        exact factOK_at (h.facts F hFS) (fun _ => hat)
  · cases hok

/-! ## Rematerialisations -/

theorem regsAre_of_map {r : ID → Option Val} {F : ID → Val} :
    ∀ {l : List ID}, (∀ a ∈ l, r a = some (F a)) → RegsAre r l (l.map F)
  | [], _ => trivial
  | a :: l, h => ⟨h a (List.mem_cons_self ..), regsAre_of_map fun b hb => h b (List.mem_cons_of_mem _ hb)⟩

theorem remat_sim {env : Env} {frA : Frame} {S : Facts} {fr : Frame} {s : LocState}
    (h : Match (Cx.make tabs f g) env frA S fr s) (hlow : f.lowered = g.lowered)
    {w u : Value} (hw : g.value? w.id = some w) (hu : f.value? u.id = some u)
    (hnd : writesNodup ((Cx.make tabs f g).lc.home w.id) ((Cx.make tabs f g).gty w.id) = true)
    (hchk : rematChecks (Cx.make tabs f g) S w u = .ok ()) :
    ∃ s', stepLoc env (Cx.make tabs f g).lc s w = .ok s' ∧
      Match (Cx.make tabs f g) env frA
        (writeFacts (Cx.make tabs f g) (clobberFacts (Cx.make tabs f g) S w) w
          ((Cx.make tabs f g).canon u.id)) fr s' := by
  unfold rematChecks at hchk
  split at hchk
  · cases hchk
  · rename_i hk
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hk
    split at hchk
    · cases hchk
    · rename_i hso
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hso
      split at hchk
      · cases hchk
      · unfold argsOK at hchk
        split at hchk
        · cases hchk
        · rename_i hsz
          simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hsz
          obtain ⟨hop, haux, hai, hty, -⟩ := sameOp_spec hso
          obtain ⟨v, hv, -, hkv⟩ := isK_spec hk
          rw [show (Cx.make tabs f g).f = f from rfl, hu] at hv
          cases hv
          have hko := (isKVal_spec hkv).1
          have hsel : selIndex u = none := by
            apply selIndex_none_of_op <;> intro he <;> rw [he] at hko <;> cases hko
          rw [hsel] at hchk
          have hregs : RegsAre (srcVal (Cx.make tabs f g) env frA fr) u.args.toList
              (u.args.toList.map (kval (Cx.make tabs f g) env frA)) :=
            regsAre_of_map fun a ha => by
              unfold srcVal
              rw [if_pos (isK_of_arg hkv (Array.mem_toList_iff.1 ha))]
          obtain ⟨argv', hargv', hrel⟩ := argsOKL_read h hlow hchk (by simpa using hsz) hregs
          have he := ArgsRel.eq_of_none hrel
          subst he
          have hkw : kOp w.op = true := hop ▸ hko
          have hne : ∀ o, kOp o = true → o ≠ .Phi ∧ o ≠ .LoadReg ∧ o ≠ .StoreReg ∧
              o ≠ .ARM64MOVDreg ∧ o ≠ .ARM64MOVDnop := by
            intro o ho
            rcases kOp_cases ho with h' | h' | h' | h' | h' | h' | h' | h' <;> subst h' <;> decide
          obtain ⟨n1, n2, n3, n4, n5⟩ := hne _ hkw
          rw [stepLoc_op n1 n2 n3 n4 n5 hargv', evalOpL_kop_eq hkw]
          refine ⟨_, rfl, ?_⟩
          have hgf : (Cx.make tabs f g).lc.ty w.id = (Cx.make tabs f g).fty u.id := by
            show (Cx.make tabs f g).gty w.id = _
            rw [gty_of_value hw, fty_of_value hu, hlow, hty]
          have hY : (LMode.loc (Cx.make tabs f g).lc.ctx.f).retype ((Cx.make tabs f g).lc.ty w.id)
              (kRes (Cx.make tabs f g).lc.ctx w (u.args.toList.map (kval (Cx.make tabs f g) env frA))
                ((Cx.make tabs f g).lc.ty w.id)) = kval (Cx.make tabs f g) env frA u.id := by
            rw [kval_eq _ env frA hu hkv, loc_md hlow, hgf,
              kRes_congr (hop.symm) haux.symm hai.symm (lc_tabs.trans sc_tabs.symm) act_eq]
          have hsv : srcVal (Cx.make tabs f g) env frA fr ((Cx.make tabs f g).canon u.id) =
              some (kval (Cx.make tabs f g) env frA u.id) :=
            (srcVal_canon (by unfold srcVal; rw [if_pos hk])).1
          refine { facts := ?_, fr_eq := h.fr_eq, s_fr := by rw [putRes_fr]; exact h.s_fr,
                   shaped := h.shaped, kinv := h.kinv, regs := putRes_regs h.regs w _,
                   fsize := h.fsize }
          intro F hF
          unfold writeFacts at hF
          rcases List.mem_append.1 hF with hF | hF
          · rw [List.mem_map] at hF
            obtain ⟨⟨l, j⟩, hl, rfl⟩ := hF
            refine (factOK_loc (writeLocs_ne hl)).2 fun x hx => ?_
            simp only [exactF] at hx
            rw [hsv] at hx; cases hx
            simp only [exactF, Bool.false_eq_true, ite_false]
            rw [putRes_at_write h.regs hnd hl, hY]
          · obtain ⟨hFS, hat⟩ := putRes_at_kill h.regs hF
            exact factOK_at (h.facts F hFS) (fun _ => hat)

end GoFV.Proof.RA

import GoFV.Proof.Pass.SchedLBlock

variable [GoFV.SSA.Sem.Addrs]

/-!
# `schedule` on `runSched`: one block's values, end to end

`walk_ok`: if the source (`runL`'s order `oS`, faulting) evaluates the block's non-`Phi`s, the
target (`runSched`'s order `oT`) evaluates its own, agreeing with the source on every value it
ran that is no nil check (`Inv`). `walk_panic`: if the source panics, the target panics alike.
Before the source's panicking value `r` the target runs values the source ran before `r`
(alike, `stepT`), values that never fail (`Cls.safe`), parameters' register pieces (`argOK`:
they evaluate), and values `swapOK` lets it run first (the source's `r` cannot be a load or nil
check whose pointer is a nil check's result, `SP`, `GetG` or the closure pointer, `nnBase`: that
pointer has no nil base) (a load on `r`'s memory, which may also be the memory of the `LDAR*`
whose `Select1` `r`'s is, `ldReach_src`, or a nil check on it of `r`'s pointer word or of a
pointer-shaped parameter piece the source ran before `r`, which reads nil or a pointer that is
not wild, `ArgPtrsAt`), which evaluate or panic with `nilDeref` of that memory, as `r` does; at
`r` the target panics as the source.
-/

namespace GoFV.Proof.SchedL

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.ScheduleCheck GoFV.Proof

variable {tabs : Tables} {f g : Func} {md : LMode} {env : Env}

/-! ## Lists -/

/-- A prefix of a dependency order holds the listed arguments of its values. -/
theorem topo_closed {D : ID → List ID} {s : List ID} :
    ∀ {pre : List ID}, TopoRem D (pre ++ s) → ∀ y ∈ pre, ∀ a ∈ D y, a ∈ pre ++ s → a ∈ pre
  | [], _, _, hy, _, _, _ => absurd hy List.not_mem_nil
  | x :: pre, ⟨h1, h2⟩, y, hy, a, ha, hm => by
    rcases List.mem_cons.1 hy with rfl | hy
    · exact absurd hm (h1 a ha)
    · rcases List.mem_cons.1 hm with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (topo_closed h2 y hy a ha hm)

theorem nodup_idx {o : List ID} (h : o.Nodup) {i j : Nat} {x : ID} (hi : o[i]? = some x)
    (hj : o[j]? = some x) : i = j := by
  obtain ⟨hi1, -⟩ := List.getElem?_eq_some_iff.1 hi
  exact (List.Nodup.getElem?_inj hi1 h).1 (hi.trans hj.symm)

theorem back_get {a : Array ID} {x : ID} (h : a.back? = some x) : a[a.size - 1]? = some x := by
  simpa [Array.back?] using h

theorem arr_two {a : Array ID} {x y : ID} (hs : a.size = 2) (h0 : a[0]? = some x)
    (h1 : a[1]? = some y) : a = #[x, y] := by
  rcases a with ⟨l⟩
  rcases l with _ | ⟨a0, _ | ⟨a1, _ | ⟨_, _⟩⟩⟩ <;> simp_all

/-! ## Classes -/

theorem mayFail_of {x : ID} {v : Value} (hv : f.value? x = some v) :
    mayFail tabs f x = (cls tabs v != .safe) := by
  unfold mayFail; rw [hv]; rfl

theorem cls_ne_safe_of_mayPanic {v : Value} (h : mayPanic tabs v = true) : cls tabs v ≠ .safe := by
  unfold mayPanic at h
  split at h
  · rename_i hg
    have hr : Sem.isRoot v.op = true := by simp only [Sem.isRoot, h, Bool.true_or]
    simp [cls, hg, specSafeOp, hr]
  · simpa using h

theorem spa_not_mayPanic {v : Value} (h : v.op = .SPanchored) : mayPanic tabs v = false := by
  have h1 : Op.SPanchored.generic = true := by decide
  have h2 : Op.SPanchored.call = false := by decide
  have h3 : Op.SPanchored.nilCheck = false := by decide
  unfold mayPanic; rw [h]; simp [h1, h2, h3]

/-! ## Memories through acquiring loads -/

theorem srcPos_pos {n : Nat} {l : List ID} {x : ID} (h : 0 < (srcPos n l)[x]!) : x ∈ l := by
  by_cases hx : x ∈ l
  · exact hx
  · rw [srcPos_out hx] at h; exact absurd h (Nat.lt_irrefl 0)

theorem ldMem1_spec {pS : Array Nat} {ℓ ℓ' : ID} (h : ldMem1 f pS ℓ = some ℓ') :
    ∃ vz l vl, f.value? ℓ = some vz ∧ vz.op = .Select1 ∧ 0 < pS[ℓ]! ∧ vz.args.toList = [l] ∧
      f.value? l = some vl ∧ ldarOp vl.op = true ∧ 0 < pS[l]! ∧ vl.args.back? = some ℓ' := by
  unfold ldMem1 at h
  split at h
  · rename_i vz hvz
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      split at h
      · rename_i l hl
        split at h
        · rename_i vl hvl
          split at h
          · rename_i hc2
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc2
            exact ⟨vz, l, vl, hvz, hc.1, hc.2, hl, hvl, hc2.1.1, hc2.2, h⟩
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- **`ldReach` along the source**: the memory the source's frame `H` holds at `ℓ` (when `ℓ` is in
the block, the source ran it) it holds at every `ℓ'` that `ldReach` reaches from `ℓ`, which is
`ℓ` or the memory argument of an `LDAR*` the source ran. -/
theorem ldReach_src {oS : List ID} {frPS H : Frame} {P : List ID}
    (Sr : Src tabs f md env frPS H P) (hPc : ∀ x ∈ P, ∀ a ∈ argsF f x, a ∈ oS → a ∈ P)
    {m : Mem} :
    ∀ (k : Nat) (ℓ ℓ' : ID), ldReach f (srcPos f.valueTab.size oS) k ℓ ℓ' = true →
      (ℓ ∈ oS → ℓ ∈ P) → H.regs[ℓ]? = some (some (.mem m)) →
      H.regs[ℓ']? = some (some (.mem m)) ∧
        (ℓ' = ℓ ∨ ∃ l ∈ P, ∃ vl, f.value? l = some vl ∧ vl.args.back? = some ℓ')
  | 0, ℓ, ℓ', hr, _, h => by
    simp only [ldReach, beq_iff_eq] at hr; subst hr; exact ⟨h, .inl rfl⟩
  | k + 1, ℓ, ℓ', hr, hℓP, h => by
    unfold ldReach at hr
    by_cases he : ℓ = ℓ'
    · subst he; exact ⟨h, .inl rfl⟩
    have he' : (ℓ == ℓ') = false := by simpa using he
    rw [he', Bool.false_or] at hr
    cases h1 : ldMem1 f (srcPos f.valueTab.size oS) ℓ with
    | none => rw [h1] at hr; cases hr
    | some ℓ'' =>
      rw [h1] at hr
      obtain ⟨vz, l, vl, hvz, hz, hpz, hza, hvl, hl, hpl, hb⟩ := ldMem1_spec h1
      have hℓS := hℓP (srcPos_pos hpz)
      have hla : l ∈ argsF f ℓ := by rw [argsF_of hvz, hza]; exact List.mem_singleton_self l
      have hlP : l ∈ P := hPc ℓ hℓS l hla (srcPos_pos hpl)
      obtain ⟨vz', y, hvz', hy, hevz⟩ := Sr.eval ℓ hℓS
      rw [hvz] at hvz'; cases hvz'
      rw [h] at hy; cases hy
      obtain ⟨vl', yl, hvl', hyl, hevl⟩ := Sr.eval l hlP
      rw [hvl] at hvl'; cases hvl'
      obtain ⟨ℓ3, hb', hH'⟩ := evalValueL_select1_ldar hz hza hl hyl hevl hevz
      rw [hb] at hb'; cases hb'
      have hℓ''a : ℓ'' ∈ argsF f l := by
        rw [argsF_of hvl]; exact Array.mem_toList_iff.2 (Array.mem_of_getElem? (back_get hb))
      obtain ⟨hH, hc⟩ := ldReach_src Sr hPc k ℓ'' ℓ' hr (hPc l hlP ℓ'' hℓ''a) hH'
      refine ⟨hH, .inr ?_⟩
      rcases hc with hc | hc
      · subst hc; exact ⟨l, hlP, vl, hvl, hb⟩
      · exact hc

/-! ## The walk -/

/-- **The target evaluates the block where the source does**, agreeing on every value that is
no nil check. -/
theorem walk_ok (S : SchedRel tabs f g) (hf : md.faulting = true) {oS oT : List ID}
    {frPS frPT H : Frame} (B : BStep tabs f g md oS oT frPS frPT)
    (Sr : Src tabs f md env frPS H oS) :
    ∀ n, n ≤ oT.length → ∃ T, evalAllL md env (Ctx.makeSched tabs g) frPT (oT.take n) = .ok T ∧
      Inv f frPT H T oS (oT.take n)
  | 0, _ => ⟨frPT, by simp; rfl, ⟨by rfl, rfl, fun _ _ => rfl, fun _ h => by simp at h,
      fun _ h => by simp at h⟩⟩
  | n + 1, hn => by
    obtain ⟨y, hy⟩ : ∃ y, oT[n]? = some y := ⟨oT[n], List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨T, hT, I⟩ := walk_ok S hf B Sr n (by omega)
    obtain ⟨fv, gv, hfv, hgv, hr⟩ := tval S B (List.mem_of_getElem? hy)
    have hyS : y ∈ oS := ((B.tMem y).1 (List.mem_of_getElem? hy)).1
    obtain ⟨v, z, hv, hz, hev⟩ := Sr.eval y hyS
    rw [hfv] at hv; cases hv
    obtain ⟨z', hz', hzz⟩ := (stepT S hf B Sr (fun _ h => h) (fun _ _ _ _ h => h) I hy
      (fun _ _ h => h) hfv hgv hr).1 z hev
    have hlt : y < T.regs.size := by rw [I.size, B.size, B.sizeS]; exact lt_of_value? hfv
    refine ⟨T.set y z', ?_, inv_step B.tNodup I hy hlt fun _ hn => by rw [hz, hzz hn]⟩
    rw [take_succ_of hy, evalAllL_append, hT]
    dsimp only
    rw [evalAllL_cons, stepVL_of (by rw [makeSched_f]; exact hgv), hz']
    all_goals rfl

/-- **The target panics where the source does, alike.** -/
theorem walk_panic (S : SchedRel tabs f g) (hf : md.faulting = true) {oS oT : List ID}
    {frPS frPT : Frame} (B : BStep tabs f g md oS oT frPS frPT)
    (hAP : ArgPtrsAt md env tabs f frPS)
    (hNR : ∀ k H, evalAllL md env (Ctx.makeL tabs f) frPS (oS.take k) = .ok H → NilRegsOK tabs f H)
    {e : Panic} {m : Mem}
    (hev : evalAllL md env (Ctx.makeL tabs f) frPS oS = .panic e m) :
    evalAllL md env (Ctx.makeSched tabs g) frPT oT = .panic e m := by
  obtain ⟨pre, r, post, H, hsplit, hpre, hr⟩ := evalAllL_panic_split hev
  subst hsplit
  have hcF : (Ctx.makeL tabs f).f = f := makeL_f tabs f
  have hnd := B.sNodup
  have hto := B.sTopo
  have hndp : pre.Nodup := (List.nodup_append.1 hnd).1
  have htp : TopoRem (argsF f) pre := topo_prefix hto
  obtain ⟨e1, e2, e3, e4⟩ := evalAllL_spec (ctx := Ctx.makeL tabs f) hndp (by rw [hcF]; exact htp)
    (by rw [hcF]; exact B.sizeS) hpre
  have hPS : ∀ x ∈ pre, x ∈ pre ++ r :: post := fun x hx => List.mem_append_left _ hx
  have hty := typedL_evalAll B.typed
    (fun x hx v hv => B.sOwn x (hPS x hx) v (by rw [hcF] at hv; exact hv)) e3 e4
  rw [hcF] at e4
  have Sr : Src tabs f md env frPS H pre := ⟨e1, e2, e3, e4, hty⟩
  have hPc : ∀ x ∈ pre, ∀ a ∈ argsF f x, a ∈ pre ++ r :: post → a ∈ pre :=
    fun x hx a ha hm => topo_closed hto x hx a ha hm
  -- the panicking value `r`
  have hrS : r ∈ pre ++ r :: post := by simp
  obtain ⟨vr, hvr⟩ := B.sVal r hrS
  rw [stepVL_of (by rw [hcF]; exact hvr)] at hr
  have hdoneR : ∀ a ∈ argsF f r, a ∈ pre ++ r :: post → a ∈ pre := fun a ha hm => by
    rcases List.mem_append.1 hm with h | h
    · exact h
    · exact absurd h (topo_mid hto a ha)
  obtain ⟨hmp, hld, hptr⟩ := evalValueL_panic_info hf hr
  rw [tabs_makeL] at hmp hld hptr
  -- `r` is no load or nil check whose base is a pointer outside the nil block (`nnBase`)
  have hrnb : nnBase tabs (Ctx.makeL tabs f).tys f vr = false := by
    cases hnb : nnBase tabs (Ctx.makeL tabs f).tys f vr
    · rfl
    · exfalso
      simp only [nnBase, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hnb
      obtain ⟨hk, hq⟩ := hnb
      obtain ⟨q, hq0, hqnn⟩ : ∃ q, vr.args[0]? = some q ∧
          isNN (Ctx.makeL tabs f).tys f q = true := by
        cases h0 : vr.args[0]? with
        | none => rw [h0] at hq; cases hq
        | some q => rw [h0] at hq; exact ⟨q, rfl, by simpa using hq⟩
      obtain ⟨p, a, hp, hHp, hnil⟩ := hptr (by
        rcases hk with h | h
        · exact .inl (mem_of_decide h)
        · exact .inr h)
      rw [hq0] at hp; cases hp
      have hqargs : q ∈ argsF f r := by
        rw [argsF_of hvr]; exact Array.mem_toList_iff.2 (Array.mem_of_getElem? hq0)
      have hnn : ¬ NilBase a := by
        by_cases hqS : q ∈ pre ++ r :: post
        · have hqP := hdoneR q hqargs hqS
          obtain ⟨vq, y, hvq, hy, hevq⟩ := Sr.eval q hqP
          obtain ⟨vq', hvq', hc⟩ := isNN_cases hqnn
          rw [hvq] at hvq'; cases hvq'
          rcases hc with hqnc | hop | ⟨hop, hw⟩
          · have hu := S.argUse hvr hq0
            obtain ⟨hne, hsh⟩ := nc_step1 hu hqnc
            exact (ncNonNil hvq (B.sOwn q hqS vq hvq) hqnc ⟨y, hy, hevq⟩ Sr.typed hsh hne a
              hHp).not_nilBase
          · rw [hHp] at hy; cases hy
            have hc : H.closure = none := by rw [Sr.frH]; exact B.clo
            exact evalValueL_clo hop hc hevq
          · rw [hHp] at hy; cases hy
            exact (evalValueL_spg hop (by rw [B.sOwn q hqS vq hvq]; exact hw) hevq).not_nilBase
        · have hHq : H.regs[q]? = frPS.regs[q]? := Sr.out q (fun h => hqS (hPS q h))
          exact (B.out r hrS q hqargs hqS).2.2.2.2 hqnn a (by rw [← hHq]; exact hHp)
      exact hnn hnil
  have hfr : mayFail tabs f r = true := by
    rw [mayFail_of hvr]; simpa using cls_ne_safe_of_mayPanic hmp
  have hrspa : isSPA f r = false := by
    rw [isSPA_of hvr]
    cases hs : (vr.op == .SPanchored)
    · rfl
    · rw [spa_not_mayPanic (by simpa using hs)] at hmp; cases hmp
  have hrT : r ∈ oT := (B.tMem r).2 ⟨hrS, hrspa⟩
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 hrT
  have hnl : n ≤ oT.length := Nat.le_of_lt (List.getElem?_eq_some_iff.1 hn).1
  have hk : (pre ++ r :: post)[pre.length]? = some r := by simp
  suffices hstep : ∀ j T y gv, j < n → Inv f frPT H T pre (oT.take j) → oT[j]? = some y →
      g.value? y = some gv →
      evalValueL md env (Ctx.makeSched tabs g) T gv = .panic e m ∨
        ∃ z, evalValueL md env (Ctx.makeSched tabs g) T gv = .ok z ∧
          (y ∈ pre → isNC f y = false → H.regs[y]? = some (some z)) by
    rcases walk_gen (env := env) S B (H := H) (P := pre) (e := e) (m := m) n hnl hstep with
      hp | ⟨T, hT, I⟩
    · rw [split_at hn, evalAllL_append, hp]
    · obtain ⟨fr', gr, hfr', hgr, hrr⟩ := tval S B hrT
      rw [hvr] at hfr'; cases hfr'
      have hstepR := (stepT S hf B Sr hPS hPc I hn hdoneR hvr hgr hrr).2 e m hr
      rw [split_at hn, evalAllL_append, hT]
      dsimp only
      rw [evalAllL_cons, stepVL_of (by rw [makeSched_f]; exact hgr), hstepR]
      all_goals rfl
  intro j T y gv hj I hyj hgv
  -- a value the target runs before `r`
  have hyT : y ∈ oT := List.mem_of_getElem? hyj
  obtain ⟨fv, gv', hfv, hgv', hrv⟩ := tval S B hyT
  rw [hgv] at hgv'; cases hgv'
  by_cases hyP : y ∈ pre
  · obtain ⟨v, z, hv, hz, hevy⟩ := Sr.eval y hyP
    rw [hfv] at hv; cases hv
    obtain ⟨z', hz', hzz⟩ := (stepT S hf B Sr hPS hPc I hyj (fun a ha hm => hPc y hyP a ha hm)
      hfv hgv hrv).1 z hevy
    exact .inr ⟨z', hz', fun _ hn => by rw [hz, hzz hn]⟩
  have hargsT := targs S B I hyj hfv hgv hrv
  have hcl : cls (Ctx.makeSched tabs g).tabs gv = cls tabs fv := by
    rw [makeSched_tabs]; exact cls_congr hrv
  cases hfy : mayFail tabs f y
  · have hs : cls tabs fv = .safe := by rw [mayFail_of hfv] at hfy; simpa using hfy
    obtain ⟨z, hz⟩ := evalValueL_safe (env := env) hf (hcl.trans hs) hargsT
    exact .inr ⟨z, hz, fun h => absurd h hyP⟩
  -- `y` runs after `r` in the source: `swapOK`
  have hyr : y ≠ r := fun h => by
    subst h; have := nodup_idx B.tNodup hyj hn; omega
  have hyPost : y ∈ post := by
    have : y ∈ pre ++ r :: post := ((B.tMem y).1 hyT).1
    simp only [List.mem_append, List.mem_cons] at this
    rcases this with h | h | h
    · exact absurd h hyP
    · exact absurd h hyr
    · exact h
  obtain ⟨l', hl'⟩ := List.mem_iff_getElem?.1 hyPost
  have hl : (pre ++ r :: post)[pre.length + (l' + 1)]? = some y := by
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, List.getElem?_cons_succ, hl']
  have hsw := B.swap j n r y hj hyj hn hfy hfr pre.length (pre.length + (l' + 1)) (by omega) hk hl
  unfold swapOK swapOKB nilPtrSwap at hsw
  rw [hvr, hfv] at hsw
  -- `y` is a parameter's register piece: it evaluates
  cases hao : argOK tabs (Ctx.makeL tabs f).params fv
  case true =>
    have hao' : argOK (Ctx.makeSched tabs g).tabs (Ctx.makeSched tabs g).params gv = true := by
      rw [makeSched_tabs, params_eq S, argOK_congr hrv, hao]
    have himg : T.images.size = (Ctx.makeSched tabs g).params.size := by
      have hTi : T.images = frPS.images := by rw [I.frT, B.frT]
      rw [hTi, params_eq S]; exact B.img
    obtain ⟨z, hz⟩ := evalValueL_argOK (md := md) (env := env) hao' himg
    exact .inr ⟨z, hz, fun h => absurd h hyP⟩
  simp only [hao, hmp, hrnb, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
    beq_iff_eq, Bool.not_eq_true'] at hsw
  obtain ⟨hcr, hsm⟩ : (cls tabs vr = .load ∨ cls tabs vr = .nil) ∧
      sameMem f (srcPos f.valueTab.size (pre ++ r :: post)) vr fv = true := by
    rcases hsw with ⟨⟨h1, h2⟩, -⟩ | ⟨⟨⟨h1, h2⟩, -⟩, -⟩ <;> exact ⟨h1, h2⟩
  obtain ⟨rfl, ℓx, hℓx, hHℓx⟩ := hld hcr
  have hDo : ∀ a ∈ oT.take j, a ∈ oT := fun a ha => List.mem_of_mem_take ha
  -- the memory: `y`'s last argument `ℓ` is `r`'s, or the memory argument of an `LDAR*` whose
  -- `Select1` `r`'s reaches (`ldReach`), which holds the same memory
  obtain ⟨ℓ, hfb, hreach, hℓspa⟩ : ∃ ℓ, fv.args.back? = some ℓ ∧
      ldReach f (srcPos f.valueTab.size (pre ++ r :: post)) f.valueTab.size ℓx ℓ = true ∧
      isSPA f ℓ = false := by
    unfold sameMem at hsm
    rw [hℓx] at hsm
    cases hfb : fv.args.back? with
    | none => rw [hfb] at hsm; cases hsm
    | some ℓ =>
      rw [hfb] at hsm
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hsm
      exact ⟨ℓ, rfl, hsm.1, hsm.2⟩
  have hfℓ : fv.args[fv.args.size - 1]? = some ℓ := back_get hfb
  obtain ⟨hgℓ, hgℓm⟩ := argsF_g hgv hrv hfℓ
  have hℓxr : ℓx ∈ argsF f r := by
    rw [argsF_of hvr]; exact Array.mem_toList_iff.2 (Array.mem_of_getElem? (back_get hℓx))
  obtain ⟨hHℓ, hcase⟩ := ldReach_src Sr hPc f.valueTab.size ℓx ℓ hreach (hdoneR ℓx hℓxr) hHℓx
  have hTℓ : T.regs[rep f ℓ]? = some (some (.mem m)) := by
    have hrepT : rep f ℓ ∈ oT → rep f ℓ ∈ oT.take j := fun hm => topo_before B.tTopo hyj hgℓm hm
    rcases hcase with hc | ⟨l, hlP, vl, hvl, hb⟩
    · subst hc
      obtain ⟨-, -, hns, -⟩ := argFact S B Sr hPS hPc I hDo hvr hrS hdoneR (back_get hℓx) hrepT
      rw [hns hℓspa, hHℓ]
    · obtain ⟨-, -, hns, -⟩ := argFact S B Sr hPS hPc I hDo hvl (hPS l hlP)
        (fun a ha hm => hPc l hlP a ha hm) (back_get hb) hrepT
      rw [hns hℓspa, hHℓ]
  have hgsz : gv.args.size = fv.args.size := by rw [hrv.args, Array.size_map]
  rcases hsw with ⟨-, (hload | ⟨⟨⟨hnil, hrk⟩, h0⟩, hall⟩) | ⟨hnil, hany⟩⟩ | ⟨⟨-, hnil⟩, hany⟩
  · rcases evalValueL_load (env := env) hf (hcl.trans hload) hargsT with ⟨z, hz⟩ |
      ⟨ℓ', m', hb', hT', hp'⟩
    · exact .inr ⟨z, hz, fun h => absurd h hyP⟩
    · have : ℓ' = rep f ℓ := by
        have := back_get hb'
        rw [hgsz, hgℓ] at this; cases this; rfl
      subst this
      rw [hTℓ] at hT'; cases hT'
      exact .inl hp'
  · obtain ⟨hnc, hsz2⟩ := cls_nil hnil
    obtain ⟨p, hp0⟩ : ∃ p, fv.args[0]? = some p := ⟨fv.args[0], by simp [hsz2]⟩
    rw [hp0] at hall
    have hpspa : isSPA f p = false := by simpa using hall
    have hf1 : fv.args[1]? = some ℓ := by rw [hsz2] at hfℓ; exact hfℓ
    have hfargs : fv.args = #[p, ℓ] := arr_two hsz2 hp0 hf1
    have hgargs : gv.args = #[rep f p, rep f ℓ] := by rw [hrv.args, hfargs]; simp
    obtain ⟨p', a, hp', hHp, hpa⟩ := hptr (by
      rcases hrk with h | h
      · exact .inl (mem_of_decide h)
      · exact .inr h)
    rw [h0, hp0] at hp'; cases hp'
    obtain ⟨hg0, hg0m⟩ := argsF_g hgv hrv hp0
    have hTp : T.regs[rep f p]? = some (some a) := by
      obtain ⟨-, -, hns, -⟩ := argFact S B Sr hPS hPc I hDo hvr hrS hdoneR (k := 0) (by rw [h0, hp0])
        (fun hm => topo_before B.tTopo hyj hg0m hm)
      rw [hns hpspa, hHp]
    exact .inl (evalValueL_nc_nil (env := env) (ctx := Ctx.makeSched tabs g) hf (hrv.op.trans hnc)
      hgargs hTp hpa hTℓ)
  · -- `y` is a nil check of a pointer-shaped parameter piece `p` that the source ran before `r`
    -- or that is outside the block
    obtain ⟨hnc, hsz2⟩ := cls_nil hnil
    obtain ⟨p, hp0⟩ : ∃ p, fv.args[0]? = some p := ⟨fv.args[0], by simp [hsz2]⟩
    rw [hp0] at hany
    simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at hany
    obtain ⟨hap, hposr⟩ := hany
    obtain ⟨vp, hvp, hpok⟩ : ∃ vp, f.value? p = some vp ∧
        argOK tabs (Ctx.makeL tabs f).params vp = true := by
      unfold argPtr at hap
      cases hvp : f.value? p with
      | none => rw [hvp] at hap; cases hap
      | some vp =>
        rw [hvp] at hap
        simp only [Bool.and_eq_true] at hap
        exact ⟨vp, rfl, hap.1⟩
    have hpop : vp.op = .ArgIntReg := by
      simp only [argOK, Bool.and_eq_true, beq_iff_eq] at hpok
      exact hpok.1.1
    have hpnc : isNC f p = false := by rw [isNC_of hvp, hpop]; rfl
    have hpspa : isSPA f p = false := by rw [isSPA_of hvp, hpop]; rfl
    have hrepp : rep f p = p := rep_self hpnc hpspa
    have hf1 : fv.args[1]? = some ℓ := by rw [hsz2] at hfℓ; exact hfℓ
    have hfargs : fv.args = #[p, ℓ] := arr_two hsz2 hp0 hf1
    have hgargs : gv.args = #[p, rep f ℓ] := by rw [hrv.args, hfargs]; simp [hrepp]
    -- the target's register of `p`: nil or a pointer that is not wild
    obtain ⟨z, q, hTp, hq, hqw⟩ : ∃ z q, T.regs[p]? = some (some z) ∧ z.asPtrWord = some q ∧
        q.wild = false := by
      by_cases hpS : p ∈ pre ++ r :: post
      · -- the source ran `p` before `r`
        obtain ⟨k', hk'⟩ := List.mem_iff_getElem?.1 hpS
        rw [srcPos_get B.sNodup B.sLt hk', srcPos_get B.sNodup B.sLt hk] at hposr
        have hpP : p ∈ pre := by
          rw [List.getElem?_append_left (by omega)] at hk'
          exact List.mem_of_getElem? hk'
        obtain ⟨vp', z, hvp', hHz, hevz⟩ := Sr.eval p hpP
        rw [hvp] at hvp'; cases hvp'
        obtain ⟨q, hq, hqw⟩ := hAP.regs Sr.frH p vp hvp hap z hevz
        obtain ⟨-, hg0m⟩ := argsF_g hgv hrv hp0
        rw [hrepp] at hg0m
        have hpD : p ∈ oT.take j :=
          topo_before B.tTopo hyj hg0m ((B.tMem p).2 ⟨hPS p hpP, hpspa⟩)
        exact ⟨z, q, by rw [I.inP p hpD hpP hpnc, hHz], hq, hqw⟩
      · -- `p` is outside the block
        have hyS : y ∈ pre ++ r :: post := ((B.tMem y).1 hyT).1
        have hpy : p ∈ argsF f y := by
          rw [argsF_of hfv]; exact Array.mem_toList_iff.2 (Array.mem_of_getElem? hp0)
        obtain ⟨z, hz⟩ := (B.out y hyS p hpy hpS).1
        obtain ⟨q, hq, hqw⟩ := B.argOut y hyS p hpy hpS hap z hz
        have hpD : p ∉ oT.take j := fun h => hpS ((B.tMem p).1 (List.mem_of_mem_take h)).1
        exact ⟨z, q, by rw [I.out p hpD, B.agree p hpnc hpspa, hz], hq, hqw⟩
    by_cases hqb : q.blk = .nil
    · have hqn : q.isNil = true := by simpa [Ptr.wild, hqb] using hqw
      exact .inl (evalValueL_nc_nil (env := env) (ctx := Ctx.makeSched tabs g) hf
        (hrv.op.trans hnc) hgargs hTp ⟨q, addr_of_asPtrWord hq, hqn⟩ hTℓ)
    · obtain ⟨w, hw⟩ := evalValueL_nc_pass (md := md) (env := env) (ctx := Ctx.makeSched tabs g)
        (hrv.op.trans hnc) hgargs hTp ⟨q, hq, hqb⟩ hTℓ
      exact .inr ⟨w, hw, fun h => absurd h hyP⟩
  · -- `y` is a nil check of a value whose bypass `q` is pointer-shaped and that the source ran
    -- before `r` or that is outside the block: `NilPtrsOK`
    obtain ⟨hnc, hsz2⟩ := cls_nil hnil
    obtain ⟨q0, hq0⟩ : ∃ q, fv.args[0]? = some q := ⟨fv.args[0], by simp [hsz2]⟩
    rw [hq0] at hany
    simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hany
    obtain ⟨⟨⟨hsh, hqnc⟩, hqspa⟩, hposr⟩ := hany
    generalize hqdef : rep f q0 = q at hsh hqnc hqspa hposr
    have hf1 : fv.args[1]? = some ℓ := by rw [hsz2] at hfℓ; exact hfℓ
    have hfargs : fv.args = #[q0, ℓ] := arr_two hsz2 hq0 hf1
    have hgargs : gv.args = #[q, rep f ℓ] := by rw [hrv.args, hfargs, ← hqdef]; simp
    -- the target's register of `q` is the source's at the panic
    have hTq : T.regs[q]? = H.regs[q]? := by
      by_cases hqS : q ∈ pre ++ r :: post
      · obtain ⟨k', hk'⟩ := List.mem_iff_getElem?.1 hqS
        rw [srcPos_get B.sNodup B.sLt hk', srcPos_get B.sNodup B.sLt hk] at hposr
        have hqP : q ∈ pre := by
          rw [List.getElem?_append_left (by omega)] at hk'
          exact List.mem_of_getElem? hk'
        obtain ⟨-, hg0m⟩ := argsF_g hgv hrv hq0
        rw [hqdef] at hg0m
        have hqD : q ∈ oT.take j :=
          topo_before B.tTopo hyj hg0m ((B.tMem q).2 ⟨hPS q hqP, hqspa⟩)
        exact I.inP q hqD hqP hqnc
      · have hqD : q ∉ oT.take j := fun h => hqS ((B.tMem q).1 (List.mem_of_mem_take h)).1
        rw [I.out q hqD, B.agree q hqnc hqspa, Sr.out q (fun h => hqS (hPS q h))]
    obtain ⟨z, hz⟩ := hargsT q (by rw [hgargs]; simp)
    have hNRH : NilRegsOK tabs f H := hNR pre.length H (by rw [List.take_left]; exact hpre)
    -- the nil check of the source that checks `q`: `y`, or the last of `q0`'s chain
    have hu := S.argUse hfv hq0
    have hq0spa : isSPA f q0 = false := by
      cases h : isSPA f q0
      · rfl
      · obtain ⟨-, hsym, -⟩ := (use_rep hu).2.2.1 h
        simp only [Option.map_some, Option.getD_some, hnc, Bool.and_eq_true] at hsym
        exact absurd hsym.1 (by decide)
    obtain ⟨c, vc, hvc, hcnc, hc0⟩ : ∃ c vc, f.value? c = some vc ∧ vc.op.nilCheck = true ∧
        vc.args[0]? = some q := by
      cases hn0 : isNC f q0
      · refine ⟨y, fv, hfv, by rw [hnc]; rfl, ?_⟩
        rw [hq0, ← hqdef, rep_self hn0 hq0spa]
      · rw [← hqdef]; exact chain_last _ q0 (use_chain hu hn0) (Nat.le_refl _) hn0
    obtain ⟨p, hp, hpw⟩ := hNRH c vc q hvc hcnc hc0 hsh z (by rw [← hTq]; exact hz)
    by_cases hpb : p.blk = .nil
    · have hpn : p.isNil = true := by simpa [Ptr.wild, hpb] using hpw
      exact .inl (evalValueL_nc_nil (env := env) (ctx := Ctx.makeSched tabs g) hf
        (hrv.op.trans hnc) hgargs hz ⟨p, addr_of_asPtrWord hp, hpn⟩ hTℓ)
    · obtain ⟨w, hw⟩ := evalValueL_nc_pass (md := md) (env := env) (ctx := Ctx.makeSched tabs g)
        (hrv.op.trans hnc) hgargs hz ⟨p, hp, hpb⟩ hTℓ
      exact .inr ⟨w, hw, fun h => absurd h hyP⟩

end GoFV.Proof.SchedL

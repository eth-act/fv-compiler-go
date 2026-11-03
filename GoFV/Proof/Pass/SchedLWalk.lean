import GoFV.Proof.Pass.SchedLBlock

/-!
# `schedule` on `runSched`: one block's values, end to end

`walk_ok`: if the source (`runL`'s order `oS`, faulting) evaluates the block's non-`Phi`s, the
target (`runSched`'s order `oT`) evaluates its own, agreeing with the source on every value it
ran that is no nil check (`Inv`). `walk_panic`: if the source panics, the target panics alike.
Before the source's panicking value `r` the target runs values the source ran before `r`
(alike, `stepT`), values that never fail (`Cls.safe`), and values `swapOK` lets it run first
(a load on `r`'s memory, or a nil check of `r`'s pointer word on it), which evaluate or panic
with `nilDeref` of that memory, as `r` does; at `r` the target panics as the source.
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
    {frPS frPT : Frame} (B : BStep tabs f g md oS oT frPS frPT) {e : Panic} {m : Mem}
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
  unfold swapOK at hsw
  rw [hvr, hfv] at hsw
  simp only [hmp, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    Bool.not_eq_true'] at hsw
  obtain ⟨⟨⟨hcr, hlast⟩, hnspa⟩, hcy⟩ := hsw
  obtain ⟨rfl, ℓ, hℓ, hHℓ⟩ := hld hcr
  have hℓspa : isSPA f ℓ = false := by rw [hℓ] at hnspa; simpa using hnspa
  have hDo : ∀ a ∈ oT.take j, a ∈ oT := fun a ha => List.mem_of_mem_take ha
  -- the memory: `y`'s last argument is `r`'s
  have hfℓ : fv.args[fv.args.size - 1]? = some ℓ := back_get (by rw [← hlast]; exact hℓ)
  obtain ⟨hgℓ, hgℓm⟩ := argsF_g hgv hrv hfℓ
  have hTℓ : T.regs[rep f ℓ]? = some (some (.mem m)) := by
    obtain ⟨-, -, hns, -⟩ := argFact S B Sr hPS hPc I hDo hvr hrS hdoneR (back_get hℓ)
      (fun hm => topo_before B.tTopo hyj hgℓm hm)
    rw [hns hℓspa, hHℓ]
  have hgsz : gv.args.size = fv.args.size := by rw [hrv.args, Array.size_map]
  rcases hcy with hload | ⟨⟨⟨hnil, hrk⟩, h0⟩, hall⟩
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
    simp only [Option.all_some, Bool.and_eq_true, Bool.not_eq_true'] at hall
    obtain ⟨hpspa, hpw⟩ := hall
    have hf1 : fv.args[1]? = some ℓ := by rw [hsz2] at hfℓ; exact hfℓ
    have hfargs : fv.args = #[p, ℓ] := arr_two hsz2 hp0 hf1
    have hgargs : gv.args = #[rep f p, rep f ℓ] := by rw [hrv.args, hfargs]; simp
    obtain ⟨p', a, hp', hHp, hpa⟩ := hptr (by
      rcases hrk with h | h
      · exact .inl (mem_of_decide h)
      · exact .inr h)
    rw [h0, hp0] at hp'; cases hp'
    have hta : a.hasTy ((Ctx.makeL tabs f).tys[p]?.getD .other) = true :=
      hasTy_of_typedL (Sr.typed p a hHp)
    obtain ⟨q, hq⟩ := asPtrWord_of_ptrIsh hpw hta hpa
    obtain ⟨hg0, hg0m⟩ := argsF_g hgv hrv hp0
    have hTp : T.regs[rep f p]? = some (some a) := by
      obtain ⟨-, -, hns, -⟩ := argFact S B Sr hPS hPc I hDo hvr hrS hdoneR (k := 0) (by rw [h0, hp0])
        (fun hm => topo_before B.tTopo hyj hg0m hm)
      rw [hns hpspa, hHp]
    rcases evalValueL_nc_word (env := env) (ctx := Ctx.makeSched tabs g) hf (hrv.op.trans hnc)
        hgargs hTp hq hTℓ with ⟨z, hz⟩ | hz
    · exact .inr ⟨z, hz, fun h => absurd h hyP⟩
    · exact .inl hz

end GoFV.Proof.SchedL

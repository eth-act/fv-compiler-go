import GoFV.Proof.Regalloc.Read

/-!
# Regalloc checker soundness, stage 3: values

One target value against the source (`docs/plans/regalloc-check.md` §3): a kept value computes
its source value's result (`kept_sim`; it panics when the source does), a `KeepAlive` turned into
`Copy`/`VarLive` its memory (`keepAlive_sim`), and a move or a rematerialised constant leaves the
source alone (`new_sim`); each preserves `Match` with the checker's new facts.
-/

namespace GoFV.Proof.RA

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RegallocCheck

variable {tabs : Tables} {f g : Func}

/-! ## The two evaluations, unfolded -/

/-- What `stepLoc` does with result `r` of `w`: clobber, then write `r` at `w`'s shape. -/
def putRes (lc : LocCtx) (s : LocState) (w : Value) (r : Val) : LocState :=
  (s.clobber lc w).write lc w.id ((LMode.loc lc.ctx.f).retype (lc.ty w.id) r)

/-- `stepLoc` of an op other than a phi, a move or `MOVDreg`/`MOVDnop`: `evalOpL`. -/
theorem stepLoc_op {env : Env} {lc : LocCtx} {s : LocState} {w : Value} {argv : List Val}
    (h1 : w.op ≠ .Phi) (h2 : w.op ≠ .LoadReg) (h3 : w.op ≠ .StoreReg)
    (h4 : w.op ≠ .ARM64MOVDreg) (h5 : w.op ≠ .ARM64MOVDnop)
    (hargs : w.args.toList.mapM (s.read lc) = .ok argv) :
    stepLoc env lc s w =
      (evalOpL true env lc.ctx s.fr w argv (lc.ty w.id)).bind fun r => .ok (putRes lc s w r) := by
  unfold stepLoc
  rw [show (w.op == .Phi) = false from by simpa using h1]
  simp only [Bool.false_eq_true, ite_false]
  show Res.bind (w.args.toList.mapM (s.read lc)) _ = _
  rw [hargs, Res.bind_ok]
  split <;> first | (exfalso; simp_all; done) | rfl

theorem stepLoc_movd {env : Env} {lc : LocCtx} {s : LocState} {w : Value} {argv : List Val}
    (hm : w.op = .ARM64MOVDreg ∨ w.op = .ARM64MOVDnop)
    (hargs : w.args.toList.mapM (s.read lc) = .ok argv) :
    stepLoc env lc s w = .ok (putRes lc s w (movdLoc lc w argv (lc.ty w.id))) := by
  obtain ⟨id, op, t, ai, ax, pos, us, args, blk⟩ := w
  dsimp only at hm hargs
  rcases hm with rfl | rfl <;>
  · unfold stepLoc
    simp only [show (Op.ARM64MOVDreg == .Phi) = false from by decide,
      show (Op.ARM64MOVDnop == .Phi) = false from by decide, Bool.false_eq_true, ite_false]
    show Res.bind (args.toList.mapM _) _ = _
    rw [hargs, Res.bind_ok]
    rfl

theorem stepLoc_move {env : Env} {lc : LocCtx} {s : LocState} {w : Value} {x : Val}
    (hm : w.op = .LoadReg ∨ w.op = .StoreReg)
    (hargs : w.args.toList.mapM (s.read lc) = .ok [x]) :
    stepLoc env lc s w = .ok (putRes lc s w x) := by
  obtain ⟨id, op, t, ai, ax, pos, us, args, blk⟩ := w
  dsimp only at hm hargs
  rcases hm with rfl | rfl <;>
  · unfold stepLoc
    simp only [show (Op.LoadReg == .Phi) = false from by decide,
      show (Op.StoreReg == .Phi) = false from by decide, Bool.false_eq_true, ite_false]
    show Res.bind (args.toList.mapM _) _ = _
    rw [hargs, Res.bind_ok]
    rfl

theorem mapM_regsAre {m : ID → String} {r : ID → Option Val} :
    ∀ {l : List ID} {L : List Val}, RegsAre r l L →
      l.mapM (fun a => Res.ofOption (m a) (r a)) = .ok L
  | [], [], _ => rfl
  | a :: l, x :: L, h => by
    rw [List.mapM_cons, h.1]
    show Res.bind (l.mapM _) _ = _
    rw [mapM_regsAre h.2]; rfl
  | [], _ :: _, h | _ :: _, [], h => by simp [RegsAre] at h

theorem evalValueL_eq {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} (h : RegsAre (fun a => (fr.regs[a]?).join) v.args.toList argv) :
    evalValueL md env ctx fr v =
      (evalOpL md.faulting env ctx fr v argv (ctx.tys[v.id]?.getD .other)).bind fun r =>
        .ok (md.retype (ctx.tys[v.id]?.getD .other) r) := by
  unfold evalValueL
  show Res.bind (v.args.toList.mapM _) _ = _
  rw [mapM_regsAre h, Res.bind_ok]
  rfl

/-- A source value that is not `stuck` has its argument registers. -/
theorem evalValueL_regsAre {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    (h : ∀ msg, evalValueL md env ctx fr v ≠ .stuck msg) :
    ∃ argv, RegsAre (fun a => (fr.regs[a]?).join) v.args.toList argv := by
  unfold evalValueL at h
  cases hm : v.args.toList.mapM (fun a =>
      Res.ofOption s!"v{v.id}: argument v{a} has no value" (fr.regs[a]?).join) with
  | ok L => exact ⟨L, mapM_ofOption_forall₂ hm⟩
  | panic e m => exact absurd hm mapM_ofOption_ne_panic
  | stuck msg =>
    exfalso
    apply h msg
    show Res.bind _ _ = _
    rw [hm]; rfl

/-! ## Writes -/

theorem putRes_fr (lc : LocCtx) (s : LocState) (w : Value) (r : Val) :
    (putRes lc s w r).fr = s.fr := by
  unfold putRes; rw [write_fr, clobber_fr]

theorem putRes_regs {lc : LocCtx} {s : LocState} (hs : RegsOK s) (w : Value) (r : Val) :
    RegsOK (putRes lc s w r) := regsOK_write (regsOK_clobber hs w) _ _

/-- A written location holds its component of the result. -/
theorem putRes_at_write {lc : LocCtx} {s : LocState} (hs : RegsOK s) {w : Value} {r : Val}
    (hnd : writesNodup (lc.home w.id) (lc.ty w.id) = true) {l : Loc} {j : Option Nat}
    (hl : (l, j) ∈ writeLocs (lc.home w.id) (lc.ty w.id)) :
    (putRes lc s w r).at l = comp j ((LMode.loc lc.ctx.f).retype (lc.ty w.id) r) :=
  at_write (regsOK_clobber hs w) hnd (tupleFits_retype _ _ _) hl

theorem mem_killAll {cx : Cx} {h : Option Location} {t : Ty} {S : Facts} {F : Fact}
    (hF : F ∈ killAll cx h t S) : F ∈ S ∧ ∀ l ∈ killLocs h t, clashes cx.tabs l F.1 = false :=
  mem_killLocs hF

/-- A fact that survives the clobbers and the write of `w` is at a location they leave alone. -/
theorem putRes_at_kill {s : LocState} (hs : RegsOK s) {w : Value} {r : Val} {S : Facts}
    {F : Fact} (hF : F ∈ killAll (Cx.make tabs f g) ((Cx.make tabs f g).lc.home w.id)
      ((Cx.make tabs f g).gty w.id) (clobberFacts (Cx.make tabs f g) S w)) :
    F ∈ S ∧ (putRes (Cx.make tabs f g).lc s w r).at F.1 = s.at F.1 := by
  obtain ⟨hF1, hcl⟩ := mem_killAll hF
  obtain ⟨hF2, hat⟩ := at_clobber hF1 s
  refine ⟨hF2, ?_⟩
  unfold putRes
  rw [at_write_other (regsOK_clobber hs w) (fun l hl => by rw [lc_tabs]; exact hcl l hl), hat]

/-! ## The source frame after a value -/

/-- The source frame after value `d` takes `y`. -/
def upd (fr : Frame) (d : ID) (y : Val) : Frame := { fr with regs := fr.regs.set! d (some y) }

theorem upd_ne {fr : Frame} {d a : ID} {y : Val} (h : a ≠ d) : (upd fr d y).regs[a]? = fr.regs[a]? := by
  simp [upd, Array.set!, Array.getElem?_setIfInBounds, Ne.symm h]

theorem upd_self {fr : Frame} {d : ID} {y : Val} :
    ((upd fr d y).regs[d]?).join = some y ∨
      (((upd fr d y).regs[d]?).join = none ∧ (fr.regs[d]?).join = none) := by
  by_cases hd : d < fr.regs.size
  · left; simp [upd, Array.set!, Array.getElem?_setIfInBounds, hd]
  · right
    have : fr.regs[d]? = none := Array.getElem?_eq_none (Nat.le_of_not_lt hd)
    simp [upd, Array.set!, Array.getElem?_setIfInBounds, hd, this]

theorem upd_fr_eq {frA fr : Frame} (h : fr = { frA with regs := fr.regs }) (d : ID) (y : Val) :
    upd fr d y = { frA with regs := (upd fr d y).regs } := by
  unfold upd; rw [h]

theorem regsAre_map {r : ID → Option Val} {F : ID → Val} :
    ∀ {l : List ID} {L : List Val}, RegsAre r l L → (∀ a ∈ l, ∀ x, r a = some x → x = F a) →
      L = l.map F
  | [], [], _, _ => rfl
  | a :: l, x :: L, h, hF => by
    rw [List.map_cons, hF a (List.mem_cons_self ..) x h.1,
      regsAre_map h.2 (fun b hb => hF b (List.mem_cons_of_mem _ hb))]
  | [], _ :: _, h, _ | _ :: _, [], h, _ => by simp [RegsAre] at h

theorem isK_of_arg {cx : Cx} {v : Value} (hk : isKVal cx.f v = true) {a : ID} (ha : a ∈ v.args) :
    cx.isK a = true := by
  obtain ⟨u, hu, hid, hop, hargs⟩ := (isKVal_spec hk).2 a ha
  unfold Cx.isK
  rw [hu]
  simp only [hid, beq_self_eq_true, Bool.true_and]
  unfold isKVal
  rw [hargs]
  simp only [Array.all_empty, Bool.and_true]
  rcases hop with h | h <;> rw [h] <;> rfl

/-- A frame constant evaluates to its `kval`. -/
theorem eval_kval {env : Env} {frA : Frame} {S : Facts} {fr : Frame} {s : LocState}
    (h : Match (Cx.make tabs f g) env frA S fr s) {d : ID} {u : Value} {y : Val}
    (hk : (Cx.make tabs f g).isK d = true) (hu : f.value? d = some u)
    (hy : evalValueL (Cx.make tabs f g).md env (Cx.make tabs f g).sc fr u = .ok y) :
    y = kval (Cx.make tabs f g) env frA d := by
  obtain ⟨v, hv, hid, hkv⟩ := isK_spec hk
  rw [show (Cx.make tabs f g).f = f from rfl, hu] at hv
  cases hv
  obtain ⟨argv, hargv⟩ := evalValueL_regsAre (fun msg h' => by rw [hy] at h'; cases h')
  have hmap : argv = u.args.toList.map (kval (Cx.make tabs f g) env frA) :=
    regsAre_map hargv fun a ha x hx =>
      h.kinv a x (isK_of_arg hkv (Array.mem_toList_iff.1 ha)) hx
  rw [evalValueL_eq hargv, evalOpL_kop_eq (isKVal_spec hkv).1, hmap] at hy
  simp only [Res.bind_ok] at hy
  cases hy
  rw [kval_eq (Cx.make tabs f g) env frA hu hkv, hid]
  rfl

theorem mem_redefine {cx : Cx} {S : Facts} {u : ID} {F : Fact} (h : F ∈ cx.redefine S u) :
    F ∈ S ∧ (cx.isK u = true ∨ (F.2.id ≠ u ∧ (F.1 = .avail → cx.reads F.2.id u = false))) := by
  unfold Cx.redefine at h
  split at h
  · exact ⟨h, .inl (by assumption)⟩
  · rw [List.mem_filter] at h
    obtain ⟨hS, hc⟩ := h
    refine ⟨hS, .inr ⟨?_, ?_⟩⟩
    · intro he; simp [he] at hc
    · intro ha; simp [ha] at hc; exact hc.2

/-- A frame constant does not read itself. -/
theorem kval_not_self {cx : Cx} {d : ID} {u : Value} (hu : cx.f.value? d = some u)
    (hk : isKVal cx.f u = true) : d ∉ u.args := by
  intro hd
  obtain ⟨u', hu', -, -, hargs⟩ := (isKVal_spec hk).2 d hd
  rw [hu] at hu'; cases hu'
  rw [hargs] at hd
  simp at hd

/-- A fact the checker keeps across source value `d` (`Cx.redefine`), at a location the target
leaves alone, holds after `d` takes its value `y`. -/
theorem factOK_keep {env : Env} {frA : Frame} {S : Facts} {fr : Frame} {s : LocState}
    (h : Match (Cx.make tabs f g) env frA S fr s) {d : ID} {u : Value} {y : Val}
    (hu : f.value? d = some u) (hud : u.id = d)
    (hy : evalValueL (Cx.make tabs f g).md env (Cx.make tabs f g).sc fr u = .ok y)
    {F : Fact} (hF : F ∈ (Cx.make tabs f g).redefine S d) {s' : LocState}
    (hat : F.1 ≠ .avail → s'.at F.1 = s.at F.1) :
    FactOK (Cx.make tabs f g) env frA (upd fr d y) s' F := by
  obtain ⟨hFS, hred⟩ := mem_redefine hF
  have hfact := h.facts F hFS
  obtain ⟨l, o⟩ := F
  by_cases hl : l = .avail
  · subst hl
    obtain ⟨v, y0, hv, hvid, hreg, hev⟩ := factOK_avail.1 hfact
    refine factOK_avail.2 ⟨v, y0, hv, hvid, ?_, ?_⟩
    · by_cases hid : o.id = d
      · rw [hid] at hreg ⊢
        rcases upd_self (fr := fr) (d := d) (y := y) with h1 | ⟨-, h2⟩
        · rw [h1]
          rw [hid] at hv
          rw [show (Cx.make tabs f g).f = f from rfl, hu] at hv
          cases hv
          rw [hy] at hev; cases hev; rfl
        · rw [hreg] at h2; cases h2
      · rw [upd_ne hid]; exact hreg
    · rw [← hev]
      symm
      apply evalValueL_congr rfl
      intro a ha
      by_cases had : a = d
      · subst had
        -- `v` reads `d`: then `d` is a frame constant, which keeps its value
        by_cases hid : o.id = a
        · rw [hid] at hv
          rw [show (Cx.make tabs f g).f = f from rfl, hu] at hv
          cases hv
          rcases hred with hk | ⟨hne, -⟩
          · obtain ⟨u', hu', -, hkv⟩ := isK_spec hk
            rw [show (Cx.make tabs f g).f = f from rfl, hu] at hu'; cases hu'
            exact absurd ha (kval_not_self hu hkv)
          · exact absurd hid hne
        · have hk : (Cx.make tabs f g).isK a = true := by
            rcases hred with hk | ⟨-, hr⟩
            · exact hk
            · have := hr rfl
              unfold Cx.reads at this
              rw [hv] at this
              simp [ha] at this
          obtain ⟨z, hz⟩ := evalValueL_args_def (fun msg h' => by rw [hev] at h'; cases h') a ha
          have hz' : (fr.regs[a]?).join = some z := by rw [hz]; rfl
          have hzk := h.kinv a z hk hz'
          have hyk := eval_kval h hk hu hy
          have hlt : a < fr.regs.size := (Array.getElem?_eq_some_iff.1 hz).1
          simp [upd, Array.set!, Array.getElem?_setIfInBounds, hlt, hz, hzk, hyk]
          rw [← hzk]; simpa [hlt] using hz
      · exact (upd_ne had).symm
  · rw [factOK_loc hl] at hfact ⊢
    intro x hx
    have hsv : srcVal (Cx.make tabs f g) env frA (upd fr d y) o.id =
        srcVal (Cx.make tabs f g) env frA fr o.id := by
      unfold srcVal
      split
      · rfl
      · rename_i hko
        have hne : o.id ≠ d := by
          rcases hred with hk | ⟨hne, -⟩
          · intro he; rw [he] at hko; exact hko hk
          · exact hne
        rw [upd_ne hne]
    rw [hsv] at hx
    have := hfact x hx
    rw [hat hl]
    exact this

/-! ## Written locations -/

theorem compLocs_lt : ∀ {ts : List Ty} {rs : List (Option Nat)} {k : Nat} {l : Loc} {j : Nat},
    (l, j) ∈ compLocs ts rs k → j < k + ts.length
  | [], _, _, _, _, h => by simp [compLocs] at h
  | t :: ts, rs, k, l, j, h => by
    have ih : ∀ {rs'}, (l, j) ∈ compLocs ts rs' (k + 1) → j < k + (t :: ts).length := fun h' => by
      have := compLocs_lt h'; simp; omega
    unfold compLocs at h
    split at h
    · simp only [List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨-, rfl⟩ | h
      · simp
      · exact ih h
    · split at h
      · simp only [List.mem_cons, Prod.mk.injEq] at h
        rcases h with ⟨-, rfl⟩ | h
        · simp
        · exact ih h
      · split at h
        · simp only [List.mem_append, List.mem_map] at h
          rcases h with ⟨l', -, he⟩ | h
          · simp only [Prod.mk.injEq] at he; rw [← he.2]; simp
          · exact ih h
        · exact ih h
        · exact ih h

theorem writeLocs_ne {h : Option Location} {t : Ty} {l : Loc} {j : Option Nat}
    (hl : (l, j) ∈ writeLocs h t) : l ≠ .avail := by
  unfold writeLocs at hl
  split at hl
  · simp at hl; rw [hl.1]; nofun
  · simp only [List.mem_map] at hl
    obtain ⟨⟨l', j'⟩, hm, he⟩ := hl
    simp only [Prod.mk.injEq] at he
    rw [← he.1]; exact compLocs_ne hm
  · simp only [List.mem_map] at hl
    obtain ⟨l', hm, he⟩ := hl
    simp only [Prod.mk.injEq] at he
    rw [← he.1]; exact regLoc_ne (by simpa using hm)
  · simp at hl; rw [hl.1]; nofun
  · split at hl
    · simp at hl; rw [hl.1]; nofun
    · simp at hl

theorem writeLocs_tuple_lt {h : Option Location} {ts : List Ty} {l : Loc} {j : Nat}
    (hl : (l, some j) ∈ writeLocs h (.tuple ts)) : j < ts.length := by
  unfold writeLocs at hl
  split at hl
  · simp at hl
  · rename_i ts' heq
    cases heq
    simp only [List.mem_map] at hl
    obtain ⟨⟨l', j'⟩, hm, he⟩ := hl
    simp only [Prod.mk.injEq, Option.some.injEq] at he
    rw [← he.2]
    have := compLocs_lt hm
    simpa using this
  · rename_i hn; exact absurd rfl (hn _)
  · cases ‹Ty.tuple ts = Ty.mem›
  · rename_i hn _; exact absurd rfl (hn _)

theorem writeLocs_none {h : Option Location} {t : Ty} {l : Loc} {j : Option Nat}
    (hl : (l, j) ∈ writeLocs h t) (ht : ∀ ts, t ≠ .tuple ts) : j = none := by
  unfold writeLocs at hl
  split at hl
  · simp at hl; exact hl.2
  · exact absurd rfl (ht _)
  · simp only [List.mem_map] at hl
    obtain ⟨l', -, he⟩ := hl
    simp only [Prod.mk.injEq] at he
    exact he.2.symm
  · simp at hl; exact hl.2
  · split at hl
    · simp at hl; exact hl.2
    · simp at hl

theorem upd_size (fr : Frame) (d : ID) (y : Val) : (upd fr d y).regs.size = fr.regs.size := by
  simp [upd, Array.set!]

theorem upd_self' {fr : Frame} {d : ID} {y : Val} (hd : d < fr.regs.size) :
    (upd fr d y).regs[d]? = some (some y) := by
  simp [upd, Array.set!, Array.getElem?_setIfInBounds, hd]

theorem value?_lt {F : Func} {d : ID} {u : Value} (h : F.value? d = some u) :
    d < F.valueTab.size := by
  unfold Func.value? at h
  cases hd : F.valueTab[d]? with
  | none => rw [hd] at h; cases h
  | some _ => exact (Array.getElem?_eq_some_iff.1 hd).1

theorem redefine_mono {cx : Cx} {S T : Facts} {d : ID} (hT : ∀ F ∈ T, F ∈ S) {F : Fact}
    (h : F ∈ cx.redefine T d) : F ∈ cx.redefine S d := by
  unfold Cx.redefine at h ⊢
  split
  · rename_i hk; rw [if_pos hk] at h; exact hT F h
  · rename_i hk; rw [if_neg hk] at h
    rw [List.mem_filter] at h ⊢
    exact ⟨hT F h.1, h.2⟩

theorem pureEqs_spec {cx : Cx} {S : Facts} {u : Value} {v : ID} (hv : v ∈ pureEqs cx S u) :
    pureArm64 u.op = true ∧ (∃ o, (Loc.avail, o) ∈ S ∧ o.id = v) ∧ v ≠ u.id ∧
      ∃ xv, cx.f.value? v = some xv ∧ sameConst xv u = true := by
  unfold pureEqs at hv
  split at hv
  · simp at hv
  · rename_i hc
    simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true] at hc
    rw [List.mem_filterMap] at hv
    obtain ⟨⟨l, o⟩, hF, he⟩ := hv
    dsimp only at he
    split at he
    · rename_i hcond
      cases he
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hcond
      obtain ⟨⟨⟨hl, -⟩, hne⟩, hsc⟩ := hcond
      subst hl
      refine ⟨hc.1, ⟨o, hF, rfl⟩, hne, ?_⟩
      cases hx : cx.f.value? o.id with
      | none => rw [hx] at hsc; simp at hsc
      | some xv => rw [hx] at hsc; exact ⟨xv, rfl, by simpa using hsc⟩
    · cases he

theorem selEqs_spec {cx : Cx} {S : Facts} {w u : Value} {v : ID} (hv : v ∈ selEqs cx S w u) :
    ∃ i a l x xv, selIndex u = some i ∧ u.args.toList = [a] ∧ l ≠ .avail ∧
      (l, (⟨a, some i, false⟩ : Orig)) ∈ S ∧ (∃ o, (Loc.avail, o) ∈ S ∧ o.id = v) ∧ v ≠ u.id ∧
      cx.f.value? v = some xv ∧ xv.args.toList = [x] ∧ xv.op = u.op ∧ xv.aux = u.aux ∧
      xv.auxInt = u.auxInt ∧ xv.type = u.type ∧ x ≠ u.id ∧
      (l, (⟨x, some i, false⟩ : Orig)) ∈ S := by
  unfold selEqs at hv
  split at hv
  · rename_i i a a' hi ha ha'
    split at hv
    · rename_i ls hr
      split at hv
      · rename_i l j hfind
        have hl : l ≠ .avail := readLoc_tuple_ne hr (List.mem_of_find?_eq_some hfind)
        split at hv
        · simp at hv
        · rename_i hS
          simp only [Bool.not_eq_true', Bool.not_eq_false] at hS
          rw [List.mem_filterMap] at hv
          obtain ⟨⟨l0, o⟩, hF, he⟩ := hv
          dsimp only at he
          split at he
          · rename_i hcond
            simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hcond
            obtain ⟨⟨hl0, -⟩, hne⟩ := hcond
            subst hl0
            split at he
            · rename_i xv hxv
              split at he
              · rename_i x hx
                split at he
                · rename_i hc
                  cases he
                  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
                  obtain ⟨⟨⟨⟨⟨hop, haux⟩, hai⟩, hty⟩, hxne⟩, hxS⟩ := hc
                  exact ⟨i, a, l, x, xv, hi, ha, hl, by simpa using hS, ⟨o, hF, rfl⟩, hne, hxv, hx,
                    hop, haux, hai, hty, hxne, by simpa using hxS⟩
                · cases he
              · cases he
            · cases he
          · cases he
      · simp at hv
    · simp at hv
  · simp at hv

theorem regsAre_length {r : ID → Option Val} :
    ∀ {l : List ID} {L : List Val}, RegsAre r l L → L.length = l.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [regsAre_length h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [RegsAre] at h

theorem regsAre_get {r : ID → Option Val} :
    ∀ {l : List ID} {L : List Val}, RegsAre r l L → ∀ {j : Nat} {a : ID}, l[j]? = some a →
      ∃ x, L[j]? = some x ∧ r a = some x
  | [], [], _, _, _, hj => by simp at hj
  | a :: l, x :: L, h, j, b, hj => by
    cases j with
    | zero => simp at hj; subst hj; exact ⟨x, rfl, h.1⟩
    | succ j => simpa using regsAre_get h.2 (by simpa using hj)
  | [], _ :: _, h, _, _, _ | _ :: _, [], h, _, _, _ => by simp [RegsAre] at h

theorem mrOK_spec {cx : Cx} {S : Facts} {w u : Value} (h : mrOK cx S w u = true) :
    u.op = .MakeResult ∧ ∃ ts, cx.gty w.id = .tuple ts ∧ ts.length ≤ u.args.size ∧
      ∀ l j, (l, j) ∈ writeLocs (cx.lc.home w.id) (cx.gty w.id) →
        ∃ j', j = some j' ∧ mrSame cx S w u ts l j' = true := by
  unfold mrOK at h
  rw [Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  revert h2
  generalize cx.gty w.id = G
  intro h2
  cases G with
  | tuple ts =>
    rw [Bool.and_eq_true] at h2
    refine ⟨ts, rfl, by simpa using h2.1, fun l j hl => ?_⟩
    have := List.all_eq_true.1 h2.2 (l, j) hl
    cases j with
    | none => simp at this
    | some j' => exact ⟨j', rfl, this⟩
  | _ => cases h2

/-! ## Kept values -/

/-- Source value `d` (= `u`) took `y`: every location written by `w` holds component `j` of
`y`; the source value of `canon d` is `y`. -/
theorem written_ok {env : Env} {frA : Frame} {S : Facts} {fr : Frame} {s : LocState}
    (h : Match (Cx.make tabs f g) env frA S fr s) {d : ID} {u : Value} {y : Val}
    (hu : f.value? d = some u) (hud : u.id = d)
    (hy : evalValueL (Cx.make tabs f g).md env (Cx.make tabs f g).sc fr u = .ok y) :
    srcVal (Cx.make tabs f g) env frA (upd fr d y) ((Cx.make tabs f g).canon d) = some y := by
  have hlt : d < fr.regs.size := by rw [h.fsize]; exact value?_lt hu
  rcases canon_cases (Cx.make tabs f g) d with hc | ⟨hk, hkc, -⟩
  · rw [hc]
    unfold srcVal
    split
    · rename_i hk; rw [eval_kval h hk hu hy]
    · rw [upd_self' hlt]; rfl
  · unfold srcVal
    rw [if_pos hkc, (kval_canon (env := env) (frA := frA) hk).1, eval_kval h hk hu hy]

theorem kept_match {env : Env} {frA : Frame} {S : Facts} {fr : Frame} {s : LocState}
    (h : Match (Cx.make tabs f g) env frA S fr s) (hlow : f.lowered = g.lowered)
    {d : ID} {u w : Value} (hu : f.value? d = some u) (hw : g.value? d = some w)
    (hud : u.id = d) (hwd : w.id = d) (hsame : sameOp u w = true)
    (hnd : writesNodup ((Cx.make tabs f g).lc.home d) ((Cx.make tabs f g).gty d) = true)
    {argv : List Val} (hargv : RegsAre (fun a => (fr.regs[a]?).join) u.args.toList argv)
    {r0 : Val} (hr0 : evalOpL true env (Cx.make tabs f g).sc fr u argv
      ((Cx.make tabs f g).fty d) = .ok r0) :
    Match (Cx.make tabs f g) env frA (keptFacts (Cx.make tabs f g) S w u)
      (upd fr d ((Cx.make tabs f g).md.retype ((Cx.make tabs f g).fty d) r0))
      (putRes (Cx.make tabs f g).lc s w r0) := by
  obtain ⟨hop, haux, hai, hty, hsz⟩ := sameOp_spec hsame
  have hgf : (Cx.make tabs f g).gty d = (Cx.make tabs f g).fty d := gty_eq_fty hlow hu hw hty
  have hval : (LMode.loc (Cx.make tabs f g).lc.ctx.f).retype ((Cx.make tabs f g).lc.ty w.id) r0 =
      (Cx.make tabs f g).md.retype ((Cx.make tabs f g).fty d) r0 := by
    rw [loc_md hlow, hwd]; exact congrArg (fun t => (Cx.make tabs f g).md.retype t r0) hgf
  -- the source value
  generalize hy : (Cx.make tabs f g).md.retype ((Cx.make tabs f g).fty d) r0 = y
  have hev : evalValueL (Cx.make tabs f g).md env (Cx.make tabs f g).sc fr u = .ok y := by
    rw [evalValueL_eq hargv, hud]
    show (evalOpL true env _ fr u argv ((Cx.make tabs f g).fty d)).bind _ = _
    rw [hr0, ← hy]; rfl
  have hlt : d < fr.regs.size := by rw [h.fsize]; exact value?_lt hu
  have hhome : (Cx.make tabs f g).lc.home w.id = (Cx.make tabs f g).lc.home d := by rw [hwd]
  have hlty : (Cx.make tabs f g).lc.ty w.id = (Cx.make tabs f g).gty d := by rw [hwd]; rfl
  have hnd' : writesNodup ((Cx.make tabs f g).lc.home w.id) ((Cx.make tabs f g).lc.ty w.id) = true := by
    rw [hhome, hlty]; exact hnd
  -- a written location holds the component of `y`
  have hW : ∀ l j, (l, j) ∈ writeLocs ((Cx.make tabs f g).lc.home w.id) ((Cx.make tabs f g).gty w.id) →
      (putRes (Cx.make tabs f g).lc s w r0).at l = comp j y := by
    intro l j hl
    rw [putRes_at_write h.regs hnd' hl, hval, hy]
  -- a source value with `y`
  have hsrcd : srcVal (Cx.make tabs f g) env frA (upd fr d y) d = some y := by
    unfold srcVal
    split
    · rename_i hk; rw [eval_kval h hk hu hev]
    · rw [upd_self' hlt]; rfl
  -- the equations
  have hEq : ∀ v ∈ pureEqs (Cx.make tabs f g) S u ++ selEqs (Cx.make tabs f g) S w u,
      srcVal (Cx.make tabs f g) env frA (upd fr d y) v = some y := by
    intro v hv
    have hold : ∀ y0, (fr.regs[v]?).join = some y0 → v ≠ d → y0 = y →
        srcVal (Cx.make tabs f g) env frA (upd fr d y) v = some y := by
      intro y0 hy0 hne he
      subst he
      unfold srcVal
      split
      · rename_i hk; rw [h.kinv v y0 hk hy0]
      · rw [upd_ne hne]; exact hy0
    rcases List.mem_append.1 hv with hv | hv
    · obtain ⟨hp, ⟨o, hoS, hov⟩, hne, xv, hxv, hsc⟩ := pureEqs_spec hv
      obtain ⟨v', y0, hv', hvid, hreg, hev0⟩ := factOK_avail.1 (h.facts _ hoS)
      rw [hov] at hv' hvid hreg
      rw [show (Cx.make tabs f g).f = f from rfl] at hxv hv'
      rw [hxv] at hv'; cases hv'
      obtain ⟨xop, xaux, xai, xty, xargs⟩ := sameConst_spec hsc
      refine hold y0 hreg (hud ▸ hne) ?_
      rw [evalValueL_eq (xargs ▸ hargv), evalOpL_pure (xop ▸ hp), hvid] at hev0
      rw [evalOpL_pure hp] at hr0
      cases hr0
      simp only [Res.bind_ok] at hev0
      cases hev0
      rw [← hy, show ((Cx.make tabs f g).sc.tys[v]?.getD Ty.other) = (Cx.make tabs f g).fty v from rfl,
        fty_eq (g := g) hxv hu xty, xop, xaux, xai]
    · obtain ⟨i, a, l, x, xv, hi, ha, hl, haS, ⟨o, hoS, hov⟩, hne, hxv, hxa, xop, xaux, xai, xty,
        hxne, hxS⟩ := selEqs_spec hv
      obtain ⟨v', y0, hv', hvid, hreg, hev0⟩ := factOK_avail.1 (h.facts _ hoS)
      rw [hov] at hv' hvid hreg
      rw [show (Cx.make tabs f g).f = f from rfl] at hxv hv'
      rw [hxv] at hv'; cases hv'
      refine hold y0 hreg (hud ▸ hne) ?_
      -- `v`'s value: component `i` of `x`'s
      obtain ⟨argx, hargx⟩ := evalValueL_regsAre (fun msg h' => by rw [hev0] at h'; cases h')
      rw [hxa] at hargx
      obtain ⟨X, rfl⟩ : ∃ X, argx = [X] := by
        match argx, hargx with
        | [X], _ => exact ⟨X, rfl⟩
      have hselx : selIndex xv = some i := by unfold selIndex; rw [xop, xai]; exact hi
      rw [evalValueL_eq (hxa ▸ hargx), evalOpL_sel hselx, hvid] at hev0
      simp only [Res.bind_ok] at hev0
      cases hev0
      -- `u`'s value: component `i` of `a`'s
      rw [ha] at hargv
      obtain ⟨A, rfl⟩ : ∃ A, argv = [A] := by
        match argv, hargv with
        | [A], _ => exact ⟨A, rfl⟩
      rw [evalOpL_sel hi] at hr0
      cases hr0
      -- both are at `l`
      have h1 := (factOK_loc hl).1 (h.facts _ hxS) X (srcVal_of_reg h hargx.1)
      have h2 := (factOK_loc hl).1 (h.facts _ haS) A (srcVal_of_reg h hargv.1)
      simp only [Bool.false_eq_true, ite_false] at h1 h2
      rw [← hy, show ((Cx.make tabs f g).sc.tys[v]?.getD Ty.other) = (Cx.make tabs f g).fty v from rfl,
        fty_eq (g := g) hxv hu xty]
      simp only [selRes]
      rw [← h1, h2]
  refine { facts := ?_, fr_eq := upd_fr_eq h.fr_eq d y,
           s_fr := by rw [putRes_fr]; exact h.s_fr, shaped := ?_, kinv := ?_,
           regs := putRes_regs h.regs w r0, fsize := by rw [upd_size]; exact h.fsize }
  · -- the facts that survive the write
    have hK : ∀ F ∈ killAll (Cx.make tabs f g) ((Cx.make tabs f g).lc.home w.id)
        ((Cx.make tabs f g).gty w.id)
        ((Cx.make tabs f g).redefine (clobberFacts (Cx.make tabs f g) S w) d),
        FactOK (Cx.make tabs f g) env frA (upd fr d y) (putRes (Cx.make tabs f g).lc s w r0) F := by
      intro F hF
      obtain ⟨hF1, hcl⟩ := mem_killAll hF
      have hF2 := (mem_redefine hF1).1
      refine factOK_keep h hu hud hev (redefine_mono (fun F hF => (at_clobber hF s).1) hF1) ?_
      intro _
      unfold putRes
      rw [at_write_other (regsOK_clobber h.regs w) (fun l hl => by rw [lc_tabs]; exact hcl l hl)]
      exact (at_clobber hF2 s).2
    intro F hF
    unfold keptFacts at hF
    simp only [List.mem_append] at hF
    rcases hF with (hF | hF) | hF
    · -- an equation
      rw [List.mem_flatMap] at hF
      obtain ⟨⟨l, j⟩, hl, hF⟩ := hF
      rw [List.mem_map] at hF
      obtain ⟨v, hv, rfl⟩ := hF
      refine (factOK_loc (writeLocs_ne hl)).2 fun x hx => ?_
      rw [hEq v hv] at hx; cases hx
      exact hW l j hl
    · -- `u` is available
      split at hF
      · rename_i hav
        simp only [List.mem_singleton] at hF
        subst hF
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hav
        simp only [exactF, hud]
        refine factOK_avail.2 ⟨u, y, hu, hud, by rw [upd_self' hlt]; rfl, ?_⟩
        rw [← hev]
        symm
        apply evalValueL_congr rfl
        intro a ha
        have hne : a ≠ d := by
          intro he; subst he
          have := hav.2
          rw [hud] at this
          simp [ha] at this
        exact (upd_ne hne).symm
      · simp at hF
    · split at hF
      · -- a `MakeResult` written where its arguments are
        rename_i hmr
        obtain ⟨hmrop, ts, hts, hlen, hall⟩ := mrOK_spec hmr
        unfold mrFacts at hF
        rcases List.mem_append.1 hF with hF | hF
        · rw [List.mem_flatMap] at hF
          obtain ⟨⟨l, j⟩, hl, hF⟩ := hF
          obtain ⟨j, rfl, hlj⟩ := hall l j hl
          simp only [Option.bind_some] at hF
          cases ha : u.args[j]? with
          | none => rw [ha] at hF; simp at hF
          | some a =>
            rw [ha] at hF
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
            unfold mrSame at hlj
            rw [ha] at hlj
            split at hlj
            · rename_i a' a2 ha' ha2
              cases ha2
              simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hlj
              obtain ⟨⟨⟨⟨hne, -⟩, -⟩, hsh⟩, -⟩ := hlj
              rw [evalOpL_makeResult hmrop] at hr0
              cases hr0
              have hj : j < ts.length := writeLocs_tuple_lt (hts ▸ hl)
              obtain ⟨A, hA, hAr⟩ := regsAre_get hargv (by simpa using ha)
              have hlenv : ts.length ≤ argv.length := by
                rw [regsAre_length hargv]; simpa using hlen
              have hsh' : shapeEq ts[j] ((Cx.make tabs f g).fty a) = true := by
                simpa [List.getD_eq_getElem?_getD, hj] using hsh
              have hAt : (putRes (Cx.make tabs f g).lc s w (.tuple argv)).at l = A := by
                rw [hW l (some j) hl, ← hy, ← hgf, ← hwd, hts, comp_retype_tuple _ hlenv hj,
                  List.getD_eq_getElem?_getD, hA, Option.getD_some,
                  retype_shapeEq _ hsh', h.shaped a A hAr]
              rcases hF with rfl | rfl
              · refine (factOK_loc (writeLocs_ne hl)).2 fun x hx => ?_
                simp only [exactF, hud] at hx
                rw [hsrcd] at hx; cases hx
                exact hW l (some j) hl
              · refine (factOK_loc (writeLocs_ne hl)).2 fun x hx => ?_
                have hsv : srcVal (Cx.make tabs f g) env frA (upd fr d y)
                    ((Cx.make tabs f g).canon a) =
                    srcVal (Cx.make tabs f g) env frA fr ((Cx.make tabs f g).canon a) := by
                  unfold srcVal
                  split
                  · rfl
                  · rename_i hkc
                    have hca : (Cx.make tabs f g).canon a = a := by
                      rcases canon_cases (Cx.make tabs f g) a with hc | ⟨-, hk, -⟩
                      · exact hc
                      · exact absurd hk hkc
                    rw [hca, upd_ne (hud ▸ hne)]
                rw [hsv, (srcVal_canon (srcVal_of_reg h hAr)).1] at hx
                cases hx
                exact hAt
            · simp at hlj
        · rw [hud] at hF; exact hK F hF
      · -- the result written at its home
        unfold writeFacts at hF
        rcases List.mem_append.1 hF with hF | hF
        · rw [List.mem_map] at hF
          obtain ⟨⟨l, j⟩, hl, rfl⟩ := hF
          refine (factOK_loc (writeLocs_ne hl)).2 fun x hx => ?_
          simp only [exactF, hud] at hx
          rw [written_ok h hu hud hev] at hx; cases hx
          exact hW l j hl
        · rw [hud] at hF; exact hK F hF
  · intro id x hx
    by_cases hid : id = d
    · subst hid
      rw [upd_self' hlt] at hx
      cases hx
      rw [← hy, LMode.retype_idem]
    · rw [upd_ne hid] at hx; exact h.shaped id x hx
  · intro id x hk hx
    by_cases hid : id = d
    · subst hid
      rw [upd_self' hlt] at hx
      cases hx
      exact eval_kval h hk hu hev
    · rw [upd_ne hid] at hx; exact h.kinv id x hk hx

theorem regsAre_srcVal {env : Env} {frA : Frame} {S : Facts} {fr : Frame} {s : LocState}
    (h : Match (Cx.make tabs f g) env frA S fr s) :
    ∀ {l : List ID} {L : List Val}, RegsAre (fun a => (fr.regs[a]?).join) l L →
      RegsAre (srcVal (Cx.make tabs f g) env frA fr) l L
  | [], [], _ => trivial
  | _ :: _, _ :: _, hr => ⟨srcVal_of_reg h hr.1, regsAre_srcVal h hr.2⟩
  | [], _ :: _, hr | _ :: _, [], hr => by simp [RegsAre] at hr

theorem keptChecks_spec {cx : Cx} {S : Facts} {w u : Value} (h : keptChecks cx S w u = .ok ()) :
    u.op ≠ .LoadReg ∧ u.op ≠ .StoreReg ∧ w.args.size = u.args.size ∧
      argsOKL cx S w.args.toList u.args.toList (selIndex u) = .ok () ∧ signOK cx w u = true ∧
      shapeEq (cx.gty w.id) (cx.fty u.id) = true := by
  unfold keptChecks at h
  split at h
  · cases h
  · rename_i hm
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hm
    split at h
    · cases h
    · rename_i hargs
      unfold argsOK at hargs
      split at hargs
      · cases hargs
      · rename_i hsz
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hsz
        split at h
        · cases h
        · rename_i hs
          split at h
          · cases h
          · rename_i hsh
            exact ⟨hm.1, hm.2, hsz, hargs, by simpa using hs, by simpa using hsh⟩

theorem selRes_rel {i : Nat} : ∀ {xs' xs : List Val}, ArgsRel (some i) xs' xs →
    selRes i xs' = selRes i xs
  | [x'], [x], h => by simpa [selRes, ArgsRel, ArgRel] using h.1
  | [], [], _ => rfl
  | _ :: _ :: _, _ :: _ :: _, _ => rfl
  | [], _ :: _, h | _ :: _, [], h => by simp [ArgsRel] at h
  | [_], _ :: _ :: _, h => by simp [ArgsRel] at h
  | _ :: _ :: _, [_], h => by simp [ArgsRel] at h

theorem selIndex_none_of_op {v : Value} (h1 : v.op ≠ .Select0) (h2 : v.op ≠ .Select1)
    (h3 : v.op ≠ .SelectN) : selIndex v = none := by
  unfold selIndex; split <;> simp_all

/-- A kept value's target step is its source op's result, written at its home. -/
theorem kept_step {env : Env} {frA : Frame} {S : Facts} {fr : Frame} {s : LocState}
    (h : Match (Cx.make tabs f g) env frA S fr s) (hlow : f.lowered = g.lowered)
    (hown : f.ownAux = g.ownAux)
    {d : ID} {u w : Value} (hu : f.value? d = some u) (hw : g.value? d = some w)
    (hud : u.id = d) (hwd : w.id = d) (hsame : sameOp u w = true) (hphi : w.op ≠ .Phi)
    (hchk : keptChecks (Cx.make tabs f g) S w u = .ok ())
    {argv : List Val} (hargv : RegsAre (fun a => (fr.regs[a]?).join) u.args.toList argv) :
    stepLoc env (Cx.make tabs f g).lc s w =
      (evalOpL true env (Cx.make tabs f g).sc fr u argv ((Cx.make tabs f g).fty d)).bind
        fun r => .ok (putRes (Cx.make tabs f g).lc s w r) := by
  obtain ⟨hop, haux, hai, hty, hsz⟩ := sameOp_spec hsame
  obtain ⟨hnl, hns, hsz', hargs, hsign, -⟩ := keptChecks_spec hchk
  have hgf : (Cx.make tabs f g).gty d = (Cx.make tabs f g).fty d := gty_eq_fty hlow hu hw hty
  have hlty : (Cx.make tabs f g).lc.ty w.id = (Cx.make tabs f g).fty d := by
    rw [hwd]; exact hgf
  obtain ⟨argv', hargv', hrel⟩ := argsOKL_read h hlow hargs (by simpa using hsz')
    (regsAre_srcVal h hargv)
  by_cases hm : w.op = .ARM64MOVDreg ∨ w.op = .ARM64MOVDnop
  · have hsel : selIndex u = none := by
      apply selIndex_none_of_op <;> rcases hm with hm | hm <;> rw [hop, hm] <;> decide
    rw [hsel] at hrel
    have he := ArgsRel.eq_of_none hrel
    subst he
    rw [stepLoc_movd hm hargv', evalOpL_movd (hop ▸ hm), Res.bind_ok, movdLoc_eq, hlty]
    congr 3
    unfold signOK at hsign
    rw [if_pos (by rcases hm with hm | hm <;> simp [hm])] at hsign
    have := (beq_iff_eq.1 hsign)
    rw [lc_f, sc_f]
    exact this.symm
  · have hm1 : w.op ≠ .ARM64MOVDreg := fun h' => hm (.inl h')
    have hm2 : w.op ≠ .ARM64MOVDnop := fun h' => hm (.inr h')
    rw [stepLoc_op hphi (hop ▸ hnl) (hop ▸ hns) hm1 hm2 hargv', hlty]
    congr 1
    cases hsel : selIndex u with
    | some i =>
      rw [hsel] at hrel
      have hsw : selIndex w = some i := by unfold selIndex at hsel ⊢; rw [← hop, ← hai]; exact hsel
      rw [evalOpL_sel hsw, evalOpL_sel hsel, selRes_rel hrel]
    | none =>
      rw [hsel] at hrel
      have he := ArgsRel.eq_of_none hrel
      subst he
      rw [h.s_fr, h.fr_eq, evalOpL_frame, evalOpL_frame]
      exact evalOpL_congr_sx hop.symm haux.symm hai.symm (hwd.trans hud.symm)
        (lc_tabs.trans sc_tabs.symm) (params_eq hown) act_eq
        (fun hm' => absurd (hop ▸ hm') hm)

end GoFV.Proof.RA

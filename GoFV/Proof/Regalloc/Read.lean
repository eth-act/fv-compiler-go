import GoFV.Proof.Regalloc.Facts

variable [GoFV.SSA.Sem.Addrs]

/-!
# Regalloc checker soundness, stage 3: reads

A target argument checked by `argOK` reads, from its home, the source argument's register
(`argOK_read`); a selector's argument, read as a tuple, has the source's component
(`ArgRel`). `argsOKL_read`: a kept value's target arguments read its source arguments.
-/

namespace GoFV.Proof.RA

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RegallocCheck

variable {tabs : Tables} {f g : Func}

/-! ## Tuples -/

theorem comp_retypePre_get : ∀ (ts : List Ty) (vs vs' : List Val), Val.retypePre ts vs = some vs' →
    ∀ i (hi : i < ts.length), vs'.getD i .poison = Val.retype ts[i] (vs.getD i .poison)
  | [], _, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | t :: ts, [], _, h, _, _ => by simp [Val.retypePre] at h
  | t :: ts, v :: vs, vs', h, i, hi => by
    simp only [Val.retypePre, Option.map_eq_some_iff] at h
    obtain ⟨ws, hws, rfl⟩ := h
    cases i with
    | zero => rfl
    | succ i =>
      simp only [List.getD_cons_succ, List.getElem_cons_succ]
      exact comp_retypePre_get ts vs ws hws i (by simpa using hi)

theorem retypePre_some : ∀ (ts : List Ty) (vs : List Val), ts.length ≤ vs.length →
    ∃ vs', Val.retypePre ts vs = some vs'
  | [], vs, _ => ⟨vs, rfl⟩
  | t :: ts, [], h => absurd h (by simp)
  | t :: ts, v :: vs, h => by
    obtain ⟨ws, hws⟩ := retypePre_some ts vs (by simpa using h)
    exact ⟨Val.retype t v :: ws, by simp [Val.retypePre, hws]⟩

theorem widenList_getD : ∀ (ts : List Ty) (vs : List Val) i, i < ts.length →
    (Val.widenList ts vs).getD i .poison = (vs.getD i .poison).widen ts[i]!
  | [], _, i, hi => absurd hi (Nat.not_lt_zero _)
  | t :: ts, [], i, _ => by
    cases i <;> simp [Val.widenList, Val.widen]
  | t :: ts, v :: vs, i, hi => by
    cases i with
    | zero => simp [Val.widenList]
    | succ i =>
      simp only [Val.widenList, List.getD_cons_succ]
      rw [widenList_getD ts vs i (by simpa using hi)]
      simp

theorem widenList_length : ∀ (ts : List Ty) (vs : List Val),
    (Val.widenList ts vs).length = vs.length
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: ts, _ :: vs => by simp [Val.widenList, widenList_length ts vs]

/-- Component `i` of a tuple read at a tuple shape is the component read at its shape. -/
theorem comp_retype_tuple (md : LMode) {ts : List Ty} {xs : List Val}
    (hlen : ts.length ≤ xs.length) {i : Nat} (hi : i < ts.length) :
    comp (some i) (md.retype (.tuple ts) (.tuple xs)) = md.retype ts[i] (xs.getD i .poison) := by
  unfold LMode.retype
  split
  · simp only [Val.retypeL, Val.widen]
    obtain ⟨ws, hws⟩ := retypePre_some ts (Val.widenList ts xs)
      (by rw [widenList_length]; exact hlen)
    simp only [Val.retype, hws, comp]
    rw [comp_retypePre_get ts _ ws hws i hi, widenList_getD ts xs i hi]
    simp [hi]
  · obtain ⟨ws, hws⟩ := retypePre_some ts xs hlen
    simp only [Val.retype, hws, comp]
    exact comp_retypePre_get ts xs ws hws i hi

theorem retype_poison (md : LMode) (t : Ty) : md.retype t .poison = .poison := by
  unfold LMode.retype Val.retypeL
  split
  · cases t <;> rfl
  · cases t <;> rfl

theorem retypePre_none : ∀ (ts : List Ty) (vs : List Val), vs.length < ts.length →
    Val.retypePre ts vs = none
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, [], _ => rfl
  | _ :: ts, _ :: vs, h => by
    simp [Val.retypePre, retypePre_none ts vs (by simpa using h)]

/-- A tuple shape makes a short tuple `poison`. -/
theorem retype_tuple_short (md : LMode) {ts : List Ty} {xs : List Val}
    (h : xs.length < ts.length) : md.retype (.tuple ts) (.tuple xs) = .poison := by
  unfold LMode.retype
  split
  · simp only [Val.retypeL, Val.widen, Val.retype]
    rw [retypePre_none ts _ (by rw [widenList_length]; exact h)]
  · simp only [Val.retype]
    rw [retypePre_none ts _ h]

/-- A tuple shape makes every other value `poison`. -/
theorem retype_tuple_other (md : LMode) (ts : List Ty) {y : Val} (hy : ∀ xs, y ≠ .tuple xs) :
    md.retype (.tuple ts) y = .poison := by
  unfold LMode.retype
  cases y with
  | tuple xs => exact absurd rfl (hy xs)
  | _ => split <;> rfl

/-- Component `i` of a value shaped at a tuple shape has the component's shape. -/
theorem comp_shaped (md : LMode) {ts : List Ty} {y : Val} (hy : md.retype (.tuple ts) y = y)
    {i : Nat} (hi : i < ts.length) :
    md.retype ts[i] (comp (some i) y) = comp (some i) y := by
  rw [← hy]
  by_cases ht : ∃ xs, y = .tuple xs
  · obtain ⟨xs, rfl⟩ := ht
    by_cases hlen : ts.length ≤ xs.length
    · rw [comp_retype_tuple md hlen hi, LMode.retype_idem]
    · rw [retype_tuple_short md (by omega)]
      simp only [comp, retype_poison]
  · rw [retype_tuple_other md ts (fun xs h => ht ⟨xs, h⟩)]
    simp only [comp, retype_poison]

/-! ## Reads -/

/-- `xs` are the registers `r` gives the IDs `as`. -/
def RegsAre (r : ID → Option Val) : List ID → List Val → Prop
  | [], [] => True
  | a :: as, x :: xs => r a = some x ∧ RegsAre r as xs
  | _, _ => False

/-- How a target argument's read relates to the source argument: equal, or (a selector's
argument) equal in the selected component. -/
def ArgRel : Option Nat → Val → Val → Prop
  | none, x', x => x' = x
  | some i, x', x => comp (some i) x' = comp (some i) x

def ArgsRel : Option Nat → List Val → List Val → Prop
  | sel, x' :: xs', x :: xs => ArgRel sel x' x ∧ ArgsRel none xs' xs
  | _, [], [] => True
  | _, _, _ => False

theorem ArgRel.of_eq {sel : Option Nat} {x' x : Val} (h : x' = x) : ArgRel sel x' x := by
  cases sel <;> simp [ArgRel, h]

theorem ArgsRel.eq_of_none : ∀ {xs' xs : List Val}, ArgsRel none xs' xs → xs' = xs
  | [], [], _ => rfl
  | x' :: xs', x :: xs, h => by
    simp only [ArgsRel, ArgRel] at h
    rw [h.1, ArgsRel.eq_of_none h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [ArgsRel] at h

theorem read_eq {lc : LocCtx} {s : LocState} {a : ID} {x : Val} (h : s.raw lc a = .ok x) :
    s.read lc a = .ok ((LMode.loc lc.ctx.f).retype (lc.ty a) x) := by
  simp only [LocState.read, h]; rfl

theorem regLoc_ne {r : Nat} {l : Loc} (h : regLoc r = some l) : l ≠ .avail := by
  unfold regLoc at h
  split at h
  · cases h
  · cases h; nofun

theorem compLocs_ne : ∀ {ts : List Ty} {rs : List (Option Nat)} {j : Nat} {l : Loc} {k : Nat},
    (l, k) ∈ compLocs ts rs j → l ≠ .avail
  | [], _, _, _, _, h => by simp [compLocs] at h
  | t :: ts, rs, j, l, k, h => by
    unfold compLocs at h
    split at h
    · simp only [List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, -⟩ | h
      · nofun
      · exact compLocs_ne h
    · split at h
      · simp only [List.mem_cons, Prod.mk.injEq] at h
        rcases h with ⟨rfl, -⟩ | h
        · nofun
        · exact compLocs_ne h
      · split at h
        · simp only [List.mem_append, List.mem_map] at h
          rcases h with ⟨l', hl', he⟩ | h
          · simp only [Prod.mk.injEq] at he
            obtain ⟨rfl, -⟩ := he
            exact regLoc_ne (by simpa using hl')
          · exact compLocs_ne h
        · exact compLocs_ne h
        · exact compLocs_ne h

theorem readLoc_loc_ne {h : Option Location} {t : Ty} {l : Loc}
    (hr : readLoc h t = some (.loc l)) : l ≠ .avail := by
  unfold readLoc at hr
  split at hr
  · cases hr; nofun
  · cases hr
  · split at hr
    · cases hr
    · split at hr
      · cases hr; rename_i hl; exact regLoc_ne hl
      · cases hr
  · cases hr
  · cases hr
  · cases hr; nofun
  · split at hr
    · cases hr; nofun
    · cases hr

theorem readLoc_tuple_ne {h : Option Location} {t : Ty} {ls : List (Loc × Nat)}
    (hr : readLoc h t = some (.tuple ls)) {l : Loc} {j : Nat} (hl : (l, j) ∈ ls) : l ≠ .avail := by
  unfold readLoc at hr
  split at hr
  · cases hr
  · cases hr; exact compLocs_ne hl
  · split at hr
    · cases hr
    · split at hr <;> cases hr
  · cases hr
  · cases hr; exact compLocs_ne hl
  · cases hr
  · split at hr <;> cases hr

theorem res_zero_shapeEq {t t' : Ty} (h : shapeEq t t' = true) : Arm64.res t 0 = Arm64.res t' 0 := by
  by_cases hb : t = .bool
  · subst hb
    have : t' = .bool := by
      unfold shapeEq at h
      simp only [isWord, Bool.false_and, Bool.false_or] at h
      exact (Ty.eq_of_beq h).symm
    rw [this]
  · have hb' : t' ≠ .bool := by
      intro h'; subst h'
      unfold shapeEq at h
      simp only [isWord, Bool.and_false, Bool.false_or] at h
      exact hb (Ty.eq_of_beq h)
    unfold Arm64.res
    split
    · exact absurd rfl hb
    · rfl

/-- `argOK`: the target argument `a'` reads the source argument `a`'s register (its component
`i` for a selector's tuple argument). -/
theorem argOK_read {env : Env} {frA : Frame} {S : Facts} {fr : Frame} {s : LocState}
    (h : Match (Cx.make tabs f g) env frA S fr s) (hlow : f.lowered = g.lowered)
    {a' a : ID} {sel : Option Nat} (hok : argOK (Cx.make tabs f g) S a' a sel = .ok ())
    {x : Val} (hx : srcVal (Cx.make tabs f g) env frA fr a = some x) :
    ∃ x', s.read (Cx.make tabs f g).lc a' = .ok x' ∧ ArgRel sel x' x := by
  have hmd := loc_md (tabs := tabs) hlow
  unfold argOK at hok
  split at hok
  · cases hok
  · cases hok
  · -- `ZERO`
    rename_i hr
    split at hok
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      obtain ⟨hz, hsh⟩ := hc
      refine ⟨_, read_eq (raw_zero hr), ArgRel.of_eq ?_⟩
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
        unfold srcVal at hx
        rw [if_pos hk] at hx
        cases hx
        rw [kval_eq _ env frA hv hkv, hargs]
        have hkr : ∀ ty, kRes (Cx.make tabs f g).sc v [] ty = Arm64.res ty 0 := by
          intro ty
          rcases hop with hop | ⟨hop, hai⟩
          · simp only [kRes, hop]; rfl
          · simp only [kRes, hop]
            show Arm64.res ty (Arm64.imm v.auxInt) = _
            rw [hai]; rfl
        simp only [Array.toList_empty, List.map_nil, hkr]
        rw [hmd]
        unfold LMode.retype
        simp only [hmdl, ite_true]
        rw [Val.retypeL_idem]
        have := retype_shapeEq (Cx.make tabs f g).md hsh (Arm64.res ((Cx.make tabs f g).gty a') 0)
        unfold LMode.retype at this
        simp only [hmdl, ite_true] at this
        rw [show (Cx.make tabs f g).lc.ty a' = (Cx.make tabs f g).gty a' from rfl, this,
          res_zero_shapeEq hsh]
      · cases hz
    · cases hok
  · -- a location
    rename_i l hr
    split at hok
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      obtain ⟨hS, hsh⟩ := hc
      refine ⟨_, read_eq (raw_loc hr), ArgRel.of_eq ?_⟩
      rw [hmd, show (Cx.make tabs f g).lc.ty a' = (Cx.make tabs f g).gty a' from rfl,
        retype_shapeEq _ hsh]
      exact holds_read h (readLoc_loc_ne hr) hS hx
    · cases hok
  · -- a tuple
    rename_i ls hr
    cases sel with
    | none => cases hok
    | some i =>
      have hsh : shapeEq ((Cx.make tabs f g).gty a') ((Cx.make tabs f g).fty a) = true := by
        cases hc : shapeEq ((Cx.make tabs f g).gty a') ((Cx.make tabs f g).fty a) with
        | false => simp [hc] at hok
        | true => rfl
      simp only [hsh, Bool.not_true, Bool.false_eq_true, ite_false] at hok
      cases hfind : ls.find? (·.2 == i) with
      | none => simp [hfind] at hok
      | some p =>
        obtain ⟨l, j⟩ := p
        have hS : S.holds l a (some i) = true := by
          cases hc : S.holds l a (some i) with
          | false => simp [hfind, hc] at hok
          | true => rfl
        clear hok
        obtain ⟨ts, xs, hty, hraw, hlen, hat⟩ := raw_tuple (s := s) hr
        have hmem := List.mem_of_find?_eq_some hfind
        have hji : j = i := by simpa using List.find?_some hfind
        subst hji
        have hxj := hat l j hmem
        have hj : j < ts.length := by
          rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hxj).1
        have hty' : (Cx.make tabs f g).gty a' = .tuple ts := hty
        have hfty : (Cx.make tabs f g).fty a = .tuple ts := by
          unfold shapeEq at hsh
          rw [hty'] at hsh
          simp only [isWord, Bool.false_and, Bool.false_or] at hsh
          exact (Ty.eq_of_beq hsh).symm
        refine ⟨_, read_eq hraw, ?_⟩
        show comp (some j) _ = comp (some j) x
        rw [hmd, hty, comp_retype_tuple _ (by omega) hj]
        have hxs : xs.getD j .poison = s.at l := by
          rw [List.getD_eq_getElem?_getD, hxj]; rfl
        rw [hxs]
        have hsv := hx
        have hshx : (Cx.make tabs f g).md.retype (.tuple ts) x = x := by
          rw [← hfty]; exact srcVal_shaped h hx
        rcases holds_iff.1 hS with hF | hF
        · have := (factOK_loc (readLoc_tuple_ne hr hmem)).1 (h.facts _ hF) x hsv
          simp only [Bool.false_eq_true, ite_false] at this
          rw [this]
          exact comp_shaped _ hshx hj
        · have := (factOK_loc (readLoc_tuple_ne hr hmem)).1 (h.facts _ hF) x hsv
          simp only [ite_true, Cx.origTy, hfty] at this
          rw [← this]
          simp [hj]

theorem argsOKL_read {env : Env} {frA : Frame} {S : Facts} {fr : Frame} {s : LocState}
    (h : Match (Cx.make tabs f g) env frA S fr s) (hlow : f.lowered = g.lowered) :
    ∀ {as' as : List ID} {sel : Option Nat} {argv : List Val},
      argsOKL (Cx.make tabs f g) S as' as sel = .ok () → as'.length = as.length →
      RegsAre (srcVal (Cx.make tabs f g) env frA fr) as argv →
      ∃ argv', as'.mapM (s.read (Cx.make tabs f g).lc) = .ok argv' ∧ ArgsRel sel argv' argv
  | [], [], _, [], _, _, _ => ⟨[], rfl, trivial⟩
  | a' :: as', a :: as, sel, x :: xs, hok, hlen, hf => by
    simp only [argsOKL] at hok
    cases h1 : argOK (Cx.make tabs f g) S a' a sel with
    | error e => rw [h1] at hok; cases hok
    | ok u =>
      rw [h1] at hok
      cases u
      obtain ⟨x', hx', hr⟩ := argOK_read h hlow h1 hf.1
      obtain ⟨xs', hxs', hrs⟩ := argsOKL_read h hlow hok (by simpa using hlen)
        hf.2
      refine ⟨x' :: xs', ?_, hr, hrs⟩
      rw [List.mapM_cons, hx', hxs']
      rfl
  | [], _ :: _, _, _, _, hlen, _ | _ :: _, [], _, _, _, hlen, _ => by simp at hlen
  | _, [], _, _ :: _, _, _, hf | _, _ :: _, _, [], _, _, hf => by simp [RegsAre] at hf

/-- The source's argument registers. -/
theorem mapM_ofOption_forall₂ {m : ID → String} {r : ID → Option Val} :
    ∀ {l : List ID} {L : List Val}, l.mapM (fun a => Res.ofOption (m a) (r a)) = .ok L →
      RegsAre r l L
  | [], L, h => by cases h; trivial
  | a :: l, L, h => by
    rw [List.mapM_cons] at h
    cases ha : r a with
    | none => rw [ha] at h; cases h
    | some z =>
      rw [ha] at h
      cases hl : l.mapM (fun a => Res.ofOption (m a) (r a)) with
      | ok L' =>
        rw [hl] at h
        cases h
        exact ⟨ha, mapM_ofOption_forall₂ hl⟩
      | panic e mm => rw [hl] at h; cases h
      | stuck msg => rw [hl] at h; cases h

end GoFV.Proof.RA

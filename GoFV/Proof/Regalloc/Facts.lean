import GoFV.Proof.Regalloc.Ops

/-!
# Regalloc checker soundness: the contexts, frame constants and facts

The two contexts of `Cx.make tabs f g` (`runSched`'s of `f`, `runLoc`'s of `g`) agree on what
`evalOpL` reads besides the function (`params_eq`, `act_eq`, …) when `f` and `g` have one
signature; their shapes are the values' types' (`fty_of_value`, `gty_of_value`). Frame constants
with one op, aux, auxint, type and arguments have one value (`kval_canon`). A fact about a
value's representative read at the value's shape gives the source register (`holds_read`).
-/

namespace GoFV.Proof.RA

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RegallocCheck

variable {tabs : Tables} {f g : Func}

/-! ## The contexts -/

theorem sc_tabs : (Cx.make tabs f g).sc.tabs = tabs := tabs_makeL tabs f
theorem lc_tabs : (Cx.make tabs f g).lc.ctx.tabs = tabs := tabs_makeL tabs g
theorem sc_f : (Cx.make tabs f g).sc.f = f := makeL_f tabs f
theorem lc_f : (Cx.make tabs f g).lc.ctx.f = g := makeL_f tabs g
theorem cx_tabs : (Cx.make tabs f g).tabs = tabs := rfl
theorem cx_f : (Cx.make tabs f g).f = f := rfl
theorem cx_g : (Cx.make tabs f g).g = g := rfl

theorem params_eq (hown : f.ownAux = g.ownAux) :
    (Cx.make tabs f g).lc.ctx.params = (Cx.make tabs f g).sc.params := by
  show (Ctx.makeL tabs g).params = (Ctx.makeL tabs f).params
  rw [params_makeL, params_makeL]
  unfold Ctx.make abiParams
  simp only [hown]

theorem act_eq : (Cx.make tabs f g).lc.ctx.act = (Cx.make tabs f g).sc.act := by
  show (Ctx.makeL tabs g).act = (Ctx.makeL tabs f).act
  rw [act_makeL, act_makeL]; rfl

theorem loc_md (hlow : f.lowered = g.lowered) :
    LMode.loc (Cx.make tabs f g).lc.ctx.f = (Cx.make tabs f g).md := by
  show LMode.sched (Ctx.makeL tabs g).f = LMode.sched f
  rw [makeL_f]
  simp only [LMode.sched, hlow]

theorem fty_of_value {x : ID} {v : Value} (h : f.value? x = some v) :
    (Cx.make tabs f g).fty x = (shapesL f.lowered tabs)[v.type]?.getD .other := by
  show ((Ctx.makeL tabs f).tys[x]?).getD .other = _
  rw [tysL_of_value h]; rfl

theorem gty_of_value {x : ID} {w : Value} (h : g.value? x = some w) :
    (Cx.make tabs f g).gty x = (shapesL g.lowered tabs)[w.type]?.getD .other := by
  show ((Ctx.makeL tabs g).tys[x]?).getD .other = _
  rw [tysL_of_value h]; rfl

/-- A kept value has one shape in the source and the target. -/
theorem gty_eq_fty (hlow : f.lowered = g.lowered) {x : ID} {u w : Value}
    (hu : f.value? x = some u) (hw : g.value? x = some w) (ht : u.type = w.type) :
    (Cx.make tabs f g).gty x = (Cx.make tabs f g).fty x := by
  rw [gty_of_value hw, fty_of_value hu, hlow, ht]

/-- Source values of one type have one shape. -/
theorem fty_eq {x y : ID} {u v : Value} (hu : f.value? x = some u) (hv : f.value? y = some v)
    (ht : u.type = v.type) : (Cx.make tabs f g).fty x = (Cx.make tabs f g).fty y := by
  rw [fty_of_value hu, fty_of_value hv, ht]

/-! ## Facts as membership -/

theorem holds_iff {S : Facts} {l : Loc} {id : ID} {c : Option Nat} :
    S.holds l id c = true ↔ (l, ⟨id, c, false⟩) ∈ S ∨ (l, ⟨id, c, true⟩) ∈ S := by
  simp [Facts.holds]

theorem holdsExact_iff {S : Facts} {l : Loc} {id : ID} :
    S.holdsExact l id = true ↔ (l, ⟨id, none, false⟩) ∈ S := by
  simp [Facts.holdsExact]

theorem sameConst_spec {x v : Value} (h : sameConst x v = true) :
    x.op = v.op ∧ x.aux = v.aux ∧ x.auxInt = v.auxInt ∧ x.type = v.type ∧ x.args = v.args := by
  simp only [sameConst, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem sameOp_spec {u w : Value} (h : sameOp u w = true) :
    u.op = w.op ∧ u.aux = w.aux ∧ u.auxInt = w.auxInt ∧ u.type = w.type ∧
      u.args.size = w.args.size := by
  simp only [sameOp, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem isK_spec {cx : Cx} {id : ID} (h : cx.isK id = true) :
    ∃ v, cx.f.value? id = some v ∧ v.id = id ∧ isKVal cx.f v = true := by
  unfold Cx.isK at h
  split at h
  · rename_i v hv; simp only [Bool.and_eq_true, beq_iff_eq] at h; exact ⟨v, hv, h.1, h.2⟩
  · cases h

theorem isKVal_spec {F : Func} {v : Value} (h : isKVal F v = true) :
    kOp v.op = true ∧ ∀ a ∈ v.args, ∃ u, F.value? a = some u ∧ u.id = a ∧
      (u.op = .SP ∨ u.op = .SB) ∧ u.args = #[] := by
  unfold isKVal at h
  simp only [Bool.and_eq_true, Array.all_eq_true_iff_forall_mem] at h
  refine ⟨h.1, fun a ha => ?_⟩
  have := h.2 a ha
  split at this
  · rename_i u hu
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Array.isEmpty_iff] at this
    exact ⟨u, hu, this.1.1, this.1.2, this.2⟩
  · cases this

/-- `canon` keeps a value, or names a frame constant with the same op, aux, auxint, type and
arguments. -/
theorem canon_cases (cx : Cx) (a : ID) :
    cx.canon a = a ∨ (cx.isK a = true ∧ cx.isK (cx.canon a) = true ∧
      ∃ v x, cx.f.value? a = some v ∧ cx.f.value? (cx.canon a) = some x ∧ sameConst x v = true) := by
  unfold Cx.canon
  split
  · rename_i r _
    split
    · rename_i v x hv hx
      split
      · rename_i hc
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
        exact .inr ⟨hc.1.1.2, hc.1.2, v, x, hv, hx, hc.2⟩
      · exact .inl rfl
    · exact .inl rfl
  · exact .inl rfl

/-! ## Frame constants -/

theorem kvalN_succ (cx : Cx) (env : Env) (frA : Frame) (n : Nat) {id : ID} {v : Value}
    (hv : cx.f.value? id = some v) :
    kvalN cx env frA (n + 1) id =
      match evalOpL true env cx.sc frA v (v.args.toList.map (kvalN cx env frA n)) (cx.fty id) with
      | .ok r => cx.md.retype (cx.fty id) r
      | _ => .poison := by
  conv => lhs; unfold kvalN
  rw [hv]
  rfl

/-- An argument of a frame constant (`SP`/`SB`, no arguments) has one value at every depth. -/
theorem kvalN_noargs (cx : Cx) (env : Env) (frA : Frame) {a : ID} {u : Value}
    (hu : cx.f.value? a = some u) (hargs : u.args = #[]) (n m : Nat) :
    kvalN cx env frA (n + 1) a = kvalN cx env frA (m + 1) a := by
  rw [kvalN_succ cx env frA n hu, kvalN_succ cx env frA m hu, hargs]
  rfl

/-- The value of a frame constant is its op evaluated on its arguments' values. -/
theorem kval_eq (cx : Cx) (env : Env) (frA : Frame) {id : ID} {v : Value}
    (hv : cx.f.value? id = some v) (hk : isKVal cx.f v = true) :
    kval cx env frA id = cx.md.retype (cx.fty id)
      (kRes cx.sc v (v.args.toList.map (kval cx env frA)) (cx.fty id)) := by
  have hk' := isKVal_spec hk
  unfold kval
  rw [kvalN_succ cx env frA 1 hv, evalOpL_kop_eq hk'.1]
  dsimp only
  congr 2
  apply List.map_congr_left
  intro a ha
  obtain ⟨u, hu, -, -, hargs⟩ := hk'.2 a (Array.mem_toList_iff.1 ha)
  exact kvalN_noargs cx env frA hu hargs 0 1

/-- Frame constants with one op, aux, auxint, type and arguments have one value and shape. -/
theorem kval_same {env : Env} {frA : Frame} {a b : ID} {v x : Value}
    (hv : f.value? a = some v) (hx : f.value? b = some x)
    (hkv : isKVal f v = true) (hc : sameConst x v = true) :
    kval (Cx.make tabs f g) env frA b = kval (Cx.make tabs f g) env frA a ∧
      (Cx.make tabs f g).fty b = (Cx.make tabs f g).fty a := by
  obtain ⟨hop, haux, hai, hty, hargs⟩ := sameConst_spec hc
  have hfty : (Cx.make tabs f g).fty b = (Cx.make tabs f g).fty a := fty_eq (tabs := tabs) (g := g) hx hv hty
  have hkx : isKVal f x = true := by
    unfold isKVal at hkv ⊢; rw [hop, hargs]; exact hkv
  refine ⟨?_, hfty⟩
  rw [kval_eq (Cx.make tabs f g) env frA hx hkx, kval_eq (Cx.make tabs f g) env frA hv hkv, hfty, hargs,
    kRes_congr hop haux hai rfl rfl]

/-- A value and its representative have one value and shape (`srcVal` of a frame constant). -/
theorem kval_canon {env : Env} {frA : Frame} {a : ID} (hk : (Cx.make tabs f g).isK a = true) :
    kval (Cx.make tabs f g) env frA ((Cx.make tabs f g).canon a) = kval (Cx.make tabs f g) env frA a ∧
      (Cx.make tabs f g).fty ((Cx.make tabs f g).canon a) = (Cx.make tabs f g).fty a := by
  rcases canon_cases (Cx.make tabs f g) a with h | ⟨-, -, v, x, hv, hx, hc⟩
  · rw [h]; exact ⟨rfl, rfl⟩
  · obtain ⟨v', hv', -, hkv⟩ := isK_spec hk
    rw [hv'] at hv; cases hv
    exact kval_same hv' hx hkv hc

/-! ## The relation -/

theorem factOK_loc {cx : Cx} {env : Env} {frA fr : Frame} {s : LocState} {l : Loc} {o : Orig}
    (hl : l ≠ .avail) :
    FactOK cx env frA fr s (l, o) ↔ ∀ x, srcVal cx env frA fr o.id = some x →
      if o.weak then cx.md.retype (cx.origTy o) (s.at l) = comp o.comp x
      else s.at l = comp o.comp x := by
  cases l <;> first | exact absurd rfl hl | exact Iff.rfl

theorem factOK_avail {cx : Cx} {env : Env} {frA fr : Frame} {s : LocState} {o : Orig} :
    FactOK cx env frA fr s (.avail, o) ↔ ∃ v y, cx.f.value? o.id = some v ∧ v.id = o.id ∧
      (fr.regs[o.id]?).join = some y ∧ evalValueL cx.md env cx.sc fr v = .ok y := Iff.rfl

theorem Match.mono {cx : Cx} {env : Env} {frA fr : Frame} {s : LocState} {S T : Facts}
    (h : Match cx env frA S fr s) (hT : ∀ F ∈ T, F ∈ S) : Match cx env frA T fr s :=
  { h with facts := fun F hF => h.facts F (hT F hF) }

/-- A defined source register is the source value (`kval` for a frame constant). -/
theorem srcVal_of_reg {cx : Cx} {env : Env} {frA : Frame} {S : Facts} {fr : Frame}
    {s : LocState} (h : Match cx env frA S fr s) {a : ID} {x : Val}
    (hx : (fr.regs[a]?).join = some x) : srcVal cx env frA fr a = some x := by
  unfold srcVal
  split
  · rename_i hk; rw [h.kinv a x hk hx]
  · exact hx

/-- A frame constant's value has its shape. -/
theorem kval_shaped (cx : Cx) (env : Env) (frA : Frame) (a : ID) :
    cx.md.retype (cx.fty a) (kval cx env frA a) = kval cx env frA a := by
  unfold kval kvalN
  split
  · split
    · exact LMode.retype_idem _ _ _
    · cases cx.md; unfold LMode.retype Val.retypeL; split <;> cases cx.fty a <;> rfl
  · cases cx.md; unfold LMode.retype Val.retypeL; split <;> cases cx.fty a <;> rfl

/-- A source value has its shape. -/
theorem srcVal_shaped {cx : Cx} {env : Env} {frA : Frame} {S : Facts} {fr : Frame}
    {s : LocState} (h : Match cx env frA S fr s) {a : ID} {x : Val}
    (hx : srcVal cx env frA fr a = some x) : cx.md.retype (cx.fty a) x = x := by
  unfold srcVal at hx
  split at hx
  · cases hx; exact kval_shaped cx env frA a
  · exact h.shaped a x hx

/-- The source value of a value's representative is the value's. -/
theorem srcVal_canon {env : Env} {frA : Frame} {fr : Frame} {a : ID} {x : Val}
    (hx : srcVal (Cx.make tabs f g) env frA fr a = some x) :
    srcVal (Cx.make tabs f g) env frA fr ((Cx.make tabs f g).canon a) = some x ∧
      (Cx.make tabs f g).fty ((Cx.make tabs f g).canon a) = (Cx.make tabs f g).fty a := by
  rcases canon_cases (Cx.make tabs f g) a with hc | ⟨hk, hkc, -⟩
  · rw [hc]; exact ⟨hx, rfl⟩
  · obtain ⟨hkv, hfty⟩ := kval_canon (env := env) (frA := frA) hk
    refine ⟨?_, hfty⟩
    unfold srcVal at hx ⊢
    rw [if_pos hkc, hkv]
    rw [if_pos hk] at hx
    exact hx

/-- A location that holds a value's representative, read at the value's shape, is the value's
source value. -/
theorem holds_read {env : Env} {frA : Frame} {S : Facts} {fr : Frame} {s : LocState}
    (h : Match (Cx.make tabs f g) env frA S fr s) {l : Loc} (hl : l ≠ .avail) {a : ID} {x : Val}
    (hS : S.holds l ((Cx.make tabs f g).canon a) = true)
    (hx : srcVal (Cx.make tabs f g) env frA fr a = some x) :
    (Cx.make tabs f g).md.retype ((Cx.make tabs f g).fty a) (s.at l) = x := by
  obtain ⟨hsv, hfty⟩ := srcVal_canon hx
  have hsh := srcVal_shaped h hx
  rcases holds_iff.1 hS with hF | hF
  · have := (factOK_loc hl).1 (h.facts _ hF) x hsv
    simp only [Bool.false_eq_true, ite_false, comp] at this
    rw [this, hsh]
  · have := (factOK_loc hl).1 (h.facts _ hF) x hsv
    simp only [ite_true, comp, Cx.origTy] at this
    rw [← hfty]; exact this

end GoFV.Proof.RA

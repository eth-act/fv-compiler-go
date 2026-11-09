import GoFV.Proof.Pass.DSEMem

variable [GoFV.SSA.Sem.Addrs]

/-!
# dse's output relation

`DRel tabs f g P`, the declarative form of the checker `GoFV.Opt.DSE.drel` (`drel_sound`, with
`P` the checker's pending sets `pendOf`): `g` has `f`'s control-flow graph, blocks (kinds,
values, controls without pending ranges) and values, each kept (`sameV`) or an eliminated store
(`elimV`); every value's pending set follows from its arguments' (`pendStep`); every argument
with pending ranges is used as `usesOK` allows; every block's schedule in `g` lists `g`'s roots
in `f`'s order. The `*_spec` lemmas read the Bool conditions off.
-/

namespace GoFV.Proof.DSE

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.DSE

/-- The checker's pending sets. -/
def pendOf (tabs : Tables) (f g : Func) (x : ID) : List Iv := (pendArr tabs f g).getD x []

/-- The declarative output relation. -/
structure DRel (tabs : Tables) (f g : Func) (P : ID → List Iv) : Prop where
  cfg : DomCert.cfgView g = DomCert.cfgView f
  ownAux : g.ownAux = f.ownAux
  vsize : g.valueTab.size = f.valueTab.size
  block : ∀ bid ∈ f.blocks, ∀ fb, f.block? bid = some fb → ∃ gb, g.block? bid = some gb ∧
    gb.kind = fb.kind ∧ gb.values = fb.values ∧ gb.controls = fb.controls ∧
    ∀ c ∈ fb.controls, P c = []
  value : ∀ x fv, f.value? x = some fv → ∃ gv, g.value? x = some gv ∧
    (sameV fv gv = true ∨ elimV fv gv = true)
  pend : ∀ x, x < f.valueTab.size → pendStep tabs f g P x = some (P x)
  uses : ∀ x, x < f.valueTab.size → usesOK f P x = true
  sched : ∀ bid ∈ f.blocks, ∀ fb gb, f.block? bid = some fb → g.block? bid = some gb →
    ∀ oS, Sem.schedule f fb = some oS → ∃ oT, Sem.schedule g gb = some oT ∧
      oT.toList.filter (CSE.rootNode g) = oS.toList.filter (CSE.rootNode g)

theorem lt_of_value? {f : Func} {x : ID} {v : Value} (h : f.value? x = some v) :
    x < f.valueTab.size := by
  unfold Func.value? at h
  rcases Nat.lt_or_ge x f.valueTab.size with hx | hx
  · exact hx
  · rw [Array.getElem?_eq_none hx] at h; cases h

/-- **The checker is sound.** -/
theorem drel_sound {tabs : Tables} {f g : Func} (h : drel tabs f g = true) :
    DRel tabs f g (pendOf tabs f g) := by
  unfold drel at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', List.all_eq_true,
    List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hcfg, hown⟩, hsz⟩, hblk⟩, hval⟩, hsch⟩ := h
  refine ⟨hcfg, hown, hsz, fun bid hb fb hfb => ?_, fun x fv hfv => ?_,
    fun x hx => (hval x hx).1.2, fun x hx => (hval x hx).2,
    fun bid hb fb gb hfb hgb oS hoS => ?_⟩
  · have := hblk bid hb
    unfold blockOK at this
    rw [hfb] at this
    cases hgb : g.block? bid with
    | none => rw [hgb] at this; cases this
    | some gb =>
      rw [hgb] at this
      simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', List.isEmpty_iff] at this
      obtain ⟨⟨⟨hk, hv⟩, hc⟩, hcs⟩ := this
      exact ⟨gb, rfl, hk, hv, hc, hcs⟩
  · have := (hval x (lt_of_value? hfv)).1.1
    unfold valueOK at this
    rw [hfv] at this
    cases hgv : g.value? x with
    | none => rw [hgv] at this; cases this
    | some gv =>
      rw [hgv] at this
      simp only [Bool.or_eq_true] at this
      exact ⟨gv, rfl, this⟩
  · have := hsch bid hb
    unfold schedOK at this
    rw [hfb, hgb] at this
    simp only [hoS] at this
    cases hoT : Sem.schedule g gb with
    | none => rw [hoT] at this; cases this
    | some oT =>
      rw [hoT] at this
      simp only [beq_iff_eq] at this
      exact ⟨oT, rfl, this⟩

/-! ## Reading the conditions -/

theorem elimV_spec {fv gv : Value} (h : elimV fv gv = true) :
    (fv.op = .Store ∨ fv.op = .Zero ∨ fv.op = .Move) ∧ gv.op = .Copy ∧ gv.aux = none ∧
      gv.auxInt = 0 ∧ gv.id = fv.id ∧ gv.type = fv.type ∧ gv.block = fv.block ∧
      ∃ m, fv.args.back? = some m ∧ gv.args = #[m] := by
  unfold elimV elimOp at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hop, hc⟩, hax⟩, hai⟩, hid⟩, hty⟩, hbl⟩, hargs⟩ := h
  refine ⟨by rcases hop with (h | h) | h <;> simp [h], hc, hax, hai, hid, hty, hbl, ?_⟩
  revert hargs
  cases fv.args.back? with
  | none => intro h; cases h
  | some m => intro h; exact ⟨m, rfl, by simpa using h⟩

theorem sameV_spec {fv gv : Value} (h : sameV fv gv = true) :
    gv.id = fv.id ∧ gv.op = fv.op ∧ gv.aux = fv.aux ∧ gv.auxInt = fv.auxInt ∧
      gv.type = fv.type ∧ gv.block = fv.block ∧ gv.args = fv.args := by
  unfold sameV at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem elimV_false_of_sameV {fv gv : Value} (h : sameV fv gv = true) (hc : fv.op ≠ .Copy) :
    elimV fv gv = false := by
  cases he : elimV fv gv with
  | false => rfl
  | true =>
    obtain ⟨-, hgc, -⟩ := elimV_spec he
    exact absurd ((sameV_spec h).2.1.symm.trans hgc) hc

/-- The pending set of a value's memory argument (its last). -/
def pm (P : ID → List Iv) (fv : Value) : List Iv :=
  match fv.args.back? with
  | some m => P m
  | none => []

theorem pendStep_eq {tabs : Tables} {f g : Func} {P : ID → List Iv} {x : ID} {fv gv : Value}
    (hfv : f.value? x = some fv) (hgv : g.value? x = some gv) :
    pendStep tabs f g P x =
      if elimV fv gv then
        (range? tabs f fv).map fun iv => if iv.2.1 < iv.2.2 then pm P fv ++ [iv] else pm P fv
      else if fv.op == .Store || fv.op == .Zero then
        some (match range? tabs f fv with
          | some r => (pm P fv).flatMap (sub r)
          | none => pm P fv)
      else if fv.op == .Move then
        if (pm P fv).isEmpty then some []
        else
          match fv.args[1]? with
          | some s =>
            match ptrAlloc tabs f s with
            | some a =>
              if (pm P fv).all (·.1 != a) then
                some (match range? tabs f fv with
                  | some r => (pm P fv).flatMap (sub r)
                  | none => pm P fv)
              else none
            | none => none
          | none => none
      else if fv.op == .VarDef then
        some (match fv.aux with
          | some n => (pm P fv).filter (·.1 != CSE.frameAlloc tabs n)
          | none => pm P fv)
      else some [] := by
  unfold pendStep
  rw [hfv, hgv]
  rfl

/-- An eliminated store's pending set: its memory argument's and its range. -/
theorem pend_elim {tabs : Tables} {f g : Func} {P : ID → List Iv} {x : ID} {fv gv : Value}
    (hfv : f.value? x = some fv) (hgv : g.value? x = some gv) (he : elimV fv gv = true)
    (h : pendStep tabs f g P x = some (P x)) :
    ∃ iv, range? tabs f fv = some iv ∧
      P x = if iv.2.1 < iv.2.2 then pm P fv ++ [iv] else pm P fv := by
  rw [pendStep_eq hfv hgv] at h
  simp only [he, ↓reduceIte] at h
  cases hr : range? tabs f fv with
  | none => rw [hr] at h; cases h
  | some iv => rw [hr] at h; exact ⟨iv, rfl, (Option.some.inj h).symm⟩

/-- A kept `Store`/`Zero`: its memory argument's pending set without its range. -/
theorem pend_store {tabs : Tables} {f g : Func} {P : ID → List Iv} {x : ID} {fv gv : Value}
    (hfv : f.value? x = some fv) (hgv : g.value? x = some gv) (he : elimV fv gv = false)
    (hop : fv.op = .Store ∨ fv.op = .Zero) (h : pendStep tabs f g P x = some (P x)) :
    P x = match range? tabs f fv with
      | some r => (pm P fv).flatMap (sub r)
      | none => pm P fv := by
  rw [pendStep_eq hfv hgv, he] at h
  have hc : (fv.op == .Store || fv.op == .Zero) = true := by
    rcases hop with hop | hop <;> simp [hop]
  simp only [Bool.false_eq_true, ite_false, hc, ite_true] at h
  exact (Option.some.inj h).symm

/-- A kept `Move` after pending ranges: it reads an allocation with none. -/
theorem pend_move {tabs : Tables} {f g : Func} {P : ID → List Iv} {x : ID} {fv gv : Value}
    (hfv : f.value? x = some fv) (hgv : g.value? x = some gv) (he : elimV fv gv = false)
    (hop : fv.op = .Move) (hne : pm P fv ≠ []) (h : pendStep tabs f g P x = some (P x)) :
    ∃ s a, fv.args[1]? = some s ∧ ptrAlloc tabs f s = some a ∧ (pm P fv).all (·.1 != a) ∧
      P x = match range? tabs f fv with
        | some r => (pm P fv).flatMap (sub r)
        | none => pm P fv := by
  rw [pendStep_eq hfv hgv, he] at h
  have hne' : (pm P fv).isEmpty = false := by
    cases hp : pm P fv with
    | nil => exact absurd hp hne
    | cons _ _ => rfl
  simp only [hop, Bool.false_eq_true, ite_false, hne'] at h
  have h1 : (Op.Move == Op.Store || Op.Move == Op.Zero) = false := rfl
  have h2 : (Op.Move == Op.Move) = true := rfl
  simp only [h1, h2, Bool.false_eq_true, ↓reduceIte] at h
  cases hs : fv.args[1]? with
  | none => rw [hs] at h; cases h
  | some s =>
    rw [hs] at h
    simp only at h
    cases ha : ptrAlloc tabs f s with
    | none => rw [ha] at h; cases h
    | some a =>
      rw [ha] at h
      simp only at h
      by_cases hall : (pm P fv).all (·.1 != a) = true
      · simp only [hall, ↓reduceIte] at h
        exact ⟨s, a, rfl, ha, hall, (Option.some.inj h).symm⟩
      · simp only [hall, Bool.false_eq_true, ↓reduceIte] at h; cases h

/-- A kept `Move` with no pending ranges before it has none. -/
theorem pend_move_nil {tabs : Tables} {f g : Func} {P : ID → List Iv} {x : ID} {fv gv : Value}
    (hfv : f.value? x = some fv) (hgv : g.value? x = some gv) (he : elimV fv gv = false)
    (hop : fv.op = .Move) (hnil : pm P fv = []) (h : pendStep tabs f g P x = some (P x)) :
    P x = [] := by
  rw [pendStep_eq hfv hgv, he, hop, hnil] at h
  exact (Option.some.inj h).symm

/-- A kept `VarDef`: its memory argument's pending set without its variable. -/
theorem pend_varDef {tabs : Tables} {f g : Func} {P : ID → List Iv} {x : ID} {fv gv : Value}
    (hfv : f.value? x = some fv) (hgv : g.value? x = some gv) (he : elimV fv gv = false)
    (hop : fv.op = .VarDef) (h : pendStep tabs f g P x = some (P x)) :
    P x = match fv.aux with
      | some n => (pm P fv).filter (·.1 != CSE.frameAlloc tabs n)
      | none => pm P fv := by
  rw [pendStep_eq hfv hgv, he, hop] at h
  exact (Option.some.inj h).symm

/-- Any other kept value has no pending ranges. -/
theorem pend_other {tabs : Tables} {f g : Func} {P : ID → List Iv} {x : ID} {fv gv : Value}
    (hfv : f.value? x = some fv) (hgv : g.value? x = some gv) (he : elimV fv gv = false)
    (hop : chainOp fv.op = false) (h : pendStep tabs f g P x = some (P x)) : P x = [] := by
  rw [pendStep_eq hfv hgv, he] at h
  unfold chainOp at hop
  simp only [Bool.or_eq_false_iff] at hop
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hop
  simp only [h1, h2, h3, h4, Bool.false_eq_true, Bool.or_self, ite_false] at h
  exact (Option.some.inj h).symm

/-- A value with no table entry has no pending ranges. -/
theorem pend_none {tabs : Tables} {f g : Func} {P : ID → List Iv} {x : ID}
    (hfv : f.value? x = none) (h : pendStep tabs f g P x = some (P x)) : P x = [] := by
  unfold pendStep at h
  rw [hfv] at h
  exact (Option.some.inj h).symm

/-- What `usesOK` allows of an argument with pending ranges. -/
theorem uses_spec {f : Func} {P : ID → List Iv} {x : ID} {fv : Value} (hfv : f.value? x = some fv)
    (h : usesOK f P x = true) {a : ID} (ha : a ∈ fv.args) (hp : P a ≠ []) :
    fv.op ≠ .Phi ∧ (f.value? a).map (·.block) = some fv.block ∧
      (blindOp fv.op = true ∨
        (chainOp fv.op = true ∧ fv.args.back? = some a ∧ a ∉ fv.args.pop)) := by
  unfold usesOK at h
  rw [hfv] at h
  simp only [Array.all_eq_true', Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq, Bool.not_eq_true', List.isEmpty_iff] at h
  rcases h a ha with h | ⟨⟨⟨hph, hb⟩, h⟩⟩
  · exact absurd h hp
  · refine ⟨hph, hb, ?_⟩
    rcases h with h | ⟨⟨h1, h2⟩, h3⟩
    · exact .inl h
    · refine .inr ⟨h1, h2, fun hm => ?_⟩
      simp [Array.contains_iff_mem, hm] at h3

end GoFV.Proof.DSE

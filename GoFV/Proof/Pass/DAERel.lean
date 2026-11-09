import GoFV.Proof.Pass.DAECall
import GoFV.Proof.Pass.DSERel

variable [GoFV.SSA.Sem.Addrs]

/-!
# dead auto elim's output relation

`ARelD tabs f g T E`, the declarative form of the checker `GoFV.Opt.DAE.arel` (`arel_sound`, with
`T` the checker's tags and `E` its eliminated names): `g` has `f`'s control-flow graph, blocks
(kinds, values, untainted controls) and values, each kept (`sameV`, with `opOK`) or an
eliminated write to a name of `E` (`elimV`); every eliminated name is a `Blk.temp`; tags follow
`tagStep`; tainted arguments are used only as `usesOK` allows; every block's schedule in `g`
lists `g`'s roots in `f`'s order. The `*_spec` lemmas read the Bool conditions off.
-/

namespace GoFV.Proof.DAE

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.DAE

/-- The checker's tags. -/
def tagOf (tabs : Tables) (f : Func) (x : ID) : Option AuxRef := (tagArr tabs f).getD x none

/-- The checker's eliminated names. -/
def namesOf (tabs : Tables) (f g : Func) : List AuxRef := names f g (tagOf tabs f)

/-- `x` is tainted: its tag is an eliminated name. -/
def Tainted (T : ID → Option AuxRef) (E : List AuxRef) (x : ID) : Prop := ∃ n, T x = some n ∧ n ∈ E

/-- The declarative output relation. -/
structure ARelD (tabs : Tables) (f g : Func) (T : ID → Option AuxRef) (E : List AuxRef) :
    Prop where
  cfg : DomCert.cfgView g = DomCert.cfgView f
  ownAux : g.ownAux = f.ownAux
  vsize : g.valueTab.size = f.valueTab.size
  temp : ∀ n ∈ E, tabs.forgeable n = false
  nodefer : ∀ n ∈ E, deferVar tabs n = false
  block : ∀ bid ∈ f.blocks, ∀ fb, f.block? bid = some fb → ∃ gb, g.block? bid = some gb ∧
    gb.kind = fb.kind ∧ gb.values = fb.values ∧ gb.controls = fb.controls ∧
    ∀ c ∈ fb.controls, ¬ Tainted T E c
  value : ∀ x fv, f.value? x = some fv → ∃ gv, g.value? x = some gv ∧
    ((DSE.sameV fv gv = true ∧ opOK tabs f fv = true) ∨
      (elimV fv gv = true ∧ ∃ n, nameOf T fv = some n ∧ n ∈ E))
  uses : ∀ x, x < f.valueTab.size → usesOK f g T E x = true
  tag : ∀ x fv, f.value? x = some fv → tagStep tabs T fv = T x
  sched : ∀ bid ∈ f.blocks, ∀ fb gb, f.block? bid = some fb → g.block? bid = some gb →
    ∀ oS, Sem.schedule f fb = some oS → ∃ oT, Sem.schedule g gb = some oT ∧
      oT.toList.filter (CSE.rootNode g) = oS.toList.filter (CSE.rootNode g)

theorem elimV_ne_same {fv gv : Value} (he : elimV fv gv = true) (hs : DSE.sameV fv gv = true) :
    False := by
  unfold elimV elimOp at he
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at he
  obtain ⟨⟨⟨⟨⟨⟨⟨hop, hc⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := he
  have := (DSE.sameV_spec hs).2.1
  rw [hc] at this
  rcases hop with ((h | h) | h) | h <;> rw [← this] at h <;> cases h

/-- **The checker is sound.** -/
theorem arel_sound {tabs : Tables} {f g : Func} (h : arel tabs f g = true) :
    ARelD tabs f g (tagOf tabs f) (namesOf tabs f g) := by
  unfold arel at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Array.all_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨hcfg, hown⟩, hsz⟩, hE⟩, hblk⟩, hval⟩, hsch⟩ := h
  refine ⟨hcfg, hown, hsz, fun n hn => ?_, fun n hn => ?_, fun bid hb fb hfb => ?_,
    fun x fv hfv => ?_, fun x hx => (hval x hx).1.1.2, fun x fv hfv => ?_,
    fun bid hb fb gb hfb hgb oS hoS => ?_⟩
  · have := hE n hn
    unfold unforgeable at this
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    exact this.1
  · have := hE n hn
    unfold unforgeable at this
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    exact this.2
  · have := hblk bid hb
    unfold blockOK at this
    rw [hfb] at this
    cases hgb : g.block? bid with
    | none => rw [hgb] at this; cases this
    | some gb =>
      rw [hgb] at this
      simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', Bool.not_eq_true',
        Option.any_eq_false] at this
      obtain ⟨⟨⟨hk, hv⟩, hc⟩, hcs⟩ := this
      refine ⟨gb, rfl, hk, hv, hc, fun c hc' ⟨n, hn, hnE⟩ => ?_⟩
      have := hcs c hc' n hn
      have h2 : (namesOf tabs f g).contains n = true := List.contains_iff_mem.2 hnE
      unfold namesOf tagOf at h2
      simp only [Array.getD_eq_getD_getElem?] at this h2
      rw [this] at h2; cases h2
  · have hx := DSE.lt_of_value? hfv
    have hv := (hval x hx).1.1.1
    have hk := (hval x hx).1.2
    unfold valueOK at hv
    unfold keptOK at hk
    rw [hfv] at hv hk
    cases hgv : g.value? x with
    | none => rw [hgv] at hv; cases hv
    | some gv =>
      rw [hgv] at hv hk
      simp only [Bool.or_eq_true, Bool.and_eq_true, Option.any_eq_true,
        List.contains_iff_mem] at hv hk
      refine ⟨gv, rfl, ?_⟩
      rcases hv with hs | ⟨he, n, hn, hnE⟩
      · rcases hk with he | hk
        · exact (elimV_ne_same he hs).elim
        · exact .inl ⟨hs, hk⟩
      · exact .inr ⟨he, n, hn, hnE⟩
  · have := (hval x (DSE.lt_of_value? hfv)).2
    rw [hfv] at this
    exact beq_iff_eq.1 this
  · have := hsch bid hb
    unfold DSE.schedOK at this
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
    (fv.op = .Store ∨ fv.op = .Zero ∨ fv.op = .Move ∨ fv.op = .VarDef) ∧ gv.op = .Copy ∧
      gv.aux = none ∧ gv.auxInt = 0 ∧ gv.id = fv.id ∧ gv.type = fv.type ∧ gv.block = fv.block ∧
      ∃ m, fv.args.back? = some m ∧ gv.args = #[m] := by
  unfold elimV elimOp at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hop, hc⟩, hax⟩, hai⟩, hid⟩, hty⟩, hbl⟩, hargs⟩ := h
  refine ⟨by rcases hop with ((h | h) | h) | h <;> simp [h], hc, hax, hai, hid, hty, hbl, ?_⟩
  revert hargs
  cases fv.args.back? with
  | none => intro h; cases h
  | some m => intro h; exact ⟨m, rfl, by simpa using h⟩

/-- What `usesOK` allows of a tainted argument. -/
theorem uses_spec {f g : Func} {T : ID → Option AuxRef} {E : List AuxRef} {x : ID} {fv : Value}
    (hfv : f.value? x = some fv) (h : usesOK f g T E x = true) {i : Nat} {a : ID}
    (ha : fv.args[i]? = some a) (ht : Tainted T E a) :
    (i = 0 ∧ propOp fv.op = true ∧ T x = T a) ∨
      (∃ gv, g.value? x = some gv ∧ elimV fv gv = true ∧
        ((i = 0 ∧ fv.op ≠ .VarDef) ∨ (i = 1 ∧ fv.op = .Move))) := by
  unfold usesOK at h
  rw [hfv] at h
  simp only [List.all_eq_true, List.mem_range] at h
  have hi : i < fv.args.size := by
    have := (Array.getElem?_eq_some_iff.1 ha).1; exact this
  have := h i hi
  rw [ha] at this
  obtain ⟨n, hn, hnE⟩ := ht
  have hc : E.contains n = true := List.contains_iff_mem.2 hnE
  simp only [hn, Option.any_some, hc, Bool.not_true,
    Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at this
  rcases this with ((⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩)
  · exact .inl ⟨h1, h2, h3.trans hn.symm⟩
  · cases hgv : g.value? x with
    | none => rw [hgv] at h1; cases h1
    | some gv => rw [hgv] at h1; exact .inr ⟨gv, rfl, h1, .inl ⟨h2, h3⟩⟩
  · cases hgv : g.value? x with
    | none => rw [hgv] at h1; cases h1
    | some gv => rw [hgv] at h1; exact .inr ⟨gv, rfl, h1, .inr ⟨h2, h3⟩⟩

theorem opOK_spec {tabs : Tables} {f : Func} {fv : Value} (h : opOK tabs f fv = true) :
    (fv.op = .Phi ∨ (∀ a ∈ fv.args, plainArg tabs f a = true) ∨
      (fv.op ∈ memOps ∧ ∀ a ∈ fv.args.pop, plainArg tabs f a = true)) ∧
    (fv.op ∈ ptrOps ∨ noPtrTy (tabs.ty fv.type) = true) := by
  unfold opOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Array.all_eq_true',
    List.contains_iff_mem] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, h2⟩
  rcases h1 with (h | h) | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr h)

end GoFV.Proof.DAE

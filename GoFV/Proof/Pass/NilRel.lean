import GoFV.Opt.NilCheckRel
import GoFV.Proof.WF
import GoFV.Proof.DomCert

/-!
# nilcheckelim's output relation

`NRel xt tabs f g`, the declarative form of the checker `GoFV.Opt.NilCheck.nrel` (`nrel_sound`):
`g` has `f`'s control-flow graph, block kinds, controls and values (each block's values
reordered, its `Phi`s in order); every value keeps its ID, block and type and is unchanged
(`VRel.same`), a `NilCheck p` turned `Copy nc` (`VRel.nc`) or an `IsNonNil p` turned
`ConstBool [1]` (`VRel.nn`), each justified (`Just`), or an `IsNonNil` of an `nnSeed` turned
`ConstBool [1]` (`VRel.nns`); and every block's schedule in `g` runs the
roots of `f`'s (by `g`'s ops) in `f`'s order.
-/

namespace GoFV.Proof.Nil

open GoFV.SSA GoFV.Opt GoFV.Opt.NilCheck

/-- Why `ptr` is non-nil at value `x` of block `bx`. -/
inductive Just (xt : Bool) (tabs : Tables) (f : Func) (bx x ptr nc : ID) (ty : TypeRef) : Bool → Prop where
  /-- `nc = ptr` and its op makes it point into an allocation. -/
  | seed : nc = ptr → safePtr xt tabs f f.valueTab.size ptr = true → Just xt tabs f bx x ptr nc ty true
  /-- `nc` is a nil check of `ptr` listed in a strict dominator of `bx`. -/
  | dom {s : Bool} {n : Value} {nb : Block} : nc ≠ ptr → f.value? nc = some n → n.op = .NilCheck →
      n.args[0]? = some ptr → n.type = ty → n.block ≠ bx →
      (DomCert.make f).anc n.block bx = true → n.block ∈ f.blocks → f.block? n.block = some nb →
      nc ∈ nb.values → Just xt tabs f bx x ptr nc ty s
  /-- `nc` is a nil check of `ptr` listed before `x` in `bx`'s schedule. -/
  | same {s : Bool} {n : Value} {fb : Block} {o : Array ID} : nc ≠ ptr → f.value? nc = some n →
      n.op = .NilCheck → n.args[0]? = some ptr → n.type = ty → n.block = bx →
      f.block? bx = some fb → nc ∈ fb.values → Sem.schedule f fb = some o →
      listedBefore o nc x = true → Just xt tabs f bx x ptr nc ty s

/-- The nil check `nc` (unchanged in `g`) checks `x`'s pointer with `x`'s memory and follows `x`
directly among the roots of its block's schedule. -/
inductive After (f g : Func) (fv : Value) (x nc : ID) : Prop where
  | mk {n gn : Value} {fb : Block} {o : Array ID} {i j : Nat} : f.value? nc = some n → nc ≠ x →
      n.op = .NilCheck → n.args = fv.args → n.type = fv.type → n.block = fv.block →
      g.value? nc = some gn → gn.op = .NilCheck → gn.args = n.args →
      f.block? fv.block = some fb → nc ∈ fb.values → Sem.schedule f fb = some o →
      o[i]? = some x → o[j]? = some nc → i < j →
      (∀ k y, i < k → k < j → o[k]? = some y → root f y = false) → After f g fv x nc

/-- How value `x` of `f` (`fv`) became `gv`. -/
inductive VRel (xt : Bool) (tabs : Tables) (f g : Func) (x : ID) : Value → Value → Prop where
  | same {fv gv : Value} : gv.op = fv.op → gv.args = fv.args → gv.aux = fv.aux →
      gv.auxInt = fv.auxInt → VRel xt tabs f g x fv gv
  | nc {fv gv : Value} {p nc : ID} : fv.op = .NilCheck → gv.op = .Copy → fv.args[0]? = some p →
      gv.args.size = 1 → gv.args[0]? = some nc → Just xt tabs f fv.block x p nc fv.type true → VRel xt tabs f g x fv gv
  | nn {fv gv : Value} {p nc : ID} : fv.op = .IsNonNil → gv.op = .ConstBool → gv.auxInt = 1 →
      gv.args.size = 0 → fv.args.size = 1 → fv.args[0]? = some p → nc ≠ p →
      Just xt tabs f fv.block x p nc (f.getV nc).type false → VRel xt tabs f g x fv gv
  | nns {fv gv : Value} {p : ID} : fv.op = .IsNonNil → gv.op = .ConstBool → gv.auxInt = 1 →
      gv.args.size = 0 → fv.args.size = 1 → fv.args[0]? = some p → nnSeed tabs f p = true →
      VRel xt tabs f g x fv gv
  | after {fv gv : Value} {nc : ID} : fv.op = .NilCheck → gv.op = .Copy → gv.args.size = 1 →
      gv.args[0]? = some nc → After f g fv x nc → VRel xt tabs f g x fv gv

/-- The declarative output relation. -/
structure NRel (xt : Bool) (tabs : Tables) (f g : Func) : Prop where
  cfg : DomCert.cfgView g = DomCert.cfgView f
  ownAux : g.ownAux = f.ownAux
  vsize : g.valueTab.size = f.valueTab.size
  block : ∀ bid ∈ f.blocks, ∀ fb, f.block? bid = some fb → ∃ gb, g.block? bid = some gb ∧
    gb.kind = fb.kind ∧ gb.controls = fb.controls ∧ gb.values.toList.Perm fb.values.toList ∧
    gb.values.filter (fun z => (g.getV z).op == .Phi) =
      fb.values.filter (fun z => (f.getV z).op == .Phi)
  value : ∀ x fv, f.value? x = some fv → ∃ gv, g.value? x = some gv ∧ gv.id = fv.id ∧
    gv.block = fv.block ∧ gv.type = fv.type ∧ VRel xt tabs f g x fv gv
  sched : ∀ bid ∈ f.blocks, ∀ fb gb, f.block? bid = some fb → g.block? bid = some gb →
    ∀ oS, Sem.schedule f fb = some oS → ∃ oT, Sem.schedule g gb = some oT ∧
      oT.toList.filter (root g) = oS.toList.filter (root g)

/-! ## Soundness of the checker -/

theorem lt_of_value? {f : Func} {x : ID} {v : Value} (h : f.value? x = some v) :
    x < f.valueTab.size := by
  unfold Func.value? at h
  rcases Nat.lt_or_ge x f.valueTab.size with hx | hx
  · exact hx
  · rw [Array.getElem?_eq_none hx] at h; cases h

theorem justified_sound {xt : Bool} {tabs : Tables} {f : Func} {bx x ptr nc : ID} {ty : TypeRef} {s : Bool}
    (h : justified xt tabs (DomCert.make f) f bx x ptr nc ty s = true) :
    Just xt tabs f bx x ptr nc ty s := by
  unfold justified at h
  by_cases hnp : nc = ptr
  · subst hnp
    simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true] at h
    rw [h.1]; exact .seed rfl h.2
  · have hb : (nc == ptr) = false := by simpa using hnp
    rw [hb] at h
    simp only [Bool.false_eq_true, ite_false] at h
    cases hn : f.value? nc with
    | none => rw [hn] at h; cases h
    | some n =>
    cases hfb : f.block? bx with
    | none => rw [hn, hfb] at h; cases h
    | some fb =>
    rw [hn, hfb] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hop, ha⟩, hty⟩, hrest⟩ := h
    by_cases hbl : n.block = bx
    · simp only [hbl, beq_self_eq_true, ite_true, Bool.and_eq_true, Array.contains_iff_mem] at hrest
      obtain ⟨hmem, hs⟩ := hrest
      cases ho : Sem.schedule f fb with
      | none => rw [ho] at hs; cases hs
      | some o =>
        rw [ho] at hs
        exact .same hnp hn hop ha hty hbl hfb hmem ho hs
    · simp only [hbl, ite_false, Bool.false_eq_true, Bool.and_eq_true,
        Array.contains_iff_mem] at hrest
      obtain ⟨⟨hanc, hblk⟩, hl⟩ := hrest
      cases hnb : f.block? n.block with
      | none => rw [hnb] at hl; cases hl
      | some nb =>
        rw [hnb] at hl
        exact .dom hnp hn hop ha hty hbl hanc hblk hnb (by simpa using hl)

theorem after_sound {f g : Func} {fv : Value} {x nc : ID} (h : after f g fv x nc = true) :
    After f g fv x nc := by
  unfold after at h
  cases hn : f.value? nc with
  | none => rw [hn] at h; cases h
  | some n =>
  cases hfb : f.block? fv.block with
  | none => rw [hn, hfb] at h; cases h
  | some fb =>
  cases hgn : g.value? nc with
  | none => rw [hn, hfb, hgn] at h; cases h
  | some gn =>
  rw [hn, hfb, hgn] at h
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Array.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hne, hop⟩, hargs⟩, hty⟩, hbl⟩, hgop⟩, hgargs⟩, hmem⟩, hrest⟩ := h
  cases ho : Sem.schedule f fb with
  | none => rw [ho] at hrest; cases hrest
  | some o =>
  rw [ho] at hrest
  dsimp only at hrest
  cases hi : o.findIdx? (· == x) with
  | none => rw [hi] at hrest; cases hrest
  | some i =>
  cases hj : o.findIdx? (· == nc) with
  | none => rw [hi, hj] at hrest; cases hrest
  | some j =>
  rw [hi, hj] at hrest
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at hrest
  obtain ⟨hij, hgap⟩ := hrest
  obtain ⟨hi1, hi2⟩ := Array.findIdx?_eq_some_iff_getElem.1 hi
  obtain ⟨hj1, hj2⟩ := Array.findIdx?_eq_some_iff_getElem.1 hj
  refine .mk hn (Ne.symm (fun h => hne h.symm)) hop hargs hty hbl hgn hgop hgargs hfb hmem ho
    (i := i) (j := j) (by rw [Array.getElem?_eq_getElem hi1]; simpa using hi2.1)
    (by rw [Array.getElem?_eq_getElem hj1]; simpa using hj2.1) hij ?_
  intro k y hik hkj hy
  have hk : k < o.size := (Array.getElem?_eq_some_iff.1 hy).1
  have hyk : o[k]! = y := by rw [getElem!_pos o k hk]; exact (Array.getElem?_eq_some_iff.1 hy).2
  rcases hgap k hk with (h1 | h1) | h1
  · omega
  · omega
  · rw [hyk] at h1; exact h1

/-- **The checker is sound.** -/
theorem nrel_sound {xt : Bool} {tabs : Tables} {f g : Func} (h : nrel xt tabs f g = true) : NRel xt tabs f g := by
  unfold nrel at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨hcfg, hown⟩, hsz⟩, hblk⟩, hval⟩, hsch⟩ := h
  refine ⟨hcfg, hown, hsz, fun bid hb fb hfb => ?_, fun x fv hfv => ?_,
    fun bid hb fb gb hfb hgb oS hoS => ?_⟩
  · have := hblk bid hb
    unfold blockOK at this
    rw [hfb] at this
    cases hgb : g.block? bid with
    | none => rw [hgb] at this; cases this
    | some gb =>
      rw [hgb] at this
      simp only [Bool.and_eq_true, beq_iff_eq, List.isPerm_iff] at this
      obtain ⟨⟨⟨hk, hc⟩, hp⟩, hphi⟩ := this
      exact ⟨gb, rfl, hk, hc, hp, hphi⟩
  · have := hval x (lt_of_value? hfv)
    unfold valueOK at this
    rw [hfv] at this
    cases hgv : g.value? x with
    | none => rw [hgv] at this; cases this
    | some gv =>
      rw [hgv] at this
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at this
      obtain ⟨⟨⟨hid, hbl⟩, hty⟩, hor⟩ := this
      refine ⟨gv, rfl, hid, hbl, hty, ?_⟩
      rcases hor with (⟨⟨⟨hop, hargs⟩, hax⟩, hai⟩ | ⟨⟨⟨hop, hcp⟩, hs1⟩, hj⟩) |
          ⟨⟨⟨⟨⟨hop, hcb⟩, hai⟩, he⟩, hs1⟩, hj⟩
      · exact .same hop hargs hax hai
      · cases hp : fv.args[0]? with
        | none => rw [hp] at hj; cases hj
        | some p =>
          cases hn : gv.args[0]? with
          | none => rw [hp, hn] at hj; cases hj
          | some nc =>
            rw [hp, hn] at hj
            simp only [Bool.or_eq_true] at hj
            rcases hj with hj | hj
            · exact .nc hop hcp hp hs1 hn (justified_sound hj)
            · exact .after hop hcp hs1 hn (after_sound hj)
      · cases hp : fv.args[0]? with
        | none => rw [hp] at hj; cases hj
        | some p =>
          rw [hp] at hj
          simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true,
            bne_iff_ne] at hj
          rcases hj with hns | ⟨nc, -, hne, hjs⟩
          · exact .nns hop hcb hai he hs1 hp hns
          · exact .nn hop hcb hai he hs1 hp hne (justified_sound hjs)
  · have := hsch bid hb
    unfold schedOK at this
    rw [hfb, hgb] at this
    simp only [hoS] at this
    cases hoT : Sem.schedule g gb with
    | none => rw [hoT] at this; cases this
    | some oT =>
      rw [hoT] at this
      simp only [beq_iff_eq] at this
      exact ⟨oT, rfl, by
        have := congrArg Array.toList this
        simpa [Array.toList_filter] using this⟩

end GoFV.Proof.Nil

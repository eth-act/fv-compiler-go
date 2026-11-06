import GoFV.Proof.Pass.SchedLEval
import GoFV.Proof.FrameL

/-!
# What `scheduleCheck` checks, as propositions

`SchedRel tabs f g` unpacks `scheduleCheck tabs f g = true` (`schedRel_of_check`): values and
blocks of `g` are `f`'s rewired by `rep` (`SchedRel.gval`, `SchedRel.fval`, `SchedRel.gblock`),
every bypassed use is `useOK` (`SchedRel.argUse`, `SchedRel.ctrlUse`), and each block's
`runSched` order lists `g`'s non-`Phi`s in a dependency order (`SchedRel.order`) keeping the
failing values in `runL`'s order up to `swapOK` (`SchedRel.swap`).
-/

namespace GoFV.Proof.SchedL

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.ScheduleCheck GoFV.Proof

/-- `scheduleCheck`'s conditions. -/
structure SchedRel (tabs : Tables) (f g : Func) : Prop where
  entry : g.entry = f.entry
  ownAux : g.ownAux = f.ownAux
  lowered : g.lowered = f.lowered
  vsize : g.valueTab.size = f.valueTab.size
  bsize : g.blockTab.size = f.blockTab.size
  value : ∀ id, valueOK f g id = true
  block : ∀ b, blockOK f g b = true
  uses : usesOK tabs f = true
  orders : ordersOK tabs f g = true

theorem value?_none_of_size {f : Func} {id : ID} (h : f.valueTab.size ≤ id) : f.value? id = none := by
  simp [Func.value?, Array.getElem?_eq_none h]

theorem block?_none_of_size {f : Func} {id : ID} (h : f.blockTab.size ≤ id) : f.block? id = none := by
  simp [Func.block?, Array.getElem?_eq_none h]

theorem schedRel_of_check {tabs : Tables} {f g : Func} (h : scheduleCheck tabs f g = true) :
    SchedRel tabs f g := by
  simp only [scheduleCheck, shapeOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨he, ho⟩, hl⟩, hv⟩, hb⟩, hval⟩, hblk⟩, hu⟩, hord⟩ := h
  refine ⟨he, ho, hl, hv, hb, fun id => ?_, fun b => ?_, hu, hord⟩
  · by_cases hid : id < f.valueTab.size
    · exact hval id hid
    · unfold valueOK
      rw [value?_none_of_size (f := f) (id := id) (Nat.le_of_not_lt hid),
        value?_none_of_size (f := g) (id := id) (by rw [hv]; exact Nat.le_of_not_lt hid)]
  · by_cases hid : b < f.blockTab.size
    · exact hblk b hid
    · unfold blockOK
      rw [block?_none_of_size (f := f) (id := b) (Nat.le_of_not_lt hid),
        block?_none_of_size (f := g) (id := b) (by rw [hb]; exact Nat.le_of_not_lt hid)]

/-- What `valueOK` says of a value of `g`. -/
structure VRel (f g : Func) (fv gv : Value) : Prop where
  notSPA : fv.op ≠ .SPanchored
  id : gv.id = fv.id
  op : gv.op = fv.op
  aux : gv.aux = fv.aux
  auxInt : gv.auxInt = fv.auxInt
  block : gv.block = fv.block
  args : gv.args = fv.args.map (rep f)
  type : fv.op.nilCheck = true ∨ gv.type = fv.type
  sx : ((gv.args[0]?.bind g.value?).map (Arm64.signExtendsIn g.value?)) =
    ((fv.args[0]?.bind f.value?).map (Arm64.signExtendsIn f.value?))

namespace SchedRel

variable {tabs : Tables} {f g : Func} (S : SchedRel tabs f g)
include S

theorem gval {x : ID} {gv : Value} (h : g.value? x = some gv) :
    ∃ fv, f.value? x = some fv ∧ VRel f g fv gv := by
  have := S.value x
  unfold valueOK at this
  rw [h] at this
  cases hf : f.value? x with
  | none => rw [hf] at this; cases this
  | some fv =>
    rw [hf] at this
    simp only [Bool.and_eq_true] at this
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := this
    simp only [bne_iff_ne, ne_eq, beq_iff_eq, Bool.or_eq_true] at h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact ⟨fv, rfl, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem fval {x : ID} {fv : Value} (h : f.value? x = some fv) (hs : fv.op ≠ .SPanchored) :
    ∃ gv, g.value? x = some gv ∧ VRel f g fv gv := by
  have := S.value x
  unfold valueOK at this
  rw [h] at this
  cases hg : g.value? x with
  | none => rw [hg] at this; simp at this; exact absurd this hs
  | some gv => obtain ⟨fv', h', hr⟩ := S.gval hg; rw [h] at h'; cases h'; exact ⟨gv, rfl, hr⟩

theorem fspa {x : ID} {fv : Value} (h : f.value? x = some fv) (hs : fv.op = .SPanchored) :
    g.value? x = none := by
  cases hg : g.value? x with
  | none => rfl
  | some gv =>
    obtain ⟨fv', h', hr⟩ := S.gval hg
    rw [h] at h'; cases h'; exact absurd hs hr.notSPA

/-- What `blockOK` says of a block of `f`. -/
theorem fblock {b : ID} {fb : Block} (h : f.block? b = some fb) :
    ∃ gb, g.block? b = some gb ∧ gb.id = fb.id ∧ gb.kind = fb.kind ∧ gb.auxInt = fb.auxInt ∧
      gb.succs = fb.succs ∧ gb.preds = fb.preds ∧ gb.controls = fb.controls.map (rep f) ∧
      gb.values.toList.Perm (fb.values.toList.filter (!isSPA f ·)) := by
  have := S.block b
  unfold blockOK at this
  rw [h] at this
  cases hg : g.block? b with
  | none => rw [hg] at this; cases this
  | some gb =>
    rw [hg] at this
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := this
    exact ⟨gb, rfl, h1, h2, h3, h4, h5, h6, List.isPerm_iff.1 h7⟩

theorem gblock {b : ID} {gb : Block} (h : g.block? b = some gb) : ∃ fb, f.block? b = some fb := by
  have := S.block b
  unfold blockOK at this
  rw [h] at this
  cases hf : f.block? b with
  | none => rw [hf] at this; cases this
  | some fb => exact ⟨fb, rfl⟩

/-- A use by a value. -/
theorem argUse {x : ID} {u : Value} (hu : f.value? x = some u) {k : Nat} {a : ID}
    (ha : u.args[k]? = some a) :
    useOK tabs (Ctx.makeL tabs f).tys f (some u) k a = true := by
  have := S.uses
  unfold usesOK at this
  simp only [Bool.and_eq_true, Array.all_eq_true] at this
  have hx : x < f.valueTab.size := by
    unfold Func.value? at hu
    cases hh : f.valueTab[x]? with
    | none => rw [hh] at hu; cases hu
    | some _ => exact (Array.getElem?_eq_some_iff.1 hh).1
  have h1 := this.1 x hx
  have heq : f.valueTab[x] = some u := by
    unfold Func.value? at hu; simp only [Array.getElem?_eq_getElem hx, Option.join_some] at hu
    exact hu
  rw [heq] at h1
  simp only [List.all_eq_true, List.mem_range] at h1
  have hk : k < u.args.size := (Array.getElem?_eq_some_iff.1 ha).1
  have := h1 k hk
  rw [getElem!_def, ha] at this
  exact this

/-- A use by a control. -/
theorem ctrlUse {b : ID} {fb : Block} (hb : f.block? b = some fb) {c : ID} (hc : c ∈ fb.controls) :
    useOK tabs (Ctx.makeL tabs f).tys f none 0 c = true := by
  have := S.uses
  unfold usesOK at this
  simp only [Bool.and_eq_true, Array.all_eq_true] at this
  have hx : b < f.blockTab.size := by
    unfold Func.block? at hb
    cases hh : f.blockTab[b]? with
    | none => rw [hh] at hb; cases hb
    | some _ => exact (Array.getElem?_eq_some_iff.1 hh).1
  have h1 := this.2 b hx
  have heq : f.blockTab[b] = some fb := by
    unfold Func.block? at hb; simp only [Array.getElem?_eq_getElem hx, Option.join_some] at hb
    exact hb
  rw [heq] at h1
  simp only [Array.all_eq_true] at h1
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hc
  exact h1 i hi

/-- The orders of a block: `runL`'s `oS`, `runSched`'s `oT` (`g`'s non-`Phi`s in a dependency
order), and `orderOK`. -/
theorem order {b : ID} {fb : Block} (hb : f.block? b = some fb) :
    ∃ oS oT gb, ((Ctx.makeL tabs f).sched[b]?).join = some oS ∧
      ((Ctx.makeSched tabs g).sched[b]?).join = some oT ∧ g.block? b = some gb ∧
      oT.toList = gb.values.toList.filter (!isPhi g ·) ∧ topoB g oT.toList = true ∧
      orderOK tabs (Ctx.makeL tabs f).params (Ctx.makeL tabs f).tys f f.valueTab.size oS oT =
        true := by
  have := S.orders
  unfold ordersOK at this
  simp only [List.all_eq_true, List.mem_range] at this
  have hx : b < f.blockTab.size := by
    unfold Func.block? at hb
    cases hh : f.blockTab[b]? with
    | none => rw [hh] at hb; cases hb
    | some _ => exact (Array.getElem?_eq_some_iff.1 hh).1
  have h1 := this b hx
  rw [hb] at h1
  simp only at h1
  split at h1
  · rename_i oS oT gb hS hT hG
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    exact ⟨oS, oT, gb, hS, hT, hG, h1.1.1, h1.1.2, h1.2⟩
  · cases h1

end SchedRel

/-! ## Order facts -/

theorem topoB_iff {g : Func} : ∀ {l : List ID}, topoB g l = true → TopoRem (argsF g) l
  | [], _ => trivial
  | x :: s, h => by
    simp only [topoB, Bool.and_eq_true, List.all_eq_true] at h
    refine ⟨fun a ha hm => ?_, topoB_iff h.2⟩
    have := h.1 a ha
    rw [List.contains_iff_mem.2 hm] at this
    cases this

theorem posFill_get : ∀ (l : List ID) (i : Nat) (a : Array Nat), l.Nodup → (∀ x ∈ l, x < a.size) →
    ∀ (k : Nat) (x : ID), l[k]? = some x → (posFill l i a)[x]! = i + k
  | [], _, _, _, _, k, x, h => by simp at h
  | y :: ys, i, a, hn, hs, k, x, h => by
    simp only [posFill]
    cases k with
    | zero =>
      simp at h; subst h
      have hy : y ∉ ys := (List.nodup_cons.1 hn).1
      rw [posFill_out ys (i + 1) _ y hy]
      have hy' := hs y List.mem_cons_self
      simp [Array.set!_eq_setIfInBounds, hy']
    | succ k =>
      rw [posFill_get ys (i + 1) _ (List.nodup_cons.1 hn).2
        (fun z hz => by simpa using hs z (List.mem_cons_of_mem _ hz)) k x (by simpa using h)]
      omega
where
  posFill_out : ∀ (l : List ID) (i : Nat) (a : Array Nat) (x : ID), x ∉ l →
      (posFill l i a)[x]! = a[x]!
    | [], _, _, _, _ => rfl
    | y :: ys, i, a, x, hx => by
      simp only [posFill]
      rw [posFill_out ys (i + 1) _ x (fun h => hx (List.mem_cons_of_mem _ h))]
      have hxy : y ≠ x := fun h => hx (h ▸ List.mem_cons_self)
      simp [getElem!_def, Array.set!_eq_setIfInBounds, hxy]

/-- The source positions: `x` at index `k` of `l` is at `k + 1`; a value not in `l` at 0. -/
theorem srcPos_get {n : Nat} {l : List ID} (hnd : l.Nodup) (hlt : ∀ x ∈ l, x < n) {k : Nat}
    {x : ID} (h : l[k]? = some x) : (srcPos n l)[x]! = k + 1 := by
  unfold srcPos
  rw [posFill_get l 1 _ hnd (by simpa using hlt) k x h]
  omega

theorem srcPos_out {n : Nat} {l : List ID} {x : ID} (hx : x ∉ l) : (srcPos n l)[x]! = 0 := by
  unfold srcPos
  rw [posFill_get.posFill_out l 1 _ x hx]
  by_cases h : x < n <;> simp [getElem!_def, Array.getElem?_replicate, h]

/-- A value at a positive source position before `x`'s is listed before `x`. -/
theorem srcPos_before {n : Nat} {l : List ID} (hnd : l.Nodup) (hlt : ∀ x ∈ l, x < n) {k : Nat}
    {x p : ID} (hx : l[k]? = some x) (h0 : 0 < (srcPos n l)[p]!)
    (hpx : (srcPos n l)[p]! < (srcPos n l)[x]!) : ∃ k', k' < k ∧ l[k']? = some p := by
  by_cases hp : p ∈ l
  · obtain ⟨k', hk'⟩ := List.mem_iff_getElem?.1 hp
    rw [srcPos_get hnd hlt hk', srcPos_get hnd hlt hx] at hpx
    exact ⟨k', by omega, hk'⟩
  · rw [srcPos_out hp] at h0; cases h0

/-- **What `orderOK` gives**: failing values `y` before `x` in the target order, with `x`
before `y` in the source order, satisfy `swapOK` at the source positions. -/
theorem orderOK_swap {tabs : Tables} {params : Array (Option AuxRef)} {tys : Array Ty} {f : Func}
    {n : Nat} {oS oT : Array ID}
    (h : orderOK tabs params tys f n oS oT = true) (hnd : oS.toList.Nodup) (hlt : ∀ x ∈ oS.toList, x < n)
    {i j : Nat} {x y : ID} (hij : i < j) (hy : oT.toList[i]? = some y) (hx : oT.toList[j]? = some x)
    (hfy : mayFail tabs f y = true) (hfx : mayFail tabs f x = true)
    {k l : Nat} (hkl : k < l) (hxk : oS.toList[k]? = some x) (hyl : oS.toList[l]? = some y) :
    swapOK tabs params tys f (srcPos n oS.toList) x y = true := by
  unfold orderOK at h
  have hp := of_decide_eq_true h
  rw [List.pairwise_filter, List.pairwise_iff_getElem] at hp
  have hi : i < oT.toList.length := (List.getElem?_eq_some_iff.1 hy).1
  have hj : j < oT.toList.length := (List.getElem?_eq_some_iff.1 hx).1
  have := hp i j hi hj hij
  rw [(List.getElem?_eq_some_iff.1 hy).2, (List.getElem?_eq_some_iff.1 hx).2] at this
  have h2 := this hfy hfx
  rw [srcPos_get hnd hlt hxk, srcPos_get hnd hlt hyl] at h2
  simpa [hkl] using h2

end GoFV.Proof.SchedL

import GoFV.Opt.Fuse.PlainCheck
import GoFV.Proof.Checked
import GoFV.Proof.Agree
import GoFV.Proof.WF
import GoFV.Proof.Sched
import GoFV.Proof.Frame
import GoFV.Proof.Avail
import GoFV.Proof.Pass.FusePlainFrame
import GoFV.Proof.SchedFast

/-!
# fuseBlockPlain: what the step checker establishes

`PRel f g run b0 c`: one checked plain fusion of the run `run` from `b0` to `c`
(`Plain.fuseBlockPlainChecked`, `GoFV.Opt.Fuse.PlainCheck`), in declarative form
(`checked_sound`: the snapshot's pre-check of `f`, the frame lemma `fuseRun_frame` for the
entries the check does not look at, and `postOK` for those it does; it needs `f` well formed).
This module unfolds the checker into the facts the simulation uses: the chain links (`link`),
the later blocks (`later`), the reads of the run's values (`reads`), the unchanged values
(`value_same`) and blocks (`block_out`), and the fused block (`merged`); the remaining fields
(`valEq` … `cpreds`) describe the result exactly enough to carry well-formedness and use
dominance over (`FusePlainPres`).
-/

namespace GoFV.Proof.FusePlain

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.Fuse GoFV.Opt.Fuse.Plain GoFV.Proof

/-- One checked plain fusion of the run `run` from `b0` to `c`. -/
structure PRel (f g : Func) (run : List ID) (b0 c : ID) : Prop where
  head : run.head? = some b0
  last : run.getLast? = some c
  parts : b0 ≠ c ∧ run.Nodup ∧ (∀ x ∈ run, x ∈ f.blocks) ∧ chainOK f run = true ∧
      (∀ y ∈ run.tail, laterOK f y = true) ∧ readsAllOK f run = true ∧ g.blocks = f.blocks ∧
      (g.entry == (if f.entry == b0 then c else f.entry)) = true ∧ g.ownAux = f.ownAux ∧
      g.valueTab.size = f.valueTab.size ∧ mergedOK f g run b0 c = true
  /-- A value outside the run's blocks is unchanged. -/
  valEq : ∀ x, (∀ y ∈ run, x ∉ (valsOf f y).toList) → g.value? x = f.value? x
  /-- A value of the run moves to `c`. -/
  moved : ∀ y ∈ run, ∀ x ∈ (valsOf f y).toList, ∃ fv gv, f.value? x = some fv ∧
    g.value? x = some gv ∧ sameV fv gv = true ∧ gv.block = c
  /-- A block outside the run that is no predecessor of `b0` is unchanged. -/
  blkEq : ∀ bid, bid ∉ run → isPredOf f b0 bid = false → g.block? bid = f.block? bid
  /-- A predecessor of `b0` outside the run has only its edges into `b0` redirected. -/
  predB : ∀ e ∈ predsOf f b0, e.b ∉ run → ∃ P, f.block? e.b = some P ∧
    g.block? e.b = some { P with succs := P.succs.map (redirect b0 c) }
  /-- The run's blocks before `c` are emptied. -/
  dead : ∀ y ∈ run.dropLast, ∃ Y', g.block? y = some Y' ∧ Y'.id = y ∧ Y'.values = #[] ∧
    Y'.preds = #[] ∧ Y'.succs = #[] ∧ Y'.controls = #[]
  /-- `c` takes `b0`'s predecessors. -/
  cpreds : ∀ C', g.block? c = some C' → C'.preds = predsOf f b0
  /-- A non-`Phi` of a block of the run reads no value of a later block. -/
  readsD : ∀ pre x suf, run = pre ++ x :: suf → ∀ v ∈ (valsOf f x).toList, ∀ fv,
    f.value? v = some fv → fv.op ≠ .Phi → ∀ a ∈ fv.args, ∀ y ∈ suf, a ∉ (valsOf f y).toList

variable {f g : Func} {run : List ID} {b0 c : ID}

theorem valsOf_mem {f : Func} {b x : ID} :
    x ∈ (valsOf f b).toList ↔ ∃ B, f.block? b = some B ∧ x ∈ B.values := by
  unfold valsOf
  cases h : f.block? b with
  | none => simp
  | some B => simp

theorem sameV_refl (v : Value) : sameV v v = true := by simp [sameV]

/-- A chain of linked blocks starting at a listed block is listed. -/
theorem chain_mem {ce : CheckEnv} (hwf : WF ce f) :
    ∀ {run : List ID} {b0 : ID}, chainOK f run = true → run.head? = some b0 → b0 ∈ f.blocks →
      ∀ x ∈ run, x ∈ f.blocks
  | [], _, _, _, _, x, hx => absurd hx List.not_mem_nil
  | [a], _, _, hh, hb, x, hx => by
    cases hh; rw [List.mem_singleton] at hx; subst hx; exact hb
  | a :: b :: rest, _, hch, hh, hb, x, hx => by
    cases hh
    unfold chainOK at hch
    rw [Bool.and_eq_true] at hch
    have hbm : b ∈ f.blocks := by
      unfold linkOK at hch
      obtain ⟨h1, -⟩ := hch
      cases hX : f.block? a with
      | none => rw [hX] at h1; cases h1
      | some X =>
        cases hY : f.block? b with
        | none => rw [hX, hY] at h1; cases h1
        | some Y =>
          rw [hX, hY] at h1
          simp only [Bool.and_eq_true, beq_iff_eq] at h1
          have := hwf.succLink a X ⟨hb, hX⟩ 0 ⟨b, 0⟩ (by rw [h1.1.2]; rfl)
          exact this.1
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hb
    · exact chain_mem hwf hch.2 rfl hbm x hx

theorem map_redirect_self {b0 c : ID} {a : Array Edge} (h : ∀ e ∈ a, e.b ≠ b0) :
    a.map (redirect b0 c) = a := by
  apply Array.ext_getElem?
  intro i
  rw [Array.getElem?_map]
  cases he : a[i]? with
  | none => rfl
  | some e =>
    have hne := h e (Array.mem_of_getElem? he)
    simp [redirect, hne]

theorem readsAllOK_spec {f : Func} : ∀ {run : List ID}, readsAllOK f run = true →
    ∀ pre x suf, run = pre ++ x :: suf → readsOK f x suf = true
  | [], _, pre, x, suf, hr => by cases pre <;> cases hr
  | a :: rest, h, pre, x, suf, hr => by
    unfold readsAllOK at h
    rw [Bool.and_eq_true] at h
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact h.1
    | cons p pre =>
      simp only [List.cons_append, List.cons.injEq] at hr
      exact readsAllOK_spec h.2 pre x suf hr.2

/-- `readsOK` in declarative form: a value of a later listed block has that block as `blockOf`. -/
theorem readsOK_spec {ce : CheckEnv} (hwf : WF ce f) {x : ID} {suf : List ID}
    (hin : ∀ y ∈ suf, y ∈ f.blocks) (hok : readsOK f x suf = true) {v : ID}
    (hv : v ∈ (valsOf f x).toList) {fv : Value} (hfv : f.value? v = some fv) (hnp : fv.op ≠ .Phi)
    {a : ID} (ha : a ∈ fv.args) {y : ID} (hy : y ∈ suf) : a ∉ (valsOf f y).toList := by
  unfold readsOK at hok
  rw [Array.all_eq_true'] at hok
  have := hok v (Array.mem_toList_iff.1 hv)
  rw [hfv] at this
  have h1 : (fv.op == .Phi) = false := by simpa using hnp
  simp only [h1, Bool.false_or, Array.all_eq_true'] at this
  have h2 := this a ha
  intro hm
  obtain ⟨Y, hY, haY⟩ := valsOf_mem.1 hm
  obtain ⟨va, hva, -, hblk⟩ := hwf.valueId y Y ⟨hin y hy, hY⟩ a haY
  have hb : DomCert.blockOf f a = y := by
    unfold DomCert.blockOf; rw [hva]; exact hblk
  rw [hb, List.contains_iff_mem.2 hy] at h2
  cases h2

private theorem filterMap_mem_pEnt {run : List ID} {preds : Array Edge} {f : Func} {e : Edge}
    (he : e ∈ preds.toList) (hn : e.b ∉ run) :
    (e.b, f.block? e.b) ∈ preds.toList.filterMap fun e =>
      if run.contains e.b then none else some (e.b, f.block? e.b) := by
  rw [List.mem_filterMap]
  exact ⟨e, he, by simp [hn]⟩

/-- A node of a block's schedule is a non-`Phi` value listed in the block. -/
theorem mem_schedule {f : Func} {B : Block} (hown : ValuesOwn f B) {o : Array ID}
    (h : schedule f B = some o) {y : ID} (hy : y ∈ o.toList) :
    y ∈ B.values ∧ ∃ v, f.value? y = some v ∧ v.op ≠ .Phi :=
  (nodeIn_schedNodes hown).1 (((schedule_spec h).topo.mem y).1 hy)

/-- On a block's own schedule, `npV` is `npAt`. -/
theorem filter_npV {ce : CheckEnv} (hwf : WF ce f) {x : ID} (hx : x ∈ f.blocks) {o : Array ID}
    (h : schedOf f x = some o) : o.toList.filter (npV f) = o.toList.filter (npAt f x) := by
  unfold schedOf at h
  cases hX : f.block? x with
  | none => rw [hX] at h; cases h
  | some X =>
    rw [hX] at h
    have hown := valuesOwn hwf hx hX
    apply List.filter_congr
    intro y hy
    obtain ⟨hyX, v, hv, -⟩ := mem_schedule hown h hy
    unfold npAt npOf npV
    rw [hX, hv]
    simp [hyX]

private theorem flatMap_congr' {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      flatMap_congr' fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- A non-pure value listed in a block is a non-pure node of its schedule nodes. -/
theorem npIn_of_npV {f : Func} {B : Block} (hown : ValuesOwn f B) {y : ID}
    (hp : npV f y = true) (hn : NodeIn (schedNodes f B).toList y) :
    npIn (schedNodes f B).toList y = true := by
  obtain ⟨n0, hn0, hid0⟩ := hn
  unfold npIn nodeOf
  cases hfd : (schedNodes f B).toList.find? (·.id == y) with
  | none =>
    exact absurd hfd (List.find?_isSome.2 ⟨n0, hn0, by simp [hid0]⟩ |> Option.isSome_iff_ne_none.1)
  | some n =>
    have hnm := List.mem_of_find?_eq_some hfd
    have hny : n.id = y := by simpa using List.find?_some hfd
    obtain ⟨id, hid, v, hv, -, rfl⟩ := mem_schedNodes.1 hnm
    obtain ⟨v', hv', hvid⟩ := hown id hid
    rw [hv] at hv'; cases hv'
    simp only at hny
    rw [hvid] at hny; subst hny
    unfold npV at hp; rw [hv] at hp
    simp only [Bool.and_eq_true] at hp
    exact hp.2

/-- The checker's schedule of a run block has the non-pure sequence of `Sem.schedule`. -/
theorem fastOf_np {ce : CheckEnv} (hwf : WF ce f) {x : ID} (hx : x ∈ f.blocks) {o : Array ID}
    (h : fastOf f x = some o) : ∃ o', schedOf f x = some o' ∧
      o.toList.filter (npV f) = o'.toList.filter (npAt f x) := by
  unfold fastOf at h
  cases hX : f.block? x with
  | none => rw [hX] at h; cases h
  | some X =>
    rw [hX] at h
    obtain ⟨o', ho', hfl⟩ := SchedFast.schedFast_filter
      (fun y hp hn => npIn_of_npV (valuesOwn hwf hx hX) hp hn) (p := npV f) h
    have hs : schedOf f x = some o' := by unfold schedOf; rw [hX]; exact ho'
    exact ⟨o', hs, hfl.symm.trans (filter_npV hwf hx hs)⟩

/-- **The checker's verdict in declarative form** (for well-formed `f`). -/
theorem checked_sound {ce : CheckEnv} (hwf : WF ce f) {b : ID} {s : Snap}
    (hs : snapOf f b = some s) (hpost : postOK s (fuseBlockPlain f b).1 = true) :
    PRel f (fuseBlockPlain f b).1 s.run s.b0 s.c := by
  unfold snapOf at hs
  split at hs
  · cases hs
  rename_i b0' c' runA hpr
  dsimp only at hs
  split at hs
  case h_2 => cases hs
  rename_i b0 c hb0 hc
  split at hs
  · cases hs
  rename_i hpre
  simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, beq_iff_eq, bne_iff_ne,
    ne_eq, decide_eq_true_eq, List.all_eq_true, Array.contains_iff_mem] at hpre
  obtain ⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, hne⟩, hnd⟩, hb0m⟩, hch⟩, hlat⟩, hrd⟩ := hpre
  split at hs
  case h_2 => cases hs
  rename_i C hC
  split at hs
  · cases hs
  rename_i hsch
  simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hsch
  cases hs
  dsimp only
  have hg : (fuseBlockPlain f b).1 = fuseRun f b0 c runA := by
    unfold fuseBlockPlain; rw [hpr]
  rw [hg] at hpost ⊢
  have hcm : c ∈ runA.toList := List.mem_of_getLast? hc
  obtain ⟨hF, hE⟩ := fuseRun_frame f b0 c runA hcm
  generalize fuseRun f b0 c runA = g at hpost hF hE ⊢
  unfold postOK at hpost
  dsimp only at hpost
  generalize runA.toList = run at hb0 hc hnd hch hlat hrd hsch hcm hF hpost ⊢
  have hin := chain_mem hwf hch hb0 hb0m
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hpost
  obtain ⟨⟨⟨⟨hmv, hpe⟩, hdead⟩, -⟩, hm⟩ := hpost
  have hmoved : ∀ y ∈ run, ∀ x ∈ (valsOf f y).toList, ∃ fv gv, f.value? x = some fv ∧
      g.value? x = some gv ∧ sameV fv gv = true ∧ gv.block = c := by
    intro y hy x hx
    have := hmv (x, f.value? x) (List.mem_flatMap.2 ⟨y, hy, List.mem_map.2 ⟨x, hx, rfl⟩⟩)
    simp only at this
    split at this
    · rename_i fv gv hf hg'
      rw [Bool.and_eq_true, beq_iff_eq] at this
      exact ⟨fv, gv, hf, hg', this.1, this.2⟩
    · cases this
  -- the fused block
  cases hC' : g.block? c with
  | none => rw [hC'] at hm; cases hm
  | some C' =>
  rw [hC'] at hm
  simp only [Bool.and_eq_true, beq_iff_eq] at hm
  obtain ⟨⟨⟨⟨⟨⟨hid, hvals⟩, hk⟩, hctl⟩, hsucc⟩, hpreds⟩, ho⟩ := hm
  cases hoF : SchedFast.schedFast g C' with
  | none => rw [hoF] at ho; cases ho
  | some oF =>
  rw [hoF, beq_iff_eq] at ho
  have hvals' : C'.values.toList = run.flatMap fun x => (valsOf f x).toList := by
    rw [hvals, List.map_flatMap]
    simp [Function.comp_def]
  -- the values of `C'` are its own in `g`
  have hownC : ValuesOwn g C' := by
    intro x hx
    rw [← Array.mem_toList_iff, hvals', List.mem_flatMap] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    obtain ⟨fv, gv, hf, hg', hsv, -⟩ := hmoved y hy x hxy
    obtain ⟨Y, hY, hxY⟩ := valsOf_mem.1 hxy
    obtain ⟨fv', hfv', hid', -⟩ := hwf.valueId y Y ⟨hin y hy, hY⟩ x hxY
    rw [hf] at hfv'; cases hfv'
    unfold sameV at hsv
    simp only [Bool.and_eq_true, beq_iff_eq] at hsv
    exact ⟨gv, hg', hsv.1.1.1.1.1.trans hid'⟩
  obtain ⟨oT, hoT, hfl⟩ := SchedFast.schedFast_filter
    (fun y hp hn => npIn_of_npV hownC hp hn) (p := npV g) hoF
  have h1 : oT.toList.filter (fun y => run.any fun x => npAt f x y) = oT.toList.filter (npV g) := by
    apply List.filter_congr
    intro y hy
    obtain ⟨hyC, gv, hgv, -⟩ := mem_schedule hownC hoT hy
    rw [← Array.mem_toList_iff, hvals', List.mem_flatMap] at hyC
    obtain ⟨x, hx, hyx⟩ := hyC
    obtain ⟨fv, gv', hf, hg', hsv, -⟩ := hmoved x hx y hyx
    rw [hgv] at hg'; cases hg'
    unfold sameV at hsv
    simp only [Bool.and_eq_true, beq_iff_eq] at hsv
    have hnpv : npV g y = npV f y := by simp only [npV, hgv, hf, hsv.1.2]
    rw [hnpv]
    obtain ⟨X, hX, hyX⟩ := valsOf_mem.1 hyx
    apply Bool.eq_iff_iff.2
    constructor
    · intro ha
      obtain ⟨x', -, hn⟩ := List.any_eq_true.1 ha
      unfold npAt at hn
      split at hn
      · unfold npOf at hn
        rw [hf, Bool.and_eq_true] at hn
        unfold npV; rw [hf]; exact hn.2
      · cases hn
    · intro hn
      refine List.any_eq_true.2 ⟨x, hx, ?_⟩
      unfold npAt npOf
      rw [hX, hf]
      simp only [npV, hf, Bool.and_eq_true] at hn
      simp only [Bool.and_eq_true]
      exact ⟨Array.contains_iff_mem.2 hyX, hn⟩
  have hmerged : mergedOK f g run b0 c = true := by
    unfold mergedOK
    simp only [hC, hC', hoT, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
    refine ⟨⟨⟨⟨⟨⟨⟨hid, hvals'⟩, hk⟩, hctl⟩, hsucc⟩, hpreds⟩, fun x hx => ?_⟩, ?_⟩
    · obtain ⟨o, ho'⟩ := Option.isSome_iff_exists.1 (hsch x hx)
      obtain ⟨o', hs', -⟩ := fastOf_np hwf (hin x hx) ho'
      rw [hs']; rfl
    rw [h1, hfl, ho]
    unfold npSeq
    rw [List.flatMap_map]
    apply flatMap_congr'
    intro x hx
    obtain ⟨o, ho'⟩ := Option.isSome_iff_exists.1 (hsch x hx)
    obtain ⟨o', hs', hnp⟩ := fastOf_np hwf (hin x hx) ho'
    rw [ho', hs']
    exact hnp
  refine ⟨hb0, hc, ⟨hne, hnd, hin, hch, hlat, hrd, hF.blocks, ?_, hF.ownAux, hF.vsize, hmerged⟩,
    fun x hx => hF.value x (fun ⟨y, hy, hxy⟩ => hx y hy hxy), hmoved,
    fun bid hn hp => hF.block bid (fun h => h.elim hn (fun h' => by rw [hp] at h'; cases h')),
    fun e he hn => ?_, fun y hy => ?_, fun C'' hC'' => ?_,
    fun pre x suf hr v hv fv hfv hnp a ha y hy =>
      readsOK_spec hwf (fun y hy => hin y (by rw [hr]; simp [hy]))
        (readsAllOK_spec hrd pre x suf hr) hv hfv hnp ha hy⟩
  · rw [beq_iff_eq, hE]
    by_cases h : f.entry = b0 <;> simp [h]
  · -- predecessors of `b0` outside the run
    have := hpe _ (filterMap_mem_pEnt (f := f) (Array.mem_toList_iff.2 he) hn)
    simp only at this
    split at this
    · rename_i P hP
      rw [beq_iff_eq] at this
      exact ⟨P, hP, this⟩
    · cases this
  · -- emptied blocks
    have := hdead y hy
    unfold deadOK at this
    split at this
    · rename_i Y' hY'
      simp only [Bool.and_eq_true, beq_iff_eq, Array.isEmpty_iff] at this
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := this
      exact ⟨Y', hY', h1, h2, h3, h4, h5⟩
    · cases this
  · rw [hC'] at hC''; cases hC''; exact hpreds

theorem PRel.entry (h : PRel f g run b0 c) :
    (f.entry = b0 → g.entry = c) ∧ (f.entry ≠ b0 → g.entry = f.entry) := by
  have he := h.parts.2.2.2.2.2.2.2.1
  constructor
  · intro hb; subst hb; simpa using he
  · intro hb; simpa [hb] using he

theorem PRel.run_cons (h : PRel f g run b0 c) : ∃ rest, run = b0 :: rest := by
  have hh := h.head
  cases run with
  | nil => cases hh
  | cons x rest => cases hh; exact ⟨rest, rfl⟩

theorem PRel.c_mem (h : PRel f g run b0 c) : c ∈ run := List.mem_of_getLast? h.last

theorem PRel.b0_mem (h : PRel f g run b0 c) : b0 ∈ run := List.mem_of_mem_head? h.head

/-- `c` is the last block: nothing follows it. -/
theorem PRel.c_last (h : PRel f g run b0 c) {pre suf : List ID} (hr : run = pre ++ c :: suf) :
    suf = [] := by
  have hl := h.last
  have hnd := h.parts.2.1
  rw [hr] at hl hnd
  cases suf with
  | nil => rfl
  | cons y suf =>
    exfalso
    rw [List.getLast?_append, List.getLast?_cons_cons,
      List.getLast?_eq_some_getLast (l := y :: suf) (List.cons_ne_nil _ _), Option.some_or] at hl
    have hcl : c ∈ y :: suf := by
      cases hl; exact List.getLast_mem _
    rw [List.nodup_append] at hnd
    exact (List.nodup_cons.1 hnd.2.1).1 hcl

/-! ## Chain links -/

theorem chainOK_spec {f : Func} : ∀ {run : List ID}, chainOK f run = true →
    ∀ pre x y suf, run = pre ++ x :: y :: suf → linkOK f x y = true
  | [], _, pre, x, y, suf, hr => by cases pre <;> cases hr
  | [_], _, pre, x, y, suf, hr => by
    rcases pre with _ | ⟨_, _ | _⟩ <;> simp at hr
  | a :: b :: rest, h, pre, x, y, suf, hr => by
    unfold chainOK at h
    rw [Bool.and_eq_true] at h
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hr
      obtain ⟨rfl, rfl, -⟩ := hr
      exact h.1
    | cons p pre =>
      simp only [List.cons_append, List.cons.injEq] at hr
      exact chainOK_spec h.2 pre x y suf hr.2

theorem linkOK_spec {f : Func} {x y : ID} (h : linkOK f x y = true) :
    ∃ X Y, f.block? x = some X ∧ f.block? y = some Y ∧ X.kind = .Plain ∧
      X.succs = #[⟨y, 0⟩] ∧ Y.preds = #[⟨x, 0⟩] := by
  unfold linkOK at h
  cases hX : f.block? x with
  | none => rw [hX] at h; cases h
  | some X =>
    cases hY : f.block? y with
    | none => rw [hX, hY] at h; cases h
    | some Y =>
      rw [hX, hY] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨X, Y, rfl, rfl, h.1.1, h.1.2, h.2⟩

/-- Consecutive blocks of the run. -/
theorem PRel.link (h : PRel f g run b0 c) {pre suf : List ID} {x y : ID}
    (hr : run = pre ++ x :: y :: suf) :
    ∃ X Y, f.block? x = some X ∧ f.block? y = some Y ∧ X.kind = .Plain ∧
      X.succs = #[⟨y, 0⟩] ∧ Y.preds = #[⟨x, 0⟩] :=
  linkOK_spec (chainOK_spec h.parts.2.2.2.1 pre x y suf hr)

/-! ## Later blocks and reads -/

theorem laterOK_spec {f : Func} {y : ID} (h : laterOK f y = true) :
    y ≠ f.entry ∧ ∀ x ∈ (valsOf f y).toList, ∃ v, f.value? x = some v ∧ v.op ≠ .Phi ∧
      v.op ≠ .Arg ∧ v.op ≠ .ArgIntReg := by
  unfold laterOK at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Array.all_eq_true'] at h
  refine ⟨h.1, fun x hx => ?_⟩
  have := h.2 x (Array.mem_toList_iff.1 hx)
  cases hv : f.value? x with
  | none => rw [hv] at this; cases this
  | some v =>
    rw [hv] at this
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    exact ⟨v, rfl, this.1.1, this.1.2, this.2⟩

/-- A block after `b0`: not the entry, no `Phi`, no parameter read. -/
theorem PRel.later (h : PRel f g run b0 c) {pre suf : List ID} {y : ID}
    (hr : run = pre ++ y :: suf) (hpre : pre ≠ []) :
    y ≠ f.entry ∧ ∀ x ∈ (valsOf f y).toList, ∃ v, f.value? x = some v ∧ v.op ≠ .Phi ∧
      v.op ≠ .Arg ∧ v.op ≠ .ArgIntReg := by
  obtain ⟨rest, hrest⟩ := h.run_cons
  refine laterOK_spec (h.parts.2.2.2.2.1 y ?_)
  rw [hrest] at hr
  cases pre with
  | nil => exact absurd rfl hpre
  | cons p pre =>
    simp only [List.cons_append, List.cons.injEq] at hr
    rw [hrest, List.tail_cons, hr.2]; simp

/-- A non-`Phi` of a block of the run reads no value of a later block. -/
theorem PRel.reads (h : PRel f g run b0 c) {pre suf : List ID} {x : ID}
    (hr : run = pre ++ x :: suf) {v : ID} (hv : v ∈ (valsOf f x).toList) {fv : Value}
    (hfv : f.value? v = some fv) (hnp : fv.op ≠ .Phi) {a : ID} (ha : a ∈ fv.args) {y : ID}
    (hy : y ∈ suf) : a ∉ (valsOf f y).toList :=
  h.readsD pre x suf hr v hv fv hfv hnp a ha y hy

/-! ## Values and blocks -/

/-- Every value is unchanged in what the semantics reads. -/
theorem PRel.value_same (h : PRel f g run b0 c) (x : ID) :
    SemEq (f.value? x) (g.value? x) ∧
      ∀ fv, f.value? x = some fv → ∃ gv, g.value? x = some gv ∧ gv.type = fv.type ∧
        gv.op = fv.op ∧ gv.args = fv.args := by
  by_cases hx : ∃ y ∈ run, x ∈ (valsOf f y).toList
  · obtain ⟨y, hy, hxy⟩ := hx
    obtain ⟨fv, gv, hf, hg, hs, -⟩ := h.moved y hy x hxy
    unfold sameV at hs
    simp only [Bool.and_eq_true, beq_iff_eq] at hs
    obtain ⟨⟨⟨⟨⟨hid, hty⟩, haux⟩, hai⟩, hop⟩, hargs⟩ := hs
    rw [hf, hg]
    exact ⟨⟨hid, hop, haux, hai, hargs⟩, fun fv' h' => by
      cases h'; exact ⟨gv, rfl, hty, hop, hargs⟩⟩
  · rw [not_exists] at hx
    rw [h.valEq x fun y hy hm => hx y ⟨hy, hm⟩]
    cases hf : f.value? x with
    | none => exact ⟨trivial, fun _ h => nomatch h⟩
    | some fv => exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun fv' h' => by
        cases h'; exact ⟨fv, rfl, rfl, rfl, rfl⟩⟩

/-- The fused block `c` of `g`. -/
theorem PRel.merged (h : PRel f g run b0 c) :
    ∃ C C' oT, f.block? c = some C ∧ g.block? c = some C' ∧ C'.id = c ∧
      C'.values.toList = run.flatMap (fun x => (valsOf f x).toList) ∧ C'.kind = C.kind ∧
      C'.controls = C.controls ∧ C'.succs = C.succs.map (redirect b0 c) ∧
      (∀ x ∈ run, (schedOf f x).isSome) ∧ schedule g C' = some oT ∧
      oT.toList.filter (fun y => run.any (npAt f · y)) = npSeq f run := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hm⟩ := h.parts
  unfold mergedOK at hm
  cases hC : f.block? c with
  | none => rw [hC] at hm; cases hm
  | some C =>
    cases hC' : g.block? c with
    | none => rw [hC, hC'] at hm; cases hm
    | some C' =>
      rw [hC, hC'] at hm
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hm
      obtain ⟨⟨⟨⟨⟨⟨⟨hid, hv⟩, hk⟩, hc⟩, hs⟩, -⟩, hsch⟩, ho⟩ := hm
      cases hoT : schedule g C' with
      | none => rw [hoT] at ho; cases ho
      | some oT =>
        rw [hoT] at ho
        exact ⟨C, C', oT, rfl, rfl, hid, hv, hk, hc, hs, hsch, hoT, by simpa using ho⟩

end GoFV.Proof.FusePlain

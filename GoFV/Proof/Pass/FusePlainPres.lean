import GoFV.Proof.Pass.FusePlainRel
import GoFV.Proof.DomRel

/-!
# fuseBlockPlain keeps well-formedness and use dominance

The step checker no longer runs `check` on its result (issue #147): `wf_pres` and `useDom_pres`
derive `WF` and `Dom.UseDom` of `g` from those of `f` and the step relation `PRel`.

- Blocks of `g`: outside the run, `f`'s block with edges into `b0` redirected to `c`
  (`gblock_out`); `c` holds the run's values, `b0`'s predecessors and `c`'s redirected
  successors (`gblock_c`); the other blocks of the run are empty (`PRel.dead`).
- Values of `g`: outside the run unchanged, the run's values moved to `c` (`gvalue`).
- Paths: a path of `g` expands into a path of `f` (`reach_back`): each visit of `c` becomes the
  run `b0 … c` (`expand`), so a block every path of `f` passes passes every path of `g`, with the
  run's blocks seen as `c` (`mem_expand`).
-/

namespace GoFV.Proof.FusePlain

open GoFV.SSA GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.Fuse GoFV.Opt.Fuse.Plain GoFV.Proof Dom

variable {ce : CheckEnv} {f g : Func} {run : List ID} {b0 c : ID}

theorem isPredOf_spec {f : Func} {b0 p : ID} (hp : isPredOf f b0 p = true) :
    ∃ e ∈ predsOf f b0, e.b = p := by
  unfold isPredOf at hp
  split at hp
  · rename_i B0 hB0
    obtain ⟨k, hk, hke⟩ := Array.any_eq_true.1 hp
    rw [beq_iff_eq] at hke
    exact ⟨B0.preds[k], by unfold predsOf; rw [hB0]; exact Array.getElem_mem hk, hke⟩
  · cases hp

theorem predsOf_eq {f : Func} {b0 : ID} {B0 : Block} (h : f.block? b0 = some B0) :
    predsOf f b0 = B0.preds := by
  unfold predsOf; rw [h]; rfl

theorem sameV_spec {fv gv : Value} (h : sameV fv gv = true) :
    gv.id = fv.id ∧ gv.type = fv.type ∧ gv.aux = fv.aux ∧ gv.auxInt = fv.auxInt ∧
      gv.op = fv.op ∧ gv.args = fv.args := by
  unfold sameV at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem redirect_ne {b0 c : ID} {e : Edge} (h : e.b ≠ b0) : redirect b0 c e = e := by
  unfold redirect; simp [h]

theorem redirect_eq {b0 c : ID} {e : Edge} (h : e.b = b0) : redirect b0 c e = ⟨c, e.i⟩ := by
  unfold redirect; simp [h]

/-- A path of `g` (most recent block first) with each visit of `c` expanded into the run
(`b0 … c`, most recent first). -/
def expand (run : List ID) (c : ID) : List ID → List ID
  | [] => []
  | y :: l => (if y = c then run.reverse else [y]) ++ expand run c l

theorem nodup_flatMap {L : ID → List ID} : ∀ {l : List ID}, l.Nodup →
    (∀ y ∈ l, (L y).Nodup) →
    (∀ y ∈ l, ∀ z ∈ l, y ≠ z → ∀ v, v ∈ L y → v ∈ L z → False) → (l.flatMap L).Nodup
  | [], _, _, _ => List.nodup_nil
  | y :: l, hnd, h1, h2 => by
    rw [List.flatMap_cons, List.nodup_append]
    obtain ⟨hy, hnd'⟩ := List.nodup_cons.1 hnd
    refine ⟨h1 y List.mem_cons_self, nodup_flatMap hnd' (fun z hz => h1 z (List.mem_cons_of_mem _ hz))
      (fun a ha b hb => h2 a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)), ?_⟩
    intro v hv w hw hvw
    subst hvw
    obtain ⟨z, hz, hvz⟩ := List.mem_flatMap.1 hw
    exact h2 y List.mem_cons_self z (List.mem_cons_of_mem _ hz) (fun he => hy (he ▸ hz)) v hv hvz

/-! ## The run -/

namespace PRel

variable (h : PRel f g run b0 c)
include h

theorem ne : b0 ≠ c := h.parts.1
theorem nodup : run.Nodup := h.parts.2.1
theorem inRun {x : ID} (hx : x ∈ run) : x ∈ f.blocks := h.parts.2.2.1 x hx
theorem gblocks : g.blocks = f.blocks := h.parts.2.2.2.2.2.2.1

theorem run_last : run = run.dropLast ++ [c] := by
  have hl := h.last
  have hne : run ≠ [] := by rintro rfl; simp at hl
  rw [List.getLast?_eq_getLast hne, Option.some.injEq] at hl
  rw [← hl]; exact (List.dropLast_concat_getLast hne).symm

theorem mem_dropLast {y : ID} (hy : y ∈ run) (hne : y ≠ c) : y ∈ run.dropLast := by
  have hr := h.run_last
  rw [hr, List.mem_append, List.mem_singleton] at hy
  rcases hy with hy | hy
  · exact hy
  · exact absurd hy hne

theorem c_not_dropLast : c ∉ run.dropLast := by
  intro hc
  have hnd := h.nodup
  rw [h.run_last, List.nodup_append] at hnd
  exact hnd.2.2 c hc c (List.mem_singleton_self c) rfl

theorem dropLast_mem {y : ID} (hy : y ∈ run.dropLast) : y ∈ run := by
  rw [h.run_last]; exact List.mem_append_left _ hy

/-- A block of the run other than `b0` follows its predecessor in the run. -/
theorem split_prev {y : ID} (hy : y ∈ run) (hne : y ≠ b0) :
    ∃ pre x suf, run = pre ++ x :: y :: suf := by
  obtain ⟨rest, hrest⟩ := h.run_cons
  rw [hrest] at hy
  rcases List.mem_cons.1 hy with rfl | hy
  · exact absurd rfl hne
  obtain ⟨p, s, hp⟩ := List.append_of_mem hy
  have hne' : b0 :: p ≠ [] := List.cons_ne_nil _ _
  refine ⟨(b0 :: p).dropLast, (b0 :: p).getLast hne', s, ?_⟩
  have hd := List.dropLast_concat_getLast hne'
  rw [hrest, hp]
  calc b0 :: (p ++ y :: s) = (b0 :: p) ++ y :: s := rfl
    _ = ((b0 :: p).dropLast ++ [(b0 :: p).getLast hne']) ++ y :: s := by rw [hd]
    _ = _ := by simp

/-- A block of the run other than `c` precedes its successor in the run. -/
theorem split_next {y : ID} (hy : y ∈ run.dropLast) :
    ∃ pre z suf, run = pre ++ y :: z :: suf := by
  obtain ⟨p, s, hp⟩ := List.append_of_mem hy
  have hr := h.run_last
  rw [hp] at hr
  cases s with
  | nil => exact ⟨p, c, [], by rw [hr]; simp⟩
  | cons z s => exact ⟨p, z, s ++ [c], by rw [hr]; simp⟩

theorem next_ne_b0 {pre suf : List ID} {x y : ID} (hr : run = pre ++ x :: y :: suf) : y ≠ b0 := by
  rintro rfl
  obtain ⟨rest, hrest⟩ := h.run_cons
  have hnd := h.nodup
  rw [hr] at hnd hrest
  cases pre with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at hrest
    rw [hrest.1] at hnd
    simp at hnd
  | cons p pre =>
    simp only [List.cons_append, List.cons.injEq] at hrest
    rw [← hrest.1] at hnd
    simp at hnd

theorem prev_ne_c {pre suf : List ID} {x y : ID} (hr : run = pre ++ x :: y :: suf) : x ≠ c := by
  rintro rfl
  have := h.c_last (pre := pre) (suf := y :: suf) (by rw [hr])
  cases this

/-- The predecessor of a block of the run other than `b0`. -/
theorem prev_link {y : ID} (hy : y ∈ run) (hne : y ≠ b0) :
    ∃ x Y, x ∈ run ∧ x ≠ c ∧ f.block? y = some Y ∧ Y.preds = #[⟨x, 0⟩] := by
  obtain ⟨pre, x, suf, hr⟩ := h.split_prev hy hne
  obtain ⟨X, Y, -, hY, -, -, hp⟩ := h.link hr
  exact ⟨x, Y, by rw [hr]; simp, h.prev_ne_c hr, hY, hp⟩

/-- The successor of a block of the run other than `c`. -/
theorem next_link {y : ID} (hy : y ∈ run.dropLast) :
    ∃ z Y, z ∈ run ∧ z ≠ b0 ∧ f.block? y = some Y ∧ Y.succs = #[⟨z, 0⟩] := by
  obtain ⟨pre, z, suf, hr⟩ := h.split_next hy
  obtain ⟨Y, Z, hY, -, -, hs, -⟩ := h.link hr
  exact ⟨z, Y, by rw [hr]; simp, h.next_ne_b0 hr, hY, hs⟩

/-- A block outside the run, or `c`, enters the run only at `b0`. -/
theorem out_succ (hwf : WF ce f) {bid : ID} (hb : bid ∈ f.blocks) (hbr : bid ∉ run ∨ bid = c)
    {B : Block} (hB : f.block? bid = some B) {e : Edge} (he : e ∈ B.succs) (her : e.b ∈ run) :
    e.b = b0 := by
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨x, Y, hx, hxc, hY, hp⟩ := h.prev_link her hne
  obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 he
  obtain ⟨-, Y', hY', hpe⟩ := hwf.succLink bid B ⟨hb, hB⟩ j e hj
  rw [hY] at hY'; cases hY'
  rw [hp] at hpe
  have h0 : e.i = 0 := by
    rcases Nat.lt_or_ge e.i 1 with h' | h'
    · omega
    · rw [Array.getElem?_eq_none (by simpa using h')] at hpe; cases hpe
  rw [h0] at hpe
  simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq,
    Edge.mk.injEq] at hpe
  rcases hbr with hbr | hbr
  · exact hbr (hpe.1 ▸ hx)
  · exact hxc (hpe.1 ▸ hbr)

/-- A predecessor of a block outside the run is not an emptied block of the run. -/
theorem out_pred (hwf : WF ce f) {bid : ID} (hb : bid ∈ f.blocks) (hbr : bid ∉ run)
    {B : Block} (hB : f.block? bid = some B) {i : Nat} {e : Edge} (he : B.preds[i]? = some e) :
    e.b ∉ run.dropLast := by
  intro hed
  obtain ⟨z, Y, hz, -, hY, hs⟩ := h.next_link hed
  obtain ⟨-, P, hP, hps⟩ := hwf.predLink bid B ⟨hb, hB⟩ i e he
  rw [hY] at hP; cases hP
  rw [hs] at hps
  have h0 : e.i = 0 := by
    rcases Nat.lt_or_ge e.i 1 with h' | h'
    · omega
    · rw [Array.getElem?_eq_none (by simpa using h')] at hps; cases hps
  rw [h0] at hps
  simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq,
    Edge.mk.injEq] at hps
  exact hbr (hps.1 ▸ hz)

/-! ## Blocks and values of `g` -/

/-- A block outside the run: edges into `b0` redirected to `c`. -/
theorem gblock_out (hwf : WF ce f) {bid : ID} (hb : bid ∈ f.blocks) (hn : bid ∉ run) :
    ∃ B, f.block? bid = some B ∧
      g.block? bid = some { B with succs := B.succs.map (redirect b0 c) } := by
  cases hp : isPredOf f b0 bid
  · obtain ⟨B, hB, -⟩ := hwf.blockId bid hb
    refine ⟨B, hB, ?_⟩
    rw [h.blkEq bid hn hp, hB]
    have hsu : B.succs.map (redirect b0 c) = B.succs := by
      refine map_redirect_self fun e he hb0e => ?_
      obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 he
      obtain ⟨-, B0, hB0, hpe⟩ := hwf.succLink bid B ⟨hb, hB⟩ j e hj
      rw [hb0e] at hB0
      unfold isPredOf at hp
      rw [hB0, Array.any_eq_false] at hp
      obtain ⟨hk, hke⟩ := Array.getElem?_eq_some_iff.1 hpe
      have := hp e.i hk
      rw [hke] at this
      simp at this
    rw [hsu]
  · obtain ⟨e, he, rfl⟩ := isPredOf_spec hp
    exact h.predB e he hn

/-- A listed block outside the run is unchanged but for edges into `b0`. -/
theorem block_out (hwf : WF ce f) {bid : ID} (hb : bid ∈ f.blocks) (hn : bid ∉ run) :
    ∃ fb gb, f.block? bid = some fb ∧ g.block? bid = some gb ∧ gb.id = fb.id ∧
      gb.values = fb.values ∧ gb.kind = fb.kind ∧ gb.controls = fb.controls ∧
      gb.succs = fb.succs.map (redirect b0 c) :=
  let ⟨B, hB, hB'⟩ := h.gblock_out hwf hb hn
  ⟨B, _, hB, hB', rfl, rfl, rfl, rfl, rfl⟩

/-- The fused block. -/
theorem gblock_c :
    ∃ C C', f.block? c = some C ∧ g.block? c = some C' ∧ C'.id = c ∧
      C'.values.toList = run.flatMap (fun x => (valsOf f x).toList) ∧ C'.kind = C.kind ∧
      C'.controls = C.controls ∧ C'.succs = C.succs.map (redirect b0 c) ∧
      C'.preds = predsOf f b0 := by
  obtain ⟨C, C', -, hC, hC', hid, hv, hk, hc, hs, -⟩ := h.merged
  exact ⟨C, C', hC, hC', hid, hv, hk, hc, hs, h.cpreds C' hC'⟩

/-- Every value of `g` is `f`'s, or a value of the run moved to `c`. -/
theorem gvalue (x : ID) :
    (∃ y ∈ run, x ∈ (valsOf f y).toList ∧ ∃ fv gv, f.value? x = some fv ∧
      g.value? x = some gv ∧ sameV fv gv = true ∧ gv.block = c) ∨
    ((∀ y ∈ run, x ∉ (valsOf f y).toList) ∧ g.value? x = f.value? x) := by
  by_cases hx : ∃ y ∈ run, x ∈ (valsOf f y).toList
  · obtain ⟨y, hy, hxy⟩ := hx
    exact .inl ⟨y, hy, hxy, h.moved y hy x hxy⟩
  · rw [not_exists] at hx
    have hx' : ∀ y ∈ run, x ∉ (valsOf f y).toList := fun y hy hm => hx y ⟨hy, hm⟩
    exact .inr ⟨hx', h.valEq x hx'⟩

/-- What the semantics reads of a value of `g` is `f`'s. -/
theorem gvalue_f {x : ID} {gv : Value} (hg : g.value? x = some gv) :
    ∃ fv, f.value? x = some fv ∧ gv.id = fv.id ∧ gv.op = fv.op ∧ gv.args = fv.args ∧
      gv.auxInt = fv.auxInt := by
  rcases h.gvalue x with ⟨-, -, -, fv, gv', hf, hg', hs, -⟩ | ⟨-, he⟩
  · rw [hg] at hg'; cases hg'
    obtain ⟨h1, -, -, h4, h5, h6⟩ := sameV_spec hs
    exact ⟨fv, hf, h1, h5, h6, h4⟩
  · rw [hg] at he
    exact ⟨gv, he.symm, rfl, rfl, rfl, rfl⟩

/-- The block of `c` other than `c` of the run is empty in `g`. -/
theorem gblock_dead {y : ID} (hy : y ∈ run) (hne : y ≠ c) :
    ∃ Y', g.block? y = some Y' ∧ Y'.id = y ∧ Y'.values = #[] ∧ Y'.preds = #[] ∧
      Y'.succs = #[] ∧ Y'.controls = #[] :=
  h.dead y (h.mem_dropLast hy hne)

/-- A value listed in a block of `g` is listed in a block of `f`: the same block outside the
run, a block of the run for `c`. -/
theorem memG (hwf : WF ce f) {bid : ID} {b : Block} (hb : BlockIn g bid b) {vid : ID}
    (hv : vid ∈ b.values) :
    ∃ y Y, BlockIn f y Y ∧ vid ∈ Y.values ∧ ((y ∈ run ∧ bid = c) ∨ (y ∉ run ∧ bid = y)) := by
  obtain ⟨hbm, hbb⟩ := hb
  rw [h.gblocks] at hbm
  by_cases hbr : bid ∈ run
  · by_cases hbc : bid = c
    · subst hbc
      obtain ⟨C, C', -, hC', -, hvals, -⟩ := h.gblock_c
      rw [hbb] at hC'; cases hC'
      have : vid ∈ b.values.toList := Array.mem_toList_iff.2 hv
      rw [hvals, List.mem_flatMap] at this
      obtain ⟨y, hy, hvy⟩ := this
      obtain ⟨Y, hY, hvY⟩ := valsOf_mem.1 hvy
      exact ⟨y, Y, ⟨h.inRun hy, hY⟩, hvY, .inl ⟨hy, rfl⟩⟩
    · obtain ⟨Y', hY', -, hvals, -⟩ := h.gblock_dead hbr hbc
      rw [hbb] at hY'; cases hY'
      rw [hvals] at hv; simp at hv
  · obtain ⟨B, hB, hB'⟩ := h.gblock_out hwf hbm hbr
    rw [hbb] at hB'; cases hB'
    exact ⟨bid, B, ⟨hbm, hB⟩, hv, .inr ⟨hbr, rfl⟩⟩

/-- A value listed in a block of `f` is listed in `g` (in `c` for a block of the run). -/
theorem memF (hwf : WF ce f) {y : ID} {Y : Block} (hy : BlockIn f y Y) {vid : ID}
    (hv : vid ∈ Y.values) : Listed g vid := by
  obtain ⟨hym, hyb⟩ := hy
  by_cases hyr : y ∈ run
  · obtain ⟨C, C', -, hC', -, hvals, -⟩ := h.gblock_c
    refine ⟨c, C', ⟨by rw [h.gblocks]; exact h.inRun h.c_mem, hC'⟩, ?_⟩
    have : vid ∈ C'.values.toList := by
      rw [hvals, List.mem_flatMap]
      exact ⟨y, hyr, valsOf_mem.2 ⟨Y, hyb, hv⟩⟩
    exact Array.mem_toList_iff.1 this
  · obtain ⟨B, hB, hB'⟩ := h.gblock_out hwf hym hyr
    rw [hyb] at hB; cases hB
    exact ⟨y, _, ⟨by rw [h.gblocks]; exact hym, hB'⟩, hv⟩

theorem listed_g (hwf : WF ce f) {a : ID} (ha : Listed f a) : Listed g a := by
  obtain ⟨y, Y, hy, hv⟩ := ha
  exact h.memF hwf hy hv

/-! ## Well-formedness -/

theorem wf_pres (hwf : WF ce f) : WF ce g where
  blockId := fun bid hbm => by
    rw [h.gblocks] at hbm
    by_cases hbr : bid ∈ run
    · by_cases hbc : bid = c
      · subst hbc
        obtain ⟨C, C', -, hC', hid, -⟩ := h.gblock_c
        exact ⟨C', hC', hid⟩
      · obtain ⟨Y', hY', hid, -⟩ := h.gblock_dead hbr hbc
        exact ⟨Y', hY', hid⟩
    · obtain ⟨B, hB, hB'⟩ := h.gblock_out hwf hbm hbr
      obtain ⟨B'', hB'', hid⟩ := hwf.blockId bid hbm
      rw [hB] at hB''; cases hB''
      exact ⟨_, hB', hid⟩
  blocksNodup := by rw [h.gblocks]; exact hwf.blocksNodup
  valueId := fun bid b hb vid hv => by
    obtain ⟨y, Y, hy, hvY, hcase⟩ := h.memG hwf hb hv
    obtain ⟨fv, hfv, hid, hblk⟩ := hwf.valueId y Y hy vid hvY
    rcases hcase with ⟨hyr, rfl⟩ | ⟨hyr, hbe⟩
    · obtain ⟨fv', gv, hf, hg, hs, hgb⟩ :=
        h.moved y hyr vid (valsOf_mem.2 ⟨Y, hy.2, hvY⟩)
      rw [hfv] at hf; cases hf
      exact ⟨gv, hg, by rw [(sameV_spec hs).1, hid], hgb⟩
    · refine ⟨fv, ?_, hid, hblk.trans hbe.symm⟩
      rcases h.gvalue vid with ⟨y', hy', hvy', -⟩ | ⟨-, he⟩
      · obtain ⟨Y'', hY'', hvY''⟩ := valsOf_mem.1 hvy'
        have := hwf.valueOnce y Y y' Y'' hy ⟨h.inRun hy', hY''⟩ vid hvY hvY''
        exact absurd (this ▸ hy') hyr
      · rw [he, hfv]
  valuesNodup := fun bid b hb => by
    obtain ⟨hbm, hbb⟩ := hb
    rw [h.gblocks] at hbm
    by_cases hbr : bid ∈ run
    · by_cases hbc : bid = c
      · subst hbc
        obtain ⟨C, C', -, hC', -, hvals, -⟩ := h.gblock_c
        rw [hbb] at hC'; cases hC'
        have : b.values.toList.Nodup := by
          rw [hvals]
          refine nodup_flatMap h.nodup (fun y hy => ?_) (fun y hy z hz hne v hvy hvz => ?_)
          · obtain ⟨Y, hY, -⟩ := hwf.blockId y (h.inRun hy)
            rw [valsOf_eq hY]
            exact hwf.valuesNodup y Y ⟨h.inRun hy, hY⟩
          · obtain ⟨Y, hY, hvY⟩ := valsOf_mem.1 hvy
            obtain ⟨Z, hZ, hvZ⟩ := valsOf_mem.1 hvz
            exact hne (hwf.valueOnce y Y z Z ⟨h.inRun hy, hY⟩ ⟨h.inRun hz, hZ⟩ v hvY hvZ)
        exact this
      · obtain ⟨Y', hY', -, hvals, -⟩ := h.gblock_dead hbr hbc
        rw [hbb] at hY'; cases hY'
        rw [hvals]; simp
    · obtain ⟨B, hB, hB'⟩ := h.gblock_out hwf hbm hbr
      rw [hbb] at hB'; cases hB'
      exact hwf.valuesNodup bid B ⟨hbm, hB⟩
  valueOnce := fun bid1 b1 bid2 b2 hb1 hb2 vid hv1 hv2 => by
    obtain ⟨y1, Y1, hy1, hvY1, hc1⟩ := h.memG hwf hb1 hv1
    obtain ⟨y2, Y2, hy2, hvY2, hc2⟩ := h.memG hwf hb2 hv2
    have he := hwf.valueOnce y1 Y1 y2 Y2 hy1 hy2 vid hvY1 hvY2
    subst he
    rcases hc1 with ⟨hr, rfl⟩ | ⟨hr, rfl⟩ <;> rcases hc2 with ⟨hr', rfl⟩ | ⟨hr', rfl⟩
    · rfl
    · exact absurd hr hr'
    · exact absurd hr' hr
    · rfl
  predLink := fun bid b hb i e he => by
    obtain ⟨hbm, hbb⟩ := hb
    rw [h.gblocks] at hbm
    rw [h.gblocks]
    -- the source edge `e.b → bid'` (`bid'` is `b0` for `c`) and its redirection
    have key : ∀ {bid' : ID} {B : Block}, bid' ∈ f.blocks → f.block? bid' = some B →
        B.preds[i]? = some e → (bid' ∉ run ∨ bid' = b0) → redirect b0 c ⟨bid', i⟩ = ⟨bid, i⟩ →
        e.b ∈ f.blocks ∧ ∃ p, g.block? e.b = some p ∧ p.succs[e.i]? = some ⟨bid, i⟩ := by
      intro bid' B hm hB hpe hcase hred
      obtain ⟨hem, P, hP, hps⟩ := hwf.predLink bid' B ⟨hm, hB⟩ i e hpe
      refine ⟨hem, ?_⟩
      by_cases hr : e.b ∈ run
      · by_cases hec : e.b = c
        · obtain ⟨C, C', hC, hC', -, -, -, -, hs, -⟩ := h.gblock_c
          rw [← hec] at hC hC'
          rw [hP] at hC; cases hC
          exact ⟨C', hC', by rw [hs, Array.getElem?_map, hps]; exact congrArg some hred⟩
        · obtain ⟨z, Y, hz, hz0, hY, hs⟩ := h.next_link (h.mem_dropLast hr hec)
          rw [hP] at hY; cases hY
          rw [hs] at hps
          have h0 : e.i = 0 := by
            rcases Nat.lt_or_ge e.i 1 with h' | h'
            · omega
            · rw [Array.getElem?_eq_none (by simpa using h')] at hps; cases hps
          rw [h0] at hps
          simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq,
            Edge.mk.injEq] at hps
          rcases hcase with hn | h0'
          · exact absurd (hps.1 ▸ hz) hn
          · exact absurd (hps.1.trans h0') hz0
      · obtain ⟨P', hP', hP''⟩ := h.gblock_out hwf hem hr
        rw [hP] at hP'; cases hP'
        exact ⟨_, hP'', by simp only [Array.getElem?_map, hps]; exact congrArg some hred⟩
    by_cases hbr : bid ∈ run
    · by_cases hbc : bid = c
      · subst hbc
        obtain ⟨C, C', -, hC', -, -, -, -, -, hp⟩ := h.gblock_c
        rw [hbb] at hC'; cases hC'
        obtain ⟨B0, hB0, -⟩ := hwf.blockId b0 (h.inRun h.b0_mem)
        rw [hp, predsOf_eq hB0] at he
        exact key (h.inRun h.b0_mem) hB0 he (.inr rfl) (redirect_eq rfl)
      · obtain ⟨Y', hY', -, -, hpr, -⟩ := h.gblock_dead hbr hbc
        rw [hbb] at hY'; cases hY'
        rw [hpr] at he; simp at he
    · obtain ⟨B, hB, hB'⟩ := h.gblock_out hwf hbm hbr
      rw [hbb] at hB'; cases hB'
      have hne : bid ≠ b0 := fun he' => hbr (he' ▸ h.b0_mem)
      exact key hbm hB he (.inl hbr) (redirect_ne hne)
  succLink := fun bid b hb j e he => by
    obtain ⟨hbm, hbb⟩ := hb
    rw [h.gblocks] at hbm
    rw [h.gblocks]
    have key : ∀ {B : Block}, f.block? bid = some B → (bid ∉ run ∨ bid = c) →
        b.succs = B.succs.map (redirect b0 c) →
        e.b ∈ f.blocks ∧ ∃ q, g.block? e.b = some q ∧ q.preds[e.i]? = some ⟨bid, j⟩ := by
      intro B hB hcase hsu
      rw [hsu, Array.getElem?_map] at he
      cases he0 : B.succs[j]? with
      | none => rw [he0] at he; cases he
      | some e0 =>
        rw [he0] at he
        cases he
        obtain ⟨hem, Q, hQ, hqp⟩ := hwf.succLink bid B ⟨hbm, hB⟩ j e0 he0
        by_cases hb0 : e0.b = b0
        · rw [redirect_eq hb0]
          obtain ⟨C, C', -, hC', -, -, -, -, -, hp⟩ := h.gblock_c
          refine ⟨h.inRun h.c_mem, C', hC', ?_⟩
          rw [hp]
          rw [hb0] at hQ
          rw [predsOf_eq hQ]
          exact hqp
        · rw [redirect_ne hb0]
          have hr : e0.b ∉ run := fun hr =>
            hb0 (h.out_succ hwf hbm hcase hB (Array.mem_of_getElem? he0) hr)
          obtain ⟨Q', hQ', hQ''⟩ := h.gblock_out hwf hem hr
          rw [hQ] at hQ'; cases hQ'
          exact ⟨hem, _, hQ'', hqp⟩
    by_cases hbr : bid ∈ run
    · by_cases hbc : bid = c
      · subst hbc
        obtain ⟨C, C', hC, hC', -, -, -, -, hs, -⟩ := h.gblock_c
        rw [hbb] at hC'; cases hC'
        exact key hC (.inr rfl) hs
      · obtain ⟨Y', hY', -, -, -, hsu, -⟩ := h.gblock_dead hbr hbc
        rw [hbb] at hY'; cases hY'
        rw [hsu] at he; simp at he
    · obtain ⟨B, hB, hB'⟩ := h.gblock_out hwf hbm hbr
      rw [hbb] at hB'; cases hB'
      exact key hB (.inl hbr) rfl
  arity := fun bid b vid v hv hn => by
    obtain ⟨hb, hvm, hgv⟩ := hv
    obtain ⟨y, Y, hy, hvY, -⟩ := h.memG hwf hb hvm
    obtain ⟨fv, hfv, -, hop, hargs, -⟩ := h.gvalue_f hgv
    rw [hop] at hn; rw [hop, hargs]
    exact hwf.arity y Y vid fv ⟨hy, hvY, hfv⟩ hn
  phiArity := fun bid b vid v hv hphi => by
    obtain ⟨hb, hvm, hgv⟩ := hv
    obtain ⟨y, Y, hy, hvY, hcase⟩ := h.memG hwf hb hvm
    obtain ⟨fv, hfv, -, hop, hargs, -⟩ := h.gvalue_f hgv
    rw [hop] at hphi
    rw [hargs]
    obtain ⟨hbm, hbb⟩ := hb
    rcases hcase with ⟨hyr, rfl⟩ | ⟨hyr, hbe⟩
    · -- only `b0` of the run holds `Phi`s
      have hy0 : y = b0 := by
        refine Classical.byContradiction fun hne => ?_
        obtain ⟨pre, x, suf, hr⟩ := h.split_prev hyr hne
        obtain ⟨-, hlat⟩ := h.later (pre := pre ++ [x]) (suf := suf) (y := y) (by rw [hr]; simp)
          (by simp)
        obtain ⟨v', hv', hnp, -⟩ := hlat vid (valsOf_mem.2 ⟨Y, hy.2, hvY⟩)
        rw [hfv] at hv'; cases hv'
        exact hnp hphi
      subst hy0
      obtain ⟨C, C', -, hC', -, -, -, -, -, hp⟩ := h.gblock_c
      rw [hbb] at hC'; cases hC'
      rw [hp, predsOf_eq hy.2]
      exact hwf.phiArity y Y vid fv ⟨hy, hvY, hfv⟩ hphi
    · subst hbe
      rw [h.gblocks] at hbm
      obtain ⟨B, hB, hB'⟩ := h.gblock_out hwf hbm hyr
      rw [hbb] at hB'; cases hB'
      rw [hy.2] at hB; cases hB
      exact hwf.phiArity bid Y vid fv ⟨hy, hvY, hfv⟩ hphi
  boolAux := fun bid b vid v hv hax => by
    obtain ⟨hb, hvm, hgv⟩ := hv
    obtain ⟨y, Y, hy, hvY, -⟩ := h.memG hwf hb hvm
    obtain ⟨fv, hfv, -, hop, -, hai⟩ := h.gvalue_f hgv
    rw [hop] at hax; rw [hai]
    exact hwf.boolAux y Y vid fv ⟨hy, hvY, hfv⟩ hax
  argListed := fun bid b vid v hv a ha => by
    obtain ⟨hb, hvm, hgv⟩ := hv
    obtain ⟨y, Y, hy, hvY, -⟩ := h.memG hwf hb hvm
    obtain ⟨fv, hfv, -, -, hargs, -⟩ := h.gvalue_f hgv
    rw [hargs] at ha
    exact h.listed_g hwf (hwf.argListed y Y vid fv ⟨hy, hvY, hfv⟩ a ha)
  ctrlListed := fun bid b hb x hx => by
    obtain ⟨hbm, hbb⟩ := hb
    rw [h.gblocks] at hbm
    by_cases hbr : bid ∈ run
    · by_cases hbc : bid = c
      · subst hbc
        obtain ⟨C, C', hC, hC', -, -, -, hc, -⟩ := h.gblock_c
        rw [hbb] at hC'; cases hC'
        rw [hc] at hx
        exact h.listed_g hwf (hwf.ctrlListed bid C ⟨hbm, hC⟩ x hx)
      · obtain ⟨Y', hY', -, -, -, -, hc⟩ := h.gblock_dead hbr hbc
        rw [hbb] at hY'; cases hY'
        rw [hc] at hx; simp at hx
    · obtain ⟨B, hB, hB'⟩ := h.gblock_out hwf hbm hbr
      rw [hbb] at hB'; cases hB'
      exact h.listed_g hwf (hwf.ctrlListed bid B ⟨hbm, hB⟩ x hx)
  entry := by
    rw [h.gblocks]
    rcases Classical.em (f.entry = b0) with he | he
    · rw [(h.entry).1 he]; exact h.inRun h.c_mem
    · rw [(h.entry).2 he]; exact hwf.entry
  entryPreds := fun b hb => by
    rcases Classical.em (f.entry = b0) with he | he
    · rw [(h.entry).1 he] at hb
      obtain ⟨C, C', -, hC', -, -, -, -, -, hp⟩ := h.gblock_c
      rw [hb] at hC'; cases hC'
      obtain ⟨B0, hB0, -⟩ := hwf.blockId b0 (h.inRun h.b0_mem)
      rw [hp, predsOf_eq hB0]
      exact hwf.entryPreds B0 (he ▸ hB0)
    · rw [(h.entry).2 he] at hb
      have hnr : f.entry ∉ run := fun hr => by
        obtain ⟨pre, x, suf, hr'⟩ := h.split_prev hr he
        exact (h.later (pre := pre ++ [x]) (suf := suf) (by rw [hr']; simp) (by simp)).1 rfl
      obtain ⟨B, hB, hB'⟩ := h.gblock_out hwf hwf.entry hnr
      rw [hb] at hB'; cases hB'
      exact hwf.entryPreds B hB

/-! ## Paths and use dominance -/

/-- A path of `f` along the run, from `b0` to a block `y` of the run. -/
theorem chain_reach {t : List ID} (h0 : Reach f b0 (b0 :: t)) :
    ∀ (n : Nat) (pre suf : List ID) (y : ID), pre.length = n → run = pre ++ y :: suf →
      Reach f y ((pre ++ [y]).reverse ++ t) := by
  intro n
  induction n with
  | zero =>
    intro pre suf y hl hr
    rw [List.length_eq_zero_iff] at hl
    subst hl
    obtain ⟨rest, hrest⟩ := h.run_cons
    rw [hr] at hrest
    simp only [List.nil_append, List.cons.injEq] at hrest
    rw [hrest.1]
    simpa using h0
  | succ n ih =>
    intro pre suf y hl hr
    have hpre : pre ≠ [] := by rintro rfl; simp at hl
    obtain ⟨pre0, x, rfl⟩ : ∃ pre0 x, pre = pre0 ++ [x] :=
      ⟨pre.dropLast, pre.getLast hpre, (List.dropLast_concat_getLast hpre).symm⟩
    have hr' : run = pre0 ++ x :: y :: suf := by rw [hr]; simp
    have hx := ih pre0 (y :: suf) x (by simpa using hl) hr'
    obtain ⟨X, Y, hX, -, -, hsu, -⟩ := h.link hr'
    have := Reach.step (e := ⟨y, 0⟩) hx hX (by rw [hsu]; simp)
    simpa using this

theorem chain_reach_c {t : List ID} (h0 : Reach f b0 (b0 :: t)) :
    Reach f c (run.reverse ++ t) := by
  have := h.chain_reach h0 run.dropLast.length run.dropLast [] c rfl h.run_last
  rwa [← h.run_last] at this

/-- **A path of `g` expands into a path of `f`** that visits no emptied block. -/
theorem reach_back (hwf : WF ce f) {ce' : CheckEnv} (hwg : WF ce' g) {x : ID} {l : List ID}
    (hr : Reach g x l) :
    (∀ z ∈ l, z ∉ run.dropLast) ∧ Reach f x (expand run c l) := by
  induction hr with
  | entry =>
    rcases Classical.em (f.entry = b0) with he | he
    · rw [(h.entry).1 he]
      refine ⟨fun z hz => by rw [List.mem_singleton] at hz; subst hz; exact h.c_not_dropLast, ?_⟩
      have h0 : Reach f b0 [b0] := he ▸ Reach.entry
      simpa [expand] using h.chain_reach_c (t := []) h0
    · rw [(h.entry).2 he]
      have hnr : f.entry ∉ run := fun hr => by
        obtain ⟨pre, x, suf, hr'⟩ := h.split_prev hr he
        exact (h.later (pre := pre ++ [x]) (suf := suf) (by rw [hr']; simp) (by simp)).1 rfl
      have hnc : f.entry ≠ c := fun he' => hnr (he' ▸ h.c_mem)
      refine ⟨fun z hz => by
        rw [List.mem_singleton] at hz; subst hz; exact fun hd => hnr (h.dropLast_mem hd), ?_⟩
      simpa [expand, hnc] using (Reach.entry : Reach f f.entry [f.entry])
  | @step p l pb e hr hpb he ih =>
    obtain ⟨hl, hrf⟩ := ih
    have hpm : p ∈ f.blocks := h.gblocks ▸ hr.mem hwg
    have hpd : p ∉ run.dropLast := hl p hr.mem_self
    -- the source block of `p` and the source edge of `e`
    obtain ⟨B, hB, hcase, e0, he0, rfl⟩ : ∃ B, f.block? p = some B ∧ (p ∉ run ∨ p = c) ∧
        ∃ e0 ∈ B.succs, e = redirect b0 c e0 := by
      by_cases hpr : p ∈ run
      · have hpc : p = c := Classical.byContradiction fun hne => hpd (h.mem_dropLast hpr hne)
        subst hpc
        obtain ⟨C, C', hC, hC', -, -, -, -, hs, -⟩ := h.gblock_c
        rw [hpb] at hC'; cases hC'
        rw [hs] at he
        obtain ⟨e0, he0, rfl⟩ := Array.mem_map.1 he
        exact ⟨C, hC, .inr rfl, e0, he0, rfl⟩
      · obtain ⟨B, hB, hB'⟩ := h.gblock_out hwf hpm hpr
        rw [hpb] at hB'; cases hB'
        obtain ⟨e0, he0, rfl⟩ := Array.mem_map.1 he
        exact ⟨B, hB, .inl hpr, e0, he0, rfl⟩
    have hstep := Reach.step hrf hB he0
    by_cases hb0 : e0.b = b0
    · rw [redirect_eq hb0]
      refine ⟨fun z hz => ?_, ?_⟩
      · rcases List.mem_cons.1 hz with rfl | hz
        · exact h.c_not_dropLast
        · exact hl z hz
      · rw [hb0] at hstep
        simpa [expand] using h.chain_reach_c hstep
    · rw [redirect_ne hb0]
      have hnr : e0.b ∉ run := fun hr' => hb0 (h.out_succ hwf hpm hcase hB he0 hr')
      have hnc : e0.b ≠ c := fun he' => hnr (he' ▸ h.c_mem)
      refine ⟨fun z hz => ?_, by simpa [expand, hnc] using hstep⟩
      rcases List.mem_cons.1 hz with rfl | hz
      · exact fun hd => hnr (h.dropLast_mem hd)
      · exact hl z hz

/-- A block of an expanded path: a block of the run means `c` is on the path. -/
theorem mem_expand {l : List ID} (hl : ∀ z ∈ l, z ∉ run.dropLast) {y : ID}
    (hy : y ∈ expand run c l) : (y ∈ run → c ∈ l) ∧ (y ∉ run → y ∈ l) := by
  induction l with
  | nil => simp [expand] at hy
  | cons z l ih =>
    have hl' : ∀ z ∈ l, z ∉ run.dropLast := fun z' hz' => hl z' (List.mem_cons_of_mem _ hz')
    simp only [expand, List.mem_append] at hy
    rcases hy with hy | hy
    · by_cases hzc : z = c
      · rw [if_pos hzc, List.mem_reverse] at hy
        exact ⟨fun _ => hzc ▸ List.mem_cons_self, fun hn => absurd hy hn⟩
      · rw [if_neg hzc, List.mem_singleton] at hy
        subst hy
        refine ⟨fun hr => absurd (h.mem_dropLast hr hzc) (hl y List.mem_cons_self),
          fun _ => List.mem_cons_self⟩
    · obtain ⟨h1, h2⟩ := ih hl' hy
      exact ⟨fun hr => List.mem_cons_of_mem _ (h1 hr), fun hn => List.mem_cons_of_mem _ (h2 hn)⟩

/-- The block of a listed value in `g`: `c` for the run's blocks, else unchanged. -/
theorem blockOf_g (hwf : WF ce f) {a : ID} (ha : Listed f a) :
    (blockOf f a ∈ run → blockOf g a = c) ∧ (blockOf f a ∉ run → blockOf g a = blockOf f a) := by
  obtain ⟨y, Y, hy, hvY⟩ := ha
  obtain ⟨fv, hfv, -, hblk⟩ := hwf.valueId y Y hy a hvY
  have hbf : blockOf f a = y := by unfold blockOf; rw [hfv]; exact hblk
  rw [hbf]
  rcases h.gvalue a with ⟨y', hy', hay', fv', gv, -, hg, -, hgb⟩ | ⟨hout, he⟩
  · obtain ⟨Y', hY', hvY'⟩ := valsOf_mem.1 hay'
    have := hwf.valueOnce y Y y' Y' hy ⟨h.inRun hy', hY'⟩ a hvY hvY'
    subst this
    refine ⟨fun _ => by unfold blockOf; rw [hg]; exact hgb, fun hn => absurd hy' hn⟩
  · refine ⟨fun hyr => absurd (valsOf_mem.2 ⟨Y, hy.2, hvY⟩) (hout y hyr), fun _ => ?_⟩
    rw [← hbf]; unfold blockOf; rw [he]

theorem proj (hwf : WF ce f) {a : ID} (ha : Listed f a) {l : List ID}
    (hl : ∀ z ∈ l, z ∉ run.dropLast) (hm : blockOf f a ∈ expand run c l) : blockOf g a ∈ l := by
  obtain ⟨h1, h2⟩ := h.blockOf_g hwf ha
  obtain ⟨m1, m2⟩ := h.mem_expand hl hm
  by_cases hr : blockOf f a ∈ run
  · rw [h1 hr]; exact m1 hr
  · rw [h2 hr]; exact m2 hr

/-- **Use dominance is kept.** -/
theorem useDom_pres (hwf : WF ce f) (hu : UseDom f) : UseDom g := by
  have hwg := h.wf_pres hwf
  intro bid b hbm hbb
  rw [h.gblocks] at hbm
  by_cases hbr : bid ∈ run
  · by_cases hbc : bid = c
    · subst hbc
      obtain ⟨C, C', hC, hC', -, hvals, -, hc, -, hp⟩ := h.gblock_c
      rw [hbb] at hC'; cases hC'
      -- a value of `c` in `g` is a value of a block `y` of the run in `f`
      have hsrc : ∀ vid ∈ b.values, ∃ y Y, y ∈ run ∧ f.block? y = some Y ∧ vid ∈ Y.values := by
        intro vid hv
        have : vid ∈ b.values.toList := Array.mem_toList_iff.2 hv
        rw [hvals, List.mem_flatMap] at this
        obtain ⟨y, hy, hvy⟩ := this
        obtain ⟨Y, hY, hvY⟩ := valsOf_mem.1 hvy
        exact ⟨y, Y, hy, hY, hvY⟩
      refine ⟨fun l hl vid hv v hgv hphi a ha => ?_, fun l hl x hx => ?_,
        fun vid hv v hgv hphi i a e l ha he hl => ?_⟩
      · obtain ⟨hl0, hrf⟩ := h.reach_back hwf hwg hl
        obtain ⟨y, Y, hy, hY, hvY⟩ := hsrc vid hv
        obtain ⟨fv, hfv, -, hop, hargs, -⟩ := h.gvalue_f hgv
        rw [hop] at hphi; rw [hargs] at ha
        obtain ⟨t, rfl⟩ := hl.head
        have hye : y ∈ expand run bid (bid :: t) := by
          simp [expand, hy]
        obtain ⟨pre, t', ht, hrt⟩ := hrf.suffix hye
        have := (hu y Y (h.inRun hy) hY).1 t' hrt vid hvY fv hfv hphi a ha
        have hla := hwf.argListed y Y vid fv ⟨⟨h.inRun hy, hY⟩, hvY, hfv⟩ a ha
        exact h.proj hwf hla hl0 (by rw [ht]; exact List.mem_append_right _ this)
      · obtain ⟨hl0, hrf⟩ := h.reach_back hwf hwg hl
        rw [hc] at hx
        have := (hu bid C (h.inRun h.c_mem) hC).2.1 _ hrf x hx
        exact h.proj hwf (hwf.ctrlListed bid C ⟨h.inRun h.c_mem, hC⟩ x hx) hl0 this
      · obtain ⟨hl0, hrf⟩ := h.reach_back hwf hwg hl
        obtain ⟨y, Y, hy, hY, hvY⟩ := hsrc vid hv
        obtain ⟨fv, hfv, -, hop, hargs, -⟩ := h.gvalue_f hgv
        rw [hop] at hphi; rw [hargs] at ha
        have hy0 : y = b0 := by
          refine Classical.byContradiction fun hne => ?_
          obtain ⟨pre, x, suf, hr⟩ := h.split_prev hy hne
          obtain ⟨-, hlat⟩ := h.later (pre := pre ++ [x]) (suf := suf) (y := y)
            (by rw [hr]; simp) (by simp)
          obtain ⟨v', hv', hnp, -⟩ := hlat vid (valsOf_mem.2 ⟨Y, hY, hvY⟩)
          rw [hfv] at hv'; cases hv'
          exact hnp hphi
        subst hy0
        rw [hp, predsOf_eq hY] at he
        have := (hu y Y (h.inRun hy) hY).2.2 vid hvY fv hfv hphi i a e _ ha he hrf
        have hla := hwf.argListed y Y vid fv ⟨⟨h.inRun hy, hY⟩, hvY, hfv⟩ a
          (Array.mem_of_getElem? ha)
        exact h.proj hwf hla hl0 this
    · obtain ⟨Y', hY', -, hvals, -, -, hc⟩ := h.gblock_dead hbr hbc
      rw [hbb] at hY'; cases hY'
      refine ⟨fun l _ vid hv => by rw [hvals] at hv; simp at hv, fun l _ x hx => by
        rw [hc] at hx; simp at hx, fun vid hv => by rw [hvals] at hv; simp at hv⟩
  · obtain ⟨B, hB, hB'⟩ := h.gblock_out hwf hbm hbr
    rw [hbb] at hB'; cases hB'
    refine ⟨fun l hl vid hv v hgv hphi a ha => ?_, fun l hl x hx => ?_,
      fun vid hv v hgv hphi i a e l ha he hl => ?_⟩
    · obtain ⟨hl0, hrf⟩ := h.reach_back hwf hwg hl
      obtain ⟨fv, hfv, -, hop, hargs, -⟩ := h.gvalue_f hgv
      rw [hop] at hphi; rw [hargs] at ha
      have := (hu bid B hbm hB).1 _ hrf vid hv fv hfv hphi a ha
      exact h.proj hwf (hwf.argListed bid B vid fv ⟨⟨hbm, hB⟩, hv, hfv⟩ a ha) hl0 this
    · obtain ⟨hl0, hrf⟩ := h.reach_back hwf hwg hl
      have := (hu bid B hbm hB).2.1 _ hrf x hx
      exact h.proj hwf (hwf.ctrlListed bid B ⟨hbm, hB⟩ x hx) hl0 this
    · obtain ⟨hl0, hrf⟩ := h.reach_back hwf hwg hl
      obtain ⟨fv, hfv, -, hop, hargs, -⟩ := h.gvalue_f hgv
      rw [hop] at hphi; rw [hargs] at ha
      have := (hu bid B hbm hB).2.2 vid hv fv hfv hphi i a e _ ha he hrf
      exact h.proj hwf (hwf.argListed bid B vid fv ⟨⟨hbm, hB⟩, hv, hfv⟩ a
        (Array.mem_of_getElem? ha)) hl0 this

end PRel

end GoFV.Proof.FusePlain

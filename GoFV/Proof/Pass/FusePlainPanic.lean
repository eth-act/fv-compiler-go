import GoFV.Proof.Pass.FusePlainMerged

/-!
# fuseBlockPlain: a panic in the run

`merged_panic`: a panic of the source in a block `y` of the run (after the blocks before it) is
a panic of the fused block. The target's schedule lists before the panicking node only values
of earlier blocks (evaluated by the source), values of `y` the source evaluated before it
(`Order.transfer_rank`: the checker makes the fused schedule list `y`'s non-pure nodes in `y`'s
sequence, `seq_part`), and values of later blocks; those are pure (their non-pure nodes come
after `y`'s, `not_before_append`), no `Phi` or parameter read (`laterOK`), hence
speculation-safe, and their arguments are defined: in the run, or in a strict ancestor of `b0`
(`anc_run`, lemma (D)).
-/

namespace GoFV.Proof.FusePlain

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.Fuse GoFV.Opt.Fuse.Plain
  GoFV.Proof Dom

/-- Filtering a flattened list by one part's predicate keeps that part. -/
theorem flatMap_filter_one {L : ID → List ID} {p : ID → ID → Bool} {y : ID} :
    ∀ {l : List ID}, l.Nodup → y ∈ l → (∀ x ∈ l, ∀ z ∈ L x, p x z = true) →
      (∀ x ∈ l, x ≠ y → ∀ z, p x z = true → p y z = false) →
      (l.flatMap L).filter (p y) = L y
  | [], _, hy, _, _ => absurd hy List.not_mem_nil
  | x :: l, hnd, hy, hL, hd => by
    rw [List.flatMap_cons, List.filter_append]
    obtain ⟨hxl, hnd'⟩ := List.nodup_cons.1 hnd
    by_cases hxy : x = y
    · subst hxy
      have h1 : (L x).filter (p x) = L x :=
        List.filter_eq_self.2 fun z hz => hL x List.mem_cons_self z hz
      have h2 : (l.flatMap L).filter (p x) = [] := List.filter_eq_nil_iff.2 fun z hz => by
        obtain ⟨x', hx', hz'⟩ := List.mem_flatMap.1 hz
        have hne : x' ≠ x := fun h => hxl (h ▸ hx')
        rw [hd x' (List.mem_cons_of_mem _ hx') hne z (hL x' (List.mem_cons_of_mem _ hx') z hz')]
        decide
      rw [h1, h2, List.append_nil]
    · have hyl : y ∈ l := by
        rcases List.mem_cons.1 hy with h | h
        · exact absurd h.symm hxy
        · exact h
      have h1 : (L x).filter (p y) = [] := List.filter_eq_nil_iff.2 fun z hz => by
        rw [hd x List.mem_cons_self hxy z (hL x List.mem_cons_self z hz)]; decide
      rw [h1, List.nil_append]
      exact flatMap_filter_one hnd' hyl (fun x' hx' => hL x' (List.mem_cons_of_mem _ hx'))
        (fun x' hx' => hd x' (List.mem_cons_of_mem _ hx'))

theorem npAt_eq {f : Func} {y : ID} {Y : Block} (hY : f.block? y = some Y) :
    npAt f y = npOf f Y := by
  funext z; unfold npAt; rw [hY]

theorem npAt_mem {f : Func} {y z : ID} (h : npAt f y z = true) : z ∈ (valsOf f y).toList := by
  unfold npAt at h
  cases hY : f.block? y with
  | none => rw [hY] at h; cases h
  | some Y =>
    rw [hY] at h
    unfold npOf at h
    rw [Bool.and_eq_true] at h
    exact valsOf_mem.2 ⟨Y, hY, Array.contains_iff_mem.1 h.1⟩

variable {f g : Func} {run : List ID} {b0 c : ID}

namespace Setup

variable (S : Setup f g run b0 c)
include S

theorem np_disj {x y : ID} (hx : x ∈ run) (hy : y ∈ run) (hne : x ≠ y) (z : ID)
    (h : npAt f x z = true) : npAt f y z = false :=
  Bool.eq_false_iff.2 fun h' => hne (S.disj (S.runIn hx) (S.runIn hy) (npAt_mem h) (npAt_mem h'))

/-- **The fused schedule lists `y`'s non-pure nodes in `y`'s sequence.** -/
theorem seq_part {y : ID} (hy : y ∈ run) {oY : Array ID} (hoY : schedOf f y = some oY)
    {oT : List ID} (hT : oT.filter (fun z => run.any (npAt f · z)) = npSeq f run) :
    oT.filter (npAt f y) = oY.toList.filter (npAt f y) := by
  have e : oT.filter (npAt f y) = (oT.filter (fun z => run.any (npAt f · z))).filter (npAt f y) := by
    rw [List.filter_filter]
    refine List.filter_congr fun z _ => ?_
    cases h : npAt f y z with
    | false => rfl
    | true =>
      have : run.any (npAt f · z) = true := List.any_eq_true.2 ⟨y, hy, h⟩
      rw [this]; rfl
  rw [e, hT]
  unfold npSeq
  rw [flatMap_filter_one S.nodup hy (fun x _ z hz => (List.mem_filter.1 hz).2)
    (fun x hx hne z h => S.np_disj hx hy hne z h), hoY]
  rfl

/-- The dominator tree along the run: a block of the run is a tree block, and its ancestors are
blocks of the run or strict ancestors of `b0`. -/
theorem anc_run (htd : ((make f).depthOf b0).isSome) :
    ∀ (n : Nat) (pre suf : List ID) (y : ID), pre.length = n → run = pre ++ y :: suf →
      ((make f).depthOf y).isSome ∧
        ∀ a, Anc (make f) a y → a ∈ run ∨ (Anc (make f) a b0 ∧ a ≠ b0) := by
  have hp := S.cf.parents
  intro n
  induction n with
  | zero =>
    intro pre suf y hl hr
    rw [List.length_eq_zero_iff] at hl
    subst hl
    obtain ⟨rest, hrest⟩ := S.rel.run_cons
    rw [hr] at hrest
    simp only [List.nil_append, List.cons.injEq] at hrest
    obtain ⟨rfl, -⟩ := hrest
    refine ⟨htd, fun a ha => ?_⟩
    by_cases hab : a = y
    · exact .inl (hab ▸ S.rel.b0_mem)
    · exact .inr ⟨ha, hab⟩
  | succ n ih =>
    intro pre suf y hl hr
    have hpre : pre ≠ [] := by rintro rfl; simp at hl
    obtain ⟨pre0, x, rfl⟩ : ∃ pre0 x, pre = pre0 ++ [x] :=
      ⟨pre.dropLast, pre.getLast hpre, (List.dropLast_concat_getLast hpre).symm⟩
    have hr' : run = pre0 ++ x :: y :: suf := by rw [hr]; simp
    obtain ⟨hdx, hax⟩ := ih pre0 (y :: suf) x (by simpa using hl) hr'
    obtain ⟨X, Y, hX, hY, -, hsu, -⟩ := S.rel.link hr'
    have hxIn := S.runIn (x := x) (by rw [hr']; simp)
    obtain ⟨-, hdy, hup⟩ := edge S.cf hxIn hX hdx (e := ⟨y, 0⟩) (by rw [hsu]; simp)
    refine ⟨hdy, fun a ha => ?_⟩
    by_cases hay : a = y
    · exact .inl (by rw [hay, hr]; simp)
    · exact hax a (Anc.trans hp (ha.up hp hay) hup)

/-- An argument of a non-`Phi` of the run that is no value of the run is defined at `b0`'s
entry (lemma (D)). -/
theorem arg_def {env : Env} {tabs : Tables} {fr : Frame}
    (htd : ((make f).depthOf b0).isSome)
    (hdi : DInv env (Ctx.make tabs f) (fun a => Anc (make f) a b0 ∧ a ≠ b0) fr)
    {y : ID} (hy : y ∈ run) {Y : Block} (hY : f.block? y = some Y) {x : ID} (hxY : x ∈ Y.values)
    {fv : Value} (hfv : f.value? x = some fv) (hnp : fv.op ≠ .Phi) {a : ID} (ha : a ∈ fv.args)
    (hout : ∀ y' ∈ run, a ∉ (valsOf f y').toList) : ∃ r, fr.regs[a]? = some (some r) := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨pre, suf, hr⟩ := S.split_mem hy
  obtain ⟨hdy, hanc⟩ := S.anc_run htd pre.length pre suf y rfl hr
  have hu := uses S.cf (S.runIn hy) hY hdy hxY hfv hnp ha
  have hl : Listed f a := hwf.argListed y Y x fv ⟨⟨S.runIn hy, hY⟩, hxY, hfv⟩ a ha
  obtain ⟨v, B, hP, hvb, hB, haB, -⟩ := blockOf_listed hwf hl
  rcases hanc _ hu with hin | ⟨hA, hne⟩
  · exact absurd (valsOf_mem.2 ⟨B, hB, haB⟩) (hout _ hin)
  · obtain ⟨r, hr', -⟩ := hdi a v hP (by rw [hvb]; exact ⟨hA, hne⟩)
    exact ⟨r, hr'⟩

/-- **A panic in the run is a panic of the fused block** (see the module doc). -/
theorem merged_panic {tabs : Tables} {env : Env} {fr G : Frame} {i idx : Nat}
    {pre suf : List ID} {y : ID} (hr : run = pre ++ y :: suf)
    (hfs : fr.regs.size = f.valueTab.size) (htd : ((make f).depthOf b0).isSome)
    (hdi : DInv env (Ctx.make tabs f) (fun a => Anc (make f) a b0 ∧ a ≠ b0) fr)
    (hA : Acc env tabs f fr i b0 pre G) (hfirst : pre = [] → y = b0 ∧ idx = i)
    {Y : Block} (hY : f.block? y = some Y) {e : Panic} {m : Mem}
    (h : enterBlock env (Ctx.make tabs f) G Y idx = .panic e m) :
    ∃ C', g.block? c = some C' ∧ enterBlock env (Ctx.make tabs g) fr C' i = .panic e m := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  obtain ⟨hGf, hGs, hGo, hGv, hGp⟩ := hA
  have hyr : y ∈ run := by rw [hr]; simp
  have hyIn := S.runIn hyr
  obtain ⟨psS, oY, preo, r, posto, Gp, hpsS, hoY, hsplit, hpre, hrp, hGpf, hGps, hGpo, hGpv, hGpp,
    hrY, rv, hrv, hrnp, hrop⟩ := enter_panic_facts hwf hyIn hY (by rw [hGs, hfs]) h
  have hnd := S.nodup
  have hnd' := hnd
  rw [hr] at hnd'
  have hyp : y ∉ pre := fun hm => by
    rw [List.nodup_append] at hnd'
    exact hnd'.2.2 y hm y List.mem_cons_self rfl
  have hys : y ∉ suf := (List.nodup_cons.1 (List.nodup_append.1 hnd').2.1).1
  have hps : ∀ y1 ∈ pre, ∀ y2 ∈ suf, y1 ≠ y2 := fun y1 h1 y2 h2 heq => by
    rw [List.nodup_append] at hnd'
    exact hnd'.2.2 y1 h1 y2 (List.mem_cons_of_mem _ h2) heq
  have hvY : ∀ z, z ∈ (valsOf f y).toList ↔ z ∈ Y.values := fun z => by
    rw [valsOf_eq hY, Array.mem_toList_iff]
  -- values of other blocks of the run are not `y`'s
  have hoth : ∀ y' ∈ run, y' ≠ y → ∀ z ∈ (valsOf f y').toList, z ∉ Y.values :=
    fun y' hy' hne z hz hzY => hne (S.disj (S.runIn hy') hyIn hz ((hvY z).2 hzY))
  have hGpfr : Gp = { fr with regs := Gp.regs } := frame_trans hGpf hGf
  -- `Gp` as a source frame of the run
  have hHo : ∀ z, (∀ y' ∈ run, z ∉ (valsOf f y').toList) → Gp.regs[z]? = fr.regs[z]? :=
    fun z hz => by
      rw [hGpo z fun hzY => hz y hyr ((hvY z).2 hzY),
        hGo z fun y' hy' => hz y' (by rw [hr]; simp [hy'])]
  have hHp : ∀ x ∈ (valsOf f b0).toList, ∀ v, f.value? x = some v → v.op = .Phi →
      ∃ a r, v.args[i]? = some a ∧ fr.regs[a]? = some (some r) ∧
        Gp.regs[x]? = some (some (r.retype ((Ctx.make tabs f).tys[x]?.getD .other))) := by
    intro x hx v hv hp
    by_cases hpre0 : pre = []
    · obtain ⟨rfl, rfl⟩ := hfirst hpre0
      subst hpre0
      obtain ⟨a, r', ha, hra, hx'⟩ := hGpp x ((hvY x).1 hx) v hv hp
      exact ⟨a, r', ha, by rw [← hra, hGo a fun _ h => by simp at h], hx'⟩
    · have hb0pre : b0 ∈ pre := by
        obtain ⟨rest, hrest⟩ := S.rel.run_cons
        rw [hr] at hrest
        cases pre with
        | nil => exact absurd rfl hpre0
        | cons p pre => simp only [List.cons_append, List.cons.injEq] at hrest; simp [hrest.1]
      have hb0y : b0 ≠ y := fun h' => hyp (h' ▸ hb0pre)
      obtain ⟨a, r', ha, hra, hx'⟩ := hGp hb0pre x hx v hv hp
      exact ⟨a, r', ha, hra, by rw [hGpo x (hoth b0 S.rel.b0_mem hb0y x hx), hx']⟩
  obtain ⟨C', psT, oT, hC', hid', hpsT, hoT, ondT, otopoT, omemT, hszT, hT0⟩ :=
    S.targetPre (tabs := tabs) hfs hHo hHp
  have hcg := S.cInG
  have hownC := valuesOwn hwg hcg hC'
  have hndC := hwg.valuesNodup c C' ⟨hcg, hC'⟩
  have hownY := valuesOwn hwf hyIn hY
  have hndY := hwf.valuesNodup y Y ⟨hyIn, hY⟩
  -- the checker's sequence of non-pure nodes
  have hT : oT.toList.filter (fun z => run.any (npAt f · z)) = npSeq f run := by
    obtain ⟨-, C2, oT2, -, hC2, -, -, -, -, -, -, hoT2, hT2⟩ := S.rel.merged
    rw [hC'] at hC2; cases hC2
    rw [hoT] at hoT2; cases hoT2
    exact hT2
  have hsY : schedOf f y = some oY := by unfold schedOf; rw [hY]; exact hoY
  -- the panicking node in the target's schedule
  obtain ⟨grv, hgrv, -, hgrop, hgrargs⟩ := (S.rel.value_same r).2 rv hrv
  obtain ⟨rv', hrv', hrid, -⟩ := hwf.valueId y Y ⟨hyIn, hY⟩ r hrY
  rw [hrv] at hrv'; cases hrv'
  have hrT : r ∈ oT.toList := (omemT r).2 ⟨(S.merged_mem hC' r).2 ⟨y, hyr, (hvY r).2 hrY⟩, grv,
    hgrv, by rw [hgrop]; exact hrnp⟩
  obtain ⟨pre', post', hsplitT⟩ := List.append_of_mem hrT
  have hspecS := schedule_spec hoY
  have hspecT := schedule_spec hoT
  have hk : oY.toList[preo.length]? = some r := by rw [hsplit]; simp
  have hk' : oT.toList[pre'.length]? = some r := by rw [hsplitT]; simp
  have hpreT : ∀ x ∈ pre', x ∈ oT.toList := fun x hx => by rw [hsplitT]; simp [hx]
  have htopo' : TopoRem (argsF (Ctx.make tabs g).f) (pre' ++ r :: post') := hsplitT ▸ otopoT
  -- `y`'s nodes in the target
  have hnodeY : ∀ x, NodeIn (schedNodes f Y).toList x ↔
      x ∈ Y.values ∧ ∃ v, f.value? x = some v ∧ v.op ≠ .Phi := fun x => nodeIn_schedNodes hownY
  have hnodeT : ∀ x, NodeIn (schedNodes g C').toList x ↔
      x ∈ C'.values ∧ ∃ v, g.value? x = some v ∧ v.op ≠ .Phi := fun x => nodeIn_schedNodes hownC
  have hYsem : ∀ x ∈ Y.values, ∀ fv, f.value? x = some fv → fv.op ≠ .Phi →
      ∃ gv, g.value? x = some gv ∧ gv.op = fv.op ∧ gv.args = fv.args := fun x _ fv hfv _ => by
    obtain ⟨gv, hgv, -, hop, hargs⟩ := (S.rel.value_same x).2 fv hfv
    exact ⟨gv, hgv, hop, hargs⟩
  have hsubN : ∀ x, NodeIn (schedNodes f Y).toList x → NodeIn (schedNodes g C').toList x := by
    intro x hx
    obtain ⟨hxY, fv, hfv, hnp⟩ := (hnodeY x).1 hx
    obtain ⟨gv, hgv, hop, -⟩ := hYsem x hxY fv hfv hnp
    exact (hnodeT x).2 ⟨(S.merged_mem hC' x).2 ⟨y, hyr, (hvY x).2 hxY⟩, gv, hgv,
      by rw [hop]; exact hnp⟩
  have hargsN : ∀ x, NodeIn (schedNodes f Y).toList x →
      argsOf (schedNodes g C').toList x = argsOf (schedNodes f Y).toList x := by
    intro x hx
    obtain ⟨hxY, fv, hfv, hnp⟩ := (hnodeY x).1 hx
    obtain ⟨gv, hgv, hop, hargs⟩ := hYsem x hxY fv hfv hnp
    rw [argsOf_schedNodes hownY hndY hxY hfv hnp,
      argsOf_schedNodes hownC hndC ((S.merged_mem hC' x).2 ⟨y, hyr, (hvY x).2 hxY⟩) hgv
        (by rw [hop]; exact hnp), hargs]
  have hseq := S.seq_part hyr hsY hT
  rw [npAt_eq hY, ← npIn_schedNodes hownY hndY] at hseq
  have hrnpY : npIn (schedNodes f Y).toList r = true := by
    rw [npIn_schedNodes hownY hndY]
    simp [npOf, hrY, hrv, hrnp, prio_panicking hrop]
  have htr := Order.transfer_rank hspecS.topo hspecS.pureFirst hspecT.topo (fun _ => npIn_iff)
    hseq.symm hk hk' hrnpY (fun a z ha hz haz hz' =>
      .direct (hsubN a ha) (.arg (hsubN a ha) hz' (by rw [hargsN z hz]; exact haz)))
  -- the later blocks' values are free
  let F : ID → Prop := fun x => ∃ y' ∈ suf, x ∈ (valsOf f y').toList
  have hargsT : ∀ x gv, g.value? x = some gv → argsF (Ctx.make tabs g).f x = gv.args.toList :=
    fun x gv hgv => argsF_of hgv
  -- a non-`Phi` of `y` or an earlier block reads no later value
  have hreadsPre : ∀ y' ∈ pre ++ [y], ∀ x ∈ (valsOf f y').toList, ∀ fv, f.value? x = some fv →
      fv.op ≠ .Phi → ∀ a ∈ fv.args, ¬ F a ∧ (y' ≠ y → a ∉ Y.values) := by
    intro y' hy' x hx fv hfv hnp a ha
    rcases List.mem_append.1 hy' with hy' | hy'
    · obtain ⟨p1, p2, hp⟩ := List.append_of_mem hy'
      have hr2 : run = p1 ++ y' :: (p2 ++ y :: suf) := by rw [hr, hp]; simp
      refine ⟨fun ⟨y'', hy'', ha''⟩ => S.rel.reads hr2 hx hfv hnp ha (by simp [hy'']) ha'',
        fun _ haY => S.rel.reads hr2 hx hfv hnp ha (y := y) (by simp) ((hvY a).2 haY)⟩
    · rw [List.mem_singleton] at hy'; subst hy'
      exact ⟨fun ⟨y'', hy'', ha''⟩ => S.rel.reads hr hx hfv hnp ha hy'' ha'', fun h' => absurd rfl h'⟩
  -- no non-pure node of a later block comes before `r` in the target
  have hnotroot : ∀ x ∈ pre', ∀ y' ∈ suf, x ∈ (valsOf f y').toList → ∀ fv, f.value? x = some fv →
      isRoot fv.op = false := by
    intro x hx y' hy' hxy' fv hfv
    cases hiso : isRoot fv.op with
    | false => rfl
    | true =>
      exfalso
      have hy'r : y' ∈ run := by rw [hr]; simp [hy']
      obtain ⟨Y', hY', hxY'⟩ := valsOf_mem.1 hxy'
      have hy'b : y' ≠ b0 := fun h' => by
        obtain ⟨rest, hrest⟩ := S.rel.run_cons
        rw [hr] at hrest
        cases pre with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at hrest
          exact hys (hrest.1 ▸ h' ▸ hy')
        | cons p pre =>
          simp only [List.cons_append, List.cons.injEq] at hrest
          exact hps p (by simp) y' hy' (hrest.1.trans h'.symm)
      have hxnp : npAt f y' x = true := by
        rw [npAt_eq hY']
        simp [npOf, hxY', hfv, (S.later_noPhi hy'r hy'b hxy' hfv).1, prio_root hiso]
      have hrnp' : npAt f y r = true := by
        rw [npAt_eq hY]; simp [npOf, hrY, hrv, hrnp, prio_panicking hrop]
      obtain ⟨jx, hjx⟩ := List.getElem?_of_mem hx
      have hjl : jx < pre'.length := (List.getElem?_eq_some_iff.1 hjx).1
      have hb : Order.Before oT.toList x r :=
        ⟨jx, pre'.length, hjl, by rw [hsplitT, List.getElem?_append_left hjl]; exact hjx, hk'⟩
      rw [← Order.before_filter (fun z => run.any (npAt f · z))
        (List.any_eq_true.2 ⟨y', hy'r, hxnp⟩) (List.any_eq_true.2 ⟨y, hyr, hrnp'⟩), hT] at hb
      have hsplitR : npSeq f run = (pre ++ [y]).flatMap
          (fun x => ((schedOf f x).getD #[]).toList.filter (npAt f x)) ++
          suf.flatMap (fun x => ((schedOf f x).getD #[]).toList.filter (npAt f x)) := by
        unfold npSeq; rw [hr, show pre ++ y :: suf = (pre ++ [y]) ++ suf by simp,
          List.flatMap_append]
      rw [hsplitR] at hb
      refine not_before_append (hsplitR ▸ hT ▸ ondT.filter _)
        (List.mem_flatMap.2 ⟨y, by simp, by
          rw [hsY]; exact List.mem_filter.2 ⟨List.mem_of_getElem? hk, hrnp'⟩⟩)
        (fun hm => ?_) hb
      obtain ⟨x', hx', hxm⟩ := List.mem_flatMap.1 hm
      have hx'r : x' ∈ run := by
        rw [hr]
        rcases List.mem_append.1 hx' with h' | h'
        · exact List.mem_append_left _ h'
        · rw [List.mem_singleton] at h'; rw [h']; simp
      have hne : x' ≠ y' := fun h' => by
        subst h'
        rcases List.mem_append.1 hx' with h' | h'
        · exact hps _ h' _ hy' rfl
        · rw [List.mem_singleton] at h'; exact hys (h' ▸ hy')
      rw [S.np_disj hx'r hy'r hne x (List.mem_filter.1 hxm).2] at hxnp
      cases hxnp
  -- `MixOK` on the target's prefix
  have hmix : MixOK env (Ctx.make tabs g) Gp F pre' := by
    intro x hx
    obtain ⟨hxC, gv, hgv, hgnp⟩ := (omemT x).1 (hpreT x hx)
    obtain ⟨y', hy', hxy'⟩ := (S.merged_mem hC' x).1 hxC
    obtain ⟨Y', hY', hxY'⟩ := valsOf_mem.1 hxy'
    obtain ⟨fv, hfv, hfid, -⟩ := hwf.valueId y' Y' ⟨S.runIn hy', hY'⟩ x hxY'
    obtain ⟨gv', hgv', -, hop, hargs⟩ := (S.rel.value_same x).2 fv hfv
    rw [hgv] at hgv'; cases hgv'
    have hfnp : fv.op ≠ .Phi := fun h' => hgnp (hop ▸ h')
    have hy'' := hy'
    rw [hr] at hy''
    by_cases hys' : y' ∈ suf
    · -- a later block's value: speculation-safe
      have hF : F x := ⟨y', hys', hxy'⟩
      refine ⟨fun hnF => absurd hF hnF, fun _ g' _ hdef => ?_⟩
      have hy'b : y' ≠ b0 := fun h' => by
        have : b0 ∈ pre ++ [y] := by
          obtain ⟨rest, hrest⟩ := S.rel.run_cons
          rw [hr] at hrest
          cases pre with
          | nil => simp only [List.nil_append, List.cons.injEq] at hrest; simp [hrest.1]
          | cons p pre => simp only [List.cons_append, List.cons.injEq] at hrest; simp [hrest.1]
        rcases List.mem_append.1 this with h2 | h2
        · exact hps _ h2 _ hys' h'.symm
        · rw [List.mem_singleton] at h2; exact hys (h2 ▸ h' ▸ hys')
      obtain ⟨hl1, hl2, hl3⟩ := S.later_noPhi hy' hy'b hxy' hfv
      have hroot := hnotroot x hx y' hys' hxy' fv hfv
      rw [stepV_eq hgv]
      refine evalValue_specSafe ?_ fun a ha => hdef a (by
        rw [hargsT x gv hgv]; exact Array.mem_toList_iff.2 ha)
      rw [hop]
      simp [specSafeOp, hroot, hl1, hl2, hl3]
    · have hy3 : y' ∈ pre ++ [y] := by
        rcases List.mem_append.1 hy'' with h' | h'
        · exact List.mem_append_left _ h'
        · rcases List.mem_cons.1 h' with h' | h'
          · simp [h']
          · exact absurd h' hys'
      have hnF : ¬ F x := fun ⟨y2, hy2, hx2⟩ => hys' (by
        have := S.disj (S.runIn hy') (S.runIn (by rw [hr]; simp [hy2])) hxy' hx2
        exact this ▸ hy2)
      refine ⟨fun _ => ?_, fun hF => absurd hF hnF⟩
      have hrd := hreadsPre y' hy3 x hxy' fv hfv hfnp
      by_cases hyy : y' = y
      · subst hyy
        -- `x` is a node of `y` listed before `r`: the source evaluated it
        obtain ⟨jx, hjx⟩ := List.getElem?_of_mem hx
        have hjl : jx < pre'.length := (List.getElem?_eq_some_iff.1 hjx).1
        obtain ⟨i', hi', hix⟩ := htr jx x hjl
          (by rw [hsplitT, List.getElem?_append_left hjl]; exact hjx)
          ((hnodeY x).2 ⟨(hvY x).1 hxy', fv, hfv, hfnp⟩)
        rw [hsplit, List.getElem?_append_left hi'] at hix
        obtain ⟨v, r', hv, hr', hev⟩ := hGpv x (List.mem_of_getElem? hix)
        rw [hfv] at hv; cases hv
        refine ⟨r', hr', fun g' hg' hag _ => ?_⟩
        rw [stepV_eq hgv, S.eval_same hfv hgv hfid hg' fun a ha => hag a (by
          rw [hargsT x gv hgv, hargs]; exact Array.mem_toList_iff.2 ha) (hrd a ha).1]
        exact hev
      · -- a value of an earlier block
        have hy'p : y' ∈ pre := by
          rcases List.mem_append.1 hy3 with h' | h'
          · exact h'
          · exact absurd (List.mem_singleton.1 h') hyy
        obtain ⟨r', hr', hev⟩ := hGv y' hy'p x hxy' fv hfv hfnp
        refine ⟨r', by rw [hGpo x (hoth y' hy' hyy x hxy'), hr'], fun g' hg' hag _ => ?_⟩
        rw [stepV_eq hgv, S.eval_same hfv hgv hfid (frame_trans hg' hGpf) fun a ha => by
          rw [hag a (by rw [hargsT x gv hgv, hargs]; exact Array.mem_toList_iff.2 ha)
            (hrd a ha).1, hGpo a ((hrd a ha).2 hyy)]]
        exact hev
  -- every argument outside the schedule has a register
  have hSd : ∀ a, a ∉ oT.toList → (∃ x ∈ oT.toList, a ∈ argsF (Ctx.make tabs g).f x) →
      ∃ z, (setPhis psT fr.regs)[a]? = some (some z) := by
    rintro a ha ⟨x, hx, hax⟩
    rw [hT0 a ha]
    by_cases hin : ∃ y' ∈ run, a ∈ (valsOf f y').toList
    · have haC := (S.merged_mem hC' a).2 hin
      obtain ⟨gv, hgv, -, -⟩ := hwg.valueId c C' ⟨hcg, hC'⟩ a haC
      have hgph : gv.op = .Phi := Classical.byContradiction fun hne =>
        ha ((omemT a).2 ⟨haC, gv, hgv, hne⟩)
      obtain ⟨hab, fv, hfv, hfph, -, -⟩ := S.merged_phi hC' haC hgv hgph
      obtain ⟨-, z, -, -, hz⟩ := hHp a hab fv hfv hfph
      exact ⟨_, hz⟩
    · have hout : ∀ y' ∈ run, a ∉ (valsOf f y').toList := fun y' hy' h' => hin ⟨y', hy', h'⟩
      rw [hHo a hout]
      obtain ⟨hxC, gv, hgv, hgnp⟩ := (omemT x).1 hx
      obtain ⟨y', hy', hxy'⟩ := (S.merged_mem hC' x).1 hxC
      obtain ⟨Y', hY', hxY'⟩ := valsOf_mem.1 hxy'
      obtain ⟨fv, hfv, -, -⟩ := hwf.valueId y' Y' ⟨S.runIn hy', hY'⟩ x hxY'
      obtain ⟨gv', hgv', -, hop, hargs⟩ := (S.rel.value_same x).2 fv hfv
      rw [hgv] at hgv'; cases hgv'
      exact S.arg_def htd hdi hy' hY' hxY' hfv (fun h' => hgnp (hop ▸ h'))
        (by rw [hargsT x gv hgv] at hax; rw [← hargs]; exact Array.mem_toList_iff.1 hax) hout
  have hGps' : Gp.regs.size = (Ctx.make tabs g).f.valueTab.size := by
    show Gp.regs.size = g.valueTab.size
    rw [hGps, hGs, hfs, S.gsize]
  have hpanT := evalAll_mix_panic (F := F) (post := post')
    (S := fun a => a ∉ oT.toList ∧ ∃ x ∈ oT.toList, a ∈ argsF (Ctx.make tabs g).f x)
    (g := { fr with regs := setPhis psT fr.regs }) hGps' hmix
    (Dead.refOK_of_topo (topoRem_prefix htopo') fun x hx a ha hna => ⟨fun haT =>
        hna (topoRem_arg_prefix htopo' x hx a ha (hsplitT ▸ haT)), x, hpreT x hx, ha⟩)
    (fun a ha _ => hT0 a ha.1) (fun a ha => hSd a ha.1 ha.2)
    (by rw [hGpfr])
    (by show (setPhis psT fr.regs).size = Gp.regs.size; rw [hszT, hGps, hGs])
    (fun a ha => by
      by_cases haT : a ∈ oT.toList
      · rw [hsplitT] at haT
        rcases List.mem_append.1 haT with h' | h'
        · exact .inr h'
        · exact absurd h' (CopyElim.topoRem_at htopo' a ha)
      · exact .inl ⟨haT, r, hrT, ha⟩)
    (fun g' hg' hag' _ => by
      have hsrc : stepV env (Ctx.make tabs f) Gp r = .panic e m := hrp
      rw [stepV_eq hrv] at hsrc
      rw [stepV_eq hgrv, S.eval_same hrv hgrv hrid hg' fun a ha => hag' a (by
        rw [hargsT r grv hgrv, hgrargs]; exact Array.mem_toList_iff.2 ha)
        (hreadsPre y (by simp) r ((hvY r).2 hrY) rv hrv hrnp a ha).1]
      exact hsrc)
  refine ⟨C', hC', ?_⟩
  rw [enterBlock_eq, hpsT]
  change (Res.ofOption _ ((Ctx.make tabs g).sched[C'.id]?).join).bind _ = _
  rw [hid', sched_of_block hC', hoT]
  change evalAll env (Ctx.make tabs g) _ oT.toList = _
  rw [hsplitT]
  exact hpanT

end Setup

end GoFV.Proof.FusePlain

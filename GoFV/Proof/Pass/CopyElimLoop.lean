import GoFV.Proof.Pass.CopyElimCtrl
import Std.Tactic.Do

/-!
# copyelim's output satisfies `CopyRel`

`copyelim_rel`: on an input that passes `check` and satisfies `CopyFrag`, copyelim's output is
related to its input by `CopyRel` (`GoFV.Proof.Pass.CopyElimRel`); `copyelim_rel_of_inv`: the
same when copyelim runs on a function already in the invariant `Inv` relative to the input.
`phielim` ends with `Inv` and every argument of a listed value a non-copy (`phielim_spec_of`);
the control step replaces each copy control by its argument (`Ctl`, `copyelim_ctl`);
`rel_of_ctl` reads `CopyRel` off both.
-/

open Std.Do

set_option mvcgen.warning false

namespace GoFV.Proof.CopyElim

open GoFV.SSA GoFV.SSA.DomCert GoFV.Opt GoFV.Proof

/-- The controls of block `bid` once the blocks `pre` and the first `k` controls of `b` are done. -/
def ctlFn (G : Func) (pre : List ID) (b : ID) (k : Nat) (bid : ID) : Array ID → Array ID :=
  if bid ∈ pre then (·.map (rc G)) else if bid = b then pmap G k else id

/-- The invariant of the control step (`G`: `phielim`'s result). -/
def Ctl (G : Func) (pre : List ID) (b : ID) (k : Nat) (H : Func) : Prop :=
  cfgView H = cfgView G ∧ vw H = vw G ∧ cskel H = cskel G ∧
    ∀ bid blk, G.block? bid = some blk → H.block? bid = some (setCtl (ctlFn G pre b k bid) blk)

theorem ctlFn_zero (G : Func) (pre : List ID) (b b' : ID) :
    ctlFn G pre b 0 = ctlFn G pre b' 0 := by
  funext bid cs
  unfold ctlFn
  have hz : pmap G 0 cs = cs := pmap_zero G cs
  split
  · rfl
  · split <;> split <;> simp [hz]

theorem setCtl_id (blk : Block) : setCtl id blk = blk := rfl

theorem setCtl_setCtl (h1 h2 : Array ID → Array ID) (blk : Block) :
    setCtl h2 (setCtl h1 blk) = setCtl (h2 ∘ h1) blk := rfl

section
variable {tabs : Tables} {ce : CheckEnv} {f G : Func}

theorem skel_parts (hI : Inv tabs f G) :
    G.entry = f.entry ∧ G.bidLast = f.bidLast ∧ G.blocks = f.blocks ∧ G.blockTab = f.blockTab ∧
      G.vidLast = f.vidLast ∧ G.ownAux = f.ownAux ∧ G.valueTab.size = f.valueTab.size := by
  have := hI.skel
  simpa only [CopyElim.skel, Prod.mk.injEq] using this

/-- `CopyRel` from the end state of the control step. -/
theorem rel_of_ctl (hwf : WF ce f) (hI : Inv tabs f G) (hset : Settled f (vw G)) {H : Func}
    (hC : Ctl G G.blocks.toList 0 0 H) (names : Array (SlotRef × Array ID)) :
    CopyRel tabs f { H with names } := by
  obtain ⟨he, hbl, hbs, hbt, -, hown, hvs⟩ := skel_parts hI
  obtain ⟨hcfg, hvw, hcs, hblk⟩ := hC
  simp only [cskel, Prod.mk.injEq] at hcs
  have hg : vw { H with names } = vw G := hvw
  have hgb : ∀ bid, ({ H with names } : Func).block? bid = H.block? bid := fun _ => rfl
  have hGb : ∀ bid, G.block? bid = f.block? bid := by
    intro bid; unfold Func.block?; rw [hbt]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show cfgView H = cfgView f
    rw [hcfg]; unfold cfgView; rw [he, hbl, hbs, hbt]
  · show H.ownAux = f.ownAux
    rw [hcs.2.2.2.1, hown]
  · show H.valueTab.size = f.valueTab.size
    rw [hcs.2.2.2.2.1, hvs]
  · intro bid hm _ fb hfb
    have hmG : bid ∈ G.blocks.toList := by rw [hbs]; simpa using hm
    have := hblk bid fb (by rw [hGb]; exact hfb)
    rw [hgb, this]
    refine ⟨_, rfl, rfl, rfl, ?_, ?_⟩
    · simp [setCtl, ctlFn, hmG]
    · intro k c hc
      refine ⟨rc G c, by simp [setCtl, ctlFn, hmG, hc], ?_⟩
      have hcl : Listed f c := hwf.ctrlListed bid fb ⟨hm, hfb⟩ c (Array.mem_of_getElem? hc)
      unfold rc
      split
      · rename_i hcop
        obtain ⟨r, n, hr⟩ := hI.acyc c hcl
        cases hr with
        | sink h0 => exact absurd (by simpa using hcop) (getV_cstep_none h0)
        | @step _ y _ n hy hs' =>
          obtain ⟨u, hu, -, ha⟩ := cstep_some_some hy
          rw [(getV_cstep_some hy).2]
          have hys : cstep (vw G) y = none := hset c hcl u hu y (by rw [ha]; simp)
          exact argRel_of_join hset hg hcl ⟨y, 1, 0, .step hy (.sink hys), .sink hys⟩ hys
      · exact .inl rfl
  · intro bid hm _ fb hfb x hx fv hfv
    have hxl : Listed f x := ⟨bid, fb, ⟨hm, hfb⟩, hx⟩
    obtain ⟨v, hv, hmode⟩ := hI.mode x hxl fv hfv
    have hv' : vw { H with names } x = some v := by rw [hg]; exact hv
    obtain ⟨gv, hgv, hop, hargs, hty, hblk', haux, hauxi⟩ := value_of_vw hv'
    obtain ⟨fv', hfv', hb', ht', -⟩ := hI.keep_some hv
    rw [hfv] at hfv'; cases hfv'
    refine ⟨gv, hgv, hblk'.trans hb', hty.trans ht', ?_⟩
    have hsk : ∀ c ∈ v.args, cstep (vw G) c = none := hset x hxl v hv
    have hal : ∀ a ∈ fv.args, Listed f a := hwf.argListed bid fb x fv ⟨⟨hm, hfb⟩, hx, hfv⟩
    cases hmode with
    | same h1 h2 h3 h4 h5 =>
      refine .same (hop.trans h1) (haux.trans h2) (hauxi.trans h3) (hargs ▸ h4) fun k a ha => ?_
      have hk : k < v.args.size := by rw [h4]; exact (Array.getElem?_eq_some_iff.1 ha).1
      refine ⟨v.args[k], by rw [hargs]; simp, ?_⟩
      have hc : v.args[k]? = some v.args[k] := by simp
      exact argRel_of_join hset hg (hal a (Array.mem_of_getElem? ha)) (h5 k a _ ha hc)
        (hsk _ (Array.getElem_mem hk))
    | phi w h1 h2 h3 h4 h5 =>
      refine .phi w h1 (hop.trans h2) (hargs.trans h3) fun a ha => ?_
      exact argRel_of_join hset hg (hal a ha) (h5 a ha) (hsk w (by rw [h3]; simp))
    | empty h1 h2 h3 => exact .empty h1 (hop.trans h2) (hargs.trans h3)
  · intro bid hm _ fb hfb x hx gv w hgv hop hargs
    have hxl : Listed f x := ⟨bid, fb, ⟨hm, hfb⟩, hx⟩
    have hvx : vw G x = some (strip gv) := by rw [← hg]; exact vw_of_value? hgv
    have hcx : cstep (vw G) x = some (some w) := cstep_of_copy hvx hop hargs
    obtain ⟨xv, wv, hxv, hwv, hty⟩ := hI.shape x hxl w hcx
    have hkw := hI.keep w
    rw [vw_of_value? hwv] at hkw
    cases hw : vw G w with
    | none => rw [hw] at hkw; cases hkw
    | some u =>
      rw [hw] at hkw
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hkw
      have hw' : vw { H with names } w = some u := by rw [hg]; exact hw
      obtain ⟨wv', hwv', -, -, hty', -⟩ := value_of_vw hw'
      obtain ⟨xv', hxv', -, hxt, -⟩ := hI.keep_some hvx
      rw [hxv] at hxv'; cases hxv'
      refine ⟨wv', hwv', .inl ?_⟩
      rw [hty', hkw.2.1]
      exact hty.trans (.of_eq (congrArg _ hxt.symm))

end

theorem ctlFn_ne (G : Func) (pre : List ID) (b : ID) (k k' : Nat) {bid : ID} (hb : bid ≠ b) :
    ctlFn G pre b k bid = ctlFn G pre b k' bid := by
  unfold ctlFn; simp [hb]

theorem setCtl_pmap_zero (G : Func) (blk : Block) : setCtl (pmap G 0) blk = blk := by
  unfold setCtl; rw [pmap_zero]

theorem ctl_init (G : Func) : Ctl G [] 0 0 G := by
  refine ⟨rfl, rfl, rfl, fun bid blk h => ?_⟩
  rw [h]
  unfold ctlFn
  simp only [List.not_mem_nil, ite_false]
  split
  · rw [setCtl_pmap_zero]
  · rfl

theorem ctl_getB {G H : Func} {pre : List ID} {b : ID} (hC : Ctl G pre 0 0 H) (hb : b ∉ pre)
    {blk : Block} (hblk : G.block? b = some blk) : H.getB b = blk := by
  have := hC.2.2.2 b blk hblk
  unfold Func.getB
  rw [this]
  unfold ctlFn
  simp only [hb, ite_false]
  split
  · rw [setCtl_pmap_zero]; rfl
  · rfl

theorem ctl_inner_init {G H : Func} {pre : List ID} {b : ID} (hC : Ctl G pre 0 0 H) :
    Ctl G pre b 0 H := by
  refine ⟨hC.1, hC.2.1, hC.2.2.1, fun bid blk h => ?_⟩
  rw [ctlFn_zero G pre b 0]
  exact hC.2.2.2 bid blk h

theorem ctl_copy {G H : Func} {pre : List ID} {b : ID} {k : Nat} (hC : Ctl G pre b k H)
    (hb : b ∉ pre) {blk : Block} (hblk : G.block? b = some blk) {cs : Array ID}
    (hcs : cs = blk.controls) (hk : k < cs.size)
    (hcop : ((H.getV cs[k]).op == .Copy) = true) :
    Ctl G pre b (k + 1) (H.replaceControl b k (H.getV cs[k]).args[0]!) := by
  subst hcs
  obtain ⟨hcfg, hvw, hcs, hblks⟩ := hC
  have hx : (H.getV blk.controls[k]).args[0]! = rc G blk.controls[k] := by
    obtain ⟨h1, h2⟩ := getV_congr hvw blk.controls[k]
    unfold rc
    rw [← h1, hcop, ite_eq_left rfl, h2]
  rw [hx]
  refine ⟨by rw [cfgView_replaceControl]; exact hcfg, by rw [vw_replaceControl]; exact hvw,
    by rw [cskel_replaceControl]; exact hcs, fun bid blk' hb' => ?_⟩
  rw [block?_replaceControl]
  split
  · rename_i hbb
    subst hbb
    rw [hblk] at hb'; cases hb'
    rw [hblks b blk hblk, Option.map_some]
    congr 1
    unfold setCtl ctlFn
    simp only [hb, ite_false, ite_true]
    rw [pmap_succ G blk.controls hk]
  · rename_i hne
    rw [hblks bid blk' hb', ctlFn_ne G pre b k (k + 1) (fun h => hne h.symm)]

theorem ctl_noncopy {G H : Func} {pre : List ID} {b : ID} {k : Nat} (hC : Ctl G pre b k H)
    (hb : b ∉ pre) {blk : Block} (hblk : G.block? b = some blk) {cs : Array ID}
    (hcs : cs = blk.controls) (hk : k < cs.size)
    (hcop : ¬((H.getV cs[k]).op == .Copy) = true) : Ctl G pre b (k + 1) H := by
  subst hcs
  obtain ⟨hcfg, hvw, hcs, hblks⟩ := hC
  have hx : rc G blk.controls[k] = blk.controls[k] := by
    obtain ⟨h1, -⟩ := getV_congr hvw blk.controls[k]
    unfold rc
    rw [← h1]
    simp only [Bool.not_eq_true] at hcop
    rw [hcop]; rfl
  refine ⟨hcfg, hvw, hcs, fun bid blk' hb' => ?_⟩
  by_cases hbb : bid = b
  · subst hbb
    rw [hblk] at hb'; cases hb'
    rw [hblks bid blk hblk]
    unfold ctlFn
    simp only [hb, ite_false, ite_true]
    unfold setCtl
    rw [pmap_succ_same G blk.controls hk hx]
  · rw [hblks bid blk' hb', ctlFn_ne G pre b k (k + 1) hbb]

theorem ctl_inner_done {G H : Func} {pre : List ID} {b : ID} {blk : Block}
    (hblk : G.block? b = some blk) (hC : Ctl G pre b blk.controls.size H) :
    Ctl G (pre ++ [b]) 0 0 H := by
  obtain ⟨hcfg, hvw, hcs, hblks⟩ := hC
  refine ⟨hcfg, hvw, hcs, fun bid blk' hb' => ?_⟩
  rw [hblks bid blk' hb']
  congr 1
  by_cases hbb : bid = b
  · subst hbb
    rw [hblk] at hb'; cases hb'
    unfold ctlFn setCtl
    by_cases hp : bid ∈ pre
    · simp [hp]
    · simp [hp, pmap_full]
  · unfold ctlFn
    by_cases hp : bid ∈ pre
    · simp [hp]
    · simp only [hp, hbb, ite_false, List.mem_append, List.mem_singleton, or_false]
      split
      · rw [setCtl_pmap_zero]; rfl
      · rfl

/-- copyelim from a start `F` in the invariant: `phielim`'s result `G` (in the invariant, with
settled arguments) and the end state `H` of the control step. -/
theorem copyelim_ctl {ce : CheckEnv} {tabs : Tables} {f F g : Func} (hwf : WF ce f)
    (hfrag : CopyFrag tabs f) (hI : Inv tabs f F) (h : copyelim tabs F = .ok g) :
    ∃ G H names, Inv tabs f G ∧ Settled f (vw G) ∧ Ctl G G.blocks.toList 0 0 H ∧
      g = { H with names } := by
  unfold copyelim at h
  obtain ⟨G, hph, h⟩ := CheckFacts.bind_ok h
  dsimp only at h
  obtain ⟨hI, hset⟩ := phielim_spec_of hwf hfrag hI hph
  suffices hx : ∃ H names, Ctl G G.blocks.toList 0 0 H ∧ g = { H with names } by
    obtain ⟨H, names, hC, rfl⟩ := hx
    exact ⟨G, H, names, hI, hset, hC, rfl⟩
  obtain ⟨he, hbl, hbs, hbt, -, -, -⟩ := skel_parts hI
  have hnd : G.blocks.toList.Nodup := hbs ▸ hwf.blocksNodup
  -- facts about the block `b` being processed
  have hblock : ∀ {pre suf : List ID} {b : ID}, G.blocks.toList = pre ++ b :: suf →
      b ∉ pre ∧ ∃ blk, G.block? b = some blk := by
    intro pre suf b hxs
    have hn := hnd
    rw [hxs] at hn
    refine ⟨fun hb => (List.nodup_append.1 hn).2.2 b hb b List.mem_cons_self rfl, ?_⟩
    have hm : b ∈ f.blocks := by
      rw [← hbs, ← Array.mem_toList_iff, hxs]; simp
    obtain ⟨blk, hblk, -⟩ := hwf.blockId b hm
    exact ⟨blk, by unfold Func.block?; rw [hbt]; exact hblk⟩
  apply Except.of_wp_eq h
    (fun r => ∀ x, r = .ok x → ∃ H names, Ctl G G.blocks.toList 0 0 H ∧ x = { H with names })
    ?_ g rfl
  mvcgen
  case inv1 => exact ⇓⟨cur, H⟩ => ⌜Ctl G cur.prefix 0 0 H⌝
  case inv2 =>
    rename_i pre b suf hxs H0 hinv
    exact ⇓⟨cur, H⟩ => ⌜Ctl G pre b cur.prefix.length H⌝
  all_goals mleave
  case vc1 =>
    rename_i pre b suf hxs H0 hC0 pref cur suff hxs2 H hcop hC
    obtain ⟨hbp, blk, hblk⟩ := hblock hxs
    have hg0 := ctl_getB hC0 hbp hblk
    obtain ⟨rfl, hlt⟩ := range_cursor hxs2
    rw [List.length_append, List.length_singleton]
    exact ctl_copy hC hbp hblk (by rw [hg0]) hlt hcop
  case vc2 =>
    rename_i pre b suf hxs H0 hC0 pref cur suff hxs2 H hcop hC
    obtain ⟨hbp, blk, hblk⟩ := hblock hxs
    have hg0 := ctl_getB hC0 hbp hblk
    obtain ⟨rfl, hlt⟩ := range_cursor hxs2
    rw [List.length_append, List.length_singleton]
    exact ctl_noncopy hC hbp hblk (by rw [hg0]) hlt hcop
  case vc3 =>
    rename_i pre b suf hxs H0 hC0
    exact ctl_inner_init hC0
  case vc4 =>
    rename_i pre b suf hxs H0 hC0 r hC
    obtain ⟨hbp, blk, hblk⟩ := hblock hxs
    have hg0 := ctl_getB hC0 hbp hblk
    have hl : [:(H0.getB b).controls.size].toList.length = blk.controls.size := by
      rw [hg0]; simp [Std.Legacy.Range.toList]
    rw [hl] at hC
    exact ctl_inner_done hblk hC
  case vc6 => exact ctl_init G
  case vc7 =>
    rename_i r hC
    intro x hx
    cases hx
    exact ⟨_, _, hC, rfl⟩

/-- **copyelim from a start in the invariant satisfies `CopyRel` with the input.** -/
theorem copyelim_rel_of_inv {ce : CheckEnv} {tabs : Tables} {f F g : Func} (hwf : WF ce f)
    (hfrag : CopyFrag tabs f) (hI : Inv tabs f F) (h : copyelim tabs F = .ok g) :
    CopyRel tabs f g := by
  obtain ⟨G, H, names, hIG, hset, hC, rfl⟩ := copyelim_ctl hwf hfrag hI h
  exact rel_of_ctl hwf hIG hset hC names

/-- **copyelim's output satisfies `CopyRel`.** -/
theorem copyelim_rel {ce : CheckEnv} {tabs : Tables} {f g : Func}
    (hf : check ce f = .ok ()) (hfrag : CopyFrag tabs f) (h : copyelim tabs f = .ok g) :
    CopyRel tabs f g :=
  copyelim_rel_of_inv (check_wf hf) hfrag (inv_init (check_wf hf) hfrag) h

end GoFV.Proof.CopyElim

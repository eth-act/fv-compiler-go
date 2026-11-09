import GoFV.Proof.Pass.PhiNotRel
import GoFV.Proof.Pass.PhiSelSim

variable [GoFV.SSA.Sem.Addrs]

/-!
# `Phi`s of `Not`s refine their input (issue #69)

`pn_refines`: if `g` is `f` with `Phi`s `v` of `Not`s `Not x_j` turned `Not p` of fresh `Phi`s `p`
of the `x_j` (`RewriteCheck.pnRel`, `generic.rules:1068`), both checked, `g` refines `f` under
monotone contracts. Lock-step simulation (`runLoop_simE`) along the same edges, with `SimAt` at
block entries: the target's registers refine the source's (`Seg.RR`) and lemma (D) holds for the
block left (`CSE.Pre`). Entering a block along edge `i`, the source's `Phi` `v` takes the register
of its argument `Not x_i`, which lemma (D) re-evaluates from `x_i`'s register (`not_arg`), and
the target's fresh `p` takes `x_i`'s register: `v`'s register is refined by the `Not` of `p`'s
(`Fact`, `entry`). Both are `Phi`s, so neither changes in the block. The target's schedule is the
source's with the turned `Phi`s inserted (as `Not`s, after their fresh `Phi`'s block entry);
`loop` walks it: a turned `Phi` is a target-only step that restores the refinement of `v`'s
register (`eval_not`), every other value is unchanged and evaluates to a refinement on refined
arguments (`PhiSel.eval_ss`), and no argument is a turned `Phi` still to be evaluated (the
schedule is topological).
-/

namespace GoFV.Proof.PhiNot

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Opt GoFV.Opt.RewriteCheck
open GoFV.Proof.Seg (RR)

variable {env : Env} {tabs : Tables} {f g : Func}

/-! ## Evaluating `Not` -/

theorem evalOp_not {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val} {ty : Ty}
    (hop : v.op = .Not) : evalOp env ctx fr v argv ty = .ok (evalPure .Not ty v.auxInt v.aux argv) := by
  simp only [evalOp, frameVal, hop]; rfl

/-- The `Not` of a `bool`-typed value, through the `bool` retypes of the source's `Phi` and the
target's fresh `Phi`, is refined. -/
theorem not_ref {sx tx : Val} (h : Sem.Refines sx tx) (hs : sx.retype .bool = sx) :
    Sem.Refines (((Cmp.not [sx]).retype .bool).retype .bool)
      ((Cmp.not [tx.retype .bool]).retype .bool) := by
  rw [retype_idem]
  refine retype_mono _ ?_
  have h1 : Sem.Refines sx (tx.retype .bool) := by
    have := retype_mono .bool h
    rwa [hs] at this
  exact evalPure_mono .Not .bool 0 none (.cons h1 .nil)

/-- The fact a turned `Phi` `v` gives until the target evaluates its `Not`: `v`'s register in the
source is refined by the `Not` of the fresh `Phi`'s register in the target. -/
def Fact {v : ID} (d : PND tabs f g v) (S T : Frame) : Prop :=
  ∃ yv yp, S.regs[v]? = some (some yv) ∧ T.regs[d.p]? = some (some yp) ∧
    Sem.Refines yv ((Cmp.not [yp]).retype .bool)

/-- **A turned `Phi`** evaluates to the `Not` of its fresh `Phi`'s register. -/
theorem eval_not {v : ID} (d : PND tabs f g v) {T : Frame} {yp : Val}
    (hyp : T.regs[d.p]? = some (some yp)) :
    evalValue env (Ctx.make tabs g) T d.w = .ok ((Cmp.not [yp]).retype .bool) := by
  have hty : (Ctx.make tabs g).tys[d.w.id]?.getD .other = .bool := by
    rw [d.hwid, tys_of_value d.hw, Option.getD_some, d.hwt, d.hut]
  unfold evalValue
  rw [PhiSel.args_one d.hwsz d.hp]
  simp only [List.mapM_cons, List.mapM_nil, hyp, Option.join, bind, Res.bind, Res.ofOption, pure]
  rw [show (some (some yp)).bind id = some yp from rfl]
  simp only [evalOp_not d.hwop, hty]
  rfl

theorem phiStep_ok {ctx : Ctx} {fr : Frame} {i : Nat} {z : ID} {v : Value} {a : ID} {y : Val}
    (hv : ctx.f.value? z = some v) (hph : v.op = .Phi) (ha : v.args[i]? = some a)
    (hy : fr.regs[a]? = some (some y)) : ∃ o, phiStep ctx fr i z = .ok o := by
  refine ⟨some (z, y.retype (ctx.tys[z]?.getD .other)), ?_⟩
  unfold phiStep
  rw [hv]
  simp only [hph, beq_self_eq_true, ↓reduceIte, ha, hy]
  rfl

theorem phiStep_ok_none {ctx : Ctx} {fr : Frame} {i : Nat} {z : ID} {v : Value}
    (hv : ctx.f.value? z = some v) (hph : v.op ≠ .Phi) : ∃ o, phiStep ctx fr i z = .ok o := by
  refine ⟨none, ?_⟩
  unfold phiStep
  rw [hv]
  have : (v.op == .Phi) = false := by simpa using hph
  simp only [this, Bool.false_eq_true, ↓reduceIte]

/-! ## The block's schedule -/

/-- The relation along a block's target schedule, with `rest` still to be evaluated: the
target's registers refine the source's but at the turned `Phi`s of `rest`, whose facts hold. -/
structure Inv (tabs : Tables) (f g : Func) (rest : List ID) (S T : Frame) : Prop where
  sz : S.regs.size = f.valueTab.size
  szT : T.regs.size = g.valueTab.size
  frame : T = { S with regs := T.regs }
  rr : ∀ a v x, (a ∈ rest → pnOK tabs f g a = false) → f.value? a = some v →
    (g.value? a).isSome = true → S.regs[a]? = some (some x) →
    ∃ y, T.regs[a]? = some (some y) ∧ Sem.Refines x y
  fact : ∀ v ∈ rest, ∀ d : PND tabs f g v, Fact d S T

theorem Inv.rrAll {S T : Frame} (h : Inv tabs f g [] S T) : RR f g S.regs T.regs :=
  fun a v x hv hg hx => h.rr a v x (fun hm => absurd hm List.not_mem_nil) hv hg hx

/-- **The target's schedule**: the source evaluates it without the turned `Phi`s, the target
with them, keeping `Inv`. -/
theorem loop {ce ce' : CheckEnv} (hwf : WF ce f) (hwg : WF ce' g) (R : PNRel tabs f g)
    (hE : env.Mono) {bid : ID} {fb gb : Block} (hb : bid ∈ f.blocks)
    (hfb : f.block? bid = some fb) (hgb : g.block? bid = some gb)
    (hvals : gb.values.toList.filter (fun z => (f.value? z).isSome) = fb.values.toList)
    (hfresh : ∀ z ∈ gb.values, (f.value? z).isSome = true ∨ pnFresh tabs f g z = true) :
    ∀ (rest : List ID) (S T : Frame),
      (∀ z ∈ rest, z ∈ gb.values ∧ ∃ w, g.value? z = some w ∧ w.op ≠ .Phi) →
      rest.Nodup → TopoRem (argsF g) rest →
      Inv tabs f g rest S T →
      Res.Rel (Inv tabs f g [])
        (evalAll env (Ctx.make tabs f) S (rest.filter fun z => !pnOK tabs f g z))
        (evalAll env (Ctx.make tabs g) T rest)
  | [], S, T, _, _, _, hI => .ok hI
  | z :: rest, S, T, hmem, hnd, htopo, hI => by
    obtain ⟨hzg, w, hgw, hwph⟩ := hmem z List.mem_cons_self
    have hbg : bid ∈ g.blocks := by rw [CopyElim.cfgView_blocks R.cfg]; exact hb
    obtain ⟨w', hw', hwid, -⟩ := hwg.valueId bid gb ⟨hbg, hgb⟩ z hzg
    rw [hgw] at hw'; cases hw'
    have hzf : (f.value? z).isSome = true := by
      rcases hfresh z hzg with h | h
      · exact h
      · obtain ⟨v, zv, gb', -, -, -, ⟨d⟩, hdp⟩ := pnFresh_spec h
        have := d.hpv
        rw [hdp d, hgw] at this; cases this
        exact absurd d.hpphi hwph
    obtain ⟨fv, hfv⟩ := Option.isSome_iff_exists.1 hzf
    have hzfb : z ∈ fb.values := by
      rw [← Array.mem_toList_iff, ← hvals, List.mem_filter]
      exact ⟨Array.mem_toList_iff.2 hzg, hzf⟩
    have hnz : z ∉ rest := (List.nodup_cons.1 hnd).1
    have hpz : ∀ v (d : PND tabs f g v), z ≠ d.p := fun v d h => by
      have := d.hpf; rw [← h, hfv] at this; cases this
    have hmem' := fun y (hy : y ∈ rest) => hmem y (List.mem_cons_of_mem _ hy)
    by_cases hpn : pnOK tabs f g z = true
    · obtain ⟨d⟩ := pnOK_spec hpn
      obtain ⟨yv, yp, hyv, hyp, hr⟩ := hI.fact z List.mem_cons_self d
      rw [List.filter_cons_of_neg (by simp [hpn]), evalAll_cons]
      unfold stepV
      simp only [show (Ctx.make tabs g).f = g from rfl, d.hw]
      rw [eval_not d hyp]
      refine loop hwf hwg R hE hb hfb hgb hvals hfresh rest S (T.set z _) hmem'
        (List.nodup_cons.1 hnd).2 htopo.2 ⟨hI.sz, by simp [Frame.set, hI.szT], ?_, ?_, ?_⟩
      · simp only [Frame.set]; rw [hI.frame]
      · intro a va x hna hva hga hx
        by_cases haz : a = z
        · subst haz
          rw [hyv] at hx; cases hx
          exact ⟨_, Frame.set_regs_self (by rw [hI.szT]; exact lt_of_value? hgw), hr⟩
        · rw [Frame.set_regs_ne (Ne.symm haz)]
          exact hI.rr a va x (fun hm => hna ((List.mem_cons.1 hm).resolve_left haz)) hva hga hx
      · intro v hv d'
        obtain ⟨yv', yp', h1, h2, h3⟩ := hI.fact v (List.mem_cons_of_mem _ hv) d'
        exact ⟨yv', yp', h1, by rw [Frame.set_regs_ne (hpz v d')]; exact h2, h3⟩
    · have hpf : pnOK tabs f g z = false := by simpa using hpn
      rw [List.filter_cons_of_pos (by simp [hpf])]
      obtain ⟨gv, hgv, hs⟩ := R.value z fv hfv
      rw [hgw] at hgv; cases hgv
      have hs : ssSame fv w = true := hs.resolve_right (by rw [hpf]; simp)
      obtain ⟨hid, -, -, -, -, -, hargs⟩ := StructStore.ssSame_spec hs
      rw [evalAll_cons, evalAll_cons]
      unfold stepV
      simp only [show (Ctx.make tabs f).f = f from rfl, show (Ctx.make tabs g).f = g from rfl,
        hfv, hgw]
      have hstep : Res.Refines (evalValue env (Ctx.make tabs f) S fv)
          (evalValue env (Ctx.make tabs g) T w) := by
        refine PhiSel.eval_ss hE R.ownAux hfv hgw (hid.symm.trans hwid) hs hI.frame
          fun a ha y hy => ?_
        obtain ⟨b', blk', hb', hab⟩ := hwf.argListed bid fb z fv ⟨⟨hb, hfb⟩, hzfb, hfv⟩ a
          (Array.mem_toList_iff.1 ha)
        obtain ⟨va, hva, -, -⟩ := hwf.valueId b' blk' hb' a hab
        obtain ⟨ga, hga, -⟩ := R.value a va hva
        refine hI.rr a va y (fun hm => absurd hm (htopo.1 a ?_)) hva (by rw [hga]; rfl) hy
        rw [argsF_of hgw, hargs]; exact ha
      revert hstep
      generalize evalValue env (Ctx.make tabs f) S fv = rS
      generalize evalValue env (Ctx.make tabs g) T w = rT
      intro hstep
      cases hstep with
      | stuck msg r => exact .stuck _ _
      | panic e hm => exact .panic e hm
      | @ok yS yT hr =>
        refine loop hwf hwg R hE hb hfb hgb hvals hfresh rest (S.set z yS) (T.set z yT) hmem'
          (List.nodup_cons.1 hnd).2 htopo.2
          ⟨by simp [Frame.set, hI.sz], by simp [Frame.set, hI.szT], ?_, ?_, ?_⟩
        · simp only [Frame.set]; rw [hI.frame]
        · intro a va x hna hva hga hx
          by_cases haz : a = z
          · subst haz
            rw [Frame.set_regs_self (by rw [hI.sz]; exact lt_of_value? hfv)] at hx
            cases hx
            exact ⟨_, Frame.set_regs_self (by rw [hI.szT]; exact lt_of_value? hgw), hr⟩
          · rw [Frame.set_regs_ne (Ne.symm haz)] at hx ⊢
            exact hI.rr a va x (fun hm => hna ((List.mem_cons.1 hm).resolve_left haz)) hva hga hx
        · intro v hv d'
          obtain ⟨yv', yp', h1, h2, h3⟩ := hI.fact v (List.mem_cons_of_mem _ hv) d'
          refine ⟨yv', yp', ?_, ?_, h3⟩
          · rw [Frame.set_regs_ne (by rintro rfl; exact hnz hv)]; exact h1
          · rw [Frame.set_regs_ne (hpz v d')]; exact h2

/-! ## Block entry -/

/-- **A turned `Phi`'s argument at its block's entry** along edge `i`: `Not c`, with `c` the fresh
`Phi`'s argument `i`, whose register lemma (D) re-evaluates from `c`'s. -/
theorem not_arg {ce : CheckEnv} (hwf : WF ce f) (hc : CertOK f) {frS : Frame} {bid : ID}
    {i : Nat} (hpre : CSE.Pre env tabs f #[] frS bid i) (hsz : frS.regs.size = f.valueTab.size)
    (hty : Proof.Typed (Ctx.make tabs f) frS) {fb : Block} (hfb : f.block? bid = some fb)
    {ps : List (ID × Val)}
    (hps : fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) frS i) = .ok ps)
    {v : ID} (d : PND tabs f g v) (hv : v ∈ fb.values) :
    ∃ a c cv sx, d.u.args[i]? = some a ∧ d.pv.args[i]? = some c ∧ f.value? c = some cv ∧
      frS.regs[a]? = some (some ((Cmp.not [sx]).retype .bool)) ∧
      frS.regs[c]? = some (some sx) ∧ sx.retype .bool = sx := by
  have hbt := CSE.pre_tree hwf hc hpre
  obtain ⟨u', hu', -, hub⟩ := hwf.valueId bid fb ⟨hbt.1, hfb⟩ v hv
  rw [d.hu] at hu'; cases hu'
  rcases hpre with rfl | ⟨P, blkp, hP, hPb, hPt, he, hD, -⟩
  · exact absurd hub d.hent
  obtain ⟨-, -, -, hphiS⟩ := phis_spec (hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩) hps
  obtain ⟨a, ya, ha, hya, -⟩ := hphiS v hv d.u d.hu d.hphi (by rw [hsz]; exact lt_of_value? d.hu)
  have hi : i < d.pv.args.size := by rw [d.hpsz]; exact (Array.getElem?_eq_some_iff.1 ha).1
  obtain ⟨c, hc'⟩ : ∃ c, d.pv.args[i]? = some c := ⟨_, Array.getElem?_eq_getElem hi⟩
  obtain ⟨av, cv, hav, hop, hasz, h0, hat, hcv, hct⟩ := d.hargs i c a hc' ha
  obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 he
  obtain ⟨-, fb', hfb', hpred⟩ := hwf.succLink P blkp ⟨hP, hPb⟩ j _ hj
  change f.block? bid = some fb' at hfb'
  rw [hfb] at hfb'; cases hfb'
  obtain ⟨bm, blkm, hbm, hmin⟩ := hwf.argListed bid fb v d.u ⟨⟨hbt.1, hfb⟩, hv, d.hu⟩ a
    (Array.mem_of_getElem? ha)
  obtain ⟨av', hav', hida, hmvb⟩ := hwf.valueId bm blkm hbm a hmin
  rw [hav] at hav'; cases hav'
  have hpl : Placed f a av := ⟨hav, hmvb ▸ hbm.1, blkm, hmvb ▸ hbm.2, hmin⟩
  have hA : Anc (make f) (blockOf f a) P :=
    hc.domRel.phiUse hbt.1 hfb hbt.2 hv d.hu d.hphi ha hpred hPt
  rw [blockOf_placed hpl] at hA
  obtain ⟨y, hy, hev⟩ := hD a av hpl hA
  rw [hya] at hy; cases hy
  obtain ⟨argv, hmap, hev⟩ := PhiSel.eval_args (hev (by rw [hop]; decide))
  rw [PhiSel.args_one hasz h0] at hmap
  match argv, hmap with
  | [], h | _ :: _ :: _, h => simp at h
  | [sx], hmap =>
  simp only [Array.toList, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmap
  have hsx := Option.join_eq_some_iff.1 hmap
  rw [hida, tys_of_value hav, Option.getD_some, hat, evalOp_not hop] at hev
  change Res.ok _ = Res.ok _ at hev
  cases hev
  have htc : sx.retype .bool = sx := by
    have := hty c sx hsx
    rwa [tys_of_value hcv, Option.getD_some, hct] at this
  exact ⟨a, c, cv, sx, ha, hc', hcv, hya, hsx, htc⟩

/-- **The block entry**: the target's `Phi`s succeed where the source's do, and the relation
holds along the target's schedule `og` with every turned `Phi` of the block pending. -/
theorem entry {ce ce' : CheckEnv} (hwf : WF ce f) (hc : CertOK f) (hwg : WF ce' g)
    (R : PNRel tabs f g) {frS frT : Frame} {bid : ID} {i : Nat}
    (hpre : CSE.Pre env tabs f #[] frS bid i) (hsz : frS.regs.size = f.valueTab.size)
    (hszT : frT.regs.size = g.valueTab.size) (hfr : frT = { frS with regs := frT.regs })
    (hrr : RR f g frS.regs frT.regs) (hty : Proof.Typed (Ctx.make tabs f) frS)
    {fb gb : Block} (hfb : f.block? bid = some fb) (hgb : g.block? bid = some gb)
    (hvals : gb.values.toList.filter (fun z => (f.value? z).isSome) = fb.values.toList)
    (hfresh : ∀ z ∈ gb.values, (f.value? z).isSome = true ∨ pnFresh tabs f g z = true)
    {og : Array ID} (hog : Sem.schedule g gb = some og) {ps : List (ID × Val)}
    (hps : fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) frS i) = .ok ps) :
    ∃ ps', gb.values.toList.filterMapM (phiStep (Ctx.make tabs g) frT i) = .ok ps' ∧
      Inv tabs f g og.toList { frS with regs := setPhis ps frS.regs }
        { frT with regs := setPhis ps' frT.regs } := by
  have hbt := CSE.pre_tree hwf hc hpre
  have hbg : bid ∈ g.blocks := by rw [CopyElim.cfgView_blocks R.cfg]; exact hbt.1
  obtain ⟨-, -, hkeepS, hphiS⟩ := phis_spec (hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩) hps
  have hinf : ∀ z, z ∈ gb.values → (f.value? z).isSome = true → z ∈ fb.values := fun z hz hs => by
    rw [← Array.mem_toList_iff, ← hvals, List.mem_filter]
    exact ⟨Array.mem_toList_iff.2 hz, hs⟩
  have hing : ∀ z, z ∈ fb.values → z ∈ gb.values := fun z hz => by
    have : z ∈ gb.values.toList.filter (fun z => (f.value? z).isSome) := by
      rw [hvals]; exact Array.mem_toList_iff.2 hz
    exact Array.mem_toList_iff.1 (List.mem_filter.1 this).1
  have hlt : ∀ z (v : Value), f.value? z = some v → z < frT.regs.size := fun z v hv => by
    rw [hszT]; exact Nat.lt_of_lt_of_le (lt_of_value? hv) R.size
  have hrrArg : ∀ z fv a, z ∈ fb.values → f.value? z = some fv → a ∈ fv.args →
      ∀ x, frS.regs[a]? = some (some x) → ∃ y, frT.regs[a]? = some (some y) ∧ Sem.Refines x y := by
    intro z fv a hz hfv ha x hx
    obtain ⟨b', blk', hb', hab⟩ := hwf.argListed bid fb z fv ⟨⟨hbt.1, hfb⟩, hz, hfv⟩ a ha
    obtain ⟨va, hva, -, -⟩ := hwf.valueId b' blk' hb' a hab
    obtain ⟨ga, hga, -⟩ := R.value a va hva
    exact hrr a va x hva (by rw [hga]; rfl) hx
  have hrrC : ∀ c cv sx, f.value? c = some cv → frS.regs[c]? = some (some sx) →
      ∃ tx, frT.regs[c]? = some (some tx) ∧ Sem.Refines sx tx := fun c cv sx hcv hsx => by
    obtain ⟨gc, hgc, -⟩ := R.value c cv hcv
    exact hrr c cv sx hcv (by rw [hgc]; rfl) hsx
  -- the target's `Phi` steps succeed
  have hstepT : ∀ z ∈ gb.values.toList, ∃ o, phiStep (Ctx.make tabs g) frT i z = .ok o := by
    intro z hz
    have hz := Array.mem_toList_iff.1 hz
    obtain ⟨w, hw, -, hwb⟩ := hwg.valueId bid gb ⟨hbg, hgb⟩ z hz
    by_cases hph : w.op = .Phi
    · rcases hfresh z hz with hs | hs
      · obtain ⟨fv, hfv⟩ := Option.isSome_iff_exists.1 hs
        have hzf := hinf z hz hs
        obtain ⟨gv, hgv, hsv⟩ := R.value z fv hfv
        rw [hw] at hgv; cases hgv
        rcases hsv with hsv | hpn
        · obtain ⟨-, hop, -, -, -, -, hargs⟩ := StructStore.ssSame_spec hsv
          obtain ⟨a, x, ha, hx, -⟩ := hphiS z hzf fv hfv (hop ▸ hph)
            (by rw [hsz]; exact lt_of_value? hfv)
          obtain ⟨y, hy, -⟩ := hrrArg z fv a hzf hfv (Array.mem_of_getElem? ha) x hx
          exact phiStep_ok hw hph (by rw [hargs]; exact ha) hy
        · obtain ⟨d⟩ := pnOK_spec hpn
          have := d.hw
          rw [hw] at this; cases this
          exact absurd (d.hwop ▸ hph) (by decide)
      · obtain ⟨v, zv, gb', hzv, hgb', hvin, ⟨d⟩, hdp⟩ := pnFresh_spec hs
        rw [hw] at hzv; cases hzv
        rw [hwb, hgb] at hgb'; cases hgb'
        have hvf := hinf v hvin (by rw [d.hu]; rfl)
        obtain ⟨a, c, cv, sx, -, hc', hcv, -, hsx, -⟩ :=
          not_arg hwf hc hpre hsz hty hfb hps d hvf
        obtain ⟨tx, htx, -⟩ := hrrC c cv sx hcv hsx
        have := d.hpv
        rw [hdp d, hw] at this; cases this
        exact phiStep_ok hw hph hc' htx
    · exact phiStep_ok_none hw hph
  obtain ⟨ps', hps'⟩ := filterMapM_phi_ok hstepT
  obtain ⟨-, -, hkeepT, hphiT⟩ := phis_spec (hwg.valuesNodup _ _ ⟨hbg, hgb⟩) hps'
  obtain ⟨-, -, omem⟩ := schedule_topo (valuesOwn hwg hbg hgb) (hwg.valuesNodup _ _ ⟨hbg, hgb⟩) hog
  refine ⟨ps', hps', ⟨by simp [setPhis_size, hsz], by simp [setPhis_size, hszT], ?_, ?_, ?_⟩⟩
  · conv => lhs; rw [hfr]
  · intro a va x hna hva hga hx
    by_cases hA : a ∈ fb.values ∧ va.op = .Phi
    · obtain ⟨gv, hgv, hsv⟩ := R.value a va hva
      have hpf : pnOK tabs f g a = false := by
        cases hpn : pnOK tabs f g a with
        | false => rfl
        | true =>
          obtain ⟨d⟩ := pnOK_spec hpn
          have := hna ((omem a).2 ⟨hing a hA.1, d.w, d.hw, by rw [d.hwop]; decide⟩)
          rw [hpn] at this
          exact this
      have hsv : ssSame va gv = true := hsv.resolve_right (by rw [hpf]; simp)
      obtain ⟨-, hop, -, -, hgt, -, hargs⟩ := StructStore.ssSame_spec hsv
      obtain ⟨a0, x0, ha0, hx0, hS'⟩ := hphiS a hA.1 va hva hA.2 (by rw [hsz]; exact lt_of_value? hva)
      change (setPhis ps frS.regs)[a]? = some (some x) at hx
      rw [hS'] at hx; cases hx
      obtain ⟨a1, y0, ha1, hy0, hT'⟩ := hphiT a (hing a hA.1) gv hgv (hop.trans hA.2) (hlt a va hva)
      rw [hargs, ha0] at ha1; cases ha1
      obtain ⟨y, hy, hxy⟩ := hrrArg a va a0 hA.1 hva (Array.mem_of_getElem? ha0) x0 hx0
      rw [hy0] at hy; cases hy
      refine ⟨_, hT', ?_⟩
      rw [tys_of_value hgv, tys_of_value hva, hgt]
      exact retype_mono _ hxy
    · have hkS : a ∉ fb.values ∨ ∃ v, (Ctx.make tabs f).f.value? a = some v ∧ v.op ≠ .Phi := by
        by_cases hin : a ∈ fb.values
        · exact .inr ⟨va, hva, fun hp => hA ⟨hin, hp⟩⟩
        · exact .inl hin
      change (setPhis ps frS.regs)[a]? = some (some x) at hx
      rw [hkeepS a hkS] at hx
      obtain ⟨y, hy, hxy⟩ := hrr a va x hva hga hx
      refine ⟨y, ?_, hxy⟩
      change (setPhis ps' frT.regs)[a]? = _
      rw [hkeepT a ?_]; exact hy
      rcases hkS with hin | ⟨v', hv', hne⟩
      · exact .inl fun hg => hin (hinf a hg (by rw [hva]; rfl))
      · change f.value? a = some v' at hv'
        rw [hva] at hv'; cases hv'
        obtain ⟨gv, hgv, hsv⟩ := R.value a va hva
        refine .inr ⟨gv, hgv, ?_⟩
        rcases hsv with hsv | hpn
        · obtain ⟨-, hop, -⟩ := StructStore.ssSame_spec hsv
          rw [hop]; exact hne
        · obtain ⟨d⟩ := pnOK_spec hpn
          have := d.hw
          rw [hgv] at this; cases this
          rw [d.hwop]; decide
  · intro v hv d
    obtain ⟨hvg, -⟩ := (omem v).1 hv
    have hvf := hinf v hvg (by rw [d.hu]; rfl)
    obtain ⟨a, c, cv, sx, ha, hc', hcv, hya, hsx, htc⟩ := not_arg hwf hc hpre hsz hty hfb hps d hvf
    obtain ⟨tx, htx, hr⟩ := hrrC c cv sx hcv hsx
    obtain ⟨a', ya, ha', hya', hS'⟩ :=
      hphiS v hvf d.u d.hu d.hphi (by rw [hsz]; exact lt_of_value? d.hu)
    rw [ha] at ha'; cases ha'
    rw [hya] at hya'; cases hya'
    obtain ⟨u', hu', -, hub⟩ := hwf.valueId bid fb ⟨hbt.1, hfb⟩ v hvf
    rw [d.hu] at hu'; cases hu'
    obtain ⟨gb', hgb', hpin⟩ := d.hpl
    rw [hub, hgb] at hgb'; cases hgb'
    obtain ⟨c', y0, hc'', hy0, hT'⟩ := hphiT d.p hpin d.pv d.hpv d.hpphi
      (by rw [hszT]; exact lt_of_value? d.hpv)
    rw [hc'] at hc''; cases hc''
    rw [htx] at hy0; cases hy0
    refine ⟨_, _, hS', hT', ?_⟩
    rw [tys_of_value d.hu, Option.getD_some, d.hut, tys_of_value d.hpv, Option.getD_some, d.hpt,
      d.hut]
    exact not_ref hr htc

/-! ## The simulation -/

/-- The simulation relation at the entry of block `bid` along edge `i`: the target's registers
refine the source's, the source's are typed, and lemma (D) holds for the block left
(`CSE.Pre`). -/
structure SimAt (env : Env) (tabs : Tables) (f g : Func) (frS frT : Frame) (bid : ID) (i : Nat) :
    Prop where
  size : frS.regs.size = f.valueTab.size
  sizeT : frT.regs.size = g.valueTab.size
  frame : frT = { frS with regs := frT.regs }
  rr : RR f g frS.regs frT.regs
  typed : Proof.Typed (Ctx.make tabs f) frS
  pre : CSE.Pre env tabs f #[] frS bid i

/-- **The terminators** on refined controls. -/
theorem term_rel {ce : CheckEnv} (hwf : WF ce f) (R : PNRel tabs f g) {G GT : Frame}
    (hr : RR f g G.regs GT.regs) {bid : ID} {fb gb : Block}
    (hb : BlockIn f bid fb) (hk : gb.kind = fb.kind) (hs : gb.succs = fb.succs) (hid : gb.id = fb.id)
    (hc : gb.controls = fb.controls) :
    Res.Rel Next.Refines (stepTerm G fb) (stepTerm GT gb) := by
  refine AtomSim.stepTerm_mono2 hk hs hid fun k => ?_
  unfold Sem.control
  rw [hc]
  cases hck : fb.controls[k]? with
  | none => exact .stuck _ _
  | some c =>
    dsimp only
    cases hx : (G.regs[c]?).join with
    | none => exact .stuck _ _
    | some x =>
      obtain ⟨bid', b', hb', hcb⟩ := hwf.ctrlListed bid fb hb c (Array.mem_of_getElem? hck)
      obtain ⟨vc, hvc, -, -⟩ := hwf.valueId bid' b' hb' c hcb
      obtain ⟨gc, hgc, -⟩ := R.value c vc hvc
      obtain ⟨y, hy, hxy⟩ := hr c vc x hvc (by rw [hgc]; rfl) (Option.join_eq_some_iff.1 hx)
      rw [hy]
      exact .ok hxy

/-- The simulation relation: the same block and edge, `SimAt`. -/
def SimR (env : Env) (tabs : Tables) (f g : Func) (frS : Frame) (bS : ID) (iS : Nat) (frT : Frame)
    (bT : ID) (iT : Nat) : Prop :=
  bT = bS ∧ iT = iS ∧ SimAt env tabs f g frS frT bS iS

/-- **One block step.** -/
theorem step {ce ce' : CheckEnv} (hwf : WF ce f) (hc : CertOK f) (hwg : WF ce' g)
    (R : PNRel tabs f g) (hE : env.Mono) {frS frT : Frame} {bid : ID} {i : Nat}
    (hA : SimAt env tabs f g frS frT bid i) :
    StepSimE Mem.Refines (SimR env tabs f g) (blockStep env (Ctx.make tabs f) frS bid i)
      (blockStep env (Ctx.make tabs g) frT bid i) := by
  have hbt := CSE.pre_tree hwf hc hA.pre
  unfold blockStep
  simp only [show (Ctx.make tabs f).f = f from rfl, show (Ctx.make tabs g).f = g from rfl]
  cases hfb : f.block? bid with
  | none => exact True.intro
  | some fb =>
  obtain ⟨gb, hgb, hk, hctl, hvals, hfresh, of, og, hof, hog, hfilt⟩ := R.block bid hbt.1 fb hfb
  obtain ⟨gb', hgb', hgid, hsucc, -⟩ := CopyElim.cfgView_block R.cfg hfb
  rw [hgb] at hgb'; cases hgb'
  obtain ⟨fb', hfb', hfid⟩ := hwf.blockId bid hbt.1
  rw [hfb] at hfb'; cases hfb'
  rw [hgb]
  simp only
  have hbg : bid ∈ g.blocks := by rw [CopyElim.cfgView_blocks R.cfg]; exact hbt.1
  -- the parts of the source's block entry, and the target's
  have parts : ∀ r, enterBlock env (Ctx.make tabs f) frS fb i = r → (∀ msg, r ≠ .stuck msg) →
      ∃ ps ps', Inv tabs f g og.toList { frS with regs := setPhis ps frS.regs }
          { frT with regs := setPhis ps' frT.regs } ∧
        evalAll env (Ctx.make tabs f) { frS with regs := setPhis ps frS.regs } of.toList = r ∧
        enterBlock env (Ctx.make tabs g) frT gb i =
          evalAll env (Ctx.make tabs g) { frT with regs := setPhis ps' frT.regs } og.toList := by
    intro r hen hr
    obtain ⟨ps, oS, hps, hsched, hev⟩ := CSE.enterBlock_split hen hr
    rw [hfid, sched_of_block hfb, hof] at hsched
    cases hsched
    obtain ⟨ps', hps', hI⟩ := entry hwf hc hwg R hA.pre hA.size hA.sizeT hA.frame hA.rr hA.typed
      hfb hgb hvals hfresh hog hps
    refine ⟨ps, ps', hI, hev, CSE.enterBlock_of_parts hps' ?_⟩
    rw [hgid, hfid, sched_of_block hgb, hog]
  -- the block's evaluation
  have blk : ∀ S T, Inv tabs f g og.toList S T →
      Res.Rel (Inv tabs f g []) (evalAll env (Ctx.make tabs f) S of.toList)
        (evalAll env (Ctx.make tabs g) T og.toList) := by
    intro S T hI
    obtain ⟨ond, otopo, omem⟩ := schedule_topo (valuesOwn hwg hbg hgb)
      (hwg.valuesNodup _ _ ⟨hbg, hgb⟩) hog
    rw [← hfilt]
    exact loop hwf hwg R hE hbt.1 hfb hgb hvals hfresh og.toList S T
      (fun z hz => (omem z).1 hz) ond otopo hI
  cases hen : enterBlock env (Ctx.make tabs f) frS fb i with
  | stuck msg => exact True.intro
  | panic e m =>
    obtain ⟨ps, ps', hI, hev, hT⟩ := parts _ hen nofun
    have hl := blk _ _ hI
    rw [hev] at hl
    rw [hT]
    generalize evalAll env (Ctx.make tabs g) { frT with regs := setPhis ps' frT.regs } og.toList = rT
      at hl ⊢
    cases hl with
    | panic e hm => exact ⟨_, rfl, hm⟩
  | ok G =>
  obtain ⟨ps, ps', hI, hev, hT⟩ := parts _ hen nofun
  have hl := blk _ _ hI
  rw [hev] at hl
  rw [hT]
  generalize evalAll env (Ctx.make tabs g) { frT with regs := setPhis ps' frT.regs } og.toList = rT
    at hl ⊢
  cases hl with
  | @ok _ GT hI =>
  simp only
  obtain ⟨hD, -, -⟩ := dinv_enter hwf hc hbt.1 hfb hA.size (CSE.pre_strict hc hA.pre).1 hen
  have hty := typed_enter hwf hbt.1 hfb hA.size hA.typed hen
  have hst := term_rel hwf R hI.rrAll ⟨hbt.1, hfb⟩ hk (by rw [hsucc]) (by rw [hgid]) hctl
  generalize hS : stepTerm G fb = sS at hst ⊢
  generalize stepTerm GT gb = sT at hst ⊢
  cases hst with
  | ok hn =>
    cases hn with
    | goto e =>
      have he : (⟨e.b, e.i⟩ : Edge) ∈ fb.succs := by cases e; exact AtomSim.stepTerm_goto_mem hS
      exact ⟨GT, e, rfl, rfl, rfl,
        { size := hI.sz, sizeT := hI.szT, frame := hI.frame, rr := hI.rrAll, typed := hty
          pre := .inr ⟨bid, fb, hbt.1, hfb, hbt.2, he, hD, DSE.repInv_nil _ _⟩ }⟩
    | ret hl hm => exact ⟨_, _, rfl, hl, hm⟩
  | panic e hm => exact ⟨_, rfl, hm⟩
  | stuck msg r => exact True.intro

/-- **`Phi`s of `Not`s turned `Not`s of fresh `Phi`s refine** under monotone contracts
(`generic.rules:1068`). -/
theorem pn_refines {ce ce' : CheckEnv} (hf : check ce f = .ok ()) (hg : check ce' g = .ok ())
    (hrel : pnRel tabs f g = true) : RefinesUnder Env.Mono tabs g tabs f := by
  have hwf := check_wf hf
  have hwg := check_wf hg
  have hc := certOK_of_check (check_domCert hf)
  have R := pnRel_spec hrel
  intro env hE args mem fuel hd
  refine ⟨fuel, ?_⟩
  have hcx := AtomSim.ctx_eq (tabs := tabs) R.ownAux.symm
  have hpar : (Ctx.make tabs g).params = (Ctx.make tabs f).params := by rw [hcx]
  have houts : (Ctx.make tabs g).outs = (Ctx.make tabs f).outs := by rw [hcx]
  have hact : (Ctx.make tabs g).act = (Ctx.make tabs f).act := by rw [hcx]
  change (runCtx env (Ctx.make tabs f) args mem fuel).Defined at hd
  change OutcomeRefines 0 (runCtx env (Ctx.make tabs f) args mem fuel)
    (runCtx env (Ctx.make tabs g) args mem fuel)
  unfold runCtx at hd ⊢
  rw [hpar, houts, hact]
  split
  · next hn => simp only [hn] at hd; exact hd.elim
  · next hn =>
    simp only [hn] at hd
    have hT : entryFrame env (Ctx.make tabs g) args mem =
        { entryFrame env (Ctx.make tabs f) args mem with
          regs := Array.replicate g.valueTab.size none } :=
      AtomSim.entryFrame_eq R.ownAux.symm args mem
    have hA0 : SimAt env tabs f g (entryFrame env (Ctx.make tabs f) args mem)
        (entryFrame env (Ctx.make tabs g) args mem) f.entry 0 :=
      { size := by simp [entryFrame]; rfl
        sizeT := by rw [hT]; simp
        frame := by rw [hT]
        rr := fun a v x hv _ h => by
          simp [entryFrame, Array.getElem?_replicate] at h
        typed := typed_replicate _ _ _ rfl
        pre := .inl rfl }
    rw [show (Ctx.make tabs g).f.entry = (Ctx.make tabs f).f.entry from
      CopyElim.cfgView_entry R.cfg]
    refine finish_refines_mono hE hd (runLoop_simE (SimR env tabs f g)
      (fun frS bS iS frT bT iT hR => ?_) fuel _ _ _ _ _ _ ⟨rfl, rfl, hA0⟩ (finish_defined hd))
    obtain ⟨rfl, rfl, hA⟩ := hR
    exact step hwf hc hwg R hE hA

end GoFV.Proof.PhiNot

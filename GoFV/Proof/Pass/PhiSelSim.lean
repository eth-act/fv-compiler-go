import GoFV.Proof.Pass.PhiSelRel
import GoFV.Proof.Pass.ECIdent

/-!
# Selections of `Phi`s of `SliceMake`s refine their input (issue #69)

`ps_refines`: if `g` is `f` with selections `v = SliceLen p` (or `SliceCap`) of a `Phi` `p` of
`SliceMake`s with argument `x` turned `Copy x` (`RewriteCheck.psRel`, `generic.rules:1049`/
`:1050`), both checked, `g` refines `f` under monotone contracts. Lock-step simulation
(`runLoop_simE`) along the same edges, with `SimAt` at block entries: the target's registers
refine the source's (`Seg.RR`), lemma (D) holds for the ancestors of the block left (`DInv`),
and so does the selection fact (`PInv`, `Fact`): for every selection whose `Phi`'s block
dominates the block left, the selection of the `Phi`'s register is refined by `x`'s register.
Entering the `Phi`'s block along edge `i` sets the `Phi` to its `SliceMake` argument `i`, which
lemma (D) re-evaluates from `x`'s register (`fact_entry`); `x` is defined in a strict dominator
of the `Phi`'s block, so neither register changes in a block the `Phi`'s block dominates. A
selection is evaluated in such a block (its argument's block dominates it), where the fact gives
the refinement of the source's selection by the target's copy (`sel_step`); every other value
is unchanged and evaluates to a refinement on refined arguments (`eval_ss`).
-/

namespace GoFV.Proof.PhiSel

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Opt GoFV.Opt.RewriteCheck
open GoFV.Proof.Seg (RR RR.set setPhis_rr phis_rel)

variable {env : Env} {tabs : Tables} {f g : Func}

/-- The fact selection `d` relies on, in the source's frame `S`: if its `Phi` has a register,
the selection of it (at `int64`) is refined by the register of `x`. -/
def Fact {v : ID} (d : PSD tabs f g v) (S : Frame) : Prop :=
  ∀ yp, S.regs[d.p]? = some (some yp) → ∃ yx, S.regs[d.x]? = some (some yx) ∧
    Sem.Refines ((Comp.select d.k [yp]).retype (.int .w64)) yx

/-- In block `b`: the facts of the selections whose `Phi`'s block dominates `b`. -/
def PInv (tabs : Tables) (f g : Func) (S : Frame) (b : ID) : Prop :=
  ∀ v (d : PSD tabs f g v), Anc (make f) d.pv.block b → Fact d S

theorem Fact.congr {v : ID} {d : PSD tabs f g v} {S S' : Frame} (h : Fact d S)
    (hp : S'.regs[d.p]? = S.regs[d.p]?) (hx : S'.regs[d.x]? = S.regs[d.x]?) : Fact d S' := by
  intro yp hyp
  rw [hp] at hyp
  obtain ⟨yx, hyx, hr⟩ := h yp hyp
  exact ⟨yx, hx ▸ hyx, hr⟩

/-! ## Evaluating the ops -/

theorem evalOp_sel {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val} {ty : Ty}
    (hop : v.op = .SliceLen ∨ v.op = .SliceCap ∨ v.op = .SliceMake) :
    evalOp env ctx fr v argv ty = .ok (evalPure v.op ty v.auxInt v.aux argv) := by
  rcases hop with h | h | h <;> (simp only [evalOp, frameVal, h]; rfl)

/-- The registers `mapM` collects. -/
theorem mapM_regs {m : ID → String} {r : ID → Option Val} :
    ∀ {l : List ID} {L : List Val}, l.mapM (fun a => Res.ofOption (m a) (r a)) = .ok L →
      l.map r = L.map some
  | [], L, h => by cases h; rfl
  | a :: l, L, h => by
    rw [List.mapM_cons] at h
    cases ha : r a with
    | none => rw [ha] at h; cases h
    | some z =>
      rw [ha] at h
      change Res.bind (List.mapM (fun a => Res.ofOption (m a) (r a)) l) _ = _ at h
      cases hl : l.mapM (fun a => Res.ofOption (m a) (r a)) with
      | ok L' =>
        rw [hl] at h
        cases h
        simp only [List.map_cons, ha, mapM_regs hl]
      | panic e m' => rw [hl] at h; cases h
      | stuck msg => rw [hl] at h; cases h

theorem map_some_get {l : List ID} {L : List Val} {r : ID → Option Val} (h : l.map r = L.map some)
    {j : Nat} {a : ID} (ha : l[j]? = some a) : ∃ y, r a = some y ∧ L[j]? = some y := by
  have := congrArg (·[j]?) h
  simp only [List.getElem?_map, ha, Option.map_some] at this
  cases hL : L[j]? with
  | none => rw [hL] at this; cases this
  | some y => rw [hL] at this; exact ⟨y, Option.some.inj this, rfl⟩

/-- The selection (at `int64`) of a `Phi`'s value set from a `SliceMake` whose component `k`
holds `yx` (of the `int64` shape): `poison` or `yx`. -/
theorem sel_make {el el' : Option Nat} {k : Nat} (hk : k = 1 ∨ k = 2) {argv : List Val}
    (hlen : argv.length = 3) {yx : Val} (hyk : argv[k]? = some yx)
    (hyx : yx.retype (.int .w64) = yx) :
    Sem.Refines ((Comp.select k [((Val.agg argv).retype (.slice el)).retype (.slice el')]).retype
      (.int .w64)) yx := by
  match argv, hlen with
  | [a0, a1, a2], _ =>
    have hY : (Val.agg [a0, a1, a2]).retype (.slice el) =
        Val.ofSlice [a0.retypePtr, a1.retypeI64, a2.retypeI64] := rfl
    rw [hY, Val.retype_of_hasTy (Val.ofSlice_hasTy el' a0 _ _)]
    unfold Val.ofSlice
    split
    · rcases hk with rfl | rfl
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hyk
        subst hyk
        show Sem.Refines ((Val.retypeI64 _).retype (.int .w64)) _
        rw [Val.retypeI64_eq, Val.retype_idem, hyx]
        exact Sem.Refines.refl _
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hyk
        subst hyk
        show Sem.Refines ((Val.retypeI64 _).retype (.int .w64)) _
        rw [Val.retypeI64_eq, Val.retype_idem, hyx]
        exact Sem.Refines.refl _
    · show Sem.Refines (Val.poison.retype (.int .w64)) yx
      exact .poison _

/-! ## Where the registers of a selection's `Phi` and `x` change -/

section
variable {ce : CheckEnv} (hwf : WF ce f) (hc : CertOK f)
include hwf hc

/-- `x` is not listed in a block its `Phi`'s block dominates. -/
theorem x_not_in {v : ID} (d : PSD tabs f g v) {bid : ID} {fb : Block} (hb : bid ∈ f.blocks)
    (hfb : f.block? bid = some fb) (hB : Anc (make f) d.pv.block bid) : d.x ∉ fb.values := by
  intro hx
  obtain ⟨v', hv', -, hvb⟩ := hwf.valueId bid fb ⟨hb, hfb⟩ d.x hx
  rw [d.hxv] at hv'; cases hv'
  have hxa : Anc (make f) d.xv.block d.pv.block := (anc_iff hc.parents).1 d.hanc
  rw [hvb] at hxa
  have := Anc.antisymm hc.parents hB hxa
  exact d.hxb (hvb.trans this.symm)

omit hc in
/-- A `Phi` listed in block `bid` is placed there. -/
theorem p_in {v : ID} (d : PSD tabs f g v) {bid : ID} {fb : Block} (hb : bid ∈ f.blocks)
    (hfb : f.block? bid = some fb) (hp : d.p ∈ fb.values) : d.pv.block = bid := by
  obtain ⟨v', hv', -, hvb⟩ := hwf.valueId bid fb ⟨hb, hfb⟩ d.p hp
  rw [d.hpv] at hv'; cases hv'; exact hvb

/-- **The selection facts after the `Phi`s** of a block entered with lemma (D) and the facts
of the block left: in the `Phi`'s block, the `Phi` holds its `SliceMake` argument along the
edge, which lemma (D) re-evaluates from `x`'s register (`sel_make`); in another block the
`Phi`'s block dominates, it dominates the block left. -/
theorem fact_entry {frS : Frame} {bid : ID} {i : Nat}
    (hpre : CSE.Pre env tabs f #[] frS bid i)
    (hinv : bid = f.entry ∨ ∃ p blkp, p ∈ f.blocks ∧ f.block? p = some blkp ∧
      ((make f).depthOf p).isSome ∧ (⟨bid, i⟩ : Edge) ∈ blkp.succs ∧
      DInv env (Ctx.make tabs f) (fun a => Anc (make f) a p) frS ∧ PInv tabs f g frS p)
    (hsz : frS.regs.size = f.valueTab.size) (hty : Proof.Typed (Ctx.make tabs f) frS)
    {fb : Block} (hfb : f.block? bid = some fb) {ps : List (ID × Val)}
    (hps : fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) frS i) = .ok ps) :
    PInv tabs f g { frS with regs := setPhis ps frS.regs } bid := by
  intro v d hB
  have hp := hc.parents
  have hbt := CSE.pre_tree hwf hc hpre
  obtain ⟨-, -, hkeep, hphiS⟩ := phis_spec (hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩) hps
  have hxk : (setPhis ps frS.regs)[d.x]? = frS.regs[d.x]? :=
    hkeep _ (.inl (x_not_in hwf hc d hbt.1 hfb hB))
  rcases hinv with rfl | ⟨P, blkp, hP, hPb, hPt, he, hD, hQ⟩
  · exact absurd (anc_of_entry hp hB) d.hpe
  by_cases hBb : d.pv.block = bid
  · obtain ⟨blk, hblk, hpin⟩ := d.hpl
    rw [hBb, hfb] at hblk; cases hblk
    obtain ⟨m, ym, hm, hym, hset⟩ := hphiS d.p hpin d.pv d.hpv d.hphi
      (by rw [hsz]; exact lt_of_value? d.hpv)
    intro yp hyp
    change (setPhis ps frS.regs)[d.p]? = some (some yp) at hyp
    rw [hset] at hyp
    cases hyp
    obtain ⟨mv, hmv, hmop, hmsz, hmk, hms⟩ := d.hm m (Array.mem_of_getElem? hm)
    obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 he
    obtain ⟨-, c, hc', hpred⟩ := hwf.succLink P blkp ⟨hP, hPb⟩ j _ hj
    change f.block? bid = some c at hc'
    rw [hfb] at hc'; cases hc'
    obtain ⟨bm, blkm, hbm, hmin⟩ := hwf.argListed bid fb d.p d.pv ⟨⟨hbt.1, hfb⟩, hpin, d.hpv⟩ m
      (Array.mem_of_getElem? hm)
    obtain ⟨mv', hmv', hmid, hmvb⟩ := hwf.valueId bm blkm hbm m hmin
    rw [hmv] at hmv'; cases hmv'
    have hpl : Placed f m mv := ⟨hmv, hmvb ▸ hbm.1, blkm, hmvb ▸ hbm.2, hmin⟩
    have hA : Anc (make f) (blockOf f m) P :=
      hc.domRel.phiUse hbt.1 hfb hbt.2 hpin d.hpv d.hphi hm hpred hPt
    rw [blockOf_placed hpl] at hA
    obtain ⟨y, hy, hev⟩ := hD m mv hpl hA
    rw [hym] at hy; cases hy
    have hev := hev (by rw [hmop]; decide)
    unfold evalValue at hev
    cases hargs : mv.args.toList.mapM (fun a =>
        Res.ofOption s!"v{mv.id}: argument v{a} has no value" (frS.regs[a]?).join) with
    | panic e mm => rw [hargs] at hev; cases hev
    | stuck msg => rw [hargs] at hev; cases hev
    | ok argv =>
    rw [hargs] at hev
    change (evalOp env (Ctx.make tabs f) frS mv argv _).bind (fun r => .ok _) = _ at hev
    rw [evalOp_sel (.inr (.inr hmop)), hmop] at hev
    change Res.ok _ = Res.ok _ at hev
    cases hev
    have hmap := mapM_regs hargs
    have hlen : argv.length = 3 := by
      have := congrArg List.length hmap
      simp only [List.length_map, Array.length_toList, hmsz] at this
      exact this.symm
    obtain ⟨yx, hyx, hyk⟩ := map_some_get hmap (by rw [Array.getElem?_toList]; exact hmk)
    have hyx' : frS.regs[d.x]? = some (some yx) := Option.join_eq_some_iff.1 hyx
    refine ⟨yx, by rw [hxk]; exact hyx', ?_⟩
    have htx : yx.retype (.int .w64) = yx := by
      have := hty d.x yx hyx'
      rwa [tys_of_value d.hxv, Option.getD_some, d.hxt] at this
    obtain ⟨el, hel⟩ := GoFV.Proof.Rules.isSliceTy_iff.1 hms
    obtain ⟨el', hel'⟩ := GoFV.Proof.Rules.isSliceTy_iff.1 d.hps
    rw [hmid, tys_of_value d.hpv, Option.getD_some, hel', tys_of_value hmv, Option.getD_some, hel]
    have hk : d.k = 1 ∨ d.k = 2 := by
      rcases psSel_some d.hk with ⟨-, h⟩ | ⟨-, h⟩
      · exact .inl h
      · exact .inr h
    exact sel_make hk hlen hyk htx
  · have hBP : Anc (make f) d.pv.block P :=
      Anc.trans hp (hB.up hp hBb) (edge hc hP hPb hPt he).2.2
    refine (hQ v d hBP).congr ?_ hxk
    exact hkeep _ (.inl fun hpin => hBb (p_in hwf d hbt.1 hfb hpin))

end

/-! ## Evaluating the target's values -/

/-- **An unchanged value** evaluates to a refinement on refined arguments. -/
theorem eval_ss (hE : env.Mono) (hown : g.ownAux = f.ownAux) {x : ID} {u w : Value}
    (hu : f.value? x = some u) (hw : g.value? x = some w) (hux : u.id = x)
    (hs : ssSame u w = true) {frS T : Frame} (hT : T = { frS with regs := T.regs })
    (hfr : ∀ a ∈ u.args.toList, ∀ y, frS.regs[a]? = some (some y) →
      ∃ y', T.regs[a]? = some (some y') ∧ Sem.Refines y y') :
    Res.Refines (evalValue env (Ctx.make tabs f) frS u) (evalValue env (Ctx.make tabs g) T w) := by
  obtain ⟨hid, hop, hax, hai, hty, -, hargs⟩ := StructStore.ssSame_spec hs
  have hwx : w.id = x := hid.trans hux
  have hwu : w = { u with pos := w.pos, uses := w.uses, block := w.block, type := w.type } := by
    cases w; cases u
    simp only at hop hai hax hargs hid ⊢
    subst hop hai hax hargs hid; rfl
  unfold evalValue
  rw [hargs]
  have hrel := EC.mapM_regs_refines u.args.toList hfr
    (fun (a : ID) => s!"v{u.id}: argument v{a} has no value")
  have hmsg : (fun (a : ID) => Res.ofOption s!"v{w.id}: argument v{a} has no value"
      (T.regs[a]?).join) =
      (fun (a : ID) => Res.ofOption s!"v{u.id}: argument v{a} has no value" (T.regs[a]?).join) := by
    rw [hux, hwx]
  rw [hmsg]
  have htys : (Ctx.make tabs g).tys[w.id]?.getD .other =
      (Ctx.make tabs f).tys[u.id]?.getD .other := by
    rw [hux, hwx, tys_of_value hu, tys_of_value hw, hty]
  rw [htys]
  revert hrel
  generalize u.args.toList.mapM (fun a => Res.ofOption s!"v{u.id}: argument v{a} has no value"
    (frS.regs[a]?).join) = rS
  generalize u.args.toList.mapM (fun a => Res.ofOption s!"v{u.id}: argument v{a} has no value"
    (T.regs[a]?).join) = rT
  intro hrel
  cases hrel with
  | stuck msg r => exact .stuck _ _
  | panic e hm => exact .panic e hm
  | @ok argv argv' hl =>
    show Res.Refines (Res.bind (Res.ok argv) _) (Res.bind (Res.ok argv') _)
    simp only [Res.bind_ok]
    have hev : evalOp env (Ctx.make tabs g) T w argv' ((Ctx.make tabs f).tys[u.id]?.getD .other) =
        evalOp env (Ctx.make tabs g) T u argv' ((Ctx.make tabs f).tys[u.id]?.getD .other) := by
      rw [hwu]; exact EC.evalOp_upd _ _ _ u _ _ _ _ _ _
    rw [hev]
    have hctx := AtomSim.ctx_eq (tabs := tabs) hown.symm
    have hm := evalOp_mono env hE (Ctx.make tabs f) (Ctx.make tabs g) hctx frS T
      (by rw [hT]) (by rw [hT]) (by rw [hT]) (by rw [hT]) u
      ((Ctx.make tabs f).tys[u.id]?.getD .other) hl
    revert hm
    generalize evalOp env (Ctx.make tabs f) frS u argv _ = r
    generalize evalOp env (Ctx.make tabs g) T u argv' _ = r'
    intro hm
    cases hm with
    | ok h => exact .ok (retype_mono _ h)
    | panic e hm => exact .panic e hm
    | stuck msg r => exact .stuck _ _

theorem args_one {u : Value} {a : ID} (hsz : u.args.size = 1) (h : u.args[0]? = some a) :
    u.args = #[a] := by
  apply Array.ext
  · simp [hsz]
  · intro j h1 h2
    have hj : j = 0 := by omega
    subst hj
    simp only [List.getElem_toArray, List.getElem_cons_zero]
    rw [Array.getElem?_eq_getElem h1] at h
    exact Option.some.inj h

/-- **A selection** evaluates to the copy of `x` refining it, under its fact. -/
theorem sel_step (R : PSRel tabs f g) {v : ID} (d : PSD tabs f g v) (hux : d.u.id = v)
    {S T : Frame} (hrr : RR f g S.regs T.regs) (hF : Fact d S) :
    Res.Refines (evalValue env (Ctx.make tabs f) S d.u) (evalValue env (Ctx.make tabs g) T d.w) := by
  have hua := args_one d.husz d.hp
  have hwa := args_one d.hwsz d.hx
  have hk : (d.u.op = .SliceLen ∧ d.k = 1) ∨ (d.u.op = .SliceCap ∧ d.k = 2) := psSel_some d.hk
  unfold evalValue
  rw [hua, hwa]
  simp only [List.mapM_cons, List.mapM_nil, Array.toList]
  cases hp : (S.regs[d.p]?).join with
  | none => simp only [Res.ofOption, hp]; exact .stuck _ _
  | some yp =>
  obtain ⟨yx, hyx, hr⟩ := hF yp (Option.join_eq_some_iff.1 hp)
  obtain ⟨gx, hgx, -⟩ := R.value d.x d.xv d.hxv
  obtain ⟨yx', hyx', hr'⟩ := hrr d.x d.xv yx d.hxv (by rw [hgx]; rfl) hyx
  have hp' : (T.regs[d.x]?).join = some yx' := by rw [hyx']; rfl
  simp only [Res.ofOption, hp, hp']
  have htu : (Ctx.make tabs f).tys[d.u.id]?.getD .other = .int .w64 := by
    rw [hux, tys_of_value d.hu, Option.getD_some, d.hut]
  have htw : (Ctx.make tabs g).tys[d.w.id]?.getD .other = .int .w64 := by
    rw [d.hwid, hux, tys_of_value d.hw, Option.getD_some, d.hwt]
  change Res.Refines ((evalOp env (Ctx.make tabs f) S d.u [yp]
      ((Ctx.make tabs f).tys[d.u.id]?.getD .other)).bind
      fun r => .ok (r.retype ((Ctx.make tabs f).tys[d.u.id]?.getD .other)))
    ((evalOp env (Ctx.make tabs g) T d.w [yx'] ((Ctx.make tabs g).tys[d.w.id]?.getD .other)).bind
      fun r => .ok (r.retype ((Ctx.make tabs g).tys[d.w.id]?.getD .other)))
  rw [htu, htw, evalOp_copy d.hwop]
  rw [evalOp_sel (by rcases hk with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h])]
  simp only [Res.bind_ok]
  have hsel : evalPure d.u.op (.int .w64) d.u.auxInt d.u.aux [yp] = Comp.select d.k [yp] := by
    rcases hk with ⟨h, hk⟩ | ⟨h, hk⟩ <;> rw [h, hk] <;> rfl
  rw [hsel]
  have h1 : Sem.Refines ((Comp.select d.k [yp]).retype (.int .w64)) (yx.retype (.int .w64)) := by
    have := retype_mono (.int .w64) hr
    rwa [Val.retype_idem] at this
  exact .ok (Sem.Refines.trans h1 (retype_mono _ hr'))

/-! ## One block's schedule -/

/-- The relation along block `bid`'s schedule. -/
structure Inv (tabs : Tables) (f g : Func) (bid : ID) (S T : Frame) : Prop where
  sz : S.regs.size = f.valueTab.size
  szT : T.regs.size = g.valueTab.size
  frame : T = { S with regs := T.regs }
  rr : RR f g S.regs T.regs
  fact : PInv tabs f g S bid

section
variable {ce : CheckEnv} (hwf : WF ce f) (hc : CertOK f) (R : PSRel tabs f g)
include hwf hc R

/-- **The schedule in lock step**: the source's and the target's evaluations of the non-`Phi`
values of a tree block `bid` keep `Inv`. -/
theorem loop (hE : env.Mono) {bid : ID} {fb : Block} (hbt : CopyElim.Tree f bid)
    (hfb : f.block? bid = some fb) :
    ∀ (rest : List ID) (S T : Frame),
      (∀ z ∈ rest, z ∈ fb.values ∧ ∃ v, f.value? z = some v ∧ v.op ≠ .Phi) →
      Inv tabs f g bid S T →
      Res.Rel (Inv tabs f g bid) (evalAll env (Ctx.make tabs f) S rest)
        (evalAll env (Ctx.make tabs g) T rest)
  | [], S, T, _, hI => .ok hI
  | z :: rest, S, T, hrest, hI => by
    obtain ⟨hz, fv, hfv, hph⟩ := hrest z List.mem_cons_self
    obtain ⟨gv, hgv, hs⟩ := R.value z fv hfv
    obtain ⟨fv', hfv', hid, -⟩ := hwf.valueId bid fb ⟨hbt.1, hfb⟩ z hz
    rw [hfv] at hfv'; cases hfv'
    rw [evalAll_cons, evalAll_cons]
    unfold stepV
    simp only [show (Ctx.make tabs f).f = f from rfl, show (Ctx.make tabs g).f = g from rfl, hfv,
      hgv]
    have hstep : Res.Refines (evalValue env (Ctx.make tabs f) S fv)
        (evalValue env (Ctx.make tabs g) T gv) := by
      rcases hs with hs | hne
      · refine eval_ss hE R.ownAux hfv hgv hid hs hI.frame fun a ha y hy => ?_
        obtain ⟨b', blk', hb', hab⟩ := hwf.argListed bid fb z fv ⟨⟨hbt.1, hfb⟩, hz, hfv⟩ a
          (Array.mem_toList_iff.1 ha)
        obtain ⟨va, hva, -, -⟩ := hwf.valueId b' blk' hb' a hab
        obtain ⟨ga, hga, -⟩ := R.value a va hva
        exact hI.rr a va y hva (by rw [hga]; rfl) hy
      · obtain ⟨d⟩ := hne
        have hu := d.hu
        rw [hfv] at hu; cases hu
        have hw := d.hw
        rw [hgv] at hw; cases hw
        have hpl : Placed f d.p d.pv := ⟨d.hpv, d.hpb, d.hpl⟩
        have hB : Anc (make f) d.pv.block bid := by
          have := hc.domRel.uses hbt.1 hfb hbt.2 hz hfv hph (Array.mem_of_getElem? d.hp)
          rwa [blockOf_placed hpl] at this
        exact sel_step R d hid hI.rr (hI.fact z d hB)
    revert hstep
    generalize evalValue env (Ctx.make tabs f) S fv = rS
    generalize evalValue env (Ctx.make tabs g) T gv = rT
    intro hstep
    cases hstep with
    | stuck msg r => exact .stuck _ _
    | panic e hm => exact .panic e hm
    | @ok yS yT hr =>
      refine loop hE hbt hfb rest (S.set z yS) (T.set z yT)
        (fun y hy => hrest y (List.mem_cons_of_mem _ hy)) ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [Frame.set, hI.sz]
      · simp [Frame.set, hI.szT]
      · simp only [Frame.set]; rw [hI.frame]
      · exact hI.rr.set (by rw [hI.sz, hI.szT, R.size]; exact Nat.le_refl _) z hr
      · intro v d hB
        refine (hI.fact v d hB).congr ?_ ?_
        · refine Frame.set_regs_ne fun h => ?_
          subst h
          rw [d.hpv] at hfv; cases hfv
          exact hph d.hphi
        · refine Frame.set_regs_ne fun h => ?_
          subst h
          exact x_not_in hwf hc d hbt.1 hfb hB hz

end

/-! ## The simulation -/

/-- The simulation relation at the entry of block `bid` along edge `i`: the target's registers
refine the source's, the source's are typed, lemma (D) holds for the strict ancestors of `bid`
(`CSE.Pre`), and for the block left, with its selection facts (`inv`). -/
structure SimAt (env : Env) (tabs : Tables) (f g : Func) (frS frT : Frame) (bid : ID) (i : Nat) :
    Prop where
  size : frS.regs.size = f.valueTab.size
  sizeT : frT.regs.size = g.valueTab.size
  frame : frT = { frS with regs := frT.regs }
  rr : RR f g frS.regs frT.regs
  typed : Proof.Typed (Ctx.make tabs f) frS
  pre : CSE.Pre env tabs f #[] frS bid i
  inv : bid = f.entry ∨ ∃ p blkp, p ∈ f.blocks ∧ f.block? p = some blkp ∧
    ((make f).depthOf p).isSome ∧ (⟨bid, i⟩ : Edge) ∈ blkp.succs ∧
    DInv env (Ctx.make tabs f) (fun a => Anc (make f) a p) frS ∧ PInv tabs f g frS p

section
variable {ce : CheckEnv} (hwf : WF ce f) (R : PSRel tabs f g)
include hwf R

/-- One `Phi` step on refined registers. -/
theorem phiStep_rel {frS frT : Frame} (hr : RR f g frS.regs frT.regs) {bid : ID} {fb : Block}
    (hb : BlockIn f bid fb) {z : ID} (hz : z ∈ fb.values) (i : Nat) :
    Res.Rel PhiRefines (phiStep (Ctx.make tabs f) frS i z) (phiStep (Ctx.make tabs g) frT i z) := by
  obtain ⟨fv, hfv, -, -⟩ := hwf.valueId bid fb hb z hz
  obtain ⟨gv, hgv, hsv⟩ := R.value z fv hfv
  unfold phiStep
  simp only [show (Ctx.make tabs f).f = f from rfl, show (Ctx.make tabs g).f = g from rfl,
    hfv, hgv]
  rcases hsv with hs | hne
  · obtain ⟨-, hop, -, -, hty, -, hargs⟩ := StructStore.ssSame_spec hs
    rw [hop, hargs, tys_of_value hgv, tys_of_value hfv, hty]
    by_cases hph : fv.op = .Phi
    · simp only [hph, beq_self_eq_true, ↓reduceIte]
      cases ha : fv.args[i]? with
      | none => exact .stuck _ _
      | some a =>
        simp only
        cases hx : (frS.regs[a]?).join with
        | none => exact .stuck _ _
        | some x =>
          obtain ⟨bid', b', hb', hab⟩ := hwf.argListed bid fb z fv ⟨hb, hz, hfv⟩ a
            (Array.mem_of_getElem? ha)
          obtain ⟨va, hva, -, -⟩ := hwf.valueId bid' b' hb' a hab
          obtain ⟨ga, hga, -⟩ := R.value a va hva
          obtain ⟨y, hy, hxy⟩ := hr a va x hva (by rw [hga]; rfl) (Option.join_eq_some_iff.1 hx)
          rw [hy]
          exact .ok (.some z (retype_mono _ hxy))
    · have : (fv.op == .Phi) = false := by simpa using hph
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      exact .ok .none
  · obtain ⟨d⟩ := hne
    have hu := d.hu
    rw [hfv] at hu; cases hu
    have hw := d.hw
    rw [hgv] at hw; cases hw
    have h1 : (d.u.op == .Phi) = false := by
      rcases psSel_some d.hk with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl
    have h2 : (d.w.op == .Phi) = false := by rw [d.hwop]; rfl
    simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
    exact .ok .none

/-- **The terminators** on refined controls. -/
theorem term_rel {G GT : Frame} (hr : RR f g G.regs GT.regs) {bid : ID} {fb gb : Block}
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

end

/-- The simulation relation: the same block and edge, `SimAt`. -/
def SimR (env : Env) (tabs : Tables) (f g : Func) (frS : Frame) (bS : ID) (iS : Nat) (frT : Frame)
    (bT : ID) (iT : Nat) : Prop :=
  bT = bS ∧ iT = iS ∧ SimAt env tabs f g frS frT bS iS

/-- **One block step.** -/
theorem step {ce ce' : CheckEnv} (hwf : WF ce f) (hc : CertOK f) (hwg : WF ce' g)
    (R : PSRel tabs f g) (hE : env.Mono) {frS frT : Frame} {bid : ID} {i : Nat}
    (hA : SimAt env tabs f g frS frT bid i) :
    StepSimE (SimR env tabs f g) (blockStep env (Ctx.make tabs f) frS bid i)
      (blockStep env (Ctx.make tabs g) frT bid i) := by
  have hbt := CSE.pre_tree hwf hc hA.pre
  unfold blockStep
  simp only [show (Ctx.make tabs f).f = f from rfl, show (Ctx.make tabs g).f = g from rfl]
  cases hfb : f.block? bid with
  | none => exact True.intro
  | some fb =>
  obtain ⟨gb, hgb, hk, hctl, hvals, hsch⟩ := R.block bid hbt.1 fb hfb
  obtain ⟨gb', hgb', hgid, hsucc, -⟩ := CopyElim.cfgView_block R.cfg hfb
  rw [hgb] at hgb'; cases hgb'
  obtain ⟨fb', hfb', hfid⟩ := hwf.blockId bid hbt.1
  rw [hfb] at hfb'; cases hfb'
  rw [hgb]
  simp only
  -- the parts of the source's block entry, and the target's
  have parts : ∀ r, enterBlock env (Ctx.make tabs f) frS fb i = r → (∀ msg, r ≠ .stuck msg) →
      ∃ ps ps' o, fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) frS i) = .ok ps ∧
        PhisRefine ps ps' ∧ schedule f fb = some o ∧
        evalAll env (Ctx.make tabs f) { frS with regs := setPhis ps frS.regs } o.toList = r ∧
        enterBlock env (Ctx.make tabs g) frT gb i =
          evalAll env (Ctx.make tabs g) { frT with regs := setPhis ps' frT.regs } o.toList := by
    intro r hen hr
    obtain ⟨ps, oS, hps, hsched, hev⟩ := CSE.enterBlock_split hen hr
    rw [hfid, sched_of_block hfb] at hsched
    have hrel := StructStore.phis_rel (F := phiStep (Ctx.make tabs f) frS i)
      (G := phiStep (Ctx.make tabs g) frT i) (l := fb.values.toList) (E := [])
      (fun z hz => phiStep_rel hwf R hA.rr ⟨hbt.1, hfb⟩ (Array.mem_toList_iff.1 hz) i)
      (fun _ h => nomatch h)
    rw [hps, List.append_nil, ← hvals] at hrel
    generalize hT' : gb.values.toList.filterMapM (phiStep (Ctx.make tabs g) frT i) = rT at hrel
    cases hrel with
    | ok hpr =>
      refine ⟨ps, _, oS, hps, hpr, hsched, hev, CSE.enterBlock_of_parts hT' ?_⟩
      rw [hgid, hfid, sched_of_block hgb, hsch, hsched]
  -- the block's evaluation
  have blk : ∀ ps ps' o,
      fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) frS i) = .ok ps →
      PhisRefine ps ps' → schedule f fb = some o →
      Res.Rel (Inv tabs f g bid)
        (evalAll env (Ctx.make tabs f) { frS with regs := setPhis ps frS.regs } o.toList)
        (evalAll env (Ctx.make tabs g) { frT with regs := setPhis ps' frT.regs } o.toList) := by
    intro ps ps' o hps hpr ho
    obtain ⟨-, -, hmem⟩ := schedule_topo (valuesOwn hwf hbt.1 hfb)
      (hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩) ho
    refine loop hwf hc R hE hbt hfb o.toList _ _ (fun z hz => (hmem z).1 hz)
      ⟨by simp [setPhis_size, hA.size], by simp [setPhis_size, hA.sizeT], ?_,
        setPhis_rr hpr hA.rr (by rw [hA.size, hA.sizeT, R.size]; exact Nat.le_refl _),
        fact_entry hwf hc hA.pre hA.inv hA.size hA.typed hfb hps⟩
    conv => lhs; rw [hA.frame]
  cases hen : enterBlock env (Ctx.make tabs f) frS fb i with
  | stuck msg => exact True.intro
  | panic e m =>
    obtain ⟨ps, ps', o, hps, hpr, ho, hev, hT⟩ := parts _ hen nofun
    have hl := blk ps ps' o hps hpr ho
    rw [hev] at hl
    rw [hT]
    generalize evalAll env (Ctx.make tabs g) { frT with regs := setPhis ps' frT.regs } o.toList = rT
      at hl ⊢
    cases hl with
    | panic e hm => exact ⟨_, rfl, hm⟩
  | ok G =>
  obtain ⟨ps, ps', o, hps, hpr, ho, hev, hT⟩ := parts _ hen nofun
  have hl := blk ps ps' o hps hpr ho
  rw [hev] at hl
  rw [hT]
  generalize evalAll env (Ctx.make tabs g) { frT with regs := setPhis ps' frT.regs } o.toList = rT
    at hl ⊢
  cases hl with
  | @ok _ GT hI =>
  simp only
  obtain ⟨hD, -, -⟩ := dinv_enter hwf hc hbt.1 hfb hA.size (CSE.pre_strict hc hA.pre).1 hen
  have hty := typed_enter hwf hbt.1 hfb hA.size hA.typed hen
  have hst := term_rel hwf R hI.rr ⟨hbt.1, hfb⟩ hk (by rw [hsucc]) (by rw [hgid]) hctl
  generalize hS : stepTerm G fb = sS at hst ⊢
  generalize stepTerm GT gb = sT at hst ⊢
  cases hst with
  | ok hn =>
    cases hn with
    | goto e =>
      have he : (⟨e.b, e.i⟩ : Edge) ∈ fb.succs := by cases e; exact AtomSim.stepTerm_goto_mem hS
      exact ⟨GT, e, rfl, rfl, rfl,
        { size := hI.sz, sizeT := hI.szT, frame := hI.frame, rr := hI.rr, typed := hty
          pre := .inr ⟨bid, fb, hbt.1, hfb, hbt.2, he, hD, DSE.repInv_nil _ _⟩
          inv := .inr ⟨bid, fb, hbt.1, hfb, hbt.2, he, hD, hI.fact⟩ }⟩
    | ret hl hm => exact ⟨_, _, rfl, hl, hm⟩
  | panic e hm => exact ⟨_, rfl, hm⟩
  | stuck msg r => exact True.intro

/-- **Selections of `Phi`s of `SliceMake`s turned copies refine** under monotone contracts. -/
theorem ps_refines {ce ce' : CheckEnv} (hf : check ce f = .ok ()) (hg : check ce' g = .ok ())
    (hrel : psRel tabs f g = true) : RefinesUnder Env.Mono tabs g tabs f := by
  have hwf := check_wf hf
  have hwg := check_wf hg
  have hc := certOK_of_check (check_domCert hf)
  have R := psRel_spec hrel
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
        pre := .inl rfl
        inv := .inl rfl }
    rw [show (Ctx.make tabs g).f.entry = (Ctx.make tabs f).f.entry from
      CopyElim.cfgView_entry R.cfg]
    refine finish_refines hd (runLoop_simE (SimR env tabs f g)
      (fun frS bS iS frT bT iT hR => ?_) fuel _ _ _ _ _ _ ⟨rfl, rfl, hA0⟩ (finish_defined hd))
    obtain ⟨rfl, rfl, hA⟩ := hR
    exact step hwf hc hwg R hE hA

end GoFV.Proof.PhiSel

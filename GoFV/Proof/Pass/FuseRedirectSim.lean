import GoFV.Proof.Pass.FuseRedirectDecide
import GoFV.Proof.Pass.FusePlainSim
import GoFV.Proof.AgreeIdx
import GoFV.Proof.Enter
import GoFV.Proof.SimIH
import GoFV.Proof.AtomSimSet
import GoFV.Proof.Pass.DeadEnter

variable [GoFV.SSA.Sem.Addrs]

/-!
# One checked redirect refines

`refines_of_step`: if `g` is `f` with one checked redirect `p → b` ⇒ `p → child`
(`Base` + `Shape`, `f` with dominated uses), every run of `f` is a run of `g`. Macro-step
simulation (`runLoop_simIH`) with frames agreeing outside `b`'s values (`AgrP`; `b` holds at
most its control, which nothing else reads): every block steps alike in both, entered along
related edge indices (`IdxR`: `b`'s last predecessor moved to `k`; `child` entered along `b`'s
edge by the source and along `p`'s new edge by the target), the target's edges renumbered by
`r` (`normal_step`). When the source leaves `p` towards `b`, it runs `b` and, by the redirect
decision (`decide_ctl`), continues to `child`; the target goes there directly (`via_b`).
-/

namespace GoFV.Proof.FuseRedirect

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.Fuse GoFV.Opt.Fuse.Redir GoFV.Opt.RewriteCheck
  GoFV.Opt.ProveCheck GoFV.Proof GoFV.Proof.Term GoFV.Proof.AtomSim GoFV.Proof.ProveCheck Dom

/-! ## Entering a block whose values read nothing the frames disagree on -/

section
variable {env : Env} {ctxS ctxT : Ctx}

theorem stepV_agreeA {frS frT : Frame} {X : ID → Prop} {x : ID} {l : List ID} (hx : x ∈ l)
    (hc : CtxAgree ctxS ctxT l) (hu : ∀ v, ctxS.f.value? x = some v → ∀ a ∈ v.args, ¬ X a)
    (hfr : frT = { frS with regs := frT.regs }) (hag : ∀ a, ¬ X a → frT.regs[a]? = frS.regs[a]?) :
    stepV env ctxT frT x = stepV env ctxS frS x := by
  unfold stepV
  have hsem := hc.value x hx
  cases hv : ctxS.f.value? x with
  | none =>
    rw [hv] at hsem
    cases hv' : ctxT.f.value? x with
    | none => rfl
    | some _ => rw [hv'] at hsem; exact hsem.elim
  | some v =>
    rw [hv] at hsem
    cases hv' : ctxT.f.value? x with
    | none => rw [hv'] at hsem; exact hsem.elim
    | some v' =>
      rw [hv'] at hsem
      exact evalValue_ctx_congr hsem hfr (fun a ha => hag a (hu v hv a ha))
        (hc.tys x hx v hv) hc.tabs hc.params hc.act

/-- **Evaluating a list in frames agreeing outside `X`**, where no value reads `X`: afterwards
they also agree on the list. -/
theorem evalAll_agreeA :
    ∀ {l : List ID} {X : ID → Prop} {frS frT : Frame}, CtxAgree ctxS ctxT l →
      (∀ x ∈ l, ∀ v, ctxS.f.value? x = some v → ∀ a ∈ v.args, ¬ X a) →
      frT = { frS with regs := frT.regs } → frT.regs.size = frS.regs.size →
      (∀ a, ¬ X a → frT.regs[a]? = frS.regs[a]?) →
      (∀ G, evalAll env ctxS frS l = .ok G → ∃ GT, evalAll env ctxT frT l = .ok GT ∧
        GT = { G with regs := GT.regs } ∧ GT.regs.size = G.regs.size ∧
        ∀ a, (¬ X a ∨ a ∈ l) → GT.regs[a]? = G.regs[a]?) ∧
      (∀ e m, evalAll env ctxS frS l = .panic e m → evalAll env ctxT frT l = .panic e m)
  | [], X, frS, frT, _, _, hfr, hs, hag =>
    ⟨fun G h => by
      cases h
      exact ⟨frT, rfl, hfr, hs, fun a ha => ha.elim (hag a) (fun h => absurd h List.not_mem_nil)⟩,
     fun _ _ h => (nomatch h)⟩
  | x :: l, X, frS, frT, hc, hu, hfr, hs, hag => by
    have hx := stepV_agreeA (env := env) List.mem_cons_self hc (hu x List.mem_cons_self) hfr hag
    rw [evalAll_cons, evalAll_cons, hx]
    cases hst : stepV env ctxS frS x with
    | panic e m => exact ⟨fun _ h => (nomatch h), fun _ _ h => h⟩
    | stuck msg => exact ⟨fun _ h => (nomatch h), fun _ _ h => (nomatch h)⟩
    | ok y =>
      simp only
      obtain ⟨h1, h2⟩ := evalAll_agreeA (X := fun a => X a ∧ a ≠ x)
        (hc.mono fun z hz => List.mem_cons_of_mem _ hz)
        (fun z hz v hv a ha h => hu z (List.mem_cons_of_mem _ hz) v hv a ha h.1)
        (frS := frS.set x y) (frT := frT.set x y) (by rw [hfr]; rfl)
        (by simp [Frame.set, hs]) (fun a ha => by
          by_cases hxa : x = a
          · subst hxa
            simp only [Frame.set, Array.set!_eq_setIfInBounds,
              Array.getElem?_setIfInBounds_self, hs]
          · rw [Frame.set_regs_ne hxa, Frame.set_regs_ne hxa]
            exact hag a fun h => ha ⟨h, Ne.symm hxa⟩)
      refine ⟨fun G hG => ?_, h2⟩
      obtain ⟨GT, hGT, h3, h4, h5⟩ := h1 G hG
      refine ⟨GT, hGT, h3, h4, fun a ha => h5 a ?_⟩
      rcases ha with ha | ha
      · exact .inl fun h => ha h.1
      · rcases List.mem_cons.1 ha with rfl | ha
        · exact .inl fun h => h.2 rfl
        · exact .inr ha

/-- **Entering a block** (along renumbered edges, with the target's `Phi` steps given) in frames
agreeing outside `X`, where the block's values read nothing of `X`: afterwards the frames also
agree on the block's scheduled values. -/
theorem enterBlock_agreeA {frS frT : Frame} {bS bT : Block} {iS iT : Nat} {X : ID → Prop}
    (hid : bT.id = bS.id) (hv : bT.values = bS.values)
    (hps : ∀ ps, bS.values.toList.filterMapM (phiStep ctxS frS iS) = .ok ps →
      bS.values.toList.filterMapM (phiStep ctxT frT iT) = .ok ps)
    (hsched : (ctxT.sched[bS.id]?).join = (ctxS.sched[bS.id]?).join)
    (horder : ∀ o, (ctxS.sched[bS.id]?).join = some o →
      CtxAgree ctxS ctxT o.toList ∧ ∀ x ∈ o.toList, ∀ v, ctxS.f.value? x = some v →
        ∀ a ∈ v.args, ¬ X a)
    (hfr : frT = { frS with regs := frT.regs }) (hs : frT.regs.size = frS.regs.size)
    (hag : ∀ a, ¬ X a → frT.regs[a]? = frS.regs[a]?) :
    (∀ G, enterBlock env ctxS frS bS iS = .ok G → ∃ GT, enterBlock env ctxT frT bT iT = .ok GT ∧
      GT = { G with regs := GT.regs } ∧ GT.regs.size = G.regs.size ∧
      ∃ o, (ctxS.sched[bS.id]?).join = some o ∧
        ∀ a, (¬ X a ∨ a ∈ o.toList) → GT.regs[a]? = G.regs[a]?) ∧
    (∀ e m, enterBlock env ctxS frS bS iS = .panic e m →
      enterBlock env ctxT frT bT iT = .panic e m) := by
  rw [enterBlock_eq, enterBlock_eq, hv, hid, hsched]
  cases hpsS : bS.values.toList.filterMapM (phiStep ctxS frS iS) with
  | panic e m => exact absurd hpsS filterMapM_phi_not_panic
  | stuck msg => exact ⟨fun _ h => (nomatch h), fun _ _ h => (nomatch h)⟩
  | ok ps =>
    rw [hps ps hpsS]
    simp only [Res.bind]
    cases ho : (ctxS.sched[bS.id]?).join with
    | none => exact ⟨fun _ h => (nomatch h), fun _ _ h => (nomatch h)⟩
    | some o =>
      obtain ⟨hco, huo⟩ := horder o ho
      obtain ⟨h1, h2⟩ := evalAll_agreeA (env := env) hco huo
        (frS := { frS with regs := setPhis ps frS.regs })
        (frT := { frT with regs := setPhis ps frT.regs }) (by rw [hfr])
        (by simp [setPhis_size, hs]) (setPhis_agree ps hs hag)
      refine ⟨fun G hG => ?_, h2⟩
      obtain ⟨GT, hGT, h3, h4, h5⟩ := h1 G hG
      exact ⟨GT, hGT, h3, h4, o, rfl, h5⟩

end

/-- A term node never panics. -/
theorem evalValue_term_ne_panic {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {e : Panic}
    {m : Mem} (ht : termOp v.op = true) : evalValue env ctx fr v ≠ .panic e m := by
  intro h
  have hr := regs_of_panic h
  rw [evalValue_of_regs hr, evalOp_term ht] at h
  cases h

/-! ## The setting -/

/-- The block a redirect may leave out: `b`'s values (at most its control). -/
def XB (B : Block) (a : ID) : Prop := a ∈ B.values

/-- Frames agreeing outside `X`. -/
def AgrP (X : ID → Prop) (frS frT : Frame) : Prop :=
  frT = { frS with regs := frT.regs } ∧ frT.regs.size = frS.regs.size ∧
    ∀ a, ¬ X a → frT.regs[a]? = frS.regs[a]?

/-- The target's predecessor index for the source's `i` at block `y`. -/
def tIdx (st : Site) (y : ID) (i : Nat) : Nat := if y = st.b ∧ i = st.n then st.k else i

/-- The edge indices the simulation relates: renumbered at `b` (never the redirected `k`), or
`child` entered along `b`'s edge by the source and along `p`'s new edge by the target. -/
def IdxR (st : Site) (C : Block) (y iS iT : Nat) : Prop :=
  ((y ≠ st.b ∨ iS ≠ st.k) ∧ iT = tIdx st y iS ∧ (y = st.child → iS < C.preds.size)) ∨
    (y = st.child ∧ iS = st.ai ∧ iT = st.cn)

/-- The simulation relation (see the module doc). -/
def Rel (env : Env) (tabs : Tables) (f : Func) (st : Site) (B C : Block) (frS : Frame)
    (bS iS : Nat) (frT : Frame) (bT iT : Nat) : Prop :=
  bT = bS ∧ bS ∈ f.blocks ∧ IdxR st C bS iS iT ∧ Reachable f bS ∧
    frS.regs.size = f.valueTab.size ∧
    DInv env (Ctx.make tabs f) (fun a => SDom f a bS ∧ a ≠ bS) frS ∧
    Proof.Typed (Ctx.make tabs f) frS ∧ AgrP (XB B) frS frT

/-- A checked redirect of a function with dominated uses, with its shape. -/
structure Setup (ce : CheckEnv) (tabs : Tables) (f g : Func) (st : Site) (B P C : Block) : Prop where
  base : Base ce tabs f g st
  H : Shape f st B P C
  dom : UseDom f

variable {ce : CheckEnv} {tabs : Tables} {f g : Func} {st : Site} {B P C : Block}

namespace Setup

variable (S : Setup ce tabs f g st B P C)
include S

theorem wf : WF ce f := S.base.wf

theorem domR : DomRel f (Reachable f) (SDom f) := S.dom.domRel

theorem tys (z : ID) : (Ctx.make tabs g).tys[z]? = (Ctx.make tabs f).tys[z]? := by
  obtain ⟨hn, hv⟩ := S.base.rel.value z
  have hsz := S.base.rel.vsize
  simp only [Ctx.make, Array.getElem?_map]
  by_cases hlt : z < f.valueTab.size
  · have hlt' : z < g.valueTab.size := by rw [hsz]; exact hlt
    rw [Array.getElem?_eq_getElem hlt, Array.getElem?_eq_getElem hlt']
    simp only [Option.map_some]
    congr 1
    have hfv : f.value? z = f.valueTab[z] := by
      simp [Func.value?, Array.getElem?_eq_getElem hlt]
    have hgv : g.value? z = g.valueTab[z] := by
      simp [Func.value?, Array.getElem?_eq_getElem hlt']
    cases hf : f.valueTab[z] with
    | none =>
      rw [hf] at hfv
      have := hn hfv
      rw [hgv] at this
      rw [this]
    | some v =>
      rw [hf] at hfv
      obtain ⟨w, hw, -, hty, -⟩ := hv v hfv
      rw [hgv] at hw
      rw [hw]
      simp [valueTy, hty]
  · have h1 : g.valueTab[z]? = none :=
      Array.getElem?_eq_none (by rw [hsz]; exact Nat.le_of_not_lt hlt)
    have h2 : f.valueTab[z]? = none := Array.getElem?_eq_none (Nat.le_of_not_lt hlt)
    rw [h1, h2]

/-- What the contexts agree on, for the non-`Phi` values of a listed block. -/
theorem ctxAgree {y : ID} (hy : y ∈ f.blocks) {Y : Block} (hY : f.block? y = some Y)
    {l : List ID} (hl : ∀ x ∈ l, x ∈ Y.values ∧ ∃ v, f.value? x = some v ∧ v.op ≠ .Phi) :
    CtxAgree (Ctx.make tabs f) (Ctx.make tabs g) l := by
  refine ⟨fun x hx => ?_, fun x _ v hv => ?_, rfl, Dead.params_eq S.base.rel.ownAux, rfl⟩
  · obtain ⟨-, v, hv, hnp⟩ := hl x hx
    obtain ⟨-, hval⟩ := S.base.rel.value x
    obtain ⟨w, hw, h1, -, h3, h4, h5, -, -, h8⟩ := hval v hv
    change SemEq (f.value? x) (g.value? x)
    rw [hv, hw]
    exact ⟨h1, h5, h3, h4, h8 fun h => hnp h.1⟩
  · exact S.tys v.id

/-- `b`'s values are read by nothing (but `b`'s terminator). -/
theorem unreadX {y : ID} (hy : y ∈ f.blocks) {Y : Block} (hY : f.block? y = some Y) {x : ID}
    (hx : x ∈ Y.values) {v : Value} (hv : f.value? x = some v) {a : ID} (ha : a ∈ v.args) :
    ¬ XB B a := by
  intro hm
  obtain ⟨rfl, hne⟩ := S.base.b_val S.H hm
  exact (S.base.rel.unread S.H.hB hne hy hY).1 x hx v hv ha

/-- The schedules agree. -/
theorem sched {y : ID} (hy : y ∈ f.blocks) {Y : Block} (hY : f.block? y = some Y) :
    ((Ctx.make tabs g).sched[Y.id]?).join = ((Ctx.make tabs f).sched[Y.id]?).join := by
  obtain ⟨Y0, hY0, hid⟩ := S.wf.blockId y hy
  rw [hY] at hY0; cases hY0
  rw [hid, sched_of_block hY, sched_of_block (S.base.gblock S.H hy hY)]
  unfold schedule
  rw [schedNodes_phiEq (f := f) (g := g) (fb := Y) (gb := st.expect y Y) expect_values
    fun x _ => ⟨(S.base.rel.value x).1, fun v hv => by
      obtain ⟨w, hw, h1, -, -, -, h5, -, -, h8⟩ := (S.base.rel.value x).2 v hv
      exact ⟨w, hw, h1, h5, fun hnp => h8 fun h => hnp h.1⟩⟩]

/-- **Entering a listed block** in related frames along related indices: the target enters its
`expect`ed block; afterwards the frames agree outside `X` and on the block's controls. -/
theorem enter {env : Env} {y : ID} (hy : y ∈ f.blocks) {Y : Block} (hY : f.block? y = some Y)
    {iS iT : Nat} (hI : IdxR st C y iS iT) {frS frT : Frame} (hA : AgrP (XB B) frS frT)
    (hsz : frS.regs.size = f.valueTab.size) :
    (∀ G, enterBlock env (Ctx.make tabs f) frS Y iS = .ok G →
      ∃ GT, enterBlock env (Ctx.make tabs g) frT (st.expect y Y) iT = .ok GT ∧
        AgrP (XB B) G GT ∧ ∀ c ∈ Y.controls, GT.regs[c]? = G.regs[c]?) ∧
    (∀ e m, enterBlock env (Ctx.make tabs f) frS Y iS = .panic e m →
      enterBlock env (Ctx.make tabs g) frT (st.expect y Y) iT = .panic e m) := by
  have hwf := S.wf
  have hcb := S.H.cb
  have hown := valuesOwn hwf hy hY
  have hnd := hwf.valuesNodup y Y ⟨hy, hY⟩
  -- the `Phi` steps
  have hps : ∀ ps, Y.values.toList.filterMapM (phiStep (Ctx.make tabs f) frS iS) = .ok ps →
      Y.values.toList.filterMapM (phiStep (Ctx.make tabs g) frT iT) = .ok ps := by
    intro ps h
    refine filterMapM_phi_rel (fun z hz v hv => ?_) (fun z _ => S.tys z) h
    have hzY := Array.mem_toList_iff.1 hz
    change f.value? z = some v at hv
    obtain ⟨-, hval⟩ := S.base.rel.value z
    obtain ⟨w, hw, -, -, -, -, hop, hb, hphi, hargs⟩ := hval v hv
    refine ⟨w, hw, hop, fun hph => ⟨?_, fun a ha => hA.2.2 a
      (S.unreadX hy hY hzY hv (Array.mem_of_getElem? ha))⟩⟩
    obtain ⟨-, hvb, -⟩ := placed_in hwf hy hY hzY hv
    by_cases hyb : y = st.b
    · subst hyb
      rw [S.H.hB] at hY; cases hY
      exact absurd hph (S.base.b_noPhi S.H hzY hv)
    have hti : tIdx st y iS = iS := by unfold tIdx; rw [if_neg fun h => hyb h.1]
    by_cases hyc : y = st.child
    · subst hyc
      rw [S.H.hC] at hY; cases hY
      obtain ⟨hlt, heq⟩ := hphi hph hvb
      have har : v.args.size = C.preds.size := hwf.phiArity _ C z v ⟨⟨hy, S.H.hC⟩, hzY, hv⟩ hph
      rw [heq]
      rcases hI with ⟨-, rfl, hlt'⟩ | ⟨-, rfl, rfl⟩
      · rw [hti, Array.getElem?_push_lt (by omega), Array.getElem?_eq_getElem (by omega)]
      · rw [← S.H.cpsz, ← har, Array.getElem?_push_size, getElem!_pos v.args st.ai hlt,
          Array.getElem?_eq_getElem hlt]
    · rw [hargs fun h => hyc (hvb.symm.trans h.2)]
      rcases hI with ⟨-, rfl, -⟩ | ⟨h, -⟩
      · rw [hti]
      · exact absurd h hyc
  have horder : ∀ o, ((Ctx.make tabs f).sched[Y.id]?).join = some o →
      CtxAgree (Ctx.make tabs f) (Ctx.make tabs g) o.toList ∧ ∀ x ∈ o.toList, ∀ v,
        (Ctx.make tabs f).f.value? x = some v → ∀ a ∈ v.args, ¬ XB B a := by
    intro o ho
    obtain ⟨Y0, hY0, hid⟩ := hwf.blockId y hy
    rw [hY] at hY0; cases hY0
    rw [hid, sched_of_block hY] at ho
    obtain ⟨-, -, omem⟩ := schedule_topo hown hnd ho
    exact ⟨S.ctxAgree hy hY fun x hx => (omem x).1 hx, fun x hx v hv a ha =>
      S.unreadX hy hY ((omem x).1 hx).1 hv ha⟩
  obtain ⟨h1, h2⟩ := enterBlock_agreeA (env := env) expect_id expect_values hps (S.sched hy hY)
    horder hA.1 hA.2.1 hA.2.2
  refine ⟨fun G hG => ?_, h2⟩
  obtain ⟨GT, hGT, h3, h4, o, ho, h5⟩ := h1 G hG
  refine ⟨GT, hGT, ⟨h3, h4, fun a ha => h5 a (.inl ha)⟩, fun c hc => h5 c ?_⟩
  by_cases hyb : y = st.b
  · subst hyb
    rw [S.H.hB] at hY; cases hY
    rcases S.H.bvals with h | ⟨h, hok⟩
    · exact .inl fun hm => by unfold XB at hm; rw [h] at hm; simp at hm
    · right
      obtain ⟨Y0, hY0, hid⟩ := hwf.blockId st.b hy
      rw [S.H.hB] at hY0; cases hY0
      rw [hid, sched_of_block S.H.hB] at ho
      obtain ⟨-, -, omem⟩ := schedule_topo hown hnd ho
      rw [S.H.bctl] at hc
      simp only [List.mem_toArray, List.mem_singleton] at hc
      subst hc
      obtain ⟨v, hv, -, ht, -⟩ := ctlOK_spec hok
      refine (omem _).2 ⟨by rw [h]; simp, v, hv, fun hp => ?_⟩
      rw [hp] at ht; exact absurd ht (by decide)
  · left
    intro hm
    obtain ⟨rfl, hne⟩ := S.base.b_val S.H hm
    exact (S.base.rel.unread S.H.hB hne hy hY).2 hyb hc

/-- Lemma (D), reachability and size along a source block step. -/
theorem dinv_step {env : Env} {y : ID} (hy : y ∈ f.blocks) {Y : Block}
    (hY : f.block? y = some Y) (ht : Reachable f y) {fr G : Frame} {i : Nat}
    (hs : fr.regs.size = f.valueTab.size)
    (hdi : DInv env (Ctx.make tabs f) (fun a => SDom f a y ∧ a ≠ y) fr)
    (h : enterBlock env (Ctx.make tabs f) fr Y i = .ok G) {e : Edge} (he : e ∈ Y.succs) :
    DInv env (Ctx.make tabs f) (fun a => SDom f a e.b ∧ a ≠ e.b) G ∧
      Reachable f e.b ∧ G.regs.size = f.valueTab.size ∧ e.b ∈ f.blocks := by
  obtain ⟨h1, h2, h3⟩ := dinv_enter_rel S.wf S.domR hy hY hs hdi h
  obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 he
  exact ⟨dinv_edge_rel S.domR hy hY ht he h1, (S.domR.edge hy hY ht he).1, by rw [h3, hs],
    (S.wf.succLink y Y ⟨hy, hY⟩ k e hk).1⟩

/-- A term argument of a listed node of a dependency order is listed. -/
theorem topo_arg : ∀ {L : List ID}, topoOK f L = true → ∀ {x : ID}, x ∈ L → ∀ {v : Value},
    f.value? x = some v → ∀ {a : ID}, a ∈ v.args → isTerm f a = true → a ∈ L
  | [], _, _, hx, _, _, _, _, _ => by simp at hx
  | y :: rest, hL, x, hx, v, hv, a, ha, hat => by
    unfold topoOK at hL
    rw [Bool.and_eq_true] at hL
    rcases List.mem_cons.1 hx with rfl | hx'
    · have h1 := hL.1
      rw [show Redir.argsOf f x = v.args by simp [Redir.argsOf, hv]] at h1
      have := (Array.all_eq_true'.1 h1) a ha
      rw [hat, Bool.not_true, Bool.false_or] at this
      exact List.mem_cons_of_mem _ (mem_of_contains this)
    · exact List.mem_cons_of_mem _ (topo_arg hL.2 hx' hv ha hat)

/-- **Through `b` to `child`**: the source leaves `p` towards `b` and, by the redirect decision,
continues from `b` to `child`; the target goes from `p` to `child` directly. -/
theorem via_b {env : Env} {n : Nat}
    (ih : SimUpTo env (Ctx.make tabs f) (Ctx.make tabs g) (Rel env tabs f st B C) n)
    {fr G GT : Frame} {iS : Nat} (hp : Reachable f st.p) (hs : fr.regs.size = f.valueTab.size)
    (hdi : DInv env (Ctx.make tabs f) (fun a => SDom f a st.p ∧ a ≠ st.p) fr)
    (hG : enterBlock env (Ctx.make tabs f) fr P iS = .ok G)
    (hterm : stepTerm G P = .ok (.goto ⟨st.b, st.k⟩))
    (htyG : Proof.Typed (Ctx.make tabs f) G) (hAG : AgrP (XB B) G GT)
    (hd : (runLoop env (Ctx.make tabs f) n G st.b st.k).Defined) :
    ∃ fuelT, LoopRefines Eq (runLoop env (Ctx.make tabs f) n G st.b st.k)
      (runLoop env (Ctx.make tabs g) fuelT GT st.child st.cn) := by
  have hwf := S.wf
  have H := S.H
  have hpm := S.base.p_in H
  have hbm := H.bIn
  have hpsucc := S.base.p_succ H
  -- lemma (D) at the end of `p`
  obtain ⟨hdiP, hGfr, hGs⟩ := dinv_enter_rel hwf S.domR hpm H.hP hs hdi hG
  have hGs' : G.regs.size = f.valueTab.size := by rw [hGs, hs]
  -- `p`'s control holds the branch into `b`
  obtain ⟨bv, e', hreg, he', hee⟩ := stepTerm_if H.pkind H.pctl hterm
  cases hee
  have hidx : (if bv then 0 else 1) = st.pi := by
    have h1 := S.base.into_b H.hB hpm H.hP he'
    rw [H.bk] at h1
    exact (Edge.mk.inj (Option.some.inj h1)).2.symm
  have hcpv : rv G st.cp = .bool (st.pi == 0) := by
    rw [rv_of hreg, ← hidx]; cases bv <;> rfl
  have hcpD : DomP f st.p st.cp := by
    have hc : st.cp ∈ P.controls := by rw [H.pctl]; simp
    obtain ⟨u, U, hPu, hub, -, -, -⟩ := blockOf_listed hwf (hwf.ctrlListed _ P ⟨hpm, H.hP⟩ _ hc)
    exact ⟨u, hPu, by rw [hub]; exact S.domR.ctrlUse hpm H.hP hp hc⟩
  -- the decision
  have hdec := S.base.rel.decide
  unfold decideOK at hdec
  simp only [Bool.and_eq_true] at hdec
  obtain ⟨⟨⟨hdc, hL⟩, hcpL⟩, hctlL⟩ := hdec
  have hA := asmXHolds hwf S.dom hdiP htyG hL hcpL hcpD hcpv
  -- `b` is reachable, the edge `p → b`
  have hpb : (⟨st.b, st.k⟩ : Edge) ∈ P.succs := Array.mem_of_getElem? hpsucc
  have hbr : Reachable f st.b := (S.domR.edge hpm H.hP hp hpb).1
  have hdom : ∀ a, SDom f a st.b → a ≠ st.b → SDom f a st.p := (S.domR.edge hpm H.hP hp hpb).2
  have hdiB : DInv env (Ctx.make tabs f) (fun a => SDom f a st.b ∧ a ≠ st.b) G :=
    dinv_edge_rel S.domR hpm H.hP hp hpb hdiP
  cases n with
  | zero => exact absurd hd runLoop_zero_not_defined
  | succ m =>
  cases hst : blockStep env (Ctx.make tabs f) G st.b st.k with
  | stuck => exact absurd hd (runLoop_stuck hst)
  | panic e mm =>
    exfalso
    obtain ⟨B2, hB2, hpan⟩ := blockStep_panic hst
    change f.block? st.b = some B2 at hB2
    rw [H.hB] at hB2; cases hB2
    obtain ⟨ps, o, pre, r, post, Gpre, -, -, -, -, hr, -, -, -, -, -, hrB, rv', hrv, -, -⟩ :=
      enter_panic_facts (tabs := tabs) hwf hbm H.hB hGs' hpan
    obtain ⟨rfl, -⟩ := S.base.b_val H hrB
    rcases H.bvals with h | ⟨-, hok⟩
    · rw [h] at hrB; simp at hrB
    · obtain ⟨v, hv, -, ht, -⟩ := ctlOK_spec hok
      unfold stepV at hr
      rw [show (Ctx.make tabs f).f.value? st.ctl = some v from hv] at hr
      exact evalValue_term_ne_panic ht hr
  | ret rs mm =>
    obtain ⟨B2, G2, hB2, -, hterm2⟩ := blockStep_ret hst
    change f.block? st.b = some B2 at hB2
    rw [H.hB] at hB2; cases hB2
    obtain ⟨_, _, -, -, h⟩ := stepTerm_if H.bkind H.bctl hterm2
    cases h
  | goto G2 e2 =>
    obtain ⟨B2, hB2, hG2, hterm2⟩ := blockStep_goto hst
    change f.block? st.b = some B2 at hB2
    rw [H.hB] at hB2; cases hB2
    obtain ⟨g1, g2, g3, g4, -⟩ := enter_ok_facts (tabs := tabs) hwf hbm H.hB hGs' hG2
    obtain ⟨bb, e3, hreg2, he3, hee⟩ := stepTerm_if H.bkind H.bctl hterm2
    have he2 : e2 = e3 := by injection hee
    subst he2
    -- the term of `ctl` settles on its register after `b`
    have hconv : ∃ N, ∀ n, N ≤ n → den f.value? tabs (rv G) n st.ctl = rv G2 st.ctl := by
      rcases H.bvals with hbv | ⟨hbv, hok⟩
      · have hc : st.ctl ∈ B.controls := by rw [H.bctl]; simp
        obtain ⟨u, U, hPu, hub, hU, hcU, -⟩ :=
          blockOf_listed hwf (hwf.ctrlListed _ B ⟨hbm, H.hB⟩ _ hc)
        have hne : blockOf f st.ctl ≠ st.b := fun h => by
          rw [h, H.hB] at hU; cases hU; rw [hbv] at hcU; simp at hcU
        have hD : DomP f st.p st.ctl :=
          ⟨u, hPu, by rw [hub]; exact hdom _ (S.domR.ctrlUse hbm H.hB hbr hc) hne⟩
        obtain ⟨N, hN⟩ := conv_root hwf S.dom hdiP hL hctlL hD
        refine ⟨N, fun n hn => (hN n hn).trans ?_⟩
        unfold rv; rw [g3 _ (by rw [hbv]; simp)]
      · obtain ⟨v, hv, hid, ht, hself⟩ := ctlOK_spec hok
        have hcB : st.ctl ∈ B.values := by rw [hbv]; simp
        have hnp : v.op ≠ .Phi := fun h => by rw [h] at ht; exact absurd ht (by decide)
        obtain ⟨y, hy, hev⟩ := g4 _ hcB v hv hnp
        have hT : (termClosure f [st.cp, st.ctl]).contains st.ctl = true := by
          rw [Bool.or_eq_true, Bool.not_eq_true'] at hctlL
          rcases hctlL with h | h
          · rw [show isTerm f st.ctl = true by simp [isTerm, hv, ht]] at h; cases h
          · exact h
        have hargs : ∀ a ∈ v.args.toList, ∃ N, ∀ n, N ≤ n →
            den f.value? tabs (rv G) n a = rv G2 a := by
          intro a ha
          have ha' := Array.mem_toList_iff.1 ha
          have hab : a ∉ B.values := fun h => by
            rw [hbv] at h; simp at h; subst h; exact hself ha'
          obtain ⟨u, U, hPu, hub, hU, haU, -⟩ :=
            blockOf_listed hwf (hwf.argListed _ B _ v ⟨⟨hbm, H.hB⟩, hcB, hv⟩ a ha')
          have hne : blockOf f a ≠ st.b := fun h => by
            rw [h, H.hB] at hU; cases hU; exact hab haU
          have hD : DomP f st.p a :=
            ⟨u, hPu, by rw [hub]; exact hdom _ (S.domR.uses hbm H.hB hbr hcB hv hnp ha') hne⟩
          have haL : (!isTerm f a || (termClosure f [st.cp, st.ctl]).contains a) = true := by
            by_cases hat : isTerm f a = true
            · rw [hat, Bool.not_true, Bool.false_or]
              simpa using S.topo_arg hL (mem_of_contains hT) hv ha' hat
            · simp [hat]
          obtain ⟨N, hN⟩ := conv_root hwf S.dom hdiP hL haL hD
          exact ⟨N, fun n hn => (hN n hn).trans (by unfold rv; rw [g3 a hab])⟩
        obtain ⟨N, hN⟩ := conv_list (fr := G2) _ hargs
        refine ⟨N + 1, fun n hn => ?_⟩
        obtain ⟨mm, rfl⟩ : ∃ mm, n = mm + 1 := ⟨n - 1, by omega⟩
        rw [den_succ_term hv ht, hN mm (by omega), rv_of hy, evalValue_term ht hev, hid,
          tys_of_value hv]
        rfl
    obtain ⟨N, hN⟩ := hconv
    have hbb := decide_ctl hA hdc hN (rv_of hreg2)
    have he3' : B.succs[st.out]? = some e2 := by
      have := H.out2
      rw [hbb] at he3
      rcases Nat.lt_or_ge st.out 1 with h | h
      · have h0 : st.out = 0 := by omega
        rw [h0] at he3 ⊢; simpa using he3
      · have h1 : st.out = 1 := by omega
        rw [h1] at he3 ⊢; simpa using he3
    rw [H.bout] at he3'; cases he3'
    rw [runLoop_goto hst] at hd ⊢
    have hcm := S.base.child_in H
    have hcr : Reachable f st.child :=
      (S.domR.edge hbm H.hB hbr (Array.mem_of_getElem? H.bout)).1
    obtain ⟨hdi2, -, hG2s, -⟩ := S.dinv_step hbm H.hB hbr hGs' hdiB hG2
      (Array.mem_of_getElem? H.bout)
    have hAG2 : AgrP (XB B) G2 GT := by
      refine ⟨hAG.1.trans (Dead.with_regs g1 _).symm, by rw [hAG.2.1, g2], fun a ha => ?_⟩
      rw [hAG.2.2 a ha, g3 a ha]
    exact ih m (by omega) _ _ _ _ _ _ ⟨rfl, hcm, .inr ⟨rfl, rfl, rfl⟩, hcr, hG2s, hdi2,
      typed_enter hwf hbm H.hB hGs' htyG hG2, hAG2⟩ hd

/-- **One step of the simulation.** -/
theorem sim_step {env : Env} (n : Nat)
    (ih : SimUpTo env (Ctx.make tabs f) (Ctx.make tabs g) (Rel env tabs f st B C) n)
    {frS frT : Frame} {bS iS bT iT : Nat} (hR : Rel env tabs f st B C frS bS iS frT bT iT)
    (hd : (runLoop env (Ctx.make tabs f) (n + 1) frS bS iS).Defined) :
    ∃ fuelT, LoopRefines Eq (runLoop env (Ctx.make tabs f) (n + 1) frS bS iS)
      (runLoop env (Ctx.make tabs g) fuelT frT bT iT) := by
  obtain ⟨hbT, hb, hI, ht, hs, hdi, hty, hA⟩ := hR
  rw [hbT]
  have hwf := S.wf
  obtain ⟨Y, hY, -⟩ := hwf.blockId bS hb
  have hY' := S.base.gblock S.H hb hY
  obtain ⟨hE1, hE2⟩ := S.enter (env := env) hb hY hI hA hs
  cases hst : blockStep env (Ctx.make tabs f) frS bS iS with
  | stuck => exact absurd hd (runLoop_stuck hst)
  | panic e m =>
    obtain ⟨Y2, hY2, hpan⟩ := blockStep_panic hst
    change f.block? bS = some Y2 at hY2
    rw [hY] at hY2; cases hY2
    refine ⟨1, ?_⟩
    rw [runLoop_panic hst, runLoop_panic (blockStep_of_panic (ctx := Ctx.make tabs g) hY'
      (hE2 e m hpan))]
    exact .panicked_refl e m
  | ret rs m =>
    obtain ⟨Y2, G, hY2, hG, hterm⟩ := blockStep_ret hst
    change f.block? bS = some Y2 at hY2
    rw [hY] at hY2; cases hY2
    obtain ⟨GT, hGT, -, hctl⟩ := hE1 G hG
    have hterm' : stepTerm GT (st.expect bS Y) = .ok (.ret rs m) := by
      rw [stepTerm_agree (bS := st.expect bS Y) (bT := st.expect bS Y) ⟨rfl, rfl, rfl, rfl, rfl⟩
        (fun c hc => hctl c (by rwa [expect_controls] at hc))]
      exact (FusePlain.stepTerm_redirect expect_kind expect_controls expect_succs).2 rs m hterm
    refine ⟨1, ?_⟩
    rw [runLoop_ret hst, runLoop_ret (ctx := Ctx.make tabs g)
      (by rw [blockStep_of (ctx := Ctx.make tabs g) hY' hGT, hterm'])]
    exact .returned (RefinesList.refl rs) (Mem.Refines.refl _)
  | goto G e =>
    obtain ⟨Y2, hY2, hG, hterm⟩ := blockStep_goto hst
    change f.block? bS = some Y2 at hY2
    rw [hY] at hY2; cases hY2
    obtain ⟨GT, hGT, hAG, hctl⟩ := hE1 G hG
    have hterm' : stepTerm GT (st.expect bS Y) = .ok (.goto (st.r e)) := by
      rw [stepTerm_agree (bS := st.expect bS Y) (bT := st.expect bS Y) ⟨rfl, rfl, rfl, rfl, rfl⟩
        (fun c hc => hctl c (by rwa [expect_controls] at hc))]
      exact (FusePlain.stepTerm_redirect expect_kind expect_controls expect_succs).1 e hterm
    have hT : blockStep env (Ctx.make tabs g) frT bS iT = .goto GT (st.r e) := by
      rw [blockStep_of (ctx := Ctx.make tabs g) hY' hGT, hterm']
    have he := stepTerm_goto_mem hterm
    have htyG := typed_enter hwf hb hY hs hty hG
    rw [runLoop_goto hst] at hd ⊢
    refine refines_goto hT ?_
    rcases r_cases (st := st) e with ⟨rfl, hr⟩ | ⟨hne, hrb, hrn, hrs⟩
    · -- the redirected edge: `bS` is `p`
      obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 he
      have h1 := S.base.into_b S.H.hB hb hY hj
      rw [S.H.bk] at h1
      have hbp : bS = st.p := (Edge.mk.inj (Option.some.inj h1)).1.symm
      subst hbp
      rw [S.H.hP] at hY; cases hY
      rw [hr]
      exact S.via_b ih ht hs hdi hG hterm htyG hAG hd
    · obtain ⟨hdi', ht', hGs', hem⟩ := S.dinv_step hb hY ht hs hdi hG he
      obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 he
      obtain ⟨-, E, hE, hEi⟩ := hwf.succLink bS Y ⟨hb, hY⟩ j e hj
      have hI' : IdxR st C e.b e.i (st.r e).i := by
        refine .inl ⟨?_, ?_, fun hc => ?_⟩
        · by_cases h : e.b = st.b
          · exact .inr fun hk => hne (by obtain ⟨eb, ei⟩ := e; simp only at h hk; subst h hk; rfl)
          · exact .inl h
        · unfold tIdx
          by_cases h : e.b = st.b ∧ e.i = st.n
          · rw [if_pos h, hrn h.1 h.2]
          · rw [if_neg h, hrs h]
        · rw [hc, S.H.hC] at hE; cases hE
          exact (Array.getElem?_eq_some_iff.1 hEi).1
      have := ih n (Nat.le_refl n) _ _ _ _ _ _
        ⟨hrb, hem, hI', ht', hGs', hdi', htyG, hAG⟩ hd
      exact this

/-- **One checked redirect refines.** -/
theorem refines_of_step : Refines tabs g tabs f := by
  have hwf := S.wf
  intro env args mem fuel hd
  unfold GoFV.SSA.run runCtx at hd ⊢
  rw [Dead.params_eq S.base.rel.ownAux]
  split
  · rename_i hn; simp only [hn] at hd; exact hd.elim
  · rename_i hn
    simp only [hn] at hd
    have hentry : entryFrame env (Ctx.make tabs g) args mem =
        entryFrame env (Ctx.make tabs f) args mem := by
      unfold entryFrame frameMem frameAllocs
      rw [show (Ctx.make tabs g).f.valueTab.size = (Ctx.make tabs f).f.valueTab.size from
        S.base.rel.vsize]
      simp only [Ctx.make, abiParams, S.base.rel.ownAux]
    have houts : (Ctx.make tabs g).outs = (Ctx.make tabs f).outs := by
      simp only [Ctx.make, abiParams, S.base.rel.ownAux]
    rw [hentry, houts, show (Ctx.make tabs g).act = (Ctx.make tabs f).act from rfl,
      show (Ctx.make tabs g).f.entry = f.entry from S.base.rel.entry]
    have hbe : f.entry ≠ st.b := fun h => by
      obtain ⟨E, hE, -⟩ := hwf.blockId f.entry hwf.entry
      have hE0 := hwf.entryPreds E hE
      rw [h, S.H.hB] at hE; cases hE
      have := S.H.bpsz; omega
    have hR0 : Rel env tabs f st B C (entryFrame env (Ctx.make tabs f) args mem) f.entry 0
        (entryFrame env (Ctx.make tabs f) args mem) f.entry 0 := by
      refine ⟨rfl, hwf.entry, .inl ⟨.inl hbe, by unfold tIdx; rw [if_neg fun h => hbe h.1],
        fun h => absurd h.symm S.H.centry⟩, S.domR.entry, by simp [Ctx.make, entryFrame],
        dinv_entry_rel S.domR _, typed_replicate _ _ _ rfl, rfl, rfl, fun _ _ => rfl⟩
    obtain ⟨fuelT, h⟩ := runLoop_simIH (Rel env tabs f st B C)
      (fun n ih _ _ _ _ _ _ hR hd' => S.sim_step n ih hR hd') fuel _ _ _ _ _ _ hR0
      (finish_defined hd)
    exact ⟨fuelT, finish_refines hd h⟩

end Setup

end GoFV.Proof.FuseRedirect

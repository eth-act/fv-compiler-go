import GoFV.Proof.Pass.FuseCmpTarget
import GoFV.Proof.Pass.FusePlainSim

variable [GoFV.SSA.Sem.Addrs]

/-!
# One checked comparison fusion refines

`refines_of_step`: if `g` is `f` with one comparison fusion at `st` (`Setup f g st`), every run
of `f` is a run of `g`. Macro-step simulation (`runLoop_simIH`) with the relation `R`: the same
block (never `b`), frames agreeing outside `Xq` of the source's predecessor (`b`'s values the
target may have speculated, and `nv`), the target's edge index `IdxOK`, and lemma (D) for the
source's frame at the entry of a reachable block.

- A block other than `p` steps alike in both (`normal_step`: `enter_rel`, the terminator reads
  agreeing controls, successors through `remapE`).
- At `p` (`p_step`) the target jumps to `b` and evaluates `b`'s values and `nv`
  (`enter_b`). If the source took `p`'s edge to `s`, the target speculated `b`'s values
  (speculation-safe, their arguments defined by lemma (D) after `p`) and `nv` is `p`'s control,
  so it enters `s` along `b`'s edge, whose `Phi` arguments agree with `p`'s. Otherwise the source
  ran `b` as well (it cannot panic: its values are speculation-safe), the target computed the
  same values, and `nv` is `b`'s control.
-/

namespace GoFV.Proof.FuseCmp

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.Fuse GoFV.Opt.Fuse.Cmp GoFV.Proof
  Dom

/-- The simulation relation (see the module doc). -/
def R (env : Env) (tabs : Tables) (f : Func) (st : Site) (frS : Frame) (bS iS : Nat)
    (frT : Frame) (bT iT : Nat) : Prop :=
  bT = bS ∧ bS ∈ f.blocks ∧ bS ≠ st.b ∧ Reachable f bS ∧ frS.regs.size = f.valueTab.size ∧
    frT = { frS with regs := frT.regs } ∧ frT.regs.size = frS.regs.size ∧
    (∀ a, ¬ Xq f st (predOf f bS iS) a → frT.regs[a]? = frS.regs[a]?) ∧
    IdxOK st bS iS iT ∧ PredT f bS iS ∧
    DInv env (Ctx.make tabs f) (fun a => SDom f a bS ∧ a ≠ bS) frS

/-- An `If` on a `bool` control. -/
theorem stepTerm_bool {G : Frame} {B : Block} {c0 : ID} (hk : B.kind = .If)
    (hc : B.controls = #[c0]) {c : Bool} (hr : G.regs[c0]? = some (some (.bool c))) {e : Edge}
    (he : B.succs[if c then 0 else 1]? = some e) : stepTerm G B = .ok (.goto e) := by
  have hctl : Sem.control G B 0 = .ok (.bool c) := by
    unfold Sem.control; rw [hc]; simp [hr, Res.ofOption]
  unfold stepTerm
  rw [hk]
  simp only [hctl, bind, Res.bind]
  cases c <;> simp_all [succ, Res.ofOption]

theorem not_panicking_of_specSafe {op : Op} (h : specSafeOp op = true) : ¬ Panicking op := by
  rintro (h1 | rfl)
  · simp [specSafeOp, isRoot, h1] at h
  · exact absurd h (by decide)

variable {f g : Func} {st : Site}

namespace Setup

variable (S : Setup f g st)
include S

/-- The controls of a block other than `b` agree after entering it. -/
theorem ctrl_agree {y : ID} (hy : y ∈ f.blocks) {Y : Block} (hY : f.block? y = some Y)
    (ht : Reachable f y) {G GT : Frame}
    (hag : ∀ a, ¬ Xq f st (some y) a → GT.regs[a]? = G.regs[a]?) :
    ∀ c ∈ Y.controls, GT.regs[c]? = G.regs[c]? := by
  obtain ⟨ce, hwf⟩ := S.wf
  intro c hc
  apply hag
  rintro (h | ⟨hbv, hnq⟩)
  · exact S.listed_ne (hwf.ctrlListed y Y ⟨hy, hY⟩ c hc) h
  · have := S.dom.ctrlUse hy hY ht hc
    rw [S.blockOf_bval hbv] at this
    exact hnq y rfl this

/-- The source of an edge, by the target's predecessor list. -/
theorem edge_src {y : ID} (hy : y ∈ f.blocks) {Y : Block} (hY : f.block? y = some Y) {e : Edge}
    (he : e ∈ Y.succs) {C : Block} (hC : f.block? e.b = some C) {q : ID} {k : Nat}
    (hq : C.preds[e.i]? = some ⟨q, k⟩) : y = q := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 he
  obtain ⟨-, C', hC', hci⟩ := hwf.succLink y Y ⟨hy, hY⟩ j e hj
  rw [hC] at hC'; cases hC'
  rw [hq] at hci
  exact (Edge.mk.inj (Option.some.inj hci)).1.symm

/-- An edge into `b` comes from `p`. -/
theorem edge_b {y : ID} (hy : y ∈ f.blocks) {Y : Block} (hY : f.block? y = some Y) {e : Edge}
    (he : e ∈ Y.succs) (heb : e.b = st.b) : y = st.p := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨B, -, hB, -, -, hpr, -⟩ := S.bblock
  obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 he
  obtain ⟨-, C, hC, hci⟩ := hwf.succLink y Y ⟨hy, hY⟩ j e hj
  rw [heb, hB] at hC; cases hC
  rw [hpr] at hci
  have h0 : e.i = 0 := by
    rcases Nat.lt_or_ge e.i 1 with h' | h'
    · omega
    · rw [Array.getElem?_eq_none (by simpa using h')] at hci; cases hci
  rw [h0] at hci
  simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq,
    Edge.mk.injEq] at hci
  exact hci.1.symm

/-- The edge into `s` at `p`'s index comes from `p`. -/
theorem edge_s {y : ID} (hy : y ∈ f.blocks) {Y : Block} (hY : f.block? y = some Y) {e : Edge}
    (he : e ∈ Y.succs) (hes : e.b = st.s) (hei : e.i = st.jp) : y = st.p := by
  obtain ⟨Sb, hS, -, hjp, -⟩ := S.s_preds
  exact S.edge_src hy hY he (C := Sb) (by rw [hes]; exact hS) (by rw [hei]; exact hjp)

/-- The relation after the source left block `y` along `e`, the target's frame agreeing outside
`Xq` of `y`. -/
theorem R_after {env : Env} {tabs : Tables} {y : ID} (hy : y ∈ f.blocks) {Y : Block}
    (hY : f.block? y = some Y) (ht : Reachable f y) {fr G GT : Frame} {i : Nat}
    (hs : fr.regs.size = f.valueTab.size)
    (hdi : DInv env (Ctx.make tabs f) (fun a => SDom f a y ∧ a ≠ y) fr)
    (h : enterBlock env (Ctx.make tabs f) fr Y i = .ok G) {e : Edge} (he : e ∈ Y.succs)
    (hb : e.b ≠ st.b) (hjp : e.b = st.s → e.i ≠ st.jp)
    (hGT : GT = { G with regs := GT.regs }) (hGTs : GT.regs.size = G.regs.size)
    (hag : ∀ a, ¬ Xq f st (some y) a → GT.regs[a]? = G.regs[a]?) :
    R env tabs f st G e.b e.i GT (st.remapE e).b (st.remapE e).i := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨hD1, -, hG1s⟩ := dinv_enter_rel hwf S.dom hy hY hs hdi h
  obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 he
  obtain ⟨hem, C, hC, hci⟩ := hwf.succLink y Y ⟨hy, hY⟩ j e hj
  have hpred : predOf f e.b e.i = some y := by rw [predOf_eq hC, hci]; rfl
  exact ⟨remapE_b, hem, hb, (S.dom.edge hy hY ht he).1, by rw [hG1s, hs], hGT, hGTs,
    by rw [hpred]; exact hag, .inr ⟨hjp, rfl⟩, .inl ⟨y, hpred, hy, ht⟩,
    dinv_edge_rel S.dom hy hY ht he hD1⟩

/-- **A block other than `p` steps alike** in `g` (successors through `remapE`). -/
theorem normal_step {tabs : Tables} {env : Env} {n : Nat}
    (ih : SimUpTo env (Ctx.make tabs f) (Ctx.make tabs g) (R env tabs f st) n)
    {frS frT : Frame} {bS iS bT iT : Nat} (hR : R env tabs f st frS bS iS frT bT iT)
    (hp : bS ≠ st.p) (hd : (runLoop env (Ctx.make tabs f) (n + 1) frS bS iS).Defined) :
    ∃ fuelT, LoopRefines Eq (runLoop env (Ctx.make tabs f) (n + 1) frS bS iS)
      (runLoop env (Ctx.make tabs g) fuelT frT bT iT) := by
  obtain ⟨rfl, hb, hbb, ht, hs, hfT, hsz, hag, hidx, hpt, hdi⟩ := hR
  obtain ⟨fb, gb, hfb, hgb, hid, hvals, hk, hc, hsu⟩ := S.block_out hb hp hbb
  have hE := S.enter_rel (env := env) (tabs := tabs) hb hbb hidx hpt hfb hgb hid hvals ht hfT hsz
    hag
  cases hst : blockStep env (Ctx.make tabs f) frS bT iS with
  | stuck => exact absurd hd (runLoop_stuck hst)
  | panic e m =>
    obtain ⟨Y, hY, hpan⟩ := blockStep_panic hst
    change f.block? bT = some Y at hY
    rw [hfb] at hY; cases hY
    refine ⟨1, ?_⟩
    rw [runLoop_panic hst,
      runLoop_panic (blockStep_of_panic (ctx := Ctx.make tabs g) hgb (hE.2 e m hpan))]
    exact .panicked_refl e m
  | ret rs m =>
    obtain ⟨Y, G, hY, hG, hterm⟩ := blockStep_ret hst
    change f.block? bT = some Y at hY
    rw [hfb] at hY; cases hY
    obtain ⟨GT, hGT, -, -, hag'⟩ := hE.1 G hG
    have hterm1 := stepTerm_same (BT := fb) rfl rfl rfl (S.ctrl_agree hb hfb ht hag') hterm
    have hterm2 := (FusePlain.stepTerm_redirect (G := GT) hk hc hsu).2 rs m hterm1
    refine ⟨1, ?_⟩
    rw [runLoop_ret hst, runLoop_ret (ctx := Ctx.make tabs g)
      (by rw [blockStep_of (ctx := Ctx.make tabs g) hgb hGT, hterm2])]
    exact .returned (RefinesList.refl rs) (Mem.Refines.refl _)
  | goto G e =>
    obtain ⟨Y, hY, hG, hterm⟩ := blockStep_goto hst
    change f.block? bT = some Y at hY
    rw [hfb] at hY; cases hY
    obtain ⟨GT, hGT, hGTf, hGTs, hag'⟩ := hE.1 G hG
    have he := stepTerm_goto_mem hterm
    have hterm1 := stepTerm_same (BT := fb) rfl rfl rfl (S.ctrl_agree hb hfb ht hag') hterm
    have hterm2 := (FusePlain.stepTerm_redirect (G := GT) hk hc hsu).1 e hterm1
    have hT : blockStep env (Ctx.make tabs g) frT bT iT = .goto GT (st.remapE e) := by
      rw [blockStep_of (ctx := Ctx.make tabs g) hgb hGT, hterm2]
    have hnb : e.b ≠ st.b := fun h => hp (S.edge_b hb hfb he h)
    have hjp : e.b = st.s → e.i ≠ st.jp := fun h1 h2 => hp (S.edge_s hb hfb he h1 h2)
    rw [runLoop_goto hst] at hd ⊢
    exact refines_goto hT (ih n (Nat.le_refl n) _ _ _ _ _ _
      (S.R_after hb hfb ht hs hdi hG he hnb hjp hGTf hGTs hag') hd)

/-- A listed value of block `b` is a value of `b`. -/
theorem bval_of_blockOf {B : Block} (hB : f.block? st.b = some B) {a : ID} (hl : Listed f a)
    (h : blockOf f a = st.b) : a ∈ B.values := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨y, Y, hy, ha⟩ := hl
  obtain ⟨v, hv, -, hvb⟩ := hwf.valueId y Y hy a ha
  have : blockOf f a = y := by unfold blockOf; rw [hv]; exact hvb
  rw [this] at h
  subst h
  rw [hy.2] at hB; cases hB
  exact ha

/-- A strict dominator of `b` dominates `p`. -/
theorem up_p {B : Block} (hB : f.block? st.b = some B) {a : ID} (hl : Listed f a)
    (hnb : a ∉ B.values) (hd : SDom f (blockOf f a) st.b) : SDom f (blockOf f a) st.p := by
  obtain ⟨-, P, -, hP, hpm, -, hps⟩ := S.bblock
  have ht : Reachable f st.p := by
    obtain ⟨l, hl'⟩ := hd.1
    obtain ⟨l', -, hr⟩ := S.reach_b hl' rfl
    exact ⟨l', hr⟩
  exact (S.dom.edge hpm hP ht (Array.mem_of_getElem? hps)).2 _ hd
    fun h => hnb (S.bval_of_blockOf hB hl h)

theorem reach_p (hbr : Reachable f st.b) : Reachable f st.p := by
  obtain ⟨l, hl⟩ := hbr
  obtain ⟨l', -, hr⟩ := S.reach_b hl rfl
  exact ⟨l', hr⟩

/-- The arguments of `b`'s values in `g` outside `b` are listed and dominate `p`. -/
theorem ext_args (hbr : Reachable f st.b) {B B' : Block} (hB : f.block? st.b = some B)
    (hvals : B'.values = B.values.push st.nv) {a : ID} (ha : a ∉ B'.values) {x : ID}
    (hx : x ∈ B'.values) (hax : a ∈ argsF g x) :
    Listed f a ∧ SDom f (blockOf f a) st.p := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨B0, P, hB0, hP, hpm, hpr, hps⟩ := S.bblock
  rw [hB] at hB0; cases hB0
  have haB : a ∉ B.values := fun h => ha (by rw [hvals]; exact Array.mem_push_of_mem _ h)
  obtain ⟨B1, P1, -, -, hB1, hP1, -, -, hbm, -, -, -, -, -, -, -, -, hBc, hPc, -⟩ := S.rel.shape
  rw [hB] at hB1; cases hB1
  rw [hP] at hP1; cases hP1
  rw [hvals, Array.mem_push] at hx
  rcases hx with hx | rfl
  · obtain ⟨v, w, hv, hw, ⟨-, -, -, -, hargs⟩, -, -, hnp, -, -, -⟩ := S.bval hB hx
    rw [argsF_of hw, hargs] at hax
    have hax' := Array.mem_toList_iff.1 hax
    have hl := hwf.argListed st.b B x v ⟨⟨hbm, hB⟩, hx, hv⟩ a hax'
    exact ⟨hl, S.up_p hB hl haB (S.dom.uses hbm hB hbr hx hv hnp hax')⟩
  · obtain ⟨-, -, -, w, hw, -, -, hargs, -⟩ := S.rel.newv
    rw [argsF_of hw, hargs] at hax
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hax
    rcases hax with rfl | rfl
    · have hc : st.pc ∈ P.controls := by rw [hPc]; simp
      exact ⟨hwf.ctrlListed st.p P ⟨hpm, hP⟩ _ hc, S.dom.ctrlUse hpm hP (S.reach_p hbr) hc⟩
    · have hc : st.bc ∈ B.controls := by rw [hBc]; simp
      have hl := hwf.ctrlListed st.b B ⟨hbm, hB⟩ _ hc
      exact ⟨hl, S.up_p hB hl haB (S.dom.ctrlUse hbm hB hbr hc)⟩

/-- Value `a` of `f` placed in a block dominating `p` holds a register after `p` (lemma (D)),
which the target's frame agrees with outside `b`'s values. -/
theorem pre_def {env : Env} {tabs : Tables} {B : Block} (hB : f.block? st.b = some B) {G1 GT1 : Frame}
    (hD1 : DInv env (Ctx.make tabs f) (fun a => SDom f a st.p) G1)
    (hag1 : ∀ a, ¬ Xq f st (some st.p) a → GT1.regs[a]? = G1.regs[a]?) {a : ID}
    (hl : Listed f a) (hd : SDom f (blockOf f a) st.p) (haB : a ∉ B.values) :
    GT1.regs[a]? = G1.regs[a]? ∧ ∃ z, G1.regs[a]? = some (some z) ∧
      ∀ v, f.value? a = some v → v.op ≠ .Phi → evalValue env (Ctx.make tabs f) G1 v = .ok z := by
  obtain ⟨ce, hwf⟩ := S.wf
  refine ⟨hag1 a ?_, ?_⟩
  · rintro (h | ⟨hbv, -⟩)
    · exact S.listed_ne hl h
    · obtain ⟨B2, hB2, h2⟩ := FusePlain.valsOf_mem.1 hbv
      rw [hB] at hB2; cases hB2; exact haB h2
  · obtain ⟨y, Y, hy, ha⟩ := hl
    obtain ⟨v, hpl, hvb, -⟩ := placed_of_mem hwf hy.1 hy.2 ha
    have hbo : blockOf f a = y := by rw [blockOf_placed hpl, hvb]
    obtain ⟨z, hz, hev⟩ := hD1 a v hpl (by rw [hvb, ← hbo]; exact hd)
    refine ⟨z, hz, fun v' hv' hnp => ?_⟩
    rw [hpl.1] at hv'; cases hv'
    exact hev hnp

/-- A control's result is fixed by `nv`'s shape (they have the same type). -/
theorem ctrl_typed {env : Env} {tabs : Tables} {G : Frame} {c : ID} {cv w : Value} {z : Val}
    (hcv : f.value? c = some cv) (hid : cv.id = c) (hw : g.value? st.nv = some w)
    (hwid : w.id = st.nv) (hty : cv.type = w.type)
    (hev : evalValue env (Ctx.make tabs f) G cv = .ok z) :
    z.retype ((Ctx.make tabs g).tys[w.id]?.getD .other) = z := by
  have h1 := evalValue_typed hev
  rw [hid, tys_of_value hcv] at h1
  rw [hwid, tys_of_value hw, ← hty]
  exact h1

/-- **The macro step at `p`** (see the module doc). -/
theorem p_step {tabs : Tables} {env : Env} {n : Nat}
    (ih : SimUpTo env (Ctx.make tabs f) (Ctx.make tabs g) (R env tabs f st) n)
    {frS frT : Frame} {iS iT : Nat} (hR : R env tabs f st frS st.p iS frT st.p iT)
    (hd : (runLoop env (Ctx.make tabs f) (n + 1) frS st.p iS).Defined) :
    ∃ fuelT, LoopRefines Eq
      (runLoop env (Ctx.make tabs f) (n + 1) frS st.p iS)
      (runLoop env (Ctx.make tabs g) fuelT frT st.p iT) := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨cg, hwg⟩ := S.wg
  obtain ⟨-, hpm, hpb, ht, hs, hfT, hsz, hag, hidx, hpt, hdi⟩ := hR
  obtain ⟨B, P, hB, hP, -, -, hPkp⟩ := S.bblock
  obtain ⟨B1, P1, S1, -, hB1, hP1, -, -, hbm, hkp2, hi, -, hsb, -, hBk, hPk, -, hBc, hPc, -, -,
    hPs, hBs, -, -, -⟩ := S.rel.shape
  rw [hB] at hB1; cases hB1
  rw [hP] at hP1; cases hP1
  obtain ⟨B0, B', hB0, hB', -, hid', hvals, hBk', hBc', hBsu', hsch⟩ := S.gB
  rw [hB] at hB0; cases hB0
  obtain ⟨X, hX, hP'⟩ := S.rel.gblock (x := st.p) (by simp)
  rw [hP] at hX; cases hX
  have hpb' : (st.p == st.b) = false := by simpa using hpb
  have hP'id : (st.expect st.p P).id = P.id := by simp [Site.expect, hpb']
  have hP'v : (st.expect st.p P).values = P.values := by simp [Site.expect, hpb']
  have hP'k : (st.expect st.p P).kind = .Plain := by simp [Site.expect, hpb']
  have hP's : (st.expect st.p P).succs = #[⟨st.b, 0⟩] := by simp [Site.expect, hpb']
  have hE := S.enter_rel (env := env) (tabs := tabs) hpm hpb hidx hpt hP hP' hP'id hP'v ht hfT
    hsz hag
  have hbr : Reachable f st.b := (S.dom.edge hpm hP ht (Array.mem_of_getElem? hPkp)).1
  have hnvB' : st.nv ∈ B'.values := by rw [hvals]; exact Array.mem_push_self
  have hmemB : ∀ a, a ∈ B'.values → a ≠ st.nv → a ∈ B.values := fun a ha hne => by
    rw [hvals, Array.mem_push] at ha
    exact ha.resolve_right hne
  have hnotB' : ∀ a, a ∉ B.values → a ≠ st.nv → a ∉ B'.values := fun a h1 h2 h3 =>
    h1 (hmemB a h3 h2)
  obtain ⟨-, -, -, w, hw, hwid, hwop, hwargs, -, ⟨pv, hpv, hpvp, hpvt⟩, ⟨bv, hbv, hbvp, hbvt⟩⟩ :=
    S.rel.newv
  have hwnp : w.op ≠ .Phi := by rw [hwop]; unfold newOp; split <;> decide
  have hpcl : Listed f st.pc := hwf.ctrlListed st.p P ⟨hpm, hP⟩ _ (by rw [hPc]; simp)
  have hpcd : SDom f (blockOf f st.pc) st.p := S.dom.ctrlUse hpm hP ht (by rw [hPc]; simp)
  have hpcB : st.pc ∉ B.values := fun h => S.not_sdom_bp (by
    rw [← S.blockOf_bval (FusePlain.valsOf_mem.2 ⟨B, hB, h⟩)]; exact hpcd)
  have hpcid : pv.id = st.pc := by
    obtain ⟨y, Y, hy, ha⟩ := hpcl
    obtain ⟨v, hv, hvid, -⟩ := hwf.valueId y Y hy st.pc ha
    rw [hpv] at hv; cases hv; exact hvid
  have hbcl : Listed f st.bc := hwf.ctrlListed st.b B ⟨hbm, hB⟩ _ (by rw [hBc]; simp)
  have hbcid : bv.id = st.bc := by
    obtain ⟨y, Y, hy, ha⟩ := hbcl
    obtain ⟨v, hv, hvid, -⟩ := hwf.valueId y Y hy st.bc ha
    rw [hbv] at hv; cases hv; exact hvid
  -- the source's step at `p`
  cases hst : blockStep env (Ctx.make tabs f) frS st.p iS with
  | stuck => exact absurd hd (runLoop_stuck hst)
  | panic e m =>
    obtain ⟨Y, hY, hpan⟩ := blockStep_panic hst
    change f.block? st.p = some Y at hY
    rw [hP] at hY; cases hY
    refine ⟨1, ?_⟩
    rw [runLoop_panic hst,
      runLoop_panic (blockStep_of_panic (ctx := Ctx.make tabs g) hP' (hE.2 e m hpan))]
    exact .panicked_refl e m
  | ret rs m =>
    obtain ⟨Y, G, hY, -, hterm⟩ := blockStep_ret hst
    change f.block? st.p = some Y at hY
    rw [hP] at hY; cases hY
    obtain ⟨_, _, _, _, hn⟩ := stepTerm_if hPk hPc hterm
    cases hn
  | goto G1 e =>
    obtain ⟨Y, hY, hG1, hterm⟩ := blockStep_goto hst
    change f.block? st.p = some Y at hY
    rw [hP] at hY; cases hY
    obtain ⟨c, e', hc, he', hn⟩ := stepTerm_if hPk hPc hterm
    cases hn
    obtain ⟨GT1, hGT1, hGT1f, hGT1s, hag1⟩ := hE.1 G1 hG1
    have hT1 : blockStep env (Ctx.make tabs g) frT st.p iT = .goto GT1 ⟨st.b, 0⟩ := by
      rw [blockStep_of (ctx := Ctx.make tabs g) hP' hGT1]
      have : stepTerm GT1 (st.expect st.p P) = .ok (.goto ⟨st.b, 0⟩) := by
        unfold stepTerm; rw [hP'k]; unfold succ; rw [hP's]; rfl
      rw [this]
    obtain ⟨hD1, hG1f, hG1s⟩ := dinv_enter_rel hwf S.dom hpm hP hs hdi hG1
    have hpre := fun {a : ID} => S.pre_def (env := env) (tabs := tabs) hB hD1 hag1 (a := a)
    obtain ⟨hpc1, -, -⟩ := hpre hpcl hpcd hpcB
    -- `p`'s control is typed at `nv`'s shape
    have hpcty : Val.retype ((Ctx.make tabs g).tys[w.id]?.getD .other) (.bool c) = .bool c := by
      obtain ⟨-, z, hz, hev⟩ := hpre hpcl hpcd hpcB
      rw [hc] at hz; cases hz
      exact S.ctrl_typed hpv hpcid hw hwid hpvt (hev pv hpv hpvp)
    have hext : ∀ a, a ∉ B'.values → (∃ x ∈ B'.values, a ∈ argsF g x) →
        GT1.regs[a]? = G1.regs[a]? ∧ ∃ z, G1.regs[a]? = some (some z) := by
      rintro a ha ⟨x, hx, hax⟩
      obtain ⟨hl, hd'⟩ := S.ext_args hbr hB hvals ha hx hax
      obtain ⟨h1, z, hz, -⟩ := hpre hl hd' fun h => ha (by rw [hvals]; exact Array.mem_push_of_mem _ h)
      exact ⟨h1, z, hz⟩
    have hspec : ∀ (G : Frame) (x : ID), x ∈ B'.values → ∀ g' : Frame,
        (∀ a ∈ argsF (Ctx.make tabs g).f x, ∃ z, g'.regs[a]? = some (some z)) →
        ∃ y, stepV env (Ctx.make tabs g) g' x = .ok y := fun G x hx g' hargs => by
      obtain ⟨w', hw', -, hsp⟩ := S.gB_vals hB hvals x hx
      rw [stepV_eq (ctx := Ctx.make tabs g) hw']
      exact evalValue_specSafe hsp fun a ha => hargs a (by
        show a ∈ argsF g x
        rw [argsF_of hw']; exact Array.mem_toList_iff.2 ha)
    rw [runLoop_goto hst] at hd ⊢
    refine refines_goto hT1 ?_
    have hk2 : (if c then 0 else 1) = st.i ∨ (if c then 0 else 1) = st.kp := by
      cases c <;> simp <;> omega
    rcases hk2 with hk | hk
    · -- `p` took its edge to `s`: the target speculates `b`
      rw [hk, hPs] at he'
      cases he'
      obtain ⟨GT2, hen, hGT2f, hGT2s, -, h5, h6⟩ := S.enter_b (env := env) (tabs := tabs) hB hB'
        hvals hid' hsch (G := G1) (GT1 := GT1) (F := fun z => z ∈ B'.values)
        (by rw [hG1s, hs]) hGT1f hGT1s hext
        (fun x hx z hz => by
          rw [List.mem_singleton] at hz; subst hz
          exact ⟨fun hF => absurd hx hF, fun _ g' _ hargs => hspec G1 z hx g' hargs⟩)
      -- `nv` is `p`'s control
      obtain ⟨-, -, -, hnp', -⟩ := enter_ok_facts hwg S.inBg hB'
        (by rw [hGT1s, hG1s, hs, S.gsize]) hen
      obtain ⟨y, hy, hev⟩ := hnp' st.nv hnvB' w hw hwnp
      have hpc2 : GT2.regs[st.pc]? = some (some (.bool c)) := by
        rw [h6 _ (hnotB' _ hpcB (S.listed_ne hpcl)), hpc1, hc]
      obtain ⟨xb, hbc2⟩ : ∃ xb, GT2.regs[st.bc]? = some (some xb) := by
        by_cases hbB' : st.bc ∈ B'.values
        · exact h5 _ hbB'
        · obtain ⟨h1, z, hz⟩ := hext _ hbB' ⟨st.nv, hnvB', by rw [argsF_of hw, hwargs]; simp⟩
          exact ⟨z, by rw [h6 _ hbB', h1, hz]⟩
      rw [evalValue_newOp hwop hwargs hpc2 hbc2, newOp_true hk, hpcty] at hev
      cases hev
      have hstep : stepTerm GT2 B' = .ok (.goto (st.remapE ⟨st.s, st.jb⟩)) := by
        refine stepTerm_bool hBk' hBc' hy ?_
        rw [hBsu', Array.getElem?_map, hk, hBs]
        rfl
      have hT2 : blockStep env (Ctx.make tabs g) GT1 st.b 0 =
          .goto GT2 (st.remapE ⟨st.s, st.jb⟩) := by
        rw [blockStep_of (ctx := Ctx.make tabs g) hB' hen, hstep]
      obtain ⟨Sb, hS, hsm, hjp, -⟩ := S.s_preds
      have hpredS : predOf f st.s st.jp = some st.p := by rw [predOf_eq hS, hjp]; rfl
      have hes : (⟨st.s, st.jp⟩ : Edge) ∈ P.succs := Array.mem_of_getElem? hPs
      refine refines_goto hT2 (ih n (Nat.le_refl n) _ _ _ _ _ _ ?_ hd)
      refine ⟨remapE_b, hsm, hsb, (S.dom.edge hpm hP ht hes).1, by rw [hG1s, hs], hGT2f, hGT2s,
        fun a ha => ?_, .inl ⟨rfl, rfl, rfl⟩, .inl ⟨st.p, hpredS, hpm, ht⟩,
        dinv_edge_rel S.dom hpm hP ht hes hD1⟩
      rw [hpredS] at ha
      have hne : a ≠ st.nv := fun h => ha (.inl h)
      have haB : a ∉ B.values := fun h =>
        ha (.inr ⟨FusePlain.valsOf_mem.2 ⟨B, hB, h⟩, fun q hq => by cases hq; exact S.not_sdom_bp⟩)
      rw [h6 a (hnotB' a haB hne)]
      exact hag1 a ha
    · -- `p` took its edge to `b`: the source runs `b` too
      rw [hk, hPkp] at he'
      cases he'
      cases n with
      | zero => exact absurd hd runLoop_zero_not_defined
      | succ n' =>
      have hs1 : G1.regs.size = f.valueTab.size := by rw [hG1s, hs]
      have hbe : (⟨st.b, 0⟩ : Edge) ∈ P.succs := Array.mem_of_getElem? hPkp
      have hdiB : DInv env (Ctx.make tabs f) (fun a => SDom f a st.b ∧ a ≠ st.b) G1 :=
        dinv_edge_rel S.dom hpm hP ht hbe hD1
      cases hst2 : blockStep env (Ctx.make tabs f) G1 st.b 0 with
      | stuck => exact absurd hd (runLoop_stuck hst2)
      | panic e2 m2 =>
        obtain ⟨Y, hY, hpan⟩ := blockStep_panic hst2
        change f.block? st.b = some Y at hY
        rw [hB] at hY; cases hY
        obtain ⟨_, _, _, r, _, _, -, -, -, -, -, -, -, -, -, -, hrB, rv, hrv, -, hrp⟩ :=
          enter_panic_facts hwf hbm hB hs1 hpan
        obtain ⟨v, -, hv, -, -, -, -, -, hsp, -, -⟩ := S.bval hB hrB
        rw [hv] at hrv; cases hrv
        exact absurd hrp (not_panicking_of_specSafe hsp)
      | ret rs m =>
        obtain ⟨Y, G, hY, -, hterm2⟩ := blockStep_ret hst2
        change f.block? st.b = some Y at hY
        rw [hB] at hY; cases hY
        obtain ⟨_, _, _, _, hn⟩ := stepTerm_if hBk hBc hterm2
        cases hn
      | goto G2 e2 =>
        obtain ⟨Y, hY, hG2, hterm2⟩ := blockStep_goto hst2
        change f.block? st.b = some Y at hY
        rw [hB] at hY; cases hY
        obtain ⟨c', e2', hc', he2', hn2⟩ := stepTerm_if hBk hBc hterm2
        cases hn2
        obtain ⟨hG2f, hG2s, hG2o, hG2v, -⟩ := enter_ok_facts hwf hbm hB hs1 hG2
        obtain ⟨hD2, -, -⟩ := dinv_enter_rel hwf S.dom hbm hB hs1 hdiB hG2
        have hext2 : ∀ a, a ∉ B'.values → (∃ x ∈ B'.values, a ∈ argsF g x) →
            GT1.regs[a]? = G2.regs[a]? ∧ ∃ z, G2.regs[a]? = some (some z) := by
          intro a ha hx
          have haB : a ∉ B.values := fun h => ha (by rw [hvals]; exact Array.mem_push_of_mem _ h)
          rw [hG2o a haB]
          exact hext a ha hx
        obtain ⟨GT2, hen, hGT2f, hGT2s, h4, -, h6⟩ := S.enter_b (env := env) (tabs := tabs) hB hB'
          hvals hid' hsch (G := G2) (GT1 := GT1) (F := fun z => z = st.nv)
          (by rw [hG2s, hs1]) (frame_same hGT1f hG2f) (by rw [hGT1s, hG2s]) hext2
          (fun x hx z hz => by
            rw [List.mem_singleton] at hz; subst hz
            refine ⟨fun hF => ?_, fun _ g' _ hargs => hspec G2 z hx g' hargs⟩
            have hzB := hmemB z hx hF
            obtain ⟨v, w', hv, hw', hsem, -, -, hnp, -, hvid, -⟩ := S.bval hB hzB
            obtain ⟨y, hy, hev⟩ := hG2v z hzB v hv hnp
            refine ⟨y, hy, fun g' hg' hag' _ => ?_⟩
            rw [stepV_eq (ctx := Ctx.make tabs g) hw']
            rw [evalValue_ctx_congr (ctxS := Ctx.make tabs f) (ctxT := Ctx.make tabs g) hsem hg' (fun a ha => hag' a (by
                show a ∈ argsF g z
                rw [argsF_of hw', hsem.2.2.2.2]; exact Array.mem_toList_iff.2 ha)
                (fun h => S.listed_ne (hwf.argListed st.b B z v ⟨⟨hbm, hB⟩, hzB, hv⟩ a ha) h))
              (by rw [hvid]; exact S.tys_eq hF) rfl S.params_eq rfl]
            exact hev)
        -- the target's frame agrees with the source's outside `nv`
        have hagr : ∀ a, a ≠ st.nv → GT2.regs[a]? = G2.regs[a]? := by
          intro a hne
          by_cases haB' : a ∈ B'.values
          · exact h4 a haB' hne
          · have haB : a ∉ B.values := fun h => haB' (by rw [hvals]; exact Array.mem_push_of_mem _ h)
            rw [h6 a haB', hG2o a haB]
            exact hag1 a (by
              rintro (h | ⟨hbv, -⟩)
              · exact hne h
              · obtain ⟨B2, hB2, h2⟩ := FusePlain.valsOf_mem.1 hbv
                rw [hB] at hB2; cases hB2; exact haB h2)
        -- `nv` is `b`'s control
        obtain ⟨-, -, -, hnp', -⟩ := enter_ok_facts hwg S.inBg hB'
          (by rw [hGT1s, hG1s, hs, S.gsize]) hen
        obtain ⟨y, hy, hev⟩ := hnp' st.nv hnvB' w hw hwnp
        have hpc2 : GT2.regs[st.pc]? = some (some (.bool c)) := by
          rw [hagr _ (S.listed_ne hpcl), hG2o _ hpcB, hc]
        have hbc2 : GT2.regs[st.bc]? = some (some (.bool c')) := by
          rw [hagr _ (S.listed_ne hbcl), hc']
        have hbcty : Val.retype ((Ctx.make tabs g).tys[w.id]?.getD .other) (.bool c') = .bool c' := by
          obtain ⟨y', Y', hy', ha'⟩ := hbcl
          obtain ⟨v', hpl, hvb, -⟩ := placed_of_mem hwf hy'.1 hy'.2 ha'
          have hbo : blockOf f st.bc = y' := by rw [blockOf_placed hpl, hvb]
          have hd' : SDom f (blockOf f st.bc) st.b := S.dom.ctrlUse hbm hB hbr (by rw [hBc]; simp)
          obtain ⟨z, hz, hevz⟩ := hD2 st.bc v' hpl (by rw [hvb, ← hbo]; exact hd')
          rw [hc'] at hz; cases hz
          rw [hpl.1] at hbv; cases hbv
          exact S.ctrl_typed hpl.1 hbcid hw hwid hbvt (hevz hbvp)
        have hk' : (if c then 0 else 1) = 1 - st.i := by omega
        rw [evalValue_newOp hwop hwargs hpc2 hbc2, newOp_pass (by omega) hk', hbcty] at hev
        cases hev
        have he2 := stepTerm_goto_mem hterm2
        have hstep : stepTerm GT2 B' = .ok (.goto (st.remapE e2)) := by
          refine stepTerm_bool hBk' hBc' hy ?_
          rw [hBsu', Array.getElem?_map, he2']
          rfl
        have hT2 : blockStep env (Ctx.make tabs g) GT1 st.b 0 = .goto GT2 (st.remapE e2) := by
          rw [blockStep_of (ctx := Ctx.make tabs g) hB' hen, hstep]
        rw [runLoop_goto hst2] at hd ⊢
        exact refines_goto hT2 (ih n' (by omega) _ _ _ _ _ _
          (S.R_after hbm hB hbr hs1 hdiB hG2 he2
            (fun h => hpb (S.edge_b hbm hB he2 h).symm)
            (fun h1 h2 => hpb (S.edge_s hbm hB he2 h1 h2).symm)
            hGT2f hGT2s (fun a ha => hagr a fun h => ha (.inl h))) hd)

/-- **One step of the simulation** (macro step at `p`). -/
theorem sim_step {tabs : Tables} {env : Env} (n : Nat)
    (ih : SimUpTo env (Ctx.make tabs f) (Ctx.make tabs g) (R env tabs f st) n)
    {frS frT : Frame} {bS iS bT iT : Nat} (hR : R env tabs f st frS bS iS frT bT iT)
    (hd : (runLoop env (Ctx.make tabs f) (n + 1) frS bS iS).Defined) :
    ∃ fuelT, LoopRefines Eq (runLoop env (Ctx.make tabs f) (n + 1) frS bS iS)
      (runLoop env (Ctx.make tabs g) fuelT frT bT iT) := by
  by_cases hp : bS = st.p
  · subst hp
    have hbT : bT = st.p := hR.1
    subst hbT
    exact S.p_step ih hR hd
  · exact S.normal_step ih hR hp hd

/-- **One checked comparison fusion refines.** -/
theorem refines_of_step {tabs : Tables} : Refines tabs g tabs f := by
  obtain ⟨ce, hwf⟩ := S.wf
  have hgsz := S.gsize
  have hown : g.ownAux = f.ownAux := S.rel.ownAux
  intro env args mem fuel hd
  unfold GoFV.SSA.run runCtx at hd ⊢
  rw [S.params_eq]
  split
  · rename_i hn; simp only [hn] at hd; exact hd.elim
  · rename_i hn
    simp only [hn] at hd
    have hentry : entryFrame env (Ctx.make tabs g) args mem =
        entryFrame env (Ctx.make tabs f) args mem := by
      unfold entryFrame frameMem frameAllocs
      rw [show (Ctx.make tabs g).f.valueTab.size = (Ctx.make tabs f).f.valueTab.size from hgsz]
      simp only [Ctx.make, abiParams, hown]
    have houts : (Ctx.make tabs g).outs = (Ctx.make tabs f).outs := by
      simp only [Ctx.make, abiParams, hown]
    rw [hentry, houts, show (Ctx.make tabs g).act = (Ctx.make tabs f).act from rfl]
    have hent : (Ctx.make tabs g).f.entry = f.entry := S.rel.entry
    rw [hent]
    obtain ⟨E, hE, -⟩ := hwf.blockId f.entry hwf.entry
    have hE0 := hwf.entryPreds E hE
    obtain ⟨Sb, hS, -, -, -, hSn, -⟩ := S.s_preds
    have hse : f.entry ≠ st.s := fun h => by
      rw [h, hS] at hE; cases hE; omega
    have hR0 : R env tabs f st (entryFrame env (Ctx.make tabs f) args mem) f.entry 0
        (entryFrame env (Ctx.make tabs f) args mem) f.entry 0 := by
      refine ⟨rfl, hwf.entry, fun h => S.b_ne_entry h.symm, S.dom.entry,
        by simp [Ctx.make, entryFrame], rfl, rfl, fun _ _ => rfl,
        .inr ⟨fun h => absurd h hse, by rw [remapE_i]; simp [hse]⟩,
        .inr ⟨by rw [predOf_eq hE, Array.getElem?_eq_none (by omega)]; rfl, rfl⟩,
        dinv_entry_rel S.dom _⟩
    obtain ⟨fuelT, h⟩ := runLoop_simIH (R env tabs f st) (fun n ih _ _ _ _ _ _ hR hd' =>
      S.sim_step n ih hR hd') fuel _ _ _ _ _ _ hR0 (finish_defined hd)
    exact ⟨fuelT, finish_refines hd h⟩

end Setup

end GoFV.Proof.FuseCmp

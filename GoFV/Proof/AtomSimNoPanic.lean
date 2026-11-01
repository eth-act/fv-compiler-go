import GoFV.Proof.AtomSimEnter

/-!
# A block entry that does not panic (issue #113)

`enter_ok`: if the source enters block `b` without panicking or getting stuck, so does the
target, and the frames afterwards are related (`EndRel`): `DenOK` of the strict ancestors'
values, the `Phi`s and the schedule on both sides, the atoms both hold refined.
-/

namespace GoFV.Proof.AtomSim

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Proof.Dom GoFV.Opt.RewriteCheck GoFV.Proof.Term

theorem frame_fields {A B : Frame} (h : A = { B with regs := A.regs }) :
    A.args = B.args ∧ A.mem0 = B.mem0 ∧ A.images = B.images ∧ A.closure = B.closure := by
  rw [h]; exact ⟨rfl, rfl, rfl, rfl⟩

theorem frame_eq {A B : Frame} (h : A.args = B.args ∧ A.mem0 = B.mem0 ∧ A.images = B.images ∧
    A.closure = B.closure) : A = { B with regs := A.regs } := by
  obtain ⟨r, a, m, i, c⟩ := A
  obtain ⟨r', a', m', i', c'⟩ := B
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only at h1 h2 h3 h4
  subst h1 h2 h3 h4; rfl

theorem frame_trans {A B C : Frame} (h1 : A = { B with regs := A.regs })
    (h2 : B = { C with regs := B.regs }) : A = { C with regs := A.regs } := by
  obtain ⟨a1, a2, a3, a4⟩ := frame_fields h1
  obtain ⟨b1, b2, b3, b4⟩ := frame_fields h2
  exact frame_eq ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4⟩

theorem frame_symm {A B : Frame} (h : A = { B with regs := A.regs }) :
    B = { A with regs := B.regs } := by
  obtain ⟨a1, a2, a3, a4⟩ := frame_fields h
  exact frame_eq ⟨a1.symm, a2.symm, a3.symm, a4.symm⟩

/-- A block entry without panic: the `Phi`s, the schedule, its evaluation. -/
theorem enterBlock_ok_split {env : Env} {ctx : Ctx} {fr fr' : Frame} {b : Block} {i : Nat}
    (h : enterBlock env ctx fr b i = .ok fr') :
    ∃ ps o, b.values.toList.filterMapM (phiStep ctx fr i) = .ok ps ∧
      (ctx.sched[b.id]?).join = some o ∧
      evalAll env ctx { fr with regs := setPhis ps fr.regs } o.toList = .ok fr' := by
  rw [enterBlock_eq] at h
  cases hps : b.values.toList.filterMapM (phiStep ctx fr i) with
  | panic e' m' => rw [hps] at h; cases h
  | stuck msg => rw [hps] at h; cases h
  | ok ps =>
    rw [hps] at h
    change (Res.ofOption _ (ctx.sched[b.id]?).join).bind _ = _ at h
    cases ho : (ctx.sched[b.id]?).join with
    | none => rw [ho] at h; cases h
    | some o =>
      rw [ho] at h
      exact ⟨ps, o, rfl, rfl, h⟩

theorem enterBlock_of {env : Env} {ctx : Ctx} {fr : Frame} {b : Block} {i : Nat}
    {ps : List (ID × Val)} {o : Array ID} {r : Res Frame}
    (hps : b.values.toList.filterMapM (phiStep ctx fr i) = .ok ps)
    (ho : (ctx.sched[b.id]?).join = some o)
    (hev : evalAll env ctx { fr with regs := setPhis ps fr.regs } o.toList = r) :
    enterBlock env ctx fr b i = r := by
  rw [enterBlock_eq, hps]
  change (Res.ofOption _ (ctx.sched[b.id]?).join).bind _ = _
  rw [ho]; exact hev

/-! ## Facts shared by both cases -/

/-- `V1` of `g` is placed. -/
theorem v1_placed {ce : CheckEnv} {g : Func} (hwf : WF ce g) {b : ID} {gb : Block}
    (hbm : b ∈ g.blocks) (hbb : g.block? b = some gb) :
    ∀ x, V1 g b gb x → ∃ w, Placed g x w := by
  intro x hx
  rcases hx with ⟨v, hp, -⟩ | ⟨hx, v, hv, -⟩
  · exact ⟨v, hp⟩
  · exact ⟨v, (placed_in hwf hbm hbb hx hv).1⟩

/-- `V1` and the schedule are disjoint. -/
theorem v1_disj {ce : CheckEnv} {h : Func} (hwf : WF ce h) {b : ID} {hb : Block}
    (hbm : b ∈ h.blocks) (hbb : h.block? b = some hb) {o : Array ID}
    (hmem : ∀ x, x ∈ o.toList ↔ x ∈ hb.values ∧ ∃ v, h.value? x = some v ∧ v.op ≠ .Phi) :
    ∀ x ∈ o.toList, ¬ V1 h b hb x := by
  intro x hx hV
  obtain ⟨hxb, v, hv, hph⟩ := (hmem x).1 hx
  rcases hV with h | ⟨-, v', hv', hph'⟩
  · exact sanc_not_mem hwf hbm hbb h hxb
  · rw [hv] at hv'; cases hv'; exact hph hph'

/-- A scheduled atom of `g` is scheduled in `f`, with the same fields. -/
theorem atom_sched {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} {I : SrcInv tabs f} (H : Hyp tabs f g ce ce' I)
    {b : ID} {fb gb : Block} {of og : Array ID} (B : BlockData f g b fb gb of og)
    {x : ID} (hx : x ∈ og.toList) {w : Value} (hw : g.value? x = some w) (ht : termOp w.op = false) :
    ∃ u, f.value? x = some u ∧ SameAtom u w ∧ x ∈ of.toList ∧ Placed g x w := by
  obtain ⟨hxb, w', hw', hph⟩ := (B.mT x).1 hx
  rw [hw] at hw'; cases hw'
  have hpw := (placed_in H.wg B.bmT B.hgb hxb hw).1
  obtain ⟨hxf, u, hu, hs⟩ := B.ba.sub x hxb w hw ht
  exact ⟨u, hu, hs, (B.mS x).2 ⟨hxf, u, hu, hs.1 ▸ hph⟩, hpw⟩

/-- An atom of `g` is not a term node of `f`. -/
theorem not_term_f {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} {I : SrcInv tabs f} (H : Hyp tabs f g ce ce' I)
    {a : ID} {w : Value} (hp : Placed g a w) (ht : termOp w.op = false) : ¬ IsTerm f.value? a := by
  intro ⟨u', hu', ht'⟩
  obtain ⟨u, hpu, hs⟩ := gatom_f H hp ht
  rw [hpu.1] at hu'; cases hu'
  rw [hs.1, ht] at ht'; cases ht'

theorem atom_of_not_term {g : Func} {a : ID} {w : Value} (hp : Placed g a w)
    (hat : ¬ IsTerm (listedDefs g) a) : termOp w.op = false := by
  cases h : termOp w.op
  · rfl
  · exact absurd ⟨w, placed_listed hp, h⟩ hat

/-- Atoms placed outside `b` keep their registers through block `b`, in `f` too. -/
theorem atom_out {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} {I : SrcInv tabs f} (H : Hyp tabs f g ce ce' I)
    {b : ID} {fb gb : Block} {of og : Array ID} (B : BlockData f g b fb gb of og)
    {a : ID} {w : Value} (hp : Placed g a w) (ht : termOp w.op = false) (hne : w.block ≠ b) :
    a ∉ gb.values ∧ a ∉ fb.values := by
  obtain ⟨u, hpu, hs⟩ := gatom_f H hp ht
  exact ⟨not_mem_of_placed H.wg hp B.bmT B.hgb hne,
    not_mem_of_placed H.wf hpu B.bmS B.hfb (hs.2.2.2.2.2.1 ▸ hne)⟩

/-- The frames after a block entry. -/
structure EndRel (tabs : Tables) (f g : Func) (I : SrcInv tabs f) (b : ID) (fb gb : Block)
    (of og : Array ID) (FS FT : Frame) : Prop where
  fr : FT = { FS with regs := FT.regs }
  szS : FS.regs.size = f.valueTab.size
  szT : FT.regs.size = g.valueTab.size
  tyS : Proof.Typed (Ctx.make tabs f) FS
  tyT : Proof.Typed (Ctx.make tabs g) FT
  dS : DenOK f.value? tabs FS (fun a => V1 f b fb a ∨ a ∈ of.toList)
  dT : DenOK (listedDefs g) tabs FT (fun a => V1 g b gb a ∨ a ∈ og.toList)
  rel : ∀ a, (V1 g b gb a ∨ a ∈ og.toList) → (V1 f b fb a ∨ a ∈ of.toList) →
    ¬ IsTerm f.value? a → ¬ IsTerm (listedDefs g) a → Sem.Refines (rv FS a) (rv FT a)
  atoms : ∀ a w, Placed g a w → termOp w.op = false → ∀ y', FT.regs[a]? = some (some y') →
    ∃ y, FS.regs[a]? = some (some y) ∧ Sem.Refines y y'
  inv : ∀ a, I.P b a (rv FS a)
  qinv : I.Q b (rv FS)
  mS : MemDefs f.value? tabs FS (fun a => V1 f b fb a ∨ a ∈ of.toList)

/-- **A block entry without panic.** -/
theorem enter_ok {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} {I : SrcInv tabs f} (H : Hyp tabs f g ce ce' I)
    {env : Env} (hE : env.Mono) {frS frT : Frame} {b : ID} {i : Nat}
    (R : BRel tabs f g I frS frT b i) {fb gb : Block} {of og : Array ID}
    (B : BlockData f g b fb gb of og) {FS : Frame}
    (he : enterBlock env (Ctx.make tabs f) frS fb i = .ok FS) :
    ∃ FT, enterBlock env (Ctx.make tabs g) frT gb i = .ok FT ∧
      EndRel tabs f g I b fb gb of og FS FT := by
  obtain ⟨psS, o, hpsS, ho, hevS⟩ := enterBlock_ok_split he
  rw [sched_eq B.hfb B.idS, B.sS] at ho; cases ho
  obtain ⟨psT, hpsT, hphis⟩ := tgt_phis H R B hpsS
  obtain ⟨VS, VT, hDS, hDT, hVT, hsS, hsT, -, -, hMS⟩ := R.den
  have hS1 := denOK_phis H.wf B.bmS B.hfb rfl hDS hsS (closed_sanc_f H.wf H.cf b) phi_not_term_f
    R.szS hpsS
  have hM1 := memDefs_phis H.wf H.cf B.bmS B.hfb rfl hMS hsS hpsS
  have hT1 := denOK_phis H.wg B.bmT B.hgb rfl hDT hsT (closed_sanc_g H.wg H.cg b) phi_not_term_g
    R.szT hpsT
  obtain ⟨pS1, pS2, pS3, pS4⟩ := phis_spec B.vS hpsS
  obtain ⟨pT1, pT2, pT3, pT4⟩ := phis_spec B.vT hpsT
  have htyPS : Proof.Typed (Ctx.make tabs f) { frS with regs := setPhis psS frS.regs } :=
    typed_phis R.tyS pS1 pS3 pS4 pS2
  have htyPT : Proof.Typed (Ctx.make tabs g) { frT with regs := setPhis psT frT.regs } :=
    typed_phis R.tyT pT1 pT3 pT4 pT2
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := src_eval H B R.treeS (P := of.toList) (Q := [])
    (by simp) hS1 (by rw [pS1, R.szS]) htyPS hevS
  have hMFS := src_eval_mem H B R.treeS (P := of.toList) (Q := []) (by simp) hS1 hM1
    (by rw [pS1, R.szS]) htyPS hevS
  obtain ⟨hinvFS, hqFS⟩ := inv_evalAll B.hfb (sched_own H B) hevS
    (inv_phis B.hfb B.vS hpsS R.szS R.inv R.phis) (R.qinv fb psS B.hfb hpsS)
  have hfrT : { frT with regs := setPhis psT frT.regs } =
      { FS with regs := ({ frT with regs := setPhis psT frT.regs } : Frame).regs } :=
    frame_trans (frame_trans rfl R.fr) (frame_symm (frame_trans g1 rfl))
  -- the atoms both entry frames hold: `Phi`s refined, others kept
  have hrel0 : ∀ a, V1 g b gb a → (V1 f b fb a ∨ a ∈ of.toList) → ¬ IsTerm f.value? a →
      ¬ IsTerm (listedDefs g) a →
      Sem.Refines (rv FS a) (rv { frT with regs := setPhis psT frT.regs } a) := by
    intro a ha _ _ hatE
    obtain ⟨w, hpw⟩ := v1_placed H.wg B.bmT B.hgb a ha
    have hwt := atom_of_not_term hpw hatE
    rcases ha with ⟨w', hpw', hanc, hne⟩ | ⟨haz, w', hw', hph⟩
    · have hww := placed_val hpw' hpw.1; subst hww
      obtain ⟨hnT, hnS⟩ := atom_out H B hpw hwt hne
      have hreg := reg_rv (hT1 a (.inl ⟨w, hpw, hanc, hne⟩)).1
      rw [pT3 a (.inl hnT)] at hreg
      obtain ⟨y, hy, hyy⟩ := R.atoms a w hpw hwt _ hreg
      have hof : a ∉ of.toList := fun hm => hnS ((B.mS a).1 hm).1
      rw [rv_of (show FS.regs[a]? = some (some y) by rw [g5 a hof]; exact (pS3 a (.inl hnS)).trans hy)]
      unfold rv; rw [pT3 a (.inl hnT), hreg]; exact hyy
    · obtain ⟨y, y', hy, hy', hyy⟩ := hphis a haz w' hw' hph
      have hof : a ∉ of.toList := fun hm => by
        obtain ⟨-, u, hu, hph'⟩ := (B.mS a).1 hm
        obtain ⟨u', hpu, hs⟩ := gatom_f H hpw hwt
        rw [placed_val hpw hw'] at hph
        rw [hpu.1] at hu; cases hu; exact hph' (hs.1.trans hph)
      rw [rv_of (show FS.regs[a]? = some (some y) by rw [g5 a hof]; exact hy)]
      show Sem.Refines y (rv { frT with regs := setPhis psT frT.regs } a)
      rw [rv_of hy']; exact hyy
  obtain ⟨FT, hevT, l1, l2, l3, l4, l5, l6⟩ := tgt_loop H hE (og := og.toList) (L := og.toList)
    (M := []) (P := of.toList) (by simp) hfrT (by rw [pT1, R.szT]) g3 htyPT g4 hMFS hT1
    (v1_placed H.wg B.bmT B.hgb) (v1_disj H.wg B.bmT B.hgb B.mT) hrel0 B.ndT B.tpT
    (b := b) (fun x hx => by
      obtain ⟨hxb, w, hw, hph⟩ := (B.mT x).1 hx
      obtain ⟨hp, hwb, hid⟩ := placed_in H.wg B.bmT B.hgb hxb hw
      exact ⟨w, hp, hid, hph, hwb⟩) hinvFS hqFS (fun a h => .inl (.inl h))
    (sched_args H.wg H.cg B.bmT B.hgb R.treeT B.mT)
    (fun a ha _ hat => by
      obtain ⟨hxb, w, hw, -⟩ := (B.mT a).1 ha
      obtain ⟨-, -, -, hof, hp⟩ := atom_sched H B ha hw (atom_of_not_term
        (placed_in H.wg B.bmT B.hgb hxb hw).1 hat)
      exact hof)
    (fun x hx w hw ht => by
      obtain ⟨u, hu, hs, hof, -⟩ := atom_sched H B hx hw ht
      refine ⟨u, hu, hs, fun _ => ⟨fun a ha => sched_args H.wf H.cf B.bmS B.hfb R.treeS B.mS x hof
        u hu a ha, ?_⟩, fun h => absurd hof h⟩
      obtain ⟨u', y, hu', hy, hev⟩ := g6 x hof
      rw [hu] at hu'; cases hu'
      exact ⟨y, hy, hev⟩)
  refine ⟨FT, enterBlock_of hpsT (by rw [sched_eq B.hgb B.idT, B.sT]) hevT, ?_⟩
  have hfr : FT = { FS with regs := FT.regs } := frame_trans l1 hfrT
  refine ⟨hfr, by rw [g2, pS1, R.szS], by rw [l2, pT1, R.szT], g3, l3, g4, l4,
    fun a h1 h2 h3 h4 => l6 a h1 h2 h3 h4, fun a w hpw hwt y' hy' => ?_, hinvFS, hqFS, hMFS⟩
  by_cases hwb : w.block = b
  · have haz : a ∈ gb.values := by
      obtain ⟨-, -, blk, hblk, hx⟩ := hpw
      rw [hwb, B.hgb] at hblk; cases hblk; exact hx
    by_cases hph : w.op = .Phi
    · obtain ⟨y, y'', hy, hy'', hyy⟩ := hphis a haz w hpw.1 hph
      have hog : a ∉ og.toList := fun hm => by
        obtain ⟨-, w', hw', hph'⟩ := (B.mT a).1 hm
        rw [hpw.1] at hw'; cases hw'; exact hph' hph
      rw [l5 a hog, hy''] at hy'; cases hy'
      have hof : a ∉ of.toList := fun hm => by
        obtain ⟨-, u, hu, hph'⟩ := (B.mS a).1 hm
        obtain ⟨u', hpu, hs⟩ := gatom_f H hpw hwt
        rw [hpu.1] at hu; cases hu; exact hph' (hs.1.trans hph)
      exact ⟨y, by rw [g5 a hof]; exact hy, hyy⟩
    · have hog : a ∈ og.toList := (B.mT a).2 ⟨haz, w, hpw.1, hph⟩
      obtain ⟨u, hu, hs, hof, -⟩ := atom_sched H B hog hpw.1 hwt
      have hr := l6 a (.inr hog) (.inr hof) (not_term_f H hpw hwt)
        (fun ⟨w', hw', ht'⟩ => by rw [placed_listed hpw] at hw'; cases hw'; rw [hwt] at ht'; cases ht')
      obtain ⟨u', y, hu', hy, -⟩ := g6 a hof
      rw [rv_of hy, rv_of hy'] at hr
      exact ⟨y, hy, hr⟩
  · obtain ⟨hnT, hnS⟩ := atom_out H B hpw hwt hwb
    have hog : a ∉ og.toList := fun hm => hnT ((B.mT a).1 hm).1
    have hof : a ∉ of.toList := fun hm => hnS ((B.mS a).1 hm).1
    rw [l5 a hog] at hy'
    change (setPhis psT frT.regs)[a]? = _ at hy'
    rw [pT3 a (.inl hnT)] at hy'
    obtain ⟨y, hy, hyy⟩ := R.atoms a w hpw hwt y' hy'
    exact ⟨y, by rw [g5 a hof]; exact (pS3 a (.inl hnS)).trans hy, hyy⟩

end GoFV.Proof.AtomSim

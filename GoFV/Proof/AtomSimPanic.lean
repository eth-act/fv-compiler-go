import GoFV.Proof.AtomSimNoPanic

/-!
# A block entry that panics (issue #113)

`enter_panic`: if the source panics entering block `b` (at root `r` of its schedule, after the
prefix `pre`), the target panics alike with a refined memory: it evaluates the prefix of its
schedule before `r` (its roots are those of `pre` that are roots of `g`, its `Arg`s precede
every root of the source schedule by `PureFirst`, other atoms never get stuck), then `r` on
refined arguments. A root of `f` that is no root of `g` is a `Store` or a `Zero`, which do not
panic, so `r` is a root of both.
-/

namespace GoFV.Proof.AtomSim

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Proof.Dom GoFV.Opt.RewriteCheck GoFV.Proof.Term

theorem isRoot_of_prio {op : Op} (h : prio op ≠ 0) : isRoot op = true := by
  unfold prio at h
  cases hn : op.nilCheck
  · cases hr : isRoot op
    · simp [hn, hr] at h
    · rfl
  · unfold isRoot; simp [hn]

/-- An `Arg`/`ArgIntReg` of the source schedule comes before its panicking root. -/
theorem arg_before {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} {I : SrcInv tabs f} (H : Hyp tabs f g ce ce' I)
    {b : ID} {fb gb : Block} {of og : Array ID} (B : BlockData f g b fb gb of og)
    {pre post : List ID} {r : ID} (hof : of.toList = pre ++ r :: post) {ur : Value}
    (hur : f.value? r = some ur) (hrp : prio ur.op ≠ 0) {x : ID} (hx : x ∈ of.toList) (hxr : x ≠ r)
    {u : Value} (hu : f.value? x = some u) (harg : u.op = .Arg ∨ u.op = .ArgIntReg) : x ∈ pre := by
  have hspec := schedule_spec B.sS
  have hown := valuesOwn H.wf B.bmS B.hfb
  obtain ⟨hxb, u', hu', hph⟩ := (B.mS x).1 hx
  rw [hu] at hu'; cases hu'
  have hrof : r ∈ of.toList := by rw [hof]; simp
  obtain ⟨hrb, ur', hur', hrph⟩ := (B.mS r).1 hrof
  rw [hur] at hur'; cases hur'
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
  have hk : of.toList[pre.length]? = some r := by rw [hof]; simp
  rcases Nat.lt_trichotomy j pre.length with hlt | heq | hgt
  · rw [hof, List.getElem?_append_left hlt] at hj
    exact List.mem_of_getElem? hj
  · subst heq; rw [hk] at hj; cases hj; exact absurd rfl hxr
  · exfalso
    have hnr := nodeOf_schedNodes hown B.vS hrb hur hrph
    have hnx := nodeOf_schedNodes hown B.vS hxb hu hph
    obtain ⟨a, ha, -⟩ := hspec.pureFirst pre.length j r x hgt hk hj
      (fun hp => hrp (hp _ hnr)) (fun n hn => by
        rw [hnx] at hn; cases hn
        rcases harg with h | h <;> rw [h] <;> rfl)
    rw [argsOf_schedNodes hown B.vS hxb hu hph] at ha
    have har := H.wf.arity b fb x u ⟨⟨B.bmS, B.hfb⟩, hxb, hu⟩
      (by rcases harg with h | h <;> rw [h] <;> decide)
    have h0 : u.args.size = 0 := by
      have hA : Op.argLen .Arg = 0 := by decide
      have hB : Op.argLen .ArgIntReg = 0 := by decide
      rcases harg with h | h
      · rw [h, hA] at har; omega
      · rw [h, hB] at har; omega
    rw [Array.size_eq_zero_iff.1 h0] at ha
    cases ha

/-- **A panicking block entry.** -/
theorem enter_panic {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} {I : SrcInv tabs f} (H : Hyp tabs f g ce ce' I)
    {env : Env} (hE : env.Mono) (hEI : I.E env) {frS frT : Frame} {b : ID} {i : Nat}
    (R : BRel tabs f g I frS frT b i) {fb gb : Block} {of og : Array ID}
    (B : BlockData f g b fb gb of og) {e : Panic} {m : Mem}
    (he : enterBlock env (Ctx.make tabs f) frS fb i = .panic e m) :
    ∃ m', enterBlock env (Ctx.make tabs g) frT gb i = .panic e m' ∧ Mem.Refines m m' := by
  obtain ⟨psS, o, hpsS, ho, hevS⟩ := enterBlock_panic he
  rw [sched_eq B.hfb B.idS, B.sS] at ho; cases ho
  obtain ⟨pre, r, post, G, hof, hpre, hstep⟩ := evalAll_panic_split hevS
  -- the panicking root, in both schedules
  obtain ⟨ur, hur, hevr⟩ : ∃ ur, f.value? r = some ur ∧
      evalValue env (Ctx.make tabs f) G ur = .panic e m := by
    unfold stepV at hstep
    cases h : (Ctx.make tabs f).f.value? r with
    | none => rw [h] at hstep; cases hstep
    | some ur => rw [h] at hstep; exact ⟨ur, h, hstep⟩
  have hrp : prio ur.op ≠ 0 := prio_panicking (evalValue_panic_op hevr)
  have hrof : r ∈ of.toList := by rw [hof]; simp
  have hrS : rootP f r = true := by simp [rootP, hur, isRoot_of_prio hrp]
  have hrG : rootP g r = true := by
    cases hg : rootP g r
    · obtain ⟨u, hu, hst⟩ := B.drop r hrof hrS hg
      rw [hur] at hu; cases hu
      have := evalValue_panic_op hevr
      rcases hst with hst | hst <;> rw [hst] at this <;> rcases this with h | h <;> cases h
    · rfl
  have hrog : r ∈ og.toList ∧ rootP g r = true := by
    have : r ∈ of.toList.filter (fun x => rootP f x && rootP g x) :=
      List.mem_filter.2 ⟨hrof, by rw [hrS, hrG]; rfl⟩
    rw [B.fl] at this; exact List.mem_filter.1 this
  obtain ⟨preT, postT, hog⟩ := List.append_of_mem hrog.1
  have hrpre : r ∉ pre := fun hm => by
    have := B.ndS; rw [hof] at this
    exact (List.nodup_append.1 this).2.2 r hm r List.mem_cons_self rfl
  have hrpreT : r ∉ preT := fun hm => by
    have := B.ndT; rw [hog] at this
    exact (List.nodup_append.1 this).2.2 r hm r List.mem_cons_self rfl
  have hfl : pre.filter (fun x => rootP f x && rootP g x) = preT.filter (rootP g) := by
    have := B.fl; rw [hof, hog] at this
    exact filter_prefix this (by rw [hrS, hrG]; rfl) hrog.2 hrpre hrpreT
  obtain ⟨wr, hwr⟩ : ∃ wr, g.value? r = some wr := by
    have := hrog.2; unfold rootP at this
    cases h : g.value? r with
    | none => rw [h] at this; cases this
    | some wr => exact ⟨wr, rfl⟩
  have hwrt : termOp wr.op = false := by
    have := hrog.2; simp only [rootP, hwr, Option.any_some] at this
    simp [termOp, this]
  obtain ⟨u, hu, hs, -, hpwr⟩ := atom_sched H B hrog.1 hwr hwrt
  rw [hur] at hu; cases hu
  -- the `Phi`s and the frames after them
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
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := src_eval H B R.treeS (P := pre) (Q := r :: post)
    hof hS1 (by rw [pS1, R.szS]) htyPS hpre
  have hMG := src_eval_mem H B R.treeS (P := pre) (Q := r :: post) hof hS1 hM1
    (by rw [pS1, R.szS]) htyPS hpre
  obtain ⟨hinvG, hqG⟩ := inv_evalAll (I := I) B.hfb hEI
    (fun x hx => sched_own H B x (by rw [hof]; exact List.mem_append_left _ hx))
      hpre (inv_phis B.hfb B.vS hpsS R.szS R.inv R.phis) (R.qinv fb psS B.hfb hpsS)
  have hfrT : { frT with regs := setPhis psT frT.regs } =
      { G with regs := ({ frT with regs := setPhis psT frT.regs } : Frame).regs } :=
    frame_trans (frame_trans rfl R.fr) (frame_symm (frame_trans g1 rfl))
  have hpreof : ∀ x ∈ pre, x ∈ of.toList := fun x hx => by rw [hof]; exact List.mem_append_left _ hx
  -- arguments of source values of `pre` and of `r` are in `V1` or `pre`
  have hargsS : ∀ x, (x ∈ pre ∨ x = r) → ∀ u, f.value? x = some u → ∀ a ∈ u.args,
      V1 f b fb a ∨ a ∈ pre := by
    intro x hx u hu a ha
    have hxof : x ∈ of.toList := hx.elim (hpreof x) fun h => h ▸ hrof
    rcases sched_args H.wf H.cf B.bmS B.hfb R.treeS B.mS x hxof u hu a ha with h | h
    · exact .inl h
    · right
      have hfa : a ∈ argsF f x := by rw [argsF_of hu]; exact Array.mem_toList_iff.2 ha
      rcases hx with hx | rfl
      · obtain ⟨d, s, hd⟩ := List.append_of_mem hx
        have htop := B.tpS
        rw [hof, hd, List.append_assoc, List.cons_append] at htop
        rw [hof, hd, List.append_assoc, List.cons_append] at h
        have := topoRem_before htop hfa h
        rw [hd]; exact List.mem_append_left _ this
      · have htop := B.tpS; rw [hof] at htop
        rw [hof] at h
        exact topoRem_before htop hfa h
  have hrelT0 : ∀ a, V1 g b gb a → (V1 f b fb a ∨ a ∈ pre) → ¬ IsTerm f.value? a →
      ¬ IsTerm (listedDefs g) a →
      Sem.Refines (rv G a) (rv { frT with regs := setPhis psT frT.regs } a) := by
    intro a ha _ _ hatE
    obtain ⟨w, hpw⟩ := v1_placed H.wg B.bmT B.hgb a ha
    have hwt := atom_of_not_term hpw hatE
    have hnpre : a ∉ pre := fun hm => v1_disj H.wf B.bmS B.hfb B.mS a (hpreof a hm) (by
      rcases ha with ⟨w', hpw', hanc, hne⟩ | ⟨haz, w', hw', hph⟩
      · have hww := placed_val hpw' hpw.1; subst hww
        obtain ⟨-, hnS⟩ := atom_out H B hpw hwt hne
        exact absurd ((B.mS a).1 (hpreof a hm)).1 hnS
      · obtain ⟨u', hpu, hs'⟩ := gatom_f H hpw hwt
        obtain ⟨-, u'', hu'', hph'⟩ := (B.mS a).1 (hpreof a hm)
        rw [hpu.1] at hu''; cases hu''
        rw [placed_val hpw hw'] at hph
        exact absurd (hs'.1.trans hph) hph')
    rcases ha with ⟨w', hpw', hanc, hne⟩ | ⟨haz, w', hw', hph⟩
    · have hww := placed_val hpw' hpw.1; subst hww
      obtain ⟨hnT, hnS⟩ := atom_out H B hpw hwt hne
      have hreg := reg_rv (hT1 a (.inl ⟨w, hpw, hanc, hne⟩)).1
      rw [pT3 a (.inl hnT)] at hreg
      obtain ⟨y, hy, hyy⟩ := R.atoms a w hpw hwt _ hreg
      rw [rv_of (show G.regs[a]? = some (some y) by
        rw [g5 a hnpre]; exact (pS3 a (.inl hnS)).trans hy)]
      unfold rv; rw [pT3 a (.inl hnT), hreg]; exact hyy
    · obtain ⟨y, y', hy, hy', hyy⟩ := hphis a haz w' hw' hph
      rw [rv_of (show G.regs[a]? = some (some y) by rw [g5 a hnpre]; exact hy)]
      show Sem.Refines y (rv { frT with regs := setPhis psT frT.regs } a)
      rw [rv_of hy']; exact hyy
  have hogpre : ∀ x ∈ preT, x ∈ og.toList := fun x hx => by rw [hog]; exact List.mem_append_left _ hx
  obtain ⟨T, hevT, l1, l2, l3, l4, l5, l6⟩ := tgt_loop H hE (og := og.toList) (L := preT)
    (M := r :: postT) (P := pre) hog hfrT (by rw [pT1, R.szT]) g3 htyPT g4 hMG hT1
    (v1_placed H.wg B.bmT B.hgb) (v1_disj H.wg B.bmT B.hgb B.mT) hrelT0 B.ndT B.tpT
    (b := b) (fun x hx => by
      obtain ⟨hxb, w, hw, hph⟩ := (B.mT x).1 hx
      obtain ⟨hp, hwb, hid⟩ := placed_in H.wg B.bmT B.hgb hxb hw
      exact ⟨w, hp, hid, hph, hwb⟩) hinvG hqG (fun a h => .inl (.inl h))
    (sched_args H.wg H.cg B.bmT B.hgb R.treeT B.mT)
    (fun a ha hVS hat => by
      rcases hVS with h | h
      · exfalso
        obtain ⟨hxb, w, hw, -⟩ := (B.mT a).1 ha
        obtain ⟨-, -, -, hof', -⟩ := atom_sched H B ha hw (atom_of_not_term
          (placed_in H.wg B.bmT B.hgb hxb hw).1 hat)
        exact v1_disj H.wf B.bmS B.hfb B.mS a hof' h
      · exact h)
    (fun x hx w hw ht => by
      obtain ⟨u, hu, hs', hxof, -⟩ := atom_sched H B (hogpre x hx) hw ht
      refine ⟨u, hu, hs', fun hxp => ⟨hargsS x (.inl hxp) u hu, ?_⟩, fun hxp => ?_⟩
      · obtain ⟨u', y, hu', hy, hev⟩ := g6 x hxp
        rw [hu] at hu'; cases hu'
        exact ⟨y, hy, hev⟩
      · have hxr : x ≠ r := fun h => hrpreT (h ▸ hx)
        refine ⟨?_, fun ha => hxp (arg_before H B hof hur hrp hxof hxr hu (.inl (hs'.1.trans ha))),
          fun ha => hxp (arg_before H B hof hur hrp hxof hxr hu (.inr (hs'.1.trans ha)))⟩
        cases hroot : isRoot w.op
        · rfl
        · exfalso
          have : x ∈ preT.filter (rootP g) := List.mem_filter.2 ⟨hx, by simp [rootP, hw, hroot]⟩
          rw [← hfl] at this
          exact hxp (List.mem_filter.1 this).1)
  -- the root `r` in the target
  have hrblk : wr.block = b :=
    (placed_in H.wg B.bmT B.hgb ((B.mT r).1 hrog.1).1 hwr).2.1
  have hrT := tgt_atom_ref H hE (frame_trans l1 hfrT) g4 hMG l4
    (fun a ha => ha.elim (v1_placed H.wg B.bmT B.hgb a) fun hm => by
      obtain ⟨hxb, w, hw, -⟩ := (B.mT a).1 (hogpre a hm)
      exact ⟨w, (placed_in H.wg B.bmT B.hgb hxb hw).1⟩)
    l6 g3 l3 hpwr hur hs hwrt (by
      obtain ⟨-, w', hw', hph⟩ := (B.mT r).1 hrog.1
      rw [hwr] at hw'; cases hw'; exact hph) (hargsS r (.inr rfl) ur hur) (fun a ha => by
      rcases sched_args H.wg H.cg B.bmT B.hgb R.treeT B.mT r hrog.1 wr hwr a ha with h | h
      · exact .inl h
      · right
        have htop := B.tpT; rw [hog] at htop h
        exact topoRem_before htop (by rw [argsF_of hwr]; exact Array.mem_toList_iff.2 ha) h)
    (hrblk ▸ hinvG) (hrblk ▸ hqG) (hrblk ▸ fun a h => .inl (.inl h))
  rw [hevr] at hrT
  obtain ⟨m', hT', hm⟩ := res_panic_of_refines hrT
  refine ⟨m', enterBlock_of hpsT (by rw [sched_eq B.hgb B.idT, B.sT]) ?_, hm⟩
  rw [hog, evalAll_append, hevT]
  show evalAll env (Ctx.make tabs g) T (r :: postT) = _
  rw [evalAll_cons]
  unfold stepV
  rw [show (Ctx.make tabs g).f = g from rfl, hwr]
  simp only [hT']

end GoFV.Proof.AtomSim

import GoFV.Proof.Pass.StructStoreBlock

/-!
# Struct-store splits: one block's evaluation (issue #151)

`Blk.step`: one value of the target's schedule keeps `TFacts`, if every target root it reaches
is covered by the source (a value the source evaluated, or a field store of a split it
evaluated) and an argument lookup it reaches was evaluated by the source. `okCase`: if the source
evaluates the block, the target does, its registers refining the source's. `panicCase`: if the
source panics, the target panics alike on a refined memory (the roots before the panicking one
are covered: `rootsBefore`, the target's roots are the source's with each split's field stores
in its place; a pure value the source did not reach is no argument lookup, as the source's
schedule lists those first).
-/

namespace GoFV.Proof.StructStore

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Proof.CopyElim GoFV.Opt GoFV.Opt.RewriteCheck
open GoFV.Proof.CSE (Base Node SFacts)
open GoFV.Proof.AtomSim (Reg rv evalValue_of_regs regs_of_ok)

variable {env : Env} {tabs : Tables} {f g : Func} {bid : ID} {fb gb : Block} {F0 F0T : Frame}
  {oS oT : Array ID}

namespace Blk

variable (K : Blk env tabs f g bid fb gb F0 F0T oS oT)
include K

/-- **One target step.** -/
theorem step (hE : env.Mono) {S T : Frame} {k j : Nat} {x : ID}
    (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hT : TFacts tabs f g F0T S T (oS.toList.take k) (oT.toList.take j))
    (hjT : oT.toList[j]? = some x)
    (hcov : CSE.rootNode g x = true → x ∈ oS.toList.take k ∨
      ∃ x' ps, ssSplit? tabs f g x' = some ps ∧ x' ∈ oS.toList.take k ∧ ∃ q ∈ ps, q.2 = x)
    (hpure : ∀ fv, f.value? x = some fv → x ∉ oS.toList.take k →
      fv.op ≠ .Arg ∧ fv.op ≠ .ArgIntReg) :
    ∃ y, stepV env (Ctx.make tabs g) T x = .ok y ∧
      TFacts tabs f g F0T S (T.set x y) (oS.toList.take k) (oT.toList.take (j + 1)) := by
  obtain ⟨hxgb, gv, hgv, hgph⟩ := K.memT.1 (List.mem_of_getElem? hjT)
  rw [stepV_of (ctx := Ctx.make tabs g) hgv]
  have hpreF : ∀ z ∈ oS.toList.take k, ∃ v, f.value? z = some v := fun z hz => by
    obtain ⟨-, v, hv, -⟩ := K.hLk k z hz; exact ⟨v, hv⟩
  cases hfx : f.value? x with
  | some fv =>
    have hne : ∀ x' ps (d : SplitD tabs f g x' ps) (i : Nat) (p s : ID), ps[i]? = some (p, s) →
        p ≠ x ∧ s ≠ x := fun x' ps d i p s hi => by
      obtain ⟨o, t, a, av, sv, ov, -, -, L⟩ := link_at d hi
      exact ⟨fun h => (by have := L.hpf; rw [h, hfx] at this; cases this),
        fun h => (by have := L.hsf; rw [h, hfx] at this; cases this)⟩
    have hxF : Node f fb x := K.nodeF ⟨hxgb, gv, hgv, hgph⟩ hfx
    obtain ⟨gv', hgv', hsv⟩ := K.gval hfx
    rw [hgv] at hgv'; cases hgv'
    have hvoff : ∀ (y : Val) x' ps (d : SplitD tabs f g x' ps), x' ∈ oS.toList.take k →
        ∀ (i : Nat) (s : ID) (o : Nat) (t : Ty) (P : Ptr), ps[i]? = some (x, s) →
        d.fs[i]? = some (o, t) → S.regs[d.dst]? = some (some (.ptr P)) →
        y = .ptr (P.add (BitVec.ofNat 64 o)) :=
      fun y x' ps d _ i s o t P hi => absurd rfl (hne x' ps d i x s hi).1
    have hvst : ∀ (y : Val) x' ps (d : SplitD tabs f g x' ps), x' ∈ oS.toList.take k →
        ∀ (i : Nat) (p : ID) (P : Ptr) (M : Mem), ps[i]? = some (p, x) →
        S.regs[d.dst]? = some (some (.ptr P)) → S.regs[d.mem]? = some (some (.mem M)) →
        ∃ Mk M', M.write P (bufK S d (i + 1)) = some Mk ∧ y = .mem M' ∧ Mem.Refines Mk M' :=
      fun y x' ps d _ i p P M hi => absurd rfl (hne x' ps d i p x hi).2
    by_cases hxS : x ∈ oS.toList.take k
    · obtain ⟨y, hy, hr⟩ : ∃ y, evalValue env (Ctx.make tabs g) T gv = .ok y ∧
          ∃ yS, S.regs[x]? = some (some yS) ∧ Sem.Refines yS y := by
        rcases hsv with hs | ⟨ps, hps⟩
        · exact K.keptOk hE hS hT hjT hxS hgv hfx hs
        · obtain ⟨d⟩ := ssSplit_spec hps
          have h := d.hgv; rw [hgv] at h; cases h
          exact K.splitOk hS hT hjT hxS d
      exact ⟨y, hy, K.tstep hjT hT (fun _ => hr) (hvoff y) (hvst y)⟩
    · obtain ⟨y, hy⟩ : ∃ y, evalValue env (Ctx.make tabs g) T gv = .ok y := by
        rcases hsv with hs | ⟨ps, hps⟩
        · obtain ⟨-, hop, -, -, -, -, hga⟩ := ssSame_spec hs
          have hroot : CSE.rootNode g x = false := by
            cases hr : CSE.rootNode g x with
            | false => rfl
            | true =>
              rcases hcov hr with h | ⟨x', ps, hps, -, q, hq, hqx⟩
              · exact absurd h hxS
              · obtain ⟨d⟩ := ssSplit_spec hps
                obtain ⟨i, hi⟩ := List.getElem?_of_mem hq
                exact absurd hqx (hne x' ps d i q.1 q.2 hi).2
          have hp0 : Sem.prio gv.op = 0 := by simpa [CSE.rootNode, hgv] using hroot
          obtain ⟨ha, hb⟩ := hpure fv hfx hxS
          refine pureEval (fun a ha' => ?_) (CSE.Blk.isRoot_of_prio hp0) (by rw [hop]; exact ha)
            (by rw [hop]; exact hb)
          obtain ⟨hxb, v, hv, hph⟩ := hxF
          rw [hfx] at hv; cases hv
          rcases K.arg_base_or_node hxb hfx hph (hga ▸ ha') with hB | hn
          · exact K.argDefd hS hT hjT hgv ha' (.inl hB)
          · exact K.argDefd hS hT hjT hgv ha' (.inr (K.nodeG hn))
        · obtain ⟨d⟩ := ssSplit_spec hps
          have h := d.hgv; rw [hgv] at h; cases h
          exact K.splitPure hS hT hjT d
      exact ⟨y, hy, K.tstep hjT hT (fun h => absurd h hxS) (hvoff y) (hvst y)⟩
  | none =>
    have hnpre : x ∉ oS.toList.take k := fun h => by
      obtain ⟨v, hv⟩ := hpreF x h; rw [hfx] at hv; cases hv
    obtain ⟨E, hE', hEf⟩ := K.gvalues
    have hxE : x ∈ E := by
      rw [hE'] at hxgb
      rcases Array.mem_append.1 hxgb with h | h
      · obtain ⟨v, hv, -⟩ := K.valueIn h; rw [hfx] at hv; cases hv
      · exact h
    obtain ⟨-, ⟨x0, ps0, hps0, q0, hq0, hxq⟩, v0, hv0, hvb⟩ := hEf x hxE
    rw [hgv] at hv0; cases hv0
    obtain ⟨d0⟩ := ssSplit_spec hps0
    obtain ⟨i0, hi0⟩ := List.getElem?_of_mem hq0
    obtain ⟨p0, s0⟩ := q0
    rcases hxq with hx | hx
    · -- a fresh `OffPtr`
      simp only at hx; subst hx
      obtain ⟨o0, t0, a0, av0, sv0, ov0, hf0, ha0, L0⟩ := link_at d0 hi0
      rw [L0.hp] at hgv; cases hgv
      have hb : d0.fv.block = bid := by rw [← L0.hpbl]; exact hvb
      have hx0 : Node f fb x0 := K.split_node d0 hb
      have hdN := K.n_arg (.inr hx0) d0.hfv (by rw [d0.hop]; decide)
        (show d0.dst ∈ d0.fv.args by rw [d0.hfargs]; simp)
      have hargs := L0.hpargs
      have hdst := L0.hdst
      generalize hd' : gv.args[0]! = d' at hargs hdst
      have hd'N := K.n_copy _ hdN hdst
      obtain ⟨y, hy⟩ := pureEval (env := env) (fun a ha => by
          have ha' := ha
          rw [hargs] at ha'; simp only [List.mem_toArray, List.mem_singleton] at ha'; subst ha'
          rcases hd'N with h | h
          · exact K.argDefd hS hT hjT L0.hp ha (.inl h)
          · exact K.argDefd hS hT hjT L0.hp ha (.inr (K.nodeG h)))
        (by rw [L0.hpop]; decide) (by rw [L0.hpop]; decide) (by rw [L0.hpop]; decide)
      refine ⟨y, hy, K.tstep hjT hT (fun h => absurd h hnpre) ?_ ?_⟩
      · intro x' ps d hx' i s o t P hi hfi hP
        obtain ⟨o', t', a, av, sv, ov, hfi', -, L⟩ := link_at d hi
        rw [hfi] at hfi'; cases hfi'
        have h := L.hp; rw [L0.hp] at h; cases h
        have := K.offVal hS hT hjT d hx' hfi L hP
        rw [hy] at this; cases this; rfl
      · intro x' ps d hx' i p P M hi hP hM
        obtain ⟨o', t', a, av, sv, ov, -, -, L⟩ := link_at d hi
        have h := L.hs; rw [L0.hp] at h; cases h
        exact absurd (L0.hpop.symm.trans L.hsop) (by decide)
    · -- a fresh field store
      simp only at hx; subst hx
      obtain ⟨o0, t0, a0, av0, sv0, ov0, hf0, ha0, L0⟩ := link_at d0 hi0
      rw [L0.hs] at hgv; cases hgv
      have hroot : CSE.rootNode g x = true := by
        unfold CSE.rootNode; rw [L0.hs]; simp only [Option.map_some, Option.getD_some, L0.hsop]
        decide
      rcases hcov hroot with h | ⟨x1, ps1, hps1, hx1, q1, hq1, hqx1⟩
      · exact absurd h hnpre
      obtain ⟨d1⟩ := ssSplit_spec hps1
      obtain ⟨i1, hi1⟩ := List.getElem?_of_mem hq1
      obtain ⟨p1, s1⟩ := q1
      simp only at hqx1; subst hqx1
      obtain ⟨P1, M1, MS1, hP1, hM1, -, -⟩ := K.split_src hS d1 hx1
      obtain ⟨sv, M2, M2', hsv, he, -, -⟩ := K.storeAt hS hT hjT d1 hx1 hi1 hP1 hM1
      rw [L0.hs] at hsv; cases hsv
      refine ⟨_, he, K.tstep hjT hT (fun h => absurd h hnpre) ?_ ?_⟩
      · intro x' ps d hx' i s o t P hi
        obtain ⟨o', t', a, av, sv, ov, -, -, L⟩ := link_at d hi
        have h := L.hp; rw [L0.hs] at h; cases h
        exact absurd (L0.hsop.symm.trans L.hpop) (by decide)
      · intro x' ps d hx' i p P M hi hP hM
        obtain ⟨sv, M3, M3', hsv, he', hw3, hr3⟩ := K.storeAt hS hT hjT d hx' hi hP hM
        rw [L0.hs] at hsv; cases hsv
        rw [he] at he'; cases he'
        exact ⟨M3, _, hw3, rfl, hr3⟩

omit K in
/-- **The target's loop** over the first `K'` values of its schedule. -/
theorem loop {S : Frame} {pre : List ID} {K' : Nat}
    (hev : ∀ j x, j < K' → oT.toList[j]? = some x → ∀ T,
      TFacts tabs f g F0T S T pre (oT.toList.take j) →
      ∃ y, stepV env (Ctx.make tabs g) T x = .ok y ∧
        TFacts tabs f g F0T S (T.set x y) pre (oT.toList.take (j + 1))) :
    ∃ T', evalAll env (Ctx.make tabs g) F0T (oT.toList.take K') = .ok T' ∧
      TFacts tabs f g F0T S T' pre (oT.toList.take K') := by
  have hstep : ∀ d x rest T, oT.toList.take K' = d ++ x :: rest →
      (d = oT.toList.take d.length ∧ TFacts tabs f g F0T S T pre d) →
      ∃ y, stepV env (Ctx.make tabs g) T x = .ok y ∧
        (d ++ [x] = oT.toList.take (d ++ [x]).length ∧
          TFacts tabs f g F0T S (T.set x y) pre (d ++ [x])) := by
    intro d x rest T hL ⟨hd, hT⟩
    have hjx : (oT.toList.take K')[d.length]? = some x := by rw [hL]; simp
    have hjK : d.length < K' := by
      have := (List.getElem?_eq_some_iff.1 hjx).1; simp at this; omega
    have hj : oT.toList[d.length]? = some x := by
      rwa [List.getElem?_take_of_lt hjK] at hjx
    rw [hd] at hT
    obtain ⟨y, hy, hT'⟩ := hev d.length x hjK hj T hT
    refine ⟨y, hy, ?_, ?_⟩
    · rw [List.length_append, List.length_singleton, take_succ_eqT hj, ← hd]
    · rw [hd, ← take_succ_eqT hj]; exact hT'
  obtain ⟨T', h1, -, h2⟩ := CSE.evalAll_loop hstep (oT.toList.take K') [] F0T rfl
    ⟨rfl, tfacts_zero (oT := oT)⟩
  exact ⟨T', h1, h2⟩

/-- **The ok case.** -/
theorem okCase (hE : env.Mono) {G : Frame}
    (h : evalAll env (Ctx.make tabs f) F0 oS.toList = .ok G) :
    ∃ GT, evalAll env (Ctx.make tabs g) F0T oT.toList = .ok GT ∧
      GT = { G with regs := GT.regs } ∧ GT.regs.size = g.valueTab.size ∧ RR f G.regs GT.regs := by
  have hS : SFacts env tabs f F0 G (oS.toList.take oS.toList.length) := by
    rw [List.take_length]; exact K.sfacts ⟨[], by simp⟩ h
  obtain ⟨T', h1, hT'⟩ := loop (env := env) (S := G) (pre := oS.toList.take oS.toList.length)
    (K' := oT.toList.length) fun j x hj hjx T hT => by
      have hxT := K.memT.1 (List.mem_of_getElem? hjx)
      refine K.step hE hS hT hjx (fun hr => ?_) (fun fv hfv hn => ?_)
      · cases hfx : f.value? x with
        | some fv => exact .inl (by rw [List.take_length]; exact K.memS.2 (K.nodeF hxT hfx))
        | none =>
          have hm : x ∈ oT.toList.filter (CSE.rootNode g) :=
            List.mem_filter.2 ⟨List.mem_of_getElem? hjx, hr⟩
          rw [K.roots] at hm
          rcases mem_ssRoots hm with hy | ⟨y, ps, hy, hs, q, hq, hqz⟩
          · obtain ⟨-, v, hv, -⟩ := K.memS.1 (List.mem_filter.1 hy).1
            rw [hfx] at hv; cases hv
          · refine .inr ⟨y, ps, ?_, by rw [List.take_length]; exact (List.mem_filter.1 hy).1,
              q, hq, hqz⟩
            rwa [splits_get] at hs
      · exact absurd (by rw [List.take_length]; exact K.memS.2 (K.nodeF hxT hfv)) hn
  have hfr := K.tframe hS hT'
  simp only [List.take_length] at h1 hT' hS
  refine ⟨T', h1, hfr, by rw [hT'.size, K.sizeT], fun a v yS hv hyS => ?_⟩
  by_cases haS : a ∈ oS.toList
  · have haT : a ∈ oT.toList := K.memT.2 (K.nodeG (K.memS.1 haS))
    obtain ⟨yS', yT, h1', h2', h3'⟩ := hT'.rel a haT haS
    rw [hyS] at h1'; cases h1'
    exact ⟨yT, h2', h3'⟩
  · have haT : a ∉ oT.toList := fun hm => haS (K.memS.2 (K.nodeF (K.memT.1 hm) hv))
    rw [hS.out a haS] at hyS
    obtain ⟨yT, hyT, hr⟩ := K.rr a v yS hv hyS
    exact ⟨yT, by rw [hT'.out a haT]; exact hyT, hr⟩

/-- The target's roots before a kept root `r` are covered by the source's before it. -/
theorem rootsBefore {k k' : Nat} {r : ID} (hk : oS.toList[k]? = some r)
    (hk' : oT.toList[k']? = some r) (hfr : CSE.rootNode f r = true)
    (hgr : CSE.rootNode g r = true) {rv0 : Value} (hrv : f.value? r = some rv0)
    (hrs : ssSplit? tabs f g r = none) :
    ∀ y ∈ oT.toList.take k', CSE.rootNode g y = true → y ∈ oS.toList.take k ∨
      ∃ x' ps, ssSplit? tabs f g x' = some ps ∧ x' ∈ oS.toList.take k ∧ ∃ q ∈ ps, q.2 = y := by
  intro y hy hry
  have hsr : ((Array.range f.valueTab.size).map (ssSplit? tabs f g))[r]?.join = none := by
    rw [splits_get, hrs]
  have hR := K.roots
  rw [CSE.split_at hk', CSE.split_at hk, List.filter_append, List.filter_append,
    List.filter_cons_of_pos hgr, List.filter_cons_of_pos hfr, ssRoots_append,
    ssRoots_cons_none _ _ hsr] at hR
  have heq := CSE.prefix_eq hR (fun hm => CSE.not_mem_take_of K.ndT hk' (List.mem_filter.1 hm).1)
    (fun hm => by
      rcases mem_ssRoots hm with h | ⟨z, ps, -, hs, q, hq, hqr⟩
      · exact CSE.not_mem_take_of K.ndS hk (List.mem_filter.1 h).1
      · rw [splits_get] at hs
        obtain ⟨d⟩ := ssSplit_spec hs
        obtain ⟨i, hi⟩ := List.getElem?_of_mem hq
        obtain ⟨o, t, a, av, sv, ov, -, -, L⟩ := link_at d hi
        have := L.hsf; rw [hqr, hrv] at this; cases this)
  have hm : y ∈ (oT.toList.take k').filter (CSE.rootNode g) := List.mem_filter.2 ⟨hy, hry⟩
  rw [heq] at hm
  rcases mem_ssRoots hm with h | ⟨z, ps, hz, hs, q, hq, hqy⟩
  · exact .inl (List.mem_filter.1 h).1
  · rw [splits_get] at hs
    exact .inr ⟨z, ps, hs, (List.mem_filter.1 hz).1, q, hq, hqy⟩

theorem nodeOf_x {x : ID} {v : Value} (hx : x ∈ fb.values) (hv : f.value? x = some v)
    (hph : v.op ≠ .Phi) : nodeOf (schedNodes f fb).toList x = some ⟨x, v.args, prio v.op⟩ := by
  obtain ⟨v', hv', hid, -⟩ := K.valueIn hx
  rw [hv] at hv'; cases hv'
  have hm : (⟨v.id, v.args, prio v.op⟩ : SNode) ∈ (schedNodes f fb).toList :=
    mem_schedNodes.2 ⟨x, hx, v, hv, hph, rfl⟩
  have := nodeOf_of_mem (schedNodes_ids K.ownF K.ndF) hm
  rw [hid] at this; exact this

/-- **The panic case.** -/
theorem panicCase (hE : env.Mono) {e : Panic} {m : Mem}
    (h : evalAll env (Ctx.make tabs f) F0 oS.toList = .panic e m) :
    ∃ m', evalAll env (Ctx.make tabs g) F0T oT.toList = .panic e m' ∧ Mem.Refines m m' := by
  obtain ⟨ce, hwf⟩ := K.wf
  obtain ⟨pre, r, post, Gp, hsplit, hpre, hrp⟩ := evalAll_panic_split h
  have hk : oS.toList[pre.length]? = some r := by rw [hsplit]; simp
  have htk : oS.toList.take pre.length = pre := by rw [hsplit]; simp
  have hS : SFacts env tabs f F0 Gp (oS.toList.take pre.length) := by
    rw [htk]; exact K.sfacts ⟨r :: post, hsplit⟩ hpre
  have hrS : r ∈ oS.toList := List.mem_of_getElem? hk
  obtain ⟨hrb, rv0, hrv, hrph⟩ := K.memS.1 hrS
  rw [stepV_of (ctx := Ctx.make tabs f) hrv] at hrp
  have hrop : Panicking rv0.op := evalValue_panic_op hrp
  have hp2 : Sem.prio rv0.op ≠ 0 := prio_panicking hrop
  have hnsplit : ∀ ps, ssSplit? tabs f g r = some ps → False := fun ps hps => by
    obtain ⟨d⟩ := ssSplit_spec hps
    rw [d.hfv] at hrv; cases hrv
    rw [d.hop] at hrop
    rcases hrop with h' | h' <;> exact absurd h' (by decide)
  obtain ⟨gr, hgr, hsr⟩ := K.gval hrv
  have hs : ssSame rv0 gr = true := hsr.resolve_right fun ⟨ps, hps⟩ => hnsplit ps hps
  have hrs : ssSplit? tabs f g r = none := by
    cases hq : ssSplit? tabs f g r with
    | none => rfl
    | some ps => exact (hnsplit ps hq).elim
  have hgroot : CSE.rootNode g r = true := by
    simp [CSE.rootNode, hgr, (ssSame_spec hs).2.1, hp2]
  have hfroot : CSE.rootNode f r = true := by simp [CSE.rootNode, hrv, hp2]
  obtain ⟨k', hk'⟩ := List.getElem?_of_mem (K.memT.2 (K.nodeG (K.memS.1 hrS)))
  have hroots := K.rootsBefore hk hk' hfroot hgroot hrv hrs
  obtain ⟨T', h1, hT'⟩ := loop (env := env) (S := Gp) (pre := oS.toList.take pre.length) (K' := k')
    (fun j x hj hjx T hT => by
      have hxmem : x ∈ oT.toList.take k' :=
        List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hj]; exact hjx)
      refine K.step hE hS hT hjx (fun hr => hroots x hxmem hr) (fun fv hfv hn => ?_)
      have hxn := K.nodeF (K.memT.1 (List.mem_of_getElem? hjx)) hfv
      obtain ⟨hxb, fv', hfv', hph⟩ := hxn
      rw [hfv] at hfv'; cases hfv'
      obtain ⟨i, hi⟩ := List.getElem?_of_mem (K.memS.2 ⟨hxb, fv, hfv, hph⟩)
      have hxr : x ≠ r := fun he => by
        subst he; exact absurd (Order.idx_unique K.ndT hjx hk') (by omega)
      have hki : pre.length < i := by
        rcases Nat.lt_or_ge pre.length i with h' | h'
        · exact h'
        · rcases Nat.lt_or_ge i pre.length with h'' | h''
          · exact absurd (List.mem_of_getElem? (by rw [List.getElem?_take_of_lt h'']; exact hi)) hn
          · have : i = pre.length := by omega
            subst this; rw [hk] at hi; cases hi; exact absurd rfl hxr
      have hxroot : CSE.rootNode g x = false := by
        cases hxr' : CSE.rootNode g x with
        | false => rfl
        | true =>
          rcases hroots x hxmem hxr' with h' | ⟨x', ps, hps, -, q, hq, hqx⟩
          · exact absurd h' hn
          · obtain ⟨d⟩ := ssSplit_spec hps
            obtain ⟨i', hi'⟩ := List.getElem?_of_mem hq
            obtain ⟨o, t, a, av, sv, ov, -, -, L⟩ := link_at d hi'
            have := L.hsf; rw [hqx, hfv] at this; cases this
      have hnA : ∀ op, fv.op = op → (op = .Arg ∨ op = .ArgIntReg) → False := by
        intro op hop hor
        obtain ⟨gv, hgv, hsv⟩ := K.gval hfv
        rcases hsv with hs' | ⟨ps, hps⟩
        · have hp0 : prio fv.op = 0 := by
            rw [← (ssSame_spec hs').2.1]; simpa [CSE.rootNode, hgv] using hxroot
          have hspec := schedule_spec K.hoS
          obtain ⟨a, haD, -⟩ := hspec.pureFirst pre.length i r x hki hk hi
            (fun hpu => by
              have := hpu _ (K.nodeOf_x hrb hrv hrph)
              exact hp2 this)
            (fun n hn => by rw [K.nodeOf_x hxb hfv hph] at hn; cases hn; exact hp0)
          rw [argsOf_schedNodes K.ownF K.ndF hxb hfv hph] at haD
          have hne : fv.args.size ≠ 0 := fun h0 => by
            rw [Array.eq_empty_of_size_eq_zero h0] at haD; simp at haD
          have har := hwf.arity bid fb x fv ⟨⟨K.tree.1, K.hfb⟩, hxb, hfv⟩
            (by rw [hop, CSE.argLen_zero_of_arg hor]; decide)
          rw [hop, CSE.argLen_zero_of_arg hor] at har
          exact hne (by exact_mod_cast har)
        · obtain ⟨d⟩ := ssSplit_spec hps
          rw [d.hfv] at hfv; cases hfv
          rw [d.hop] at hop
          rcases hor with h' | h' <;> rw [h'] at hop <;> cases hop
      exact ⟨fun h' => hnA _ h' (.inl rfl), fun h' => hnA _ h' (.inr rfl)⟩)
  have hrid : rv0.id = r := by
    obtain ⟨v', hv', hid, -⟩ := K.valueIn hrb
    rw [hrv] at hv'; cases hv'; exact hid
  have hres := K.keptRes hE hS hT' hk' hrv hrid hgr hs (fun a ha => by
      rcases K.arg_base_or_node hrb hrv hrph ha with hB | hn
      · exact .inl hB
      · obtain ⟨i, hi, hia⟩ := K.topoS hk hrv ha hn
        exact .inr (List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hi]; exact hia)))
    (AtomSim.regs_of_panic hrp)
  rw [hrp] at hres
  generalize hT'r : evalValue env (Ctx.make tabs g) T' gr = rT at hres
  cases hres with
  | panic e hm =>
    refine ⟨_, ?_, hm⟩
    rw [CSE.split_at hk', evalAll_append, h1]
    show evalAll env (Ctx.make tabs g) T' (r :: oT.toList.drop (k' + 1)) = _
    rw [evalAll_cons, stepV_of (ctx := Ctx.make tabs g) hgr, hT'r]

end Blk

end GoFV.Proof.StructStore

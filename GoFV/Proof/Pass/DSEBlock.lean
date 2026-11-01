import GoFV.Proof.Pass.DSEBlockBase

/-!
# dse: one block's evaluation

`okCase`: if the source evaluates the block's schedule to `G`, the target evaluates its schedule
to a frame that agrees with `G` on every value without pending ranges; `panicCase`: if the
source panics, the target panics alike. Induction along the target's schedule
(`CSE.evalAll_loop`): a value the source evaluated before it stops evaluates to a related
register (`step_ok`); a value it did not reach (it panicked first) is pure in the target (the
roots of `g` keep their order, `CSE.roots_before`): an eliminated store's `Copy`, or a pure
value with arguments (`PureFirst`), which evaluates; the panicking value panics alike
(`step_panic`).
-/

namespace GoFV.Proof.DSE

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Proof.CopyElim GoFV.Opt GoFV.Opt.DSE
open GoFV.Proof.CSE (Base Node SFacts)

variable {env : Env} {tabs : Tables} {f g : Func} {P : ID → List Iv} {bid : ID}
  {fb gb : Block} {F0 F0T : Frame} {oS oT : Array ID}

namespace Blk

variable (K : Blk env tabs f g P bid fb gb F0 F0T oS oT)
include K

theorem tframe {S T : Frame} {pre done : List ID} (hS : SFacts env tabs f F0 S pre)
    (hT : TFacts P F0T S T pre done) : T = { S with regs := T.regs } :=
  calc T = { F0T with regs := T.regs } := hT.frame
    _ = { F0 with regs := T.regs } := by rw [K.frT]
    _ = { S with regs := T.regs } := by rw [hS.frame]

/-- A target argument of a node the source evaluated: related registers. -/
theorem argRel {S T : Frame} {k j : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hT : TFacts P F0T S T (oS.toList.take k) (oT.toList.take j)) {x : ID} {fv gv : Value}
    (hfv : f.value? x = some fv) (hgv : g.value? x = some gv) (hxb : fv.block = bid)
    (hjT : oT.toList[j]? = some x) {a : ID} (ha : a ∈ gv.args)
    (hpre : Base f bid a ∨ a ∈ oS.toList.take k) :
    ∃ vS vT, S.regs[a]? = some (some vS) ∧ T.regs[a]? = some (some vT) ∧
      VRel (IvQ (P a)) vS vT := by
  have hL : ∀ y ∈ oS.toList.take k, Node f fb y := fun y hy => K.memS.1 (List.mem_of_mem_take hy)
  have hLT : ∀ y ∈ oT.toList.take j, Node f fb y := fun y hy => K.memT.1 (List.mem_of_mem_take hy)
  have base : Base f bid a → ∃ vS vT, S.regs[a]? = some (some vS) ∧
      T.regs[a]? = some (some vT) ∧ VRel (IvQ (P a)) vS vT := fun hB => by
    have hc := K.base_clean hfv (K.gargs hfv hgv ha) hB hxb
    obtain ⟨-, y, -, hy, -⟩ := K.base_val hS hL hB
    refine ⟨y, y, hy, ?_, .inl rfl⟩
    rw [K.base_reg hB hLT hT.out, K.agree a hc, ← K.base_reg hB hL hS.out, hy]
  rcases hpre with hB | hp
  · exact base hB
  · rcases K.tArgsT hjT hgv ha with hB | hd
    · exact base hB
    · exact hT.rel a hd hp

/-- **A value the source evaluated before it stops** evaluates in the target to a related
register. -/
theorem sameStep {S T : Frame} {k j : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hT : TFacts P F0T S T (oS.toList.take k) (oT.toList.take j)) {x : ID}
    (hjT : oT.toList[j]? = some x) (hxS : x ∈ oS.toList.take k) :
    ∃ y, stepV env (Ctx.make tabs g) T x = .ok y ∧
      ∃ yS, S.regs[x]? = some (some yS) ∧ VRel (IvQ (P x)) yS y := by
  obtain ⟨fv, yS, hfv, hyS, hev⟩ := hS.eval x hxS
  obtain ⟨hxb, fv', hfv', hph⟩ := K.memS.1 (List.mem_of_mem_take hxS)
  rw [hfv] at hfv'; cases hfv'
  obtain ⟨v', hv', hid, hbl⟩ := K.valueIn hxb
  rw [hfv] at hv'; cases hv'
  obtain ⟨gv, hgv, -⟩ := K.gval hfv
  have H := K.avail hS
  obtain ⟨y, hy, hrel⟩ := step_ok K.rel H (K.tframe hS hT) hfv hgv hid
    (fun a ha => H.cl x fv (.inr hxS) hfv hph a ha)
    (fun a ha => K.argRel hS hT hfv hgv hbl hjT ha
      (H.cl x fv (.inr hxS) hfv hph a (K.gargs hfv hgv ha))) hev
  exact ⟨y, by rw [stepV_of (ctx := Ctx.make tabs g) hgv]; exact hy, yS, hyS, hrel⟩

/-- **The panicking value** panics alike in the target. -/
theorem panicStep {S T : Frame} {k j : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hT : TFacts P F0T S T (oS.toList.take k) (oT.toList.take j)) {r : ID}
    (hjT : oT.toList[j]? = some r) (hk : oS.toList[k]? = some r) {e : Panic} {m : Mem}
    (h : stepV env (Ctx.make tabs f) S r = .panic e m) :
    stepV env (Ctx.make tabs g) T r = .panic e m := by
  obtain ⟨hrb, fv, hfv, hph⟩ := K.memS.1 (List.mem_of_getElem? hk)
  obtain ⟨v', hv', hid, hbl⟩ := K.valueIn hrb
  rw [hfv] at hv'; cases hv'
  obtain ⟨gv, hgv, -⟩ := K.gval hfv
  rw [stepV_of (ctx := Ctx.make tabs f) hfv] at h
  rw [stepV_of (ctx := Ctx.make tabs g) hgv]
  refine step_panic K.rel (K.tframe hS hT) hfv hgv hid (fun a ha => ?_) h
  refine K.argRel hS hT hfv hgv hbl hjT ha ?_
  rcases K.arg_base_or_node hrb hfv hph (K.gargs hfv hgv ha) with hB | hn
  · exact .inl hB
  · obtain ⟨i, hi, hia⟩ := K.topoS hk hfv (K.gargs hfv hgv ha) hn
    have : (oS.toList.take k)[i]? = some a := by rw [List.getElem?_take_of_lt hi]; exact hia
    exact .inr (List.mem_of_getElem? this)

/-- **A value pure in the target** evaluates once its arguments are defined (not an argument
lookup). -/
theorem pureStep {S T : Frame} {k j : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hT : TFacts P F0T S T (oS.toList.take k) (oT.toList.take j)) {x : ID}
    (hjT : oT.toList[j]? = some x) (hr : CSE.rootNode g x = false) {fv : Value}
    (hfv : f.value? x = some fv) (ha : fv.op ≠ .Arg) (hb : fv.op ≠ .ArgIntReg) :
    ∃ y, stepV env (Ctx.make tabs g) T x = .ok y := by
  have hL : ∀ y ∈ oS.toList.take k, Node f fb y := fun y hy => K.memS.1 (List.mem_of_mem_take hy)
  have hLT : ∀ y ∈ oT.toList.take j, Node f fb y := fun y hy => K.memT.1 (List.mem_of_mem_take hy)
  obtain ⟨hxb, -⟩ := K.memT.1 (List.mem_of_getElem? hjT)
  obtain ⟨v', hv', -, hbl⟩ := K.valueIn hxb
  rw [hfv] at hv'; cases hv'
  obtain ⟨gv, hgv, hsv⟩ := K.gval hfv
  rw [stepV_of (ctx := Ctx.make tabs g) hgv]
  have hdef : ∀ a ∈ gv.args, ∃ y, T.regs[a]? = some (some y) := fun a ha' => by
    rcases K.tArgsT hjT hgv ha' with hB | hd
    · have hc := K.base_clean hfv (K.gargs hfv hgv ha') hB hbl
      obtain ⟨-, y, -, hy, -⟩ := K.base_val hS hL hB
      exact ⟨y, by rw [K.base_reg hB hLT hT.out, K.agree a hc, ← K.base_reg hB hL hS.out, hy]⟩
    · exact hT.defd a hd
  rcases hsv with hs | he
  · obtain ⟨-, hgop, -⟩ := sameV_spec hs
    obtain ⟨vs, hvs⟩ := CSE.argVals_some (fr := T) (as := gv.args) hdef
    have hp0 : prio gv.op = 0 := by
      simpa [CSE.rootNode, hgv] using hr
    obtain ⟨r, hr'⟩ := CSE.evalOp_total (env := env) (ctx := Ctx.make tabs g) (fr := T)
      (argv := vs) (ty := (Ctx.make tabs g).tys[gv.id]?.getD .other) (v := gv)
      (CSE.Blk.isRoot_of_prio hp0) (by rw [hgop]; exact ha) (by rw [hgop]; exact hb)
    exact ⟨_, by rw [CSE.evalValue_of_argVals hvs, hr']; rfl⟩
  · obtain ⟨-, hgc, -, -, -, -, -, m, -, hgargs⟩ := elimV_spec he
    obtain ⟨y, hy⟩ := hdef m (by rw [hgargs]; simp)
    exact ⟨_, evalValue_copy hgc hgargs hy⟩

theorem tfacts_zero {S : Frame} {pre : List ID} : TFacts P F0T S F0T pre (oT.toList.take 0) :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ h => by simp at h, fun _ h => by simp at h⟩

/-- **The target's loop** over the first `K'` values of its schedule. -/
theorem loop {S : Frame} {pre : List ID} {K' : Nat}
    (hev : ∀ j x, j < K' → oT.toList[j]? = some x → ∀ T,
      TFacts P F0T S T pre (oT.toList.take j) →
      ∃ y, stepV env (Ctx.make tabs g) T x = .ok y ∧
        (x ∈ pre → ∃ yS, S.regs[x]? = some (some yS) ∧ VRel (IvQ (P x)) yS y)) :
    ∃ T', evalAll env (Ctx.make tabs g) F0T (oT.toList.take K') = .ok T' ∧
      TFacts P F0T S T' pre (oT.toList.take K') := by
  have hstep : ∀ d x rest T, oT.toList.take K' = d ++ x :: rest →
      (d = oT.toList.take d.length ∧ TFacts P F0T S T pre d) →
      ∃ y, stepV env (Ctx.make tabs g) T x = .ok y ∧
        (d ++ [x] = oT.toList.take (d ++ [x]).length ∧
          TFacts P F0T S (T.set x y) pre (d ++ [x])) := by
    intro d x rest T hL ⟨hd, hT⟩
    have hjx : (oT.toList.take K')[d.length]? = some x := by rw [hL]; simp
    have hjK : d.length < K' := by
      have := (List.getElem?_eq_some_iff.1 hjx).1; simp at this; omega
    have hj : oT.toList[d.length]? = some x := by
      rwa [List.getElem?_take_of_lt hjK] at hjx
    rw [hd] at hT
    obtain ⟨y, hy, hag⟩ := hev d.length x hjK hj T hT
    refine ⟨y, hy, ?_, ?_⟩
    · rw [List.length_append, List.length_singleton, K.take_succ_eq hj, ← hd]
    · rw [hd, ← K.take_succ_eq hj]
      exact K.tstep hj hT hag
  obtain ⟨T', h1, -, h2⟩ := CSE.evalAll_loop hstep (oT.toList.take K') [] F0T rfl
    ⟨rfl, K.tfacts_zero⟩
  exact ⟨T', h1, h2⟩

theorem sfacts {pre : List ID} {G : Frame} (hpre : ∃ post, oS.toList = pre ++ post)
    (h : evalAll env (Ctx.make tabs f) F0 pre = .ok G) : SFacts env tabs f F0 G pre := by
  obtain ⟨post, hpost⟩ := hpre
  obtain ⟨ond, otopo, -⟩ := schedule_topo K.ownF K.ndF K.hoS
  rw [hpost] at ond otopo
  obtain ⟨e1, e2, e3, e4⟩ := evalAll_spec (List.nodup_append.1 ond).1
    (topoRem_append_left otopo) (by rw [K.size]; rfl) h
  exact ⟨e1, e2, e3, e4⟩

/-- **The ok case.** -/
theorem okCase {G : Frame} (h : evalAll env (Ctx.make tabs f) F0 oS.toList = .ok G) :
    ∃ GT, evalAll env (Ctx.make tabs g) F0T oT.toList = .ok GT ∧
      GT = { G with regs := GT.regs } ∧ GT.regs.size = G.regs.size ∧
      ∀ z, P z = [] → GT.regs[z]? = G.regs[z]? := by
  have hS : SFacts env tabs f F0 G (oS.toList.take oS.toList.length) := by
    rw [List.take_length]; exact K.sfacts ⟨[], by simp⟩ h
  have hall : ∀ x ∈ oT.toList, x ∈ oS.toList.take oS.toList.length := fun x hx => by
    rw [List.take_length]; exact K.memS.2 (K.memT.1 hx)
  obtain ⟨T', h1, hT'⟩ := K.loop (S := G) (pre := oS.toList.take oS.toList.length)
    (K' := oT.toList.length) fun j x hj hjx T hT => by
      obtain ⟨y, hy, hag⟩ := K.sameStep hS hT hjx (hall x (List.mem_of_getElem? hjx))
      exact ⟨y, hy, fun _ => hag⟩
  simp only [List.take_length] at h1 hT' hS hall
  refine ⟨T', h1, K.tframe hS hT', by rw [hT'.size, K.sizeT, hS.size], fun z hz => ?_⟩
  by_cases hzo : z ∈ oT.toList
  · obtain ⟨yS, yT, h1, h2, h3⟩ := hT'.rel z hzo (hall z hzo)
    rw [hz] at h3
    rw [h1, h2, h3.eq_nil]
  · have hzS : z ∉ oS.toList := fun hm => hzo (K.memT.2 (K.memS.1 hm))
    rw [hT'.out z hzo, hS.out z hzS, K.agree z hz]

theorem nodeOf_x {x : ID} {v : Value} (hx : x ∈ fb.values) (hv : f.value? x = some v)
    (hph : v.op ≠ .Phi) : nodeOf (schedNodes f fb).toList x = some ⟨x, v.args, prio v.op⟩ := by
  obtain ⟨v', hv', hid, -⟩ := K.valueIn hx
  rw [hv] at hv'; cases hv'
  have hm : (⟨v.id, v.args, prio v.op⟩ : SNode) ∈ (schedNodes f fb).toList :=
    mem_schedNodes.2 ⟨x, hx, v, hv, hph, rfl⟩
  have := nodeOf_of_mem (schedNodes_ids K.ownF K.ndF) hm
  rw [hid] at this; exact this

/-- **The panic case.** -/
theorem panicCase {e : Panic} {m : Mem}
    (h : evalAll env (Ctx.make tabs f) F0 oS.toList = .panic e m) :
    evalAll env (Ctx.make tabs g) F0T oT.toList = .panic e m := by
  obtain ⟨ce, hwf⟩ := K.wf
  obtain ⟨pre, r, post, Gp, hsplit, hpre, hrp⟩ := evalAll_panic_split h
  have hk : oS.toList[pre.length]? = some r := by rw [hsplit]; simp
  have htk : oS.toList.take pre.length = pre := by rw [hsplit]; simp
  have hS : SFacts env tabs f F0 Gp (oS.toList.take pre.length) := by
    rw [htk]; exact K.sfacts ⟨r :: post, hsplit⟩ hpre
  have hrS : r ∈ oS.toList := List.mem_of_getElem? hk
  obtain ⟨hrb, rv, hrv, hrph⟩ := K.memS.1 hrS
  have hrop : Panicking rv.op := by
    rw [stepV_of (ctx := Ctx.make tabs f) hrv] at hrp; exact evalValue_panic_op hrp
  have hp2 : prio rv.op ≠ 0 := prio_panicking hrop
  have hfroot : CSE.rootNode f r = true := by simp [CSE.rootNode, hrv, hp2]
  have hgroot : CSE.rootNode g r = true := by
    obtain ⟨gv, hgv, hsv⟩ := K.gval hrv
    rcases hsv with hs | he
    · simp [CSE.rootNode, hgv, (sameV_spec hs).2.1, hp2]
    · obtain ⟨h1, -⟩ := elimV_spec he
      rcases h1 with h1 | h1 | h1 <;> rw [h1] at hrop <;> rcases hrop with h2 | h2 <;>
        exact absurd h2 (by decide)
  obtain ⟨k', hk'⟩ := List.getElem?_of_mem (K.memT.2 (K.memS.1 hrS))
  have hroots := CSE.roots_before K.roots K.ndT K.ndS hk' hk hgroot
  obtain ⟨T', h1, hT'⟩ := K.loop (S := Gp) (pre := oS.toList.take pre.length) (K' := k')
    (fun j x hj hjx T hT => by
      have hxn := K.memT.1 (List.mem_of_getElem? hjx)
      obtain ⟨i, hi⟩ := List.getElem?_of_mem (K.memS.2 hxn)
      by_cases hik : i < pre.length
      · have hxS : x ∈ oS.toList.take pre.length :=
          List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hik]; exact hi)
        obtain ⟨y, hy, hag⟩ := K.sameStep hS hT hjx hxS
        exact ⟨y, hy, fun _ => hag⟩
      · -- not reached by the source: pure in the target
        obtain ⟨hxb, fv, hfv, hph⟩ := hxn
        have hxr : x ≠ r := fun he => by
          subst he; exact absurd (Order.idx_unique K.ndT hjx hk') (by omega)
        have hki : pre.length < i := by
          rcases Nat.lt_or_ge pre.length i with h' | h'
          · exact h'
          · have : i = pre.length := by omega
            subst this; rw [hk] at hi; cases hi; exact absurd rfl hxr
        have hnotS : x ∉ oS.toList.take pre.length := fun hm => by
          obtain ⟨i', hi'⟩ := List.getElem?_of_mem hm
          have hi'k : i' < pre.length := by
            have := (List.getElem?_eq_some_iff.1 hi').1; simp at this; omega
          rw [List.getElem?_take_of_lt hi'k] at hi'
          exact absurd (Order.idx_unique K.ndS hi' hi) (by omega)
        have hxroot : CSE.rootNode g x = false := by
          cases hxr' : CSE.rootNode g x with
          | false => rfl
          | true =>
            exact absurd (hroots x (List.mem_of_getElem?
              (by rw [List.getElem?_take_of_lt hj]; exact hjx)) hxr') hnotS
        -- an argument lookup is a root of neither function
        have hnA : ∀ op, fv.op = op → (op = .Arg ∨ op = .ArgIntReg) → False := by
          intro op hop hor
          obtain ⟨gv, hgv, hsv⟩ := K.gval hfv
          rcases hsv with hs | he
          · have hp0 : prio fv.op = 0 := by
              rw [← (sameV_spec hs).2.1]; simpa [CSE.rootNode, hgv] using hxroot
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
          · obtain ⟨h1, -⟩ := elimV_spec he
            rcases hor with h2 | h2 <;> rcases h1 with h1 | h1 | h1 <;> rw [h1, h2] at hop <;>
              cases hop
        obtain ⟨y, hy⟩ := K.pureStep hS hT hjx hxroot hfv (fun h' => hnA _ h' (.inl rfl))
          (fun h' => hnA _ h' (.inr rfl))
        exact ⟨y, hy, fun hm => absurd hm hnotS⟩)
  have hsplitT := CSE.split_at hk'
  rw [hsplitT, evalAll_append, h1]
  show evalAll env (Ctx.make tabs g) T' (r :: oT.toList.drop (k' + 1)) = _
  rw [evalAll_cons, K.panicStep hS hT' hk' hk hrp]

end Blk

end GoFV.Proof.DSE

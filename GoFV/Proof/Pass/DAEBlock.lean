import GoFV.Proof.Pass.DAEBlockBase

/-!
# dead auto elim: one block's evaluation

`okCase`: if the source evaluates the block's schedule to `G`, the target evaluates its schedule
to a frame whose registers are related to `G`'s; `panicCase`: if the source panics, the target
panics alike with a memory equal outside `U` (and the source's panic value and memory avoid
`U`, `src_panic`). Induction along the target's schedule
(`CSE.evalAll_loop`): a value the source evaluated before it stops evaluates to a related
register (`tgt_rel`); a value it did not reach (it panicked first) is pure in the target (the
roots of `g` keep their order, `CSE.roots_before`): an eliminated write's `Copy`, or a pure value
with arguments (`PureFirst`), which evaluates; the panicking value panics alike.
-/

namespace GoFV.Proof.DAE

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Proof.CopyElim GoFV.Opt GoFV.Opt.DAE
open GoFV.Proof.CSE (Base Node SFacts)

variable {env : Env} {tabs : Tables} {f g : Func} {T : ID → Option AuxRef} {E : List AuxRef}
  {bid : ID} {fb gb : Block} {F0 F0T : Frame} {oS oT : Array ID}

namespace BlkSim

variable (K : BlkSim env tabs f g T E bid fb gb F0 F0T oS oT)
include K

theorem tframe {S Tf : Frame} {pre done : List ID} (hS : SFacts env tabs f F0 S pre)
    (hT : TFacts E F0T S Tf pre done) : Tf = { S with regs := Tf.regs } :=
  calc Tf = { F0T with regs := Tf.regs } := hT.frame
    _ = { F0 with regs := Tf.regs } := by rw [K.frT]
    _ = { S with regs := Tf.regs } := by rw [hS.frame]

/-- The source keeps its register property along its schedule. -/
theorem srcPr {pre : List ID} {G : Frame} (hpre : ∀ x ∈ pre, Node f fb x)
    (h : evalAll env (Ctx.make tabs f) F0 pre = .ok G) : RegsP (SPr tabs f T E) G := by
  refine evalAll_regsP (Q := fun x => Node f fb x) (F0 := F0) (fun fr x v y hfr hP hx hv hy => ?_)
    pre F0 G rfl K.pr hpre h
  obtain ⟨v', hv', hid, -⟩ := K.valueIn hx.1
  have hv'' : f.value? x = some v := hv
  rw [hv''] at hv'; cases hv'
  have hfok : FrameOK (UE E) fr := by
    rw [hfr]; exact ⟨K.fok.images, K.fok.closure, K.fok.mem0⟩
  refine ⟨src_step K.fs K.rel hfok (regsP_inv hP) hv'' hid hy, ?_⟩
  have := evalValue_typed hy
  rw [hid] at this
  exact this

/-- A target argument of a value the source evaluated: related registers. -/
theorem argRel {S Tf : Frame} {k j : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hT : TFacts E F0T S Tf (oS.toList.take k) (oT.toList.take j)) {x : ID} {fv gv : Value}
    (hfv : f.value? x = some fv) (hgv : g.value? x = some gv)
    (hjT : oT.toList[j]? = some x) (hxS : ∃ i ≤ k, oS.toList[i]? = some x) {a : ID}
    (ha : a ∈ gv.args) :
    ∃ vS vT, S.regs[a]? = some (some vS) ∧ Tf.regs[a]? = some (some vT) ∧ VR (UE E) vS vT := by
  have hL : ∀ y ∈ oS.toList.take k, Node f fb y := fun y hy => K.memS.1 (List.mem_of_mem_take hy)
  have hLT : ∀ y ∈ oT.toList.take j, Node f fb y := fun y hy => K.memT.1 (List.mem_of_mem_take hy)
  rcases K.tArgsT hjT hgv ha with hB | hd
  · obtain ⟨y, hy0, hyS⟩ := K.base_def hS hL hB
    obtain ⟨y', hy', hv⟩ := K.agree a y hy0
    exact ⟨y, y', hyS, by rw [K.base_reg hB hLT hT.out, hy'], hv⟩
  · refine hT.rel a hd ?_
    obtain ⟨i, hik, hi⟩ := hxS
    have hn : Node f fb a := K.memT.1 (List.mem_of_mem_take hd)
    obtain ⟨i', hi', hia⟩ := K.topoS hi hfv (K.gargs hfv hgv ha) hn
    exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt (show i' < k by omega)]; exact hia)

/-- The relation of one value the source evaluated before it stops. -/
theorem valRel {S Tf : Frame} {k j : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hT : TFacts E F0T S Tf (oS.toList.take k) (oT.toList.take j))
    (hpr : RegsP (SPr tabs f T E) S) {x : ID}
    (hjT : oT.toList[j]? = some x) (hxS : ∃ i ≤ k, oS.toList[i]? = some x) {fv : Value}
    (hfv : f.value? x = some fv) :
    ResRel (UE E) (stepV env (Ctx.make tabs f) S x) (stepV env (Ctx.make tabs g) Tf x) := by
  obtain ⟨hxb, fv', hfv', hph⟩ := K.memS.1 (by
    obtain ⟨i, -, hi⟩ := hxS; exact List.mem_of_getElem? hi)
  rw [hfv] at hfv'; cases hfv'
  obtain ⟨v', hv', hid, -⟩ := K.valueIn hxb
  rw [hfv] at hv'; cases hv'
  obtain ⟨gv, hgv, -⟩ := K.gval hfv
  rw [stepV_of (ctx := Ctx.make tabs f) hfv, stepV_of (ctx := Ctx.make tabs g) hgv]
  exact tgt_rel K.fs K.rel (K.tframe hS hT) (regsP_inv hpr) (regsP_typed hpr) hfv hgv hid hph
    fun a ha => K.argRel hS hT hfv hgv hjT hxS ha

/-- **A value the source evaluated before it stops** evaluates in the target to a related
register. -/
theorem sameStep {S Tf : Frame} {k j : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hT : TFacts E F0T S Tf (oS.toList.take k) (oT.toList.take j))
    (hpr : RegsP (SPr tabs f T E) S) {x : ID}
    (hjT : oT.toList[j]? = some x) (hxS : x ∈ oS.toList.take k) :
    ∃ y, stepV env (Ctx.make tabs g) Tf x = .ok y ∧
      ∃ yS, S.regs[x]? = some (some yS) ∧ VR (UE E) yS y := by
  obtain ⟨fv, yS, hfv, hyS, hev⟩ := hS.eval x hxS
  have hxS' : ∃ i ≤ k, oS.toList[i]? = some x := by
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hxS
    have hik : i < k := by
      have := (List.getElem?_eq_some_iff.1 hi).1; simp at this; omega
    rw [List.getElem?_take_of_lt hik] at hi
    exact ⟨i, by omega, hi⟩
  have hR := K.valRel hS hT hpr hjT hxS' hfv
  rw [stepV_of (ctx := Ctx.make tabs f) hfv, hev] at hR
  obtain ⟨y, hy, hv⟩ := hR.1 yS rfl
  exact ⟨y, hy, yS, hyS, hv⟩

/-- **A value pure in the target** evaluates once its arguments are defined (not an argument
lookup). -/
theorem pureStep {S Tf : Frame} {k j : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hT : TFacts E F0T S Tf (oS.toList.take k) (oT.toList.take j)) {x : ID}
    (hjT : oT.toList[j]? = some x) (hr : CSE.rootNode g x = false) {fv : Value}
    (hfv : f.value? x = some fv) (ha : fv.op ≠ .Arg) (hb : fv.op ≠ .ArgIntReg) :
    ∃ y, stepV env (Ctx.make tabs g) Tf x = .ok y := by
  have hL : ∀ y ∈ oS.toList.take k, Node f fb y := fun y hy => K.memS.1 (List.mem_of_mem_take hy)
  have hLT : ∀ y ∈ oT.toList.take j, Node f fb y := fun y hy => K.memT.1 (List.mem_of_mem_take hy)
  obtain ⟨gv, hgv, hsv⟩ := K.gval hfv
  rw [stepV_of (ctx := Ctx.make tabs g) hgv]
  have hdef : ∀ a ∈ gv.args, ∃ y, Tf.regs[a]? = some (some y) := fun a ha' => by
    rcases K.tArgsT hjT hgv ha' with hB | hd
    · obtain ⟨y, hy0, -⟩ := K.base_def hS hL hB
      obtain ⟨y', hy', -⟩ := K.agree a y hy0
      exact ⟨y', by rw [K.base_reg hB hLT hT.out, hy']⟩
    · exact hT.defd a hd
  rcases hsv with hs | he
  · obtain ⟨-, hgop, -⟩ := DSE.sameV_spec hs
    obtain ⟨vs, hvs⟩ := CSE.argVals_some (fr := Tf) (as := gv.args) hdef
    have hp0 : prio gv.op = 0 := by
      simpa [CSE.rootNode, hgv] using hr
    obtain ⟨r, hr'⟩ := CSE.evalOp_total (env := env) (ctx := Ctx.make tabs g) (fr := Tf)
      (argv := vs) (ty := (Ctx.make tabs g).tys[gv.id]?.getD .other) (v := gv)
      (CSE.Blk.isRoot_of_prio hp0) (by rw [hgop]; exact ha) (by rw [hgop]; exact hb)
    exact ⟨_, by rw [CSE.evalValue_of_argVals hvs, hr']; rfl⟩
  · obtain ⟨-, hgc, -, -, -, -, -, m, -, hgargs⟩ := elimV_spec he
    obtain ⟨y, hy⟩ := hdef m (by rw [hgargs]; simp)
    exact ⟨_, evalValue_copy hgc hgargs hy⟩

theorem tfacts_zero {S : Frame} {pre : List ID} : TFacts E F0T S F0T pre (oT.toList.take 0) :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ h => by simp at h, fun _ h => by simp at h⟩

/-- **The target's loop** over the first `K'` values of its schedule. -/
theorem loop {S : Frame} {pre : List ID} {K' : Nat}
    (hev : ∀ j x, j < K' → oT.toList[j]? = some x → ∀ Tf,
      TFacts E F0T S Tf pre (oT.toList.take j) →
      ∃ y, stepV env (Ctx.make tabs g) Tf x = .ok y ∧
        (x ∈ pre → ∃ yS, S.regs[x]? = some (some yS) ∧ VR (UE E) yS y)) :
    ∃ T', evalAll env (Ctx.make tabs g) F0T (oT.toList.take K') = .ok T' ∧
      TFacts E F0T S T' pre (oT.toList.take K') := by
  have hstep : ∀ d x rest Tf, oT.toList.take K' = d ++ x :: rest →
      (d = oT.toList.take d.length ∧ TFacts E F0T S Tf pre d) →
      ∃ y, stepV env (Ctx.make tabs g) Tf x = .ok y ∧
        (d ++ [x] = oT.toList.take (d ++ [x]).length ∧
          TFacts E F0T S (Tf.set x y) pre (d ++ [x])) := by
    intro d x rest Tf hL ⟨hd, hT⟩
    have hjx : (oT.toList.take K')[d.length]? = some x := by rw [hL]; simp
    have hjK : d.length < K' := by
      have := (List.getElem?_eq_some_iff.1 hjx).1; simp at this; omega
    have hj : oT.toList[d.length]? = some x := by
      rwa [List.getElem?_take_of_lt hjK] at hjx
    rw [hd] at hT
    obtain ⟨y, hy, hag⟩ := hev d.length x hjK hj Tf hT
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
    (by exact topoRem_append_left otopo) (by rw [K.size]; rfl) h
  exact ⟨e1, e2, e3, e4⟩

/-- **The ok case.** -/
theorem okCase {G : Frame} (h : evalAll env (Ctx.make tabs f) F0 oS.toList = .ok G) :
    ∃ GT, evalAll env (Ctx.make tabs g) F0T oT.toList = .ok GT ∧
      GT = { G with regs := GT.regs } ∧ GT.regs.size = G.regs.size ∧
      ∀ (z : ID) (y : Val), G.regs[z]? = some (some y) →
        ∃ y', GT.regs[z]? = some (some y') ∧ VR (UE E) y y' := by
  have hS : SFacts env tabs f F0 G (oS.toList.take oS.toList.length) := by
    rw [List.take_length]; exact K.sfacts ⟨[], by simp⟩ h
  have hpr : RegsP (SPr tabs f T E) G := K.srcPr (fun x hx => K.memS.1 hx) h
  have hall : ∀ x ∈ oT.toList, x ∈ oS.toList.take oS.toList.length := fun x hx => by
    rw [List.take_length]; exact K.memS.2 (K.memT.1 hx)
  obtain ⟨T', h1, hT'⟩ := K.loop (S := G) (pre := oS.toList.take oS.toList.length)
    (K' := oT.toList.length) fun j x hj hjx Tf hT => by
      obtain ⟨y, hy, hag⟩ := K.sameStep hS hT hpr hjx (hall x (List.mem_of_getElem? hjx))
      exact ⟨y, hy, fun _ => hag⟩
  simp only [List.take_length] at h1 hT' hS hall
  refine ⟨T', h1, K.tframe hS hT', by rw [hT'.size, K.sizeT, hS.size], fun z y hz => ?_⟩
  by_cases hzo : z ∈ oT.toList
  · obtain ⟨yS, yT, h1, h2, h3⟩ := hT'.rel z hzo (hall z hzo)
    rw [hz] at h1; cases h1
    exact ⟨yT, h2, h3⟩
  · have hzS : z ∉ oS.toList := fun hm => hzo (K.memT.2 (K.memS.1 hm))
    rw [hS.out z hzS] at hz
    obtain ⟨y', hy', hv⟩ := K.agree z y hz
    exact ⟨y', by rw [hT'.out z hzo, hy'], hv⟩

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
    ∃ m', evalAll env (Ctx.make tabs g) F0T oT.toList = .panic e m' ∧ Mem.EqOff (UE E) m m' ∧
      e.Avoids (UE E) ∧ m.Avoids (UE E) := by
  obtain ⟨ce, hwf⟩ := K.wf
  obtain ⟨pre, r, post, Gp, hsplit, hpre, hrp⟩ := evalAll_panic_split h
  have hk : oS.toList[pre.length]? = some r := by rw [hsplit]; simp
  have htk : oS.toList.take pre.length = pre := by rw [hsplit]; simp
  have hS : SFacts env tabs f F0 Gp (oS.toList.take pre.length) := by
    rw [htk]; exact K.sfacts ⟨r :: post, hsplit⟩ hpre
  have hpr : RegsP (SPr tabs f T E) Gp :=
    K.srcPr (fun x hx => K.memS.1 (by rw [hsplit]; exact List.mem_append_left _ hx)) hpre
  have hrS : r ∈ oS.toList := List.mem_of_getElem? hk
  obtain ⟨hrb, rv, hrv, hrph⟩ := K.memS.1 hrS
  have hrop : Panicking rv.op := by
    rw [stepV_of (ctx := Ctx.make tabs f) hrv] at hrp; exact evalValue_panic_op hrp
  have hp2 : prio rv.op ≠ 0 := prio_panicking hrop
  have hgroot : CSE.rootNode g r = true := by
    obtain ⟨gv, hgv, hsv⟩ := K.gval hrv
    rcases hsv with hs | he
    · simp [CSE.rootNode, hgv, (DSE.sameV_spec hs).2.1, hp2]
    · obtain ⟨h1, -⟩ := elimV_spec he
      rcases h1 with h1 | h1 | h1 | h1 <;> rw [h1] at hrop <;> rcases hrop with h2 | h2 <;>
        exact absurd h2 (by decide)
  obtain ⟨k', hk'⟩ := List.getElem?_of_mem (K.memT.2 (K.memS.1 hrS))
  have hroots := CSE.roots_before K.roots K.ndT K.ndS hk' hk hgroot
  obtain ⟨T', h1, hT'⟩ := K.loop (S := Gp) (pre := oS.toList.take pre.length) (K' := k')
    (fun j x hj hjx Tf hT => by
      have hxn := K.memT.1 (List.mem_of_getElem? hjx)
      obtain ⟨i, hi⟩ := List.getElem?_of_mem (K.memS.2 hxn)
      by_cases hik : i < pre.length
      · have hxS : x ∈ oS.toList.take pre.length :=
          List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hik]; exact hi)
        obtain ⟨y, hy, hag⟩ := K.sameStep hS hT hpr hjx hxS
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
              rw [← (DSE.sameV_spec hs).2.1]; simpa [CSE.rootNode, hgv] using hxroot
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
            rcases hor with h2 | h2 <;> rcases h1 with h1 | h1 | h1 | h1 <;> rw [h1, h2] at hop <;>
              cases hop
        obtain ⟨y, hy⟩ := K.pureStep hS hT hjx hxroot hfv (fun h' => hnA _ h' (.inl rfl))
          (fun h' => hnA _ h' (.inr rfl))
        exact ⟨y, hy, fun hm => absurd hm hnotS⟩)
  have hsplitT := CSE.split_at hk'
  have hR := K.valRel hS hT' hpr hk' ⟨pre.length, Nat.le_refl _, hk⟩ hrv
  obtain ⟨m', hm', hEq⟩ := hR.2 e m hrp
  have hrp' : evalValue env (Ctx.make tabs f) Gp rv = .panic e m := by
    rw [stepV_of (ctx := Ctx.make tabs f) hrv] at hrp; exact hrp
  obtain ⟨heA, hmA⟩ := src_panic K.fs K.rel (regsP_inv hpr) hrv hrp'
  refine ⟨m', ?_, hEq, heA, hmA⟩
  rw [hsplitT, evalAll_append, h1]
  show evalAll env (Ctx.make tabs g) T' (r :: oT.toList.drop (k' + 1)) = _
  rw [evalAll_cons, hm']

end BlkSim

end GoFV.Proof.DAE

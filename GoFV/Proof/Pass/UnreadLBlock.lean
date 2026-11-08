import GoFV.Proof.Pass.UnreadLStep
import GoFV.Proof.AvailL
import GoFV.Proof.SimL
import GoFV.Proof.EvalOpLDispatch

variable [GoFV.SSA.Sem.Addrs]

/-!
# elim unread autos on `runL`: one block's evaluation

`UBlk`: a tree block `bid` entered after its `Phi`s with source frame `F0` (lemma (D) for the
strict ancestors, `DInvL`; the `Phi`s defined; the source's registers avoid `UE E` and are typed,
`SPrL`; the frame's inputs avoid `UE E`) and target frame `F0T`, whose registers are related
(`VR`) to `F0`'s. As dead auto elim's `DAE.BlkSim` for `runL`:

* `okCase`: if the source evaluates the block's schedule to `G`, the target evaluates its schedule
  to a frame whose registers are related to `G`'s (each value with related arguments,
  `tgt_rel`);
* `panicCase`: if the source panics, the target panics alike with a memory equal outside `UE E`.
  A value the source did not reach is pure in the target (the roots of `g` keep their order): an
  eliminated write's `Copy`, or a pure value with arguments, which evaluates (`evalOpL_total`).
-/

namespace GoFV.Proof.UnreadL

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Proof.DAE GoFV.Proof.CopyElim GoFV.Opt
open GoFV.Proof.CSE (Base Node)

/-! ## Totality of pure lowered values -/

/-- **A non-root lowered value evaluates**, unless it is an `Arg`/`ArgIntReg`. -/
theorem evalOpL_total {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val} {ty : Ty}
    (hr : isRoot v.op = false) (ha : v.op ≠ .Arg) (hb : v.op ≠ .ArgIntReg) :
    ∃ r, evalOpL false env ctx fr v argv ty = .ok r := by
  rw [evalOpL_eq]
  split
  · exact CSE.evalOp_total hr ha hb
  · split
    · exact arm64Op_total_of_actOp ‹_› hr
    · simp only [hr, Bool.false_eq_true, ite_false]; exact ⟨_, rfl⟩

theorem prio_panickingL' {op : Op} (h : PanickingL false op) : prio op ≠ 0 := by
  rcases h with h | h | ⟨h, -⟩
  · rw [prio_call h]; decide
  · unfold prio; simp [h]
  · cases h

/-! ## The source's frames -/

/-- The source's frame after evaluating the prefix `pre` of its schedule. -/
structure SFactsL (env : Env) (tabs : Tables) (f : Func) (F0 S : Frame) (pre : List ID) :
    Prop where
  frame : S = { F0 with regs := S.regs }
  size : S.regs.size = F0.regs.size
  out : ∀ z, z ∉ pre → S.regs[z]? = F0.regs[z]?
  eval : ∀ x ∈ pre, ∃ v y, f.value? x = some v ∧ S.regs[x]? = some (some y) ∧
    evalValueL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) S v = .ok y

/-- **The source's evaluation keeps a property of its registers** that each step establishes. -/
theorem evalAllL_regsP {md : LMode} {env : Env} {ctx : Ctx} {P : ID → Val → Prop}
    {Q : ID → Prop} {F0 : Frame}
    (hstep : ∀ (fr : Frame) x v y, fr = { F0 with regs := fr.regs } → RegsP P fr → Q x →
      ctx.f.value? x = some v → evalValueL md env ctx fr v = .ok y → P x y) :
    ∀ (o : List ID) (fr fr' : Frame), fr = { F0 with regs := fr.regs } → RegsP P fr →
      (∀ x ∈ o, Q x) → evalAllL md env ctx fr o = .ok fr' → RegsP P fr'
  | [], fr, fr', _, hP, _, h => by cases h; exact hP
  | x :: o, fr, fr', hfr, hP, hQ, h => by
    rw [evalAllL_cons] at h
    unfold stepVL at h
    cases hv : ctx.f.value? x with
    | none => rw [hv] at h; cases h
    | some v =>
      rw [hv] at h
      simp only at h
      cases he : evalValueL md env ctx fr v with
      | panic e m => rw [he] at h; cases h
      | stuck msg => rw [he] at h; cases h
      | ok y =>
        rw [he] at h
        simp only at h
        refine evalAllL_regsP hstep o _ fr' ?_ (regsP_set hP (hstep fr x v y hfr hP
          (hQ x List.mem_cons_self) hv he)) (fun z hz => hQ z (List.mem_cons_of_mem _ hz)) h
        unfold Frame.set; conv => lhs; rw [hfr]

/-- Iterating steps along a list. -/
theorem evalAllL_loop {md : LMode} {env : Env} {ctx : Ctx} {I : List ID → Frame → Prop}
    {L : List ID}
    (hstep : ∀ d x rest T, L = d ++ x :: rest → I d T →
      ∃ y, stepVL md env ctx T x = .ok y ∧ I (d ++ [x]) (T.set x y)) :
    ∀ rest d T, L = d ++ rest → I d T → ∃ T', evalAllL md env ctx T rest = .ok T' ∧ I L T'
  | [], d, T, hL, hI => ⟨T, rfl, by rw [hL, List.append_nil]; exact hI⟩
  | x :: rest, d, T, hL, hI => by
    obtain ⟨y, hy, hI'⟩ := hstep d x rest T hL hI
    rw [evalAllL_cons, hy]
    exact evalAllL_loop hstep rest (d ++ [x]) (T.set x y) (by rw [hL]; simp) hI'

/-! ## One tree block -/

variable {env : Env} {tabs : Tables} {f g : Func} {E : List AuxRef}
  {bid : ID} {fb gb : Block} {F0 F0T : Frame} {oS oT : Array ID}

/-- One tree block's evaluation in source and target, after the `Phi`s. -/
structure UBlk (env : Env) (tabs : Tables) (f g : Func) (E : List AuxRef)
    (bid : ID) (fb gb : Block) (F0 F0T : Frame) (oS oT : Array ID) : Prop where
  rel : URel tabs f g E
  fs : env.FrameSafe
  wf : ∃ ce, WF ce f
  cf : CertOK f
  tree : Tree f bid
  hfb : f.block? bid = some fb
  hgb : g.block? bid = some gb
  size : F0.regs.size = f.valueTab.size
  dinv : DInvL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) (fun a => Anc (make f) a bid ∧ a ≠ bid) F0
  phiDef : ∀ z ∈ fb.values, ∀ v, f.value? z = some v → v.op = .Phi →
    ∃ y, F0.regs[z]? = some (some y)
  frT : F0T = { F0 with regs := F0T.regs }
  sizeT : F0T.regs.size = F0.regs.size
  agree : ∀ (z : ID) (y : Val), F0.regs[z]? = some (some y) →
    ∃ y', F0T.regs[z]? = some (some y') ∧ VR (UE E) y y'
  pr : RegsP (SPrL tabs f E) F0
  fok : FrameOK (UE E) F0
  hoS : schedule f fb = some oS
  hoT : schedule g gb = some oT
  roots : oT.toList.filter (CSE.rootNode g) = oS.toList.filter (CSE.rootNode g)

namespace UBlk

variable (K : UBlk env tabs f g E bid fb gb F0 F0T oS oT)
include K

theorem hp : parentsOK (make f) f.entry = true := K.cf.parents

theorem gvalues : gb.values = fb.values := by
  obtain ⟨gb', hgb', -, hv, -⟩ := K.rel.block bid K.tree.1 fb K.hfb
  rw [K.hgb] at hgb'; cases hgb'; exact hv

theorem valueIn {x : ID} (hx : x ∈ fb.values) :
    ∃ v, f.value? x = some v ∧ v.id = x ∧ v.block = bid := by
  obtain ⟨ce, hwf⟩ := K.wf
  exact hwf.valueId bid fb ⟨K.tree.1, K.hfb⟩ x hx

theorem placed_node {x : ID} (hx : x ∈ fb.values) {v : Value} (hv : f.value? x = some v) :
    Placed f x v ∧ v.block = bid := by
  obtain ⟨v', hv', -, hb⟩ := K.valueIn hx
  rw [hv] at hv'; cases hv'
  exact ⟨⟨hv, hb ▸ K.tree.1, fb, hb ▸ K.hfb, hx⟩, hb⟩

theorem base_or_node {a : ID} {va : Value} (hpl : Placed f a va) (hanc : Anc (make f) va.block bid) :
    Base f bid a ∨ Node f fb a := by
  by_cases h : va.block = bid ∧ va.op ≠ .Phi
  · obtain ⟨hb, hph⟩ := h
    obtain ⟨hv, -, blk, hblk, hxa⟩ := hpl
    rw [hb, K.hfb] at hblk; cases hblk
    exact .inr ⟨hxa, va, hv, hph⟩
  · refine .inl ⟨va, hpl, hanc, ?_⟩
    by_cases hb : va.block = bid
    · exact .inr (Classical.byContradiction fun hph => h ⟨hb, hph⟩)
    · exact .inl hb

theorem arg_base_or_node {x : ID} (hx : x ∈ fb.values) {v : Value} (hv : f.value? x = some v)
    (hph : v.op ≠ .Phi) {a : ID} (ha : a ∈ v.args) : Base f bid a ∨ Node f fb a := by
  obtain ⟨ce, hwf⟩ := K.wf
  have hu := uses K.cf K.tree.1 K.hfb K.tree.2 hx hv hph ha
  obtain ⟨b', blk', hbin, hab⟩ := hwf.argListed bid fb x v ⟨⟨K.tree.1, K.hfb⟩, hx, hv⟩ a ha
  obtain ⟨va, hpl, -, -⟩ := placed_of_mem hwf hbin.1 hbin.2 hab
  rw [blockOf_placed hpl] at hu
  exact K.base_or_node hpl hu

theorem ownF : ValuesOwn f fb := by
  obtain ⟨ce, hwf⟩ := K.wf; exact valuesOwn hwf K.tree.1 K.hfb

theorem ndF : fb.values.toList.Nodup := by
  obtain ⟨ce, hwf⟩ := K.wf; exact hwf.valuesNodup bid fb ⟨K.tree.1, K.hfb⟩

/-- `g`'s value of a value of `f`, kept or an eliminated write. -/
theorem gval {x : ID} {fv : Value} (hfv : f.value? x = some fv) :
    ∃ gv, g.value? x = some gv ∧ (DSE.sameV fv gv = true ∨ elimV fv gv = true) := by
  obtain ⟨gv, hgv, h⟩ := K.rel.value x fv hfv
  exact ⟨gv, hgv, h.imp (fun h => h.1) (fun h => h.1)⟩

theorem elim_not_phi {fv gv : Value} (he : elimV fv gv = true) : fv.op ≠ .Phi ∧ gv.op ≠ .Phi := by
  obtain ⟨hop, hc, -⟩ := elimV_spec he
  refine ⟨fun h => ?_, by rw [hc]; nofun⟩
  rw [h] at hop; simp [elimOps] at hop

theorem gval_phi {x : ID} {fv gv : Value} (hfv : f.value? x = some fv)
    (hgv : g.value? x = some gv) : gv.op = .Phi ↔ fv.op = .Phi := by
  obtain ⟨gv', hgv', h⟩ := K.gval hfv
  rw [hgv] at hgv'; cases hgv'
  rcases h with h | h
  · rw [(DSE.sameV_spec h).2.1]
  · obtain ⟨h1, h2⟩ := K.elim_not_phi h
    exact ⟨fun h => absurd h h2, fun h => absurd h h1⟩

/-- `g`'s arguments are among `f`'s. -/
theorem gargs {x : ID} {fv gv : Value} (hfv : f.value? x = some fv) (hgv : g.value? x = some gv)
    {a : ID} (ha : a ∈ gv.args) : a ∈ fv.args := by
  obtain ⟨gv', hgv', h⟩ := K.gval hfv
  rw [hgv] at hgv'; cases hgv'
  rcases h with h | h
  · rwa [(DSE.sameV_spec h).2.2.2.2.2.2] at ha
  · obtain ⟨-, -, -, -, -, -, -, m, hm, hga⟩ := elimV_spec h
    rw [hga] at ha
    simp only [List.mem_toArray, List.mem_singleton] at ha
    subst ha
    rw [Array.back?_eq_getElem?] at hm
    exact Array.mem_of_getElem? hm

theorem ownG : ValuesOwn g gb := by
  intro x hx
  rw [K.gvalues] at hx
  obtain ⟨v, hv, hid, -⟩ := K.valueIn hx
  obtain ⟨gv, hgv, h⟩ := K.gval hv
  refine ⟨gv, hgv, ?_⟩
  rcases h with h | h
  · rw [(DSE.sameV_spec h).1, hid]
  · rw [(elimV_spec h).2.2.2.2.1, hid]

theorem ndG : gb.values.toList.Nodup := by rw [K.gvalues]; exact K.ndF

theorem memS {x : ID} : x ∈ oS.toList ↔ Node f fb x := (schedule_topo K.ownF K.ndF K.hoS).2.2 x

theorem memT {x : ID} : x ∈ oT.toList ↔ Node f fb x := by
  rw [(schedule_topo K.ownG K.ndG K.hoT).2.2 x, K.gvalues]
  constructor
  · rintro ⟨hx, gv, hgv, hph⟩
    obtain ⟨v, hv, -⟩ := K.valueIn hx
    exact ⟨hx, v, hv, fun h => hph ((K.gval_phi hv hgv).2 h)⟩
  · rintro ⟨hx, v, hv, hph⟩
    obtain ⟨gv, hgv, -⟩ := K.gval hv
    exact ⟨hx, gv, hgv, fun h => hph ((K.gval_phi hv hgv).1 h)⟩

theorem ndS : oS.toList.Nodup := (schedule_topo K.ownF K.ndF K.hoS).1
theorem ndT : oT.toList.Nodup := (schedule_topo K.ownG K.ndG K.hoT).1

theorem topoS {j : Nat} {x : ID} (hj : oS.toList[j]? = some x) {v : Value}
    (hv : f.value? x = some v) {a : ID} (ha : a ∈ v.args) (hn : Node f fb a) :
    ∃ i < j, oS.toList[i]? = some a := by
  have hs := (schedule_spec K.hoS).topo
  have hx : Node f fb x := K.memS.1 (List.mem_of_getElem? hj)
  obtain ⟨hxb, v', hv', hph⟩ := hx
  rw [hv] at hv'; cases hv'
  refine hs.before j x hj a ?_ ((nodeIn_schedNodes K.ownF).2 hn)
  rw [argsOf_schedNodes K.ownF K.ndF hxb hv hph]; exact Array.mem_toList_iff.2 ha

theorem topoT {j : Nat} {x : ID} (hj : oT.toList[j]? = some x) {v : Value}
    (hv : g.value? x = some v) {a : ID} (ha : a ∈ v.args) (hn : Node f fb a) :
    ∃ i < j, oT.toList[i]? = some a := by
  have hs := (schedule_spec K.hoT).topo
  have hnT := (schedule_topo K.ownG K.ndG K.hoT).2.2
  obtain ⟨hxb, v', hv', hph⟩ := (hnT x).1 (List.mem_of_getElem? hj)
  rw [hv] at hv'; cases hv'
  refine hs.before j x hj a ?_ ((nodeIn_schedNodes K.ownG).2 ((hnT a).1 (K.memT.2 hn)))
  rw [argsOf_schedNodes K.ownG K.ndG hxb hv hph]; exact Array.mem_toList_iff.2 ha

theorem base_not_node {x : ID} (hB : Base f bid x) (hn : Node f fb x) : False := by
  obtain ⟨v, hpl, -, hor⟩ := hB
  obtain ⟨hxb, v', hv', hph⟩ := hn
  rw [hpl.1] at hv'; cases hv'
  obtain ⟨-, hb⟩ := K.placed_node hxb hpl.1
  rcases hor with h | h
  · exact h hb
  · exact hph h

theorem base_reg {x : ID} (hB : Base f bid x) {fr F : Frame} {L : List ID}
    (hL : ∀ y ∈ L, Node f fb y) (hout : ∀ z, z ∉ L → fr.regs[z]? = F.regs[z]?) :
    fr.regs[x]? = F.regs[x]? := hout x fun hm => K.base_not_node hB (hL x hm)

/-- A value from before the block holds its register in every source frame of the block. -/
theorem base_def {S : Frame} {pre : List ID} (hS : SFactsL env tabs f F0 S pre)
    (hL : ∀ y ∈ pre, Node f fb y) {x : ID} (hB : Base f bid x) :
    ∃ y, F0.regs[x]? = some (some y) ∧ S.regs[x]? = some (some y) := by
  have bS0 : S.regs[x]? = F0.regs[x]? := K.base_reg hB hL hS.out
  obtain ⟨v, hpl, hanc, hor⟩ := hB
  by_cases hb : v.block = bid
  · have hph := hor.resolve_left (fun h => h hb)
    obtain ⟨hv, -, blk, hblk, hxb⟩ := hpl
    rw [hb, K.hfb] at hblk; cases hblk
    obtain ⟨y, hy⟩ := K.phiDef x hxb v hv hph
    exact ⟨y, hy, by rw [bS0, hy]⟩
  · obtain ⟨y, hy, -⟩ := K.dinv x v (by rw [makeL_f]; exact hpl) ⟨hanc, hb⟩
    exact ⟨y, hy, by rw [bS0, hy]⟩

theorem lt_valueTab {x : ID} (hx : Node f fb x) : x < F0T.regs.size := by
  obtain ⟨-, v, hv, -⟩ := hx
  rw [K.sizeT, K.size]; exact DSE.lt_of_value? hv

/-- A target argument of the value at position `i` of the target schedule is from before the
block or listed before it. -/
theorem tArgsT {i : Nat} {x : ID} (hi : oT.toList[i]? = some x) {gv : Value}
    (hgv : g.value? x = some gv) {a : ID} (ha : a ∈ gv.args) :
    Base f bid a ∨ a ∈ oT.toList.take i := by
  obtain ⟨hxb, fv, hfv, hph⟩ := K.memT.1 (List.mem_of_getElem? hi)
  rcases K.arg_base_or_node hxb hfv hph (K.gargs hfv hgv ha) with hB | hn
  · exact .inl hB
  · obtain ⟨i', hi', hia⟩ := K.topoT hi hgv ha hn
    exact .inr (List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hi']; exact hia))

theorem notMem_take {j : Nat} {x : ID} (hj : oT.toList[j]? = some x) : x ∉ oT.toList.take j :=
  CSE.not_mem_take_of K.ndT hj

theorem take_succ_eq {j : Nat} {x : ID} (hj : oT.toList[j]? = some x) :
    oT.toList.take (j + 1) = oT.toList.take j ++ [x] := by
  rw [List.take_add_one, hj]; rfl

/-- **One target step** keeps `TFacts`. -/
theorem tstep {S T : Frame} {pre : List ID} {j : Nat} {x : ID} (hj : oT.toList[j]? = some x)
    (hT : TFacts E F0T S T pre (oT.toList.take j)) {y : Val}
    (hag : x ∈ pre → ∃ yS, S.regs[x]? = some (some yS) ∧ VR (UE E) yS y) :
    TFacts E F0T S (T.set x y) pre (oT.toList.take (j + 1)) := by
  have hxn := K.memT.1 (List.mem_of_getElem? hj)
  have hxlt : x < T.regs.size := by rw [hT.size]; exact K.lt_valueTab hxn
  have hnot := K.notMem_take hj
  rw [K.take_succ_eq hj]
  have hkeep : ∀ z, z ≠ x → (T.set x y).regs[z]? = T.regs[z]? := fun z hz =>
    Frame.set_regs_ne (Ne.symm hz)
  refine ⟨?_, by simp [Frame.set, hT.size], fun z hz => ?_, fun z hz => ?_, fun z hz hzp => ?_⟩
  · have hf := hT.frame
    unfold Frame.set
    conv => lhs; rw [hf]
  · have hzx : z ≠ x := fun h => hz (by simp [h])
    rw [hkeep z hzx, hT.out z (fun h => hz (List.mem_append_left _ h))]
  · rcases List.mem_append.1 hz with hz | hz
    · have hzx : z ≠ x := fun h => hnot (h ▸ hz)
      rw [hkeep z hzx]; exact hT.defd z hz
    · simp only [List.mem_singleton] at hz; subst hz
      exact ⟨y, Frame.set_regs_self hxlt⟩
  · rcases List.mem_append.1 hz with hz | hz
    · have hzx : z ≠ x := fun h => hnot (h ▸ hz)
      rw [hkeep z hzx]; exact hT.rel z hz hzp
    · simp only [List.mem_singleton] at hz; subst hz
      obtain ⟨yS, hyS, hv⟩ := hag hzp
      exact ⟨yS, y, hyS, Frame.set_regs_self hxlt, hv⟩

theorem tframe {S Tf : Frame} {pre done : List ID} (hS : SFactsL env tabs f F0 S pre)
    (hT : TFacts E F0T S Tf pre done) : Tf = { S with regs := Tf.regs } :=
  calc Tf = { F0T with regs := Tf.regs } := hT.frame
    _ = { F0 with regs := Tf.regs } := by rw [K.frT]
    _ = { S with regs := Tf.regs } := by rw [hS.frame]

/-- The source keeps its register property along its schedule. -/
theorem srcPr {pre : List ID} {G : Frame} (hpre : ∀ x ∈ pre, Node f fb x)
    (h : evalAllL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) F0 pre = .ok G) :
    RegsP (SPrL tabs f E) G := by
  refine evalAllL_regsP (Q := fun x => Node f fb x) (F0 := F0)
    (fun fr x v y hfr hP hx hv hy => ?_) pre F0 G rfl K.pr hpre h
  rw [makeL_f] at hv
  obtain ⟨v', hv', hid, -⟩ := K.valueIn hx.1
  rw [hv] at hv'; cases hv'
  have hfok : FrameOK (UE E) fr := by
    rw [hfr]; exact ⟨K.fok.images, K.fok.closure, K.fok.mem0⟩
  exact src_av K.fs K.rel hfok hP hv hid hy

/-- A target argument of a value the source evaluated: related registers. -/
theorem argRel {S Tf : Frame} {k j : Nat} (hS : SFactsL env tabs f F0 S (oS.toList.take k))
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
theorem valRel {S Tf : Frame} {k j : Nat} (hS : SFactsL env tabs f F0 S (oS.toList.take k))
    (hT : TFacts E F0T S Tf (oS.toList.take k) (oT.toList.take j))
    (hpr : RegsP (SPrL tabs f E) S) {x : ID}
    (hjT : oT.toList[j]? = some x) (hxS : ∃ i ≤ k, oS.toList[i]? = some x) {fv : Value}
    (hfv : f.value? x = some fv) :
    ResRel (UE E) (stepVL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) S x)
      (stepVL ⟨f.lowered, false⟩ env (Ctx.makeL tabs g) Tf x) := by
  obtain ⟨hxb, fv', hfv', hph⟩ := K.memS.1 (by
    obtain ⟨i, -, hi⟩ := hxS; exact List.mem_of_getElem? hi)
  rw [hfv] at hfv'; cases hfv'
  obtain ⟨v', hv', hid, -⟩ := K.valueIn hxb
  rw [hfv] at hv'; cases hv'
  obtain ⟨gv, hgv, -⟩ := K.gval hfv
  rw [stepVL_of (by rw [makeL_f]; exact hfv), stepVL_of (by rw [makeL_f]; exact hgv)]
  exact tgt_rel K.fs K.rel (K.tframe hS hT) hpr hfv hgv hid hph
    fun a ha => K.argRel hS hT hfv hgv hjT hxS ha

/-- **A value the source evaluated before it stops** evaluates in the target to a related
register. -/
theorem sameStep {S Tf : Frame} {k j : Nat} (hS : SFactsL env tabs f F0 S (oS.toList.take k))
    (hT : TFacts E F0T S Tf (oS.toList.take k) (oT.toList.take j))
    (hpr : RegsP (SPrL tabs f E) S) {x : ID}
    (hjT : oT.toList[j]? = some x) (hxS : x ∈ oS.toList.take k) :
    ∃ y, stepVL ⟨f.lowered, false⟩ env (Ctx.makeL tabs g) Tf x = .ok y ∧
      ∃ yS, S.regs[x]? = some (some yS) ∧ VR (UE E) yS y := by
  obtain ⟨fv, yS, hfv, hyS, hev⟩ := hS.eval x hxS
  have hxS' : ∃ i ≤ k, oS.toList[i]? = some x := by
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hxS
    have hik : i < k := by
      have := (List.getElem?_eq_some_iff.1 hi).1; simp at this; omega
    rw [List.getElem?_take_of_lt hik] at hi
    exact ⟨i, by omega, hi⟩
  have hR := K.valRel hS hT hpr hjT hxS' hfv
  rw [stepVL_of (by rw [makeL_f]; exact hfv), hev] at hR
  obtain ⟨y, hy, hv⟩ := hR.1 yS rfl
  exact ⟨y, hy, yS, hyS, hv⟩

/-- **A value pure in the target** evaluates once its arguments are defined (not an argument
lookup). -/
theorem pureStep {S Tf : Frame} {k j : Nat} (hS : SFactsL env tabs f F0 S (oS.toList.take k))
    (hT : TFacts E F0T S Tf (oS.toList.take k) (oT.toList.take j)) {x : ID}
    (hjT : oT.toList[j]? = some x) (hr : CSE.rootNode g x = false) {fv : Value}
    (hfv : f.value? x = some fv) (ha : fv.op ≠ .Arg) (hb : fv.op ≠ .ArgIntReg) :
    ∃ y, stepVL ⟨f.lowered, false⟩ env (Ctx.makeL tabs g) Tf x = .ok y := by
  have hL : ∀ y ∈ oS.toList.take k, Node f fb y := fun y hy => K.memS.1 (List.mem_of_mem_take hy)
  have hLT : ∀ y ∈ oT.toList.take j, Node f fb y := fun y hy => K.memT.1 (List.mem_of_mem_take hy)
  obtain ⟨gv, hgv, hsv⟩ := K.gval hfv
  rw [stepVL_of (by rw [makeL_f]; exact hgv)]
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
    obtain ⟨r, hr'⟩ := evalOpL_total (env := env) (ctx := Ctx.makeL tabs g) (fr := Tf)
      (argv := vs) (ty := (Ctx.makeL tabs g).tys[gv.id]?.getD .other) (v := gv)
      (CSE.Blk.isRoot_of_prio hp0) (by rw [hgop]; exact ha) (by rw [hgop]; exact hb)
    exact ⟨_, by rw [evalValueL_of_argVals hvs]; simp only; rw [hr']; rfl⟩
  · obtain ⟨-, hgc, -, -, -, -, -, m, -, hgargs⟩ := elimV_spec he
    obtain ⟨y, hy⟩ := hdef m (by rw [hgargs]; simp)
    exact ⟨_, evalValueL_copy hgc hgargs hy⟩

theorem tfacts_zero {S : Frame} {pre : List ID} : TFacts E F0T S F0T pre (oT.toList.take 0) :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ h => by simp at h, fun _ h => by simp at h⟩

/-- **The target's loop** over the first `K'` values of its schedule. -/
theorem loop {S : Frame} {pre : List ID} {K' : Nat}
    (hev : ∀ j x, j < K' → oT.toList[j]? = some x → ∀ Tf,
      TFacts E F0T S Tf pre (oT.toList.take j) →
      ∃ y, stepVL ⟨f.lowered, false⟩ env (Ctx.makeL tabs g) Tf x = .ok y ∧
        (x ∈ pre → ∃ yS, S.regs[x]? = some (some yS) ∧ VR (UE E) yS y)) :
    ∃ T', evalAllL ⟨f.lowered, false⟩ env (Ctx.makeL tabs g) F0T (oT.toList.take K') = .ok T' ∧
      TFacts E F0T S T' pre (oT.toList.take K') := by
  have hstep : ∀ d x rest Tf, oT.toList.take K' = d ++ x :: rest →
      (d = oT.toList.take d.length ∧ TFacts E F0T S Tf pre d) →
      ∃ y, stepVL ⟨f.lowered, false⟩ env (Ctx.makeL tabs g) Tf x = .ok y ∧
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
  obtain ⟨T', h1, -, h2⟩ := evalAllL_loop hstep (oT.toList.take K') [] F0T rfl
    ⟨rfl, K.tfacts_zero⟩
  exact ⟨T', h1, h2⟩

theorem sfacts {pre : List ID} {G : Frame} (hpre : ∃ post, oS.toList = pre ++ post)
    (h : evalAllL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) F0 pre = .ok G) :
    SFactsL env tabs f F0 G pre := by
  obtain ⟨post, hpost⟩ := hpre
  obtain ⟨ond, otopo, -⟩ := schedule_topo K.ownF K.ndF K.hoS
  rw [hpost] at ond otopo
  obtain ⟨e1, e2, e3, e4⟩ := evalAllL_spec (ctx := Ctx.makeL tabs f) (List.nodup_append.1 ond).1
    (by rw [makeL_f]; exact topoRem_append_left otopo) (by rw [K.size, makeL_f]) h
  refine ⟨e1, e2, e3, fun x hx => ?_⟩
  obtain ⟨v, y, hv, hy, hev⟩ := e4 x hx
  rw [makeL_f] at hv
  exact ⟨v, y, hv, hy, hev⟩

/-- **The ok case.** -/
theorem okCase {G : Frame}
    (h : evalAllL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) F0 oS.toList = .ok G) :
    ∃ GT, evalAllL ⟨f.lowered, false⟩ env (Ctx.makeL tabs g) F0T oT.toList = .ok GT ∧
      GT = { G with regs := GT.regs } ∧ GT.regs.size = G.regs.size ∧
      ∀ (z : ID) (y : Val), G.regs[z]? = some (some y) →
        ∃ y', GT.regs[z]? = some (some y') ∧ VR (UE E) y y' := by
  have hS : SFactsL env tabs f F0 G (oS.toList.take oS.toList.length) := by
    rw [List.take_length]; exact K.sfacts ⟨[], by simp⟩ h
  have hpr : RegsP (SPrL tabs f E) G := K.srcPr (fun x hx => K.memS.1 hx) h
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
    (h : evalAllL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) F0 oS.toList = .panic e m) :
    ∃ m', evalAllL ⟨f.lowered, false⟩ env (Ctx.makeL tabs g) F0T oT.toList = .panic e m' ∧
      Mem.EqOff (UE E) m m' ∧ e.Avoids (UE E) ∧ m.Avoids (UE E) := by
  obtain ⟨ce, hwf⟩ := K.wf
  obtain ⟨pre, r, post, Gp, hsplit, hpre, hrp⟩ := evalAllL_panic_split h
  have hk : oS.toList[pre.length]? = some r := by rw [hsplit]; simp
  have htk : oS.toList.take pre.length = pre := by rw [hsplit]; simp
  have hS : SFactsL env tabs f F0 Gp (oS.toList.take pre.length) := by
    rw [htk]; exact K.sfacts ⟨r :: post, hsplit⟩ hpre
  have hpr : RegsP (SPrL tabs f E) Gp :=
    K.srcPr (fun x hx => K.memS.1 (by rw [hsplit]; exact List.mem_append_left _ hx)) hpre
  have hrS : r ∈ oS.toList := List.mem_of_getElem? hk
  obtain ⟨hrb, rv, hrv, hrph⟩ := K.memS.1 hrS
  have hrp' : evalValueL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) Gp rv = .panic e m := by
    rw [stepVL_of (by rw [makeL_f]; exact hrv)] at hrp; exact hrp
  have hrop : PanickingL false rv.op := evalValueL_panic_op hrp'
  have hp2 : prio rv.op ≠ 0 := prio_panickingL' hrop
  have hgroot : CSE.rootNode g r = true := by
    obtain ⟨gv, hgv, hsv⟩ := K.gval hrv
    rcases hsv with hs | he
    · simp [CSE.rootNode, hgv, (DSE.sameV_spec hs).2.1, hp2]
    · exact absurd hrop (elimOps_noPanic (elimV_spec he).1)
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
            rw [hop] at h1
            rcases hor with rfl | rfl <;> simp [elimOps] at h1
        obtain ⟨y, hy⟩ := K.pureStep hS hT hjx hxroot hfv (fun h' => hnA _ h' (.inl rfl))
          (fun h' => hnA _ h' (.inr rfl))
        exact ⟨y, hy, fun hm => absurd hm hnotS⟩)
  have hsplitT := CSE.split_at hk'
  have hR := K.valRel hS hT' hpr hk' ⟨pre.length, Nat.le_refl _, hk⟩ hrv
  obtain ⟨m', hm', hEq⟩ := hR.2 e m hrp
  obtain ⟨heA, hmA⟩ := src_panic K.fs hpr hrp'
  refine ⟨m', ?_, hEq, heA, hmA⟩
  rw [hsplitT, evalAllL_append, h1]
  show evalAllL _ env (Ctx.makeL tabs g) T' (r :: oT.toList.drop (k' + 1)) = _
  rw [evalAllL_cons, hm']

end UBlk

end GoFV.Proof.UnreadL

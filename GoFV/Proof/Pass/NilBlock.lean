import GoFV.Proof.Pass.NilEval

/-!
# nilcheckelim: one block's evaluation

`blockOK`: after a tree block's `Phi`s (one frame `F0` for source and target), the target's
evaluation of its schedule reaches the source's frame, or panics alike. Induction along the
target's schedule (`CSE.evalAll_loop`, the `CSE.TFacts` of cse's proof): each value the source
evaluated before it stops evaluates in the target to the source's register (`sameOk`: an
unchanged value from the same argument registers; a removed nil check to the pointer its
justifying check or the pointer itself holds; a constant `IsNonNil` to `true`); a value the
source did not reach is pure in the target, not an `Arg`, with defined arguments, so it
evaluates (`pureEval`); the root the source panics at is unchanged (justified checks never
panic) and panics alike (roots keep their order, `NRel.sched`).
-/

namespace GoFV.Proof.Nil

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Proof.CopyElim GoFV.Proof.CSE
open GoFV.Opt.NilCheck (root)

/-- One tree block's evaluation (after its `Phi`s) in source and target. -/
def BlockOK (env : Env) (tabs : Tables) (f g : Func) : Prop :=
  ∀ (bid : ID) (fb gb : Block) (F0 : Frame) (oS oT : Array ID),
    Tree f bid → f.block? bid = some fb → g.block? bid = some gb →
    F0.regs.size = f.valueTab.size →
    DInv env (Ctx.make tabs f) (fun a => Anc (make f) a bid ∧ a ≠ bid) F0 →
    (∀ z ∈ fb.values, ∀ v, f.value? z = some v → v.op = .Phi →
      ∃ y, F0.regs[z]? = some (some y)) →
    schedule f fb = some oS → schedule g gb = some oT →
    oT.toList.filter (root g) = oS.toList.filter (root g) →
    (∀ G, evalAll env (Ctx.make tabs f) F0 oS.toList = .ok G →
      evalAll env (Ctx.make tabs g) F0 oT.toList = .ok G) ∧
    (∀ e m, evalAll env (Ctx.make tabs f) F0 oS.toList = .panic e m →
      evalAll env (Ctx.make tabs g) F0 oT.toList = .panic e m)

/-- The hypotheses of `BlockOK`, with the relation and well-formedness. -/
structure Blk (env : Env) (tabs : Tables) (f g : Func) (bid : ID)
    (fb gb : Block) (F0 : Frame) (oS oT : Array ID) : Prop where
  rel : NRel tabs f g
  wf : ∃ ce, WF ce f
  cf : CertOK f
  tree : Tree f bid
  hfb : f.block? bid = some fb
  hgb : g.block? bid = some gb
  size : F0.regs.size = f.valueTab.size
  dinv : DInv env (Ctx.make tabs f) (fun a => Anc (make f) a bid ∧ a ≠ bid) F0
  phiDef : ∀ z ∈ fb.values, ∀ v, f.value? z = some v → v.op = .Phi →
    ∃ y, F0.regs[z]? = some (some y)
  hoS : schedule f fb = some oS
  hoT : schedule g gb = some oT
  roots : oT.toList.filter (root g) = oS.toList.filter (root g)

variable {env : Env} {tabs : Tables} {f g : Func} {bid : ID}
  {fb gb : Block} {F0 : Frame} {oS oT : Array ID}

/-- Phi-ness is kept. -/
theorem vrel_phi {x : ID} {fv gv : Value} (h : VRel tabs f g x fv gv) : gv.op = .Phi ↔ fv.op = .Phi := by
  cases h with
  | same hop => rw [hop]
  | nc h1 h2 => rw [h1, h2]; decide
  | nn h1 h2 => rw [h1, h2]; decide
  | after h1 h2 => rw [h1, h2]; decide

namespace Blk

variable (K : Blk env tabs f g bid fb gb F0 oS oT)
include K

theorem hp : parentsOK (make f) f.entry = true := K.cf.parents

theorem gperm : gb.values.toList.Perm fb.values.toList := by
  obtain ⟨gb', hgb', -, -, hp, -⟩ := K.rel.block bid K.tree.1 fb K.hfb
  rw [K.hgb] at hgb'; cases hgb'; exact hp

theorem gmem {x : ID} : x ∈ gb.values ↔ x ∈ fb.values := by
  rw [← Array.mem_toList_iff, ← Array.mem_toList_iff]; exact K.gperm.mem_iff

theorem fid : fb.id = bid := by
  obtain ⟨ce, hwf⟩ := K.wf
  obtain ⟨b', hb', hid⟩ := hwf.blockId bid K.tree.1
  rw [K.hfb] at hb'; cases hb'; exact hid

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
    (hph : v.op ≠ .Phi) {a : ID} (ha : a ∈ v.args) :
    ∃ va, Placed f a va ∧ Anc (make f) va.block bid ∧ (Base f bid a ∨ Node f fb a) := by
  obtain ⟨ce, hwf⟩ := K.wf
  have hu := uses K.cf K.tree.1 K.hfb K.tree.2 hx hv hph ha
  obtain ⟨b', blk', hbin, hab⟩ := hwf.argListed bid fb x v ⟨⟨K.tree.1, K.hfb⟩, hx, hv⟩ a ha
  obtain ⟨va, hpl, hvb, -⟩ := placed_of_mem hwf hbin.1 hbin.2 hab
  rw [blockOf_placed hpl] at hu
  exact ⟨va, hpl, hu, K.base_or_node hpl hu⟩

theorem ownF : ValuesOwn f fb := by
  obtain ⟨ce, hwf⟩ := K.wf; exact valuesOwn hwf K.tree.1 K.hfb

theorem ndF : fb.values.toList.Nodup := by
  obtain ⟨ce, hwf⟩ := K.wf; exact hwf.valuesNodup bid fb ⟨K.tree.1, K.hfb⟩

theorem ownG : ValuesOwn g gb := by
  intro x hx
  obtain ⟨v, hv, hid, -⟩ := K.valueIn (K.gmem.1 hx)
  obtain ⟨gv, hgv, hgid, -⟩ := K.rel.value x v hv
  exact ⟨gv, hgv, hgid.trans hid⟩

theorem ndG : gb.values.toList.Nodup := K.gperm.nodup_iff.2 K.ndF

theorem memS {x : ID} : x ∈ oS.toList ↔ Node f fb x := (schedule_topo K.ownF K.ndF K.hoS).2.2 x

theorem memT {x : ID} : x ∈ oT.toList ↔ Node f fb x := by
  rw [(schedule_topo K.ownG K.ndG K.hoT).2.2 x, K.gmem]
  constructor
  · rintro ⟨hx, gv, hgv, hph⟩
    obtain ⟨v, hv, -⟩ := K.valueIn hx
    obtain ⟨gv', hgv', -, -, -, hrel⟩ := K.rel.value x v hv
    rw [hgv] at hgv'; cases hgv'
    exact ⟨hx, v, hv, fun h => hph ((vrel_phi hrel).2 h)⟩
  · rintro ⟨hx, v, hv, hph⟩
    obtain ⟨gv, hgv, -, -, -, hrel⟩ := K.rel.value x v hv
    exact ⟨hx, gv, hgv, fun h => hph ((vrel_phi hrel).1 h)⟩

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

/-- A strict dominator's listed value is from before the block. -/
theorem base_of_dom {nc : ID} {n : Value} {nb : Block} (hn : f.value? nc = some n)
    (hne : n.block ≠ bid) (hanc : (make f).anc n.block bid = true) (hb : n.block ∈ f.blocks)
    (hnb : f.block? n.block = some nb) (hm : nc ∈ nb.values) : Base f bid nc :=
  ⟨n, ⟨hn, hb, nb, hnb, hm⟩, (anc_iff K.hp).1 hanc, .inl hne⟩

/-- The justifying check of the same block, listed before `x` in the source schedule. -/
theorem same_before {x nc : ID} {fb' : Block} {o : Array ID}
    (hfb' : f.block? bid = some fb') (ho : schedule f fb' = some o)
    (hl : Opt.NilCheck.listedBefore o nc x = true) :
    ∃ i j : Nat, i < j ∧ oS.toList[i]? = some nc ∧ oS.toList[j]? = some x := by
  rw [K.hfb] at hfb'; cases hfb'
  rw [K.hoS] at ho; cases ho
  unfold Opt.NilCheck.listedBefore at hl
  cases hi : oS.findIdx? (· == nc) with
  | none => rw [hi] at hl; cases hl
  | some i =>
  cases hj : oS.findIdx? (· == x) with
  | none => rw [hi, hj] at hl; cases hl
  | some j =>
  rw [hi, hj] at hl
  simp only [decide_eq_true_eq] at hl
  refine ⟨i, j, hl, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := Array.findIdx?_eq_some_iff_getElem.1 hi
    rw [Array.getElem?_toList, Array.getElem?_eq_getElem h1]; simpa using h2.1
  · obtain ⟨h1, h2⟩ := Array.findIdx?_eq_some_iff_getElem.1 hj
    rw [Array.getElem?_toList, Array.getElem?_eq_getElem h1]; simpa using h2.1

/-- A target argument of a node: from before the block or a node. -/
theorem tgtArg {x : ID} (hx : Node f fb x) {gv : Value} (hgv : g.value? x = some gv) {a : ID}
    (ha : a ∈ gv.args) : Base f bid a ∨ Node f fb a := by
  obtain ⟨hxb, v, hv, hph⟩ := hx
  obtain ⟨gv', hgv', -, hbl, -, hrel⟩ := K.rel.value x v hv
  rw [hgv] at hgv'; cases hgv'
  have hvb := (K.placed_node hxb hv).2
  cases hrel with
  | same hop hargs =>
    rw [hargs] at ha
    obtain ⟨-, -, -, h⟩ := K.arg_base_or_node hxb hv hph ha
    exact h
  | @nc p nc hop hcp hp hs1 hn hj =>
    have hanc : a = nc := by
      obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 ha
      have : k < 1 := hs1 ▸ (Array.getElem?_eq_some_iff.1 hk).1
      have hk0 : k = 0 := by omega
      subst hk0; rw [hn] at hk; exact (Option.some.inj hk).symm
    subst hanc
    rw [hvb] at hj
    cases hj with
    | seed he _ =>
      subst he
      obtain ⟨-, -, -, h⟩ := K.arg_base_or_node hxb hv hph (Array.mem_of_getElem? hp)
      exact h
    | dom hne hn' _ _ _ hnb hanc' hb hnb' hm =>
      exact .inl (K.base_of_dom hn' hnb hanc' hb hnb' hm)
    | same hne hn' hop' _ _ hnb hfb' hm _ _ =>
      rw [K.hfb] at hfb'; cases hfb'
      exact .inr ⟨hm, _, hn', by rw [hop']; decide⟩
  | nn hop hcb hai hs0 =>
    rw [Array.eq_empty_of_size_eq_zero hs0] at ha; simp at ha
  | @after nc hop hcp hs1 hn hA =>
    have hanc : a = nc := by
      obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 ha
      have : k < 1 := hs1 ▸ (Array.getElem?_eq_some_iff.1 hk).1
      have hk0 : k = 0 := by omega
      subst hk0; rw [hn] at hk; exact (Option.some.inj hk).symm
    subst hanc
    obtain ⟨hn', -, hop', -, -, hbl', -, -, -, hfb', hm, -⟩ := hA
    rw [hvb, K.hfb] at hfb'; cases hfb'
    exact .inr ⟨hm, _, hn', by rw [hop']; decide⟩

theorem base_not_node {x : ID} (hB : Base f bid x) (hn : Node f fb x) : False := by
  obtain ⟨v, hpl, -, hor⟩ := hB
  obtain ⟨hxb, v', hv', hph⟩ := hn
  rw [hpl.1] at hv'; cases hv'
  obtain ⟨-, hb⟩ := K.placed_node hxb hpl.1
  rcases hor with h | h
  · exact h hb
  · exact hph h

/-- Arguments of a non-`Phi` value from before the block are from before it. -/
theorem base_closed {x : ID} {v : Value} (hB : Base f bid x) (hv : f.value? x = some v)
    (hph : v.op ≠ .Phi) {a : ID} (ha : a ∈ v.args) : Base f bid a := by
  obtain ⟨ce, hwf⟩ := K.wf
  have hp := K.hp
  obtain ⟨v', hpl, hanc, hor⟩ := hB
  rw [hpl.1] at hv; cases hv
  have hne : v.block ≠ bid := hor.resolve_right hph
  obtain ⟨hv, hvb, blk, hblk, hxb⟩ := hpl
  have hu := uses K.cf hvb hblk (Anc.left hp hanc) hxb hv hph ha
  obtain ⟨b', blk', hbin, hab⟩ := hwf.argListed v.block blk x v ⟨⟨hvb, hblk⟩, hxb, hv⟩ a ha
  obtain ⟨va, hpla, -, -⟩ := placed_of_mem hwf hbin.1 hbin.2 hab
  rw [blockOf_placed hpla] at hu
  refine ⟨va, hpla, Anc.trans hp hu hanc, .inl fun he => hne ?_⟩
  rw [he] at hu; exact Anc.antisymm hp hanc hu

/-- A value from before the block, in a frame of the block: `F0`'s register, and a non-`Phi`
one re-evaluates to it (lemma (D)). -/
theorem base_eval {S : Frame} {L : List ID} (hL : ∀ y ∈ L, Node f fb y)
    (hout : ∀ z, z ∉ L → S.regs[z]? = F0.regs[z]?) (hfr : S = { F0 with regs := S.regs })
    {x : ID} {v : Value} (hB : Base f bid x) (hv : f.value? x = some v) :
    ∃ y, S.regs[x]? = some (some y) ∧
      (v.op ≠ .Phi → evalValue env (Ctx.make tabs f) S v = .ok y) := by
  have b0 : ∀ z, Base f bid z → S.regs[z]? = F0.regs[z]? :=
    fun z hz => hout z fun hm => K.base_not_node hz (hL z hm)
  obtain ⟨v', hpl, hanc, hor⟩ := hB
  rw [hpl.1] at hv; cases hv
  by_cases hb : v.block = bid
  · have hph := hor.resolve_left (fun h => h hb)
    obtain ⟨hv, -, blk, hblk, hxb⟩ := hpl
    rw [hb, K.hfb] at hblk; cases hblk
    obtain ⟨y, hy⟩ := K.phiDef x hxb v hv hph
    exact ⟨y, by rw [b0 x ⟨v, ⟨hv, hb ▸ K.tree.1, fb, hb ▸ K.hfb, hxb⟩, hanc, hor⟩, hy],
      fun h => absurd hph h⟩
  · obtain ⟨y, hy, hev⟩ := K.dinv x v hpl ⟨hanc, hb⟩
    refine ⟨y, by rw [b0 x ⟨v, hpl, hanc, hor⟩, hy], fun hph => ?_⟩
    rw [← hev hph]
    refine (evalValue_congr hfr fun a ha => ?_).symm
    exact (b0 a (K.base_closed ⟨v, hpl, hanc, hor⟩ hpl.1 hph ha)).symm

/-- Source facts for a value available at the source's prefix `take k`. -/
theorem availS {S : Frame} {k : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k))
    {x : ID} {v : Value} (hx : Base f bid x ∨ x ∈ oS.toList.take k) (hv : f.value? x = some v)
    (hph : v.op ≠ .Phi) :
    ∃ y, S.regs[x]? = some (some y) ∧ evalValue env (Ctx.make tabs f) S v = .ok y := by
  rcases hx with hB | hx
  · obtain ⟨y, hy, hev⟩ := K.base_eval (L := oS.toList.take k)
      (fun y hy => K.memS.1 (List.mem_of_mem_take hy)) hS.out hS.frame hB hv
    exact ⟨y, hy, hev hph⟩
  · obtain ⟨v', y, hv', hy, hev⟩ := hS.eval x hx
    rw [hv] at hv'; cases hv'
    exact ⟨y, hy, hev⟩

/-- Source and target frames agree on what both have: values from before the block, and the
values both evaluated. -/
theorem agreeT {S T : Frame} {k j : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hT : TFacts env tabs g F0 S T (oS.toList.take k) (oT.toList.take j)) {a : ID}
    (h1 : Base f bid a ∨ a ∈ oS.toList.take k) (h2 : Base f bid a ∨ a ∈ oT.toList.take j) :
    T.regs[a]? = S.regs[a]? := by
  by_cases hB : Base f bid a
  · rw [hT.out a fun hm => K.base_not_node hB (K.memT.1 (List.mem_of_mem_take hm)),
      hS.out a fun hm => K.base_not_node hB (K.memS.1 (List.mem_of_mem_take hm))]
  · exact hT.agree a (h2.resolve_left hB) (h1.resolve_left hB)

/-- A source argument of the value at position `i` of the source schedule: from before the
block or listed before it. -/
theorem srcArg {i : Nat} {x : ID} (hi : oS.toList[i]? = some x) {v : Value}
    (hv : f.value? x = some v) {a : ID} (ha : a ∈ v.args) :
    Base f bid a ∨ a ∈ oS.toList.take i := by
  obtain ⟨hxb, v', hv', hph⟩ := K.memS.1 (List.mem_of_getElem? hi)
  rw [hv] at hv'; cases hv'
  obtain ⟨-, -, -, hor⟩ := K.arg_base_or_node hxb hv hph ha
  rcases hor with hB | hn
  · exact .inl hB
  · obtain ⟨i', hi', hia⟩ := K.topoS hi hv ha hn
    exact .inr (List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hi']; exact hia))

/-- A target argument of the value at position `i` of the target schedule: from before the
block or listed before it. -/
theorem tArgsT {i : Nat} {x : ID} (hi : oT.toList[i]? = some x) {gv : Value}
    (hgv : g.value? x = some gv) {a : ID} (ha : a ∈ gv.args) :
    Base f bid a ∨ a ∈ oT.toList.take i := by
  rcases K.tgtArg (K.memT.1 (List.mem_of_getElem? hi)) hgv ha with hB | hn
  · exact .inl hB
  · obtain ⟨i', hi', hia⟩ := K.topoT hi hgv ha hn
    exact .inr (List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hi']; exact hia))

theorem take_mono {i k : Nat} (h : i ≤ k) {a : ID} (ha : a ∈ oS.toList.take i) :
    a ∈ oS.toList.take k := List.take_subset_take_left _ h ha

/-- An available value is listed in a block, with its ID. -/
theorem listed_avail {k : Nat} {z : ID} (hz : Base f bid z ∨ z ∈ oS.toList.take k) {v : Value}
    (hv : f.value? z = some v) :
    ∃ b blk, BlockIn f b blk ∧ z ∈ blk.values ∧ v.id = z := by
  obtain ⟨ce, hwf⟩ := K.wf
  obtain ⟨b, blk, hbin, hxb⟩ : ∃ b blk, BlockIn f b blk ∧ z ∈ blk.values := by
    rcases hz with hB | hx
    · obtain ⟨v', ⟨-, hb, blk, hblk, hxb⟩, -⟩ := hB
      exact ⟨_, blk, ⟨hb, hblk⟩, hxb⟩
    · exact ⟨bid, fb, ⟨K.tree.1, K.hfb⟩, (K.memS.1 (List.mem_of_mem_take hx)).1⟩
  obtain ⟨v', hv', hid, -⟩ := hwf.valueId b blk hbin z hxb
  rw [hv] at hv'; cases hv'
  exact ⟨b, blk, hbin, hxb, hid⟩

/-- **An available nil check passed** on its pointer, and holds it. -/
theorem nc_eval {S : Frame} {k : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k))
    {p nc : ID} {n : Value} (hn : f.value? nc = some n) (hop : n.op = .NilCheck)
    (ha0 : n.args[0]? = some p) (havail : Base f bid nc ∨ nc ∈ oS.toList.take k) :
    ∃ yp w, S.regs[p]? = some (some yp) ∧ NN yp ∧ S.regs[nc]? = some (some w) ∧
      w = yp.retype (tabs.ty n.type) := by
  obtain ⟨ce, hwf⟩ := K.wf
  have hph : n.op ≠ .Phi := by rw [hop]; decide
  obtain ⟨w, hw, hev⟩ := K.availS hS havail hn hph
  obtain ⟨b, blk, hbin, hxb, hid⟩ := K.listed_avail havail hn
  have hsz : n.args.size = 2 := by
    have := hwf.arity b blk nc n ⟨hbin, hxb, hn⟩ (by rw [hop]; decide)
    rw [hop, show Op.NilCheck.argLen = 2 by decide] at this
    exact_mod_cast this
  obtain ⟨vs, hvs⟩ := argVals_of_eval (env := env) (ctx := Ctx.make tabs f) (fr := S) (v := n)
    (by rw [hev]; nofun)
  obtain ⟨p', m', yp, ym, hargs, rfl, hyp, -⟩ := argVals_two hvs hsz
  rw [hargs] at ha0
  simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at ha0
  subst ha0
  rw [evalValue_of_argVals hvs, evalOp_nilCheck hop] at hev
  obtain ⟨r, hr, hwr⟩ := bind_ok hev
  obtain ⟨a, hra, hnn⟩ := nilCheck_ok hop hr
  simp only [List.cons.injEq] at hra
  obtain ⟨rfl, -⟩ := hra
  refine ⟨_, w, hyp, hnn, hw, ?_⟩
  rw [hwr, hid, tys_of_value hn]; rfl

/-- **A justifying nil check passed** on the pointer of the value at position `i ≤ k`. -/
theorem just_nn {S : Frame} {k i : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hik : i ≤ k) {x : ID} (hi : oS.toList[i]? = some x) {p nc : ID} {ty : TypeRef} {s : Bool}
    (hj : Just tabs f bid x p nc ty s) (hne : nc ≠ p) :
    ∃ yp w, S.regs[p]? = some (some yp) ∧ NN yp ∧ S.regs[nc]? = some (some w) ∧
      w = yp.retype (tabs.ty ty) ∧ (Base f bid nc ∨ nc ∈ oS.toList.take k) := by
  obtain ⟨n, hn, hop, ha0, hty, havail⟩ : ∃ n, f.value? nc = some n ∧ n.op = .NilCheck ∧
      n.args[0]? = some p ∧ n.type = ty ∧ (Base f bid nc ∨ nc ∈ oS.toList.take k) := by
    cases hj with
    | seed he => exact absurd he hne
    | dom _ hn hop ha hty _ hanc hb hnb hm =>
      exact ⟨_, hn, hop, ha, hty, .inl (K.base_of_dom hn (by assumption) hanc hb hnb hm)⟩
    | same _ hn hop ha hty _ hfb' _ ho hl =>
      obtain ⟨i', j', hij, hi', hj'⟩ := K.same_before hfb' ho hl
      have := Order.idx_unique K.ndS hj' hi
      subst this
      exact ⟨_, hn, hop, ha, hty, .inr (K.take_mono hik
        (List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hij]; exact hi')))⟩
  obtain ⟨yp, w, hyp, hnn, hw, hwe⟩ := K.nc_eval hS hn hop ha0 havail
  exact ⟨yp, w, hyp, hnn, hw, by rw [hwe, hty], havail⟩

omit K in
theorem argVals_congr {S T : Frame} {as : Array ID} (h : ∀ a ∈ as, T.regs[a]? = S.regs[a]?) :
    argVals T as = argVals S as := by
  unfold argVals
  exact mapM_congr' _ fun a ha => by rw [h a (Array.mem_toList_iff.1 ha)]

omit K in
theorem frame_TS {S T : Frame} {k j : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hT : TFacts env tabs g F0 S T (oS.toList.take k) (oT.toList.take j)) :
    T = { S with regs := T.regs } := by
  calc T = { F0 with regs := T.regs } := hT.frame
    _ = { S with regs := T.regs } := by rw [hS.frame]

theorem ctx_params : (Ctx.make tabs g).params = (Ctx.make tabs f).params := by
  simp only [Ctx.make, abiParams, K.rel.ownAux]

theorem idOf {x : ID} (hx : x ∈ fb.values) {v : Value} (hv : f.value? x = some v) : v.id = x := by
  obtain ⟨v', hv', hid, -⟩ := K.valueIn hx
  rw [hv] at hv'; cases hv'; exact hid

omit K in
theorem frameVal_none {ctx : Ctx} {v : Value}
    (h : v.op ≠ .SP ∧ v.op ≠ .GetCallerSP ∧ v.op ≠ .LocalAddr ∧ v.op ≠ .Addr ∧
      v.op ≠ .ConstString) :
    frameVal ctx v = none := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  unfold frameVal; split <;> simp_all

omit K in
theorem evalOp_pure {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val} {ty : Ty}
    (hop : v.op = .IsNonNil ∨ v.op = .ConstBool) :
    evalOp env ctx fr v argv ty = .ok (evalPure v.op ty v.auxInt v.aux argv) := by
  have hr : isRoot v.op = false := by rcases hop with h | h <;> rw [h] <;> decide
  have hfv : frameVal ctx v = none :=
    frameVal_none (by rcases hop with h | h <;> rw [h] <;> decide)
  rw [evalOp_tail hr (by rcases hop with h | h <;> rw [h] <;> decide)
    (by rcases hop with h | h <;> rw [h] <;> decide) (by rcases hop with h | h <;> rw [h] <;> decide)
    (by rcases hop with h | h <;> rw [h] <;> decide), hfv]
  rfl

omit K in
theorem isNonNil_nn {q : Val} (h : NN q) : PtrOps.isNonNil [q] = .bool true := by
  match q, h with
  | .ptr p, h => simp only [NN] at h; simp [PtrOps.isNonNil, Ptr.isNil, h]
  | .int .w64 x, h =>
    simp only [NN] at h
    have hx : x ≠ 0 := by rintro rfl; exact h ofAddr_zero
    simpa [PtrOps.isNonNil] using hx

/-- **A value the source evaluated before it stops** evaluates in the target to the source's
register. -/
theorem sameOk {S T : Frame} {k j : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hT : TFacts env tabs g F0 S T (oS.toList.take k) (oT.toList.take j))
    (hroots : ∀ x ∈ oT.toList.take j, root g x = true → x ∈ oS.toList.take k)
    {x : ID} (hjT : oT.toList[j]? = some x) {i : Nat} (hiS : oS.toList[i]? = some x)
    (hik : i < k) :
    ∃ y, stepV env (Ctx.make tabs g) T x = .ok y ∧ S.regs[x]? = some (some y) := by
  obtain ⟨ce, hwf⟩ := K.wf
  have hxk : x ∈ oS.toList.take k :=
    List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hik]; exact hiS)
  obtain ⟨fv, y, hfv, hy, hev⟩ := hS.eval x hxk
  obtain ⟨hxb, fv', hfv', hph⟩ := K.memS.1 (List.mem_of_getElem? hiS)
  rw [hfv] at hfv'; cases hfv'
  obtain ⟨gv, hgv, hid, hbl, hty, hrel⟩ := K.rel.value x fv hfv
  have hxid := K.idOf hxb hfv
  have hvb := (K.placed_node hxb hfv).2
  refine ⟨y, ?_, hy⟩
  rw [stepV_of (ctx := Ctx.make tabs g) hgv]
  have hsrc : ∀ a ∈ fv.args, Base f bid a ∨ a ∈ oS.toList.take k := fun a ha =>
    (K.srcArg hiS hfv ha).imp id (K.take_mono (Nat.le_of_lt hik))
  have htys : (Ctx.make tabs g).tys[x]? = (Ctx.make tabs f).tys[x]? := by
    rw [tys_of_value hgv, tys_of_value hfv, hty]
  cases hrel with
  | same hop hargs hax hai =>
    obtain ⟨vs, hvs⟩ := argVals_of_eval (env := env) (ctx := Ctx.make tabs f) (fr := S) (v := fv)
      (by rw [hev]; nofun)
    have hT' : argVals T gv.args = some vs := by
      rw [argVals_congr fun a ha => K.agreeT hS hT (hsrc a (hargs ▸ ha)) (K.tArgsT hjT hgv ha),
        hargs, hvs]
    rw [evalValue_rel (ctxF := Ctx.make tabs f) (ctxG := Ctx.make tabs g) hop hax hai hid
      (by rw [hid, hxid, htys]) rfl K.ctx_params rfl
      (frame_TS hS hT) hvs (.inl hT'), hev]
  | @nc p nc hop hcp hp hs1 hn hj =>
    have hga : gv.args = #[nc] := by
      apply Array.ext (by simp [hs1]); intro k h1 h2
      have : k = 0 := by simp at h2; omega
      subst this; simpa [Array.getElem?_eq_getElem h1] using hn
    -- the source's nil check passed on `S[p]`
    have hsz : fv.args.size = 2 := by
      have := hwf.arity bid fb x fv ⟨⟨K.tree.1, K.hfb⟩, hxb, hfv⟩ (by rw [hop]; decide)
      rw [hop, show Op.NilCheck.argLen = 2 by decide] at this
      exact_mod_cast this
    obtain ⟨vs, hvs⟩ := argVals_of_eval (env := env) (ctx := Ctx.make tabs f) (fr := S) (v := fv)
      (by rw [hev]; nofun)
    obtain ⟨p', m', yp, ym, hargs, rfl, hyp, -⟩ := argVals_two hvs hsz
    rw [hargs] at hp
    simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at hp
    subst hp
    have hev' := hev
    rw [evalValue_of_argVals hvs, evalOp_nilCheck hop] at hev'
    obtain ⟨r, hr, hyr⟩ := bind_ok hev'
    obtain ⟨a, hra, -⟩ := nilCheck_ok hop hr
    simp only [List.cons.injEq] at hra
    obtain ⟨rfl, -⟩ := hra
    rw [hvb] at hj
    have hpS : Base f bid p' ∨ p' ∈ oS.toList.take k := hsrc p' (by rw [hargs]; simp)
    by_cases hne : nc = p'
    · subst hne
      have hTn : T.regs[nc]? = some (some yp) := by
        rw [K.agreeT hS hT hpS (K.tArgsT hjT hgv (by rw [hga]; simp)), hyp]
      rw [evalValue_copy hcp hga hTn, hyr, hid, hxid, htys]
    · obtain ⟨yp, w, hyp', -, hw, hwe, hav⟩ := K.just_nn hS (Nat.le_of_lt hik) hiS hj hne
      rw [hyp] at hyp'; cases hyp'
      have hTn : T.regs[nc]? = some (some w) := by
        rw [K.agreeT hS hT hav (K.tArgsT hjT hgv (by rw [hga]; simp)), hw]
      rw [evalValue_copy hcp hga hTn, hyr, hid, hxid, htys, hwe, tys_of_value hfv]
      simp only [Option.getD_some]
      exact congrArg _ (retype_idem _ _)
  | @after nc hop hcp hs1 hn hA =>
    obtain ⟨hn', hne', hop', hargs', hty', -, hgn, hgop, -, hfb', hm, -⟩ := hA
    rw [hvb, K.hfb] at hfb'; cases hfb'
    have hga : gv.args = #[nc] := by
      apply Array.ext (by simp [hs1]); intro k h1 h2
      have : k = 0 := by simp at h2; omega
      subst this; simpa [Array.getElem?_eq_getElem h1] using hn
    -- the copied check comes before `x` in the target, so the source reached it
    have hncT : nc ∈ oT.toList.take j := by
      rcases K.tArgsT (a := nc) hjT hgv (by rw [hga]; simp) with hB | hm'
      · exact absurd (⟨hm, _, hn', by rw [hop']; decide⟩ : Node f fb nc) (K.base_not_node hB)
      · exact hm'
    have hncS : nc ∈ oS.toList.take k :=
      hroots nc hncT (by
        simp only [Opt.NilCheck.root, hgn, hgop, Option.map_some, Option.getD_some]; decide)
    have hsz : fv.args.size = 2 := by
      have := hwf.arity bid fb x fv ⟨⟨K.tree.1, K.hfb⟩, hxb, hfv⟩ (by rw [hop]; decide)
      rw [hop, show Op.NilCheck.argLen = 2 by decide] at this
      exact_mod_cast this
    obtain ⟨vs, hvs⟩ := argVals_of_eval (env := env) (ctx := Ctx.make tabs f) (fr := S) (v := fv)
      (by rw [hev]; nofun)
    obtain ⟨p', m', yp, ym, hargs, rfl, hyp, -⟩ := argVals_two hvs hsz
    have hev' := hev
    rw [evalValue_of_argVals hvs, evalOp_nilCheck hop] at hev'
    obtain ⟨r, hr, hyr⟩ := bind_ok hev'
    obtain ⟨a, hra, -⟩ := nilCheck_ok hop hr
    simp only [List.cons.injEq] at hra
    obtain ⟨rfl, -⟩ := hra
    obtain ⟨yp', w, hyp', -, hw, hwe⟩ := K.nc_eval (p := p') hS hn' hop'
      (by rw [hargs', hargs]; simp) (.inr hncS)
    rw [hyp] at hyp'; cases hyp'
    have hTn : T.regs[nc]? = some (some w) := by
      rw [K.agreeT hS hT (.inr hncS) (.inr hncT), hw]
    rw [evalValue_copy hcp hga hTn, hyr, hid, hxid, htys, hwe, hty', tys_of_value hfv]
    simp only [Option.getD_some]
    exact congrArg _ (retype_idem _ _)
  | @nn p nc hop hcb hai hs0 hs1 hp hne hj =>
    rw [hvb] at hj
    obtain ⟨yp, -, hyp, hnn, -⟩ := K.just_nn hS (Nat.le_of_lt hik) hiS hj hne
    obtain ⟨vs, hvs⟩ := argVals_of_eval (env := env) (ctx := Ctx.make tabs f) (fr := S) (v := fv)
      (by rw [hev]; nofun)
    have hfa : fv.args = #[p] := by
      apply Array.ext (by simp [hs1]); intro k h1 h2
      have : k = 0 := by simp at h2; omega
      subst this; simpa [Array.getElem?_eq_getElem h1] using hp
    have hvs' : vs = [yp] := by
      rw [hfa] at hvs; unfold argVals at hvs
      simp [hyp] at hvs; exact hvs.symm
    subst hvs'
    rw [evalValue_of_argVals hvs, evalOp_pure (.inl hop), hop] at hev
    obtain ⟨r, hr, hyr⟩ := bind_ok hev
    cases hr
    have hT0 : argVals T gv.args = some [] := by
      rw [Array.eq_empty_of_size_eq_zero hs0]; rfl
    rw [evalValue_of_argVals hT0, evalOp_pure (.inr hcb), hcb, hai, hyr, hid, hxid, htys]
    change Res.ok (Val.retype _ (Conv.constBool 1)) = Res.ok (Val.retype _ (PtrOps.isNonNil [yp]))
    rw [isNonNil_nn hnn]; rfl

theorem nodeOf_x {x : ID} {v : Value} (hx : x ∈ fb.values) (hv : f.value? x = some v)
    (hph : v.op ≠ .Phi) : nodeOf (schedNodes f fb).toList x = some ⟨x, v.args, prio v.op⟩ := by
  obtain ⟨v', hv', hid, -⟩ := K.valueIn hx
  rw [hv] at hv'; cases hv'
  have hm : (⟨v.id, v.args, prio v.op⟩ : SNode) ∈ (schedNodes f fb).toList :=
    mem_schedNodes.2 ⟨x, hx, v, hv, hph, rfl⟩
  have := nodeOf_of_mem (schedNodes_ids K.ownF K.ndF) hm
  rw [hid] at this; exact this

/-- An available value's arguments are available. -/
theorem avail_args {k : Nat} {z : ID} {v : Value} (hz : Base f bid z ∨ z ∈ oS.toList.take k)
    (hv : f.value? z = some v) (hph : v.op ≠ .Phi) {a : ID} (ha : a ∈ v.args) :
    Base f bid a ∨ a ∈ oS.toList.take k := by
  rcases hz with hB | hz
  · exact .inl (K.base_closed hB hv hph ha)
  · obtain ⟨iz, hiz⟩ := List.getElem?_of_mem hz
    have hizk : iz < k := by
      have := (List.getElem?_eq_some_iff.1 hiz).1; simp at this; omega
    rw [List.getElem?_take_of_lt hizk] at hiz
    exact (K.srcArg hiz hv ha).imp id (K.take_mono (Nat.le_of_lt hizk))

omit K in
theorem offPtr_safe {ai : Int64} {w : Val} (hw : Safe w) (hni : ∀ x, w ≠ .int .w64 x) :
    Safe (PtrOps.offPtr ai [w]) := by
  match w, hw with
  | .ptr q, hw => simpa [PtrOps.offPtr, Ptr.add, Safe] using hw
  | .int .w64 x, _ => exact absurd rfl (hni x)
  | .int .w8 _, _ | .int .w16 _, _ | .int .w32 _, _ | .bool _, _ | .mem _, _ | .tuple _, _
  | .agg _, _ | .blob _, _ | .empty, _ | .poison, _ => simp [PtrOps.offPtr, Safe]

omit K in
theorem addPtr_safe {w i : Val} (hw : Safe w) (hni : ∀ x, w ≠ .int .w64 x) :
    Safe (PtrOps.addPtr [w, i]) := by
  match w, hw with
  | .ptr q, hw =>
    unfold PtrOps.addPtr
    simp only
    split <;> simp_all [Safe, Ptr.add]
  | .int .w64 x, _ => exact absurd rfl (hni x)
  | .int .w8 _, _ | .int .w16 _, _ | .int .w32 _, _ | .bool _, _ | .mem _, _ | .tuple _, _
  | .agg _, _ | .blob _, _ | .empty, _ | .poison, _ => simp [PtrOps.addPtr, Safe]

omit K in
/-- A pointer-shaped register is no 64-bit integer. -/
theorem not_int_of_ptr {y : Val} {e : Option Nat} (h : y.retype (.ptr e) = y) :
    ∀ x, y ≠ .int .w64 x := by
  rintro x rfl; simp [Val.retype] at h

omit K in
/-- What `safePtr` says of a value. -/
theorem safePtr_spec {n : Nat} {z : ID} (h : Opt.NilCheck.safePtr tabs f (n + 1) z = true) :
    ∃ v e, f.value? z = some v ∧ tabs.ty v.type = .ptr e ∧
      (((v.op = .Addr ∨ v.op = .LocalAddr) ∧ v.aux.isSome = true) ∨ v.op = .NilCheck ∨
        ((v.op = .OffPtr ∨ v.op = .AddPtr) ∧
          ∃ a, v.args[0]? = some a ∧ Opt.NilCheck.safePtr tabs f n a = true)) := by
  unfold Opt.NilCheck.safePtr at h
  cases hv : f.value? z with
  | none => rw [hv] at h; cases h
  | some v =>
  rw [hv] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hps, hop⟩ := h
  obtain ⟨e, he⟩ : ∃ e, tabs.ty v.type = .ptr e := by
    unfold Opt.NilCheck.ptrShaped at hps
    split at hps
    · exact ⟨_, by assumption⟩
    · cases hps
  refine ⟨v, e, rfl, he, ?_⟩
  split at hop
  · next h => exact .inl ⟨.inl h, hop⟩
  · next h => exact .inl ⟨.inr h, hop⟩
  · next h => exact .inr (.inl h)
  · next h =>
    split at hop
    · next a ha => exact .inr (.inr ⟨.inl h, a, ha, hop⟩)
    · cases hop
  · next h =>
    split at hop
    · next a ha => exact .inr (.inr ⟨.inr h, a, ha, hop⟩)
    · cases hop
  · cases hop

omit K in
theorem frameVal_addr_safe {ctx : Ctx} {v : Value} (h : v.op = .Addr) :
    ∃ x, frameVal ctx v = some x ∧ Safe x := by
  unfold frameVal; rw [h]
  simp only
  split <;> simp [Safe]

omit K in
theorem frameVal_local_safe {ctx : Ctx} {v : Value} (h : v.op = .LocalAddr)
    (ha : v.aux.isSome = true) : ∃ x, frameVal ctx v = some x ∧ Safe x := by
  unfold frameVal; rw [h]
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 ha
  simp [hn, Safe]

/-- **`safePtr` values are `Safe`** in the source's frames. -/
theorem safe_chain {S : Frame} {k : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k)) :
    ∀ (n : Nat) (z : ID), Opt.NilCheck.safePtr tabs f n z = true →
      (Base f bid z ∨ z ∈ oS.toList.take k) →
        ∃ y, S.regs[z]? = some (some y) ∧ Safe y ∧ ∀ x, y ≠ .int .w64 x
  | 0, _, h, _ => by simp [Opt.NilCheck.safePtr] at h
  | n + 1, z, h, hz => by
    obtain ⟨ce, hwf⟩ := K.wf
    obtain ⟨v, e, hv, he, hop⟩ := safePtr_spec h
    have hph : v.op ≠ .Phi := by
      intro hp
      rcases hop with ⟨h1 | h1, -⟩ | h1 | ⟨h1 | h1, -⟩ <;> rw [hp] at h1 <;> cases h1
    obtain ⟨b, blk, hbin, hxb, hid⟩ := K.listed_avail hz hv
    obtain ⟨y, hy, hev⟩ := K.availS hS hz hv hph
    have hty : (Ctx.make tabs f).tys[v.id]?.getD .other = .ptr e := by
      rw [hid, tys_of_value hv]; simpa using he
    have htyp := evalValue_typed hev
    rw [hty] at htyp
    refine ⟨y, hy, ?_, not_int_of_ptr htyp⟩
    obtain ⟨vs, hvs⟩ := argVals_of_eval (env := env) (ctx := Ctx.make tabs f) (fr := S) (v := v)
      (by rw [hev]; nofun)
    rw [evalValue_of_argVals hvs, hty] at hev
    obtain ⟨r, hr, hyr⟩ := bind_ok hev
    subst hyr
    apply safe_retype_ptr
    have hnr : (v.op = .Addr ∨ v.op = .LocalAddr ∨ v.op = .OffPtr ∨ v.op = .AddPtr) →
        isRoot v.op = false ∧ v.op ≠ .InitMem ∧ v.op ≠ .Arg ∧ v.op ≠ .ArgIntReg ∧
          v.op ≠ .GetClosurePtr := by
      intro h; rcases h with h | h | h | h <;> rw [h] <;> decide
    rcases hop with ⟨h1, hax⟩ | h1 | ⟨h1, a, ha, hsa⟩
    · obtain ⟨hr1, hr2, hr3, hr4, hr5⟩ := hnr (by rcases h1 with h1 | h1 <;> simp [h1])
      rw [evalOp_tail hr1 hr2 hr3 hr4 hr5] at hr
      obtain ⟨x, hx, hsx⟩ : ∃ x, frameVal (Ctx.make tabs f) v = some x ∧ Safe x := by
        rcases h1 with h1 | h1
        · exact frameVal_addr_safe h1
        · exact frameVal_local_safe h1 hax
      rw [hx] at hr; cases hr; exact hsx
    · rw [evalOp_nilCheck h1] at hr
      exact nilCheck_ok_safe h1 hr
    · obtain ⟨hr1, hr2, hr3, hr4, hr5⟩ := hnr (by rcases h1 with h1 | h1 <;> simp [h1])
      rw [evalOp_tail hr1 hr2 hr3 hr4 hr5] at hr
      have hfv : frameVal (Ctx.make tabs f) v = none :=
        frameVal_none (by rcases h1 with h1 | h1 <;> rw [h1] <;> decide)
      rw [hfv] at hr; cases hr
      have haa := K.avail_args hz hv hph (Array.mem_of_getElem? ha)
      obtain ⟨ya, hya, hsa', hni⟩ := safe_chain hS n a hsa haa
      rcases h1 with h1 | h1
      · have har := hwf.arity b blk z v ⟨hbin, hxb, hv⟩ (by rw [h1]; decide)
        rw [h1, show Op.OffPtr.argLen = 1 by decide] at har
        have hsz : v.args.size = 1 := by exact_mod_cast har
        have hva : v.args = #[a] := by
          apply Array.ext (by simp [hsz]); intro k h1' h2'
          have : k = 0 := by simp at h2'; omega
          subst this; simpa [Array.getElem?_eq_getElem h1'] using ha
        have hvs' : vs = [ya] := by
          rw [hva] at hvs; unfold argVals at hvs
          simp [hya] at hvs; exact hvs.symm
        subst hvs'
        rw [h1]
        exact offPtr_safe hsa' hni
      · have har := hwf.arity b blk z v ⟨hbin, hxb, hv⟩ (by rw [h1]; decide)
        rw [h1, show Op.AddPtr.argLen = 2 by decide] at har
        have hsz : v.args.size = 2 := by exact_mod_cast har
        obtain ⟨a', i', ya'', yi, hargs, rfl, hya'', -⟩ := argVals_two hvs hsz
        rw [hargs] at ha
        simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at ha
        subst ha
        rw [hya] at hya''; cases hya''
        rw [h1]
        exact addPtr_safe hsa' hni

/-- A nil check of a pointer that `safePtr` holds of never panics. -/
theorem seedNoPanic {S : Frame} {k i : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k))
    {x : ID} (hi : oS.toList[i]? = some x) (hik : i ≤ k) {fv : Value} (hfv : f.value? x = some fv)
    (hop : fv.op = .NilCheck) {p' m' : ID} (hargs : fv.args = #[p', m'])
    (hj : Just tabs f bid x p' p' fv.type true) {yp : Val} (hyp : S.regs[p']? = some (some yp))
    {ym : Val} {e : Panic} {m : Mem}
    (h : memRoot (Ctx.make tabs f) fv [yp, ym] = .panic e m) : False := by
  have hsp : Opt.NilCheck.safePtr tabs f f.valueTab.size p' = true := by
    cases hj with
    | seed _ h => exact h
    | dom hne => exact absurd rfl hne
    | same hne => exact absurd rfl hne
  have hav : Base f bid p' ∨ p' ∈ oS.toList.take k :=
    (K.srcArg hi hfv (by rw [hargs]; simp)).imp id (K.take_mono hik)
  obtain ⟨y, hy, hsafe, -⟩ := K.safe_chain hS _ p' hsp hav
  rw [hyp] at hy; cases hy
  exact nilCheck_safe hop hsafe h

/-- The value the source panics at is unchanged in the target. -/
theorem panic_same {S : Frame} {k : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k))
    {r : ID} (hkS : oS.toList[k]? = some r) {fv : Value} (hfv : f.value? r = some fv)
    {e : Panic} {m : Mem} (hrp : evalValue env (Ctx.make tabs f) S fv = .panic e m)
    {gv : Value} (hgv : g.value? r = some gv)
    (hna : ∀ nc, ¬ (gv.op = .Copy ∧ gv.args[0]? = some nc ∧ After f g fv r nc ∧ fv.op = .NilCheck)) :
    gv.op = fv.op ∧ gv.args = fv.args ∧ gv.aux = fv.aux ∧ gv.auxInt = fv.auxInt := by
  obtain ⟨ce, hwf⟩ := K.wf
  obtain ⟨hxb, fv', hfv', hph⟩ := K.memS.1 (List.mem_of_getElem? hkS)
  rw [hfv] at hfv'; cases hfv'
  obtain ⟨gv', hgv', -, -, -, hrel⟩ := K.rel.value r fv hfv
  rw [hgv] at hgv'; cases hgv'
  have hvb := (K.placed_node hxb hfv).2
  obtain ⟨vs, hvs⟩ := argVals_of_eval (env := env) (ctx := Ctx.make tabs f) (fr := S) (v := fv)
    (by rw [hrp]; nofun)
  cases hrel with
  | same hop hargs hax hai => exact ⟨hop, hargs, hax, hai⟩
  | @nc p nc hop hcp hp hs1 hn hj =>
    exfalso
    have hsz : fv.args.size = 2 := by
      have := hwf.arity bid fb r fv ⟨⟨K.tree.1, K.hfb⟩, hxb, hfv⟩ (by rw [hop]; decide)
      rw [hop, show Op.NilCheck.argLen = 2 by decide] at this
      exact_mod_cast this
    obtain ⟨p', m', yp, ym, hargs, rfl, hyp, -⟩ := argVals_two hvs hsz
    rw [hargs] at hp
    simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at hp
    subst hp
    rw [evalValue_of_argVals hvs, evalOp_nilCheck hop] at hrp
    have hmr : ∃ e' m', memRoot (Ctx.make tabs f) fv [yp, ym] = .panic e' m' := by
      cases h : memRoot (Ctx.make tabs f) fv [yp, ym] with
      | ok z => rw [h] at hrp; cases hrp
      | panic e' m' => exact ⟨e', m', rfl⟩
      | stuck msg => rw [h] at hrp; cases hrp
    obtain ⟨e', m', hmr⟩ := hmr
    rw [hvb] at hj
    by_cases hne : nc = p'
    · subst hne
      exact K.seedNoPanic hS hkS (Nat.le_refl k) hfv hop hargs hj hyp hmr
    · obtain ⟨yp', -, hyp', hnn, -⟩ := K.just_nn hS (Nat.le_refl k) hkS hj hne
      rw [hyp] at hyp'; cases hyp'
      exact (nilCheck_nn (a := ym) hop hnn).1 e' m' hmr
  | @nn p nc hop hcb hai hs0 hs1 hp hne hj =>
    exfalso
    rw [evalValue_of_argVals hvs, evalOp_pure (.inl hop)] at hrp
    cases hrp
  | @after nc hop hcp hs1 hn hA => exact absurd ⟨hcp, hn, hA, hop⟩ (hna nc)

/-- The root the source panics at is a root of the target. -/
theorem panic_root {S : Frame} {k : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k))
    {r : ID} (hkS : oS.toList[k]? = some r) {e : Panic} {m : Mem}
    (hrp : stepV env (Ctx.make tabs f) S r = .panic e m)
    (hna : ∀ fv gv nc, f.value? r = some fv → g.value? r = some gv →
      ¬ (gv.op = .Copy ∧ gv.args[0]? = some nc ∧ After f g fv r nc ∧ fv.op = .NilCheck)) : root g r = true := by
  obtain ⟨hxb, fv, hfv, hph⟩ := K.memS.1 (List.mem_of_getElem? hkS)
  rw [stepV_of (ctx := Ctx.make tabs f) hfv] at hrp
  obtain ⟨gv, hgv, -⟩ := K.rel.value r fv hfv
  obtain ⟨hop, -⟩ := K.panic_same hS hkS hfv hrp hgv (hna fv gv · hfv hgv)
  have hpo := evalValue_panic_op hrp
  have : prio fv.op ≠ 0 := prio_panicking hpo
  simp [Opt.NilCheck.root, hgv, hop, this]

/-- **The root the source panics at** panics alike in the target. -/
theorem panicSame {S T : Frame} {k j : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hT : TFacts env tabs g F0 S T (oS.toList.take k) (oT.toList.take j))
    {r : ID} (hjT : oT.toList[j]? = some r) (hkS : oS.toList[k]? = some r) {e : Panic} {m : Mem}
    (hrp : stepV env (Ctx.make tabs f) S r = .panic e m)
    (hna : ∀ fv gv nc, f.value? r = some fv → g.value? r = some gv →
      ¬ (gv.op = .Copy ∧ gv.args[0]? = some nc ∧ After f g fv r nc ∧ fv.op = .NilCheck)) :
    stepV env (Ctx.make tabs g) T r = .panic e m := by
  obtain ⟨hxb, fv, hfv, hph⟩ := K.memS.1 (List.mem_of_getElem? hkS)
  rw [stepV_of (ctx := Ctx.make tabs f) hfv] at hrp
  obtain ⟨gv, hgv, hid, hbl, hty, -⟩ := K.rel.value r fv hfv
  obtain ⟨hop, hargs, hax, hai⟩ := K.panic_same hS hkS hfv hrp hgv (hna fv gv · hfv hgv)
  have hxid := K.idOf hxb hfv
  have hsrc : ∀ a ∈ fv.args, Base f bid a ∨ a ∈ oS.toList.take k := fun a ha => K.srcArg hkS hfv ha
  have htys : (Ctx.make tabs g).tys[r]? = (Ctx.make tabs f).tys[r]? := by
    rw [tys_of_value hgv, tys_of_value hfv, hty]
  obtain ⟨vs, hvs⟩ := argVals_of_eval (env := env) (ctx := Ctx.make tabs f) (fr := S) (v := fv)
    (by rw [hrp]; nofun)
  have hT' : argVals T gv.args = some vs := by
    rw [argVals_congr fun a ha => K.agreeT hS hT (hsrc a (hargs ▸ ha)) (K.tArgsT hjT hgv ha),
      hargs, hvs]
  rw [stepV_of (ctx := Ctx.make tabs g) hgv,
    evalValue_rel (ctxF := Ctx.make tabs f) (ctxG := Ctx.make tabs g) hop hax hai hid
      (by rw [hid, hxid, htys]) rfl K.ctx_params rfl (frame_TS hS hT) hvs (.inl hT'), hrp]

/-- **A value the source did not reach** is pure in the target and evaluates (its arguments
are defined). -/
theorem pureEval {S T : Frame} {k j : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hT : TFacts env tabs g F0 S T (oS.toList.take k) (oT.toList.take j))
    {x : ID} (hjT : oT.toList[j]? = some x) (hr : root g x = false) {gv : Value}
    (hgv : g.value? x = some gv) (ha : gv.op ≠ .Arg) (hb : gv.op ≠ .ArgIntReg) :
    ∃ y, stepV env (Ctx.make tabs g) T x = .ok y := by
  rw [stepV_of (ctx := Ctx.make tabs g) hgv]
  obtain ⟨vs, hvs⟩ := argVals_some (fr := T) (as := gv.args) fun a hga => by
    rcases K.tArgsT hjT hgv hga with hB | hm
    · obtain ⟨va, hpl, -, -⟩ := id hB
      obtain ⟨y, hy, -⟩ := K.base_eval (S := F0) (L := []) (fun _ h => absurd h List.not_mem_nil)
        (fun _ _ => rfl) rfl hB hpl.1
      exact ⟨y, by
        rw [hT.out a fun hm => K.base_not_node hB (K.memT.1 (List.mem_of_mem_take hm)), hy]⟩
    · obtain ⟨-, y, -, hy, -⟩ := hT.eval a hm
      exact ⟨y, hy⟩
  have hp0 : prio gv.op = 0 := by
    simp only [Opt.NilCheck.root, hgv, Option.map_some, Option.getD_some, bne_eq_false_iff_eq] at hr
    exact hr
  obtain ⟨r, hr'⟩ := evalOp_total (env := env) (ctx := Ctx.make tabs g) (fr := T) (argv := vs)
    (ty := (Ctx.make tabs g).tys[gv.id]?.getD .other) (v := gv) (CSE.Blk.isRoot_of_prio hp0) ha hb
  exact ⟨_, by rw [evalValue_of_argVals hvs, hr']; rfl⟩

theorem lt_valueTab {x : ID} (hx : Node f fb x) : x < F0.regs.size := by
  obtain ⟨-, v, hv, -⟩ := hx
  rw [K.size]; exact GoFV.Proof.lt_of_value? hv

theorem notMem_take {j : Nat} {x : ID} (hj : oT.toList[j]? = some x) : x ∉ oT.toList.take j := by
  intro hm
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hm
  have hij : i < j := by
    have := (List.getElem?_eq_some_iff.1 hi).1; simp at this; omega
  rw [List.getElem?_take_of_lt hij] at hi
  exact absurd (Order.idx_unique K.ndT hi hj) (by omega)

theorem take_succ_eq {j : Nat} {x : ID} (hj : oT.toList[j]? = some x) :
    oT.toList.take (j + 1) = oT.toList.take j ++ [x] := by
  rw [List.take_add_one, hj]; rfl

/-- **One target step** keeps `TFacts`. -/
theorem tstep {S T : Frame} {pre : List ID} {j : Nat} {x : ID} (hj : oT.toList[j]? = some x)
    (hT : TFacts env tabs g F0 S T pre (oT.toList.take j)) {y : Val}
    (hy : stepV env (Ctx.make tabs g) T x = .ok y)
    (hag : x ∈ pre → S.regs[x]? = some (some y)) :
    TFacts env tabs g F0 S (T.set x y) pre (oT.toList.take (j + 1)) := by
  have hxn := K.memT.1 (List.mem_of_getElem? hj)
  have hxlt : x < T.regs.size := by rw [hT.size]; exact K.lt_valueTab hxn
  have hnot := K.notMem_take hj
  rw [K.take_succ_eq hj]
  have hkeep : ∀ z, z ≠ x → (T.set x y).regs[z]? = T.regs[z]? := fun z hz =>
    Frame.set_regs_ne (Ne.symm hz)
  have hargs : ∀ i z gz, i ≤ j → oT.toList[i]? = some z → g.value? z = some gz →
      ∀ a ∈ gz.args, a ≠ x := by
    intro i z gz hij hz hgz a ha hax
    subst hax
    rcases K.tArgsT hz hgz ha with hB | hm
    · exact K.base_not_node hB hxn
    · exact hnot (List.take_subset_take_left _ hij hm)
  refine ⟨?_, by simp [Frame.set, hT.size], fun z hz => ?_, fun z hz => ?_, fun z hz hzp => ?_⟩
  · have hf := hT.frame
    unfold Frame.set
    conv => lhs; rw [hf]
  · have hzx : z ≠ x := fun h => hz (by simp [h])
    rw [hkeep z hzx, hT.out z (fun h => hz (List.mem_append_left _ h))]
  · rcases List.mem_append.1 hz with hz | hz
    · obtain ⟨gz, yz, hgz, hyz, hev⟩ := hT.eval z hz
      have hzx : z ≠ x := fun h => hnot (h ▸ hz)
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hz
      have hij : i < j := by
        have := (List.getElem?_eq_some_iff.1 hi).1; simp at this; omega
      rw [List.getElem?_take_of_lt hij] at hi
      refine ⟨gz, yz, hgz, by rw [hkeep z hzx, hyz], ?_⟩
      rw [← hev]
      refine (evalValue_congr (g := T.set x y) rfl fun a ha => ?_).symm
      exact (hkeep a (hargs i z gz (by omega) hi hgz a ha)).symm
    · simp only [List.mem_singleton] at hz; subst hz
      obtain ⟨gz, hgz⟩ : ∃ gz, g.value? z = some gz := by
        unfold stepV at hy
        cases h : g.value? z with
        | some gz => exact ⟨gz, rfl⟩
        | none => simp [Ctx.make, h] at hy
      rw [stepV_of (ctx := Ctx.make tabs g) hgz] at hy
      refine ⟨gz, y, hgz, Frame.set_regs_self hxlt, ?_⟩
      rw [← hy]
      refine (evalValue_congr (g := T.set z y) rfl fun a ha => ?_).symm
      exact (hkeep a (hargs j z gz (Nat.le_refl _) hj hgz a ha)).symm
  · rcases List.mem_append.1 hz with hz | hz
    · have hzx : z ≠ x := fun h => hnot (h ▸ hz)
      rw [hkeep z hzx, hT.agree z hz hzp]
    · simp only [List.mem_singleton] at hz; subst hz
      rw [Frame.set_regs_self hxlt, hag hzp]

/-- The invariant of the target's loop. -/
def Inv (S : Frame) (pre : List ID) (d : List ID) (T : Frame) : Prop :=
  d = oT.toList.take d.length ∧ TFacts env tabs g F0 S T pre d ∧
    ∀ x ∈ d, root g x = true → x ∈ pre

omit K in
theorem inv_zero {S : Frame} {pre : List ID} :
    Inv (env := env) (tabs := tabs) (g := g) (F0 := F0) (oT := oT) S pre [] F0 :=
  ⟨rfl, ⟨rfl, rfl, fun _ _ => rfl, fun _ h => by simp at h, fun _ h => by simp at h⟩,
    fun _ h => by simp at h⟩

/-- **The target's loop** over the first `K'` values of its schedule. -/
theorem loop {S : Frame} {k : Nat} {K' : Nat}
    (hroots : ∀ x ∈ oT.toList.take K', root g x = true → x ∈ oS.toList.take k)
    (hev : ∀ j x, j < K' → oT.toList[j]? = some x → ∀ T,
      TFacts env tabs g F0 S T (oS.toList.take k) (oT.toList.take j) →
      ∃ y, stepV env (Ctx.make tabs g) T x = .ok y ∧
        (x ∈ oS.toList.take k → S.regs[x]? = some (some y))) :
    ∃ T', evalAll env (Ctx.make tabs g) F0 (oT.toList.take K') = .ok T' ∧
      TFacts env tabs g F0 S T' (oS.toList.take k) (oT.toList.take K') := by
  have hstep : ∀ d x rest T, oT.toList.take K' = d ++ x :: rest →
      Inv (env := env) (tabs := tabs) (g := g) (F0 := F0) (oT := oT) S (oS.toList.take k) d T →
      ∃ y, stepV env (Ctx.make tabs g) T x = .ok y ∧
        Inv (env := env) (tabs := tabs) (g := g) (F0 := F0) (oT := oT) S
          (oS.toList.take k) (d ++ [x]) (T.set x y) := by
    intro d x rest T hL ⟨hd, hT, hr⟩
    have hjx : (oT.toList.take K')[d.length]? = some x := by rw [hL]; simp
    have hjK : d.length < K' := by
      have := (List.getElem?_eq_some_iff.1 hjx).1; simp at this; omega
    have hj : oT.toList[d.length]? = some x := by
      rwa [List.getElem?_take_of_lt hjK] at hjx
    rw [hd] at hT hr
    obtain ⟨y, hy, hag⟩ := hev d.length x hjK hj T hT
    refine ⟨y, hy, ?_, ?_, fun z hz hzr => ?_⟩
    · rw [List.length_append, List.length_singleton, K.take_succ_eq hj, ← hd]
    · rw [hd, ← K.take_succ_eq hj]
      exact K.tstep hj hT hy hag
    · exact hroots z (by rw [hL]; rcases List.mem_append.1 hz with h | h
                         · exact List.mem_append_left _ h
                         · simp at h; subst h; simp) hzr
  obtain ⟨T', h1, -, h2, -⟩ := evalAll_loop hstep (oT.toList.take K') [] F0 rfl inv_zero
  exact ⟨T', h1, h2⟩

theorem sfacts {pre : List ID} {G : Frame} (hpre : ∃ post, oS.toList = pre ++ post)
    (h : evalAll env (Ctx.make tabs f) F0 pre = .ok G) : SFacts env tabs f F0 G pre := by
  obtain ⟨post, hpost⟩ := hpre
  obtain ⟨ond, otopo, -⟩ := schedule_topo K.ownF K.ndF K.hoS
  rw [hpost] at ond otopo
  obtain ⟨e1, e2, e3, e4⟩ := evalAll_spec (List.nodup_append.1 ond).1
    (topoRem_append_left otopo) (by rw [K.size]; rfl) h
  exact ⟨e1, e2, e3, e4⟩

/-- The ok case. -/
theorem okCase {G : Frame} (h : evalAll env (Ctx.make tabs f) F0 oS.toList = .ok G) :
    evalAll env (Ctx.make tabs g) F0 oT.toList = .ok G := by
  have hS : SFacts env tabs f F0 G (oS.toList.take oS.toList.length) := by
    rw [List.take_length]; exact K.sfacts ⟨[], by simp⟩ h
  have hall : ∀ x ∈ oT.toList, x ∈ oS.toList.take oS.toList.length := fun x hx => by
    rw [List.take_length]; exact K.memS.2 (K.memT.1 hx)
  obtain ⟨T', h1, hT'⟩ := K.loop (S := G) (k := oS.toList.length) (K' := oT.toList.length)
    (fun x hx _ => hall x (List.mem_of_mem_take hx)) (fun j x hj hjx T hT => by
      obtain ⟨i, hi⟩ := List.getElem?_of_mem (K.memS.2 (K.memT.1 (List.mem_of_getElem? hjx)))
      have hik : i < oS.toList.length := (List.getElem?_eq_some_iff.1 hi).1
      obtain ⟨y, hy, hSy⟩ := K.sameOk hS hT (fun z hz _ => hall z (List.mem_of_mem_take hz))
        hjx hi hik
      exact ⟨y, hy, fun _ => hSy⟩)
  simp only [List.take_length] at h1 hT'
  have hTG : T' = G := by
    refine frame_ext (by rw [hT'.frame, hS.frame]) fun z => ?_
    by_cases hz : z ∈ oT.toList
    · exact hT'.agree z hz (K.memS.2 (K.memT.1 hz))
    · rw [hT'.out z hz, hS.out z ?_]
      intro hm; rw [List.take_length] at hm
      exact hz (K.memT.2 (K.memS.1 hm))
  rw [h1, hTG]

/-- **The target's prefix up to `K'`** when the source stopped at the root `r` (position
`pre.length`): values the source reached evaluate alike, the others are pure. -/
theorem prefixLoop {pre : List ID} {Gp : Frame}
    (hS : SFacts env tabs f F0 Gp (oS.toList.take pre.length)) {r : ID}
    (hk : oS.toList[pre.length]? = some r) (hrnp : ∀ rv, f.value? r = some rv → prio rv.op ≠ 0)
    {K' : Nat} (hroots : ∀ x ∈ oT.toList.take K', root g x = true → x ∈ oS.toList.take pre.length)
    (hxr : ∀ j x, j < K' → oT.toList[j]? = some x → x ≠ r) :
    ∃ T', evalAll env (Ctx.make tabs g) F0 (oT.toList.take K') = .ok T' ∧
      TFacts env tabs g F0 Gp T' (oS.toList.take pre.length) (oT.toList.take K') := by
  obtain ⟨ce, hwf⟩ := K.wf
  have hrS : r ∈ oS.toList := List.mem_of_getElem? hk
  refine K.loop hroots (fun j x hj hjx T hT => ?_)
  have hr' : ∀ z ∈ oT.toList.take j, root g z = true → z ∈ oS.toList.take pre.length :=
    fun z hz hzr => hroots z (List.take_subset_take_left _ (Nat.le_of_lt hj) hz) hzr
  have hxn := K.memT.1 (List.mem_of_getElem? hjx)
  obtain ⟨i, hi⟩ := List.getElem?_of_mem (K.memS.2 hxn)
  by_cases hik : i < pre.length
  · obtain ⟨y, hy, hSy⟩ := K.sameOk hS hT hr' hjx hi hik
    exact ⟨y, hy, fun _ => hSy⟩
  · -- not reached by the source: pure in the target
    obtain ⟨hxb, fv, hfv, hph⟩ := hxn
    have hxr' := hxr j x hj hjx
    have hki : pre.length < i := by
      rcases Nat.lt_or_ge pre.length i with h' | h'
      · exact h'
      · have : i = pre.length := by omega
        subst this; rw [hk] at hi; cases hi; exact absurd rfl hxr'
    have hnotS : x ∉ oS.toList.take pre.length := fun hm => by
      obtain ⟨i', hi'⟩ := List.getElem?_of_mem hm
      have hi'k : i' < pre.length := by
        have := (List.getElem?_eq_some_iff.1 hi').1; simp at this; omega
      rw [List.getElem?_take_of_lt hi'k] at hi'
      exact absurd (Order.idx_unique K.ndS hi' hi) (by omega)
    have hxroot : root g x = false := by
      cases hxr'' : root g x with
      | false => rfl
      | true =>
        exact absurd (hroots x (List.mem_of_getElem?
          (by rw [List.getElem?_take_of_lt hj]; exact hjx)) hxr'') hnotS
    obtain ⟨gv, hgv, -, -, -, hrel⟩ := K.rel.value x fv hfv
    have hnA : gv.op ≠ .Arg ∧ gv.op ≠ .ArgIntReg := by
      cases hrel with
      | nc _ hcp => rw [hcp]; decide
      | nn _ hcb => rw [hcb]; decide
      | after _ hcp => rw [hcp]; decide
      | same hop =>
        rw [hop]
        have hp0 : prio fv.op = 0 := by
          simpa [Opt.NilCheck.root, hgv, hop] using hxroot
        obtain ⟨hrb, rv, hrv, hrph⟩ := K.memS.1 hrS
        have hspec := schedule_spec K.hoS
        obtain ⟨a, haD, -⟩ := hspec.pureFirst pre.length i r x hki hk hi
          (fun hpu => by
            have := hpu _ (K.nodeOf_x hrb hrv hrph)
            exact hrnp rv hrv this)
          (fun n hn => by rw [K.nodeOf_x hxb hfv hph] at hn; cases hn; exact hp0)
        rw [argsOf_schedNodes K.ownF K.ndF hxb hfv hph] at haD
        have hne : fv.args.size ≠ 0 := fun h0 => by
          rw [Array.eq_empty_of_size_eq_zero h0] at haD; simp at haD
        have hnA : ∀ op, fv.op = op → (op = .Arg ∨ op = .ArgIntReg) → False := by
          intro op hop' hor
          have har := hwf.arity bid fb x fv ⟨⟨K.tree.1, K.hfb⟩, hxb, hfv⟩
            (by rw [hop', argLen_zero_of_arg hor]; decide)
          rw [hop', argLen_zero_of_arg hor] at har
          exact hne (by exact_mod_cast har)
        exact ⟨fun h' => hnA _ h' (.inl rfl), fun h' => hnA _ h' (.inr rfl)⟩
    obtain ⟨y, hy⟩ := K.pureEval hS hT hjx hxroot hgv hnA.1 hnA.2
    exact ⟨y, hy, fun hm => absurd hm hnotS⟩

/-- A target root is a source root. -/
theorem root_f_of_g {y : ID} {fy : Value} (hfy : f.value? y = some fy) (hy : root g y = true) :
    root f y = true := by
  obtain ⟨gy, hgy, -, -, -, hr⟩ := K.rel.value y fy hfy
  cases hr with
  | same hop => simpa [Opt.NilCheck.root, hgy, hfy, hop] using hy
  | nc _ hcp =>
    simp only [Opt.NilCheck.root, hgy, hcp, Option.map_some, Option.getD_some] at hy
    exact absurd hy (by decide)
  | nn _ hcb =>
    simp only [Opt.NilCheck.root, hgy, hcb, Option.map_some, Option.getD_some] at hy
    exact absurd hy (by decide)
  | after _ hcp =>
    simp only [Opt.NilCheck.root, hgy, hcp, Option.map_some, Option.getD_some] at hy
    exact absurd hy (by decide)

/-- **The source panics at a removed check `r`** whose copied check `nc` follows it directly:
the target runs the same roots up to `nc`, which panics alike. -/
theorem panicAfter {e : Panic} {m : Mem} {pre post : List ID} {r : ID} {Gp : Frame}
    (hsplit : oS.toList = pre ++ r :: post)
    (hpre : evalAll env (Ctx.make tabs f) F0 pre = .ok Gp)
    (hrp : stepV env (Ctx.make tabs f) Gp r = .panic e m) {fv gv : Value} {nc : ID}
    (hfv : f.value? r = some fv) (hgv : g.value? r = some gv) (hcp : gv.op = .Copy)
    (hgn0 : gv.args[0]? = some nc) (hA : After f g fv r nc) (hop : fv.op = .NilCheck) :
    evalAll env (Ctx.make tabs g) F0 oT.toList = .panic e m := by
  obtain ⟨ce, hwf⟩ := K.wf
  have hk : oS.toList[pre.length]? = some r := by rw [hsplit]; simp
  have htk : oS.toList.take pre.length = pre := by rw [hsplit]; simp
  have hS : SFacts env tabs f F0 Gp (oS.toList.take pre.length) := by
    rw [htk]; exact K.sfacts ⟨r :: post, hsplit⟩ hpre
  obtain ⟨hrb, -⟩ := K.memS.1 (List.mem_of_getElem? hk)
  have hvb := (K.placed_node hrb hfv).2
  cases hA with
  | @mk n gn fb' o i j hn _ hop' hargs' _ hbl' hgn hgop hgargs hfb' hm ho hi hj hij hgap =>
  rw [hvb, K.hfb] at hfb'; cases hfb'
  rw [K.hoS] at ho; cases ho
  have hipre := Order.idx_unique K.ndS (by simpa using hi) hk
  subst hipre
  have hncN : Node f fb nc := ⟨hm, _, hn, by rw [hop']; decide⟩
  obtain ⟨k'', hk''⟩ := List.getElem?_of_mem (K.memT.2 hncN)
  have hrootnc : root g nc = true := by
    simp only [Opt.NilCheck.root, hgn, hgop, Option.map_some, Option.getD_some]; decide
  have hroots0 := roots_before K.roots K.ndT K.ndS hk'' (by simpa using hj) hrootnc
  have hroots : ∀ y ∈ oT.toList.take k'', root g y = true → y ∈ oS.toList.take pre.length := by
    intro y hy hry
    have hyj := hroots0 y hy hry
    obtain ⟨iy, hiy⟩ := List.getElem?_of_mem hyj
    have hiyj : iy < j := by
      have := (List.getElem?_eq_some_iff.1 hiy).1; simp at this
      exact Nat.lt_of_lt_of_le (Nat.lt_of_succ_le this) (Nat.min_le_left _ _)
    rw [List.getElem?_take_of_lt hiyj] at hiy
    rcases Nat.lt_or_ge iy pre.length with h1 | h1
    · exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt h1]; exact hiy)
    · exfalso
      rcases Nat.lt_or_ge pre.length iy with h2 | h2
      · have hyS : y ∈ oS.toList := List.mem_of_getElem? (by simpa using hiy)
        obtain ⟨-, fy, hfy, -⟩ := K.memS.1 hyS
        have := hgap iy y h2 hiyj (by simpa using hiy)
        rw [K.root_f_of_g hfy hry] at this; cases this
      · have : iy = pre.length := by omega
        subst this; rw [hk] at hiy; cases hiy
        simp only [Opt.NilCheck.root, hgv, hcp, Option.map_some, Option.getD_some] at hry
        exact absurd hry (by decide)
  have hrnp : ∀ rv, f.value? r = some rv → prio rv.op ≠ 0 := by
    intro rv hrv; rw [hfv] at hrv; cases hrv
    rw [hop]; decide
  have hxr : ∀ j x, j < k'' → oT.toList[j]? = some x → x ≠ r := by
    intro j x hjk hjx hxr
    subst hxr
    have : nc ∈ gv.args := Array.mem_of_getElem? hgn0
    obtain ⟨i', hi', hia⟩ := K.topoT hjx hgv this hncN
    exact absurd (Order.idx_unique K.ndT hia hk'') (by omega)
  obtain ⟨T', h1, hT'⟩ := K.prefixLoop hS hk hrnp hroots hxr
  -- the source's check panicked on `[yp, mem m]`
  rw [stepV_of (ctx := Ctx.make tabs f) hfv] at hrp
  have hsz : fv.args.size = 2 := by
    have := hwf.arity bid fb r fv ⟨⟨K.tree.1, K.hfb⟩, hrb, hfv⟩ (by rw [hop]; decide)
    rw [hop, show Op.NilCheck.argLen = 2 by decide] at this
    exact_mod_cast this
  obtain ⟨vs, hvs⟩ := argVals_of_eval (env := env) (ctx := Ctx.make tabs f) (fr := Gp) (v := fv)
    (by rw [hrp]; nofun)
  obtain ⟨p', m', yp, ym, hargs, rfl, hyp, hym⟩ := argVals_two hvs hsz
  rw [evalValue_of_argVals hvs, evalOp_nilCheck hop] at hrp
  have hmr : memRoot (Ctx.make tabs f) fv [yp, ym] = .panic e m := by
    cases h : memRoot (Ctx.make tabs f) fv [yp, ym] with
    | ok z => rw [h] at hrp; cases hrp
    | panic e' m' => rw [h] at hrp; exact hrp
    | stuck msg => rw [h] at hrp; cases hrp
  obtain ⟨q, hq, he, hnn, hsh⟩ := nilCheck_panic hop hmr
  simp only [List.cons.injEq] at hq
  obtain ⟨rfl, rfl, -⟩ := hq
  subst he
  -- the target's check reads the same registers and panics alike
  have hTargs : ∀ a ∈ gn.args, T'.regs[a]? = Gp.regs[a]? := fun a ha =>
    K.agreeT hS hT' (K.srcArg hk hfv (by rw [← hargs', ← hgargs]; exact ha))
      (K.tArgsT hk'' hgn ha)
  have hvsT : argVals T' gn.args = some [yp, .mem m] := by
    rw [argVals_congr hTargs, hgargs, hargs', hvs]
  have hstep : stepV env (Ctx.make tabs g) T' nc = .panic .nilDeref m := by
    rw [stepV_of (ctx := Ctx.make tabs g) hgn, evalValue_of_argVals hvsT, evalOp_nilCheck hgop,
      nilCheck_panic_of hgop hnn hsh]
    rfl
  rw [split_at hk'', evalAll_append, h1]
  show evalAll env (Ctx.make tabs g) T' (nc :: oT.toList.drop (k'' + 1)) = _
  rw [evalAll_cons, hstep]

/-- The panic case. -/
theorem panicCase {e : Panic} {m : Mem}
    (h : evalAll env (Ctx.make tabs f) F0 oS.toList = .panic e m) :
    evalAll env (Ctx.make tabs g) F0 oT.toList = .panic e m := by
  obtain ⟨ce, hwf⟩ := K.wf
  obtain ⟨pre, r, post, Gp, hsplit, hpre, hrp⟩ := evalAll_panic_split h
  have hk : oS.toList[pre.length]? = some r := by rw [hsplit]; simp
  have htk : oS.toList.take pre.length = pre := by rw [hsplit]; simp
  have hS : SFacts env tabs f F0 Gp (oS.toList.take pre.length) := by
    rw [htk]; exact K.sfacts ⟨r :: post, hsplit⟩ hpre
  have hrS : r ∈ oS.toList := List.mem_of_getElem? hk
  obtain ⟨hrb, rv, hrv, -⟩ := K.memS.1 hrS
  obtain ⟨gr, hgr, -⟩ := K.rel.value r rv hrv
  by_cases hA : ∃ nc, gr.op = .Copy ∧ gr.args[0]? = some nc ∧ After f g rv r nc ∧
      rv.op = .NilCheck
  · obtain ⟨nc, hcp, hn0, hA, hop⟩ := hA
    exact K.panicAfter hsplit hpre hrp hrv hgr hcp hn0 hA hop
  have hna : ∀ fv gv nc, f.value? r = some fv → g.value? r = some gv →
      ¬ (gv.op = .Copy ∧ gv.args[0]? = some nc ∧ After f g fv r nc ∧ fv.op = .NilCheck) := by
    intro fv gv nc hfv hgv h'
    rw [hrv] at hfv; cases hfv; rw [hgr] at hgv; cases hgv
    exact hA ⟨nc, h'⟩
  obtain ⟨k', hk'⟩ := List.getElem?_of_mem (K.memT.2 (K.memS.1 hrS))
  have hrroot : root g r = true := K.panic_root hS hk hrp hna
  have hroots := roots_before K.roots K.ndT K.ndS hk' hk hrroot
  have hrnp : ∀ rv', f.value? r = some rv' → prio rv'.op ≠ 0 := by
    intro rv' hrv'
    have hop' := (K.panic_same hS hk hrv'
      (by rw [← stepV_of (ctx := Ctx.make tabs f) hrv']; exact hrp) hgr
      (hna rv' gr · hrv' hgr)).1
    simpa [Opt.NilCheck.root, hgr, hop'] using hrroot
  obtain ⟨T', h1, hT'⟩ := K.prefixLoop hS hk hrnp hroots (fun j x hj hjx he => by
    subst he; exact absurd (Order.idx_unique K.ndT hjx hk') (by omega))
  have hsplitT := split_at hk'
  rw [hsplitT, evalAll_append, h1]
  show evalAll env (Ctx.make tabs g) T' (r :: oT.toList.drop (k' + 1)) = _
  rw [evalAll_cons, K.panicSame hS hT' hk' hk hrp hna]

end Blk

/-- **One block's evaluation in source and target** (`BlockOK`). -/
theorem blockOK {tabs : Tables} {f g : Func} (hrel : NRel tabs f g) (hwf : ∃ ce, WF ce f)
    (hc : CertOK f) (env : Env) : BlockOK env tabs f g := by
  intro bid fb gb F0 oS oT ht hfb hgb hsz hd hphiD hoS hoT hroots
  have K : Blk env tabs f g bid fb gb F0 oS oT :=
    ⟨hrel, hwf, hc, ht, hfb, hgb, hsz, hd, hphiD, hoS, hoT, hroots⟩
  exact ⟨fun G h => K.okCase h, fun e m h => K.panicCase h⟩

end GoFV.Proof.Nil

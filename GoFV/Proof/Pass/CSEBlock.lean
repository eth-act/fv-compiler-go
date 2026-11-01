import GoFV.Proof.Pass.CSEClass
import GoFV.Proof.Pass.CSEBlockSpec
import GoFV.Proof.Sched
import GoFV.Proof.Pass.CopyElimEnter

/-!
# cse: one block's evaluation

`blockOK`: after a tree block's `Phi`s (one frame `F0` for source and target), the target's
evaluation of its schedule reaches the source's frame, or panics alike. Induction along the
target's schedule (`evalAll_loop`): each value the source evaluated before it stops evaluates in
the target to the source's register (`rep_corr`: its arguments' representatives hold the source
arguments' registers); a value the source did not reach (it panicked first) is pure, not an
`Arg`, and its arguments are defined, so it evaluates (roots keep their order, `CRel.sched`).
-/

namespace GoFV.Proof.CSE

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Proof.CopyElim

/-- Iterating steps along a list. -/
theorem evalAll_loop {env : Env} {ctx : Ctx} {I : List ID → Frame → Prop} {L : List ID}
    (hstep : ∀ d x rest T, L = d ++ x :: rest → I d T →
      ∃ y, stepV env ctx T x = .ok y ∧ I (d ++ [x]) (T.set x y)) :
    ∀ rest d T, L = d ++ rest → I d T → ∃ T', evalAll env ctx T rest = .ok T' ∧ I L T'
  | [], d, T, hL, hI => ⟨T, rfl, by rw [hL, List.append_nil]; exact hI⟩
  | x :: rest, d, T, hL, hI => by
    obtain ⟨y, hy, hI'⟩ := hstep d x rest T hL hI
    rw [evalAll_cons, hy]
    exact evalAll_loop hstep rest (d ++ [x]) (T.set x y) (by rw [hL]; simp) hI'

/-- The values from before block `bid`: placed in a strict ancestor, or a `Phi` of `bid`. -/
def Base (f : Func) (bid : ID) (x : ID) : Prop :=
  ∃ v, Placed f x v ∧ Anc (make f) v.block bid ∧ (v.block ≠ bid ∨ v.op = .Phi)

/-- A non-`Phi` value of block `fb`. -/
def Node (f : Func) (fb : Block) (x : ID) : Prop :=
  x ∈ fb.values ∧ ∃ v, f.value? x = some v ∧ v.op ≠ .Phi

/-- The hypotheses of `BlockOK`, with cse's relation and well-formedness. -/
structure Blk (env : Env) (tabs : Tables) (f g : Func) (rw : Array (Option ID)) (bid : ID)
    (fb gb : Block) (F0 : Frame) (oS oT : Array ID) : Prop where
  rel : CRel tabs f g rw
  wf : ∃ ce, WF ce f
  wg : ∃ ce, WF ce g
  cf : CertOK f
  tree : Tree f bid
  hfb : f.block? bid = some fb
  hgb : g.block? bid = some gb
  size : F0.regs.size = f.valueTab.size
  dinv : DInv env (Ctx.make tabs f) (fun a => Anc (make f) a bid ∧ a ≠ bid) F0
  rep : RepInv f rw F0 (fun a => Anc (make f) a bid ∧ a ≠ bid)
  phiDef : ∀ z ∈ fb.values, ∀ v, f.value? z = some v → v.op = .Phi →
    ∃ y, F0.regs[z]? = some (some y)
  phiRep : ∀ z v, Placed f z v → v.block = bid → v.op = .Phi →
    F0.regs[Opt.CSE.rep rw z]? = F0.regs[z]?
  hoS : schedule f fb = some oS
  hoT : schedule g gb = some oT
  roots : oT.toList.filter (Opt.CSE.rootNode f) = oS.toList.filter (Opt.CSE.rootNode f)

variable {env : Env} {tabs : Tables} {f g : Func} {rw : Array (Option ID)} {bid : ID}
  {fb gb : Block} {F0 : Frame} {oS oT : Array ID}

namespace Blk

variable (K : Blk env tabs f g rw bid fb gb F0 oS oT)
include K

theorem hp : parentsOK (make f) f.entry = true := K.cf.parents

theorem gvalues : gb.values = fb.values := by
  obtain ⟨gb', hgb', -, hv, -⟩ := K.rel.block bid K.tree.1 fb K.hfb
  rw [K.hgb] at hgb'; cases hgb'; exact hv

theorem fid : fb.id = bid := by
  obtain ⟨ce, hwf⟩ := K.wf
  obtain ⟨b', hb', hid⟩ := hwf.blockId bid K.tree.1
  rw [K.hfb] at hb'; cases hb'; exact hid

/-- Listed values of the block have their ID and the block. -/
theorem valueIn {x : ID} (hx : x ∈ fb.values) :
    ∃ v, f.value? x = some v ∧ v.id = x ∧ v.block = bid := by
  obtain ⟨ce, hwf⟩ := K.wf
  exact hwf.valueId bid fb ⟨K.tree.1, K.hfb⟩ x hx

theorem placed_node {x : ID} (hx : x ∈ fb.values) {v : Value} (hv : f.value? x = some v) :
    Placed f x v ∧ v.block = bid := by
  obtain ⟨v', hv', -, hb⟩ := K.valueIn hx
  rw [hv] at hv'; cases hv'
  exact ⟨⟨hv, hb ▸ K.tree.1, fb, hb ▸ K.hfb, hx⟩, hb⟩

theorem anc_self : Anc (make f) bid bid := anc_refl K.tree.2

/-- A value placed in an ancestor of the block is from before it or a node. -/
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

/-- The arguments of a node are from before the block or nodes. -/
theorem arg_base_or_node {x : ID} (hx : x ∈ fb.values) {v : Value} (hv : f.value? x = some v)
    (hph : v.op ≠ .Phi) {a : ID} (ha : a ∈ v.args) :
    ∃ va, Placed f a va ∧ Anc (make f) va.block bid ∧ (Base f bid a ∨ Node f fb a) := by
  obtain ⟨ce, hwf⟩ := K.wf
  have hu := uses K.cf K.tree.1 K.hfb K.tree.2 hx hv hph ha
  obtain ⟨b', blk', hbin, hab⟩ := hwf.argListed bid fb x v ⟨⟨K.tree.1, K.hfb⟩, hx, hv⟩ a ha
  obtain ⟨va, hpl, hvb, -⟩ := placed_of_mem hwf hbin.1 hbin.2 hab
  rw [blockOf_placed hpl] at hu
  exact ⟨va, hpl, hu, K.base_or_node hpl hu⟩

/-- A representative of a value placed in an ancestor is placed in an ancestor; of a value from
before the block, from before the block. -/
theorem rep_placed {a : ID} {va : Value} (hpl : Placed f a va)
    (hanc : Anc (make f) va.block bid) :
    ∃ vr, Placed f (Opt.CSE.rep rw a) vr ∧ Anc (make f) vr.block bid ∧
      (Base f bid a → Base f bid (Opt.CSE.rep rw a)) ∧ vr.op = va.op := by
  cases hrw : rw.getD a none with
  | none => rw [rep_none hrw]; exact ⟨va, hpl, hanc, id, rfl⟩
  | some r =>
    rw [rep_some hrw]
    obtain ⟨-, fx, fr, gx, gr, hfx, hfr, -, -, hcg, -, hphi, hanc', hmem, blk, hblk, hrb⟩ :=
      K.rel.subst a r hrw
    rw [hpl.1] at hfx; cases hfx
    have hA : Anc (make f) fr.block va.block := (anc_iff K.hp).1 hanc'
    have hop : fr.op = va.op := hcg.1
    refine ⟨fr, ⟨hfr, hmem, blk, hblk, hrb⟩, Anc.trans K.hp hA hanc, fun hB => ?_, hop⟩
    obtain ⟨va', hpl', -, hor⟩ := hB
    have h1 := hpl'.1
    rw [hpl.1] at h1; cases h1
    refine ⟨fr, ⟨hfr, hmem, blk, hblk, hrb⟩, Anc.trans K.hp hA hanc, ?_⟩
    rcases hor with hne | hph
    · left; intro he
      exact hne (Anc.antisymm K.hp hanc (he ▸ hA))
    · right; rw [hop]; exact hph

theorem ownF : ValuesOwn f fb := by
  obtain ⟨ce, hwf⟩ := K.wf; exact valuesOwn hwf K.tree.1 K.hfb

theorem ndF : fb.values.toList.Nodup := by
  obtain ⟨ce, hwf⟩ := K.wf; exact hwf.valuesNodup bid fb ⟨K.tree.1, K.hfb⟩

theorem bidG : bid ∈ g.blocks := by
  rw [CopyElim.cfgView_blocks K.rel.cfg]; exact K.tree.1

theorem ownG : ValuesOwn g gb := by
  obtain ⟨ce, hwg⟩ := K.wg; exact valuesOwn hwg K.bidG K.hgb

theorem ndG : gb.values.toList.Nodup := by
  obtain ⟨ce, hwg⟩ := K.wg; exact hwg.valuesNodup bid gb ⟨K.bidG, K.hgb⟩

theorem memS {x : ID} : x ∈ oS.toList ↔ Node f fb x := (schedule_topo K.ownF K.ndF K.hoS).2.2 x

theorem memT {x : ID} : x ∈ oT.toList ↔ Node f fb x := by
  rw [(schedule_topo K.ownG K.ndG K.hoT).2.2 x, K.gvalues]
  constructor
  · rintro ⟨hx, gv, hgv, hph⟩
    obtain ⟨v, hv, -⟩ := K.valueIn hx
    obtain ⟨gv', hgv', -, hop, -⟩ := K.rel.value x v hv
    rw [hgv] at hgv'; cases hgv'
    exact ⟨hx, v, hv, by rw [← hop]; exact hph⟩
  · rintro ⟨hx, v, hv, hph⟩
    obtain ⟨gv, hgv, -, hop, -⟩ := K.rel.value x v hv
    exact ⟨hx, gv, hgv, by rw [hop]; exact hph⟩

theorem ndS : oS.toList.Nodup := (schedule_topo K.ownF K.ndF K.hoS).1
theorem ndT : oT.toList.Nodup := (schedule_topo K.ownG K.ndG K.hoT).1

/-- Source dependency order by positions. -/
theorem topoS {j : Nat} {x : ID} (hj : oS.toList[j]? = some x) {v : Value}
    (hv : f.value? x = some v) {a : ID} (ha : a ∈ v.args) (hn : Node f fb a) :
    ∃ i < j, oS.toList[i]? = some a := by
  have hs := (schedule_spec K.hoS).topo
  have hx : Node f fb x := K.memS.1 (List.mem_of_getElem? hj)
  obtain ⟨hxb, v', hv', hph⟩ := hx
  rw [hv] at hv'; cases hv'
  refine hs.before j x hj a ?_ ((nodeIn_schedNodes K.ownF).2 hn)
  rw [argsOf_schedNodes K.ownF K.ndF hxb hv hph]; exact Array.mem_toList_iff.2 ha

/-- Target dependency order by positions. -/
theorem topoT {j : Nat} {x : ID} (hj : oT.toList[j]? = some x) {v : Value}
    (hv : g.value? x = some v) {a : ID} (ha : a ∈ v.args) (hn : Node f fb a) :
    ∃ i < j, oT.toList[i]? = some a := by
  have hs := (schedule_spec K.hoT).topo
  have hnT := (schedule_topo K.ownG K.ndG K.hoT).2.2
  obtain ⟨hxb, v', hv', hph⟩ := (hnT x).1 (List.mem_of_getElem? hj)
  rw [hv] at hv'; cases hv'
  refine hs.before j x hj a ?_ ((nodeIn_schedNodes K.ownG).2 ((hnT a).1 (K.memT.2 hn)))
  rw [argsOf_schedNodes K.ownG K.ndG hxb hv hph]; exact Array.mem_toList_iff.2 ha

/-- A target argument of a node: from before the block or a node. -/
theorem tgtArg {x : ID} (hx : Node f fb x) {gv : Value} (hgv : g.value? x = some gv) {a : ID}
    (ha : a ∈ gv.args) : ∃ va, Placed f a va ∧ Anc (make f) va.block bid ∧
      (Base f bid a ∨ Node f fb a) := by
  obtain ⟨hxb, v, hv, hph⟩ := hx
  obtain ⟨gv', hgv', -, -, -, -, -, -, hrel⟩ := K.rel.value x v hv
  rw [hgv] at hgv'; cases hgv'
  obtain ⟨a0, ha0, rfl⟩ := mem_of_argsRel hrel ha
  obtain ⟨va, hpl, hanc, -⟩ := K.arg_base_or_node hxb hv hph ha0
  obtain ⟨vr, hplr, hancr, -, -⟩ := K.rep_placed hpl hanc
  exact ⟨vr, hplr, hancr, K.base_or_node hplr hancr⟩

theorem base_not_node {x : ID} (hB : Base f bid x) (hn : Node f fb x) : False := by
  obtain ⟨v, hpl, -, hor⟩ := hB
  obtain ⟨hxb, v', hv', hph⟩ := hn
  rw [hpl.1] at hv'; cases hv'
  obtain ⟨-, hb⟩ := K.placed_node hxb hpl.1
  rcases hor with h | h
  · exact h hb
  · exact hph h

end Blk

/-- The source's frame after evaluating the first `k` values of its schedule. -/
structure SFacts (env : Env) (tabs : Tables) (f : Func) (F0 S : Frame) (pre : List ID) : Prop where
  frame : S = { F0 with regs := S.regs }
  size : S.regs.size = F0.regs.size
  out : ∀ z, z ∉ pre → S.regs[z]? = F0.regs[z]?
  eval : ∀ x ∈ pre, ∃ v y, f.value? x = some v ∧ S.regs[x]? = some (some y) ∧
    evalValue env (Ctx.make tabs f) S v = .ok y

/-- The target's frame after evaluating `done` (agreeing with the source on what both did). -/
structure TFacts (env : Env) (tabs : Tables) (g : Func) (F0 S T : Frame) (pre done : List ID) :
    Prop where
  frame : T = { F0 with regs := T.regs }
  size : T.regs.size = F0.regs.size
  out : ∀ z, z ∉ done → T.regs[z]? = F0.regs[z]?
  eval : ∀ x ∈ done, ∃ v y, g.value? x = some v ∧ T.regs[x]? = some (some y) ∧
    evalValue env (Ctx.make tabs g) T v = .ok y
  agree : ∀ x ∈ done, x ∈ pre → T.regs[x]? = S.regs[x]?



namespace Blk

variable (K : Blk env tabs f g rw bid fb gb F0 oS oT)
include K

/-- Registers of values from before the block are `F0`'s in every frame of the block. -/
theorem base_reg {x : ID} (hB : Base f bid x) {fr : Frame} {L : List ID}
    (hL : ∀ y ∈ L, Node f fb y) (hout : ∀ z, z ∉ L → fr.regs[z]? = F0.regs[z]?) :
    fr.regs[x]? = F0.regs[x]? := hout x fun hm => K.base_not_node hB (hL x hm)

/-- **The block's evaluation state gives `Corr`.** -/
theorem corr {S T : Frame} {k j : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hT : TFacts env tabs g F0 S T (oS.toList.take k) (oT.toList.take j))
    (hroots : ∀ x ∈ oT.toList.take j, Opt.CSE.rootNode f x = true → x ∈ oS.toList.take k) :
    Corr env tabs f g rw bid (Base f bid) S T (oS.toList.take k) (oT.toList.take j) := by
  obtain ⟨ce, hwf⟩ := K.wf
  have hp := K.hp
  have hLS : ∀ y ∈ oS.toList.take k, Node f fb y := fun y hy => K.memS.1 (List.mem_of_mem_take hy)
  have hLT : ∀ y ∈ oT.toList.take j, Node f fb y := fun y hy => K.memT.1 (List.mem_of_mem_take hy)
  have bS0 : ∀ x, Base f bid x → S.regs[x]? = F0.regs[x]? := fun x hB => K.base_reg hB hLS hS.out
  have bT0 : ∀ x, Base f bid x → T.regs[x]? = F0.regs[x]? := fun x hB => K.base_reg hB hLT hT.out
  -- arguments of a value from before the block (not a `Phi`) are from before it
  have bCl : ∀ x v, Base f bid x → f.value? x = some v → v.op ≠ .Phi → ∀ a ∈ v.args,
      Base f bid a := by
    intro x v hB hv hph a ha
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
  refine
    { rel := K.rel
      frame := by
        calc T = { F0 with regs := T.regs } := hT.frame
          _ = { S with regs := T.regs } := by rw [hS.frame]
      bS := fun x hB => ?_
      bT := fun x hB => by rw [bT0 x hB, bS0 x hB]
      bRep := fun x hB => ?_
      bCl := bCl
      bOut := fun x v hB hv => by
        obtain ⟨v', hpl, -, hor⟩ := hB
        rw [hpl.1] at hv; cases hv; exact hor
      sPre := fun x hx => ?_
      sOrd := fun j' x hj' v hv a ha => ?_
      tPre := fun x hx => ?_
      tArgs := fun x hx v hv a ha => ?_
      ts := fun x h1 h2 => hT.agree x h2 h1
      roots := hroots
      load2 := fun x v hv hld hx => ?_
      ids := fun x v hv hx => ?_ }
  · -- from before the block: lemma (D) or the block's `Phi`s
    obtain ⟨v, hpl, hanc, hor⟩ := hB
    refine ⟨v, ?_⟩
    by_cases hb : v.block = bid
    · have hph := hor.resolve_left (fun h => h hb)
      obtain ⟨hv, -, blk, hblk, hxb⟩ := hpl
      rw [hb, K.hfb] at hblk; cases hblk
      obtain ⟨y, hy⟩ := K.phiDef x hxb v hv hph
      exact ⟨y, hv, by rw [bS0 x ⟨v, ⟨hv, hb ▸ K.tree.1, fb, hb ▸ K.hfb, hxb⟩, hanc, hor⟩, hy],
        fun h => absurd hph h⟩
    · obtain ⟨y, hy, hev⟩ := K.dinv x v hpl ⟨hanc, hb⟩
      refine ⟨y, hpl.1, by rw [bS0 x ⟨v, hpl, hanc, hor⟩, hy], fun hph => ?_⟩
      rw [← hev hph]
      refine (evalValue_congr hS.frame fun a ha => ?_).symm
      exact (bS0 a (bCl x v ⟨v, hpl, hanc, hor⟩ hpl.1 hph a ha)).symm
  · -- representatives of values from before the block
    obtain ⟨v, hpl, hanc, hor⟩ := hB
    obtain ⟨vr, hplr, hancr, hBr, -⟩ := K.rep_placed hpl hanc
    have hBr' := hBr ⟨v, hpl, hanc, hor⟩
    refine ⟨hBr', ?_⟩
    rw [bS0 _ hBr', bS0 x ⟨v, hpl, hanc, hor⟩]
    by_cases hb : v.block = bid
    · exact K.phiRep x v hpl hb (hor.resolve_left fun h => h hb)
    · exact K.rep x v hpl ⟨hanc, hb⟩
  · obtain ⟨hxb, v, hv, hph⟩ := hLS x hx
    obtain ⟨v', y, hv', hy, hev⟩ := hS.eval x hx
    rw [hv] at hv'; cases hv'
    exact ⟨v, y, hv, hph, (K.placed_node hxb hv).2, hy, hev⟩
  · have hj'k : j' < k := by
      have := (List.getElem?_eq_some_iff.1 hj').1
      simp at this; omega
    have hjS : oS.toList[j']? = some x := by rwa [List.getElem?_take_of_lt hj'k] at hj'
    obtain ⟨hxb, v', hv', hph⟩ := K.memS.1 (List.mem_of_getElem? hjS)
    rw [hv] at hv'; cases hv'
    obtain ⟨va, hpl, hanc, hor⟩ := K.arg_base_or_node hxb hv hph ha
    rcases hor with hB | hn
    · exact .inl hB
    · obtain ⟨i, hi, hia⟩ := K.topoS hjS hv ha hn
      exact .inr ⟨i, hi, by rw [List.getElem?_take_of_lt (by omega)]; exact hia⟩
  · obtain ⟨gv, y, hgv, hy, hev⟩ := hT.eval x hx
    obtain ⟨hxb, v, hv, hph⟩ := hLT x hx
    obtain ⟨gv', hgv', -, hop, -, -, -, hbl, -⟩ := K.rel.value x v hv
    rw [hgv] at hgv'; cases hgv'
    exact ⟨gv, y, hgv, by rw [hop]; exact hph, by rw [hbl]; exact (K.placed_node hxb hv).2, hy, hev⟩
  · obtain ⟨i, hix⟩ := List.getElem?_of_mem hx
    have hik : i < j := by
      have := (List.getElem?_eq_some_iff.1 hix).1
      simp at this; omega
    have hiT : oT.toList[i]? = some x := by rwa [List.getElem?_take_of_lt hik] at hix
    obtain ⟨va, hpl, hanc, hor⟩ := K.tgtArg (hLT x hx) hv ha
    rcases hor with hB | hn
    · exact .inl hB
    · obtain ⟨i', hi', hia⟩ := K.topoT hiT hv ha hn
      exact .inr (List.mem_of_getElem? (by rw [List.getElem?_take_of_lt (show i' < j by omega)]; exact hia))
  · have hlisted : ∃ b blk, BlockIn f b blk ∧ x ∈ blk.values ∧ v.block = b := by
      rcases hx with hB | hx | hx
      · obtain ⟨v', ⟨h1, hb, blk, hblk, hxb⟩, -⟩ := hB
        rw [hv] at h1; cases h1
        exact ⟨v.block, blk, ⟨hb, hblk⟩, hxb, rfl⟩
      · obtain ⟨hxb, -⟩ := hLS x hx
        exact ⟨bid, fb, ⟨K.tree.1, K.hfb⟩, hxb, (K.placed_node hxb hv).2⟩
      · obtain ⟨hxb, -⟩ := hLT x hx
        exact ⟨bid, fb, ⟨K.tree.1, K.hfb⟩, hxb, (K.placed_node hxb hv).2⟩
    obtain ⟨b, blk, hbin, hxb, -⟩ := hlisted
    have := hwf.arity b blk x v ⟨hbin, hxb, hv⟩ (by rw [hld]; decide)
    rw [hld, show Op.Load.argLen = 2 by decide] at this
    exact_mod_cast this
  · obtain ⟨b, blk, hbin, hxb⟩ : ∃ b blk, BlockIn f b blk ∧ x ∈ blk.values := by
      rcases hx with hB | hx | hx
      · obtain ⟨v', ⟨-, hb, blk, hblk, hxb⟩, -⟩ := hB
        exact ⟨_, blk, ⟨hb, hblk⟩, hxb⟩
      · exact ⟨bid, fb, ⟨K.tree.1, K.hfb⟩, (hLS x hx).1⟩
      · exact ⟨bid, fb, ⟨K.tree.1, K.hfb⟩, (hLT x hx).1⟩
    obtain ⟨v', hv', hid, -⟩ := hwf.valueId b blk hbin x hxb
    rw [hv] at hv'; cases hv'; exact hid

end Blk

end GoFV.Proof.CSE

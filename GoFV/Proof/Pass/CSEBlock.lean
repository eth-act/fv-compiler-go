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
  intro x hx
  rw [K.gvalues] at hx
  obtain ⟨v, hv, hid, -⟩ := K.valueIn hx
  obtain ⟨gv, hgv, hgid, -⟩ := K.rel.value x v hv
  exact ⟨gv, hgv, hgid.trans hid⟩

theorem ndG : gb.values.toList.Nodup := by rw [K.gvalues]; exact K.ndF

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


theorem lt_valueTab {x : ID} (hx : Node f fb x) : x < F0.regs.size := by
  obtain ⟨-, v, hv, -⟩ := hx
  rw [K.size]; exact lt_of_value? hv

/-- A target argument of the value at position `i` of the target schedule is from before the
block or listed before it. -/
theorem tArgsT {i : Nat} {x : ID} (hi : oT.toList[i]? = some x) {gv : Value}
    (hgv : g.value? x = some gv) {a : ID} (ha : a ∈ gv.args) :
    Base f bid a ∨ a ∈ oT.toList.take i := by
  obtain ⟨va, hpl, hanc, hor⟩ := K.tgtArg (K.memT.1 (List.mem_of_getElem? hi)) hgv ha
  rcases hor with hB | hn
  · exact .inl hB
  · obtain ⟨i', hi', hia⟩ := K.topoT hi hgv ha hn
    exact .inr (List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hi']; exact hia))

theorem notMem_take {j : Nat} {x : ID} (hj : oT.toList[j]? = some x) : x ∉ oT.toList.take j := by
  intro hm
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hm
  have hij : i < j := by
    have := (List.getElem?_eq_some_iff.1 hi).1; simp at this; omega
  rw [List.getElem?_take_of_lt hij] at hi
  exact absurd (Order.idx_unique K.ndT hi hj) (by omega)

theorem take_succ_eq {j : Nat} {x : ID} (hj : oT.toList[j]? = some x) :
    oT.toList.take (j + 1) = oT.toList.take j ++ [x] := by
  rw [List.take_succ, hj]; rfl

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
  -- the target values evaluated so far read only arguments other than `x`
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

theorem tfacts_zero {S : Frame} {pre : List ID} : TFacts env tabs g F0 S F0 pre (oT.toList.take 0) :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ h => by simp at h, fun _ h => by simp at h⟩

/-- **A value the source evaluated before it stops** evaluates in the target as in the source. -/
theorem sameEval {S T : Frame} {k j : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hT : TFacts env tabs g F0 S T (oS.toList.take k) (oT.toList.take j))
    (hroots : ∀ x ∈ oT.toList.take j, Opt.CSE.rootNode f x = true → x ∈ oS.toList.take k)
    {x : ID} (hjT : oT.toList[j]? = some x) {i : Nat} (hiS : oS.toList[i]? = some x) (hik : i ≤ k) :
    stepV env (Ctx.make tabs g) T x = stepV env (Ctx.make tabs f) S x := by
  have C := K.corr hS hT hroots
  obtain ⟨hxb, fv, hfv, hph⟩ := K.memS.1 (List.mem_of_getElem? hiS)
  obtain ⟨gv, hgv, -⟩ := K.rel.value x fv hfv
  obtain ⟨-, hrel⟩ : True ∧ ArgsRel rw fv.op fv.args gv.args := by
    obtain ⟨gv', hgv', -, -, -, -, -, -, h⟩ := K.rel.value x fv hfv
    rw [hgv] at hgv'; cases hgv'; exact ⟨trivial, h⟩
  obtain ⟨v', -, hxid, -⟩ := K.valueIn hxb
  have hxid' : fv.id = x := by
    obtain ⟨v'', hv'', hid, -⟩ := K.valueIn hxb
    rw [hfv] at hv''; cases hv''; exact hid
  rw [stepV_of (ctx := Ctx.make tabs g) hgv, stepV_of (ctx := Ctx.make tabs f) hfv]
  refine C.eval_rel hfv hgv hxid' fun a ha => ?_
  have haA : Base f bid a ∨ a ∈ oS.toList.take k := by
    obtain ⟨va, hpl, hanc, hor⟩ := K.arg_base_or_node hxb hfv hph ha
    rcases hor with hB | hn
    · exact .inl hB
    · obtain ⟨i', hi', hia⟩ := K.topoS hiS hfv ha hn
      exact .inr (List.mem_of_getElem? (by rw [List.getElem?_take_of_lt (show i' < k by omega)]; exact hia))
  have hrA : Base f bid (Opt.CSE.rep rw a) ∨ Opt.CSE.rep rw a ∈ oT.toList.take j :=
    K.tArgsT hjT hgv (C.rep_mem_of_argsRel hrel ha)
  obtain ⟨-, y, -, hy, -⟩ := C.memA_facts.1 a haA
  exact ⟨y, hy, by rw [C.rep_corr haA hrA, hy]⟩

omit K in
theorem isRoot_of_prio {op : Op} (h : prio op = 0) : isRoot op = false := by
  unfold prio at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i h1; simpa using h1

/-- **A pure value that is not an argument read evaluates** once its arguments are defined. -/
theorem pureEval {S T : Frame} {k j : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hT : TFacts env tabs g F0 S T (oS.toList.take k) (oT.toList.take j))
    (hroots : ∀ x ∈ oT.toList.take j, Opt.CSE.rootNode f x = true → x ∈ oS.toList.take k)
    {x : ID} (hjT : oT.toList[j]? = some x) (hr : Opt.CSE.rootNode f x = false)
    {fv : Value} (hfv : f.value? x = some fv) (ha : fv.op ≠ .Arg) (hb : fv.op ≠ .ArgIntReg) :
    ∃ y, stepV env (Ctx.make tabs g) T x = .ok y := by
  have C := K.corr hS hT hroots
  obtain ⟨gv, hgv, -, hop, -⟩ := K.rel.value x fv hfv
  rw [stepV_of (ctx := Ctx.make tabs g) hgv]
  obtain ⟨vs, hvs⟩ := argVals_some (fr := T) (as := gv.args) fun a ha => by
    rcases K.tArgsT hjT hgv ha with hB | hm
    · obtain ⟨-, y, -, hy, -⟩ := C.bS a hB
      exact ⟨y, by rw [C.bT a hB, hy]⟩
    · obtain ⟨-, y, -, hy, -⟩ := hT.eval a hm
      exact ⟨y, hy⟩
  have hp0 : prio fv.op = 0 := by
    simp only [Opt.CSE.rootNode, hfv, Option.map_some, Option.getD_some, bne_eq_false_iff_eq] at hr
    exact hr
  obtain ⟨r, hr'⟩ := evalOp_total (env := env) (ctx := Ctx.make tabs g) (fr := T) (argv := vs)
    (ty := (Ctx.make tabs g).tys[gv.id]?.getD .other) (v := gv)
    (by rw [hop]; exact isRoot_of_prio hp0) (by rw [hop]; exact ha) (by rw [hop]; exact hb)
  exact ⟨_, by rw [evalValue_of_argVals hvs, hr']; rfl⟩

end Blk

theorem prefix_eq {r : ID} : ∀ {A B C D : List ID}, A ++ r :: B = C ++ r :: D → r ∉ A → r ∉ C →
    A = C
  | [], _, [], _, _, _, _ => rfl
  | [], _, c :: C, _, h, _, hC => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) hC
  | a :: A, _, [], _, h, hA, _ => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) hA
  | a :: A, B, c :: C, D, h, hA, hC => by
    simp only [List.cons_append, List.cons.injEq] at h
    rw [h.1, prefix_eq h.2 (fun hm => hA (List.mem_cons_of_mem _ hm))
      (fun hm => hC (List.mem_cons_of_mem _ hm))]

theorem split_at {L : List ID} {k : Nat} {r : ID} (h : L[k]? = some r) :
    L = L.take k ++ r :: L.drop (k + 1) := by
  obtain ⟨hk, hr⟩ := List.getElem?_eq_some_iff.1 h
  conv => lhs; rw [← List.take_append_drop k L]
  rw [List.drop_eq_getElem_cons hk, hr]

theorem not_mem_take_of {L : List ID} (hn : L.Nodup) {k : Nat} {r : ID} (h : L[k]? = some r) :
    r ∉ L.take k := by
  intro hm
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hm
  have hik : i < k := by
    have := (List.getElem?_eq_some_iff.1 hi).1; simp at this; omega
  rw [List.getElem?_take_of_lt hik] at hi
  exact absurd (Order.idx_unique hn hi h) (by omega)

/-- Roots listed before root `r` in one order with the same roots as another are listed before
`r` in the other. -/
theorem roots_before {L1 L2 : List ID} {p : ID → Bool} (hf : L1.filter p = L2.filter p)
    (h1 : L1.Nodup) (h2 : L2.Nodup) {k1 k2 : Nat} {r : ID} (hr1 : L1[k1]? = some r)
    (hr2 : L2[k2]? = some r) (hp : p r = true) :
    ∀ x ∈ L1.take k1, p x = true → x ∈ L2.take k2 := by
  intro x hx hpx
  have e1 := split_at hr1
  have e2 := split_at hr2
  have hf' : (L1.take k1).filter p ++ r :: (L1.drop (k1 + 1)).filter p =
      (L2.take k2).filter p ++ r :: (L2.drop (k2 + 1)).filter p := by
    have := hf
    rw [e1, e2] at this
    simpa [List.filter_append, List.filter_cons, hp] using this
  have heq := prefix_eq hf' (fun hm => not_mem_take_of h1 hr1 ((List.mem_filter.1 hm).1))
    (fun hm => not_mem_take_of h2 hr2 ((List.mem_filter.1 hm).1))
  have : x ∈ (L1.take k1).filter p := List.mem_filter.2 ⟨hx, hpx⟩
  rw [heq] at this
  exact (List.mem_filter.1 this).1

namespace Blk

variable (K : Blk env tabs f g rw bid fb gb F0 oS oT)
include K

/-- The invariant of the target's loop. -/
def Inv (S : Frame) (pre : List ID) (d : List ID) (T : Frame) : Prop :=
  d = oT.toList.take d.length ∧ TFacts env tabs g F0 S T pre d ∧
    ∀ x ∈ d, Opt.CSE.rootNode f x = true → x ∈ pre

omit K in
theorem inv_zero {S : Frame} {pre : List ID} :
    Inv (env := env) (tabs := tabs) (g := g) (F0 := F0) (oT := oT) (f := f) S pre [] F0 :=
  ⟨rfl, ⟨rfl, rfl, fun _ _ => rfl, fun _ h => by simp at h, fun _ h => by simp at h⟩,
    fun _ h => by simp at h⟩

theorem sfacts {pre : List ID} {G : Frame} (hpre : ∃ post, oS.toList = pre ++ post)
    (h : evalAll env (Ctx.make tabs f) F0 pre = .ok G) : SFacts env tabs f F0 G pre := by
  obtain ⟨post, hpost⟩ := hpre
  obtain ⟨ond, otopo, -⟩ := schedule_topo K.ownF K.ndF K.hoS
  rw [hpost] at ond otopo
  obtain ⟨e1, e2, e3, e4⟩ := evalAll_spec (List.nodup_append.1 ond).1
    (topoRem_append_left otopo) (by rw [K.size]; rfl) h
  exact ⟨e1, e2, e3, e4⟩

/-- A panicking value is a root. -/
theorem root_of_panic {G : Frame} {r : ID} {e : Panic} {m : Mem}
    (h : stepV env (Ctx.make tabs f) G r = .panic e m) : Opt.CSE.rootNode f r = true := by
  unfold stepV at h
  cases hv : f.value? r with
  | none => simp [Ctx.make, hv] at h
  | some v =>
    simp only [show (Ctx.make tabs f).f = f from rfl, hv] at h
    have hop := evalValue_panic_op h
    have : prio v.op ≠ 0 := by
      rcases hop with h1 | h1 | h1 | h1
      · rw [prio_panicking (.inl h1)]; decide
      · rw [prio_panicking (.inr (.inl h1))]; decide
      · rw [prio_panicking (.inr (.inr h1))]; decide
      · rw [h1]; decide
    simp [Opt.CSE.rootNode, hv, this]


/-- **The target's loop** over the first `K'` values of its schedule. -/
theorem loop {S : Frame} {k : Nat} {K' : Nat}
    (hroots : ∀ x ∈ oT.toList.take K', Opt.CSE.rootNode f x = true → x ∈ oS.toList.take k)
    (hev : ∀ j x, j < K' → oT.toList[j]? = some x → ∀ T,
      TFacts env tabs g F0 S T (oS.toList.take k) (oT.toList.take j) →
      (∀ z ∈ oT.toList.take j, Opt.CSE.rootNode f z = true → z ∈ oS.toList.take k) →
      ∃ y, stepV env (Ctx.make tabs g) T x = .ok y ∧
        (x ∈ oS.toList.take k → S.regs[x]? = some (some y))) :
    ∃ T', evalAll env (Ctx.make tabs g) F0 (oT.toList.take K') = .ok T' ∧
      TFacts env tabs g F0 S T' (oS.toList.take k) (oT.toList.take K') := by
  have hstep : ∀ d x rest T, oT.toList.take K' = d ++ x :: rest →
      Inv (env := env) (tabs := tabs) (g := g) (F0 := F0) (oT := oT) (f := f) S
        (oS.toList.take k) d T →
      ∃ y, stepV env (Ctx.make tabs g) T x = .ok y ∧
        Inv (env := env) (tabs := tabs) (g := g) (F0 := F0) (oT := oT) (f := f) S
          (oS.toList.take k) (d ++ [x]) (T.set x y) := by
    intro d x rest T hL ⟨hd, hT, hr⟩
    have hjx : (oT.toList.take K')[d.length]? = some x := by rw [hL]; simp
    have hjK : d.length < K' := by
      have := (List.getElem?_eq_some_iff.1 hjx).1; simp at this; omega
    have hj : oT.toList[d.length]? = some x := by
      rwa [List.getElem?_take_of_lt hjK] at hjx
    rw [hd] at hT hr
    obtain ⟨y, hy, hag⟩ := hev d.length x hjK hj T hT hr
    refine ⟨y, hy, ?_, ?_, fun z hz hzr => ?_⟩
    · rw [List.length_append, List.length_singleton, K.take_succ_eq hj, ← hd]
    · rw [hd, ← K.take_succ_eq hj]
      exact K.tstep hj hT hy hag
    · exact hroots z (by rw [hL]; rcases List.mem_append.1 hz with h | h
                         · exact List.mem_append_left _ h
                         · simp at h; subst h; simp) hzr
  obtain ⟨T', h1, -, h2, -⟩ := evalAll_loop hstep (oT.toList.take K') [] F0 rfl inv_zero
  exact ⟨T', h1, h2⟩

theorem nodeOf_x {x : ID} {v : Value} (hx : x ∈ fb.values) (hv : f.value? x = some v)
    (hph : v.op ≠ .Phi) : nodeOf (schedNodes f fb).toList x = some ⟨x, v.args, prio v.op⟩ := by
  obtain ⟨v', hv', hid, -⟩ := K.valueIn hx
  rw [hv] at hv'; cases hv'
  have hm : (⟨v.id, v.args, prio v.op⟩ : SNode) ∈ (schedNodes f fb).toList :=
    mem_schedNodes.2 ⟨x, hx, v, hv, hph, rfl⟩
  have := nodeOf_of_mem (schedNodes_ids K.ownF K.ndF) hm
  rw [hid] at this; exact this

theorem rootNode_iff {x : ID} {v : Value} (hv : f.value? x = some v) :
    Opt.CSE.rootNode f x = true ↔ prio v.op ≠ 0 := by
  simp [Opt.CSE.rootNode, hv]

/-- The ok case. -/
theorem okCase {G : Frame} (h : evalAll env (Ctx.make tabs f) F0 oS.toList = .ok G) :
    evalAll env (Ctx.make tabs g) F0 oT.toList = .ok G ∧
      RepInv f rw G (fun a => Anc (make f) a bid) := by
  have hS : SFacts env tabs f F0 G (oS.toList.take oS.toList.length) := by
    rw [List.take_length]; exact K.sfacts ⟨[], by simp⟩ h
  have hall : ∀ x ∈ oT.toList, x ∈ oS.toList.take oS.toList.length := fun x hx => by
    rw [List.take_length]; exact K.memS.2 (K.memT.1 hx)
  obtain ⟨T', h1, hT'⟩ := K.loop (S := G) (k := oS.toList.length) (K' := oT.toList.length)
    (fun x hx _ => hall x (List.mem_of_mem_take hx)) (fun j x hj hjx T hT hr => by
      obtain ⟨i, hi⟩ := List.getElem?_of_mem (K.memS.2 (K.memT.1 (List.mem_of_getElem? hjx)))
      have hik : i ≤ oS.toList.length := by
        have := (List.getElem?_eq_some_iff.1 hi).1; omega
      rw [K.sameEval hS hT hr hjx hi hik]
      have hxS := hall x (List.mem_of_getElem? hjx)
      obtain ⟨v, y, hv, hy, hev⟩ := hS.eval x hxS
      exact ⟨y, by rw [stepV_of (ctx := Ctx.make tabs f) hv]; exact hev, fun _ => hy⟩)
  have hT0 := hT'
  simp only [List.take_length] at h1 hT'
  have hTG : T' = G := by
    refine frame_ext (by rw [hT'.frame, hS.frame]) fun z => ?_
    by_cases hz : z ∈ oT.toList
    · exact hT'.agree z hz (K.memS.2 (K.memT.1 hz))
    · rw [hT'.out z hz, hS.out z ?_]
      intro hm; rw [List.take_length] at hm
      exact hz (K.memT.2 (K.memS.1 hm))
  subst hTG
  refine ⟨h1, fun x v hpl hanc => ?_⟩
  have hp := K.hp
  have hLS : ∀ y ∈ oS.toList.take oS.toList.length, Node f fb y := fun y hy => by
    rw [List.take_length] at hy; exact K.memS.1 hy
  obtain ⟨vr, hplr, hancr, hBr, -⟩ := K.rep_placed hpl hanc
  rcases K.base_or_node hpl hanc with hB | hn
  · have hBr' := hBr hB
    rw [K.base_reg hBr' hLS hS.out, K.base_reg hB hLS hS.out]
    obtain ⟨v', hpl', hanc', hor⟩ := hB
    have h1 := hpl'.1; rw [hpl.1] at h1; cases h1
    by_cases hb : v.block = bid
    · exact K.phiRep x v hpl hb (hor.resolve_left fun h => h hb)
    · exact K.rep x v hpl ⟨hanc, hb⟩
  · have C := K.corr hS hT0 (fun x hx _ => hall x (List.mem_of_mem_take hx))
    refine C.rep_corr (.inr (by rw [List.take_length]; exact K.memS.2 hn)) ?_
    rcases K.base_or_node hplr hancr with hB' | hn'
    · exact .inl hB'
    · exact .inr (by rw [List.take_length]; exact K.memT.2 hn')

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
  have hrroot := K.root_of_panic hrp
  have hrS : r ∈ oS.toList := List.mem_of_getElem? hk
  obtain ⟨k', hk'⟩ := List.getElem?_of_mem (K.memT.2 (K.memS.1 hrS))
  have hroots := roots_before K.roots K.ndT K.ndS hk' hk hrroot
  obtain ⟨T', h1, hT'⟩ := K.loop (S := Gp) (k := pre.length) (K' := k') hroots
    (fun j x hj hjx T hT hr => by
      have hxn := K.memT.1 (List.mem_of_getElem? hjx)
      obtain ⟨i, hi⟩ := List.getElem?_of_mem (K.memS.2 hxn)
      by_cases hik : i < pre.length
      · rw [K.sameEval hS hT hr hjx hi (Nat.le_of_lt hik)]
        have hxS : x ∈ oS.toList.take pre.length :=
          List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hik]; exact hi)
        obtain ⟨v, y, hv, hy, hev⟩ := hS.eval x hxS
        exact ⟨y, by rw [stepV_of (ctx := Ctx.make tabs f) hv]; exact hev, fun _ => hy⟩
      · -- not reached by the source: pure, with arguments
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
        have hxroot : Opt.CSE.rootNode f x = false := by
          cases hxr' : Opt.CSE.rootNode f x with
          | false => rfl
          | true =>
            exact absurd (hroots x (List.mem_of_getElem?
              (by rw [List.getElem?_take_of_lt hj]; exact hjx)) hxr') hnotS
        have hp0 : prio fv.op = 0 := by
          simpa [Opt.CSE.rootNode, hfv] using hxroot
        -- `PureFirst`: an argument of `x` comes at or after `r`
        obtain ⟨hrb, rv, hrv, hrph⟩ := K.memS.1 hrS
        have hspec := schedule_spec K.hoS
        obtain ⟨a, haD, -⟩ := hspec.pureFirst pre.length i r x hki hk hi
          (fun hpu => by
            have := hpu _ (K.nodeOf_x hrb hrv hrph)
            exact (K.rootNode_iff hrv).1 hrroot this)
          (fun n hn => by rw [K.nodeOf_x hxb hfv hph] at hn; cases hn; exact hp0)
        rw [argsOf_schedNodes K.ownF K.ndF hxb hfv hph] at haD
        have hne : fv.args.size ≠ 0 := fun h0 => by
          rw [Array.eq_empty_of_size_eq_zero h0] at haD; simp at haD
        have hnA : ∀ op, fv.op = op → (op = .Arg ∨ op = .ArgIntReg) → False := by
          intro op hop hor
          have har := hwf.arity bid fb x fv ⟨⟨K.tree.1, K.hfb⟩, hxb, hfv⟩
            (by rw [hop, argLen_zero_of_arg hor]; decide)
          rw [hop, argLen_zero_of_arg hor] at har
          exact hne (by exact_mod_cast har)
        obtain ⟨y, hy⟩ := K.pureEval hS hT hr hjx hxroot hfv
          (fun h' => hnA _ h' (.inl rfl)) (fun h' => hnA _ h' (.inr rfl))
        exact ⟨y, hy, fun hm => absurd hm hnotS⟩)
  have hsplitT := split_at hk'
  rw [hsplitT, evalAll_append, h1]
  show evalAll env (Ctx.make tabs g) T' (r :: oT.toList.drop (k' + 1)) = _
  rw [evalAll_cons, K.sameEval hS hT' (fun x hx hxr => hroots x hx hxr) hk' hk (Nat.le_refl _),
    hrp]

end Blk

/-- **One block's evaluation in source and target** (`BlockOK`), for cse's relation. -/
theorem blockOK {tabs : Tables} {f g : Func} {rw : Array (Option ID)} (hrel : CRel tabs f g rw)
    (hwf : ∃ ce, WF ce f) (hc : CertOK f) (env : Env) :
    BlockOK env tabs f g rw := by
  intro bid fb gb F0 oS oT ht hfb hgb hsz hd hrep hphiD hphiR hoS hoT hroots
  have K : Blk env tabs f g rw bid fb gb F0 oS oT :=
    ⟨hrel, hwf, hc, ht, hfb, hgb, hsz, hd, hrep, hphiD, hphiR, hoS, hoT, hroots⟩
  exact ⟨fun G h => K.okCase h, fun e m h => K.panicCase h⟩

end GoFV.Proof.CSE

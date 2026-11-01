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

end Blk

end GoFV.Proof.CSE

import GoFV.Proof.Pass.DSEStep
import GoFV.Proof.Pass.CSEBlock

/-!
# dse: one block's evaluation, the setting

`Blk`: a tree block `bid` entered after its `Phi`s with source frame `F0` (lemma (D) for the
strict ancestors, the `Phi`s defined) and target frame `F0T`, which agrees with `F0` on every
value without pending ranges. Its values from before the block (`CSE.Base`) have none
(`base_clean`), so the target reads them as the source does. `avail`: in a source frame that
evaluated a prefix of the schedule, the values from before the block and the prefix hold their
evaluation (`CSE.Mem.Avail`, which locates the stores' pointers). `TFacts`: the target's frame
after a prefix of its schedule, its registers related (`VRel`) to the source's.
-/

namespace GoFV.Proof.DSE

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Proof.CopyElim GoFV.Opt GoFV.Opt.DSE
open GoFV.Proof.CSE (Base Node SFacts)

/-- One tree block's evaluation in source and target, after the `Phi`s. -/
structure Blk (env : Env) (tabs : Tables) (f g : Func) (P : ID → List Iv) (bid : ID)
    (fb gb : Block) (F0 F0T : Frame) (oS oT : Array ID) : Prop where
  rel : DRel tabs f g P
  wf : ∃ ce, WF ce f
  cf : CertOK f
  tree : Tree f bid
  hfb : f.block? bid = some fb
  hgb : g.block? bid = some gb
  size : F0.regs.size = f.valueTab.size
  dinv : DInv env (Ctx.make tabs f) (fun a => Anc (make f) a bid ∧ a ≠ bid) F0
  phiDef : ∀ z ∈ fb.values, ∀ v, f.value? z = some v → v.op = .Phi →
    ∃ y, F0.regs[z]? = some (some y)
  frT : F0T = { F0 with regs := F0T.regs }
  sizeT : F0T.regs.size = F0.regs.size
  agree : ∀ z, P z = [] → F0T.regs[z]? = F0.regs[z]?
  hoS : schedule f fb = some oS
  hoT : schedule g gb = some oT
  roots : oT.toList.filter (CSE.rootNode g) = oS.toList.filter (CSE.rootNode g)

/-- The target's frame after evaluating `done`: registers related to the source's on what both
evaluated, defined on the rest. -/
structure TFacts (P : ID → List Iv) (F0T S T : Frame) (pre done : List ID) : Prop where
  frame : T = { F0T with regs := T.regs }
  size : T.regs.size = F0T.regs.size
  out : ∀ z, z ∉ done → T.regs[z]? = F0T.regs[z]?
  defd : ∀ x ∈ done, ∃ y, T.regs[x]? = some (some y)
  rel : ∀ x ∈ done, x ∈ pre → ∃ yS yT, S.regs[x]? = some (some yS) ∧
    T.regs[x]? = some (some yT) ∧ VRel (IvQ (P x)) yS yT

variable {env : Env} {tabs : Tables} {f g : Func} {P : ID → List Iv} {bid : ID}
  {fb gb : Block} {F0 F0T : Frame} {oS oT : Array ID}

namespace Blk

variable (K : Blk env tabs f g P bid fb gb F0 F0T oS oT)
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

/-- `g`'s value of a value of `f`, kept or an eliminated store. -/
theorem gval {x : ID} {fv : Value} (hfv : f.value? x = some fv) :
    ∃ gv, g.value? x = some gv ∧ (sameV fv gv = true ∨ elimV fv gv = true) :=
  K.rel.value x fv hfv

theorem gval_phi {x : ID} {fv gv : Value} (hfv : f.value? x = some fv)
    (hgv : g.value? x = some gv) : gv.op = .Phi ↔ fv.op = .Phi := by
  obtain ⟨gv', hgv', h⟩ := K.gval hfv
  rw [hgv] at hgv'; cases hgv'
  rcases h with h | h
  · rw [(sameV_spec h).2.1]
  · obtain ⟨hop, hc, -⟩ := elimV_spec h
    rw [hc]
    constructor
    · intro h; cases h
    · intro h; rcases hop with h' | h' | h' <;> rw [h'] at h <;> cases h

/-- `g`'s arguments are among `f`'s. -/
theorem gargs {x : ID} {fv gv : Value} (hfv : f.value? x = some fv) (hgv : g.value? x = some gv)
    {a : ID} (ha : a ∈ gv.args) : a ∈ fv.args := by
  obtain ⟨gv', hgv', h⟩ := K.gval hfv
  rw [hgv] at hgv'; cases hgv'
  rcases h with h | h
  · rwa [(sameV_spec h).2.2.2.2.2.2] at ha
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
  · rw [(sameV_spec h).1, hid]
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

/-- **An argument from before the block has no pending ranges.** -/
theorem base_clean {x : ID} {fv : Value} (hfv : f.value? x = some fv) {a : ID}
    (ha : a ∈ fv.args) (hB : Base f bid a) (hxb : fv.block = bid) : P a = [] := by
  refine Classical.byContradiction fun hp => ?_
  obtain ⟨-, hbl, -⟩ := uses_spec hfv (K.rel.uses x (lt_of_value? hfv)) ha hp
  obtain ⟨va, hpl, -, hor⟩ := hB
  rw [hpl.1] at hbl
  simp only [Option.map_some, Option.some.injEq] at hbl
  rcases hor with hne | hph
  · exact hne (hbl.trans hxb)
  · obtain ⟨gva, hgva, h⟩ := K.gval hpl.1
    have hne : elimV va gva = false := by
      rcases h with h | h
      · exact elimV_false_of_sameV h (by rw [hph]; decide)
      · obtain ⟨hop, -⟩ := elimV_spec h
        rcases hop with h' | h' | h' <;> rw [h'] at hph <;> cases hph
    exact hp (pend_other hpl.1 hgva hne (by rw [hph]; rfl)
      (K.rel.pend a (lt_of_value? hpl.1)))

/-- Arguments of values from before the block (not a `Phi`) are from before it. -/
theorem base_cl {x : ID} {v : Value} (hB : Base f bid x) (hv : f.value? x = some v)
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

/-- A value from before the block holds its register, which (outside `Phi`s) is its evaluation,
in every source frame of the block. -/
theorem base_val {S : Frame} {pre : List ID} (hS : SFacts env tabs f F0 S pre)
    (hL : ∀ y ∈ pre, Node f fb y) {x : ID} (hB : Base f bid x) :
    ∃ v y, f.value? x = some v ∧ S.regs[x]? = some (some y) ∧
      (v.op ≠ .Phi → evalValue env (Ctx.make tabs f) S v = .ok y) := by
  have bS0 : ∀ x, Base f bid x → S.regs[x]? = F0.regs[x]? := fun x hB => K.base_reg hB hL hS.out
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
    exact (bS0 a (K.base_cl ⟨v, hpl, hanc, hor⟩ hpl.1 hph ha)).symm

/-- In the source frame after a prefix of the schedule, the values from before the block and the
prefix are available. -/
theorem avail {S : Frame} {k : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k)) :
    CSE.Mem.Avail env tabs f S (fun a => Base f bid a ∨ a ∈ oS.toList.take k) := by
  have hL : ∀ y ∈ oS.toList.take k, Node f fb y := fun y hy => K.memS.1 (List.mem_of_mem_take hy)
  refine ⟨fun x hx => ?_, fun x v hx hv hph a ha => ?_⟩
  · rcases hx with hB | hx
    · exact K.base_val hS hL hB
    · obtain ⟨v, y, hv, hy, hev⟩ := hS.eval x hx
      exact ⟨v, y, hv, hy, fun _ => hev⟩
  · rcases hx with hB | hx
    · exact .inl (K.base_cl hB hv hph ha)
    · obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
      have hjk : j < k := by
        have := (List.getElem?_eq_some_iff.1 hj).1; simp at this; omega
      rw [List.getElem?_take_of_lt hjk] at hj
      obtain ⟨hxb, -⟩ := K.memS.1 (List.mem_of_getElem? hj)
      rcases K.arg_base_or_node hxb hv hph ha with hB | hn
      · exact .inl hB
      · obtain ⟨i, hi, hia⟩ := K.topoS hj hv ha hn
        have : (oS.toList.take k)[i]? = some a := by
          rw [List.getElem?_take_of_lt (by omega)]; exact hia
        exact .inr (List.mem_of_getElem? this)

theorem lt_valueTab {x : ID} (hx : Node f fb x) : x < F0T.regs.size := by
  obtain ⟨-, v, hv, -⟩ := hx
  rw [K.sizeT, K.size]; exact lt_of_value? hv

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
    (hT : TFacts P F0T S T pre (oT.toList.take j)) {y : Val}
    (hag : x ∈ pre → ∃ yS, S.regs[x]? = some (some yS) ∧ VRel (IvQ (P x)) yS y) :
    TFacts P F0T S (T.set x y) pre (oT.toList.take (j + 1)) := by
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

end Blk

end GoFV.Proof.DSE

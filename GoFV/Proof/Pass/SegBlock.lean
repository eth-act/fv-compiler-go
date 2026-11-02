import GoFV.Proof.Pass.SegRel
import GoFV.Proof.Pass.StructStoreBlock
import GoFV.Proof.MemInv

/-!
# Segments: one block of the target (issue #151)

`Blk`: a tree block `bid` of the source (`StructStore.Src`) and the target's block `gb`
(`BlockSpec`: the source's values but the dropped ones, then the segments' fresh values; the
source's roots with each segment's roots replaced, at the last of them, by its fresh roots and its
anchor), the target entered with registers refining the source's on the values the target keeps
(`RR`), every segment of `f` sound (`SegSound` with the source's memory invariant `Q`, which the
source's frames along the block have). `TFacts`: the target's frame after a prefix of
its schedule; its registers refine the source's on what both evaluated, and a fresh value or
anchor of a segment whose roots the source evaluated refines the target's definitions run on the
source's frame (`segRun`). `segStep`: the target evaluates such a value.
-/

namespace GoFV.Proof.Seg

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Proof.CopyElim GoFV.Opt GoFV.Opt.RewriteCheck
open GoFV.Proof.CSE (Base Node SFacts)
open GoFV.Proof.CSE.Mem (Avail)
open GoFV.Proof.AtomSim (Reg rv evalValue_of_regs regs_of_ok evalOp_term)
open GoFV.Proof.StructStore (Src ssSame_spec pureEval)

/-- The source's registers of the values the target keeps refined by the target's. -/
def RR (f g : Func) (r r' : Array (Option Val)) : Prop :=
  ∀ (a : ID) v x, f.value? a = some v → (g.value? a).isSome = true → r[a]? = some (some x) →
    ∃ y, r'[a]? = some (some y) ∧ Sem.Refines x y

/-- A source frame with `n` registers (the target's), the new ones empty. -/
def ext (n : Nat) (S : Frame) : Frame :=
  { S with regs := S.regs ++ Array.replicate (n - S.regs.size) none }

theorem ext_regs_lt {n : Nat} {S : Frame} {z : ID} (h : z < S.regs.size) :
    (ext n S).regs[z]? = S.regs[z]? := by
  simp [ext, Array.getElem?_append_left h]

theorem ext_regs_none {n : Nat} {S : Frame} {z : ID} (h : S.regs.size ≤ z) :
    (ext n S).regs[z]? = none ∨ (ext n S).regs[z]? = some none := by
  simp only [ext, Array.getElem?_append_right h, Array.getElem?_replicate]
  split <;> simp

theorem ext_size {n : Nat} {S : Frame} (h : S.regs.size ≤ n) : (ext n S).regs.size = n := by
  simp [ext]; omega

theorem ext_frame (n : Nat) (S : Frame) : ext n S = { S with regs := (ext n S).regs } := rfl

theorem ext_regs_some {n : Nat} {S : Frame} {z : ID} {y : Val}
    (h : (ext n S).regs[z]? = some (some y)) : S.regs[z]? = some (some y) := by
  by_cases hlt : z < S.regs.size
  · rwa [ext_regs_lt hlt] at h
  · rcases ext_regs_none (n := n) (Nat.le_of_not_lt hlt) with h' | h' <;> rw [h'] at h <;> cases h

/-- A value of `f` reads its arguments' registers only. -/
theorem ext_eval {env : Env} {ctx : Ctx} {f : Func} {n : Nat} {S : Frame}
    (hs : S.regs.size = f.valueTab.size) {v : Value} (hv : ∀ a ∈ v.args, a < f.valueTab.size) :
    evalValue env ctx (ext n S) v = evalValue env ctx S v :=
  (evalValue_congr (ext_frame n S) fun a ha => (ext_regs_lt (hs ▸ hv a ha)).symm).symm

/-- One tree block's evaluation, source and target, after the `Phi`s. -/
structure Blk (Q : Mem → Prop) (env : Env) (tabs : Tables) (f g : Func) (bid : ID) (fb gb : Block)
    (F0 F0T : Frame) (oS oT : Array ID) : Prop extends Src env tabs f bid fb F0 oS where
  rel : SRel tabs f g
  wg : ∃ ce, WF ce g
  hgb : g.block? bid = some gb
  spec : BlockSpec tabs f g bid fb gb
  hoT : schedule g gb = some oT
  roots : oT.toList.filter (CSE.rootNode g) =
    segRoots g (segList (segArr tabs f g)) (oS.toList.filter (CSE.rootNode f))
  frT : F0T = { F0 with regs := F0T.regs }
  sizeT : F0T.regs.size = g.valueTab.size
  rr : RR f g F0.regs F0T.regs
  sound : ∀ x D N, segOK tabs f g x = some (D, N) → SegSound Q env tabs f g x D N
  /-- The source's frames along the block's schedule have the memory invariant. -/
  inv : ∀ L S, L <+: oS.toList → evalAll env (Ctx.make tabs f) F0 L = .ok S →
    ∀ (z : ID) (y : Val), S.regs[z]? = some (some y) → MemInv.MemsOK Q y

/-- The roots in `f` of the segment of anchor `x` (dropping `D`) are in `pre`. -/
def Covered (f : Func) (pre : List ID) (x : ID) (D : List ID) : Prop :=
  ∀ s ∈ D ++ [x], CSE.rootNode f s = true → s ∈ pre

/-- The target's frame after evaluating `done`. -/
structure TFacts (env : Env) (tabs : Tables) (f g : Func) (F0T S T : Frame) (pre done : List ID) :
    Prop where
  frame : T = { F0T with regs := T.regs }
  size : T.regs.size = F0T.regs.size
  out : ∀ z, z ∉ done → T.regs[z]? = F0T.regs[z]?
  defd : ∀ x ∈ done, ∃ y, T.regs[x]? = some (some y)
  rel : ∀ x ∈ done, x ∈ pre → ∃ yS yT, S.regs[x]? = some (some yS) ∧
    T.regs[x]? = some (some yT) ∧ Sem.Refines yS yT
  seg : ∀ x D N, segOK tabs f g x = some (D, N) → Covered f pre x D →
    ∀ S', evalAll env (Ctx.make tabs g) (ext g.valueTab.size S) (segL x N) = .ok S' →
    ∀ n ∈ segL x N, n ∈ done → ∃ y y', S'.regs[n]? = some (some y) ∧
      T.regs[n]? = some (some y') ∧ Sem.Refines y y'

theorem root_ne_phi {h : Func} {x : ID} {v : Value} (hr : CSE.rootNode h x = true)
    (hv : h.value? x = some v) : v.op ≠ .Phi := by
  intro hp
  simp [CSE.rootNode, hv, hp] at hr
  revert hr; decide

/-- A value of a segment in `g` (a fresh value or the anchor) is no `Phi`. -/
theorem SegD.ne_phi {tabs : Tables} {f g : Func} {x : ID} {D N : List ID} (d : SegD tabs f g x D N)
    {n : ID} (hn : n ∈ segL x N) {v : Value} (hv : g.value? n = some v) : v.op ≠ .Phi := by
  simp only [segL, List.mem_append, List.mem_singleton] at hn
  rcases hn with hn | rfl
  · rcases d.hfresh n hn with hr | ⟨v', hv', hop, -⟩
    · exact root_ne_phi hr hv
    · rw [hv] at hv'; cases hv'; rw [hop]; decide
  · exact root_ne_phi d.hroot hv

/-- What `argReach` reaches from an available value is available. -/
theorem avail_reach {env : Env} {tabs : Tables} {f : Func} {fr : Frame} {A : ID → Prop}
    (H : Avail env tabs f fr A) : ∀ (k : Nat) {s a : ID}, A s → argReach f k s a = true → A a
  | 0, _, _, _, h => by simp [argReach] at h
  | k + 1, s, a, hs, h => by
    unfold argReach at h
    cases hv : f.value? s with
    | none => rw [hv] at h; simp at h
    | some sv =>
      rw [hv] at h
      simp only [Option.any_some, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true,
        Array.contains_iff_mem, Array.any_eq_true] at h
      obtain ⟨hph, h | ⟨i, hi, hb⟩⟩ := h
      · exact H.cl s sv hs hv hph a h
      · exact avail_reach H k (H.cl s sv hs hv hph _ (Array.getElem_mem hi)) hb

variable {Q : Mem → Prop} {env : Env} {tabs : Tables} {f g : Func} {bid : ID} {fb gb : Block}
  {F0 F0T : Frame} {oS oT : Array ID}

namespace Blk

variable (K : Blk Q env tabs f g bid fb gb F0 F0T oS oT)
include K

theorem bidG : bid ∈ g.blocks := by
  rw [cfgView_blocks K.rel.cfg]; exact K.tree.1

theorem ownG : ValuesOwn g gb := by
  obtain ⟨ce, hwg⟩ := K.wg; exact valuesOwn hwg K.bidG K.hgb

theorem ndG : gb.values.toList.Nodup := by
  obtain ⟨ce, hwg⟩ := K.wg; exact hwg.valuesNodup bid gb ⟨K.bidG, K.hgb⟩

theorem memT {x : ID} : x ∈ oT.toList ↔ Node g gb x := (schedule_topo K.ownG K.ndG K.hoT).2.2 x

theorem ndT : oT.toList.Nodup := (schedule_topo K.ownG K.ndG K.hoT).1

theorem topoT {j : Nat} {x : ID} (hj : oT.toList[j]? = some x) {v : Value}
    (hv : g.value? x = some v) {a : ID} (ha : a ∈ v.args) (hn : Node g gb a) :
    a ∈ oT.toList.take j := by
  have hs := (schedule_spec K.hoT).topo
  obtain ⟨hxb, v', hv', hph⟩ := K.memT.1 (List.mem_of_getElem? hj)
  rw [hv] at hv'; cases hv'
  obtain ⟨i, hi, hia⟩ := hs.before j x hj a (by
    rw [argsOf_schedNodes K.ownG K.ndG hxb hv hph]; exact Array.mem_toList_iff.2 ha)
    ((nodeIn_schedNodes K.ownG).2 hn)
  exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hi]; exact hia)

/-- The segment owner of a value of `f`, as `Drop`. -/
theorem notDrop_iff {z : ID} :
    (segOwner (segList (segArr tabs f g)) z).isNone = true ↔ ∀ x, ¬ Drop tabs f g x z := by
  constructor
  · intro h x hd
    rw [(K.rel.own z x).2 hd] at h; cases h
  · intro h
    cases ho : segOwner (segList (segArr tabs f g)) z with
    | none => rfl
    | some x => exact absurd ((K.rel.own z x).1 ho) (h x)

theorem gvalues : ∃ E : Array ID,
    gb.values = fb.values.filter (fun z => (segOwner (segList (segArr tabs f g)) z).isNone) ++ E ∧
    ∀ z ∈ E, f.value? z = none ∧ Fresh tabs f g z ∧ ∃ v, g.value? z = some v ∧ v.block = bid :=
  K.spec.values

/-- `g`'s value of a value of `f` it keeps: kept, or an anchor. -/
theorem gval {x : ID} {fv : Value} (hfv : f.value? x = some fv) (hnd : ∀ x', ¬ Drop tabs f g x' x) :
    ∃ gv, g.value? x = some gv ∧ (ssSame fv gv = true ∨ ∃ D N, segOK tabs f g x = some (D, N)) := by
  rcases K.rel.value x fv hfv with h | ⟨-, x', hd⟩
  · exact h
  · exact absurd hd (hnd x')

theorem gval_nonPhi {x : ID} {fv gv : Value} (hfv : f.value? x = some fv)
    (hgv : g.value? x = some gv) (hph : fv.op ≠ .Phi) : gv.op ≠ .Phi := by
  rcases K.rel.value x fv hfv with ⟨gv', hgv', h⟩ | ⟨hn, -⟩
  · rw [hgv] at hgv'; cases hgv'
    rcases h with h | ⟨D, N, hs⟩
    · rw [(ssSame_spec h).2.1]; exact hph
    · obtain ⟨d⟩ := segOK_spec hs
      exact root_ne_phi d.hroot hgv
  · rw [hgv] at hn; cases hn

/-- A source node the target keeps is a target node. -/
theorem nodeG {x : ID} (hn : Node f fb x) (hnd : ∀ x', ¬ Drop tabs f g x' x) : Node g gb x := by
  obtain ⟨hx, fv, hfv, hph⟩ := hn
  obtain ⟨E, hE, -⟩ := K.gvalues
  obtain ⟨gv, hgv, -⟩ := K.gval hfv hnd
  refine ⟨?_, gv, hgv, K.gval_nonPhi hfv hgv hph⟩
  rw [hE]
  exact Array.mem_append_left _ (Array.mem_filter.2 ⟨hx, (K.notDrop_iff).2 hnd⟩)

/-- A target node that is a value of the source is a source node it keeps. -/
theorem nodeF {x : ID} (hn : Node g gb x) {fv : Value} (hfv : f.value? x = some fv) :
    Node f fb x ∧ ∀ x', ¬ Drop tabs f g x' x := by
  obtain ⟨hx, gv, hgv, hph⟩ := hn
  obtain ⟨E, hE, hEf⟩ := K.gvalues
  rw [hE] at hx
  rcases Array.mem_append.1 hx with hx | hx
  · obtain ⟨hx, hk⟩ := Array.mem_filter.1 hx
    refine ⟨⟨hx, fv, hfv, fun hp => hph ?_⟩, (K.notDrop_iff).1 hk⟩
    rcases K.rel.value x fv hfv with ⟨gv', hgv', h⟩ | ⟨hn, -⟩
    · rw [hgv] at hgv'; cases hgv'
      rcases h with h | ⟨D, N, hs⟩
      · rw [(ssSame_spec h).2.1]; exact hp
      · obtain ⟨d⟩ := segOK_spec hs
        rw [d.hfv] at hfv; cases hfv
        exact absurd hp d.hfph
    · rw [hgv] at hn; cases hn
  · rw [(hEf x hx).1] at hfv; cases hfv

/-- An argument of a value of `g` is a value `g` has. -/
theorem argG {x : ID} {gv : Value} (hx : x ∈ gb.values) (hgv : g.value? x = some gv) {a : ID}
    (ha : a ∈ gv.args) : (g.value? a).isSome = true := by
  obtain ⟨ce, hwg⟩ := K.wg
  obtain ⟨b', blk', hbin, hab⟩ := hwg.argListed bid gb x gv ⟨⟨K.bidG, K.hgb⟩, hx, hgv⟩ a ha
  obtain ⟨va, hva, -, -⟩ := hwg.valueId b' blk' hbin a hab
  rw [hva]; rfl

theorem hLk (k : Nat) : ∀ y ∈ oS.toList.take k, Node f fb y :=
  fun _ hy => K.memS.1 (List.mem_of_mem_take hy)

theorem base_notT {a : ID} (hB : Base f bid a) : a ∉ oT.toList := fun hm => by
  obtain ⟨v, hpl, -, -⟩ := id hB
  exact K.base_not_node hB (K.nodeF (K.memT.1 hm) hpl.1).1

/-- **A value from before the block** that the target keeps: refined registers. -/
theorem baseRel {S T : Frame} {k : Nat} {pre done : List ID}
    (hS : SFacts env tabs f F0 S (oS.toList.take k)) (hT : TFacts env tabs f g F0T S T pre done)
    (hd : ∀ z ∈ done, z ∈ oT.toList) {a : ID} (hB : Base f bid a)
    (hg : (g.value? a).isSome = true) :
    ∃ yS yT, S.regs[a]? = some (some yS) ∧ T.regs[a]? = some (some yT) ∧ Sem.Refines yS yT := by
  obtain ⟨va, yS, hva, hyS, -⟩ := K.base_val hS (K.hLk k) hB
  have h0 : S.regs[a]? = F0.regs[a]? := K.base_reg hB (K.hLk k) hS.out
  obtain ⟨yT, hyT, hr⟩ := K.rr a va yS hva hg (by rw [← h0]; exact hyS)
  exact ⟨yS, yT, hyS, by rw [hT.out a fun hm => K.base_notT hB (hd a hm)]; exact hyT, hr⟩

/-- An argument from before the block or of it has a target register. -/
theorem argDefd {S T : Frame} {k j : Nat} {pre : List ID}
    (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hT : TFacts env tabs f g F0T S T pre (oT.toList.take j)) {x : ID} (hjT : oT.toList[j]? = some x)
    {gv : Value} (hgv : g.value? x = some gv) {a : ID} (ha : a ∈ gv.args)
    (hN : Base f bid a ∨ Node g gb a) : ∃ y, T.regs[a]? = some (some y) := by
  have hxg := (K.memT.1 (List.mem_of_getElem? hjT)).1
  rcases hN with hB | hn
  · obtain ⟨-, yT, -, hyT, -⟩ := K.baseRel hS hT (fun z hz => List.mem_of_mem_take hz) hB
      (K.argG hxg hgv ha)
    exact ⟨yT, hyT⟩
  · exact hT.defd a (K.topoT hjT hgv ha hn)

/-- An argument the source evaluated: refined registers. -/
theorem argRel {S T : Frame} {k j : Nat}
    (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hT : TFacts env tabs f g F0T S T (oS.toList.take k) (oT.toList.take j)) {x : ID}
    (hjT : oT.toList[j]? = some x) {gv : Value} (hgv : g.value? x = some gv) {a : ID}
    (ha : a ∈ gv.args) (hA : Base f bid a ∨ a ∈ oS.toList.take k) :
    ∃ yS yT, S.regs[a]? = some (some yS) ∧ T.regs[a]? = some (some yT) ∧ Sem.Refines yS yT := by
  have hxg := (K.memT.1 (List.mem_of_getElem? hjT)).1
  rcases hA with hB | hp
  · exact K.baseRel hS hT (fun z hz => List.mem_of_mem_take hz) hB (K.argG hxg hgv ha)
  · have hag := K.argG hxg hgv ha
    obtain ⟨av, hav⟩ := Option.isSome_iff_exists.1 hag
    have hnd : ∀ x', ¬ Drop tabs f g x' a := fun x' hd => by
      rw [K.rel.dropNone x' a hd] at hav; cases hav
    exact hT.rel a (K.topoT hjT hgv ha (K.nodeG (K.hLk k a hp) hnd)) hp

omit K in
theorem take_succ_eqT {j : Nat} {x : ID} (hj : oT.toList[j]? = some x) :
    oT.toList.take (j + 1) = oT.toList.take j ++ [x] := by
  rw [List.take_add_one, hj]; rfl

theorem tframe {S T : Frame} {pre done : List ID} {k : Nat}
    (hS : SFacts env tabs f F0 S (oS.toList.take k)) (hT : TFacts env tabs f g F0T S T pre done) :
    T = { S with regs := T.regs } :=
  calc T = { F0T with regs := T.regs } := hT.frame
    _ = { F0 with regs := T.regs } := by rw [K.frT]
    _ = { S with regs := T.regs } := by rw [hS.frame]

/-- **A kept value** evaluates to a refinement of the source's on refined arguments. -/
theorem keptRes (hE : env.Mono) {S T : Frame} {k j : Nat}
    (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hT : TFacts env tabs f g F0T S T (oS.toList.take k) (oT.toList.take j)) {x : ID}
    (hjT : oT.toList[j]? = some x) {fv gv : Value} (hfv : f.value? x = some fv)
    (hfid : fv.id = x) (hgv : g.value? x = some gv) (hs : ssSame fv gv = true)
    (hargs : ∀ a ∈ fv.args, Base f bid a ∨ a ∈ oS.toList.take k)
    (hregS : ∀ a ∈ fv.args, Reg S a) :
    Res.Refines (evalValue env (Ctx.make tabs f) S fv) (evalValue env (Ctx.make tabs g) T gv) := by
  obtain ⟨hid, hop, hax, hai, hty, hbl, hga⟩ := ssSame_spec hs
  have hrel : ∀ a ∈ gv.args, ∃ yS yT, S.regs[a]? = some (some yS) ∧
      T.regs[a]? = some (some yT) ∧ Sem.Refines yS yT :=
    fun a ha => K.argRel hS hT hjT hgv ha (hargs a (hga ▸ ha))
  refine AtomSim.atom_eval_mono hE (AtomSim.ctx_eq K.rel.ownAux.symm) (K.tframe hS hT)
    ⟨hop.symm, hty.symm, hai.symm, hax.symm, by rw [hga], hbl.symm, hid.symm⟩ ?_ hregS
    (fun a ha => by obtain ⟨-, yT, -, h, -⟩ := hrel a ha; exact ⟨yT, h⟩) (fun i hi => ?_)
  · rw [hid, hfid, tys_of_value hgv, tys_of_value hfv, hty]
  · rw [← hga]
    have hmem : gv.args[i]! ∈ gv.args := by
      rw [getElem!_pos gv.args i (by rw [hga]; exact hi)]; exact Array.getElem_mem _
    obtain ⟨yS, yT, h1, h2, h3⟩ := hrel _ hmem
    rw [AtomSim.rv_of h1, AtomSim.rv_of h2]; exact h3

theorem keptOk (hE : env.Mono) {S T : Frame} {k j : Nat}
    (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hT : TFacts env tabs f g F0T S T (oS.toList.take k) (oT.toList.take j)) {x : ID}
    (hjT : oT.toList[j]? = some x) (hxS : x ∈ oS.toList.take k) {gv : Value}
    (hgv : g.value? x = some gv) {fv : Value} (hfv : f.value? x = some fv)
    (hs : ssSame fv gv = true) :
    ∃ y, evalValue env (Ctx.make tabs g) T gv = .ok y ∧
      ∃ yS, S.regs[x]? = some (some yS) ∧ Sem.Refines yS y := by
  obtain ⟨fv', yS, hfv', hyS, hev⟩ := hS.eval x hxS
  rw [hfv] at hfv'; cases hfv'
  obtain ⟨hxb, fv', hfv', hph⟩ := K.hLk k x hxS
  rw [hfv] at hfv'; cases hfv'
  obtain ⟨v', hv', hid, -⟩ := K.valueIn hxb
  rw [hfv] at hv'; cases hv'
  have H := K.avail hS
  have h := K.keptRes hE hS hT hjT hfv hid hgv hs (fun a ha => H.cl x fv (.inr hxS) hfv hph a ha)
    (regs_of_ok hev)
  rw [hev] at h
  generalize evalValue env (Ctx.make tabs g) T gv = r at h ⊢
  cases h with
  | ok hr => exact ⟨_, rfl, yS, hyS, hr⟩

/-- The values the source evaluated (or from before the block) have their own IDs. -/
theorem hidA {k : Nat} : ∀ z v, (Base f bid z ∨ z ∈ oS.toList.take k) → f.value? z = some v →
    v.id = z := fun _ _ hz hv => K.own hz hv

/-- **One target step** keeps `TFacts`. -/
theorem tstep {S T : Frame} {pre : List ID} {j : Nat} {x : ID} (hj : oT.toList[j]? = some x)
    (hT : TFacts env tabs f g F0T S T pre (oT.toList.take j)) {y : Val}
    (hrel : x ∈ pre → ∃ yS, S.regs[x]? = some (some yS) ∧ Sem.Refines yS y)
    (hseg : ∀ x' D N, segOK tabs f g x' = some (D, N) → Covered f pre x' D →
      ∀ S', evalAll env (Ctx.make tabs g) (ext g.valueTab.size S) (segL x' N) = .ok S' →
      x ∈ segL x' N → ∃ y0, S'.regs[x]? = some (some y0) ∧ Sem.Refines y0 y) :
    TFacts env tabs f g F0T S (T.set x y) pre (oT.toList.take (j + 1)) := by
  have hxlt : x < T.regs.size := by
    obtain ⟨-, v, hv, -⟩ := K.memT.1 (List.mem_of_getElem? hj)
    rw [hT.size, K.sizeT]; exact lt_of_value? hv
  have hnot : x ∉ oT.toList.take j := CSE.not_mem_take_of K.ndT hj
  rw [take_succ_eqT hj]
  have hkeep : ∀ z, z ≠ x → (T.set x y).regs[z]? = T.regs[z]? := fun z hz =>
    Frame.set_regs_ne (Ne.symm hz)
  have hself : (T.set x y).regs[x]? = some (some y) := Frame.set_regs_self hxlt
  refine ⟨?_, by simp [Frame.set, hT.size], fun z hz => ?_, fun z hz => ?_, fun z hz hzp => ?_,
    fun x' D N hs hc S' hev n hn hnd => ?_⟩
  · have hf := hT.frame
    unfold Frame.set
    conv => lhs; rw [hf]
  · have hzx : z ≠ x := fun h => hz (by simp [h])
    rw [hkeep z hzx, hT.out z (fun h => hz (List.mem_append_left _ h))]
  · rcases List.mem_append.1 hz with hz | hz
    · rw [hkeep z (fun h => hnot (h ▸ hz))]; exact hT.defd z hz
    · simp only [List.mem_singleton] at hz; subst hz; exact ⟨y, hself⟩
  · rcases List.mem_append.1 hz with hz | hz
    · rw [hkeep z (fun h => hnot (h ▸ hz))]; exact hT.rel z hz hzp
    · simp only [List.mem_singleton] at hz; subst hz
      obtain ⟨yS, hyS, hv⟩ := hrel hzp
      exact ⟨yS, y, hyS, hself, hv⟩
  · rcases List.mem_append.1 hnd with hnd | hnd
    · rw [hkeep n (fun h => hnot (h ▸ hnd))]; exact hT.seg x' D N hs hc S' hev n hn hnd
    · simp only [List.mem_singleton] at hnd; subst hnd
      obtain ⟨y0, hy0, hr⟩ := hseg x' D N hs hc S' hev hn
      exact ⟨y0, y, hy0, hself, hr⟩

/-- An anchor or fresh value lies in one segment. -/
theorem seg_uniq {n x x' : ID} {D D' N N' : List ID} (hs : segOK tabs f g x = some (D, N))
    (hs' : segOK tabs f g x' = some (D', N')) (hn : n ∈ segL x N) (hn' : n ∈ segL x' N') :
    x = x' := by
  obtain ⟨d⟩ := segOK_spec hs
  obtain ⟨d'⟩ := segOK_spec hs'
  simp only [segL, List.mem_append, List.mem_singleton] at hn hn'
  rcases hn with hn | rfl <;> rcases hn' with hn' | rfl
  · exact K.rel.freshUniq x x' D D' N N' n hs hs' hn hn'
  · have := d'.hfv; rw [(d.hN n hn).1] at this; cases this
  · have := d.hfv; rw [(d'.hN n hn').1] at this; cases this
  · rfl

/-- The source frame, extended to the target's registers, with the values from before the block
and those the source evaluated available. -/
theorem availExt {S : Frame} {k : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k)) :
    Avail env tabs f (ext g.valueTab.size S) (fun a => Base f bid a ∨ a ∈ oS.toList.take k) := by
  have H := K.avail hS
  have hsz : S.regs.size = f.valueTab.size := by rw [hS.size, K.size]
  refine ⟨fun z hz => ?_, H.cl⟩
  obtain ⟨v, y, hv, hy, hev⟩ := H.val z hz
  refine ⟨v, y, hv, by rw [ext_regs_lt (hsz ▸ lt_of_value? hv)]; exact hy, fun hph => ?_⟩
  rw [ext_eval hsz fun a ha => ?_]
  · exact hev hph
  · obtain ⟨va, -, hva, -, -⟩ := H.val a (H.cl z v hz hv hph a ha)
    exact lt_of_value? hva

theorem typedExt {S : Frame} {k : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k)) :
    Proof.Typed (Ctx.make tabs f) (ext g.valueTab.size S) := by
  have hty := K.typedS hS (K.hLk k)
  intro z y hz
  by_cases hlt : z < S.regs.size
  · rw [ext_regs_lt hlt] at hz; exact hty z y hz
  · rcases ext_regs_none (n := g.valueTab.size) (Nat.le_of_not_lt hlt) with h | h <;>
      rw [h] at hz <;> cases hz

/-- A segment with a value in the target's block is of the block. -/
theorem segBlock {x n : ID} {D N : List ID} (hs : segOK tabs f g x = some (D, N))
    (d : SegD tabs f g x D N) (hn : n ∈ segL x N) (hnb : n ∈ gb.values) {gv : Value}
    (hgv : g.value? n = some gv) : d.fv.block = bid := by
  obtain ⟨ce, hwg⟩ := K.wg
  obtain ⟨gv', hgv', -, hb⟩ := hwg.valueId bid gb ⟨K.bidG, K.hgb⟩ n hnb
  rw [hgv] at hgv'; cases hgv'
  simp only [segL, List.mem_append, List.mem_singleton] at hn
  rcases hn with hn | rfl
  · obtain ⟨-, -, v, hv, hvb⟩ := d.hN n hn
    rw [hgv] at hv; cases hv
    rw [← hvb, hb]
  · rw [d.hgv] at hgv; cases hgv
    rw [← d.hgbl, hb]

/-- The values of a segment of the block are target nodes. -/
theorem segNode {x a : ID} {D N : List ID} (hs : segOK tabs f g x = some (D, N))
    {d : SegD tabs f g x D N} (hb : d.fv.block = bid) (ha : a ∈ segL x N) : Node g gb a := by
  simp only [segL, List.mem_append, List.mem_singleton] at ha
  rcases ha with ha | rfl
  · obtain ⟨-, ⟨b, hgb, hab⟩, v, hv, -⟩ := d.hN a ha
    rw [hb, K.hgb] at hgb; cases hgb
    exact ⟨hab, v, hv, d.ne_phi (by simp [segL, ha]) hv⟩
  · obtain ⟨b, hfb, hxb⟩ := d.hlisted
    rw [hb, K.hfb] at hfb; cases hfb
    exact K.nodeG ⟨hxb, d.fv, d.hfv, d.hfph⟩ (K.rel.anchorNot a D N hs)

/-- **A segment's value**: a fresh value or the anchor `n` of a segment whose roots the source
evaluated evaluates in the target to a refinement of the target's definitions run on the source's
frame (`SegSound`), and of the source's anchor. -/
theorem segStep (hE : env.Mono) {S T : Frame} {k j : Nat}
    (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hT : TFacts env tabs f g F0T S T (oS.toList.take k) (oT.toList.take j)) {n : ID}
    (hjT : oT.toList[j]? = some n) {x : ID} {D N : List ID} (hs : segOK tabs f g x = some (D, N))
    (hc : Covered f (oS.toList.take k) x D) (hn : n ∈ segL x N)
    (hinv : ∀ (z : ID) (y : Val), S.regs[z]? = some (some y) → MemInv.MemsOK Q y) :
    ∃ y, stepV env (Ctx.make tabs g) T n = .ok y ∧
      TFacts env tabs f g F0T S (T.set n y) (oS.toList.take k) (oT.toList.take (j + 1)) := by
  obtain ⟨d⟩ := segOK_spec hs
  have H := K.avail hS
  have hsz : S.regs.size = f.valueTab.size := by rw [hS.size, K.size]
  have hszg : S.regs.size ≤ g.valueTab.size := hsz ▸ K.rel.size
  -- the target's definitions run on the source's frame
  obtain ⟨S', hev, hanc⟩ := (K.sound x D N hs).2 (ext g.valueTab.size S)
    (fun a => Base f bid a ∨ a ∈ oS.toList.take k) (K.availExt hS) (K.typedExt hS)
    (fun z y h => hinv z y (ext_regs_some h)) K.hidA
    (Nat.le_of_eq (ext_size hszg).symm) (fun s hs' hr => .inr (hc s hs' hr))
  have hnd := K.rel.lnd x D N hs
  have htopo : TopoRem (argsF (Ctx.make tabs g).f) (segL x N) := by
    refine topoRem_of hnd fun i y hy a ha haL => ?_
    have hil : i < (segL x N).length := (List.getElem?_eq_some_iff.1 hy).1
    have hyv : ∃ v, g.value? y = some v := by
      have := (List.getElem?_eq_some_iff.1 hy).2
      by_cases hyx : y = x
      · exact ⟨d.gv, hyx ▸ d.hgv⟩
      · have hyN : y ∈ N := by
          have hm := List.mem_of_getElem? hy
          simp only [segL, List.mem_append, List.mem_singleton] at hm
          exact hm.resolve_right hyx
        obtain ⟨-, -, v, hv, -⟩ := d.hN y hyN
        exact ⟨v, hv⟩
    obtain ⟨v, hv⟩ := hyv
    have hgi : (segL x N).getD i 0 = y := by rw [List.getD_eq_getElem?_getD, hy]; rfl
    rw [show (Ctx.make tabs g).f = g from rfl, argsF_of hv] at ha
    rcases d.hargs i hil v (by rw [hgi]; exact hv) a (Array.mem_toList_iff.1 ha) with h | ⟨-, h, -⟩
    · obtain ⟨i', hia⟩ := List.getElem?_of_mem h
      have hi'l : i' < i := by
        have := (List.getElem?_eq_some_iff.1 hia).1; simp at this; omega
      exact ⟨i', hi'l, by rwa [List.getElem?_take_of_lt hi'l] at hia⟩
    · exact absurd haL h
  obtain ⟨hfr', -, hout', hall⟩ := evalAll_spec hnd htopo (by rw [ext_size hszg]; rfl) hev
  obtain ⟨gv, y0, hgv, hy0, hev0⟩ := hall n hn
  change g.value? n = some gv at hgv
  -- the position of `n` in the segment
  obtain ⟨i0, hi0⟩ := List.getElem?_of_mem hn
  have hi0l : i0 < (segL x N).length := (List.getElem?_eq_some_iff.1 hi0).1
  have hgi0 : (segL x N).getD i0 0 = n := by rw [List.getD_eq_getElem?_getD, hi0]; rfl
  have hnT := K.memT.1 (List.mem_of_getElem? hjT)
  -- the arguments: refined registers
  have hargR : ∀ a ∈ gv.args, ∃ yS yT, S'.regs[a]? = some (some yS) ∧
      T.regs[a]? = some (some yT) ∧ Sem.Refines yS yT := by
    intro a ha
    rcases d.hargs i0 hi0l gv (by rw [hgi0]; exact hgv) a ha with h | ⟨-, haL, s, hsm, hsr, hreach⟩
    · -- an earlier fresh value of the segment, which the target evaluated
      have haL : a ∈ segL x N := List.mem_of_mem_take h
      have haN : Node g gb a := K.segNode hs (d := d) (K.segBlock hs d hn hnT.1 hgv) haL
      obtain ⟨y1, y2, h1, h2, h3⟩ := hT.seg x D N hs hc S' hev a haL (K.topoT hjT hgv ha haN)
      exact ⟨y1, y2, h1, h2, h3⟩
    · -- an argument of a root of the segment, which the source evaluated
      have hsA : Base f bid s ∨ s ∈ oS.toList.take k := .inr (hc s hsm hsr)
      have haA := avail_reach H 8 hsA hreach
      obtain ⟨yS, yT, h1, h2, h3⟩ := K.argRel hS hT hjT hgv ha haA
      refine ⟨yS, yT, ?_, h2, h3⟩
      rw [hout' a haL, ext_regs_lt]
      · exact h1
      · obtain ⟨va, -, hva, -, -⟩ := H.val a haA
        exact hsz ▸ lt_of_value? hva
  have hres : Res.Refines (evalValue env (Ctx.make tabs g) S' gv)
      (evalValue env (Ctx.make tabs g) T gv) := by
    refine AtomSim.atom_eval_mono hE rfl ?_ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl
      (regs_of_ok hev0) (fun a ha => by obtain ⟨-, yT, -, h, -⟩ := hargR a ha; exact ⟨yT, h⟩)
      (fun i hi => ?_)
    · calc T = { F0T with regs := T.regs } := hT.frame
        _ = { F0 with regs := T.regs } := by rw [K.frT]
        _ = { S with regs := T.regs } := by rw [hS.frame]
        _ = { S' with regs := T.regs } := by rw [hfr']; rfl
    · have hmem : gv.args[i]! ∈ gv.args := by
        rw [getElem!_pos gv.args i hi]; exact Array.getElem_mem _
      obtain ⟨yS, yT, h1, h2, h3⟩ := hargR _ hmem
      rw [AtomSim.rv_of h1, AtomSim.rv_of h2]; exact h3
  rw [hev0] at hres
  generalize hT0 : evalValue env (Ctx.make tabs g) T gv = r at hres
  cases hres with
  | ok hr =>
  rename_i y
  refine ⟨y, by rw [stepV_of (ctx := Ctx.make tabs g) hgv, hT0], K.tstep hjT hT (fun hp => ?_)
    fun x' D' N' hs' hc' S'' hev' hn' => ?_⟩
  · -- the anchor the source evaluated
    have hnx : n = x := by
      refine Classical.byContradiction fun hne => ?_
      have hnN : n ∈ N := by
        simp only [segL, List.mem_append, List.mem_singleton] at hn
        exact hn.resolve_right hne
      obtain ⟨_, fv', hfv', _⟩ := K.hLk k n hp
      rw [(d.hN n hnN).1] at hfv'; cases hfv'
    subst hnx
    obtain ⟨ya, yb, ha1, ha2, ha3⟩ := hanc (.inr hp)
    rw [ext_regs_lt (hsz ▸ lt_of_value? d.hfv)] at ha1
    rw [hy0] at ha2; cases ha2
    exact ⟨ya, ha1, ha3.trans hr⟩
  · have hxx := K.seg_uniq hs hs' hn hn'
    subst hxx
    rw [hs] at hs'; cases hs'
    rw [hev] at hev'; cases hev'
    exact ⟨y0, hy0, hr⟩

end Blk

end GoFV.Proof.Seg

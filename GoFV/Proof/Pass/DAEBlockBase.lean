import GoFV.Proof.Pass.DAEStep
import GoFV.Proof.Pass.DSEBlockBase

/-!
# dead auto elim: one block's evaluation, the setting

`Blk`: a tree block `bid` entered after its `Phi`s with source frame `F0` (lemma (D) for the
strict ancestors, the `Phi`s defined, the source invariant and typed registers, inputs avoiding
`U`) and target frame `F0T`, whose registers are related (`VR`) to `F0`'s. `TFacts`: the target's
frame after a prefix of its schedule, its registers related to the source's. `evalAll_regsP`: the
source's evaluation keeps a property of its registers established by each step (the invariant
and typing, `SPr`).
-/

namespace GoFV.Proof.DAE

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Proof.CopyElim GoFV.Opt GoFV.Opt.DAE
open GoFV.Proof.CSE (Base Node SFacts)

/-- The source's register property: the invariant and typing. -/
def SPr (tabs : Tables) (f : Func) (T : ID → Option AuxRef) (E : List AuxRef) (x : ID) (y : Val) :
    Prop :=
  SInv T E x y ∧ y.retype ((Ctx.make tabs f).tys[x]?.getD .other) = y

/-- One tree block's evaluation in source and target, after the `Phi`s. -/
structure Blk (env : Env) (tabs : Tables) (f g : Func) (T : ID → Option AuxRef) (E : List AuxRef)
    (bid : ID) (fb gb : Block) (F0 F0T : Frame) (oS oT : Array ID) : Prop where
  rel : ARelD tabs f g T E
  fs : env.FrameSafe
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
  agree : ∀ (z : ID) (y : Val), F0.regs[z]? = some (some y) →
    ∃ y', F0T.regs[z]? = some (some y') ∧ VR (UE E) y y'
  pr : RegsP (SPr tabs f T E) F0
  fok : FrameOK (UE E) F0
  hoS : schedule f fb = some oS
  hoT : schedule g gb = some oT
  roots : oT.toList.filter (CSE.rootNode g) = oS.toList.filter (CSE.rootNode g)

/-- The target's frame after evaluating `done`: registers related to the source's on what both
evaluated, defined on the rest. -/
structure TFacts (E : List AuxRef) (F0T S T : Frame) (pre done : List ID) : Prop where
  frame : T = { F0T with regs := T.regs }
  size : T.regs.size = F0T.regs.size
  out : ∀ z, z ∉ done → T.regs[z]? = F0T.regs[z]?
  defd : ∀ x ∈ done, ∃ y, T.regs[x]? = some (some y)
  rel : ∀ x ∈ done, x ∈ pre → ∃ yS yT, S.regs[x]? = some (some yS) ∧
    T.regs[x]? = some (some yT) ∧ VR (UE E) yS yT

theorem regsP_inv {tabs : Tables} {f : Func} {T : ID → Option AuxRef} {E : List AuxRef} {fr : Frame}
    (h : RegsP (SPr tabs f T E) fr) : RegsP (SInv T E) fr := fun x y hx => (h x y hx).1

theorem regsP_typed {tabs : Tables} {f : Func} {T : ID → Option AuxRef} {E : List AuxRef}
    {fr : Frame} (h : RegsP (SPr tabs f T E) fr) : Proof.Typed (Ctx.make tabs f) fr :=
  fun x y hx => (h x y hx).2

theorem regsP_set {P : ID → Val → Prop} {fr : Frame} (h : RegsP P fr) {x : ID} {y : Val}
    (hy : P x y) : RegsP P (fr.set x y) := by
  intro z w hz
  by_cases hzx : x = z
  · subst hzx
    by_cases hlt : x < fr.regs.size
    · rw [Frame.set_regs_self hlt] at hz; cases hz; exact hy
    · simp [Frame.set, Array.set!_eq_setIfInBounds, hlt] at hz
  · rw [Frame.set_regs_ne hzx] at hz; exact h z w hz

/-- **The source's evaluation keeps a property of its registers** that each step establishes. -/
theorem evalAll_regsP {env : Env} {ctx : Ctx} {P : ID → Val → Prop} {Q : ID → Prop} {F0 : Frame}
    (hstep : ∀ (fr : Frame) x v y, fr = { F0 with regs := fr.regs } → RegsP P fr → Q x →
      ctx.f.value? x = some v → evalValue env ctx fr v = .ok y → P x y) :
    ∀ (o : List ID) (fr fr' : Frame), fr = { F0 with regs := fr.regs } → RegsP P fr →
      (∀ x ∈ o, Q x) → evalAll env ctx fr o = .ok fr' → RegsP P fr'
  | [], fr, fr', _, hP, _, h => by cases h; exact hP
  | x :: o, fr, fr', hfr, hP, hQ, h => by
    rw [evalAll_cons] at h
    unfold stepV at h
    cases hv : ctx.f.value? x with
    | none => rw [hv] at h; cases h
    | some v =>
      rw [hv] at h
      simp only at h
      cases he : evalValue env ctx fr v with
      | panic e m => rw [he] at h; cases h
      | stuck msg => rw [he] at h; cases h
      | ok y =>
        rw [he] at h
        simp only at h
        refine evalAll_regsP hstep o _ fr' ?_ (regsP_set hP (hstep fr x v y hfr hP
          (hQ x List.mem_cons_self) hv he)) (fun z hz => hQ z (List.mem_cons_of_mem _ hz)) h
        unfold Frame.set; conv => lhs; rw [hfr]

variable {env : Env} {tabs : Tables} {f g : Func} {T : ID → Option AuxRef} {E : List AuxRef}
  {bid : ID} {fb gb : Block} {F0 F0T : Frame} {oS oT : Array ID}

namespace Blk

variable (K : Blk env tabs f g T E bid fb gb F0 F0T oS oT)
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

theorem gval_phi {x : ID} {fv gv : Value} (hfv : f.value? x = some fv)
    (hgv : g.value? x = some gv) : gv.op = .Phi ↔ fv.op = .Phi := by
  obtain ⟨gv', hgv', h⟩ := K.gval hfv
  rw [hgv] at hgv'; cases hgv'
  rcases h with h | h
  · rw [(DSE.sameV_spec h).2.1]
  · obtain ⟨hop, hc, -⟩ := elimV_spec h
    rw [hc]
    constructor
    · intro h; cases h
    · intro h; rcases hop with h' | h' | h' | h' <;> rw [h'] at h <;> cases h

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

/-- A value from before the block holds its register in every source frame of the block. -/
theorem base_def {S : Frame} {pre : List ID} (hS : SFacts env tabs f F0 S pre)
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
  · obtain ⟨y, hy, -⟩ := K.dinv x v hpl ⟨hanc, hb⟩
    exact ⟨y, hy, by rw [bS0, hy]⟩

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

end Blk

end GoFV.Proof.DAE

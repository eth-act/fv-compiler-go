import GoFV.Proof.Pass.StructStoreSrc
import GoFV.Proof.PtrAddr

/-!
# Struct-store splits: one block of the target (issue #151)

`Blk`: a tree block `bid` of the source (`Src`) and the target's block `gb` (`BlockSpec`: the
source's values, then the splits' fresh values; the source's roots with each split `Store`
replaced by its chain of field stores), the target entered with registers refining the source's
(`RR`). `TFacts`: the target's frame after a prefix of its schedule; its registers refine the
source's on what both evaluated, a fresh `OffPtr` holds a word of its field's address (`off`: the
source's `dst` read as a pointer word, `Val.asPtrWord`, moved by the field's offset) and a fresh
field store a memory refining the struct write with the fields so far (`store`: the struct's
bytes `bufK` start `poison`, `StructStoreMem`).
-/

namespace GoFV.Proof.StructStore

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Proof.CopyElim GoFV.Opt GoFV.Opt.RewriteCheck
open GoFV.Proof.CSE (Base Node SFacts)
open GoFV.Proof.CSE.Mem (Avail)
open GoFV.Proof.AtomSim (Reg rv evalValue_of_regs regs_of_ok evalOp_term)

/-- The source's registers of its values refined by the target's (which has more values). -/
def RR (f : Func) (r r' : Array (Option Val)) : Prop :=
  ∀ (a : ID) v x, f.value? a = some v → r[a]? = some (some x) →
    ∃ y, r'[a]? = some (some y) ∧ Sem.Refines x y

theorem ssSame_spec {fv gv : Value} (h : ssSame fv gv = true) :
    gv.id = fv.id ∧ gv.op = fv.op ∧ gv.aux = fv.aux ∧ gv.auxInt = fv.auxInt ∧
      gv.type = fv.type ∧ gv.block = fv.block ∧ gv.args = fv.args := by
  unfold ssSame at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- The struct's bytes with its first `j` fields written (`poison` elsewhere). -/
def bufK (S : Frame) {x : ID} {ps : List (ID × ID)} (d : SplitD tabs f g x ps) (j : Nat) :
    Array Byte :=
  encodeFields (Array.replicate d.n .poison) (d.fs.take j) ((d.smv.args.toList.map (rv S)).take j)

/-- The memory before field `k` of a split: `m0`, then the previous field store. -/
def prevId (ps : List (ID × ID)) (m0 : ID) : Nat → ID
  | 0 => m0
  | k + 1 => (ps[k]?.map (·.2)).getD 0

/-- One tree block's evaluation, source and target, after the `Phi`s. -/
structure Blk (env : Env) (tabs : Tables) (f g : Func) (bid : ID) (fb gb : Block)
    (F0 F0T : Frame) (oS oT : Array ID) : Prop extends Src env tabs f bid fb F0 oS where
  rel : SRel tabs f g
  wg : ∃ ce, WF ce g
  hgb : g.block? bid = some gb
  spec : BlockSpec tabs f g bid fb gb
  hoT : schedule g gb = some oT
  roots : oT.toList.filter (CSE.rootNode g) =
    ssRoots ((Array.range f.valueTab.size).map (ssSplit? tabs f g))
      (oS.toList.filter (CSE.rootNode f))
  frT : F0T = { F0 with regs := F0T.regs }
  sizeT : F0T.regs.size = g.valueTab.size
  rr : RR f F0.regs F0T.regs

/-- The target's frame after evaluating `done`. -/
structure TFacts (tabs : Tables) (f g : Func) (F0T S T : Frame) (pre done : List ID) : Prop where
  frame : T = { F0T with regs := T.regs }
  size : T.regs.size = F0T.regs.size
  out : ∀ z, z ∉ done → T.regs[z]? = F0T.regs[z]?
  defd : ∀ x ∈ done, ∃ y, T.regs[x]? = some (some y)
  rel : ∀ x ∈ done, x ∈ pre → ∃ yS yT, S.regs[x]? = some (some yS) ∧
    T.regs[x]? = some (some yT) ∧ Sem.Refines yS yT
  off : ∀ x ps (d : SplitD tabs f g x ps), x ∈ pre → ∀ (k : Nat) (p s : ID) (o : Nat) (t : Ty)
    (P : Ptr), ps[k]? = some (p, s) →
    d.fs[k]? = some (o, t) → f.value? p = none → p ∈ done → (rv S d.dst).asPtrWord = some P →
    ∃ yp, T.regs[p]? = some (some yp) ∧ yp.asPtrWord = some (P.add (BitVec.ofNat 64 o))
  store : ∀ x ps (d : SplitD tabs f g x ps), x ∈ pre → ∀ (k : Nat) (p s : ID) (P : Ptr) (M : Mem),
    ps[k]? = some (p, s) →
    s ∈ done → (rv S d.dst).asPtrWord = some P → S.regs[d.mem]? = some (some (.mem M)) →
    ∃ Mk M', M.write P (bufK S d (k + 1)) = some Mk ∧ T.regs[s]? = some (some (.mem M')) ∧
      Mem.Refines Mk M'

variable {env : Env} {tabs : Tables} {f g : Func} {bid : ID} {fb gb : Block} {F0 F0T : Frame}
  {oS oT : Array ID}

namespace Blk

variable (K : Blk env tabs f g bid fb gb F0 F0T oS oT)
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

theorem gvalues : ∃ E : Array ID, gb.values = fb.values ++ E ∧
    ∀ z ∈ E, f.value? z = none ∧ Fresh tabs f g z ∧ ∃ v, g.value? z = some v ∧ v.block = bid :=
  K.spec.values

/-- `g`'s value of a value of `f`: kept, or a split `Store` (its `Copy`). -/
theorem gval {x : ID} {fv : Value} (hfv : f.value? x = some fv) :
    ∃ gv, g.value? x = some gv ∧ (ssSame fv gv = true ∨ ∃ ps, ssSplit? tabs f g x = some ps) :=
  K.rel.value x fv hfv

theorem gval_nonPhi {x : ID} {fv gv : Value} (hfv : f.value? x = some fv)
    (hgv : g.value? x = some gv) (hph : fv.op ≠ .Phi) : gv.op ≠ .Phi := by
  obtain ⟨gv', hgv', h⟩ := K.gval hfv
  rw [hgv] at hgv'; cases hgv'
  rcases h with h | ⟨ps, hs⟩
  · rw [(ssSame_spec h).2.1]; exact hph
  · obtain ⟨d⟩ := ssSplit_spec hs
    rw [d.hgv] at hgv; cases hgv
    rcases d.hmode with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide

/-- A source node is a target node. -/
theorem nodeG {x : ID} (hn : Node f fb x) : Node g gb x := by
  obtain ⟨hx, fv, hfv, hph⟩ := hn
  obtain ⟨E, hE, -⟩ := K.gvalues
  obtain ⟨gv, hgv, -⟩ := K.gval hfv
  exact ⟨by rw [hE]; exact Array.mem_append_left _ hx, gv, hgv, K.gval_nonPhi hfv hgv hph⟩

/-- A target node that is a value of the source is a source node. -/
theorem nodeF {x : ID} (hn : Node g gb x) {fv : Value} (hfv : f.value? x = some fv) :
    Node f fb x := by
  obtain ⟨hx, gv, hgv, hph⟩ := hn
  obtain ⟨E, hE, hEf⟩ := K.gvalues
  rw [hE] at hx
  rcases Array.mem_append.1 hx with hx | hx
  · refine ⟨hx, fv, hfv, fun hp => hph ?_⟩
    obtain ⟨gv', hgv', h⟩ := K.gval hfv
    rw [hgv] at hgv'; cases hgv'
    rcases h with h | ⟨ps, hs⟩
    · rw [(ssSame_spec h).2.1]; exact hp
    · obtain ⟨d⟩ := ssSplit_spec hs
      rw [d.hfv] at hfv; cases hfv
      rw [d.hop] at hp; cases hp
  · rw [(hEf x hx).1] at hfv; cases hfv

/-- A split of a value of the block: listed in it, so a source node. -/
theorem split_node {x : ID} {ps : List (ID × ID)} (d : SplitD tabs f g x ps) (hb : d.fv.block = bid) :
    Node f fb x := by
  obtain ⟨b, hb', hx⟩ := d.hlisted
  rw [hb, K.hfb] at hb'; cases hb'
  exact ⟨hx, d.fv, d.hfv, by rw [d.hop]; decide⟩

/-- A fresh pointer of a split of the block is a target node. -/
theorem fresh_node {x : ID} {ps : List (ID × ID)} (d : SplitD tabs f g x ps) (hb : d.fv.block = bid)
    {k : Nat} {p s : ID} (hk : ps[k]? = some (p, s)) (hpf : f.value? p = none) :
    Node g gb p := by
  have hkl : k < d.fs.length := by
    rw [← d.hlen]; exact (List.getElem?_eq_some_iff.1 hk).1
  obtain ⟨o, t, a, p', s', av, sv, ov, -, -, hk', L⟩ := ssLink_spec (d.hlink k hkl)
  rw [hk] at hk'; cases hk'
  obtain ⟨gb', hgb', hin⟩ := K.rel.listed x ps d.fv d.hsplit d.hfv
  rw [hb, K.hgb] at hgb'; cases hgb'
  have P := L.hoff hpf
  exact ⟨(hin (p, s) (List.mem_of_getElem? hk)).1 hpf, ov, P.hp, by rw [P.hpop]; decide⟩

/-- The stores of a split of the block (fresh, or the split `Store` itself) are target nodes. -/
theorem store_node {x : ID} {ps : List (ID × ID)} (d : SplitD tabs f g x ps) (hb : d.fv.block = bid)
    {k : Nat} {p s : ID} (hk : ps[k]? = some (p, s)) : Node g gb s := by
  have hkl : k < d.fs.length := by
    rw [← d.hlen]; exact (List.getElem?_eq_some_iff.1 hk).1
  obtain ⟨o, t, a, p', s', av, sv, ov, -, -, hk', L⟩ := ssLink_spec (d.hlink k hkl)
  rw [hk] at hk'; cases hk'
  rcases L.hsf with hsf | ⟨rfl, -⟩
  · obtain ⟨gb', hgb', hin⟩ := K.rel.listed x ps d.fv d.hsplit d.hfv
    rw [hb, K.hgb] at hgb'; cases hgb'
    exact ⟨(hin (p, s) (List.mem_of_getElem? hk)).2 hsf, sv, L.hs, by rw [L.hsop]; decide⟩
  · exact K.nodeG (K.split_node d hb)

theorem hLk (k : Nat) : ∀ y ∈ oS.toList.take k, Node f fb y :=
  fun _ hy => K.memS.1 (List.mem_of_mem_take hy)

theorem base_notT {a : ID} (hB : Base f bid a) : a ∉ oT.toList := fun hm => by
  obtain ⟨v, hpl, -, -⟩ := id hB
  exact K.base_not_node hB (K.nodeF (K.memT.1 hm) hpl.1)

/-- **A value from before the block**: refined registers. -/
theorem baseRel {S T : Frame} {k : Nat} {pre done : List ID}
    (hS : SFacts env tabs f F0 S (oS.toList.take k)) (hT : TFacts tabs f g F0T S T pre done)
    (hd : ∀ z ∈ done, z ∈ oT.toList) {a : ID} (hB : Base f bid a) :
    ∃ yS yT, S.regs[a]? = some (some yS) ∧ T.regs[a]? = some (some yT) ∧ Sem.Refines yS yT := by
  obtain ⟨va, yS, hva, hyS, -⟩ := K.base_val hS (K.hLk k) hB
  have h0 : S.regs[a]? = F0.regs[a]? := K.base_reg hB (K.hLk k) hS.out
  obtain ⟨yT, hyT, hr⟩ := K.rr a va yS hva (by rw [← h0]; exact hyS)
  exact ⟨yS, yT, hyS, by rw [hT.out a fun hm => K.base_notT hB (hd a hm)]; exact hyT, hr⟩

theorem n_arg {x : ID} {v : Value} (hx : Base f bid x ∨ Node f fb x) (hv : f.value? x = some v)
    (hph : v.op ≠ .Phi) {a : ID} (ha : a ∈ v.args) : Base f bid a ∨ Node f fb a := by
  rcases hx with hB | ⟨hxb, -⟩
  · exact .inl (K.base_cl hB hv hph ha)
  · exact K.arg_base_or_node hxb hv hph ha

/-- Values from before the block or of it reach only such values through copies. -/
theorem n_copy : ∀ (n : Nat) {a w : ID}, (Base f bid a ∨ Node f fb a) →
    copyReach tabs f.valueTab n a w = true → Base f bid w ∨ Node f fb w
  | 0, a, w, ha, h => by
    simp only [copyReach, beq_iff_eq] at h; subst h; exact ha
  | n + 1, a, w, ha, h => by
    unfold copyReach at h
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact ha
    have hget : ∀ z, Defs.get? f.valueTab z = f.value? z := fun _ => rfl
    rw [hget] at h
    cases hx : f.value? a with
    | none => rw [hx] at h; cases h
    | some x =>
      rw [hx] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨hop, hsz⟩, -⟩, hr⟩ := h
      have hargs : x.args = #[x.args[0]!] := args1 hsz
      generalize hcd : x.args[0]! = c at hr hargs
      have hc0 : c ∈ x.args := by rw [hargs]; simp
      exact n_copy n (K.n_arg ha hx (by rw [hop]; decide) hc0) hr

/-- An argument from before the block or of it has a target register. -/
theorem argDefd {S T : Frame} {k j : Nat} {pre : List ID}
    (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hT : TFacts tabs f g F0T S T pre (oT.toList.take j)) {x : ID} (hjT : oT.toList[j]? = some x)
    {gv : Value} (hgv : g.value? x = some gv) {a : ID} (ha : a ∈ gv.args)
    (hN : Base f bid a ∨ Node g gb a) : ∃ y, T.regs[a]? = some (some y) := by
  rcases hN with hB | hn
  · obtain ⟨-, yT, -, hyT, -⟩ := K.baseRel hS hT (fun z hz => List.mem_of_mem_take hz) hB
    exact ⟨yT, hyT⟩
  · exact hT.defd a (K.topoT hjT hgv ha hn)

/-- An argument the source evaluated: refined registers. -/
theorem argRel {S T : Frame} {k j : Nat}
    (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hT : TFacts tabs f g F0T S T (oS.toList.take k) (oT.toList.take j)) {x : ID}
    (hjT : oT.toList[j]? = some x) {gv : Value} (hgv : g.value? x = some gv) {a : ID}
    (ha : a ∈ gv.args) (hA : Base f bid a ∨ a ∈ oS.toList.take k) :
    ∃ yS yT, S.regs[a]? = some (some yS) ∧ T.regs[a]? = some (some yT) ∧ Sem.Refines yS yT := by
  rcases hA with hB | hp
  · exact K.baseRel hS hT (fun z hz => List.mem_of_mem_take hz) hB
  · exact hT.rel a (K.topoT hjT hgv ha (K.nodeG (K.hLk k a hp))) hp

omit K in
theorem take_succ_eqT {j : Nat} {x : ID} (hj : oT.toList[j]? = some x) :
    oT.toList.take (j + 1) = oT.toList.take j ++ [x] := by
  rw [List.take_add_one, hj]; rfl

/-- **One target step** keeps `TFacts`. -/
theorem tstep {S T : Frame} {pre : List ID} {j : Nat} {x : ID} (hj : oT.toList[j]? = some x)
    (hT : TFacts tabs f g F0T S T pre (oT.toList.take j)) {y : Val}
    (hrel : x ∈ pre → ∃ yS, S.regs[x]? = some (some yS) ∧ Sem.Refines yS y)
    (hoff : ∀ x' ps (d : SplitD tabs f g x' ps), x' ∈ pre → ∀ (k : Nat) (s : ID) (o : Nat)
      (t : Ty) (P : Ptr), ps[k]? = some (x, s) → d.fs[k]? = some (o, t) → f.value? x = none →
      (rv S d.dst).asPtrWord = some P → y.asPtrWord = some (P.add (BitVec.ofNat 64 o)))
    (hstore : ∀ x' ps (d : SplitD tabs f g x' ps), x' ∈ pre → ∀ (k : Nat) (p : ID) (P : Ptr)
      (M : Mem), ps[k]? = some (p, x) → (rv S d.dst).asPtrWord = some P →
      S.regs[d.mem]? = some (some (.mem M)) →
      ∃ Mk M', M.write P (bufK S d (k + 1)) = some Mk ∧ y = .mem M' ∧ Mem.Refines Mk M') :
    TFacts tabs f g F0T S (T.set x y) pre (oT.toList.take (j + 1)) := by
  have hxlt : x < T.regs.size := by
    obtain ⟨-, v, hv, -⟩ := K.memT.1 (List.mem_of_getElem? hj)
    rw [hT.size, K.sizeT]; exact lt_of_value? hv
  have hnot : x ∉ oT.toList.take j := CSE.not_mem_take_of K.ndT hj
  rw [take_succ_eqT hj]
  have hkeep : ∀ z, z ≠ x → (T.set x y).regs[z]? = T.regs[z]? := fun z hz =>
    Frame.set_regs_ne (Ne.symm hz)
  have hself : (T.set x y).regs[x]? = some (some y) := Frame.set_regs_self hxlt
  refine ⟨?_, by simp [Frame.set, hT.size], fun z hz => ?_, fun z hz => ?_, fun z hz hzp => ?_,
    fun x' ps d hx' k p s o t P hk hf hpf hp hP => ?_, fun x' ps d hx' k p s P M hk hs hP hM => ?_⟩
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
  · rcases List.mem_append.1 hp with hp | hp
    · rw [hkeep p (fun h => hnot (h ▸ hp))]; exact hT.off x' ps d hx' k p s o t P hk hf hpf hp hP
    · simp only [List.mem_singleton] at hp; subst hp
      exact ⟨y, hself, hoff x' ps d hx' k s o t P hk hf hpf hP⟩
  · rcases List.mem_append.1 hs with hs | hs
    · rw [hkeep s (fun h => hnot (h ▸ hs))]; exact hT.store x' ps d hx' k p s P M hk hs hP hM
    · simp only [List.mem_singleton] at hs; subst hs
      obtain ⟨Mk, M', h1, rfl, h3⟩ := hstore x' ps d hx' k p P M hk hP hM
      exact ⟨Mk, M', h1, hself, h3⟩

theorem tframe {S T : Frame} {pre done : List ID} {k : Nat}
    (hS : SFacts env tabs f F0 S (oS.toList.take k)) (hT : TFacts tabs f g F0T S T pre done) :
    T = { S with regs := T.regs } :=
  calc T = { F0T with regs := T.regs } := hT.frame
    _ = { F0 with regs := T.regs } := by rw [K.frT]
    _ = { S with regs := T.regs } := by rw [hS.frame]

/-- **A kept value** evaluates to a refinement of the source's on refined arguments. -/
theorem keptRes (hE : env.Mono) {S T : Frame} {k j : Nat}
    (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hT : TFacts tabs f g F0T S T (oS.toList.take k) (oT.toList.take j)) {x : ID}
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
    (hT : TFacts tabs f g F0T S T (oS.toList.take k) (oT.toList.take j)) {x : ID}
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

/-- The arguments of a split's `StructMake` are available. -/
theorem fieldA {S : Frame} {k : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k)) {x : ID}
    {ps : List (ID × ID)} (d : SplitD tabs f g x ps) (hx : x ∈ oS.toList.take k) {a : ID}
    (ha : a ∈ d.smv.args) : Base f bid a ∨ a ∈ oS.toList.take k := by
  have H := K.avail hS
  have hT := K.typedS hS (K.hLk k)
  have hsmA := H.cl x d.fv (.inr hx) d.hfv (by rw [d.hop]; decide) d.sm (by rw [d.hfargs]; simp)
  obtain ⟨hA1, -⟩ := copy_reg H hT K.hidA _ hsmA (copyReach_copyEnd f.valueTab _ d.sm)
  exact H.cl _ d.smv hA1 d.hsmv (make_ne_phi d.hsmop) a ha

end Blk

theorem bufK_zero (S : Frame) {x : ID} {ps : List (ID × ID)} (d : SplitD tabs f g x ps) :
    bufK S d 0 = Array.replicate d.n .poison := by
  simp [bufK, encodeFields]

theorem bufK_size (S : Frame) {x : ID} {ps : List (ID × ID)} (d : SplitD tabs f g x ps) (j : Nat) :
    (bufK S d j).size = d.n := by
  simp [bufK, Sem.encodeFields_size]

theorem bufK_full (S : Frame) {x : ID} {ps : List (ID × ID)} (d : SplitD tabs f g x ps) :
    bufK S d ps.length = encode (.agg d.fs d.n) (.agg (d.smv.args.toList.map (rv S))) := by
  have h1 : (d.smv.args.toList.map (rv S)).length = d.fs.length := by simp [d.hsmsz]
  simp only [bufK, encode, d.hlen]
  rw [List.take_of_length_le (Nat.le_refl _), List.take_of_length_le (Nat.le_of_eq h1)]

theorem bufK_succ (S : Frame) {x : ID} {ps : List (ID × ID)} (d : SplitD tabs f g x ps) {k o : Nat}
    {t : Ty} {a : ID} (hf : d.fs[k]? = some (o, t)) (ha : d.smv.args[k]? = some a) :
    bufK S d (k + 1) = putBytes (bufK S d k) o (encode t (rv S a)) :=
  encodeFields_take_succ k _ _ _ o t _ hf (by
    rw [List.getElem?_map, Array.getElem?_toList, ha]; rfl)

theorem prevId_eq (ps : List (ID × ID)) (m0 : ID) (k : Nat) :
    (if k = 0 then m0 else (ps[k - 1]?.map (·.2)).getD 0) = prevId ps m0 k := by
  cases k <;> simp [prevId]

theorem getLast_prevId (ps : List (ID × ID)) (m0 : ID) :
    (ps.getLast?.map (·.2)).getD m0 = prevId ps m0 ps.length := by
  cases hl : ps.length with
  | zero => rw [List.length_eq_zero_iff.1 hl]; rfl
  | succ n =>
    have hn : n < ps.length := by omega
    rw [List.getLast?_eq_getElem?, hl, show n + 1 - 1 = n by omega,
      List.getElem?_eq_getElem hn]
    simp [prevId, List.getElem?_eq_getElem hn]

theorem link_at {x : ID} {ps : List (ID × ID)} (d : SplitD tabs f g x ps) {k : Nat} {p s : ID}
    (hk : ps[k]? = some (p, s)) : ∃ o t a av sv ov, d.fs[k]? = some (o, t) ∧
      d.smv.args[k]? = some a ∧ Link tabs f g d.fv.block d.dst x ps d.m0 k o t a p s av sv ov := by
  have hkl : k < d.fs.length := by rw [← d.hlen]; exact (List.getElem?_eq_some_iff.1 hk).1
  obtain ⟨o, t, a, p', s', av, sv, ov, hf, ha, hk', L⟩ := ssLink_spec (d.hlink k hkl)
  rw [hk] at hk'; cases hk'
  exact ⟨o, t, a, av, sv, ov, hf, ha, L⟩

/-- A non-root value that is not an argument lookup evaluates once its arguments have
registers. -/
theorem pureEval {T : Frame} {gv : Value} (hdef : ∀ a ∈ gv.args, ∃ y, T.regs[a]? = some (some y))
    (hr : isRoot gv.op = false) (ha : gv.op ≠ .Arg) (hb : gv.op ≠ .ArgIntReg) :
    ∃ y, evalValue env (Ctx.make tabs g) T gv = .ok y := by
  obtain ⟨vs, hvs⟩ := CSE.argVals_some (fr := T) (as := gv.args) hdef
  obtain ⟨r, hr'⟩ := CSE.evalOp_total (env := env) (ctx := Ctx.make tabs g) (fr := T) (argv := vs)
    (ty := (Ctx.make tabs g).tys[gv.id]?.getD .other) (v := gv) hr ha hb
  exact ⟨_, by rw [CSE.evalValue_of_argVals hvs, hr']; rfl⟩

theorem ofInt_ofNat (o : Nat) : BitVec.ofInt 64 (Int64.ofNat o).toInt = BitVec.ofNat 64 o := by
  rw [← Int64.toInt_toBitVec, BitVec.ofInt_toInt]; simp

/-- **A field store's evaluation**: on its field's address, a refinement of the field's value
and a memory refining the struct write with the fields before it, a memory refining the struct
write with one field more. -/
theorem store_val {S T : Frame} {x : ID} {ps : List (ID × ID)} (d : SplitD tabs f g x ps)
    {k o : Nat} {t : Ty} {a p s : ID} {av sv ov : Value}
    (hfk : d.fs[k]? = some (o, t)) (hak : d.smv.args[k]? = some a)
    (L : Link tabs f g d.fv.block d.dst x ps d.m0 k o t a p s av sv ov) {P : Ptr} {M Mk M' : Mem}
    {yp : Val} (hp : T.regs[p]? = some (some yp))
    (hyp : yp.asPtrWord = some (P.add (BitVec.ofNat 64 o)))
    {vT : Val} (hw : T.regs[sv.args[1]!]? = some (some vT)) (hwr : Sem.Refines (rv S a) vT)
    (hpk : M.write P (bufK S d k) = some Mk)
    (hpT : T.regs[prevId ps d.m0 k]? = some (some (.mem M'))) (hpr : Mem.Refines Mk M') :
    ∃ M2 M2', evalValue env (Ctx.make tabs g) T sv = .ok (.mem M2') ∧
      M.write P (bufK S d (k + 1)) = some M2 ∧ Mem.Refines M2 M2' := by
  have hlay := layoutsOK_in d.hlay (o, t) (List.mem_of_getElem? hfk)
  rw [bufK_succ S d hfk hak]
  obtain ⟨M2, hw1, hw2⟩ := write_putBytes hpk (E := encode t (rv S a)) (o := o)
    (by rw [Sem.encode_size, bufK_size]; exact hlay)
  obtain ⟨M2', hwT, hr⟩ := hpr.write (encode_mono t hwr) hw1
  refine ⟨M2, M2', ?_, hw2, hr⟩
  have hargs := L.hsargs
  rw [prevId_eq] at hargs
  generalize hwid : sv.args[1]! = w at hargs hw
  have hreg : ∀ b ∈ sv.args, Reg T b := fun b hb => by
    rw [hargs] at hb
    simp only [List.mem_toArray, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact ⟨_, hp⟩
    · exact ⟨_, hw⟩
    · exact ⟨_, hpT⟩
  rw [evalValue_of_regs hreg, CSE.Mem.evalOp_memRoot (.inl L.hsop), hargs]
  simp only [List.map_toArray, List.map_cons, List.map_nil, AtomSim.rv_of hp, AtomSim.rv_of hw,
    AtomSim.rv_of hpT]
  have hm : memRoot (Ctx.make tabs g) sv [yp, vT, .mem M'] = .ok (.mem M2') := by
    unfold memRoot
    rw [L.hsop]
    simp only [hyp, writeRes]
    rw [show auxTy (Ctx.make tabs g).tabs sv.aux = t from L.hsty, hwT]
  rw [hm, L.hsid, tys_of_value L.hs, L.hsmem]
  rfl

end GoFV.Proof.StructStore

namespace GoFV.Proof.StructStore

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Proof.CopyElim GoFV.Opt GoFV.Opt.RewriteCheck
open GoFV.Proof.CSE (Base Node SFacts)
open GoFV.Proof.CSE.Mem (Avail)
open GoFV.Proof.AtomSim (Reg rv evalValue_of_regs regs_of_ok evalOp_term)

variable {env : Env} {tabs : Tables} {f g : Func} {bid : ID} {fb gb : Block} {F0 F0T : Frame}
  {oS oT : Array ID}

theorem ssRoots_append (S : Array (Option (List (ID × ID)))) (A B : List ID) :
    ssRoots S (A ++ B) = ssRoots S A ++ ssRoots S B := by
  simp [ssRoots, List.flatMap_append]

theorem ssRoots_cons_none (S : Array (Option (List (ID × ID)))) {r : ID} (B : List ID)
    (h : S[r]?.join = none) : ssRoots S (r :: B) = r :: ssRoots S B := by
  simp [ssRoots, List.flatMap_cons, h]

theorem mem_ssRoots {S : Array (Option (List (ID × ID)))} {L : List ID} {z : ID}
    (h : z ∈ ssRoots S L) : z ∈ L ∨ ∃ y ps, y ∈ L ∧ S[y]?.join = some ps ∧ ∃ q ∈ ps, q.2 = z := by
  unfold ssRoots at h
  obtain ⟨y, hy, hz⟩ := List.mem_flatMap.1 h
  cases hs : S[y]?.join with
  | none =>
    simp only [hs, List.mem_singleton] at hz
    subst hz; exact .inl hy
  | some ps =>
    simp only [hs, List.mem_map] at hz
    obtain ⟨q, hq, rfl⟩ := hz
    exact .inr ⟨y, ps, hy, hs, q, hq, rfl⟩

theorem tfacts_zero {S : Frame} {pre : List ID} :
    TFacts tabs f g F0T S F0T pre (oT.toList.take 0) := by
  refine ⟨rfl, rfl, fun _ _ => rfl, fun _ h => by simp at h, fun _ h => by simp at h, ?_, ?_⟩
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ hp _; simp at hp
  · intro _ _ _ _ _ _ _ _ _ _ hs _ _; simp at hs

namespace Blk

variable (K : Blk env tabs f g bid fb gb F0 F0T oS oT)
include K

theorem split_block {x : ID} {ps : List (ID × ID)} (d : SplitD tabs f g x ps) (hx : x ∈ fb.values) :
    d.fv.block = bid := by
  obtain ⟨v, hv, -, hb⟩ := K.valueIn hx
  rw [d.hfv] at hv; cases hv; exact hb

/-- **The last field store of a split** the source evaluated (an argument of the target's value
`x`): a memory refining the struct write with the fields up to it. -/
theorem prevInv_succ {S T : Frame} {k j : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hT : TFacts tabs f g F0T S T (oS.toList.take k) (oT.toList.take j)) {x : ID}
    (hjT : oT.toList[j]? = some x) {gv : Value} (hgv : g.value? x = some gv) {x' : ID}
    {ps : List (ID × ID)} (d : SplitD tabs f g x' ps) (hx' : x' ∈ oS.toList.take k) {i : Nat}
    (hil : i < ps.length) (harg : prevId ps d.m0 (i + 1) ∈ gv.args) {P : Ptr} {M : Mem}
    (hP : (rv S d.dst).asPtrWord = some P) (hM : S.regs[d.mem]? = some (some (.mem M))) :
    ∃ Mk M', M.write P (bufK S d (i + 1)) = some Mk ∧
      T.regs[prevId ps d.m0 (i + 1)]? = some (some (.mem M')) ∧ Mem.Refines Mk M' := by
  obtain ⟨⟨p, s⟩, hq⟩ : ∃ q, ps[i]? = some q := ⟨_, List.getElem?_eq_getElem hil⟩
  have hpid : prevId ps d.m0 (i + 1) = s := by simp [prevId, hq]
  rw [hpid] at harg ⊢
  have hb := K.split_block d (K.hLk k x' hx').1
  have hsT := K.topoT hjT hgv harg (K.store_node d hb hq)
  exact hT.store x' ps d hx' i p s P M hq hsT hP hM

/-- **The memory before a field store** (or the split's `Copy`) refines the struct write with the
fields before it. -/
theorem prevInv {S T : Frame} {k j : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hT : TFacts tabs f g F0T S T (oS.toList.take k) (oT.toList.take j)) {x : ID}
    (hjT : oT.toList[j]? = some x) {gv : Value} (hgv : g.value? x = some gv) {x' : ID}
    {ps : List (ID × ID)} (d : SplitD tabs f g x' ps) (hx' : x' ∈ oS.toList.take k) {i : Nat}
    (hi : i ≤ ps.length) (harg : prevId ps d.m0 i ∈ gv.args) {P : Ptr} {M MS : Mem}
    (hP : (rv S d.dst).asPtrWord = some P) (hM : S.regs[d.mem]? = some (some (.mem M)))
    (hMS : M.write P (encode (.agg d.fs d.n) (.agg (d.smv.args.toList.map (rv S)))) = some MS) :
    ∃ Mk M', M.write P (bufK S d i) = some Mk ∧
      T.regs[prevId ps d.m0 i]? = some (some (.mem M')) ∧ Mem.Refines Mk M' := by
  cases i with
  | zero =>
    change d.m0 ∈ gv.args at harg
    show ∃ Mk M', M.write P (bufK S d 0) = some Mk ∧ T.regs[d.m0]? = some (some (.mem M')) ∧
      Mem.Refines Mk M'
    have H := K.avail hS
    have hTy := K.typedS hS (K.hLk k)
    have hmA := H.cl x' d.fv (.inr hx') d.hfv (by rw [d.hop]; decide) d.mem
      (by rw [d.hfargs]; simp)
    -- the chain's start holds a memory refining the split `Store`'s
    obtain ⟨M', h2, hMM⟩ : ∃ M', T.regs[d.m0]? = some (some (.mem M')) ∧ Mem.Refines M M' := by
      obtain ⟨hA0, hr0⟩ := copy_reg H hTy K.hidA _ hmA d.hm0
      obtain ⟨yS, yT, h1, h2, h3⟩ := K.argRel hS hT hjT hgv harg hA0
      rw [hr0, hM] at h1; cases h1
      cases h3 with
      | mem hMM => exact ⟨_, h2, hMM⟩
    obtain ⟨MB, hMB⟩ := write_size_congr hMS (bs' := Array.replicate d.n .poison)
      (by rw [Sem.encode_size]; simp [Ty.size])
    exact ⟨MB, _, by rw [bufK_zero]; exact hMB, h2, write_poison_left hMM hMB⟩
  | succ i => exact K.prevInv_succ hS hT hjT hgv d hx' (by omega) harg hP hM

/-- **A fresh `OffPtr`** of a split the source evaluated: a word of its field's address. -/
theorem offVal {S T : Frame} {k j : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hT : TFacts tabs f g F0T S T (oS.toList.take k) (oT.toList.take j)) {x : ID}
    (hjT : oT.toList[j]? = some x) {x' : ID} {ps : List (ID × ID)} (d : SplitD tabs f g x' ps)
    (hx' : x' ∈ oS.toList.take k) {i o : Nat} {t : Ty} {ov : Value}
    (hfi : d.fs[i]? = some (o, t)) (L : POff tabs f g d.fv.block d.dst x o ov)
    {P : Ptr} (hP : (rv S d.dst).asPtrWord = some P) :
    ∃ y, evalValue env (Ctx.make tabs g) T ov = .ok y ∧
      y.asPtrWord = some (P.add (BitVec.ofNat 64 o)) := by
  obtain ⟨P', M, MS, -, hP', -, hMS, -, -⟩ := K.split_src hS d hx'
  rw [hP] at hP'; cases hP'
  have H := K.avail hS
  have hTy := K.typedS hS (K.hLk k)
  have hdA := H.cl x' d.fv (.inr hx') d.hfv (by rw [d.hop]; decide) d.dst (by rw [d.hfargs]; simp)
  have hargs := L.hpargs
  have hdst := L.hdst
  generalize hd' : ov.args[0]! = d' at hargs hdst
  obtain ⟨hA, hr⟩ := copy_reg H hTy K.hidA _ hdA hdst
  obtain ⟨yS, yT, h1, h2, h3⟩ := K.argRel hS hT hjT L.hp (by rw [hargs]; simp) hA
  rw [hr] at h1
  have hyT : yT.asPtrWord = some P := h3.asPtrWord (by rw [← AtomSim.rv_of h1]; exact hP)
  have hreg : ∀ b ∈ ov.args, Reg T b := fun b hb => by
    rw [hargs] at hb; simp only [List.mem_toArray, List.mem_singleton] at hb; subst hb
    exact ⟨_, h2⟩
  have hlt : o < (encode (.agg d.fs d.n) (.agg (d.smv.args.toList.map (rv S)))).size := by
    rw [Sem.encode_size]; simp only [Ty.size]; exact d.hlt (o, t) (List.mem_of_getElem? hfi)
  rw [evalValue_of_regs hreg, evalOp_term (by rw [L.hpop]; decide),
    GoFV.Proof.Rules.opVal_pure (by rw [L.hpop]; decide), L.hpop, evalPure_offPtr, hargs]
  simp only [List.map_toArray, List.map_cons, List.map_nil, AtomSim.rv_of h2]
  rw [L.hpid, tys_of_value L.hp]
  refine ⟨_, rfl, ?_⟩
  have hpt := L.hpty
  generalize tabs.ty ov.type = ty at hpt ⊢
  cases ty <;> simp [isPtrTy] at hpt
  rw [Option.getD_some, Val.asPtrWord_retype_ptr, PtrOps.offPtr_asPtrWord, hyT, Option.bind_some,
    L.hpai, ofInt_ofNat, Ptr.step?, if_pos (inWindow_of_write hMS hlt)]

/-- **A fresh field store** of a split the source evaluated: a memory refining the struct write
with the fields up to it. -/
theorem storeAt {S T : Frame} {k j : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hT : TFacts tabs f g F0T S T (oS.toList.take k) (oT.toList.take j)) {x : ID}
    (hjT : oT.toList[j]? = some x) {x' : ID} {ps : List (ID × ID)} (d : SplitD tabs f g x' ps)
    (hx' : x' ∈ oS.toList.take k) {i : Nat} {p : ID} (hi : ps[i]? = some (p, x)) {P : Ptr}
    {M : Mem} (hP : (rv S d.dst).asPtrWord = some P)
    (hM : S.regs[d.mem]? = some (some (.mem M))) :
    ∃ sv M2 M2', g.value? x = some sv ∧ evalValue env (Ctx.make tabs g) T sv = .ok (.mem M2') ∧
      M.write P (bufK S d (i + 1)) = some M2 ∧ Mem.Refines M2 M2' := by
  obtain ⟨P', M0, MS, -, hP', hM', hMS, -, -⟩ := K.split_src hS d hx'
  rw [hP] at hP'; cases hP'
  rw [hM] at hM'; cases hM'
  obtain ⟨o, t, a, av, sv, ov, hfi, hai, L⟩ := link_at d hi
  have hb := K.split_block d (K.hLk k x' hx').1
  have hil : i < ps.length := (List.getElem?_eq_some_iff.1 hi).1
  have hargs := L.hsargs
  rw [prevId_eq] at hargs
  have hpm : p ∈ sv.args := by rw [hargs]; simp
  have H := K.avail hS
  have hTy := K.typedS hS (K.hLk k)
  -- the field's pointer: a fresh `OffPtr`, or (offset `0`) `dst` itself through copies
  have hp : ∃ yp, T.regs[p]? = some (some yp) ∧
      yp.asPtrWord = some (P.add (BitVec.ofNat 64 o)) := by
    cases hpf : f.value? p with
    | none =>
      exact hT.off x' ps d hx' i p x o t P hi hfi hpf
        (K.topoT hjT L.hs hpm (K.fresh_node d hb hi hpf)) hP
    | some pv =>
      obtain ⟨ho, hdp⟩ := L.hold (by rw [hpf]; rfl)
      subst ho
      have hdA := H.cl x' d.fv (.inr hx') d.hfv (by rw [d.hop]; decide) d.dst
        (by rw [d.hfargs]; simp)
      obtain ⟨hpA, hrp⟩ := copy_reg H hTy K.hidA _ hdA hdp
      obtain ⟨yS, yT, h1, h2, h3⟩ := K.argRel hS hT hjT L.hs hpm hpA
      rw [hrp] at h1
      refine ⟨yT, h2, ?_⟩
      rw [GoFV.Proof.MemCombine.Ptr.add_zero]
      exact h3.asPtrWord (by rw [← AtomSim.rv_of h1]; exact hP)
  obtain ⟨yp, hp, hyp⟩ := hp
  have haA := K.fieldA hS d hx' (Array.mem_of_getElem? hai)
  obtain ⟨hwA, hwr⟩ := copy_reg H hTy K.hidA _ haA L.hw
  have hwm : sv.args[1]! ∈ sv.args := by rw [hargs]; simp
  obtain ⟨yS, yT, h1, h2, h3⟩ := K.argRel hS hT hjT L.hs hwm hwA
  rw [hwr] at h1
  have hra : rv S a = yS := AtomSim.rv_of h1
  obtain ⟨Mk, M', hk1, hk2, hk3⟩ := K.prevInv hS hT hjT L.hs d hx' (Nat.le_of_lt hil)
    (by rw [hargs]; simp) hP hM hMS
  obtain ⟨M2, M2', he, hw2, hr2⟩ :=
    store_val d hfi hai L hp hyp h2 (by rw [hra]; exact h3) hk1 hk2 hk3
  exact ⟨sv, M2, M2', L.hs, he, hw2, hr2⟩

/-- **A split the source evaluated**: its `Copy` holds a memory refining the struct write. -/
theorem splitOk {S T : Frame} {k j : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hT : TFacts tabs f g F0T S T (oS.toList.take k) (oT.toList.take j)) {x : ID}
    (hjT : oT.toList[j]? = some x) (hxS : x ∈ oS.toList.take k) {ps : List (ID × ID)}
    (d : SplitD tabs f g x ps) :
    ∃ y, evalValue env (Ctx.make tabs g) T d.gv = .ok y ∧
      ∃ yS, S.regs[x]? = some (some yS) ∧ Sem.Refines yS y := by
  obtain ⟨P, M, MS, MS0, hP, hM, hMS, hR0, hx⟩ := K.split_src hS d hxS
  rcases d.hmode with ⟨hgop, hga⟩ | ⟨hgst, hlx⟩
  · have hlast : d.gv.args = #[prevId ps d.m0 ps.length] := by rw [hga, getLast_prevId]
    obtain ⟨Mk, M', h1, h2, h3⟩ := K.prevInv hS hT hjT d.hgv d hxS (Nat.le_refl _)
      (by rw [hlast]; simp) hP hM hMS
    rw [bufK_full, hMS] at h1
    cases h1
    refine ⟨_, evalValue_copy hgop hlast h2, _, hx, ?_⟩
    rw [d.hgid, tys_of_value d.hgv, d.hgty]
    exact retype_mono _ (.mem (hR0.trans h3))
  · -- in place: `x` is the chain's last store
    rw [List.getLast?_eq_getElem?, Option.map_eq_some_iff] at hlx
    obtain ⟨⟨p, x''⟩, hq, rfl⟩ := hlx
    have hil : ps.length - 1 < ps.length := (List.getElem?_eq_some_iff.1 hq).1
    obtain ⟨sv, M2, M2', hsv, he, hw2, hr2⟩ := K.storeAt hS hT hjT d hxS hq hP hM
    rw [d.hgv] at hsv; cases hsv
    rw [show ps.length - 1 + 1 = ps.length by omega, bufK_full, hMS] at hw2
    cases hw2
    obtain ⟨o, t, a, av, sv', ov, -, -, L⟩ := link_at d hq
    have hsv' : sv' = d.gv := by
      have h1 := L.hs
      have h2 := d.hgv
      simp only at h2
      rw [h2] at h1; cases h1; rfl
    have hmem : tabs.ty d.fv.type = .mem := by
      have := L.hsmem
      rw [hsv', d.hgty] at this
      exact this
    refine ⟨_, he, _, hx, ?_⟩
    rw [hmem]
    exact .mem (hR0.trans hr2)

/-- A split the source did not evaluate: its `Copy` evaluates. -/
theorem splitPure {S T : Frame} {k j : Nat} {pre : List ID}
    (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hT : TFacts tabs f g F0T S T pre (oT.toList.take j)) {x : ID}
    (hjT : oT.toList[j]? = some x) {ps : List (ID × ID)} (d : SplitD tabs f g x ps)
    (hgop : d.gv.op = .Copy) :
    ∃ y, evalValue env (Ctx.make tabs g) T d.gv = .ok y := by
  have hlast : d.gv.args = #[prevId ps d.m0 ps.length] := by
    rcases d.hmode with ⟨-, h⟩ | ⟨h, -⟩
    · rw [h, getLast_prevId]
    · rw [hgop] at h; cases h
  have hxF : Node f fb x := K.nodeF (K.memT.1 (List.mem_of_getElem? hjT)) d.hfv
  have hb := K.split_block d hxF.1
  have harg : prevId ps d.m0 ps.length ∈ d.gv.args := by rw [hlast]; simp
  obtain ⟨y, hy⟩ : ∃ y, T.regs[prevId ps d.m0 ps.length]? = some (some y) := by
    cases hl : ps.length with
    | zero =>
      rw [hl] at harg
      change d.m0 ∈ d.gv.args at harg
      show ∃ y, T.regs[d.m0]? = some (some y)
      have hmN := K.n_arg (.inr hxF) d.hfv (by rw [d.hop]; decide)
        (show d.mem ∈ d.fv.args by rw [d.hfargs]; simp)
      rcases K.n_copy _ hmN d.hm0 with h | h
      · exact K.argDefd hS hT hjT d.hgv harg (.inl h)
      · exact K.argDefd hS hT hjT d.hgv harg (.inr (K.nodeG h))
    | succ n =>
      rw [hl] at harg
      have hn : n < ps.length := by omega
      obtain ⟨⟨p, s⟩, hq⟩ : ∃ q, ps[n]? = some q := ⟨_, List.getElem?_eq_getElem hn⟩
      have hpid : prevId ps d.m0 (n + 1) = s := by simp [prevId, hq]
      rw [hpid] at harg ⊢
      exact K.argDefd hS hT hjT d.hgv harg (.inr (K.store_node d hb hq))
  exact ⟨_, evalValue_copy hgop hlast hy⟩

end Blk

end GoFV.Proof.StructStore

import GoFV.Proof.Pass.StructStoreRel
import GoFV.Proof.Pass.StructStoreMem
import GoFV.Proof.Pass.DSEBlock
import GoFV.Proof.AtomSimStep
import GoFV.Proof.Pass.RewriteTermDen

/-!
# Struct-store splits: the source side of a block (issue #151)

`Src`: a tree block `bid` of the source entered after its `Phi`s with frame `F0` (lemma (D) for
the strict ancestors, the `Phi`s defined, every register typed). In a source frame `S` that
evaluated a prefix of the schedule, the values from before the block and the prefix hold their
evaluation (`avail`, `CSE.Mem.Avail`) and are typed (`typedS`); a value reached from one of them
through copies (`copyReach`) has its register (`copy_reg`). A split `Store` the source evaluated
wrote the `StructMake`'s argument registers at the fields of the struct (`split_src`).
-/

namespace GoFV.Proof.StructStore

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Proof.CopyElim GoFV.Opt GoFV.Opt.RewriteCheck
open GoFV.Proof.CSE (Base Node SFacts)
open GoFV.Proof.CSE.Mem (Avail)
open GoFV.Proof.AtomSim (Reg rv evalValue_of_regs regs_of_ok evalOp_term)

/-- The source side of one tree block's evaluation, after its `Phi`s. -/
structure Src (env : Env) (tabs : Tables) (f : Func) (bid : ID) (fb : Block) (F0 : Frame)
    (oS : Array ID) : Prop where
  wf : ∃ ce, WF ce f
  cf : CertOK f
  tree : Tree f bid
  hfb : f.block? bid = some fb
  size : F0.regs.size = f.valueTab.size
  dinv : DInv env (Ctx.make tabs f) (fun a => Anc (make f) a bid ∧ a ≠ bid) F0
  phiDef : ∀ z ∈ fb.values, ∀ v, f.value? z = some v → v.op = .Phi →
    ∃ y, F0.regs[z]? = some (some y)
  typed : Proof.Typed (Ctx.make tabs f) F0
  hoS : schedule f fb = some oS

variable {env : Env} {tabs : Tables} {f : Func} {bid : ID} {fb : Block} {F0 : Frame}
  {oS : Array ID}

namespace Src

variable (K : Src env tabs f bid fb F0 oS)
include K

theorem hp : parentsOK (make f) f.entry = true := K.cf.parents

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

theorem memS {x : ID} : x ∈ oS.toList ↔ Node f fb x := (schedule_topo K.ownF K.ndF K.hoS).2.2 x

theorem ndS : oS.toList.Nodup := (schedule_topo K.ownF K.ndF K.hoS).1

theorem topoS {j : Nat} {x : ID} (hj : oS.toList[j]? = some x) {v : Value}
    (hv : f.value? x = some v) {a : ID} (ha : a ∈ v.args) (hn : Node f fb a) :
    ∃ i < j, oS.toList[i]? = some a := by
  have hs := (schedule_spec K.hoS).topo
  have hx : Node f fb x := K.memS.1 (List.mem_of_getElem? hj)
  obtain ⟨hxb, v', hv', hph⟩ := hx
  rw [hv] at hv'; cases hv'
  refine hs.before j x hj a ?_ ((nodeIn_schedNodes K.ownF).2 hn)
  rw [argsOf_schedNodes K.ownF K.ndF hxb hv hph]; exact Array.mem_toList_iff.2 ha

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
    Avail env tabs f S (fun a => Base f bid a ∨ a ∈ oS.toList.take k) := by
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

theorem sfacts {pre : List ID} {G : Frame} (hpre : ∃ post, oS.toList = pre ++ post)
    (h : evalAll env (Ctx.make tabs f) F0 pre = .ok G) : SFacts env tabs f F0 G pre := by
  obtain ⟨post, hpost⟩ := hpre
  obtain ⟨ond, otopo, -⟩ := schedule_topo K.ownF K.ndF K.hoS
  rw [hpost] at ond otopo
  obtain ⟨e1, e2, e3, e4⟩ := evalAll_spec (List.nodup_append.1 ond).1
    (topoRem_append_left otopo) (by rw [K.size]; rfl) h
  exact ⟨e1, e2, e3, e4⟩

/-- The source's registers stay typed. -/
theorem typedS {S : Frame} {pre : List ID} (hS : SFacts env tabs f F0 S pre)
    (hL : ∀ y ∈ pre, Node f fb y) : Proof.Typed (Ctx.make tabs f) S := by
  intro z y hz
  by_cases hzp : z ∈ pre
  · obtain ⟨v, y', hv, hy', hev⟩ := hS.eval z hzp
    rw [hz] at hy'; cases hy'
    have := evalValue_typed hev
    obtain ⟨hzb, -⟩ := hL z hzp
    obtain ⟨v', hv', hid, -⟩ := K.valueIn hzb
    rw [hv] at hv'; cases hv'
    rwa [hid] at this
  · rw [hS.out z hzp] at hz
    exact K.typed z y hz

end Src

/-! ## Copies -/

theorem evalPure_copy (ty : Ty) (ai : Int64) (ax : Option AuxRef) (x : Val) :
    evalPure .Copy ty ai ax [x] = x := rfl

theorem evalPure_structMake (ty : Ty) (ai : Int64) (ax : Option AuxRef) (xs : List Val) :
    evalPure .StructMake ty ai ax xs = .agg xs := rfl

theorem evalPure_offPtr (ty : Ty) (ai : Int64) (ax : Option AuxRef) (xs : List Val) :
    evalPure .OffPtr ty ai ax xs = PtrOps.offPtr ai xs := rfl

theorem retype_ptr_indep {v : Val} {e e' : Option Nat} (h : v.retype (.ptr e) = v) :
    v.retype (.ptr e') = v := by
  cases v with
  | int w x => cases w <;> simp [Val.retype] at h
  | _ => simp_all [Val.retype]

theorem copyReach_copyEnd (M : Defs) : ∀ (n : Nat) (a : ID),
    copyReach tabs M n a (copyEnd tabs M n a) = true
  | 0, a => by simp [copyReach, copyEnd]
  | n + 1, a => by
    unfold copyEnd copyReach
    cases hx : M.get? a with
    | none => simp
    | some x =>
      simp only
      generalize hc : (x.op == .Copy && x.args.size == 1 &&
          (match M.get? x.args[0]! with
            | some y => copyCompat (tabs.ty x.type) (tabs.ty y.type)
            | none => false)) = c
      cases c with
      | true =>
        simp [copyReach_copyEnd M n]
      | false => simp

/-- **A value reached through copies** holds the register of the value it is reached from. -/
theorem copy_reg {S : Frame} {A : ID → Prop} (H : Avail env tabs f S A)
    (hT : Proof.Typed (Ctx.make tabs f) S) (hid : ∀ z v, A z → f.value? z = some v → v.id = z) :
    ∀ (n : Nat) {a w : ID}, A a → copyReach tabs f.valueTab n a w = true →
      A w ∧ S.regs[w]? = S.regs[a]?
  | 0, a, w, ha, h => by
    simp only [copyReach, beq_iff_eq] at h; subst h; exact ⟨ha, rfl⟩
  | n + 1, a, w, ha, h => by
    unfold copyReach at h
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact ⟨ha, rfl⟩
    have hget : ∀ z, Defs.get? f.valueTab z = f.value? z := fun _ => rfl
    rw [hget] at h
    cases hx : f.value? a with
    | none => rw [hx] at h; cases h
    | some x =>
      rw [hx] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨hop, hsz⟩, hc⟩, hr⟩ := h
      have hargs : x.args = #[x.args[0]!] := args1 hsz
      generalize hcd : x.args[0]! = c at hc hr hargs
      have hc0 : c ∈ x.args := by rw [hargs]; simp
      have hA0 := H.cl a x ha hx (by rw [hop]; decide) _ hc0
      obtain ⟨ih1, ih2⟩ := copy_reg H hT hid n hA0 hr
      refine ⟨ih1, ih2.trans ?_⟩
      rw [hget] at hc
      cases hy : f.value? c with
      | none => rw [hy] at hc; cases hc
      | some yv =>
        rw [hy] at hc
        obtain ⟨x', ya, hx', hya, hev⟩ := H.val a ha
        rw [hx] at hx'; cases hx'
        obtain ⟨-, yc, -, hyc, -⟩ := H.val _ hA0
        have hev := hev (by rw [hop]; decide)
        rw [evalValue_of_regs (fun b hb => by
          rw [hargs] at hb; simp at hb; subst hb; exact ⟨yc, hyc⟩), evalOp_copy hop] at hev
        have hrv : (x.args.toList.map (rv S)) = [yc] := by
          rw [hargs]; simp [rv, hyc]
        rw [hrv, hid a x ha hx, tys_of_value hx] at hev
        rw [Option.getD_some, evalPure_copy] at hev
        simp only [pure, Res.bind, bind] at hev
        cases hev
        rw [hyc, hya]
        have htc := hT _ yc hyc
        rw [tys_of_value hy, Option.getD_some] at htc
        unfold copyCompat at hc
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hc
        rcases hc with hc | ⟨h1, h2⟩
        · rw [GoFV.Proof.Pass.Rewrite.tyEq_sound hc, htc]
        · revert h1 h2
          cases hs : tabs.ty x.type <;> cases ht : tabs.ty yv.type <;> intro h1 h2 <;>
            simp_all
          rw [retype_ptr_indep htc]

/-! ## Evaluations of the ops of a split -/

theorem memRoot_store_ok {ctx : Ctx} {v : Value} (hop : v.op = .Store) {a b c r : Val}
    (h : memRoot ctx v [a, b, c] = .ok r) :
    ∃ P M M', a = .ptr P ∧ c = .mem M ∧ M.write P (encode (auxTy ctx.tabs v.aux) b) = some M' ∧
      r = .mem M' := by
  unfold memRoot at h
  rw [hop] at h
  cases a <;> cases c <;> simp only at h <;> try (split at h <;> cases h)
  rename_i P M
  cases hw : M.write P (encode (auxTy ctx.tabs v.aux) b) with
  | none => rw [hw] at h; cases h
  | some M' => rw [hw] at h; cases h; exact ⟨P, M, M', rfl, rfl, hw, rfl⟩

theorem retypeFields_self : ∀ (fs : List (Nat × Ty)) (vs : List Val), vs.length = fs.length →
    (∀ i (hi : i < fs.length) (hv : i < vs.length), Val.retype fs[i].2 vs[i] = vs[i]) →
    Val.retypeFields fs vs = some vs
  | [], [], _, _ => by simp [Val.retypeFields]
  | (o, t) :: fs, v :: vs, hl, h => by
    simp only [Val.retypeFields]
    rw [retypeFields_self fs vs (by simpa using hl) fun i hi hv => h (i + 1) (by simp; omega)
      (by simp; omega)]
    simp only [Option.map_some, Option.some.injEq, List.cons.injEq, and_true]
    exact h 0 (by simp) (by simp)
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

namespace Src

variable (K : Src env tabs f bid fb F0 oS)
include K

/-- The values of `A` (from before the block or the prefix) have their own IDs. -/
theorem own {k : Nat} {z : ID} {v : Value} (hz : Base f bid z ∨ z ∈ oS.toList.take k)
    (hv : f.value? z = some v) : v.id = z := by
  obtain ⟨ce, hwf⟩ := K.wf
  rcases hz with ⟨v', hpl, -, -⟩ | hz
  · obtain ⟨hv', hb, blk, hblk, hx⟩ := hpl
    rw [hv] at hv'; cases hv'
    obtain ⟨v'', h1, h2, -⟩ := hwf.valueId _ blk ⟨hb, hblk⟩ z hx
    rw [hv] at h1; cases h1; exact h2
  · obtain ⟨hzb, -⟩ := K.memS.1 (List.mem_of_mem_take hz)
    obtain ⟨v', hv', hid, -⟩ := K.valueIn hzb
    rw [hv] at hv'; cases hv'; exact hid

/-- **A split `Store` the source evaluated** wrote the registers of the `StructMake`'s arguments
at the struct's fields. -/
theorem split_src {g : Func} {S : Frame} {k : Nat} (hS : SFacts env tabs f F0 S (oS.toList.take k))
    {x : ID} {ps : List (ID × ID)} (d : SplitD tabs f g x ps) (hx : x ∈ oS.toList.take k) :
    ∃ P M MS, S.regs[d.dst]? = some (some (.ptr P)) ∧ S.regs[d.mem]? = some (some (.mem M)) ∧
      M.write P (encode (.agg d.fs d.n) (.agg (d.smv.args.toList.map (rv S)))) = some MS ∧
      S.regs[x]? = some (some ((Val.mem MS).retype (tabs.ty d.fv.type))) := by
  have hL : ∀ y ∈ oS.toList.take k, Node f fb y := fun y hy => K.memS.1 (List.mem_of_mem_take hy)
  have H := K.avail hS
  have hT := K.typedS hS hL
  have hid : ∀ z v, (Base f bid z ∨ z ∈ oS.toList.take k) → f.value? z = some v → v.id = z :=
    fun z v hz hv => K.own hz hv
  obtain ⟨fv', y, hfv', hy, hev⟩ := hS.eval x hx
  rw [d.hfv] at hfv'; cases hfv'
  have hargs := regs_of_ok hev
  rw [evalValue_of_regs hargs, GoFV.Proof.CSE.Mem.evalOp_memRoot (.inl d.hop), d.hfargs] at hev
  simp only [List.map_toArray, List.map_cons, List.map_nil] at hev
  cases hm : memRoot (Ctx.make tabs f) d.fv [rv S d.dst, rv S d.sm, rv S d.mem] with
  | panic e m => rw [hm] at hev; cases hev
  | stuck msg => rw [hm] at hev; cases hev
  | ok r =>
  rw [hm] at hev
  simp only [Res.bind, bind] at hev
  cases hev
  obtain ⟨P, M, MS, hP, hM, hw, rfl⟩ := memRoot_store_ok d.hop hm
  have hmem : ∀ a ∈ d.fv.args, Base f bid a ∨ a ∈ oS.toList.take k :=
    fun a ha => H.cl x d.fv (.inr hx) d.hfv (by rw [d.hop]; decide) a ha
  have hreg : ∀ a ∈ d.fv.args, S.regs[a]? = some (some (rv S a)) := fun a ha => by
    obtain ⟨-, ya, -, hya, -⟩ := H.val a (hmem a ha)
    simp [rv, hya]
  have hdst := hreg d.dst (by rw [d.hfargs]; simp)
  have hmm := hreg d.mem (by rw [d.hfargs]; simp)
  rw [hP] at hdst; rw [hM] at hmm
  -- the stored value: the `StructMake`'s, through copies
  have hsmA := hmem d.sm (by rw [d.hfargs]; simp)
  obtain ⟨hA1, hr1⟩ := copy_reg H hT hid _ hsmA (copyReach_copyEnd f.valueTab _ d.sm)
  generalize hce : copyEnd tabs f.valueTab f.valueTab.size d.sm = smid at hA1 hr1
  have hsmv := d.hsmv; rw [hce] at hsmv
  obtain ⟨smv', ysm, hsmv', hysm, hevs⟩ := H.val smid hA1
  rw [hsmv] at hsmv'; cases hsmv'
  have hevs := hevs (by rw [d.hsmop]; decide)
  have hsmargs : ∀ a ∈ d.smv.args, Base f bid a ∨ a ∈ oS.toList.take k :=
    fun a ha => H.cl smid d.smv hA1 hsmv (by rw [d.hsmop]; decide) a ha
  rw [evalValue_of_regs (regs_of_ok hevs), evalOp_term (by rw [d.hsmop]; decide),
    GoFV.Proof.Rules.opVal_pure (by rw [d.hsmop]; decide), d.hsmop, evalPure_structMake,
    hid smid d.smv hA1 hsmv, tys_of_value hsmv, Option.getD_some, d.hsmty] at hevs
  simp only [pure, Res.bind, bind] at hevs
  cases hevs
  have hvs : Val.retypeFields d.fs (d.smv.args.toList.map (rv S)) =
      some (d.smv.args.toList.map (rv S)) := by
    refine retypeFields_self _ _ (by simp [d.hsmsz]) fun i hi hv => ?_
    obtain ⟨o, t, a, p, s, av, sv, ov, hfi, hai, -, L⟩ := ssLink_spec (d.hlink i hi)
    have hfs : d.fs[i] = (o, t) := by
      rw [List.getElem?_eq_getElem hi] at hfi; exact Option.some.inj hfi
    have ha : d.smv.args.toList[i]'(by simpa using hv) = a := by
      rw [Array.getElem_toList]
      rw [Array.getElem?_eq_getElem (by simpa using hv)] at hai; cases hai; rfl
    rw [hfs, List.getElem_map, ha]
    have hA : Base f bid a ∨ a ∈ oS.toList.take k :=
      hsmargs a (by rw [← ha]; exact Array.mem_toList_iff.1 (List.getElem_mem _))
    obtain ⟨-, ya, -, hya, -⟩ := H.val a hA
    have := hT a ya hya
    rw [tys_of_value L.ha, Option.getD_some, L.haty] at this
    simp only [rv, hya, Option.join_some, Option.getD_some]
    exact this
  have hagg : Val.retype (.agg d.fs d.n) (.agg (d.smv.args.toList.map (rv S))) =
      .agg (d.smv.args.toList.map (rv S)) := by
    simp only [Val.retype, hvs]
  rw [hagg] at hysm
  have hsmreg : rv S d.sm = .agg (d.smv.args.toList.map (rv S)) := by
    simp only [rv, ← hr1, hysm, Option.join_some, Option.getD_some]
  refine ⟨P, M, MS, hdst, hmm, ?_, ?_⟩
  · rw [← hsmreg, ← d.haux]; exact hw
  · rw [hy, hid x d.fv (.inr hx) d.hfv, tys_of_value d.hfv, Option.getD_some]

end Src

end GoFV.Proof.StructStore

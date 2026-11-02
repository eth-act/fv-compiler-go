import GoFV.Proof.Pass.CSEMemChain
import GoFV.Proof.WF

/-!
# cse's memory skips are sound

`load_memEnd`: a `Load` of type `t` at `p` reads the same through its memory argument `m` as
through `CSE.memEnd tabs f p t m`: every `Store`/`Zero` the walk skips writes bytes the load does
not read (`disjointP_sep`: an empty access, another block, or a byte range apart modulo 2^64),
and a read after a separate write reads what it read before (`read_write_sep`).
-/

namespace GoFV.Proof.CSE

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt

namespace Mem

variable {env : Env} {tabs : Tables} {f : Func} {fr : Frame} {A : ID → Prop}

theorem ofInt_sub (a b : Int) : BitVec.ofInt 64 (a - b) = BitVec.ofInt 64 a - BitVec.ofInt 64 b := by
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

/-- Offsets apart modulo 2^64 give separate accesses. -/
theorem apart_sep {P Q : Ptr} {op oq wq : Int} {w k : Nat}
    (ha : CSE.apart op w oq wq = true) (hk : k = 0 ∨ (k : Int) = wq)
    (hoff : Q.off = P.off + BitVec.ofInt 64 (oq - op)) : Sep P w Q k := by
  unfold CSE.apart at ha
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
  rcases hk with hk | hk
  · exact .inr (.inl hk)
  have hq := congrArg BitVec.toNat hoff
  rw [BitVec.toNat_add, BitVec.toNat_ofInt] at hq
  have hp := P.off.isLt
  simp only [Nat.reducePow, Int.reducePow] at ha hq hp
  right; right; right
  omega

theorem retype_mem {t : Ty} (h : CSE.keepsMem t = true) (M : Sem.Mem) :
    (Val.mem M).retype t = .mem M := by
  cases t <;> first | rfl | cases h

theorem args_two {a : Array ID} (h : a.size = 2) : a = #[a[0]!, a[1]!] := by
  rcases a with ⟨l⟩; rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, l⟩⟩⟩ <;> simp_all

theorem args_three {a : Array ID} (h : a.size = 3) : a = #[a[0]!, a[1]!, a[2]!] := by
  rcases a with ⟨l⟩; rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨u, l⟩⟩⟩⟩ <;> simp_all

theorem evalOp_memRoot {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val} {ty : Ty}
    (hop : v.op = .Store ∨ v.op = .Zero) : evalOp env ctx fr v argv ty = memRoot ctx v argv := by
  rcases hop with hop | hop <;> simp only [evalOp, hop]

theorem writeRes_ok {what : String} {o : Option Sem.Mem} {r : Val} (h : writeRes what o = .ok r) :
    ∃ M', o = some M' ∧ r = .mem M' := by
  cases o with
  | none => cases h
  | some M' => cases h; exact ⟨M', rfl, rfl⟩

/-- A `Store`'s write. -/
theorem store_val {v : Value} {q x m : ID} {qv xv mv y : Val} (hop : v.op = .Store)
    (hnb : CSE.keepsMem (CSE.valShape tabs f v) = true)
    (ha : v.args = #[q, x, m]) (hq : fr.regs[q]? = some (some qv))
    (hx : fr.regs[x]? = some (some xv)) (hm : fr.regs[m]? = some (some mv))
    (h : evalValue env (Ctx.make tabs f) fr v = .ok y) :
    ∃ Q M M', qv.asPtrWord = some Q ∧ mv = .mem M ∧
      M.write Q (encode (auxTy tabs v.aux) xv) = some M' ∧ y = .mem M' := by
  obtain ⟨argv, r, hargs, ho, rfl⟩ := evalValue_ok h
  have : argv = [qv, xv, mv] := map_some_inj (by rw [← hargs, ha]; simp [hq, hx, hm])
  subst this
  rw [evalOp_memRoot (.inl hop)] at ho
  unfold memRoot at ho
  simp only [hop] at ho
  cases mv with
  | mem M =>
    simp only at ho
    cases hQ : qv.asPtrWord with
    | none => simp only [hQ] at ho; cases ho
    | some Q =>
      simp only [hQ] at ho
      obtain ⟨M', hw, rfl⟩ := writeRes_ok ho
      exact ⟨Q, M, M', rfl, rfl, hw, by rw [tys_getD]; exact retype_mem hnb _⟩
  | _ => simp only at ho; split at ho <;> cases ho

/-- A `Zero`'s write. -/
theorem zero_val {v : Value} {q m : ID} {qv mv y : Val} (hop : v.op = .Zero)
    (hnb : CSE.keepsMem (CSE.valShape tabs f v) = true)
    (ha : v.args = #[q, m]) (hq : fr.regs[q]? = some (some qv))
    (hm : fr.regs[m]? = some (some mv)) (h : evalValue env (Ctx.make tabs f) fr v = .ok y) :
    ∃ Q M M', qv.asPtrWord = some Q ∧ mv = .mem M ∧
      M.write Q (Array.replicate v.auxInt.toInt.toNat (.b 0)) = some M' ∧ y = .mem M' := by
  obtain ⟨argv, r, hargs, ho, rfl⟩ := evalValue_ok h
  have : argv = [qv, mv] := map_some_inj (by rw [← hargs, ha]; simp [hq, hm])
  subst this
  rw [evalOp_memRoot (.inr hop)] at ho
  unfold memRoot at ho
  simp only [hop] at ho
  cases mv with
  | mem M =>
    simp only at ho
    cases hQ : qv.asPtrWord with
    | none => simp only [hQ] at ho; cases ho
    | some Q =>
      simp only [hQ] at ho
      obtain ⟨M', hw, rfl⟩ := writeRes_ok ho
      exact ⟨Q, M, M', rfl, rfl, hw, by rw [tys_getD]; exact retype_mem hnb _⟩
  | _ => simp only at ho; split at ho <;> cases ho

/-- `disjointP` gives separate accesses at the pointers' values (pointer words: pointers, or
integers read as the pointers at their addresses). -/
theorem disjointP_sep (H : Avail env tabs f fr A) {p q : ID} {w k : Nat} {wq : Int}
    (hd : CSE.disjointP tabs f p (w : Int) q wq = true) (hp : A p) (hq : A q) {pv qv : Val}
    {P Q : Ptr} (hpv : fr.regs[p]? = some (some pv)) (hqv : fr.regs[q]? = some (some qv))
    (hpP : pv.asPtrWord = some P) (hqQ : qv.asPtrWord = some Q)
    (hk : k = 0 ∨ (k : Int) = wq) : Sep P w Q k := by
  unfold CSE.disjointP at hd
  simp only [Bool.or_eq_true, beq_iff_eq] at hd
  rcases hd with (hw | hwq) | hd
  · exact .inl (by omega)
  · exact .inr (.inl (by omega))
  obtain ⟨hAp, hrp⟩ := baseOff_rel H 64 p 0 hp
  obtain ⟨hAq, hrq⟩ := baseOff_rel H 64 q 0 hq
  generalize CSE.baseOff tabs f 64 p 0 = BP at hd hAp hrp
  generalize CSE.baseOff tabs f 64 q 0 = BQ at hd hAq hrq
  obtain ⟨bp, op⟩ := BP
  obtain ⟨bq, oq⟩ := BQ
  simp only [Int.sub_zero] at hd hAp hAq hrp hrq
  obtain ⟨bvp, hbvp⟩ := H.reg hAp
  obtain ⟨bvq, hbvq⟩ := H.reg hAq
  have rp := hrp _ _ hpv hbvp
  have rq := hrq _ _ hqv hbvq
  by_cases hb : P.blk ≠ Q.blk
  · exact .inr (.inr (.inl hb))
  rw [ne_eq, Classical.not_not] at hb
  split at hd
  · rename_i hbb
    subst hbb
    rw [hbvp] at hbvq
    cases hbvq
    exact apart_sep hd hk (rel_same hpP hqQ rp rq hb)
  · split at hd
    · rename_i a b hpa hqb
      have ep := allocOf_val H hAp hpa hbvp
      have eq := allocOf_val H hAq hqb hbvq
      subst ep eq
      have e1 : P = ⟨blkOf a, 0 + BitVec.ofInt 64 op⟩ := by
        rcases rp.2 _ _ rfl with h | h <;> rw [h] at hpP
        · cases hpP
        · exact (Option.some.inj hpP).symm
      have e2 : Q = ⟨blkOf b, 0 + BitVec.ofInt 64 oq⟩ := by
        rcases rq.2 _ _ rfl with h | h <;> rw [h] at hqQ
        · cases hqQ
        · exact (Option.some.inj hqQ).symm
      subst e1 e2
      have hab := blkOf_inj hb
      subst hab
      simp only [bne_self_eq_false, Bool.false_or] at hd
      refine apart_sep hd hk ?_
      simp only [ofInt_sub]
      bv_omega
    · cases hd

/-- A load reads the same through its memory argument as through the arguments it skips to. -/
theorem load_mem_eq {ty : Ty} {ai : Int64} {aux : Option AuxRef} {pv : Val} {M M' : Sem.Mem}
    {Q : Ptr} {bs : Array Byte} (hw : M.write Q bs = some M')
    (hs : ∀ P, pv.asPtrWord = some P → Sep P ty.size Q bs.size) :
    evalPure .Load ty ai aux [pv, .mem M'] = evalPure .Load ty ai aux [pv, .mem M] := by
  show loadOp ty [pv, .mem M'] = loadOp ty [pv, .mem M]
  simp only [loadOp]
  cases hP : pv.asPtrWord with
  | none => rfl
  | some P =>
    show M'.load ty P = M.load ty P
    unfold Sem.Mem.load
    split <;> first | rfl | rw [read_write_sep hw (hs P hP)]

theorem memSkip_sound (H : Avail env tabs f fr A) {p : ID} (hp : A p) {ty : Ty} {m m' : ID}
    (hm : A m) (hs : CSE.memSkip tabs f p ty.size m = some m') :
    A m' ∧ ∀ (ai : Int64) (aux : Option AuxRef) (pv mv mv' : Val),
      fr.regs[p]? = some (some pv) → fr.regs[m]? = some (some mv) →
      fr.regs[m']? = some (some mv') →
      evalPure .Load ty ai aux [pv, mv] = evalPure .Load ty ai aux [pv, mv'] := by
  unfold CSE.memSkip at hs
  cases hv : f.value? m with
  | none => rw [hv] at hs; cases hs
  | some d =>
    rw [hv] at hs
    simp only at hs
    split at hs
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨⟨hop, hsz⟩, hnb⟩, hdj⟩ := hc
      cases hs
      have hphi : d.op ≠ .Phi := by rw [hop]; decide
      have hmem : ∀ i, i < 3 → A d.args[i]! :=
        fun i hi => H.cl m d hm hv hphi _ (getElem!_mem (by omega))
      refine ⟨hmem 2 (by decide), fun ai aux pv mv mv' hpv h1 h2 => ?_⟩
      obtain ⟨qv, hqv⟩ := H.reg (hmem 0 (by decide))
      obtain ⟨xv, hxv⟩ := H.reg (hmem 1 (by decide))
      obtain ⟨Q, M, M', hQ, rfl, hw, rfl⟩ :=
        store_val hop hnb (args_three hsz) hqv hxv h2 (H.eval hm hv hphi h1)
      refine load_mem_eq hw fun P hP => ?_
      exact disjointP_sep H hdj hp (hmem 0 (by decide)) hpv hqv hP hQ (.inr (by rw [encode_size]))
    · split at hs
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨⟨⟨hop, hsz⟩, hnb⟩, hdj⟩ := hc
        cases hs
        have hphi : d.op ≠ .Phi := by rw [hop]; decide
        have hmem : ∀ i, i < 2 → A d.args[i]! :=
          fun i hi => H.cl m d hm hv hphi _ (getElem!_mem (by omega))
        refine ⟨hmem 1 (by decide), fun ai aux pv mv mv' hpv h1 h2 => ?_⟩
        obtain ⟨qv, hqv⟩ := H.reg (hmem 0 (by decide))
        obtain ⟨Q, M, M', hQ, rfl, hw, rfl⟩ :=
          zero_val hop hnb (args_two hsz) hqv h2 (H.eval hm hv hphi h1)
        refine load_mem_eq hw fun P hP => ?_
        exact disjointP_sep H hdj hp (hmem 0 (by decide)) hpv hqv hP hQ
          (by simp only [Array.size_replicate]; omega)
      · cases hs

theorem memWalk_sound (H : Avail env tabs f fr A) {p : ID} (hp : A p) {ty : Ty} :
    ∀ (n : Nat) (m : ID), A m → A (CSE.memWalk tabs f p ty.size n m) ∧
      ∀ (ai : Int64) (aux : Option AuxRef) (pv mv ev : Val), fr.regs[p]? = some (some pv) →
        fr.regs[m]? = some (some mv) →
        fr.regs[CSE.memWalk tabs f p ty.size n m]? = some (some ev) →
        evalPure .Load ty ai aux [pv, mv] = evalPure .Load ty ai aux [pv, ev] := by
  intro n
  induction n with
  | zero =>
    intro m hm
    exact ⟨hm, fun ai aux pv mv ev _ h1 h2 => by
      rw [CSE.memWalk, h1] at h2; cases h2; rfl⟩
  | succ n ih =>
    intro m hm
    rw [CSE.memWalk]
    cases hs : CSE.memSkip tabs f p ty.size m with
    | none => exact ⟨hm, fun ai aux pv mv ev _ h1 h2 => by rw [h1] at h2; cases h2; rfl⟩
    | some m' =>
      simp only
      obtain ⟨hm', hstep⟩ := memSkip_sound H hp hm hs
      obtain ⟨hA, hrec⟩ := ih m' hm'
      refine ⟨hA, fun ai aux pv mv ev hpv h1 h2 => ?_⟩
      obtain ⟨mv', h'⟩ := H.reg hm'
      rw [hstep ai aux pv mv mv' hpv h1 h', hrec ai aux pv mv' ev hpv h' h2]

end Mem

open Mem in
/-- A `Load` of `t` at `p` reads the same through memory `m` as through `CSE.memEnd tabs f p t m`
(both in the frame of a run, for values whose registers hold their evaluation). -/
theorem load_memEnd {tabs : Tables} {f : Func} {env : Sem.Env} {fr : Sem.Frame}
    {A : ID → Prop}
    (hA : ∀ x, A x → ∃ v y, f.value? x = some v ∧ fr.regs[x]? = some (some y) ∧
      (v.op ≠ .Phi → Sem.evalValue env (Sem.Ctx.make tabs f) fr v = .ok y))
    (hcl : ∀ x v, A x → f.value? x = some v → v.op ≠ .Phi → ∀ a ∈ v.args, A a)
    {p m : ID} {t : TypeRef} (hp : A p) (hm : A m) :
    A (CSE.memEnd tabs f p t m) ∧
    ∀ (ai : Int64) (aux : Option AuxRef) (pv mv ev : Sem.Val), fr.regs[p]? = some (some pv) →
      fr.regs[m]? = some (some mv) → fr.regs[CSE.memEnd tabs f p t m]? = some (some ev) →
      Sem.evalPure .Load (tabs.ty t) ai aux [pv, mv] = Sem.evalPure .Load (tabs.ty t) ai aux [pv, ev] :=
  memWalk_sound (A := A) ⟨hA, hcl⟩ hp 256 m hm

end GoFV.Proof.CSE

namespace GoFV.Proof.CSE.Mem.Witness

open GoFV.SSA GoFV.Opt

/-! ## Non-vacuity: `memEnd` skips a store to another global

`v5 = Store {int64} (Addr {a}) v6 v1`: a load of `int64` at `Addr {b}` through `v5` reads
through to `v1` (`InitMem`); one at `Addr {a}` does not skip the store. -/

def tabs : Tables :=
  { types := #[some { (default : TypeDef) with kind := .INT64, size := some 8 },
      some { (default : TypeDef) with kind := .PTR, size := some 8 },
      some { (default : TypeDef) with kind := .SSA, str := GoStr.ofString "mem" }]
    auxes := #[some { fmt := default, kind := .sym (GoStr.ofString "a") 0 "" 8 default none none none #[] none },
      some { fmt := default, kind := .sym (GoStr.ofString "b") 0 "" 8 default none none none #[] none },
      some { fmt := default, kind := .type 0 }] }

def val (id : ID) (op : Op) (type : TypeRef) (aux : Option AuxRef) (args : Array ID) : Value :=
  { (default : Value) with id, op, type, aux, args }

def func : Func :=
  { (default : Func) with
    valueTab := #[none, some (val 1 .InitMem 2 none #[]), some (val 2 .SB 1 none #[]),
      some (val 3 .Addr 1 (some 0) #[2]), some (val 4 .Addr 1 (some 1) #[2]),
      some (val 5 .Store 2 (some 2) #[3, 6, 1]), some (val 6 .Const64 0 none #[])] }

theorem memEnd_skips : CSE.memEnd tabs func 4 0 5 = 1 ∧ CSE.memEnd tabs func 3 0 5 = 5 := by
  decide +kernel

end GoFV.Proof.CSE.Mem.Witness

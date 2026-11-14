import GoFV.Proof.Pass.DSERel
import GoFV.Proof.Pass.CSEClass

variable [GoFV.SSA.Sem.Addrs]

/-!
# dse: one value's evaluation in source and target

`VRel Q vS vT`: a target register `vT` relates to the source's `vS` when they are equal or
both memories, equal outside `Q`. `step_ok`: a value the source evaluates (in frame `S`) to `y`,
whose arguments' target registers (in `T`) relate to the source's with their pending sets,
evaluates in the target to a register related to `y` with its own pending set:

* an eliminated store is `Copy mem` in the target: the source's write adds its bytes, which lie
  in its static range (`ptrLoc_val`: the pointer is its `Addr`/`LocalAddr` base plus the summed
  offset), to the pending set (`MemEq.write_left`);
* a kept `Store`/`Zero`/`Move`/`VarDef` after pending ranges writes the same bytes on both
  sides (a `Move` reads an allocation with no pending range), which leave the pending set;
* `LocalAddr`/`InlMark` ignore their arguments' values;
* any other value reads arguments without pending ranges, which are equal.

`step_panic`: a panicking value (a call, `PanicBounds`, `NilCheck`) reads only arguments without
pending ranges and panics alike.
-/

-- Parallel elaboration (-j4) wrote this module's constants in a different order on every build,
-- so its `.olean` was never reproducible and importers missed the shared cache (#1, #34);
-- sequential elaboration costs no CPU here (11.2 s either way).
set_option Elab.async false

namespace GoFV.Proof.DSE

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.DSE GoFV.Proof.CSE GoFV.Proof.CSE.Mem

/-! ## Related registers -/

/-- The target register `vT` is the source's `vS`, or both are memories equal outside `Q`. -/
def VRel (Q : Blk → Nat → Prop) (vS vT : Val) : Prop :=
  vT = vS ∨ ∃ mS mT, vS = .mem mS ∧ vT = .mem mT ∧ MemEq Q mS mT

theorem VRel.eq_nil {vS vT : Val} (h : VRel (IvQ []) vS vT) : vT = vS := by
  rcases h with h | ⟨mS, mT, rfl, rfl, hm⟩
  · exact h
  · rw [hm.eq fun b k => ivQ_nil b k]

theorem VRel.mem {Q : Blk → Nat → Prop} {mS : Mem} {vT : Val} (h : VRel Q (.mem mS) vT) :
    ∃ mT, vT = .mem mT ∧ MemEq Q mS mT := by
  rcases h with rfl | ⟨mS', mT, h1, rfl, hm⟩
  · exact ⟨mS, rfl, MemEq.refl _ _⟩
  · cases h1; exact ⟨mT, rfl, hm⟩

/-- Retyping two related memories: the memory shape keeps them, others send both to
`poison`. -/
theorem VRel.retype_mem {Q : Blk → Nat → Prop} {mS mT : Mem} (t : Ty) (h : MemEq Q mS mT) :
    VRel Q ((Val.mem mS).retype t) ((Val.mem mT).retype t) := by
  cases t with
  | mem => exact .inr ⟨mS, mT, rfl, rfl, h⟩
  | _ => exact .inl rfl

/-! ## Where a store writes -/

variable {env : Env} {tabs : Tables} {f g : Func}

theorem ptrAlloc_val {fr : Frame} {A : ID → Prop} (H : Avail env tabs f fr A) {p : ID} (hp : A p)
    {a : CSE.Alloc} (h : ptrAlloc tabs f p = some a) {pv : Val} {P : Ptr}
    (hv : fr.regs[p]? = some (some pv)) (hP : pv.asPtrWord = some P) : P.blk = blkOf a ∧
      P.off = BitVec.ofInt 64 (CSE.baseOff tabs f 64 p 0).2 := by
  obtain ⟨hAb, hrel⟩ := baseOff_rel H 64 p 0 hp
  obtain ⟨bv, hbv⟩ := H.reg hAb
  have hb := allocOf_val H hAb h hbv
  have := ((hrel _ _ hv hbv).2 _ _ hb).resolve_left (by intro h; rw [h] at hP; cases hP)
  rw [this] at hP
  cases hP
  simp

theorem ptrLoc_val {fr : Frame} {A : ID → Prop} (H : Avail env tabs f fr A) {p : ID} (hp : A p)
    {a : CSE.Alloc} {o : Int} (h : ptrLoc tabs f p = some (a, o)) {pv : Val} {P : Ptr}
    (hv : fr.regs[p]? = some (some pv)) (hP : pv.asPtrWord = some P) :
    P.blk = blkOf a ∧ P.off.toNat = o.toNat ∧ 0 ≤ o := by
  unfold ptrLoc at h
  cases ha : ptrAlloc tabs f p with
  | none => rw [ha] at h; cases h
  | some a' =>
    rw [ha] at h
    simp only at h
    split at h
    · rename_i hc
      cases h
      obtain ⟨hb, hoff⟩ := ptrAlloc_val H hp ha hv hP
      refine ⟨hb, ?_, hc.1⟩
      rw [hoff, BitVec.toNat_ofInt]
      congr 1
      exact Int.emod_eq_of_lt hc.1 (by have := hc.2; omega)
    · cases h

/-- The bytes a store with a static range writes, if its pointer word is the range's. -/
theorem region_range {fv : Value} {iv : Iv} (h : range? tabs f fv = some iv) {fr : Frame}
    {A : ID → Prop} (H : Avail env tabs f fr A) (hA : ∀ a ∈ fv.args, A a) {P : Ptr}
    (hP : ∀ p, fv.args[0]? = some p → ∃ pv, fr.regs[p]? = some (some pv) ∧ pv.asPtrWord = some P)
    {b : Blk} {k : Nat} :
    Region P (wsize tabs fv) b k ↔ b = blkOf iv.1 ∧ iv.2.1 ≤ (k : Int) ∧ (k : Int) < iv.2.2 := by
  unfold range? at h
  cases hp : fv.args[0]? with
  | none => rw [hp] at h; cases h
  | some p =>
    rw [hp] at h
    simp only at h
    cases hl : ptrLoc tabs f p with
    | none => rw [hl] at h; cases h
    | some ao =>
      obtain ⟨a, o⟩ := ao
      rw [hl] at h
      cases h
      obtain ⟨pv, hpv, hpP⟩ := hP p hp
      obtain ⟨hb, ho, h0⟩ := ptrLoc_val H (hA p (Array.mem_of_getElem? hp)) hl hpv hpP
      unfold Region
      rw [hb, ho]
      simp only
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by omega, by omega⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by omega, by omega⟩

/-! ## Argument lists -/

theorem mapM_length {r : ID → Option Val} : ∀ {l : List ID} {vs : List Val},
    l.mapM r = some vs → vs.length = l.length
  | [], vs, h => by simp at h; subst h; rfl
  | a :: l, vs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨y, -, ys, hys, rfl⟩ := h
    simp [mapM_length hys]

theorem mapM_get {r : ID → Option Val} : ∀ {l : List ID} {vs : List Val}, l.mapM r = some vs →
    ∀ {k : Nat} {a : ID}, l[k]? = some a → ∃ v, vs[k]? = some v ∧ r a = some v
  | [], _, _, _, _, hk => by simp at hk
  | b :: l, vs, h, k, a, hk => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨y, hy, ys, hys, rfl⟩ := h
    cases k with
    | zero => simp at hk; subst hk; exact ⟨y, rfl, hy⟩
    | succ k => exact mapM_get hys (by simpa using hk)

theorem mapM_snoc {r r' : ID → Option Val} {m : ID} {w' : Val} (hm : r' m = some w') :
    ∀ {l : List ID} {L : List Val} {w : Val}, (∀ a ∈ l, r' a = r a) →
      (l ++ [m]).mapM r = some (L ++ [w]) → (l ++ [m]).mapM r' = some (L ++ [w'])
  | [], L, w, _, h => by
    simp only [List.nil_append, List.mapM_cons, List.mapM_nil, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨y, -, ys, rfl, he⟩ := h
    cases L with
    | nil => simp [hm]
    | cons _ L => cases L <;> simp at he
  | a :: l, L, w, hl, h => by
    simp only [List.cons_append, List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h ⊢
    obtain ⟨y, hy, ys, hys, he⟩ := h
    have hlen := mapM_length hys
    cases L with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at he
      rw [he.2] at hlen; simp at hlen
    | cons y' L =>
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨y, by rw [hl a List.mem_cons_self, hy], L ++ [w'], ?_, rfl⟩
      exact mapM_snoc hm (fun b hb => hl b (List.mem_cons_of_mem _ hb)) hys

theorem argVals_get {fr : Frame} {as : Array ID} {vs : List Val} (h : argVals fr as = some vs)
    {k : Nat} {a : ID} (hk : as[k]? = some a) : ∃ v, vs[k]? = some v ∧ fr.regs[a]? = some (some v) := by
  obtain ⟨v, hv, hr⟩ := mapM_get h (by simpa using hk)
  refine ⟨v, hv, ?_⟩
  revert hr
  cases fr.regs[a]? with
  | none => intro h; cases h
  | some o => intro h; simp at h; rw [h]

theorem back_eq {as : Array ID} {m : ID} (h : as.back? = some m) :
    as.toList = as.pop.toList ++ [m] := by
  obtain ⟨ys, rfl⟩ := Array.back?_eq_some_iff.1 h
  simp

theorem mem_of_mem_pop {as : Array ID} {a : ID} (h : a ∈ as.pop) : a ∈ as :=
  Array.mem_toList_iff.1 ((List.dropLast_sublist _).subset (Array.mem_toList_iff.2 h))

/-- The last argument's register is the last of the argument registers. -/
theorem argVals_back {fr : Frame} {as : Array ID} {m : ID} {L : List Val} {w : Val}
    (h : argVals fr as = some (L ++ [w])) (hm : as.back? = some m) : fr.regs[m]? = some (some w) := by
  have hlen := mapM_length h
  simp only [List.length_append, List.length_singleton, Array.length_toList] at hlen
  have hk : as[L.length]? = some m := by
    rw [Array.back?_eq_getElem?] at hm; rwa [show as.size - 1 = L.length by omega] at hm
  obtain ⟨v, hv, hr⟩ := argVals_get h hk
  simp at hv; rw [hv]; exact hr

/-- The target's argument registers: the source's but for the last. -/
theorem argVals_last {fr fr' : Frame} {as : Array ID} {m : ID} {L : List Val} {w w' : Val}
    (h : argVals fr as = some (L ++ [w])) (hm : as.back? = some m)
    (hpop : ∀ a ∈ as.pop, fr'.regs[a]? = fr.regs[a]?) (hw : fr'.regs[m]? = some (some w')) :
    argVals fr' as = some (L ++ [w']) := by
  unfold argVals at h ⊢
  rw [back_eq hm] at h ⊢
  exact mapM_snoc (by simp [hw]) (fun a ha => by rw [hpop a (Array.mem_toList_iff.1 ha)]) h

/-! ## The memory ops -/

theorem evalOp_chain {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val} {ty : Ty}
    (hop : v.op = .Store ∨ v.op = .Zero ∨ v.op = .Move ∨ v.op = .VarDef) :
    evalOp env ctx fr v argv ty = memRoot ctx v argv := by
  rcases hop with hop | hop | hop | hop <;> simp only [evalOp, hop]

theorem read_size {M : Mem} {p : Ptr} {n : Nat} {bs : Array Byte} (h : M.read p n = some bs) :
    bs.size = n := by
  unfold Mem.read at h
  by_cases hn : n = 0
  · simp only [hn, beq_self_eq_true, ite_true] at h; cases h; simp [hn]
  · simp only [beq_iff_eq, hn, ite_false, Option.bind_eq_bind] at h
    cases ha : M.find? p.blk with
    | none => rw [ha] at h; cases h
    | some a =>
      rw [ha] at h
      simp only [Option.bind_some] at h
      split at h
      · cases h; simp; omega
      · cases h

/-- What a `Store`/`Zero`/`Move` that succeeds does, and that it does the same write on another
memory (a `Move` reading it alike). Addresses are pointer words (`Val.asPtrWord`). -/
theorem write_shape {ctx : Ctx} {v : Value} {argv : List Val} {y : Val}
    (hop : v.op = .Store ∨ v.op = .Zero ∨ v.op = .Move) (h : memRoot ctx v argv = .ok y) :
    ∃ a p L M bs M1, argv = a :: (L ++ [.mem M]) ∧ a.asPtrWord = some p ∧
      M.write p bs = some M1 ∧ y = .mem M1 ∧ bs.size = wsize ctx.tabs v ∧
      (v.op = .Move → ∃ b s, L = [b] ∧ b.asPtrWord = some s ∧ M.read s bs.size = some bs) ∧
      ∀ M' M1', (∀ b s, v.op = .Move → L = [b] → b.asPtrWord = some s →
          M'.read s bs.size = M.read s bs.size) →
        M'.write p bs = some M1' → memRoot ctx v (a :: (L ++ [.mem M'])) = .ok (.mem M1') := by
  rcases hop with hop | hop | hop
  · unfold memRoot at h
    simp only [hop] at h
    split at h
    all_goals first
      | contradiction
      | (split at h <;> cases h <;> done)
      | skip
    rename_i a x M _
    cases hp : a.asPtrWord with
    | none => rw [hp] at h; cases h
    | some p =>
    rw [hp] at h
    obtain ⟨M1, hw, rfl⟩ := writeRes_ok h
    refine ⟨a, p, [x], M, _, M1, rfl, hp, hw, rfl, ?_, (fun h => by rw [hop] at h; cases h), ?_⟩
    · unfold wsize; rw [hop]; exact Sem.encode_size _ _
    · intro M' M1' _ hw'
      simp only [List.cons_append, List.nil_append, memRoot, hop, hp, hw']
      rfl
  · unfold memRoot at h
    simp only [hop] at h
    split at h
    all_goals first
      | contradiction
      | (split at h <;> cases h <;> done)
      | skip
    rename_i a M _
    cases hp : a.asPtrWord with
    | none => rw [hp] at h; cases h
    | some p =>
    rw [hp] at h
    obtain ⟨M1, hw, rfl⟩ := writeRes_ok h
    refine ⟨a, p, [], M, _, M1, rfl, hp, hw, rfl, ?_, (fun h => by rw [hop] at h; cases h), ?_⟩
    · unfold wsize; rw [hop]; simp
    · intro M' M1' _ hw'
      simp only [List.nil_append, memRoot, hop, hp, hw']
      rfl
  · unfold memRoot at h
    simp only [hop] at h
    split at h
    all_goals first
      | contradiction
      | (split at h <;> cases h <;> done)
      | skip
    rename_i a b M _
    cases hp : a.asPtrWord with
    | none => rw [hp] at h; cases h
    | some d =>
    cases hq : b.asPtrWord with
    | none => rw [hp, hq] at h; cases h
    | some s =>
    rw [hp, hq] at h
    simp only at h
    cases hr : M.read s v.auxInt.toInt.toNat with
    | none => rw [hr] at h; cases h
    | some bs =>
      rw [hr] at h
      obtain ⟨M1, hw, rfl⟩ := writeRes_ok h
      have hsz := read_size hr
      refine ⟨a, d, [b], M, bs, M1, rfl, hp, hw, rfl, ?_,
        fun _ => ⟨b, s, rfl, hq, by rw [hsz, hr]⟩, ?_⟩
      · unfold wsize; rw [hop]; simpa using hsz
      · intro M' M1' hrd hw'
        have hr' : M'.read s v.auxInt.toInt.toNat = some bs := by
          rw [← hsz, hrd b s hop rfl hq, hsz, hr]
        simp only [List.cons_append, List.nil_append, memRoot, hop, hp, hq, hr', hw']
        rfl

/-- What a `VarDef` that succeeds does, and on another memory. -/
theorem varDef_shape {ctx : Ctx} {v : Value} {argv : List Val} {y : Val} (hop : v.op = .VarDef)
    (h : memRoot ctx v argv = .ok y) :
    ∃ M n, argv = [.mem M] ∧ v.aux = some n ∧ y = .mem (varDefMem ctx.tabs ctx.act n M) ∧
      ∀ M', memRoot ctx v [.mem M'] = .ok (.mem (varDefMem ctx.tabs ctx.act n M')) := by
  unfold memRoot at h
  simp only [hop] at h
  split at h
  all_goals first
    | contradiction
    | skip
  all_goals first
    | (split at h <;> cases h <;> done)
    | skip
  rename_i M _
  cases ha : v.aux with
  | none => rw [ha] at h; cases h
  | some n =>
    rw [ha] at h
    cases h
    refine ⟨M, n, rfl, rfl, rfl, fun M' => ?_⟩
    simp only [memRoot, hop, ha]

/-- `LocalAddr` and `InlMark` ignore their arguments' values. -/
theorem evalOp_blind {ctx : Ctx} {fr : Frame} {v : Value} {ty : Ty} (hb : blindOp v.op = true)
    (argv argv' : List Val) : evalOp env ctx fr v argv ty = evalOp env ctx fr v argv' ty := by
  unfold blindOp at hb
  simp only [Bool.or_eq_true, beq_iff_eq] at hb
  rcases hb with hop | hop <;> (delta evalOp; rw [hop]; rfl)

end GoFV.Proof.DSE

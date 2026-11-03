import GoFV.Opt.NilLateCheck
import GoFV.Proof.EvalL

/-!
# `late nilcheck` under `runSched`: the values

What the `late nilcheck` proof needs of single values when memory ops fault (`runSched`):

* `nc_panic`: a `LoweredNilCheck` that panics does so with `nilDeref` of its memory argument, its
  pointer's base being nil (`Ptr.isNil`; a wild pointer is `stuck`, `wildNil`);
* `faults_panic`: a value accepted by `faultsOnB` on that pointer and memory panics with the same
  `nilDeref`;
* `safe_res`: a value accepted by `safeOpB` is `.ok` or panics with that `nilDeref`.
-/

namespace GoFV.Proof.NilLateL

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof GoFV.Opt.NilLate

/-! ## Dispatch of `evalOpL` -/

theorem evalOpL_listed {faulting : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} (hg : v.op.generic = false) (hl : arm64Listed v.op = true) :
    evalOpL faulting env ctx fr v argv ty = arm64Op faulting env ctx fr v argv ty := by
  unfold arm64Listed at hl
  unfold evalOpL
  simp only [hg, Bool.false_eq_true, ite_false]
  split at hl <;> first | (rename_i heq; rw [heq]) | exact absurd hl (by decide)

theorem evalOpL_unlisted {faulting : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} (hg : v.op.generic = false) (hl : arm64Listed v.op = false) :
    evalOpL faulting env ctx fr v argv ty =
      if isRoot v.op then atomicRoot v argv else pure (Arm64.evalPure v.op ty v.auxInt v.aux argv) := by
  unfold evalOpL
  simp only [hg, Bool.false_eq_true, ite_false]
  split <;> first | rfl | (rename_i heq; rw [heq] at hl; exact absurd hl (by decide))

/-! ## Addresses -/

theorem addr_zero_of_word {a : Val} {p : Ptr} (h : a.asPtrWord = some p) : Arm64.addr a 0 = some p := by
  cases a with
  | ptr q =>
    simp only [Val.asPtrWord, Option.some.injEq] at h; subst h
    simp [Arm64.addr, Ptr.add]
  | int w x =>
    cases w <;> simp only [Val.asPtrWord, reduceCtorEq] at h
    simp only [Option.some.injEq] at h; subst h
    simp [Arm64.addr, Arm64.reg]
  | _ => simp [Val.asPtrWord] at h

theorem nilFault_of_isNil {b : Ptr} (h : b.isNil = true) : b.nilFault = true := by
  simp only [Ptr.isNil, Bool.and_eq_true, beq_iff_eq] at h
  simp [Ptr.nilFault, h.1, h.2, minZeroPage]

/-- A concrete address in the nil block is that address. -/
theorem ofAddr_nil {x : BitVec 64} (h : (Ptr.ofAddr x).blk = .nil) : Ptr.ofAddr x = ⟨.nil, x⟩ := by
  by_cases hx : x.toNat < 2 ^ 40
  · simp [Ptr.ofAddr, hx]
  · exfalso
    by_cases hy : x.toNat < 2 ^ 62
    · simp [Ptr.ofAddr, hx, hy] at h
    · simp only [Ptr.ofAddr, hx, hy, ↓reduceIte] at h
      split at h <;> simp at h

theorem ofAddr_small {x : BitVec 64} (h : x.toNat < 2 ^ 40) : Ptr.ofAddr x = ⟨.nil, x⟩ := by
  simp [Ptr.ofAddr, h]

/-- An access at offset `k < minZeroPage` from a nil base faults. -/
theorem addr_nilFault {a : Val} {b : Ptr} {k : BitVec 64} (h : Arm64.addr a 0 = some b)
    (hb : b.isNil = true) (hk : k.toNat < minZeroPage) :
    ∃ c, Arm64.addr a k = some c ∧ c.nilFault = true := by
  simp only [Ptr.isNil, Bool.and_eq_true, beq_iff_eq] at hb
  obtain ⟨hblk, hoff⟩ := hb
  cases a with
  | ptr q =>
    simp only [Arm64.addr, Option.some.injEq] at h
    subst h
    simp only [Ptr.add] at hblk hoff
    have hq : q.off = 0 := by simpa using hoff
    refine ⟨_, rfl, ?_⟩
    simp only [Ptr.nilFault, Ptr.add, hblk, hq, beq_self_eq_true, Bool.true_and,
      decide_eq_true_eq]
    simpa using hk
  | _ =>
    simp only [Arm64.addr, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, rfl⟩ := h
    refine ⟨_, by simp only [Arm64.addr, hx, Option.map_some]; rfl, ?_⟩
    have hx0 : x = 0 := by
      have := ofAddr_nil hblk
      rw [this] at hoff
      simpa using hoff
    subst hx0
    have hk' : (0 + k).toNat < 2 ^ 40 := by
      simp only [minZeroPage] at hk; simp; omega
    rw [ofAddr_small hk']
    simp only [Ptr.nilFault, beq_self_eq_true, Bool.true_and, decide_eq_true_eq]
    simpa using hk

/-! ## A nil check that panics -/

theorem nilFaults_some {faulting : Bool} {ctx : Ctx} {v : Value} {argv : List Val} {m : Mem}
    (h : nilFaults faulting ctx v argv = some m) : argv.getLast? = some (.mem m) := by
  unfold nilFaults at h
  split at h
  · cases h
  · split at h
    · rename_i m' hl
      split at h
      · cases h; exact hl
      · cases h
    · cases h

theorem nilFaults_mem {faulting : Bool} {ctx : Ctx} {v : Value} {argv : List Val} {m : Mem}
    (h : nilFaults faulting ctx v argv = some m) :
    ∃ x ∈ nilAccesses ctx v argv, x.1.isNil = true ∧ x.2.nilFault = true := by
  unfold nilFaults at h
  split at h
  · cases h
  · split at h
    · split at h
      · rename_i hany
        simp only [List.any_eq_true, Bool.and_eq_true] at hany
        obtain ⟨x, hx, h1, h2⟩ := hany
        exact ⟨x, hx, h1, h2⟩
      · cases h
    · cases h

theorem nilFaults_of_mem {ctx : Ctx} {v : Value} {argv : List Val} {m : Mem}
    (hl : argv.getLast? = some (.mem m))
    (hx : ∃ x ∈ nilAccesses ctx v argv, x.1.isNil = true ∧ x.2.nilFault = true) :
    nilFaults true ctx v argv = some m := by
  obtain ⟨x, hx, h1, h2⟩ := hx
  unfold nilFaults
  simp only [Bool.not_true, Bool.false_eq_true, ite_false, hl]
  split
  · rfl
  · rename_i hn
    exfalso; apply hn
    simp only [List.any_eq_true, Bool.and_eq_true]
    exact ⟨x, hx, h1, h2⟩

/-- The accesses of an op other than `LoweredMemEq` are all its faulting arguments'. -/
theorem nilAccesses_eq {ctx : Ctx} {v : Value} {argv : List Val}
    (hne : v.op ≠ .ARM64LoweredMemEq) :
    nilAccesses ctx v argv =
      (if !v.op.faultOnNilArg0 then none else
        argv.head?.bind fun a => (Arm64.addr a 0).bind fun b =>
          (if v.op.auxType == .SymOff then symAddr ctx v a else some b).map (b, ·)).toList ++
      (if !v.op.faultOnNilArg1 then none else
        argv[1]?.bind fun a => (Arm64.addr a 0).map fun b => (b, b)).toList := by
  unfold nilAccesses
  dsimp only
  split
  · exact absurd ‹v.op = .ARM64LoweredMemEq› hne
  · rfl

theorem mem_nilAccesses0 {ctx : Ctx} {v : Value} {argv : List Val} {a : Val} {b c : Ptr}
    (h0 : v.op.faultOnNilArg0 = true) (hne : v.op ≠ .ARM64LoweredMemEq)
    (ha : argv.head? = some a) (hb : Arm64.addr a 0 = some b)
    (hc : (if v.op.auxType == .SymOff then symAddr ctx v a else some b) = some c) :
    (b, c) ∈ nilAccesses ctx v argv := by
  rw [nilAccesses_eq hne]
  apply List.mem_append_left
  simp only [h0, Bool.not_true, Bool.false_eq_true, ite_false, ha, Option.bind_some, hb, hc,
    Option.map_some, Option.toList_some, List.mem_singleton]

theorem mem_nilAccesses1 {ctx : Ctx} {v : Value} {argv : List Val} {a : Val} {b : Ptr}
    (h1 : v.op.faultOnNilArg1 = true) (hne : v.op ≠ .ARM64LoweredMemEq)
    (ha : argv[1]? = some a) (hb : Arm64.addr a 0 = some b) :
    (b, b) ∈ nilAccesses ctx v argv := by
  rw [nilAccesses_eq hne]
  apply List.mem_append_right
  simp only [h1, Bool.not_true, Bool.false_eq_true, ite_false, ha, Option.bind_some, hb,
    Option.map_some, Option.toList_some, List.mem_singleton]

/-- A nil check's only access is at its pointer. -/
theorem nilAccesses_nc {ctx : Ctx} {v : Value} {argv : List Val} {x : Ptr × Ptr}
    (hop : v.op = .ARM64LoweredNilCheck) (hx : x ∈ nilAccesses ctx v argv) :
    ∃ a, argv.head? = some a ∧ Arm64.addr a 0 = some x.1 := by
  rw [nilAccesses_eq (by rw [hop]; decide)] at hx
  have e0 : Op.faultOnNilArg0 .ARM64LoweredNilCheck = true := rfl
  have e1 : Op.faultOnNilArg1 .ARM64LoweredNilCheck = false := rfl
  have e2 : (Op.auxType .ARM64LoweredNilCheck == .SymOff) = false := rfl
  simp only [hop, e0, e1, e2, Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false,
    ite_true, Option.toList_none, List.append_nil] at hx
  cases hh : argv.head? with
  | none => simp only [hh, Option.bind_none, Option.toList_none, List.not_mem_nil] at hx
  | some a =>
    simp only [hh, Option.bind_some] at hx
    cases hb : Arm64.addr a 0 with
    | none => simp only [hb, Option.bind_none, Option.toList_none, List.not_mem_nil] at hx
    | some b =>
      simp only [hb, Option.bind_some, Option.map_some, Option.toList_some,
        List.mem_singleton] at hx
      subst hx
      exact ⟨a, rfl, hb⟩

/-- **A `LoweredNilCheck` that panics under `runSched`** panics with `nilDeref` of its memory
argument, and its pointer's base is nil. -/
theorem nc_panic {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val} {ty : Ty}
    {e : Panic} {m : Mem} (hop : v.op = .ARM64LoweredNilCheck)
    (h : evalOpL true env ctx fr v argv ty = .panic e m) :
    e = .nilDeref ∧ argv.getLast? = some (.mem m) ∧
      ∃ a b, argv.head? = some a ∧ Arm64.addr a 0 = some b ∧ b.isNil = true := by
  rw [evalOpL_listed (by rw [hop]; rfl) (by rw [hop]; rfl)] at h
  unfold arm64Op at h
  cases hnf : nilFaults true ctx v argv with
  | some m' =>
    rw [hnf] at h
    cases h
    refine ⟨rfl, nilFaults_some hnf, ?_⟩
    obtain ⟨x, hx, h1, -⟩ := nilFaults_mem hnf
    obtain ⟨a, ha, hb⟩ := nilAccesses_nc hop hx
    exact ⟨a, x.1, ha, hb, h1⟩
  | none =>
    rw [hnf] at h
    simp only [hop, Bool.true_and] at h
    split at h
    · cases h
    · rename_i hw
      unfold memRoot at h
      split at h <;> try (simp only [reduceCtorEq] at *; done)
      · rename_i a0 m0 _
        simp only at h
        split at h
        · rename_i p hp
          split at h
          · rename_i hblk
            cases h
            refine ⟨rfl, rfl, a0, p, rfl, addr_zero_of_word hp, ?_⟩
            have hw' : p.wild = false := by
              unfold wildNil at hw
              simp only [List.head?_cons, Option.bind_some, addr_zero_of_word hp,
                Option.map_some, Option.getD_some, Bool.not_eq_true] at hw
              exact hw
            simp only [Ptr.wild, hblk, Bool.true_and, Bool.not_eq_false'] at hw'
            exact hw'
          · cases h
        · cases h
      · simp only at h
        split at h <;> cases h

/-! ## The value that faults -/

/-- **A value accepted by `faultsOnB u p mm`** panics with `nilDeref` of the memory when the
base of `p`'s value `a` is nil. -/
theorem faults_panic {env : Env} {ctx : Ctx} {fr : Frame} {u : Value} {argv : List Val}
    {ty : Ty} {m : Mem} {p mm : ID} {a : Val} {b : Ptr} (hf : faultsOnB u p mm = true)
    (hargs : ∀ k : Nat, u.args[k]? = some p → argv[k]? = some a)
    (hlast : argv.getLast? = some (.mem m)) (ha : Arm64.addr a 0 = some b)
    (hb : b.isNil = true) :
    evalOpL true env ctx fr u argv ty = .panic .nilDeref m := by
  unfold faultsOnB at hf
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.or_eq_true, decide_eq_true_eq] at hf
  obtain ⟨⟨⟨⟨hg, hl⟩, hne⟩, -⟩, hor⟩ := hf
  rw [evalOpL_listed hg hl]
  have hnf : nilFaults true ctx u argv = some m := by
    refine nilFaults_of_mem hlast ?_
    rcases hor with ⟨⟨h0, hp⟩, hoff⟩ | ⟨h1, hp⟩
    · have ha0 : argv.head? = some a := by
        rw [List.head?_eq_getElem?]; exact hargs 0 hp
      by_cases hs : u.op.auxType = .SymOff
      · obtain ⟨⟨haux, h0le⟩, hlt⟩ := hoff.resolve_left (fun h => h hs)
        simp only [Option.isNone_iff_eq_none] at haux
        have hk : (BitVec.ofInt 64 u.auxInt.toInt).toNat < minZeroPage := by
          simp only [minZeroPage] at hlt ⊢
          rw [BitVec.toNat_ofInt]
          omega
        obtain ⟨c, hc, hcf⟩ := addr_nilFault ha hb hk
        refine ⟨(b, c), mem_nilAccesses0 h0 hne ha0 ha ?_, hb, hcf⟩
        simp only [hs, beq_self_eq_true, ite_true, symAddr, haux]
        exact hc
      · refine ⟨(b, b), mem_nilAccesses0 h0 hne ha0 ha ?_, hb, nilFault_of_isNil hb⟩
        simp only [beq_iff_eq, hs, ite_false]
    · exact ⟨(b, b), mem_nilAccesses1 h1 hne (hargs 1 hp) ha, hb, nilFault_of_isNil hb⟩
  unfold arm64Op
  rw [hnf]

/-! ## The values between -/

theorem nilFaults_none_of {ctx : Ctx} {v : Value} {argv : List Val}
    (h0 : v.op.faultOnNilArg0 = false) (h1 : v.op.faultOnNilArg1 = false)
    (hne : v.op ≠ .ARM64LoweredMemEq) : nilFaults true ctx v argv = none := by
  unfold nilFaults
  rw [nilAccesses_eq hne]
  simp only [h0, h1, Bool.not_false, ite_true, Option.toList_none, List.append_nil,
    List.any_nil, Bool.false_eq_true, ite_false, Bool.not_true]
  split <;> rfl

/-- **A value accepted by `safeOpB w mm`** evaluates, or panics with `nilDeref` of the memory
`mm` holds. -/
theorem safe_res {env : Env} {ctx : Ctx} {fr : Frame} {w : Value} {argv : List Val} {ty : Ty}
    {m : Mem} {mm : ID} (hs : safeOpB w mm = true)
    (hlast : w.args.back? = some mm → argv.getLast? = some (.mem m)) :
    (∃ y, evalOpL true env ctx fr w argv ty = .ok y) ∨
      evalOpL true env ctx fr w argv ty = .panic .nilDeref m := by
  unfold safeOpB at hs
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq,
    beq_iff_eq] at hs
  rcases hs with ((⟨⟨⟨⟨hg, hroot⟩, hArg⟩, hAIR⟩, hPB⟩ | ⟨⟨hg, hl⟩, hroot⟩) | hok) | ⟨hld, hback⟩
  · left
    unfold evalOpL
    simp only [hg, ite_true]
    unfold evalOp
    split <;> first
      | exact ⟨_, rfl⟩
      | (rename_i heq; exact absurd heq hArg)
      | (rename_i heq; exact absurd heq hAIR)
      | (rename_i heq; exact absurd heq hPB)
      | (rename_i heq; rw [heq] at hroot; exact absurd hroot (by decide))
      | (split
         · exact ⟨_, rfl⟩
         · rw [ite_eq_right_iff.2 (fun h => absurd h (by simp [hroot]))]; exact ⟨_, rfl⟩)
  · left
    rw [evalOpL_unlisted hg hl]
    rw [ite_eq_right_iff.2 (fun h => absurd h (by simp [hroot]))]
    exact ⟨_, rfl⟩
  · left
    unfold okOp at hok
    split at hok <;> (try exact absurd hok (by decide)) <;> (rename_i heq) <;>
    · rw [evalOpL_listed (by rw [heq]; rfl) (by rw [heq]; rfl)]
      unfold arm64Op
      rw [nilFaults_none_of (by rw [heq]; rfl) (by rw [heq]; rfl) (by rw [heq]; decide)]
      simp only [heq]
      first | exact ⟨_, rfl⟩ | (split <;> exact ⟨_, rfl⟩) | (split <;> (try split) <;> exact ⟨_, rfl⟩)
  · have hl := hlast (by simpa using hback)
    unfold Opt.NilLate.loadOp at hld
    split at hld <;> (try exact absurd hld (by decide)) <;> (rename_i heq) <;>
    · rw [evalOpL_listed (by rw [heq]; rfl) (by rw [heq]; rfl)]
      unfold arm64Op
      cases hnf : nilFaults true ctx w argv with
      | some m' =>
        right
        rw [nilFaults_some hnf] at hl
        cases hl
        rfl
      | none =>
        left
        simp only [heq]
        split <;> exact ⟨_, rfl⟩

end GoFV.Proof.NilLateL

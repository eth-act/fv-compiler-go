import GoFV.Proof.RetypeL
import GoFV.Proof.Speculate
import GoFV.Opt.ScheduleCheck
import GoFV.Proof.EvalOpLDispatch
import GoFV.Proof.PtrAddr
import GoFV.Proof.Pass.CSEOp

variable [GoFV.SSA.Sem.Addrs]

/-!
# `schedule` on `runSched`: what a value's class says about its evaluation

The classes of `scheduleCheck` (`GoFV.Opt.ScheduleCheck.cls`) under faulting evaluation
(`LMode.faulting`, `runSched` and `runLF`):

* `evalValueL_safe`: a `Cls.safe` value evaluates whenever its arguments have registers;
* `evalValueL_load`: a `Cls.load` value (`faultOp`) evaluates or panics with `nilDeref` of its
  last argument's memory;
* `evalValueL_panic_info`: a value that panics may panic (`mayPanic`); a `Cls.load` or
  `Cls.nil` one panics with `nilDeref` of its last argument's memory, and a load or lowered nil
  check that panics has a nil first argument (`NilBase`: faults need a nil base, a nil check of
  a wild pointer is `stuck`);
* nil checks: an evaluated one returns its pointer, outside the nil block (`evalValueL_nc_ok`,
  `NonNil`); a lowered nil check of
  a nil pointer on a memory panics with `nilDeref` of it (`evalValueL_nc_nil`);
* a symbolic `symAddrOp` (`MOV*load`, `MOV*store`, `MOVDaddr` at a symbol or frame variable)
  ignores its first argument's value (`evalOpL_arg0`), which `schedule`'s `SPanchored` bypass
  changes;
* a `Select1` of an acquiring load `LDAR*` that evaluated to a memory holds the load's memory
  argument's (`evalValueL_select1_ldar`: `atomicLoad` keeps the memory), what `sameMem`'s
  `ldReach` steps read.
-/

namespace GoFV.Proof.SchedL

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.ScheduleCheck GoFV.Proof

/-- `r'` evaluates where `r` does, alike (`stuck` messages aside). -/
def ResSim (r r' : Res Val) : Prop :=
  (∀ y, r = .ok y → r' = .ok y) ∧ (∀ e m, r = .panic e m → r' = .panic e m)

theorem ResSim.of_eq {r r' : Res Val} (h : r' = r) : ResSim r r' :=
  ⟨fun _ hy => h ▸ hy, fun _ _ hm => h ▸ hm⟩

/-! ## Arguments -/

theorem mapM_ofOption_spec {m : ID → String} {r : ID → Option Val} :
    ∀ {l : List ID} {L : List Val}, l.mapM (fun a => Res.ofOption (m a) (r a)) = .ok L →
      L.length = l.length ∧ ∀ (k : Nat) a, l[k]? = some a → ∃ z, r a = some z ∧ L[k]? = some z
  | [], L, h => by
    rw [List.mapM_nil] at h; cases h; exact ⟨rfl, fun _ _ h => by simp at h⟩
  | a :: l, L, h => by
    rw [List.mapM_cons] at h
    cases ha : r a with
    | none => rw [ha] at h; cases h
    | some z =>
      rw [ha] at h
      change (l.mapM (fun a => Res.ofOption (m a) (r a))).bind (fun L' => .ok (z :: L')) = _ at h
      cases hl : l.mapM (fun a => Res.ofOption (m a) (r a)) with
      | panic e mm => rw [hl] at h; cases h
      | stuck msg => rw [hl] at h; cases h
      | ok L' =>
        rw [hl] at h; cases h
        obtain ⟨h1, h2⟩ := mapM_ofOption_spec hl
        refine ⟨by simp [h1], fun k b hb => ?_⟩
        cases k with
        | zero => simp at hb; subst hb; exact ⟨z, ha, rfl⟩
        | succ k => exact h2 k b (by simpa using hb)

/-- The arguments `evalValueL` reads. -/
abbrev argsM (fr : Frame) (v : Value) : Res (List Val) :=
  v.args.toList.mapM fun a => Res.ofOption s!"v{v.id}: argument v{a} has no value" (fr.regs[a]?).join

theorem evalValueL_bind {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} (hm : argsM fr v = .ok argv) :
    evalValueL md env ctx fr v =
      (evalOpL md.faulting env ctx fr v argv (ctx.tys[v.id]?.getD .other)).bind
        (fun r => .ok (md.retype (ctx.tys[v.id]?.getD .other) r)) := by
  unfold evalValueL; simp only [argsM] at hm; rw [hm]; rfl

theorem argsM_ok {fr : Frame} {v : Value} (h : ∀ a ∈ v.args, ∃ z, fr.regs[a]? = some (some z)) :
    ∃ argv, argsM fr v = .ok argv :=
  mapM_ofOption_ok fun a ha => by
    obtain ⟨z, hz⟩ := h a (Array.mem_toList_iff.1 ha)
    exact ⟨z, by rw [hz]; rfl⟩

/-- The `k`-th argument value is the `k`-th argument's register. -/
theorem argsM_get {fr : Frame} {v : Value} {argv : List Val} (h : argsM fr v = .ok argv)
    {k : Nat} {a : ID} (ha : v.args[k]? = some a) :
    ∃ z, fr.regs[a]? = some (some z) ∧ argv[k]? = some z := by
  obtain ⟨-, h2⟩ := mapM_ofOption_spec h
  obtain ⟨z, hz, hk⟩ := h2 k a (by rw [Array.getElem?_toList]; exact ha)
  refine ⟨z, ?_, hk⟩
  cases hr : fr.regs[a]? with
  | none => rw [hr] at hz; cases hz
  | some o => rw [hr] at hz; simp at hz; rw [hz]

theorem argsM_length {fr : Frame} {v : Value} {argv : List Val} (h : argsM fr v = .ok argv) :
    argv.length = v.args.size := by
  simpa using (mapM_ofOption_spec h).1

/-- The last argument value is the last argument's register. -/
theorem argsM_last {fr : Frame} {v : Value} {argv : List Val} (h : argsM fr v = .ok argv)
    {z : Val} (hz : argv.getLast? = some z) :
    ∃ ℓ, v.args.back? = some ℓ ∧ fr.regs[ℓ]? = some (some z) := by
  have hl := argsM_length h
  have hne : argv ≠ [] := by intro h0; rw [h0] at hz; cases hz
  have hpos : 0 < argv.length := List.length_pos_iff.2 hne
  have hk : argv[argv.length - 1]? = some z := by
    rw [List.getLast?_eq_getElem?] at hz; exact hz
  have hsz : v.args.size - 1 < v.args.size := by omega
  obtain ⟨y, hy, hk'⟩ := argsM_get h (k := v.args.size - 1) (a := v.args[v.args.size - 1])
    (by simp [hsz])
  rw [hl] at hk; rw [hk] at hk'; cases hk'
  exact ⟨_, by simp [Array.back?, hsz], hy⟩

/-- The first argument value is the first argument's register. -/
theorem argsM_head {fr : Frame} {v : Value} {argv : List Val} (h : argsM fr v = .ok argv)
    {z : Val} (hz : argv.head? = some z) :
    ∃ p, v.args[0]? = some p ∧ fr.regs[p]? = some (some z) := by
  have hl := argsM_length h
  have hne : argv ≠ [] := by intro h0; rw [h0] at hz; cases hz
  have hpos : 0 < v.args.size := by rw [← hl]; exact List.length_pos_iff.2 hne
  obtain ⟨y, hy, hk⟩ := argsM_get h (k := 0) (a := v.args[0]) (by simp [hpos])
  rw [List.head?_eq_getElem?] at hz; rw [hz] at hk; cases hk
  exact ⟨_, by simp [hpos], hy⟩

/-! ## Ops -/

theorem actOps_generic {op : Op} (h : op ∈ actOps) : op.generic = false := by
  simp only [actOps, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;>
    subst h <;> rfl

/-- `evalOpL` of an op of `actOps` is `arm64Op`. -/
theorem evalOpL_act {faulting : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} (h : v.op ∈ actOps) :
    evalOpL faulting env ctx fr v argv ty = arm64Op faulting env ctx fr v argv ty := by
  simp only [actOps, List.mem_cons, List.not_mem_nil, or_false] at h
  unfold evalOpL
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;>
    rw [h] <;> rfl

/-- An op `LowerTerm.actOp` accepts is in `actOps` (the same 91 ops; for `evalOpL_eq`). -/
private theorem lowerActOp_mem (op : Op) (h : GoFV.Opt.LowerTerm.actOp op = true) : op ∈ actOps := by
  cases op <;> first | exact absurd h Bool.false_ne_true | decide +kernel

/-- `evalOpL` of an arm64 op not in `actOps`: `atomicRoot` for a root, else `Arm64.evalPure`. -/
theorem evalOpL_nonact {faulting : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} (hg : v.op.generic = false) (h : v.op ∉ actOps) :
    evalOpL faulting env ctx fr v argv ty =
      if isRoot v.op then atomicRoot v argv else pure (Arm64.evalPure v.op ty v.auxInt v.aux argv) := by
  apply evalOpL_of_not_actOp hg
  cases ha : GoFV.Opt.LowerTerm.actOp v.op
  · rfl
  · exact absurd (lowerActOp_mem _ ha) h

theorem mem_of_decide {op : Op} {l : List Op} (h : decide (op ∈ l) = true) : op ∈ l :=
  of_decide_eq_true h

/-! ## `nilFaults` -/

/-- An access through `a` faults when its address is in the nil page (`nilFaults`): `a`'s base
is the nil pointer. -/
def NilBase (a : Val) : Prop := ∃ b, Arm64.addr a 0 = some b ∧ b.isNil = true

theorem nilAccesses_nil_of {ctx : Ctx} {v : Value} {argv : List Val}
    (h0 : v.op.faultOnNilArg0 = false) (h1 : v.op.faultOnNilArg1 = false) :
    nilAccesses ctx v argv = [] := by
  unfold nilAccesses; simp [h0, h1]

theorem nilFaults_none_of {faulting : Bool} {ctx : Ctx} {v : Value} {argv : List Val}
    (h0 : v.op.faultOnNilArg0 = false) (h1 : v.op.faultOnNilArg1 = false) :
    nilFaults faulting ctx v argv = none := by
  unfold nilFaults
  rw [nilAccesses_nil_of h0 h1]
  split
  · rfl
  · split <;> simp

theorem nilFaults_mem {faulting : Bool} {ctx : Ctx} {v : Value} {argv : List Val} {m : Mem}
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

/-- The access `nilFaults` finds through the first argument, for an op that does not fault on
its second: a nil base and an address in the nil page. -/
theorem nilFaults_base0 {faulting : Bool} {ctx : Ctx} {v : Value} {argv : List Val} {m : Mem}
    (h1 : v.op.faultOnNilArg1 = false) (h : nilFaults faulting ctx v argv = some m) :
    ∃ a b q, argv.head? = some a ∧ Arm64.addr a 0 = some b ∧ b.isNil = true ∧
      q.nilFault = true ∧
      (if v.op.auxType == .SymOff then symAddr ctx v a else some b) = some q := by
  have hsel : ∀ (c : Bool) (l : List (Ptr × Ptr)) (x : Ptr × Ptr),
      x ∈ (if c = true then l else []) → x ∈ l := by
    intro c l x hx; cases c <;> simp_all
  unfold nilFaults at h
  split at h
  · cases h
  · split at h
    · split at h
      · rename_i hany
        obtain ⟨⟨b, q⟩, hm, hbq⟩ := List.any_eq_true.1 hany
        simp only [Bool.and_eq_true] at hbq
        unfold nilAccesses at hm
        dsimp only at hm
        rcases List.mem_append.1 (hsel _ _ _ hm) with hm | hm
        · have h0 : v.op.faultOnNilArg0 = true := by
            cases h0 : v.op.faultOnNilArg0
            · rw [h0] at hm; simp at hm
            · rfl
          rw [h0] at hm
          simp only [Bool.not_true, Bool.false_eq_true, ite_false, Option.mem_toList,
            Option.bind_eq_some_iff, Option.map_eq_some_iff] at hm
          obtain ⟨a, ha, b', hb', q', hq', heq⟩ := hm
          cases heq
          exact ⟨a, b, q, ha, hb', hbq.1, hbq.2, hq'⟩
        · simp [h1] at hm
      · cases h
    · cases h

/-- A symbolic value's address (`symAddr`) is a global or frame address, whatever its base. -/
theorem symAddr_symbolic {ctx : Ctx} {v : Value} (h : symbolic ctx.tabs v = true) :
    ∃ q, q.blk ≠ .nil ∧ ∀ a, symAddr ctx v a = some q := by
  unfold symbolic at h
  cases hx : v.aux with
  | none => simp [hx] at h
  | some n =>
    rw [hx] at h
    simp only [Option.bind_some] at h
    cases hd : ctx.tabs.aux? n with
    | none => simp [hd] at h
    | some d =>
      rw [hd] at h
      obtain ⟨_, kind⟩ := d
      cases kind with
      | sym name =>
        exact ⟨⟨.global name.toStringLossy, BitVec.ofInt 64 v.auxInt.toInt⟩, by simp,
          fun _ => by simp [symAddr, hx, hd]⟩
      | name =>
        refine ⟨⟨frameBlk ctx.tabs ctx.act n, BitVec.ofInt 64 v.auxInt.toInt⟩, ?_,
          fun _ => by simp [symAddr, hx, hd]⟩
        simp only [frameBlk]; split <;> simp
      | _ => simp at h

/-- A symbolic value's pair addresses (`pairAddr`) do not depend on its base. -/
theorem pairAddr_symbolic {ctx : Ctx} {v : Value} (h : symbolic ctx.tabs v = true) (n : Nat) :
    ∃ pq, ∀ a, pairAddr ctx v n a = some pq := by
  obtain ⟨q, -, hq⟩ := symAddr_symbolic h
  obtain ⟨q', -, hq'⟩ := symAddr_symbolic (ctx := ctx) (v := { v with auxInt := v.auxInt + Int64.ofNat n }) h
  exact ⟨(q, q'), fun a => by simp only [pairAddr, hq, hq', Option.bind_some, Option.map_some]⟩

/-- A nil-page access through `symAddr`: the base without a symbol, at some offset. -/
theorem symAddr_nilFault {ctx : Ctx} {v : Value} {a : Val} {q : Ptr}
    (h : symAddr ctx v a = some q) (hq : q.nilFault = true) : ∃ k, Arm64.addr a k = some q := by
  unfold symAddr at h
  split at h
  · rename_i n hx
    split at h
    · cases h; simp [Ptr.nilFault] at hq
    · cases h; simp only [Ptr.nilFault, frameBlk, Bool.and_eq_true, beq_iff_eq] at hq
      split at hq <;> simp at hq
    · cases h
  · exact ⟨_, h⟩

/-- `nilFaults` of a symbolic `symAddrOp` finds nothing. -/
theorem nilFaults_symbolic {faulting : Bool} {ctx : Ctx} {v : Value} {argv : List Val}
    (hop : v.op ∈ symAddrOps) (hs : symbolic ctx.tabs v = true) :
    nilFaults faulting ctx v argv = none := by
  obtain ⟨q, hq, hall⟩ := symAddr_symbolic hs
  have hf : v.op.faultOnNilArg1 = false ∧ v.op.auxType = .SymOff := by
    simp only [symAddrOps, ldOps, stOps, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hop
    rcases hop with ((h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h)|(h|h|h|h|h|h|h|h|h|h|h|h))|h <;>
      rw [h] <;> exact ⟨rfl, rfl⟩
  cases hn : nilFaults faulting ctx v argv with
  | none => rfl
  | some m =>
    obtain ⟨a, b, q', -, -, -, hq', hs'⟩ := nilFaults_base0 hf.1 hn
    rw [hf.2, hall a] at hs'
    simp only [beq_self_eq_true, ite_true, Option.some.injEq] at hs'
    subst hs'
    simp [Ptr.nilFault, hq] at hq'

/-- A nil base's address is in the nil page. -/
theorem Ptr.nilFault_of_isNil {b : Ptr} (h : b.isNil = true) : b.nilFault = true := by
  simp only [Ptr.isNil, Bool.and_eq_true, beq_iff_eq] at h
  simp [Ptr.nilFault, h.1, h.2, minZeroPage]

/-! ## `arm64Op` by class (faulting) -/

theorem arm64Op_actSafe {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (h : v.op ∈ actSafeOps) : ∃ y, arm64Op true env ctx fr v argv ty = .ok y := by
  simp only [actSafeOps, List.mem_cons, List.not_mem_nil, or_false] at h
  have hnf : nilFaults true ctx v argv = none := by
    apply nilFaults_none_of <;> rcases h with h|h|h|h|h <;> rw [h] <;> rfl
  unfold arm64Op
  simp only [hnf]
  rcases h with h|h|h|h|h <;> rw [h] <;> dsimp only <;> (repeat' split) <;> exact ⟨_, rfl⟩

/-- The body of `arm64Op` for a `faultOp` evaluates. -/
theorem arm64Op_fault_none {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (h : v.op ∈ faultOps) (hnf : nilFaults true ctx v argv = none) :
    ∃ y, arm64Op true env ctx fr v argv ty = .ok y := by
  simp only [faultOps, ldOps, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
  unfold arm64Op
  simp only [hnf]
  rcases h with (h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h)|(h|h|h|h|h|h|h|h) <;> rw [h] <;> dsimp only <;>
    first | exact ⟨_, rfl⟩ | ((repeat' split) <;> exact ⟨_, rfl⟩)

theorem arm64Op_fault {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (h : v.op ∈ faultOps) : (∃ y, arm64Op true env ctx fr v argv ty = .ok y) ∨
      ∃ m, argv.getLast? = some (.mem m) ∧ arm64Op true env ctx fr v argv ty = .panic .nilDeref m := by
  cases hnf : nilFaults true ctx v argv with
  | some m => exact .inr ⟨m, nilFaults_mem hnf, by unfold arm64Op; simp only [hnf]⟩
  | none => exact .inl (arm64Op_fault_none h hnf)

theorem ldOps_sub {op : Op} (h : op ∈ ldOps) : op ∈ faultOps ∧ op ∈ symAddrOps ∧ op ∈ actOps ∧
    op.faultOnNilArg1 = false ∧ op.auxType = .SymOff := by
  simp only [ldOps, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> decide

theorem faultOps_act {op : Op} (h : op ∈ faultOps) : op ∈ actOps := by
  simp only [faultOps, ldOps, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with (h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h)|(h|h|h|h|h|h|h|h) <;> subst h <;> decide

theorem symAddrOps_act {op : Op} (h : op ∈ symAddrOps) : op ∈ actOps := by
  simp only [symAddrOps, ldOps, stOps, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at h
  rcases h with ((h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h)|(h|h|h|h|h|h|h|h|h|h|h|h))|h <;> subst h <;>
    decide

theorem actSafeOps_act {op : Op} (h : op ∈ actSafeOps) : op ∈ actOps := by
  simp only [actSafeOps, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h|h|h|h|h <;> subst h <;> decide

/-- A load at a symbol or frame variable evaluates. -/
theorem arm64Op_symld {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (h : v.op ∈ ldOps) (hs : symbolic ctx.tabs v = true) :
    ∃ y, arm64Op true env ctx fr v argv ty = .ok y :=
  arm64Op_fault_none (ldOps_sub h).1 (nilFaults_symbolic (ldOps_sub h).2.1 hs)

/-- A load panics only with `nilDeref` of its memory, at a nil base. -/
theorem arm64Op_ld_panic {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} {e : Panic} {m : Mem} (h : v.op ∈ ldOps)
    (hp : arm64Op true env ctx fr v argv ty = .panic e m) :
    e = .nilDeref ∧ argv.getLast? = some (.mem m) ∧ ∃ a, argv.head? = some a ∧ NilBase a := by
  obtain ⟨hf, -, -, h1, hsym⟩ := ldOps_sub h
  cases hnf : nilFaults true ctx v argv with
  | none =>
    obtain ⟨y, hy⟩ := arm64Op_fault_none (ty := ty) (env := env) (fr := fr) hf hnf
    rw [hy] at hp; cases hp
  | some m' =>
    have hp' : arm64Op true env ctx fr v argv ty = .panic .nilDeref m' := by
      unfold arm64Op; simp only [hnf]
    rw [hp'] at hp; cases hp
    refine ⟨rfl, nilFaults_mem hnf, ?_⟩
    obtain ⟨a, b, -, ha, hb, hnil, -⟩ := nilFaults_base0 h1 hnf
    exact ⟨a, ha, b, hb, hnil⟩

/-- A `faultOp` panics only with `nilDeref` of its memory. -/
theorem arm64Op_fault_panic {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} {e : Panic} {m : Mem} (h : v.op ∈ faultOps)
    (hp : arm64Op true env ctx fr v argv ty = .panic e m) :
    e = .nilDeref ∧ argv.getLast? = some (.mem m) := by
  rcases arm64Op_fault (env := env) (fr := fr) (ty := ty) (argv := argv) h with ⟨y, hy⟩ | ⟨m', hm, hy⟩
  · rw [hy] at hp; cases hp
  · rw [hy] at hp; cases hp; exact ⟨rfl, hm⟩

/-! ## Nil checks -/

theorem nilCheck_cases {op : Op} (h : op.nilCheck = true) :
    op = .NilCheck ∨ op = .ARM64LoweredNilCheck := by
  unfold Op.nilCheck at h
  split at h
  · exact .inr rfl
  · exact .inl rfl
  · cases h

/-- A pointer word outside the nil block: what a nil check that passes has checked. -/
def NonNil (a : Val) : Prop := ∃ p, a.asPtrWord = some p ∧ p.blk ≠ .nil

theorem memRoot_nc_ok {ctx : Ctx} {w : Value} {argv : List Val} {y : Val} (hw : w.op = .NilCheck)
    (h : memRoot ctx w argv = .ok y) : ∃ a m, argv = [a, .mem m] ∧ y = a ∧ NonNil a := by
  unfold memRoot at h
  rw [hw] at h
  split at h
  all_goals first
    | (simp_all; done)
    | (split at h
       · rename_i p hp
         by_cases hb : (p.blk == .nil) = true
         · simp [hb] at h
         · simp only [hb, Bool.false_eq_true, ite_false, Res.ok.injEq] at h
           subst h
           exact ⟨_, _, rfl, rfl, p, hp, by simpa using hb⟩
       · cases h)
    | (split at h <;> cases h)

theorem memRoot_nc_panic {ctx : Ctx} {w : Value} {argv : List Val} {e : Panic} {m : Mem}
    (hw : w.op = .NilCheck) (h : memRoot ctx w argv = .panic e m) :
    e = .nilDeref ∧ ∃ a, argv = [a, .mem m] ∧ ∃ p, a.asPtrWord = some p ∧ p.blk = .nil := by
  unfold memRoot at h
  rw [hw] at h
  split at h
  all_goals first
    | (simp_all; done)
    | (split at h
       · rename_i p hp
         by_cases hb : (p.blk == .nil) = true
         · simp only [hb, ite_true, Res.panic.injEq] at h
           obtain ⟨rfl, rfl⟩ := h
           exact ⟨rfl, _, rfl, p, hp, by simpa using hb⟩
         · simp [hb] at h
       · cases h)
    | (split at h <;> cases h)

/-- The base of a pointer word is the pointer. -/
theorem addr_of_asPtrWord {a : Val} {p : Ptr} (h : a.asPtrWord = some p) : Arm64.addr a 0 = some p := by
  cases a with
  | ptr q => simp only [Val.asPtrWord, Option.some.injEq] at h; subst h; simp [Arm64.addr, Ptr.add]
  | int w x =>
    cases w <;> simp only [Val.asPtrWord, reduceCtorEq, Option.some.injEq] at h
    subst h; simp [Arm64.addr, Arm64.reg]
  | _ => simp [Val.asPtrWord] at h

/-- A pointer word outside the nil block has no nil base. -/
theorem NonNil.not_nilBase {a : Val} (h : NonNil a) (hb : NilBase a) : False := by
  obtain ⟨p, hp, hblk⟩ := h
  obtain ⟨b, hab, hnil⟩ := hb
  rw [addr_of_asPtrWord hp] at hab
  cases hab
  simp only [Ptr.isNil, Bool.and_eq_true, beq_iff_eq] at hnil
  exact hblk hnil.1

theorem evalOpL_ncG {faulting : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} (h : v.op = .NilCheck) :
    evalOpL faulting env ctx fr v argv ty = memRoot ctx v argv := by
  unfold evalOpL evalOp
  rw [h]
  rfl

theorem evalOpL_ncL {faulting : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} (h : v.op = .ARM64LoweredNilCheck) :
    evalOpL faulting env ctx fr v argv ty =
      match nilFaults faulting ctx v argv with
      | some m => .panic .nilDeref m
      | none =>
        if faulting && wildNil argv then .stuck s!"v{v.id}: {v.op.name}: nil check of a wild pointer"
        else memRoot ctx { v with op := .NilCheck } argv := by
  rw [evalOpL_act (by rw [h]; decide)]
  unfold arm64Op
  rw [h]
  rfl

/-- A nil check's evaluation does not read the shape it is evaluated at. -/
theorem evalOpL_nc_ty {faulting : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty ty' : Ty} (h : v.op.nilCheck = true) :
    evalOpL faulting env ctx fr v argv ty = evalOpL faulting env ctx fr v argv ty' := by
  rcases nilCheck_cases h with h | h
  · rw [evalOpL_ncG h, evalOpL_ncG h]
  · rw [evalOpL_ncL h, evalOpL_ncL h]

/-- An evaluated nil check returns its pointer. -/
theorem evalOpL_nc_ok {faulting : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} {y : Val} (h : v.op.nilCheck = true)
    (ho : evalOpL faulting env ctx fr v argv ty = .ok y) :
    ∃ a m, argv = [a, .mem m] ∧ y = a ∧ NonNil a := by
  rcases nilCheck_cases h with h | h
  · rw [evalOpL_ncG h] at ho; exact memRoot_nc_ok h ho
  · rw [evalOpL_ncL h] at ho
    split at ho
    · cases ho
    · split at ho
      · cases ho
      · exact memRoot_nc_ok rfl ho

/-- A lowered nil check that panics (memory ops faulting): `nilDeref` of its memory, at a nil
pointer. -/
theorem evalOpL_nc_panic {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} {e : Panic} {m : Mem} (h : v.op = .ARM64LoweredNilCheck)
    (ho : evalOpL true env ctx fr v argv ty = .panic e m) :
    e = .nilDeref ∧ argv.getLast? = some (.mem m) ∧ ∃ a, argv.head? = some a ∧ NilBase a := by
  rw [evalOpL_ncL h] at ho
  split at ho
  · rename_i m' hnf
    cases ho
    refine ⟨rfl, nilFaults_mem hnf, ?_⟩
    obtain ⟨a, b, -, ha, hb, hnil, -⟩ := nilFaults_base0 (by rw [h]; rfl) hnf
    exact ⟨a, ha, b, hb, hnil⟩
  · split at ho
    · cases ho
    · rename_i hw
      obtain ⟨he, a, ha, p, hp, hblk⟩ := memRoot_nc_panic rfl ho
      subst ha
      refine ⟨he, rfl, a, rfl, p, addr_of_asPtrWord hp, ?_⟩
      simp only [Bool.true_and, wildNil, List.head?_cons, Option.bind_some,
        addr_of_asPtrWord hp, Option.map_some, Option.getD_some, Ptr.wild, hblk,
        beq_self_eq_true, Bool.not_eq_true'] at hw
      simpa using hw

/-- **A lowered nil check of a nil pointer panics** with `nilDeref` of its memory (memory ops
faulting). -/
theorem evalOpL_nc_nil {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {ty : Ty} {a : Val}
    {m : Mem} (h : v.op = .ARM64LoweredNilCheck) (hb : NilBase a) :
    evalOpL true env ctx fr v [a, .mem m] ty = .panic .nilDeref m := by
  obtain ⟨b, hab, hnil⟩ := hb
  have hnf : nilFaults true ctx v [a, .mem m] = some m := by
    have h0 : Op.ARM64LoweredNilCheck.faultOnNilArg0 = true := rfl
    have h1 : Op.ARM64LoweredNilCheck.faultOnNilArg1 = false := rfl
    have hs : (Op.ARM64LoweredNilCheck.auxType == .SymOff) = false := rfl
    have hacc : nilAccesses ctx v [a, .mem m] = [(b, b)] := by
      unfold nilAccesses
      simp only [h, h0, h1, hs, Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_true,
        ite_false, List.head?_cons, Option.bind_some, hab, Option.map_some, Option.toList_some,
        Option.toList_none, List.append_nil]
    unfold nilFaults
    simp [hacc, hnil, Ptr.nilFault_of_isNil hnil]
  rw [evalOpL_ncL h, hnf]

/-! ## Symbolic `symAddrOp`s ignore their base -/

theorem ite_stuck_ne_ok {c : Prop} [Decidable c] {s1 s2 : String} {y : Val} :
    (if c then Res.stuck s1 else Res.stuck s2) ≠ (.ok y : Res Val) := by
  split <;> nofun

theorem ite_stuck_ne_panic {c : Prop} [Decidable c] {s1 s2 : String} {e : Panic} {m : Mem} :
    (if c then Res.stuck s1 else Res.stuck s2) ≠ (.panic e m : Res Val) := by
  split <;> nofun

theorem arm64Op_arg0 {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {ty : Ty} {a a' : Val}
    {rest : List Val} (hop : v.op ∈ symAddrOps) (hs : symbolic ctx.tabs v = true) :
    ResSim (arm64Op true env ctx fr v (a :: rest) ty) (arm64Op true env ctx fr v (a' :: rest) ty) := by
  obtain ⟨q, -, hall⟩ := symAddr_symbolic hs
  obtain ⟨_, h4⟩ := pairAddr_symbolic hs 4
  obtain ⟨_, h8⟩ := pairAddr_symbolic hs 8
  obtain ⟨_, h16⟩ := pairAddr_symbolic hs 16
  have hn : ∀ l, nilFaults true ctx v l = none := fun l => nilFaults_symbolic hop hs
  unfold arm64Op
  simp only [hn]
  simp only [symAddrOps, ldOps, stOps, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hop
  rcases hop with ((h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h)|(h|h|h|h|h|h|h|h|h|h|h|h))|h <;> rw [h] <;>
    dsimp only <;> simp only [hall, h4, h8, h16] <;>
    exact ⟨fun y hy => by
        split at hy <;> (try (obtain ⟨-, rfl⟩ := ‹_ ∧ rest = _›)) <;> simp_all [ite_stuck_ne_ok],
      fun e m hm => by
        split at hm <;> (try (obtain ⟨-, rfl⟩ := ‹_ ∧ rest = _›)) <;> simp_all [ite_stuck_ne_panic]⟩

/-! ## Classes -/

theorem cls_safe {tabs : Tables} {v : Value} (h : cls tabs v = .safe) :
    (v.op.generic = true ∧ specSafeOp v.op = true) ∨
      (v.op.generic = false ∧ ((v.op ∈ ldOps ∧ symbolic tabs v = true) ∨ v.op ∈ actSafeOps ∨
        (v.op ∉ actOps ∧ isRoot v.op = false))) := by
  unfold cls at h
  split at h
  · split at h
    · exact .inl ⟨‹_›, ‹_›⟩
    · cases h
  · rename_i hg
    refine .inr ⟨by simpa using hg, ?_⟩
    split at h
    · cases h
    split at h
    · rename_i hl
      simp only [ldOp, Bool.and_eq_true, decide_eq_true_eq] at hl
      exact .inl hl
    split at h
    · cases h
    split at h
    · rename_i ha; exact .inr (.inl (of_decide_eq_true ha))
    split at h
    · rename_i hn
      simp only [actOp, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hn
      exact .inr (.inr hn)
    · cases h

theorem cls_load {tabs : Tables} {v : Value} (h : cls tabs v = .load) :
    v.op.generic = false ∧ v.op ∈ faultOps := by
  unfold cls at h
  split at h
  · split at h <;> cases h
  · rename_i hg
    split at h
    · cases h
    split at h
    · cases h
    split at h
    · rename_i hf; exact ⟨by simpa using hg, of_decide_eq_true hf⟩
    split at h
    · cases h
    split at h <;> cases h

theorem cls_nil {tabs : Tables} {v : Value} (h : cls tabs v = .nil) :
    v.op = .ARM64LoweredNilCheck ∧ v.args.size = 2 := by
  unfold cls at h
  split at h
  · split at h <;> cases h
  · split at h
    · rename_i hn; simpa using hn
    split at h
    · cases h
    split at h
    · cases h
    split at h
    · cases h
    split at h <;> cases h

theorem mayPanic_false {tabs : Tables} {v : Value} (h : mayPanic tabs v = false) :
    (v.op.generic = true ∧ v.op.call = false ∧ v.op.nilCheck = false) ∨
      (v.op.generic = false ∧ cls tabs v = .safe) := by
  unfold mayPanic at h
  split at h
  · rename_i hg
    simp only [Bool.or_eq_false_iff] at h
    exact .inl ⟨hg, h⟩
  · rename_i hg
    exact .inr ⟨by simpa using hg, by simpa using h⟩

/-! ## Evaluation by class -/

theorem evalOp_specSafe {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {L : List Val} {ty : Ty}
    (hs : specSafeOp v.op = true) : ∃ r, evalOp env ctx fr v L ty = .ok r := by
  have hroot : isRoot v.op = false := by
    simp only [specSafeOp, Bool.and_eq_true, Bool.not_eq_true'] at hs; exact hs.1.1.1
  have hne : ∀ op, isRoot op = true → v.op ≠ op := fun op h he => by rw [he] at hroot; simp_all
  have hspec : v.op ≠ .Arg ∧ v.op ≠ .ArgIntReg := by
    simp only [specSafeOp, Bool.and_eq_true, bne_iff_ne, ne_eq] at hs
    exact ⟨hs.1.2, hs.2⟩
  unfold evalOp
  split
  · exact ⟨_, rfl⟩
  · exact absurd ‹_› hspec.1
  · exact absurd ‹_› hspec.2
  all_goals first
    | exact absurd ‹v.op = _› (hne _ (by decide))
    | exact ⟨_, rfl⟩
    | skip
  split
  · exact ⟨_, rfl⟩
  · rw [hroot]
    exact ⟨_, rfl⟩

/-- A `Cls.safe` value's op evaluates. -/
theorem evalOpL_safe {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val} {ty : Ty}
    (hc : cls ctx.tabs v = .safe) : ∃ r, evalOpL true env ctx fr v argv ty = .ok r := by
  rcases cls_safe hc with ⟨hg, hs⟩ | ⟨hg, (⟨hl, hs⟩ | ha | ⟨hna, hr⟩)⟩
  · rw [evalOpL_generic _ _ _ _ _ _ hg]; exact evalOp_specSafe hs
  · rw [evalOpL_act (ldOps_sub hl).2.2.1]; exact arm64Op_symld hl hs
  · rw [evalOpL_act (actSafeOps_act ha)]; exact arm64Op_actSafe ha
  · rw [evalOpL_nonact hg hna, hr]; exact ⟨_, rfl⟩

theorem evalValueL_args_ok {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {r : Res Val} (h : evalValueL md env ctx fr v = r) (hr : ∀ msg, r ≠ .stuck msg) :
    ∃ argv, argsM fr v = .ok argv := by
  cases hm : argsM fr v with
  | ok argv => exact ⟨argv, rfl⟩
  | panic e m => exact absurd hm mapM_ofOption_ne_panic
  | stuck msg =>
    unfold evalValueL at h
    simp only [argsM] at hm
    rw [hm] at h
    exact absurd h.symm (hr _)

/-- **A `Cls.safe` value evaluates** wherever its arguments have registers. -/
theorem evalValueL_safe {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    (hf : md.faulting = true) (hc : cls ctx.tabs v = .safe)
    (hargs : ∀ a ∈ v.args, ∃ z, fr.regs[a]? = some (some z)) :
    ∃ y, evalValueL md env ctx fr v = .ok y := by
  obtain ⟨argv, hm⟩ := argsM_ok hargs
  rw [evalValueL_bind hm, hf]
  obtain ⟨r, hr⟩ := evalOpL_safe (env := env) (fr := fr) (argv := argv)
    (ty := ctx.tys[v.id]?.getD .other) hc
  rw [hr]
  exact ⟨_, rfl⟩

/-- **A `Cls.load` value evaluates or panics with `nilDeref` of its last argument's memory.** -/
theorem evalValueL_load {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    (hf : md.faulting = true) (hc : cls ctx.tabs v = .load)
    (hargs : ∀ a ∈ v.args, ∃ z, fr.regs[a]? = some (some z)) :
    (∃ y, evalValueL md env ctx fr v = .ok y) ∨
      ∃ ℓ m, v.args.back? = some ℓ ∧ fr.regs[ℓ]? = some (some (.mem m)) ∧
        evalValueL md env ctx fr v = .panic .nilDeref m := by
  obtain ⟨-, hfo⟩ := cls_load hc
  obtain ⟨argv, hm⟩ := argsM_ok hargs
  rw [evalValueL_bind hm, hf, evalOpL_act (faultOps_act hfo)]
  rcases arm64Op_fault (env := env) (ctx := ctx) (fr := fr) (argv := argv)
    (ty := ctx.tys[v.id]?.getD .other) hfo with ⟨y, hy⟩ | ⟨m, hl, hy⟩
  · rw [hy]; exact .inl ⟨_, rfl⟩
  · rw [hy]
    obtain ⟨ℓ, hℓ, hr⟩ := argsM_last hm hl
    exact .inr ⟨ℓ, m, hℓ, hr, rfl⟩

/-- **What a panic says** (memory ops faulting): the value may panic; a `Cls.load` or `Cls.nil`
one panics with `nilDeref` of its last argument's memory; a load or nil check that panics has a
pointer-like first argument. -/
theorem evalValueL_panic_info {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {e : Panic} {m : Mem} (hf : md.faulting = true)
    (h : evalValueL md env ctx fr v = .panic e m) :
    mayPanic ctx.tabs v = true ∧
      ((cls ctx.tabs v = .load ∨ cls ctx.tabs v = .nil) →
        e = .nilDeref ∧ ∃ ℓ, v.args.back? = some ℓ ∧ fr.regs[ℓ]? = some (some (.mem m))) ∧
      ((v.op ∈ ldOps ∨ cls ctx.tabs v = .nil) →
        ∃ p a, v.args[0]? = some p ∧ fr.regs[p]? = some (some a) ∧ NilBase a) := by
  obtain ⟨argv, hm⟩ := evalValueL_args_ok h (by intro msg hh; cases hh)
  rw [evalValueL_bind hm, hf] at h
  generalize ctx.tys[v.id]?.getD .other = ty at h
  have ho : evalOpL true env ctx fr v argv ty = .panic e m := by
    cases ho : evalOpL true env ctx fr v argv ty with
    | ok r => rw [ho] at h; cases h
    | stuck msg => rw [ho] at h; cases h
    | panic e' m' => rw [ho] at h; cases h; rfl
  refine ⟨?_, fun hc => ?_, fun hc => ?_⟩
  · cases hp : mayPanic ctx.tabs v
    · exfalso
      rcases mayPanic_false hp with ⟨hg, hc, hn⟩ | ⟨-, hs⟩
      · rw [evalOpL_generic _ _ _ _ _ _ hg] at ho
        rcases evalOp_panic_op ho with h' | h'
        · rw [hc] at h'; cases h'
        · rw [h'] at hn; cases hn
      · obtain ⟨r, hr⟩ := evalOpL_safe (env := env) (fr := fr) (argv := argv) (ty := ty) hs
        rw [hr] at ho; cases ho
    · rfl
  · rcases hc with hc | hc
    · obtain ⟨-, hfo⟩ := cls_load hc
      rw [evalOpL_act (faultOps_act hfo)] at ho
      obtain ⟨he, hl⟩ := arm64Op_fault_panic hfo ho
      exact ⟨he, argsM_last hm hl⟩
    · obtain ⟨hnc, -⟩ := cls_nil hc
      obtain ⟨he, hl, -⟩ := evalOpL_nc_panic hnc ho
      exact ⟨he, argsM_last hm hl⟩
  · rcases hc with hc | hc
    · rw [evalOpL_act (ldOps_sub hc).2.2.1] at ho
      obtain ⟨-, -, a, ha, hpa⟩ := arm64Op_ld_panic hc ho
      obtain ⟨p, hp, hr⟩ := argsM_head hm ha
      exact ⟨p, a, hp, hr, hpa⟩
    · obtain ⟨hnc, -⟩ := cls_nil hc
      obtain ⟨-, -, a, ha, hpa⟩ := evalOpL_nc_panic hnc ho
      obtain ⟨p, hp, hr⟩ := argsM_head hm ha
      exact ⟨p, a, hp, hr, hpa⟩

/-- **An evaluated nil check returns its pointer**, at its shape. -/
theorem evalValueL_nc_ok {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {y : Val}
    (hnc : v.op.nilCheck = true) (h : evalValueL md env ctx fr v = .ok y) :
    ∃ p yp, v.args[0]? = some p ∧ fr.regs[p]? = some (some yp) ∧
      y = md.retype (ctx.tys[v.id]?.getD .other) yp ∧ NonNil yp := by
  obtain ⟨argv, hm⟩ := evalValueL_args_ok h (by intro msg hh; cases hh)
  rw [evalValueL_bind hm] at h
  cases ho : evalOpL md.faulting env ctx fr v argv (ctx.tys[v.id]?.getD .other) with
  | panic e m => rw [ho] at h; cases h
  | stuck msg => rw [ho] at h; cases h
  | ok r =>
    rw [ho] at h; cases h
    obtain ⟨a, m, hargv, hra, hnn⟩ := evalOpL_nc_ok hnc ho
    subst hargv
    obtain ⟨p, hp, hr⟩ := argsM_head hm rfl
    exact ⟨p, a, hp, hr, by rw [hra], hnn⟩

/-- **A nil check of a nil pointer on a memory panics with `nilDeref` of it** (memory ops
faulting). -/
theorem evalValueL_nc_nil {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {p ℓ : ID} {a : Val} {m : Mem} (hf : md.faulting = true)
    (hop : v.op = .ARM64LoweredNilCheck) (hargs : v.args = #[p, ℓ])
    (hp : fr.regs[p]? = some (some a)) (hb : NilBase a)
    (hl : fr.regs[ℓ]? = some (some (.mem m))) :
    evalValueL md env ctx fr v = .panic .nilDeref m := by
  have hm : argsM fr v = .ok [a, .mem m] := by
    simp only [argsM, hargs]
    simp [hp, hl, Res.ofOption]
    rfl
  rw [evalValueL_bind hm, hf, evalOpL_nc_nil hop hb]
  rfl

/-- **A nil check of a pointer outside the nil block on a memory evaluates** (memory ops faulting
or not). -/
theorem evalValueL_nc_pass {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {p ℓ : ID} {a : Val} {m : Mem}
    (hop : v.op = .ARM64LoweredNilCheck) (hargs : v.args = #[p, ℓ])
    (hp : fr.regs[p]? = some (some a)) (hn : NonNil a)
    (hl : fr.regs[ℓ]? = some (some (.mem m))) :
    ∃ y, evalValueL md env ctx fr v = .ok y := by
  obtain ⟨q, hq, hblk⟩ := hn
  have hm : argsM fr v = .ok [a, .mem m] := by
    simp only [argsM, hargs]
    simp [hp, hl, Res.ofOption]
    rfl
  have hacc : nilAccesses ctx v [a, .mem m] = [(q, q)] := by
    have h0 : Op.ARM64LoweredNilCheck.faultOnNilArg0 = true := rfl
    have h1 : Op.ARM64LoweredNilCheck.faultOnNilArg1 = false := rfl
    have hs : (Op.ARM64LoweredNilCheck.auxType == .SymOff) = false := rfl
    unfold nilAccesses
    simp only [hop, h0, h1, hs, Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_true,
      ite_false, List.head?_cons, Option.bind_some, addr_of_asPtrWord hq, Option.map_some,
      Option.toList_some, Option.toList_none, List.append_nil]
  have hqn : q.isNil = false := by simp [Ptr.isNil, hblk]
  have hnf : nilFaults md.faulting ctx v [a, .mem m] = none := by
    unfold nilFaults
    split
    · rfl
    · simp [hacc, hqn]
  have hw : wildNil [a, .mem m] = false := by
    simp only [wildNil, List.head?_cons, Option.bind_some, addr_of_asPtrWord hq, Option.map_some,
      Option.getD_some, Ptr.wild]
    simp [hblk]
  rw [evalValueL_bind hm, evalOpL_ncL hop, hnf]
  simp only [hw, Bool.and_false, Bool.false_eq_true, ite_false]
  cases hr : memRoot ctx { v with op := .NilCheck } [a, .mem m] with
  | ok y => exact ⟨_, rfl⟩
  | panic e m' =>
    obtain ⟨-, a', ha', q', hq', hb'⟩ := memRoot_nc_panic rfl hr
    simp only [List.cons.injEq, Val.mem.injEq, and_true] at ha'
    obtain ⟨rfl, -⟩ := ha'
    rw [hq] at hq'; cases hq'
    exact absurd hb' hblk
  | stuck msg =>
    exfalso
    unfold memRoot at hr
    simp [hq, hblk] at hr

/-! ## Parameter pieces -/

/-- **A parameter's register piece evaluates** (`argOK`) in a frame with an image per
parameter. -/
theorem evalValueL_argOK {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    (h : argOK ctx.tabs ctx.params v = true) (himg : fr.images.size = ctx.params.size) :
    ∃ y, evalValueL md env ctx fr v = .ok y := by
  unfold argOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hop, hargs⟩, haux⟩ := h
  have hm : argsM fr v = .ok [] := by
    have h0 : v.args = #[] := by simpa using hargs
    simp only [argsM, h0]; rfl
  rw [evalValueL_bind hm]
  have hg : v.op.generic = true := by rw [hop]; rfl
  rw [evalOpL_generic _ _ _ _ _ _ hg]
  split at haux
  · rename_i d n off hx
    have hex : ∃ x, x ∈ ctx.params ∧ (x == some n) = true :=
      ⟨some n, Array.mem_of_contains_eq_true haux, by simp⟩
    have hi := Array.findIdx?_eq_some_of_exists hex
    have hlt := Array.findIdx_lt_size_of_exists hex
    have hev : evalOp env ctx fr v [] (ctx.tys[v.id]?.getD .other) =
        argVal ctx fr n off (ctx.tys[v.id]?.getD .other) := by
      unfold evalOp; rw [hop]; dsimp only; rw [hx]
    rw [hev]
    unfold argVal
    rw [hi]
    dsimp only
    rw [Array.getElem?_eq_getElem (by rw [himg]; exact hlt)]
    dsimp only
    split <;> exact ⟨_, rfl⟩
  · cases haux

/-! ## Pointers outside the nil block -/

/-- A pointer outside the nil block, inside its window, is one at a word shape. -/
theorem nonNil_retype_ptr (md : LMode) {t : Ty} (ht : wordShape t = true) {p : Ptr}
    (hp : p.blk ≠ .nil) (hw : p.inWindow = true) : NonNil (md.retype t (.ptr p)) := by
  refine ⟨p, ?_, hp⟩
  unfold wordShape at ht
  split at ht
  · cases md with
    | mk low faulting =>
      cases low <;> simp [LMode.retype, Val.retypeL, Val.widen, Val.retype, Ptr.word_asPtrWord hw]
  · cases md with
    | mk low faulting =>
      cases low <;> simp [LMode.retype, Val.retypeL, Val.widen, Val.retype, Ptr.word_asPtrWord hw]
  · cases ht

/-- **`SP` and `GetG` hold pointers outside the nil block** at a word shape: the
outgoing-arguments area and the current goroutine. -/
theorem evalValueL_spg {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {y : Val}
    (hop : v.op = .SP ∨ v.op = .GetG) (hw : wordShape (ctx.tys[v.id]?.getD .other) = true)
    (h : evalValueL md env ctx fr v = .ok y) : NonNil y := by
  obtain ⟨argv, hm⟩ := evalValueL_args_ok h (by intro msg hh; cases hh)
  rw [evalValueL_bind hm] at h
  have hg : v.op.generic = true := by rcases hop with h | h <;> rw [h] <;> rfl
  rw [evalOpL_generic _ _ _ _ _ _ hg] at h
  rcases hop with hop | hop
  · have he : evalOp env ctx fr v argv (ctx.tys[v.id]?.getD .other) =
        .ok (.ptr ⟨.outargs ctx.act, 0⟩) := by
      unfold evalOp; rw [hop]; simp only [frameVal, hop]; rfl
    rw [he] at h; cases h
    exact nonNil_retype_ptr md hw (by simp) (Ptr.inWindow_zero _)
  · have he : evalOp env ctx fr v argv (ctx.tys[v.id]?.getD .other) =
        .ok (.ptr ⟨.global "runtime.g", 0⟩) := by
      unfold evalOp; rw [hop]; simp only [frameVal, hop]; rfl
    rw [he] at h; cases h
    exact nonNil_retype_ptr md hw (by simp) (Ptr.inWindow_zero _)

/-- At a word shape, a value has a nil base only if it had one: `md.retype` keeps an integer's
or a boolean's register and a pointer's address (`Ptr.word`), and makes anything else `poison`. -/
theorem nilBase_of_retype_word (md : LMode) {t : Ty} (ht : wordShape t = true) {c : Val}
    (h : NilBase (md.retype t c)) : NilBase c := by
  obtain ⟨b, hb, hnil⟩ := h
  refine ⟨b, ?_, hnil⟩
  -- a pointer's word addresses the pointer
  have hword : ∀ p : Ptr, Arm64.addr p.word 0 = some b → Arm64.addr (.ptr p) 0 = some b := by
    intro p hp
    rcases Ptr.word_cases p with ⟨-, e⟩ | ⟨hc, a, ha, e⟩ | ⟨-, e⟩ <;> rw [e] at hp
    · exact hp
    · have hq : (Val.int .w64 a).asPtrWord = some p := by
        simp only [Val.asPtrWord, Ptr.ofAddr_addr hc ha]
      rw [addr_of_asPtrWord hq] at hp
      rw [addr_of_asPtrWord (rfl : (Val.ptr p).asPtrWord = some p)]
      exact hp
    · simp [Arm64.addr, Arm64.reg] at hp
  have ht' : t = .int .w64 ∨ ∃ e, t = .ptr e := by
    unfold wordShape at ht
    split at ht
    · exact .inl rfl
    · exact .inr ⟨_, rfl⟩
    · cases ht
  obtain ⟨low, faulting⟩ := md
  rcases ht' with rfl | ⟨e, rfl⟩ <;>
  · cases c with
    | ptr p =>
      apply hword
      cases low <;> simpa [LMode.retype, Val.retypeL, Val.widen, Val.retype] using hb
    | int w x =>
      clear hword
      cases low <;> cases w <;>
        simp_all [LMode.retype, Val.retypeL, Val.widen, Val.retype, Arm64.addr, Arm64.reg,
          Width.bits]
    | _ =>
      clear hword
      cases low <;>
        simp_all [LMode.retype, Val.retypeL, Val.widen, Val.retype, Arm64.addr, Arm64.reg]

/-- **The closure pointer has no nil base** at a word shape when the frame's closure context has
none (`poison` without a context; `ArgPtrsOK`: the top-level context is no nil pointer). -/
theorem evalValueL_clo {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {y : Val}
    (hop : v.op = .ARM64LoweredGetClosurePtr) (hc : ∀ c, fr.closure = some c → ¬ NilBase c)
    (hw : wordShape (ctx.tys[v.id]?.getD .other) = true)
    (h : evalValueL md env ctx fr v = .ok y) : ¬ NilBase y := by
  obtain ⟨argv, hm⟩ := evalValueL_args_ok h (by intro msg hh; cases hh)
  rw [evalValueL_bind hm, evalOpL_act (by rw [hop]; decide)] at h
  have he : arm64Op md.faulting env ctx fr v argv (ctx.tys[v.id]?.getD .other) =
      .ok (fr.closure.getD .poison) := by
    have hnf : nilFaults md.faulting ctx v argv = none := by
      apply nilFaults_none_of <;> rw [hop] <;> rfl
    (unfold arm64Op; simp only [hnf]; rw [hop]) <;> rfl
  rw [he] at h; cases h
  intro hb
  have hb' := nilBase_of_retype_word md hw hb
  cases hcl : fr.closure with
  | none =>
    rw [hcl] at hb'
    obtain ⟨b, hb'', -⟩ := hb'
    simp [Arm64.addr, Arm64.reg] at hb''
  | some c => rw [hcl] at hb'; exact hc c hcl hb'

/-! ## Value correspondence -/

/-- `evalOpL` of a symbolic `symAddrOp` ignores its first argument. -/
theorem evalOpL_arg0 {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {ty : Ty} {a a' : Val}
    {rest : List Val} (hop : v.op ∈ symAddrOps) (hs : symbolic ctx.tabs v = true) :
    ResSim (evalOpL true env ctx fr v (a :: rest) ty) (evalOpL true env ctx fr v (a' :: rest) ty) := by
  rw [evalOpL_act (symAddrOps_act hop), evalOpL_act (symAddrOps_act hop)]
  exact arm64Op_arg0 hop hs

theorem ResSim.trans {r1 r2 r3 : Res Val} (h12 : ResSim r1 r2) (h23 : ResSim r2 r3) :
    ResSim r1 r3 :=
  ⟨fun y h => h23.1 y (h12.1 y h), fun e m h => h23.2 e m (h12.2 e m h)⟩

/-- **Value correspondence.** A value `v'` of another function (context `ctx'`, frame `fr'` of
the same activation) with `v`'s op, aux, auxint and ID evaluates where `v` does, alike, when its
arguments hold `v`'s arguments' registers, except possibly the base of a symbolic `symAddrOp`
(the result alike when the shapes agree; a nil check may change its shape). -/
theorem evalValueL_vc {md : LMode} {env : Env} {ctx ctx' : Ctx} {fr fr' : Frame} {v v' : Value}
    (hf : md.faulting = true) (hop : v'.op = v.op) (haux : v'.aux = v.aux)
    (hai : v'.auxInt = v.auxInt) (hid : v'.id = v.id) (hsz : v'.args.size = v.args.size)
    (htabs : ctx'.tabs = ctx.tabs) (hpar : ctx'.params = ctx.params) (hact : ctx'.act = ctx.act)
    (hsx : sxOf ctx'.f v' = sxOf ctx.f v) (hfr : fr' = { fr with regs := fr'.regs })
    (hty : ctx'.tys[v.id]? = ctx.tys[v.id]? ∨ v.op.nilCheck = true)
    (hargs : ∀ (k : Nat) (a : ID), v.args[k]? = some a → ∃ a' y, v'.args[k]? = some a' ∧
      fr.regs[a]? = some (some y) ∧ ∃ y', fr'.regs[a']? = some (some y') ∧
        (y' = y ∨ (k = 0 ∧ v.op ∈ symAddrOps ∧ symbolic ctx.tabs v = true))) :
    (∀ y, evalValueL md env ctx fr v = .ok y → ∃ y', evalValueL md env ctx' fr' v' = .ok y' ∧
      (ctx'.tys[v.id]? = ctx.tys[v.id]? → y' = y)) ∧
    (∀ e m, evalValueL md env ctx fr v = .panic e m → evalValueL md env ctx' fr' v' = .panic e m) := by
  -- the argument lists
  obtain ⟨argv, hm⟩ := argsM_ok (fr := fr) (v := v) fun a ha => by
    obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 ha
    obtain ⟨-, y, -, hy, -⟩ := hargs k a hk
    exact ⟨y, hy⟩
  obtain ⟨argv', hm'⟩ := argsM_ok (fr := fr') (v := v') fun a' ha' => by
    obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 ha'
    have hkl : k < v.args.size := by rw [← hsz]; exact (Array.getElem?_eq_some_iff.1 hk).1
    obtain ⟨a'', -, hk', -, y', hy', -⟩ := hargs k v.args[k] (by simp [hkl])
    rw [hk] at hk'; cases hk'
    exact ⟨y', hy'⟩
  have hl := argsM_length hm
  have hl' := argsM_length hm'
  -- position `k` of the two lists
  have hpos : ∀ k (hk : k < v.args.size), ∃ y y', argv[k]? = some y ∧ argv'[k]? = some y' ∧
      (y' = y ∨ (k = 0 ∧ v.op ∈ symAddrOps ∧ symbolic ctx.tabs v = true)) := by
    intro k hk
    obtain ⟨a', y, hk', hy, y', hy', hrel⟩ := hargs k v.args[k] (by simp [hk])
    obtain ⟨z, hz, hz'⟩ := argsM_get hm (k := k) (a := v.args[k]) (by simp [hk])
    obtain ⟨z', hzz, hz''⟩ := argsM_get hm' hk'
    rw [hy] at hz; cases hz
    rw [hy'] at hzz; cases hzz
    exact ⟨y, y', hz', hz'', hrel⟩
  have hrel : argv' = argv ∨ (v.op ∈ symAddrOps ∧ symbolic ctx.tabs v = true ∧
      ∃ a a' rest, argv = a :: rest ∧ argv' = a' :: rest) := by
    by_cases hx : v.op ∈ symAddrOps ∧ symbolic ctx.tabs v = true
    · cases argv with
      | nil =>
        left
        have : argv'.length = 0 := by rw [hl', hsz, ← hl]; rfl
        exact List.eq_nil_of_length_eq_zero this
      | cons a rest =>
        cases argv' with
        | nil => simp at hl'; simp at hl; omega
        | cons a' rest' =>
          refine .inr ⟨hx.1, hx.2, a, a', rest, rfl, ?_⟩
          congr 1
          apply List.ext_getElem?
          intro k
          by_cases hk : k + 1 < v.args.size
          · obtain ⟨y, y', h1, h2, hr⟩ := hpos (k + 1) hk
            simp only [List.getElem?_cons_succ] at h1 h2
            rw [h1, h2]
            rcases hr with rfl | ⟨h0, -⟩
            · rfl
            · omega
          · have e1 : rest.length ≤ k := by simp at hl; omega
            have e2 : rest'.length ≤ k := by simp at hl'; omega
            rw [List.getElem?_eq_none e1, List.getElem?_eq_none e2]
    · left
      apply List.ext_getElem?
      intro k
      by_cases hk : k < v.args.size
      · obtain ⟨y, y', h1, h2, hr⟩ := hpos k hk
        rw [h1, h2]
        rcases hr with rfl | ⟨-, h3, h4⟩
        · rfl
        · exact absurd ⟨h3, h4⟩ hx
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  -- the op
  have hT : evalOpL true env ctx' fr' v' argv' (ctx'.tys[v'.id]?.getD .other) =
      evalOpL true env ctx fr v argv' (ctx'.tys[v.id]?.getD .other) := by
    rw [hfr, evalOpL_frame, evalOpL_congr hop haux hai hid htabs hpar hact hsx, hid]
  have hS : ResSim (evalOpL true env ctx fr v argv (ctx.tys[v.id]?.getD .other))
      (evalOpL true env ctx fr v argv' (ctx'.tys[v.id]?.getD .other)) := by
    have hty' : evalOpL true env ctx fr v argv' (ctx'.tys[v.id]?.getD .other) =
        evalOpL true env ctx fr v argv' (ctx.tys[v.id]?.getD .other) := by
      rcases hty with h | h
      · rw [h]
      · exact evalOpL_nc_ty h
    rw [hty']
    rcases hrel with h | ⟨h1, h2, a, a', rest, rfl, rfl⟩
    · rw [h]; exact ResSim.of_eq rfl
    · exact evalOpL_arg0 h1 h2
  rw [evalValueL_bind hm, hf]
  rw [evalValueL_bind hm', hf, hT, hid]
  refine ⟨fun y hy => ?_, fun e m hp => ?_⟩
  · cases hr : evalOpL true env ctx fr v argv (ctx.tys[v.id]?.getD .other) with
    | ok r =>
      rw [hr] at hy; cases hy
      rw [hS.1 r hr]
      exact ⟨_, rfl, fun h => by rw [h]⟩
    | panic e m => rw [hr] at hy; cases hy
    | stuck msg => rw [hr] at hy; cases hy
  · cases hr : evalOpL true env ctx fr v argv (ctx.tys[v.id]?.getD .other) with
    | ok r => rw [hr] at hp; cases hp
    | panic e' m' =>
      rw [hr] at hp; cases hp
      rw [hS.2 _ _ hr]; rfl
    | stuck msg => rw [hr] at hp; cases hp

/-! ## `Select1` of an acquiring load -/

theorem word_ne_mem (p : Ptr) (m : Mem) : p.word ≠ .mem m := by
  unfold Ptr.word; split
  · nofun
  · split <;> nofun

theorem Val.retype_eq_mem {t : Ty} {v : Val} {m : Mem} (h : v.retype t = .mem m) : v = .mem m := by
  unfold Val.retype at h
  split at h <;>
    first
    | exact h
    | exact absurd h (word_ne_mem _ _)
    | (split at h <;> cases h)
    | (unfold Val.ofStr at h; split at h <;> cases h)
    | (unfold Val.ofSlice at h; split at h <;> cases h)
    | cases h

theorem Val.widen_eq_mem {t : Ty} {v : Val} {m : Mem} (h : v.widen t = .mem m) : v = .mem m := by
  unfold Val.widen at h
  split at h <;>
    first
    | exact h
    | (split at h <;> cases h)
    | cases h

/-- A value retyped to a memory was that memory. -/
theorem LMode.retype_eq_mem {md : LMode} {t : Ty} {v : Val} {m : Mem}
    (h : md.retype t v = .mem m) : v = .mem m := by
  unfold LMode.retype at h
  split at h
  · exact Val.widen_eq_mem (Val.retype_eq_mem h)
  · exact Val.retype_eq_mem h

theorem LMode.retype_poison (md : LMode) (t : Ty) : md.retype t .poison = .poison := by
  unfold LMode.retype Val.retypeL
  split <;> cases t <;> rfl

/-- **The memory of an acquiring load's result** at its shape is its memory argument's. -/
theorem atomicLoad_mem {md : LMode} {t : Ty} {argv vs : List Val} {m : Mem}
    (h : md.retype t (atomicLoad t argv) = .tuple vs) (h1 : vs.getD 1 .poison = .mem m) :
    argv.getLast? = some (.mem m) := by
  unfold atomicLoad at h
  split at h
  · rename_i a m'
    split at h
    · rename_i p vt hp
      unfold LMode.retype at h
      split at h <;>
        simp [Val.retypeL, Val.widen, Val.widenList, Val.retype, Val.retypePre] at h <;>
        subst h <;> simp at h1 <;> subst h1 <;> rfl
    · rw [LMode.retype_poison] at h; cases h
  · rw [LMode.retype_poison] at h; cases h

theorem evalOpL_select1 {faulting : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} (h : v.op = .Select1) :
    evalOpL faulting env ctx fr v argv ty = .ok (Tuple.select 1 argv) := by
  have hg : v.op.generic = true := by rw [h]; rfl
  rw [evalOpL_generic _ _ _ _ _ _ hg]
  have hr : isRoot v.op = false := by rw [h]; rfl
  rw [CSE.evalOp_tail hr (by rw [h]; nofun) (by rw [h]; nofun) (by rw [h]; nofun)
    (by rw [h]; nofun) (by rw [h]; nofun)]
  have hf : frameVal ctx v = none := by unfold frameVal; rw [h]
  rw [hf, h]; rfl

theorem ldarOp_cases {op : Op} (h : ldarOp op = true) :
    op = .ARM64LDAR ∨ op = .ARM64LDARB ∨ op = .ARM64LDARW := by
  simpa [ldarOp, or_assoc] using h

theorem ldarOp_act {op : Op} (h : ldarOp op = true) : op ∈ actOps := by
  rcases ldarOp_cases h with h | h | h <;> rw [h] <;> decide

theorem arm64Op_ldar {faulting : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} (h : ldarOp v.op = true) :
    arm64Op faulting env ctx fr v argv ty =
      match nilFaults faulting ctx v argv with
      | some m => .panic .nilDeref m
      | none => .ok (atomicLoad ty argv) := by
  unfold arm64Op
  cases nilFaults faulting ctx v argv with
  | some m => rfl
  | none => rcases ldarOp_cases h with h | h | h <;> rw [h] <;> rfl

/-- **A `Select1` of an acquiring load holds the load's memory argument's memory.** -/
theorem evalValueL_select1_ldar {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {vz vl : Value}
    {l : ID} {m : Mem} {yl : Val} (hz : vz.op = .Select1) (hza : vz.args.toList = [l])
    (hl : ldarOp vl.op = true) (hyl : fr.regs[l]? = some (some yl))
    (hevl : evalValueL md env ctx fr vl = .ok yl)
    (hevz : evalValueL md env ctx fr vz = .ok (.mem m)) :
    ∃ ℓ, vl.args.back? = some ℓ ∧ fr.regs[ℓ]? = some (some (.mem m)) := by
  -- the `Select1` reads the second component of `yl`
  obtain ⟨argv, hm⟩ := evalValueL_args_ok hevz (by intro msg hh; cases hh)
  rw [evalValueL_bind hm, evalOpL_select1 hz] at hevz
  have h2 := LMode.retype_eq_mem (Res.ok.inj hevz)
  have hargv : argv = [yl] := by
    have hlen := argsM_length hm
    have h0 : vz.args[0]? = some l := by rw [← Array.getElem?_toList, hza]; rfl
    obtain ⟨z, hz', hk⟩ := argsM_get hm h0
    rw [hyl] at hz'; cases hz'
    have hsz : vz.args.size = 1 := by rw [← Array.length_toList, hza]; rfl
    rw [hsz] at hlen
    match argv, hlen, hk with
    | [a], _, hk => simp at hk; rw [hk]
  subst hargv
  unfold Tuple.select at h2
  split at h2
  · rename_i vs hvs
    cases hvs
    -- the `LDAR*`
    obtain ⟨argl, hml⟩ := evalValueL_args_ok hevl (by intro msg hh; cases hh)
    rw [evalValueL_bind hml, evalOpL_act (ldarOp_act hl), arm64Op_ldar hl] at hevl
    cases hnf : nilFaults md.faulting ctx vl argl with
    | some mm => rw [hnf] at hevl; cases hevl
    | none =>
      rw [hnf] at hevl
      exact argsM_last hml (atomicLoad_mem (Res.ok.inj hevl) h2)
  · cases h2

/-! ## The function of the context -/

/-- `arm64Op` reads its context's function only for `MOVDreg`/`MOVDnop`. -/
theorem arm64Op_withF {faulting : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} (F : Func) (hm : v.op ≠ .ARM64MOVDreg)
    (hn : v.op ≠ .ARM64MOVDnop) :
    arm64Op faulting env { ctx with f := F } fr v argv ty = arm64Op faulting env ctx fr v argv ty := by
  unfold arm64Op
  rw [show nilFaults faulting { ctx with f := F } v argv = nilFaults faulting ctx v argv from rfl]
  cases nilFaults faulting ctx v argv with
  | some m => rfl
  | none =>
    dsimp only
    split
    all_goals first | rfl | (exfalso; simp_all; done)

/-- `evalOpL` reads its context's function only for `MOVDreg`/`MOVDnop`. -/
theorem evalOpL_withF {faulting : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} (F : Func) (hm : v.op ≠ .ARM64MOVDreg)
    (hn : v.op ≠ .ARM64MOVDnop) :
    evalOpL faulting env { ctx with f := F } fr v argv ty = evalOpL faulting env ctx fr v argv ty := by
  rw [evalOpL_eq, evalOpL_eq]
  split
  · exact evalOp_congr rfl rfl rfl rfl rfl rfl rfl
  · split
    · exact arm64Op_withF F hm hn
    · rfl

/-- `evalValueL` reads its context's function only for `MOVDreg`/`MOVDnop`. -/
theorem evalValueL_withF {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    (F : Func) (hm : v.op ≠ .ARM64MOVDreg) (hn : v.op ≠ .ARM64MOVDnop) :
    evalValueL md env { ctx with f := F } fr v = evalValueL md env ctx fr v := by
  unfold evalValueL
  simp only [evalOpL_withF F hm hn]

end GoFV.Proof.SchedL

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt

/-- `y`, read as a pointer word, is nil or a pointer that is not wild (`Ptr.wild`). -/
def PtrOK (y : Val) : Prop := ∃ p, y.asPtrWord = some p ∧ p.wild = false

/-- In frame `fr` (mode `md`), every pointer-shaped register piece of a parameter of `f`
(`ScheduleCheck.argPtr`) evaluates to nil or a pointer that is not wild. -/
def ArgPtrsAt (md : LMode) (env : Env) (tabs : Tables) (f : Func) (fr : Frame) : Prop :=
  ∀ x v, f.value? x = some v →
    ScheduleCheck.argPtr tabs (Ctx.makeL tabs f).params (Ctx.makeL tabs f).tys f x = true →
    ∀ y, evalValueL md env (Ctx.makeL tabs f) fr v = .ok y → PtrOK y

/-- **The pointer parameters are valid** (`docs/plans/semantics2.md` §6): on the input `args`,
`mem`, every pointer-shaped register piece of a parameter of `f` (`ArgIntReg` at a `.ptr` shape)
reads nil or a pointer that is not wild, in `runLF`'s entry frame. A Go-level assumption: Go's
type system and the garbage collector require a pointer parameter to be nil or valid; `unsafe`
code that forges a wild pointer is outside the model. `schedule` may move a nil check of such a
piece before a fault on the same memory (`ScheduleCheck.swapOK`).

The top-level closure context (`Env.closure`) has no nil base: a closure is entered through its
funcval, and the caller loads the code word from it before the call
(`cmd/compile/internal/ssagen/ssa.go:5141-5149`, `rawLoad` of the closure), a load that faults
on nil. So a load off the closure pointer cannot fault (`ScheduleCheck.isNN`). -/
def ArgPtrsOK (tabs : Tables) (f : Func) (env : Env) (args : List Val) (mem : Mem) : Prop :=
  ArgPtrsAt ⟨f.lowered, true⟩ env tabs f (entryFrame env (Ctx.makeL tabs f) args mem) ∧
    ∀ c, env.closure = some c → ¬ SchedL.NilBase c

/-- Outside a closure (`env.closure = none`), `ArgPtrsOK` is the condition on the parameter
pieces alone. -/
theorem argPtrsOK_iff_of_none {tabs : Tables} {f : Func} {env : Env} (h : env.closure = none)
    {args : List Val} {mem : Mem} :
    ArgPtrsOK tabs f env args mem ↔
      ArgPtrsAt ⟨f.lowered, true⟩ env tabs f (entryFrame env (Ctx.makeL tabs f) args mem) :=
  ⟨fun h' => h'.1, fun h' => ⟨h', fun c hc => by rw [h] at hc; cases hc⟩⟩

/-- A parameter's register piece reads no register: `ArgPtrsAt` holds in every frame equal up
to the registers. -/
theorem ArgPtrsAt.regs {md : LMode} {env : Env} {tabs : Tables} {f : Func} {fr fr' : Frame}
    (h : ArgPtrsAt md env tabs f fr) (hfr : fr' = { fr with regs := fr'.regs }) :
    ArgPtrsAt md env tabs f fr' := by
  intro x v hv hp y hy
  have ha : v.args = #[] := by
    unfold ScheduleCheck.argPtr at hp
    rw [hv] at hp
    simp only [ScheduleCheck.argOK, Bool.and_eq_true, beq_iff_eq, Array.isEmpty_iff] at hp
    exact hp.1.1.2
  rw [← evalValueL_congr hfr (fun a h => by rw [ha] at h; simp at h)] at hy
  exact h x v hv hp y hy

/-- `ArgPtrsOK` holds when `f` has no pointer-shaped register piece of a parameter and the
closure context, if any, has no nil base. -/
theorem argPtrsOK_of_none {tabs : Tables} {f : Func}
    (h : (List.range f.valueTab.size).all
      (fun x => !ScheduleCheck.argPtr tabs (Ctx.makeL tabs f).params (Ctx.makeL tabs f).tys f x) =
        true)
    (env : Env) (args : List Val) (mem : Mem)
    (hc : ∀ c, env.closure = some c → ¬ SchedL.NilBase c) :
    ArgPtrsOK tabs f env args mem := by
  refine ⟨fun x v hv hp => ?_, hc⟩
  have hx : x < f.valueTab.size := by
    simp only [Func.value?, Option.join_eq_some_iff] at hv
    exact (Array.getElem?_eq_some_iff.1 hv).1
  have := List.all_eq_true.1 h x (List.mem_range.2 hx)
  rw [hp] at this
  cases this

/-- In frame `fr`, every pointer-shaped value (`f`'s `runL` shapes) that a nil check of `f`
checks reads nil or a pointer that is not wild, if it has a register. -/
def NilRegsOK (tabs : Tables) (f : Func) (fr : Frame) : Prop :=
  ∀ y vy q, f.value? y = some vy → vy.op.nilCheck = true → vy.args[0]? = some q →
    ScheduleCheck.ptrShape ((Ctx.makeL tabs f).tys[q]?.getD .other) = true →
    ∀ z, fr.regs[q]? = some (some z) → PtrOK z

/-- Value `v` of `f` with its arguments bypassed (`ScheduleCheck.rep`): what `schedule`'s output
evaluates in its place. -/
def hoisted (f : Func) (v : Value) : Value := { v with args := v.args.map (ScheduleCheck.rep f) }

/-- `H'` is frame `H` with the registers of some values of `f` that `schedule` may hoist
(`ScheduleCheck.hoistOp`: 64-bit loads and selections) set, one after the other, to their
evaluation (`hoisted`, mode `md`) in the frame so far. -/
inductive HoistExt (md : LMode) (env : Env) (tabs : Tables) (f : Func) (H : Frame) : Frame → Prop
  | refl : HoistExt md env tabs f H H
  | step {H' : Frame} {a : ID} {va : Value} {z : Val} : HoistExt md env tabs f H H' →
      f.value? a = some va → ScheduleCheck.hoistOp va.op = true →
      evalValueL md env (Ctx.makeL tabs f) H' (hoisted f va) = .ok z →
      HoistExt md env tabs f H (H'.set a z)

/-- From frame `H`: the value `q` that the nil check `y` of `f` checks, bypassed (`rep`),
evaluated as `schedule` hoists it (`hoisted`) in any frame that extends `H` by hoisted values
(`HoistExt`), reads nil or a pointer that is not wild. -/
def HoistOKAt (md : LMode) (env : Env) (tabs : Tables) (f : Func) (y : ID) (H : Frame) : Prop :=
  ∀ H', HoistExt md env tabs f H H' → ∀ vy q0 vq, f.value? y = some vy → vy.args[0]? = some q0 →
    f.value? (ScheduleCheck.rep f q0) = some vq →
    ∀ z, evalValueL md env (Ctx.makeL tabs f) H' (hoisted f vq) = .ok z → PtrOK z

end GoFV.Proof

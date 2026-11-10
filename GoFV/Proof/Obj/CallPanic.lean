import GoFV.Proof.Obj.G60

variable [GoFV.SSA.Sem.Addrs]

/-!
# Calls whose callee panics (`docs/plans/proofs3.md` §6, §9)

A static call of slice G60 that panics in `runLoc` (its callee panicked, `callOp`): genssa's
Progs run the no-ops before the `CALL sym(SB)` and the `CALL` (`X30` the return address, the PC the
callee's symbol), where the runtime hook panics with the same panic by the callee contract of the
activation's mode (trusted): `CallPanicOK` (as `CallOK` for a callee that returns) or, in G48's
mode (the `outargs` block at `SP`, `SepFromW`), `CallPanicOKS` (as `CallOKS`, also at G48's calls
with stack arguments or results, on `callRegsS`; `CallPanicOKAt`): `g60_callPanic` (`runLoc` →
`runProg` on P0), `g60_obj_callPanic` (→ `runMach` on the linked words, `obj_panic`). A function
with no arm64 op has no call (`nl30_ops`); in one with, what `vkind60` accepts of a call `vkind49`
accepts (a call is no op of G52–G59's groups, `vkind60_ok49`) or G48's `callKind48` (a call with
stack arguments or results, on `callRegsS`, `callKind48_facts`, in G48's mode); what `vkind49`
accepts of a call `vkind51` accepts (`vkind49_ok51`: a call is no frame-variable access), and
`vkind51` of a call is
`vkind47`'s (`vkind51_eq50`, `vkind50_eq47`: a call is no G51 op, pair load or select), which is
`vkind46`'s or G47's
`callKind47`
(`vkind47_call`). `vkind46`'s is `vkind45`'s (`vkind46_eq45`), so `vkind44`'s
(`vkind45_eq44`), `vkind43`'s (`vkind44_eq43`), `vkind42`'s (`vkind43_eq42`), `vkind41`'s
(`vkind42_eq41`), `vkind40`'s (`vkind41_eq40`), `vkind38`'s (`vkind40_eq38`) and `vkind28`'s
(`vkind38_eq28`), whose static calls are G15's (`vk28_vk18`, `vk18_call`), with the ABI registers
in `R0`–`R15`; `callKind47`'s (`callKind47_facts`) admits `F0`–`F15`, an argument there at a float
shape read from its V register (`argsV`).

An interface or closure call that panics: the no-ops, then `CALL (Rn)` to the code pointer in
`Rn`, where the callee's hook panics with the same panic by `ICallPanicOK` (trusted, as `ICallOK`)
or, in G48's mode, `ICallPanicOKS` (as `ICallOKS`; `ICallPanicOKAt`):
`g60_icallPanic`, `g60_obj_icallPanic`. What `vkind60` accepts of such a call `vkind49` accepts
(`vkind60_ok49`; G48's `kind48` takes none, `kind48_icall`), what `vkind49` accepts of it
`vkind51` accepts (`vkind49_ok51`), and `vkind51`'s is `vkind47`'s (`vkind51_eq50`, `vkind50_eq47`),
which is `vkind10`'s, `icallKind`
(`vkind46_eq45`, `vkind45_eq44`, `vkind44_eq43`, `vkind43_eq42`, `vkind42_eq41`, `vkind41_eq40`,
`vkind40_eq38`, `vkind38_eq28`, `vkind28_icall`, `icallKind_facts`), or G47's `icallKind47`
(`icallKind47_facts`), with `F0`–`F15` admitted alike (`vkind47_icall`).
-/

namespace GoFV.Proof.Obj

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj
open GoFV.Proof.Gen

/-- **The callee contract for a panic** at the static call `v` from `s`, which panics with `e`: at
every machine state `m₁` at the callee's symbol that is `m` but for `X30`, with the arguments in
their ABI registers `ins` and the memory injected (`CallSpec`'s premises), the runtime hook
panics with `e` (trusted, as `CallOK`). -/
def CallPanicOK (H : Hooks) (E : MatchEnv) (g : G2In) (L : Link) (lc : LocCtx) (s : LocState)
    (v : Value) (m : MState) (e : Panic) : Prop :=
  v.op = .ARM64CALLstatic → ∀ name abi cabi ins outs y (args : List Val) (mm : Mem) (m₁ : MState),
    callOf? lc.ctx.tabs v.aux = some (name, abi, cabi) →
    callRegsZ lc.ctx.tabs cabi = .ok (ins, outs) → g.syms[y]? = some (name, abi) →
    args.length = v.args.toList.dropLast.length →
    (∀ (j : Nat) (a : ID) (x : Val), v.args.toList.dropLast[j]? = some a → args[j]? = some x →
      s.read lc a = .ok x) →
    s.mem = .mem mm → m₁.pc = L.sym y → m₁.sp = m.sp → m₁.v = m.v → m₁.nzcv = m.nzcv →
    m₁.mem = m.mem → (∀ k, k ≠ 30 → m₁.x k = m.x k) →
    args.length = ins.length →
    (∀ (j r : Nat) (x : Val), ins[j]? = some r → args[j]? = some x → RegRel E.ι x m₁ r) →
    MemInj E.ι mm m₁.mem → KeysNodup mm → SepFrom E.ι (StkAt E) mm →
    ∃ m', H.call m₁ = some (.panicked e m')

/-- **The callee contract for a panic in an activation whose `outargs` block sits at `SP`**
(trusted, as `CallOKS`; `MatchEnv.outSP`, G48's mode): `CallPanicOK` with the separation
`SepFromW` in place of `SepFrom`, at the register arguments of the call's ABI (`callRegsZ`) or, at a
static call with stack arguments or results, of the ABI without them (`callRegsS`, as G48's
`CallOKStk`): the hook at the callee's symbol panics with `e`. -/
def CallPanicOKS (H : Hooks) (E : MatchEnv) (g : G2In) (L : Link) (lc : LocCtx) (s : LocState)
    (v : Value) (m : MState) (e : Panic) : Prop :=
  v.op = .ARM64CALLstatic → ∀ name abi cabi ins outs y (args : List Val) (mm : Mem) (m₁ : MState),
    callOf? lc.ctx.tabs v.aux = some (name, abi, cabi) →
    (callRegsZ lc.ctx.tabs cabi = .ok (ins, outs) ∨ callRegsS cabi = .ok (ins, outs)) →
    g.syms[y]? = some (name, abi) →
    args.length = v.args.toList.dropLast.length →
    (∀ (j : Nat) (a : ID) (x : Val), v.args.toList.dropLast[j]? = some a → args[j]? = some x →
      s.read lc a = .ok x) →
    s.mem = .mem mm → m₁.pc = L.sym y → m₁.sp = m.sp → m₁.v = m.v → m₁.nzcv = m.nzcv →
    m₁.mem = m.mem → (∀ k, k ≠ 30 → m₁.x k = m.x k) →
    args.length = ins.length →
    (∀ (j r : Nat) (x : Val), ins[j]? = some r → args[j]? = some x → RegRel E.ι x m₁ r) →
    MemInj E.ι mm m₁.mem → KeysNodup mm → SepFromW E.ι (StkAt E) mm →
    ∃ m', H.call m₁ = some (.panicked e m')

/-- The static-call panic contract of mode `w`: `CallPanicOK` (`false`) or `CallPanicOKS`
(`true`). -/
def CallPanicOKAt : Bool → Hooks → MatchEnv → G2In → Link → LocCtx → LocState → Value → MState →
    Panic → Prop
  | false, H, E, g, L, lc, s, v, m, e => CallPanicOK H E g L lc s v m e
  | true, H, E, g, L, lc, s, v, m, e => CallPanicOKS H E g L lc s v m e

/-- `CallPanicOKAt` at the ABI registers `callRegsZ` gives, in the separation of its mode. -/
theorem CallPanicOKAt.z {w : Bool} {H : Hooks} {E : MatchEnv} {g : G2In} {L : Link} {lc : LocCtx}
    {s : LocState} {v : Value} {m : MState} {e : Panic} (h : CallPanicOKAt w H E g L lc s v m e) :
    v.op = .ARM64CALLstatic → ∀ name abi cabi ins outs y (args : List Val) (mm : Mem)
      (m₁ : MState),
      callOf? lc.ctx.tabs v.aux = some (name, abi, cabi) →
      callRegsZ lc.ctx.tabs cabi = .ok (ins, outs) → g.syms[y]? = some (name, abi) →
      args.length = v.args.toList.dropLast.length →
      (∀ (j : Nat) (a : ID) (x : Val), v.args.toList.dropLast[j]? = some a → args[j]? = some x →
        s.read lc a = .ok x) →
      s.mem = .mem mm → m₁.pc = L.sym y → m₁.sp = m.sp → m₁.v = m.v → m₁.nzcv = m.nzcv →
      m₁.mem = m.mem → (∀ k, k ≠ 30 → m₁.x k = m.x k) →
      args.length = ins.length →
      (∀ (j r : Nat) (x : Val), ins[j]? = some r → args[j]? = some x → RegRel E.ι x m₁ r) →
      MemInj E.ι mm m₁.mem → KeysNodup mm → SepAt w E.ι (StkAt E) mm →
      ∃ m', H.call m₁ = some (.panicked e m') := by
  cases w with
  | false => exact h
  | true =>
    intro hop name abi cabi ins outs y args mm m₁ hc hr
    exact h hop name abi cabi ins outs y args mm m₁ hc (.inl hr)

/-- A static call of G18's kinds is `VK15.call`'s. -/
theorem vk18_call {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK18 lc g v kd)
    (hop : v.op = .ARM64CALLstatic) :
    ∃ name abi cabi ins outs, callOf? lc.ctx.tabs v.aux = some (name, abi, cabi) ∧
      callRegsZ lc.ctx.tabs cabi = .ok (ins, outs) ∧ (∀ r ∈ ins ++ outs, r < 16) ∧
      v.args.toList.dropLast.length = ins.length ∧
      (∀ a r, (a, r) ∈ v.args.toList.dropLast.zip ins → lc.home a = some (.reg r)) ∧
      kd = .prog (callPat g name abi) := by
  cases h with
  | stIdx h => rw [hop] at h; cases h
  | g17 h =>
    cases h with
    | getG h => rw [hop] at h; cases h
    | g16 h =>
      cases h with
      | addSh h => rw [hop] at h; cases h
      | g15 h =>
        cases h with
        | g14 hne _ => exact absurd hop hne
        | call _ hcall hcr _ _ _ _ h16 hlen hargs _ _ =>
          exact ⟨_, _, _, _, _, hcall, hcr, h16, hlen, hargs, rfl⟩

/-- A static call of G28's kinds is G18's. -/
theorem vk28_vk18 {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (hVK : VK28 lc g v kd)
    (h : v.op = .ARM64CALLstatic) : VK18 lc g v kd := by
  cases hVK with
  | memEq h' => rw [h] at h'; cases h'
  | g27 _ h27 =>
    cases h27 with
    | logSh h' => rw [h] at h'; cases h'
    | g25 _ h25 =>
      cases h25 with
      | csel h' => rw [h] at h'; cases h'
      | csel0 h' => rw [h] at h'; cases h'
      | tst h' => rw [h] at h'; cases h'
      | tstw h' => rw [h] at h'; cases h'
      | g24 _ _ h24 =>
        cases h24 with
        | sp h' => rw [h] at h'; cases h'
        | g23 _ h23 =>
          cases h23 with
          | cset h' => rw [h] at h'; simp [Cond.ofOp] at h'
          | g22 _ h22 =>
            cases h22 with
            | ldp h' => rw [h] at h'; cases h'
            | stp h' => rw [h] at h'; cases h'
            | g21 _ h21 =>
              cases h21 with
              | regSame h' => rw [h] at h'; cases h'
              | regMov h' => rw [h] at h'; cases h'
              | g20 _ h20 =>
                cases h20 with
                | nop h' => rw [h] at h'; cases h'
                | g19 _ h19 =>
                  cases h19 with
                  | pb h' => rw [h] at h'; cases h'
                  | g18 _ h18 => exact h18

/-- `vkind38` of an op that none of G32's, G33's, G36's, G37's and G38's own kinds take is
`vkind28`'s. -/
theorem vkind38_eq28 {lc : LocCtx} {g : G2In} {v : Value} (h1 : un33? v.op = none)
    (h2 : v.op ≠ .ARM64UBFIZ) (h3 : v.op ≠ .ARM64SRAconst) (h4 : v.op ≠ .ARM64CMNWconst)
    (h5 : bin32? v.op = none) (h6 : binK32? v.op = none) (h7 : un32? v.op = none)
    (h8 : stlr? v.op = none) (h9 : v.op ≠ .ARM64CSINC) (h10 : sh36? v.op = none)
    (h11 : shOp36? v.op = none) (h12 : v.op ≠ .ARM64TST) (h13 : full37? v.op = none)
    (h14 : w37? v.op = none) (h15 : un37? v.op = none) (h16 : madd37? v.op = none)
    (h17 : v.op ≠ .ARM64SBFX) (h18 : ldar? v.op = none) (h19 : v.op ≠ .Select0)
    (h20 : v.op ≠ .Select1) : vkind38 lc g v = vkind28 lc g v := by
  simp [vkind38, selLdar, vkind37, vkind36, vkind33, vkind32, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]

/-- `vkind40` of an op other than `InitMem` is `vkind38`'s. -/
theorem vkind40_eq38 {lc : LocCtx} {g : G2In} {v : Value} (h : v.op ≠ .InitMem) :
    vkind40 lc g v = vkind38 lc g v := by
  simp [vkind40, h]

/-- `vkind41` of an op other than G41's compares is `vkind40`'s. -/
theorem vkind41_eq40 {lc : LocCtx} {g : G2In} {v : Value} (h1 : v.op ≠ .ARM64CMNconst)
    (h2 : cmpSh41? v.op = none) : vkind41 lc g v = vkind40 lc g v := by
  simp [vkind41, h1, h2]

/-- `vkind42` of an op other than `ANDconst` is `vkind41`'s. -/
theorem vkind42_eq41 {lc : LocCtx} {g : G2In} {v : Value} (h : v.op ≠ .ARM64ANDconst) :
    vkind42 lc g v = vkind41 lc g v := by
  unfold vkind42
  cases vkind41 lc g v with
  | ok kd => rfl
  | error e => simp [h]

/-- `vkind38` of a static call is `vkind28`'s. -/
theorem vkind38_call {lc : LocCtx} {g : G2In} {v : Value} (hop : v.op = .ARM64CALLstatic) :
    vkind38 lc g v = vkind28 lc g v := by
  apply vkind38_eq28 <;> rw [hop] <;> first | rfl | nofun

/-- What `callKind47` accepted: `VK47.call`'s facts. -/
theorem callKind47_facts {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : callKind47 lc g v = .ok kd) :
    ∃ name abi cabi ins outs, callOf? lc.ctx.tabs v.aux = some (name, abi, cabi) ∧
      callRegsZ lc.ctx.tabs cabi = .ok (ins, outs) ∧ (∀ r ∈ ins ++ outs, r < 16 ∨ (31 ≤ r ∧ r < 47)) ∧
      v.args.toList.dropLast.length = ins.length ∧
      (∀ a r, (a, r) ∈ v.args.toList.dropLast.zip ins → lc.home a = some (.reg r)) ∧
      (∀ a r, (a, r) ∈ v.args.toList.dropLast.zip ins → 31 ≤ r → fTy (lc.ty a) = true) ∧
      kd = .prog (callPat g name abi) := by
  unfold callKind47 at h
  by_cases ht : (lc.temps[v.id]?).join = none
  · simp only [ht, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    next name abi cabi hcall =>
      obtain ⟨⟨ins, outs⟩, hcr, h⟩ := ex_bind_eq_ok h
      obtain ⟨-, h⟩ := ex_guard h
      split at h
      next m hm =>
        obtain ⟨-, h⟩ := ex_guard h
        obtain ⟨h16, h⟩ := ex_guard h
        obtain ⟨hlen, h⟩ := ex_guard h
        obtain ⟨hargs, h⟩ := ex_guard h
        obtain ⟨hfa, h⟩ := ex_guard h
        simp only [beq_iff_eq] at hlen
        refine ⟨name, abi, cabi, ins, outs, hcall, hcr,
          fun r hr => abiRegOK_spec ((List.all_eq_true.mp h16) r hr), hlen, fun a r har => ?_,
          fArgsOK_spec hfa, ?_⟩
        · have := (List.all_eq_true.mp hargs) (a, r) har
          simpa only [beq_iff_eq, regHome?_eq] using this
        · split at h
          all_goals first
            | (simp [ex_throw, ex_bind_error] at h; done)
            | (obtain ⟨-, h⟩ := ex_guard h
               obtain ⟨-, h⟩ := ex_guard h
               obtain ⟨-, h⟩ := ex_guard h
               cases h
               rfl)
      next => simp [ex_throw] at h
    next => simp [ex_throw] at h
  · simp [ht, ex_throw, ex_bind_error] at h

/-- A static call `vkind47` accepted: `vkind46`'s (G15's, through `vkind28`), its ABI registers in
`R0`–`R15`, or G47's `callKind47`, with `F0`–`F15` admitted and an argument there at a float
shape. -/
theorem vkind47_call {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (hop : v.op = .ARM64CALLstatic) (h : vkind47 lc g v = .ok kd) :
    ∃ name abi cabi ins outs, callOf? lc.ctx.tabs v.aux = some (name, abi, cabi) ∧
      callRegsZ lc.ctx.tabs cabi = .ok (ins, outs) ∧ (∀ r ∈ ins ++ outs, r < 16 ∨ (31 ≤ r ∧ r < 47)) ∧
      v.args.toList.dropLast.length = ins.length ∧
      (∀ a r, (a, r) ∈ v.args.toList.dropLast.zip ins → lc.home a = some (.reg r)) ∧
      (∀ a r, (a, r) ∈ v.args.toList.dropLast.zip ins → 31 ≤ r → fTy (lc.ty a) = true) ∧
      kd = .prog (callPat g name abi) := by
  unfold vkind47 at h
  cases h46 : vkind46 lc g v with
  | ok kd' =>
    rw [h46] at h
    cases h
    rw [vkind46_eq45 (by rw [hop]; simp [fops46]),
      vkind45_eq44 (by rw [hop]; rfl) (by rw [hop]; rfl),
      vkind44_eq43 (by rw [hop]; rfl), vkind43_eq42 (by rw [hop]; nofun),
      vkind42_eq41 (by rw [hop]; nofun),
      vkind41_eq40 (by rw [hop]; nofun) (by rw [hop]; rfl),
      vkind40_eq38 (by rw [hop]; nofun), vkind38_call hop] at h46
    obtain ⟨-, hVK⟩ := vkind28_spec h46 (by rw [hop]; rfl)
    obtain ⟨name, abi, cabi, ins, outs, hcall, hcr, h16, hlen, hargs, rfl⟩ :=
      vk18_call (vk28_vk18 hVK hop) hop
    exact ⟨name, abi, cabi, ins, outs, hcall, hcr, fun r hr => .inl (h16 r hr), hlen, hargs,
      fun _ r har hr => absurd (h16 r (List.mem_append_left _ (List.of_mem_zip har).2))
        (by omega), rfl⟩
  | error e =>
    rw [h46] at h
    simp only [fcall47, hop, ↓reduceIte] at h
    exact callKind47_facts h

/-- What `callKind48` accepted: `callKind47_facts` on the ABI without the stack-assigned inputs
and outputs (`callRegsS`). -/
theorem callKind48_facts {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : callKind48 lc g v = .ok kd) :
    ∃ name abi cabi ins outs, callOf? lc.ctx.tabs v.aux = some (name, abi, cabi) ∧
      callRegsS cabi = .ok (ins, outs) ∧ (∀ r ∈ ins ++ outs, r < 16 ∨ (31 ≤ r ∧ r < 47)) ∧
      v.args.toList.dropLast.length = ins.length ∧
      (∀ a r, (a, r) ∈ v.args.toList.dropLast.zip ins → lc.home a = some (.reg r)) ∧
      (∀ a r, (a, r) ∈ v.args.toList.dropLast.zip ins → 31 ≤ r → fTy (lc.ty a) = true) ∧
      kd = .prog (callPat g name abi) := by
  unfold callKind48 at h
  by_cases ht : (lc.temps[v.id]?).join = none
  · simp only [ht, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    next name abi cabi hcall =>
      obtain ⟨⟨ins, outs⟩, hcr, h⟩ := ex_bind_eq_ok h
      obtain ⟨-, h⟩ := ex_guard h
      split at h
      next m hm =>
        obtain ⟨-, h⟩ := ex_guard h
        obtain ⟨h16, h⟩ := ex_guard h
        obtain ⟨hlen, h⟩ := ex_guard h
        obtain ⟨hargs, h⟩ := ex_guard h
        obtain ⟨hfa, h⟩ := ex_guard h
        simp only [beq_iff_eq] at hlen
        refine ⟨name, abi, cabi, ins, outs, hcall, hcr,
          fun r hr => abiRegOK_spec ((List.all_eq_true.mp h16) r hr), hlen, fun a r har => ?_,
          fArgsOK_spec hfa, ?_⟩
        · have := (List.all_eq_true.mp hargs) (a, r) har
          simpa only [beq_iff_eq, regHome?_eq] using this
        · split at h
          all_goals first
            | (simp [ex_throw, ex_bind_error] at h; done)
            | (obtain ⟨-, h⟩ := ex_guard h
               obtain ⟨-, h⟩ := ex_guard h
               obtain ⟨-, h⟩ := ex_guard h
               cases h
               rfl)
      next => simp [ex_throw] at h
    next => simp [ex_throw] at h
  · simp [ht, ex_throw, ex_bind_error] at h

/-- **A static call of slice G60 whose callee panics**: from a `LocMatch`ed P0 state, the Progs
of the call run to the callee's symbol, where the runtime panics with `e` (`CallPanicOKAt` of the
mode `osp`, which is `true` for a function that needs G48's mode, `hn48`: a call G48 accepts, on
`callRegsS`, is
`CallPanicOKS`'s). -/
theorem g60_callPanic {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {osp : Bool}
    (hc : checkG60L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64CALLstatic) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s osp) (hok : CallPanicOKAt osp H E g L lc s v m e)
    (hn48 : needs48 lc = true → osp = true) :
    ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  cases hl0 : lc.ctx.f.lowered with
  | false =>
    rcases nl30_ops (checkNL30_of_60L hl0 hc) hbid hb hi hv (by rw [hop]; rfl) with
      h | h | h | h <;>
      rw [h] at hop <;> cases hop
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, hsyms, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, -, -, -⟩ :=
    checkG60L_spec hl0 hc
  obtain ⟨b, j, js, e', next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk] at hkd
  -- the call's ABI registers: `vkind47`'s (`callRegsZ`), or G48's on `callRegsS` (mode `true`)
  have hfacts : ∃ name abi cabi ins outs, callOf? c.cx.lc.ctx.tabs v.aux = some (name, abi, cabi) ∧
      (callRegsZ c.cx.lc.ctx.tabs cabi = .ok (ins, outs) ∨
        (osp = true ∧ callRegsS cabi = .ok (ins, outs))) ∧
      (∀ r ∈ ins ++ outs, r < 16 ∨ (31 ≤ r ∧ r < 47)) ∧
      v.args.toList.dropLast.length = ins.length ∧
      (∀ a r, (a, r) ∈ v.args.toList.dropLast.zip ins → c.cx.lc.home a = some (.reg r)) ∧
      (∀ a r, (a, r) ∈ v.args.toList.dropLast.zip ins → 31 ≤ r → fTy (c.cx.lc.ty a) = true) ∧
      kd = .prog (callPat c.g name abi) := by
    rcases vkind60_ok49 (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl)
      (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl)
      (by rw [hop]; rfl) hkd with hkd | ⟨e0, hkd⟩
    · have hkd := vkind49_ok51 (by rw [hop]; nofun) (by rw [hop]; rfl) (by rw [hop]; rfl)
        (by rw [hop]; nofun) (by rw [hop]; nofun) hkd
      rw [vkind51_eq50 (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl),
        vkind50_eq47 (by rw [hop]; rfl) (by rw [hop]; nofun) (by rw [hop]; nofun)] at hkd
      obtain ⟨name, abi, cabi, ins, outs, h1, h2, h3, h4, h5, h6, h7⟩ := vkind47_call hop hkd
      exact ⟨name, abi, cabi, ins, outs, h1, .inl h2, h3, h4, h5, h6, h7⟩
    · rcases kind48_cases hkd with ⟨-, hkd⟩ | ⟨hne, -⟩
      · obtain ⟨name, abi, cabi, ins, outs, h1, h2, h3, h4, h5, h6, h7⟩ := callKind48_facts hkd
        cases ho : osp
        · have ht : take48 c.cx.lc v = false := by
            cases h : take48 c.cx.lc v
            · rfl
            · exact absurd (hn48 (take48_of_needs48 hl0 hv h)) (by rw [ho]; decide)
          exact ⟨name, abi, cabi, ins, outs, h1, .inl (take48_call ht hop h1 h2), h3, h4, h5, h6,
            h7⟩
        · exact ⟨name, abi, cabi, ins, outs, h1, .inr ⟨rfl, h2⟩, h3, h4, h5, h6, h7⟩
      · exact absurd hop hne
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have hR : KRead c.cx.lc v (kAt c.cx.lc kt bid blk i).get := kread_of_reads hreads
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  obtain ⟨name, abi, cabi, ins, outs, hcall', hcr, h16, hlen, hargs, hfa, rfl⟩ := hfacts
  -- the machine: no-ops, then the `CALL`
  obtain ⟨k, -, hk', hokp, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
  rw [pc_eta hm hj] at hstar
  obtain ⟨has, -, -, -, -, -, ht1, ht2, ht3, y, hy1, hy⟩ := callPat_spec hokp
  let m₁ : MState :=
    { m with x := (fun q => if q = 30 then pcAt text c.cx.ps.toList (k + 1) else m.x q),
             pc := (Link.byId sym text az ez c.cx.ps.toList).sym y }
  have hm1x : ∀ q, q ≠ 30 → m₁.x q = m.x q := fun q hq => by
    show (if q = 30 then _ else m.x q) = m.x q
    exact ite_eq_right_iff.2 fun h => absurd h hq
  have hcstep : progStep (Link.byId sym text az ez c.cx.ps.toList) c.cx.ps.toList[k]
      { m with pc := pcAt text c.cx.ps.toList k } = .ok m₁ := by
    rw [progStep_callSym (nextAddr_pcAt F.nodup hk') has ht1 ht2 ht3 hy1, wX_pc]
    simp only [MState.wX, show ¬ ((30 : Reg) = 31) by decide, ↓reduceIte]
    rfl
  -- the arguments, read from their ABI registers (an X register, or a V register by `argsV`)
  have hargs' : ∀ a ∈ v.args.toList.dropLast, ∃ x, s.read c.cx.lc a = .ok x ∧
      ∀ r, c.cx.lc.home a = some (.reg r) → RegRel E.ι x m₁ r := by
    intro a ha
    obtain ⟨j0, hj0, rfl⟩ := List.getElem_of_mem ha
    have hjin : j0 < ins.length := hlen ▸ hj0
    have hz : (v.args.toList.dropLast[j0], ins[j0]) ∈ v.args.toList.dropLast.zip ins :=
      List.mem_of_getElem? (List.getElem?_zip_eq_some.2 ⟨List.getElem?_eq_getElem hj0,
        List.getElem?_eq_getElem hjin⟩)
    have hh := hargs _ _ hz
    by_cases hr31 : 31 ≤ ins[j0]
    · obtain ⟨x, hx, hxv⟩ := argsV F hm hinv.core hR (by rw [hop]; nofun)
        (fun a ha => List.dropLast_subset _ ha) hargs hfa _ _ hz hr31
      refine ⟨x, hx, fun r hr => ?_⟩
      rw [hh] at hr
      cases hr
      exact ⟨fun q hq => (by rw [objX?_high hr31] at hq; cases hq), fun q hq => hxv q hq⟩
    have hr16 : ins[j0] < 16 := by
      rcases h16 _ (List.mem_append_left _ (List.getElem_mem hjin)) with h | h <;> omega
    have hrz : ins[j0] ≠ zeroReg := by unfold zeroReg; omega
    obtain ⟨c0, hc0⟩ : ∃ c0, cls (c.cx.lc.ty v.args.toList.dropLast[j0]) = some c0 :=
      Option.isSome_iff_exists.1 (F.clsReg _ _ hh hrz)
    obtain ⟨x, hx, hxv, -⟩ := arg_rel hA hl hm hinv.core hh hc0
      (fun hr => hR (by rw [hop]; nofun) _ (List.dropLast_subset _ ha) _ _ hh hr hc0)
      (Or.inr ⟨by omega, objX?_low hr16⟩)
    refine ⟨x, hx, fun r hr => ?_⟩
    rw [hh] at hr
    cases hr
    refine ⟨fun q hq => ?_, fun q hq => by rw [objV?_low (by omega)] at hq; cases hq⟩
    rw [objX?_low hr16] at hq
    cases hq
    rw [rX_lt (by omega)] at hxv
    rw [hm1x _ (reg5_ne30 hr16)]
    exact hxv
  obtain ⟨args, hal, hargsP⟩ := list_choose _ hargs'
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨mm0, hmm0, hkn, hsep⟩ := hinv.core.mem
  rw [hmm] at hmm0
  cases hmm0
  have hregs : ∀ (j r : Nat) (x : Val), ins[j]? = some r → args[j]? = some x → RegRel E.ι x m₁ r :=
    fun j r x hr hx => by
      have hjl : j < v.args.toList.dropLast.length := by
        rw [← hal]; exact (List.getElem?_eq_some_iff.1 hx).1
      have ha := List.getElem?_eq_getElem hjl
      exact (hargsP j _ x ha hx).2 r
        (hargs _ _ (List.mem_of_getElem? (List.getElem?_zip_eq_some.2 ⟨ha, hr⟩)))
  obtain ⟨m', hcallH⟩ : ∃ m', H.call m₁ = some (.panicked e m') := by
    rcases hcr with hcr | ⟨rfl, hcr⟩
    · exact hok.z hop name abi cabi ins outs y args mm m₁ hcall' hcr hy hal
        (fun j a x ha hx => (hargsP j a x ha hx).1) hmm rfl rfl rfl rfl rfl hm1x
        (by rw [hal, hlen]) hregs hMI hkn hsep
    · exact hok hop name abi cabi ins outs y args mm m₁ hcall' (.inr hcr) hy hal
        (fun j a x ha hx => (hargsP j a x ha hx).1) hmm rfl rfl rfl rfl rfl hm1x
        (by rw [hal, hlen]) hregs hMI hkn hsep
  refine ⟨m₁, hstar.tail (pstep_at F.nodup F.lt F.ret hk' rfl hcstep),
    (hsyms y).1, Or.inr ⟨progAt?_none (hsyms y).2, m', hcallH⟩⟩

/-- **A static call of slice G60 whose callee panics, down to the machine words**: machine steps
of the linked code to a state that panics with `e` (the hook at the callee's symbol,
`MPanics`). -/
theorem g60_obj_callPanic {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState} {m : MState}
    {e : Panic} {osp : Bool} {spills : Array Spill} {o : ObjIn} {otab : Tab} {base : BitVec 64}
    {code : Code} {retM : BitVec 64} {t : MState}
    (hc : checkG60L lc ps bstart g = .ok (tab, kt))
    (hE : G28Env lc g L ps (endP L.text ps.toList) tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64CALLstatic) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s osp) (hok : CallPanicOKAt osp H E g L lc s v m e)
    (hn48 : needs48 lc = true → osp = true)
    (hO : ObjEnv ps spills o otab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hHP : HookPanicMap H L ps.toList (ObjEnv.map otab ps L base))
    (hR : ObjRel (ObjEnv.map otab ps L base) m t)
    (hic : ∀ u, PStar H L ps.toList (endP L.text ps.toList) m u → ICallOut L ps.toList u) :
    ∃ t', MStar H code retM t t' ∧ MPanics H code retM t' e := by
  obtain ⟨m', hp, hpp⟩ := g60_callPanic hc hE hbid hb hi hv hop hm hinv hok hn48
  obtain ⟨t1, ht1, hR1, hI1⟩ := obj_star hO hH hp hR (locMatch_inv hE.env.env.env.env hm) hic
  obtain ⟨t2, ht2, hpan⟩ := obj_panic hO hHP hR1 (hI1.resolve_right hpp.1) hpp
  exact ⟨t2, mstar_trans ht1 ht2, hpan⟩

/-! ## Interface and closure calls -/

/-- **The callee contract for a panic at an interface or closure call** `v` from `s`, which
panics with `e` (trusted, as `ICallOK`): at every machine state `m₁` that is `m` but for `X30`,
with the PC the content of the code register `Rn` (related to `runLoc`'s code pointer), `R26`
holding the closure context of a closure call, the remaining register arguments in their ABI
registers `ins` and the memory injected, the callee's code is no Prog of the caller and not its
return address `ret`, and the hook there panics with `e`. -/
def ICallPanicOK (H : Hooks) (E : MatchEnv) (L : Link) (ret : BitVec 64) (lc : LocCtx)
    (s : LocState) (v : Value) (m : MState) (e : Panic) : Prop :=
  ∀ n cabi ins outs a0 rc (q : Reg) (args : List Val) (mm : Mem) (m₁ : MState),
    icallLead v.op = some n → callABI? lc.ctx.tabs v.aux = some cabi →
    callRegs cabi = .ok (ins, outs) → v.args[0]? = some a0 → lc.home a0 = some (.reg rc) →
    objX? rc = some q → m₁.pc = m.x q →
    (∀ x, s.read lc a0 = .ok x → ValRel E.ι x m₁.pc) →
    (n = 2 → ∀ a1 x, v.args[1]? = some a1 → s.read lc a1 = .ok x → RegRel E.ι x m₁ ctxReg) →
    args.length = (v.args.toList.drop n).dropLast.length →
    (∀ (j : Nat) (a : ID) (x : Val), (v.args.toList.drop n).dropLast[j]? = some a →
      args[j]? = some x → s.read lc a = .ok x) →
    s.mem = .mem mm → m₁.sp = m.sp → m₁.v = m.v → m₁.nzcv = m.nzcv → m₁.mem = m.mem →
    (∀ k, k ≠ 30 → m₁.x k = m.x k) →
    args.length = ins.length →
    (∀ (j r : Nat) (x : Val), ins[j]? = some r → args[j]? = some x → RegRel E.ι x m₁ r) →
    MemInj E.ι mm m₁.mem → KeysNodup mm → SepFrom E.ι (StkAt E) mm →
    m₁.pc ≠ ret ∧ (∀ id, L.addr id ≠ some m₁.pc) ∧ ∃ m', H.call m₁ = some (.panicked e m')

/-- **The callee contract for a panic at an interface or closure call in an activation whose
`outargs` block sits at `SP`** (trusted, as `ICallOKS`; G48's mode): `ICallPanicOK` with the
separation `SepFromW` in place of `SepFrom`. -/
def ICallPanicOKS (H : Hooks) (E : MatchEnv) (L : Link) (ret : BitVec 64) (lc : LocCtx)
    (s : LocState) (v : Value) (m : MState) (e : Panic) : Prop :=
  ∀ n cabi ins outs a0 rc (q : Reg) (args : List Val) (mm : Mem) (m₁ : MState),
    icallLead v.op = some n → callABI? lc.ctx.tabs v.aux = some cabi →
    callRegs cabi = .ok (ins, outs) → v.args[0]? = some a0 → lc.home a0 = some (.reg rc) →
    objX? rc = some q → m₁.pc = m.x q →
    (∀ x, s.read lc a0 = .ok x → ValRel E.ι x m₁.pc) →
    (n = 2 → ∀ a1 x, v.args[1]? = some a1 → s.read lc a1 = .ok x → RegRel E.ι x m₁ ctxReg) →
    args.length = (v.args.toList.drop n).dropLast.length →
    (∀ (j : Nat) (a : ID) (x : Val), (v.args.toList.drop n).dropLast[j]? = some a →
      args[j]? = some x → s.read lc a = .ok x) →
    s.mem = .mem mm → m₁.sp = m.sp → m₁.v = m.v → m₁.nzcv = m.nzcv → m₁.mem = m.mem →
    (∀ k, k ≠ 30 → m₁.x k = m.x k) →
    args.length = ins.length →
    (∀ (j r : Nat) (x : Val), ins[j]? = some r → args[j]? = some x → RegRel E.ι x m₁ r) →
    MemInj E.ι mm m₁.mem → KeysNodup mm → SepFromW E.ι (StkAt E) mm →
    m₁.pc ≠ ret ∧ (∀ id, L.addr id ≠ some m₁.pc) ∧ ∃ m', H.call m₁ = some (.panicked e m')

/-- The interface or closure call panic contract of mode `w`: `ICallPanicOK` (`false`) or
`ICallPanicOKS` (`true`). -/
def ICallPanicOKAt : Bool → Hooks → MatchEnv → Link → BitVec 64 → LocCtx → LocState → Value →
    MState → Panic → Prop
  | false, H, E, L, ret, lc, s, v, m, e => ICallPanicOK H E L ret lc s v m e
  | true, H, E, L, ret, lc, s, v, m, e => ICallPanicOKS H E L ret lc s v m e

/-- `ICallPanicOKAt`, in the separation of its mode. -/
theorem ICallPanicOKAt.spec {w : Bool} {H : Hooks} {E : MatchEnv} {L : Link} {ret : BitVec 64}
    {lc : LocCtx} {s : LocState} {v : Value} {m : MState} {e : Panic}
    (h : ICallPanicOKAt w H E L ret lc s v m e) :
    ∀ n cabi ins outs a0 rc (q : Reg) (args : List Val) (mm : Mem) (m₁ : MState),
      icallLead v.op = some n → callABI? lc.ctx.tabs v.aux = some cabi →
      callRegs cabi = .ok (ins, outs) → v.args[0]? = some a0 → lc.home a0 = some (.reg rc) →
      objX? rc = some q → m₁.pc = m.x q →
      (∀ x, s.read lc a0 = .ok x → ValRel E.ι x m₁.pc) →
      (n = 2 → ∀ a1 x, v.args[1]? = some a1 → s.read lc a1 = .ok x → RegRel E.ι x m₁ ctxReg) →
      args.length = (v.args.toList.drop n).dropLast.length →
      (∀ (j : Nat) (a : ID) (x : Val), (v.args.toList.drop n).dropLast[j]? = some a →
        args[j]? = some x → s.read lc a = .ok x) →
      s.mem = .mem mm → m₁.sp = m.sp → m₁.v = m.v → m₁.nzcv = m.nzcv → m₁.mem = m.mem →
      (∀ k, k ≠ 30 → m₁.x k = m.x k) →
      args.length = ins.length →
      (∀ (j r : Nat) (x : Val), ins[j]? = some r → args[j]? = some x → RegRel E.ι x m₁ r) →
      MemInj E.ι mm m₁.mem → KeysNodup mm → SepAt w E.ι (StkAt E) mm →
      m₁.pc ≠ ret ∧ (∀ id, L.addr id ≠ some m₁.pc) ∧ ∃ m', H.call m₁ = some (.panicked e m') := by
  cases w <;> exact h

/-- G48's `kind48` accepts no interface or closure call: it takes static calls and accesses off
`SP`. -/
theorem kind48_icall {lc : LocCtx} {g : G2In} {v : Value} {e : String} {kd : VKind2} {n : Nat}
    (hn : icallLead v.op = some n) (h : kind48 lc g v e = .ok kd) : False := by
  rcases kind48_cases h with ⟨hop, -⟩ | ⟨-, -, -, -, hk⟩
  · rcases icallLead_some hn with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [hop] at h1 <;> cases h1
  · have ho := (spKind48_spec hk).ops
    rcases icallLead_some hn with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] at ho <;>
      simp [loadOp?, storeOp?, narrowLoad?, narrowStore?] at ho

/-- `vkind28` of an interface or closure call is `vkind10`'s. -/
theorem vkind28_icall {lc : LocCtx} {g : G2In} {v : Value} {n : Nat} {kd : VKind2}
    (hn : icallLead v.op = some n) (h : vkind28 lc g v = .ok kd) : vkind10 lc g v = .ok kd := by
  rcases icallLead_some hn with ⟨hop, -⟩ | ⟨hop, -⟩ <;>
    simpa [vkind28, vkind27, vkind25, vkind24, vkind23, vkind22, vkind21, vkind20, vkind19,
      vkind18, vkind17, vkind16, vkind15, vkind14, vkind13, vkind12, vkind11, globPair, logSh?,
      pbOp, Cond.ofOp, storeIdxOp?, loadIdxOp?, hop] using h

/-- `vkind38` of an interface or closure call is `vkind28`'s. -/
theorem vkind38_icall {lc : LocCtx} {g : G2In} {v : Value} {n : Nat}
    (hn : icallLead v.op = some n) : vkind38 lc g v = vkind28 lc g v := by
  rcases icallLead_some hn with ⟨hop, -⟩ | ⟨hop, -⟩ <;>
    apply vkind38_eq28 <;> rw [hop] <;> first | rfl | nofun

/-- What `icallKind` accepted, as the facts of `VK10.icall`. -/
theorem icallKind_facts {lc : LocCtx} {v : Value} {k : Nat} {kd : VKind2}
    (h : icallKind lc v k = .ok kd) :
    ∃ cabi ins outs a0 rc o, callABI? lc.ctx.tabs v.aux = some cabi ∧
      callRegs cabi = .ok (ins, outs) ∧ (∀ r ∈ ins ++ outs, r < 16) ∧
      v.args[0]? = some a0 ∧ lc.home a0 = some (.reg rc) ∧ rc < 26 ∧
      (cls (lc.ty a0)).isSome = true ∧ objOf? rc = some o ∧
      (k = 2 → ∃ a1, v.args[1]? = some a1 ∧ lc.home a1 = some (.reg ctxReg) ∧
        (cls (lc.ty a1)).isSome = true) ∧
      (v.args.toList.drop k).dropLast.length = ins.length ∧
      (∀ a r, (a, r) ∈ (v.args.toList.drop k).dropLast.zip ins → lc.home a = some (.reg r)) ∧
      kd = .prog (icallPat o) := by
  unfold icallKind at h
  by_cases ht : (lc.temps[v.id]?).join = none
  · simp only [ht, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    next => cases h
    next cabi hcabi =>
      split at h
      next => cases h
      next ins outs hcr =>
        split at h
        next => cases h
        next a0 ha0 =>
          split at h
          next => cases h
          next rc hrc =>
            split at h
            next => cases h
            next o ho =>
              split at h
              next => cases h
              next herr =>
                cases h
                obtain ⟨-, -, -, h16, hrc26, hcl0, hctx, hlen, hargs, -, -⟩ := icallErr_spec herr
                exact ⟨cabi, ins, outs, a0, rc, o, hcabi, hcr, h16, ha0, regHome?_eq.mp hrc, hrc26,
                  hcl0, ho, fun h2 => ctxOK_spec (hctx h2), hlen, hargs, rfl⟩
  · have hne : ((lc.temps[v.id]?).join != none) = true := by simpa using ht
    simp only [hne, ↓reduceIte] at h
    cases h

/-- What `icallKind47` accepted, as the facts of `VK47.icall`. -/
theorem icallKind47_facts {lc : LocCtx} {v : Value} {k : Nat} {kd : VKind2}
    (h : icallKind47 lc v k = .ok kd) :
    ∃ cabi ins outs a0 rc o, callABI? lc.ctx.tabs v.aux = some cabi ∧
      callRegs cabi = .ok (ins, outs) ∧ (∀ r ∈ ins ++ outs, r < 16 ∨ (31 ≤ r ∧ r < 47)) ∧
      v.args[0]? = some a0 ∧ lc.home a0 = some (.reg rc) ∧ rc < 26 ∧
      (cls (lc.ty a0)).isSome = true ∧ objOf? rc = some o ∧
      (k = 2 → ∃ a1, v.args[1]? = some a1 ∧ lc.home a1 = some (.reg ctxReg) ∧
        (cls (lc.ty a1)).isSome = true) ∧
      (v.args.toList.drop k).dropLast.length = ins.length ∧
      (∀ a r, (a, r) ∈ (v.args.toList.drop k).dropLast.zip ins → lc.home a = some (.reg r)) ∧
      (∀ a r, (a, r) ∈ (v.args.toList.drop k).dropLast.zip ins → 31 ≤ r →
        fTy (lc.ty a) = true) ∧
      kd = .prog (icallPat o) := by
  unfold icallKind47 at h
  by_cases ht : (lc.temps[v.id]?).join = none
  · simp only [ht, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
    split at h
    next => cases h
    next cabi hcabi =>
      split at h
      next => cases h
      next ins outs hcr =>
        split at h
        next => cases h
        next a0 ha0 =>
          split at h
          next => cases h
          next rc hrc =>
            split at h
            next => cases h
            next o ho =>
              split at h
              next => cases h
              next herr =>
                cases h
                obtain ⟨-, -, -, h16, hrc26, hcl0, hctx, hlen, hargs, hfa, -, -⟩ :=
                  icallErr47_spec herr
                exact ⟨cabi, ins, outs, a0, rc, o, hcabi, hcr, h16, ha0, regHome?_eq.mp hrc, hrc26,
                  hcl0, ho, fun h2 => ctxOK_spec (hctx h2), hlen, hargs, hfa, rfl⟩
  · have hne : ((lc.temps[v.id]?).join != none) = true := by simpa using ht
    simp only [hne, ↓reduceIte] at h
    cases h

/-- An interface or closure call `vkind47` accepted: `vkind46`'s (G10's `icallKind`, through
`vkind28`), its ABI registers in `R0`–`R15`, or G47's `icallKind47`, with `F0`–`F15` admitted and
an argument there at a float shape. -/
theorem vkind47_icall {lc : LocCtx} {g : G2In} {v : Value} {n : Nat} {kd : VKind2}
    (hn : icallLead v.op = some n) (h : vkind47 lc g v = .ok kd) :
    ∃ cabi ins outs a0 rc o, callABI? lc.ctx.tabs v.aux = some cabi ∧
      callRegs cabi = .ok (ins, outs) ∧ (∀ r ∈ ins ++ outs, r < 16 ∨ (31 ≤ r ∧ r < 47)) ∧
      v.args[0]? = some a0 ∧ lc.home a0 = some (.reg rc) ∧ rc < 26 ∧
      (cls (lc.ty a0)).isSome = true ∧ objOf? rc = some o ∧
      (n = 2 → ∃ a1, v.args[1]? = some a1 ∧ lc.home a1 = some (.reg ctxReg) ∧
        (cls (lc.ty a1)).isSome = true) ∧
      (v.args.toList.drop n).dropLast.length = ins.length ∧
      (∀ a r, (a, r) ∈ (v.args.toList.drop n).dropLast.zip ins → lc.home a = some (.reg r)) ∧
      (∀ a r, (a, r) ∈ (v.args.toList.drop n).dropLast.zip ins → 31 ≤ r →
        fTy (lc.ty a) = true) ∧
      kd = .prog (icallPat o) := by
  unfold vkind47 at h
  cases h46 : vkind46 lc g v with
  | ok kd' =>
    rw [h46] at h
    cases h
    rw [vkind46_eq45 (by
        rcases icallLead_some hn with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> simp [fops46]),
      vkind45_eq44 (by rcases icallLead_some hn with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl)
        (by rcases icallLead_some hn with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl),
      vkind44_eq43 (by rcases icallLead_some hn with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl),
      vkind43_eq42 (by rcases icallLead_some hn with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun),
      vkind42_eq41 (by rcases icallLead_some hn with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun),
      vkind41_eq40 (by rcases icallLead_some hn with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun)
        (by rcases icallLead_some hn with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl),
      vkind40_eq38 (by rcases icallLead_some hn with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun),
      vkind38_icall hn] at h46
    have h10 := vkind28_icall hn h46
    unfold vkind10 at h10
    rw [hn] at h10
    obtain ⟨cabi, ins, outs, a0, rc, o, hcabi, hcr, h16, ha0, hrc, hrc26, hcl0, ho, hctx, hlen,
      hargs, rfl⟩ := icallKind_facts h10
    exact ⟨cabi, ins, outs, a0, rc, o, hcabi, hcr, fun r hr => .inl (h16 r hr), ha0, hrc, hrc26,
      hcl0, ho, hctx, hlen, hargs,
      fun _ r har hr => absurd (h16 r (List.mem_append_left _ (List.of_mem_zip har).2))
        (by omega), rfl⟩
  | error e =>
    rw [h46] at h
    have hne : v.op ≠ .ARM64CALLstatic := by
      rcases icallLead_some hn with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun
    simp only [fcall47, hne, hn, ↓reduceIte] at h
    exact icallKind47_facts h

/-- **An interface or closure call of slice G60 whose callee panics**: from a `LocMatch`ed P0
state, the no-ops and the `CALL (Rn)` run to the callee's code, where the hook panics with `e`
(`ICallPanicOK`). -/
theorem g60_icallPanic {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {n : Nat} {osp : Bool}
    (hc : checkG60L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hn : icallLead v.op = some n) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s osp)
    (hok : ICallPanicOKAt osp H E L ret lc s v m e) :
    ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  have hen : entryOp24 v.op = false := by
    rcases icallLead_some hn with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl
  cases hl0 : lc.ctx.f.lowered with
  | false =>
    rcases nl30_ops (checkNL30_of_60L hl0 hc) hbid hb hi hv hen with
      h | h | h | h <;>
      rcases icallLead_some hn with ⟨h', -⟩ | ⟨h', -⟩ <;> rw [h] at h' <;> cases h'
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, -, -, -⟩ :=
    checkG60L_spec hl0 hc
  obtain ⟨b, j, js, e', next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  have h7x : op57a v.op = false ∧ op57b v.op = false ∧ op58a v.op = false ∧ op59p v.op = false := by
    rcases icallLead_some hn with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> exact ⟨rfl, rfl, rfl, rfl⟩
  have h5x : op56 v.op = false ∧ op55a v.op = false ∧ op55b v.op = false ∧
      op52b v.op = false ∧ op53a v.op = false ∧ op54a v.op = false := by
    rcases icallLead_some hn with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;>
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [hvk] at hkd
  have hkd : vkind49 _ _ v = .ok kd :=
    (vkind60_ok49 h7x.1 h7x.2.1 h7x.2.2.1 h7x.2.2.2 h5x.1 h5x.2.1 h5x.2.2.1 h5x.2.2.2.1
      h5x.2.2.2.2.1 h5x.2.2.2.2.2 hkd).resolve_right fun ⟨_, h⟩ => kind48_icall hn h
  have hkd := vkind49_ok51
    (by rcases icallLead_some hn with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun)
    (by rcases icallLead_some hn with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl)
    (by rcases icallLead_some hn with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl)
    (by rcases icallLead_some hn with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun)
    (by rcases icallLead_some hn with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun) hkd
  rw [vkind51_eq50
    (by rcases icallLead_some hn with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl)
    (by rcases icallLead_some hn with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl)
    (by rcases icallLead_some hn with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl),
    vkind50_eq47
    (by rcases icallLead_some hn with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl)
    (by rcases icallLead_some hn with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun)
    (by rcases icallLead_some hn with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun)] at hkd
  obtain ⟨cabi, ins, outs, a0, rc, o, hcabi, hcr, h16, ha0, hrc, hrc26, hcl0, ho, hctx, hlen,
    hargs, hfa, rfl⟩ := vkind47_icall hn hkd
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have hR : KRead c.cx.lc v (kAt c.cx.lc kt bid blk i).get := kread_of_reads hreads
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  have hRa : ∀ a ∈ v.args.toList, ∀ r c0, c.cx.lc.home a = some (.reg r) → r ≠ zeroReg →
      cls (c.cx.lc.ty a) = some c0 → (kAt c.cx.lc kt bid blk i).get r = some c0 :=
    hR (icall_notPhi hn)
  have hmem0 : a0 ∈ v.args.toList := List.mem_of_getElem? (by simpa using ha0)
  -- the machine: no-ops, then the `CALL (Rn)`
  obtain ⟨k, -, hk', hokp, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
  rw [pc_eta hm hj] at hstar
  obtain ⟨has, -, -, -, -, -, ht1, ht2, ht3⟩ := icallPat_spec hokp
  obtain ⟨kc, hkc32, rfl, hkc⟩ := objOf?_some ho
  have hrz : rc ≠ zeroReg := by unfold zeroReg; omega
  have hkc' : kc < 31 ∧ objX? rc = some (BitVec.ofNat 5 kc) := by
    rcases hkc with ⟨hz, -⟩ | h
    · exact absurd hz hrz
    · exact h
  let m₁ : MState :=
    { m with x := (fun q => if q = 30 then pcAt text c.cx.ps.toList (k + 1) else m.x q),
             pc := m.x (BitVec.ofNat 5 kc) }
  have hm1x : ∀ q, q ≠ 30 → m₁.x q = m.x q := fun q hq => by
    show (if q = 30 then _ else m.x q) = m.x q
    exact ite_eq_right_iff.2 fun h => absurd h hq
  have hcstep : progStep (Link.byId sym text az ez c.cx.ps.toList) c.cx.ps.toList[k]
      { m with pc := pcAt text c.cx.ps.toList k } = .ok m₁ := by
    rw [progStep_callReg (nextAddr_pcAt F.nodup hk') has ht1 ht2 ht3 hkc32, wX_pc,
      rX_lt hkc'.1]
    simp only [MState.wX, show ¬ ((30 : Reg) = 31) by decide, ↓reduceIte]
    rfl
  -- the code pointer, related to the PC
  obtain ⟨c0, hc0⟩ := Option.isSome_iff_exists.1 hcl0
  obtain ⟨xc, hxc, hxcv, -⟩ := arg_rel hA hl hm hinv.core hrc hc0
    (fun hr => hRa a0 hmem0 rc c0 hrc hr hc0) (Or.inr hkc')
  rw [rX_lt hkc'.1] at hxcv
  have hcode : ∀ x, s.read c.cx.lc a0 = .ok x → ValRel E.ι x m₁.pc := by
    intro x hx
    rw [hxc] at hx
    cases hx
    exact hxcv
  -- the closure context, in `R26`
  have hctxR : n = 2 → ∀ a1 x, v.args[1]? = some a1 → s.read c.cx.lc a1 = .ok x →
      RegRel E.ι x m₁ ctxReg := by
    intro h2 a1 x ha1 hx
    obtain ⟨a1', ha1', hh1, hcl1⟩ := hctx h2
    rw [ha1] at ha1'
    cases ha1'
    obtain ⟨c1, hc1⟩ := Option.isSome_iff_exists.1 hcl1
    have hmem1 : a1 ∈ v.args.toList := List.mem_of_getElem? (by simpa using ha1)
    obtain ⟨x1, hx1, hx1v, -⟩ := arg_rel (k := 26) hA hl hm hinv.core hh1 hc1
      (fun hr => hRa a1 hmem1 ctxReg c1 hh1 hr hc1) (Or.inr ⟨by decide, rfl⟩)
    rw [hx] at hx1
    cases hx1
    refine ⟨fun q hq => ?_, fun q hq => by simp [objV?, ctxReg] at hq⟩
    have hq' : q = BitVec.ofNat 5 26 :=
      (Option.some.inj ((rfl : objX? ctxReg = _).symm.trans hq)).symm
    subst hq'
    rw [hm1x _ (by decide)]
    rw [rX_lt (by decide)] at hx1v
    exact hx1v
  -- the register arguments, read from their ABI registers (an X register, or a V register by
  -- `argsV`)
  have hargs' : ∀ a ∈ (v.args.toList.drop n).dropLast, ∃ x, s.read c.cx.lc a = .ok x ∧
      ∀ r, c.cx.lc.home a = some (.reg r) → RegRel E.ι x m₁ r := by
    intro a ha
    obtain ⟨j0, hj0, rfl⟩ := List.getElem_of_mem ha
    have hjin : j0 < ins.length := hlen ▸ hj0
    have hz : ((v.args.toList.drop n).dropLast[j0], ins[j0]) ∈
        (v.args.toList.drop n).dropLast.zip ins :=
      List.mem_of_getElem? (List.getElem?_zip_eq_some.2 ⟨List.getElem?_eq_getElem hj0,
        List.getElem?_eq_getElem hjin⟩)
    have hh := hargs _ _ hz
    by_cases hr31 : 31 ≤ ins[j0]
    · obtain ⟨x, hx, hxv⟩ := argsV F hm hinv.core hR (icall_notPhi hn)
        (fun a ha => List.mem_of_mem_drop (List.dropLast_subset _ ha)) hargs hfa _ _ hz hr31
      refine ⟨x, hx, fun r hr => ?_⟩
      rw [hh] at hr
      cases hr
      exact ⟨fun q hq => (by rw [objX?_high hr31] at hq; cases hq), fun q hq => hxv q hq⟩
    have hr16 : ins[j0] < 16 := by
      rcases h16 _ (List.mem_append_left _ (List.getElem_mem hjin)) with h | h <;> omega
    have hrz' : ins[j0] ≠ zeroReg := by unfold zeroReg; omega
    obtain ⟨c2, hc2⟩ : ∃ c2, cls (c.cx.lc.ty (v.args.toList.drop n).dropLast[j0]) = some c2 :=
      Option.isSome_iff_exists.1 (F.clsReg _ _ hh hrz')
    obtain ⟨x, hx, hxv, -⟩ := arg_rel hA hl hm hinv.core hh hc2
      (fun hr => hRa _ (List.mem_of_mem_drop (List.dropLast_subset _ ha)) _ _ hh hr hc2)
      (Or.inr ⟨by omega, objX?_low hr16⟩)
    refine ⟨x, hx, fun r hr => ?_⟩
    rw [hh] at hr
    cases hr
    refine ⟨fun q hq => ?_, fun q hq => by rw [objV?_low (by omega)] at hq; cases hq⟩
    rw [objX?_low hr16] at hq
    cases hq
    rw [rX_lt (by omega)] at hxv
    rw [hm1x _ (reg5_ne30 hr16)]
    exact hxv
  obtain ⟨args, hal, hargsP⟩ := list_choose _ hargs'
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨mm0, hmm0, hkn, hsep⟩ := hinv.core.mem
  rw [hmm] at hmm0
  cases hmm0
  obtain ⟨hret1, haddr1, m', hcallH⟩ :=
    hok.spec n cabi ins outs a0 rc (BitVec.ofNat 5 kc) args mm m₁
    hn hcabi hcr ha0 hrc hkc'.2 rfl hcode hctxR hal (fun j a x ha hx => (hargsP j a x ha hx).1)
    hmm rfl rfl rfl rfl hm1x (by rw [hal, hlen])
    (fun j r x hr hx => by
      have hjl : j < (v.args.toList.drop n).dropLast.length := by
        rw [← hal]; exact (List.getElem?_eq_some_iff.1 hx).1
      have ha := List.getElem?_eq_getElem hjl
      exact (hargsP j _ x ha hx).2 r
        (hargs _ _ (List.mem_of_getElem? (List.getElem?_zip_eq_some.2 ⟨ha, hr⟩))))
    hMI hkn hsep
  exact ⟨m₁, hstar.tail (pstep_at F.nodup F.lt F.ret hk' rfl hcstep), hret1,
    Or.inr ⟨progAt?_none fun p _ => haddr1 p.id, m', hcallH⟩⟩

/-- **An interface or closure call of slice G60 whose callee panics, down to the machine
words**: machine steps of the linked code to a state that panics with `e` (`MPanics`). -/
theorem g60_obj_icallPanic {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState} {m : MState}
    {e : Panic} {n : Nat} {osp : Bool} {spills : Array Spill} {o : ObjIn} {otab : Tab}
    {base : BitVec 64}
    {code : Code} {retM : BitVec 64} {t : MState}
    (hc : checkG60L lc ps bstart g = .ok (tab, kt))
    (hE : G28Env lc g L ps (endP L.text ps.toList) tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hn : icallLead v.op = some n) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s osp)
    (hok : ICallPanicOKAt osp H E L (endP L.text ps.toList) lc s v m e)
    (hO : ObjEnv ps spills o otab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hHP : HookPanicMap H L ps.toList (ObjEnv.map otab ps L base))
    (hR : ObjRel (ObjEnv.map otab ps L base) m t)
    (hic : ∀ u, PStar H L ps.toList (endP L.text ps.toList) m u → ICallOut L ps.toList u) :
    ∃ t', MStar H code retM t t' ∧ MPanics H code retM t' e := by
  obtain ⟨m', hp, hpp⟩ := g60_icallPanic hc hE hbid hb hi hv hn hm hinv hok
  obtain ⟨t1, ht1, hR1, hI1⟩ := obj_star hO hH hp hR (locMatch_inv hE.env.env.env.env hm) hic
  obtain ⟨t2, ht2, hpan⟩ := obj_panic hO hHP hR1 (hI1.resolve_right hpp.1) hpp
  exact ⟨t2, mstar_trans ht1 ht2, hpan⟩

end GoFV.Proof.Obj

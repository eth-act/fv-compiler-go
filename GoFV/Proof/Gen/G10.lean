import GoFV.Proof.Gen.G9
import GoFV.Proof.Gen.Spec10

variable [GoFV.SSA.Sem.Addrs]

/-!
# Soundness of the genssa validator's slice G10: interface and closure calls (`docs/plans/proofs3.md` §4)

`g10_value`, `g10_term`, `g10_nilPanic`: `g9_value`'s, `g9_term`'s and `g9_nilPanic`'s statements
over `checkG10`, under the activation `G10Env` (G8's, and no interface or closure call in a
frameless function: its `CALL` overwrites `X30`), with the trusted contract of an indirect callee
`ICallOK` as a premise of `g10_value` next to `CallOK` and `WbOK`.

An interface call `CALLinter code args… mem` or a closure call `CALLclosure code ctx args… mem`
runs under `runLoc` as `callOp` on the callee its code pointer names (`callTarget`), with the
closure context for a closure call; its effect on `runLoc`'s state is a static call's: the
caller-saved registers and the flags `poison`, the results in the result registers, the memory
the callee's (`stepLoc_icall`, `clobber_icall`). On the machine its Prog `CALL (Rn)` puts the
return address in `X30` and jumps to the address in the code register (`progStep_callReg`), where
the runtime hook runs the callee. What the hook does is the trusted contract `ICallOK` (listed in
`docs/proofs/STATUS.md` Assumptions): `CallSpec`, the static callee's contract, at the code
register's address, which is no address of the caller's Progs nor its return address, from a
state whose PC is related to `runLoc`'s code pointer and whose `R26` holds the closure context
(Go's internal ABI: the closure context register). What the compiled code must do for that (the
code pointer in its register, the context in `R26`, the arguments in their ABI registers, the
results homed in the result registers) is proven here from what `checkG10` accepted (`g10_icall`).
The selects of such a call are G2's (`g2_selMem`, `g2_selReg`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm

/-! ## The premises -/

/-- **The callee contract at an interface or closure call** (trusted, semantics3 §6;
`docs/proofs/STATUS.md` Assumptions): at every machine state `m₁` that is `m` but for `X30`, with
the PC the content of the code register `Rn` (related to `runLoc`'s code pointer), `R26` holding
the closure context of a closure call and the ABI argument registers the remaining register
arguments, the callee's code is no Prog of the caller and not its return address `ret`, and the
hook there satisfies the callee contract `CallSpec` of a static call. -/
def ICallOK (H : Hooks) (E : MatchEnv) (L : Link) (ret : BitVec 64) (lc : LocCtx)
    (s s' : LocState) (v : Value) (m : MState) : Prop :=
  ∀ n cabi ins outs a0 rc (q : Reg) args mm (m₁ : MState),
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
    m₁.pc ≠ ret ∧ (∀ id, L.addr id ≠ some m₁.pc) ∧ CallSpec H E ins outs args mm s' m₁

/-- `ICallOK` with `CallSpecS` (trusted; a function whose `outargs` block sits at `SP`). -/
def ICallOKS (H : Hooks) (E : MatchEnv) (L : Link) (ret : BitVec 64) (lc : LocCtx)
    (s s' : LocState) (v : Value) (m : MState) : Prop :=
  ∀ n cabi ins outs a0 rc (q : Reg) args mm (m₁ : MState),
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
    m₁.pc ≠ ret ∧ (∀ id, L.addr id ≠ some m₁.pc) ∧ CallSpecS H E ins outs args mm s' m₁

/-- The interface/closure-call contract of mode `w`: `ICallOK` (`false`) or `ICallOKS` (`true`). -/
def ICallOKAt : Bool → Hooks → MatchEnv → Link → BitVec 64 → LocCtx → LocState → LocState →
    Value → MState → Prop
  | false, H, E, L, ret, lc, s, s', v, m => ICallOK H E L ret lc s s' v m
  | true, H, E, L, ret, lc, s, s', v, m => ICallOKS H E L ret lc s s' v m

theorem ICallOKAt.spec {w : Bool} {H : Hooks} {E : MatchEnv} {L : Link} {ret : BitVec 64}
    {lc : LocCtx} {s s' : LocState} {v : Value} {m : MState}
    (h : ICallOKAt w H E L ret lc s s' v m) :
    ∀ n cabi ins outs a0 rc (q : Reg) args mm (m₁ : MState),
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
      m₁.pc ≠ ret ∧ (∀ id, L.addr id ≠ some m₁.pc) ∧ CallSpecM w H E ins outs args mm s' m₁ := by
  cases w <;> exact h

/-- The activation of a function `checkG10` accepted: G8's, and a function with an interface or
closure call has a frame (the `CALL` overwrites `X30`). -/
structure G10Env (lc : LocCtx) (g : G2In) (L : Link) (ps : Array Prog) (ret : BitVec 64)
    (tab : PcTab) (E : MatchEnv) : Prop where
  env : G8Env lc g L ps ret tab E
  icalls : E.framed = false → ∀ id v, lc.ctx.f.value? id = some v → icallLead v.op = none

/-! ## `stepLoc` of an interface or closure call -/

section Step

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value} {n : Nat}

theorem icall_notPhi (hn : icallLead v.op = some n) : v.op ≠ .Phi := by
  rcases icallLead_some hn with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun

/-- What a successful step of an interface or closure call writes. -/
theorem stepLoc_icall (hl : lc.ctx.f.lowered = true) (hn : icallLead v.op = some n)
    (h : stepLoc env lc s v = .ok s') :
    ∃ r : Val, s' = (s.clobber lc v).write lc v.id (r.retypeL (lc.ty v.id)) := by
  rcases icallLead_some hn with ⟨hop, -⟩ | ⟨hop, -⟩ <;>
  · obtain ⟨argv, r, -, -, rfl⟩ := stepLoc_ok_eval (by rw [hop]; nofun) (by rw [hop]; nofun)
      (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) h
    exact ⟨r, by rw [lmode_retype hl]⟩

/-- An interface or closure call clobbers what a static call does. -/
theorem icall_regInfo {o : Op} (hn : icallLead o = some n) :
    o.regInfo.clobbers = Op.ARM64CALLstatic.regInfo.clobbers ∧ o.regInfo.clobbersArg0 = false ∧
      o.regInfo.clobbersArg1 = false ∧ o.clobberFlags = true := by
  rcases icallLead_some hn with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact ⟨rfl, by decide, by decide, by decide⟩

theorem clobber_icall (hn : icallLead v.op = some n) (ht : (lc.temps[v.id]?).join = none) :
    s.clobber lc v = { s.clobberMask Op.ARM64CALLstatic.regInfo.clobbers with flags := .poison } := by
  obtain ⟨h1, h2, h3, h4⟩ := icall_regInfo hn
  unfold LocState.clobber
  simp only [h1, h2, h3, h4, ht, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

/-- A register after an interface or closure call's clobbers: `poison`, or kept and one a call
keeps. -/
theorem clobber_icall_reg (hn : icallLead v.op = some n) (ht : (lc.temps[v.id]?).join = none)
    {r : Nat} {x : Val} (h : (s.clobber lc v).regs[r]? = some x) :
    x = .poison ∨ (s.regs[r]? = some x ∧ (r = 27 ∨ r = 29 ∨ r = 30 ∨ 63 ≤ r)) := by
  rw [clobber_icall hn ht] at h
  simp only [LocState.clobberMask, call_mask_ne, Bool.false_eq_true, ↓reduceIte,
    Array.getElem?_mapIdx] at h
  cases hr : s.regs[r]? with
  | none => rw [hr] at h; cases h
  | some y =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq] at h
    by_cases hm : Op.ARM64CALLstatic.regInfo.clobbers.hasReg r = true
    · left; simp only [hm, ↓reduceIte] at h; exact h.symm
    · right
      simp only [hm, Bool.false_eq_true, ↓reduceIte] at h
      exact ⟨by rw [h], call_keeps (by simpa using hm)⟩

theorem clobber_icall_slots (hn : icallLead v.op = some n) (ht : (lc.temps[v.id]?).join = none) :
    (s.clobber lc v).slots = s.slots := by
  rw [clobber_icall hn ht]
  simp only [LocState.clobberMask, call_mask_ne, Bool.false_eq_true, ↓reduceIte]

theorem clobber_icall_flags (hn : icallLead v.op = some n) (ht : (lc.temps[v.id]?).join = none) :
    (s.clobber lc v).flags = .poison := by
  rw [clobber_icall hn ht]

end Step

/-! ## `CALL (Rn)` -/

/-- An indirect call `CALL (Rn)` (`TYPE_MEM`, `NAME_NONE`, register `Rn`): `X30` the
fall-through, the PC the content of `Rn`. -/
theorem progStep_callReg {L : Link} {p : Prog} {s : MState} {next : BitVec 64} {kk : Nat}
    (hn : L.nextAddr p.id = some next) (has : p.as = .CALL) (ht1 : p.to.type = .MEM)
    (ht2 : p.to.name = .NONE) (ht3 : p.to.reg = GoFV.Asm.ARM64.REG_R0 + kk) (hk : kk < 32) :
    progStep L p s = .ok { s.wX 30 next with pc := s.rX (BitVec.ofNat 5 kk) } := by
  have hname : As.name .CALL = "CALL" := rfl
  have hfall : (ProgCtx.mk L s p).fall = .ok next := by simp [ProgCtx.fall, hn]; rfl
  have hw : ({} : Eff).wX (GoFV.Asm.ARM64.REG_R0 + 30) next = .ok { x := [(30, next)] } :=
    eff_wX_r0 (k := 30) (by omega)
  have hx : (ProgCtx.mk L s p).x (GoFV.Asm.ARM64.REG_R0 + kk) = .ok (s.rX (BitVec.ofNat 5 kk)) :=
    ctx_x_r0 hk
  have he : progEffect ⟨L, s, p⟩ =
      .ok { x := [(30, next)], pc := some (s.rX (BitVec.ofNat 5 kk)) } := by
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, ht1, ht2, ht3, ProgOp.baseOf,
      ↓reduceIte, ProgOp.movMem, ProgOp.pairOp, ProgOp.rmw, ProgOp.bcond, ProgOp.startsS, hfall,
      hx]
    simp only [pure, Except.pure, bind, Except.bind, hw]
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he rfl]
  rfl

theorem objX?_ne30 {r : Nat} {q : Reg} (h : objX? r = some q) (hr : r < 26) : q ≠ 30 := by
  obtain ⟨-, hq⟩ := objX?_some h
  intro h30
  rw [h30] at hq
  simp only [show (30 : Reg).toNat = 30 from rfl] at hq
  split at hq
  · omega
  · first | omega | (split at hq <;> omega)

/-! ## The call -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {g : G2In} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- An interface or closure call: the code pointer in `Rn`, the closure context in `R26`, the
register arguments in their ABI registers (`R0`–`R15`, or `F0`–`F15` read from their V registers,
`hV`), `CALL (Rn)` with the return address in `X30`, the callee by the trusted contract
(`ICallOK`), the results in the result registers. The injection grows by the callee's. -/
theorem g10_icall (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E) (hlc : E.lc = lc)
    (hcf : checkFrame lc g = .ok ()) (hframed : E.framed = true)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {n : Nat} {cabi : CallABI} {ins outs : List Nat} {a0 rc : Nat} {o : Int}
    (hn : icallLead v.op = some n) (hcabi : callABI? lc.ctx.tabs v.aux = some cabi)
    (hcr : callRegs cabi = .ok (ins, outs)) (h16 : ∀ r ∈ ins ++ outs, r < 16 ∨ (31 ≤ r ∧ r < 47))
    (ha0 : v.args[0]? = some a0) (hrc : lc.home a0 = some (.reg rc)) (hrc26 : rc < 26)
    (hcl0 : (cls (lc.ty a0)).isSome = true) (ho : objOf? rc = some o)
    (hctx : n = 2 → ∃ a1, v.args[1]? = some a1 ∧ lc.home a1 = some (.reg ctxReg) ∧
      (cls (lc.ty a1)).isSome = true)
    (hlen : (v.args.toList.drop n).dropLast.length = ins.length)
    (hargs : ∀ a r, (a, r) ∈ (v.args.toList.drop n).dropLast.zip ins → lc.home a = some (.reg r))
    (hV : ∀ a r, (a, r) ∈ (v.args.toList.drop n).dropLast.zip ins → 31 ≤ r →
      ∃ x, s.read lc a = .ok x ∧ ∀ k, objV? r = some k → FValRel x (m.v k))
    (hres : lc.home v.id = some (.results (outs.map some).toArray) ∨
      (lc.home v.id = none ∧ outs = []))
    (hct : callTy outs.length (lc.ty v.id) = true)
    (hKc : KCall (tupleTys (lc.ty v.id)) outs K K')
    (hvs : OneAt2 psA j (icallPat o) j') (htemp : (lc.temps[v.id]?).join = none)
    (hs : stepLoc env lc s v = .ok s')
    (hok : ICallOKAt osp H E (Link.byId sym text az ez psA.toList) ret lc s s' v m) :
    ∃ ι', (∀ b a, E.ι b = some a → ι' b = some a) ∧ AddrAgree ι' ∧ ∃ m',
      PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch { E with ι := ι' } s' b (i + 1) m' ∧
      CoreInv ι' (StkAt { E with ι := ι' }) K' s' osp ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have hnp := icall_notPhi hn
  -- the result's shape and `runLoc`'s state after the call
  obtain ⟨ts, hty⟩ : ∃ ts, lc.ty v.id = .tuple ts := by
    cases h : lc.ty v.id with
    | tuple ts => exact ⟨ts, rfl⟩
    | _ => rw [h] at hct; simp [callTy] at hct
  rw [hty] at hct hKc
  simp only [tupleTys] at hKc
  obtain ⟨ts', rfl, hts'len, hcls⟩ := callTy_split hct
  obtain ⟨r0, hs'⟩ := stepLoc_icall hl hn hs
  rw [write_call hty hres, hty] at hs'
  have hsl' : s'.slots = s.slots := by
    rw [hs', writeParts_slots, clobber_icall_slots hn htemp]
  have hfl' : s'.flags = .poison := by
    rw [hs', writeParts_flags _ _ _ _ (fun t ht => by
      rcases List.mem_append.1 ht with ht | ht
      · exact cls_notFlags (hcls t ht)
      · simp at ht; subst ht; rfl), clobber_icall_flags hn htemp]
  -- the code register
  obtain ⟨kc, hkc32, rfl, hkc⟩ := objOf?_some ho
  have hrz : rc ≠ zeroReg := by unfold zeroReg; omega
  have hkc' : kc < 31 ∧ objX? rc = some (BitVec.ofNat 5 kc) := by
    rcases hkc with ⟨hz, -⟩ | h
    · exact absurd hz hrz
    · exact h
  have hq30 : (BitVec.ofNat 5 kc : Reg) ≠ 30 := objX?_ne30 hkc'.2 hrc26
  have hRa : ∀ a ∈ v.args.toList, ∀ r c, lc.home a = some (.reg r) → r ≠ zeroReg →
      cls (lc.ty a) = some c → K r = some c := hR hnp
  have hmem0 : a0 ∈ v.args.toList := List.mem_of_getElem? (by simpa using ha0)
  -- the machine: no-ops, then the `CALL`
  obtain ⟨k, rfl, hk, hokp, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
  rw [pc_eta hm hj] at hstar
  obtain ⟨has, -, -, -, -, -, ht1, ht2, ht3⟩ := icallPat_spec hokp
  let m₁ : MState :=
    { m with x := (fun q => if q = 30 then pcAt text psA.toList (k + 1) else m.x q),
             pc := m.x (BitVec.ofNat 5 kc) }
  have hm1x : ∀ q, q ≠ 30 → m₁.x q = m.x q := fun q hq => by
    show (if q = 30 then _ else m.x q) = m.x q
    exact ite_eq_right_iff.2 fun h => absurd h hq
  have hcstep : progStep (Link.byId sym text az ez psA.toList) psA.toList[k]
      { m with pc := pcAt text psA.toList k } = .ok m₁ := by
    rw [progStep_callReg (nextAddr_pcAt F.nodup hk) has ht1 ht2 ht3 hkc32, wX_pc, rX_lt hkc'.1]
    simp only [MState.wX, show ¬ ((30 : Reg) = 31) by decide, ↓reduceIte]
    rfl
  -- the code pointer, related to the PC
  obtain ⟨c0, hc0⟩ := Option.isSome_iff_exists.1 hcl0
  obtain ⟨xc, hxc, hxcv, -⟩ := arg_rel hA hl hm hinv hrc hc0
    (fun hr => hRa a0 hmem0 rc c0 hrc hr hc0) (Or.inr hkc')
  rw [rX_lt hkc'.1] at hxcv
  have hcode : ∀ x, s.read lc a0 = .ok x → ValRel E.ι x m₁.pc := by
    intro x hx
    rw [hxc] at hx
    cases hx
    exact hxcv
  -- the closure context, in `R26`
  have hctxR : n = 2 → ∀ a1 x, v.args[1]? = some a1 → s.read lc a1 = .ok x →
      RegRel E.ι x m₁ ctxReg := by
    intro h2 a1 x ha1 hx
    obtain ⟨a1', ha1', hh1, hcl1⟩ := hctx h2
    rw [ha1] at ha1'
    cases ha1'
    obtain ⟨c1, hc1⟩ := Option.isSome_iff_exists.1 hcl1
    have hmem1 : a1 ∈ v.args.toList := List.mem_of_getElem? (by simpa using ha1)
    obtain ⟨x1, hx1, hx1v, -⟩ := arg_rel (k := 26) hA hl hm hinv hh1 hc1
      (fun hr => hRa a1 hmem1 ctxReg c1 hh1 hr hc1) (Or.inr ⟨by decide, rfl⟩)
    rw [hx] at hx1
    cases hx1
    refine ⟨fun q hq => ?_, fun q hq => by simp [objV?, ctxReg] at hq⟩
    have hq' : q = BitVec.ofNat 5 26 := (Option.some.inj ((rfl : objX? ctxReg = _).symm.trans hq)).symm
    subst hq'
    rw [hm1x _ (by decide)]
    rw [rX_lt (by decide)] at hx1v
    exact hx1v
  -- the register arguments, read from their ABI registers (an X register, or a V register by
  -- `hV`)
  have hargs' : ∀ a ∈ (v.args.toList.drop n).dropLast, ∃ x, s.read lc a = .ok x ∧
      ∀ r, lc.home a = some (.reg r) → RegRel E.ι x m₁ r := by
    intro a ha
    obtain ⟨j0, hj0, rfl⟩ := List.getElem_of_mem ha
    have hjin : j0 < ins.length := hlen ▸ hj0
    have hz : ((v.args.toList.drop n).dropLast[j0], ins[j0]) ∈
        (v.args.toList.drop n).dropLast.zip ins :=
      List.mem_of_getElem? (List.getElem?_zip_eq_some.2 ⟨List.getElem?_eq_getElem hj0,
        List.getElem?_eq_getElem hjin⟩)
    have hh := hargs _ _ hz
    by_cases hr31 : 31 ≤ ins[j0]
    · obtain ⟨x, hx, hxv⟩ := hV _ _ hz hr31
      refine ⟨x, hx, fun r hr => ?_⟩
      rw [hh] at hr
      cases hr
      exact ⟨fun q hq => (by rw [objX?_high hr31] at hq; cases hq), fun q hq => hxv q hq⟩
    have hr16 : ins[j0] < 16 := by
      rcases h16 _ (List.mem_append_left _ (List.getElem_mem hjin)) with h | h <;> omega
    have hrz' : ins[j0] ≠ zeroReg := by unfold zeroReg; omega
    obtain ⟨c, hc⟩ : ∃ c, cls (lc.ty (v.args.toList.drop n).dropLast[j0]) = some c :=
      Option.isSome_iff_exists.1 (F.clsReg _ _ hh hrz')
    obtain ⟨x, hx, hxv, -⟩ := arg_rel hA hl hm hinv hh hc
      (fun hr => hRa _ (List.mem_of_mem_drop (List.dropLast_subset _ ha)) _ _ hh hr hc)
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
  obtain ⟨mm0, hmm0, hkn, hsep⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  obtain ⟨hret1, haddr1, hspec⟩ := hok.spec n cabi ins outs a0 rc (BitVec.ofNat 5 kc) args mm m₁ hn
    hcabi hcr ha0 hrc hkc'.2 rfl hcode hctxR hal (fun j a x ha hx => (hargsP j a x ha hx).1) hmm
    rfl rfl rfl rfl hm1x
  obtain ⟨ι', m', mm', hcallH, hext, hA', hpc', hsp', h28, h29, hstk, hmem', hMI', hkn', hsep',
      hregs'⟩ := hspec (by rw [hal, hlen])
    (fun j r x hr hx => by
      have hjl : j < (v.args.toList.drop n).dropLast.length := by
        rw [← hal]; exact (List.getElem?_eq_some_iff.1 hx).1
      have ha := List.getElem?_eq_getElem hjl
      exact (hargsP j _ x ha hx).2 r
        (hargs _ _ (List.mem_of_getElem? (List.getElem?_zip_eq_some.2 ⟨ha, hr⟩))))
    hMI hkn hsep
  have hstep2 : PStep H (Link.byId sym text az ez psA.toList) psA.toList ret m₁ m' :=
    .hook hret1 (progAt?_none fun p _ => haddr1 p.id) hcallH
  have hstar' := (hstar.tail (pstep_at F.nodup F.lt F.ret hk rfl hcstep)).tail hstep2
  -- the registers after the call
  have hregs : ∀ r x, s'.regs[r]? = some x → r ∉ outs →
      x = .poison ∨ (s.regs[r]? = some x ∧ (r = 27 ∨ r = 29 ∨ r = 30 ∨ 63 ≤ r)) := by
    intro r x h hro
    rw [hs'] at h
    rcases writeParts_call ts' _ outs _ hcls hts'len r x h with h1 | ⟨j, t, -, ho, -⟩
    · exact clobber_icall_reg hn htemp h1
    · exact absurd (List.mem_of_getElem? ho) hro
  have hfits : ∀ r x c, r ≠ zeroReg → s'.regs[r]? = some x → K' r = some c → FitsW c x := by
    intro r x c hrz h hc
    obtain ⟨hKout, hKin⟩ := hKc r c hrz hc
    have h' := h
    rw [hs'] at h'
    rcases writeParts_call ts' _ outs _ hcls hts'len r x h' with h1 | ⟨j, t, ht, ho, hx⟩
    · rcases clobber_icall_reg hn htemp h1 with rfl | ⟨h2, hr⟩
      · trivial
      · by_cases hro : r ∈ outs
        · have := h16 r (List.mem_append_right _ hro)
          rcases hr with hr | hr | hr | hr <;> omega
        · exact hinv.regs r x c hrz h2 (hKin hro)
    · have hjt : j < ts'.length := (List.getElem?_eq_some_iff.1 ht).1
      have ht2 : (ts' ++ [Ty.mem])[j]? = some t := by rw [List.getElem?_append_left hjt]; exact ht
      have hct := hKout j t ho ht2
      exact fitsW_of_fits (fits_tuple_get ht2 hct hx)
  -- the frame and the slots under the larger injection
  obtain ⟨hslots', hframe'⟩ := stk_slots_frame (E' := { E with ι := ι' }) (m' := m') hm hF
    (slot_sizes hlc hcf hsi) rfl hext (fun q hq => hstk q hq) hsp'
    (h28.trans (hm1x 28 (by decide))) (h29.trans (hm1x 29 (by decide)))
    (fun hf => by rw [hframed] at hf; cases hf)
  refine ⟨ι', hext, hA', m', hstar', ⟨fun r x h => ?_, by rw [hfl']; trivial,
    by rw [hsl']; exact hslots', ⟨mm', hmem', hMI'⟩, hframe', ?_⟩,
    ⟨hfits, mm', hmem', hkn', hsep'⟩, fun k v hk => hsi k v (hsl' ▸ hk)⟩
  · by_cases hro : r ∈ outs
    · exact hregs' r hro x h
    · rcases hregs r x h hro with rfl | ⟨h2, hr⟩
      · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
      · obtain ⟨hx1, -⟩ := hm.regs r x h2
        refine ⟨fun q hq => ?_, fun q hq => ?_⟩
        · rcases hr with rfl | rfl | rfl | hr
          · have hq' : q = 29 := by simp [objX?] at hq; exact hq.symm
            subst hq'
            rw [h29, hm1x 29 (by decide)]
            exact valRel_mono hext (hx1 29 (by simp [objX?]))
          · simp [objX?] at hq
          · simp [objX?] at hq
          · simp only [objX?] at hq
            split at hq
            · omega
            · split at hq
              · omega
              · split at hq
                · omega
                · cases hq
        · rcases hr with rfl | rfl | rfl | hr
          · simp [objV?] at hq
          · simp [objV?] at hq
          · simp [objV?] at hq
          · simp only [objV?] at hq
            split at hq
            · omega
            · cases hq
  · show m'.pc = E.pcOf b (i + 1)
    rw [hpc', hj']
    simp [m₁]

end Cases

/-! ## Static facts of an accepted function -/

/-- A register home G10 handles other than `ZERO` holds a value with a class. -/
theorem clsReg_of_home10 {lc : LocCtx} (h : ∀ i, homeOK10 lc i = true) :
    ∀ i r, lc.home i = some (.reg r) → r ≠ zeroReg → (cls (lc.ty i)).isSome = true := by
  intro i r hh hr
  have h4 := homeOK4_of_10 (h i) (fun rs hrs => by rw [hh] at hrs; cases hrs)
  have := homeOK3_of_4 h4 (fun a b hab => by rw [hh] at hab; cases hab)
  simp only [homeOK3, hh, Bool.or_eq_true, beq_iff_eq, hr, false_or] at this
  exact this

/-- A slot home G10 handles is a spill's. -/
theorem slot_spill10 {lc : LocCtx} (h : ∀ i, homeOK10 lc i = true) {c : ID} {u : Value}
    (hu : lc.ctx.f.value? c = some u) {k : SlotKey} (hk : lc.home c = some (.slot k)) :
    u.op = .StoreReg := by
  have h4 := homeOK4_of_10 (h c) (fun rs hrs => by rw [hk] at hrs; cases hrs)
  have := homeOK3_of_4 h4 (fun a b hab => by rw [hk] at hab; cases hab)
  simpa [homeOK3, homeOK2, hk, hu] using this

theorem callsNotSlot10 {lc : LocCtx} (h : ∀ i, homeOK10 lc i = true) : CallsNotSlot lc :=
  fun _ _ hu hcop k hk => by rw [slot_spill10 h hu hk] at hcop; cases hcop

theorem icallNotSlot10 {lc : LocCtx} (h : ∀ i, homeOK10 lc i = true) {c : ID} {u : Value}
    (hu : lc.ctx.f.value? c = some u) (hi : (icallLead u.op).isSome = true) :
    ∀ k, lc.home c ≠ some (.slot k) := fun k hk => by
  rw [slot_spill10 h hu hk] at hi
  cases hi

/-! ## The theorems -/

/-- `G10Env` under an activation that extends the injection. -/
theorem G10Env.extend {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog} {ret : BitVec 64}
    {tab : PcTab} {E E' : MatchEnv} (hE : G10Env lc g L ps ret tab E) (hx : E.Extends E')
    (hE' : G8Env lc g L ps ret tab E') : G10Env lc g L ps ret tab E' where
  env := hE'
  icalls := fun hf => hE.icalls (by rw [hx.1] at hf; exact hf)

/-- One value of G10's kinds (`VK10`) emitted at the Progs from `j` to `j'`: `vk9_step`'s
statement for G10's values under `G10Env`, with the indirect callee contract `ICallOK`. -/
theorem vk10_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2}
    (hE : G10Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK10 lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s osp) (hpre : G7Pre lc s v)
    (hcall : CallOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hicall : ICallOKAt osp H E (Link.byId sym text az ez ps.toList) ret lc s s' v m)
    (hwb : WbOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s v m)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G10Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp := by
  have hE10 := hE
  have hE0 := hE.env.env.env
  obtain ⟨hlcE, -, -, -, -, -, -, -, -, -, hF⟩ := hE.env.env.env
  have same : ∀ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E s' bid (i + 1) m' ∧ CoreInv E.ι (StkAt E) (kStep lc K v).get s' osp ∧
      SlotInv lc s' →
      ∃ E' m', E.Extends E' ∧ G10Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
        PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
        LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp :=
    fun m' ⟨h1, h2, h3, h4⟩ => ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE10, h1, h2, ⟨h3, h4⟩⟩
  cases hVK with
  | g9 hVK9 =>
    obtain ⟨E', m', hx, hE', h⟩ := vk9_step hE.env F (callsNotSlot10 hhome) hcf hv hVK9 hvs htemp
      hj hj' hreads hm hinv hpre hcall hwb hs
    exact ⟨E', m', hx, hE10.extend hx hE', h⟩
  | icall hn hcabi hcr hnd _ _ _ _ h16 ha0 hrc hrc26 hcl0 ho hctx hlen hargs hres hct =>
    have hframed : E.framed = true := by
      cases hfr : E.framed
      · rw [hE.icalls hfr id v hv] at hn; cases hn
      · rfl
    obtain ⟨ι', hext', hA', m', hstar, hlm, hcore', hsl'⟩ := g10_icall (H := H) (g := g) F hF hlcE
      hcf hframed hm hinv.core hinv.slots (kread_of_reads hreads) hj hj' hn hcabi hcr
      (fun r hr => .inl (h16 r hr)) ha0 hrc hrc26 hcl0 ho hctx hlen hargs
      (fun _ r har hr => absurd (h16 r (List.mem_append_left _ (List.of_mem_zip har).2))
        (by omega)) hres hct
      (kcall_kStep (icall_notPhi hn) hres hnd (callTy_len hct)) hvs htemp hs hicall
    have hx : E.Extends { E with ι := ι' } := ⟨rfl, hext'⟩
    exact ⟨_, m', hx, hE10.extend hx (hE.env.extend hx (hE0.extend hext' hA')), hstar, hlm,
      ⟨hcore', hsl'⟩⟩
  | selMem hop hsz1 hc0 hu hi hts hct hpos hmt hnone hidx =>
    obtain ⟨m', h⟩ := g2_selMem (H := H) F hm hinv.core hinv.slots
      (knext_kStep fun _ => (hs_none hnone).noRegs) hj hj' hop hsz1 hc0 hu
      (icallNotSlot10 hhome hu hi) hts hct hpos hmt hnone hidx hvs htemp hs
    exact same m' h
  | selReg hop hsz1 hc0 hu hi hts hct hpos _ hvh hr16 hlt' hcl hhc hrs =>
    obtain ⟨m', h⟩ := g2_selReg (H := H) F hm hinv.core hinv.slots
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz1 hc0 hu
      (icallNotSlot10 hhome hu hi) hts hct hpos hvh hr16
      (fun c0 hc0' => ksel_of_reads hreads hop hc0 hts hhc hrs (hcl.trans hc0'))
      hlt' hcl hhc hrs hvs htemp hs
    exact same m' h

/-- **G10, values.** `g9_value`'s statement over `checkG10`, under `G10Env`, with the trusted
indirect callee contract `ICallOK` next to `CallOK` and `WbOK`: a value (not an entry value) of an
accepted function run by `runLoc` is matched by `runProg` steps of genssa's P0 Progs to a state
related before the next value, with the registers at the classes before the next value, under an
activation that extends `E`'s injection (by the callee's at a call, by the buffer at a write
barrier) and is again a `G10Env`. -/
theorem g10_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG10 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp3 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hpre : G7Pre lc s v)
    (hcall : CallOK H E g L lc s s' v m) (hicall : ICallOK H E L ret lc s s' v m)
    (hwb : WbOK H E g L lc s v m) (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G10Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' := by
  have hE0 := hE
  obtain ⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, hcf, hk, hlt, hnd, hblocks⟩ := checkG10_spec hc
  obtain ⟨b, j, js, e, next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk] at hkd
  obtain ⟨htemp, hVK⟩ := vkind10_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  rw [kAt_succ hi hv]
  exact vk10_step hE0 F hhome hcf hv hVK hvs htemp hj hj' hreads hm hinv hpre hcall hicall hwb hs

/-- **G10, nil panics.** `g9_nilPanic`'s statement over `checkG10`. -/
theorem g10_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG10 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  obtain ⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks⟩ := checkG10_spec hc
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
  obtain ⟨-, hVK⟩ := vkind10_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases hVK with
  | g9 hVK9 =>
    cases hVK9 with
    | g8 _ hVK8 =>
      cases hVK8 with
      | g7 hVK7 =>
        cases hVK7 with
        | g6 hne _ => exact absurd hop hne
        | nil _ hsz2 _ _ hao hma =>
          exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma
            hvs hs
      | wb hop' => rw [hop] at hop'; cases hop'
      | sel0 hop' => rw [hop] at hop'; cases hop'
      | sel1 hop' => rw [hop] at hop'; cases hop'
    | call hop' => rw [hop] at hop'; cases hop'
  | icall hn => rw [hop] at hn; cases hn
  | selMem hop' => rw [hop] at hop'; cases hop'
  | selReg hop' => rw [hop] at hop'; cases hop'

/-- **G10, terminators.** `g9_term`'s statement over `checkG10`. -/
theorem g10_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG10 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList := by
  obtain ⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome, -, hk, hlt, hnd, hblocks⟩ := checkG10_spec hc
  exact termK_step hpcOf ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb
    hm hinv hpre ht

end GoFV.Proof.Gen

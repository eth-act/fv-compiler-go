import GoFV.Proof.Gen.G27
import GoFV.Proof.Gen.Spec28

variable [GoFV.SSA.Sem.Addrs]

/-!
# Soundness of the genssa validator's slice G28: `LoweredMemEq` (`docs/plans/proofs3.md` §4)

`g28_value`, `g28_term`, `g28_nilPanic`, `g28_boundsPanic`: `g27_value`'s, `g27_term`'s,
`g27_nilPanic`'s and `g27_boundsPanic`'s statements over `checkG28`, under `G28Env` (a function
with `LoweredMemEq` has a frame) and, for values, the trusted `runtime.memequal` contract
`MemEqOK`.

`LoweredMemEq p q n mem` runs under `runLoc` as a call's clobbers, then `memEq [p, q, n, mem]` in
`R0` (`stepLoc`, `evalOpL_memEq`), with `p`, `q`, `n` read from `R0`, `R1`, `R2`. genssa emits
`CALL runtime.memequal(SB)`: the return address in `X30`, then the runtime hook, which by
`MemEqOK` returns to `X30` with `SP`, `R28`, `R29` and the memory kept and `X0` related to
`memEq` of the arguments it was given in `X0`–`X2` and of the memory (`g28_memEq`). Every other
register is `poison` in `runLoc`'s state, as after a static call.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The premises -/

/-- **The `runtime.memequal` contract** (trusted, `docs/proofs/STATUS.md` Assumptions): from the
machine state `m` at `runtime.memequal`'s entry, if `X0`, `X1`, `X2` hold `p`, `q`, `n` and the
memory injects `runLoc`'s memory `mm` (distinct keys, the live blocks away from the frame), the
hook returns to `X30` with `SP`, `R28`, `R29` and the memory kept, and `X0` holds whether the `n`
bytes at `p` and at `q` agree (`memEq`). -/
def MemEqSpec (H : Hooks) (E : MatchEnv) (p q n : Val) (mm : Mem) (m : MState) : Prop :=
  ValRel E.ι p (m.x 0) → ValRel E.ι q (m.x 1) → ValRel E.ι n (m.x 2) →
    MemInj E.ι mm m.mem → KeysNodup mm → SepFrom E.ι (StkAt E) mm →
  ∃ m', H.call m = some (.ret m') ∧ m'.pc = m.x 30 ∧ m'.sp = m.sp ∧ m'.x 28 = m.x 28 ∧
    m'.x 29 = m.x 29 ∧ m'.mem = m.mem ∧ ValRel E.ι (memEq [p, q, n, .mem mm]) (m'.x 0)

/-- The `runtime.memequal` contract (`MemEqSpec`) at the value `v` from `s`, with the arguments
`runLoc` reads, at every machine state at the symbol of `runtime.memequal` that is `m` but for
`X30`. -/
def MemEqOK (H : Hooks) (E : MatchEnv) (g : G2In) (L : Link) (lc : LocCtx) (s : LocState)
    (v : Value) (m : MState) : Prop :=
  v.op = .ARM64LoweredMemEq → ∀ y a0 a1 a2 p q n mm (m₁ : MState), g.syms[y]? = some memEqSym →
    v.args[0]? = some a0 → v.args[1]? = some a1 → v.args[2]? = some a2 →
    s.read lc a0 = .ok p → s.read lc a1 = .ok q → s.read lc a2 = .ok n → s.mem = .mem mm →
    m₁.pc = L.sym y → m₁.sp = m.sp → m₁.v = m.v → m₁.nzcv = m.nzcv → m₁.mem = m.mem →
    (∀ k, k ≠ 30 → m₁.x k = m.x k) → MemEqSpec H E p q n mm m₁

/-- **The `runtime.memequal` contract from a function whose `outargs` block sits at `SP`**
(trusted; `docs/proofs/STATUS.md` Assumptions; `MatchEnv.outSP`): `MemEqSpec` with the separation
`SepFromW` in place of `SepFrom` in its premise. -/
def MemEqSpecS (H : Hooks) (E : MatchEnv) (p q n : Val) (mm : Mem) (m : MState) : Prop :=
  ValRel E.ι p (m.x 0) → ValRel E.ι q (m.x 1) → ValRel E.ι n (m.x 2) →
    MemInj E.ι mm m.mem → KeysNodup mm → SepFromW E.ι (StkAt E) mm →
  ∃ m', H.call m = some (.ret m') ∧ m'.pc = m.x 30 ∧ m'.sp = m.sp ∧ m'.x 28 = m.x 28 ∧
    m'.x 29 = m.x 29 ∧ m'.mem = m.mem ∧ ValRel E.ι (memEq [p, q, n, .mem mm]) (m'.x 0)

/-- `MemEqOK` with `MemEqSpecS` (trusted; a function whose `outargs` block sits at `SP`). -/
def MemEqOKS (H : Hooks) (E : MatchEnv) (g : G2In) (L : Link) (lc : LocCtx) (s : LocState)
    (v : Value) (m : MState) : Prop :=
  v.op = .ARM64LoweredMemEq → ∀ y a0 a1 a2 p q n mm (m₁ : MState), g.syms[y]? = some memEqSym →
    v.args[0]? = some a0 → v.args[1]? = some a1 → v.args[2]? = some a2 →
    s.read lc a0 = .ok p → s.read lc a1 = .ok q → s.read lc a2 = .ok n → s.mem = .mem mm →
    m₁.pc = L.sym y → m₁.sp = m.sp → m₁.v = m.v → m₁.nzcv = m.nzcv → m₁.mem = m.mem →
    (∀ k, k ≠ 30 → m₁.x k = m.x k) → MemEqSpecS H E p q n mm m₁

/-- `MemEqSpec` (`w = false`) or `MemEqSpecS` (`w = true`), by the separation of mode `w`. -/
def MemEqSpecM (w : Bool) (H : Hooks) (E : MatchEnv) (p q n : Val) (mm : Mem) (m : MState) :
    Prop :=
  ValRel E.ι p (m.x 0) → ValRel E.ι q (m.x 1) → ValRel E.ι n (m.x 2) →
    MemInj E.ι mm m.mem → KeysNodup mm → SepAt w E.ι (StkAt E) mm →
  ∃ m', H.call m = some (.ret m') ∧ m'.pc = m.x 30 ∧ m'.sp = m.sp ∧ m'.x 28 = m.x 28 ∧
    m'.x 29 = m.x 29 ∧ m'.mem = m.mem ∧ ValRel E.ι (memEq [p, q, n, .mem mm]) (m'.x 0)

/-- The `runtime.memequal` contract of mode `w`: `MemEqOK` (`false`) or `MemEqOKS` (`true`). -/
def MemEqOKAt : Bool → Hooks → MatchEnv → G2In → Link → LocCtx → LocState → Value → MState →
    Prop
  | false, H, E, g, L, lc, s, v, m => MemEqOK H E g L lc s v m
  | true, H, E, g, L, lc, s, v, m => MemEqOKS H E g L lc s v m

theorem MemEqOKAt.spec {w : Bool} {H : Hooks} {E : MatchEnv} {g : G2In} {L : Link} {lc : LocCtx}
    {s : LocState} {v : Value} {m : MState} (h : MemEqOKAt w H E g L lc s v m) :
    v.op = .ARM64LoweredMemEq → ∀ y a0 a1 a2 p q n mm (m₁ : MState), g.syms[y]? = some memEqSym →
      v.args[0]? = some a0 → v.args[1]? = some a1 → v.args[2]? = some a2 →
      s.read lc a0 = .ok p → s.read lc a1 = .ok q → s.read lc a2 = .ok n → s.mem = .mem mm →
      m₁.pc = L.sym y → m₁.sp = m.sp → m₁.v = m.v → m₁.nzcv = m.nzcv → m₁.mem = m.mem →
      (∀ k, k ≠ 30 → m₁.x k = m.x k) → MemEqSpecM w H E p q n mm m₁ := by
  cases w <;> exact h

/-- The activation of a function `checkG28` accepted: G10's, and a function with `LoweredMemEq`
has a frame (the `CALL` overwrites `X30`). -/
structure G28Env (lc : LocCtx) (g : G2In) (L : Link) (ps : Array Prog) (ret : BitVec 64)
    (tab : PcTab) (E : MatchEnv) : Prop where
  env : G10Env lc g L ps ret tab E
  memeqs : E.framed = false → ∀ id v, lc.ctx.f.value? id = some v → v.op ≠ .ARM64LoweredMemEq

/-! ## `stepLoc` of `LoweredMemEq` -/

section Step

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

theorem memEq_clobbers :
    Op.ARM64LoweredMemEq.regInfo.clobbers = Op.ARM64CALLstatic.regInfo.clobbers := rfl

theorem memEq_noArg0 : Op.ARM64LoweredMemEq.regInfo.clobbersArg0 = false := by decide

theorem memEq_noArg1 : Op.ARM64LoweredMemEq.regInfo.clobbersArg1 = false := by decide

theorem memEq_flags : Op.ARM64LoweredMemEq.clobberFlags = true := by decide

/-- `LoweredMemEq` clobbers what a static call does. -/
theorem clobber_memEq (hop : v.op = .ARM64LoweredMemEq) (ht : (lc.temps[v.id]?).join = none) :
    s.clobber lc v = { s.clobberMask Op.ARM64CALLstatic.regInfo.clobbers with flags := .poison } := by
  unfold LocState.clobber
  simp only [hop, memEq_clobbers, memEq_noArg0, memEq_noArg1, ht, memEq_flags, Bool.not_false,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte]

/-- A register after `LoweredMemEq`'s clobbers: `poison`, or kept and one a call keeps. -/
theorem clobber_memEq_reg (hop : v.op = .ARM64LoweredMemEq) (ht : (lc.temps[v.id]?).join = none)
    {r : Nat} {x : Val} (h : (s.clobber lc v).regs[r]? = some x) :
    x = .poison ∨ (s.regs[r]? = some x ∧ (r = 27 ∨ r = 29 ∨ r = 30 ∨ 63 ≤ r)) := by
  have hc := clobber_call_reg (s := s) (lc := lc) (v := { v with op := .ARM64CALLstatic }) rfl ht
    (r := r) (x := x)
  rw [clobber_call (v := { v with op := .ARM64CALLstatic }) (s := s) (lc := lc) rfl ht,
    ← clobber_memEq hop ht] at hc
  exact hc h

theorem clobber_memEq_slots (hop : v.op = .ARM64LoweredMemEq)
    (ht : (lc.temps[v.id]?).join = none) : (s.clobber lc v).slots = s.slots := by
  rw [clobber_memEq hop ht]
  simp only [LocState.clobberMask, call_mask_ne, Bool.false_eq_true, ↓reduceIte]

theorem clobber_memEq_mem (hop : v.op = .ARM64LoweredMemEq)
    (ht : (lc.temps[v.id]?).join = none) : (s.clobber lc v).mem = s.mem := by
  rw [clobber_memEq hop ht]
  simp only [LocState.clobberMask, call_mask_ne, Bool.false_eq_true, ↓reduceIte]

/-- `runLoc`'s value of `LoweredMemEq`, when it does not panic: `memEq` of its arguments. -/
theorem evalOpL_memEq {ctx : Ctx} {fr : Sem.Frame} {argv : List Val} {t : Ty} {r : Val}
    (hop : v.op = .ARM64LoweredMemEq) (h : evalOpL true env ctx fr v argv t = .ok r) :
    r = memEq argv := by
  have e : evalOpL true env ctx fr v argv t =
      (match nilFaults true ctx v argv with
        | some m => .panic .nilDeref m
        | none => .ok (memEq argv)) := by
    obtain ⟨id, op, type, auxInt, aux, pos, uses, args, block⟩ := v
    dsimp only at hop
    subst hop
    rfl
  rw [e] at h
  split at h
  · cases h
  · cases h
    rfl

/-- `memEq` is a boolean or `poison`. -/
theorem fits_memEq (xs : List Val) : Fits 1 (memEq xs) := by
  unfold memEq
  split
  · split
    · split
      · split
        · trivial
        · exact (rfl : (1 : Nat) = 1)
      · trivial
    · trivial
  · trivial

private theorem mapM_res_four {α β : Type} {f : α → Res β} {a b c d : α} {x y z w : β}
    {ys : List β} (h : [a, b, c, d].mapM f = .ok ys) (hx : f a = .ok x) (hy : f b = .ok y)
    (hz : f c = .ok z) (hw : f d = .ok w) : ys = [x, y, z, w] := by
  obtain ⟨hlen, hk⟩ := mapM_res h
  match ys, hlen with
  | [x', y', z', w'], _ =>
    have h0 := hk 0 (by simp) (by simp)
    have h1 := hk 1 (by simp) (by simp)
    have h2 := hk 2 (by simp) (by simp)
    have h3 := hk 3 (by simp) (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, hx, hy, hz, hw,
      Res.ok.injEq] at h0 h1 h2 h3
    rw [h0, h1, h2, h3]

end Step

/-! ## The value -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {g : G2In} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- `LoweredMemEq p q n mem`: `CALL runtime.memequal(SB)` with the return address in `X30`, the
hook by the trusted contract (`MemEqOK`): `memEq` of the arguments in `R0`, every other register
`poison`, the memory unchanged. -/
theorem g28_memEq (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E) (hlc : E.lc = lc)
    (hcf : checkFrame lc g = .ok ()) (hframed : E.framed = true)
    (hsyms : ∀ y, (Link.byId sym text az ez psA.toList).sym y ≠ ret ∧ ∀ p ∈ psA.toList,
      (Link.byId sym text az ez psA.toList).addr p.id ≠
        some ((Link.byId sym text az ez psA.toList).sym y))
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {a0 a1 a2 : ID} (hop : v.op = .ARM64LoweredMemEq) (hsz : v.args.size = 4)
    (hh : lc.home v.id = some (.reg 0)) (hty : lc.ty v.id = .bool)
    (ha0 : v.args[0]? = some a0) (ha1 : v.args[1]? = some a1) (ha2 : v.args[2]? = some a2)
    (hh0 : lc.home a0 = some (.reg 0)) (hh1 : lc.home a1 = some (.reg 1))
    (hh2 : lc.home a2 = some (.reg 2)) (hc0 : cls (lc.ty a0) = some 64)
    (hc1 : cls (lc.ty a1) = some 64) (hc2 : cls (lc.ty a2) = some 64)
    (hma : memArg lc v 3 = .ok ()) (hvs : OneAt2 psA j (memEqPat g) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s')
    (hok : MemEqOKAt osp H E g (Link.byId sym text az ez psA.toList) lc s v m) :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨a3, ha3, hmt3, hh3⟩ := memArg_spec hma
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨mm0, hmm0, hkn, hsep⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  -- the arguments, read from `R0`, `R1`, `R2`
  obtain ⟨x0, hx0, hx0v, -⟩ := arg_rel (k := 0) hA hl hm hinv hh0 hc0
    (kread_arg hR hnp ha0 hh0 hc0) (Or.inr ⟨by decide, objX?_low (by decide)⟩)
  obtain ⟨x1, hx1, hx1v, -⟩ := arg_rel (k := 1) hA hl hm hinv hh1 hc1
    (kread_arg hR hnp ha1 hh1 hc1) (Or.inr ⟨by decide, objX?_low (by decide)⟩)
  obtain ⟨x2, hx2, hx2v, -⟩ := arg_rel (k := 2) hA hl hm hinv hh2 hc2
    (kread_arg hR hnp ha2 hh2 hc2) (Or.inr ⟨by decide, objX?_low (by decide)⟩)
  rw [rX_lt (by decide)] at hx0v hx1v hx2v
  -- `runLoc`'s state after the value
  obtain ⟨argv, r, hmv, hr, rfl⟩ := stepLoc_ok_eval hnp (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) hs
  rw [arr4 hsz ha0 ha1 ha2 ha3] at hmv
  obtain rfl := mapM_res_four hmv hx0 hx1 hx2 (read_mem hl hh3 hmt3 hmm)
  obtain rfl := evalOpL_memEq hop hr
  have hcb : cls (lc.ty v.id) = some 1 := by rw [hty]; rfl
  rw [lmode_retype hl, write_reg hh hcb]
  have hsl' : ((s.clobber lc v).setReg 0 ((memEq [x0, x1, x2, .mem mm]).retypeL (lc.ty v.id))).slots
      = s.slots := by
    unfold LocState.setReg
    exact clobber_memEq_slots hop htemp
  have hmem's : ((s.clobber lc v).setReg 0
      ((memEq [x0, x1, x2, .mem mm]).retypeL (lc.ty v.id))).mem = .mem mm := by
    unfold LocState.setReg
    exact (clobber_memEq_mem hop htemp).trans hmm
  have hfl' : ((s.clobber lc v).setReg 0
      ((memEq [x0, x1, x2, .mem mm]).retypeL (lc.ty v.id))).flags = .poison := by
    unfold LocState.setReg
    rw [clobber_memEq hop htemp]
  -- the machine: no-ops, then the `CALL`
  obtain ⟨k, rfl, hk, hokp, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
  rw [pc_eta hm hj] at hstar
  obtain ⟨has, -, -, -, -, -, ht1, ht2, ht3, y, hy1, hy⟩ := memEqPat_spec hokp
  let m₁ : MState :=
    { m with x := (fun q => if q = 30 then pcAt text psA.toList (k + 1) else m.x q),
             pc := (Link.byId sym text az ez psA.toList).sym y }
  have hm1x : ∀ q, q ≠ 30 → m₁.x q = m.x q := fun q hq => by
    show (if q = 30 then _ else m.x q) = m.x q
    exact ite_eq_right_iff.2 fun h => absurd h hq
  have hcstep : progStep (Link.byId sym text az ez psA.toList) psA.toList[k]
      { m with pc := pcAt text psA.toList k } = .ok m₁ := by
    rw [progStep_callSym (nextAddr_pcAt F.nodup hk) has ht1 ht2 ht3 hy1, wX_pc]
    simp only [MState.wX, show ¬ ((30 : Reg) = 31) by decide, ↓reduceIte]
    rfl
  obtain ⟨m', hcallH, hpc', hsp', h28, h29, hmem', hres⟩ :=
    hok.spec hop y a0 a1 a2 x0 x1 x2 mm m₁ hy ha0 ha1 ha2 hx0 hx1 hx2 hmm rfl rfl rfl rfl rfl hm1x
      (by rw [hm1x _ (by decide)]; exact hx0v) (by rw [hm1x _ (by decide)]; exact hx1v)
      (by rw [hm1x _ (by decide)]; exact hx2v) hMI hkn hsep
  have hstep2 : PStep H (Link.byId sym text az ez psA.toList) psA.toList ret m₁ m' :=
    .hook (hsyms y).1 (progAt?_none (hsyms y).2) hcallH
  have hstar' := (hstar.tail (pstep_at F.nodup F.lt F.ret hk rfl hcstep)).tail hstep2
  -- the result in `R0`
  have hres' : ValRel E.ι ((memEq [x0, x1, x2, .mem mm]).retypeL (lc.ty v.id)) (m'.x 0) :=
    valRel_retypeL hA hcb (fits_memEq _) hres
  -- the frame and the slots
  obtain ⟨hslots', hframe'⟩ := stk_slots_frame (E' := E) (m' := m') hm hF
    (slot_sizes hlc hcf hsi) rfl (fun _ _ h => h) (fun q _ => by rw [hmem']) hsp'
    ((h28.trans (hm1x 28 (by decide)))) (h29.trans (hm1x 29 (by decide)))
    (fun hf => by rw [hframed] at hf; cases hf)
  refine ⟨m', hstar', ⟨fun r x h => ?_, by rw [hfl']; trivial,
    by rw [hsl']; exact hslots', ⟨mm, hmem's, by rw [hmem']; exact hMI⟩, hframe', ?_⟩,
    ⟨fun r x c hrz h hc => ?_, mm, hmem's, hkn, hsep⟩, fun k v hk => hsi k v (hsl' ▸ hk)⟩
  · rcases setReg_get h with ⟨rfl, rfl⟩ | ⟨hne, h2⟩
    · refine ⟨fun q hq => ?_, fun q hq => by rw [objV?_low (by decide)] at hq; cases hq⟩
      rw [objX?_low (by decide)] at hq
      cases hq
      exact hres'
    · rcases clobber_memEq_reg hop htemp h2 with rfl | ⟨h3, hr⟩
      · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
      · obtain ⟨hx1', -⟩ := hm.regs r x h3
        refine ⟨fun q hq => ?_, fun q hq => ?_⟩
        · rcases hr with rfl | rfl | rfl | hr
          · have hq' : q = 29 := by simp [objX?] at hq; exact hq.symm
            subst hq'
            rw [h29, hm1x 29 (by decide)]
            exact hx1' 29 (by simp [objX?])
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
  · have hc' := hK r c hrz hc
    rcases setReg_get h with ⟨rfl, rfl⟩ | ⟨hne, h2⟩
    · rw [if_pos ⟨hnp, hh⟩, hcb] at hc'
      cases hc'
      exact fits_retypeL hcb _
    · have hr0 : r ≠ 0 := by
        rcases hne with hne | hne
        · exact hne
        · exact absurd hne (by decide)
      rw [if_neg (fun h' => hr0 (by rw [hh] at h'; cases h'.2; rfl))] at hc'
      rcases clobber_memEq_reg hop htemp h2 with rfl | ⟨h3, -⟩
      · trivial
      · exact hinv.regs r x c hrz h3 hc'

end Cases

/-! ## The theorems -/

/-- `G28Env` under an activation that extends the injection. -/
theorem G28Env.extend {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog} {ret : BitVec 64}
    {tab : PcTab} {E E' : MatchEnv} (hE : G28Env lc g L ps ret tab E) (hx : E.Extends E')
    (hE' : G10Env lc g L ps ret tab E') : G28Env lc g L ps ret tab E' where
  env := hE'
  memeqs := fun hf => hE.memeqs (by rw [hx.1] at hf; exact hf)

theorem narrowLd?_memEq {lc : LocCtx} {v : Value} (hop : v.op = .ARM64LoweredMemEq) :
    narrowLd? lc v = none := by
  unfold narrowLd?
  rw [hop]
  rfl

/-- One value of G28's kinds: `vk27_step`'s statement under `G28Env`, with the `runtime.memequal`
contract `MemEqOK`. -/
theorem vk28_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2}
    (hE : G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK28 lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s osp)
    (hu : ∀ x, (v.op = .ARM64MOVDnop ∨ v.op = .ARM64MOVDreg) → v.args[0]? = some x →
      ∃ r c, regHome? lc x = some r ∧ cls (lc.ty x) = some c ∧
        UOK m (some (r, c, lc.signOf lc.ctx.f.valueTab.size x)))
    (hpre : G14Pre lc s v)
    (hcall : CallOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hcallz : CallOKZAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hicall : ICallOKAt osp H E (Link.byId sym text az ez ps.toList) ret lc s s' v m)
    (hwb : WbOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s v m) (hclo : CloOK E s v m)
    (hgetg : GetGOK E v) (hmeq : MemEqOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s v m)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp ∧ UOK m' (uEntry lc v) := by
  cases hVK with
  | g27 _ hVK27 =>
    obtain ⟨E', m', hx, hE', h⟩ := vk27_step hE.env F hhome hcf hv hVK27 hvs htemp hj hj' hreads
      hm hinv hu hpre hcall hcallz hicall hwb hclo hgetg hs
    exact ⟨E', m', hx, hE.extend hx hE', h⟩
  | memEq hop hsz hh hty ha0 ha1 ha2 hh0 hh1 hh2 hc0 hc1 hc2 hma =>
    obtain ⟨hlcE, -, -, -, -, -, hsyms, -, -, -, hF⟩ := hE.env.env.env.env
    have hframed : E.framed = true := by
      cases hfr : E.framed
      · exact absurd hop (hE.memeqs hfr id v hv)
      · rfl
    have hue : uEntry lc v = none := by simp only [uEntry, narrowLd?_memEq hop]
    rw [hue]
    obtain ⟨m', h1, h2, h3, h4⟩ := g28_memEq (H := H) F hF hlcE hcf hframed hsyms hm hinv.core
      hinv.slots (kread_of_reads hreads) (knext_kStep fun _ => (hs_reg hh).noRegs) hj hj' hop hsz
      hh hty ha0 ha1 ha2 hh0 hh1 hh2 hc0 hc1 hc2 hma hvs htemp hs hmeq
    exact ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩, trivial⟩

/-- **G28, values.** `g27_value`'s statement over `checkG28`, under `G28Env`, with the trusted
`runtime.memequal` contract `MemEqOK` next to `CallOK`, `CallOKZ`, `ICallOK`, `WbOK`, `CloOK` and
`GetGOK`. -/
theorem g28_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG28 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s osp) (hu : UOK m (uAt lc blk i))
    (hpre : G14Pre lc s v)
    (hcall : CallOKAt osp H E g L lc s s' v m) (hcallz : CallOKZAt osp H E g L lc s s' v m)
    (hicall : ICallOKAt osp H E L ret lc s s' v m)
    (hwb : WbOKAt osp H E g L lc s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hmeq : MemEqOKAt osp H E g L lc s v m) (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' osp ∧
      UOK m' (uAt lc blk (i + 1)) := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    obtain ⟨E', m', hx, hE', h⟩ := g27_value (checkG27_of_28 hl hc) hE.env hbid hb hi hv hen hm
      hinv hu hpre hcall hcallz hicall hwb hclo hgetg hs
    exact ⟨E', m', hx, hE.extend hx hE', h⟩
  | true =>
  have hE0 := hE
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, hcf, hk, hlt, hnd, hblocks, -, hmovd⟩ :=
    checkG28_spec hl hc
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
  obtain ⟨htemp, hVK⟩ := vkind28_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  have hu1 : uAt c.cx.lc blk (i + 1) = uEntry c.cx.lc v := by simp [uAt, hi, hv]
  rw [kAt_succ hi hv, hu1]
  exact vk28_step hE0 F hhome hcf hv hVK hvs htemp hj hj' hreads hm hinv
    (fun x hop hx => by
      obtain ⟨r, c', hr, hc', hu0⟩ := movdOK_spec hmovd hbid hb hi hv hop hx
      exact ⟨r, c', hr, hc', hu0 ▸ hu⟩)
    hpre hcall hcallz hicall hwb hclo hgetg hmeq hs

/-- A nil check of G28's kinds is G7's. -/
theorem vk28_nil {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK28 lc g v kd)
    (hop : v.op = .ARM64LoweredNilCheck) : VK7 lc g v kd := by
  cases h with
  | g27 _ h => exact vk27_nil h hop
  | memEq h => rw [hop] at h; cases h

/-- **G28, nil panics.** `g27_nilPanic`'s statement over `checkG28`, under `G28Env`. -/
theorem g28_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG28 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  cases hl : lc.ctx.f.lowered with
  | false => exact g27_nilPanic (checkG27_of_28 hl hc) hE.env hbid hb hi hv hop hm hinv hs
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, -, -⟩ :=
    checkG28_spec hl hc
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
  obtain ⟨-, hVK⟩ := vkind28_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases vk28_nil hVK hop with
  | g6 hne _ => exact absurd hop hne
  | nil _ hsz2 _ _ hao hma =>
    exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma hvs hs

/-- A bounds panic of G28's kinds is G19's (`vk19_boundsPanic`). -/
theorem vk28_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In}
    {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64}
    {tab : PcTab} {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value}
    {s : LocState} {m : MState} {e : Panic} {mm' : Mem} {K : KMap} {kd : VKind2} {row : List Nat}
    (F : Facts lc sym text az ez ps.toList ret E)
    (hsyms : ∀ y, (Link.byId sym text az ez ps.toList).sym y ≠ ret ∧
      ∀ p ∈ ps.toList, (Link.byId sym text az ez ps.toList).addr p.id ≠
        some ((Link.byId sym text az ez ps.toList).sym y))
    (hpb : pbOK lc ps.toList tab = true) (hrow : tab.lookup bid = some row)
    (hb : lc.ctx.f.block? bid = some blk) (hi : blk.values[i]? = some id)
    (hv : lc.ctx.f.value? id = some v) (hVK : VK28 lc g v kd)
    (hvs : VStep2 ps kd (row.getD i 0) (row.getD (i + 1) 0))
    (hj : E.pcOf bid i = pcAt text ps.toList (row.getD i 0))
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s osp)
    (hbok : BoundsOK H g (Link.byId sym text az ez ps.toList) ps.toList)
    (hs : stepLoc env lc s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      PPanics H (Link.byId sym text az ez ps.toList) ps.toList ret m' e' := by
  cases hVK with
  | memEq h => rcases pbOp_cases hop with h' | h' | h' | h' <;> rw [h'] at h <;> cases h
  | g27 _ hVK27 =>
  cases hVK27 with
  | logSh h => rcases pbOp_cases hop with h' | h' | h' | h' <;> rw [h'] at h <;> cases h
  | g25 _ hVK25 =>
  cases hVK25 with
  | csel h => rcases pbOp_cases hop with h' | h' | h' | h' <;> rw [h'] at h <;> cases h
  | csel0 h => rcases pbOp_cases hop with h' | h' | h' | h' <;> rw [h'] at h <;> cases h
  | tst h => rcases pbOp_cases hop with h' | h' | h' | h' <;> rw [h'] at h <;> cases h
  | tstw h => rcases pbOp_cases hop with h' | h' | h' | h' <;> rw [h'] at h <;> cases h
  | g24 _ _ hVK24 =>
    cases hVK24 with
    | sp hsp => rcases pbOp_cases hop with h | h | h | h <;> rw [h] at hsp <;> cases hsp
    | g23 _ hVK23 =>
      cases hVK23 with
      | cset hc =>
        rcases pbOp_cases hop with h | h | h | h <;> rw [h] at hc <;> simp [Cond.ofOp] at hc
      | g22 _ hVK22 =>
        cases hVK22 with
        | ldp hop' => rw [hop'] at hop; cases hop
        | stp hop' => rw [hop'] at hop; cases hop
        | g21 _ hVK21 =>
          cases hVK21 with
          | regSame hop' => rw [hop'] at hop; cases hop
          | regMov hop' => rw [hop'] at hop; cases hop
          | g20 _ hVK20 =>
            cases hVK20 with
            | nop hop' => rw [hop'] at hop; cases hop
            | g19 _ hVK19 =>
              exact vk19_boundsPanic F hsyms hpb hrow hb hi hv hVK19 hvs hj hreads hop hm hinv
                hbok hs

/-- **G28, bounds panics.** `g27_boundsPanic`'s statement over `checkG28`, under `G28Env` and
`BoundsOK`. -/
theorem g28_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG28 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hbok : BoundsOK H g L ps.toList)
    (hs : stepLoc env lc s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    exact g27_boundsPanic (checkG27_of_28 hl hc) hE.env hbid hb hi hv hop hm hinv hbok hs
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, hsyms, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, hpb, -⟩ :=
    checkG28_spec hl hc
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
  have hen : entryOp24 v.op = false := by
    rcases pbOp_cases hop with h | h | h | h <;> rw [h] <;> rfl
  obtain ⟨-, hVK⟩ := vkind28_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  exact vk28_boundsPanic F hsyms hpb hrow hb hi hv hVK hvs hj hreads hop hm hinv hbok hs

/-- **G28, terminators.** `g27_term`'s statement over `checkG28`, under `G28Env`. -/
theorem g28_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG28 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList := by
  cases hl : lc.ctx.f.lowered with
  | false => exact g27_term (checkG27_of_28 hl hc) hE.env hbid hb hm hinv hpre ht
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome, -, hk, hlt, hnd, hblocks, -, -⟩ :=
    checkG28_spec hl hc
  exact termK_step hpcOf ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb
    hm hinv hpre ht

end GoFV.Proof.Gen

import GoFV.Proof.Gen.G18
import GoFV.Proof.Gen.Spec19
import GoFV.SSA.Sem.Hooks

variable [GoFV.SSA.Sem.Addrs]

/-!
# Soundness of the genssa validator's slice G19: bounds panics (`docs/plans/proofs3.md` §4)

`g19_value`, `g19_term`, `g19_nilPanic`: `g18_value`'s, `g18_term`'s and `g18_nilPanic`'s
statements over `checkG19`, with the same premises (a bounds panic never steps to a state).
`g19_boundsPanic`: a bounds panic that `runLoc` runs to a panic `e` is matched by `runProg` steps
to a state where the runtime hook panics with `e` (`BoundsAgree`: or, for a constant index of a
signed kind, with the unsigned kind, which Go reports the same), under the hook's contract
`BoundsOK`.

`LoweredPanicBounds{RR,RC,CR,CC} [k] … mem` runs under `runLoc` as Phase 1's `panicBounds` of the
index `x` and the length `y` (registers, or the aux constants as 64-bit integers): the panic
`.bounds k x' y'` with `x'` read signed for the signed kinds (`stepLoc_pb_panic`). Genssa emits the
`MOVD`s of the constants outside `0..31` into `R0`/`R1` (`pstar_pbMovs`), a `PCDATA` no-op and
`CALL runtime.panicBounds(SB)`. The hook decodes the `PCDATA_PanicBounds` value in force at the
`CALL`, which `checkG19` checked is the encoding of the operands (`pbOK`), and reads the registers it
names (`boundsPanic`, `boundsDecode_pbEnc`). A register operand of class 64 is the machine word
(`reg_low`); a moved constant is the word `MOVD` wrote; an encoded constant is itself
(`boundsPanic_agree`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The premise and the panics -/

/-- **The bounds-panic hook's contract** (trusted, semantics3 §6, mirroring `panicBoundsHook`;
`docs/proofs/STATUS.md` Assumptions): from every machine state at the symbol of
`runtime.panicBounds` whose `X30` is the return address of a `CALL` at index `k` of the Prog list,
the hook panics with `boundsPanic` of the `PCDATA_PanicBounds` value in force at that `CALL`
(`pbData`) and the state's registers. -/
def BoundsOK (H : Hooks) (g : G2In) (L : Link) (ps : List Prog) : Prop :=
  ∀ k (hk : k < ps.length) y (c : Nat) next (m₁ : MState), ps[k].to.sym = some y →
    g.syms[y]? = some pbSym → pbData ps k = some (constA c) → L.nextAddr ps[k].id = some next →
    m₁.pc = L.sym y → m₁.x 30 = next → ∃ s', H.call m₁ = some (.panicked (boundsPanic c m₁) s')

/-- The machine's bounds panic `e'` and Phase 1's `e`: the same, or, for a constant index (which
the encoding records as unsigned) of a signed kind, the unsigned kind `k + 1` of the same
nonnegative index, which Go's `boundsError` reports with the same message. -/
def BoundsAgree (e e' : Panic) : Prop :=
  e' = e ∨ ∃ k x y, e = .bounds k x y ∧ e' = .bounds (k + 1) x y ∧ k % 2 = 0 ∧ k < 16 ∧ 0 ≤ x

/-! ## The encoding -/

/-- `abi.BoundsDecode` inverts `pbEnc` on its ranges. -/
theorem boundsDecode_pbEnc {code xv yv : Nat} {sg xr yr : Bool} (hc : code < 9)
    (hx : xv < (if xr then 16 else 32)) (hy : yv < (if yr then 16 else 32)) :
    boundsDecode (pbEnc code sg xr yr xv yv) = (code, sg && xr, xr, yr, xv, yv) := by
  cases xr <;> cases yr <;> cases sg <;> simp only [↓reduceIte, Bool.false_eq_true] at hx hy <;>
  · generalize hE : pbEnc _ _ _ _ xv yv = E
    simp only [pbEnc, ↓reduceIte, Bool.false_eq_true] at hE
    simp only [boundsDecode, Prod.mk.injEq]
    repeat' split
    all_goals simp only [beq_iff_eq, beq_eq_false_iff_ne, Bool.and_true, Bool.and_false,
      Bool.false_eq_true, Bool.true_eq_false, ne_eq, Bool.not_eq_true] at *
    all_goals (repeat' apply And.intro)
    all_goals first | trivial | omega

theorem toInt_ofNat_small {n : Nat} (h : n < 32) : (BitVec.ofNat 64 n).toInt = n := by
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)]
  split <;> omega

/-- The hook's panic for the encoding of a bounds panic of kind `k` whose operands are registers
(`xr`, `yr`) holding `X`, `Y` or constants `xv`, `yv`: Phase 1's panic, up to `BoundsAgree`. -/
theorem boundsPanic_agree {k : Nat} (hk : k ≤ 16) {xr yr : Bool} {xv yv : Nat}
    (hx : xv < (if xr then 16 else 32)) (hy : yv < (if yr then 16 else 32)) (m₁ : MState)
    {X Y : BitVec 64} (hX : X = if xr then m₁.x (BitVec.ofNat 5 xv) else BitVec.ofNat 64 xv)
    (hY : Y = if yr then m₁.x (BitVec.ofNat 5 yv) else BitVec.ofNat 64 yv) :
    BoundsAgree (.bounds k (if k % 2 == 0 && k < 16 then X.toInt else (X.toNat : Int)) Y.toInt)
      (boundsPanic (pbEnc (k / 2) (pbSigned k) xr yr xv yv) m₁) := by
  unfold boundsPanic
  rw [boundsDecode_pbEnc (by omega) hx hy]
  have hYi : (if yr then (m₁.x (BitVec.ofNat 5 yv)).toInt else (yv : Int)) = Y.toInt := by
    cases yr
    · simp only [↓reduceIte, Bool.false_eq_true] at hY hy ⊢
      subst hY
      rw [toInt_ofNat_small hy]
    · simp only [↓reduceIte] at hY ⊢
      rw [hY]
  simp only [hYi]
  by_cases h16 : k = 16
  · subst h16
    have h8 : (16 : Nat) / 2 = 8 := rfl
    simp only [h8, ↓reduceIte, pbSigned]
    left
    cases xr
    · simp only [↓reduceIte, Bool.false_eq_true] at hX hx ⊢
      subst hX
      simp [BitVec.toNat_ofNat]
      omega
    · simp only [↓reduceIte] at hX ⊢
      subst hX
      simp
  · have h8 : ¬ k / 2 = 8 := by omega
    simp only [h8, ↓reduceIte]
    cases xr
    · simp only [↓reduceIte, Bool.false_eq_true, Bool.and_false] at hX hx ⊢
      subst hX
      have hxi : (BitVec.ofNat 64 xv).toInt = xv := toInt_ofNat_small hx
      have hxn : ((BitVec.ofNat 64 xv).toNat : Int) = xv := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [hxi, hxn]
      rcases Nat.mod_two_eq_zero_or_one k with he | ho
      · right
        refine ⟨k, xv, Y.toInt, ?_, ?_, he, by omega, by omega⟩
        · simp [he, show k < 16 by omega]
        · congr 1; omega
      · left
        have : ¬ (k % 2 == 0 && decide (k < 16)) = true := by simp [ho]
        simp only [this, ↓reduceIte]
        congr 1; omega
    · simp only [↓reduceIte, Bool.and_true] at hX ⊢
      subst hX
      left
      unfold pbSigned
      by_cases he : k % 2 = 0
      · have : (k % 2 == 0 && decide (k < 16)) = true := by simp [he]; omega
        simp only [this, ↓reduceIte]
        congr 1; omega
      · have : (k % 2 == 0 && decide (k < 16)) = false := by simp [he]
        simp only [this, Bool.false_eq_true, ↓reduceIte]
        congr 1; omega

/-! ## `stepLoc` of a bounds panic -/

section Step

variable {env : Env} {lc : LocCtx} {s : LocState} {v : Value}

theorem pbOp_cases {op : Op} (h : pbOp op = true) :
    op = .ARM64LoweredPanicBoundsRR ∨ op = .ARM64LoweredPanicBoundsRC ∨
      op = .ARM64LoweredPanicBoundsCR ∨ op = .ARM64LoweredPanicBoundsCC := by
  unfold pbOp at h
  split at h <;> simp_all

/-- A bounds panic faults on no argument. -/
theorem pb_nilFaults {ctx : Ctx} (hop : pbOp v.op = true) (argv : List Val) :
    nilFaults true ctx v argv = none := by
  have hf0 : v.op.faultOnNilArg0 = false := by
    rcases pbOp_cases hop with h | h | h | h <;> rw [h] <;> decide
  have hf1 : v.op.faultOnNilArg1 = false := by
    rcases pbOp_cases hop with h | h | h | h <;> rw [h] <;> decide
  have hn : nilAccesses ctx v argv = [] := by
    simp only [nilAccesses, hf0, hf1, Bool.not_false, ↓reduceIte, Option.toList_none,
      List.append_nil]
    split <;> simp
  unfold nilFaults
  simp only [hn, List.any_nil, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
  split <;> rfl

theorem pbcOf_spec {c : Int} (h : pbcOf lc v = some c) :
    ∃ a : AuxDef, v.aux.bind lc.ctx.tabs.aux? = some a ∧ a.kind = .pbc c := by
  unfold pbcOf at h
  split at h
  · rename_i heq
    cases h
    exact ⟨_, heq, rfl⟩
  · cases h

theorem pbccOf_spec {cx cy : Int} (h : pbccOf lc v = some (cx, cy)) :
    ∃ a : AuxDef, v.aux.bind lc.ctx.tabs.aux? = some a ∧ a.kind = .pbcc cx cy := by
  unfold pbccOf at h
  split at h
  · rename_i heq
    cases h
    exact ⟨_, heq, rfl⟩
  · cases h

/-- The arguments of a bounds panic as `panicBounds` reads them. -/
theorem evalOpL_pb {ctx : Ctx} {fr : GoFV.SSA.Sem.Frame} {ty : Ty} {argv : List Val}
    (hop : pbOp v.op = true) :
    (v.op = .ARM64LoweredPanicBoundsRR →
      evalOpL true env ctx fr v argv ty = panicBounds v.auxInt argv) ∧
    (v.op = .ARM64LoweredPanicBoundsRC → ∀ a c x m, v.aux.bind ctx.tabs.aux? = some a →
      a.kind = .pbc c → argv = [x, m] →
      evalOpL true env ctx fr v argv ty = panicBounds v.auxInt [x, .i64 (BitVec.ofInt 64 c), m]) ∧
    (v.op = .ARM64LoweredPanicBoundsCR → ∀ a c y m, v.aux.bind ctx.tabs.aux? = some a →
      a.kind = .pbc c → argv = [y, m] →
      evalOpL true env ctx fr v argv ty = panicBounds v.auxInt [.i64 (BitVec.ofInt 64 c), y, m]) ∧
    (v.op = .ARM64LoweredPanicBoundsCC → ∀ a cx cy m, v.aux.bind ctx.tabs.aux? = some a →
      a.kind = .pbcc cx cy → argv = [m] →
      evalOpL true env ctx fr v argv ty =
        panicBounds v.auxInt [.i64 (BitVec.ofInt 64 cx), .i64 (BitVec.ofInt 64 cy), m]) := by
  have h0 := pb_nilFaults (ctx := ctx) hop argv
  refine ⟨fun hw => ?_, fun hw a c x m ha hk hargv => ?_, fun hw a c y m ha hk hargv => ?_,
    fun hw a cx cy m ha hk hargv => ?_⟩
  · have hg : Op.ARM64LoweredPanicBoundsRR.generic = false := by decide
    unfold evalOpL
    rw [hw]
    simp only [hg, Bool.false_eq_true, ite_false]
    unfold arm64Op
    rw [h0]
    dsimp only
    rw [hw]
  · subst hargv
    have hg : Op.ARM64LoweredPanicBoundsRC.generic = false := by decide
    cases a; cases hk
    unfold evalOpL
    rw [hw]
    simp only [hg, Bool.false_eq_true, ite_false]
    unfold arm64Op
    rw [h0]
    dsimp only
    rw [hw, ha]
  · subst hargv
    have hg : Op.ARM64LoweredPanicBoundsCR.generic = false := by decide
    cases a; cases hk
    unfold evalOpL
    rw [hw]
    simp only [hg, Bool.false_eq_true, ite_false]
    unfold arm64Op
    rw [h0]
    dsimp only
    rw [hw, ha]
  · subst hargv
    have hg : Op.ARM64LoweredPanicBoundsCC.generic = false := by decide
    cases a; cases hk
    unfold evalOpL
    rw [hw]
    simp only [hg, Bool.false_eq_true, ite_false]
    unfold arm64Op
    rw [h0]
    dsimp only
    rw [hw, ha]

/-- `panicBounds` panics only on integer operands, with their kind-dependent reading. -/
theorem panicBounds_panic {kind : Int64} {x y : Val} {m : Mem} {e : Panic} {m' : Mem}
    (h : panicBounds kind [x, y, .mem m] = .panic e m') :
    ∃ (w : Width) (X : BitVec w.bits) (w' : Width) (Y : BitVec w'.bits), x = .int w X ∧
      y = .int w' Y ∧ e = .bounds kind.toInt.toNat
        (if kind.toInt.toNat % 2 == 0 && kind.toInt.toNat < 16 then X.toInt else (X.toNat : Int))
        Y.toInt := by
  cases x <;> cases y <;> simp only [panicBounds] at h <;> try cases h
  exact ⟨_, _, _, _, rfl, rfl, rfl⟩

/-- `panicBounds` never returns a value. -/
theorem panicBounds_ne_ok {kind : Int64} {argv : List Val} {r : Val} :
    panicBounds kind argv ≠ .ok r := by
  unfold panicBounds
  split <;> nofun

/-- `stepLoc` of a bounds panic with the arguments read as `argv`: the panic of `evalOpL`. -/
theorem stepLoc_pb_panic (hop : pbOp v.op = true) {argv : List Val}
    (hmap : v.args.toList.mapM (s.read lc) = .ok argv) {e : Panic} {mm' : Mem}
    (h : stepLoc env lc s v = .panic e mm') :
    evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) = .panic e mm' := by
  have hfl : (LMode.loc lc.ctx.f).faulting = true := rfl
  unfold stepLoc at h
  rcases pbOp_cases hop with ho | ho | ho | ho <;>
  · simp only [hmap, Res.bind, ho, hfl] at h
    rw [if_neg (by decide)] at h
    change (evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) >>=
      fun r => pure ((s.clobber lc v).write lc v.id ((LMode.loc lc.ctx.f).retype (lc.ty v.id) r)))
      = _ at h
    cases he : evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) with
    | ok r => rw [he] at h; cases h
    | panic e' m' => rw [he] at h; cases h; rfl
    | stuck msg => rw [he] at h; cases h

/-- A bounds panic's `evalOpL` never returns a value. -/
theorem evalOpL_pb_ne_ok {ctx : Ctx} {fr : GoFV.SSA.Sem.Frame} {ty : Ty} {argv : List Val}
    {r : Val} (hop : pbOp v.op = true) : evalOpL true env ctx fr v argv ty ≠ .ok r := by
  have h0 := pb_nilFaults (ctx := ctx) hop argv
  have hg : v.op.generic = false := by
    rcases pbOp_cases hop with ho | ho | ho | ho <;> rw [ho] <;> decide
  rcases pbOp_cases hop with ho | ho | ho | ho <;>
  · unfold evalOpL
    rw [hg]
    simp only [Bool.false_eq_true, ite_false]
    rw [ho]
    dsimp only
    unfold arm64Op
    rw [h0]
    dsimp only
    rw [ho]
    dsimp only
    first
    | exact panicBounds_ne_ok
    | (split
       · exact panicBounds_ne_ok
       · split <;> nofun)

/-- A bounds panic never steps to a state. -/
theorem stepLoc_pb_ne_ok (hop : pbOp v.op = true) {s' : LocState} :
    stepLoc env lc s v ≠ .ok s' := by
  intro h
  have hfl : (LMode.loc lc.ctx.f).faulting = true := rfl
  unfold stepLoc at h
  rcases pbOp_cases hop with ho | ho | ho | ho <;>
  · simp only [Res.bind, ho, hfl] at h
    rw [if_neg (by decide)] at h
    cases hm : v.args.toList.mapM (s.read lc) with
    | panic e m => rw [hm] at h; cases h
    | stuck msg => rw [hm] at h; cases h
    | ok argv =>
      rw [hm] at h
      change (evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) >>=
        fun r => pure ((s.clobber lc v).write lc v.id ((LMode.loc lc.ctx.f).retype (lc.ty v.id) r)))
        = _ at h
      cases he : evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) with
      | ok r => exact absurd he (evalOpL_pb_ne_ok hop)
      | panic e m => rw [he] at h; cases h
      | stuck msg => rw [he] at h; cases h

end Step

/-! ## The machine -/

/-- The machine after the `MOVD`s of the moves `mvs` (register, constant). -/
def movRegs (m : MState) : List (Nat × Int) → MState
  | [] => m
  | (k, c) :: r => movRegs (m.wX (BitVec.ofNat 5 k) (BitVec.ofInt 64 c)) r

theorem movRegs_append (m : MState) (l₁ l₂ : List (Nat × Int)) :
    movRegs m (l₁ ++ l₂) = movRegs (movRegs m l₁) l₂ := by
  induction l₁ generalizing m with
  | nil => rfl
  | cons km r ih => obtain ⟨k, c⟩ := km; exact ih _

theorem ofNat5_inj {k q : Nat} (hk : k < 32) (hq : q < 32) (h : BitVec.ofNat 5 k = BitVec.ofNat 5 q) :
    k = q := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  omega

theorem wX_x_self {m : MState} {k : Nat} (hk : k < 31) (val : BitVec 64) :
    (m.wX (BitVec.ofNat 5 k) val).x (BitVec.ofNat 5 k) = val := by
  have h31 : BitVec.ofNat 5 k ≠ BitVec.ofNat 5 31 := fun h => by
    have := ofNat5_inj (k := k) (q := 31) (by omega) (by omega) h; omega
  unfold MState.wX
  split
  · rename_i h; exact absurd h h31
  · simp

theorem wX_x_ne {m : MState} {k q : Nat} (hk : k < 32) (hq : q < 32) (hkq : q ≠ k)
    (val : BitVec 64) : (m.wX (BitVec.ofNat 5 k) val).x (BitVec.ofNat 5 q) = m.x (BitVec.ofNat 5 q) := by
  unfold MState.wX
  split
  · rfl
  · have : BitVec.ofNat 5 q ≠ BitVec.ofNat 5 k := fun h => hkq (ofNat5_inj hq hk h)
    simp [this]

private theorem pstar_trans {H : Hooks} {L : Link} {ps : List Prog} {ret : BitVec 64}
    {a b c : MState} (h1 : PStar H L ps ret a b) (h2 : PStar H L ps ret b c) :
    PStar H L ps ret a c := by
  induction h2 with
  | refl => exact h1
  | tail _ hs ih => exact ih.tail hs

section Run

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx}

/-- The `MOVD`s of the moves `mvs`, each after no-ops. -/
theorem pstar_pbMovs (F : Facts lc sym text az ez psA.toList ret E) :
    ∀ (mvs : List (Nat × Int)), (∀ km ∈ mvs, km.1 < 31) → ∀ {j j' : Nat} {pats : List Pat}
      (m : MState), ManyAt2 psA j (mvs.map (fun km => pbMov km.1 km.2) ++ pats) j' →
      ∃ j₁, ManyAt2 psA j₁ pats j' ∧ PStar H (Link.byId sym text az ez psA.toList) psA.toList ret
        { m with pc := pcAt text psA.toList j } { movRegs m mvs with pc := pcAt text psA.toList j₁ }
  | [], _, j, _, _, _, h => ⟨j, h, .refl⟩
  | (k, c) :: r, hlt, _, _, _, m, h => by
    obtain ⟨j0, h1, h2⟩ := h
    obtain ⟨kk, rfl, hkk, hok, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret h1 m
    have hok' : (Pat.mk (plain .MOVD (· == constA c) (· == regA (REG_R0 + (k : Int)))) "MOVD").ok
        psA.toList[kk] = true := hok
    obtain ⟨has, hf, -, ht, -, -, -⟩ := plain_spec hok'
    simp only [beq_iff_eq] at hf ht
    have hk : k < 31 := hlt _ List.mem_cons_self
    have hstep := progStep_movConst (L := Link.byId sym text az ez psA.toList)
      (s := { m with pc := pcAt text psA.toList kk }) (by omega : k < 32)
      (nextAddr_pcAt F.nodup hkk) has hf ht
    rw [wX_pc] at hstep
    obtain ⟨j₁, h3, hstar2⟩ := pstar_pbMovs F r (fun km h => hlt km (List.mem_cons_of_mem _ h))
      (m.wX (BitVec.ofNat 5 k) (BitVec.ofInt 64 c)) h2
    exact ⟨j₁, h3, pstar_trans (hstar.tail (pstep_at F.nodup F.lt F.ret hkk rfl hstep)) hstar2⟩

end Run

/-! ## Phase 1's panic and the machine words -/

section Phase1

variable {env : Env} {lc : LocCtx} {s : LocState} {v : Value} {E : MatchEnv} {b : ID} {i : Nat}
  {m : MState} {P : BitVec 64 → Prop} {K : Nat → Option Nat}

private theorem mapM_one {a : ID} : [a].mapM (s.read lc) = (s.read lc a).bind fun x => .ok [x] := rfl

private theorem mapM_two {a b : ID} :
    [a, b].mapM (s.read lc) =
      (s.read lc a).bind fun x => (s.read lc b).bind fun y => .ok [x, y] := rfl

private theorem mapM_three {a b c : ID} :
    [a, b, c].mapM (s.read lc) =
      (s.read lc a).bind fun x => (s.read lc b).bind fun y => (s.read lc c).bind fun z =>
        .ok [x, y, z] := rfl

/-- A register operand `REG_R0 + xv` of class 64: an integer it holds is the machine word. -/
theorem pb_reg (hA : AddrAgree E.ι) (hl : lc.ctx.f.lowered = true) (hm : LocMatch E s b i m)
    (hinv : CoreInv E.ι P K s osp) (hR : KRead lc v K) (hnp : v.op ≠ .Phi) {n : Nat} {r : Int}
    {xv : Nat} (hao : argObj lc v n = .ok (64, r)) (hr : r = REG_R0 + xv) (hxv : xv ≤ 15) :
    ∃ a x, v.args[n]? = some a ∧ s.read lc a = .ok x ∧ ∀ (w : Width) (X : BitVec w.bits),
      x = .int w X → X.toInt = (m.x (BitVec.ofNat 5 xv)).toInt ∧
        (X.toNat : Int) = (m.x (BitVec.ofNat 5 xv)).toNat := by
  obtain ⟨a, r', ha, hah, hor, hca⟩ := argObj_spec hao
  obtain ⟨kk, hkk, heq, hkobj⟩ := objOf?_some hor
  have hk : kk = xv := by omega
  subst hk
  obtain ⟨x, hx, hxv', hxf⟩ := arg_rel hA hl hm hinv hah hca (kread_arg hR hnp ha hah hca) hkobj
  rw [rX_lt (by omega)] at hxv'
  refine ⟨a, x, ha, hx, fun w X he => ?_⟩
  subst he
  obtain rfl : w = .w64 := by cases w <;> simp [Fits, Width.bits] at hxf ⊢
  change BitVec 64 at X
  have h1 := reg_low hA hxv' hxf (x' := X.setWidth 64) rfl
  simp only [BitVec.setWidth_eq] at h1
  rw [h1]
  exact ⟨rfl, rfl⟩

theorem bounds_congr {k : Nat} {kind : Int64} (hk : kind.toInt = k) {w w' : Width}
    {X0 : BitVec w.bits} {Y0 : BitVec w'.bits} {X Y : BitVec 64} (hxi : X0.toInt = X.toInt)
    (hxn : (X0.toNat : Int) = X.toNat) (hyi : Y0.toInt = Y.toInt) :
    Panic.bounds kind.toInt.toNat
        (if kind.toInt.toNat % 2 == 0 && kind.toInt.toNat < 16 then X0.toInt else (X0.toNat : Int))
        Y0.toInt =
      .bounds k (if k % 2 == 0 && k < 16 then X.toInt else (X.toNat : Int)) Y.toInt := by
  rw [hk, Int.toNat_natCast, hxi, hxn, hyi]

theorem ofInt_const {c : Int} (h : pbConst c = true) :
    BitVec.ofInt 64 c = BitVec.ofNat 64 c.toNat := by
  obtain ⟨hc, -⟩ := pbConst_spec h
  conv => lhs; rw [hc]
  exact BitVec.ofInt_natCast 64 c.toNat

/-- Phase 1's panic of a bounds panic, and the machine words the encoding names after the moves:
the index `X` and the length `Y` in the registers (`xr`, `yr`) or the constants of the encoding. -/
theorem pb_phase1 (hA : AddrAgree E.ι) (hl : lc.ctx.f.lowered = true) (hm : LocMatch E s b i m)
    (hinv : CoreInv E.ι P K s osp) (hR : KRead lc v K) (hop : pbOp v.op = true) {c : Nat}
    {mvs : List (Nat × Int)} (hinfo : pbInfo lc v = .ok (c, mvs)) {e : Panic} {mm' : Mem}
    (hs : stepLoc env lc s v = .panic e mm') :
    ∃ (k : Nat) (xr yr : Bool) (xv yv : Nat) (X Y : BitVec 64), k ≤ 16 ∧
      xv < (if xr then 16 else 32) ∧ yv < (if yr then 16 else 32) ∧
      c = pbEnc (k / 2) (pbSigned k) xr yr xv yv ∧
      e = .bounds k (if k % 2 == 0 && k < 16 then X.toInt else (X.toNat : Int)) Y.toInt ∧
      X = (if xr then (movRegs m mvs).x (BitVec.ofNat 5 xv) else BitVec.ofNat 64 xv) ∧
      Y = (if yr then (movRegs m mvs).x (BitVec.ofNat 5 yv) else BitVec.ofNat 64 yv) ∧
      (∀ km ∈ mvs, km.1 < 31) := by
  have hnp : v.op ≠ .Phi := by rcases pbOp_cases hop with h | h | h | h <;> rw [h] <;> nofun
  obtain ⟨mm, hmm, -⟩ := hm.mem
  obtain ⟨k, hk1, hk2, hcase⟩ := pbInfo_spec hinfo
  rcases hcase with ⟨ho, hsz, rx, ry, xv, yv, hax, hay, hma, hrx, hxl, hry, hyl, rfl, rfl⟩ |
    ⟨ho, hsz, rx, xv, cy, hax, hma, hrx, hxl, hcy, hrest⟩ |
    ⟨ho, hsz, ry, yv, cx, hay, hma, hry, hyl, hcx, hpc, rfl, rfl⟩ |
    ⟨ho, hsz, cx, cy, hma, hcc, rfl, rfl⟩
  · -- RR
    obtain ⟨a0, x, ha0, hx, hX⟩ := pb_reg hA hl hm hinv hR hnp hax hrx hxl
    obtain ⟨a1, y, ha1, hy, hY⟩ := pb_reg hA hl hm hinv hR hnp hay hry hyl
    obtain ⟨a2, ha2, hamt, hah2⟩ := memArg_spec hma
    have hmap : v.args.toList.mapM (s.read lc) = .ok [x, y, .mem mm] := by
      rw [arr3 hsz ha0 ha1 ha2]
      show [a0, a1, a2].mapM (s.read lc) = _
      rw [mapM_three, hx, hy, read_mem hl hah2 hamt hmm]
      rfl
    have h := stepLoc_pb_panic hop hmap hs
    rw [(evalOpL_pb (env := env) (ctx := lc.ctx) (fr := s.fr) (ty := lc.ty v.id)
      (argv := [x, y, .mem mm]) hop).1 ho] at h
    obtain ⟨w, X0, w', Y0, rfl, rfl, rfl⟩ := panicBounds_panic h
    obtain ⟨hxi, hxn⟩ := hX w X0 rfl
    obtain ⟨hyi, -⟩ := hY w' Y0 rfl
    exact ⟨k, true, true, xv, yv, _, _, hk2, by simp; omega, by simp; omega, rfl,
      bounds_congr hk1 hxi hxn hyi, rfl, rfl, nofun⟩
  · -- RC
    obtain ⟨a0, x, ha0, hx, hX⟩ := pb_reg hA hl hm hinv hR hnp hax hrx hxl
    obtain ⟨a1, ha1, hamt, hah1⟩ := memArg_spec hma
    have hmap : v.args.toList.mapM (s.read lc) = .ok [x, .mem mm] := by
      rw [arr2 hsz ha0 ha1]
      show [a0, a1].mapM (s.read lc) = _
      rw [mapM_two, hx, read_mem hl hah1 hamt hmm]
      rfl
    obtain ⟨au, hau, hku⟩ := pbcOf_spec hcy
    have h := stepLoc_pb_panic hop hmap hs
    rw [(evalOpL_pb (env := env) (ctx := lc.ctx) (fr := s.fr) (ty := lc.ty v.id)
      (argv := [x, .mem mm]) hop).2.1 ho au cy x (.mem mm) hau hku rfl] at h
    obtain ⟨w, X0, w', Y0, rfl, hy0, rfl⟩ := panicBounds_panic h
    cases hy0
    obtain ⟨hxi, hxn⟩ := hX w X0 rfl
    rcases hrest with ⟨hp, rfl, rfl⟩ | ⟨hp, rfl, rfl⟩
    · obtain ⟨-, hc31⟩ := pbConst_spec hp
      exact ⟨k, true, false, xv, cy.toNat, (movRegs m []).x (BitVec.ofNat 5 xv),
        BitVec.ofNat 64 cy.toNat, hk2, by simp; omega, by simp; omega, rfl,
        bounds_congr hk1 hxi hxn (congrArg BitVec.toInt (ofInt_const hp)), rfl, rfl, nofun⟩
    · have hyv : (if xv = 0 then 1 else 0) ≠ xv := by split <;> omega
      have hy31 : (if xv = 0 then 1 else 0) < 31 := by split <;> omega
      refine ⟨k, true, true, xv, if xv = 0 then 1 else 0, _, BitVec.ofInt 64 cy, hk2,
        by simp; omega, by simp; split <;> omega, rfl, bounds_congr hk1 hxi hxn rfl, ?_, ?_, ?_⟩
      · simp only [↓reduceIte, movRegs]
        rw [wX_x_ne (by omega) (by omega) (Ne.symm hyv)]
      · simp only [↓reduceIte, movRegs]
        rw [wX_x_self hy31]
      · intro km hkm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hkm
        subst hkm
        exact hy31
  · -- CR
    obtain ⟨a0, y, ha0, hy, hY⟩ := pb_reg hA hl hm hinv hR hnp hay hry hyl
    obtain ⟨a1, ha1, hamt, hah1⟩ := memArg_spec hma
    have hmap : v.args.toList.mapM (s.read lc) = .ok [y, .mem mm] := by
      rw [arr2 hsz ha0 ha1]
      show [a0, a1].mapM (s.read lc) = _
      rw [mapM_two, hy, read_mem hl hah1 hamt hmm]
      rfl
    obtain ⟨au, hau, hku⟩ := pbcOf_spec hcx
    have h := stepLoc_pb_panic hop hmap hs
    rw [(evalOpL_pb (env := env) (ctx := lc.ctx) (fr := s.fr) (ty := lc.ty v.id)
      (argv := [y, .mem mm]) hop).2.2.1 ho au cx y (.mem mm) hau hku rfl] at h
    obtain ⟨w, X0, w', Y0, hx0, rfl, rfl⟩ := panicBounds_panic h
    cases hx0
    obtain ⟨hyi, -⟩ := hY w' Y0 rfl
    obtain ⟨-, hc31⟩ := pbConst_spec hpc
    exact ⟨k, false, true, cx.toNat, yv, BitVec.ofNat 64 cx.toNat,
      (movRegs m []).x (BitVec.ofNat 5 yv), hk2, by simp; omega, by simp; omega, rfl,
      bounds_congr hk1 (congrArg BitVec.toInt (ofInt_const hpc))
        (congrArg (fun z : BitVec 64 => (z.toNat : Int)) (ofInt_const hpc)) hyi, rfl, rfl, nofun⟩
  · -- CC
    obtain ⟨a0, ha0, hamt, hah0⟩ := memArg_spec hma
    have hmap : v.args.toList.mapM (s.read lc) = .ok [.mem mm] := by
      rw [arr1 hsz ha0]
      show [a0].mapM (s.read lc) = _
      rw [mapM_one, read_mem hl hah0 hamt hmm]
      rfl
    obtain ⟨au, hau, hku⟩ := pbccOf_spec hcc
    have h := stepLoc_pb_panic hop hmap hs
    rw [(evalOpL_pb (env := env) (ctx := lc.ctx) (fr := s.fr) (ty := lc.ty v.id)
      (argv := [.mem mm]) hop).2.2.2 ho au cx cy (.mem mm) hau hku rfl] at h
    obtain ⟨w, X0, w', Y0, hx0, hy0, rfl⟩ := panicBounds_panic h
    cases hx0
    cases hy0
    -- the machine words after the moves
    have hX : (if !pbConst cx then (movRegs m ((if pbConst cx then [] else [(0, cx)]) ++
        (if pbConst cy then [] else [(1, cy)]))).x
        (BitVec.ofNat 5 (if pbConst cx then cx.toNat else 0))
        else BitVec.ofNat 64 (if pbConst cx then cx.toNat else 0)) = BitVec.ofInt 64 cx := by
      cases hpx : pbConst cx
      · simp only [Bool.not_false, ↓reduceIte, List.nil_append, movRegs_append, Bool.false_eq_true]
        cases pbConst cy
        · simp only [Bool.false_eq_true, ↓reduceIte, movRegs]
          rw [wX_x_ne (by omega) (by omega) (by omega), wX_x_self (by omega)]
        · simp only [↓reduceIte, movRegs]
          rw [wX_x_self (by omega)]
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact (ofInt_const hpx).symm
    have hY : (if !pbConst cy then (movRegs m ((if pbConst cx then [] else [(0, cx)]) ++
        (if pbConst cy then [] else [(1, cy)]))).x
        (BitVec.ofNat 5 (if pbConst cy then cy.toNat else 1))
        else BitVec.ofNat 64 (if pbConst cy then cy.toNat else 1)) = BitVec.ofInt 64 cy := by
      cases hpy : pbConst cy
      · simp only [Bool.not_false, ↓reduceIte, movRegs_append, Bool.false_eq_true]
        cases pbConst cx
        · simp only [Bool.false_eq_true, ↓reduceIte, movRegs]
          rw [wX_x_self (by omega)]
        · simp only [↓reduceIte, movRegs]
          rw [wX_x_self (by omega)]
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact (ofInt_const hpy).symm
    refine ⟨k, !pbConst cx, !pbConst cy, if pbConst cx then cx.toNat else 0,
      if pbConst cy then cy.toNat else 1, BitVec.ofInt 64 cx, BitVec.ofInt 64 cy, hk2, ?_, ?_, rfl,
      bounds_congr hk1 rfl rfl rfl, hX.symm, hY.symm, ?_⟩
    · cases hpx : pbConst cx
      · simp
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        have := (pbConst_spec hpx).2; omega
    · cases hpy : pbConst cy
      · simp
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        have := (pbConst_spec hpy).2; omega
    · intro km hkm
      simp only [List.mem_append] at hkm
      rcases hkm with h | h <;> split at h <;>
        simp only [List.not_mem_nil, List.mem_cons, or_false] at h <;> subst h <;> simp

end Phase1


/-! ## The theorems -/

theorem wX30_x {s : MState} {q : Nat} (hq : q < 30) (val : BitVec 64) :
    (s.wX 30 val).x (BitVec.ofNat 5 q) = s.x (BitVec.ofNat 5 q) :=
  wX_x_ne (k := 30) (by omega) (by omega) (by omega) val

/-- One value of G19's kinds (`VK19`) emitted at the Progs from `j` to `j'`: `vk18_step`'s
statement for G19's values, under the same premises (a bounds panic never steps). -/
theorem vk19_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2}
    (hE : G10Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK19 lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s osp) (hpre : G14Pre lc s v)
    (hcall : CallOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hcallz : CallOKZAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hicall : ICallOKAt osp H E (Link.byId sym text az ez ps.toList) ret lc s s' v m)
    (hwb : WbOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s v m) (hclo : CloOK E s v m)
    (hgetg : GetGOK E v) (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G10Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp := by
  cases hVK with
  | g18 _ hVK18 =>
    exact vk18_step hE F hhome hcf hv hVK18 hvs htemp hj hj' hreads hm hinv hpre hcall hcallz
      hicall hwb hclo hgetg hs
  | pb hop => exact absurd hs (stepLoc_pb_ne_ok hop)

/-- **G19, values.** `g18_value`'s statement over `checkG19`, with the same premises. -/
theorem g19_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG19 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp3 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hpre : G14Pre lc s v)
    (hcall : CallOK H E g L lc s s' v m) (hcallz : CallOKZ H E g L lc s s' v m)
    (hicall : ICallOK H E L ret lc s s' v m)
    (hwb : WbOK H E g L lc s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G10Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' := by
  have hE0 := hE
  obtain ⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, hcf, hk, hlt, hnd, hblocks, -⟩ := checkG19_spec hc
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
  obtain ⟨htemp, hVK⟩ := vkind19_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  rw [kAt_succ hi hv]
  exact vk19_step hE0 F hhome hcf hv hVK hvs htemp hj hj' hreads hm hinv hpre hcall hcallz hicall
    hwb hclo hgetg hs

/-- A nil check of G19's kinds is G7's. -/
theorem vk19_nil {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK19 lc g v kd)
    (hop : v.op = .ARM64LoweredNilCheck) : VK7 lc g v kd := by
  cases h with
  | g18 _ h => exact vk18_nil h hop
  | pb hop' => exact absurd hop' (by rw [hop]; decide)

/-- **G19, nil panics.** `g18_nilPanic`'s statement over `checkG19`. -/
theorem g19_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG19 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
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
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, -⟩ := checkG19_spec hc
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
  obtain ⟨-, hVK⟩ := vkind19_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases vk19_nil hVK hop with
  | g6 hne _ => exact absurd hop hne
  | nil _ hsz2 _ _ hao hma =>
    exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma hvs hs

/-- A bounds panic of G19's kinds (`VK19`) at value `i` of block `bid`, whose PC table row is
`row`: `g19_boundsPanic`'s conclusion, from the facts of an accepted function (`g19_boundsPanic`,
G20's `g20_boundsPanic`). -/
theorem vk19_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In}
    {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64}
    {tab : PcTab} {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value}
    {s : LocState} {m : MState} {e : Panic} {mm' : Mem} {K : KMap} {kd : VKind2} {row : List Nat}
    (F : Facts lc sym text az ez ps.toList ret E)
    (hsyms : ∀ y, (Link.byId sym text az ez ps.toList).sym y ≠ ret ∧
      ∀ p ∈ ps.toList, (Link.byId sym text az ez ps.toList).addr p.id ≠
        some ((Link.byId sym text az ez ps.toList).sym y))
    (hpb : pbOK lc ps.toList tab = true) (hrow : tab.lookup bid = some row)
    (hb : lc.ctx.f.block? bid = some blk) (hi : blk.values[i]? = some id)
    (hv : lc.ctx.f.value? id = some v) (hVK : VK19 lc g v kd)
    (hvs : VStep2 ps kd (row.getD i 0) (row.getD (i + 1) 0))
    (hj : E.pcOf bid i = pcAt text ps.toList (row.getD i 0))
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s osp)
    (hbok : BoundsOK H g (Link.byId sym text az ez ps.toList) ps.toList)
    (hs : stepLoc env lc s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      PPanics H (Link.byId sym text az ez ps.toList) ps.toList ret m' e' := by
  have hA := F.addr
  have hl := F.lowered
  cases hVK with
  | g18 hn _ => rw [hop] at hn; cases hn
  | @pb cc mvs _ _ _ hinfo =>
    obtain ⟨k, xr, yr, xv, yv, X, Y, hk16, hxv, hyv, hcenc, rfl, hX, hY, hmv⟩ :=
      pb_phase1 hA hl hm hinv.core (kread_of_reads hreads) hop hinfo hs
    -- the `MOVD`s, then the `CALL`
    have hvs' : ManyAt2 ps (row.getD i 0)
        (mvs.map (fun km => pbMov km.1 km.2) ++ [pbCall g]) (row.getD (i + 1) 0) := hvs
    obtain ⟨j₁, hmany, hstar1⟩ := pstar_pbMovs (H := H) F mvs hmv m hvs'
    rw [pc_eta hm hj] at hstar1
    obtain ⟨k0, hone, hk0⟩ := hmany
    obtain ⟨kc, rfl, hkc, hokc, hstar2⟩ :=
      pstar_oneAt2 (H := H) F.nodup F.lt F.ret hone (movRegs m mvs)
    have hokc' : (Pat.mk (plain .CALL (fun a : Addr => a == {}) (pbTarget g)) "CALL").ok
        ps.toList[kc] = true := hokc
    obtain ⟨has, -, -, ht, -, -, -⟩ := plain_spec hokc'
    simp only [pbTarget, Bool.and_eq_true, beq_iff_eq] at ht
    obtain ⟨⟨⟨⟨⟨ht1, ht2⟩, -⟩, -⟩, ht3⟩, ht4⟩ := ht
    cases hy : ps.toList[kc].to.sym with
    | none => rw [hy] at ht4; cases ht4
    | some y =>
      rw [hy] at ht4
      have hy' : g.syms[y]? = some pbSym := by simpa using ht4
      obtain ⟨m₁, hm₁⟩ : ∃ m₁ : MState, m₁ = { ({ movRegs m mvs with
          pc := pcAt text ps.toList kc } : MState).wX 30 (pcAt text ps.toList (kc + 1)) with
          pc := (Link.byId sym text az ez ps.toList).sym y } := ⟨_, rfl⟩
      have hcstep := progStep_callSym (L := Link.byId sym text az ez ps.toList)
        (s := { movRegs m mvs with pc := pcAt text ps.toList kc })
        (nextAddr_pcAt F.nodup hkc) has ht1 ht2 ht3 hy
      rw [← hm₁] at hcstep
      have hstar := pstar_trans hstar1 (hstar2.tail (pstep_at F.nodup F.lt F.ret hkc rfl hcstep))
      -- the `PCDATA_PanicBounds` in force at the `CALL`
      have hdata : pbData ps.toList kc = some (constA cc) := by
        have := pbOK_spec hpb hrow hb hi hv hop hinfo
        simp only [ManyAt2] at hk0
        rw [hk0] at this
        simpa using this
      have hpc1 : m₁.pc = (Link.byId sym text az ez ps.toList).sym y := by rw [hm₁]
      have hx30 : m₁.x 30 = pcAt text ps.toList (kc + 1) := by
        rw [hm₁]; simp [MState.wX]
      obtain ⟨s', hcall⟩ := hbok kc hkc y cc _ m₁ hy hy' hdata (nextAddr_pcAt F.nodup hkc) hpc1 hx30
      refine ⟨boundsPanic cc m₁, m₁, ?_, hstar, ?_⟩
      · have hm1 : ∀ q, q < 16 → m₁.x (BitVec.ofNat 5 q) = (movRegs m mvs).x (BitVec.ofNat 5 q) :=
          fun q hq => by rw [hm₁]; exact wX30_x (by omega) _
        subst hcenc
        refine boundsPanic_agree hk16 hxv hyv m₁ ?_ ?_
        · cases xr
          · simpa using hX
          · simp only [↓reduceIte] at hX hxv ⊢
            rw [hX, hm1 xv hxv]
        · cases yr
          · simpa using hY
          · simp only [↓reduceIte] at hY hyv ⊢
            rw [hY, hm1 yv hyv]
      · exact ⟨by rw [hpc1]; exact (hsyms y).1,
          .inr ⟨by rw [hpc1]; exact progAt?_none (hsyms y).2, s', hcall⟩⟩

/-- **G19, bounds panics.** A bounds panic of an accepted function that `runLoc` runs to a panic
`e` from a state related to `m` is matched by `runProg` steps of genssa's P0 Progs (the `MOVD`s of
its moved constants and `CALL runtime.panicBounds(SB)`) to a state where `runProg` panics with
`e'`, `e` up to the signedness of a constant index (`BoundsAgree`), under the hook's contract
`BoundsOK`. -/
theorem g19_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG19 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hbok : BoundsOK H g L ps.toList)
    (hs : stepLoc env lc s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' := by
  obtain ⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, hsyms, -, -, -, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, hpb⟩ :=
    checkG19_spec hc
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
  have hen : entryOp3 v.op = false := by
    rcases pbOp_cases hop with h | h | h | h <;> rw [h] <;> rfl
  obtain ⟨-, hVK⟩ := vkind19_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  exact vk19_boundsPanic F hsyms hpb hrow hb hi hv hVK hvs hj hreads hop hm hinv hbok hs

/-- **G19, terminators.** `g18_term`'s statement over `checkG19`. -/
theorem g19_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG19 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
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
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome, -, hk, hlt, hnd, hblocks, -⟩ := checkG19_spec hc
  exact termK_step hpcOf ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb
    hm hinv hpre ht

end GoFV.Proof.Gen

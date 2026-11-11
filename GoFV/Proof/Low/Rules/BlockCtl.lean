import GoFV.Proof.Low.Rules.BlockFlags

variable [GoFV.SSA.Sem.Addrs]

/-!
# Lowering rule lemmas: block rules that build a new control (`ARM64.rules:558-561`, `603`, `604`)

Block rules of lowered code whose result control is a fresh node built from the matched values
(#385; the build case of `BlockRuleL.Sound`, `obl_build`):

* `(K (CMPconst [0] z:(AND x y)))` as `(K (TST x y))` (`558`), `(K (CMPconst [0] x:(ANDconst [c]
  y)))` as `(K (TSTconst [c] y))` (`559`), and the `CMPWconst` forms as `TSTW` (`560`) and
  `TSTWconst [int32(c)]` (`561`), for `K` among `EQ NE LT LE GT GE`: `TST` leaves `C` clear where
  `CMP k, #0` sets it, and both leave `V` clear, so they agree on every condition that does not
  read `C` (`logic_sub0`).
* `(UGT|ULE (CMPconst [0] x))` as `(NE|EQ (CMPconst [0] x))` (`603`) and the `CMPWconst` forms
  (`604`): with `C` set by `x - 0`, `HI` is `NE` and `LS` is `EQ` (`hi_sub0`, `ls_sub0`).
-/

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low
open GoFV.Rules.Generated.ARM64

/-- The conditions that do not read `C`. -/
def noC : Cond → Bool
  | .hs | .lo | .hi | .ls => false
  | _ => true

/-- `TST` of `k` and `CMP k, #0` agree on the conditions that do not read `C`. -/
theorem logic_sub0 {n : Nat} (hn : 0 < n) (k : BitVec n) {c : Cond} (hc : noC c = true) :
    c.onVal (logicFlags k).toVal = c.onVal (Arm64.subFlags k 0).2.toVal := by
  rw [subFlags_zero hn]
  cases c <;> simp_all [noC, logicFlags, Flags.toVal, Cond.onVal, Cond.eval, Val.flagBit]

/-- `HI` on the flags of `x - 0` (`C` set) is `NE`. -/
theorem hi_sub0 {n : Nat} (hn : 0 < n) (k : BitVec n) :
    Cond.hi.onVal (Arm64.subFlags k 0).2.toVal = Cond.ne.onVal (Arm64.subFlags k 0).2.toVal := by
  rw [subFlags_zero hn]; simp [Flags.toVal, Cond.onVal, Cond.eval, Val.flagBit]

/-- `LS` on the flags of `x - 0` (`C` set) is `EQ`. -/
theorem ls_sub0 {n : Nat} (hn : 0 < n) (k : BitVec n) :
    Cond.ls.onVal (Arm64.subFlags k 0).2.toVal = Cond.eq.onVal (Arm64.subFlags k 0).2.toVal := by
  rw [subFlags_zero hn]; simp [Flags.toVal, Cond.onVal, Cond.eval, Val.flagBit]

theorem cmp_int0 (k : BitVec 64) :
    Arm64.cmp (.int .w64 k) (.int .w64 0) = Arm64.cmpRes (Arm64.subFlags k 0) := by
  simp [Arm64.cmp, Arm64.reg]

theorem cmp_poison_int0 : Arm64.cmp .poison (.int .w64 0) = .poison := by
  simp [Arm64.cmp, Arm64.reg]

theorem readsN_hi : readsN .hi := fun _ => rfl
theorem readsN_ls : readsN .ls := fun _ => rfl

set_option hygiene false in
/-- The goal of a block rule building its new control, unfolded: `nodeDenL` of the built node,
`hc`/`harg` normalized, both blocks' conditions (`brVal`, `Arm64.taken`). -/
local macro "arm_bbuild" : tactic => `(tactic| (
  arm_bunfold
  all_goals (
    arm_norm
    simp only [nodeDenL, nodeTyL, nodeAuxL, toAuxIntL, List.getElem?_cons_zero, DV.valOr, sigmaL,
      Pat.bindsL, Pat.bindssL, rule_unfold_ds, rule_helper, rule_unfold_s] at ⊢
    arm_norm
    (try simp (config := { decide := true }) only [Pat.argsOKL, Pat.argsOKLs, Pat.argsOKLn,
      Pat.argsOKLns, Pat.isOpL, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, and_true,
      true_and, false_or, true_or, or_true, Nat.reduceAdd] at harg)
    (try simp only [DV.int.injEq] at hc)
    simp (config := { decide := true }) only [brVal, Arm64.taken, ite_true, Bool.bne_false]
      at hbr ⊢)))

set_option hygiene false in
/-- `(UGT|ULE (CMPconst [0] x)) => (NE|EQ (CMPconst [0] x))`. -/
local macro "arm_ugt0" hr:term "," hs:term : tactic => `(tactic| (
  arm_bbuild
  rw [hc, show BitVec.ofInt 64 0 = 0 from rfl] at hbr
  obtain ⟨r, hrx, h⟩ := reg_of_cmp0 $hr (Mono.onVal_of (retypeL_cmp_ref _ _ _) hbr)
  have hcmp : Arm64.cmp (e.leaf [0]) (.int .w64 (BitVec.ofInt 64 0)) =
      Arm64.cmpRes (Arm64.subFlags r 0) := by
    unfold Arm64.cmp; rw [hrx]; rfl
  rw [hcmp, retypeL_cmpRes, onVal_cmpRes, ← h, $hs (by decide)]))

/-- `ARM64.rules:603`: `(UGT (CMPconst [0] x)) => (NE (CMPconst [0] x))` -/
theorem r_ARM64_603_sound : BlockRuleL.Sound r_ARM64_603 := by arm_ugt0 readsN_hi, hi_sub0

/-- `ARM64.rules:603`: `(ULE (CMPconst [0] x)) => (EQ (CMPconst [0] x))` -/
theorem r_ARM64_603_2_sound : BlockRuleL.Sound r_ARM64_603_2 := by arm_ugt0 readsN_ls, ls_sub0

set_option hygiene false in
/-- `(K (CMPconst [0] x:(ANDconst [c] y))) => (K (TSTconst [c] y))`. -/
local macro "arm_tstc" : tactic => `(tactic| (
  arm_bbuild
  have hw : 64 ≤ argWidth (e.ty [0]) := harg.1
  rw [hc, show BitVec.ofInt 64 0 = 0 from rfl] at hbr
  have h1 := Mono.onVal_of (retypeL_cmp_ref _ _ _) hbr
  cases hy : Arm64.reg (e.leaf [0, 0]) with
  | none =>
    simp only [Arm64.op1, hy, retypeL_poison, cmp_poison_int0] at h1
    simp [Cond.onVal] at h1
  | some r =>
    simp only [Arm64.op1, hy] at h1
    simp only [Arm64.flags1, hy, retypeL_flags_toVal]
    rcases retypeL_res_wide hw (r &&& BitVec.ofInt 64 (e.auxInt [0]).toInt) with h | h <;>
      rw [h] at h1
    · rw [cmp_int0, onVal_cmpRes] at h1; rw [logic_sub0 (by decide) _ rfl]; exact h1
    · rw [cmp_poison_int0] at h1; simp [Cond.onVal] at h1))

/-- `ARM64.rules:559`: `(EQ (CMPconst [0] x:(ANDconst [c] y)) yes no) && x.Uses == 1 => (EQ (TSTconst [c] y) yes no)` -/
theorem r_ARM64_559_sound : BlockRuleL.Sound r_ARM64_559 := by arm_tstc

/-- `ARM64.rules:559`: `(GE (CMPconst [0] x:(ANDconst [c] y)) yes no) && x.Uses == 1 => (GE (TSTconst [c] y) yes no)` -/
theorem r_ARM64_559_2_sound : BlockRuleL.Sound r_ARM64_559_2 := by arm_tstc

/-- `ARM64.rules:559`: `(GT (CMPconst [0] x:(ANDconst [c] y)) yes no) && x.Uses == 1 => (GT (TSTconst [c] y) yes no)` -/
theorem r_ARM64_559_3_sound : BlockRuleL.Sound r_ARM64_559_3 := by arm_tstc

/-- `ARM64.rules:559`: `(LE (CMPconst [0] x:(ANDconst [c] y)) yes no) && x.Uses == 1 => (LE (TSTconst [c] y) yes no)` -/
theorem r_ARM64_559_4_sound : BlockRuleL.Sound r_ARM64_559_4 := by arm_tstc

/-- `ARM64.rules:559`: `(LT (CMPconst [0] x:(ANDconst [c] y)) yes no) && x.Uses == 1 => (LT (TSTconst [c] y) yes no)` -/
theorem r_ARM64_559_5_sound : BlockRuleL.Sound r_ARM64_559_5 := by arm_tstc

/-- `ARM64.rules:559`: `(NE (CMPconst [0] x:(ANDconst [c] y)) yes no) && x.Uses == 1 => (NE (TSTconst [c] y) yes no)` -/
theorem r_ARM64_559_6_sound : BlockRuleL.Sound r_ARM64_559_6 := by arm_tstc

set_option hygiene false in
/-- `(UGT|ULE (CMPWconst [0] x)) => (NE|EQ (CMPWconst [0] x))`. -/
local macro "arm_ugtw0" hs:term : tactic => `(tactic| (
  arm_bbuild
  rw [imm32_of_zero hc] at hbr
  rw [show Arm64.imm32 (Int64.ofInt 0) = 0 from rfl]
  obtain ⟨r, hr, h⟩ := reg32_of_cmpw0 (Mono.onVal_of (retypeL_cmp1w_ref _ _ _) hbr)
  simp only [Arm64.cmp1w, hr, retypeL_cmpRes, onVal_cmpRes]
  rw [← h, $hs (by decide)]))

/-- `ARM64.rules:604`: `(UGT (CMPWconst [0] x)) => (NE (CMPWconst [0] x))` -/
theorem r_ARM64_604_sound : BlockRuleL.Sound r_ARM64_604 := by arm_ugtw0 hi_sub0

/-- `ARM64.rules:604`: `(ULE (CMPWconst [0] x)) => (EQ (CMPWconst [0] x))` -/
theorem r_ARM64_604_2_sound : BlockRuleL.Sound r_ARM64_604_2 := by arm_ugtw0 ls_sub0

/-- The low word of a 64-bit `AND` with a constant is the `AND` of the low words. -/
theorem setWidth32_and_ofInt (r : BitVec 64) (c : Int) :
    (r &&& BitVec.ofInt 64 c).setWidth 32 = r.setWidth 32 &&& BitVec.ofInt 32 c := by
  rw [BitVec.setWidth_and]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  have h1 : (0:Int) ≤ c % ↑((2:Nat) ^ 64) := Int.emod_nonneg _ (by decide)
  have h2 : (0:Int) ≤ c % ↑((2:Nat) ^ 32) := Int.emod_nonneg _ (by decide)
  have h3 : c % ↑((2:Nat) ^ 64) % ↑((2:Nat) ^ 32) = c % ↑((2:Nat) ^ 32) :=
    Int.emod_emod_of_dvd c (by decide)
  apply Int.ofNat_inj.mp
  rw [Int.natCast_emod, Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2]
  exact h3

set_option hygiene false in
/-- `(K (CMPWconst [0] x:(ANDconst [c] y))) => (K (TSTWconst [int32(c)] y))`. -/
local macro "arm_tstwc" : tactic => `(tactic| (
  arm_bbuild
  have hw : 32 ≤ argWidth (e.ty [0]) := harg
  rw [imm32_of_zero hc] at hbr
  rw [imm32_wrap]
  obtain ⟨r, hr, h⟩ := reg32_of_cmpw0 (Mono.onVal_of (retypeL_cmp1w_ref _ _ _) hbr)
  cases hy : Arm64.reg (e.leaf [0, 0]) with
  | none =>
    simp only [Arm64.op1, hy, retypeL_poison] at hr
    simp [Arm64.reg32, Arm64.reg] at hr
  | some R =>
    simp only [Arm64.op1, hy] at hr
    rcases retypeL_res_w32 hw (R &&& BitVec.ofInt 64 (e.auxInt [0]).toInt) with h' | h' <;>
      rw [h'] at hr
    · simp only [Option.some.injEq] at hr
      subst hr
      simp only [Arm64.flags1w, Arm64.reg32, hy, Option.map_some, retypeL_flags_toVal]
      rw [logic_sub0 (by decide) _ rfl, ← h, setWidth32_and_ofInt]
    · simp [Arm64.reg32, Arm64.reg] at hr))

/-- `ARM64.rules:561`: `(EQ (CMPWconst [0] x:(ANDconst [c] y)) yes no) && x.Uses == 1 => (EQ (TSTWconst [int32(c)] y) yes no)` -/
theorem r_ARM64_561_sound : BlockRuleL.Sound r_ARM64_561 := by arm_tstwc

/-- `ARM64.rules:561`: `(GE (CMPWconst [0] x:(ANDconst [c] y)) yes no) && x.Uses == 1 => (GE (TSTWconst [int32(c)] y) yes no)` -/
theorem r_ARM64_561_2_sound : BlockRuleL.Sound r_ARM64_561_2 := by arm_tstwc

/-- `ARM64.rules:561`: `(GT (CMPWconst [0] x:(ANDconst [c] y)) yes no) && x.Uses == 1 => (GT (TSTWconst [int32(c)] y) yes no)` -/
theorem r_ARM64_561_3_sound : BlockRuleL.Sound r_ARM64_561_3 := by arm_tstwc

/-- `ARM64.rules:561`: `(LE (CMPWconst [0] x:(ANDconst [c] y)) yes no) && x.Uses == 1 => (LE (TSTWconst [int32(c)] y) yes no)` -/
theorem r_ARM64_561_4_sound : BlockRuleL.Sound r_ARM64_561_4 := by arm_tstwc

/-- `ARM64.rules:561`: `(LT (CMPWconst [0] x:(ANDconst [c] y)) yes no) && x.Uses == 1 => (LT (TSTWconst [int32(c)] y) yes no)` -/
theorem r_ARM64_561_5_sound : BlockRuleL.Sound r_ARM64_561_5 := by arm_tstwc

/-- `ARM64.rules:561`: `(NE (CMPWconst [0] x:(ANDconst [c] y)) yes no) && x.Uses == 1 => (NE (TSTWconst [int32(c)] y) yes no)` -/
theorem r_ARM64_561_6_sound : BlockRuleL.Sound r_ARM64_561_6 := by arm_tstwc

/-- `CMPconst [0]` of a 64-bit `AND` and `TST` (either argument order) agree on the conditions
that do not read `C`. -/
theorem tst2_core {c : Cond} (hc : noC c = true) {T0 : Ty} (hw : 64 ≤ argWidth T0) {x y : Val}
    {b : Bool}
    (h1 : c.onVal (Arm64.cmp ((Arm64.op2 T0 (fun x1 x2 => x1 &&& x2) [x, y]).retypeL T0)
      (.int .w64 0)) = some b) :
    c.onVal ((Arm64.flags2 (fun a b => logicFlags (a &&& b)) [x, y]).retypeL Ty.flags) = some b ∧
    c.onVal ((Arm64.flags2 (fun a b => logicFlags (a &&& b)) [y, x]).retypeL Ty.flags) =
      some b := by
  cases hx : Arm64.reg x with
  | none =>
    simp only [Arm64.op2, hx, retypeL_poison, cmp_poison_int0] at h1; cases h1
  | some rx =>
    cases hy : Arm64.reg y with
    | none =>
      simp only [Arm64.op2, hx, hy, retypeL_poison, cmp_poison_int0] at h1; cases h1
    | some ry =>
      simp only [Arm64.op2, hx, hy] at h1
      simp only [Arm64.flags2, hx, hy, retypeL_flags_toVal]
      rcases retypeL_res_wide hw (rx &&& ry) with h | h <;> rw [h] at h1
      · rw [cmp_int0, onVal_cmpRes] at h1
        rw [logic_sub0 (by decide) _ hc, logic_sub0 (by decide) _ hc, BitVec.and_comm ry rx]
        exact ⟨h1, h1⟩
      · rw [cmp_poison_int0] at h1; cases h1

set_option hygiene false in
/-- `(K (CMPconst [0] z:(AND x y))) => (K (TST x y))`, both argument orders of `AND`. -/
local macro "arm_tst2" : tactic => `(tactic| (
  arm_bbuild
  all_goals (
    rw [hc, show BitVec.ofInt 64 0 = 0 from rfl] at hbr
    rw [Arm64.and_of_ne_bool (ne_bool_of_isBoolL harg.2.1.2)] at hbr
    have h1 := tst2_core (by decide) harg.1 (Mono.onVal_of (retypeL_cmp_ref _ _ _) hbr)
    first | exact h1.1 | exact h1.2)))

/-- `ARM64.rules:558`: `(EQ (CMPconst [0] z:(AND x y)) yes no) && z.Uses == 1 => (EQ (TST x y) yes no)` -/
theorem r_ARM64_558_sound : BlockRuleL.Sound r_ARM64_558 := by arm_tst2

/-- `ARM64.rules:558`: `(GE (CMPconst [0] z:(AND x y)) yes no) && z.Uses == 1 => (GE (TST x y) yes no)` -/
theorem r_ARM64_558_2_sound : BlockRuleL.Sound r_ARM64_558_2 := by arm_tst2

/-- `ARM64.rules:558`: `(GT (CMPconst [0] z:(AND x y)) yes no) && z.Uses == 1 => (GT (TST x y) yes no)` -/
theorem r_ARM64_558_3_sound : BlockRuleL.Sound r_ARM64_558_3 := by arm_tst2

/-- `ARM64.rules:558`: `(LE (CMPconst [0] z:(AND x y)) yes no) && z.Uses == 1 => (LE (TST x y) yes no)` -/
theorem r_ARM64_558_4_sound : BlockRuleL.Sound r_ARM64_558_4 := by arm_tst2

/-- `ARM64.rules:558`: `(LT (CMPconst [0] z:(AND x y)) yes no) && z.Uses == 1 => (LT (TST x y) yes no)` -/
theorem r_ARM64_558_5_sound : BlockRuleL.Sound r_ARM64_558_5 := by arm_tst2

/-- `ARM64.rules:558`: `(NE (CMPconst [0] z:(AND x y)) yes no) && z.Uses == 1 => (NE (TST x y) yes no)` -/
theorem r_ARM64_558_6_sound : BlockRuleL.Sound r_ARM64_558_6 := by arm_tst2

/-- `CMPWconst [0]` of an `AND` and `TSTW` (either argument order) agree on the conditions that
do not read `C`. -/
theorem tstw2_core {c : Cond} (hc : noC c = true) {T0 : Ty} (hw : 32 ≤ argWidth T0) {x y : Val}
    {b : Bool}
    (h1 : c.onVal (Arm64.cmp1w (fun r => Arm64.subFlags r 0)
      [(Arm64.op2 T0 (fun x1 x2 => x1 &&& x2) [x, y]).retypeL T0]) = some b) :
    c.onVal ((Arm64.flags2w (fun a b => logicFlags (a &&& b)) [x, y]).retypeL Ty.flags) = some b ∧
    c.onVal ((Arm64.flags2w (fun a b => logicFlags (a &&& b)) [y, x]).retypeL Ty.flags) =
      some b := by
  obtain ⟨r, hr, h⟩ := reg32_of_cmpw0 h1
  cases hx : Arm64.reg x with
  | none => simp only [Arm64.op2, hx, retypeL_poison] at hr; cases hr
  | some rx =>
    cases hy : Arm64.reg y with
    | none => simp only [Arm64.op2, hx, hy, retypeL_poison] at hr; cases hr
    | some ry =>
      simp only [Arm64.op2, hx, hy] at hr
      rcases retypeL_res_w32 hw (rx &&& ry) with h' | h' <;> rw [h'] at hr
      · simp only [Option.some.injEq] at hr
        subst hr
        simp only [Arm64.flags2w, Arm64.reg32, hx, hy, Option.map_some, retypeL_flags_toVal]
        rw [logic_sub0 (by decide) _ hc, logic_sub0 (by decide) _ hc, ← BitVec.setWidth_and,
          ← BitVec.setWidth_and, BitVec.and_comm ry rx]
        exact ⟨h, h⟩
      · cases hr

set_option hygiene false in
/-- `(K (CMPWconst [0] z:(AND x y))) => (K (TSTW x y))`, both argument orders of `AND`. -/
local macro "arm_tstw2" : tactic => `(tactic| (
  arm_bbuild
  all_goals (
    rw [imm32_of_zero hc] at hbr
    rw [Arm64.and_of_ne_bool (ne_bool_of_isBoolL harg.2.1.2)] at hbr
    have h1 := tstw2_core (by decide) harg.1 (Mono.onVal_of (retypeL_cmp1w_ref _ _ _) hbr)
    first | exact h1.1 | exact h1.2)))

/-- `ARM64.rules:560`: `(EQ (CMPWconst [0] z:(AND x y)) yes no) && z.Uses == 1 => (EQ (TSTW x y) yes no)` -/
theorem r_ARM64_560_sound : BlockRuleL.Sound r_ARM64_560 := by arm_tstw2

/-- `ARM64.rules:560`: `(GE (CMPWconst [0] z:(AND x y)) yes no) && z.Uses == 1 => (GE (TSTW x y) yes no)` -/
theorem r_ARM64_560_2_sound : BlockRuleL.Sound r_ARM64_560_2 := by arm_tstw2

/-- `ARM64.rules:560`: `(GT (CMPWconst [0] z:(AND x y)) yes no) && z.Uses == 1 => (GT (TSTW x y) yes no)` -/
theorem r_ARM64_560_3_sound : BlockRuleL.Sound r_ARM64_560_3 := by arm_tstw2

/-- `ARM64.rules:560`: `(LE (CMPWconst [0] z:(AND x y)) yes no) && z.Uses == 1 => (LE (TSTW x y) yes no)` -/
theorem r_ARM64_560_4_sound : BlockRuleL.Sound r_ARM64_560_4 := by arm_tstw2

/-- `ARM64.rules:560`: `(LT (CMPWconst [0] z:(AND x y)) yes no) && z.Uses == 1 => (LT (TSTW x y) yes no)` -/
theorem r_ARM64_560_5_sound : BlockRuleL.Sound r_ARM64_560_5 := by arm_tstw2

/-- `ARM64.rules:560`: `(NE (CMPWconst [0] z:(AND x y)) yes no) && z.Uses == 1 => (NE (TSTW x y) yes no)` -/
theorem r_ARM64_560_6_sound : BlockRuleL.Sound r_ARM64_560_6 := by arm_tstw2

/-- `ARM64.rules:478`: `(JumpTable idx) => (JUMPTABLE {makeJumpTableSym(b)} idx (MOVDaddr
<typ.Uintptr> {makeJumpTableSym(b)} (SB)))`, a rule on a `JumpTable`, whose events the validator
checks by their effect (`GoFV.Opt.LowerCheck.jumpOKL`). -/
theorem r_ARM64_478_sound : BlockRuleL.Checked r_ARM64_478 := .inr rfl

end GoFV.Proof.Low.Rules

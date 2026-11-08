import GoFV.Proof.Low.Rules.Tactic
import GoFV.Rules.Derive
import GoFV.Rules.Generated.ARM64

variable [GoFV.SSA.Sem.Addrs]

/-!
# Lowering rule lemmas: `CondSelect` (`ARM64.rules:302`, `303`)

`(CondSelect x y boolval) && flagArg(boolval) != nil => (CSEL [boolval.Op] x y flagArg(boolval))`
in its derived form (`GoFV.Rules.Derive.flagSplit`): one rule `(CondSelect x y boolval:(cc f)) =>
(CSEL [cc] x y f)` per condition op `cc` (`condOps`). The boolean `cc f` is the condition `cc` of
the flags `f` (`Arm64.cset`), which `CSEL [cc]` decides alike (`Cond.ofAux` of `cc`'s Go opcode
number); the selected arm moves as its register (`regVal`), which a word or integer shape
(`topOKL`) reads back as the arm's own reading (`retypeL_regVal`: `Arm64.reg` zero-extends a
narrow integer, `retypeL` keeps its low bits).

`(CondSelect x y boolval) && flagArg(boolval) == nil => (CSEL [OpARM64NotEqual] x y (TSTWconst
[1] boolval))` (`303`) is listed as it is: its result reads no field of `boolval`, and the
obligation holds without its condition (`refines_condSel_tstw`), which the validator's oracle
answers.
-/

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low
open GoFV.Rules.Generated.ARM64 GoFV.Rules.Derive

/-- A register value moved unchanged (`regVal`) and read at a word or integer shape is the value
read at that shape. -/
theorem retypeL_regVal {T : Ty} (hT : (∃ w, T = .int w) ∨ ∃ e, T = .ptr e) (X : Val) :
    Refines (X.retypeL T) ((Arm64.regVal T X).retypeL T) := by
  rcases hT with ⟨⟨⟩, rfl⟩ | ⟨el, rfl⟩
  all_goals
    cases X with
    | ptr p => exact Refines.refl _
    | int w x =>
      cases w <;> simp [Arm64.regVal, Arm64.reg, Arm64.res, Val.retypeL, Val.widen, Val.retype,
        Width.bits, BitVec.setWidth_setWidth_of_le] <;> exact Refines.refl _
    | bool b =>
      cases b <;>
        simp [Arm64.regVal, Arm64.reg, Arm64.res, Val.retypeL, Val.widen, Val.retype, Width.bits] <;>
        exact Refines.refl _
    | _ => simp [Arm64.regVal, Arm64.reg, Val.retypeL, Val.widen, Val.retype]; exact .poison _

/-- A `CSET` result read as a boolean at any shape is the condition (or not a boolean). -/
theorem asBool_cset {Tc : Ty} {b b' : Bool}
    (h : ((Arm64.res Tc (if b then 1 else 0)).retypeL Tc).asBool = some b') : b' = b := by
  cases Tc with
  | int w =>
    cases w <;> cases b <;>
      simp_all [Arm64.res, Val.retypeL, Val.widen, Val.retype, Val.asBool, Width.bits]
  | _ => cases b <;> simp_all [Arm64.res, Val.retypeL, Val.widen, Val.retype, Val.asBool]

/-- **`CondSelect x y (cc f)` as `CSEL [cc] x y f`** at a word or integer shape: both select by
the condition of `cc` on `f` (`CSEL`'s auxint is `cc`'s Go opcode number, `hk`). -/
theorem refines_condSel_csel {T : Ty} (hT : (∃ w, T = .int w) ∨ ∃ e, T = .ptr e) {cc : Op}
    (hk : Cond.ofAux (Int64.ofNat cc.goNum) = Cond.ofOp cc) (Tc : Ty) (X Y F : Val) :
    Refines (Val.retypeL T
      ((Val.retypeL Tc (Arm64.cset Tc cc [F])).asBool.elim Val.poison fun b => bif b then X else Y))
      (Val.retypeL T (Arm64.csel T (Int64.ofNat cc.goNum) none [X, Y, F])) := by
  simp only [Arm64.cset, Arm64.csel, Arm64.condOn, hk]
  rcases h : (Cond.ofOp cc).bind (·.onVal F) with _ | b
  · simp only [retypeL_poison, Val.asBool, Option.elim]; exact .poison _
  · simp only
    rcases hs : (Val.retypeL Tc (Arm64.res Tc (if b = true then 1 else 0))).asBool with _ | b'
    · simp only [Option.elim, retypeL_poison]; exact .poison _
    · obtain rfl := asBool_cset hs
      cases b'
      · exact retypeL_regVal hT Y
      · exact retypeL_regVal hT X

/-- `flagSplit r_ARM64_302` on the condition op `cc`. -/
def r302 (cc : Op) : Rule where
  loc := ⟨"ARM64", 302⟩
  op := .CondSelect
  vars := [⟨"x", .value, (.named "*Value")⟩, ⟨"y", .value, (.named "*Value")⟩,
    ⟨"boolval", .value, (.named "*Value")⟩, ⟨"flagArg", .value, .named "*Value"⟩]
  pat := .op .CondSelect none .any .any .any .fixed
    [.bind 0, .bind 1, .op cc (some 2) .any .any .any .fixed [.bind 3] false] false
  cond := none
  block := none
  result := .build
      [{ op := .ARM64CSEL, ty := none, auxInt := some (.op cc), aux := none,
         args := [.var 0, .var 1, .var 3] }]
  pos := []

theorem flagSplit_302 : flagSplit r_ARM64_302 = condOps.map r302 := by rfl

set_option maxRecDepth 100000 in
/-- `ARM64.rules:302`: `(CondSelect x y boolval) && flagArg(boolval) != nil => (CSEL [boolval.Op] x y flagArg(boolval))`, split by the condition op (`flagSplit`) -/
theorem r_ARM64_302_flag_sound : ForallL ArmRule.Checked (flagSplit r_ARM64_302) := by
  rw [flagSplit_302]
  simp only [condOps, List.map_cons, List.map_nil, ForallL]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  all_goals
    left
    arm_unfold
    all_goals arm_shape
    all_goals arm_norm
    all_goals first
      | exact refines_condSel_csel (.inl ⟨_, rfl⟩) (by rfl) _ _ _ _
      | exact refines_condSel_csel (.inr ⟨_, rfl⟩) (by rfl) _ _ _ _

set_option maxRecDepth 100000 in
/-- **`CondSelect x y b` as `CSEL [NotEqual] x y (TSTWconst [1] b)`** at a word or integer
shape: a boolean `b` is the register 1 or 0, whose low bit `TSTWconst [1]` tests (`Z` clear iff
`b`), and `NotEqual` selects `x` exactly when `Z` is clear; any other `b` makes the source
`poison`. -/
theorem refines_condSel_tstw {T : Ty} (hT : (∃ w, T = .int w) ∨ ∃ e, T = .ptr e) (B X Y : Val) :
    Refines (Val.retypeL T (B.asBool.elim Val.poison fun b => bif b then X else Y))
      (Val.retypeL T (Arm64.csel T (Int64.ofNat Op.ARM64NotEqual.goNum) none
        [X, Y, Val.retypeL Ty.flags
          (Arm64.flags1w (fun x => logicFlags (x &&& Arm64.imm32 (Int64.ofInt 1))) [B])])) := by
  have hk : Cond.ofAux (Int64.ofNat Op.ARM64NotEqual.goNum) = Cond.ofOp .ARM64NotEqual := rfl
  cases B with
  | bool b =>
    cases b
    all_goals
      simp [Arm64.csel, Arm64.condOn, hk, Arm64.flags1w, Val.asBool]
      split
      all_goals first
        | exact retypeL_regVal hT _
        | (rename_i h; exact absurd h (by decide))
  | _ => simp [Val.asBool, retypeL_poison]; exact .poison _

set_option maxRecDepth 100000 in
/-- `ARM64.rules:303`: `(CondSelect x y boolval) && flagArg(boolval) == nil => (CSEL [OpARM64NotEqual] x y (TSTWconst [1] boolval))` -/
theorem r_ARM64_303_sound : ArmRule.Checked r_ARM64_303 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals first
    | exact refines_condSel_tstw (.inl ⟨_, rfl⟩) _ _ _
    | exact refines_condSel_tstw (.inr ⟨_, rfl⟩) _ _ _

end GoFV.Proof.Low.Rules

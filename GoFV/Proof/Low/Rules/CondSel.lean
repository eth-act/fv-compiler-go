import GoFV.Proof.Low.Rules.Tactic
import GoFV.Rules.Derive
import GoFV.Rules.Generated.ARM64

/-!
# Lowering rule lemma: `CondSelect` on a condition (`ARM64.rules:302`)

`(CondSelect x y boolval) && flagArg(boolval) != nil => (CSEL [boolval.Op] x y flagArg(boolval))`
in its derived form (`GoFV.Rules.Derive.flagSplit`): one rule `(CondSelect x y boolval:(cc f)) =>
(CSEL [cc] x y f)` per condition op `cc` (`condOps`). The boolean `cc f` is the condition `cc` of
the flags `f` (`Arm64.cset`), which `CSEL [cc]` decides alike (`Cond.ofAux` of `cc`'s Go opcode
number); the selected arm moves as its register (`regVal`), which a word shape (`topOKL`) reads
back whole (`retypeL_regVal_word`).
-/

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low
open GoFV.Rules.Generated.ARM64 GoFV.Rules.Derive

/-- A register value moved unchanged (`regVal`) and read at a word shape is the value read at
that shape. -/
theorem retypeL_regVal_word {T : Ty} (hT : T = .int .w64 ∨ ∃ e, T = .ptr e) (X : Val) :
    Refines (X.retypeL T) ((Arm64.regVal T X).retypeL T) := by
  rcases hT with rfl | ⟨el, rfl⟩
  all_goals
    cases X with
    | ptr p => exact Refines.refl _
    | int w x =>
      cases w <;> simp [Arm64.regVal, Arm64.reg, Arm64.res, Val.retypeL, Val.widen, Val.retype,
        Width.bits] <;> exact Refines.refl _
    | bool b =>
      simp [Arm64.regVal, Arm64.reg, Arm64.res, Val.retypeL, Val.widen, Val.retype, Width.bits]
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

/-- **`CondSelect x y (cc f)` as `CSEL [cc] x y f`** at a word shape: both select by the condition
of `cc` on `f` (`CSEL`'s auxint is `cc`'s Go opcode number, `hk`). -/
theorem refines_condSel_csel {T : Ty} (hT : T = .int .w64 ∨ ∃ e, T = .ptr e) {cc : Op}
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
      · exact retypeL_regVal_word hT Y
      · exact retypeL_regVal_word hT X

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
      | exact refines_condSel_csel (.inl rfl) (by rfl) _ _ _ _
      | exact refines_condSel_csel (.inr ⟨_, rfl⟩) (by rfl) _ _ _ _

end GoFV.Proof.Low.Rules

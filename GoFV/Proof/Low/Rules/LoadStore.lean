import GoFV.Proof.Low.Rules.Tactic
import GoFV.Proof.Low.SimMem
import GoFV.Rules.Generated.ARM64

/-!
# Lowering rule lemmas: frame addresses, scalar loads and scalar stores (`ARM64.rules:309-310`,
`313-322`, `326-331`)

`(Load <t> ptr mem) && … => (MOV{B,BU,H,HU,W,WU,D}load ptr mem)` and `FMOV{S,D}load`: the scalar
loads are lowered terms (`termVL`, `opValL`'s `ldVal`; a float load reads as `MOVWUload` or
`MOVDload`, a float shape being the integer shape of its size), and at offset 0 without aux
`ldVal` is `Sim.ldRes`, so the rules are `Sim.ld_ref` at a shape the load's size fits. Go's
conditions (`t.IsBoolean()`, `is8BitInt(t)`, …, `is64BitInt(t) || isPtr(t)`, `is32BitFloat(t)`,
`is64BitFloat(t)`) are oracle atoms of the rule denotation; the size fit is the validator's
instance check `resFitsL` (the obligation's `hfit`). The signedness (`t.IsSigned()`) does not
matter: `retypeL` at the narrow shape cuts the extension.

`(Store {t} ptr val mem) && t.Size() == n … => (MOV{B,H,W,D}store ptr val mem)` and
`FMOV{S,D}store`: stores are atoms, the validator pairs each lowered store with the `Store` it
lowers (`memLower`, `Sim.store_lower_eval`), so these rules are `ArmRule.Mem` (`checked_store`).

`(LocalAddr {sym} base mem) => (MOVDaddr {sym} (SPanchored base mem))` and `(MOVDaddr {sym}
base)`: frame addresses are atoms, the validator pairs each `MOVDaddr` with the `LocalAddr` it
lowers (`addrLower`, `addr_lower_eval`: the frame variable's address, whatever the argument), so
these rules are `ArmRule.Mem` (`checked_localAddr`).

Not covered: `FMOVQload` (323), a 128-bit load term (`ldQ?`, not `ldOp?`); `FMOVQstore` (332)
stores a 16-byte shape `memLower` does not pair.
-/

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low
open GoFV.Rules.Generated.ARM64

theorem fitsB_loadFits {ty : Ty} {n : Nat} (h : fitsB ty n = true) : Sim.LoadFits ty n := by
  unfold fitsB at h
  split at h <;> simp only [beq_iff_eq, Bool.false_eq_true] at h
  · exact .inl ⟨rfl, h⟩
  · exact .inr (.inl ⟨_, rfl, h⟩)
  · exact .inr (.inr ⟨_, rfl, h⟩)

/-- `opValL` of a generic `Load`: `loadOp`. -/
theorem opValL_load (tabs : Tables) (ty : Ty) (ai : Int64) (ax : Option AuxRef) (args : List Val) :
    opValL tabs .Load ty ai ax args = loadOp ty args := by
  simp only [opValL, show Op.Load.generic = true by decide, ite_true,
    GoFV.Proof.Rules.opVal_pure (op := .Load) (by decide)]
  rfl

/-- An integer load at offset 0 without aux: `Sim.ldRes`. -/
theorem ldVal_zero (tabs : Tables) (n : Nat) (s : Bool) (ty : Ty) (args : List Val) :
    ldVal tabs n s ty 0 none args = Sim.ldRes ty n s args := by
  rcases args with _ | ⟨a, _ | ⟨x, _ | ⟨y, l⟩⟩⟩
  · rfl
  · rfl
  · cases x <;> rfl
  · cases x <;> rfl

/-- **`Load` as an integer load** of a size the shape fits. -/
theorem refines_ld {o : Op} {n : Nat} {s : Bool} (hl : ldOp? o = some (n, s))
    (hg : o.generic = false) (hm : (o == .ARM64MOVDaddr) = false) {T : Ty}
    (hfit : fitsB T n = true) (tabs : Tables) (ai : Int64) (ax : Option AuxRef)
    (args : List Val) :
    Sem.Refines ((opValL tabs .Load T ai ax args).retypeL T)
      ((opValL tabs o T 0 none args).retypeL T) := by
  rw [opValL_load, opValL_ld hg hm hl, ldVal_zero]
  exact Sim.ld_ref (fitsB_loadFits hfit) s args

/-- `ARM64.rules:309`: `(LocalAddr <t> {sym} base mem) && t.Elem().HasPointers() => (MOVDaddr {sym} (SPanchored base mem))` -/
theorem r_ARM64_309_sound : ArmRule.Checked r_ARM64_309 := checked_localAddr rfl

/-- `ARM64.rules:310`: `(LocalAddr <t> {sym} base _) && !t.Elem().HasPointers() => (MOVDaddr {sym} base)` -/
theorem r_ARM64_310_sound : ArmRule.Checked r_ARM64_310 := checked_localAddr rfl

/-- `ARM64.rules:313`: `(Load <t> ptr mem) && t.IsBoolean() => (MOVBUload ptr mem)` -/
theorem r_ARM64_313_sound : ArmRule.Checked r_ARM64_313 := by
  left
  arm_unfold
  simp only [resFitsL, ldOp?] at hfit
  exact refines_ld rfl rfl rfl hfit _ _ _ _

/-- `ARM64.rules:314`: `(Load <t> ptr mem) && (is8BitInt(t) && t.IsSigned()) => (MOVBload ptr mem)` -/
theorem r_ARM64_314_sound : ArmRule.Checked r_ARM64_314 := by
  left
  arm_unfold
  simp only [resFitsL, ldOp?] at hfit
  exact refines_ld rfl rfl rfl hfit _ _ _ _

/-- `ARM64.rules:315`: `(Load <t> ptr mem) && (is8BitInt(t) && !t.IsSigned()) => (MOVBUload ptr mem)` -/
theorem r_ARM64_315_sound : ArmRule.Checked r_ARM64_315 := by
  left
  arm_unfold
  simp only [resFitsL, ldOp?] at hfit
  exact refines_ld rfl rfl rfl hfit _ _ _ _

/-- `ARM64.rules:316`: `(Load <t> ptr mem) && (is16BitInt(t) && t.IsSigned()) => (MOVHload ptr mem)` -/
theorem r_ARM64_316_sound : ArmRule.Checked r_ARM64_316 := by
  left
  arm_unfold
  simp only [resFitsL, ldOp?] at hfit
  exact refines_ld rfl rfl rfl hfit _ _ _ _

/-- `ARM64.rules:317`: `(Load <t> ptr mem) && (is16BitInt(t) && !t.IsSigned()) => (MOVHUload ptr mem)` -/
theorem r_ARM64_317_sound : ArmRule.Checked r_ARM64_317 := by
  left
  arm_unfold
  simp only [resFitsL, ldOp?] at hfit
  exact refines_ld rfl rfl rfl hfit _ _ _ _

/-- `ARM64.rules:318`: `(Load <t> ptr mem) && (is32BitInt(t) && t.IsSigned()) => (MOVWload ptr mem)` -/
theorem r_ARM64_318_sound : ArmRule.Checked r_ARM64_318 := by
  left
  arm_unfold
  simp only [resFitsL, ldOp?] at hfit
  exact refines_ld rfl rfl rfl hfit _ _ _ _

/-- `ARM64.rules:319`: `(Load <t> ptr mem) && (is32BitInt(t) && !t.IsSigned()) => (MOVWUload ptr mem)` -/
theorem r_ARM64_319_sound : ArmRule.Checked r_ARM64_319 := by
  left
  arm_unfold
  simp only [resFitsL, ldOp?] at hfit
  exact refines_ld rfl rfl rfl hfit _ _ _ _

/-- `ARM64.rules:320`: `(Load <t> ptr mem) && (is64BitInt(t) || isPtr(t)) => (MOVDload ptr mem)` -/
theorem r_ARM64_320_sound : ArmRule.Checked r_ARM64_320 := by
  left
  arm_unfold
  simp only [resFitsL, ldOp?] at hfit
  exact refines_ld rfl rfl rfl hfit _ _ _ _

/-- `ARM64.rules:321`: `(Load <t> ptr mem) && is32BitFloat(t) => (FMOVSload ptr mem)` -/
theorem r_ARM64_321_sound : ArmRule.Checked r_ARM64_321 := by
  left
  arm_unfold
  simp only [resFitsL, ldOp?] at hfit
  exact refines_ld rfl rfl rfl hfit _ _ _ _

/-- `ARM64.rules:322`: `(Load <t> ptr mem) && is64BitFloat(t) => (FMOVDload ptr mem)` -/
theorem r_ARM64_322_sound : ArmRule.Checked r_ARM64_322 := by
  left
  arm_unfold
  simp only [resFitsL, ldOp?] at hfit
  exact refines_ld rfl rfl rfl hfit _ _ _ _

/-- `ARM64.rules:326`: `(Store {t} ptr val mem) && t.Size() == 1 => (MOVBstore ptr val mem)` -/
theorem r_ARM64_326_sound : ArmRule.Checked r_ARM64_326 := checked_store rfl

/-- `ARM64.rules:327`: `(Store {t} ptr val mem) && t.Size() == 2 => (MOVHstore ptr val mem)` -/
theorem r_ARM64_327_sound : ArmRule.Checked r_ARM64_327 := checked_store rfl

/-- `ARM64.rules:328`: `(Store {t} ptr val mem) && t.Size() == 4 && !t.IsFloat() => (MOVWstore ptr val mem)` -/
theorem r_ARM64_328_sound : ArmRule.Checked r_ARM64_328 := checked_store rfl

/-- `ARM64.rules:329`: `(Store {t} ptr val mem) && t.Size() == 8 && !t.IsFloat() => (MOVDstore ptr val mem)` -/
theorem r_ARM64_329_sound : ArmRule.Checked r_ARM64_329 := checked_store rfl

/-- `ARM64.rules:330`: `(Store {t} ptr val mem) && t.Size() == 4 &&  t.IsFloat() => (FMOVSstore ptr val mem)` -/
theorem r_ARM64_330_sound : ArmRule.Checked r_ARM64_330 := checked_store rfl

/-- `ARM64.rules:331`: `(Store {t} ptr val mem) && t.Size() == 8 &&  t.IsFloat() => (FMOVDstore ptr val mem)` -/
theorem r_ARM64_331_sound : ArmRule.Checked r_ARM64_331 := checked_store rfl

end GoFV.Proof.Low.Rules

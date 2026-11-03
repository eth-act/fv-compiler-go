import GoFV.Proof.Pass.NilLateL
import GoFV.Proof.Witness.DeadcodeL

/-!
# Non-vacuity witness: late nilcheck under `runSched`

`ncL`: lowered, scheduled `func(x, lo, hi int) int { return *(*int)(unsafe.Pointer(x)) }` on the
tables of lowered `clamp` (`GoFV.Proof.Witness.ClampL`), one block:

```
b1: v12 = LoweredNilCheck v8 v1; v13 = MOVDload [0] v8 v1; Ret (MakeResult v13 v1)
```

`late nilcheck` removes `v12` (the load faults on a nil `x`), `nilLateB` accepts, and `ncL`
passes `check` (all by kernel evaluation). With `x = 0`, `runSched` of `ncL` panics with
`nilDeref` at the check; `nilcheckelim2_refinesSched` gives a `runSched` of the output that
panics with `nilDeref` too, now at the load (`nilLateL_witness`).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.NilLate GoFV.Proof GoFV.Proof.NilLateL

/-- The values of `ncL`, by ID. -/
def ncLValues : Array (Option Value) :=
  let t := Array.replicate 25 (none : Option Value)
  let t := t.set! 1 (some (mkV 1 .InitMem 28 none p0 3 #[] 1))
  let t := t.set! 8 (some (mkVI 8 .ArgIntReg 2 0 (some 7) (pos 2 22 7 0) 2 #[] 1))
  let t := t.set! 9 (some (mkVI 9 .ArgIntReg 2 1 (some 8) (pos 2 22 7 0) 0 #[] 1))
  let t := t.set! 10 (some (mkVI 10 .ArgIntReg 2 2 (some 9) (pos 2 22 7 0) 0 #[] 1))
  let t := t.set! 12 (some (mkVI 12 .ARM64LoweredNilCheck 30 0 none (pos 2 23 3 1) 0 #[8, 1] 1))
  let t := t.set! 13 (some (mkVI 13 .ARM64MOVDload 2 0 none (pos 2 23 3 1) 1 #[8, 1] 1))
  t.set! 15 (some (mkV 15 .MakeResult 33 none (pos 2 23 3 1) 1 #[13, 1] 1))

/-- The blocks of `ncL`, by ID. -/
def ncLBlocks : Array (Option Block) := #[none,
  some (mkB 1 .Ret (pos 2 23 3 1) #[15] #[] #[] #[1, 8, 9, 10, 12, 13, 15])]

/-- A lowered, scheduled load through `x` after a nil check of `x`. -/
def ncL : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 24
  bidLast := 1
  blocks := #[1]
  blockTab := ncLBlocks
  valueTab := ncLValues
  names := #[(1, #[8]), (2, #[9]), (3, #[10])]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := [24, 23, 22, 21, 20, 19, 18, 17, 16, 14, 11, 7, 6, 5, 4, 3, 2]
  freeBlocks := []
  cache := { lineStarts := some #[⟨2, none, #[]⟩] }

/-- A pass environment for `ncL`. -/
def ncLPassEnv : PassEnv where
  passName := "late nilcheck"
  pkg := GoStr.ofString "main"
  funcName := GoStr.ofString "clamp"
  abi := 1
  nosplit := false
  pgohot := false
  config := #[]
  typs := #[("Mem", 28), ("Flags", 29), ("Void", 30)]
  typeOrder := default
  tables := clampLTabs

/-- `runSched` panics with `nilDeref`. -/
def panicsNil : Outcome → Bool
  | .panicked .nilDeref _ => true
  | _ => false

theorem ncL_facts :
    (check clampLCheckEnv ncL).toBool = true ∧ ncL.lowered = true ∧
    panicsNil (runSched Env.p1 clampLTabs ncL (clampArgs 0) {} 2) = true ∧
    ((nilcheckelim2 ncLPassEnv ncL).toOption.map fun g =>
      nilLateB clampLTabs ncL g && (g.value? 12).isNone && (ncL.value? 12).isSome) = some true := by
  decide +kernel

private theorem check_ok_of_toBool' {ce : CheckEnv} {f : Func} (h : (check ce f).toBool = true) :
    check ce f = .ok () := by
  revert h; cases check ce f <;> simp [Except.toBool]

/-- **`nilcheckelim2_refinesSched` is not vacuous**: `late nilcheck` removes `ncL`'s nil check,
`nilLateB` accepts, and where `ncL` panics with `nilDeref` under `runSched` (`x = 0`), so does
the output. -/
theorem nilLateL_witness :
    ∃ out, nilcheckelim2Pass ncLPassEnv ncL = .ok out ∧ out.func.value? 12 = none ∧
      (ncL.value? 12).isSome ∧
      ∃ fuel m, runSched Env.p1 out.tables out.func (clampArgs 0) {} fuel = .panicked .nilDeref m := by
  obtain ⟨h1, -, h3, h4⟩ := ncL_facts
  cases hc : nilcheckelim2 ncLPassEnv ncL with
  | error e => rw [hc] at h4; cases h4
  | ok g =>
    rw [hc] at h4
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Bool.and_eq_true,
      Option.isNone_iff_eq_none] at h4
    obtain ⟨⟨hv, hg12⟩, hf12⟩ := h4
    have hp : nilcheckelim2Pass ncLPassEnv ncL = .ok { func := g, tables := clampLTabs } := by
      simp only [nilcheckelim2Pass, Pass.ofFunc]
      rw [hc]; rfl
    refine ⟨_, hp, hg12, hf12, ?_⟩
    have hr : RefinesSched clampLTabs g clampLTabs ncL :=
      nilcheckelim2_refinesSched hp (check_ok_of_toBool' h1) hv
    cases hs : runSched Env.p1 clampLTabs ncL (clampArgs 0) {} 2 with
    | panicked e m =>
      rw [hs] at h3
      cases e <;> simp [panicsNil] at h3
      obtain ⟨fuel, ho⟩ := hr Env.p1 (clampArgs 0) {} 2 (by rw [hs]; trivial)
      rw [hs] at ho
      refine ⟨fuel, ?_⟩
      show ∃ m, runSched Env.p1 clampLTabs g (clampArgs 0) {} fuel = .panicked .nilDeref m
      revert ho
      generalize runSched Env.p1 clampLTabs g (clampArgs 0) {} fuel = o
      intro ho
      cases ho with
      | panicked _ _ => exact ⟨_, rfl⟩
    | returned _ _ => rw [hs] at h3; simp [panicsNil] at h3
    | stuck _ => rw [hs] at h3; simp [panicsNil] at h3
    | outOfFuel => rw [hs] at h3; simp [panicsNil] at h3

end GoFV.Proof.Witness

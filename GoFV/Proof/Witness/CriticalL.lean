import GoFV.Proof.Pass.CriticalL
import GoFV.Proof.Witness.DeadcodeL

/-!
# Non-vacuity witness: critical on lowered code

`maxL`: lowered `clamp` (`GoFV.Proof.Witness.ClampL`) cut down to `max(x, lo)` with a `Phi`:

```
b1: ARM64GT (CMP lo x) -> b3 b2     b2: Plain -> b3
b3: v11 = Phi lo x; Ret v11         (x, lo, hi: ArgIntReg)
```

The edge `b1 → b3` is critical (`b1` has two successors, `b3` two predecessors, `b1` is not
`Plain`). `critical` splits it through a new empty `Plain` block `b4`; `critRelB` accepts the
output, both pass `check` and are lowered, and the output returns `max(5, 0) = 5` and
`max(-3, 0) = 0` (through `b4`) under `runL` (all by kernel evaluation). `critical_refinesL`
applies (`criticalL_witness`).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof GoFV.Proof.Crit

/-- The values of `maxL`, by ID. -/
def maxLValues : Array (Option Value) :=
  let t := Array.replicate 25 (none : Option Value)
  let t := t.set! 1 (some (mkV 1 .InitMem 28 none p0 1 #[] 1))
  let t := t.set! 8 (some (mkVI 8 .ArgIntReg 2 0 (some 7) (pos 2 22 7 0) 2 #[] 1))
  let t := t.set! 9 (some (mkVI 9 .ArgIntReg 2 1 (some 8) (pos 2 22 7 0) 2 #[] 1))
  let t := t.set! 10 (some (mkVI 10 .ArgIntReg 2 2 (some 9) (pos 2 22 7 0) 0 #[] 1))
  let t := t.set! 22 (some (mkV 22 .ARM64CMP 29 none (pos 2 22 7 1) 1 #[9, 8] 1))
  let t := t.set! 11 (some (mkV 11 .Phi 2 none (pos 2 23 3 1) 1 #[9, 8] 3))
  t.set! 15 (some (mkV 15 .MakeResult 33 none (pos 2 23 3 1) 1 #[11, 1] 3))

/-- The blocks of `maxL`, by ID. -/
def maxLBlocks : Array (Option Block) := #[none,
  some (mkB 1 .ARM64GT (pos 2 22 7 0) #[22] #[⟨3, 0⟩, ⟨2, 0⟩] #[] #[1, 8, 9, 10, 22]),
  some (mkB 2 .Plain (pos 2 25 7 0) #[] #[⟨3, 1⟩] #[⟨1, 1⟩] #[]),
  some (mkB 3 .Ret (pos 2 23 3 1) #[15] #[] #[⟨1, 0⟩, ⟨2, 0⟩] #[11, 15])]

/-- `max(x, lo)`, lowered, with a critical edge `b1 → b3`. -/
def maxL : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 24
  bidLast := 3
  blocks := #[1, 2, 3]
  blockTab := maxLBlocks
  valueTab := maxLValues
  names := #[(1, #[8]), (2, #[9]), (3, #[10])]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := [18, 13, 12, 23, 19, 20, 17, 16, 14, 24, 21, 7, 6, 5, 4, 3, 2]
  freeBlocks := []
  cache := { postorder := some #[3, 2, 1] }

/-- A pass environment for `maxL`. -/
def maxLPassEnv : PassEnv := { deadLPassEnv with passName := "critical" }

theorem maxL_facts :
    (check clampLCheckEnv maxL).toBool = true ∧ maxL.lowered = true ∧
    returnsInt (runL Env.p1 clampLTabs maxL (clampArgs 5) {} 3) 5 = true ∧
    returnsInt (runL Env.p1 clampLTabs maxL (clampArgs (-3)) {} 3) 0 = true ∧
    ((critical maxL).toOption.map fun g =>
      critRelB maxL g && (check clampLCheckEnv g).toBool && g.lowered &&
        decide (maxL.blocks.size < g.blocks.size) &&
        returnsInt (runL Env.p1 clampLTabs g (clampArgs 5) {} 3) 5 &&
        returnsInt (runL Env.p1 clampLTabs g (clampArgs (-3)) {} 3) 0) = some true := by
  decide +kernel

private theorem check_ok_of_toBool' {ce : CheckEnv} {f : Func} (h : (check ce f).toBool = true) :
    check ce f = .ok () := by
  revert h; cases check ce f <;> simp [Except.toBool]

/-- **`critical_refinesL` is not vacuous**: `critical` splits `maxL`'s critical edge (one more
block), `critRelB` accepts the output, which passes `check`, and by `critical_refinesL` returns
`max(-3, 0) = 0` under `runL` (through the splitter), as `maxL` does. -/
theorem criticalL_witness :
    ∃ out, criticalPass maxLPassEnv maxL = .ok out ∧ critRelB maxL out.func = true ∧
      check clampLCheckEnv out.func = .ok () ∧ maxL.blocks.size < out.func.blocks.size ∧
      ∃ fuel m, runL Env.p1 out.tables out.func (clampArgs (-3)) {} fuel = .returned [.i64 0] m := by
  obtain ⟨h1, -, -, h4, h5⟩ := maxL_facts
  obtain ⟨m, hm⟩ := returnsInt_iff.1 h4
  cases hc : critical maxL with
  | error e => rw [hc] at h5; cases h5
  | ok g =>
    rw [hc] at h5
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Bool.and_eq_true,
      decide_eq_true_eq] at h5
    obtain ⟨⟨⟨⟨⟨hcr, hgc⟩, -⟩, hsz⟩, -⟩, -⟩ := h5
    have hp : criticalPass maxLPassEnv maxL = .ok { func := g, tables := clampLTabs } := by
      simp only [criticalPass, Pass.ofFunc, maxLPassEnv]
      rw [hc]; rfl
    refine ⟨_, hp, hcr, check_ok_of_toBool' hgc, hsz, ?_⟩
    obtain ⟨fuel, m', h⟩ := RefinesL.returned_int
      (critical_refinesL hp (check_ok_of_toBool' h1) hcr) hm
    exact ⟨fuel, m', h⟩

end GoFV.Proof.Witness

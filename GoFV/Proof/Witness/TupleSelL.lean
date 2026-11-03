import GoFV.Proof.Pass.TupleSelL
import GoFV.Proof.Witness.TightenL

/-!
# Non-vacuity witness: tighten tuple selectors on a lowered function

`tupL` (lowered: arm64 `ADDSflags`), with `x`, `lo` its first two arguments:

```
b1: v40 = ADDSflags x lo  (int, flags); Plain -> b2
b2: v41 = Select0 v40; Ret v41
```

`tighten tuple selectors` (`tightenTupleSelectorsPass`) clones the selector into the tuple's
block `b1` (`v43 = Select0 v40`) and makes `v41` a `Copy` of the clone; input and output pass
`check` and the value-motion validator `moveB` accepts the pair (`v41 = Copy v43` stands for the
source's `v41` through the clone), all by kernel evaluation, so
`tightenTupleSelectors_refinesL` applies: the output returns `5 + 3 = 8` under `runL`, as the
input does.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof GoFV.Proof.MoveL

/-- `clampLTabs` with the tuple type `(int, flags)` as type 31. -/
def tupLTabs : Tables :=
  { clampLTabs with
    types := clampLTabs.types.set! 31 (some (mkT .TUPLE none "(int,flags)" (.tuple 2 29))) }

def tupLValues : Array (Option Value) :=
  let t := Array.replicate 43 (none : Option Value)
  let t := t.set! 1 (some (mkV 1 .InitMem 28 none p0 1 #[] 1))
  let t := t.set! 8 (some (mkVI 8 .ArgIntReg 2 0 (some 7) (pos 2 22 7 0) 1 #[] 1))
  let t := t.set! 9 (some (mkVI 9 .ArgIntReg 2 1 (some 8) (pos 2 22 7 0) 1 #[] 1))
  let t := t.set! 40 (some (mkV 40 .ARM64ADDSflags 31 none (pos 2 22 7 1) 1 #[8, 9] 1))
  let t := t.set! 41 (some (mkV 41 .Select0 2 none (pos 2 23 3 1) 1 #[40] 2))
  t.set! 42 (some (mkV 42 .MakeResult 33 none (pos 2 23 3 1) 1 #[41, 1] 2))

def tupLBlocks : Array (Option Block) := #[none,
  some (mkB 1 .Plain (pos 2 22 7 0) #[] #[⟨2, 0⟩] #[] #[1, 8, 9, 40]),
  some (mkB 2 .Ret (pos 2 23 3 1) #[42] #[] #[⟨1, 0⟩] #[41, 42])]

/-- A selector outside its tuple's block. -/
def tupL : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 42
  bidLast := 2
  blocks := #[1, 2]
  blockTab := tupLBlocks
  valueTab := tupLValues
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := {}

def tupLCheckEnv : CheckEnv := { clampCheckEnv with tabs := tupLTabs }

def tupLPassEnv : PassEnv :=
  { clampTLPassEnv with passName := "tighten tuple selectors", tables := tupLTabs }

/-- The kernel-evaluated facts: `tupL` passes `check` and returns `5 + 3 = 8` under `runL`;
the pass's output passes `check`, `moveB` accepts the pair, the clone `v43` is a `Select0` in
`b1` and `v41` a `Copy`. -/
theorem tupL_facts :
    (check tupLCheckEnv tupL).toBool = true ∧
    returnsInt (runL Env.p1 tupLTabs tupL [.i64 5, .i64 3, .i64 10] {} 3) 8 = true ∧
    ((tightenTupleSelectorsPass tupLPassEnv tupL).toOption.map fun o =>
      decide ((check tupLCheckEnv o.func).toBool = true ∧ moveB tupL o.func = true ∧
        (o.func.block? 1).map (·.values) = some #[1, 8, 9, 40, 43] ∧
        (o.func.value? 41).map (·.op) = some .Copy)) = some true := by
  decide +kernel

/-- **`tighten tuple selectors` on lowered `tupL`**: it clones the selector into the tuple's
block, and its output returns 8 under `runL` (`tightenTupleSelectors_refinesL`). -/
theorem tupleSelL_witness :
    ∃ out, tightenTupleSelectorsPass tupLPassEnv tupL = .ok out ∧
      (out.func.value? 41).map (·.op) = some .Copy ∧
      ∃ fuel m, runL Env.p1 out.tables out.func [.i64 5, .i64 3, .i64 10] {} fuel =
        .returned [.i64 8] m := by
  obtain ⟨h1, h2, h3⟩ := tupL_facts
  obtain ⟨m, hm⟩ := returnsInt_iff.1 h2
  have hf : check tupLCheckEnv tupL = .ok () := by
    revert h1; cases check tupLCheckEnv tupL <;> simp [Except.toBool]
  obtain ⟨out, hp, hg, hmv, -, h41⟩ := ok_of_toOption h3
  have hg' : check tupLCheckEnv out.func = .ok () := by
    revert hg; cases check tupLCheckEnv out.func <;> simp [Except.toBool]
  exact ⟨out, hp, h41, RefinesL.returned_int (tightenTupleSelectors_refinesL hp hf hg' hmv) hm⟩

end GoFV.Proof.Witness

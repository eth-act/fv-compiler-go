import GoFV.Proof.Pass.PairL
import GoFV.Proof.Witness.LowerLoadStore
import GoFV.Proof.Witness.LowCong

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: `pair` on lowered loads and stores

`prw(p *int) int` lowered (hand-written, one block): `v4 = MOVDstore [0] p 5 mem`,
`v5 = MOVDstore [8] p 5 v4`, `v6 = MOVDload [0] p v5`, `v7 = MOVDload [8] p v5`, returning
`v8 = ADD v6 v7`. `pair` (`pairPass`) makes `v6`/`v7` the selectors `Select0`/`Select1` of a new
pair load `v10 = LDP [0] p v5` and `v4` the pair store `STP [0] p 5 5 mem`, `v5` a `Copy` of it.
Input and output pass `check`, and the `pair` validator `PairCheck.pairB` accepts the pair, all by
kernel evaluation, so `pair_refinesL` applies: on a 16-byte heap block the output returns 10 under
`runL`, as the input does.

`prr` stores in the other order (`v4 = MOVDstore [8] p 5 mem`, `v5 = MOVDstore [0] p 7 v4`):
`pair` makes `v5` the pair store `STP [0] p 7 5 v4` and `v4` a `Copy` of `mem`, which `pairB`
accepts by its reversed store case (the two writes commute); the output returns 12.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof GoFV.Proof.MoveL

/-- `prw`, lowered: two stores of 5 at `p` and `p + 8`, two loads of them, their sum. -/
def prwFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 9
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[9] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8, 9])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 1 #[] 1),
    some (mkVI 2 .ArgIntReg 3 0 (some 5) p0 4 #[] 1),
    some (mkVI 3 .ARM64MOVDconst 2 5 none p0 2 #[] 1),
    some (mkVI 4 .ARM64MOVDstore 28 0 none p0 1 #[2, 3, 1] 1),
    some (mkVI 5 .ARM64MOVDstore 28 8 none p0 3 #[2, 3, 4] 1),
    some (mkVI 6 .ARM64MOVDload 2 0 none p0 1 #[2, 5] 1),
    some (mkVI 7 .ARM64MOVDload 2 8 none p0 1 #[2, 5] 1),
    some (mkV 8 .ARM64ADD 2 none p0 1 #[6, 7] 1),
    some (mkV 9 .MakeResult 33 none p0 1 #[8, 5] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `pair` (arm64, `ldst`'s tables). -/
def prwPassEnv : PassEnv := { ldsPassEnv with passName := "pair" }

def prwCheckEnv (tabs : Tables) : CheckEnv :=
  { tabs, typs := #[("Int", 2), ("Mem", 28), ("Void", 31)] }

/-- A 16-byte heap block. -/
def prwMem : Mem := { blocks := #[(.heap 0, { data := Array.replicate 16 (.b 0) })], nextHeap := 1 }

/-- The kernel-evaluated facts: `prw` passes `check` and returns 10 under `runL`; `pair`'s output
passes `check`, `pairB` accepts the pair, and the output's `v4` is `STP`, `v5` a `Copy`, `v6`
and `v7` selectors of `v10 = LDP`. -/
theorem prw_facts :
    (check (prwCheckEnv ldsTabs) prwFunc).toBool = true ∧
    returnsInt (runL Env.p1 ldsTabs prwFunc ldsArgs prwMem 1) 10 = true ∧
    ((pairPass prwPassEnv prwFunc).toOption.map fun o =>
      decide ((check (prwCheckEnv o.tables) o.func).toBool = true ∧
        PairCheck.pairB prwPassEnv.tables o.tables prwFunc o.func = true ∧
        (o.func.value? 4).map (·.op) = some .ARM64STP ∧
        (o.func.value? 5).map (·.op) = some .Copy ∧
        (o.func.value? 6).map (·.op) = some .Select0 ∧
        (o.func.value? 7).map (·.op) = some .Select1 ∧
        (o.func.value? 10).map (·.op) = some .ARM64LDP)) = some true := by
  decide +kernel

/-- **`pair_refinesL` is not vacuous**: `pair` merges `prw`'s two stores into an `STP` and its
two loads into an `LDP`, and its output returns 10 under `runL` (`pair_refinesL`). -/
theorem pairL_witness :
    ∃ out, pairPass prwPassEnv prwFunc = .ok out ∧
      (out.func.value? 4).map (·.op) = some .ARM64STP ∧
      (out.func.value? 10).map (·.op) = some .ARM64LDP ∧
      ∃ fuel m, runL Env.p1 out.tables out.func ldsArgs prwMem fuel = .returned [.i64 10] m := by
  obtain ⟨h1, h2, h3⟩ := prw_facts
  obtain ⟨m, hm⟩ := returnsInt_iff.1 h2
  have hf : check (prwCheckEnv ldsTabs) prwFunc = .ok () := by
    revert h1; cases check (prwCheckEnv ldsTabs) prwFunc <;> simp [Except.toBool]
  obtain ⟨out, hp, hg, hv, h4, -, -, -, h10⟩ := ok_of_toOption h3
  have hg' : check (prwCheckEnv out.tables) out.func = .ok () := by
    revert hg; cases check (prwCheckEnv out.tables) out.func <;> simp [Except.toBool]
  exact ⟨out, hp, h4, h10, RefinesL.returned_int (pair_refinesL hp hf hg' hv) hm⟩

/-- `prr`, lowered: stores of 5 at `p + 8` and then 7 at `p`, two loads of them, their sum. -/
def prrFunc : Func :=
  { prwFunc with
    valueTab := #[none,
      some (mkV 1 .InitMem 28 none p0 1 #[] 1),
      some (mkVI 2 .ArgIntReg 3 0 (some 5) p0 4 #[] 1),
      some (mkVI 3 .ARM64MOVDconst 2 5 none p0 1 #[] 1),
      some (mkVI 4 .ARM64MOVDstore 28 8 none p0 1 #[2, 3, 1] 1),
      some (mkVI 5 .ARM64MOVDstore 28 0 none p0 3 #[2, 11, 4] 1),
      some (mkVI 6 .ARM64MOVDload 2 0 none p0 1 #[2, 5] 1),
      some (mkVI 7 .ARM64MOVDload 2 8 none p0 1 #[2, 5] 1),
      some (mkV 8 .ARM64ADD 2 none p0 1 #[6, 7] 1),
      some (mkV 9 .MakeResult 33 none p0 1 #[8, 5] 1),
      none,
      some (mkVI 11 .ARM64MOVDconst 2 7 none p0 1 #[] 1)]
    vidLast := 11
    blockTab := #[none,
      some (mkB 1 .Ret p0 #[9] #[] #[] #[1, 2, 3, 11, 4, 5, 6, 7, 8, 9])] }

/-- The kernel-evaluated facts: `prr` passes `check` and returns 12 under `runL`; `pair`'s output
passes `check`, `pairB` accepts the pair, and the output's `v5` is `STP`, `v4` a `Copy`. -/
theorem prr_facts :
    (check (prwCheckEnv ldsTabs) prrFunc).toBool = true ∧
    returnsInt (runL Env.p1 ldsTabs prrFunc ldsArgs prwMem 1) 12 = true ∧
    ((pairPass prwPassEnv prrFunc).toOption.map fun o =>
      decide ((check (prwCheckEnv o.tables) o.func).toBool = true ∧
        PairCheck.pairB prwPassEnv.tables o.tables prrFunc o.func = true ∧
        (o.func.value? 5).map (·.op) = some .ARM64STP ∧
        (o.func.value? 4).map (·.op) = some .Copy)) = some true := by
  decide +kernel

/-- **`pair_refinesL` covers reversed stores**: `pair` merges `prr`'s two stores, the higher
one first, into an `STP`, and its output returns 12 under `runL` (`pair_refinesL`). -/
theorem pairL_witness_rev :
    ∃ out, pairPass prwPassEnv prrFunc = .ok out ∧
      (out.func.value? 5).map (·.op) = some .ARM64STP ∧
      ∃ fuel m, runL Env.p1 out.tables out.func ldsArgs prwMem fuel = .returned [.i64 12] m := by
  obtain ⟨h1, h2, h3⟩ := prr_facts
  obtain ⟨m, hm⟩ := returnsInt_iff.1 h2
  have hf : check (prwCheckEnv ldsTabs) prrFunc = .ok () := by
    revert h1; cases check (prwCheckEnv ldsTabs) prrFunc <;> simp [Except.toBool]
  obtain ⟨out, hp, hg, hv, h5, -⟩ := ok_of_toOption h3
  have hg' : check (prwCheckEnv out.tables) out.func = .ok () := by
    revert hg; cases check (prwCheckEnv out.tables) out.func <;> simp [Except.toBool]
  exact ⟨out, hp, h5, RefinesL.returned_int (pair_refinesL hp hf hg' hv) hm⟩

end GoFV.Proof.Witness

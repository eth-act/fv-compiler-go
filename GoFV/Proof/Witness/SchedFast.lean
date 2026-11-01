import GoFV.Proof.SchedFast
import GoFV.Proof.Witness.Max3

/-!
# Non-vacuity witness: `schedFast` on a block with a `NilCheck` and a `Store`

`schedW` (hand-written, `max3`'s tables) has one block of six values listed in reverse
dependency order: `InitMem` (v1), two `ArgIntReg`s (v8, v9), `NilCheck v8 v1` (v12, priority
1), `Store v8 v9 v1` (v13, priority 2) and `Add64 v9 v9` (v14). `schedFast` renames IDs
1, 8, 9, 12, 13, 14 to 0–5, schedules them as `[1, 8, 9, 14, 12, 13]` and agrees with
`Sem.schedule` (by kernel evaluation). `schedFast_spec` and `schedFast_filter` apply: the
non-pure nodes come as `[12, 13]` in `schedule`'s order. `schedFast` also agrees with
`schedule` on every block of the corpus function `max3`.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.SchedFast GoFV.Proof GoFV.Proof.SchedFast

/-- The values of `schedW`, by ID. -/
def schedWValues : Array (Option Value) := #[none,
  some (mkV 1 .InitMem 28 none p0 2 #[] 1),
  none, none, none, none, none, none,
  some (mkV 8 .ArgIntReg 2 (some 8) p0 2 #[] 1),
  some (mkV 9 .ArgIntReg 2 (some 9) p0 2 #[] 1),
  none, none,
  some (mkV 12 .NilCheck 2 none p0 1 #[8, 1] 1),
  some (mkV 13 .Store 28 none p0 1 #[8, 9, 1] 1),
  some (mkV 14 .Add64 2 none p0 1 #[9, 9] 1)]

/-- The block of `schedW`, values in reverse dependency order. -/
def schedWB1 : Block := mkB 1 .Plain p0 #[] #[] #[] #[14, 13, 12, 9, 8, 1]

/-- One block, six values. -/
def schedW : Func :=
  { max3 with valueTab := schedWValues, blockTab := #[none, some schedWB1], blocks := #[1] }

theorem schedFast_schedW :
    schedFast schedW schedWB1 = some #[1, 8, 9, 14, 12, 13] ∧
      schedule schedW schedWB1 = some #[1, 8, 9, 14, 12, 13] := by
  decide +kernel

/-- `schedFast` is defined on every block of `max3` and agrees with `schedule`. -/
theorem schedFast_max3 : (max3.blocks.toList.all fun b => match max3.block? b with
    | some B => (schedFast max3 B).isSome && schedFast max3 B == schedule max3 B
    | none => false) = true := by
  decide +kernel

theorem schedFast_witness :
    SchedSpec (schedNodes schedW schedWB1).toList [1, 8, 9, 14, 12, 13] ∧
      ∃ o', schedule schedW schedWB1 = some o' ∧
        o'.toList.filter (npIn (schedNodes schedW schedWB1).toList) = [12, 13] := by
  refine ⟨schedFast_spec schedFast_schedW.1, ?_⟩
  obtain ⟨o', ho', he⟩ := schedFast_filter (p := npIn (schedNodes schedW schedWB1).toList)
    (fun _ h _ => h) schedFast_schedW.1
  refine ⟨o', ho', ?_⟩
  rw [he]
  decide +kernel

end GoFV.Proof.Witness

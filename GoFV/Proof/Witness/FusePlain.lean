import GoFV.Proof.Pass.FusePlain
import GoFV.Proof.Witness.Max3

/-!
# Non-vacuity witness: plain fusion of a 3-block chain

`sum3` (hand-written in the shape of `max3`, same tables and ABI) is the chain
`b1 (Plain) → b2 (Plain) → b3 (Ret)` computing `a + b + c`; `b1` is the entry. The checked
step `fuseBlockPlainChecked` at `b1` fuses the whole run `[b1, b2, b3]` into `b3`, which
becomes the entry (accepted by the step checker; by kernel evaluation). By
`fuseBlockPlainChecked_refines` the fused function returns `sum3(1, 7, 4) = 12`, as the source
does.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.Fuse.Plain GoFV.Proof GoFV.Proof.FusePlain

/-- The values of `sum3`, by ID. -/
def sum3Values : Array (Option Value) := #[none,
  some (mkV 1 .InitMem 28 none p0 2 #[] 1),
  none, none, none, none, none, none,
  some (mkV 8 .ArgIntReg 2 (some 8) (pos 2 42 7 0) 1 #[] 1),
  some (mkV 9 .ArgIntReg 2 (some 9) (pos 2 42 7 0) 1 #[] 1),
  some (mkV 10 .ArgIntReg 2 (some 10) (pos 2 42 7 0) 1 #[] 1),
  none,
  some (mkV 12 .Add64 2 none (pos 2 43 7 1) 1 #[8, 9] 2),
  some (mkV 13 .OffPtr 20 none p0 0 #[19] 1),
  none, none,
  some (mkV 16 .Add64 2 none (pos 2 44 7 1) 1 #[12, 10] 3),
  some (mkV 17 .SB 15 none p0 0 #[] 1),
  none,
  some (mkV 19 .SP 15 none p0 2 #[] 1),
  some (mkV 20 .MakeResult 33 none (pos 2 45 2 1) 1 #[16, 1] 3),
  some (mkV 21 .LocalAddr 20 (some 6) (pos 2 45 2 1) 0 #[19, 1] 3)]

/-- The blocks of `sum3`, by ID: the chain `b1 → b2 → b3`. -/
def sum3Blocks : Array (Option Block) := #[none,
  some (mkB 1 .Plain (pos 2 42 7 0) #[] #[⟨2, 0⟩] #[] #[1, 8, 9, 10, 17, 19, 13]),
  some (mkB 2 .Plain (pos 2 43 7 0) #[] #[⟨3, 0⟩] #[⟨1, 0⟩] #[12]),
  some (mkB 3 .Ret (pos 2 45 2 1) #[20] #[] #[⟨2, 0⟩] #[16, 20, 21])]

/-- `sum3 a b c = a + b + c` as a chain of three blocks. -/
def sum3 : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 21
  bidLast := 3
  blocks := #[1, 2, 3]
  blockTab := sum3Blocks
  valueTab := sum3Values
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[(0, #[13])]
  freeValues := [18, 15, 14, 11, 7, 6, 5, 4, 3, 2]
  freeBlocks := []
  cache := {}

def sum3CE : CheckEnv :=
  { tabs := max3Tabs, typs := #[("Bool", 3), ("Int", 2), ("Uintptr", 15), ("Mem", 28), ("Void", 30)] }

/-- `sum3(1, 7, 4) = 12`, with fuel 3 (`b1`, `b2`, `b3`). -/
theorem sum3_run : returnsInt (run Env.p1 max3Tabs sum3 max3Args {} 3) 12 = true := by
  decide +kernel

/-- `sum3` passes `check`; the checked step at `b1` fires, fuses the run `[b1, b2, b3]`
(`plainRun`) and makes `b3` the entry block, a `Ret` block holding all eleven values. -/
theorem sum3_fuse :
    (checkOK sum3CE sum3 &&
      decide (Fuse.plainRun sum3 1 = some [1, 2, 3]) &&
      (fuseBlockPlainChecked sum3CE sum3 1).2 &&
      decide ((fuseBlockPlainChecked sum3CE sum3 1).1.entry = 3) &&
      decide (((fuseBlockPlainChecked sum3CE sum3 1).1.block? 3).map (·.kind) = some .Ret) &&
      decide (((fuseBlockPlainChecked sum3CE sum3 1).1.block? 3).map (·.values.size) = some 11))
      = true := by
  decide +kernel

theorem fusePlain_witness :
    (fuseBlockPlainChecked sum3CE sum3 1).2 = true ∧
      (fuseBlockPlainChecked sum3CE sum3 1).1.entry = 3 ∧
      ∃ fuel m, run Env.p1 max3Tabs (fuseBlockPlainChecked sum3CE sum3 1).1 max3Args {} fuel =
        .returned [.i64 12] m := by
  have h := sum3_fuse
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hck, -⟩, hch⟩, hent⟩, -⟩, -⟩ := h
  obtain ⟨m, hm⟩ := returnsInt_iff.1 sum3_run
  obtain ⟨fuel, m', h⟩ := Refines.returned_int
    (fuseBlockPlainChecked_refines (tabs := max3Tabs) (b := 1) (checkOK_sound hck)).1 hm
  exact ⟨hch, hent, fuel, m', h⟩

end GoFV.Proof.Witness

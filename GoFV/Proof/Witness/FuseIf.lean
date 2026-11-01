import GoFV.Proof.Pass.FuseIf
import GoFV.Proof.Witness.Max3

/-!
# Non-vacuity witness: `fuseBlockIf` on an if-triangle

`tri3` (hand-written in the shape of `max3`, same tables and ABI) is the triangle
`b1 (If a < b) → b3 (empty Plain) → b2 (Ret)` with `b1`'s other edge entering `b2` directly;
it returns `a + c` either way. The checked step `fuseBlockIfChecked` at `b1` drops the branch:
`b1` becomes `Plain` into `b2`, the empty arm `b3` is unlinked, and the comparison `a < b` and
its now unused argument `b` are reset to `OpInvalid` (accepted by the step checker; by kernel
evaluation). By `fuseBlockIfChecked_refines` the rewritten function returns
`tri3(1, 7, 4) = 5`, as the source does.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.Fuse GoFV.Proof GoFV.Proof.FuseIf

/-- The values of `tri3`, by ID. -/
def tri3Values : Array (Option Value) := #[none,
  some (mkV 1 .InitMem 28 none p0 2 #[] 1),
  none, none, none, none, none, none,
  some (mkV 8 .ArgIntReg 2 (some 8) (pos 2 42 7 0) 2 #[] 1),
  some (mkV 9 .ArgIntReg 2 (some 9) (pos 2 42 7 0) 1 #[] 1),
  some (mkV 10 .ArgIntReg 2 (some 10) (pos 2 42 7 0) 1 #[] 1),
  none,
  some (mkV 12 .Less64 3 none (pos 2 42 7 1) 1 #[8, 9] 1),
  some (mkV 13 .OffPtr 20 none p0 0 #[19] 1),
  none, none,
  some (mkV 16 .Add64 2 none (pos 2 44 7 1) 1 #[8, 10] 2),
  some (mkV 17 .SB 15 none p0 0 #[] 1),
  none,
  some (mkV 19 .SP 15 none p0 2 #[] 1),
  some (mkV 20 .MakeResult 33 none (pos 2 45 2 1) 1 #[16, 1] 2),
  some (mkV 21 .LocalAddr 20 (some 6) (pos 2 45 2 1) 0 #[19, 1] 2)]

/-- The blocks of `tri3`, by ID: `b1 → b3 → b2` and `b1 → b2`. -/
def tri3Blocks : Array (Option Block) := #[none,
  some (mkB 1 .If (pos 2 42 7 0) #[12] #[⟨3, 0⟩, ⟨2, 0⟩] #[] #[1, 8, 9, 10, 12, 17, 19, 13]),
  some (mkB 2 .Ret (pos 2 45 2 1) #[20] #[] #[⟨1, 1⟩, ⟨3, 0⟩] #[16, 20, 21]),
  some (mkB 3 .Plain (pos 2 43 5 1) #[] #[⟨2, 1⟩] #[⟨1, 0⟩] #[])]

/-- `tri3 a b c = a + c`, behind a branch on `a < b` whose sides join. -/
def tri3 : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 21
  bidLast := 3
  blocks := #[1, 2, 3]
  blockTab := tri3Blocks
  valueTab := tri3Values
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[(0, #[13])]
  freeValues := [18, 15, 14, 11, 7, 6, 5, 4, 3, 2]
  freeBlocks := []
  cache := {}

def tri3CE : CheckEnv :=
  { tabs := max3Tabs, typs := #[("Bool", 3), ("Int", 2), ("Uintptr", 15), ("Mem", 28), ("Void", 30)] }

def tri3TV : TypeView := { tabs := max3Tabs, mem := 28, void := 30 }

/-- `tri3(1, 7, 4) = 5`, with fuel 3 (`b1`, `b3`, `b2`). -/
theorem tri3_run : returnsInt (run Env.p1 max3Tabs tri3 max3Args {} 3) 5 = true := by
  decide +kernel

/-- `tri3` passes `check`; the checked step at `b1` fires: `b1` becomes `Plain`, `b3` is
unlinked, and `a < b` (`v12`) and `b` (`v9`) are reset to `OpInvalid`. -/
theorem tri3_fuse :
    (checkOK tri3CE tri3 &&
      match fuseBlockIfChecked tri3CE tri3TV tri3 1 with
      | .ok (g, ch) => ch && decide ((g.block? 1).map (·.kind) = some .Plain) &&
          decide ((g.block? 3).map (·.kind) = some .Invalid) &&
          decide ((g.value? 12).map (·.op) = some .Invalid) &&
          decide ((g.value? 9).map (·.op) = some .Invalid)
      | .error _ => false)
      = true := by
  decide +kernel

theorem fuseIf_witness :
    ∃ g, fuseBlockIfChecked tri3CE tri3TV tri3 1 = .ok (g, true) ∧
      (g.block? 1).map (·.kind) = some .Plain ∧
      ∃ fuel m, run Env.p1 max3Tabs g max3Args {} fuel = .returned [.i64 5] m := by
  have h := tri3_fuse
  simp only [Bool.and_eq_true] at h
  obtain ⟨hck, h⟩ := h
  split at h
  · rename_i g ch hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hch, hk⟩, -⟩, -⟩, -⟩ := h
    subst hch
    obtain ⟨m, hm⟩ := returnsInt_iff.1 tri3_run
    obtain ⟨fuel, m', h⟩ := Refines.returned_int
      (fuseBlockIfChecked_refines (tabs := max3Tabs) hr
        (Dom.WFDom.of_check (checkOK_sound hck))).1 hm
    exact ⟨g, hr, hk, fuel, m', h⟩
  · cases h

end GoFV.Proof.Witness

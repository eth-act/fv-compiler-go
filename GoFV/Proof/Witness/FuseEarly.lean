import GoFV.Proof.Pass.FuseEarlyPass
import GoFV.Proof.Witness.Max3

/-!
# Non-vacuity witness: early fuse on `0 <= a && a < 10`

`inRange` (hand-written in the shape of `max3`, same tables and ABI) returns `1` if
`0 <= a && a < 10`, else `0`, as the frontend builds it: `b1` branches on `0 <= a` to `b2`
(true) or `b4` (false); `b2` branches on `a < 10` to `b3` (`return 1`) or `b4` (`return 0`).
Early fuse fuses the two comparisons (`fuseIntInRange`: `b2`'s control becomes
`AndB (0 <= a) (a < 10)`, `b1` jumps to `b2`), then the now plain `b1` into `b2`, which becomes
the entry (each rewrite accepted by its step checker; by kernel evaluation). By
`fuseEarly_refines` the output returns `inRange(5) = 1`, as the source does.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof GoFV.Proof.FuseEarly

private def mkVc (id : ID) (op : Op) (t : TypeRef) (auxInt : Int64) (p : Pos) (uses : Nat)
    (args : Array ID) (blk : ID) : Value :=
  { id, op, type := t, auxInt, aux := none, pos := p, uses, args, block := blk }

/-- The values of `inRange`, by ID. -/
def inRangeValues : Array (Option Value) := #[none,
  some (mkV 1 .InitMem 28 none p0 2 #[] 1),
  none, none, none, none, none, none,
  some (mkV 8 .ArgIntReg 2 (some 8) (pos 2 42 7 0) 2 #[] 1),
  none, none,
  some (mkVc 11 .Const64 2 0 p0 2 #[] 1),
  some (mkV 12 .Leq64 3 none (pos 2 43 7 1) 1 #[11, 8] 1),
  some (mkVc 13 .Const64 2 10 p0 1 #[] 2),
  some (mkV 14 .Less64 3 none (pos 2 43 17 1) 1 #[8, 13] 2),
  some (mkVc 15 .Const64 2 1 p0 1 #[] 3),
  some (mkV 16 .MakeResult 33 none (pos 2 44 3 1) 1 #[15, 1] 3),
  none,
  some (mkV 18 .MakeResult 33 none (pos 2 46 2 1) 1 #[11, 1] 4)]

/-- The blocks of `inRange`, by ID. -/
def inRangeBlocks : Array (Option Block) := #[none,
  some (mkB 1 .If (pos 2 43 7 0) #[12] #[⟨2, 0⟩, ⟨4, 0⟩] #[] #[1, 8, 11, 12]),
  some (mkB 2 .If (pos 2 43 17 0) #[14] #[⟨3, 0⟩, ⟨4, 1⟩] #[⟨1, 0⟩] #[13, 14]),
  some (mkB 3 .Ret (pos 2 44 3 1) #[16] #[] #[⟨2, 0⟩] #[15, 16]),
  some (mkB 4 .Ret (pos 2 46 2 1) #[18] #[] #[⟨1, 1⟩, ⟨2, 1⟩] #[18])]

/-- `inRange a _ _ = if 0 <= a && a < 10 then 1 else 0`. -/
def inRange : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 18
  bidLast := 4
  blocks := #[1, 2, 3, 4]
  blockTab := inRangeBlocks
  valueTab := inRangeValues
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[(0, #[11]), (1, #[15]), (10, #[13])]
  freeValues := [17, 10, 9, 7, 6, 5, 4, 3, 2]
  freeBlocks := []
  cache := {}

def inRangeArgs : List Val := [.i64 5, .i64 0, .i64 0]

/-- `inRange(5) = 1`, with fuel 3 (`b1`, `b2`, `b3`). -/
theorem inRange_run : returnsInt (run Env.p1 max3Tabs inRange inRangeArgs {} 3) 1 = true := by
  decide +kernel

/-- The checked comparison fusion at `b2` fires on `inRange` (`fuseIntInRange`). -/
theorem inRange_fuseCmp :
    (checkOK { tabs := max3Tabs, typs := #[("Bool", 3), ("Int", 2), ("Mem", 28), ("Void", 30)] }
        inRange &&
      (Fuse.Cmp.fuseComparisonsChecked (· == 28) Fuse.canOptIntInRange inRange 2).2 &&
      decide (((Fuse.Cmp.fuseComparisonsChecked (· == 28) Fuse.canOptIntInRange inRange 2).1.block? 1).map
        (·.kind) = some .Plain)) = true := by
  decide +kernel

/-- **Non-vacuity of `fuseComparisonsChecked_refines`**: the step fires on `inRange`, and its
result returns `inRange(5) = 1`. -/
theorem fuseCmp_witness :
    (Fuse.Cmp.fuseComparisonsChecked (· == 28) Fuse.canOptIntInRange inRange 2).2 = true ∧
      ∃ fuel m, run Env.p1 max3Tabs
        (Fuse.Cmp.fuseComparisonsChecked (· == 28) Fuse.canOptIntInRange inRange 2).1
        inRangeArgs {} fuel = .returned [.i64 1] m := by
  have h := inRange_fuseCmp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hck, hch⟩, -⟩ := h
  obtain ⟨m, hm⟩ := returnsInt_iff.1 inRange_run
  obtain ⟨fuel, m', h⟩ := Refines.returned_int
    (FuseCmp.fuseComparisonsChecked_refines (tabs := max3Tabs) (b := 2)
      (Dom.WFDom.of_check (checkOK_sound hck))).1 hm
  exact ⟨hch, fuel, m', h⟩

def inRangePassEnv : PassEnv where
  passName := "early fuse"
  pkg := GoStr.ofString "main"
  funcName := GoStr.ofString "inRange"
  abi := 1
  nosplit := false
  pgohot := false
  config := #[("arch", #[.word "arm64"]), ("regsize", #[.word "8"])]
  typs := #[("Bool", 3), ("Int", 2), ("Uintptr", 15), ("Mem", 28), ("Void", 30)]
  typeOrder := default
  tables := max3Tabs

/-- `inRange` passes `check`; early fuse turns it into one `If` block `b2`, the entry, branching
on the fused comparison `AndB (0 <= a) (a < 10)` (`v17`, the first free ID). -/
theorem inRange_fuseEarly :
    (checkOK { tabs := max3Tabs, typs := inRangePassEnv.typs } inRange &&
      match fuseEarlyPass inRangePassEnv inRange with
      | .ok out => decide (out.func.entry = 2) &&
          decide ((out.func.block? 2).map (·.kind) = some .If) &&
          decide ((out.func.block? 2).map (·.controls) = some #[17]) &&
          decide ((out.func.value? 17).map (·.op) = some .AndB) &&
          decide ((out.func.value? 17).map (·.args) = some #[12, 14])
      | .error _ => false) = true := by
  decide +kernel

theorem fuseEarly_witness :
    ∃ out, fuseEarlyPass inRangePassEnv inRange = .ok out ∧ out.func.entry = 2 ∧
      (out.func.value? 17).map (·.op) = some .AndB ∧
      ∃ fuel m, run Env.p1 out.tables out.func inRangeArgs {} fuel = .returned [.i64 1] m := by
  have h1 := inRange_fuseEarly
  obtain ⟨m, hm⟩ := returnsInt_iff.1 inRange_run
  cases hp : fuseEarlyPass inRangePassEnv inRange with
  | error e => rw [hp] at h1; simp at h1
  | ok out =>
    rw [hp] at h1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    obtain ⟨fuel, m', h⟩ := Refines.returned_int (fuseEarly_refines hp) hm
    exact ⟨out, rfl, h1.2.1.1.1.1, h1.2.1.2, fuel, m', h⟩

end GoFV.Proof.Witness

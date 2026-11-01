import GoFV.Proof.Pass.ShortCircCpa
import GoFV.Proof.Witness.FusePlain

/-!
# Non-vacuity witness: short circuit of `a < b && b < c`

`andLt` (hand-written in the shape of `max3`, same tables and ABI) returns `a` if
`a < b && b < c`, else `c`, lowered as Go lowers `&&`: `b1` branches on `a < b` to `b2` (which
computes `b < c`) or straight to the join `b3`, whose boolean `Phi` `v18` takes `b < c` from `b2`
and `a < b` from `b1`; `b3` branches on it to `b4`/`b5`, which join at the `Ret` block `b6`.

`constPhiArgs` replaces `v18`'s argument from `b1` (along `b1`'s `false` edge, where its control
`a < b` is `false`) by a new `ConstBool false` of the entry (accepted by `cpaOK`; by kernel
evaluation). By `constPhiArgsChecked_refines` the result returns `andLt(1, 7, 4) = 4`, as the
source does.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.ShortCircuit GoFV.Proof GoFV.Proof.ShortCirc

/-- The values of `andLt`, by ID. -/
def andLtValues : Array (Option Value) := #[none,
  some (mkV 1 .InitMem 28 none p0 1 #[] 1),
  none, none, none, none, none, none,
  some (mkV 8 .ArgIntReg 2 (some 8) (pos 2 42 7 0) 2 #[] 1),
  some (mkV 9 .ArgIntReg 2 (some 9) (pos 2 42 7 0) 2 #[] 1),
  some (mkV 10 .ArgIntReg 2 (some 10) (pos 2 42 7 0) 2 #[] 1),
  none,
  some (mkV 12 .Less64 3 none (pos 2 42 7 1) 2 #[8, 9] 1),
  some (mkV 13 .OffPtr 20 none p0 0 #[19] 1),
  none, none,
  some (mkV 16 .Less64 3 none (pos 2 42 7 1) 1 #[9, 10] 2),
  some (mkV 17 .SB 15 none p0 0 #[] 1),
  some (mkV 18 .Phi 3 none (pos 2 42 7 0) 1 #[16, 12] 3),
  some (mkV 19 .SP 15 none p0 1 #[] 1),
  some (mkV 20 .Phi 2 none (pos 2 45 2 0) 1 #[8, 10] 6),
  some (mkV 21 .MakeResult 33 none (pos 2 45 2 1) 1 #[20, 1] 6)]

/-- The blocks of `andLt`, by ID. -/
def andLtBlocks : Array (Option Block) := #[none,
  some (mkB 1 .If (pos 2 42 7 0) #[12] #[⟨2, 0⟩, ⟨3, 1⟩] #[] #[1, 8, 9, 10, 12, 17, 19, 13]),
  some (mkB 2 .Plain (pos 2 42 7 0) #[] #[⟨3, 0⟩] #[⟨1, 0⟩] #[16]),
  some (mkB 3 .If (pos 2 42 7 0) #[18] #[⟨4, 0⟩, ⟨5, 0⟩] #[⟨2, 0⟩, ⟨1, 1⟩] #[18]),
  some (mkB 4 .Plain (pos 2 43 5 1) #[] #[⟨6, 0⟩] #[⟨3, 0⟩] #[]),
  some (mkB 5 .Plain (pos 2 44 5 1) #[] #[⟨6, 1⟩] #[⟨3, 1⟩] #[]),
  some (mkB 6 .Ret (pos 2 45 2 1) #[21] #[] #[⟨4, 0⟩, ⟨5, 0⟩] #[20, 21])]

/-- `andLt a b c = if a < b && b < c then a else c`. -/
def andLt : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 21
  bidLast := 6
  blocks := #[1, 2, 3, 4, 5, 6]
  blockTab := andLtBlocks
  valueTab := andLtValues
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[(0, #[13])]
  freeValues := [15, 14, 11, 7, 6, 5, 4, 3, 2]
  freeBlocks := []
  cache := {}

/-- `isBool` of the tables of `max3` (type 3 is `bool`). -/
def isBool3 (t : TypeRef) : Bool := t == 3

/-- `andLt(1, 7, 4) = 4`, with fuel 5 (`b1`, `b2`, `b3`, `b5`, `b6`). -/
theorem andLt_run : returnsInt (run Env.p1 max3Tabs andLt max3Args {} 5) 4 = true := by
  decide +kernel

/-- `andLt` passes `check`; checked `constPhiArgs` replaces `v18`'s argument from `b1` by a new
`ConstBool false` (`v15`, from the free list) of the entry. -/
theorem andLt_cpa :
    (checkOK sum3CE andLt &&
      match constPhiArgsChecked max3Tabs isBool3 (· == ·) 3 andLt with
      | .ok g => decide ((g.value? 18).map (·.args) = some #[16, 15]) &&
          decide ((g.value? 15).map (·.op) = some .ConstBool) &&
          decide ((g.value? 15).map (·.auxInt) = some 0)
      | .error _ => false)
      = true := by
  decide +kernel

theorem shortCircCpa_witness :
    ∃ g, constPhiArgsChecked max3Tabs isBool3 (· == ·) 3 andLt = .ok g ∧
      (g.value? 18).map (·.args) = some #[16, 15] ∧
      ∃ fuel m, run Env.p1 max3Tabs g max3Args {} fuel = .returned [.i64 4] m := by
  have h := andLt_cpa
  simp only [Bool.and_eq_true] at h
  obtain ⟨hck, h⟩ := h
  split at h
  · rename_i g hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hargs, -⟩, -⟩ := h
    obtain ⟨m, hm⟩ := returnsInt_iff.1 andLt_run
    obtain ⟨fuel, m', h⟩ := Refines.returned_int
      (constPhiArgsChecked_refines hr (checkOK_sound hck)).1 hm
    exact ⟨g, hr, hargs, fuel, m', h⟩
  · cases h

end GoFV.Proof.Witness

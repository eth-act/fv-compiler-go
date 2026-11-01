import GoFV.Proof.Pass.FuseLatePass
import GoFV.Proof.Witness.Max3

/-!
# Non-vacuity witness: late fuse redirects `a < 5` past `a < 10`

`lt5lt10` (hand-written in the shape of `max3`, same tables and ABI) returns `1` if
`a < 5 && a < 10`, else `0`: `b1` branches on `a < 5` to `b2` (true) or `b3` (false); `b2`
holds only its control `a < 10` and branches to `b4` (`return 1`) or `b3` (`return 0`). Late
fuse's branch redirect sends `b1`'s true edge straight to `b4`: under the path fact `a < 5`,
prove's validator decides `a < 10` to be true (`Redir.stepOK`, by kernel evaluation); `b2` is
left without predecessors and becomes `Invalid`. By `fuseLate_refines` the output returns
`lt5lt10(3) = 1`, as the source does.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.Fuse GoFV.Proof GoFV.Proof.FuseLate

private def mkVl (id : ID) (op : Op) (t : TypeRef) (auxInt : Int64) (uses : Nat)
    (args : Array ID) (blk : ID) : Value :=
  { id, op, type := t, auxInt, aux := none, pos := p0, uses, args, block := blk }

/-- The values of `lt5lt10`, by ID. -/
def lt5lt10Values : Array (Option Value) := #[none,
  some (mkV 1 .InitMem 28 none p0 2 #[] 1),
  none, none, none, none, none, none,
  some (mkV 8 .ArgIntReg 2 (some 8) p0 2 #[] 1),
  none, none,
  some (mkVl 11 .Const64 2 5 1 #[] 1),
  some (mkV 12 .Less64 3 none p0 1 #[8, 11] 1),
  some (mkVl 13 .Const64 2 10 1 #[] 1),
  some (mkV 14 .Less64 3 none p0 1 #[8, 13] 2),
  some (mkVl 15 .Const64 2 0 1 #[] 1),
  some (mkVl 16 .Const64 2 1 1 #[] 1),
  some (mkV 17 .MakeResult 33 none p0 1 #[16, 1] 4),
  some (mkV 18 .MakeResult 33 none p0 1 #[15, 1] 3)]

/-- The blocks of `lt5lt10`, by ID. -/
def lt5lt10Blocks : Array (Option Block) := #[none,
  some (mkB 1 .If p0 #[12] #[⟨2, 0⟩, ⟨3, 0⟩] #[] #[1, 8, 11, 12, 13, 15, 16]),
  some (mkB 2 .If p0 #[14] #[⟨4, 0⟩, ⟨3, 1⟩] #[⟨1, 0⟩] #[14]),
  some (mkB 3 .Ret p0 #[18] #[] #[⟨1, 1⟩, ⟨2, 1⟩] #[18]),
  some (mkB 4 .Ret p0 #[17] #[] #[⟨2, 0⟩] #[17])]

/-- `lt5lt10 a _ _ = if a < 5 && a < 10 then 1 else 0`. -/
def lt5lt10 : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 18
  bidLast := 4
  blocks := #[1, 2, 3, 4]
  blockTab := lt5lt10Blocks
  valueTab := lt5lt10Values
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[(0, #[15]), (1, #[16]), (5, #[11]), (10, #[13])]
  freeValues := [10, 9, 7, 6, 5, 4, 3, 2]
  freeBlocks := []
  cache := {}

def lt5lt10Args : List Val := [.i64 3, .i64 0, .i64 0]

/-- `lt5lt10(3) = 1`, with fuel 3 (`b1`, `b2`, `b4`). -/
theorem lt5lt10_run : returnsInt (run Env.p1 max3Tabs lt5lt10 lt5lt10Args {} 3) 1 = true := by
  decide +kernel

def lt5lt10PassEnv : PassEnv where
  passName := "late fuse"
  pkg := GoStr.ofString "main"
  funcName := GoStr.ofString "lt5lt10"
  abi := 1
  nosplit := false
  pgohot := false
  config := #[("arch", #[.word "arm64"]), ("ptrsize", #[.word "8"]), ("regsize", #[.word "8"]),
    ("havecondselect", #[.word "1"])]
  typs := #[("Bool", 3), ("Int", 2), ("Uintptr", 15), ("Mem", 28), ("Void", 30)]
  typeOrder := default
  tables := max3Tabs

/-- The redirect `b1 → b2` ⇒ `b1 → b4` (predecessor 0 of `b2`, its successor 0) is accepted by
the checker. -/
theorem lt5lt10_redirectOK :
    Redir.stepOK max3Tabs lt5lt10 (redirect lt5lt10 2 0 0) 2 0 0 = true := by
  decide +kernel

/-- Late fuse sends `b1`'s true edge to `b4` and marks `b2` `Invalid`. -/
theorem lt5lt10_fuseLate :
    (match fuseLatePass lt5lt10PassEnv lt5lt10 with
      | .ok out => decide ((out.func.block? 1).map (·.succs) = some #[⟨4, 1⟩, ⟨3, 0⟩]) &&
          decide ((out.func.block? 2).map (·.kind) = some .Invalid)
      | .error _ => false) = true := by
  decide +kernel

/-- **Non-vacuity of `fuseLate_refines`**: late fuse performs a validated branch redirect on
`lt5lt10`, and its output returns `lt5lt10(3) = 1`. -/
theorem fuseLate_witness :
    ∃ out, fuseLatePass lt5lt10PassEnv lt5lt10 = .ok out ∧
      (out.func.block? 1).map (·.succs) = some #[⟨4, 1⟩, ⟨3, 0⟩] ∧
      ∃ fuel m, run Env.p1 out.tables out.func lt5lt10Args {} fuel = .returned [.i64 1] m := by
  have h1 := lt5lt10_fuseLate
  obtain ⟨m, hm⟩ := returnsInt_iff.1 lt5lt10_run
  cases hp : fuseLatePass lt5lt10PassEnv lt5lt10 with
  | error e => rw [hp] at h1; simp at h1
  | ok out =>
    rw [hp] at h1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    obtain ⟨fuel, m', h⟩ := Refines.returned_int (fuseLate_refines hp) hm
    exact ⟨out, rfl, h1.1, fuel, m', h⟩

/-- **Non-vacuity of `FuseRedirect.redirect_refines`**: the checked redirect on `lt5lt10`
returns `lt5lt10(3) = 1`. -/
theorem fuseRedirect_witness :
    Redir.stepOK max3Tabs lt5lt10 (redirect lt5lt10 2 0 0) 2 0 0 = true ∧
      ∃ fuel m, run Env.p1 max3Tabs (redirect lt5lt10 2 0 0) lt5lt10Args {} fuel =
        .returned [.i64 1] m := by
  have hck : wfDomOK lt5lt10 = true := by decide +kernel
  obtain ⟨m, hm⟩ := returnsInt_iff.1 lt5lt10_run
  obtain ⟨fuel, m', h⟩ := Refines.returned_int
    (FuseRedirect.redirect_refines lt5lt10_redirectOK
      (Dom.WFDom.of_wfDomCheck (ce := { tabs := max3Tabs, typs := lt5lt10PassEnv.typs })
        (wfDomOK_sound hck))).1 hm
  exact ⟨lt5lt10_redirectOK, fuel, m', h⟩

end GoFV.Proof.Witness

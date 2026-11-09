import GoFV.Proof.Pass.Sccp
import GoFV.Proof.Witness.AddZero

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: sccp on `pick` (hand-written)

```go
func pick() int64 {
	x := int64(7)
	if true {
		x = 5
	}
	return x
}
```

as SSA before sccp: the entry `b1` branches on `ConstBool [true]` to `b2` and `b3`, both jump to
`b4`, where `v5 = Phi v3 v4` (`Const64 [5]` from `b2`, `Const64 [7]` from `b3`) is returned.
sccp's analysis finds only the edge into `b2` executable, so `v5` is the constant 5: it becomes
`Const64 [5]`, and the entry's `If` becomes `Plain` with the edge into `b3` removed (both
stages of the checker: constant replacement and edge removal). The checkers accept the result,
input and output pass `check` (kernel evaluation), so `sccp_refines` applies: the output returns
5, as the source does.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof GoFV.Proof.Sccp

/-- `abiInfo` of `pick`: no parameters, one result. -/
def pkABI : CallABI :=
  { abi := 1, nin := 0, nout := 1, spillOff := 8, spillSize := 0, inRegs := 0, outRegs := 1,
    params := #[{ out := true, index := 0, type := 10, name := some 3, regs := #[0],
                  offset := -1 }] }

/-- The definition tables. -/
def pkTabs : Tables where
  types :=
    let t := Array.replicate 41 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func() int64" (.func 0 0 1 #[])))
    let t := t.set! 6 (some (mkT .BOOL (some 1) "bool"))
    let t := t.set! 10 (some (mkT .INT64 (some 8) "int64"))
    let t := t.set! 31 (some (mkT .SSA none "mem"))
    t.set! 40 (some (mkT .RESULTS none "int64,mem" (.results #[10, 31])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.pick}", kind := .call (some 2) (some pkABI) },
    some { fmt := GoStr.ofString "main.pick",
           kind := .sym (GoStr.ofString "main.pick") 1 "" 0 default none none none #[] none },
    some (paramNameT "~r0" .PPARAMOUT 10 0)]

/-- The values, by ID. -/
def pkValues : Array (Option Value) := #[none,
  some (mkVi 1 .InitMem 31 0 p0 1 #[] 1),
  some (mkVi 2 .ConstBool 6 1 p0 1 #[] 1),
  some (mkVi 3 .Const64 10 5 p0 1 #[] 1),
  some (mkVi 4 .Const64 10 7 p0 1 #[] 1),
  some (mkVi 5 .Phi 10 0 p0 1 #[3, 4] 4),
  some (mkVi 6 .MakeResult 40 0 p0 1 #[5, 1] 4)]

/-- The blocks, by ID. -/
def pkBlocks : Array (Option Block) := #[none,
  some (mkB 1 .If p0 #[2] #[⟨2, 0⟩, ⟨3, 0⟩] #[] #[1, 2, 3, 4]),
  some (mkB 2 .Plain p0 #[] #[⟨4, 0⟩] #[⟨1, 0⟩] #[]),
  some (mkB 3 .Plain p0 #[] #[⟨4, 1⟩] #[⟨1, 1⟩] #[]),
  some (mkB 4 .Ret p0 #[6] #[] #[⟨2, 0⟩, ⟨3, 0⟩] #[5, 6])]

/-- `pick`, the input of `sccp`. -/
def pick : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 6
  bidLast := 4
  blocks := #[1, 2, 3, 4]
  blockTab := pkBlocks
  valueTab := pkValues
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[(1, #[2]), (5, #[3]), (7, #[4])]
  freeValues := []
  freeBlocks := []
  cache := {}

def pkTyps : Array (String × TypeRef) := #[("Bool", 6), ("Int64", 10), ("Mem", 31)]

def pkCheckEnv : CheckEnv := { tabs := pkTabs, typs := pkTyps }

/-- The pass environment of `sccp` (arm64, the export's fixed configuration). -/
def pkPassEnv : PassEnv where
  passName := "sccp"
  pkg := GoStr.ofString "main"
  funcName := GoStr.ofString "pick"
  abi := 1
  nosplit := false
  pgohot := false
  config := azPassEnv.config
  typs := pkTyps
  typeOrder := default
  tables := pkTabs

theorem pick_check : (check pkCheckEnv pick).toBool = true := by decide +kernel

/-- By kernel evaluation: the validated pass changes `pick` (`v5` is now `Const64 [5]`, `b1` is
`Plain` towards `b2`) and its result passes `check`. -/
theorem pick_sccp :
    (sccpChecked pkPassEnv pick).toOption.map
      (fun o => (check pkCheckEnv o.func).toBool && o.func != pick &&
        (o.func.value? 5).map (fun (v : Value) => (v.op, v.auxInt, v.args)) ==
          some (.Const64, 5, #[]) &&
        (o.func.block? 1).map (fun (b : Block) => (b.kind, b.succs)) ==
          some (.Plain, #[⟨2, 0⟩])) = some true := by
  decide +kernel

/-- `pick()` returns 5 in three block entries. -/
theorem pick_run : returnsInt (run Env.p1 pkTabs pick [] {} 3) 5 = true := by decide +kernel

/-- **Witness of `sccp_refines`**: sccp folds `pick`'s `Phi` to `Const64 [5]` and removes the
untaken edge of its constant branch; the output returns 5, as the source does. -/
theorem sccp_witness :
    ∃ out, sccpChecked pkPassEnv pick = .ok out ∧ out.func ≠ pick ∧
      (out.func.block? 1).map (fun b => (b.kind, b.succs)) = some (.Plain, #[⟨2, 0⟩]) ∧
      ∃ fuel m, run Env.p1 out.tables out.func [] {} fuel = .returned [.i64 5] m := by
  have hf : check pkCheckEnv pick = .ok () := ok_of_toBool pick_check
  have h2 := pick_sccp
  have h5 := pick_run
  cases hp : sccpChecked pkPassEnv pick with
  | error e => rw [hp] at h2; cases h2
  | ok out =>
    rw [hp] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Bool.and_eq_true,
      bne_iff_ne, ne_eq, beq_iff_eq] at h2
    obtain ⟨⟨⟨hc, hne⟩, -⟩, h4⟩ := h2
    have hg : check pkCheckEnv out.func = .ok () := ok_of_toBool hc
    refine ⟨out, rfl, by simpa using hne, h4, ?_⟩
    have hr := sccp_refines hp hf hg
    obtain ⟨m, hm⟩ := returnsInt_iff.1 h5
    have hm' : run Env.p1 pkPassEnv.tables pick [] {} 3 = .returned [.i64 5] m := hm
    obtain ⟨fuel', ho⟩ := hr Env.p1 Env.p1_mono [] {} 3 (by rw [hm']; trivial)
    rw [hm'] at ho
    refine ⟨fuel', ?_⟩
    generalize run Env.p1 out.tables out.func [] {} fuel' = o at ho ⊢
    cases ho with
    | returned hl =>
      cases hl with
      | cons h1 t =>
        cases t
        cases h1
        exact ⟨_, rfl⟩

end GoFV.Proof.Witness

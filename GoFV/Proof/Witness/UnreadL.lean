import GoFV.Proof.Pass.UnreadL
import GoFV.Proof.Witness.DAE

/-!
# Non-vacuity witness: elim unread autos on lowered `math.NaN`

`std/math/NaN,1.ssa`, the output of section 38 (`lowered cse`, the input of
`elim unread autos`), of the corpus `gofv-corpus/2aae1000ea1d/quick-v7/plain`, transcribed by
hand (the analysis caches, `names` and `canon` left empty; `runL`, `check` and the pass do not
read them). Found by `lake exe unread-probe` (the smallest accepted changed section):

```go
func NaN() float64 { return Float64frombits(uvnan) }   // math/unsafe.go: *(*float64)(unsafe.Pointer(&b))
```

After lowering the inlined `Float64frombits` stores its argument into its parameter copy `b`
(`a4`, a `PAUTO` whose address is no longer used: a frame temporary `Blk.temp`) with
`MOVDstore {b} SP c mem` (`v8`) and reads it back as `FMOVDgpfp c` (`v14`), so nothing reads `b`:
elim unread autos turns `v8` into `Copy mem`. By kernel evaluation: the pass succeeds, its
checker `UnreadL.urel` accepts the result (so `nanL` is in `unreadLFrag`), input and output pass
`check`, `v8` became `Copy`, and the input returns the NaN `0x7FF8000000000001` under `runL`.
`Env.p1` is frame-safe and the empty memory holds no pointer, so `elimUnreadAutos_refinesL`
gives that the output returns it too (`elimUnreadAutosL_witness`).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof

/-- `abiInfo` of `NaN`: no parameters, one `float64` result in `F0` (`RegIndex` 16). -/
def nanABI : CallABI :=
  { abi := 1, nin := 0, nout := 1, spillOff := 8, spillSize := 0, inRegs := 0, outRegs := 1,
    params := #[{ out := true, index := 0, type := 2, name := some 3, regs := #[16]
                  offset := -1 }] }

/-- The definition tables (the types of the values and auxes and `typs`' `UInt64`, `Float64`,
`Uintptr`, `Mem`, `Flags`, `Void`, `ResultMem`). -/
def nanTabs : Tables where
  posBases := #[]
  types :=
    let t := Array.replicate 35 (none : Option TypeDef)
    let t := t.set! 1 (some (mkTy .FUNC (some 8) (some 8) (some 8) true true false false
      "func() float64" "func() float64"
      (.func 0 0 1 #[{ name := GoStr.ofString "", type := 2, offset := none, embedded := false }])))
    let t := t.set! 2 (some (mkTy .FLOAT64 (some 8) (some 8) (some 0) false false true true
      "float64" "float64"))
    let t := t.set! 11 (some (mkTy .UINT64 (some 8) (some 8) (some 0) false false true true
      "uint64" "uint64"))
    let t := t.set! 15 (some (mkTy .UINTPTR (some 8) (some 8) (some 0) false false true true
      "uintptr" "uintptr"))
    let t := t.set! 28 (some (mkTy .SSA none none none false false false false "mem" ""))
    let t := t.set! 29 (some (mkTy .SSA none none none false false false false "flags" ""))
    let t := t.set! 30 (some (mkTy .SSA none none none false false false false "void" ""))
    let t := t.set! 32 (some (mkTy .RESULTS none none none false false false false "mem" ""
      (.results #[28])))
    t.set! 34 (some (mkTy .RESULTS none none none false false false false "float64,mem" ""
      (.results #[2, 28])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{math.NaN}", kind := .call (some 2) (some nanABI) },
    some { fmt := GoStr.ofString "math.NaN",
           kind := .sym (GoStr.ofString "math.NaN") 1 "-" 0 default none none none #[] none },
    some { fmt := GoStr.ofString "~r0",
           kind := .name (GoStr.ofString "~r0") .PPARAMOUT 2 0 1 {} (pos 18 31 12 0) },
    some { fmt := GoStr.ofString "b",
           kind := .name (GoStr.ofString "b") .PAUTO 11 0 1 { addrtaken := true, used := true }
             (pos 58 41 22 0) },
    some { fmt := GoStr.ofString "uint64", kind := .type 11 },
    some { fmt := GoStr.ofString "~r0",
           kind := .name (GoStr.ofString "~r0") .PAUTO 2 0 1 {} (pos 58 41 32 0) }]
  slots := #[]

def nanV (id : ID) (op : Op) (t : TypeRef) (auxInt : Int64) (aux : Option AuxRef) (p : Pos)
    (uses : Nat) (args : Array ID) : Value :=
  { id, op, type := t, auxInt, aux, pos := p, uses, args, block := 2 }

/-- The values, by ID. -/
def nanLValues : Array (Option Value) :=
  let t := Array.replicate 18 (none : Option Value)
  let t := t.set! 1 (some (nanV 1 .InitMem 28 0 none p0 1 #[]))
  let t := t.set! 2 (some (nanV 2 .SP 15 0 none p0 1 #[]))
  let t := t.set! 6 (some (nanV 6 .ARM64MOVDconst 11 9221120237041090561 none p0 2 #[]))
  let t := t.set! 8 (some (nanV 8 .ARM64MOVDstore 28 0 (some 4) (pos 18 31 44 1) 2 #[2, 6, 1]))
  let t := t.set! 9 (some (nanV 9 .InlMark 30 2 none (pos 18 31 44 0) 0 #[8]))
  let t := t.set! 14 (some (nanV 14 .ARM64FMOVDgpfp 2 0 none (pos 58 41 49 1) 1 #[6]))
  t.set! 17 (some (nanV 17 .MakeResult 34 0 none (pos 18 31 22 1) 1 #[14, 8]))

/-- `math.NaN`, lowered: the input of `elim unread autos`. -/
def nanL : Func where
  entry := 2
  type := 1
  ownAux := some 1
  vidLast := 17
  bidLast := 2
  blocks := #[2]
  blockTab := #[none, none,
    some (mkB 2 .Ret (pos 18 31 22 1) #[17] #[] #[] #[1, 2, 6, 8, 9, 14, 17])]
  valueTab := nanLValues
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := [7, 13, 10, 16, 15, 12, 11, 5, 4, 3]
  freeBlocks := [1]
  cache := {}

/-- `Config.Types` (the part `check` and the pass read). -/
def nanTyps : Array (String × TypeRef) :=
  #[("UInt64", 11), ("Float64", 2), ("Uintptr", 15), ("Mem", 28), ("Flags", 29), ("Void", 30),
    ("ResultMem", 32)]

/-- `check`'s environment. -/
def nanCheckEnv : CheckEnv := { tabs := nanTabs, typs := nanTyps }

/-- What `elim unread autos` reads of the export's environment. -/
def nanPassEnv : PassEnv where
  passName := "elim unread autos"
  pkg := GoStr.ofString "math"
  funcName := GoStr.ofString "NaN"
  abi := 1
  nosplit := false
  pgohot := false
  config := #[]
  typs := nanTyps
  typeOrder := default
  tables := nanTabs

/-! ## Certificates (kernel evaluation) -/

/-- The NaN `math.NaN` returns: `uvnan`. -/
def uvnan : BitVec 64 := 0x7FF8000000000001

theorem nanL_facts :
    (check nanCheckEnv nanL).toBool = true ∧ nanL.lowered = true ∧
      unreadLFrag nanPassEnv nanL = true ∧
      (nanL.value? 8).map (·.op) = some .ARM64MOVDstore ∧ nanTabs.forgeable 4 = false ∧
      returnsInt (runL Env.p1 nanTabs nanL [] {} 1) uvnan = true := by
  decide +kernel

theorem nanL_pass :
    ((elimUnreadAutosPass nanPassEnv nanL).toOption.map fun o =>
      (check nanCheckEnv o.func).toBool && o.func != nanL &&
        UnreadL.urel nanTabs nanL o.func &&
        (o.func.value? 8).map (·.op) == some .Copy) = some true := by
  decide +kernel

/-! ## The witness -/

/-- **Non-vacuity of `elimUnreadAutos_refinesL`**: elim unread autos eliminates `NaN`'s
`MOVDstore` `v8` into the frame temporary `b` (`a4`, not `Tables.forgeable`), the checker
`UnreadL.urel` accepts the changed output, which passes `check`, and by
`elimUnreadAutos_refinesL` the output returns `uvnan` under `runL`, as the source does. -/
theorem elimUnreadAutosL_witness :
    ∃ out, elimUnreadAutosPass nanPassEnv nanL = .ok out ∧ out.func ≠ nanL ∧
      UnreadL.urel nanTabs nanL out.func = true ∧ check nanCheckEnv out.func = .ok () ∧
      (nanL.value? 8).map (·.op) = some .ARM64MOVDstore ∧ nanTabs.forgeable 4 = false ∧
      (out.func.value? 8).map (·.op) = some .Copy ∧
      ∃ fuel m, runL Env.p1 out.tables out.func [] {} fuel = .returned [.i64 uvnan] m := by
  obtain ⟨hc, -, hfrag, hst, hfg, hrun⟩ := nanL_facts
  have hp := nanL_pass
  cases hpe : elimUnreadAutosPass nanPassEnv nanL with
  | error e => rw [hpe] at hp; cases hp
  | ok out =>
    rw [hpe] at hp
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Bool.and_eq_true,
      bne_iff_ne, ne_eq, beq_iff_eq] at hp
    obtain ⟨⟨⟨hcg, hne⟩, hu⟩, hcopy⟩ := hp
    refine ⟨out, rfl, hne, hu, ok_of_toBool hcg, hst, hfg, hcopy, ?_⟩
    have hr := UnreadL.elimUnreadAutos_refinesL hpe (ok_of_toBool hc) (ok_of_toBool hcg) hfrag
    obtain ⟨m, hm⟩ := returnsInt_iff.1 hrun
    obtain ⟨fuel', ho⟩ := hr Env.p1 [] {} ⟨p1_frameSafe, stackF0_initAvoids⟩ 1
      (by rw [show nanPassEnv.tables = nanTabs from rfl, hm]; trivial)
    rw [show nanPassEnv.tables = nanTabs from rfl, hm] at ho
    refine ⟨fuel', ?_⟩
    generalize runL Env.p1 out.tables out.func [] {} fuel' = o at ho ⊢
    cases ho with
    | @returned _ _ _ m' hl _ =>
      cases hl with
      | cons h1 t =>
        cases t
        cases h1
        exact ⟨m', rfl⟩

end GoFV.Proof.Witness

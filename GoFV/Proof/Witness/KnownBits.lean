import GoFV.Proof.Pass.KnownBits
import GoFV.Proof.Witness.TraceFP
import GoFV.Proof.Witness.Util

/-!
# Non-vacuity witness: known bits on `sort.isNaN[go.shape.string]`

`std/std/sort/isNaN%5Bgo.shape.string%5D,1.ssa`, the output of section 17 (`middle opt`, the
input of `known bits`), of the corpus `gofv-corpus/2aae1000ea1d/quick-v1`, transcribed by hand
(the tables: the definitions `check`, `knownBits` and `run` read; the stale `names`/`canon`
entries of the dead parameter `x` are dropped):

```go
func isNaN[T Ordered](x T) bool {
	return x != x
}
```

For strings `x != x` became `false` on `b2`; the entry is a `First` block, so `b3` is only
entered from `b2` and its `Phi` `v30` of `true` (edge 0, from `b1`, never taken) and `false`
(from `b2`) is fully known: known bits makes it `Copy v28` of a new `ConstBool [false]` of the
entry. The checker `kbOK` accepts the result, input and output pass `check` (kernel evaluation),
so `knownBits_refines` applies: the output returns `false`, as the source does.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof GoFV.Proof.KnownBits

/-- `abiInfo` of `isNaN[go.shape.string]`: the dictionary and the string in registers, one
result. -/
def inABI : CallABI :=
  { abi := 1, nin := 2, nout := 1, spillOff := 8, spillSize := 24, inRegs := 3, outRegs := 1,
    params := #[{ out := false, index := 0, type := 2, name := some 3, regs := #[0], offset := 0 },
                { out := false, index := 1, type := 5, name := some 4, regs := #[1, 2],
                  offset := 8 },
                { out := true, index := 0, type := 6, name := some 5, regs := #[0],
                  offset := -1 }] }

/-- The definition tables `check`, `knownBits` and `run` read. -/
def inTabs : Tables where
  types :=
    let t := Array.replicate 40 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(*[1]uintptr, go.shape.string) bool"
      (.func 0 2 1 #[])))
    let t := t.set! 2 (some (mkT .PTR (some 8) "*[1]uintptr" (.elem 3)))
    let t := t.set! 3 (some (mkT .ARRAY none "[1]uintptr" (.array 4 1)))
    let t := t.set! 4 (some (mkT .UINTPTR (some 8) "uintptr"))
    let t := t.set! 5 (some { mkT .STRING (some 16) "go.shape.string" with align := some 8 })
    let t := t.set! 6 (some (mkT .BOOL (some 1) "bool"))
    let t := t.set! 31 (some (mkT .SSA none "mem"))
    t.set! 39 (some (mkT .RESULTS none "bool,mem" (.results #[6, 31])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{cmp.isNaN[go.shape.string]}",
           kind := .call (some 2) (some inABI) },
    some { fmt := GoStr.ofString "cmp.isNaN[go.shape.string]",
           kind := .sym (GoStr.ofString "cmp.isNaN[go.shape.string]") 1 "" 0 default none none
             none #[] none },
    some (paramNameT ".dict" .PPARAM 2 0),
    some (paramNameT "x" .PPARAM 5 8),
    some (paramNameT "~r0" .PPARAMOUT 6 0)]

/-- The values, by ID. -/
def inValues : Array (Option Value) :=
  let t := Array.replicate 33 (none : Option Value)
  let t := t.set! 1 (some (mkVi 1 .InitMem 31 0 p0 1 #[] 1))
  let t := t.set! 29 (some (mkVi 29 .ConstBool 6 0 (pos 8 64 11 0) 1 #[] 2))
  let t := t.set! 30 (some (mkVi 30 .Phi 6 0 (pos 8 64 11 0) 1 #[31, 29] 3))
  let t := t.set! 31 (some (mkVi 31 .ConstBool 6 1 p0 1 #[] 1))
  t.set! 32 (some (mkVi 32 .MakeResult 39 0 (pos 8 64 2 0) 1 #[30, 1] 3))

/-- The blocks, by ID. -/
def inBlocks : Array (Option Block) := #[none,
  some (mkB 1 .First (pos 8 64 11 1) #[] #[⟨2, 0⟩, ⟨3, 0⟩] #[] #[1, 31]),
  some (mkB 2 .Plain (pos 8 64 11 0) #[] #[⟨3, 1⟩] #[⟨1, 0⟩] #[29]),
  some (mkB 3 .Ret (pos 8 64 11 1) #[32] #[] #[⟨1, 1⟩, ⟨2, 0⟩] #[30, 32])]

/-- `isNaN[go.shape.string]`, the input of `known bits`. -/
def isNaNStr : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 32
  bidLast := 3
  blocks := #[1, 2, 3]
  blockTab := inBlocks
  valueTab := inValues
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[(1, #[31])]
  freeValues := [28, 19, 11, 8, 16, 25, 22, 14, 27, 26, 24, 23, 21, 20, 18, 17, 15, 13, 12, 10, 9,
    7, 6, 5, 4, 3, 2]
  freeBlocks := []
  cache := {}

def inCheckEnv : CheckEnv :=
  { tabs := inTabs, typs := #[("Bool", 6), ("Uintptr", 4), ("Mem", 31)] }

def inPassEnv : PassEnv where
  passName := "known bits"
  pkg := GoStr.ofString "sort"
  funcName := GoStr.ofString "isNaN[go.shape.string]"
  abi := 1
  nosplit := false
  pgohot := false
  config := #[]
  typs := #[("Bool", 6)]
  typeOrder := default
  tables := inTabs

/-- The arguments: the result does not depend on them. -/
def inArgs : List Val := [.poison, .poison]

theorem isNaNStr_checks :
    (check inCheckEnv isNaNStr).toBool = true ∧
    (knownBitsChecked inTabs default isNaNStr).toOption.map
      (fun g => (check inCheckEnv g).toBool && g != isNaNStr) = some true ∧
    (knownBitsChecked inTabs default isNaNStr).toOption.map
      (fun g => (g.value? 30).map (fun (v : Value) => (v.op, v.args))) = some (some (.Copy, #[28])) ∧
    (knownBitsChecked inTabs default isNaNStr).toOption.map
      (fun g => (g.value? 28).map (fun (v : Value) => (v.op, v.auxInt))) =
        some (some (.ConstBool, 0)) ∧
    returnsBool (run Env.p1 inTabs isNaNStr inArgs {} 3) false = true := by
  decide +kernel

/-- **Witness of `knownBits_refines`**: known bits changes `isNaN[go.shape.string]` (`v30`
becomes `Copy v28`), and the output returns `false`, as the source does. -/
theorem knownBits_witness :
    ∃ out, knownBitsPass inPassEnv isNaNStr = .ok out ∧ out.func ≠ isNaNStr ∧
      (out.func.value? 30).map (fun v => (v.op, v.args)) = some (.Copy, #[28]) ∧
      ∃ fuel m, run Env.p1 out.tables out.func inArgs {} fuel = .returned [.bool false] m := by
  obtain ⟨h1, h2, h4, -, h3⟩ := isNaNStr_checks
  obtain ⟨m, hm⟩ := returnsBool_iff.1 h3
  have hf : check inCheckEnv isNaNStr = .ok () := ok_of_toBool h1
  cases hp : knownBitsChecked inTabs default isNaNStr with
  | error e => rw [hp] at h2; cases h2
  | ok g =>
    rw [hp] at h2 h4
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Bool.and_eq_true] at h2 h4
    obtain ⟨hc, hne⟩ := h2
    have hg : check inCheckEnv g = .ok () := ok_of_toBool hc
    have hpass : knownBitsPass inPassEnv isNaNStr = .ok { func := g, tables := inTabs } := by
      have ht : inPassEnv.tables = inTabs := rfl
      have ho : inPassEnv.typeOrder = default := rfl
      simp only [knownBitsPass, Pass.ofFunc, ht, ho, hp, bind, Except.bind, pure, Except.pure]
    refine ⟨_, hpass, by simpa using hne, by simpa using h4, ?_⟩
    have hr := knownBits_refines hpass hf (ce' := inCheckEnv) hg
    have hm' : run Env.p1 inPassEnv.tables isNaNStr inArgs {} 3 = .returned [.bool false] m := hm
    obtain ⟨fuel', ho⟩ := hr Env.p1 Env.p1_mono inArgs {} 3 (by rw [hm']; trivial)
    rw [hm'] at ho
    refine ⟨fuel', ?_⟩
    generalize run Env.p1 inTabs g inArgs {} fuel' = o at ho ⊢
    cases ho with
    | returned hl =>
      cases hl with
      | cons h1 t =>
        cases t
        cases h1
        exact ⟨_, rfl⟩

end GoFV.Proof.Witness

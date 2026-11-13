import GoFV.Proof.Pass.CopyZero
import GoFV.Opt.Verified
import GoFV.Proof.Witness.Clamp

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: copyelim's zero-size fragment on `(*dloggerFake).b`

`stdall/std/runtime/(*dloggerFake).b,1.ssa` of the corpus `gofv-corpus/2aae1000ea1d/full-v11/plain`,
section 1 (`number lines`, the input of `early phielim and copyelim`), transcribed by hand (equal
to the parsed export but for its cache, and so are the tables' entries it uses): the
compiler-generated pointer wrapper of

```go
func (l dloggerFake) b(x bool) dloggerFake { return l }   // runtime/debuglog.go:207
```

`dloggerFake` is `struct {}`. The wrapper calls `runtime.panicwrap` on a nil `l`, else loads `*l`
after a nil check (`v18 = Load <t3> (NilCheck v15 v16) v16`) and returns its copy
`v21 = Copy <t3> v18`. phielim resets both to `Empty`. The old fragment rejects the function
(`emptyFragB`: `v18` is a zero-size `Load`; `copyFrag`'s `copyNZ`: `v21` is a zero-size copy), but
`CopyZero.zeroGuard` accepts it, so `copyGuard` holds (by kernel evaluation), and
`copyelim_refines_zero` applies to copyelim's output.
-/

namespace GoFV.Proof.Witness.CopyZero

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.Verified GoFV.Proof GoFV.Proof.CopyElim
open GoFV.Proof.Witness (pos p0 mkV mkT mkB)

def nameAux (s : String) (cls : NameClass) (t : TypeRef) (off : Int) (used : Bool) (p : Pos) :
    AuxDef :=
  { fmt := GoStr.ofString s, kind := .name (GoStr.ofString s) cls t off 1 { used } p }

def symAux (s : String) : AuxDef :=
  { fmt := GoStr.ofString s,
    kind := .sym (GoStr.ofString s) 1 "-" 0 default none none none #[] none }

/-- `abiInfo` of `(*dloggerFake).b`: `l`, `x` in registers, the zero-size result on the stack. -/
def bABI : CallABI :=
  { abi := 1, nin := 2, nout := 1, spillOff := 8, spillSize := 16, inRegs := 2, outRegs := 0,
    params := #[{ out := false, index := 0, type := 2, name := some 3, regs := #[0], offset := 0 },
                { out := false, index := 1, type := 4, name := some 4, regs := #[1], offset := 8 },
                { out := true, index := 0, type := 3, name := some 5, regs := #[], offset := 8 }] }

/-- `abiInfo` of `runtime.panicwrap`: no parameters. -/
def panicwrapABI : CallABI :=
  { abi := 1, nin := 0, nout := 0, spillOff := 8, spillSize := 0, inRegs := 0, outRegs := 0,
    params := #[] }

/-- A type definition with its size, alignment, pointer bytes and the flags the export sets. -/
def tdef (kind : TypeKind) (size align ptrdata : Int) (hasptr direct comparable named : Bool)
    (str sym : String) (tail : TypeTail := .none) : TypeDef :=
  { kind, size := some size, align := some align, ptrdata := some ptrdata,
    flags := { hasptr, direct, comparable, named }, str := GoStr.ofString str,
    symName := GoStr.ofString sym, tail }

/-- The definition tables of sections 0 and 1. -/
def dlogTabs : Tables where
  types :=
    let t := Array.replicate 38 (none : Option TypeDef)
    let t := t.set! 1 (some (tdef .FUNC 8 8 8 true true false false
      "method(*dloggerFake) func(bool) dloggerFake"
      "method(*runtime.dloggerFake) func(bool) runtime.dloggerFake"
      (.func 1 1 1 #[⟨GoStr.ofString "l", 2, none, false⟩, ⟨GoStr.ofString "x", 4, none, false⟩,
        ⟨GoStr.ofString "", 3, none, false⟩])))
    let t := t.set! 2 (some (tdef .PTR 8 8 8 true true true false "*dloggerFake"
      "*runtime.dloggerFake" (.elem 3)))
    let t := t.set! 3 (some (tdef .STRUCT 0 1 0 false false true true "dloggerFake"
      "runtime.dloggerFake" (.struct #[])))
    let t := t.set! 4 (some (tdef .BOOL 1 1 0 false false true true "bool" "bool"))
    let t := t.set! 13 (some (tdef .INT 8 8 0 false false true true "int" "int"))
    let t := t.set! 17 (some (tdef .UINTPTR 8 8 0 false false true true "uintptr" "uintptr"))
    let t := t.set! 30 (some (mkT .SSA none "mem"))
    let t := t.set! 32 (some (mkT .SSA none "void"))
    let t := t.set! 34 (some (mkT .RESULTS none "mem" (.results #[30])))
    let t := t.set! 35 (some (tdef .PTR 8 8 8 true true true false "**dloggerFake"
      "**runtime.dloggerFake" (.elem 2)))
    let t := t.set! 36 (some (tdef .PTR 8 8 8 true true true false "*bool" "*bool" (.elem 4)))
    t.set! 37 (some (mkT .RESULTS none "dloggerFake,mem" (.results #[3, 30])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{runtime.(*dloggerFake).b}", kind := .call (some 2) (some bABI) },
    some (symAux "runtime.(*dloggerFake).b"),
    some (nameAux "l" .PPARAM 2 0 true (pos 122 207 7 0)),
    some (nameAux "x" .PPARAM 4 8 true (pos 122 207 24 0)),
    some (nameAux "~r0" .PPARAMOUT 3 0 false (pos 122 207 32 0)),
    some { fmt := GoStr.ofString "AuxCall{runtime.panicwrap}", kind := .call (some 7) (some panicwrapABI) },
    some (symAux "runtime.panicwrap"),
    some (nameAux "l" .PAUTO 3 0 true (pos 10462 207 7 0)),
    some (nameAux "~r0" .PAUTO 3 0 false (pos 10462 207 32 0))]
  slots := #[none, some ⟨3, 2, 0, none, 0⟩, some ⟨4, 4, 0, none, 0⟩, some ⟨8, 3, 0, none, 0⟩,
    some ⟨9, 3, 0, none, 0⟩]

/-- The values of section 1, by ID. -/
def dlogValues : Array (Option Value) := #[none,
  some (mkV 1 .InitMem 30 none p0 5 #[] 1),
  some (mkV 2 .SP 17 none p0 3 #[] 1),
  some (mkV 3 .SB 17 none p0 0 #[] 1),
  some (mkV 4 .LocalAddr 35 (some 3) p0 0 #[2, 1] 1),
  some (mkV 5 .LocalAddr 36 (some 4) p0 0 #[2, 1] 1),
  some (mkV 6 .LocalAddr 2 (some 5) p0 0 #[2, 1] 1),
  some (mkV 7 .Arg 2 (some 3) (pos 1 1 0 2) 2 #[] 1),
  some (mkV 8 .Arg 4 (some 4) (pos 1 1 0 2) 0 #[] 1),
  some (mkV 9 .Empty 3 none p0 0 #[] 1),
  some (mkV 10 .ConstNil 2 none p0 1 #[] 1),
  some (mkV 11 .EqPtr 4 none (pos 1 1 0 1) 1 #[7, 10] 1),
  some (mkV 12 .Copy 30 none (pos 1 1 0 2) 1 #[1] 3),
  some (mkV 13 .StaticLECall 34 (some 6) (pos 1 1 0 0) 1 #[12] 3),
  some (mkV 14 .SelectN 30 none (pos 1 1 0 0) 1 #[13] 3),
  some (mkV 15 .Copy 2 none (pos 1 1 0 2) 1 #[7] 2),
  some (mkV 16 .Copy 30 none (pos 1 1 0 2) 4 #[1] 2),
  some (mkV 17 .NilCheck 2 none (pos 1 1 0 0) 1 #[15, 16] 2),
  some (mkV 18 .Load 3 none (pos 1 1 0 0) 1 #[17, 16] 2),
  some (mkV 19 .Const64 13 none p0 0 #[] 1),
  some { mkV 20 .InlMark 32 none (pos 1 1 0 0) 0 #[16] 2 with auxInt := 10183 },
  some (mkV 21 .Copy 3 none (pos 1 1 0 2) 1 #[18] 4),
  some (mkV 22 .Copy 30 none (pos 1 1 0 2) 1 #[16] 4),
  some (mkV 23 .MakeResult 37 none (pos 1 1 0 0) 1 #[21, 22] 4)]

/-- The blocks of section 1, by ID. -/
def dlogBlocks : Array (Option Block) := #[none,
  some (mkB 1 .If (pos 1 1 0 0) #[11] #[⟨3, 0⟩, ⟨2, 0⟩] #[] #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 19]),
  some (mkB 2 .Plain (pos 1 1 0 1) #[] #[⟨4, 0⟩] #[⟨1, 1⟩] #[15, 16, 17, 18, 20]),
  some (mkB 3 .Exit (pos 1 1 0 0) #[14] #[] #[⟨1, 0⟩] #[12, 13, 14]),
  some (mkB 4 .Ret (pos 1 1 0 1) #[23] #[] #[⟨2, 0⟩] #[21, 22, 23])]

/-- `(*dloggerFake).b`, section 1 (`number lines`). -/
def dlogB : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 23
  bidLast := 4
  blocks := #[1, 2, 3, 4]
  blockTab := dlogBlocks
  valueTab := dlogValues
  names := #[(1, #[7, 15]), (2, #[8]), (3, #[18]), (4, #[18, 21])]
  namedx := #[]
  splits := #[]
  canon := #[(⟨3, 2, 0, none, 0⟩, 1), (⟨4, 4, 0, none, 0⟩, 2), (⟨8, 3, 0, none, 0⟩, 3),
    (⟨9, 3, 0, none, 0⟩, 4)]
  consts := #[(0, #[19]), (3344556677, #[10])]
  freeValues := []
  freeBlocks := []
  cache := {}

def dlogTyps : Array (String × TypeRef) :=
  #[("Bool", 4), ("Int", 13), ("Uintptr", 17), ("Mem", 30), ("Void", 32)]

def dlogPassEnv : PassEnv where
  passName := "early phielim and copyelim"
  pkg := GoStr.ofString "runtime"
  funcName := GoStr.ofString "(*dloggerFake).b"
  abi := 1
  nosplit := false
  pgohot := false
  config := #[]
  typs := dlogTyps
  typeOrder := default
  tables := dlogTabs

def dlogCheckEnv : CheckEnv := { tabs := dlogTabs, typs := dlogTyps }

/-- By kernel evaluation: the input and copyelim's output pass `check`; the old fragment rejects
the input, `copyGuard` accepts it (by `zeroGuard`); copyelim resets `v18` and `v21` to `Empty`. -/
theorem dlogB_facts :
    (check dlogCheckEnv dlogB).toBool = true ∧
    ((copyelim dlogTabs dlogB).toOption.map fun g =>
      (check dlogCheckEnv g).toBool && (g.value? 18).map (·.op) == some .Empty &&
        (g.value? 21).map (·.op) == some .Empty) = some true ∧
    (copyFrag dlogTabs dlogB && emptyFragB dlogTabs dlogB) = false ∧
    copyGuard dlogPassEnv dlogB = true := by
  decide +kernel

/-- **Non-vacuity of `copyelim_refines_zero`**: copyelim runs on `(*dloggerFake).b`, which is
outside `copyelim_refines`' fragment, its guard holds, and its output refines the input under
monotone contracts. -/
theorem copyelim_zero_witness :
    ∃ out, copyelimPass dlogPassEnv dlogB = .ok out ∧
      (copyFrag dlogTabs dlogB && emptyFragB dlogTabs dlogB) = false ∧
      CopyZero.zeroGuard dlogPassEnv dlogB = true ∧
      RefinesUnder Env.Mono out.tables out.func dlogTabs dlogB := by
  obtain ⟨h1, h2, h3, h4⟩ := dlogB_facts
  have hf : check dlogCheckEnv dlogB = .ok () := by
    revert h1; cases check dlogCheckEnv dlogB <;> simp [Except.toBool]
  have hz : CopyZero.zeroGuard dlogPassEnv dlogB = true := by
    have h3' : (copyFrag dlogPassEnv.tables dlogB && emptyFragB dlogPassEnv.tables dlogB) = false :=
      h3
    simp only [copyGuard, Bool.or_eq_true, h3', Bool.false_eq_true, false_or] at h4
    exact h4
  cases hc : copyelim dlogTabs dlogB with
  | error e => rw [hc] at h2; cases h2
  | ok g =>
    rw [hc] at h2
    have hg : check dlogCheckEnv g = .ok () := by
      simp only [Except.toOption, Option.map_some, Option.some.injEq, Bool.and_eq_true] at h2
      have := h2.1.1
      revert this; cases check dlogCheckEnv g <;> simp [Except.toBool]
    have hp : copyelimPass dlogPassEnv dlogB = .ok { func := g, tables := dlogTabs } := by
      simp only [copyelimPass, Pass.ofFunc, dlogPassEnv]
      rw [hc]; rfl
    have hr := CopyZero.copyelim_refines_zero (penv := dlogPassEnv) (f := dlogB)
      (out := { func := g, tables := dlogTabs }) (ce := dlogCheckEnv) (ce' := dlogCheckEnv) hp hf hg hz
    exact ⟨_, hp, h3, hz, hr⟩

/-! ## A zero-size `Phi`

`dlogPhi`: `dlogB` with a join, by hand. Block 2 branches on `x` (`v8`) to the return block 4
directly or through a new empty block 5, and block 4 returns the copy of
`v24 = Phi <dloggerFake> v18 v9` (the loaded `*l` from block 2, the entry's `Empty` from block 5).
phielim resets the `Phi` to `Empty` as well; `zeroReset` resets it too (a droppable atom), so
`zeroGuard` accepts the function. -/

/-- The values of `dlogPhi`, by ID. -/
def phiValues : Array (Option Value) :=
  (dlogValues.set! 1 (some (mkV 1 .InitMem 30 none p0 6 #[] 1))
    |>.set! 8 (some (mkV 8 .Arg 4 (some 4) (pos 1 1 0 2) 1 #[] 1))
    |>.set! 9 (some (mkV 9 .Empty 3 none p0 1 #[] 1))
    |>.set! 16 (some (mkV 16 .Copy 30 none (pos 1 1 0 2) 3 #[1] 2))
    |>.set! 21 (some (mkV 21 .Copy 3 none (pos 1 1 0 2) 1 #[24] 4))
    |>.set! 22 (some (mkV 22 .Copy 30 none (pos 1 1 0 2) 1 #[1] 4))).push
  (some (mkV 24 .Phi 3 none (pos 1 1 0 2) 1 #[18, 9] 4))

/-- The blocks of `dlogPhi`, by ID. -/
def phiBlocks : Array (Option Block) := #[none,
  some (mkB 1 .If (pos 1 1 0 0) #[11] #[⟨3, 0⟩, ⟨2, 0⟩] #[] #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 19]),
  some (mkB 2 .If (pos 1 1 0 1) #[8] #[⟨4, 0⟩, ⟨5, 0⟩] #[⟨1, 1⟩] #[15, 16, 17, 18, 20]),
  some (mkB 3 .Exit (pos 1 1 0 0) #[14] #[] #[⟨1, 0⟩] #[12, 13, 14]),
  some (mkB 4 .Ret (pos 1 1 0 1) #[23] #[] #[⟨2, 0⟩, ⟨5, 0⟩] #[24, 21, 22, 23]),
  some (mkB 5 .Plain (pos 1 1 0 1) #[] #[⟨4, 1⟩] #[⟨2, 1⟩] #[])]

/-- `dlogB` with a zero-size `Phi` at the join of a branch on `x`. -/
def dlogPhi : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 24
  bidLast := 5
  blocks := #[1, 2, 3, 4, 5]
  blockTab := phiBlocks
  valueTab := phiValues
  names := dlogB.names
  namedx := #[]
  splits := #[]
  canon := dlogB.canon
  consts := dlogB.consts
  freeValues := []
  freeBlocks := []
  cache := {}

/-- By kernel evaluation: the input and copyelim's output pass `check`; the old fragment rejects
the input; `zeroReset` resets the `Phi` `v24` to `Empty`, and `copyGuard` accepts the input (by
`zeroGuard`); copyelim resets `v24` to `Empty`. -/
theorem dlogPhi_facts :
    (check dlogCheckEnv dlogPhi).toBool = true ∧
    ((copyelim dlogTabs dlogPhi).toOption.map fun g =>
      (check dlogCheckEnv g).toBool && (g.value? 24).map (·.op) == some .Empty) = some true ∧
    (copyFrag dlogTabs dlogPhi && emptyFragB dlogTabs dlogPhi) = false ∧
    (dlogPhi.value? 24).map (·.op) = some .Phi ∧
    ((CopyZero.zeroReset dlogTabs dlogPhi).value? 24).map (·.op) = some .Empty ∧
    copyGuard dlogPassEnv dlogPhi = true := by
  decide +kernel

/-- **Non-vacuity of `copyelim_refines_zero` with a zero-size `Phi`**: copyelim runs on
`dlogPhi`, which is outside `copyelim_refines`' fragment and has a zero-size `Phi`, its guard
holds, and its output refines the input under monotone contracts. -/
theorem copyelim_zero_phi_witness :
    ∃ out, copyelimPass dlogPassEnv dlogPhi = .ok out ∧
      (copyFrag dlogTabs dlogPhi && emptyFragB dlogTabs dlogPhi) = false ∧
      (dlogPhi.value? 24).map (·.op) = some .Phi ∧
      CopyZero.zeroGuard dlogPassEnv dlogPhi = true ∧
      RefinesUnder Env.Mono out.tables out.func dlogTabs dlogPhi := by
  obtain ⟨h1, h2, h3, hphi, -, h4⟩ := dlogPhi_facts
  have hf : check dlogCheckEnv dlogPhi = .ok () := by
    revert h1; cases check dlogCheckEnv dlogPhi <;> simp [Except.toBool]
  have hz : CopyZero.zeroGuard dlogPassEnv dlogPhi = true := by
    have h3' : (copyFrag dlogPassEnv.tables dlogPhi && emptyFragB dlogPassEnv.tables dlogPhi) =
        false := h3
    simp only [copyGuard, Bool.or_eq_true, h3', Bool.false_eq_true, false_or] at h4
    exact h4
  cases hc : copyelim dlogTabs dlogPhi with
  | error e => rw [hc] at h2; cases h2
  | ok g =>
    rw [hc] at h2
    have hg : check dlogCheckEnv g = .ok () := by
      simp only [Except.toOption, Option.map_some, Option.some.injEq, Bool.and_eq_true] at h2
      have := h2.1
      revert this; cases check dlogCheckEnv g <;> simp [Except.toBool]
    have hp : copyelimPass dlogPassEnv dlogPhi = .ok { func := g, tables := dlogTabs } := by
      simp only [copyelimPass, Pass.ofFunc, dlogPassEnv]
      rw [hc]; rfl
    have hr := CopyZero.copyelim_refines_zero (penv := dlogPassEnv) (f := dlogPhi)
      (out := { func := g, tables := dlogTabs }) (ce := dlogCheckEnv) (ce' := dlogCheckEnv) hp hf hg hz
    exact ⟨_, hp, h3, hphi, hz, hr⟩

end GoFV.Proof.Witness.CopyZero

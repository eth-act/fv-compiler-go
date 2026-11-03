import GoFV.Proof.Regalloc.Sound
import GoFV.Proof.Witness.ClampL

/-!
# Witness function: `runtime.randn` before and after `regalloc` (a spill around a call)

`std/std/runtime/randn,1.ssa` of the corpus `gofv-corpus/2aae1000ea1d/quick-v7/plain`, sections
53 (`flagalloc`, the input of `regalloc`: scheduled, L1) and 54 (`regalloc`, L2), transcribed by
hand (the tables restricted to the entries the runs read; no `f.cached*` analyses):

```go
func randn(n uint32) uint32 {
	return uint32((uint64(uint32(rand())) * uint64(n)) >> 32)
}
```

```
flagalloc: v6 = ArgIntReg {n+0} [0]  v1 = InitMem  v8 = CALLstatic {runtime.rand} v1
           v10 = SelectN [0] v8  v9 = SelectN [1] v8  v14 = UMULL v10 v6  v16 = SRLconst [32] v14
           v18 = MakeResult v16 v9;  Ret v18
regalloc:  v6 (R0), v17 = StoreReg v6 (slot n), v1, v8 ([R0]), v10 (R0), v9,
           v12 = LoadReg v17 (R1), v14 = UMULL v10 v12 (R0), v16 (R0), v18 ([])
```

`n` is live across the call, which clobbers every caller-saved register: `regalloc` spills it to
its parameter slot before the call and reloads it after. `checkRA` accepts (kernel evaluation),
so `checkRA_sound` applies; with `runtime.rand` returning `0xDEADBEEF12345678`,
`randn(1000) = (0x12345678 * 1000) >> 32 = 71` under both `runSched` and `runLoc`.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RegallocCheck

/-- `abiInfo` of `runtime.randn`: one `uint32` register parameter, one `uint32` result. -/
def randnABI : CallABI :=
  { abi := 1, nin := 1, nout := 1, spillOff := 8, spillSize := 8, inRegs := 1, outRegs := 1,
    params := #[{ out := false, index := 0, type := 2, name := some 3, regs := #[0], offset := 0 },
                { out := true, index := 0, type := 2, name := some 4, regs := #[0], offset := -1 }] }

/-- `abiInfo` of `runtime.rand`: no parameter, one `uint64` result. -/
def randABI : CallABI :=
  { abi := 1, nin := 0, nout := 1, spillOff := 8, spillSize := 0, inRegs := 0, outRegs := 1,
    params := #[{ out := true, index := 0, type := 10, name := none, regs := #[0], offset := -1 }] }

/-- `n` (or `~r0`) of type `t` at frame offset `off`. -/
def randnName (s : String) (cls : NameClass) (t : TypeRef) (off : Int) : AuxDef :=
  { fmt := GoStr.ofString s, kind := .name (GoStr.ofString s) cls t off 1 {} p0 }

/-- A function symbol. -/
def randnSym (s : String) : AuxDef :=
  { fmt := GoStr.ofString s, kind := .sym (GoStr.ofString s) 1 "" 0 default none none none #[] none }

/-- The definition tables of section 54 that the runs read. -/
def randnTabs : Tables where
  types :=
    let t := Array.replicate 35 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(uint32) uint32" (.func 0 1 1 #[])))
    let t := t.set! 2 (some (mkT .UINT32 (some 4) "uint32"))
    let t := t.set! 10 (some (mkT .UINT64 (some 8) "uint64"))
    let t := t.set! 28 (some (mkT .SSA none "mem"))
    let t := t.set! 33 (some (mkT .RESULTS none "uint64,mem" (.results #[10, 28])))
    t.set! 34 (some (mkT .RESULTS none "uint32,mem" (.results #[2, 28])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{runtime.randn}", kind := .call (some 2) (some randnABI) },
    some (randnSym "runtime.randn"),
    some (randnName "n" .PPARAM 2 0),
    some (randnName "~r0" .PPARAMOUT 2 0),
    some { fmt := GoStr.ofString "AuxCall{runtime.rand}", kind := .call (some 6) (some randABI) },
    some (randnSym "runtime.rand"),
    some { fmt := GoStr.ofString "n+0", kind := .nameOff 3 0 }]

/-- The values both sections share. -/
def randnValues : Array (Option Value) :=
  let t := Array.replicate 19 (none : Option Value)
  let t := t.set! 6 (some (mkVI 6 .ArgIntReg 2 0 (some 7) (pos 173 209 56 1) 1 #[] 1))
  let t := t.set! 1 (some (mkV 1 .InitMem 28 none p0 1 #[] 1))
  let t := t.set! 8 (some (mkV 8 .ARM64CALLstatic 33 (some 5) (pos 173 209 35 1) 2 #[1] 1))
  let t := t.set! 10 (some (mkVI 10 .SelectN 10 0 none (pos 173 209 35 1) 1 #[8] 1))
  let t := t.set! 9 (some (mkVI 9 .SelectN 28 1 none (pos 173 209 35 0) 1 #[8] 1))
  let t := t.set! 16 (some (mkVI 16 .ARM64SRLconst 10 32 none (pos 173 209 53 0) 1 #[14] 1))
  t.set! 18 (some (mkV 18 .MakeResult 34 none (pos 173 209 2 0) 1 #[16, 9] 1))

/-- `randn` after `flagalloc` (section 53, L1). -/
def randnS : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 18
  bidLast := 1
  blocks := #[1]
  blockTab := #[none,
    some (mkB 1 .Ret (pos 173 209 56 1) #[18] #[] #[] #[6, 1, 8, 10, 9, 14, 16, 18])]
  valueTab := randnValues.set! 14
    (some (mkV 14 .ARM64UMULL 10 none (pos 173 209 40 0) 1 #[10, 6] 1))
  names := #[(1, #[6])]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := [17, 12, 11, 13, 15, 3, 4, 5, 7, 2]
  freeBlocks := []
  cache := {}
  low := { scheduled := true, laidout := true }

/-- The spill slot of `n` (its parameter slot). -/
def randnSlot : SlotKey := { name := 3, type := 2, off := 0, splitOf := none, splitOffset := 0 }

/-- `randn` after `regalloc` (section 54, L2): `n` spilled before the call, reloaded after. -/
def randnRA : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 18
  bidLast := 1
  blocks := #[1]
  blockTab := #[none,
    some (mkB 1 .Ret (pos 173 209 56 1) #[18] #[] #[] #[6, 17, 1, 8, 10, 9, 12, 14, 16, 18])]
  valueTab :=
    let t := randnValues
    let t := t.set! 17 (some (mkV 17 .StoreReg 2 none (pos 173 209 56 1) 1 #[6] 1))
    let t := t.set! 12 (some (mkV 12 .LoadReg 2 none (pos 173 209 40 2) 1 #[17] 1))
    t.set! 14 (some (mkV 14 .ARM64UMULL 10 none (pos 173 209 40 0) 1 #[10, 12] 1))
  names := #[(1, #[6])]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := [2, 3, 4, 5, 7, 11, 13, 15]
  freeBlocks := []
  cache := {}
  low := { scheduled := true, laidout := true
           regAlloc := some (19, #[(6, .reg 0), (8, .results #[some 0]), (10, .reg 0), (12, .reg 1),
             (14, .reg 0), (16, .reg 0), (17, .slot randnSlot), (18, .results #[])]) }

/-- The environment: `runtime.rand` returns `0xDEADBEEF12345678`. -/
def randnEnv : Env where
  extern n := if n == "runtime.rand" then some (fun _ _ m => .returned [.i64 0xDEADBEEF12345678] m)
    else none

/-- The outcome returns the single `uint32` result `v`. -/
def returnsU32 : Outcome → BitVec 32 → Bool
  | .returned [.int .w32 x] _, v => x == v
  | _, _ => false

/-- `checkRA` accepts the allocation (kernel evaluation, certificate included). -/
theorem randnRA_check_toBool : (checkRA randnTabs randnS randnRA).toBool = true := by
  decide +kernel

theorem randnRA_check : checkRA randnTabs randnS randnRA = .ok () := by
  have h := randnRA_check_toBool
  revert h
  cases checkRA randnTabs randnS randnRA with
  | ok u => intro _; rfl
  | error e => intro h; cases h

/-- Under `runSched` (L1) and `runLoc` (L2): `randn(1000) = 71`. -/
theorem randnRA_run :
    returnsU32 (runSched randnEnv randnTabs randnS [.i32 1000] {} 1) 71 = true ∧
    returnsU32 (runLoc randnEnv randnTabs randnRA [.i32 1000] {} 1) 71 = true := by
  decide +kernel

theorem randnS_defined : (runSched randnEnv randnTabs randnS [.i32 1000] {} 1).Defined := by
  have h := randnRA_run.1
  revert h
  cases runSched randnEnv randnTabs randnS [.i32 1000] {} 1 with
  | returned => intro _; trivial
  | panicked => intro _; trivial
  | stuck => intro h; cases h
  | outOfFuel => intro h; cases h

/-- **Witness of `checkRA_sound`**: on `randn`, with a spill and a reload around a call, the
checker accepts, so the allocated function refines the scheduled one; its run on `1000` is a
defined `runLoc` run that the theorem relates to the scheduled run. -/
theorem randnRA_refines : RefinesLS randnTabs randnRA randnTabs randnS :=
  GoFV.Proof.RA.checkRA_sound randnRA_check

theorem randnRA_refines_run :
    ∃ fuel', OutcomeRefines 0 (runSched randnEnv randnTabs randnS [.i32 1000] {} 1)
      (runLoc randnEnv randnTabs randnRA [.i32 1000] {} fuel') :=
  randnRA_refines randnEnv [.i32 1000] {} 1 randnS_defined

end GoFV.Proof.Witness

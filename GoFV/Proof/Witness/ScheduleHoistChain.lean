import GoFV.Proof.Pass.SchedLPass
import GoFV.Proof.Witness.ClampL
import GoFV.Proof.Witness.InitF10
import GoFV.Proof.Witness.LowCong
import GoFV.Proof.Witness.ScheduleHoist
import GoFV.Proof.Witness.Util

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: `NilHoistOK` on a real function with a hoisted chain of depth 2

`cmd/compile/internal/ssa.rewriteValueAMD64_OpGetG` (`rewriteAMD64.go`, generated from
`_gen/AMD64.rules`):

```go
func rewriteValueAMD64_OpGetG(v *Value) bool {
	v_0 := v.Args[0]
	for {
		mem := v_0
		if !(v.Block.Func.OwnAux.Fn.ABI() != obj.ABIInternal) {
			break
		}
		v.reset(OpAMD64LoweredGetG)
		v.AddArg(mem)
		return true
	}
	return false
}
```

Its section 50 (`layout`, the input of `schedule`) in the corpus
`gofv-corpus/2aae1000ea1d/full-v11/plain` (`cmd/cmd/cmd/compile/internal/ssa/
rewriteValueAMD64_OpGetG,1.ssa`), transcribed with the definition tables the passes and the runs
read (`ggTabs`): the values, blocks, names, caches and table entries are printed from the parsed
export and checked equal to it. `b1` checks `v` (`v8`) and loads `v.Args` (`v56 = LDP [40] v8`,
`v48` its pointer, `v44` its length); with `len(v.Args) ≠ 0` it goes to `b9`, which loads
`v.Args[0]` (`v19 = MOVDload v48`) and the chain `v25 = v.Block` (`[64] v8`),
`v28 = v25.Func` (`[136]`), `v31 = v28.OwnAux` (`[288]`), `v34 = v31.Fn` (`[0]`), each through the
nil check of the one before (`v26`, `v29`, `v32`), and `v35` checks `v34`.

`runLF`'s order of `b9` (`o9`) runs `v25`, then the load `v19`, then the chain; Go's `schedule`
(`ScoreNilCheck`: nil checks first) runs the whole chain with its nil checks before `v19` (`t9`).
When `v.Args`'s pointer is nil the source panics at `v19` and never computes `v28`, `v31`, `v34`,
so the target's nil checks `v29`, `v32`, `v35` read pointers the source never evaluates: only
`hoistSwap` allows those pairs (`hoistNeeded`). `v29` checks `v28 = *(v25 + 136)` (the source ran
`v25`: depth 0); `v32` checks `v31`, whose argument `v29` bypasses to the hoisted `v28` (depth 1);
`v35` checks `v34`, whose argument `v32` bypasses to `v31`, itself hoisted on `v28` (depth 2,
`hoistDepth`, not accepted at depth 1: `ggF_depth`).

On the input `mem` (`v` = `heap 1`, an `ssa.Value` whose `Args` has a nil pointer and length 1 (no
Go slice is that; it makes the source fault before the chain), whose `Block` is `heap 2`, whose
`Func` is `heap 3`, whose `OwnAux` is `heap 4`, whose `Fn` is `heap 5`), `NilHoistOK` holds
(`ggF_nilHoistOK`): the only state where a hoisted nil check applies is `b9` before `v19`
(`pairs_fact`), and there, in every extension of the state by hoisted values (`HoistExt`), `v28`,
`v31`, `v34` hoisted read `heap 3`, `heap 4`, `heap 5`, or do not evaluate (`inv_of_ext`).
`NilPtrsOK` and `ArgPtrsOK` hold as well; then `schedule_refinesSchedLF` applies and the output's
`runSched` panics with the nil dereference as the input's `runLF` does
(`schedule_hoist_chain_witness`).

All facts by kernel evaluation (`decide +kernel`).
-/

namespace GoFV.Proof.Witness.ScheduleHoistChain

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.ScheduleCheck GoFV.Proof GoFV.Proof.SchedL
open GoFV.Proof.Witness (pos mkVI mkB mkTy ok_of_toOption ok_of_toBool)
open GoFV.Proof.Witness.ScheduleHoist (isNilPanic isNilPanic_iff ptrOKb ptrOK_of notGoto frags)

/-! ## The function -/

/-- A field at offset `off`. -/
private def fld (name : String) (t : TypeRef) (off : Int) : Field :=
  { name := GoStr.ofString name, type := t, offset := some off, embedded := false }

/-- An `abiparam` line. -/
private def prm (out : Bool) (index : Nat) (t : TypeRef) (name : Option AuxRef) (regs : Array Nat)
    (offset : Int) : ABIParam :=
  { out, index, type := t, name, regs, offset }

/-- The ABI data of a `call` aux (no `callreg`). -/
private def cabi (abi nin nout : Nat) (spillOff spillSize inRegs outRegs : Int)
    (params : Array ABIParam) : CallABI :=
  { abi, nin, nout, spillOff, spillSize, inRegs, outRegs, params }

/-- A local slot of name `n` and type `t`. -/
private def slot (n : AuxRef) (t : TypeRef) : SlotDef :=
  { name := n, type := t, off := 0, splitOf := none, splitOffset := 0 }

/-- The definition tables of section 50 that `schedule`, `check` and the runs read: the types of
the values (with the element and component types of pointers, tuples and results), the function's
auxes and the auxes of the values, and the slots. -/
def ggTabs : Tables where
  types :=
    let t := Array.replicate 359 (none : Option TypeDef)
    let t := t.set! 1 (some (
    mkTy .FUNC (some 8) (some 8) (some 8) true true false false
      "func(*Value) bool" "func(*cmd/compile/internal/ssa.Value) bool"
      (.func 0 1 1 #[{ name := (GoStr.ofString "v"), type := 2, offset := none, embedded := false },
        { name := (GoStr.ofString ""), type := 37, offset := none, embedded := false }])))
    let t := t.set! 2 (some (
    mkTy .PTR (some 8) (some 8) (some 8) true true true false
      "*Value" "*cmd/compile/internal/ssa.Value"
      (.elem 3)))
    let t := t.set! 3 (some (
    mkTy .STRUCT (some 112) (some 8) (some 112) true false false true
      "Value" "cmd/compile/internal/ssa.Value"
      (.struct #[fld "ID" 4 0, fld "Op" 5 4, fld "Type" 6 8, fld "AuxInt" 9 16, fld "Aux" 42 24,
        fld "Args" 43 40, fld "Block" 44 64, fld "Pos" 17 72, fld "Uses" 18 80,
        fld "OnWasmStack" 37 84, fld "InCache" 37 85, fld "argstorage" 331 88])))
    let t := t.set! 5 (some (
    mkTy .INT32 (some 4) (some 4) (some 0) false false true true
      "Op" "cmd/compile/internal/ssa.Op"
      .none))
    let t := t.set! 26 (some (
    mkTy .PTR (some 8) (some 8) (some 8) true true true false
      "*obj.LSym" "*cmd/internal/obj.LSym"
      (.elem 27)))
    let t := t.set! 27 (some (
    mkTy .STRUCT (some 120) (some 8) (some 104) true false false true
      "obj.LSym" "cmd/internal/obj.LSym"
      (.struct #[fld "Name" 22 0,
        { name := (GoStr.ofString "Attribute"), type := 28, offset := (some 16), embedded := true },
        fld "Type" 29 20, fld "Align" 30 22, fld "Size" 9 24, fld "Gotype" 26 32, fld "P" 31 40,
        fld "R" 33 64, fld "Extra" 36 88, fld "Pkg" 22 96, fld "PkgIdx" 18 112, fld "SymIdx" 18 116])))
    let t := t.set! 28 (some (
    mkTy .UINT32 (some 4) (some 4) (some 0) false false true true
      "obj.Attribute" "cmd/internal/obj.Attribute"
      .none))
    let t := t.set! 37 (some (
    mkTy .BOOL (some 1) (some 1) (some 0) false false true true
      "bool" "bool"
      .none))
    let t := t.set! 44 (some (
    mkTy .PTR (some 8) (some 8) (some 8) true true true false
      "*Block" "*cmd/compile/internal/ssa.Block"
      (.elem 45)))
    let t := t.set! 45 (some (
    mkTy .STRUCT (some 312) (some 8) (some 312) true false false true
      "Block" "cmd/compile/internal/ssa.Block"
      (.struct #[fld "ID" 4 0, fld "Pos" 17 4, fld "CPUfeatures" 46 12, fld "Kind" 47 16,
        fld "Likely" 48 17, fld "FlagsLiveAtEnd" 37 18, fld "Hotness" 49 19, fld "Succs" 50 24,
        fld "Preds" 50 48, fld "Controls" 53 72, fld "Aux" 42 88, fld "AuxInt" 9 104,
        fld "Values" 43 112, fld "Func" 54 136, fld "succstorage" 328 144,
        fld "predstorage" 329 176, fld "valstorage" 330 240])))
    let t := t.set! 52 (some (
    mkTy .INT (some 8) (some 8) (some 0) false false true true
      "int" "int"
      .none))
    let t := t.set! 54 (some (
    mkTy .PTR (some 8) (some 8) (some 8) true true true false
      "*Func" "*cmd/compile/internal/ssa.Func"
      (.elem 55)))
    let t := t.set! 55 (some (
    mkTy .STRUCT (some 472) (some 8) (some 472) true false false true
      "Func" "cmd/compile/internal/ssa.Func"
      (.struct #[fld "Config" 56 0, fld "Cache" 171 8, fld "fe" 274 16, fld "pass" 275 32,
        fld "Name" 22 40, fld "Type" 6 56, fld "Blocks" 279 64, fld "Entry" 44 88, fld "bid" 280 96,
        fld "vid" 280 100, fld "HTMLWriter" 281 104, fld "PrintOrHtmlSSA" 37 112,
        fld "ruleMatches" 132 120, fld "ABI0" 67 128, fld "ABI1" 67 136, fld "ABISelf" 67 144,
        fld "ABIDefault" 67 152, fld "maxCPUFeatures" 46 160, fld "scheduled" 37 164,
        fld "laidout" 37 165, fld "NoSplit" 37 166, fld "dumpFileSeq" 16 167, fld "IsPgoHot" 37 168,
        fld "DeferReturn" 44 176, fld "RegAlloc" 286 184, fld "tempRegs" 287 208,
        fld "NamedValues" 288 216, fld "Names" 289 224, fld "CanonicalLocalSlots" 290 248,
        fld "CanonicalLocalSplits" 291 256, fld "RegArgs" 292 264, fld "OwnAux" 294 288,
        fld "CloSlot" 187 296, fld "freeValues" 2 304, fld "freeBlocks" 44 312,
        fld "cachedPostorder" 279 320, fld "cachedIdom" 279 344, fld "cachedSdom" 308 368,
        fld "cachedLoopnest" 310 392, fld "cachedLineStarts" 315 400, fld "auxmap" 324 408,
        fld "constants" 325 416, fld "gofvTypeInfo" 326 424, fld "gofvStem" 22 432,
        fld "gofvHash" 22 448, fld "gofvAux" 327 464])))
    let t := t.set! 105 (some (
    mkTy .UINT32 (some 4) (some 4) (some 0) false false true true
      "uint32" "uint32"
      .none))
    let t := t.set! 294 (some (
    mkTy .PTR (some 8) (some 8) (some 8) true true true false
      "*AuxCall" "*cmd/compile/internal/ssa.AuxCall"
      (.elem 295)))
    let t := t.set! 295 (some (
    mkTy .STRUCT (some 24) (some 8) (some 24) true false true true
      "AuxCall" "cmd/compile/internal/ssa.AuxCall"
      (.struct #[fld "Fn" 26 0, fld "reg" 296 8, fld "abiInfo" 302 16])))
    let t := t.set! 344 (some (
    mkTy .SSA none none none false false false false
      "mem" ""
      .none))
    let t := t.set! 345 (some (
    mkTy .SSA none none none false false false false
      "flags" ""
      .none))
    let t := t.set! 346 (some (
    mkTy .SSA none none none false false false false
      "void" ""
      .none))
    let t := t.set! 348 (some (
    mkTy .RESULTS none none none false false false false
      "mem" ""
      (.results #[344])))
    let t := t.set! 349 (some (
    mkTy .PTR (some 8) (some 8) (some 8) true true true false
      "**Value" "**cmd/compile/internal/ssa.Value"
      (.elem 2)))
    let t := t.set! 355 (some (
    mkTy .PTR (some 8) (some 8) (some 8) true true true false
      "*obj.Attribute" "*cmd/internal/obj.Attribute"
      (.elem 28)))
    let t := t.set! 356 (some (
    mkTy .TUPLE none none none false false false false
      "uint32,mem" ""
      (.tuple 105 344)))
    let t := t.set! 357 (some (
    mkTy .RESULTS none none none false false false false
      "bool,mem" ""
      (.results #[37, 344])))
    let t := t.set! 358 (some (
    mkTy .TUPLE none none none false false false false
      "**Value,int" ""
      (.tuple 349 52)))
    t
  auxes :=
    let t := Array.replicate 17 (none : Option AuxDef)
    let t := t.set! 1 (some
    { fmt := (GoStr.ofString "AuxCall{cmd/compile/internal/ssa.rewriteValueAMD64_OpGetG}"),
      kind := (.call (some 2) (some (cabi 1 1 1 8 8 1 1
        #[prm false 0 2 (some 3) #[0] 0, prm true 0 37 (some 4) #[0] (-1)]))) })
    let t := t.set! 2 (some
    { fmt := (GoStr.ofString "cmd/compile/internal/ssa.rewriteValueAMD64_OpGetG"),
      kind := (.sym (GoStr.ofString "cmd/compile/internal/ssa.rewriteValueAMD64_OpGetG") 1 "-" 0
        {} none none none #[] none) })
    let t := t.set! 3 (some
    { fmt := (GoStr.ofString "v"),
      kind := (.name (GoStr.ofString "v") .PPARAM 2 0 1 { used := true }
        (pos 200 97856 31 0)) })
    let t := t.set! 4 (some
    { fmt := (GoStr.ofString "~r0"),
      kind := (.name (GoStr.ofString "~r0") .PPARAMOUT 37 0 1 {}
        (pos 200 97856 41 0)) })
    let t := t.set! 5 (some
    { fmt := (GoStr.ofString "AuxCall{cmd/compile/internal/ssa.(*Value).reset}"),
      kind := (.call (some 6) (some (cabi 1 2 0 8 16 2 0
        #[prm false 0 2 none #[0] 0, prm false 1 5 none #[1] 8]))) })
    let t := t.set! 6 (some
    { fmt := (GoStr.ofString "cmd/compile/internal/ssa.(*Value).reset"),
      kind := (.sym (GoStr.ofString "cmd/compile/internal/ssa.(*Value).reset") 1 "-" 0
        {} none none none #[] none) })
    let t := t.set! 7 (some
    { fmt := (GoStr.ofString "AuxCall{cmd/compile/internal/ssa.(*Value).AddArg}"),
      kind := (.call (some 8) (some (cabi 1 2 0 8 16 2 0
        #[prm false 0 2 none #[0] 0, prm false 1 2 none #[1] 8]))) })
    let t := t.set! 8 (some
    { fmt := (GoStr.ofString "cmd/compile/internal/ssa.(*Value).AddArg"),
      kind := (.sym (GoStr.ofString "cmd/compile/internal/ssa.(*Value).AddArg") 1 "-" 0
        {} none none none #[] none) })
    let t := t.set! 15 (some
    { fmt := (GoStr.ofString "v+0"),
      kind := (.nameOff 3 0) })
    let t := t.set! 16 (some
    { fmt := (GoStr.ofString "{0 0}"),
      kind := (.pbcc 0 0) })
    t
  slots :=
    #[none, some (slot 3 2), some (slot 9 2), some (slot 10 2), some (slot 11 355),
      some (slot 12 355), some (slot 13 28), some (slot 14 70)]

/-- The values of section 50, by ID. -/
def ggValues : Array (Option Value) := #[
  none,
  some (mkVI 1 .InitMem 344 0 none (pos 0 0 0 0) 15 #[] 1),
  none,
  none,
  none,
  none,
  some (mkVI 6 .ArgIntReg 2 0 (some 15) (pos 200 97857 16 0) 3 #[] 1),
  some (mkVI 7 .ARM64ZERO 37 0 none (pos 0 0 0 0) 1 #[] 7),
  some (mkVI 8 .ARM64LoweredNilCheck 2 0 none (pos 200 97857 10 1) 2 #[6, 1] 1),
  none,
  none,
  none,
  none,
  none,
  none,
  some (mkVI 15 .ARM64LoweredPanicBoundsCC 344 0 (some 16) (pos 200 97857 15 0) 1 #[1] 3),
  none,
  none,
  none,
  some (mkVI 19 .ARM64MOVDload 2 0 none (pos 200 97857 15 0) 1 #[48, 1] 9),
  none,
  none,
  none,
  none,
  none,
  some (mkVI 25 .ARM64MOVDload 44 64 none (pos 200 97863 9 0) 1 #[8, 1] 9),
  some (mkVI 26 .ARM64LoweredNilCheck 44 0 none (pos 200 97863 15 1) 1 #[25, 1] 9),
  none,
  some (mkVI 28 .ARM64MOVDload 54 136 none (pos 200 97863 15 0) 1 #[26, 1] 9),
  some (mkVI 29 .ARM64LoweredNilCheck 54 0 none (pos 200 97863 20 0) 1 #[28, 1] 9),
  none,
  some (mkVI 31 .ARM64MOVDload 294 288 none (pos 200 97863 20 0) 1 #[29, 1] 9),
  some (mkVI 32 .ARM64LoweredNilCheck 294 0 none (pos 200 97863 27 0) 1 #[31, 1] 9),
  none,
  some (mkVI 34 .ARM64MOVDload 26 0 none (pos 200 97863 27 0) 1 #[32, 1] 9),
  some (mkVI 35 .ARM64LoweredNilCheck 26 0 none (pos 200 97863 30 0) 1 #[34, 1] 9),
  some (mkVI 36 .ARM64ADDconst 355 16 none (pos 200 97863 30 0) 1 #[35] 9),
  some (mkVI 37 .InlMark 346 20391 none (pos 200 97863 34 1) 0 #[1] 9),
  some (mkVI 38 .InlMark 346 20392 none (pos 22260 1042 50 1) 0 #[1] 9),
  none,
  some (mkVI 40 .ARM64LDARW 356 0 none (pos 22262 1003 74 1) 2 #[36, 1] 9),
  some (mkVI 41 .Select1 344 0 none (pos 22262 1003 74 0) 2 #[40] 9),
  some (mkVI 42 .Select0 105 0 none (pos 22262 1003 74 0) 1 #[40] 9),
  none,
  some (mkVI 44 .Select1 52 0 none (pos 200 97857 10 0) 1 #[56] 1),
  none,
  some (mkVI 46 .ARM64UBFX 28 5387 none (pos 22260 1042 53 1) 1 #[42] 9),
  none,
  some (mkVI 48 .Select0 349 0 none (pos 200 97857 10 0) 1 #[56] 1),
  none,
  none,
  none,
  some (mkVI 52 .ARM64MOVDconst 5 715 none (pos 0 0 0 0) 1 #[] 10),
  none,
  some (mkVI 54 .ARM64CALLstatic 348 16 (some 5) (pos 200 97866 10 1) 1 #[6, 52, 41] 10),
  some (mkVI 55 .SelectN 344 0 none (pos 200 97866 10 0) 1 #[54] 10),
  some (mkVI 56 .ARM64LDP 358 40 none (pos 200 97857 10 0) 2 #[8, 1] 1),
  some (mkVI 57 .ARM64CALLstatic 348 16 (some 7) (pos 200 97867 11 1) 1 #[6, 19, 55] 10),
  some (mkVI 58 .SelectN 344 0 none (pos 200 97867 11 0) 1 #[57] 10),
  some (mkVI 59 .ARM64MOVDconst 37 1 none (pos 0 0 0 0) 1 #[] 10),
  some (mkVI 60 .MakeResult 357 0 none (pos 200 97868 3 1) 1 #[59, 58] 10),
  none,
  some (mkVI 62 .MakeResult 357 0 none (pos 200 97870 2 1) 1 #[7, 41] 7),
  none,
  none,
  none,
  some (mkVI 66 .ARM64CMPWconst 345 1 none (pos 200 97863 37 1) 1 #[68] 9),
  none,
  some (mkVI 68 .ARM64MOVBUreg 105 0 none (pos 200 97863 37 1) 1 #[46] 9)
]

/-- The blocks of section 50, by ID. -/
def ggBlocks : Array (Option Block) := #[
  none,
  some ({ mkB 1 .ARM64NZ (pos 200 97857 16 0) #[44] #[⟨9, 0⟩, ⟨3, 0⟩] #[]
    #[1, 6, 56, 44, 48, 8] with likely := .likely, auxInt := 0, aux := none }),
  none,
  some (mkB 3 .Exit (pos 200 97857 16 0) #[15] #[] #[⟨1, 1⟩]
    #[15]),
  none,
  none,
  none,
  some (mkB 7 .Ret (pos 200 97870 9 1) #[62] #[] #[⟨9, 1⟩]
    #[62, 7]),
  none,
  some (mkB 9 .ARM64NE (pos 200 97863 43 1) #[66] #[⟨10, 0⟩, ⟨7, 0⟩] #[⟨1, 0⟩]
    #[37, 38, 19, 25, 26, 28, 29, 31, 32, 34, 35, 36, 40, 41, 42, 46, 66, 68]),
  some (mkB 10 .Ret (pos 200 97868 10 1) #[60] #[] #[⟨9, 0⟩]
    #[54, 55, 57, 58, 60, 52, 59]),
  none
]

/-- The caches of sections 50 and 51. -/
def ggCache : Caches :=
  { postorder := some #[10, 7, 9, 3, 1],
    idom := some #[none, none, none, some 1, none, none, none, some 9, none, some 1, some 9, none],
    sdom := some #[{ parent := none, child := none, sibling := none, entry := 0, exit := 0 },
      { parent := none, child := some 3, sibling := none, entry := 2, exit := 29 },
      { parent := none, child := none, sibling := none, entry := 0, exit := 0 },
      { parent := some 1, child := none, sibling := some 9, entry := 5, exit := 8 },
      { parent := none, child := none, sibling := none, entry := 0, exit := 0 },
      { parent := none, child := none, sibling := none, entry := 0, exit := 0 },
      { parent := none, child := none, sibling := none, entry := 0, exit := 0 },
      { parent := some 9, child := none, sibling := some 10, entry := 14, exit := 17 },
      { parent := none, child := none, sibling := none, entry := 0, exit := 0 },
      { parent := some 1, child := some 7, sibling := none, entry := 11, exit := 26 },
      { parent := some 9, child := none, sibling := none, entry := 20, exit := 23 },
      { parent := none, child := none, sibling := none, entry := 0, exit := 0 }],
    loopnest := some { b2lSize := 12, irreducible := false, loops := #[], b2l := #[] },
    auxmap := some #[(some 3, 1), (none, 2), (some 15, 3)],
    lineStarts := some #[{ index := 200, bounds := some (97857, 97870), pending := #[] },
      { index := 22260, bounds := some (1042, 1042), pending := #[] },
      { index := 22262, bounds := some (1003, 1003), pending := #[] }] }

/-- `rewriteValueAMD64_OpGetG`, section 50 (`layout`). -/
def ggF : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 68
  bidLast := 11
  blocks := #[1, 9, 10, 7, 3]
  blockTab := ggBlocks
  valueTab := ggValues
  names := #[(1, #[6]), (2, #[19]), (3, #[19]), (4, #[36]), (5, #[36]), (6, #[42])]
  namedx := #[]
  splits := #[]
  canon := #[(slot 3 2, 1), (slot 9 2, 2), (slot 10 2, 3), (slot 11 355, 4), (slot 12 355, 5),
    (slot 13 28, 6), (slot 14 70, 7)]
  consts := #[]
  freeValues := [17, 50, 47, 33, 30, 27, 24, 23, 53, 45, 61, 13, 9, 51, 49, 11, 10, 16, 12, 64, 43,
    39, 22, 21, 20, 67, 65, 63, 14, 18, 5, 4, 3, 2]
  freeBlocks := [11, 8, 5, 4, 2, 6]
  cache := ggCache
  low := { laidout := true }

/-- Section 51 (`schedule`): the blocks' new orders; the nil checks are `void` and unused, the
loads read the checked pointers, `v6`, `v25`, `v28`, `v31` gain those uses. -/
def ggS : Func :=
  { ggF with
    blockTab := ggBlocks
      |>.set! 1 (some { mkB 1 .ARM64NZ (pos 200 97857 16 0) #[44] #[⟨9, 0⟩, ⟨3, 0⟩] #[]
          #[6, 1, 8, 56, 44, 48] with likely := .likely })
      |>.set! 7 (some (mkB 7 .Ret (pos 200 97870 9 1) #[62] #[] #[⟨9, 1⟩] #[7, 62]))
      |>.set! 9 (some (mkB 9 .ARM64NE (pos 200 97863 43 1) #[66] #[⟨10, 0⟩, ⟨7, 0⟩] #[⟨1, 0⟩]
          #[25, 26, 28, 29, 31, 32, 34, 35, 36, 19, 37, 38, 40, 42, 41, 46, 68, 66]))
      |>.set! 10 (some (mkB 10 .Ret (pos 200 97868 10 1) #[60] #[] #[⟨9, 0⟩]
          #[59, 52, 54, 55, 57, 58, 60]))
    valueTab := ggValues
      |>.set! 6 (some (mkVI 6 .ArgIntReg 2 0 (some 15) (pos 200 97857 16 0) 5 #[] 1))
      |>.set! 8 (some (mkVI 8 .ARM64LoweredNilCheck 346 0 none (pos 200 97857 10 1) 0 #[6, 1] 1))
      |>.set! 25 (some (mkVI 25 .ARM64MOVDload 44 64 none (pos 200 97863 9 0) 2 #[6, 1] 9))
      |>.set! 26
        (some (mkVI 26 .ARM64LoweredNilCheck 346 0 none (pos 200 97863 15 1) 0 #[25, 1] 9))
      |>.set! 28 (some (mkVI 28 .ARM64MOVDload 54 136 none (pos 200 97863 15 0) 2 #[25, 1] 9))
      |>.set! 29
        (some (mkVI 29 .ARM64LoweredNilCheck 346 0 none (pos 200 97863 20 0) 0 #[28, 1] 9))
      |>.set! 31 (some (mkVI 31 .ARM64MOVDload 294 288 none (pos 200 97863 20 0) 2 #[28, 1] 9))
      |>.set! 32
        (some (mkVI 32 .ARM64LoweredNilCheck 346 0 none (pos 200 97863 27 0) 0 #[31, 1] 9))
      |>.set! 34 (some (mkVI 34 .ARM64MOVDload 26 0 none (pos 200 97863 27 0) 2 #[31, 1] 9))
      |>.set! 35
        (some (mkVI 35 .ARM64LoweredNilCheck 346 0 none (pos 200 97863 30 0) 0 #[34, 1] 9))
      |>.set! 36 (some (mkVI 36 .ARM64ADDconst 355 16 none (pos 200 97863 30 0) 1 #[34] 9))
      |>.set! 56 (some (mkVI 56 .ARM64LDP 358 40 none (pos 200 97857 10 0) 2 #[6, 1] 1))
    low := { scheduled := true, laidout := true } }

/-- The SSA pseudo-types (`typs` of the export). -/
def ggTyps : Array (String × TypeRef) :=
  #[("Bool", 37), ("Int8", 66), ("Int16", 30), ("Int32", 18), ("Int64", 9), ("UInt8", 16),
    ("UInt16", 93), ("UInt32", 105), ("UInt64", 64), ("Int", 52), ("Float32", 332),
    ("Float64", 333), ("UInt", 130), ("Uintptr", 122), ("String", 22), ("BytePtr", 334),
    ("Int32Ptr", 335), ("UInt32Ptr", 336), ("IntPtr", 337), ("UintptrPtr", 338),
    ("Float32Ptr", 339), ("Float64Ptr", 340), ("BytePtrPtr", 341), ("Complex64", 342),
    ("Complex128", 343), ("UnsafePtr", 120), ("Mem", 344), ("Flags", 345), ("Void", 346),
    ("Int128", 347), ("ResultMem", 348)]

/-- The pass environment of `schedule` on section 50. -/
def ggEnv : PassEnv where
  passName := "schedule"
  pkg := GoStr.ofString "cmd/compile/internal/ssa"
  funcName := GoStr.ofString "rewriteValueAMD64_OpGetG"
  abi := 1
  nosplit := false
  pgohot := false
  config := #[("arch", #[.word "arm64"]), ("hasgreg", #[.word "1"]), ("optimize", #[.word "1"])]
  typs := ggTyps
  typeOrder := default
  tables := ggTabs

def ggCheckEnv : CheckEnv := { tabs := ggTabs, typs := ggTyps }

theorem ggF_check : (check ggCheckEnv ggF).toBool = true := by decide +kernel

/-- `schedule` outputs section 51 on section 50. -/
theorem ggF_schedule :
    ((schedulePass ggEnv ggF).toOption.map fun o => decide (o.func = ggS)) = some true := by
  decide +kernel

/-- `scheduleCheck` accepts the scheduling, and some pair only through `hoistSwap`
(`hoistNeeded`). -/
theorem ggS_check : scheduleCheck ggTabs ggF ggS = true ∧ hoistNeeded ggTabs ggF ggS = true := by
  decide +kernel

/-! ## The orders and the depth of the chains -/

local notation "cS" => Ctx.makeL ggTabs ggF
local notation "mdF" => LMode.mk ggF.lowered true

/-- `runLF`'s order of `b1` (`Ctx.makeL`). -/
def o1 : Array ID := #[6, 1, 8, 56, 48, 44]

/-- `runLF`'s order of `b9`: `v25`, the load `v19`, then the chain. -/
def o9 : Array ID := #[25, 19, 38, 37, 26, 28, 29, 31, 32, 34, 35, 36, 40, 42, 46, 68, 66, 41]

/-- `runSched`'s order of `b1` in `ggS` (`Ctx.makeSched`). -/
def t1 : Array ID := #[6, 1, 8, 56, 44, 48]

/-- `runSched`'s order of `b9` in `ggS`: the chain and its nil checks before `v19`. -/
def t9 : Array ID := #[25, 26, 28, 29, 31, 32, 34, 35, 36, 19, 37, 38, 40, 42, 41, 46, 68, 66]

theorem o_eq : ((cS).sched[1]?).join = some o1 ∧ ((cS).sched[9]?).join = some o9 := by
  decide +kernel

theorem t_eq : ((Ctx.makeSched ggTabs ggS).sched[1]?).join = some t1 ∧
    ((Ctx.makeSched ggTabs ggS).sched[9]?).join = some t9 := by
  decide +kernel

/-- **Depth 2**: `v35` checks `v34`, whose argument `v32` (bypass `v31`) is a hoisted value at
depth 2 (`hoistDepth`) and not at depth 1; `v32` checks `v31`, whose argument `v29` (bypass `v28`)
is one at depth 1 and not at depth 0. -/
theorem ggF_depth :
    hoistArg ggF (srcPos ggF.valueTab.size o9.toList) 19 1 32 = false ∧
      hoistArg ggF (srcPos ggF.valueTab.size o9.toList) 19 hoistDepth 32 = true ∧
      hoistArg ggF (srcPos ggF.valueTab.size o9.toList) 19 0 29 = false ∧
      hoistArg ggF (srcPos ggF.valueTab.size o9.toList) 19 1 29 = true := by
  decide +kernel

/-! ## The input -/

/-- Heap object `n`. -/
def hp (n : Nat) : Ptr := ⟨.heap n, 0⟩

/-- A little-endian 64-bit word below 256. -/
def word (n : Nat) : Array Byte :=
  #[.b (BitVec.ofNat 8 n), .b 0, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0]

/-- `*v` (`heap 1`, an `ssa.Value`, 112 bytes): `Args` (offset 40) a nil pointer with length and
capacity 1, `Block` (offset 64) `heap 2`. -/
def valueObj : Alloc :=
  { data := Array.replicate 48 (.b 0) ++ word 1 ++ word 1 ++ frags (hp 2) ++
      Array.replicate 40 (.b 0) }

/-- `v.Block` (`heap 2`): `Func` (offset 136) `heap 3`. -/
def blockObj : Alloc := { data := Array.replicate 136 (.b 0) ++ frags (hp 3) }

/-- `v.Block.Func` (`heap 3`): `OwnAux` (offset 288) `heap 4`. -/
def funcObj : Alloc := { data := Array.replicate 288 (.b 0) ++ frags (hp 4) }

/-- `v.Block.Func.OwnAux` (`heap 4`): `Fn` (offset 0) `heap 5`. -/
def auxObj : Alloc := { data := frags (hp 5) }

/-- `v.Block.Func.OwnAux.Fn` (`heap 5`), its `Attribute` at offset 16. -/
def lsymObj : Alloc := { data := Array.replicate 24 (.b 0) }

/-- The input memory. -/
def mem : Mem :=
  { blocks := #[(.heap 1, valueObj), (.heap 2, blockObj), (.heap 3, funcObj), (.heap 4, auxObj),
      (.heap 5, lsymObj)],
    nextHeap := 6 }

/-- The argument `v`. -/
def args : List Val := [.ptr (hp 1)]

/-- The environment (no closure). -/
def env : Env := Env.p1

/-- The input's `runLF` panics at `v19` (the load of `v.Args[0]` through a nil pointer). -/
theorem ggF_runLF : isNilPanic (runLF env ggTabs ggF args mem 3) = true := by decide +kernel

/-- The only pointer-shaped register piece of a parameter is `v6` (`v`); it reads `heap 1`. -/
theorem argPtr_fact :
    (List.range ggF.valueTab.size).all (fun x =>
      !argPtr ggTabs (cS).params (cS).tys ggF x ||
        match ggF.value? x with
        | some v =>
          match evalValueL mdF env cS (entryFrame env cS args mem) v with
          | .ok y => ptrOKb y
          | _ => true
        | none => true) = true := by
  decide +kernel

/-- **`ArgPtrsOK` on `mem`**. -/
theorem ggF_argPtrsOK : ArgPtrsOK ggTabs ggF env args mem := by
  refine ⟨fun x v hv hp y hy => ?_, fun c hc => by cases hc⟩
  have hx : x < ggF.valueTab.size := by
    simp only [Func.value?, Option.join_eq_some_iff] at hv
    exact (Array.getElem?_eq_some_iff.1 hv).1
  have h1 := List.all_eq_true.1 argPtr_fact x (List.mem_range.2 hx)
  simp only [hp, hv, hy, Bool.not_true, Bool.false_or] at h1
  exact ptrOK_of h1

/-! ## The states `runLF` reaches -/

/-- `b1`'s block step goes to `b9` along its edge 0 (`len(v.Args) = 1`). -/
def goto90 : Step → Bool
  | .goto _ e => e.b == 9 && e.i == 0
  | _ => false

theorem step1 : goto90 (blockStepL mdF env cS (entryFrame env cS args mem) 1 0) = true := by
  decide +kernel

/-- The frame `b1` hands to `b9`. -/
def F9 : Frame :=
  match blockStepL mdF env cS (entryFrame env cS args mem) 1 0 with
  | .goto fr _ => fr
  | _ => entryFrame env cS args mem

/-- `b9`'s block step panics (at `v19`). -/
theorem step9 : notGoto (blockStepL mdF env cS F9 9 0) = true := by decide +kernel

/-- `runLF` reaches the entry and `b9` (from `b1`), nothing else. -/
theorem reach {fr : Frame} {b : ID} {i : Nat}
    (h : ReachL mdF env cS (entryFrame env cS args mem) 1 0 fr b i) :
    (fr = entryFrame env cS args mem ∧ b = 1 ∧ i = 0) ∨ (fr = F9 ∧ b = 9 ∧ i = 0) := by
  cases h with
  | refl => exact .inl ⟨rfl, rfl, rfl⟩
  | @step _ fr' _ _ _ _ _ e hs h2 =>
    have h1 := step1
    have hF : F9 = fr' := by unfold F9; rw [hs]
    rw [hs] at h1
    simp only [goto90, Bool.and_eq_true, beq_iff_eq] at h1
    obtain ⟨hb, hi⟩ := h1
    rw [hb, hi, ← hF] at h2
    cases h2 with
    | refl => exact .inr ⟨rfl, rfl, rfl⟩
    | step hs' _ =>
      have h3 := step9
      rw [hs'] at h3
      cases h3

/-- The frame after block `b`'s `Phi`s (none here, entered along edge 0 from `fr`) and the
first `k` values of `o`, if they evaluate. -/
def prefixAt (fr : Frame) (b : ID) (o : Array ID) (k : Nat) : Option Frame :=
  match ggF.block? b with
  | some blk =>
    match blk.values.toList.filterMapM (phiStepL mdF cS fr 0) with
    | .ok ps =>
      match evalAllL mdF env cS { fr with regs := setPhis ps fr.regs } (o.toList.take k) with
      | .ok H => some H
      | _ => none
    | _ => none
  | none => none

theorem prefixAt_of {fr : Frame} {b : ID} {o : Array ID} {blk : Block} {ps : List (ID × Val)}
    {k : Nat} {H : Frame} (hb : ggF.block? b = some blk)
    (hps : blk.values.toList.filterMapM (phiStepL mdF cS fr 0) = .ok ps)
    (hev : evalAllL mdF env cS { fr with regs := setPhis ps fr.regs } (o.toList.take k) = .ok H) :
    prefixAt fr b o k = some H := by
  unfold prefixAt
  simp only [hb, hps, hev]

/-- A fact `P` of every prefix of `o` (up to `o.size`) holds of every prefix. -/
theorem prefix_all {fr : Frame} {b : ID} {o : Array ID} {P : Frame → Bool}
    (hall : (List.range (o.size + 1)).all (fun k => match prefixAt fr b o k with
      | some H => P H
      | none => true) = true)
    {blk : Block} {ps : List (ID × Val)} {k : Nat} {H : Frame} (hb : ggF.block? b = some blk)
    (hps : blk.values.toList.filterMapM (phiStepL mdF cS fr 0) = .ok ps)
    (hev : evalAllL mdF env cS { fr with regs := setPhis ps fr.regs } (o.toList.take k) = .ok H) :
    P H = true := by
  have hk : o.toList.take k = o.toList.take (min k o.size) := by
    rcases Nat.le_total k o.size with h | h
    · rw [Nat.min_eq_left h]
    · rw [Nat.min_eq_right h, List.take_of_length_le (l := o.toList) (i := k) (by simpa using h),
        List.take_of_length_le (l := o.toList) (i := o.size) (by simp)]
  rw [hk] at hev
  have h1 := List.all_eq_true.1 hall (min k o.size) (List.mem_range.2 (by omega))
  rw [prefixAt_of hb hps hev] at h1
  exact h1

/-! ## The checked pointers on `mem` -/

/-- `NilRegsOK`, computed. -/
def nilRegsB (H : Frame) : Bool :=
  (List.range ggF.valueTab.size).all fun y =>
    match ggF.value? y with
    | some vy => !vy.op.nilCheck ||
      match vy.args[0]? with
      | some q => !ptrShape ((cS).tys[q]?.getD .other) ||
        match H.regs[q]? with
        | some (some z) => ptrOKb z
        | _ => true
      | none => true
    | none => true

theorem nilRegsOK_of {H : Frame} (h : nilRegsB H = true) : NilRegsOK ggTabs ggF H := by
  intro y vy q hy hnc hq hsh z hz
  have hlt : y < ggF.valueTab.size := by
    simp only [Func.value?, Option.join_eq_some_iff] at hy
    exact (Array.getElem?_eq_some_iff.1 hy).1
  have h1 := List.all_eq_true.1 h y (List.mem_range.2 hlt)
  simp only [hy, hnc, Bool.not_true, Bool.false_or, hq, hsh, hz] at h1
  exact ptrOK_of h1

/-- In every prefix of `b1` and of `b9`, every checked register (`v`, `v.Block`, …, once
computed) is not wild. -/
theorem nilPtrs_fact :
    ((List.range (o1.size + 1)).all fun k => match prefixAt (entryFrame env cS args mem) 1 o1 k with
      | some H => nilRegsB H
      | none => true) = true ∧
    ((List.range (o9.size + 1)).all fun k => match prefixAt F9 9 o9 k with
      | some H => nilRegsB H
      | none => true) = true := by
  decide +kernel

/-- **`NilPtrsOK` on `mem`**. -/
theorem ggF_nilPtrsOK : NilPtrsOK ggTabs ggF env args mem := by
  intro fr' b' i' hr
  rcases reach hr with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · intro blk ps o k H hb hps ho hev
    rw [o_eq.1] at ho
    cases ho
    exact nilRegsOK_of (prefix_all nilPtrs_fact.1 hb hps hev)
  · intro blk ps o k H hb hps ho hev
    rw [o_eq.2] at ho
    cases ho
    exact nilRegsOK_of (prefix_all nilPtrs_fact.2 hb hps hev)

/-! ## The hoisted chain on `mem` -/

/-- The 64-bit register word `c`. -/
def wv (c : Nat) : Val := .int .w64 (BitVec.ofNat 64 c)

/-- The register word of `heap n` (its `Fixed` address `(n + 1) * 2^40`). -/
def hw (n : Nat) : Val := wv ((n + 1) * 2 ^ 40)

/-- The register `o` holds `wv c`, computed. -/
def isW (o : Option (Option Val)) (c : Nat) : Bool :=
  match o with
  | some (some (.int .w64 x)) => x == BitVec.ofNat 64 c
  | _ => false

theorem isW_eq {o : Option (Option Val)} {c : Nat} (h : isW o c = true) :
    o = some (some (wv c)) := by
  unfold isW at h
  split at h
  · simp only [beq_iff_eq] at h
    subst h
    rfl
  · cases h

/-- The result `r` is `.ok (wv c)`, computed. -/
def okW (r : Res Val) (c : Nat) : Bool :=
  match r with
  | .ok (.int .w64 x) => x == BitVec.ofNat 64 c
  | _ => false

theorem okW_eq {r : Res Val} {c : Nat} {z : Val} (h : okW r c = true) (hz : r = .ok z) :
    z = wv c := by
  subst hz
  unfold okW at h
  split at h
  · next x hx =>
    cases hx
    simp only [beq_iff_eq] at h
    subst h
    rfl
  · cases h

/-- The result `r` is `.ok`, computed. -/
def isOk (r : Res Val) : Bool :=
  match r with
  | .ok _ => true
  | _ => false

theorem not_ok {r : Res Val} {z : Val} (h : isOk r = false) (hz : r = .ok z) : False := by
  subst hz
  cases h

/-- `schedule`'s evaluation of the value at `a` (its arguments bypassed, `hoisted`) in `G`. -/
def ev (G : Frame) (a : ID) : Res Val :=
  match ggF.value? a with
  | some v => evalValueL mdF env cS G (hoisted ggF v)
  | none => .stuck ""

theorem ev_eq {G : Frame} {a : ID} {va : Value} (hva : ggF.value? a = some va) :
    ev G a = evalValueL mdF env cS G (hoisted ggF va) := by
  unfold ev
  rw [hva]

/-- The arguments of the value at `a`, bypassed. -/
def hargs (a : ID) : Array ID :=
  match ggF.value? a with
  | some v => (hoisted ggF v).args
  | none => #[]

theorem hargs_eq {a : ID} {va : Value} (hva : ggF.value? a = some va) :
    (hoisted ggF va).args = hargs a := by
  unfold hargs
  rw [hva]

/-- The values `schedule` may hoist (`hoistOp`): the loads `v19`, `v25`, `v28`, `v31`, `v34` and
the selections `v42`, `v48`, `v55`, `v58`, with their bypassed arguments. -/
theorem hoistOps_fact :
    (List.range ggF.valueTab.size).all (fun a => match ggF.value? a with
      | some va => !hoistOp va.op || [19, 25, 28, 31, 34, 42, 48, 55, 58].contains a
      | none => true) = true ∧
    hargs 19 = #[48, 1] ∧ hargs 25 = #[6, 1] ∧ hargs 28 = #[25, 1] ∧ hargs 31 = #[28, 1] ∧
      hargs 34 = #[31, 1] ∧ hargs 42 = #[40] ∧ hargs 48 = #[56] ∧ hargs 55 = #[54] ∧
      hargs 58 = #[57] := by
  decide +kernel

/-- Before `v19` in `b9`: `v25` holds `heap 2` and `v48` the nil pointer, and so does their
hoisted evaluation; `v19` (through the nil pointer), `v42`, `v55`, `v58` (whose arguments have no
register) do not evaluate; hoisted, `v28` reads `heap 3`, `v31` reads `heap 4` once `v28` holds
`heap 3`, `v34` reads `heap 5` once `v31` holds `heap 4` (neither evaluates before). -/
theorem hoist_fact :
    (match prefixAt F9 9 o9 1 with
      | some H =>
        isW H.regs[25]? (3 * 2 ^ 40) && okW (ev H 25) (3 * 2 ^ 40) && isW H.regs[48]? 0 &&
          okW (ev H 48) 0 && !isOk (ev H 19) && !isOk (ev H 42) && !isOk (ev H 55) &&
          !isOk (ev H 58) && okW (ev H 28) (4 * 2 ^ 40) && !isOk (ev H 31) && !isOk (ev H 34) &&
          okW (ev (H.set 28 (hw 3)) 31) (5 * 2 ^ 40) &&
          okW (ev (H.set 31 (hw 4)) 34) (6 * 2 ^ 40) && decide (34 < H.regs.size)
      | none => false) = true := by
  decide +kernel

/-- The facts of `hoist_fact`, for a frame `H` before `v19`. -/
structure HoistFacts (H : Frame) : Prop where
  r25 : H.regs[25]? = some (some (hw 2))
  e25 : okW (ev H 25) (3 * 2 ^ 40) = true
  r48 : H.regs[48]? = some (some (wv 0))
  e48 : okW (ev H 48) 0 = true
  e19 : isOk (ev H 19) = false
  e42 : isOk (ev H 42) = false
  e55 : isOk (ev H 55) = false
  e58 : isOk (ev H 58) = false
  e28 : okW (ev H 28) (4 * 2 ^ 40) = true
  e31 : isOk (ev H 31) = false
  e34 : isOk (ev H 34) = false
  e31' : okW (ev (H.set 28 (hw 3)) 31) (5 * 2 ^ 40) = true
  e34' : okW (ev (H.set 31 (hw 4)) 34) (6 * 2 ^ 40) = true
  sz28 : 28 < H.regs.size
  sz31 : 31 < H.regs.size

theorem hoistFacts {H : Frame} (hH : prefixAt F9 9 o9 1 = some H) : HoistFacts H := by
  have hf := hoist_fact
  rw [hH] at hf
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨r25, e25⟩, r48⟩, e48⟩, e19⟩, e42⟩, e55⟩, e58⟩, e28⟩, e31⟩, e34⟩, e31'⟩,
    e34'⟩, sz⟩ := hf
  exact ⟨isW_eq r25, e25, isW_eq r48, e48, e19, e42, e55, e58, e28, e31, e34, e31', e34',
    by omega, by omega⟩

/-- The frames `HoistExt` reaches from `H`: `H`'s registers, but `v28`, `v31`, `v34` may hold
`heap 3`, `heap 4`, `heap 5`. -/
def Inv (H H' : Frame) : Prop :=
  H' = { H with regs := H'.regs } ∧
    (∀ i, i ≠ 28 → i ≠ 31 → i ≠ 34 → H'.regs[i]? = H.regs[i]?) ∧
    (H'.regs[28]? = H.regs[28]? ∨ H'.regs[28]? = some (some (hw 3))) ∧
    (H'.regs[31]? = H.regs[31]? ∨ H'.regs[31]? = some (some (hw 4))) ∧
    (H'.regs[34]? = H.regs[34]? ∨ H'.regs[34]? = some (some (hw 5)))

theorem set_regs (fr : Frame) (a i : ID) (z : Val) :
    (fr.set a z).regs[i]? = fr.regs[i]? ∨ (a = i ∧ (fr.set a z).regs[i]? = some (some z)) := by
  by_cases h : a = i
  · subst h
    by_cases hl : a < fr.regs.size
    · exact .inr ⟨rfl, Frame.set_regs_self hl⟩
    · left
      simp [Frame.set, hl]
  · exact .inl (Frame.set_regs_ne h)

/-- Two frames of `H` that agree on the bypassed arguments of `va` evaluate it alike. -/
theorem ev_congr {H H' G : Frame} {va : Value} (h1 : H' = { H with regs := H'.regs })
    (h2 : G = { H with regs := G.regs })
    (h : ∀ a ∈ (hoisted ggF va).args, H'.regs[a]? = G.regs[a]?) :
    evalValueL mdF env cS H' (hoisted ggF va) = evalValueL mdF env cS G (hoisted ggF va) :=
  evalValueL_congr (by rw [h1]; exact h2) h

/-- In a frame of `Inv`, the value at `a` evaluates (hoisted) as in `G` when `G` and `H'` agree
on its bypassed arguments `as`. -/
theorem ev_of {H H' G : Frame} {a : ID} {va : Value} {as : Array ID} (hI : Inv H H')
    (hva : ggF.value? a = some va) (has : hargs a = as) (hG : G = { H with regs := G.regs })
    (h : ∀ b ∈ as, H'.regs[b]? = G.regs[b]?) :
    evalValueL mdF env cS H' (hoisted ggF va) = ev G a := by
  rw [ev_eq hva]
  refine ev_congr hI.1 hG fun b hb => h b ?_
  rwa [hargs_eq hva, has] at hb

/-- `ev_of` for one bypassed argument `p`. -/
theorem ev_of1 {H H' G : Frame} {a p : ID} {va : Value} (hI : Inv H H')
    (hva : ggF.value? a = some va) (has : hargs a = #[p]) (hG : G = { H with regs := G.regs })
    (hp : H'.regs[p]? = G.regs[p]?) :
    evalValueL mdF env cS H' (hoisted ggF va) = ev G a :=
  ev_of hI hva has hG fun b hb => by
    obtain rfl : b = p := by simpa using hb
    exact hp

/-- `ev_of` for two bypassed arguments `p`, `q`. -/
theorem ev_of2 {H H' G : Frame} {a p q : ID} {va : Value} (hI : Inv H H')
    (hva : ggF.value? a = some va) (has : hargs a = #[p, q])
    (hG : G = { H with regs := G.regs }) (hp : H'.regs[p]? = G.regs[p]?)
    (hq : H'.regs[q]? = G.regs[q]?) :
    evalValueL mdF env cS H' (hoisted ggF va) = ev G a :=
  ev_of hI hva has hG fun b hb => by
    have : b = p ∨ b = q := by simpa using hb
    rcases this with rfl | rfl
    · exact hp
    · exact hq

/-- Setting a register other than `v28`, `v31`, `v34` to the value `H` holds keeps `Inv`. -/
theorem inv_set_same {H H' : Frame} {a : ID} {z : Val} (hI : Inv H H') (h28 : a ≠ 28)
    (h31 : a ≠ 31) (h34 : a ≠ 34) (hz : H.regs[a]? = some (some z)) : Inv H (H'.set a z) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hI
  have hs : ∀ i, i ≠ a → (H'.set a z).regs[i]? = H'.regs[i]? := fun i hi =>
    Frame.set_regs_ne (Ne.symm hi)
  refine ⟨by rw [h1]; rfl, fun i i28 i31 i34 => ?_, by rw [hs 28 (Ne.symm h28)]; exact h3,
    by rw [hs 31 (Ne.symm h31)]; exact h4, by rw [hs 34 (Ne.symm h34)]; exact h5⟩
  rcases set_regs H' a i z with h | ⟨rfl, h⟩
  · rw [h]; exact h2 i i28 i31 i34
  · rw [h, hz]

/-- Setting `v28`, `v31` or `v34` to `heap 3`, `heap 4`, `heap 5` keeps `Inv`. -/
theorem inv_set_chain {H H' : Frame} {a n : Nat} (hI : Inv H H')
    (ha : (a = 28 ∧ n = 3) ∨ (a = 31 ∧ n = 4) ∨ (a = 34 ∧ n = 5)) : Inv H (H'.set a (hw n)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hI
  have hk : ∀ i m, (i = 28 ∧ m = 3) ∨ (i = 31 ∧ m = 4) ∨ (i = 34 ∧ m = 5) →
      (H'.regs[i]? = H.regs[i]? ∨ H'.regs[i]? = some (some (hw m))) →
      ((H'.set a (hw n)).regs[i]? = H.regs[i]? ∨
        (H'.set a (hw n)).regs[i]? = some (some (hw m))) := by
    intro i m him hi
    rcases set_regs H' a i (hw n) with h | ⟨rfl, h⟩
    · rw [h]; exact hi
    · rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        rcases him with ⟨he, rfl⟩ | ⟨he, rfl⟩ | ⟨he, rfl⟩ <;>
        first | (exact .inr h) | (exact absurd he (by decide))
  refine ⟨by rw [h1]; rfl, fun i i28 i31 i34 => ?_, hk 28 3 (.inl ⟨rfl, rfl⟩) h3,
    hk 31 4 (.inr (.inl ⟨rfl, rfl⟩)) h4, hk 34 5 (.inr (.inr ⟨rfl, rfl⟩)) h5⟩
  have hia : a ≠ i := by
    rintro rfl
    rcases ha with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact i28 rfl
    · exact i31 rfl
    · exact i34 rfl
  rw [Frame.set_regs_ne hia]
  exact h2 i i28 i31 i34

/-- **One hoisted value more keeps `Inv`.** -/
theorem inv_step {H H' : Frame} (hH : prefixAt F9 9 o9 1 = some H) (hI : Inv H H') {a : ID}
    {va : Value} {z : Val} (hva : ggF.value? a = some va) (hop : hoistOp va.op = true)
    (hz : evalValueL mdF env cS H' (hoisted ggF va) = .ok z) : Inv H (H'.set a z) := by
  have F := hoistFacts hH
  obtain ⟨hops, a19, a25, a28, a31, a34, a42, a48, a55, a58⟩ := hoistOps_fact
  have ha : a < ggF.valueTab.size := by
    simp only [Func.value?, Option.join_eq_some_iff] at hva
    exact (Array.getElem?_eq_some_iff.1 hva).1
  have hmem := List.all_eq_true.1 hops a (List.mem_range.2 ha)
  simp only [hva, hop, Bool.not_true, Bool.false_or, List.contains_iff_mem, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  -- the registers other than `v28`, `v31`, `v34` are `H`'s
  have same : ∀ b, b ≠ 28 → b ≠ 31 → b ≠ 34 → H'.regs[b]? = H.regs[b]? := hI.2.1
  have h1 : H'.regs[1]? = H.regs[1]? := same 1 (by decide) (by decide) (by decide)
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- `v19`: through the nil pointer
    rw [ev_of2 hI hva a19 rfl (same 48 (by decide) (by decide) (by decide)) h1] at hz
    exact (not_ok F.e19 hz).elim
  · -- `v25`: `heap 2`, as in `H`
    rw [ev_of2 hI hva a25 rfl (same 6 (by decide) (by decide) (by decide)) h1] at hz
    rw [show z = hw 2 from okW_eq F.e25 hz]
    exact inv_set_same hI (by decide) (by decide) (by decide) F.r25
  · -- `v28`: `heap 3`
    rw [ev_of2 hI hva a28 rfl (same 25 (by decide) (by decide) (by decide)) h1] at hz
    rw [show z = hw 3 from okW_eq F.e28 hz]
    exact inv_set_chain hI (.inl ⟨rfl, rfl⟩)
  · -- `v31`: no value while `v28` has none, `heap 4` once `v28` holds `heap 3`
    rcases hI.2.2.1 with h28 | h28
    · rw [ev_of2 hI hva a31 rfl h28 h1] at hz
      exact (not_ok F.e31 hz).elim
    · rw [ev_of2 hI hva a31 (G := H.set 28 (hw 3)) rfl
        (by rw [h28, Frame.set_regs_self F.sz28])
        (by rw [h1, Frame.set_regs_ne (by decide)])] at hz
      rw [show z = hw 4 from okW_eq F.e31' hz]
      exact inv_set_chain hI (.inr (.inl ⟨rfl, rfl⟩))
  · -- `v34`: no value while `v31` has none, `heap 5` once `v31` holds `heap 4`
    rcases hI.2.2.2.1 with h31 | h31
    · rw [ev_of2 hI hva a34 rfl h31 h1] at hz
      exact (not_ok F.e34 hz).elim
    · rw [ev_of2 hI hva a34 (G := H.set 31 (hw 4)) rfl
        (by rw [h31, Frame.set_regs_self F.sz31])
        (by rw [h1, Frame.set_regs_ne (by decide)])] at hz
      rw [show z = hw 5 from okW_eq F.e34' hz]
      exact inv_set_chain hI (.inr (.inr ⟨rfl, rfl⟩))
  · -- `v42`: `v40` has no register
    rw [ev_of1 hI hva a42 rfl (same 40 (by decide) (by decide) (by decide))] at hz
    exact (not_ok F.e42 hz).elim
  · -- `v48`: the nil pointer, as in `H`
    rw [ev_of1 hI hva a48 rfl (same 56 (by decide) (by decide) (by decide))] at hz
    rw [show z = wv 0 from okW_eq F.e48 hz]
    exact inv_set_same hI (by decide) (by decide) (by decide) F.r48
  · -- `v55`: `v54` has no register
    rw [ev_of1 hI hva a55 rfl (same 54 (by decide) (by decide) (by decide))] at hz
    exact (not_ok F.e55 hz).elim
  · -- `v58`: `v57` has no register
    rw [ev_of1 hI hva a58 rfl (same 57 (by decide) (by decide) (by decide))] at hz
    exact (not_ok F.e58 hz).elim

/-- **Every hoisted extension of the frame before `v19` is in `Inv`.** -/
theorem inv_of_ext {H H' : Frame} (hH : prefixAt F9 9 o9 1 = some H)
    (h : HoistExt mdF env ggTabs ggF H H') : Inv H H' := by
  induction h with
  | refl => exact ⟨rfl, fun _ _ _ _ => rfl, .inl rfl, .inl rfl, .inl rfl⟩
  | step _ hva hop hz ih => exact inv_step hH ih hva hop hz

/-- The nil checks `v29`, `v32`, `v35` check `v28`, `v31`, `v34` (their own bypasses), and
`heap 3`, `heap 4`, `heap 5` are not wild. -/
theorem checks_fact :
    ((match ggF.value? 29 with | some v => v.args[0]? == some 28 | none => false) &&
      (match ggF.value? 32 with | some v => v.args[0]? == some 31 | none => false) &&
      (match ggF.value? 35 with | some v => v.args[0]? == some 34 | none => false) &&
      rep ggF 28 == 28 && rep ggF 31 == 31 && rep ggF 34 == 34 &&
      ptrOKb (hw 3) && ptrOKb (hw 4) && ptrOKb (hw 5)) = true := by
  decide +kernel

/-- **`HoistOKAt` before `v19`**: `v28`, `v31`, `v34`, hoisted, read `heap 3`, `heap 4`,
`heap 5` (or do not evaluate) in every hoisted extension of the frame. -/
theorem hoistOKAt {H : Frame} (hH : prefixAt F9 9 o9 1 = some H) {y : ID}
    (hy : y = 29 ∨ y = 32 ∨ y = 35) : HoistOKAt mdF env ggTabs ggF y H := by
  intro H' hext vy q0 vq hvy hq0 hvq z hz
  have hI := inv_of_ext hH hext
  have F := hoistFacts hH
  obtain ⟨-, -, -, a28, a31, a34, -, -, -, -⟩ := hoistOps_fact
  have same : ∀ b, b ≠ 28 → b ≠ 31 → b ≠ 34 → H'.regs[b]? = H.regs[b]? := hI.2.1
  have h1 : H'.regs[1]? = H.regs[1]? := same 1 (by decide) (by decide) (by decide)
  have hc := checks_fact
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨c29, c32⟩, c35⟩, r28⟩, r31⟩, r34⟩, p3⟩, p4⟩, p5⟩ := hc
  rcases hy with rfl | rfl | rfl
  · simp only [hvy, beq_iff_eq] at c29
    rw [c29] at hq0
    cases hq0
    rw [r28] at hvq
    rw [ev_of2 hI hvq a28 rfl (same 25 (by decide) (by decide) (by decide)) h1] at hz
    rw [show z = hw 3 from okW_eq F.e28 hz]
    exact ptrOK_of p3
  · simp only [hvy, beq_iff_eq] at c32
    rw [c32] at hq0
    cases hq0
    rw [r31] at hvq
    rcases hI.2.2.1 with h28 | h28
    · rw [ev_of2 hI hvq a31 rfl h28 h1] at hz
      exact (not_ok F.e31 hz).elim
    · rw [ev_of2 hI hvq a31 (G := H.set 28 (hw 3)) rfl
        (by rw [h28, Frame.set_regs_self F.sz28])
        (by rw [h1, Frame.set_regs_ne (by decide)])] at hz
      rw [show z = hw 4 from okW_eq F.e31' hz]
      exact ptrOK_of p4
  · simp only [hvy, beq_iff_eq] at c35
    rw [c35] at hq0
    cases hq0
    rw [r34] at hvq
    rcases hI.2.2.2.1 with h31 | h31
    · rw [ev_of2 hI hvq a34 rfl h31 h1] at hz
      exact (not_ok F.e34 hz).elim
    · rw [ev_of2 hI hvq a34 (G := H.set 31 (hw 4)) rfl
        (by rw [h31, Frame.set_regs_self F.sz31])
        (by rw [h1, Frame.set_regs_ne (by decide)])] at hz
      rw [show z = hw 5 from okW_eq F.e34' hz]
      exact ptrOK_of p5

/-- The source runs `x` (at `k` in `o`) before `y` (at `i'` in `t`), the target `y` before `x` (at
`j` in `t`), both may fail, and only `hoistSwap` allows the pair (`hoistOnly`), computed. -/
def hoistPair (o t : Array ID) (k i' j : Nat) : Bool :=
  match o.toList[k]?, t.toList[i']?, t.toList[j]? with
  | some x, some y, some x' =>
    x' == x && decide (i' < j) && mayFail ggTabs ggF y && mayFail ggTabs ggF x &&
      decide ((srcPos ggF.valueTab.size o.toList)[x]! < (srcPos ggF.valueTab.size o.toList)[y]!) &&
      hoistOnly ggTabs (cS).params (cS).tys ggF (srcPos ggF.valueTab.size o.toList) x y
  | _, _, _ => false

/-- The pairs that only `hoistSwap` allows: none in `b1`; in `b9` the load `v19` (`k = 1`) and
the nil checks `v29`, `v32`, `v35`. -/
theorem pairs_fact :
    ((List.range o1.size).all fun k => (List.range t1.size).all fun i' =>
      (List.range t1.size).all fun j => !hoistPair o1 t1 k i' j) = true ∧
    ((List.range o9.size).all fun k => (List.range t9.size).all fun i' =>
      (List.range t9.size).all fun j => !hoistPair o9 t9 k i' j ||
        (k == 1 && match t9.toList[i']? with
          | some y => y == 29 || y == 32 || y == 35
          | none => false)) = true := by
  decide +kernel

theorem hoistPair_of {o t : Array ID} {k i' j : Nat} {x y : ID} (hx : o.toList[k]? = some x)
    (hy : t.toList[i']? = some y) (hjx : t.toList[j]? = some x) (hij : i' < j)
    (hfy : mayFail ggTabs ggF y = true) (hfx : mayFail ggTabs ggF x = true)
    (hpos : (srcPos ggF.valueTab.size o.toList)[x]! < (srcPos ggF.valueTab.size o.toList)[y]!)
    (hho : hoistOnly ggTabs (cS).params (cS).tys ggF (srcPos ggF.valueTab.size o.toList) x y =
      true) :
    k < o.size ∧ i' < t.size ∧ j < t.size ∧ hoistPair o t k i' j = true := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using (List.getElem?_eq_some_iff.1 hx).1
  · simpa using (List.getElem?_eq_some_iff.1 hy).1
  · simpa using (List.getElem?_eq_some_iff.1 hjx).1
  · unfold hoistPair
    rw [hx, hy, hjx]
    simp [hfy, hfx, hpos, hho, hij]

/-- **`NilHoistOK` on `mem`** (not vacuous: `hoistNeeded`, `ggS_check`; depth 2, `ggF_depth`):
the hoisted nil checks `v29`, `v32`, `v35` read `v.Block.Func`, `v.Block.Func.OwnAux` and
`v.Block.Func.OwnAux.Fn` before the load `v19` that faults. -/
theorem ggF_nilHoistOK : NilHoistOK ggTabs ggF ggS env args mem := by
  intro fr' b' i' hr
  rcases reach hr with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · intro blk ps oS' oT' k H hb hps hoS hoT hev x y i' j hx hy hjx hij hfy hfx hpos hho
    rw [o_eq.1] at hoS
    cases hoS
    rw [t_eq.1] at hoT
    cases hoT
    obtain ⟨hk, hi, hj, hp⟩ := hoistPair_of hx hy hjx hij hfy hfx hpos hho
    have h1 := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 pairs_fact.1 k
      (List.mem_range.2 hk)) i' (List.mem_range.2 hi)) j (List.mem_range.2 hj)
    simp [hp] at h1
  · intro blk ps oS' oT' k H hb hps hoS hoT hev x y i' j hx hy hjx hij hfy hfx hpos hho
    rw [o_eq.2] at hoS
    cases hoS
    rw [t_eq.2] at hoT
    cases hoT
    obtain ⟨hk, hi, hj, hp⟩ := hoistPair_of hx hy hjx hij hfy hfx hpos hho
    have h1 := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 pairs_fact.2 k
      (List.mem_range.2 hk)) i' (List.mem_range.2 hi)) j (List.mem_range.2 hj)
    rw [hp, hy] at h1
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h1
    obtain ⟨rfl, hy'⟩ := h1
    exact hoistOKAt (prefixAt_of hb hps hev) (or_assoc.1 hy')

/-- **Non-vacuity of `NilHoistOK` on a real function with a chain of depth 2**: `schedule`
outputs section 51 on `rewriteValueAMD64_OpGetG`'s section 50, `scheduleCheck` accepts it with
pairs that only `hoistSwap` allows (`hoistNeeded`), one of them at depth 2 (`ggF_depth`),
`NilHoistOK` holds on `mem` (a nil `v.Args` pointer, `v.Block.Func.OwnAux.Fn` reachable), and by
`schedule_refinesSchedLF` (its premises discharged) the output's `runSched` panics with the nil
dereference of `v.Args[0]`, as the input's `runLF` does before it computes the chain. -/
theorem schedule_hoist_chain_witness :
    ∃ out, schedulePass ggEnv ggF = .ok out ∧ out.func = ggS ∧
      scheduleCheck ggTabs ggF ggS = true ∧ hoistNeeded ggTabs ggF ggS = true ∧
      hoistArg ggF (srcPos ggF.valueTab.size o9.toList) 19 1 32 = false ∧
      NilHoistOK ggTabs ggF ggS env args mem ∧
      (∃ m, runLF env ggTabs ggF args mem 3 = .panicked .nilDeref m) ∧
      ∃ fuel m, runSched env out.tables out.func args mem fuel = .panicked .nilDeref m := by
  obtain ⟨out, hp, hS⟩ := ok_of_toOption (P := fun o => o.func = ggS) ggF_schedule
  obtain ⟨m, hm⟩ := isNilPanic_iff.1 ggF_runLF
  have R := schedule_refinesSchedLF (penv := ggEnv) hp (ok_of_toBool ggF_check)
    (by rw [hS]; exact ggS_check.1)
  obtain ⟨fuel', ho⟩ := R env args mem
    ⟨ggF_argPtrsOK, ggF_nilPtrsOK, by rw [hS]; exact ggF_nilHoistOK⟩ 3
    (by show (runLF env ggTabs ggF args mem 3).Defined; rw [hm]; trivial)
  refine ⟨out, hp, hS, ggS_check.1, ggS_check.2, ggF_depth.1, ggF_nilHoistOK, ⟨m, hm⟩, fuel', ?_⟩
  change OutcomeRefines 0 (runLF env ggTabs ggF args mem 3) _ at ho
  rw [hm] at ho
  generalize runSched env out.tables out.func args mem fuel' = o at ho ⊢
  cases ho with
  | panicked e _ => exact ⟨_, rfl⟩

end GoFV.Proof.Witness.ScheduleHoistChain

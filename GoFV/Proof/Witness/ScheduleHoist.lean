import GoFV.Proof.Pass.SchedLPass
import GoFV.Proof.Witness.ClampL
import GoFV.Proof.Witness.InitF10
import GoFV.Proof.Witness.LowCong
import GoFV.Proof.Witness.Util

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: `NilHoistOK` on a real function (`schedule` hoists a nil check)

`go/parser.(*parser).parseBinaryExpr.func1`, the deferred closure of `parseBinaryExpr`
(`go/parser/parser.go:1882`), which captures `p` and `n` (by reference):

```go
n := 0
defer func() { p.nestLev -= n }()
```

Its section 50 (`layout`, the input of `schedule`) in the corpus
`gofv-corpus/2aae1000ea1d/full-v11/plain` (`stdall/std/go/parser/
%28%2Aparser%29.parseBinaryExpr.func1,1.ssa`), transcribed by hand with the definition tables the
passes and the runs read (`phTabs`): one block, `v10 = LDP [8] v4` loads the captured `p` and `&n`
off the closure pointer `v4`, `v6 = Select0 v10` is `p`, `v8 = Select1 v10` is `&n`, the nil check
`v9` checks `p`, `v12 = MOVDload v8` loads `n`, `v11 = MOVDload [344] v9` loads `p.nestLev`.

`runLF`'s order of `b1` (`Ctx.makeL`'s `kahn` order) is `v4 v1 v10 v8 v12 v6 v9 v11 v13 v16 v17`:
the source loads `n` (`v12`) before it computes `p` (`v6`) and checks it (`v9`). Go's `schedule`
(`schedule.go`, `ScoreNilCheck`: nil checks first) outputs `v4 v1 v10 v8 v6 v9 v11 v12 v13 v16 v17`
(`phS`, section 51): the nil check `v9` of `p` runs before the load `v12`. When `&n` is nil the
source panics at `v12` and never computes `p`, so the target's nil check reads a pointer the source
never evaluates: no case of `swapOK` but `hoistSwap` allows the swap (`hoistNeeded`), and
`schedule_refinesSchedLF` assumes `NilHoistOK` of the input.

On the input `mem` (the closure object `heap 1` holds the code pointer, `p` = the parser object
`heap 2`, and a nil `&n`), `NilHoistOK` holds (`phF_nilHoistOK`): the only state where a hoisted
nil check applies is before `v12` (`pairs_fact`), where `p`, `Select0` of `v10`'s register,
evaluates to the parser object, not wild, and stays so when other hoistable values are evaluated
first (`HoistExt` never sets `v10`, an `LDP`). `NilPtrsOK` holds as well (`phF_nilPtrsOK`: every
checked register read in any prefix of the run is that pointer). Then `schedule_refinesSchedLF`
applies and the output's `runSched` panics with the nil dereference as the input's `runLF` does
(`schedule_hoist_witness`).

All facts by kernel evaluation (`decide +kernel`).
-/

namespace GoFV.Proof.Witness.ScheduleHoist

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.ScheduleCheck GoFV.Proof GoFV.Proof.SchedL
open GoFV.Proof.Witness (pos p0 mkVI mkB mkTy ok_of_toOption ok_of_toBool)

/-! ## The function -/

private def fld (name : String) (t : TypeRef) (off : Int) : Field :=
  { name := GoStr.ofString name, type := t, offset := some off, embedded := false }

/-- `go/parser.parser`: its size and fields (`t35`; the fields' types are not read). -/
def parserTy : TypeDef :=
  mkTy .STRUCT (some 352) (some 8) (some 328) true false false true "parser" "go/parser.parser"
    (.struct #[fld "file" 36 0, fld "errors" 44 8, fld "scanner" 48 32, fld "mode" 55 168,
      fld "trace" 2 176, fld "indent" 11 184, fld "comments" 56 192, fld "leadComment" 57 216,
      fld "lineComment" 57 224, fld "top" 2 232, fld "goVersion" 16 240, fld "pos" 54 256,
      fld "tok" 62 264, fld "lit" 16 272, fld "syncPos" 54 288, fld "syncCnt" 11 296,
      fld "exprLev" 11 304, fld "inRhs" 2 312, fld "imports" 63 320, fld "nestLev" 11 344])

/-- The definition tables of section 50 that `schedule`, `check` and the runs read: the types of
the values (and the element types of their pointers), the function's auxes and its slots. -/
def phTabs : Tables where
  types :=
    let t := Array.replicate 76 (none : Option TypeDef)
    let t := t.set! 1 (some (mkTy .FUNC (some 8) (some 8) (some 8) true true false false
      "func()" "func()" (.func 0 0 0 #[])))
    let t := t.set! 7 (some (mkTy .UINT8 (some 1) (some 1) (some 0) false false true true
      "uint8" "uint8"))
    let t := t.set! 11 (some (mkTy .INT (some 8) (some 8) (some 0) false false true true
      "int" "int"))
    let t := t.set! 17 (some (mkTy .PTR (some 8) (some 8) (some 8) true true true false
      "*uint8" "*uint8" (.elem 7)))
    let t := t.set! 20 (some (mkTy .PTR (some 8) (some 8) (some 8) true true true false
      "*int" "*int" (.elem 11)))
    let t := t.set! 28 (some (mkTy .SSA none none none false false false false "mem" ""))
    let t := t.set! 30 (some (mkTy .SSA none none none false false false false "void" ""))
    let t := t.set! 32 (some (mkTy .RESULTS none none none false false false false "mem" ""
      (.results #[28])))
    let t := t.set! 34 (some (mkTy .PTR (some 8) (some 8) (some 8) true true true false
      "*parser" "*go/parser.parser" (.elem 35)))
    let t := t.set! 35 (some parserTy)
    t.set! 75 (some (mkTy .TUPLE none none none false false false false "*parser,*int" ""
      (.tuple 34 20)))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{go/parser.(*parser).parseBinaryExpr.func1}",
           kind := .call (some 2) (some
             { abi := 1, nin := 0, nout := 0, spillOff := 8, spillSize := 0, inRegs := 0,
               outRegs := 0, params := #[] }) },
    some { fmt := GoStr.ofString "go/parser.(*parser).parseBinaryExpr.func1",
           kind := (.sym (GoStr.ofString "go/parser.(*parser).parseBinaryExpr.func1") 1 "-" 0
             default none none none #[] none) },
    some { fmt := GoStr.ofString "int", kind := .type 11 },
    some { fmt := GoStr.ofString "p",
           kind := .name (GoStr.ofString "p") .PAUTO 34 0 0 { used := true } (pos 2 1882 17 0) },
    some { fmt := GoStr.ofString "&n",
           kind := .name (GoStr.ofString "&n") .PAUTO 20 0 0 { used := true } (pos 2 1882 8 0) }]
  slots := #[none,
    some { name := 4, type := 34, off := 0, splitOf := none, splitOffset := 0 },
    some { name := 5, type := 20, off := 0, splitOf := none, splitOffset := 0 }]

/-- The SSA pseudo-types (`typs` of the export). -/
def phTyps : Array (String × TypeRef) :=
  #[("Bool", 2), ("Int8", 3), ("Int16", 4), ("Int32", 5), ("Int64", 6), ("UInt8", 7),
    ("UInt16", 8), ("UInt32", 9), ("UInt64", 10), ("Int", 11), ("Float32", 12), ("Float64", 13),
    ("UInt", 14), ("Uintptr", 15), ("String", 16), ("BytePtr", 17), ("Int32Ptr", 18),
    ("UInt32Ptr", 19), ("IntPtr", 20), ("UintptrPtr", 21), ("Float32Ptr", 22), ("Float64Ptr", 23),
    ("BytePtrPtr", 24), ("Complex64", 25), ("Complex128", 26), ("UnsafePtr", 27), ("Mem", 28),
    ("Flags", 29), ("Void", 30), ("Int128", 31), ("ResultMem", 32)]

/-- `v6 = Select0 v10`: the captured `p`. -/
def v6 : Value := mkVI 6 .Select0 34 0 none (pos 2 1882 8 1) 1 #[10] 1

/-- `v9 = LoweredNilCheck v6 v1`: the nil check of `p`. -/
def v9 : Value := mkVI 9 .ARM64LoweredNilCheck 34 0 none (pos 2 1882 18 0) 2 #[6, 1] 1

/-- `v10 = LDP [8] v4 v1`: the captured `p` and `&n`. -/
def v10 : Value := mkVI 10 .ARM64LDP 75 8 none (pos 2 1882 8 1) 2 #[4, 1] 1

/-- The values of section 50, by ID. -/
def phValues : Array (Option Value) := #[none,
  some (mkVI 1 .InitMem 28 0 none p0 5 #[] 1),
  none, none,
  some (mkVI 4 .ARM64LoweredGetClosurePtr 17 0 none p0 1 #[] 1),
  none,
  some v6,
  none,
  some (mkVI 8 .Select1 20 0 none (pos 2 1882 8 0) 1 #[10] 1),
  some v9,
  some v10,
  some (mkVI 11 .ARM64MOVDload 11 344 none (pos 2 1882 18 0) 1 #[9, 1] 1),
  some (mkVI 12 .ARM64MOVDload 11 0 none (pos 2 1882 27 0) 1 #[8, 1] 1),
  some (mkVI 13 .ARM64SUB 11 0 none (pos 2 1882 27 0) 1 #[11, 12] 1),
  none, none,
  some (mkVI 16 .ARM64MOVDstore 28 344 none (pos 2 1882 27 0) 1 #[9, 13, 1] 1),
  some (mkVI 17 .MakeResult 32 0 none (pos 2 1882 32 0) 1 #[16] 1)]

/-- `b1` of section 50. -/
def phB1 : Block :=
  mkB 1 .Ret (pos 2 1882 32 0) #[17] #[] #[] #[1, 4, 6, 8, 9, 12, 11, 13, 16, 17, 10]

/-- The caches of sections 50 and 51. -/
def phCache : Caches :=
  { postorder := some #[1], idom := some #[none, none],
    sdom := some #[{ parent := none, child := none, sibling := none, entry := 0, exit := 0 },
      { parent := none, child := none, sibling := none, entry := 2, exit := 5 }],
    loopnest := some { b2lSize := 2, irreducible := false, loops := #[], b2l := #[] },
    auxmap := some #[(none, 1)],
    lineStarts := some #[{ index := 2, bounds := some (1882, 1882), pending := #[] }] }

/-- `(*parser).parseBinaryExpr.func1`, section 50 (`layout`). -/
def phF : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 17
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some phB1]
  valueTab := phValues
  names := #[(1, #[6]), (2, #[8])]
  namedx := #[]
  splits := #[]
  canon := #[({ name := 4, type := 34, off := 0, splitOf := none, splitOffset := 0 }, 1),
    ({ name := 5, type := 20, off := 0, splitOf := none, splitOffset := 0 }, 2)]
  consts := #[]
  freeValues := [7, 5, 15, 14, 3, 2]
  freeBlocks := []
  cache := phCache
  low := { laidout := true }

/-- Section 51 (`schedule`): `b1` lists `v4 v1 v10 v8 v6 v9 v11 v12 v13 v16 v17`, the nil check
`v9` is `void` and unused, `v11` and `v16` read `v6` (the nil check's pointer). -/
def phS : Func :=
  { phF with
    blockTab := #[none,
      some (mkB 1 .Ret (pos 2 1882 32 0) #[17] #[] #[] #[4, 1, 10, 8, 6, 9, 11, 12, 13, 16, 17])]
    valueTab := ((((phValues.set! 6 (some (mkVI 6 .Select0 34 0 none (pos 2 1882 8 1) 3 #[10] 1))).set!
      9 (some (mkVI 9 .ARM64LoweredNilCheck 30 0 none (pos 2 1882 18 0) 0 #[6, 1] 1))).set!
      11 (some (mkVI 11 .ARM64MOVDload 11 344 none (pos 2 1882 18 0) 1 #[6, 1] 1))).set!
      16 (some (mkVI 16 .ARM64MOVDstore 28 344 none (pos 2 1882 27 0) 1 #[6, 13, 1] 1)))
    low := { scheduled := true, laidout := true } }

/-- The pass environment of `schedule` on section 50. -/
def phEnv : PassEnv where
  passName := "schedule"
  pkg := GoStr.ofString "go/parser"
  funcName := GoStr.ofString "(*parser).parseBinaryExpr.func1"
  abi := 1
  nosplit := false
  pgohot := false
  config := #[("arch", #[.word "arm64"]), ("hasgreg", #[.word "1"]), ("optimize", #[.word "1"])]
  typs := phTyps
  typeOrder := default
  tables := phTabs

def phCheckEnv : CheckEnv := { tabs := phTabs, typs := phTyps }

theorem phF_check : (check phCheckEnv phF).toBool = true := by decide +kernel

/-- `schedule` outputs section 51 on section 50. -/
theorem phF_schedule :
    ((schedulePass phEnv phF).toOption.map fun o => decide (o.func = phS)) = some true := by
  decide +kernel

/-- `scheduleCheck` accepts the scheduling, and only through `hoistSwap` (`hoistNeeded`). -/
theorem phS_check : scheduleCheck phTabs phF phS = true ∧ hoistNeeded phTabs phF phS = true := by
  decide +kernel

/-! ## The input -/

/-- The closure object `heap 1`. -/
def cloP : Ptr := ⟨.heap 1, 0⟩

/-- The parser object `heap 2`. -/
def parP : Ptr := ⟨.heap 2, 0⟩

/-- The closure's code pointer. -/
def codeP : Ptr := ⟨.global "go/parser.(*parser).parseBinaryExpr.func1", 0⟩

/-- The eight bytes of pointer `p`. -/
def frags (p : Ptr) : Array Byte := #[.frag p 0, .frag p 1, .frag p 2, .frag p 3, .frag p 4,
  .frag p 5, .frag p 6, .frag p 7]

/-- The input memory: the closure object (the code pointer, `p` = the parser object, a nil `&n`)
and the parser object (`nestLev = 3`). -/
def mem : Mem :=
  { blocks := #[(.heap 1, { data := frags codeP ++ frags parP ++ Array.replicate 8 (.b 0) }),
      (.heap 2, { data := Array.replicate 344 (.b 0) ++ #[.b 3, .b 0, .b 0, .b 0, .b 0, .b 0,
        .b 0, .b 0] })],
    nextHeap := 3 }

/-- The environment: the closure context is the closure object. -/
def env : Env := { Env.p1 with closure := some (.ptr cloP) }

/-- The outcome panics with a nil dereference. -/
def isNilPanic : Outcome → Bool
  | .panicked .nilDeref _ => true
  | _ => false

theorem isNilPanic_iff {o : Outcome} : isNilPanic o = true ↔ ∃ m, o = .panicked .nilDeref m := by
  constructor
  · intro h
    match o, h with
    | .panicked .nilDeref m, _ => exact ⟨m, rfl⟩
  · rintro ⟨m, rfl⟩
    rfl

/-- The input's `runLF` panics at `v12` (the load of the nil `&n`). -/
theorem phF_runLF : isNilPanic (runLF env phTabs phF [] mem 3) = true := by decide +kernel

/-- No value of `phF` is a pointer-shaped register piece of a parameter (it has no parameter). -/
theorem phF_noArgPtr :
    (List.range phF.valueTab.size).all
      (fun x => !argPtr phTabs (Ctx.makeL phTabs phF).params (Ctx.makeL phTabs phF).tys phF x) =
      true := by
  decide +kernel

/-- `ArgPtrsOK` on `mem`: no parameter piece, and the closure context is the closure object. -/
theorem phF_argPtrsOK : ArgPtrsOK phTabs phF env [] mem := by
  refine argPtrsOK_of_none phF_noArgPtr env [] mem ?_
  rintro c h ⟨b, hb, hnil⟩
  cases h
  simp only [cloP, Arm64.addr, Option.some.injEq] at hb
  subst hb
  simp [Ptr.isNil, Ptr.add] at hnil

/-! ## The checked and the hoisted pointers on `mem` -/

/-- `runLF`'s order of `b1` (`Ctx.makeL`). -/
def oS : Array ID := #[4, 1, 10, 8, 12, 6, 9, 11, 13, 16, 17]

/-- `runSched`'s order of `b1` in `phS` (`Ctx.makeSched`). -/
def oT : Array ID := #[4, 1, 10, 8, 6, 9, 11, 12, 13, 16, 17]

theorem oS_eq : ((Ctx.makeL phTabs phF).sched[1]?).join = some oS := by decide +kernel

theorem oT_eq : ((Ctx.makeSched phTabs phS).sched[1]?).join = some oT := by decide +kernel

/-- A block step that does not continue along an edge. -/
def notGoto : Step → Bool
  | .goto .. => false
  | _ => true

/-- `b1` is a `Ret` block: `runLF`'s block step from the entry does not continue along an edge. -/
theorem entry_noGoto :
    notGoto (blockStepL ⟨phF.lowered, true⟩ env (Ctx.makeL phTabs phF)
      (entryFrame env (Ctx.makeL phTabs phF) [] mem) 1 0) = true := by
  decide +kernel

/-- The only block entry `runLF` reaches on `mem` is the function's entry. -/
theorem reach_entry {fr : Frame} {b : ID} {i : Nat}
    (h : ReachL ⟨phF.lowered, true⟩ env (Ctx.makeL phTabs phF)
      (entryFrame env (Ctx.makeL phTabs phF) [] mem) 1 0 fr b i) :
    fr = entryFrame env (Ctx.makeL phTabs phF) [] mem ∧ b = 1 ∧ i = 0 := by
  cases h with
  | refl => exact ⟨rfl, rfl, rfl⟩
  | step hs _ =>
    have h1 := entry_noGoto
    rw [hs] at h1
    cases h1

/-- The frame after `b1`'s `Phi`s (it has none) and the first `k` values of `oS`, if they
evaluate. -/
def prefixAt (k : Nat) : Option Frame :=
  match phB1.values.toList.filterMapM
      (phiStepL ⟨phF.lowered, true⟩ (Ctx.makeL phTabs phF)
        (entryFrame env (Ctx.makeL phTabs phF) [] mem) 0) with
  | .ok ps =>
    match evalAllL ⟨phF.lowered, true⟩ env (Ctx.makeL phTabs phF)
        { entryFrame env (Ctx.makeL phTabs phF) [] mem with
          regs := setPhis ps (entryFrame env (Ctx.makeL phTabs phF) [] mem).regs }
        (oS.toList.take k) with
    | .ok H => some H
    | _ => none
  | _ => none

theorem prefixAt_of {ps : List (ID × Val)} {k : Nat} {H : Frame}
    (hps : phB1.values.toList.filterMapM
      (phiStepL ⟨phF.lowered, true⟩ (Ctx.makeL phTabs phF)
        (entryFrame env (Ctx.makeL phTabs phF) [] mem) 0) = .ok ps)
    (hev : evalAllL ⟨phF.lowered, true⟩ env (Ctx.makeL phTabs phF)
        { entryFrame env (Ctx.makeL phTabs phF) [] mem with
          regs := setPhis ps (entryFrame env (Ctx.makeL phTabs phF) [] mem).regs }
        (oS.toList.take k) = .ok H) :
    prefixAt k = some H := by
  unfold prefixAt
  rw [hps]
  simp only [hev]

/-- `PtrOK`, computed. -/
def ptrOKb (z : Val) : Bool :=
  match z.asPtrWord with
  | some p => !p.wild
  | none => false

theorem ptrOK_of {z : Val} (h : ptrOKb z = true) : PtrOK z := by
  unfold ptrOKb at h
  split at h
  · next p hp => exact ⟨p, hp, by simpa using h⟩
  · cases h

/-- `NilRegsOK`, computed. -/
def nilRegsB (H : Frame) : Bool :=
  (List.range phF.valueTab.size).all fun y =>
    match phF.value? y with
    | some vy => !vy.op.nilCheck ||
      match vy.args[0]? with
      | some q => !ptrShape ((Ctx.makeL phTabs phF).tys[q]?.getD .other) ||
        match H.regs[q]? with
        | some (some z) => ptrOKb z
        | _ => true
      | none => true
    | none => true

theorem nilRegsOK_of {H : Frame} (h : nilRegsB H = true) : NilRegsOK phTabs phF H := by
  intro y vy q hy hnc hq hsh z hz
  have hlt : y < phF.valueTab.size := by
    simp only [Func.value?, Option.join_eq_some_iff] at hy
    exact (Array.getElem?_eq_some_iff.1 hy).1
  have h1 := List.all_eq_true.1 h y (List.mem_range.2 hlt)
  simp only [hy, hnc, Bool.not_true, Bool.false_or, hq, hsh, hz] at h1
  exact ptrOK_of h1

/-- In every prefix of the run, the checked register (`p`, once computed) is not wild. -/
theorem nilPtrs_fact :
    (List.range 12).all (fun k => match prefixAt k with
      | some H => nilRegsB H
      | none => true) = true := by
  decide +kernel

/-- **`NilPtrsOK` on `mem`**. -/
theorem phF_nilPtrsOK : NilPtrsOK phTabs phF env [] mem := by
  intro fr' b' i' hr
  obtain ⟨rfl, rfl, rfl⟩ := reach_entry hr
  intro blk ps o k H hb hps ho hev
  rw [show phF.block? 1 = some phB1 from rfl] at hb
  cases hb
  rw [oS_eq] at ho
  cases ho
  apply nilRegsOK_of
  by_cases hk : k < 12
  · have h1 := List.all_eq_true.1 nilPtrs_fact k (List.mem_range.2 hk)
    rw [prefixAt_of hps hev] at h1
    exact h1
  · have ht : ∀ k', 11 ≤ k' → oS.toList.take k' = oS.toList := fun k' h' =>
      List.take_of_length_le (by simp [oS]; omega)
    rw [ht k (by omega), ← ht 11 (Nat.le_refl 11)] at hev
    have h1 := List.all_eq_true.1 nilPtrs_fact 11 (List.mem_range.2 (by omega))
    rw [prefixAt_of hps hev] at h1
    exact h1

/-- The pairs `(x, y)` (`x` at `k` in `oS`, `y` at `i'` in `oT`) that only `hoistSwap` allows:
only the load `v12` (`k = 4`) and the nil check `v9`. -/
theorem pairs_fact :
    (List.range 11).all (fun k => (List.range 11).all fun i' =>
      match oS.toList[k]?, oT.toList[i']? with
      | some x, some y =>
        !(mayFail phTabs phF y && mayFail phTabs phF x &&
          decide ((srcPos phF.valueTab.size oS.toList)[x]! <
            (srcPos phF.valueTab.size oS.toList)[y]!) &&
          hoistOnly phTabs (Ctx.makeL phTabs phF).params (Ctx.makeL phTabs phF).tys phF
            (srcPos phF.valueTab.size oS.toList) x y) || (k == 4 && y == 9)
      | _, _ => true) = true := by
  decide +kernel

/-- Before `v12`: `p` (`v6`, hoisted) evaluates to a pointer that is not wild, and `v10` has a
register. -/
theorem hoist_fact :
    (match prefixAt 4 with
      | some H =>
        (match evalValueL ⟨phF.lowered, true⟩ env (Ctx.makeL phTabs phF) H (hoisted phF v6) with
          | .ok z => ptrOKb z
          | _ => false) && (H.regs[10]?).join.isSome
      | none => false) = true := by
  decide +kernel

/-- Extending a frame by hoisted values (`HoistExt`) keeps `v10`'s register (an `LDP` is no
`hoistOp`) and every field but the registers. -/
theorem hoistExt_regs {H H' : Frame}
    (h : HoistExt ⟨phF.lowered, true⟩ env phTabs phF H H') :
    H'.regs[10]? = H.regs[10]? ∧ H' = { H with regs := H'.regs } := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | @step H' a va z _ hva hop _ ih =>
    have ha : a ≠ 10 := by
      rintro rfl
      rw [show phF.value? 10 = some v10 from rfl] at hva
      cases hva
      exact absurd hop (by decide)
    refine ⟨?_, ?_⟩
    · simp only [Frame.set, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, ha,
        ite_false]
      exact ih.1
    · simp only [Frame.set]
      rw [ih.2]

/-- **`HoistOKAt` before `v12`**: `p`, hoisted, is not wild in every hoisted extension of the
frame. -/
theorem hoistOKAt {H : Frame} (hH : prefixAt 4 = some H) :
    HoistOKAt ⟨phF.lowered, true⟩ env phTabs phF 9 H := by
  have hf := hoist_fact
  rw [hH] at hf
  simp only [Bool.and_eq_true] at hf
  obtain ⟨hz0, hreg⟩ := hf
  obtain ⟨y10, hy10⟩ : ∃ y, H.regs[10]? = some (some y) := by
    revert hreg
    cases H.regs[10]? with
    | none => intro h; cases h
    | some o =>
      cases o with
      | none => intro h; cases h
      | some y => intro _; exact ⟨y, rfl⟩
  intro H' hext vy q0 vq hvy hq0 hvq z hz
  rw [show phF.value? 9 = some v9 from rfl] at hvy
  cases hvy
  rw [show v9.args[0]? = some 6 from rfl] at hq0
  cases hq0
  rw [show rep phF 6 = 6 by decide +kernel, show phF.value? 6 = some v6 from rfl] at hvq
  cases hvq
  obtain ⟨hr10, hfr⟩ := hoistExt_regs hext
  have hha : (hoisted phF v6).args = #[10] := by decide +kernel
  obtain ⟨y', hy', heq⟩ := (evalValueL_vc (ctx' := Ctx.makeL phTabs phF) (fr' := H)
    (v' := hoisted phF v6) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by rw [hfr]) (Or.inl rfl)
    (fun k a hk => by
      have ha : a = 10 := by
        rw [hha] at hk
        rcases k with _ | k
        · simpa using hk.symm
        · simp at hk
      subst ha
      exact ⟨10, y10, hk, by rw [hr10, hy10], y10, hy10, Or.inl rfl⟩)).1 z hz
  obtain rfl := heq rfl
  rw [hy'] at hz0
  exact ptrOK_of hz0

/-- **`NilHoistOK` on `mem`** (not vacuous: `hoistNeeded`, `phS_check`): the hoisted nil check
`v9` reads `p`, the parser object, before the load `v12` that faults. -/
theorem phF_nilHoistOK : NilHoistOK phTabs phF phS env [] mem := by
  intro fr' b' i' hr
  obtain ⟨rfl, rfl, rfl⟩ := reach_entry hr
  intro blk ps oS' oT' k H hb hps hoS hoT hev x y i' j hx hy _ _ hfy hfx hpos hho
  rw [show phF.block? 1 = some phB1 from rfl] at hb
  cases hb
  rw [oS_eq] at hoS
  cases hoS
  rw [oT_eq] at hoT
  cases hoT
  have hk : k < 11 := by
    have := (List.getElem?_eq_some_iff.1 hx).1
    simpa [oS] using this
  have hi : i' < 11 := by
    have := (List.getElem?_eq_some_iff.1 hy).1
    simpa [oT] using this
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 pairs_fact k (List.mem_range.2 hk)) i'
    (List.mem_range.2 hi)
  rw [hx, hy] at h1
  simp only [hfy, hfx, hpos, hho, decide_true, Bool.and_self, Bool.not_true, Bool.false_or,
    Bool.and_eq_true, beq_iff_eq] at h1
  obtain ⟨rfl, rfl⟩ := h1
  exact hoistOKAt (prefixAt_of hps hev)

/-- **Non-vacuity of `NilHoistOK` on a real function**: `schedule` outputs section 51 on
`(*parser).parseBinaryExpr.func1`'s section 50, `scheduleCheck` accepts it only through
`hoistSwap` (`hoistNeeded`), `NilHoistOK` holds on `mem` (a nil `&n`, `p` the parser object), and
by `schedule_refinesSchedLF` (its premises discharged) the output's `runSched` panics with the nil
dereference of `n`, as the input's `runLF` does before it computes `p`. -/
theorem schedule_hoist_witness :
    ∃ out, schedulePass phEnv phF = .ok out ∧ out.func = phS ∧
      scheduleCheck phTabs phF phS = true ∧ hoistNeeded phTabs phF phS = true ∧
      NilHoistOK phTabs phF phS env [] mem ∧
      (∃ m, runLF env phTabs phF [] mem 3 = .panicked .nilDeref m) ∧
      ∃ fuel m, runSched env out.tables out.func [] mem fuel = .panicked .nilDeref m := by
  obtain ⟨out, hp, hS⟩ := ok_of_toOption (P := fun o => o.func = phS) phF_schedule
  obtain ⟨m, hm⟩ := isNilPanic_iff.1 phF_runLF
  have R := schedule_refinesSchedLF (penv := phEnv) hp (ok_of_toBool phF_check)
    (by rw [hS]; exact phS_check.1)
  obtain ⟨fuel', ho⟩ := R env [] mem
    ⟨phF_argPtrsOK, phF_nilPtrsOK, by rw [hS]; exact phF_nilHoistOK⟩ 3
    (by show (runLF env phTabs phF [] mem 3).Defined; rw [hm]; trivial)
  refine ⟨out, hp, hS, phS_check.1, phS_check.2, phF_nilHoistOK, ⟨m, hm⟩, fuel', ?_⟩
  change OutcomeRefines 0 (runLF env phTabs phF [] mem 3) _ at ho
  rw [hm] at ho
  generalize runSched env out.tables out.func [] mem fuel' = o at ho ⊢
  cases ho with
  | panicked e _ => exact ⟨_, rfl⟩

end GoFV.Proof.Witness.ScheduleHoist

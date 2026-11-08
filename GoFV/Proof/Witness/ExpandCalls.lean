import GoFV.Proof.Pass.ECMain
import GoFV.Proof.Witness.SumOfInt
import GoFV.Proof.Witness.HasWaitingReaders
import GoFV.Proof.Witness.StackF2
import GoFV.Proof.Witness.UuidNew
import GoFV.Proof.PtrAddr
import GoFV.Proof.Witness.Util

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witnesses: expand calls on `sumOf[int]` and `syscall_hasWaitingReaders`

expand calls lowers `sumOf[int]`'s slice parameter (`Arg` `v6` becomes a `SliceMake` of three
`ArgIntReg`s) and its call `v9` of `sumOf[go.shape.int]` (`StaticLECall` becomes `StaticCall`
with the slice's three words as register arguments). In the ABI0 wrapper
`syscall_hasWaitingReaders` (a stack-assigned result, issue #28) it stores the result into its
frame slot (`v2 = Store {bool} (LocalAddr {~r0}) v10 v9`) and returns only the memory
(`v11 = MakeResult v2`). By kernel evaluation: the pass succeeds, the input and the output (in
the output's tables) pass `check`, and the input is in `expandCallsFrag` (the output's tables
agree with the input's and `ECCheck.ecCheck` accepts the output), so `expandCalls_refines`
applies; its contracts' condition holds for `Env.p1` (`Env.p1_mono`, `Env.p1_frameKeep`). A
synthetic call with two wide stack arguments, each copied by its own `Move` (the upper one reading
a frame variable), is accepted by `ECCheck.ecCheck`, and `EC.ecm_moves` reads both slots back on
concrete memories. A two-block variant of `test/stack` `f2` whose invalidated self-move
`Dereference` the target schedules after its `MakeResult`, with an unused `Mul64uhilo` (a tuple
of integers), is accepted and refines its source.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof GoFV.Proof.AtomSim

/-- `check`'s environment for the pass output (in the output's tables). -/
def sumOfOutCheckEnv (o : PassOut) : CheckEnv := { tabs := o.tables, typs := sumOfTyps }

/-! ## Certificates (kernel evaluation) -/

theorem sumOf_checks :
    (check sumOfCheckEnv sumOf).toBool = true ∧ expandCallsFrag sumOfPassEnv sumOf = true ∧
      (sumOf.value? 9).map (·.op) = some .StaticLECall := by
  decide +kernel

theorem sumOf_pass :
    ((expandCallsPass sumOfPassEnv sumOf).toOption.map fun o =>
      (check (sumOfOutCheckEnv o) o.func).toBool &&
        (o.func.value? 9).map (·.op) == some .StaticCall) = some true := by
  decide +kernel

/-! ## The witness -/

/-- **Non-vacuity of `expandCalls_refines`**: expand calls lowers `sumOf[int]`'s call `v9`
(`StaticLECall` to `StaticCall`), and the output refines the input. -/
theorem expandCalls_witness :
    ∃ out, expandCallsPass sumOfPassEnv sumOf = .ok out ∧
      (sumOf.value? 9).map (·.op) = some .StaticLECall ∧
      (out.func.value? 9).map (·.op) = some .StaticCall ∧
      RefinesUnder (fun env => env.Mono ∧ env.FrameKeep) out.tables out.func sumOfPassEnv.tables
        sumOf := by
  obtain ⟨hc, hfrag, hle⟩ := sumOf_checks
  have hp := sumOf_pass
  cases hpe : expandCallsPass sumOfPassEnv sumOf with
  | error e => rw [hpe] at hp; cases hp
  | ok out =>
    rw [hpe] at hp
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Bool.and_eq_true,
      beq_iff_eq] at hp
    obtain ⟨hcg, hcall⟩ := hp
    exact ⟨out, rfl, hle, hcall,
      GoFV.Proof.EC.expandCalls_refines hpe (ok_of_toBool hc) (ok_of_toBool hcg) hfrag⟩

/-! ## Non-vacuity of the call-argument lemmas (#28) -/

/-- `ecc_ofPieces_arg` at a pointer argument of a `uintptr` parameter (`castOK`): the decoded
argument refines the pointer retyped at the parameter's shape (a global pointer, which has no
address and so stays a pointer in an integer register). -/
theorem expandCalls_castArg_witness :
    Sem.Refines ((Val.ptr ⟨.global "g", 8⟩).retype (.int .w64))
      (ofPieces (.int .w64) [.ptr ⟨.global "g", 8⟩]) :=
  GoFV.Proof.EC.ecc_ofPieces_arg rfl (.inr ⟨rfl, none, rfl⟩) (.cons (Sem.Refines.refl _) .nil)

/-- `ecs_decode_hasTy_mov` at a blob (a `Move`-copied `[2]byte` stack argument). -/
theorem expandCalls_movTy_witness : (decode #[.b 1, .b 2] 0 (.blob 2)).hasTy (.blob 2) = true :=
  GoFV.Proof.EC.ecs_decode_hasTy_mov (.blob 2) _ 0 rfl (by decide)

/-- `ecc_hasPoison_retype` at an aggregate with a `poison` field. -/
theorem expandCalls_poisonArg_witness :
    ((Val.agg [.poison]).retype (.agg [(0, .int .w64)] 8)).hasPoison = true :=
  GoFV.Proof.EC.ecc_hasPoison_retype _ _ rfl

/-! ## A stack-assigned result -/

/-- `check`'s environment for the pass output of `syscall_hasWaitingReaders`. -/
def hwrOutCheckEnv (o : PassOut) : CheckEnv := { tabs := o.tables, typs := hwrTyps }

theorem hwr_checks :
    (check hwrCheckEnv hwr).toBool = true ∧ expandCallsFrag hwrPassEnv hwr = true ∧
      (hwr.value? 11).map (·.args) = some #[10, 9] := by
  decide +kernel

theorem hwr_pass :
    ((expandCallsPass hwrPassEnv hwr).toOption.map fun o =>
      (check (hwrOutCheckEnv o) o.func).toBool &&
        (o.func.value? 2).map (·.op) == some .Store &&
        (o.func.value? 11).map (·.args) == some #[2]) = some true := by
  decide +kernel

/-- **Non-vacuity of `expandCalls_refines` on a stack-assigned result**: expand calls stores
`syscall_hasWaitingReaders`'s result (`MakeResult v10 v9`) into its frame slot (the `Store` `v2`,
returned as `MakeResult v2`), the output refines the input under monotone contracts that keep
the caller's frame, and `Env.p1` satisfies that condition. -/
theorem expandCalls_stack_witness :
    ∃ out, expandCallsPass hwrPassEnv hwr = .ok out ∧
      (hwr.value? 11).map (·.args) = some #[10, 9] ∧
      (out.func.value? 2).map (·.op) = some .Store ∧ (out.func.value? 11).map (·.args) = some #[2] ∧
      RefinesUnder (fun env => env.Mono ∧ env.FrameKeep) out.tables out.func hwrPassEnv.tables
        hwr ∧ (Env.p1.Mono ∧ Env.p1.FrameKeep) := by
  obtain ⟨hc, hfrag, hres⟩ := hwr_checks
  have hp := hwr_pass
  cases hpe : expandCallsPass hwrPassEnv hwr with
  | error e => rw [hpe] at hp; cases hp
  | ok out =>
    rw [hpe] at hp
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Bool.and_eq_true,
      beq_iff_eq] at hp
    obtain ⟨⟨hcg, hst⟩, hmr⟩ := hp
    exact ⟨out, rfl, hres, hst, hmr,
      GoFV.Proof.EC.expandCalls_refines hpe (ok_of_toBool hc) (ok_of_toBool hcg) hfrag,
      Env.p1_mono, Env.p1_frameKeep⟩

/-! ## A tail call's stack-argument `Move` -/

/-- A source block: the tail call `v2 = TailLECall v1` on the initial memory. -/
def tailFB : Block := mkB 1 .RetJmp p0 #[2] #[] #[] #[1, 2]

def tailF : Func :=
  { hwr with
    valueTab := #[none, some (mkV 1 .InitMem 0 none p0 2 #[] 1),
      some (mkV 2 .TailLECall 0 none p0 0 #[1] 1)]
    blockTab := #[none, some tailFB], blocks := #[1] }

/-- Its rewrite: a new `v3 = Move v1 v1 v1` (a stack argument's copy) right before the tail
call `v2 = TailCall v3`. -/
def tailGB : Block := mkB 1 .RetJmp p0 #[2] #[] #[] #[1, 2, 3]

def tailG : Func :=
  { hwr with
    valueTab := #[none, some (mkV 1 .InitMem 0 none p0 3 #[] 1),
      some (mkV 2 .TailCall 0 none p0 0 #[3] 1), some (mkV 3 .Move 0 none p0 1 #[1, 1, 1] 1)]
    blockTab := #[none, some tailGB], blocks := #[1] }

/-- `blockOK` accepts the new `Move` of a tail call's stack argument as anchored at the tail
call (`tailAnchoredB`, `ECStruct`'s `AnchoredAt` with a vacuous obligation: the source's tail
call is `stuck`). -/
theorem expandCalls_tailMove_witness :
    ECCheck.tailAnchoredB tailF tailG tailFB tailGB 3 = true := by
  decide +kernel

/-! ## A self-moved stack-assigned result -/

/-- `check`'s environment for the pass output of `test/stack` `f2`. -/
def sf2OutCheckEnv (o : PassOut) : CheckEnv := { tabs := o.tables, typs := sf2Typs }

theorem sf2_checks :
    (check sf2CheckEnv sf2).toBool = true ∧ expandCallsFrag sf2PassEnv sf2 = true ∧
      (sf2.value? 10).map (·.args) = some #[9, 5] := by
  decide +kernel

theorem sf2_pass :
    ((expandCallsPass sf2PassEnv sf2).toOption.map fun o =>
      (check (sf2OutCheckEnv o) o.func).toBool &&
        (o.func.value? 9).map (·.op) == some .Invalid &&
        (o.func.value? 10).map (·.args) == some #[5]) = some true := by
  decide +kernel

/-- **Non-vacuity of `expandCalls_refines` on a self-moved stack-assigned result**: `test/stack`
`f2` returns its `[3000]byte` result (a byte blob, no `wf` shape) by a self-move
(`MakeResult v9 v5`, `v9 = Dereference (LocalAddr {~r0}) v5`); expand calls stores nothing,
invalidates `v9` and returns `MakeResult v5`, and the output refines the input under monotone
contracts that keep the caller's frame. -/
theorem expandCalls_selfMove_witness :
    ∃ out, expandCallsPass sf2PassEnv sf2 = .ok out ∧
      (sf2.value? 10).map (·.args) = some #[9, 5] ∧
      (out.func.value? 9).map (·.op) = some .Invalid ∧
      (out.func.value? 10).map (·.args) = some #[5] ∧
      RefinesUnder (fun env => env.Mono ∧ env.FrameKeep) out.tables out.func sf2PassEnv.tables
        sf2 := by
  obtain ⟨hc, hfrag, hres⟩ := sf2_checks
  have hp := sf2_pass
  cases hpe : expandCallsPass sf2PassEnv sf2 with
  | error e => rw [hpe] at hp; cases hp
  | ok out =>
    rw [hpe] at hp
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Bool.and_eq_true,
      beq_iff_eq] at hp
    obtain ⟨⟨hcg, hinv⟩, hmr⟩ := hp
    exact ⟨out, rfl, hres, hinv, hmr,
      GoFV.Proof.EC.expandCalls_refines hpe (ok_of_toBool hc) (ok_of_toBool hcg) hfrag⟩

/-! ## Several wide stack arguments, each copied by its own `Move` -/

/-- A call's ABI: two stack-assigned `sync.RWMutex` arguments (24 bytes, `t3`) at offsets 0 and
24. -/
def mmABI : CallABI :=
  { abi := 0, nin := 2, nout := 0, spillOff := 48, spillSize := 0, inRegs := 0, outRegs := 0,
    params := #[{ out := false, index := 0, type := 3, name := none, regs := #[], offset := 0 },
                { out := false, index := 1, type := 3, name := none, regs := #[], offset := 24 }] }

/-- Its `AuxCall` (aux `a7`). -/
def mmCallAux : AuxDef :=
  { fmt := GoStr.ofString "AuxCall{f}", kind := .call (some 2) (some mmABI) }

/-- `syscall_hasWaitingReaders`'s tables with the call's aux. -/
def mmTabs : Tables := { hwrTabs with auxes := hwrTabs.auxes.push (some mmCallAux) }

/-- A value of `b1`. -/
def mmV (id : ID) (op : Op) (t : TypeRef) (auxInt : Int64) (aux : Option AuxRef) (args : Array ID) :
    Value :=
  { id, op, type := t, auxInt, aux, pos := p0, uses := 1, args, block := 1 }

/-- The source block: `v7 = StaticLECall {a7} v5 v6 v1` of two `Dereference`s of frame variables
(`LocalAddr {rw}`, `LocalAddr {~r0}`). -/
def mmFB : Block := mkB 1 .Exit p0 #[7] #[] #[] #[1, 2, 3, 4, 5, 6, 7]

def mmF : Func :=
  { hwr with
    valueTab := #[none, some (mmV 1 .InitMem 35 0 none #[]),
      some (mmV 2 .SP 22 0 none #[]),
      some (mmV 3 .LocalAddr 2 0 (some 3) #[2, 1]),
      some (mmV 4 .LocalAddr 2 0 (some 4) #[2, 1]),
      some (mmV 5 .Dereference 3 0 none #[3, 1]),
      some (mmV 6 .Dereference 3 0 none #[4, 1]),
      some (mmV 7 .StaticLECall 39 0 (some 7) #[5, 6, 1])]
    blockTab := #[none, some mmFB], blocks := #[1], vidLast := 7 }

/-- Its rewrite: the arguments copied into their slots by `v9 = Move [24] (OffPtr [0] SP) v3 v1`
and, above it, `v11 = Move [24] (OffPtr [24] SP) v4 v9`; the call `v7 = StaticCall {a7} v11`. -/
def mmGB : Block := mkB 1 .Exit p0 #[7] #[] #[] #[1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 7]

def mmG : Func :=
  { hwr with
    valueTab := #[none, some (mmV 1 .InitMem 35 0 none #[]),
      some (mmV 2 .SP 22 0 none #[]),
      some (mmV 3 .LocalAddr 2 0 (some 3) #[2, 1]),
      some (mmV 4 .LocalAddr 2 0 (some 4) #[2, 1]),
      some (mmV 5 .Dereference 3 0 none #[3, 1]),
      some (mmV 6 .Dereference 3 0 none #[4, 1]),
      some (mmV 7 .StaticCall 39 0 (some 7) #[11]),
      some (mmV 8 .OffPtr 2 0 none #[2]),
      some (mmV 9 .Move 35 24 (some 3) #[8, 3, 1]),
      some (mmV 10 .OffPtr 2 24 none #[2]),
      some (mmV 11 .Move 35 24 (some 3) #[10, 4, 9])]
    blockTab := #[none, some mmGB], blocks := #[1], vidLast := 11 }

/-- **`ecCheck` accepts a call with two wide stack arguments, each copied by its own `Move`**
(`callMoves`: `v9`, then `v11` above it, whose source is a frame variable, `localSrcOK`). -/
theorem expandCalls_multiMove_witness :
    ((mmF.value? 7).bind fun u => (mmG.value? 7).map fun w => ECCheck.callMoves mmF mmG u w) =
      some [9, 11] ∧ ECCheck.ecCheck mmTabs mmF mmG = true := by
  decide +kernel

/-- The memory of the witness: the outgoing-arguments area (48 bytes) and the two frame
variables (24 bytes each). -/
def mmMem : Mem :=
  { blocks := #[(.outargs 0, { data := Array.replicate 48 (.b 0) }),
      (.local 0 3, { data := Array.replicate 24 (.b 1) }),
      (.local 0 4, { data := Array.replicate 24 (.b 2) })] }

/-- The memory after `v9`'s copy of `v3`'s bytes into slot 0, then after `v11`'s of `v4`'s
into slot 24. -/
def mmMem9 : Mem := ((mmMem.write ⟨.outargs 0, 0⟩ (Array.replicate 24 (.b 1))).getD {})
def mmMem11 : Mem := ((mmMem9.write ⟨.outargs 0, 24⟩ (Array.replicate 24 (.b 2))).getD {})

/-- The target's registers: the memories of `v1`, `v9` and `v11`. -/
def mmT : Frame :=
  { regs := #[none, some (.mem mmMem), none, none, none, none, none, none, none,
      some (.mem mmMem9), none, some (.mem mmMem11)], args := [], mem0 := {} }

/-- `EC.ecm_moves` on the chain `v9`, `v11` of the witness (`v11` reads its frame variable's
block, outside the area `v9` wrote): both slots read back the bytes of their frame variables. -/
theorem expandCalls_moves_witness :
    ∃ Mt, rv mmT 11 = .mem Mt ∧
      Mt.read ⟨.outargs 0, 0⟩ 24 = some (Array.replicate 24 (.b 1)) ∧
      Mt.read ⟨.outargs 0, 24⟩ 24 = some (Array.replicate 24 (.b 2)) := by
  have hc : ECCheck.moveChain mmG (ECCheck.isNewB mmF) 12 11 1 = some [9, 11] := by decide +kernel
  have hv9 : mmG.value? 9 = some (mmV 9 .Move 35 24 (some 3) #[8, 3, 1]) := by decide +kernel
  have hv11 : mmG.value? 11 = some (mmV 11 .Move 35 24 (some 3) #[10, 4, 9]) := by decide +kernel
  obtain ⟨Mt, hMt, -, -, -, hR⟩ := EC.ecm_moves (T := mmT) (M := mmMem) rfl
    (fun _ => 24) (fun e bs => bs = Array.replicate 24 (.b (if e.2 = 5 then 1 else 2)))
    12 (sp := [(mmABI.params[0]!, 5), (mmABI.params[1]!, 6)]) hc rfl (by decide) (by decide)
    (by
      intro e z hez mw M0 hmw hM0
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, Prod.mk.injEq,
        List.not_mem_nil, or_false] at hez
      rcases hez with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hv9] at hmw; cases hmw
        cases hM0
        exact ⟨⟨.local 0 3, 0⟩, Array.replicate 24 (.b 1), mmMem9, by decide +kernel,
          by decide +kernel, rfl, .inl rfl, fun _ => by decide⟩
      · rw [hv11] at hmw; cases hmw
        cases hM0
        exact ⟨⟨.local 0 4, 0⟩, Array.replicate 24 (.b 2), mmMem11, by decide +kernel,
          by decide +kernel, rfl, .inr nofun, fun _ => by decide⟩)
  obtain ⟨b0, h0, rfl⟩ := hR _ List.mem_cons_self
  obtain ⟨b1, h1, rfl⟩ := hR _ (List.mem_cons_of_mem _ List.mem_cons_self)
  exact ⟨Mt, hMt, h0, h1⟩

/-! ## An invalidated self-move after its `MakeResult`; an integer tuple op -/

/-- `f2`'s tables with the tuple type `t37 = (uint64, uint64)`. -/
def ivTabs : Tables :=
  { sf2Tabs with types := sf2Tabs.types.push (some (mkTy .TUPLE none none none false false false
      false "(uint64,uint64)" "" (.tuple 12 12))) }

def ivCheckEnv : CheckEnv := { tabs := ivTabs, typs := sf2Typs }

def ivV (id : ID) (op : Op) (t : TypeRef) (auxInt : Int64) (aux : Option AuxRef) (uses : Nat)
    (args : Array ID) (blk : ID) : Value :=
  { id, op, type := t, auxInt, aux, pos := p0, uses, args, block := blk }

/-- The entry block: `f2`'s slot cleared (`v5 = Zero [3000] (LocalAddr {~r0}) v1`) and an unused
`v8 = Mul64uhilo v6 v7` (of the tuple type `t37`). -/
def ivFB1 : Block := mkB 1 .Plain p0 #[] #[⟨2, 0⟩] #[] #[1, 2, 4, 5, 6, 7, 8]

/-- The exit block: the self-move `v10 = MakeResult v9 v5`, `v9 = Dereference v4 v5`. -/
def ivFB2 : Block := mkB 2 .Ret p0 #[10] #[] #[⟨1, 0⟩] #[9, 10]

def ivF : Func :=
  { sf2 with
    valueTab := #[none, some (ivV 1 .InitMem 30 0 none 2 #[] 1),
      some (ivV 2 .SP 17 0 none 1 #[] 1), none,
      some (ivV 4 .LocalAddr 35 0 (some 3) 2 #[2, 1] 1),
      some (ivV 5 .Zero 30 3000 (some 4) 2 #[4, 1] 1),
      some (ivV 6 .Const64 12 3 none 1 #[] 1), some (ivV 7 .Const64 12 5 none 1 #[] 1),
      some (ivV 8 .Mul64uhilo 37 0 none 0 #[6, 7] 1),
      some (ivV 9 .Dereference 2 0 none 1 #[4, 5] 2),
      some (ivV 10 .MakeResult 36 0 none 1 #[9, 5] 2)]
    blockTab := #[none, some ivFB1, some ivFB2], blocks := #[1, 2], bidLast := 2
    freeValues := [3], cache := {} }

/-- Its rewrite: `v9` invalidated, `v10 = MakeResult v5`; with both nodes ready, the schedule
puts `v10` first. -/
def ivGB2 : Block := mkB 2 .Ret p0 #[10] #[] #[⟨1, 0⟩] #[9, 10]

def ivG : Func :=
  { ivF with
    valueTab := #[none, some (ivV 1 .InitMem 30 0 none 2 #[] 1),
      some (ivV 2 .SP 17 0 none 1 #[] 1), none,
      some (ivV 4 .LocalAddr 35 0 (some 3) 1 #[2, 1] 1),
      some (ivV 5 .Zero 30 3000 (some 4) 1 #[4, 1] 1),
      some (ivV 6 .Const64 12 3 none 1 #[] 1), some (ivV 7 .Const64 12 5 none 1 #[] 1),
      some (ivV 8 .Mul64uhilo 37 0 none 0 #[6, 7] 1),
      some (ivV 9 .Invalid 2 0 none 0 #[] 2),
      some (ivV 10 .MakeResult 34 0 none 1 #[5] 2)]
    blockTab := #[none, some ivFB1, some ivGB2] }

theorem iv_checks :
    (check ivCheckEnv ivF).toBool = true ∧ (check ivCheckEnv ivG).toBool = true ∧
      ECCheck.ecCheck ivTabs ivF ivG = true ∧ schedule ivG ivGB2 = some #[10, 9] ∧
      WBCheck.memFree (ivTabs.ty 37) = false := by
  decide +kernel

/-- **Non-vacuity of the invalidated-argument and `memFreeOps` relaxations**: the target
schedules the invalidated self-move `v9` after its `MakeResult` `v10` (so `v9` does not precede
it, `beforeB`), the source holds the tuple-typed `Mul64uhilo` `v8` (a shape that may hold a
memory, `memFree` false), `ecCheck` accepts, and the target refines the source under monotone
contracts that keep the caller's frame. -/
theorem expandCalls_invalidLate_witness :
    schedule ivG ivGB2 = some #[10, 9] ∧ ECCheck.beforeB [10, 9] 9 10 = false ∧
      (ivF.value? 8).map (·.op) = some .Mul64uhilo ∧ WBCheck.memFree (ivTabs.ty 37) = false ∧
      RefinesUnder (fun env => env.Mono ∧ env.FrameKeep) ivTabs ivG ivTabs ivF := by
  obtain ⟨hf, hg, hec, hs, hmf⟩ := iv_checks
  exact ⟨hs, by decide, rfl, hmf, EC.cvSim_refines (ok_of_toBool hf) (ok_of_toBool hg)
    (EC.ecRel_of_check (ok_of_toBool hf) (ok_of_toBool hg) hec)⟩

/-- `MemInv.evalOp_memFreeOps_mems` at `Mul64uhilo` on `3` and `5` (any environment, context and
frame): the result is `(0, 15)`, without memories. -/
theorem memFreeOps_witness (env : Env) (ctx : Ctx) (fr : Frame) :
    ∃ r, evalOp env ctx fr (ivV 8 .Mul64uhilo 37 0 none 0 #[6, 7] 1)
        [.int .w64 3, .int .w64 5] (.tuple [.int .w64, .int .w64]) = .ok r ∧
      r.mems = [] ∧ r = .tuple [.int .w64 0, .int .w64 15] :=
  have h := TabsMod.evalOp_pure_of (env := env) (ctx := ctx) (fr := fr)
    (v := ivV 8 .Mul64uhilo 37 0 none 0 #[6, 7] 1) (argv := [.int .w64 3, .int .w64 5])
    (ty := .tuple [.int .w64, .int .w64]) (by decide) rfl
  ⟨_, h, MemInv.evalOp_memFreeOps_mems rfl h, by rfl⟩

/-- `MemInv.int3_mems` on a ternary op returning its first operand. -/
theorem int3_mems_witness :
    (GoFV.SSA.Sem.int3 .w64 (fun x _ _ => .int .w64 x) [.int .w64 1, .int .w64 2, .int .w64 3]).mems
      = [] :=
  MemInv.int3_mems .w64 _ (fun _ _ _ => rfl) _

/-- `EC.ec_not_invalidated` on the witness's `Zero` `v5` (unconverted). -/
theorem ec_not_invalidated_witness : ECCheck.invalidated ivG 5 = false :=
  EC.ec_not_invalidated (f := ivF) (by decide +kernel)

theorem hwr_ownStores :
    ((expandCallsPass hwrPassEnv hwr).toOption.map fun o =>
      ECCheck.ownStores hwr o.func 11 == [2] && (o.func.value? 2).map (·.args[1]!) == some 10 &&
        !ECCheck.invalidated o.func 11 && !ECCheck.isNewB hwr 10 &&
        !ECCheck.frameDet hwr o.func 11) = some true := by
  decide +kernel

/-- `EC.ecFront_own` on `syscall_hasWaitingReaders`: its result store `v2` stores the source
value `v10`, which is in the front of the `MakeResult` `v11` (its obligation reads it). -/
theorem expandCalls_ownFront_witness :
    ∃ out, expandCallsPass hwrPassEnv hwr = .ok out ∧ ECCheck.ownStores hwr out.func 11 = [2] ∧
      10 ∈ EC.ecFront hwr out.func 11 := by
  have hp := hwr_ownStores
  cases hpe : expandCallsPass hwrPassEnv hwr with
  | error e => rw [hpe] at hp; cases hp
  | ok out =>
    rw [hpe] at hp
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Bool.and_eq_true,
      beq_iff_eq, Bool.not_eq_true'] at hp
    obtain ⟨⟨⟨⟨hos, hv2⟩, hi⟩, hn⟩, hfd⟩ := hp
    refine ⟨out, rfl, hos, EC.ecFront_own hi hfd ?_ hn⟩
    have hsv : ECCheck.storeVal out.func 2 = 10 := by
      unfold ECCheck.storeVal
      cases h2 : out.func.value? 2 with
      | none => rw [h2] at hv2; cases hv2
      | some w2 =>
        rw [h2] at hv2
        exact Option.some.inj hv2
    rw [hos, List.map_cons, List.map_nil, hsv]
    exact List.mem_singleton_self _

/-! ## A stack-assigned call result read by its address -/

/-- `check`'s environment for the pass output of `uuid.New`. -/
def uuidOutCheckEnv (o : PassOut) : CheckEnv := { tabs := o.tables, typs := sf2Typs }

theorem uuid_checks :
    (check uuidCheckEnv uuidNew).toBool = true ∧ expandCallsFrag uuidPassEnv uuidNew = true ∧
      (uuidNew.value? 8).map (·.op) = some .SelectNAddr := by
  decide +kernel

theorem uuid_pass :
    ((expandCallsPass uuidPassEnv uuidNew).toOption.map fun o =>
      (check (uuidOutCheckEnv o) o.func).toBool &&
        (o.func.value? 8).map (·.op) == some .Copy &&
        (o.func.value? 6).map (·.op) == some .StaticCall) = some true := by
  decide +kernel

/-- **Non-vacuity of `expandCalls_refines` on a result address**: `uuid.New` reads its callee's
`[16]byte` result (a byte blob, no `wf` shape) by its address (`v8 = SelectNAddr v6`); expand
calls computes the address from the frame (`v8 = Copy (OffPtr [8] SP)`, frame-determined), and
the output refines the input under monotone contracts that keep the caller's frame. -/
theorem expandCalls_selAddr_witness :
    ∃ out, expandCallsPass uuidPassEnv uuidNew = .ok out ∧
      (uuidNew.value? 8).map (·.op) = some .SelectNAddr ∧
      (out.func.value? 8).map (·.op) = some .Copy ∧
      (out.func.value? 6).map (·.op) = some .StaticCall ∧
      RefinesUnder (fun env => env.Mono ∧ env.FrameKeep) out.tables out.func uuidPassEnv.tables
        uuidNew := by
  obtain ⟨hc, hfrag, hsa⟩ := uuid_checks
  have hp := uuid_pass
  cases hpe : expandCallsPass uuidPassEnv uuidNew with
  | error e => rw [hpe] at hp; cases hp
  | ok out =>
    rw [hpe] at hp
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Bool.and_eq_true,
      beq_iff_eq] at hp
    obtain ⟨⟨hcg, hcp⟩, hcall⟩ := hp
    exact ⟨out, rfl, hsa, hcp, hcall,
      GoFV.Proof.EC.expandCalls_refines hpe (ok_of_toBool hc) (ok_of_toBool hcg) hfrag⟩

/-- At `Addrs.fixed`, the slot of offset 8 of activation 0 (`uuid.New`'s callee result,
`SelectNAddr`) is an integer word that reads back as the slot. -/
theorem expandCalls_slotWord_witness :
    ∃ x, (⟨.outargs 0, 8⟩ : Ptr).word = .int .w64 x ∧ Ptr.ofAddr x = ⟨.outargs 0, 8⟩ := by
  have hc : (⟨.outargs 0, 8⟩ : Ptr).convertible = true := by decide +kernel
  have ha : (⟨.outargs 0, 8⟩ : Ptr).addr? = some (BitVec.ofNat 64 (2 ^ 62 + 8)) := by
    decide +kernel
  exact ⟨_, by simp only [Ptr.word, hc, ha], Ptr.ofAddr_addr hc ha⟩

end GoFV.Proof.Witness

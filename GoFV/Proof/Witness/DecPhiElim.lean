import GoFV.Proof.Witness.DecStore

/-!
# Witness function for decompose builtin's phi eliminations: `pickLen` (hand-written, issue #17)

```go
func pickLen(q *uint8, n int, b bool) int {
	var s string
	if b {
		s = unsafe.String(q, n)
	} else {
		s = unsafe.String(q, n)
	}
	return len(s)
}
```

as decompose builtin sees it after its phi stage: the string `Phi`'s length component is
`v9 = Phi (StringLen v5) (StringLen v7)`, with `v5`, `v7` the two `StringMake q n`. The proven
dec rules turn both `StringLen`s into copies of `n` (`dec.rules:43`), the rewrite loop replaces
the phi's arguments by `n` and eliminates the phi (`phielimValue`: `v9 = Copy n`), the result
`v10` reads `n` and the dead `v9` is dropped. By kernel evaluation the decompose builtin stage
checks accept it: the log without the phi elimination is validated against the output with `v9`
kept a `Phi` (`DecPhiElim.phStrip`: `h`), copyelim's relation relates `h` to the output with
`v9` listed as `Copy n` (`DecPhiElim.phRelOK`), and that to the output (`Sccp.deadOK`), so
`refinesFrom_of_decBuiltinStagesOK` applies through `refines_of_decRewriteOK`.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.Decompose GoFV.Proof GoFV.Proof.Decompose GoFV.Rules

/-- `abiInfo` of `pickLen`: three register parameters, one integer result. -/
def pklABI : CallABI :=
  { abi := 1, nin := 3, nout := 1, spillOff := 8, spillSize := 24, inRegs := 3, outRegs := 1,
    params := #[{ out := false, index := 0, type := 5, name := some 3, regs := #[0], offset := 0 },
                { out := false, index := 1, type := 2, name := some 4, regs := #[1], offset := 8 },
                { out := false, index := 2, type := 3, name := some 5, regs := #[2], offset := 16 },
                { out := true, index := 0, type := 2, name := some 6, regs := #[0],
                  offset := -1 }] }

/-- The definition tables: `int` (type 2), `bool` (3), `string` (4), `*uint8` (5). -/
def pklTabs : Tables where
  types :=
    let t := Array.replicate 36 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(*uint8, int, bool) int" (.func 0 3 1 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 3 (some (mkT .BOOL (some 1) "bool"))
    let t := t.set! 4 (some (mkT .STRING (some 16) "string"))
    let t := t.set! 5 (some (mkT .PTR (some 8) "*uint8" (.elem 6)))
    let t := t.set! 6 (some (mkT .UINT8 (some 1) "uint8"))
    let t := t.set! 7 (some (mkT .PTR (some 8) "*int" (.elem 2)))
    let t := t.set! 29 (some (mkT .SSA none "mem"))
    let t := t.set! 31 (some (mkT .SSA none "void"))
    t.set! 35 (some (mkT .RESULTS none "int,mem" (.results #[2, 29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.pickLen}", kind := .call (some 2) (some pklABI) },
    some { fmt := GoStr.ofString "main.pickLen",
           kind := .sym (GoStr.ofString "main.pickLen") 1 "" 0 default none none none #[] none },
    some (paramNameT "q" .PPARAM 5 0), some (paramNameT "n" .PPARAM 2 8),
    some (paramNameT "b" .PPARAM 3 16), some (paramNameT "~r0" .PPARAMOUT 2 0)]

/-- `pickLen` after decompose builtin's phi stage. -/
def pklFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 10
  bidLast := 4
  blocks := #[1, 2, 3, 4]
  blockTab := #[none,
    some (mkB 1 .If p0 #[4] #[⟨2, 0⟩, ⟨3, 0⟩] #[] #[1, 2, 3, 4]),
    some (mkB 2 .Plain p0 #[] #[⟨4, 0⟩] #[⟨1, 0⟩] #[5, 6]),
    some (mkB 3 .Plain p0 #[] #[⟨4, 1⟩] #[⟨1, 1⟩] #[7, 8]),
    some (mkB 4 .Ret p0 #[10] #[] #[⟨2, 0⟩, ⟨3, 0⟩] #[9, 10])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 1 #[] 1),
    some (mkV 2 .Arg 5 (some 3) p0 2 #[] 1),
    some (mkV 3 .Arg 2 (some 4) p0 2 #[] 1),
    some (mkV 4 .Arg 3 (some 5) p0 1 #[] 1),
    some (mkVi 5 .StringMake 4 0 p0 1 #[2, 3] 2),
    some (mkVi 6 .StringLen 2 0 p0 1 #[5] 2),
    some (mkVi 7 .StringMake 4 0 p0 1 #[2, 3] 3),
    some (mkVi 8 .StringLen 2 0 p0 1 #[7] 3),
    some (mkVi 9 .Phi 2 0 p0 1 #[6, 8] 4),
    some (mkVi 10 .MakeResult 35 0 p0 1 #[9, 1] 4)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

def pklTyps : Array (String × TypeRef) :=
  #[("Int", 2), ("Bool", 3), ("String", 4), ("BytePtr", 5), ("UInt8", 6), ("IntPtr", 7),
    ("Mem", 29), ("Void", 31)]

def pklPassEnv : PassEnv :=
  { azPassEnv with passName := "decompose builtin", funcName := GoStr.ofString "pickLen",
                   typs := pklTyps, tables := pklTabs }

/-- The log has a phi elimination. -/
def hasPhielim (log : Array RwEvent) : Bool := log.any fun | .phielim .. => true | _ => false

/-- The op and arguments of value `x` of `g`. -/
def pklOpArgs (g : Func) (x : ID) : Option (Op × Array ID) :=
  (g.value? x).map fun (v : Value) => (v.op, v.args)

/-- By kernel evaluation: the input passes `check`; the proven dec rules' rewrite eliminates the
phi `v9` (logged as a phi elimination; the result `v10` now reads `n`) and the decompose builtin stage checks
accept it (with the input as its own phi stage: its only `Phi` is not a composite). -/
theorem pkl_stages :
    (check { tabs := pklTabs, typs := pklTyps } pklFunc).toBool = true ∧
    (match Rules.rewriteRun decProvenTable false true pklPassEnv pklFunc with
      | .ok (o, _, log) =>
        decBuiltinStagesOK pklPassEnv pklFunc pklFunc o.func log o && hasPhielim log &&
          pklOpArgs o.func 10 == some (.MakeResult, #[3, 1])
      | .error _ => false) = true := by
  decide +kernel

/-- **Pass execution witness** for decompose builtin's phi eliminations: on `pickLen`, the
proven dec rules' rewrite eliminates the length `Phi` (a phi elimination in its log; the result reads `n`),
and the result refines the input for `DecPre` (`refinesFrom_of_decBuiltinStagesOK`, through
`refines_of_decRewriteOK`, `DecPhiElim.phRelOK_spec` and `CopyElim.refines_of_rel`). -/
theorem decPhiElim_witness :
    ∃ o n log, Rules.rewriteRun decProvenTable false true pklPassEnv pklFunc = .ok (o, n, log) ∧
      hasPhielim log = true ∧ pklOpArgs o.func 10 = some (.MakeResult, #[3, 1]) ∧
      RefinesFrom DecPre o.tables o.func pklTabs pklFunc := by
  obtain ⟨hcf, h⟩ := pkl_stages
  cases hr : Rules.rewriteRun decProvenTable false true pklPassEnv pklFunc with
  | error e => rw [hr] at h; cases h
  | ok r =>
    obtain ⟨o, n, log⟩ := r
    rw [hr] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hok, hp⟩, h9⟩ := h
    have r := refinesFrom_of_decBuiltinStagesOK hok (ok_of_toBool hcf)
    rw [show pklPassEnv.tables = pklTabs from rfl] at r
    exact ⟨o, n, log, rfl, hp, h9, r⟩

end GoFV.Proof.Witness

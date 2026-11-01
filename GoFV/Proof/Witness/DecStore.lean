import GoFV.Proof.Witness.StructStore
import GoFV.Proof.Witness.Decompose
import GoFV.Proof.Rules.DecStore

/-!
# Witness function for the decompose `Store` splits: `storeStr` (hand-written, issue #17)

```go
func storeStr(p *string, q *uint8, n int, r *string) int {
	*p = unsafe.String(q, n)
	*p = *r
	return n
}
```

as decompose builtin sees it (one block: `v5 = StringMake v3 v4`, `v6 = Store {string} v2 v5 v1`,
`v8 = Load <string> v7 v6`, `v9 = Store {string} v2 v8 v6`). The proven dec rules expand the
`Load` (`dec.rules:45`, into a `StringMake` of two `Load`s) and split both `Store`s in place
(`dec.rules:51`: `v6`, `v9` become the length stores at `OffPtr [8] v2`, each on a fresh pointer
store at `v2`). By kernel evaluation the decompose builtin rewrite step's checks accept it, the
`Load` expansion as a layer (`RewriteCheck.ldPre`) and the splits by `RewriteCheck.ssRel`
(`RewriteCheck.decLayers`), so `refinesFrom_of_decBuiltinStagesOK` applies.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.Decompose GoFV.Proof GoFV.Proof.Decompose GoFV.Rules

/-- `abiInfo` of `storeStr`: four register parameters, one integer result. -/
def dsABI : CallABI :=
  { abi := 1, nin := 4, nout := 1, spillOff := 8, spillSize := 32, inRegs := 4, outRegs := 1,
    params := #[{ out := false, index := 0, type := 3, name := some 3, regs := #[0], offset := 0 },
                { out := false, index := 1, type := 5, name := some 4, regs := #[1], offset := 8 },
                { out := false, index := 2, type := 2, name := some 5, regs := #[2], offset := 16 },
                { out := false, index := 3, type := 3, name := some 6, regs := #[3], offset := 24 },
                { out := true, index := 0, type := 2, name := some 7, regs := #[0],
                  offset := -1 }] }

/-- The definition tables: `string` (type 4), `*string` (3), `*uint8` (5), `*int` (7);
`Store {string}` names its type by aux 8. -/
def dsTabs : Tables where
  types :=
    let t := Array.replicate 36 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(*string, *uint8, int, *string) int"
      (.func 0 4 1 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 3 (some (mkT .PTR (some 8) "*string" (.elem 4)))
    let t := t.set! 4 (some (mkT .STRING (some 16) "string"))
    let t := t.set! 5 (some (mkT .PTR (some 8) "*uint8" (.elem 6)))
    let t := t.set! 6 (some (mkT .UINT8 (some 1) "uint8"))
    let t := t.set! 7 (some (mkT .PTR (some 8) "*int" (.elem 2)))
    let t := t.set! 29 (some (mkT .SSA none "mem"))
    let t := t.set! 31 (some (mkT .SSA none "void"))
    t.set! 35 (some (mkT .RESULTS none "int,mem" (.results #[2, 29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.storeStr}", kind := .call (some 2) (some dsABI) },
    some { fmt := GoStr.ofString "main.storeStr",
           kind := .sym (GoStr.ofString "main.storeStr") 1 "" 0 default none none none #[] none },
    some (paramNameT "p" .PPARAM 3 0), some (paramNameT "q" .PPARAM 5 8),
    some (paramNameT "n" .PPARAM 2 16), some (paramNameT "r" .PPARAM 3 24),
    some (paramNameT "~r0" .PPARAMOUT 2 0),
    some { fmt := GoStr.ofString "string", kind := .type 4 }]

/-- The `typs` of the export (what the dec rules' `typ.…` read). -/
def dsTyps : Array (String × TypeRef) :=
  #[("Int", 2), ("String", 4), ("BytePtr", 5), ("UInt8", 6), ("IntPtr", 7), ("Mem", 29),
    ("Void", 31)]

/-- `storeStr`, the input of decompose builtin. -/
def dsFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 10
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[10] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 1 #[] 1),
    some (mkV 2 .Arg 3 (some 3) p0 2 #[] 1),
    some (mkV 3 .Arg 5 (some 4) p0 1 #[] 1),
    some (mkV 4 .Arg 2 (some 5) p0 2 #[] 1),
    some (mkVi 5 .StringMake 4 0 p0 1 #[3, 4] 1),
    some (mkV 6 .Store 29 (some 8) p0 2 #[2, 5, 1] 1),
    some (mkV 7 .Arg 3 (some 6) p0 1 #[] 1),
    some (mkVi 8 .Load 4 0 p0 1 #[7, 6] 1),
    some (mkV 9 .Store 29 (some 8) p0 1 #[2, 8, 6] 1),
    some (mkVi 10 .MakeResult 35 0 p0 1 #[4, 9] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

def dsPassEnv : PassEnv :=
  { azPassEnv with passName := "decompose builtin", funcName := GoStr.ofString "storeStr",
                   typs := dsTyps, tables := dsTabs }

/-- The pointer argument's op and offset of the `Store` `x` of `g`. -/
def dsPtrOf (g : Func) (x : ID) : Option (Op × Int64) :=
  ((g.value? x).bind fun s => s.args[0]?.bind g.value?).map fun p => (p.op, p.auxInt)

/-- By kernel evaluation: the input passes `check`; the proven dec rules' rewrite splits both
`Store`s in place (each now the length store at `OffPtr [8] v2`) and expands the `Load`, and the
decompose builtin stage checks accept it (with the input as its own phi stage: it has no
`Phi`). -/
theorem ds_stages :
    (check { tabs := dsTabs, typs := dsTyps } dsFunc).toBool = true ∧
    (match Rules.rewriteRun decProvenTable false true dsPassEnv dsFunc with
      | .ok (o, _, log) =>
        decBuiltinStagesOK dsPassEnv dsFunc dsFunc o.func log o &&
          dsPtrOf o.func 6 == some (.OffPtr, 8) && dsPtrOf o.func 9 == some (.OffPtr, 8) &&
          (o.func.value? 8).map (·.op) == some .StringMake
      | .error _ => false) = true := by
  decide +kernel

/-- **Pass execution witness** for the decompose `Store` splits (`dec.rules:51`) and the
value-rule `Load` expansion layer (`dec.rules:45`): on `storeStr`, the proven dec rules split
both string `Store`s in place and expand the `Load`, and the result refines the input for
`DecPre` (`refinesFrom_of_decBuiltinStagesOK`, through `Pass.Rewrite.layersOK_refines` and
`StructStore.ss_refines`). -/
theorem decStore_witness :
    ∃ o n log, Rules.rewriteRun decProvenTable false true dsPassEnv dsFunc = .ok (o, n, log) ∧
      dsPtrOf o.func 6 = some (.OffPtr, 8) ∧ dsPtrOf o.func 9 = some (.OffPtr, 8) ∧
      (o.func.value? 8).map (·.op) = some .StringMake ∧
      RefinesFrom DecPre o.tables o.func dsTabs dsFunc := by
  obtain ⟨hcf, h⟩ := ds_stages
  cases hr : Rules.rewriteRun decProvenTable false true dsPassEnv dsFunc with
  | error e => rw [hr] at h; cases h
  | ok r =>
    obtain ⟨o, n, log⟩ := r
    rw [hr] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hok, h6⟩, h9⟩, h8⟩ := h
    have r := refinesFrom_of_decBuiltinStagesOK hok (ok_of_toBool hcf)
    rw [show dsPassEnv.tables = dsTabs from rfl] at r
    exact ⟨o, n, log, rfl, h6, h9, h8, r⟩

end GoFV.Proof.Witness

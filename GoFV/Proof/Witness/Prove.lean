import GoFV.Proof.Pass.Prove
import GoFV.Proof.Witness.AddZero
import GoFV.Proof.Witness.Util

/-!
# Witness of `proveChecked_refines`: a dominated bounds check (hand-written)

```go
func at(i, n int) int {
	if uint(i) < uint(n) {
		if 0 <= i && i < n { // the bounds check of s[i] with len(s) = n
			return 1
		}
		return 2 // panicIndex in Go
	}
	return 0
}
```

as the SSA `prove` sees it: the entry branches on `v4 = Less64U v2 v3`, its successor `b2` on the
bounds check `v5 = IsInBounds v2 v3`. `prove` removes `b2`'s branch (`b2` becomes `First` towards
`b3`); the validator re-derives it from `b2`'s path fact `v4 = true` (`Less64U` of the same two
sides), so `proveChecked` keeps it. Input and output pass `check` (kernel evaluation), and by
`proveChecked_refines` the output returns `at(1, 3) = 1`, as the source does.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof

/-- `abiInfo` of `at`: two integer register parameters, one result. -/
def pwABI : CallABI :=
  { abi := 1, nin := 2, nout := 1, spillOff := 8, spillSize := 16, inRegs := 2, outRegs := 1,
    params := #[{ out := false, index := 0, type := 2, name := some 3, regs := #[0], offset := 0 },
                { out := false, index := 1, type := 2, name := some 4, regs := #[1], offset := 8 },
                { out := true, index := 0, type := 2, name := some 5, regs := #[0],
                  offset := -1 }] }

/-- The definition tables. -/
def pwTabs : Tables where
  types :=
    let t := Array.replicate 36 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(int, int) int" (.func 0 2 1 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 4 (some (mkT .BOOL (some 1) "bool"))
    let t := t.set! 29 (some (mkT .SSA none "mem"))
    let t := t.set! 31 (some (mkT .SSA none "void"))
    t.set! 35 (some (mkT .RESULTS none "int,mem" (.results #[2, 29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.at}", kind := .call (some 2) (some pwABI) },
    some { fmt := GoStr.ofString "main.at",
           kind := .sym (GoStr.ofString "main.at") 1 "" 0 default none none none #[] none },
    some (paramNameT "i" .PPARAM 2 0), some (paramNameT "n" .PPARAM 2 8),
    some (paramNameT "~r0" .PPARAMOUT 2 0)]

/-- The values, by ID. -/
def pwValues : Array (Option Value) := #[none,
  some (mkVi 1 .InitMem 29 0 p0 3 #[] 1),
  some (mkV 2 .Arg 2 (some 3) p0 2 #[] 1),
  some (mkV 3 .Arg 2 (some 4) p0 2 #[] 1),
  some (mkVi 4 .Less64U 4 0 p0 1 #[2, 3] 1),
  some (mkVi 5 .IsInBounds 4 0 p0 1 #[2, 3] 2),
  some (mkVi 6 .Const64 2 1 p0 1 #[] 3),
  some (mkVi 7 .MakeResult 35 0 p0 1 #[6, 1] 3),
  some (mkVi 8 .Const64 2 0 p0 1 #[] 4),
  some (mkVi 9 .MakeResult 35 0 p0 1 #[8, 1] 4),
  some (mkVi 10 .Const64 2 2 p0 1 #[] 5),
  some (mkVi 11 .MakeResult 35 0 p0 1 #[10, 1] 5)]

/-- `at`, the input of `prove`. -/
def atFn : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 11
  bidLast := 5
  blocks := #[1, 2, 3, 4, 5]
  blockTab := #[none,
    some (mkB 1 .If p0 #[4] #[⟨2, 0⟩, ⟨4, 0⟩] #[] #[1, 2, 3, 4]),
    some (mkB 2 .If p0 #[5] #[⟨3, 0⟩, ⟨5, 0⟩] #[⟨1, 0⟩] #[5]),
    some (mkB 3 .Ret p0 #[7] #[] #[⟨2, 0⟩] #[6, 7]),
    some (mkB 4 .Ret p0 #[9] #[] #[⟨1, 1⟩] #[8, 9]),
    some (mkB 5 .Ret p0 #[11] #[] #[⟨2, 1⟩] #[10, 11])]
  valueTab := pwValues
  names := #[(1, #[2]), (2, #[3])]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[(1, #[6]), (0, #[8]), (2, #[10])]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `prove` (arm64, the export's fixed configuration). -/
def pwPassEnv : PassEnv :=
  { azPassEnv with passName := "prove", funcName := GoStr.ofString "at",
                   config := azPassEnv.config.push ("havecondselect", #[.word "1"]),
                   typs := #[("Bool", 4), ("Int", 2), ("Mem", 29), ("Void", 31)],
                   tables := pwTabs }

def pwCheckEnv : CheckEnv := { tabs := pwTabs, typs := #[("Int", 2), ("Mem", 29)] }

/-- By kernel evaluation: the input passes `check`; `proveChecked` turns `b2` into a `First`
block towards `b3` and its result passes `check`; `at(1, 3) = 1`. -/
theorem atFn_checks :
    (check pwCheckEnv atFn).toBool = true ∧
    (proveChecked pwPassEnv atFn).toOption.map
      (fun o => ((check pwCheckEnv o.func).toBool,
        (o.func.block? 2).map (fun b => (b.kind, b.succs.map (·.b))))) =
      some (true, some (.First, #[3, 5])) ∧
    returnsInt (run Env.p1 pwTabs atFn [.i64 1, .i64 3] {} 3) 1 = true := by
  decide +kernel

/-- **Witness of `proveChecked_refines`**: on `at`, the checked prove removes the dominated
bounds check (`b2` becomes `First`), and the output returns `at(1, 3) = 1`, as the source does. -/
theorem proveChecked_witness :
    ∃ out, proveChecked pwPassEnv atFn = .ok out ∧
      (out.func.block? 2).map (fun b => (b.kind, b.succs.map (·.b))) = some (.First, #[3, 5]) ∧
      RefinesUnder Env.Mono out.tables out.func pwTabs atFn ∧
      ∃ fuel m, run Env.p1 out.tables out.func [.i64 1, .i64 3] {} fuel = .returned [.i64 1] m := by
  obtain ⟨h1, h2, h3⟩ := atFn_checks
  cases hc : proveChecked pwPassEnv atFn with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, hb⟩ := h2
    have hR := ProveCheck.proveChecked_refines hc (ok_of_toBool h1) (ok_of_toBool hg)
    rw [show pwPassEnv.tables = pwTabs from rfl] at hR
    refine ⟨out, rfl, hb, hR, ?_⟩
    obtain ⟨m, hm⟩ := returnsInt_iff.1 h3
    obtain ⟨fuel', ho⟩ := hR Env.p1 Env.p1_mono [.i64 1, .i64 3] {} 3 (by rw [hm]; trivial)
    rw [hm] at ho
    refine ⟨fuel', ?_⟩
    generalize run Env.p1 out.tables out.func [.i64 1, .i64 3] {} fuel' = o at ho ⊢
    cases ho with
    | returned hl =>
      cases hl with
      | cons h1 t =>
        cases t
        cases h1
        exact ⟨_, rfl⟩

end GoFV.Proof.Witness

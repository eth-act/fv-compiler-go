import GoFV.Proof.Pass.Prove
import GoFV.Proof.Witness.AddZero
import GoFV.Proof.Witness.Util

open scoped GoFV.SSA.Sem.Fixed

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

/-! ## A bounds check in a downward loop, decided by a relation

```go
func at(i, n int) int { // `at`'s signature and tables; `i` is unused
	if n < 0 {
		return 1
	}
	for j := n - 1; j >= 0; j-- {
		if !(0 <= j && j < n) { // the bounds check of s[j] with len(s) = n
			return 2 // panicIndex in Go
		}
	}
	return 0
}
```

The loop header `b2` has `v15 = Phi(v13, v17)` with `v13 = n - 1` and `v17 = v15 - 1`; `b3` checks
`v18 = IsInBounds v15 v3`. `prove` removes `b3`'s branch. The path facts give only `0 ≤ v15`;
the validator re-derives the upper bound from the relation `v15 - n ≤ -1`, checked on both edges
into `b2` (`n - 1` with `n ≥ 0`; `v15 - 1` with `v15 ≥ 0` and the relation at `b4`). -/

/-- The values of the downward loop, by ID. -/
def downValues : Array (Option Value) := #[none,
  some (mkVi 1 .InitMem 29 0 p0 3 #[] 1),
  some (mkV 2 .Arg 2 (some 3) p0 0 #[] 1),
  some (mkV 3 .Arg 2 (some 4) p0 3 #[] 1),
  none,
  some (mkVi 5 .Less64 4 0 p0 1 #[3, 14] 1),
  none, none, none, none, none, none,
  some (mkVi 12 .Const64 2 (-1) p0 2 #[] 1),
  some (mkVi 13 .Add64 2 0 p0 1 #[12, 3] 8),
  some (mkVi 14 .Const64 2 0 p0 3 #[] 1),
  some (mkVi 15 .Phi 2 0 p0 3 #[13, 17] 2),
  some (mkVi 16 .Leq64 4 0 p0 1 #[14, 15] 2),
  some (mkVi 17 .Add64 2 0 p0 1 #[12, 15] 4),
  some (mkVi 18 .IsInBounds 4 0 p0 1 #[15, 3] 3),
  none,
  some (mkVi 20 .MakeResult 35 0 p0 1 #[14, 1] 5),
  some (mkVi 21 .Const64 2 2 p0 1 #[] 6),
  some (mkVi 22 .MakeResult 35 0 p0 1 #[21, 1] 6),
  some (mkVi 23 .Const64 2 1 p0 1 #[] 7),
  some (mkVi 24 .MakeResult 35 0 p0 1 #[23, 1] 7)]

/-- The downward loop, the input of `prove`. -/
def downFn : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 24
  bidLast := 8
  blocks := #[1, 7, 8, 2, 3, 4, 5, 6]
  blockTab := #[none,
    some (mkB 1 .If p0 #[5] #[⟨7, 0⟩, ⟨8, 0⟩] #[] #[1, 2, 3, 5, 12, 14]),
    some (mkB 2 .If p0 #[16] #[⟨3, 0⟩, ⟨5, 0⟩] #[⟨8, 0⟩, ⟨4, 0⟩] #[15, 16]),
    some (mkB 3 .If p0 #[18] #[⟨4, 0⟩, ⟨6, 0⟩] #[⟨2, 0⟩] #[18]),
    some (mkB 4 .Plain p0 #[] #[⟨2, 1⟩] #[⟨3, 0⟩] #[17]),
    some (mkB 5 .Ret p0 #[20] #[] #[⟨2, 1⟩] #[20]),
    some (mkB 6 .Ret p0 #[22] #[] #[⟨3, 1⟩] #[21, 22]),
    some (mkB 7 .Ret p0 #[24] #[] #[⟨1, 0⟩] #[23, 24]),
    some (mkB 8 .Plain p0 #[] #[⟨2, 0⟩] #[⟨1, 1⟩] #[13])]
  valueTab := downValues
  names := #[(1, #[2]), (2, #[3])]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[(-1, #[12]), (0, #[14]), (2, #[21]), (1, #[23])]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- By kernel evaluation: the input passes `check`; `proveChecked` turns `b3` into a `First`
block towards `b4` and its result passes `check`; the loop returns `0` for `n = 3`. -/
theorem downFn_checks :
    (check pwCheckEnv downFn).toBool = true ∧
    (proveChecked pwPassEnv downFn).toOption.map
      (fun o => ((check pwCheckEnv o.func).toBool,
        (o.func.block? 3).map (fun b => (b.kind, b.succs.map (·.b))))) =
      some (true, some (.First, #[4, 6])) ∧
    returnsInt (run Env.p1 pwTabs downFn [.i64 1, .i64 3] {} 20) 0 = true := by
  decide +kernel

/-- **Witness of `proveChecked_refines` with a relation**: on the downward loop, the checked
prove removes the bounds check (`b3` becomes `First`), and the output returns `0` for `n = 3`, as
the source does. -/
theorem proveChecked_relWitness :
    ∃ out, proveChecked pwPassEnv downFn = .ok out ∧
      (out.func.block? 3).map (fun b => (b.kind, b.succs.map (·.b))) = some (.First, #[4, 6]) ∧
      RefinesUnder Env.Mono out.tables out.func pwTabs downFn ∧
      ∃ fuel m, run Env.p1 out.tables out.func [.i64 1, .i64 3] {} fuel = .returned [.i64 0] m := by
  obtain ⟨h1, h2, h3⟩ := downFn_checks
  cases hc : proveChecked pwPassEnv downFn with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, hb⟩ := h2
    have hR := ProveCheck.proveChecked_refines hc (ok_of_toBool h1) (ok_of_toBool hg)
    rw [show pwPassEnv.tables = pwTabs from rfl] at hR
    refine ⟨out, rfl, hb, hR, ?_⟩
    obtain ⟨m, hm⟩ := returnsInt_iff.1 h3
    obtain ⟨fuel', ho⟩ := hR Env.p1 Env.p1_mono [.i64 1, .i64 3] {} 20 (by rw [hm]; trivial)
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

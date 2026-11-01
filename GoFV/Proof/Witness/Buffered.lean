import GoFV.Proof.Pass.NilSim
import GoFV.Proof.Witness.DecodedLen
import GoFV.SSA.Check

/-!
# Non-vacuity witness: nilcheckelim on `(*bufio.Reader).Buffered`

`std/std/bufio/(*Reader).Buffered,1.ssa`, the output of section 12 (`gcse deadcode`, the input
of `nilcheckelim`), of the corpus `gofv-corpus/2aae1000ea1d/plain`, transcribed by hand (names,
slots and caches other than the line map omitted: no semantics, and nilcheckelim recomputes the
dominator tree):

```go
func (b *Reader) Buffered() int { return b.w - b.r }
```

`b.w` and `b.r` each nil-check `b` (`v8`, `v11`, both `NilCheck v6 v1`); nilcheckelim turns the
second into `Copy v8` (justified by `v8`, listed before it in the block's schedule) and reorders
the block (`storeOrder`). By kernel evaluation: the pass succeeds, its result is in `nilFrag`,
the input passes `check`, and the source returns `b.w - b.r = 10 - 3 = 7` on a heap `Reader`;
`nilcheck_refines` then gives the output's run.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt

/-- `abiInfo` of `Buffered`: the receiver in an integer register, one result. -/
def bufABI : CallABI :=
  { abi := 1, nin := 1, nout := 1, spillOff := 8, spillSize := 8, inRegs := 1, outRegs := 1,
    params := #[{ out := false, index := 0, type := 2, name := some 3, regs := #[0], offset := 0 },
                { out := true, index := 0, type := 7, name := some 4, regs := #[0],
                  offset := -1 }] }

/-- The definition tables (the types and auxes the function refers to). -/
def bufTabs : Tables where
  types :=
    let t := Array.replicate 41 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "method(*Reader) func() int"
      (.func 1 0 1 #[{ name := GoStr.ofString "b", type := 2, offset := none, embedded := false },
                     { name := GoStr.ofString "", type := 7, offset := none, embedded := false }])))
    let t := t.set! 2 (some (mkT .PTR (some 8) "*Reader" (.elem 3)))
    let t := t.set! 3 (some (mkT .STRUCT (some 88) "Reader"))
    let t := t.set! 7 (some (mkT .INT (some 8) "int"))
    let t := t.set! 26 (some (mkT .PTR (some 8) "*int" (.elem 7)))
    let t := t.set! 34 (some (mkT .SSA none "mem"))
    t.set! 40 (some (mkT .RESULTS none "int,mem" (.results #[7, 34])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{bufio.(*Reader).Buffered}",
           kind := .call (some 2) (some bufABI) },
    some { fmt := GoStr.ofString "bufio.(*Reader).Buffered",
           kind := .sym (GoStr.ofString "bufio.(*Reader).Buffered") 1 "" 0 default none none
             none #[] none },
    some (paramNameT "b" .PPARAM 2 0), some (paramNameT "~r0" .PPARAMOUT 7 0)]

/-- The values, by ID. -/
def bufValues : Array (Option Value) := #[none,
  some (mkVi 1 .InitMem 34 0 p0 5 #[] 1),
  none, none, none, none,
  some (mkV 6 .Arg 2 (some 3) (pos 2 336 6 2) 2 #[] 1),
  none,
  some (mkVi 8 .NilCheck 2 0 (pos 2 336 43 1) 2 #[6, 1] 1),
  some (mkVi 9 .OffPtr 26 48 (pos 2 336 43 0) 1 #[8] 1),
  some (mkVi 10 .Load 7 0 (pos 2 336 43 0) 1 #[9, 1] 1),
  some (mkVi 11 .NilCheck 2 0 (pos 2 336 49 0) 0 #[6, 1] 1),
  some (mkVi 12 .OffPtr 26 40 (pos 2 336 49 0) 1 #[8] 1),
  some (mkVi 13 .Load 7 0 (pos 2 336 49 0) 1 #[12, 1] 1),
  some (mkVi 14 .Sub64 7 0 (pos 2 336 46 0) 1 #[10, 13] 1),
  some (mkVi 15 .MakeResult 40 0 (pos 2 336 35 0) 1 #[14, 1] 1)]

/-- The blocks, by ID. -/
def bufBlocks : Array (Option Block) := #[none,
  some (mkB 1 .Ret (pos 2 336 49 1) #[15] #[] #[] #[1, 6, 8, 9, 10, 11, 12, 13, 14, 15])]

/-- `(*Reader).Buffered`, the input of `nilcheckelim`. -/
def bufIn : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 15
  bidLast := 1
  blocks := #[1]
  blockTab := bufBlocks
  valueTab := bufValues
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := [7, 5, 4, 3, 2]
  freeBlocks := []
  cache := { lineStarts := some #[{ index := 2, bounds := some (336, 336), pending := #[] }] }

def bufTyps : Array (String × TypeRef) := #[("Int", 7), ("IntPtr", 26), ("Mem", 34)]

/-- What `nilcheckelim` reads of the export's environment. -/
def bufPassEnv : PassEnv where
  passName := "nilcheckelim"
  pkg := GoStr.ofString "bufio"
  funcName := GoStr.ofString "(*Reader).Buffered"
  abi := 1
  nosplit := false
  pgohot := false
  config := #[]
  typs := bufTyps
  typeOrder := TypeOrder.ofGroups #[] #[]
  tables := bufTabs

def bufCheckEnv : CheckEnv := { tabs := bufTabs, typs := bufTyps }

/-- Little-endian bytes of a 64-bit integer. -/
def le8 (x : Nat) : List Byte := (List.range 8).map fun i => .b (BitVec.ofNat 8 (x / 2 ^ (8 * i)))

/-- A heap `bufio.Reader` with `r = 3`, `w = 10` (other fields zero). -/
def bufMem : Mem :=
  { blocks := #[(.heap 0, { data := (List.replicate 40 (Byte.b 0) ++ le8 3 ++ le8 10 ++
      List.replicate 32 (Byte.b 0)).toArray })], nextHeap := 1 }

def bufArgs : List Val := [.ptr ⟨.heap 0, 0⟩]

/-! ## Kernel evaluation -/

theorem buf_ok_of_toBool {e : Except String Unit} (h : e.toBool = true) : e = .ok () := by
  revert h; cases e <;> simp [Except.toBool]

theorem bufIn_check : (check bufCheckEnv bufIn).toBool = true := by decide +kernel

/-- The pass succeeds and turns the second nil check into a `Copy`. -/
theorem buf_pass_copy :
    (match nilcheckelimPass bufPassEnv bufIn with
      | .ok out => (out.func.value? 11).map (fun v => (v.op, v.args)) == some (.Copy, #[8])
      | .error _ => false) = true := by
  decide +kernel

theorem buf_nilFrag : nilFrag bufPassEnv bufIn = true := by decide +kernel

/-- `b.w - b.r = 7`, with fuel 1 (one block). -/
theorem bufIn_run : returnsInt (run Env.p1 bufTabs bufIn bufArgs bufMem 1) 7 = true := by
  decide +kernel

/-! ## The witness -/

/-- **Non-vacuity of `nilcheck_refines`**: nilcheckelim removes `Buffered`'s second nil check
(`v11` becomes `Copy v8`), and the output returns the source's result. -/
theorem nilcheck_witness :
    ∃ out, nilcheckelimPass bufPassEnv bufIn = .ok out ∧
      (out.func.value? 11).map (fun v => (v.op, v.args)) = some (.Copy, #[8]) ∧
      ∃ fuel m, run Env.p1 out.tables out.func bufArgs bufMem fuel = .returned [.i64 7] m := by
  have hpc := buf_pass_copy
  cases h : nilcheckelimPass bufPassEnv bufIn with
  | error e => rw [h] at hpc; cases hpc
  | ok out =>
    rw [h] at hpc
    obtain ⟨m, hm⟩ := returnsInt_iff.1 bufIn_run
    obtain ⟨fuel, m', hr⟩ := Refines.returned_int
      (GoFV.Proof.Nil.nilcheck_refines h (buf_ok_of_toBool bufIn_check) buf_nilFrag) hm
    exact ⟨out, rfl, by simpa using hpc, fuel, m', hr⟩

end GoFV.Proof.Witness

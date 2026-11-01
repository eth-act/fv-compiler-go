import GoFV.Proof.Witness.DecodedLen

/-!
# Witness function: `decodedLen` at `generic cse`

`std/std/encoding/base64/decodedLen,1.ssa`, the output of section 9 (`opt deadcode`, the
input of `generic cse`), of the corpus `gofv-corpus/2aae1000ea1d/plain`, transcribed by hand
(the definition tables are `dlTabs`; source in `GoFV.Proof.Witness.DecodedLen`).

zero arg cse merged opt's `Const64 [4]` `v28` into `v13`, so `b3` computes `n/4` twice:
`v14 = Div64 v7 v13` and `v12 = Div64 v7 v13`. generic cse merges `v12` into `v14`, redirecting
`v23` (`Mul64 v12 v13` becomes `Mul64 v13 v14`, its arguments also swapped by class order).
`decodedLenCseOut` and `dlCseRw` transcribe its result (section 10) and substitution.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem

/-- The values, by ID. -/
def dlCseValues : Array (Option Value) := #[none,
  some (mkVi 1 .InitMem 29 0 p0 2 #[] 1),
  none, none, none, none, none,
  some (mkV 7 .Arg 2 (some 3) (pos 2 653 6 2) 4 #[] 1),
  some (mkV 8 .Arg 3 (some 4) (pos 2 653 6 2) 1 #[] 1),
  none,
  some (mkVi 10 .Const32 3 (-1) p0 1 #[] 1),
  some (mkVi 11 .Eq32 4 0 (pos 2 654 13 1) 1 #[8, 10] 1),
  some (mkVi 12 .Div64 2 0 (pos 2 656 19 0) 1 #[7, 13] 3),
  some (mkVi 13 .Const64 2 4 p0 4 #[] 1),
  some (mkVi 14 .Div64 2 0 (pos 2 656 11 1) 1 #[7, 13] 3),
  some (mkVi 15 .Const64 2 3 p0 2 #[] 1),
  some (mkVi 16 .Mul64 2 0 (pos 2 656 13 0) 1 #[14, 15] 3),
  some (mkVi 17 .Sub64 2 0 (pos 2 656 19 0) 1 #[7, 23] 3),
  some (mkVi 18 .Const64 2 6 p0 1 #[] 1),
  some (mkVi 19 .Mul64 2 0 (pos 2 656 21 0) 1 #[17, 18] 3),
  some (mkVi 20 .Const64 2 8 p0 1 #[] 1),
  some (mkVi 21 .Div64 2 0 (pos 2 656 23 0) 1 #[19, 20] 3),
  some (mkVi 22 .Add64 2 0 (pos 2 656 16 0) 1 #[16, 21] 3),
  some (mkVi 23 .Mul64 2 0 (pos 2 656 19 0) 1 #[12, 13] 3),
  some (mkVi 24 .MakeResult 35 0 (pos 2 656 3 0) 1 #[22, 1] 3),
  none,
  some (mkVi 26 .Div64 2 0 (pos 2 659 11 1) 1 #[7, 13] 2),
  some (mkVi 27 .Mul64 2 0 (pos 2 659 15 0) 1 #[26, 15] 2),
  none,
  some (mkVi 29 .MakeResult 35 0 (pos 2 659 2 0) 1 #[27, 1] 2)]

/-- The blocks, by ID. -/
def dlCseBlocks : Array (Option Block) := #[none,
  some (mkB 1 .If (pos 2 654 16 0) #[11] #[⟨3, 0⟩, ⟨2, 0⟩] #[] #[1, 7, 8, 10, 11, 13, 15, 18, 20]),
  some (mkB 2 .Ret (pos 2 659 17 1) #[29] #[] #[⟨1, 1⟩] #[26, 27, 29]),
  some (mkB 3 .Ret (pos 2 656 24 1) #[24] #[] #[⟨1, 0⟩]
    #[14, 16, 17, 19, 21, 22, 24, 23, 12])]

/-- `decodedLen`, the input of `generic cse`. -/
def decodedLenCse : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 29
  bidLast := 3
  blocks := #[1, 2, 3]
  blockTab := dlCseBlocks
  valueTab := dlCseValues
  names := #[(1, #[7]), (2, #[8])]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[(-1, #[10]), (3, #[15]), (4, #[13]), (6, #[18]), (8, #[20])]
  freeValues := [28, 25, 9, 6, 5, 4, 3, 2]
  freeBlocks := []
  cache := {}

/-- The values of cse's result (section 10, `generic cse`): `v12` unused, `v14` used twice,
`v16`, `v19`, `v23` and `v27` with their arguments in class order. -/
def dlCseOutValues : Array (Option Value) := #[none,
  some (mkVi 1 .InitMem 29 0 p0 2 #[] 1),
  none, none, none, none, none,
  some (mkV 7 .Arg 2 (some 3) (pos 2 653 6 2) 4 #[] 1),
  some (mkV 8 .Arg 3 (some 4) (pos 2 653 6 2) 1 #[] 1),
  none,
  some (mkVi 10 .Const32 3 (-1) p0 1 #[] 1),
  some (mkVi 11 .Eq32 4 0 (pos 2 654 13 1) 1 #[8, 10] 1),
  some (mkVi 12 .Div64 2 0 (pos 2 656 19 0) 0 #[7, 13] 3),
  some (mkVi 13 .Const64 2 4 p0 4 #[] 1),
  some (mkVi 14 .Div64 2 0 (pos 2 656 11 1) 2 #[7, 13] 3),
  some (mkVi 15 .Const64 2 3 p0 2 #[] 1),
  some (mkVi 16 .Mul64 2 0 (pos 2 656 13 0) 1 #[15, 14] 3),
  some (mkVi 17 .Sub64 2 0 (pos 2 656 19 0) 1 #[7, 23] 3),
  some (mkVi 18 .Const64 2 6 p0 1 #[] 1),
  some (mkVi 19 .Mul64 2 0 (pos 2 656 21 0) 1 #[18, 17] 3),
  some (mkVi 20 .Const64 2 8 p0 1 #[] 1),
  some (mkVi 21 .Div64 2 0 (pos 2 656 23 0) 1 #[19, 20] 3),
  some (mkVi 22 .Add64 2 0 (pos 2 656 16 0) 1 #[16, 21] 3),
  some (mkVi 23 .Mul64 2 0 (pos 2 656 19 0) 1 #[13, 14] 3),
  some (mkVi 24 .MakeResult 35 0 (pos 2 656 3 0) 1 #[22, 1] 3),
  none,
  some (mkVi 26 .Div64 2 0 (pos 2 659 11 1) 1 #[7, 13] 2),
  some (mkVi 27 .Mul64 2 0 (pos 2 659 15 0) 1 #[15, 26] 2),
  none,
  some (mkVi 29 .MakeResult 35 0 (pos 2 659 2 0) 1 #[27, 1] 2)]

/-- cse's result: the values above, and the caches it computed (postorder, dominator tree, its
aux numbering), as section 10 exports them. -/
def decodedLenCseOut : Func :=
  { decodedLenCse with
    valueTab := dlCseOutValues
    cache := {
      postorder := some #[3, 2, 1]
      idom := some #[none, none, some 1, some 1]
      sdom := some #[⟨none, none, none, 0, 0⟩, ⟨none, some 2, none, 2, 17⟩,
        ⟨some 1, none, some 3, 5, 8⟩, ⟨some 1, none, none, 11, 14⟩]
      auxmap := some #[(some 3, 1), (some 4, 2), (none, 3)] } }

/-- cse's substitution: `v12` is replaced by `v14`. -/
def dlCseRw : Array (Option ID) := (Array.replicate 30 none).set! 12 (some 14)

/-- `decodedLen(10, NoPadding) = 7`, with fuel 2 (entry, then `b3`). -/
theorem decodedLenCse_run :
    returnsInt (run Env.p1 dlTabs decodedLenCse dlArgs {} 2) 7 = true := by
  decide +kernel

/-- cse's result returns the same. -/
theorem decodedLenCseOut_run :
    returnsInt (run Env.p1 dlTabs decodedLenCseOut dlArgs {} 2) 7 = true := by
  decide +kernel

end GoFV.Proof.Witness

import GoFV.Gen.Check38

/-!
# The genssa validator, slice G39: the homes of removed values (`docs/plans/proofs3.md` §4)

`regalloc` records a home for every value it allocated; passes after it (`trim`) remove values,
e.g. the `Phi`s of a block `trim` merges into its predecessor, and the export keeps their homes. Such
a home belongs to no value of the function: `runLoc` reads homes only of the values it runs, their
arguments and the blocks' controls, which are values of the function. The shape of a removed value
is `Ty.other` (`valueTy`), so G1's home check (`homeOK`, a register value has a class) rejected the
function for it.

`checkG39 lc ps bstart g` checks that every argument of a value of the function is a value of the
function, and the value's own ID too (`refsLive`), and is then slice G38 (`GoFV/Gen/Check38.lean`)
on `liveCtx lc`: `lc` with the homes of the IDs that are no value of the function dropped.
`GoFV/Proof/Gen/G39.lean` proves that `runLoc` runs alike under `lc` and `liveCtx lc`
(`runLoopLoc_live`) and what an accepted function satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- `lc` with the homes of the IDs that are no value of the function dropped. -/
def liveCtx (lc : LocCtx) : LocCtx :=
  { lc with homes := lc.homes.mapIdx fun i h => if (lc.ctx.f.value? i).isSome then h else none }

/-- Every value of the function is at its own ID, and its arguments are values of the function. -/
def refsLive (lc : LocCtx) : Bool :=
  (List.range lc.ctx.f.valueTab.size).all fun i => match lc.ctx.f.value? i with
    | some v => (lc.ctx.f.value? v.id).isSome && v.args.all fun a => (lc.ctx.f.value? a).isSome
    | none => true

/-- Slice G39 of the genssa validator (module doc): `refsLive`, then G38's check on `liveCtx lc`. -/
def checkG39 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless refsLive lc do throw "a value refers to an ID that is no value of the function"
  checkG38 (liveCtx lc) ps bstart g

end GoFV.Gen.Check

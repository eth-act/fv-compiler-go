import GoFV.Gen.Check42

/-!
# The genssa validator, slice G43: `InitMem` where the memory is still the initial one
(`docs/plans/proofs3.md` §4)

G40 accepts `InitMem` after the entry values only in a function whose values all keep the memory
(`memPure`). In a function that also calls or stores, `schedule` may still place `InitMem` in a
block that no such value precedes on any path from the entry (the stores and calls sit in blocks
that end in a panic, or after `InitMem` in its block). There the state's memory is still the
activation's initial memory, so `InitMem` changes nothing and emits no code.

`cleanBlocks lc` are the blocks no block with a value that changes the memory (`memKeep` false)
reaches in one step or more; `cleanOK lc C` checks that `C` is closed backwards: a predecessor of
a block of `C` is in `C` and all its values keep the memory. A position `(b, i)` is clean
(`cleanAt`) when `b ∈ C` and the values of `b` before `i` keep the memory: the state there holds
the initial memory, since the run starts with it and every step to a clean position keeps it.

`checkG43 lc ps bstart g` is slice G42 (`GoFV/Gen/Check42.lean`) with, in a function with an arm64
op where `cleanOK lc (cleanBlocks lc)` holds, `InitMem` at clean positions: no temporary, no
argument, no home, of shape `mem`; no code. `GoFV/Proof/Gen/G43.lean` proves what an accepted
function satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The values of block `b` before index `i` keep the memory. -/
def keepsTo (lc : LocCtx) (b : Block) (i : Nat) : Bool :=
  (List.range i).all fun j => (b.values[j]?.bind lc.ctx.f.value?).all (memKeep lc)

/-- The blocks some block with a value that changes the memory reaches in one step or more. -/
def dirtyReach (lc : LocCtx) : List ID := Id.run do
  let bids := lc.ctx.f.blocks.toList
  let succsOf (bid : ID) : List ID :=
    ((lc.ctx.f.block? bid).map fun b => b.succs.toList.map (·.b)).getD []
  let src := bids.filter fun bid => (lc.ctx.f.block? bid).any fun b => !keepsTo lc b b.values.size
  let mut r : List ID := src.flatMap succsOf
  for _ in [0:bids.length] do
    r := (r ++ r.flatMap succsOf).eraseDups
  return r

/-- The blocks no value that changes the memory precedes (module doc). -/
def cleanBlocks (lc : LocCtx) : List ID :=
  let r := dirtyReach lc
  lc.ctx.f.blocks.toList.filter (!r.contains ·)

/-- `C` is closed backwards: a block with a successor in `C` is in `C`, and its values keep the
memory. -/
def cleanOK (lc : LocCtx) (C : List ID) : Bool :=
  lc.ctx.f.blocks.toList.all fun bid => (lc.ctx.f.block? bid).all fun b =>
    b.succs.all fun e => !C.contains e.b || (C.contains bid && keepsTo lc b b.values.size)

/-- Position `i` of block `bid` (`b`) is clean: `bid ∈ C`, and the values before `i` keep the
memory. -/
def cleanAt (lc : LocCtx) (C : List ID) (bid : ID) (b : Block) (i : Nat) : Bool :=
  C.contains bid && keepsTo lc b i

/-- Every position of `v` in a block of the function is clean. -/
def initMemClean (lc : LocCtx) (C : List ID) (v : Value) : Bool :=
  lc.ctx.f.blocks.toList.all fun bid => (lc.ctx.f.block? bid).all fun b =>
    (List.range b.values.size).all fun i => b.values[i]? != some v.id || cleanAt lc C bid b i

/-- What `v` emits in G43, or why it is outside the slice: `InitMem` at clean positions only (in a
function whose values keep the memory every position is clean), any other value as G42. -/
def vkind43 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  if v.op == .InitMem then
    if cleanOK lc (cleanBlocks lc) && initMemClean lc (cleanBlocks lc) v then initMemKind lc v
    else throw s!"v{v.id}: InitMem after the entry values"
  else vkind42 lc g v

/-- G42's check with G43's value check. -/
def checkG43L (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind43 lc g, tm := cx.termG3 }
    let tab ← c.blocks lc.ctx.f.blocks.toList
    unless pbOK lc ps.toList tab do throw "bounds panic PCDATA"
    unless movdOK35 lc && uEdgesOK35 lc do throw "MOVDnop/MOVDreg: upper bits unknown"
    if let some i := (List.range lc.homes.size).find? (!homeOK10 lc ·) then throw (homeErr lc i)
    unless cloFirst lc do throw "LoweredGetClosurePtr after code"
    checkFrame lc g
    checkVars lc g
    let kin := kFlow lc (65 * lc.ctx.f.blocks.size + 2)
    let kt : KTab := lc.ctx.f.blocks.toList.map fun b => (b, (kin[b]?).getD KMap.bot)
    checkK lc kt
    let ids := ps.toList.map (·.id)
    unless ids.all (· < 2 ^ 32) && ids.Nodup do throw "Prog IDs"
    return (tab, kt)
  else checkNL30 lc ps bstart g

/-- Slice G43 of the genssa validator (module doc): `refsLive`, then G43's check on `liveCtx lc`. -/
def checkG43 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless refsLive lc do throw "a value refers to an ID that is no value of the function"
  checkG43L (liveCtx lc) ps bstart g

end GoFV.Gen.Check

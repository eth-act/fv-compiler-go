import GoFV.Gen.Check4

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G5: memory markers (`docs/plans/proofs3.md` §4)

`checkG5 lc ps bstart g` extends slice G4 (`GoFV/Gen/Check4.lean`) by the memory ops genssa emits
no code for (`Genssa.lean`'s value loop): they change only Phase 1's memory, which the machine
does not see.

**Values** beyond G4's (`vkind5`), each of the memory shape with no home, its memory argument last:

* `VarDef {x} mem`: a `PAUTO` `x`'s block becomes poison (`Mem.poisonBlock`), for any other `x`
  the memory is unchanged (`Sem.varDefMem`);
* `VarLive {x} mem` and `KeepAlive a mem`: the memory unchanged;
* `WBend mem`: the write-barrier buffer is freed (`Mem.free .wbuf`).

`GoFV/Proof/Gen/G5.lean` proves what an accepted function satisfies (`g5_value`, `g5_term`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The memory markers: their number of arguments (the memory last). -/
def markOp? : Op → Option Nat
  | .VarDef | .VarLive | .WBend => some 1
  | .KeepAlive => some 2
  | _ => none

/-- What `v` emits in G5, or why it is outside the slice. -/
def vkind5 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 := do
  let some n := markOp? v.op | vkind4 lc g v
  if (lc.temps[v.id]?).join != none then throw s!"v{v.id}: temporary register"
  unless v.args.size == n && memTy (lc.ty v.id) && lc.home v.id == none do
    throw s!"v{v.id}: marker shape"
  memArg lc v (n - 1)
  return .none

/-- Slice G5 of the genssa validator (module doc): G4's tables of the accepted function. -/
def checkG5 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless lc.ctx.f.lowered do throw "not lowered"
  let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
  let cx : Cx := { lc, ps, idx, bstart }
  let c : Cx2 := { cx, g, vk := vkind5 lc g, tm := cx.termG3 }
  let tab ← c.blocks lc.ctx.f.blocks.toList
  if let some i := (List.range lc.homes.size).find? (!homeOK4 lc ·) then throw (homeErr lc i)
  checkFrame lc g
  let kin := kFlow lc (65 * lc.ctx.f.blocks.size + 2)
  let kt : KTab := lc.ctx.f.blocks.toList.map fun b => (b, (kin[b]?).getD KMap.bot)
  checkK lc kt
  let ids := ps.toList.map (·.id)
  unless ids.all (· < 2 ^ 32) && ids.Nodup do throw "Prog IDs"
  return (tab, kt)

end GoFV.Gen.Check

import GoFV.Gen.Check22
import GoFV.Asm.OpAsm

/-!
# The genssa validator, slice G23: flags to a register (`docs/plans/proofs3.md` §4)

`checkG23 lc ps bstart g` extends slice G22 (`GoFV/Gen/Check22.lean`) by the arm64 comparison
pseudo-ops `Equal`, `NotEqual`, `LessThan`, …, `GreaterEqualU` and their floating-point and
`Noov` forms (`Cond.ofOp`), which genssa emits as `CSET cond, Rd` (`ssa.go`, `condBits`): the
register gets 1 when the condition holds on `NZCV`, else 0. `runLoc` runs them as `Arm64.cset`:
the boolean the condition gives on its flags argument (`Cond.onVal`), `poison` when a flag bit it
reads is unknown.

G23 accepts such a value with no temporary, one argument of the flags shape with no home (the
flags register), a boolean result in a register G1 may write.

`GoFV/Proof/Gen/G23.lean` proves what an accepted function satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The `SPECIAL` operand of a condition (`SPOP_EQ` …), as genssa's `CSET` has it. -/
def specA (o : Int) : Addr := { type := .SPECIAL, offset := o }

/-- A comparison pseudo-op (`cond`, from its flags argument, as `CSET cond, Rd`): no temporary,
one argument of the flags shape with no home, a boolean result in a register G1 may write. -/
def csetKind (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  let some cc := ARM64.condBits v.op | throw s!"v{v.id}: op {v.op.name}"
  unless v.args.size == 1 do throw s!"v{v.id}: condition shape"
  let some a := v.args[0]? | throw s!"v{v.id}: condition shape"
  unless (lc.ty a).isFlags && lc.home a == none do throw s!"v{v.id}: condition argument"
  let (c, rd) ← resObj lc v
  unless c == 1 do throw s!"v{v.id}: condition result shape"
  return .prog ⟨plain .CSET (· == specA cc) (· == regA rd), "CSET"⟩

/-- What `v` emits in G23, or why it is outside the slice. -/
def vkind23 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  if (Cond.ofOp v.op).isSome then csetKind lc v else vkind22 lc g v

/-- Slice G23 of the genssa validator (module doc): G4's tables of the accepted function. -/
def checkG23 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless lc.ctx.f.lowered do throw "not lowered"
  let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
  let cx : Cx := { lc, ps, idx, bstart }
  let c : Cx2 := { cx, g, vk := vkind23 lc g, tm := cx.termG3 }
  let tab ← c.blocks lc.ctx.f.blocks.toList
  unless pbOK lc ps.toList tab do throw "bounds panic PCDATA"
  unless movdOK lc do throw "MOVDnop/MOVDreg: upper bits unknown"
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

end GoFV.Gen.Check

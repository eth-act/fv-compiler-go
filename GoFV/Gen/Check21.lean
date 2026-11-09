import GoFV.Gen.Check20

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G21: `MOVDreg` after its narrow load (`docs/plans/proofs3.md` §4, §8)

`checkG21 lc ps bstart g` extends slice G20 (`GoFV/Gen/Check20.lean`) by `MOVDreg x`, which genssa
emits as `Copy` does (`ssa.go:579`, `genCopy`): nothing when `x` and the value share a register,
else `MOVD Rx, Rv`. `runLoc` runs it as `MOVDnop`, `movdLoc`: the 64-bit zero or sign extension
of `x`'s low bits that `LocCtx.signOf` names; the machine register holds that word when `x`'s
register does, which G20's upper-bit table `uAt` says (`movdOK`).

G21 accepts `MOVDreg x` with no temporary, `x` its only argument, in a register at class 8, 16 or
32, the value in a register G1 may write at an integer class (`movRegKind`), when the table before
it names `x`'s register at `x`'s class with the signedness `signOf` gives `x` (`movdOK`, shared
with `MOVDnop`).

`GoFV/Proof/Gen/G21.lean` proves what an accepted function satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- `MOVDreg x`: no temporary, one argument in a register other than `ZERO` at class 8, 16 or 32,
the value in a register G1 may write at class 8, 16, 32 or 64; nothing when the registers agree,
else `MOVD Rx, Rv`. -/
def movRegKind (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 1 do throw s!"v{v.id}: MOVDreg shape"
  let (ca, ra) ← argObj lc v 0
  let (cd, rd) ← resObj lc v
  unless ra != ARM64.REGZERO do throw s!"v{v.id}: MOVDreg of ZERO"
  unless ca == 8 || ca == 16 || ca == 32 do throw s!"v{v.id}: MOVDreg widths"
  unless cd == 8 || cd == 16 || cd == 32 || cd == 64 do throw s!"v{v.id}: MOVDreg widths"
  if ra == rd then return .none
  return .prog (.ofShape { as := .MOVD, from_ := regA ra, to := regA rd })

/-- What `v` emits in G21, or why it is outside the slice. -/
def vkind21 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  if v.op == .ARM64MOVDreg then movRegKind lc v else vkind20 lc g v

/-- Slice G21 of the genssa validator (module doc): G4's tables of the accepted function. -/
def checkG21 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless lc.ctx.f.lowered do throw "not lowered"
  let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
  let cx : Cx := { lc, ps, idx, bstart }
  let c : Cx2 := { cx, g, vk := vkind21 lc g, tm := cx.termG3 }
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

import GoFV.Gen.Check13

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G14: register-index loads (`docs/plans/proofs3.md` §4)

`checkG14 lc ps bstart g` extends slice G13 (`GoFV/Gen/Check13.lean`) by the integer
register-index loads `MOV{D,W,WU,H,HU,B,BU}loadidx ptr idx mem` and their scaled forms
`MOV{H,HU}loadidx2`, `MOV{W,WU}loadidx4`, `MOVDloadidx8` (`loadIdxOp?`): Phase 1's
`Arm64.loadIdx`, the `n` bytes at `ptr + idx · 2^sh`. Genssa emits one load from the operand of
`genIndexedOperand` (`ssa.go:155`, `GoFV/Gen/Arm64Value.lean`): base register `Rp`, index
register `Ri`, unscaled (`(Rp)(Ri)`) or shifted left by `sh` (`(Rp)(Ri<<sh)`, the index
`REG_LSL + 32·sh + (Ri & 31)`; `idxA`).

G14 accepts it with no temporary, `ptr` and `idx` in registers of class 64, the memory last, the
destination as a load's (`vkind3`: at least 8 bits, or a boolean loaded by `MOVBU`).

`GoFV/Proof/Gen/G14.lean` proves what an accepted function satisfies (`g14_value`, `g14_term`,
`g14_nilPanic`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The integer register-index loads: opcode, bytes, index shift, sign extension. -/
def loadIdxOp? : Op → Option (As × Nat × Nat × Bool)
  | .ARM64MOVDloadidx => some (.MOVD, 8, 0, false)
  | .ARM64MOVWloadidx => some (.MOVW, 4, 0, true)
  | .ARM64MOVWUloadidx => some (.MOVWU, 4, 0, false)
  | .ARM64MOVHloadidx => some (.MOVH, 2, 0, true)
  | .ARM64MOVHUloadidx => some (.MOVHU, 2, 0, false)
  | .ARM64MOVBloadidx => some (.MOVB, 1, 0, true)
  | .ARM64MOVBUloadidx => some (.MOVBU, 1, 0, false)
  | .ARM64MOVHloadidx2 => some (.MOVH, 2, 1, true)
  | .ARM64MOVHUloadidx2 => some (.MOVHU, 2, 1, false)
  | .ARM64MOVWloadidx4 => some (.MOVW, 4, 2, true)
  | .ARM64MOVWUloadidx4 => some (.MOVWU, 4, 2, false)
  | .ARM64MOVDloadidx8 => some (.MOVD, 8, 3, false)
  | _ => none

/-- The memory operand `(Rn)(Ri)` (`sh = 0`) or `(Rn)(Ri<<sh)` of obj registers `rn`, `ri`:
`genIndexedOperand`'s, the shifted index `REG_LSL ||| sh <<< 5 ||| (ri &&& 31)` written as a
sum (`ri` is `REG_R0 + k`, `k < 32`). -/
def idxA (rn ri : Int) (sh : Nat) : Addr :=
  { type := .MEM, reg := rn,
    index := if sh = 0 then ri else ARM64.REG_LSL + 32 * sh + (ri - ARM64.REG_R0) }

/-- A register-index load: no temporary, three arguments, `ptr` and `idx` in registers of class
64, the memory last, the destination as a load's; one load from `idxA`. -/
def idxKind (lc : LocCtx) (v : Value) (as : As) (n sh : Nat) (sg : Bool) :
    Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 3 do throw s!"v{v.id}: indexed load shape"
  let (ca, rn) ← argObj lc v 0
  let (ci, ri) ← argObj lc v 1
  unless ca == 64 && ci == 64 do throw s!"v{v.id}: indexed load widths"
  memArg lc v 2
  let (c, rd) ← resObj lc v
  unless 8 ≤ c || (c == 1 && n == 1 && !sg) do throw s!"v{v.id}: load widths"
  return .prog ⟨plain as (· == idxA rn ri sh) (· == regA rd), as.name⟩

/-- What `v` emits in G14, or why it is outside the slice. -/
def vkind14 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  match loadIdxOp? v.op with
  | some (as, n, sh, sg) => idxKind lc v as n sh sg
  | none => vkind13 lc g v

/-- Slice G14 of the genssa validator (module doc): G4's tables of the accepted function. -/
def checkG14 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless lc.ctx.f.lowered do throw "not lowered"
  let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
  let cx : Cx := { lc, ps, idx, bstart }
  let c : Cx2 := { cx, g, vk := vkind14 lc g, tm := cx.termG3 }
  let tab ← c.blocks lc.ctx.f.blocks.toList
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

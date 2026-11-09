import GoFV.Gen.Check17

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G18: register-index stores (`docs/plans/proofs3.md` §4)

`checkG18 lc ps bstart g` extends slice G17 (`GoFV/Gen/Check17.lean`) by the integer
register-index stores `MOV{D,W,H,B}storeidx ptr idx val mem` and their scaled forms
`MOVHstoreidx2`, `MOVWstoreidx4`, `MOVDstoreidx8` (`storeIdxOp?`): Phase 1's `stIdx` (`arm64Op`),
the `n`-byte store of `val` at `ptr + idx · 2^sh`. Genssa emits one store to the operand of
`genIndexedOperand` (`ssa.go:155`), as for the register-index loads of G14 (`idxA`).

G18 accepts it with no temporary, the memory shape and no home, `ptr` and `idx` in registers of
class 64, `val` in a register as a store's (`vkind3`: at least `8n` bits, or a boolean byte), the
memory last.

`GoFV/Proof/Gen/G18.lean` proves what an accepted function satisfies (`g18_value`, `g18_term`,
`g18_nilPanic`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The integer register-index stores: opcode, bytes, index shift. -/
def storeIdxOp? : Op → Option (As × Nat × Nat)
  | .ARM64MOVDstoreidx => some (.MOVD, 8, 0)
  | .ARM64MOVWstoreidx => some (.MOVW, 4, 0)
  | .ARM64MOVHstoreidx => some (.MOVH, 2, 0)
  | .ARM64MOVBstoreidx => some (.MOVB, 1, 0)
  | .ARM64MOVHstoreidx2 => some (.MOVH, 2, 1)
  | .ARM64MOVWstoreidx4 => some (.MOVW, 4, 2)
  | .ARM64MOVDstoreidx8 => some (.MOVD, 8, 3)
  | _ => none

/-- A register-index store: no temporary, four arguments, the memory shape and no home, `ptr` and
`idx` in registers of class 64, `val` in a register of at least `8n` bits (or a boolean byte), the
memory last; one store to `idxA`. -/
def stIdxKind (lc : LocCtx) (v : Value) (as : As) (n sh : Nat) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 4 && memTy (lc.ty v.id) && lc.home v.id == none do
    throw s!"v{v.id}: indexed store shape"
  let (ca, rn) ← argObj lc v 0
  let (ci, ri) ← argObj lc v 1
  unless ca == 64 && ci == 64 do throw s!"v{v.id}: indexed store widths"
  let (cs, rs) ← argObj lc v 2
  unless 8 * n ≤ cs || (cs == 1 && n == 1) do throw s!"v{v.id}: store widths"
  memArg lc v 3
  return .prog ⟨plain as (· == regA rs) (· == idxA rn ri sh), as.name⟩

/-- What `v` emits in G18, or why it is outside the slice. -/
def vkind18 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  match storeIdxOp? v.op with
  | some (as, n, sh) => stIdxKind lc v as n sh
  | none => vkind17 lc g v

/-- Slice G18 of the genssa validator (module doc): G4's tables of the accepted function. -/
def checkG18 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless lc.ctx.f.lowered do throw "not lowered"
  let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
  let cx : Cx := { lc, ps, idx, bstart }
  let c : Cx2 := { cx, g, vk := vkind18 lc g, tm := cx.termG3 }
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

import GoFV.Gen.Check26

/-!
# The genssa validator, slice G27: shifted logic ops (`docs/plans/proofs3.md` §4)

`checkG27 lc ps bstart g` extends slice G26 (`GoFV/Gen/Check26.lean`) by `ANDshiftXX`,
`ORshiftXX`, `XORshiftXX` and `BICshiftXX [k] x y`, with `XX` one of `LL`, `RL`, `RA`:
`x op (y SHIFT k)`. genssa emits one `AND`/`ORR`/`EOR`/`BIC Rm SHIFT k, Rn, Rd` (`genshift`,
`ssa.go:141`), whose source operand is `makeshift`'s (`ssa.go:133`): `TYPE_SHIFT` with offset
`(Rm & 31) << 16 | typ | k << 10`, `typ` = `SHIFT_LL`, `SHIFT_LR` or `SHIFT_AR` (`shiftA`).

G27 accepts such a value with no temporary, two register arguments and a result of at least 8
bits no wider than `x`, with the shift amount in `[0, 64)` (`makeshift` rejects any other). The
low bits of `y << k` are those of `y`, so for `LL`, `y`'s class must be at least the result's.
A right shift reads `y`'s upper bits, so for `RL` and `RA`, `y` must have class 64.
`GoFV/Proof/Gen/G27.lean` proves what an accepted function satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- `makeshift`'s operand for obj register `rm` (`REG_R0 + k`, `k < 32`) shifted by `s` of kind
`typ` (0 `LSL`, 1 `LSR`, 2 `ASR`): `k << 16 | typ << 22 | s << 10`, written as a sum. -/
def shiftA (typ : Nat) (rm : Int) (s : Nat) : Addr :=
  { type := .SHIFT, offset := (rm - ARM64.REG_R0) * 65536 + typ * 4194304 + s * 1024 }

/-- A shifted logic op: its opcode and its shift kind (0 `LSL`, 1 `LSR`, 2 `ASR`). -/
def logSh? : Op → Option (As × Nat)
  | .ARM64ANDshiftLL => some (.AND, 0) | .ARM64ANDshiftRL => some (.AND, 1)
  | .ARM64ANDshiftRA => some (.AND, 2)
  | .ARM64ORshiftLL => some (.ORR, 0) | .ARM64ORshiftRL => some (.ORR, 1)
  | .ARM64ORshiftRA => some (.ORR, 2)
  | .ARM64XORshiftLL => some (.EOR, 0) | .ARM64XORshiftRL => some (.EOR, 1)
  | .ARM64XORshiftRA => some (.EOR, 2)
  | .ARM64BICshiftLL => some (.BIC, 0) | .ARM64BICshiftRL => some (.BIC, 1)
  | .ARM64BICshiftRA => some (.BIC, 2)
  | _ => none

/-- A shifted logic op `x op (y SHIFT k)`: no temporary, two register arguments, a result of at
least 8 bits no wider than `x`, `y` at least as wide (`LL`) or of class 64 (`RL`, `RA`),
`0 ≤ k < 64`; one `op Rm SHIFT k, Rn, Rd`. -/
def logShKind (lc : LocCtx) (v : Value) (as : As) (typ : Nat) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 2 do throw s!"v{v.id}: shape"
  unless 0 ≤ v.auxInt.toInt && v.auxInt.toInt < 64 do throw s!"v{v.id}: shift amount"
  let (ca, rn) ← argObj lc v 0
  let (cb, rm) ← argObj lc v 1
  let (c, rd) ← resObj lc v
  unless 8 ≤ c && c ≤ ca && (if typ == 0 then c ≤ cb else cb == 64) do
    throw s!"v{v.id}: shifted logic widths"
  return .prog (.ofShape
    { as, from_ := shiftA typ rm v.auxInt.toInt.toNat, reg := rn, to := regA rd })

/-- What `v` emits in G27, or why it is outside the slice. -/
def vkind27 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  match logSh? v.op with
  | some (as, typ) => logShKind lc v as typ
  | none => vkind25 lc g v

/-- Slice G27 of the genssa validator (module doc): G26 with G27's value check. -/
def checkG27 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind27 lc g, tm := cx.termG3 }
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
  else checkNL lc ps bstart g

end GoFV.Gen.Check

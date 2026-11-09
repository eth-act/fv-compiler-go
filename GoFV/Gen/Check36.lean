import GoFV.Gen.Check35

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G36: register shifts, shifted adds and subtracts, `TST`
(`docs/plans/proofs3.md` §4)

`checkG36 lc ps bstart g` is slice G35 (`GoFV/Gen/Check35.lean`) with more single-instruction ops
in a function with an arm64 op:

* `SLL x y`, `SRL x y`, `SRA x y` (`sh36?`): `LSL`/`LSR`/`ASR Rm, Rn, Rd`, `x` shifted by `y`
  modulo 64. The amount is `y`'s low 6 bits, so `y` of any class of at least 8 bits; bit `i` of
  `x << s` is bit `i - s` of `x`, so `SLL` of an `x` of class at least the result's, and `SRL`,
  `SRA` (whose low bits read `x`'s high ones) of a 64-bit `x`;
* `ADDshiftRL`, `ADDshiftRA`, `SUBshiftLL`, `SUBshiftRL`, `SUBshiftRA [k] x y` (`shOp36?`,
  `0 ≤ k < 64`): `ADD`/`SUB Rm>>k, Rn, Rd` (the shifted source operand of `makeshift`, G27's
  `shiftA`),
  `x ± (y` shifted by `k)`, with `ADD`'s pointer case for a pointer `x` (Phase 1's `addSh`,
  `subSh`), as G16's `ADDshiftLL`: `x` of class at least the result's, and `y` too for `SUBshiftLL`
  (bit `i` of `y << k` is bit `i - k` of `y`), else of 64 bits;
* `TST x y`: `TST Rm, Rn`, the flags of `x & y`, of two 64-bit arguments; its result is the flags,
  with no home.

An ALU op has no temporary and a result of class `c ≥ 8`. The G36 ops empty the upper-bit table
(`uStep35` is `uStepL` on them).

On a function with no arm64 op, `checkG36` is `checkG33`'s `checkNL30`.
`GoFV/Proof/Gen/G36.lean` proves what an accepted function satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The register shifts and their opcode: `op Rm, Rn, Rd`. -/
def sh36? : Op → Option As
  | .ARM64SLL => some .LSL | .ARM64SRL => some .LSR | .ARM64SRA => some .ASR
  | _ => none

/-- The shifted adds and subtracts of G36: opcode and shift kind (0 `LSL`, 1 `LSR`, 2 `ASR`, as
G27's `logSh?`). -/
def shOp36? : Op → Option (As × Nat)
  | .ARM64ADDshiftRL => some (.ADD, 1) | .ARM64ADDshiftRA => some (.ADD, 2)
  | .ARM64SUBshiftLL => some (.SUB, 0) | .ARM64SUBshiftRL => some (.SUB, 1)
  | .ARM64SUBshiftRA => some (.SUB, 2)
  | _ => none

/-- A register shift `x op y` (module doc): what it emits. -/
def sh36Kind (lc : LocCtx) (v : Value) (as : As) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 2 do throw s!"v{v.id}: shape"
  let (ca, rn) ← argObj lc v 0
  let (cb, rm) ← argObj lc v 1
  let (c, rd) ← resObj lc v
  unless 8 ≤ c && 8 ≤ cb && (if as == .LSL then c ≤ ca else ca == 64) do
    throw s!"v{v.id}: {v.op.name} widths"
  return .prog (.ofShape { as, from_ := regA rm, reg := rn, to := regA rd })

/-- A shifted add or subtract `x ± (y` shifted by `k)` (module doc): what it emits. -/
def shOp36Kind (lc : LocCtx) (v : Value) (as : As) (typ : Nat) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 2 do throw s!"v{v.id}: shape"
  unless 0 ≤ v.auxInt.toInt && v.auxInt.toInt < 64 do throw s!"v{v.id}: shift amount"
  let (ca, rn) ← argObj lc v 0
  let (cb, rm) ← argObj lc v 1
  let (c, rd) ← resObj lc v
  unless 8 ≤ c && c ≤ ca && (if typ == 0 then c ≤ cb else cb == 64) do
    throw s!"v{v.id}: arithmetic widths"
  return .prog (.ofShape
    { as, from_ := shiftA typ rm v.auxInt.toInt.toNat, reg := rn, to := regA rd })

/-- `TST x y` (module doc): what it emits. -/
def tst36Kind (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 2 && (lc.ty v.id).isFlags && lc.home v.id == none do
    throw s!"v{v.id}: compare shape"
  let (ca, rn) ← argObj lc v 0
  let (cb, rm) ← argObj lc v 1
  unless ca == 64 && cb == 64 do throw s!"v{v.id}: compare widths"
  return .prog (.ofShape { as := .TST, from_ := regA rm, reg := rn })

/-- What `v` emits in G36, or why it is outside the slice. -/
def vkind36 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  match sh36? v.op, shOp36? v.op with
  | some as, _ => sh36Kind lc v as
  | none, some (as, typ) => shOp36Kind lc v as typ
  | none, none => if v.op == .ARM64TST then tst36Kind lc v else vkind33 lc g v

/-- Slice G36 of the genssa validator (module doc): G35's check with G36's value check. -/
def checkG36 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind36 lc g, tm := cx.termG3 }
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

end GoFV.Gen.Check

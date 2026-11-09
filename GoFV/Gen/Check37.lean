import GoFV.Gen.Check36

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G37: multiplies, divides, byte and bit reversals, `SBFX`
(`docs/plans/proofs3.md` §4)

`checkG37 lc ps bstart g` is slice G36 (`GoFV/Gen/Check36.lean`) with more single-instruction ops
in a function with an arm64 op:

* `UMULH`, `MULH`, `UDIV`, `DIV x y` (`full37?`): `UMULH`/`SMULH`/`UDIV`/`SDIV Rm, Rn, Rd`, of two
  64-bit arguments (their low bits read every bit of both);
* `MULW`, `UDIVW`, `DIVW`, `UMULL x y` (`w37?`): `MULW`/`UDIVW`/`SDIVW`/`UMULL Rm, Rn, Rd`, which
  read the low words of the registers, of two arguments of at least 32 bits;
* `RBIT x` (`RBIT Rm, Rd`) of a 64-bit argument; `REVW`, `REV16W x` (`REVW`/`REV16W Rm, Rd`) of an
  argument of at least 32 bits (`un37?`);
* `MADD`, `MSUB a x y` (`madd37?`): `MADD`/`MSUB Rm, Ra, Rn, Rd`, `a ± x · y` with `ADD`'s pointer
  case for a pointer `a`, of arguments of classes at least the result's (the product's low bits
  read only the factors' low bits); `MADDW`, `MSUBW a x y`: `MADDW`/`MSUBW Rm, Ra, Rn, Rd` on the low
  words, of arguments of at least 32 bits;
* `SBFX [k] x` (`k = lsb · 256 + width`): `SBFX $lsb, Rn, $width, Rd`, as G3's `UBFX` with the
  field sign-extended: `0 < width`, `lsb + width ≤` the argument's class.

An ALU op has no temporary and a result of class `c ≥ 8`. The G37 ops empty the upper-bit table
(`uStep35` is `uStepL` on them).

On a function with no arm64 op, `checkG37` is `checkG33`'s `checkNL30`.
`GoFV/Proof/Gen/G37.lean` proves what an accepted function satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The register ops of G37 on two 64-bit arguments and their opcode: `op Rm, Rn, Rd`. -/
def full37? : Op → Option As
  | .ARM64UMULH => some .UMULH | .ARM64MULH => some .SMULH | .ARM64UDIV => some .UDIV
  | .ARM64DIV => some .SDIV
  | _ => none

/-- The register ops of G37 on the low words and their opcode: `op Rm, Rn, Rd`. -/
def w37? : Op → Option As
  | .ARM64MULW => some .MULW | .ARM64UDIVW => some .UDIVW | .ARM64DIVW => some .SDIVW
  | .ARM64UMULL => some .UMULL
  | _ => none

/-- The unary ops of G37, their opcode and the class they need of the argument: `op Rm, Rd`. -/
def un37? : Op → Option (As × Nat)
  | .ARM64RBIT => some (.RBIT, 64) | .ARM64REVW => some (.REVW, 32)
  | .ARM64REV16W => some (.REV16W, 32)
  | _ => none

/-- The multiply-adds of G37, their opcode and whether they read only the low words. -/
def madd37? : Op → Option (As × Bool)
  | .ARM64MADD => some (.MADD, false) | .ARM64MSUB => some (.MSUB, false)
  | .ARM64MADDW => some (.MADDW, true) | .ARM64MSUBW => some (.MSUBW, true)
  | _ => none

/-- A multiply-add Prog `op Rm, Ra, Rn, Rd`: `Rm` in `from_`, `Ra` in `reg`, `Rn` the one
`RestArgs` source, `Rd` in `to`. -/
def maddOK (as : As) (ra rm rn rd : Int) (p : Prog) : Bool :=
  p.as == as && p.from_ == regA rm && p.reg == ra && p.to == regA rd && p.scond == 0 &&
    p.regTo2 == 0 && match p.rest with
    | #[(_, a)] => a == regA rn
    | _ => false

/-- An `SBFX` operand pair: `$lsb` in `from_`, `$width` the one `RestArgs` source. -/
def sbfxOK (lsb width : Int) (rn rd : Int) (p : Prog) : Bool :=
  p.as == .SBFX && p.from_ == constA lsb && p.reg == rn && p.to == regA rd && p.scond == 0 &&
    p.regTo2 == 0 && match p.rest with
    | #[(_, a)] => a == constA width
    | _ => false

/-- A register op `x op y` of G37 (module doc): what it emits, the arguments of at least `ca`
bits. -/
def bin37Kind (lc : LocCtx) (v : Value) (as : As) (ca : Nat) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 2 do throw s!"v{v.id}: shape"
  let (cx, rn) ← argObj lc v 0
  let (cy, rm) ← argObj lc v 1
  let (c, rd) ← resObj lc v
  unless 8 ≤ c && ca ≤ cx && ca ≤ cy do throw s!"v{v.id}: {v.op.name} widths"
  return .prog (.ofShape { as, from_ := regA rm, reg := rn, to := regA rd })

/-- A unary op of G37 (module doc): what it emits, the argument of at least `ca` bits. -/
def un37Kind (lc : LocCtx) (v : Value) (as : As) (ca : Nat) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 1 do throw s!"v{v.id}: shape"
  let (cx, rm) ← argObj lc v 0
  let (c, rd) ← resObj lc v
  unless 8 ≤ c && ca ≤ cx do throw s!"v{v.id}: {v.op.name} widths"
  return .prog (.ofShape { as, from_ := regA rm, to := regA rd })

/-- A multiply-add `a ± x · y` (module doc): what it emits. -/
def madd37Kind (lc : LocCtx) (v : Value) (as : As) (w : Bool) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 3 do throw s!"v{v.id}: shape"
  let (ca, ra) ← argObj lc v 0
  let (cx, rm) ← argObj lc v 1
  let (cy, rn) ← argObj lc v 2
  let (c, rd) ← resObj lc v
  unless 8 ≤ c && (if w then 32 ≤ ca && 32 ≤ cx && 32 ≤ cy else c ≤ ca && c ≤ cx && c ≤ cy) do
    throw s!"v{v.id}: {v.op.name} widths"
  return .prog ⟨maddOK as ra rm rn rd, as.name⟩

/-- `SBFX [k] x` (module doc): what it emits. -/
def sbfxKind (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 1 && 0 ≤ v.auxInt.toInt && v.auxInt.toInt < 2 ^ 16 do
    throw s!"v{v.id}: bitfield shape"
  let (ca, rn) ← argObj lc v 0
  let (c, rd) ← resObj lc v
  let lsb := v.auxInt.toInt / 256
  let width := v.auxInt.toInt % 256
  unless 8 ≤ c && 0 < width && lsb + width ≤ ca do throw s!"v{v.id}: bitfield widths"
  return .prog ⟨sbfxOK lsb width rn rd, "SBFX"⟩

/-- What `v` emits in G37, or why it is outside the slice. -/
def vkind37 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  match full37? v.op, w37? v.op, un37? v.op, madd37? v.op with
  | some as, _, _, _ => bin37Kind lc v as 64
  | none, some as, _, _ => bin37Kind lc v as 32
  | none, none, some (as, ca), _ => un37Kind lc v as ca
  | none, none, none, some (as, w) => madd37Kind lc v as w
  | none, none, none, none => if v.op == .ARM64SBFX then sbfxKind lc v else vkind36 lc g v

/-- Slice G37 of the genssa validator (module doc): G36's check with G37's value check. -/
def checkG37 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind37 lc g, tm := cx.termG3 }
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

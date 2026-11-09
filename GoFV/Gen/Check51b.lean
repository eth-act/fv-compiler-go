import GoFV.Gen.Check50

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G51, group b: shifted `MVN`, `SBFIZ`, rotates
(`docs/plans/proofs3.md` §4)

`vkind51b lc v` is the value check of slice G51's group b, `none` on every other op (`op51b`):

* `MVNshiftLL`, `MVNshiftRL`, `MVNshiftRA [k] x` (`mvnSh51b?`, `0 ≤ k < 64`): genssa's
  `shiftUnary` emits `MVN Rm SHIFT k, Rd` (`genshift` with no `Rn`, G27's `shiftA` operand),
  `~(x` shifted by `k)`. Bit `i` of `x << k` is bit `i - k` of `x`, so `LL` of an `x` of class at
  least the result's (as G32's `MVN`), and `RL`, `RA` (whose low bits read `x`'s high ones) of a
  64-bit `x` (as G27's shifted logic ops);
* `SBFIZ [k] x` (`k = lsb · 256 + width`, `0 ≤ k < 2 ^ 16`): `SBFIZ $lsb, Rn, $width, Rd`, the low
  `width` bits of `x` sign-extended and moved up to bit `lsb` (G33's `UBFIZ` with the field
  sign-extended). Bit `i < c` of the result is bit `i - lsb` of `x` below `width`, else bit
  `width - 1`, so `0 < width ≤ 64` (Go's `armBFAuxInt` range) and, as `UBFIZ`, `width ≤ ca` or
  `c ≤ ca`;
* `RORconst`, `RORWconst [k] x` (`rorK51b?`): `ROR`/`RORW $k, Rn, Rd`, `x` rotated right by `k`
  (`0 ≤ k < 64`, `< 32` for the word rotate, Go's ranges): a rotate reads every bit of its
  operand, so a 64-bit `x` for `ROR` and one of at least 32 bits for `RORW` (its low word);
* `ROR`, `RORW x y` (`ror51b?`): `ROR`/`RORW Rm, Rn, Rd`, `x` rotated right by `y` modulo 64 (32):
  `x` as for the constant rotates, `y` of at least 8 bits (the amount reads its low 6 bits, as
  G36's register shifts).

An ALU op has no temporary and a result of class `c ≥ 8`. `GoFV/Proof/Gen/Spec51b.lean` unfolds
what `vkind51b` accepts and `GoFV/Proof/Gen/G51b.lean` proves one such value.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The shifted `MVN`s of G51b and their shift kind (0 `LSL`, 1 `LSR`, 2 `ASR`, as G27's
`logSh?`). -/
def mvnSh51b? (op : Op) : Option Nat :=
  if op = .ARM64MVNshiftLL then some 0
  else if op = .ARM64MVNshiftRL then some 1
  else if op = .ARM64MVNshiftRA then some 2
  else none

/-- The constant rotates of G51b: opcode and the width they rotate. -/
def rorK51b? (op : Op) : Option (As × Nat) :=
  if op = .ARM64RORconst then some (.ROR, 64)
  else if op = .ARM64RORWconst then some (.RORW, 32)
  else none

/-- The register rotates of G51b: opcode and the width they rotate. -/
def ror51b? (op : Op) : Option (As × Nat) :=
  if op = .ARM64ROR then some (.ROR, 64)
  else if op = .ARM64RORW then some (.RORW, 32)
  else none

/-- The ops of G51b. -/
def op51b (op : Op) : Bool :=
  (mvnSh51b? op).isSome || decide (op = .ARM64SBFIZ) || (rorK51b? op).isSome ||
    (ror51b? op).isSome

/-- An `SBFIZ` operand pair: `$lsb` in `from_`, `$width` the one `RestArgs` source. -/
def sbfizOK (lsb width : Int) (rn rd : Int) (p : Prog) : Bool :=
  p.as == .SBFIZ && p.from_ == constA lsb && p.reg == rn && p.to == regA rd && p.scond == 0 &&
    p.regTo2 == 0 && match p.rest with
    | #[(_, a)] => a == constA width
    | _ => false

/-- `MVNshiftXX [k] x` (module doc): what it emits. -/
def mvnSh51bKind (lc : LocCtx) (v : Value) (typ : Nat) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 1 do throw s!"v{v.id}: shape"
  unless 0 ≤ v.auxInt.toInt && v.auxInt.toInt < 64 do throw s!"v{v.id}: shift amount"
  let (ca, rm) ← argObj lc v 0
  let (c, rd) ← resObj lc v
  unless 8 ≤ c && (if typ == 0 then c ≤ ca else ca == 64) do
    throw s!"v{v.id}: shifted MVN widths"
  return .prog (.ofShape
    { as := .MVN, from_ := shiftA typ rm v.auxInt.toInt.toNat, to := regA rd })

/-- `SBFIZ [k] x` (module doc): what it emits. -/
def sbfiz51bKind (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 1 && 0 ≤ v.auxInt.toInt && v.auxInt.toInt < 2 ^ 16 do
    throw s!"v{v.id}: bitfield shape"
  let (ca, rn) ← argObj lc v 0
  let (c, rd) ← resObj lc v
  let lsb := v.auxInt.toInt / 256
  let width := v.auxInt.toInt % 256
  unless 8 ≤ c && 0 < width && width ≤ 64 && (width ≤ ca || c ≤ ca) do
    throw s!"v{v.id}: bitfield widths"
  return .prog ⟨sbfizOK lsb width rn rd, "SBFIZ"⟩

/-- `RORconst`, `RORWconst [k] x` (module doc): what they emit, rotating `w` bits. -/
def rorK51bKind (lc : LocCtx) (v : Value) (as : As) (w : Nat) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 1 do throw s!"v{v.id}: shape"
  let (ca, rn) ← argObj lc v 0
  let (c, rd) ← resObj lc v
  unless 8 ≤ c && w ≤ ca && 0 ≤ v.auxInt.toInt && v.auxInt.toInt < w do
    throw s!"v{v.id}: rotate widths"
  return .prog (.ofShape { as, from_ := constA v.auxInt.toInt, reg := rn, to := regA rd })

/-- `ROR`, `RORW x y` (module doc): what they emit, rotating `w` bits. -/
def ror51bKind (lc : LocCtx) (v : Value) (as : As) (w : Nat) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 2 do throw s!"v{v.id}: shape"
  let (ca, rn) ← argObj lc v 0
  let (cb, rm) ← argObj lc v 1
  let (c, rd) ← resObj lc v
  unless 8 ≤ c && w ≤ ca && 8 ≤ cb do throw s!"v{v.id}: {v.op.name} widths"
  return .prog (.ofShape { as, from_ := regA rm, reg := rn, to := regA rd })

/-- What `v` emits in G51b, or why not (`some`), or `none` if `v` is none of G51b's ops. -/
def vkind51b (lc : LocCtx) (v : Value) : Option (Except String VKind2) :=
  match mvnSh51b? v.op with
  | some typ => some (mvnSh51bKind lc v typ)
  | none =>
    if v.op = .ARM64SBFIZ then some (sbfiz51bKind lc v)
    else match rorK51b? v.op with
      | some (as, w) => some (rorK51bKind lc v as w)
      | none =>
        match ror51b? v.op with
        | some (as, w) => some (ror51bKind lc v as w)
        | none => none

end GoFV.Gen.Check

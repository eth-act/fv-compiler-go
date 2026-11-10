import GoFV.Gen.Check51b

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G55, group B: shifted `NEG`, `CLZW`, `MULL`, `EXTR`
(`docs/plans/proofs3.md` §4)

`vkind55b lc v` is the value check of slice G55's group B, `none` on every other op (`op55b`):

* `NEGshiftLL`, `NEGshiftRL`, `NEGshiftRA [k] x` (`negSh55b?`, `0 ≤ k < 64`): genssa's
  `shiftUnary` emits `NEG Rm SHIFT k, Rd`, `-(x` shifted by `k)`, as G51b's shifted `MVN`. The low
  bits of a negation read only the low bits of its operand, so `LL` of an `x` of class at least the
  result's and `RL`, `RA` of a 64-bit `x`;
* `CLZW x`: `CLZW Rm, Rd` (`unary`), the leading zeros of the low word, of an `x` of at least 32 bits
  (as G37's `REVW`);
* `MULL x y`: `SMULL Rm, Rn, Rd` (`binary`, `x` in `Rn`), the signed product of the low words, of
  two arguments of at least 32 bits (as G37's `UMULL`);
* `EXTRconst`, `EXTRWconst [k] x y` (`extr55b?`, `0 ≤ k <` the width): `EXTR`/`EXTRW $k, Rx, Ry,
  Rd` (`x`, the high half, the one `RestArgs` source, `y` in `reg`), the width bits of `x:y` from
  bit `k`, of two 64-bit arguments (`EXTR`) or of at least 32 bits (`EXTRW`, the low words).

An ALU op has no temporary and a result of class `c ≥ 8`. `GoFV/Proof/Gen/Spec55b.lean` unfolds
what `vkind55b` accepts and `GoFV/Proof/Gen/G55b.lean` proves one such value.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The shifted `NEG`s of G55b and their shift kind (0 `LSL`, 1 `LSR`, 2 `ASR`). -/
def negSh55b? (op : Op) : Option Nat :=
  if op = .ARM64NEGshiftLL then some 0
  else if op = .ARM64NEGshiftRL then some 1
  else if op = .ARM64NEGshiftRA then some 2
  else none

/-- The extracts of G55b: opcode and width. -/
def extr55b? (op : Op) : Option (As × Nat) :=
  if op = .ARM64EXTRconst then some (.EXTR, 64)
  else if op = .ARM64EXTRWconst then some (.EXTRW, 32)
  else none

/-- The ops of G55b. -/
def op55b (op : Op) : Bool :=
  (negSh55b? op).isSome || decide (op = .ARM64CLZW) || decide (op = .ARM64MULL) ||
    (extr55b? op).isSome

/-- An `EXTR` operand list: `$k` in `from_`, `Rm` in `reg`, `Rn` the one `RestArgs` source. -/
def extrOK (as : As) (k : Int) (rn rm rd : Int) (p : Prog) : Bool :=
  p.as == as && p.from_ == constA k && p.reg == rm && p.to == regA rd && p.scond == 0 &&
    p.regTo2 == 0 && match p.rest with
    | #[(_, a)] => a == regA rn
    | _ => false

/-- `NEGshiftXX [k] x` (module doc): what it emits. -/
def negSh55bKind (lc : LocCtx) (v : Value) (typ : Nat) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 1 do throw s!"v{v.id}: shape"
  unless 0 ≤ v.auxInt.toInt && v.auxInt.toInt < 64 do throw s!"v{v.id}: shift amount"
  let (ca, rm) ← argObj lc v 0
  let (c, rd) ← resObj lc v
  unless 8 ≤ c && (if typ == 0 then c ≤ ca else ca == 64) do
    throw s!"v{v.id}: shifted NEG widths"
  return .prog (.ofShape
    { as := .NEG, from_ := shiftA typ rm v.auxInt.toInt.toNat, to := regA rd })

/-- `EXTRconst`, `EXTRWconst [k] x y` (module doc): what they emit, of width `w`. -/
def extr55bKind (lc : LocCtx) (v : Value) (as : As) (w : Nat) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 2 do throw s!"v{v.id}: shape"
  let (ca, rn) ← argObj lc v 0
  let (cb, rm) ← argObj lc v 1
  let (c, rd) ← resObj lc v
  unless 8 ≤ c && w ≤ ca && w ≤ cb && 0 ≤ v.auxInt.toInt && v.auxInt.toInt < w do
    throw s!"v{v.id}: extract widths"
  return .prog ⟨extrOK as v.auxInt.toInt rn rm rd, as.name⟩

/-- What `v` emits in G55b, or why not (`some`), or `none` if `v` is none of G55b's ops. -/
def vkind55b (lc : LocCtx) (v : Value) : Option (Except String VKind2) :=
  match negSh55b? v.op with
  | some typ => some (negSh55bKind lc v typ)
  | none =>
    if v.op = .ARM64CLZW then some (un37Kind lc v .CLZW 32)
    else if v.op = .ARM64MULL then some (bin37Kind lc v .SMULL 32)
    else match extr55b? v.op with
      | some (as, w) => some (extr55bKind lc v as w)
      | none => none

end GoFV.Gen.Check

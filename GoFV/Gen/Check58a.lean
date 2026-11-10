import GoFV.Gen.Check51c

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G58, group A: narrow and boolean operands of earlier ops, wider
store-release sources, `LoweredRound*F` (`docs/plans/proofs3.md` §4)

The earlier slices ask more of an argument's class than the op reads. G58a accepts, emitting the
Prog of the earlier check (no temporary, a result of class `c ≥ 8` where it has one):

* `REV16W x` (`rev16w58`): `REV16W Rm, Rd` of an `x` of at least 16 bits for a result of at most
  16 (G37 asks 32): the low halfword of `REV16W` swaps the bytes of the low halfword only;
* `MADDW`, `MSUBW a x y` (`maddw58`): `MADDW`/`MSUBW Rm, Ra, Rn, Rd` for a result of class
  `c ≤ 32` of arguments of classes at least `c` (G37 asks 32): the low `c` bits of the low word's
  `a ± x · y` read only the low `c` bits of `a`, `x`, `y`;
* G32's register ops (`bin32?`, `bin58`), constant ops (`binK32?`, `binK58`), G36's register
  shifts (`sh36?`, `sh58`, the shift amount), G33's `UBFIZ` (`ubfiz58`) and G32's `CSINC`
  (`csinc58`) where an argument is a boolean (class 1): its register is 0 or 1 on all 64 bits
  (`ValRel` of `.bool`, `Arm64.reg`), as G51c's arithmetic (`wid51c`);
* `STLRW`, `STLRB p x mem` (`stlr58`): `STLRW`/`STLRB Rx, (Rp)` of a source of more than the
  access's bits (G32 asks exactly them): Phase 1's generic atomic store fits the operand to the
  location (`fitPiece`, which truncates an integer), the machine stores the register's low bytes;
* `LoweredRound32F`, `LoweredRound64F x` (`round58`): no code (`ssaGenValue`'s `nop` case,
  `regalloc`'s `resultInArg0`), the result in `x`'s `F` register at `x`'s class (32 or 64): Phase 1's
  `Round32F`/`Round64F` is the identity on the float (`FOps.round`).

`vkind58a lc g v` is `none` exactly off these ops (`op58a`). `GoFV/Proof/Gen/G58a.lean` proves
what an accepted value satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- `REV16W x`: `REV16W Rm, Rd`, `x` of at least 16 bits, the result of at most 16. -/
def rev16w58 (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 1 do throw s!"v{v.id}: shape"
  let (cx, rm) ← argObj lc v 0
  let (c, rd) ← resObj lc v
  unless 8 ≤ c && c ≤ 16 && 16 ≤ cx do throw s!"v{v.id}: {v.op.name} widths"
  return .prog (.ofShape { as := .REV16W, from_ := regA rm, to := regA rd })

/-- `MADDW`, `MSUBW a x y` (`as`): `as Rm, Ra, Rn, Rd`, the result of class `c ≤ 32`, the
arguments of at least `c` bits. -/
def maddw58 (lc : LocCtx) (v : Value) (as : As) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 3 do throw s!"v{v.id}: shape"
  let (ca, ra) ← argObj lc v 0
  let (cx, rm) ← argObj lc v 1
  let (cy, rn) ← argObj lc v 2
  let (c, rd) ← resObj lc v
  unless 8 ≤ c && c ≤ 32 && c ≤ ca && c ≤ cx && c ≤ cy do throw s!"v{v.id}: {v.op.name} widths"
  return .prog ⟨maddOK as ra rm rn rd, as.name⟩

/-- A register op `x op y` of G32 (`as`) with a boolean argument: `as Rm, Rn, Rd`. -/
def bin58 (lc : LocCtx) (v : Value) (as : As) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 2 do throw s!"v{v.id}: shape"
  let (ca, rn) ← argObj lc v 0
  let (cb, rm) ← argObj lc v 1
  let (c, rd) ← resObj lc v
  unless 8 ≤ c && wid51c c ca && wid51c c cb do throw s!"v{v.id}: {v.op.name} widths"
  return .prog (.ofShape { as, from_ := regA rm, reg := rn, to := regA rd })

/-- A constant op `x op k` of G32 (`as`) of a boolean `x`: `as $k, Rn, Rd`. -/
def binK58 (lc : LocCtx) (v : Value) (as : As) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 1 do throw s!"v{v.id}: shape"
  let (ca, rn) ← argObj lc v 0
  let (c, rd) ← resObj lc v
  unless 8 ≤ c && ca == 1 do throw s!"v{v.id}: {v.op.name} widths"
  return .prog (.ofShape { as, from_ := constA v.auxInt.toInt, reg := rn, to := regA rd })

/-- A register shift `x op y` of G36 (`as`) by a boolean `y`: `as Rm, Rn, Rd`, `x` as G36 asks. -/
def sh58 (lc : LocCtx) (v : Value) (as : As) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 2 do throw s!"v{v.id}: shape"
  let (ca, rn) ← argObj lc v 0
  let (cb, rm) ← argObj lc v 1
  let (c, rd) ← resObj lc v
  unless 8 ≤ c && cb == 1 && (if as == .LSL then c ≤ ca else ca == 64) do
    throw s!"v{v.id}: {v.op.name} widths"
  return .prog (.ofShape { as, from_ := regA rm, reg := rn, to := regA rd })

/-- `UBFIZ [k] x` of a boolean `x`: G33's `UBFIZ $lsb, Rn, $width, Rd`. -/
def ubfiz58 (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 1 && 0 ≤ v.auxInt.toInt && v.auxInt.toInt < 2 ^ 16 do
    throw s!"v{v.id}: bitfield shape"
  let (ca, rn) ← argObj lc v 0
  let (c, rd) ← resObj lc v
  unless 8 ≤ c && ca == 1 do throw s!"v{v.id}: bitfield widths"
  return .prog ⟨ubfizOK (v.auxInt.toInt / 256) (v.auxInt.toInt % 256) rn rd, "UBFIZ"⟩

/-- `CSINC [cc] x y f` with arguments of at least the result's class or booleans: G32's
`CSINC cond, Rx, Ry, Rd`. -/
def csinc58 (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 3 do throw s!"v{v.id}: select shape"
  let some f := v.args[2]? | throw s!"v{v.id}: select shape"
  unless (lc.ty f).isFlags && lc.home f == none do throw s!"v{v.id}: select condition argument"
  let some o := ccOp? v.auxInt | throw s!"v{v.id}: select condition"
  unless (Cond.ofOp o).isSome do throw s!"v{v.id}: select condition"
  let some cc := ARM64.condBits o | throw s!"v{v.id}: select condition"
  let (ca, rn) ← argObj lc v 0
  let (cb, rm) ← argObj lc v 1
  let (c, rd) ← resObj lc v
  unless 8 ≤ c && wid51c c ca && wid51c c cb do throw s!"v{v.id}: select widths"
  return .prog ⟨csincOK cc rn rm rd, "CSINC"⟩

/-- `STLRW`, `STLRB p x mem` (`as`, `n` bytes) of a source of at least `8 n` bits: G32's
`as Rx, (Rp)`. -/
def stlr58 (lc : LocCtx) (v : Value) (as : As) (n : Nat) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 3 && memTy (lc.ty v.id) && lc.home v.id == none && v.aux == none &&
      v.auxInt.toInt == 0 do
    throw s!"v{v.id}: store-release shape"
  let (ca, rn) ← argObj lc v 0
  let (cs, rs) ← argObj lc v 1
  memArg lc v 2
  unless ca == 64 && 8 * n ≤ cs do throw s!"v{v.id}: {v.op.name} widths"
  return .prog ⟨plain as (· == regA rs) (· == memA rn 0), as.name⟩

/-- `LoweredRound32F`, `LoweredRound64F x` (`c` the float's bits): no code, the result in `x`'s
`F` register at `x`'s class `c`. -/
def round58 (lc : LocCtx) (v : Value) (c : Nat) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 1 do throw s!"v{v.id}: shape"
  let (ca, ra) ← fargObj lc v 0
  let (cd, rd) ← fresObj lc v
  unless ca == c && cd == c && ra == rd do throw s!"v{v.id}: round registers"
  return .none

/-- The ops of G58's group A. -/
def op58a (op : Op) : Bool :=
  op == .ARM64REV16W || op == .ARM64MADDW || op == .ARM64MSUBW || (bin32? op).isSome ||
    (binK32? op).isSome || (sh36? op).isSome || op == .ARM64UBFIZ || op == .ARM64CSINC ||
    op == .ARM64STLRW || op == .ARM64STLRB || op == .ARM64LoweredRound32F ||
    op == .ARM64LoweredRound64F

/-- What `v` emits if it is one of G58's group A (module doc), else `none`. -/
def vkind58a (lc : LocCtx) (_g : G2In) (v : Value) : Option (Except String VKind2) :=
  if v.op = .ARM64REV16W then some (rev16w58 lc v)
  else if v.op = .ARM64MADDW then some (maddw58 lc v .MADDW)
  else if v.op = .ARM64MSUBW then some (maddw58 lc v .MSUBW)
  else if v.op = .ARM64UBFIZ then some (ubfiz58 lc v)
  else if v.op = .ARM64CSINC then some (csinc58 lc v)
  else if v.op = .ARM64STLRW then some (stlr58 lc v .STLRW 4)
  else if v.op = .ARM64STLRB then some (stlr58 lc v .STLRB 1)
  else if v.op = .ARM64LoweredRound32F then some (round58 lc v 32)
  else if v.op = .ARM64LoweredRound64F then some (round58 lc v 64)
  else match bin32? v.op with
    | some as => some (bin58 lc v as)
    | none => match binK32? v.op with
      | some as => some (binK58 lc v as)
      | none => match sh36? v.op with
        | some as => some (sh58 lc v as)
        | none => none

end GoFV.Gen.Check

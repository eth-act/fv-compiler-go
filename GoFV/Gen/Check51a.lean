import GoFV.Gen.Check50

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G51, group A: conditional negation and register compares
(`docs/plans/proofs3.md` §4)

The flag and conditional ops of slice G51, each one Prog of `ssaGenValue`:

* `CSNEG [cc] x y f`: `CSNEG cond, Rx, Ry, Rd` (the `csinc` case: `x` if the condition holds on
  `NZCV`, else `-y`), as G32's `CSINC`: the flags argument last with no home, the auxint an op
  number that names a condition, register arguments of classes at least the result's class
  `c ≥ 8` (the low `c` bits of `-y` depend only on `y`'s low `c` bits);
* `TSTW x y`, `CMNW x y`: `TSTW`/`CMNW Rm, Rn` (the `cmp` case: `x` in `Rn`, `y` in `Rm`), the
  flags of the 32-bit `ANDS`/`ADDS` of the low words, of arguments of classes at least 32 (as G3's
  `CMPW`);
* `CMN x y`: `CMN Rm, Rn`, the flags of the 64-bit `ADDS`, of two 64-bit arguments;
* `CMPshiftRA [k] x y` (`0 ≤ k < 64`): `CMP Rm->k, Rn` (`genshift`'s shifted operand, G27's
  `shiftA` of kind 2), the flags of the `SUBS` of `x` and `y` shifted arithmetically by `k`, of two
  64-bit arguments (as G41's `CMPshiftLL`/`CMPshiftRL`).

A compare's result is the flags, with no home. `vkind51a lc v` is `none` exactly off these ops
(`op51a`). On a pointer without an integer form `runLoc` gives `CMN`'s and `CMPshiftRA`'s flags `Z`
clear (Phase 1's `cmpP`/`cmpSh`); `GoFV/Proof/Gen/G51a.lean` proves what an accepted value
satisfies under the run premise `Pre51a` that excludes that case.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The ops of G51's group A. -/
def op51a (op : Op) : Bool :=
  op == .ARM64CSNEG || op == .ARM64TSTW || op == .ARM64CMN || op == .ARM64CMNW ||
    op == .ARM64CMPshiftRA

/-- A `CSNEG` Prog: the condition `cc` in `from_`, `Rn` in `reg`, `Rm` the one `RestArgs` source,
`Rd` in `to`. -/
def csnegOK (cc rn rm rd : Int) (p : Prog) : Bool :=
  p.as == .CSNEG && p.from_ == specA cc && p.reg == rn && p.to == regA rd && p.scond == 0 &&
    p.regTo2 == 0 && p.rest.size == 1 && (p.rest[0]?.map (·.2)) == some (regA rm)

/-- `CSNEG [cc] x y f` (module doc): what it emits. -/
def csnegKind (lc : LocCtx) (v : Value) : Except String VKind2 := do
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
  unless 8 ≤ c && c ≤ ca && c ≤ cb do throw s!"v{v.id}: select widths"
  return .prog ⟨csnegOK cc rn rm rd, "CSNEG"⟩

/-- `TSTW`, `CMNW`, `CMN x y` (module doc, `as` the opcode, `w` the datasize): what it emits. -/
def cmpRegKind51a (lc : LocCtx) (v : Value) (as : As) (w : Nat) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 2 && (lc.ty v.id).isFlags && lc.home v.id == none do
    throw s!"v{v.id}: compare shape"
  let (ca, rn) ← argObj lc v 0
  let (cb, rm) ← argObj lc v 1
  unless (if w == 64 then ca == 64 && cb == 64 else 32 ≤ ca && 32 ≤ cb) do
    throw s!"v{v.id}: compare widths"
  return .prog (.ofShape { as, from_ := regA rm, reg := rn })

/-- `CMPshiftRA [k] x y` (module doc): what it emits. -/
def cmpShRAKind (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 2 && (lc.ty v.id).isFlags && lc.home v.id == none do
    throw s!"v{v.id}: compare shape"
  unless 0 ≤ v.auxInt.toInt && v.auxInt.toInt < 64 do throw s!"v{v.id}: shift amount"
  let (ca, rn) ← argObj lc v 0
  let (cb, rm) ← argObj lc v 1
  unless ca == 64 && cb == 64 do throw s!"v{v.id}: compare widths"
  return .prog (.ofShape { as := .CMP, from_ := shiftA 2 rm v.auxInt.toInt.toNat, reg := rn })

/-- What `v` emits if its op is one of G51's group A (`op51a`), else `none`. -/
def vkind51a (lc : LocCtx) (v : Value) : Option (Except String VKind2) :=
  if v.op == .ARM64CSNEG then some (csnegKind lc v)
  else if v.op == .ARM64TSTW then some (cmpRegKind51a lc v .TSTW 32)
  else if v.op == .ARM64CMNW then some (cmpRegKind51a lc v .CMNW 32)
  else if v.op == .ARM64CMN then some (cmpRegKind51a lc v .CMN 64)
  else if v.op == .ARM64CMPshiftRA then some (cmpShRAKind lc v)
  else none

end GoFV.Gen.Check

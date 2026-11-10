import GoFV.Gen.Check50

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G57, group A: `STPW`; narrow pair loads of a global or a frame
variable (`docs/plans/proofs3.md` §4)

The pair accesses of words that the earlier slices reject, each one Prog of `ssaGenValue`'s
`LDP*`/`STP*` case (`GoFV/Gen/Arm64Value.lean`), of no temporary:

* `STPW [off] p x y mem` (`stpw57`): `STPW (Rx, Ry), off(Rn)`, as G4's `STP` (`p` in a 64-bit
  register, no aux), the sources of classes of at least 32 bits (the machine stores their low
  words; `ZR` included);
* `LDPW`/`LDPSW {x} [off] base mem` with an aux (`ldpw57`), into two distinct X registers G1 may
  write (`pairTys`, as G50's `ldp50`): of a global (`symOf?`: `op sym+off(SB), (Ra, Rb)`, as G22's
  `LDP`) or of a frame variable whose block is `Blk.temp` (`frameVar?`: `op off'(RSP), (Ra, Rb)`
  at its `NAME_AUTO` operand, as G6's `LDP`).

`vkind57a lc g v` is `none` exactly off these ops (`op57a`; a pair load without an aux is G50's).
`GoFV/Proof/Gen/G57a.lean` proves what an accepted value satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- `STPW (Rx, Ry), off(Rn)`: the address in a 64-bit register, sources of at least 32 bits. -/
def stpw57 (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 4 && v.aux == none && memTy (lc.ty v.id) && lc.home v.id == none do
    throw s!"v{v.id}: pair store shape"
  let (ca, rn) ← argObj lc v 0
  let (cx, rx) ← argObj lc v 1
  let (cy, ry) ← argObj lc v 2
  memArg lc v 3
  unless ca == 64 && 32 ≤ cx && 32 ≤ cy do throw s!"v{v.id}: pair store widths"
  return .prog (.ofShape { as := .STPW, from_ := pairA rx ry, to := memA rn v.auxInt.toInt })

/-- `LDPW`/`LDPSW` (`as`) with an aux into two distinct X registers: of a global,
`as sym+off(SB), (Ra, Rb)`, or of a frame variable in a `Blk.temp` block, `as off'(RSP), (Ra, Rb)`. -/
def ldpw57 (lc : LocCtx) (g : G2In) (v : Value) (as : As) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 2 && pairTys (lc.ty v.id) do throw s!"v{v.id}: pair load shape"
  memArg lc v 1
  let some (ra, rb) := pairHome? lc v.id | throw s!"v{v.id}: pair load home"
  unless ra != rb && ra != zeroReg && rb != zeroReg && destOK ra && destOK rb do
    throw s!"v{v.id}: pair load registers"
  let some oa := objOf? ra | throw s!"v{v.id}: register {ra}"
  let some ob := objOf? rb | throw s!"v{v.id}: register {rb}"
  let some x := v.aux | throw s!"v{v.id}: pair load shape"
  match symOf? lc.ctx.tabs x with
  | some (name, abi) =>
    return .prog ⟨plain as (globA g name abi v.auxInt.toInt) (· == pairA oa ob), "LDPW sym(SB)"⟩
  | none =>
    match ← frameVar? lc g v with
    | some (_, off) => return .prog ⟨plain as (slotA · .AUTO off) (· == pairA oa ob), "LDPW var"⟩
    | none => throw s!"v{v.id}: pair load shape"

/-- The ops of G57's group A. -/
def op57a (op : Op) : Bool := op == .ARM64STPW || op == .ARM64LDPW || op == .ARM64LDPSW

/-- What `v` emits if it is one of G57's group A (`STPW`, or `LDPW`/`LDPSW` with an aux), else
`none`. -/
def vkind57a (lc : LocCtx) (g : G2In) (v : Value) : Option (Except String VKind2) :=
  if v.op = .ARM64STPW then some (stpw57 lc v)
  else if v.op = .ARM64LDPW then (if v.aux.isSome then some (ldpw57 lc g v .LDPW) else none)
  else if v.op = .ARM64LDPSW then (if v.aux.isSome then some (ldpw57 lc g v .LDPSW) else none)
  else none

end GoFV.Gen.Check

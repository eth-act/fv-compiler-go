import GoFV.Gen.Check50

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G59, group P: float pair loads of a global or a frame variable
(`docs/plans/proofs3.md` §4)

G50's `ldp50` takes an `FLDPD`/`FLDPS` only without an aux (`op off(Rn), (Fa, Fb)`). Group P takes
the ones with an aux, one Prog of `ssaGenValue`'s `LDP*`/`FLDP*` case (`GoFV/Gen/Arm64Value.lean`)
with no temporary, as G57's group A takes `LDPW`/`LDPSW` (`ldpw57`):

* `FLDPD`/`FLDPS {x} [off] base mem` (`fldp59`, 8- and 4-byte elements) into two distinct V
  registers, each component a float shape of the element's width (G50's `fpairTys`): of a global
  (`symOf?`: `op sym+off(SB), (Fa, Fb)`, as G57's `LDPW`) or of a frame variable whose block is
  `Blk.temp` (`frameVar?`: `op off'(RSP), (Fa, Fb)` at its `NAME_AUTO` operand).

Their `Select0`/`Select1` are G50's (`sel50` reads the op, not the aux). `vkind59p lc g v` is `none`
exactly off these ops and on a float pair load without an aux (`op59p`; that one is G50's).
`GoFV/Proof/Gen/G59p.lean` proves what an accepted value satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- `FLDPD`/`FLDPS` (`as`, `n`-byte elements) with an aux into two distinct V registers: of a
global, `as sym+off(SB), (Fa, Fb)`, or of a frame variable in a `Blk.temp` block,
`as off'(RSP), (Fa, Fb)`. -/
def fldp59 (lc : LocCtx) (g : G2In) (v : Value) (as : As) (n : Nat) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 2 && fpairTys (lc.ty v.id) n do throw s!"v{v.id}: pair load shape"
  memArg lc v 1
  let some (ra, rb) := pairHome? lc v.id | throw s!"v{v.id}: pair load home"
  unless ra != rb do throw s!"v{v.id}: pair load registers"
  let some oa := fobjOf? ra | throw s!"v{v.id}: register {ra}"
  let some ob := fobjOf? rb | throw s!"v{v.id}: register {rb}"
  let some x := v.aux | throw s!"v{v.id}: pair load shape"
  match symOf? lc.ctx.tabs x with
  | some (name, abi) =>
    return .prog ⟨plain as (globA g name abi v.auxInt.toInt) (· == pairA oa ob), "FLDP sym(SB)"⟩
  | none =>
    match ← frameVar? lc g v with
    | some (_, off) => return .prog ⟨plain as (slotA · .AUTO off) (· == pairA oa ob), "FLDP var"⟩
    | none => throw s!"v{v.id}: pair load shape"

/-- The ops of G59's group P. -/
def op59p (op : Op) : Bool := op == .ARM64FLDPD || op == .ARM64FLDPS

/-- What `v` emits if it is one of G59's group P (`FLDPD`/`FLDPS` with an aux), else `none`. -/
def vkind59p (lc : LocCtx) (g : G2In) (v : Value) : Option (Except String VKind2) :=
  if v.op = .ARM64FLDPD then (if v.aux.isSome then some (fldp59 lc g v .FLDPD 8) else none)
  else if v.op = .ARM64FLDPS then (if v.aux.isSome then some (fldp59 lc g v .FLDPS 4) else none)
  else none

end GoFV.Gen.Check

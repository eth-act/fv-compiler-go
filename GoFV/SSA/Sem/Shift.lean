import GoFV.SSA.Sem.Int

variable [GoFV.SSA.Sem.Addrs]

/-!
# Shifts (`docs/plans/semantics.md` §4.3)

`Lsh{A}x{B}`, `Rsh{A}x{B}`, `Rsh{A}Ux{B}`: an `A`-bit value shifted by a `B`-bit amount read
unsigned (gO 107-111). An amount `≥ A` gives 0 (`Lsh`, `RshU`) or the sign fill (`Rsh`), as the
Go spec says — exactly `BitVec`'s `<<<`, `>>>`, `sshiftRight` on `Nat` amounts (the amount is
capped at `A`, which changes no result and keeps compiled code from building `x <<< 2^63`).
The auxint flag ("bounded", set by `prove` and rules) promises an amount `< A`; broken ⇒
`poison`.
-/

namespace GoFV.SSA.Sem

namespace Shift

/-- A shift of an `w`-bit value by an `a`-bit amount. -/
@[inline] def shift (w a : Width) (bounded : Bool) (f : BitVec w.bits → Nat → BitVec w.bits) :
    List Val → Val
  | [x, s] => match x.asInt w, s.asInt a with
    | some x, some s =>
      if bounded && w.bits ≤ s.toNat then .poison else .int w (f x (min s.toNat w.bits))
    | _, _ => .poison
  | _ => .poison

def lsh (w a : Width) (bounded : Bool) : List Val → Val := shift w a bounded fun x n => x <<< n
def rsh (w a : Width) (bounded : Bool) : List Val → Val := shift w a bounded fun x n => x.sshiftRight n
def rshu (w a : Width) (bounded : Bool) : List Val → Val := shift w a bounded fun x n => x >>> n

end Shift

end GoFV.SSA.Sem

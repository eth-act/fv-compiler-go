import GoFV.Gen.Check50

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G52, group B: remainders (`docs/plans/proofs3.md` §4)

The remainders of slice G52, each one Prog of `ssaGenValue`'s `binary` case (`op Rm, Rn, Rd`, `x`
in `Rn`, `y` in `Rm`), as G37's divides (`full37?`, `w37?`, `bin37Kind`):

* `MOD`, `UMOD x y`: `REM`/`UREM Rm, Rn, Rd`, of two 64-bit arguments (the remainder reads every
  bit of both);
* `MODW`, `UMODW x y`: `REMW`/`UREMW Rm, Rn, Rd`, which read the low words of the registers, of two
  arguments of at least 32 bits.

The result has no temporary and a class `c ≥ 8` (`rem52b?` gives the opcode and the arguments'
least class). `vkind52b lc v` is `none` exactly off these ops (`op52b`). `GoFV/Proof/Gen/G52b.lean`
proves what an accepted value satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The remainders of G52's group B, their opcode and the class they need of both arguments. -/
def rem52b? : Op → Option (As × Nat)
  | .ARM64MOD => some (.REM, 64) | .ARM64UMOD => some (.UREM, 64)
  | .ARM64MODW => some (.REMW, 32) | .ARM64UMODW => some (.UREMW, 32)
  | _ => none

/-- The ops of G52's group B. -/
def op52b (op : Op) : Bool := (rem52b? op).isSome

/-- What `v` emits if its op is one of G52's group B (`op52b`), else `none`. -/
def vkind52b (lc : LocCtx) (v : Value) : Option (Except String VKind2) :=
  (rem52b? v.op).map fun (as, cw) => bin37Kind lc v as cw

end GoFV.Gen.Check

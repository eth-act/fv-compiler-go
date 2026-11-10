import GoFV.Gen.Check46

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G55, group A: `VCNT`, `VUADDLV`, `FRINT*` (`docs/plans/proofs3.md` §4)

The SIMD and float values of slice G55, each one Prog of `ssaGenValue`
(`GoFV/Gen/Arm64Value.lean`) on V registers, of no temporary:

* `VCNT x` (`PopCount*`'s byte counts): `VCNT Va.B8, Vd.B8` (`simdV11Asm`, `ARNG_8B`), the argument
  and the result 64-bit values in V registers (`simd55`);
* `VUADDLV x` (their sum): `VUADDLV Va.B8, Vd` (`simdV11Scalar`: the source `ARNG_8B`, the
  destination the `V` register of the result's `F` register) (`simd55`);
* `FRINTN`/`FRINTP`/`FRINTM`/`FRINTZ`/`FRINTA` `D`/`S` (`frintOf`): `op Fa, Fd` (`unary`), as G46's
  `FNEG` (`fun46`).

`arng8B r` is `simdRegArng r ARNG_8B` for an `F` register `r` (`ARNG_8B = 0`, `REG_F0 ≡ 0 mod 32`).
`vkind55a lc v` is `none` exactly off these ops (`op55a`). `GoFV/Proof/Gen/G55a.lean` proves what an
accepted value satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The rounds to an integral value: bytes `n`, `ftype` and `opc` of `fp1Op`. -/
def frintOf (op : Op) : Option (Nat × BitVec 2 × BitVec 6) :=
  if op = .ARM64FRINTND then some (8, 1, 8) else if op = .ARM64FRINTNS then some (4, 0, 8)
  else if op = .ARM64FRINTPD then some (8, 1, 9) else if op = .ARM64FRINTPS then some (4, 0, 9)
  else if op = .ARM64FRINTMD then some (8, 1, 10) else if op = .ARM64FRINTMS then some (4, 0, 10)
  else if op = .ARM64FRINTZD then some (8, 1, 11) else if op = .ARM64FRINTZS then some (4, 0, 11)
  else if op = .ARM64FRINTAD then some (8, 1, 12) else if op = .ARM64FRINTAS then some (4, 0, 12)
  else none

/-- The `8B` arrangement of the V register of `F` register `r` (`simdRegArng r ARNG_8B`). -/
def arng8B (r : Int) : Int := ARM64.REG_ARNG + (r - ARM64.REG_F0)

/-- The scalar `V` register of `F` register `r` (`simdV11Scalar`'s destination). -/
def vOfF (r : Int) : Int := r - ARM64.REG_F0 + ARM64.REG_V0

/-- The Prog of `VCNT` (`cnt`, `VCNT Va.B8, Vd.B8`) or `VUADDLV` (`VUADDLV Va.B8, Vd`) of the `F`
registers `ra`, `rd`. -/
def simdShape (cnt : Bool) (ra rd : Int) : Shape where
  as := cond cnt .VCNT .VUADDLV
  from_ := regA (arng8B ra)
  to := regA (cond cnt (arng8B rd) (vOfF rd))

/-- `VCNT` (`cnt`): `VCNT Va.B8, Vd.B8`; `VUADDLV`: `VUADDLV Va.B8, Vd`. -/
def simd55 (lc : LocCtx) (v : Value) (cnt : Bool) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 1 do throw s!"v{v.id}: SIMD op shape"
  let (ca, ra) ← fargObj lc v 0
  let (cd, rd) ← fresObj lc v
  unless ca == 64 && cd == 64 do throw s!"v{v.id}: SIMD op widths"
  return .prog (.ofShape (simdShape cnt ra rd))

/-- The ops of G55's group A. -/
def op55a (op : Op) : Bool := op == .ARM64VCNT || op == .ARM64VUADDLV || (frintOf op).isSome

/-- What `v` emits if its op is one of G55's group A (`op55a`), else `none`. -/
def vkind55a (lc : LocCtx) (v : Value) : Option (Except String VKind2) :=
  if v.op = .ARM64VCNT then some (simd55 lc v true)
  else if v.op = .ARM64VUADDLV then some (simd55 lc v false)
  else (frintOf v.op).map fun (n, _, _) => fun46 lc v n n

end GoFV.Gen.Check

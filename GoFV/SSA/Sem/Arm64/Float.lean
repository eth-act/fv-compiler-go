import GoFV.SSA.Sem.Arm64.Reg
import GoFV.SSA.Sem.Float

variable [GoFV.SSA.Sem.Addrs]

/-!
# arm64 floating-point ops (`docs/plans/semantics2.md` §4 (c.1), §2.1)

The scalar FP instructions on Phase 1's `GoFV.IEEE` (`Sem/Float`, the ASL port, `FPCR = 0`):
a float in a register is its bit pattern, `.int .w32`/`.int .w64` as in Phase 1. The commutative
`FADD`/`FMUL` take their operands in encoding order as Phase 1's `Add*F`/`Mul*F` (`FOps.ordered`:
Go marks them commutative, `cse` and the rules reorder them; the order only matters for two NaNs).

* `FADD`…`FDIV`, `FNEG`, `FABS`, `FSQRT`, `FMIN`/`FMAX`, `FRINT{A,M,N,P,Z}`, `FCVT`, `SCVTF`/`UCVTF`,
  `FCVTZS`/`FCVTZU` (saturating, NaN ↦ 0), `LoweredRound*F` (the identity): Phase 1's `FOps`;
* `FNMUL` = `FPNeg(FPMul(n, m))` (the sign of a NaN product flips);
* the fused multiply-adds `FMADD a n m` = `FPMulAdd(a, n, m)`, `FMSUB` = `FPMulAdd(a, −n, m)`,
  `FNMADD` = `FPMulAdd(−a, −n, m)`, `FNMSUB` = `FPMulAdd(−a, n, m)` (operand negations as in the
  ASL, so NaN signs follow the machine). These are the right-hand sides of the 12 `useFMA`
  rules; `lower` refines its input only up to `Contract` (§2.1);
* `FCMP` sets `NZCV` from `FPCompare`: unordered `0011`, equal `0110`, less `1000`,
  greater `0010`;
* `FMOV` between register files moves bits (`FMOVSfpgp` zero-extends).
-/

namespace GoFV.SSA.Sem.Arm64

open GoFV.IEEE (Fmt Cmp)

/-- A float register operand of width `w` (low `w` bits of an integer of any width). -/
def fval (w : Width) (v : Val) : Val :=
  match v with
  | .int _ x => .int w (x.setWidth w.bits)
  | v => v

/-- A Phase 1 float op applied to operands read at width `w`. -/
@[inline] def fop (w : Width) (g : Width → List Val → Val) (args : List Val) : Val :=
  g w (args.map (fval w))

/-- `FNMUL`. -/
def fnmul (w : Width) (args : List Val) : Val := FOps.neg w [fop w FOps.mul args]

/-- The fused multiply-adds `FMADD`/`FMSUB`/`FNMADD`/`FNMSUB` `a n m` (`negA`, `negN`: the ASL's
operand negations). -/
def fmadd (w : Width) (negA negN : Bool) : List Val → Val
  | [a, n, m] =>
    let a := fval w a
    let n := fval w n
    let a := if negA then FOps.neg w [a] else a
    let n := if negN then FOps.neg w [n] else n
    FOps.fma w [n, fval w m, a]
  | _ => .poison

/-- `NZCV` of an `FPCompare` outcome. -/
def fcmpFlags : Cmp → Flags
  | .un => ⟨false, false, true, true⟩
  | .eq => ⟨false, true, true, false⟩
  | .lt => ⟨true, false, false, false⟩
  | .gt => ⟨false, false, true, false⟩

/-- `FCMP x y` (`zero`: `FCMP x, #0.0`). -/
def fcmp (w : Width) (zero : Bool) (args : List Val) : Val :=
  let args := (if zero then args ++ [.int w 0] else args).map (fval w)
  match w with
  | .w32 => int2 .w32 (fun x y => (fcmpFlags (IEEE.compare Fmt.b32 x y)).toVal) args
  | .w64 => int2 .w64 (fun x y => (fcmpFlags (IEEE.compare Fmt.b64 x y)).toVal) args
  | _ => .poison
/-- `SCVTF`/`UCVTF` from a `W` (`w = .w32`) or `X` register. -/
def cvtf (unsigned : Bool) (w w' : Width) : List Val → Val
  | [a] => match reg a with
    | some x => FOps.ofInt unsigned w w' [.int w (x.setWidth w.bits)]
    | none => .poison
  | _ => .poison

/-- `FCVTZS`/`FCVTZU` into a `W` (`w' = .w32`, zero-extended) or `X` register. -/
def fcvtz (ty : Ty) (unsigned : Bool) (w w' : Width) (args : List Val) : Val :=
  match FOps.toInt unsigned w' w (args.map (fval w)) with
  | .int _ r => res ty (r.setWidth 64)
  | v => v

/-- `FMOV` of the low `w` bits between register files (no conversion). -/
def fmov (w : Width) (ty : Ty) : List Val → Val
  | [a] => match reg a with
    | some x => match w with
      | .w64 => res ty x
      | _ => res ty ((x.setWidth w.bits).setWidth 64)
    | none => .poison
  | _ => .poison

end GoFV.SSA.Sem.Arm64

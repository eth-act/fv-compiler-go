import GoFV.SSA.Op
import GoFV.SSA.Sem.Val

/-!
# Condition flags of lowered arm64 SSA (`docs/plans/semantics2.md` §3, §5)

A value of Go's `flags` type is `PSTATE.NZCV` after the instruction that produced it: the four
bits and a fifth (below) as a value of the shape `Ty.flags`, `Val.agg [n, z, c, v, g]` of
booleans (§3 option 2: no new `Val` constructor, so no Phase 1 case analysis changes). A
component may be `poison` on its own: a comparison of pointers without concrete addresses fixes
`Z` (allocations are distinct) and leaves the order bits undefined. A condition reads only the
bits it needs (`Cond.eval`), so it is defined whenever those are.

The fifth component `g` is no machine state: it is the sign of the negated difference of an
integer compare (`CMP x y`: the `N` of `y - x`), which `InvertFlags` needs to give the flags of
the swapped compare exactly (`invertFlags`); `poison` for every other flags producer.

Definitions follow the Arm ARM pseudocode (DDI 0487, shared/functions): `AddWithCarry`
(`aarch64/functions/arithmetic`), `ConditionHolds` (`shared/functions/system`), the `FPCompare`
outcome encoding of `FCMP` (`aarch64/instrs/float/compare`), and Go's condition-code table
`condBits` (`cmd/compile/internal/arm64/ssa.go:1942`).
-/

namespace GoFV.SSA.Sem

/-- `PSTATE.NZCV`. -/
structure Flags where
  n : Bool
  z : Bool
  c : Bool
  v : Bool
  deriving DecidableEq, Repr, Inhabited

namespace Flags

/-- The flags as a value of shape `Ty.flags`, without the swapped compare's sign (`g` `poison`). -/
def toVal (f : Flags) : Val := .agg [.bool f.n, .bool f.z, .bool f.c, .bool f.v, .poison]

/-- The flags of an integer compare whose difference is `r`, with `g` the sign of `-r`. -/
def toValSub {n : Nat} (f : Flags) (r : BitVec n) : Val :=
  .agg [.bool f.n, .bool f.z, .bool f.c, .bool f.v, .bool (-r).msb]

/-- Go's `flagConstant` encoding (`rewrite.go:2329`): `N` bit 0, `Z` bit 1, `C` bit 2, `V` bit 3. -/
def ofFlagConstant (k : Nat) : Flags :=
  ⟨k % 2 == 1, k / 2 % 2 == 1, k / 4 % 2 == 1, k / 8 % 2 == 1⟩

/-- The `#nzcv` immediate of `CCMP`/`CCMN` (Arm order: `N` bit 3, `Z` bit 2, `C` bit 1, `V` bit 0). -/
def ofNZCV (k : Nat) : Flags :=
  ⟨k / 8 % 2 == 1, k / 4 % 2 == 1, k / 2 % 2 == 1, k % 2 == 1⟩

end Flags

/-- The shape of Go's `flags` type: four booleans and the swapped compare's sign. -/
def Ty.flags : Ty := .agg [(0, .bool), (1, .bool), (2, .bool), (3, .bool), (4, .bool)] 5

/-- `AddWithCarry(x, y, carry_in)` of width `n`: the result and `NZCV`. -/
def addWithCarry {n : Nat} (x y : BitVec n) (carry : Bool) : BitVec n × Flags :=
  let ci := if carry then 1 else 0
  let usum := x.toNat + y.toNat + ci
  let ssum := x.toInt + y.toInt + ci
  let r : BitVec n := BitVec.ofNat n usum
  (r, ⟨r.msb, r == 0, r.toNat != usum, r.toInt != ssum⟩)

/-- The flags of `ANDS`/`TST` (`LogicalShiftedReg` with `setflags`): `N` and `Z` of the result,
`C = V = 0`. -/
def logicFlags {n : Nat} (r : BitVec n) : Flags := ⟨r.msb, r == 0, false, false⟩

/-- An Arm condition code (`cond`, encoded as in instructions). -/
inductive Cond where
  | eq | ne | hs | lo | mi | pl | vs | vc | hi | ls | ge | lt | gt | le | al | nv
  deriving DecidableEq, Repr, Inhabited

namespace Cond

/-- `ConditionHolds(cond)` on flags whose bits may each be unknown (`none`): defined when the
bits the condition reads are. -/
def eval (c : Cond) (n z cf v : Option Bool) : Option Bool :=
  match c with
  | .eq => z
  | .ne => z.map (!·)
  | .hs => cf
  | .lo => cf.map (!·)
  | .mi => n
  | .pl => n.map (!·)
  | .vs => v
  | .vc => v.map (!·)
  | .hi => do let c ← cf; let z ← z; pure (c && !z)
  | .ls => do let c ← cf; let z ← z; pure (!(c && !z))
  | .ge => do let n ← n; let v ← v; pure (n == v)
  | .lt => do let n ← n; let v ← v; pure (n != v)
  | .gt => do let n ← n; let v ← v; let z ← z; pure (n == v && !z)
  | .le => do let n ← n; let v ← v; let z ← z; pure (!(n == v && !z))
  | .al | .nv => some true

/-- `ConditionHolds(cond)`. -/
def holds (c : Cond) (f : Flags) : Bool := (c.eval f.n f.z f.c f.v).getD true

/-- The condition of an arm64 comparison pseudo-op (`Equal`, `LessThanU`, …; the `CCop` auxint of
`CSEL` and friends, the `cond` of `ARM64ConditionalParams`): Go's `condBits`. -/
def ofOp : Op → Option Cond
  | .ARM64Equal => some .eq
  | .ARM64NotEqual => some .ne
  | .ARM64LessThan => some .lt
  | .ARM64LessThanU => some .lo
  | .ARM64LessEqual => some .le
  | .ARM64LessEqualU => some .ls
  | .ARM64GreaterThan => some .gt
  | .ARM64GreaterThanU => some .hi
  | .ARM64GreaterEqual => some .ge
  | .ARM64GreaterEqualU => some .hs
  | .ARM64LessThanF => some .mi
  | .ARM64LessEqualF => some .ls
  | .ARM64GreaterThanF => some .gt
  | .ARM64GreaterEqualF => some .ge
  | .ARM64NotLessThanF => some .pl
  | .ARM64NotLessEqualF => some .hi
  | .ARM64NotGreaterThanF => some .le
  | .ARM64NotGreaterEqualF => some .lt
  | .ARM64LessThanNoov => some .mi
  | .ARM64GreaterEqualNoov => some .pl
  | _ => none

/-- The condition named by a `CCop` auxint (an `Op` number). -/
def ofAux (k : Int64) : Option Cond :=
  if k.toInt < 0 then none else (Op.ofGoNum? k.toInt.toNat).bind ofOp

end Cond

/-- A flag bit of a flags value: a boolean, else unknown. -/
def Val.flagBit : Val → Option Bool
  | .bool b => some b
  | _ => none

/-- Condition `c` on a flags value (`Val.agg [n, z, c, v, g]`); `none` if a bit it reads is not a
boolean (`poison`). -/
def Cond.onVal (c : Cond) : Val → Option Bool
  | .agg [n, z, cf, v, _] => c.eval n.flagBit z.flagBit cf.flagBit v.flagBit
  | _ => none

/-- A condition never reads the fifth component `g` (no machine state; only `invertFlags` reads
it). -/
theorem Cond.onVal_ghost (c : Cond) (n z cf v g g' : Val) :
    c.onVal (.agg [n, z, cf, v, g]) = c.onVal (.agg [n, z, cf, v, g']) := rfl

/-- A condition on a compare's flags is the condition on its `NZCV`. -/
@[simp] theorem Flags.onVal_toValSub (c : Cond) (f : Flags) {k : Nat} (r : BitVec k) :
    c.onVal (f.toValSub r) = c.onVal f.toVal := rfl

/-- A flags component of an optional bit: `poison` if unknown. -/
def Val.ofFlagBit : Option Bool → Val
  | some b => .bool b
  | none => .poison

/-- `InvertFlags f`: the flags of the compare with swapped operands, as Go's `arm64Invert` reads
them. For `f` the flags `[n, z, c, v, g]` of `x - y` (`g` the sign of `y - x`), the flags of
`y - x` are `N = g`, `Z = z`, `C = ¬c ∨ z` (no borrow), `V = g ⊕ (x > y)` (`N ⊕ V` is `y < x`),
and its `g` is `n`. A bit is `poison` if a bit it is computed from is, and where `[n, z, c, v, g]`
cannot be the flags of a subtraction: `C` if `z ∧ ¬c`, `V` if `z ∧ n ≠ v` (a zero difference
has `C` set and `N = V = 0`). So every integer condition (`EQ` … `UGE`, swapped by `arm64Invert`)
reads, on the result, what its swapped condition reads on `f`, whatever `f`
(`GoFV.Proof.Low.Rules.invertFlags_cond`), and each bit is monotone in `f`'s. -/
def invertFlags : Val → Val
  | .agg [n, z, c, v, g] =>
    let n := n.flagBit; let z := z.flagBit; let c := c.flagBit; let v := v.flagBit
    let g := g.flagBit
    .agg [Val.ofFlagBit g, Val.ofFlagBit z,
      Val.ofFlagBit (do let c ← c; let z ← z; if z && !c then none else pure (!c || z)),
      Val.ofFlagBit (do
        let g ← g; let n ← n; let v ← v; let z ← z
        if z && n != v then none else pure (g != (n == v && !z))),
      Val.ofFlagBit n]
  | _ => .poison

end GoFV.SSA.Sem

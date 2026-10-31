/-!
# Semantic values (`docs/plans/semantics.md` §3.2, phase P1)

The value domain of `GoFV.SSA.run`. Phase P1 (integers, booleans, control flow) has integer
values of the four widths, booleans, the memory as an opaque token, tuples (`TUPLE` and
`RESULTS` types) and `poison` (§3.5). Pointers, composites, floats and real memory snapshots
are added by later phases (P2–P4) as further constructors.

Integers carry no sign: signedness lives in the op (`Less64` vs `Less64U`), as in Go.
-/

namespace GoFV.SSA.Sem

/-- Integer widths of Go SSA (`int`, `uint`, `uintptr` are `w64` on arm64). -/
inductive Width where
  | w8 | w16 | w32 | w64
  deriving DecidableEq, Repr, Inhabited

namespace Width

/-- Number of bits. -/
@[reducible] def bits : Width → Nat
  | .w8 => 8 | .w16 => 16 | .w32 => 32 | .w64 => 64

/-- The width of an integer type of `size` bytes. -/
def ofSize? : Int → Option Width
  | 1 => some .w8 | 2 => some .w16 | 4 => some .w32 | 8 => some .w64 | _ => none

end Width

/-- The memory. P1 treats it as an opaque token: no op of P1 reads or writes memory, and the
ops that do (P2) are not evaluated (`docs/plans/semantics.md` §9). P2 replaces this structure by
the allocation/byte model of §3.4. -/
structure Mem where
  deriving DecidableEq, Repr, Inhabited

/-- A semantic value. -/
inductive Val where
  /-- An integer of any Go integer kind, as a bit pattern. -/
  | int (w : Width) (x : BitVec w.bits)
  | bool (b : Bool)
  /-- A memory value (`InitMem`, the memory component of calls and `MakeResult`). -/
  | mem (m : Mem)
  /-- `TUPLE` and `RESULTS` values (`MakeResult`, `Mul64uhilo`, call results). -/
  | tuple (vs : List Val)
  /-- The result of a partial op outside its domain, of `Unknown`, and of ops whose semantics
  belongs to a later phase (§3.5). Observing it is `stuck`. -/
  | poison
  deriving Inhabited, Repr

namespace Val

/-- `int` of width 8/16/32/64 (convenience constructors with a fixed width). -/
abbrev i8 (x : BitVec 8) : Val := .int .w8 x
abbrev i16 (x : BitVec 16) : Val := .int .w16 x
abbrev i32 (x : BitVec 32) : Val := .int .w32 x
abbrev i64 (x : BitVec 64) : Val := .int .w64 x

mutual
/-- Decidable equality (nested `List Val`, dependent `BitVec`). -/
def beq : Val → Val → Bool
  | .int w x, .int w' y =>
    if h : w = w' then (h ▸ x) == y else false
  | .bool a, .bool b => a == b
  | .mem _, .mem _ => true
  | .tuple as, .tuple bs => beqList as bs
  | .poison, .poison => true
  | _, _ => false
def beqList : List Val → List Val → Bool
  | [], [] => true
  | a :: as, b :: bs => beq a b && beqList as bs
  | _, _ => false
end

instance : BEq Val := ⟨beq⟩

/-- Short rendering for test output: `i64:-3`, `u8:255` style integers are printed signed
(`toInt`), booleans as `true`/`false`. -/
partial def render : Val → String
  | .int w x => s!"i{w.bits}:{x.toInt}"
  | .bool b => toString b
  | .mem _ => "mem"
  | .tuple vs => "(" ++ ", ".intercalate (vs.map render) ++ ")"
  | .poison => "poison"

end Val

mutual
/-- Refinement (§3.5): `Refines src tgt` iff `src` is `poison` or `src = tgt`, pointwise through
tuples. A pass is correct when every value it computes refines the source's. -/
inductive Refines : Val → Val → Prop where
  | poison (v : Val) : Refines .poison v
  | int (w : Width) (x : BitVec w.bits) : Refines (.int w x) (.int w x)
  | bool (b : Bool) : Refines (.bool b) (.bool b)
  | mem (m : Mem) : Refines (.mem m) (.mem m)
  | tuple {as bs : List Val} : RefinesList as bs → Refines (.tuple as) (.tuple bs)
/-- Pointwise refinement of lists of equal length. -/
inductive RefinesList : List Val → List Val → Prop where
  | nil : RefinesList [] []
  | cons {a b : Val} {as bs : List Val} : Refines a b → RefinesList as bs →
      RefinesList (a :: as) (b :: bs)
end

mutual
theorem Refines.refl : (v : Val) → Refines v v
  | .int w x => .int w x
  | .bool b => .bool b
  | .mem m => .mem m
  | .tuple vs => .tuple (RefinesList.refl vs)
  | .poison => .poison _
theorem RefinesList.refl : (vs : List Val) → RefinesList vs vs
  | [] => .nil
  | v :: vs => .cons (Refines.refl v) (RefinesList.refl vs)
end

/-- The shape of an SSA type, as far as P1 evaluates it (`Layout` in later phases). -/
inductive Ty where
  | int (w : Width)
  | bool
  | mem
  /-- `TUPLE` (two components) and `RESULTS` (memory last). -/
  | tuple (ts : List Ty)
  /-- Any type P1 does not evaluate (pointers, composites, floats, `void`, …). -/
  | other
  deriving Inhabited, Repr

/-- Why a run panicked (§6). P1 produces `bounds` (`PanicBounds`) and the panics of the
runtime's panicking entry points it models (`runtime.panicdivide`, `runtime.panicshift`,
`runtime.panicoverflow`). -/
inductive Panic where
  /-- `PanicBounds [kind] x y`: `kind` is the `ssa.BoundsKind` auxint (`op.go:470-489`), `x`
  the index read signed or unsigned as the kind says, `y` the length/capacity (signed). -/
  | bounds (kind : Nat) (x y : Int)
  | divide
  | shift
  /-- `runtime.panicoverflow` (`math/bits.Div64` with a quotient overflow). -/
  | overflow
  /-- Any other panicking runtime entry point, by symbol name. -/
  | runtime (name : String)
  deriving DecidableEq, Repr, Inhabited

namespace Panic

/-- The text of the `runtime.Error` Go reports for the panic (`runtime/error.go`
`boundsErrorFmts`/`boundsNegErrorFmts`, `divideError`, `shiftError`), for comparison with
native runs. -/
def message : Panic → String
  | .bounds kind x y =>
    let neg := x < 0
    let s := match kind / 2 with
      | 0 => if neg then s!"index out of range [{x}]"
             else s!"index out of range [{x}] with length {y}"
      | 1 => if neg then s!"slice bounds out of range [:{x}]"
             else s!"slice bounds out of range [:{x}] with length {y}"
      | 2 => if neg then s!"slice bounds out of range [:{x}]"
             else s!"slice bounds out of range [:{x}] with capacity {y}"
      | 3 => if neg then s!"slice bounds out of range [{x}:]"
             else s!"slice bounds out of range [{x}:{y}]"
      | 4 => if neg then s!"slice bounds out of range [::{x}]"
             else s!"slice bounds out of range [::{x}] with length {y}"
      | 5 => if neg then s!"slice bounds out of range [::{x}]"
             else s!"slice bounds out of range [::{x}] with capacity {y}"
      | 6 => if neg then s!"slice bounds out of range [:{x}:]"
             else s!"slice bounds out of range [:{x}:{y}]"
      | 7 => if neg then s!"slice bounds out of range [{x}::]"
             else s!"slice bounds out of range [{x}:{y}:]"
      | _ => s!"cannot convert slice with length {y} to array or pointer to array with length {x}"
    "runtime error: " ++ s
  | .divide => "runtime error: integer divide by zero"
  | .shift => "runtime error: negative shift amount"
  | .overflow => "runtime error: integer overflow"
  | .runtime name => s!"panic in {name}"

end Panic

end GoFV.SSA.Sem

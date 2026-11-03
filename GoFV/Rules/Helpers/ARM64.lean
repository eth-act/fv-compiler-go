import GoFV.Rules.Helpers.Build
import GoFV.Rules.Helpers.Types
import GoFV.SSA.TypeNew
import Std.Data.HashMap

/-!
# Helpers of the arm64 rule files (`ARM64.rules`, `ARM64latelower.rules`)

Ports of the `rewrite.go` helpers only these rule files use (docs/contracts/rules.md, "Used only
by the arm64 rule files"): `flagConstant` (N = bit 0, Z = bit 1, C = bit 2, V = bit 3; the
carry of a subtraction means "no borrow", `rewrite.go:2318-2484`), `arm64BitField`
(`width | lsb<<8`, `rewrite.go:1952-1985`), the encodability tests `isARM64bitcon` /
`isARM64addcon`, the condition tables `arm64Negate` / `arm64Invert` / `ccARM64Eval`,
`ZeroUpper32Bits`, `flagArg`, `canonLessThan`, `makeJumpTableSym`, the `PanicBoundsC{…}` aux
values, `types.TypeVec128`, and `Config.mulRecipes` with `mulStrengthReduce`
(`config.go:420-697`, the arm64 linear combinations), which the export does not carry.

Integers are Go integers as `Int` (the evaluator's representation); the helpers wrap them to
the Go parameter types themselves.
-/

namespace GoFV.Rules.Arm64

open GoFV.SSA GoFV.Rules RwM

@[inline] private def i64 (x : Int) : Int := wrapInt 64 true x
@[inline] private def i32 (x : Int) : Int := wrapInt 32 true x
@[inline] private def u64 (x : Int) : Int := x.emod (2 ^ 64)
@[inline] private def u32 (x : Int) : Int := x.emod (2 ^ 32)

/-! ## `flagConstant` -/

/-- `flagConstantBuilder.encode()`. -/
def fcEncode (n z c v : Bool) : Int :=
  (if n then 1 else 0) + (if z then 2 else 0) + (if c then 4 else 0) + (if v then 8 else 0)

/-- Bit `k` of `flagConstant(fc)` (a `uint8`). -/
@[inline] def fcBit (fc : Int) (k : Nat) : Bool := (fc.emod 256).toNat.testBit k

/-- The `flagConstant` predicate methods (`eq` … `geNoov`) by name. -/
def fcMethod? (name : String) (fc : Int) : Option Bool :=
  let n := fcBit fc 0
  let z := fcBit fc 1
  let c := fcBit fc 2
  let v := fcBit fc 3
  let lt := n != v
  let ge := n == v
  let le := z || lt
  let gt := !z && ge
  let ult := !c
  let uge := c
  match name with
  | "eq" => some z
  | "ne" => some !z
  | "lt" => some lt
  | "le" => some le
  | "gt" => some gt
  | "ge" => some ge
  | "ult" => some ult
  | "ule" => some (z || ult)
  | "ugt" => some (!z && uge)
  | "uge" => some uge
  | "ltNoov" => some (lt && !v)
  | "leNoov" => some (le && !v)
  | "gtNoov" => some (gt && !v)
  | "geNoov" => some (ge && !v)
  | _ => none

/-- `addFlags64(x, y)`. -/
def addFlags64 (x y : Int) : Int :=
  let x := i64 x
  let y := i64 y
  let s := i64 (x + y)
  fcEncode (s < 0) (s == 0) (u64 s < u64 x) (x ≥ 0 && y ≥ 0 && s < 0 || x < 0 && y < 0 && s ≥ 0)

/-- `subFlags64(x, y)`. -/
def subFlags64 (x y : Int) : Int :=
  let x := i64 x
  let y := i64 y
  let s := i64 (x - y)
  fcEncode (s < 0) (s == 0) (u64 y ≤ u64 x) (x ≥ 0 && y < 0 && s < 0 || x < 0 && y ≥ 0 && s ≥ 0)

/-- `addFlags32(x, y)`. -/
def addFlags32 (x y : Int) : Int :=
  let x := i32 x
  let y := i32 y
  let s := i32 (x + y)
  fcEncode (s < 0) (s == 0) (u32 s < u32 x) (x ≥ 0 && y ≥ 0 && s < 0 || x < 0 && y < 0 && s ≥ 0)

/-- `subFlags32(x, y)`. -/
def subFlags32 (x y : Int) : Int :=
  let x := i32 x
  let y := i32 y
  let s := i32 (x - y)
  fcEncode (s < 0) (s == 0) (u32 y ≤ u32 x) (x ≥ 0 && y < 0 && s < 0 || x < 0 && y ≥ 0 && s ≥ 0)

/-- `logicFlags64(x)`. -/
def logicFlags64 (x : Int) : Int := let x := i64 x; fcEncode (x < 0) (x == 0) false false

/-- `logicFlags32(x)`. -/
def logicFlags32 (x : Int) : Int := let x := i32 x; fcEncode (x < 0) (x == 0) false false

/-! ## Bit fields and immediates -/

/-- `armBFAuxInt(lsb, width)`: `width | lsb<<8`; Go panics out of range. -/
def armBFAuxInt (lsb width : Int) : Except String Int :=
  if lsb < 0 || lsb > 63 then .error "ARM(64) bit field lsb constant out of range"
  else if width < 1 || lsb + width > 64 then .error "ARM(64) bit field width constant out of range"
  else .ok (width + lsb * 256)

/-- `arm64BitField.lsb()`: `int64(uint64(bfc) >> 8)`. -/
def bfLsb (bfc : Int) : Int := i64 (u64 bfc / 256)

/-- `arm64BitField.width()`: `int64(bfc) & 0xff`. -/
def bfWidth (bfc : Int) : Int := u64 bfc % 256

/-- `int64(uint64(mask) >> uint64(rshift))`. -/
private def shiftedMask (mask rshift : Int) : Int :=
  let r := u64 rshift
  if r ≥ 64 then 0 else i64 (u64 mask / 2 ^ r.toNat)

/-- `nto(x)`: the number of trailing ones of the `int64` `x` (`ntz64(^x)`). -/
def nto (x : Int) : Int := trailingZeros (pat64 (-(i64 x) - 1)) 64

/-- `isARM64BFMask(lsb, mask, rshift)`. -/
def isARM64BFMask (lsb mask rshift : Int) : Bool :=
  let sm := shiftedMask mask rshift
  let p := i64 (sm + 1)
  sm != 0 && (p > 0 && (pat64 p &&& pat64 (p - 1)) == 0) && nto sm + lsb < 64

/-- `arm64BFWidth(mask, rshift)`; Go panics on a zero shifted mask. -/
def arm64BFWidth (mask rshift : Int) : Except String Int :=
  let sm := shiftedMask mask rshift
  if sm == 0 then .error "ARM64 BF mask is zero" else .ok (nto sm)

/-- `rotateRight64(v, rotate)`: `bits.RotateLeft64(uint64(v), int(-rotate))`. -/
def rotateRight64 (v rotate : Int) : Int :=
  let s := ((-rotate).emod 64).toNat
  let x := pat64 v
  i64 ((((x <<< s) ||| (x >>> (64 - s))) % 2 ^ 64 : Nat))

/-- `sequenceOfOnes(x)` on a 64-bit pattern. -/
def sequenceOfOnes (x : Nat) : Bool :=
  let y := x &&& ((2 ^ 64 - x) % 2 ^ 64)
  let y := (y + x) % 2 ^ 64
  ((y + 2 ^ 64 - 1) % 2 ^ 64) &&& y == 0

/-- `isARM64bitcon(uint64(x))`: `x` encodable as a logical immediate. -/
def isARM64bitcon (x0 : Int) : Bool := Id.run do
  let x := pat64 x0
  if x == 2 ^ 64 - 1 || x == 0 then return false
  let rot (k : Nat) : Nat := ((x >>> k) ||| (x <<< (64 - k))) % 2 ^ 64
  let x ←
    if x != rot 32 then pure x
    else if x != rot 16 then pure (pat64 (wrapInt 32 true x))
    else if x != rot 8 then pure (pat64 (wrapInt 16 true x))
    else if x != rot 4 then pure (pat64 (wrapInt 8 true x))
    else return true
  return sequenceOfOnes x || sequenceOfOnes (2 ^ 64 - 1 - x)

/-- `isARM64addcon(v)`: `v` encodable as an ADD/SUB immediate (uimm12, optionally `<< 12`). -/
def isARM64addcon (v : Int) : Bool :=
  let v := i64 v
  if v < 0 then false
  else (if v % 4096 == 0 then v / 4096 else v) ≤ 0xFFF

/-! ## Conditions -/

/-- `arm64Negate(op)`; Go panics on other ops. -/
def arm64Negate : Op → Except String Op
  | .ARM64LessThan => .ok .ARM64GreaterEqual
  | .ARM64LessThanU => .ok .ARM64GreaterEqualU
  | .ARM64GreaterThan => .ok .ARM64LessEqual
  | .ARM64GreaterThanU => .ok .ARM64LessEqualU
  | .ARM64LessEqual => .ok .ARM64GreaterThan
  | .ARM64LessEqualU => .ok .ARM64GreaterThanU
  | .ARM64GreaterEqual => .ok .ARM64LessThan
  | .ARM64GreaterEqualU => .ok .ARM64LessThanU
  | .ARM64Equal => .ok .ARM64NotEqual
  | .ARM64NotEqual => .ok .ARM64Equal
  | .ARM64LessThanF => .ok .ARM64NotLessThanF
  | .ARM64NotLessThanF => .ok .ARM64LessThanF
  | .ARM64LessEqualF => .ok .ARM64NotLessEqualF
  | .ARM64NotLessEqualF => .ok .ARM64LessEqualF
  | .ARM64GreaterThanF => .ok .ARM64NotGreaterThanF
  | .ARM64NotGreaterThanF => .ok .ARM64GreaterThanF
  | .ARM64GreaterEqualF => .ok .ARM64NotGreaterEqualF
  | .ARM64NotGreaterEqualF => .ok .ARM64GreaterEqualF
  | _ => .error "arm64Negate: unreachable"

/-- `arm64Invert(op)`; Go panics on other ops. -/
def arm64Invert : Op → Except String Op
  | .ARM64LessThan => .ok .ARM64GreaterThan
  | .ARM64LessThanU => .ok .ARM64GreaterThanU
  | .ARM64GreaterThan => .ok .ARM64LessThan
  | .ARM64GreaterThanU => .ok .ARM64LessThanU
  | .ARM64LessEqual => .ok .ARM64GreaterEqual
  | .ARM64LessEqualU => .ok .ARM64GreaterEqualU
  | .ARM64GreaterEqual => .ok .ARM64LessEqual
  | .ARM64GreaterEqualU => .ok .ARM64LessEqualU
  | .ARM64Equal => .ok .ARM64Equal
  | .ARM64NotEqual => .ok .ARM64NotEqual
  | .ARM64LessThanF => .ok .ARM64GreaterThanF
  | .ARM64GreaterThanF => .ok .ARM64LessThanF
  | .ARM64LessEqualF => .ok .ARM64GreaterEqualF
  | .ARM64GreaterEqualF => .ok .ARM64LessEqualF
  | .ARM64NotLessThanF => .ok .ARM64NotGreaterThanF
  | .ARM64NotGreaterThanF => .ok .ARM64NotLessThanF
  | .ARM64NotLessEqualF => .ok .ARM64NotGreaterEqualF
  | .ARM64NotGreaterEqualF => .ok .ARM64NotLessEqualF
  | _ => .error "arm64Invert: unreachable"

/-- `ccARM64Eval(op, flags)` with fuel for the `InvertFlags` chain: 1 true, -1 false, 0 not
constant. -/
def ccARM64EvalF (f : Func) (op : Op) : Nat → ID → Except String Int
  | 0, _ => .error "ccARM64Eval: InvertFlags chain too long"
  | fuel + 1, w => do
    let x := f.getV w
    if x.op == .ARM64InvertFlags then
      let some a := x.args[0]? | throw "ccARM64Eval: InvertFlags without an argument"
      return -(← ccARM64EvalF f op fuel a)
    if x.op != .ARM64FlagConstant then return 0
    let fc := x.auxInt.toInt
    let r (name : String) : Int := if (fcMethod? name fc).getD false then 1 else -1
    return match op with
      | .ARM64Equal => r "eq"
      | .ARM64NotEqual => r "ne"
      | .ARM64LessThan => r "lt"
      | .ARM64LessThanU => r "ult"
      | .ARM64GreaterThan => r "gt"
      | .ARM64GreaterThanU => r "ugt"
      | .ARM64LessEqual => r "le"
      | .ARM64LessEqualU => r "ule"
      | .ARM64GreaterEqual => r "ge"
      | .ARM64GreaterEqualU => r "uge"
      | _ => 0

/-- `ccARM64Eval(op, flags)`. -/
def ccARM64Eval (f : Func) (op : Op) (flags : ID) : Except String Int :=
  ccARM64EvalF f op (f.valueTab.size + 1) flags

/-- `ZeroUpper32Bits(x, depth)` (`rewrite.go:1383`); the amd64 cases cannot occur (no amd64
ops), and an `Arg` counts only on amd64. -/
def zeroUpper32Bits (f : Func) (tabs : Tables) (arch : String) (x : ID) (depth : Nat) :
    Except String Bool := do
  let v := f.getV x
  if (← Ty.isSigned tabs v.type) then
    if (← Ty.size tabs v.type) < 8 then return false
  match v.op with
  | .ARM64REV16W | .ARM64REVW | .ARM64RBITW | .ARM64CLZW | .ARM64EXTRWconst | .ARM64MULW
  | .ARM64MNEGW | .ARM64UDIVW | .ARM64DIVW | .ARM64UMODW | .ARM64MADDW | .ARM64MSUBW
  | .ARM64RORW | .ARM64RORWconst => return true
  | .Arg => return (← Ty.size tabs v.type) == 4 && arch == "amd64"
  | .Phi | .Select0 | .Select1 =>
    match depth with
    | 0 => return false
    | d + 1 => v.args.allM fun a => zeroUpper32Bits f tabs arch a d
  | _ => return false

/-- `flagArg(v)`: `v`'s only argument if it has flags type (`Type.IsFlags`: the object
`types.TypeFlags`), else nil. -/
def flagArg (f : Func) (flagsTy : TypeRef) (v : ID) : Option ID :=
  let x := f.getV v
  if x.args.size != 1 then none
  else
    let a := x.args[0]!
    if (f.getV a).type == flagsTy then some a else none

/-- `canonLessThan(x, y)`: by Go opcode number, then position, then ID. -/
def canonLessThan (f : Func) (x y : ID) : Bool :=
  let a := f.getV x
  let b := f.getV y
  if a.op != b.op then a.op.goNum < b.op.goNum
  else if !a.pos.sameFileAndLine b.pos then a.pos.before b.pos
  else x < y

/-! ## Objects -/

/-- `fe.Func().LSym.Name`: the callee symbol of `f.OwnAux` (`ssagen` builds it as
`OwnAuxCall(fn.LSym, …)`). -/
def fnSymName : RwM GoStr := do
  let tabs ← tables
  let some own := (← getF).ownAux | throw "makeJumpTableSym: function has no OwnAux"
  let .call (some fn) _ := (← liftE (Sym.auxDef tabs own)).kind
    | throw s!"makeJumpTableSym: OwnAux a{own} is not a call with a callee"
  let .sym name .. := (← liftE (Sym.auxDef tabs fn)).kind
    | throw s!"makeJumpTableSym: callee a{fn} is not a symbol"
  return name

/-- `makeJumpTableSym(b)`: `base.Ctxt.Lookup("<fn LSym>.jump<b.ID>")`, a symbol whose contents
the export does not carry. -/
def makeJumpTableSym (b : ID) : RwM AuxRef := do
  let name := (← fnSymName) ++ GoStr.ofString s!".jump{b}"
  symAux name (some 0) (plainSym name)

/-- The aux of a `PanicBoundsC`/`PanicBoundsCC` value: Go keeps the struct itself in `Aux`, and
the export numbers such values by equality, so an equal one already in the tables is reused. -/
def panicBoundsAux (k : AuxKind) : RwM AuxRef := do
  let tabs ← tables
  if let some i := tabs.auxes.findIdx? (fun d? => d?.any (·.kind == k)) then return i
  let fmt := match k with
    | .pbc c => s!"\{{c}}"
    | .pbcc cx cy => s!"\{{cx} {cy}}"
    | _ => ""
  addAux { fmt := GoStr.ofString fmt, kind := k }

/-- `typ.Vec128` (`types.TypeVec128`): the `Config.Types` entry if the export lists it, else the
`SSA` type `vec128` (16 bytes, alignment 8) by its identity key, new if absent. -/
def vec128 : RwM TypeRef := do
  if let some (_, t) := (← read).typs.find? (·.1 == "Vec128") then return t
  let d : TypeDef :=
    { kind := .SSA, size := some 16, align := some 8, ptrdata := none, flags := {}
      str := GoStr.ofString "vec128", symName := GoStr.ofString "", tail := .none }
  let s ← get
  if let some t := s.tables.findType? (· == d) then return t
  let floor := max s.tables.types.size (← read).typeOrder.rank.size
  let (t, tabs) := s.tables.mintType floor d
  set { s with tables := tabs }
  return t

/-- `types.NewTuple(t1, t2)`. -/
def newTuple (t1 t2 : TypeRef) : RwM TypeRef := do
  let s ← get
  let floor := max s.tables.types.size (← read).typeOrder.rank.size
  let (t, tabs) ← liftE (s.tables.newTuple floor t1 t2)
  set { s with tables := tabs }
  return t

/-! ## Multiplication by constants (`Config.mulRecipes`, arm64) -/

/-- The instruction of an arm64 linear combination `a*x + b*y` (`config.go:504-571`). -/
inductive Combo where
  | add | neg | sub
  | sll (i : Nat)
  | addShiftLL (i : Nat)
  | negShiftLL (i : Nat)
  | subShiftLL (i : Nat)
  deriving Inhabited, Repr

/-- A `linearCombo`: computes `a*x + b*y` at `cost`. -/
structure LinearCombo where
  a : Int
  b : Int
  cost : Nat
  combo : Combo
  deriving Inhabited, Repr

/-- The arm64 `linearCombos`, in Go's order. -/
def linearCombos : Array LinearCombo := Id.run do
  let mut r : Array LinearCombo :=
    #[⟨1, 1, 10, .add⟩, ⟨-1, 0, 10, .neg⟩, ⟨1, -1, 10, .sub⟩]
  for i in [1:64] do
    r := r.push ⟨i64 (2 ^ i), 0, if i == 1 then 9 else 10, .sll i⟩
  for i in [1:64] do
    r := r.push ⟨1, i64 (2 ^ i), if i > 4 then 21 else 20, .addShiftLL i⟩
  for i in [1:64] do
    r := r.push ⟨i64 (-(2 ^ i)), 0, if i > 4 then 21 else 20, .negShiftLL i⟩
  for i in [1:64] do
    r := r.push ⟨1, i64 (-(2 ^ i)), if i > 4 then 21 else 20, .subShiftLL i⟩
  return r

/-- A `mulRecipe`'s construction: one combination of `v` with itself, or two (`config.go`'s
cases A, B, C). -/
inductive Recipe where
  | one (c : LinearCombo)
  /-- `outer(inner(v, v), inner(v, v))`. -/
  | twoA (inner outer : LinearCombo)
  /-- `outer(v, inner(v, v))`. -/
  | twoB (inner outer : LinearCombo)
  /-- `outer(inner(v, v), v)`. -/
  | twoC (inner outer : LinearCombo)
  deriving Inhabited

/-- arm64 `mulCost`. -/
def mulCost : Nat := 35

/-- `Config.mulRecipes` for arm64: multiplier (`int64`) ↦ cost and recipe; an entry is replaced
only by a strictly cheaper one, and only recipes cheaper than `mulCost` enter. -/
def mulRecipes : Std.HashMap Int (Nat × Recipe) := Id.run do
  let cs := linearCombos
  let upd (m : Std.HashMap Int (Nat × Recipe)) (x : Int) (cost : Nat) (r : Recipe) :=
    let x := i64 x
    let better := match m[x]? with
      | some (old, _) => cost < old
      | none => true
    if better && cost < mulCost then m.insert x (cost, r) else m
  let mut m : Std.HashMap Int (Nat × Recipe) := {}
  for c in cs do
    m := upd m (c.a + c.b) c.cost (.one c)
  for inner in cs do
    for outer in cs do
      m := upd m ((inner.a + inner.b) * (outer.a + outer.b)) (inner.cost + outer.cost)
        (.twoA inner outer)
  for inner in cs do
    for outer in cs do
      m := upd m (outer.a + outer.b * (inner.a + inner.b)) (inner.cost + outer.cost)
        (.twoB inner outer)
  for inner in cs do
    for outer in cs do
      m := upd m (outer.a * (inner.a + inner.b) + outer.b) (inner.cost + outer.cost)
        (.twoC inner outer)
  return m

/-- `canMulStrengthReduce(config, x)` (`x` the `int64` multiplier). -/
def canMulStrengthReduce (x : Int) : Bool := mulRecipes.contains (i64 x)

/-- A linear combination's `build(m, x, y)`: a new value in `m`'s block at `m`'s position with
`m`'s type. -/
def buildCombo (m : Value) (c : LinearCombo) (x y : ID) : RwM ID :=
  match c.combo with
  | .add => newValue m.block m.pos .ARM64ADD m.type (args := #[x, y])
  | .neg => newValue m.block m.pos .ARM64NEG m.type (args := #[x])
  | .sub => newValue m.block m.pos .ARM64SUB m.type (args := #[x, y])
  | .sll i => newValue m.block m.pos .ARM64SLLconst m.type (auxInt := Int64.ofNat i) (args := #[x])
  | .addShiftLL i =>
    newValue m.block m.pos .ARM64ADDshiftLL m.type (auxInt := Int64.ofNat i) (args := #[x, y])
  | .negShiftLL i =>
    newValue m.block m.pos .ARM64NEGshiftLL m.type (auxInt := Int64.ofNat i) (args := #[x])
  | .subShiftLL i =>
    newValue m.block m.pos .ARM64SUBshiftLL m.type (auxInt := Int64.ofNat i) (args := #[x, y])

/-- `mulStrengthReduce(m, v, x)`: `v * x` built at `m`'s block and position. -/
def mulStrengthReduce (m v : ID) (x : Int) : RwM ID := do
  let some (_, r) := mulRecipes[i64 x]? | throw s!"mulStrengthReduce: no recipe for {x}"
  let mv ← val m
  let made ← match r with
    | .one c => buildCombo mv c v v
    | .twoA i o => do let w ← buildCombo mv i v v; buildCombo mv o w w
    | .twoB i o => do let w ← buildCombo mv i v v; buildCombo mv o v w
    | .twoC i o => do let w ← buildCombo mv i v v; buildCombo mv o w v
  return made

end GoFV.Rules.Arm64

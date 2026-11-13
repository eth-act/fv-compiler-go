import GoFV.Rules.Syntax
import GoFV.Rules.Helpers.Magic
import GoFV.SSA.Sem.Pure
import GoFV.SSA.Sem.Layout
import GoFV.SSA.Sem.TyEq

variable [GoFV.SSA.Sem.Addrs]

/-!
# The denotation of a value rule (`docs/proofs/rules.md`)

`Rule.Sound r` is the correctness obligation of one exported rewrite rule
(`GoFV.Rules.Rule`): for every instance of the match pattern whose checks and condition hold,
the value the result builds refines (`Sem.Refines`) the value of the matched value `v`, where
values are those of `GoFV.SSA.Sem.evalValue`: `(evalPure op ty auxInt aux args).retype ty`.
It is the obligation the rule interpreter's soundness proof (`GoFV.Rules.Interp`) consumes, in
the role of clifv's `Opt.SimplifyFn` obligation.

**Instances.** A pattern is instantiated by a `PEnv`: for every position of the pattern (a
reversed path of argument indices; `[]` is `v`), the value at a leaf (`_`, `x`), and the type
shape, auxint and aux of an op node. The value of an op node is computed from its arguments,
so the only freedom is at the leaves and in the node fields. Rule variables are bound at their
binding occurrence (`Pat.binds`); `same x`, `[e]`, `<e>` occurrences become hypotheses
(`Pat.cons`). Comparisons by pointer identity (`same x`, `<t>`) are weakened to equality of
values and type shapes, which only strengthens the obligation.

**Commutative patterns.** Only the written argument order is considered. The interpreter's
swapped matches are covered by the symmetry of the commutative ops' semantics
(`GoFV.Proof.Rules.Comm`), so `Rule.Sound` need not consider them.

**Expressions** (`[auxint]`, `<type>`, conditions) are evaluated by `evalE`, a total pure
evaluator mirroring `GoFV.Rules.Eval.eval` on integers, booleans, op constants, type shapes
and the pure `rewrite.go` helpers. Everything else (a value's `Uses`, `clobber`, `config`
fields, symbol helpers, floats, …) is read from an `Oracle`, over which the obligation is
universally quantified: a rule whose correctness depends on such an atom is not provable from
this denotation. The same holds on the result side: an aux, a type or an auxint the evaluator
does not model comes from the oracle.

**The matched value's type.** The obligation assumes that `v`'s computed value has the shape of
`v`'s type (`Val.hasTy`), i.e. that `v`'s type is not narrower than its op (the semantics reads
a narrower type as the low bits, `Val.retype`). The checker does not guarantee this
(`docs/contracts/check.md`, "Argument sizes"); see `docs/proofs/rules.md`, "Narrow result
types".

**Leaf types.** A leaf's type is the instance's type at its position (`x.Type`), and the
obligation assumes that every leaf value has its type's shape (`Pat.typed`): a matched leaf is
a register whose value `evalValue` retyped to its type (`docs/proofs/rules.md`, "Assumptions to
discharge").

**Argument shapes.** The obligation assumes that the arguments of pointer ops and integer
comparisons have the shapes the checked types give them (`Pat.argsOK`, `argShapeOk`): the
pointer argument of `OffPtr`, `AddPtr`, `PtrIndex`, `IsNonNil`, `EqPtr`, `NeqPtr` is
pointer-typed, the offset of `AddPtr`/`PtrIndex` a 64-bit integer, a `Convert` goes between a
pointer and a 64-bit integer, both arguments of `Eq<N>`/`Neq<N>` are `N`-bit integers.
Without it `(OffPtr (OffPtr p [y]) [x]) => (OffPtr p [x+y])` is false for a `uintptr` leaf
under a pointer-typed inner node (the pointer `p + y` keeps its allocation, the integer does
not). The rewrite validator checks it on the matched types (`GoFV.Opt.RewriteCheck.ruleOK`).

What the interpreter proof has to supply, besides the match: the shapes of `typ.<T>` and
`types.Types[k]` (`typShape`, `typesShape`) for the export's `Config.Types`, and that
`t.Size()` of an integer or boolean shape is its byte size.
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

/-- A position in a pattern: the argument indices from the top, innermost first. -/
abbrev Path := List Nat

/-- The value of a rule expression in the denotation. `val v p`: a `*Value` with semantic value
`v`; `p = some path` if it is a node of the pattern (then its fields are those of the instance
at `path`: an op node's type, auxint, …; a leaf's type). -/
inductive DV where
  | int (i : Int)
  | bool (b : Bool)
  | ty (t : Ty)
  | op (o : Op)
  | val (v : Val) (p : Option Path)
  | strct (fs : List (String × DV))
  /-- A `float64`/`float32` value (Go's `auxIntToFloat64`/`auxIntToFloat32` of an auxint, a
  float literal), by its IEEE 754 encoding. -/
  | f64 (b : BitVec 64)
  | f32 (b : BitVec 32)
  | other

/-- An instance of a pattern: leaf values and op-node fields by position. -/
structure PEnv where
  leaf : Path → Val
  ty : Path → Ty
  auxInt : Path → Int64
  aux : Path → Option AuxRef

/-- What the denotation does not model, by expression. -/
structure Oracle where
  dv : Expr → DV
  ty : Expr → Ty
  auxInt : Expr → Int64
  aux : Expr → Option AuxRef
  val : Expr → Val

/-! ## Patterns -/

mutual
/-- The value of the pattern node at position `p` (`evalValue`'s value of the matched value). -/
def Pat.den (e : PEnv) (p : Path) : Pat → Val
  | .op o _ _ _ _ _ args _ =>
    (evalPure o (e.ty p) (e.auxInt p) (e.aux p) (Pat.dens e p 0 args)).retype (e.ty p)
  | _ => e.leaf p
/-- The values of argument patterns `i, i+1, …` of the node at `p`. -/
def Pat.dens (e : PEnv) (p : Path) (i : Nat) : List Pat → List Val
  | [] => []
  | q :: qs => Pat.den e (i :: p) q :: Pat.dens e p (i + 1) qs
end

/-- The value of the top node before `retype` (`Rule.Sound` assumes the two agree). -/
def Pat.raw (e : PEnv) : Pat → Val
  | .op o _ _ _ _ _ args _ => evalPure o (e.ty []) (e.auxInt []) (e.aux []) (Pat.dens e [] 0 args)
  | _ => e.leaf []

/-- `auxIntTo<T>` of an op's aux type (`GoFV.Rules.Interp.auxIntVal`). -/
def auxIntDV (aty : AuxType) (i : Int64) : DV :=
  match aty with
  | .Bool => .bool (i != 0)
  | .Int8 => .int (wrapInt 8 true i.toInt)
  | .Int16 => .int (wrapInt 16 true i.toInt)
  | .Int32 | .SymOff | .CallOff => .int (wrapInt 32 true i.toInt)
  | .Int64 | .TypSize => .int i.toInt
  | .UInt8 => .int (wrapInt 8 false i.toInt)
  | .Float64 => .f64 (BitVec.ofInt 64 i.toInt)
  | .Float32 => .f32 (IEEE.convert .b64 .b32 .rne (BitVec.ofInt 64 i.toInt))
  | _ => .other

/-- What a `bind` field binds. -/
def Field.bindDV (e : PEnv) (p : Path) (o : Op) : Nat → DV
  | 0 => .ty (e.ty p)
  | 1 => auxIntDV o.auxType (e.auxInt p)
  | _ => .other

mutual
/-- The bindings made by the pattern at `p`: `(variable, value)`. -/
def Pat.binds (e : PEnv) (p : Path) : Pat → List (Nat × DV)
  | .wild | .same _ => []
  | .bind x => [(x, .val (e.leaf p) (some p))]
  | pat@(.op o name ty ai _ _ args _) =>
    (match name with | some x => [(x, .val (Pat.den e p pat) (some p))] | none => []) ++
    (match ty with | .bind x => [(x, .ty (e.ty p))] | _ => []) ++
    (match ai with | .bind x => [(x, auxIntDV o.auxType (e.auxInt p))] | _ => []) ++
    Pat.bindss e p 0 args
def Pat.bindss (e : PEnv) (p : Path) (i : Nat) : List Pat → List (Nat × DV)
  | [] => []
  | q :: qs => Pat.binds e (i :: p) q ++ Pat.bindss e p (i + 1) qs
end

/-- The rule variables' values under the instance `e` (unbound: `other`). -/
def sigma (e : PEnv) (pat : Pat) (x : Nat) : DV :=
  ((Pat.binds e [] pat).lookup x).getD .other

/-! ## Expressions -/

/-- The Go type of an expression (`GoFV.Rules.Scope.tyOf`). -/
def exprTy (vtys : List GoTy) : Expr → GoTy
  | .lit t _ | .cnst _ t _ | .glob _ t | .field _ _ t | .call _ _ t | .method _ _ _ t
  | .builtin _ _ t | .conv t _ | .assert t _ | .unop _ _ t | .binop _ _ _ t | .index _ _ t
  | .deref _ t => t
  | .op _ => .named "Op"
  | .var i => vtys.getD i (.named "?")
  | .rsv _ => .named "?"

/-- The shape of `typ.<name>` (`Config.Types` on a 64-bit target; `BytePtr` is `*uint8`, the
other pointer types point to their element: `IntPtr` is `*int`, …; floats have the integer
shapes of their width, as `Sem.tyOf`). -/
def typShape : String → Option Ty
  | "Int8" | "UInt8" => some (.int .w8)
  | "Int16" | "UInt16" => some (.int .w16)
  | "Int32" | "UInt32" | "Float32" => some (.int .w32)
  | "Int64" | "UInt64" | "Int" | "UInt" | "Uintptr" | "Float64" => some (.int .w64)
  | "Bool" => some .bool
  | "BytePtr" => some (.ptr (some 1))
  | "Int32Ptr" | "UInt32Ptr" | "Float32Ptr" => some (.ptr (some 4))
  | "IntPtr" | "UintptrPtr" | "Float64Ptr" | "BytePtrPtr" => some (.ptr (some 8))
  | _ => none

/-- The shape of `types.Types[k]` (`types.Kind` numbering). -/
def typesShape : Int → Option Ty
  | 1 | 2 => some (.int .w8)
  | 3 | 4 => some (.int .w16)
  | 5 | 6 => some (.int .w32)
  | 7 | 8 | 9 | 10 | 11 => some (.int .w64)
  | 16 => some .bool
  | _ => none

/-- Byte size of an integer, boolean or pointer shape, or of an aggregate shape (`t.Size()`;
`Ty.size`; `Sem.tyOf` gives a struct, `[1]T` array, interface or complex type the shape
`.agg fs n` with `n` its size). -/
def shapeSize : Ty → Option Int
  | .int w => some (w.bits / 8)
  | .bool => some 1
  | .ptr _ => some 8
  | .agg _ n => some n
  | _ => none

/-- The shape of a string (`Sem.tyOf` of `STRING`). -/
def strShape : Ty → Bool
  | .str => true
  | _ => false

/-- The shape of a slice. -/
def sliceShape : Ty → Bool
  | .slice _ => true
  | _ => false

/-- The shape of an interface. -/
def interShape : Ty → Bool
  | .agg [(0, .int .w64), (8, .ptr (some 1))] 16 => true
  | _ => false

/-- The shape of a complex number (`Sem.tyOf` of `COMPLEX64`, `COMPLEX128`). -/
def complexShape : Ty → Bool
  | .agg [(0, .int .w32), (4, .int .w32)] 8 => true
  | .agg [(0, .int .w64), (8, .int .w64)] 16 => true
  | _ => false

/-- The type predicates `kindE` models. -/
inductive KindPred where
  | ptrShaped | string | slice | inter | complex

/-- `t.IsPtrShaped()`, `t.IsString()`, `t.IsSlice()`, `t.IsInterface()`, `t.IsComplex()` of a type
of shape `t`, as far as the shape decides it (`Sem.tyOf`): a pointer shape is exactly a
pointer-shaped type (`PTR`, `UNSAFEPTR`, `MAP`, `CHAN`, `FUNC`); a string, slice, interface or
complex number has the kind's shape, so the predicate is false at every other shape, and at the
kind's shape (which a struct can share) and at `.other` (an unknown type) it is the oracle's. -/
def kindE : KindPred → Ty → Option Bool
  | _, .other => none
  | .ptrShaped, .ptr _ => some true
  | .ptrShaped, _ => some false
  | .string, t => if strShape t then none else some false
  | .slice, t => if sliceShape t then none else some false
  | .inter, t => if interShape t then none else some false
  | .complex, t => if complexShape t then none else some false

/-- `kindE` of a type value. -/
def kindDV (k : KindPred) : DV → Option DV
  | .ty t => (kindE k t).map .bool
  | _ => none

/-- Field `n` of a struct value. -/
def strctField (fs : List (String × DV)) (n : String) : Option DV :=
  (fs.find? (·.1 == n)).map (·.2)

/-- Integer binary operators (`GoFV.Rules.Eval.intBin`); `none` where Go panics. -/
def intBin (o : BinOp) (ty : GoTy) (a b : Int) : Option DV :=
  match o with
  | .add => some (.int (wrapTo ty (a + b)))
  | .sub => some (.int (wrapTo ty (a - b)))
  | .mul => some (.int (wrapTo ty (a * b)))
  | .quo => if b == 0 then none else some (.int (wrapTo ty (goQuo a b)))
  | .rem => if b == 0 then none else some (.int (wrapTo ty (goRem a b)))
  | .and => some (.int (bitwise ty (· &&& ·) a b))
  | .or => some (.int (bitwise ty (· ||| ·) a b))
  | .xor => some (.int (bitwise ty (· ^^^ ·) a b))
  | .andNot => some (.int (bitwise ty (fun x y => x &&& (2 ^ 64 - 1 - y)) a b))
  | .shl =>
    if b < 0 then none
    else some (.int (wrapTo ty (goShl a b.toNat ((ty.intInfo?.map (·.1)).getD 64))))
  | .shr => if b < 0 then none else some (.int (wrapTo ty (goShr a b.toNat)))
  | .eq => some (.bool (a == b))
  | .ne => some (.bool (a != b))
  | .lt => some (.bool (a < b))
  | .le => some (.bool (a ≤ b))
  | .gt => some (.bool (a > b))
  | .ge => some (.bool (a ≥ b))
  | _ => none

/-- Go's float comparisons from `FPCompare`'s result: unordered (a NaN) makes every comparison
false except `!=`; `+0 == -0`. -/
def floatCmp (o : BinOp) (c : IEEE.Cmp) : Option DV :=
  match o with
  | .eq => some (.bool (c == .eq))
  | .ne => some (.bool (c != .eq))
  | .lt => some (.bool (c == .lt))
  | .le => some (.bool (c == .lt || c == .eq))
  | .gt => some (.bool (c == .gt))
  | .ge => some (.bool (c == .gt || c == .eq))
  | _ => none

/-- Non-short-circuit binary operators on evaluated operands (`GoFV.Rules.Eval.binop` on the
modelled kinds; of the float arithmetic only division, IEEE 754 round to nearest even as Go's
constant `1/c` of `generic.rules:1330`/`:1331`). -/
def binDV (o : BinOp) (ty : GoTy) : DV → DV → Option DV
  | .int a, .int b => intBin o ty a b
  | .bool a, .bool b =>
    match o with
    | .eq => some (.bool (a == b))
    | .ne => some (.bool (a != b))
    | _ => none
  | .op a, .op b =>
    match o with
    | .eq => some (.bool (a == b))
    | .ne => some (.bool (a != b))
    | _ => none
  | .f64 a, .f64 b =>
    if o = .quo then some (.f64 (IEEE.div .b64 .rne a b)) else floatCmp o (IEEE.compare .b64 a b)
  | .f32 a, .f32 b =>
    if o = .quo then some (.f32 (IEEE.div .b32 .rne a b)) else floatCmp o (IEEE.compare .b32 a b)
  | _, _ => none

/-- Unary operators (`GoFV.Rules.Eval.unop`). -/
def unDV (o : UnOp) (ty : GoTy) : DV → Option DV
  | .int i => match o with
    | .neg => some (.int (wrapTo ty (-i)))
    | .com => some (.int (wrapTo ty (-i - 1)))
    | .plus => some (.int i)
    | .not => none
  | .bool b => match o with
    | .not => some (.bool (!b))
    | .plus => some (.bool b)
    | _ => none
  | _ => none

/-- `umagicData`/`smagicData` and the other helper result structs. -/
def magicDV (r : Except String (Int × Nat)) : Option DV :=
  match r with
  | .ok (s, m) => some (.strct [("s", .int s), ("m", .int m)])
  | .error _ => none

def udivDV (r : Except String (Int × Nat × Nat)) : Option DV :=
  match r with
  | .ok (k, m, mx) => some (.strct [("k", .int k), ("m", .int m), ("max", .int mx)])
  | .error _ => none

def sdivDV (r : Except String (Int × Nat × Nat × Nat)) : Option DV :=
  match r with
  | .ok (k, m, a, mx) =>
    some (.strct [("k", .int k), ("m", .int m), ("a", .int a), ("max", .int mx)])
  | .error _ => none

/-- The modelled `rewrite.go` helpers; widths are the `8/16/32/64` suffixes. -/
inductive Helper where
  | shiftIsBounded | isPowerOfTwo | oneBit | uaddOvf | is32Bit | bool2int
  | log (w : Nat) | logu | ntz (w : Nat) | nlz (w : Nat) | bitsLen | onesCount
  | bitsMulU64 | bitsMulU32 | bitsAdd64 | modInverse
  | umagicOK (w : Nat) | smagicOK | udivisibleOK (w : Nat)
  | umagic (w : Nat) | smagic (w : Nat) | udivisible (w : Nat) | sdivisible (w : Nat)
  | reciprocalExact64 | reciprocalExact32
  | armBFAuxInt | bfMask | bfWidth
  deriving DecidableEq, Repr

/-- The width `k` of the arm64 bit-field mask `mask >> rshift` (`isARM64BFMask`,
`arm64BFWidth`): `int64(uint64(mask) >> uint64(rshift))` is `2^k - 1` with `1 ≤ k ≤ 62`, which
Go's `isPowerOfTwo(shiftedMask+1)` (an `int64`) and `shiftedMask != 0` ask; `nto` of it is `k`.
`none` for any other mask (where `arm64BFWidth` panics on a zero mask, and is the oracle's on the
others, which `isARM64BFMask` rejects). -/
def bfMaskW (mask rshift : Int) : Option Nat :=
  if 0 ≤ rshift ∧ rshift < 64 then
    let n := (mask.emod (2 ^ 64)).toNat / 2 ^ rshift.toNat
    let k := Nat.log2 (n + 1)
    if n ≠ 0 ∧ n + 1 = 2 ^ k ∧ k ≤ 62 then some k else none
  else none

/-- `reciprocalExact64`/`reciprocalExact32` on the encoding `b` of a float with `E` exponent and
`F` fraction bits: a power of two whose reciprocal is a normal number (fraction 0, biased
exponent neither 0 nor the two largest). -/
def reciprocalExactB (E F b : Nat) : Bool :=
  let ex := (b / 2 ^ F) % 2 ^ E
  b % 2 ^ F == 0 && ex != 0 && ex != 2 ^ E - 1 && ex != 2 ^ E - 2

/-- The helper a call names (`none`: not modelled, the call is the oracle's). The rule lemmas
rewrite it on a literal name with the lemmas of `GoFV/Proof/Rules/Names.lean`. -/
def Helper.ofName : String → Option Helper
  | "shiftIsBounded" => some .shiftIsBounded
  | "isPowerOfTwo" => some .isPowerOfTwo
  | "oneBit" => some .oneBit
  | "uaddOvf" => some .uaddOvf
  | "is32Bit" => some .is32Bit
  | "bool2int" => some .bool2int
  | "log8" => some (.log 8) | "log16" => some (.log 16) | "log32" => some (.log 32)
  | "log64" => some (.log 64)
  | "log8u" | "log16u" | "log32u" | "log64u" => some .logu
  | "ntz8" => some (.ntz 8) | "ntz16" => some (.ntz 16) | "ntz32" => some (.ntz 32)
  | "ntz64" => some (.ntz 64)
  | "nlz8" => some (.nlz 8) | "nlz16" => some (.nlz 16) | "nlz32" => some (.nlz 32)
  | "nlz64" => some (.nlz 64)
  | "bits.Len8" | "bits.Len16" | "bits.Len32" | "bits.Len64" => some .bitsLen
  | "bits.OnesCount8" | "bits.OnesCount16" | "bits.OnesCount32" | "bits.OnesCount64" =>
    some .onesCount
  | "bitsMulU64" => some .bitsMulU64
  | "bitsMulU32" => some .bitsMulU32
  | "bitsAdd64" => some .bitsAdd64
  | "modularMultiplicativeInverse" => some .modInverse
  | "umagicOK8" => some (.umagicOK 8) | "umagicOK16" => some (.umagicOK 16)
  | "umagicOK32" => some (.umagicOK 32) | "umagicOK64" => some (.umagicOK 64)
  | "smagicOK8" | "smagicOK16" | "smagicOK32" | "smagicOK64" | "sdivisibleOK8"
  | "sdivisibleOK16" | "sdivisibleOK32" | "sdivisibleOK64" => some .smagicOK
  | "udivisibleOK8" => some (.udivisibleOK 8) | "udivisibleOK16" => some (.udivisibleOK 16)
  | "udivisibleOK32" => some (.udivisibleOK 32) | "udivisibleOK64" => some (.udivisibleOK 64)
  | "umagic8" => some (.umagic 8) | "umagic16" => some (.umagic 16)
  | "umagic32" => some (.umagic 32) | "umagic64" => some (.umagic 64)
  | "smagic8" => some (.smagic 8) | "smagic16" => some (.smagic 16)
  | "smagic32" => some (.smagic 32) | "smagic64" => some (.smagic 64)
  | "udivisible8" => some (.udivisible 8) | "udivisible16" => some (.udivisible 16)
  | "udivisible32" => some (.udivisible 32) | "udivisible64" => some (.udivisible 64)
  | "sdivisible8" => some (.sdivisible 8) | "sdivisible16" => some (.sdivisible 16)
  | "sdivisible32" => some (.sdivisible 32) | "sdivisible64" => some (.sdivisible 64)
  | "reciprocalExact32" => some .reciprocalExact32
  | "reciprocalExact64" => some .reciprocalExact64
  | "armBFAuxInt" => some .armBFAuxInt
  | "isARM64BFMask" => some .bfMask
  | "arm64BFWidth" => some .bfWidth
  | _ => none

/-- A helper applied to evaluated arguments with their Go types (`GoFV.Rules.Eval.call`);
`none` where Go would fail or the arguments are not modelled. -/
def callH (e : PEnv) : Helper → List (DV × GoTy) → Option DV
  | .shiftIsBounded, [(.val _ (some p), _)] => some (.bool (e.auxInt p != 0))
  | .isPowerOfTwo, [(.int x, t)] =>
    t.intInfo?.map fun (w, s) => .bool (x > 0 && wrapInt w s (andPred t x) == 0)
  | .oneBit, [(.int x, t)] =>
    t.intInfo?.map fun (w, s) => .bool (wrapInt w s (andPred t x) == 0 && x != 0)
  | .uaddOvf, [(.int a, _), (.int b, _)] =>
    some (.bool ((a.emod (2 ^ 64) + b.emod (2 ^ 64)).emod (2 ^ 64) < a.emod (2 ^ 64)))
  | .is32Bit, [(.int n, _)] => some (.bool (n == wrapInt 32 true n))
  | .bool2int, [(.bool b, _)] => some (.int (if b then 1 else 0))
  | .log w, [(.int n, _)] => some (.int (bitsLen (n.emod (2 ^ w)).toNat - 1))
  | .logu, [(.int n, _)] => some (.int (bitsLen n.toNat - 1))
  | .ntz w, [(.int x, _)] => some (.int (trailingZeros (x.emod (2 ^ w)).toNat w))
  | .nlz w, [(.int x, _)] => some (.int (w - bitsLen (x.emod (2 ^ w)).toNat))
  | .bitsLen, [(.int x, _)] => some (.int (bitsLen x.toNat))
  | .onesCount, [(.int x, _)] => some (.int (onesCount x.toNat))
  | .bitsMulU64, [(.int x, _), (.int y, _)] =>
    let p := x.emod (2 ^ 64) * y.emod (2 ^ 64)
    some (.strct [("hi", .int (wrapInt 64 true (p / 2 ^ 64))), ("lo", .int (wrapInt 64 true p))])
  | .bitsMulU32, [(.int x, _), (.int y, _)] =>
    let p := x.emod (2 ^ 32) * y.emod (2 ^ 32)
    some (.strct [("hi", .int (wrapInt 32 true (p / 2 ^ 32))), ("lo", .int (wrapInt 32 true p))])
  | .bitsAdd64, [(.int x, _), (.int y, _), (.int c, _)] =>
    let s := x.emod (2 ^ 64) + y.emod (2 ^ 64) + c.emod (2 ^ 64)
    some (.strct [("sum", .int (wrapInt 64 true s)), ("carry", .int (s / 2 ^ 64))])
  | .modInverse, [(.int x, _)] =>
    match Magic.modInverse (x.emod (2 ^ 64)).toNat with
    | .ok y => some (.int y)
    | .error _ => none
  | .umagicOK w, [(.int c, _)] => some (.bool (Magic.umagicOK w c))
  | .smagicOK, [(.int c, _)] => some (.bool (Magic.smagicOK c))
  | .udivisibleOK w, [(.int c, _)] => some (.bool (Magic.udivisibleOK w c))
  | .umagic w, [(.int c, _)] => magicDV (Magic.umagic w c)
  | .smagic w, [(.int c, _)] => magicDV (Magic.smagic w c)
  | .udivisible w, [(.int c, _)] => udivDV (Magic.udivisible w c)
  | .sdivisible w, [(.int c, _)] => sdivDV (Magic.sdivisible w c)
  | .reciprocalExact64, [(.f64 x, _)] => some (.bool (reciprocalExactB 11 52 x.toNat))
  | .reciprocalExact32, [(.f32 x, _)] => some (.bool (reciprocalExactB 8 23 x.toNat))
  | .armBFAuxInt, [(.int l, _), (.int w, _)] =>
    if 0 ≤ l ∧ l ≤ 63 ∧ 1 ≤ w ∧ l + w ≤ 64 then some (.int (w + l * 256)) else none
  | .bfMask, [(.int l, _), (.int m, _), (.int r, _)] =>
    match bfMaskW m r with
    | some k => some (.bool (decide ((k : Int) + l < 64)))
    | none => some (.bool false)
  | .bfWidth, [(.int m, _), (.int r, _)] =>
    match bfMaskW m r with
    | some k => some (.int k)
    | none => none
  | _, _ => none

/-- Field selection on modelled values. -/
def fieldDV (e : PEnv) : DV → String → Option DV
  | .val _ (some p), "Type" => some (.ty (e.ty p))
  | .val _ (some p), "AuxInt" => some (.int (e.auxInt p).toInt)
  | .strct fs, n => strctField fs n
  | _, _ => none

/-- `DV.int` of a `.int`, else `none`. -/
def DV.asInt? : DV → Option Int
  | .int i => some i
  | _ => none

/-- A constant (a float literal by its encoding: a pattern check `[c]` then asks the auxint's
encoding to be `c`'s, which for `±0` is stricter than Go's float `==`). -/
def litDV : Lit → Option DV
  | .int i => some (.int i)
  | .bool b => some (.bool b)
  | .float64 b => some (.f64 (BitVec.ofNat 64 b))
  | .float32 b => some (.f32 (BitVec.ofNat 32 b))
  | _ => none

/-- `config.<name>` (a 64-bit target: `PtrSize` is 8, the size of the semantics' pointers,
`Ty.size`); the other fields are the oracle's. -/
def configField : String → Option Int
  | "PtrSize" => some 8
  | _ => none

/-- `y.n`, given `y` and its value (`typ.<T>` is a type shape, `config.<n>` by `configField`). -/
def fieldE (e : PEnv) (y : Expr) (dy : DV) (n : String) : Option DV :=
  match y with
  | .rsv .typ => (typShape n).map .ty
  | .rsv .config => match configField n with
    | some i => some (.int i)
    | none => fieldDV e dy n
  | _ => fieldDV e dy n

/-- `y[k]` (only `types.Types[k]`). -/
def indexE (y : Expr) (dk : DV) : Option DV :=
  match y, dk with
  | .glob "types.Types" _, .int k => (typesShape k).map .ty
  | _, _ => none

/-- `T(y)` between integer types. -/
def convE (ty : GoTy) : DV → Option DV
  | .int i => if ty.intInfo?.isSome then some (.int (wrapTo ty i)) else none
  | _ => none

/-- Binary operators; `&&`/`||` give the right operand's value when it decides. Comparisons
take the left operand's type, the others the node's (`GoFV.Rules.Eval.eval`). -/
def binE (vtys : List GoTy) (o : BinOp) (ty : GoTy) (y : Expr) (dy dz : DV) : Option DV :=
  match o with
  | .land => match dy with
    | .bool true => some dz
    | .bool false => some (.bool false)
    | _ => none
  | .lor => match dy with
    | .bool true => some (.bool true)
    | .bool false => some dz
    | _ => none
  | .eq | .ne | .lt | .le | .gt | .ge => binDV o (exprTy vtys y) dy dz
  | _ => binDV o ty dy dz

/-- Calls of the modelled helpers. -/
def callE (vtys : List GoTy) (e : PEnv) (fn : String) (args : List Expr) (dargs : List DV) :
    Option DV :=
  match Helper.ofName fn with
  | some h => callH e h (dargs.zip (args.map (exprTy vtys)))
  | none => none

/-- Method calls: `t.Size()` of an integer or boolean shape; `t.Elem()` of a pointer shape
with a known element size `k` is the element type known by its size only, a record with the
one attribute `Size` (`t.Elem().Size()` is `k`; any other use of it is the oracle's); `t.Elem()`
of a slice shape `.slice el` (data pointer `.ptr el`), or of an aggregate of at least two fields
whose first is a pointer `.ptr el` (or the 64-bit integer word, which has the same values as a
pointer, `Val.hasTy_ptr_eq_i64`: `.ptr none`), is the element type known by its pointer type
only, the record with the one attribute `PtrTo` (`t.Elem().PtrTo()` is `.ptr el`); `t.Elem()` of an
aggregate of one field at offset 0 is that field's shape (`Sem.tyOf` of a one-element array
`[1]T`: `T`'s shape); `t.FieldType(i)` of a tuple shape with a literal `i` is its component `i`
(`generic.rules:193`: the flag of a `Mul64uover`); the kind predicates by `kindE`. The method
name is matched first, so that a method of an unknown type shape is still `none`. An
`arm64BitField` (an integer) has `lsb()`, `int64(uint64(bfc) >> 8)`, and `width()`,
`int64(bfc) & 0xff`. -/
def methodE (dy : DV) (n : String) (args : List Expr) : Option DV :=
  match n, args with
  | "Size", [] => match dy with
    | .ty t => (shapeSize t).map .int
    | .strct fs => strctField fs "Size"
    | _ => none
  | "Elem", [] => match dy with
    | .ty (.ptr (some k)) => some (.strct [("Size", .int k)])
    | .ty (.slice el) => some (.strct [("PtrTo", .ty (.ptr el))])
    | .ty (.agg ((_, .ptr el) :: _ :: _) _) => some (.strct [("PtrTo", .ty (.ptr el))])
    | .ty (.agg ((_, .int .w64) :: _ :: _) _) => some (.strct [("PtrTo", .ty (.ptr none))])
    | .ty (.agg [(0, f)] _) => some (.ty f)
    | _ => none
  | "PtrTo", [] => match dy with
    | .strct fs => strctField fs "PtrTo"
    | _ => none
  | "FieldType", [.lit _ (.int i)] => match dy with
    | .ty (.tuple ts) => if i < 0 then none else (ts[i.toNat]?).map .ty
    | _ => none
  | "lsb", [] => match dy with
    | .int i => some (.int ((i.emod (2 ^ 64)).toNat / 256 : Nat))
    | _ => none
  | "width", [] => match dy with
    | .int i => some (.int (i.emod 256))
    | _ => none
  | "IsPtrShaped", [] => kindDV .ptrShaped dy
  | "IsString", [] => kindDV .string dy
  | "IsSlice", [] => kindDV .slice dy
  | "IsInterface", [] => kindDV .inter dy
  | "IsComplex", [] => kindDV .complex dy
  | _, _ => none

/-- Builtins: `min` of two integers. -/
def builtinE (fn : String) (dargs : List DV) : Option DV :=
  match fn, dargs with
  | "min", [.int a, .int b] => some (.int (min a b))
  | _, _ => none

mutual
/-- The evaluator. `vtys`: the rule variables' Go types; `σ`: their values; `e`: the instance
(for the fields of pattern nodes); `top`: the value of `v`. One equation per constructor. -/
def evalE (vtys : List GoTy) (σ : Nat → DV) (or : Oracle) (e : PEnv) (top : Val) :
    Expr → DV
  | x@(.lit _ c) => (litDV c).getD (or.dv x)
  | x@(.cnst _ _ c) => (litDV c).getD (or.dv x)
  | .op o => .op o
  | .var i => σ i
  | x@(.rsv r) => match r with
    | .v => .val top (some [])
    | _ => or.dv x
  | x@(.glob _ _) => or.dv x
  | x@(.field y n _) => (fieldE e y (evalE vtys σ or e top y) n).getD (or.dv x)
  | x@(.call fn args _) =>
    (callE vtys e fn args (evalEs vtys σ or e top args)).getD (or.dv x)
  | x@(.method y n args _) => (methodE (evalE vtys σ or e top y) n args).getD (or.dv x)
  | x@(.builtin fn args _) => (builtinE fn (evalEs vtys σ or e top args)).getD (or.dv x)
  | x@(.conv ty y) => (convE ty (evalE vtys σ or e top y)).getD (or.dv x)
  | x@(.assert _ _) => or.dv x
  | x@(.unop o y ty) => (unDV o ty (evalE vtys σ or e top y)).getD (or.dv x)
  | x@(.binop o y z ty) =>
    (binE vtys o ty y (evalE vtys σ or e top y) (evalE vtys σ or e top z)).getD (or.dv x)
  | x@(.index y k _) => (indexE y (evalE vtys σ or e top k)).getD (or.dv x)
  | x@(.deref _ _) => or.dv x
/-- `evalE` of each expression. -/
def evalEs (vtys : List GoTy) (σ : Nat → DV) (or : Oracle) (e : PEnv) (top : Val) :
    List Expr → List DV
  | [] => []
  | a :: as => evalE vtys σ or e top a :: evalEs vtys σ or e top as
end

/-! ## Pattern checks and results -/

mutual
/-- The checks of the pattern at `p` that are not structural: `same x`, `<e>`, `[e]`, each
stated as "the instance's field equals the expected value" (the instance on the left, so that
`simp` rewrites instance terms into the rule's constants). -/
def Pat.cons (ev : Expr → DV) (σ : Nat → DV) (e : PEnv) (p : Path) : Pat → Prop
  | .wild | .bind _ => True
  | .same x =>
    match σ x with
    | .val w _ => e.leaf p = w
    | _ => True
  | .op o _ ty ai _ _ args _ =>
    (match ty with | .eq te => DV.ty (e.ty p) = ev te | _ => True) ∧
    (match ai with | .eq ae => auxIntDV o.auxType (e.auxInt p) = ev ae | _ => True) ∧
    Pat.conss ev σ e p 0 args
def Pat.conss (ev : Expr → DV) (σ : Nat → DV) (e : PEnv) (p : Path) (i : Nat) :
    List Pat → Prop
  | [] => True
  | q :: qs => Pat.cons ev σ e (i :: p) q ∧ Pat.conss ev σ e p (i + 1) qs
end

mutual
/-- Every leaf of the pattern at `p` has its type's shape: a matched value is a register whose
value `evalValue` retyped to its `Type` (docs/proofs/rules.md, "Assumptions to discharge"). -/
def Pat.typed (e : PEnv) (p : Path) : Pat → Prop
  | .op _ _ _ _ _ _ args _ => Pat.typeds e p 0 args
  | _ => (e.leaf p).hasTy (e.ty p) = true
def Pat.typeds (e : PEnv) (p : Path) (i : Nat) : List Pat → Prop
  | [] => True
  | q :: qs => Pat.typed e (i :: p) q ∧ Pat.typeds e p (i + 1) qs
end

/-- The checker's facts about an auxint of aux type `aty` that the rules rely on
(`docs/contracts/check.md`, "Aux"): `Bool` auxints are 0 or 1, float auxints (the `float64`
encoding, also of `Float32`) are not NaN. -/
def auxIntOk (aty : AuxType) (a : Int64) : Prop :=
  match aty with
  | .Bool => a = 0 ∨ a = 1
  | .Float32 | .Float64 => IEEE.isNaN .b64 (BitVec.ofInt 64 a.toInt) = false
  | _ => True

mutual
/-- Every op node of the pattern at `p` has a well-formed auxint (`auxIntOk`). -/
def Pat.wf (e : PEnv) (p : Path) : Pat → Prop
  | .op o _ _ _ _ _ args _ => auxIntOk o.auxType (e.auxInt p) ∧ Pat.wfs e p 0 args
  | _ => True
def Pat.wfs (e : PEnv) (p : Path) (i : Nat) : List Pat → Prop
  | [] => True
  | q :: qs => Pat.wf e (i :: p) q ∧ Pat.wfs e p (i + 1) qs
end

/-- A pointer shape. -/
def isPtrTy : Ty → Bool
  | .ptr _ => true
  | _ => false

/-- `.int .w64`. -/
def isInt64Ty : Ty → Bool
  | .int .w64 => true
  | _ => false

/-- `.int w`. -/
def isIntWTy : Width → Ty → Bool
  | .w8, .int .w8 | .w16, .int .w16 | .w32, .int .w32 | .w64, .int .w64 => true
  | _, _ => false

/-- A slice shape. -/
def isSliceTy : Ty → Bool
  | .slice _ => true
  | _ => false

/-- The argument of a `Convert` of shape `ty`: a 64-bit integer to a pointer, a pointer to a
64-bit integer; nothing else. -/
def convArgOk (ty t : Ty) : Bool :=
  match ty with
  | .ptr _ => isInt64Ty t
  | .int .w64 => isPtrTy t
  | _ => false

/-- A value of shape `t` has shape `f` too (and `retype f` keeps it, `retype_of_hasTy`): the
same shape, or two pointer shapes (`Val.hasTy` and `Val.retype` at a pointer shape ignore the
element size). -/
def shapeSub (t f : Ty) : Bool := Ty.beq t f || (isPtrTy t && isPtrTy f)

/-- The shape of component `i` of a composite shape (of a string or slice: of its aggregate
layout, `Ty.asAgg`). -/
def fieldShape? (t : Ty) (i : Nat) : Option Ty :=
  match t.asAgg with
  | .agg fs _ => fs[i]?.map (·.2)
  | _ => none

/-- Argument `i` (of shape `t`) of a `Make` op of shape `ty` has the shape of component `i`
(`shapeSub`); unconstrained if `ty` has no component `i` (the `Make` is then `poison`). -/
def makeArgOk (ty : Ty) (i : Nat) (t : Ty) : Bool :=
  match fieldShape? ty i with
  | some f => shapeSub t f
  | none => true

/-- An `EqInter`/`NeqInter` operand of shape `t`: its first component (the itab word) has the
64-bit integer shape, so it holds an integer or a pointer without a concrete address and
`ITab`'s `uintptr` retype keeps it. Unconstrained if `t` has no first component (the
comparison is then `poison`). -/
def ifaceArgOk (t : Ty) : Bool :=
  match fieldShape? t 0 with
  | some f => isInt64Ty f
  | none => true

/-- An `IData` operand of shape `t`: an aggregate whose second component (the data word) has a
word shape, the interface shape (`generic.rules:982`: a data word read at a struct shape is
`poison`, so a selection of it is; at an aggregate data word it would select a field). -/
def idataArgOk : Ty → Bool
  | .agg fs _ =>
    match fs[1]? with
    | some (_, f) => isPtrTy f || isInt64Ty f
    | none => false
  | _ => false

/-- Component `i` of the tuple shape `tt` is `t`. -/
def tupleCompOk (tt : Ty) (i : Nat) (t : Ty) : Bool :=
  match tt with
  | .tuple ts => (ts[i]?).any (Ty.beq · t)
  | _ => false

/-- The shape the checker guarantees for argument `i` (of shape `t`) of an op `o` of shape `ty`:
the pointer argument of `OffPtr`/`IsNonNil` a word (a pointer or a 64-bit integer: `SP` and
some `ConstNil`s are `uintptr`-typed; the two word shapes have the same values and retype alike,
`Val.hasTy_ptr_eq_i64`, `Val.retype_ptr_eq_i64`), the pointer argument of `AddPtr`/`PtrIndex`,
both of `EqPtr`/`NeqPtr` a
pointer or a 64-bit integer (`uintptr`: the itabs `NeqInter` compares, `generic.rules:791`), a
64-bit integer offset of `AddPtr`/`PtrIndex`, an `AddPtr` itself of a pointer shape (a
`uintptr`-typed one would be compared by the concrete address, which a pointer that does not
convert back to itself does not round-trip: `generic.rules:1680`), `Convert` between a
pointer and a 64-bit integer (`convArgOk`), both arguments of `Eq<N>`/`Neq<N>` integers of
width `N`, both of
`IsInBounds`/`IsSliceInBounds` and the argument of `Slicemask` 64-bit integers (`int` on the
64-bit target: the semantics compares (masks) at the first argument's (the result's) width, the
rules' `Const64` operands mean 64-bit values), the
first word of an `EqInter`/`NeqInter` operand a 64-bit integer (the itab word of the interface
shape, `ifaceArgOk`), the
components of a `Make` op the shapes of its type's components (`makeArgOk`, issue #17), a
`SliceMake` itself of a slice shape (whose `retype` checks `0 ≤ len ≤ cap`: `generic.rules:1053`
needs it), the
argument of `SlicePtr`/`SliceLen`/`SliceCap` a slice (so it is `poison` or has
`0 ≤ len ≤ cap`: `generic.rules:278`), the argument of `IData` of the interface shape
(`idataArgOk`), the
arguments of the float arithmetic and comparisons floats of their width (shape `.int w`), a
`Mul32uover`/`Mul64uover` itself of its tuple shape (the integer and the overflow flag), the
components of a `MakeTuple` the shapes of its two-component tuple shape's, and the argument of a
`Select0`/`Select1` a tuple whose selected component has the selection's shape (`tupleCompOk`;
`generic.rules:193`, `:1339`, `:1340`). Other arguments are unconstrained. -/
def argShapeOk (o : Op) (ty : Ty) (i : Nat) (t : Ty) : Bool :=
  match o with
  | .OffPtr | .IsNonNil => i != 0 || isPtrTy t || isInt64Ty t
  | .EqPtr | .NeqPtr => isPtrTy t || isInt64Ty t
  | .AddPtr => if i == 0 then isPtrTy t && isPtrTy ty else i != 1 || isInt64Ty t
  | .PtrIndex => if i == 0 then isPtrTy t else i != 1 || isInt64Ty t
  | .Convert => i != 0 || convArgOk ty t
  | .Eq64 | .Neq64 => isIntWTy .w64 t
  | .Eq32 | .Neq32 => isIntWTy .w32 t
  | .Eq16 | .Neq16 => isIntWTy .w16 t
  | .Eq8 | .Neq8 => isIntWTy .w8 t
  | .IsInBounds | .IsSliceInBounds | .Slicemask => isIntWTy .w64 t
  | .EqInter | .NeqInter => ifaceArgOk t
  | .StringMake | .IMake | .ComplexMake | .StructMake | .ArrayMake1 => makeArgOk ty i t
  | .SliceMake => isSliceTy ty && makeArgOk ty i t
  | .SlicePtr | .SliceLen | .SliceCap => isSliceTy t
  | .IData => idataArgOk t
  | .Add64F | .Sub64F | .Mul64F | .Div64F | .Neg64F | .Min64F | .Max64F | .Eq64F | .Neq64F
  | .Less64F | .Leq64F | .Abs | .Copysign | .Sqrt | .Floor | .Ceil | .Trunc | .Round
  | .RoundToEven | .FMA | .Round64F => isIntWTy .w64 t
  | .Add32F | .Sub32F | .Mul32F | .Div32F | .Neg32F | .Min32F | .Max32F | .Eq32F | .Neq32F
  | .Less32F | .Leq32F | .Sqrt32 | .Round32F => isIntWTy .w32 t
  | .Mul32uover => Ty.beq ty (.tuple [.int .w32, .bool])
  | .Mul64uover => Ty.beq ty (.tuple [.int .w64, .bool])
  | .MakeTuple => match ty with
    | .tuple ts => ts.length == 2 && tupleCompOk ty i t
    | _ => false
  | .Select0 => i != 0 || tupleCompOk t 0 ty
  | .Select1 => i != 0 || tupleCompOk t 1 ty
  | _ => true

/-- Leaf positions of a rule's pattern that hold the same value although the rule does not say
so, as the compiler builds them: `generic.rules:1053` (`(SliceMake (AddPtr <t> x (And64 y
(Slicemask _))) w:(Const64 [c]) z) && c > 0`) relies on the `Slicemask` argument being the
capacity `z` (`ssagen`'s slicing builds `SliceMake (AddPtr ptr (And64 delta (Slicemask cap)))
len cap`; Go: "len > 0 implies cap > 0 implies Slicemask is all 1"). The rewrite validator
checks them on the instance (`RewriteCheck.condFrameOK`: the same value). -/
def sameLeaves (r : Rule) : List (Path × Path) :=
  if r.loc = ⟨"generic", 1053⟩ then [([0, 1, 1, 0], [2])] else []

mutual
/-- Every argument of every op node of the pattern at `p` has the shape `argShapeOk` asks for,
by the instance's types `ty` (`docs/proofs/rules.md`, "Assumptions to discharge"). -/
def Pat.argsOK (ty : Path → Ty) (p : Path) : Pat → Bool
  | .op o _ _ _ _ _ args _ => Pat.argsOKs ty p o 0 args
  | _ => true
/-- `Pat.argsOK` of the arguments `i, i+1, …` of an `o` node at `p`. -/
def Pat.argsOKs (ty : Path → Ty) (p : Path) (o : Op) (i : Nat) : List Pat → Bool
  | [] => true
  | q :: qs => argShapeOk o (ty p) i (ty (i :: p)) && Pat.argsOK ty (i :: p) q &&
      Pat.argsOKs ty p o (i + 1) qs
end

/-- A nonnegative integer (sign bit clear at its width) or `poison`. -/
def _root_.GoFV.SSA.Sem.Val.nonNeg : Val → Bool
  | .poison => true
  | .int _ x => !x.msb
  | _ => false

/-- The rule variables `x` of the conjuncts `isNonNegative(x)` of a condition. -/
def nonNegVars : Expr → List Nat
  | .binop .land a b _ => nonNegVars a ++ nonNegVars b
  | .call fn [.var x] _ => if fn == "isNonNegative" then [x] else []
  | _ => []

mutual
/-- The position of the first leaf of the pattern at `p` that binds `x`. -/
def Pat.leafPos (x : Nat) (p : Path) : Pat → Option Path
  | .bind y => if y == x then some p else none
  | .op _ _ _ _ _ _ args _ => Pat.leafPoss x p 0 args
  | _ => none
/-- `Pat.leafPos` in the arguments `i, i+1, …` of a node at `p`. -/
def Pat.leafPoss (x : Nat) (p : Path) (i : Nat) : List Pat → Option Path
  | [] => none
  | q :: qs => (Pat.leafPos x (i :: p) q).orElse fun _ => Pat.leafPoss x p (i + 1) qs
end

/-- For every conjunct `isNonNegative(x)` of the condition with `x` bound at a leaf, the leaf's
value is a nonnegative integer or `poison` (`Val.nonNeg`; `docs/proofs/rules.md`, "Assumptions
to discharge"). The rewrite validator decides `isNonNegative` on the matched value's
definitions (`GoFV.Opt.RewriteCheck.nonNegD`), where it implies this of every evaluation. -/
def Pat.nonNegOK (e : PEnv) (pat : Pat) : Option Expr → Bool
  | some c => (nonNegVars c).all fun x => match Pat.leafPos x [] pat with
    | some p => (e.leaf p).nonNeg
    | none => true
  | none => true

mutual
/-- The argument counts are those of the pattern (no `___`, no ellipsis). -/
def Pat.arityOk : Pat → Bool
  | .op _ _ _ _ _ ar args _ =>
    (match ar with | .fixed | .exact _ => true | _ => false) && Pat.arityOks args
  | _ => true
def Pat.arityOks : List Pat → Bool
  | [] => true
  | q :: qs => Pat.arityOk q && Pat.arityOks qs
end

/-- `<T>ToAuxInt` (`GoFV.Rules.Interp.toAuxInt`); `none` where the interpreter fails. -/
def toAuxIntD (aty : AuxType) : DV → Option Int64
  | .bool b => match aty with
    | .Bool => some (if b then 1 else 0)
    | _ => none
  | .int i => match aty with
    | .UInt8 => some (Int64.ofInt (wrapInt 8 true i))
    | _ => some (Int64.ofInt i)
  | .f64 b => match aty with
    | .Float64 => some (Int64.ofInt b.toInt)
    | _ => none
  | .f32 b => match aty with
    | .Float32 => some (Int64.ofInt (IEEE.convert .b32 .b64 .rne b).toInt)
    | _ => none
  | _ => none

/-- The value a variable argument of a result refers to. -/
def DV.valOr (d : DV) (dflt : Val) : Val :=
  match d with
  | .val v _ => v
  | _ => dflt

/-- The values of result nodes: node `k` with `fuel` levels below it (`nodes.length`
suffices). The top (node 0) keeps `v`'s type shape `topTy` unless it has a `<type>`; reset
fields are 0/nil. -/
def nodeDen (ev : Expr → DV) (or : Oracle) (σ : Nat → DV) (topTy : Ty) (nodes : List RNode) :
    Nat → Nat → Val
  | 0, _ => .poison
  | fuel + 1, k =>
    match nodes[k]? with
    | none => .poison
    | some n =>
      let t := match n.ty with
        | some te => match ev te with
          | .ty t => t
          | _ => or.ty te
        | none => topTy
      let ai := match n.auxInt with
        | some ae => (toAuxIntD n.op.auxType (ev ae)).getD (or.auxInt ae)
        | none => 0
      let ax := match n.aux with
        | some xe => or.aux xe
        | none => none
      let argv := n.args.map fun
        | .var x => (σ x).valOr (or.val (.var x))
        | .node j => nodeDen ev or σ topTy nodes fuel j
        | .expr e => (ev e).valOr (or.val e)
      (evalPure n.op t ai ax argv).retype t

/-- The value `v` has after the rewrite. -/
def resDen (ev : Expr → DV) (or : Oracle) (σ : Nat → DV) (topTy : Ty) : Result → Val
  | .copy ce => match ev ce with
    | .val w _ => w
    | _ => or.val ce
  | .build nodes => nodeDen ev or σ topTy nodes nodes.length 0
  | .setOp o => or.val (.op o)

/-- The condition holds. -/
def condHolds (ev : Expr → DV) : Option Expr → Prop
  | some c => ev c = .bool true
  | none => True

/-- The oracle answers every unmodelled expression of Go type `bool` with a boolean (Go's
evaluation of a well-typed `bool` expression gives a boolean). Without it an oracle atom in a
conjunct (`div.Uses == 1 && …`) could make `&&` see a non-boolean, and the whole condition
would be the oracle's, unrelated to the modelled conjuncts. -/
def Oracle.BoolTyped (or : Oracle) : Prop :=
  ∀ x : Expr, exprTy [] x = .bool → ∃ b, or.dv x = .bool b

/-- **The obligation of a value rule.** For every instance of the pattern whose auxints are
well formed (`Pat.wf`), whose checks and condition hold, whose top value has its type's
shape, whose leaves have their types' shapes (`Pat.typed`), whose op nodes' arguments the
shapes the checker guarantees (`Pat.argsOK`) and whose `isNonNegative` leaves are nonnegative
(`Pat.nonNegOK`), and every oracle answering `bool` expressions with booleans
(`Oracle.BoolTyped`), the rewritten value refines the matched one. -/
def Rule.Sound (r : Rule) : Prop :=
  Pat.arityOk r.pat = true ∧
  ∀ (e : PEnv) (or : Oracle), Oracle.BoolTyped or →
    let σ := sigma e r.pat
    let ev := evalE (r.vars.map (·.ty)) σ or e (Pat.den e [] r.pat)
    Pat.wf e [] r.pat →
    Pat.cons ev σ e [] r.pat →
    condHolds ev r.cond →
    (Pat.raw e r.pat).hasTy (e.ty []) = true →
    Pat.typed e [] r.pat →
    Pat.argsOK e.ty [] r.pat = true →
    Pat.nonNegOK e r.pat r.cond = true →
    Refines (Pat.raw e r.pat) (resDen ev or σ (e.ty []) r.result)



/-! Equation lemmas of the denotation, generated here once rather than in every rule module
(LEARNINGS.md, "Large `match` on a variable"). -/
attribute [local simp] Pat.den Pat.dens Pat.raw Pat.binds Pat.bindss Pat.cons Pat.conss
  Pat.wf Pat.wfs Pat.typed Pat.typeds auxIntOk Pat.argsOK Pat.argsOKs
  Pat.arityOk Pat.arityOks evalE evalEs nodeDen resDen condHolds sigma auxIntDV toAuxIntD
  litDV fieldE indexE convE binE callE callH methodE builtinE binDV floatCmp unDV intBin fieldDV DV.valOr
  Field.bindDV
end GoFV.Proof.Rules

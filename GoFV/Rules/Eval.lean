import GoFV.Rules.GoVal
import GoFV.Rules.Helpers.Build
import GoFV.Rules.Helpers.Magic
import GoFV.Rules.Helpers.Ptr

/-!
# Evaluation of rule expressions

`evalExpr` gives a type-checked Go expression of a rule (`GoFV.Rules.Expr`) its Go meaning in
the rewrite state: rule variables, the reserved names (`v`, `b`, `config`, `fe`, `typ`),
fields, the `rewrite.go` helpers, `*types.Type` methods, conversions and operators
(docs/contracts/rules.md, "Go expression semantics" and the helper inventory).
-/

namespace GoFV.Rules

open GoFV.SSA

/-- The bindings an expression is evaluated under: `v` (absent in block rules), `b`, and the
rule variables. -/
structure Scope where
  v : Option ID
  b : ID
  binds : Array GVal
  /-- The Go types of the rule variables. -/
  vtys : Array GoTy
  /-- Type variables bound from a matched value's `<type>` field, with that value (the
  variable stands for its `*types.Type` object, #101). -/
  tySrc : List (Nat × ID) := []

namespace GVal

def asInt : GVal → Except String Int
  | .int i => .ok i
  | _ => .error "expected an integer"
def asBool : GVal → Except String Bool
  | .bool b => .ok b
  | _ => .error "expected a bool"
def asVal : GVal → Except String ID
  | .val v => .ok v
  | _ => .error "expected a *Value"
def asTyp : GVal → Except String TypeRef
  | .typ t => .ok t
  | _ => .error "expected a *types.Type"
def asAux : GVal → Except String (Option AuxRef)
  | .aux a => .ok a
  | .nil => .ok none
  | _ => .error "expected an Aux"
def asStr : GVal → Except String ByteArray
  | .str s => .ok s
  | _ => .error "expected a string"
def asF32 : GVal → Except String Float32
  | .f32 x => .ok x
  | _ => .error "expected a float32"
def asF64 : GVal → Except String Float
  | .f64 x => .ok x
  | _ => .error "expected a float64"

/-- Go `==` (pointer identity for compiler objects). -/
def beq : GVal → GVal → Bool
  | .int a, .int b => a == b
  | .bool a, .bool b => a == b
  | .f32 a, .f32 b => a == b
  | .f64 a, .f64 b => a == b
  | .str a, .str b => a == b
  | .val a, .val b => a == b
  | .blk a, .blk b => a == b
  | .typ a, .typ b => a == b
  | .aux a, .aux b => a == b
  | .aux a, .nil => a.isNone
  | .nil, .aux b => b.isNone
  | .op a, .op b => a == b
  | .nil, .nil => true
  | _, _ => false

end GVal

namespace Eval

open RwM

@[inline] def lift {α} (x : Except String α) : RwM α := RwM.liftE x

/-- The field `name` of a struct value. -/
def strctField (fs : List (String × GVal)) (name : String) : RwM GVal :=
  match fs.find? (·.1 == name) with
  | some (_, x) => pure x
  | none => throw s!"no struct field {name}"

/-- `x.name`. -/
def field (x : GVal) (name : String) : RwM GVal := do
  match x, name with
  | .val v, "Type" => return .typ (← val v).type
  | .val v, "Op" => return .op (← val v).op
  | .val v, "Uses" => return .int (← val v).uses
  | .val v, "AuxInt" => return .int (← val v).auxInt.toInt
  | .val v, "Block" => return .blk (← val v).block
  | .val v, "Aux" => return .aux (← val v).aux
  | .val v, "Args" => return .args v
  | .rsv .typ, n => return .typ (← typ n)
  | .rsv .config, "PtrSize" => return .int (← read).ptrSize
  | .rsv .config, "RegSize" => return .int (← read).regSize
  | .rsv .config, "ctxt" => return .ctxt
  | .ctxt, "Arch" => return .arch
  | .arch, "ByteOrder" => return .byteOrder
  | .blk _, "Func" => return .func
  | .func, "pass" => return .pass
  | .pass, "name" => return .str (← read).passName.toUTF8
  | .irSyms, "Zerobase" =>
    let z := (← read).zerobase
    return .aux (some (← symAux z none (plainSym z)))
  | .strct fs, n => strctField fs n
  | _, n => throw s!"unsupported field selection .{n}"

/-- `types.Types[k]`: the `Config.Types` entry of basic kind `k`. -/
def typesIndex (k : Int) : RwM GVal := do
  let name ← match k with
    | 1 => pure "Int8" | 2 => pure "UInt8" | 3 => pure "Int16" | 4 => pure "UInt16"
    | 5 => pure "Int32" | 6 => pure "UInt32" | 7 => pure "Int64" | 8 => pure "UInt64"
    | 9 => pure "Int" | 10 => pure "UInt" | 11 => pure "Uintptr" | 12 => pure "Complex64"
    | 13 => pure "Complex128" | 14 => pure "Float32" | 15 => pure "Float64" | 16 => pure "Bool"
    | 27 => pure "String" | 28 => pure "UnsafePtr"
    | _ => throw s!"types.Types[{k}] unsupported"
  return .typ (← typ name)

/-- `T(x)`. -/
def conv (ty : GoTy) (x : GVal) : RwM GVal := do
  match x, ty with
  | .int i, .float32 => return .f32 (intToF32 i)
  | .int i, .float64 => return .f64 (intToF64 i)
  | .int i, t =>
    if t.intInfo?.isSome then return .int (wrapTo t i)
    throw "unsupported integer conversion"
  | .f32 x, .float64 => return .f64 x.toFloat
  | .f32 x, .float32 => return .f32 x
  | .f64 x, .float32 => return .f32 x.toFloat32
  | .f64 x, .float64 => return .f64 x
  | .f32 x, t =>
    match t.intInfo? with
    | some (w, true) => return .int (floatToSigned x.toFloat w)
    | _ => throw "unsupported float conversion"
  | .f64 x, t =>
    match t.intInfo? with
    | some (w, true) => return .int (floatToSigned x w)
    | _ => throw "unsupported float conversion"
  | x, .named _ => return x
  | _, _ => throw "unsupported conversion"

/-- Integer binary operator in type `ty` (`sty` is the right operand's type for shifts). -/
def intBin (o : BinOp) (ty : GoTy) (a b : Int) : RwM GVal := do
  match o with
  | .add => return .int (wrapTo ty (a + b))
  | .sub => return .int (wrapTo ty (a - b))
  | .mul => return .int (wrapTo ty (a * b))
  | .quo => if b == 0 then throw "integer divide by zero" else return .int (wrapTo ty (goQuo a b))
  | .rem => if b == 0 then throw "integer divide by zero" else return .int (wrapTo ty (goRem a b))
  | .and => return .int (bitwise ty (· &&& ·) a b)
  | .or => return .int (bitwise ty (· ||| ·) a b)
  | .xor => return .int (bitwise ty (· ^^^ ·) a b)
  | .andNot => return .int (bitwise ty (fun x y => x &&& (2 ^ 64 - 1 - y)) a b)
  | .shl =>
    if b < 0 then throw "negative shift amount"
    let w := (ty.intInfo?.map (·.1)).getD 64
    return .int (wrapTo ty (goShl a b.toNat w))
  | .shr =>
    if b < 0 then throw "negative shift amount"
    return .int (wrapTo ty (goShr a b.toNat))
  | .eq => return .bool (a == b)
  | .ne => return .bool (a != b)
  | .lt => return .bool (a < b)
  | .le => return .bool (a ≤ b)
  | .gt => return .bool (a > b)
  | .ge => return .bool (a ≥ b)
  | _ => throw "bad integer operator"

def f64Bin (o : BinOp) (a b : Float) : RwM GVal := do
  match o with
  | .add => return .f64 (a + b)
  | .sub => return .f64 (a - b)
  | .mul => return .f64 (a * b)
  | .quo => return .f64 (a / b)
  | .eq => return .bool (a == b)
  | .ne => return .bool (a != b)
  | .lt => return .bool (a < b)
  | .le => return .bool (a ≤ b)
  | .gt => return .bool (a > b)
  | .ge => return .bool (a ≥ b)
  | _ => throw "bad float64 operator"

def f32Bin (o : BinOp) (a b : Float32) : RwM GVal := do
  match o with
  | .add => return .f32 (a + b)
  | .sub => return .f32 (a - b)
  | .mul => return .f32 (a * b)
  | .quo => return .f32 (a / b)
  | .eq => return .bool (a == b)
  | .ne => return .bool (a != b)
  | .lt => return .bool (a < b)
  | .le => return .bool (a ≤ b)
  | .gt => return .bool (a > b)
  | .ge => return .bool (a ≥ b)
  | _ => throw "bad float32 operator"

/-- Non-short-circuit binary operator on evaluated operands. -/
def binop (o : BinOp) (ty : GoTy) (a b : GVal) : RwM GVal := do
  match a, b with
  | .int x, .int y => intBin o ty x y
  | .f64 x, .f64 y => f64Bin o x y
  | .f32 x, .f32 y => f32Bin o x y
  | .bool x, .bool y =>
    match o with
    | .eq => return .bool (x == y)
    | .ne => return .bool (x != y)
    | _ => throw "bad bool operator"
  | x, y =>
    match o with
    | .eq => return .bool (x.beq y)
    | .ne => return .bool (!x.beq y)
    | _ => throw "bad operator on non-numeric values"

def unop (o : UnOp) (ty : GoTy) (x : GVal) : RwM GVal := do
  match o, x with
  | .neg, .int i => return .int (wrapTo ty (-i))
  | .neg, .f64 f => return .f64 (-f)
  | .neg, .f32 f => return .f32 (-f)
  | .not, .bool b => return .bool (!b)
  | .com, .int i => return .int (wrapTo ty (-i - 1))
  | .plus, x => return x
  | _, _ => throw "bad unary operator"

/-- Width of an integer argument type (for the generic helpers `isPowerOfTwo`, `oneBit`). -/
def widthOf (ty : GoTy) : RwM (Nat × Bool) :=
  match ty.intInfo? with
  | some x => pure x
  | none => throw "expected an integer type"

/-- The Go type of an expression node, where it carries one. -/
def exprTy : Expr → GoTy
  | .lit t _ | .cnst _ t _ | .glob _ t | .field _ _ t | .call _ _ t | .method _ _ _ t
  | .builtin _ _ t | .conv t _ | .assert t _ | .unop _ _ t | .binop _ _ _ t | .index _ _ t
  | .deref _ t => t
  | .op _ => .named "Op"
  | .var _ | .rsv _ => .named "?"

/-- The Go type of `e` under the scope's variable types. -/
def _root_.GoFV.Rules.Scope.tyOf (sc : Scope) (e : Expr) : GoTy :=
  match e with
  | .var i => sc.vtys.getD i (.named "?")
  | e => exprTy e

/-- Magic data as a Go struct value. -/
def umagicVal (r : Int × Nat) : GVal := .strct [("s", .int r.1), ("m", .int r.2)]
def udivisibleVal (r : Int × Nat × Nat) : GVal :=
  .strct [("k", .int r.1), ("m", .int r.2.1), ("max", .int r.2.2)]
def sdivisibleVal (r : Int × Nat × Nat × Nat) : GVal :=
  .strct [("k", .int r.1), ("m", .int r.2.1), ("a", .int r.2.2.1), ("max", .int r.2.2.2)]

/-- `CanSSA(t)` (`value.go`); `GOEXPERIMENT=simd` is off. -/
def canSSA (tabs : Tables) (ptrSize : Int) : Nat → TypeRef → Except String Bool
  | 0, _ => .error "CanSSA: type nesting too deep"
  | n + 1, t => do
    let sz ← Ty.size tabs t
    if sz == 0 then return true
    if sz > 4 * ptrSize then return false
    match ← Ty.kind tabs t with
    | .ARRAY =>
      if (← Ty.numElem tabs t) ≤ 1 then canSSA tabs ptrSize n (← Ty.elem tabs t) else return false
    | .STRUCT =>
      if ← Ty.isDirectIface tabs t then return true
      let fs ← Ty.fields tabs t
      if fs.size > 4 then return false
      for fd in fs do
        if !(← canSSA tabs ptrSize n fd.type) then return false
      return true
    | _ => return true

/-- `rewriteCondSelectIntoMath(config, op, constant)`. -/
def rewriteCondSelectIntoMath (arch : String) (op : Op) (c : Int) : Bool :=
  let pow2 (x : Int) : Bool :=
    let u := x.emod (2 ^ 64)
    u > 0 && (pat64 u &&& pat64 (u - 1)) == 0
  match arch with
  | "amd64" =>
    if c == 1 then true else
    match op with
    | .Add64 | .Add32 | .Add16 | .Add8 => c == 2 || c == 4 || c == 8
    | _ => false
  | "arm64" =>
    match op with
    | .Add64 | .Add32 | .Add16 | .Add8 => if c == 1 then false else pow2 c
    | .Sub64 | .Sub32 | .Sub16 | .Sub8 | .And64 | .And32 | .And16 | .And8
    | .Or64 | .Or32 | .Or16 | .Or8 | .Xor64 | .Xor32 | .Xor16 | .Xor8 => pow2 c
    | _ => c == 1
  | _ => c == 1

/-- The descriptor fields of `rttype.Type` the export records (`config rttype.*`). -/
def rtFields (cfg : Array (String × Sym.RtField)) : Array Sym.RtField :=
  (cfg.filter (·.1 != "PtrType.Elem")).map (·.2)

mutual

/-- Evaluate `e`. -/
partial def eval (sc : Scope) (e : Expr) : RwM GVal := do
  match e with
  | .lit _ c | .cnst _ _ c =>
    match c with
    | .int i => return .int i
    | .bool b => return .bool b
    | .float32 bits => return .f32 (Float32.ofBits (UInt32.ofNat bits))
    | .float64 bits => return .f64 (Float.ofBits (UInt64.ofNat bits))
    | .str s => return .str s.toUTF8
    | .nil => return .nil
  | .op o => return .op o
  | .var i =>
    match sc.binds[i]? with
    | some x => return x
    | none => throw s!"unbound rule variable {i}"
  | .rsv r =>
    match r with
    | .v => match sc.v with
      | some v => return .val v
      | none => throw "v in a block rule"
    | .b => return .blk sc.b
    | r => return .rsv r
  | .glob name _ =>
    match name with
    | "types.TypeMem" => return .typ (← typ "Mem")
    | "ir.Syms" => return .irSyms
    | "types.Types" => return .rsv .typ  -- only indexed, see `.index`
    | n => throw s!"unsupported global {n}"
  | .field x name _ => field (← eval sc x) name
  | .call fn args ty => call sc fn args ty
  | .method x name args _ => method sc (← eval sc x) name args
  | .builtin fn args _ =>
    match fn, args with
    | "len", [a] =>
      match ← eval sc a with
      | .str s => return .int s.size
      | .args v => return .int (← val v).args.size
      | _ => throw "len of an unsupported value"
    | "min", a :: rest => do
      let mut m ← lift (← eval sc a).asInt
      for r in rest do
        m := min m (← lift (← eval sc r).asInt)
      return .int m
    | f, _ => throw s!"unsupported builtin {f}"
  | .conv ty x => conv ty (← eval sc x)
  | .assert _ x =>
    -- `Sym.(*obj.LSym)`: the symbol itself; panics if it is not one
    let a ← lift (← eval sc x).asAux
    let _ ← lift (Sym.lsym (← tables) a)
    return .aux a
  | .unop o x ty => unop o ty (← eval sc x)
  | .binop .land x y _ =>
    if ← lift (← eval sc x).asBool then eval sc y else return .bool false
  | .binop .lor x y _ =>
    if ← lift (← eval sc x).asBool then return .bool true else eval sc y
  | .binop o x y ty => do
    let a ← eval sc x
    let b ← eval sc y
    -- comparisons carry `bool`; arithmetic is in the left operand's type
    let ty := match o with
      | .eq | .ne | .lt | .le | .gt | .ge => exprTy x
      | _ => ty
    binop o ty a b
  | .index x i _ =>
    match x with
    | .glob "types.Types" _ => typesIndex (← lift (← eval sc i).asInt)
    | _ =>
      match ← eval sc x with
      | .args v =>
        let k ← lift (← eval sc i).asInt
        match (← val v).args[k.toNat]? with
        | some a => if k < 0 then throw "index out of range" else return .val a
        | none => throw "index out of range"
      | _ => throw "unsupported index expression"
  | .deref _ _ => throw "unsupported dereference"

/-- `x.name(args)`. -/
partial def method (sc : Scope) (x : GVal) (name : String) (args : List Expr) : RwM GVal := do
  match x with
  | .typ t =>
    let tq {α} (q : Tables → Except String α) : RwM α := ty q
    match name, args with
    | "Size", [] => return .int (← tq (Ty.size · t))
    | "Alignment", [] => return .int (← tq (Ty.alignment · t))
    | "Elem", [] => return .typ (← tq (Ty.elem · t))
    | "PtrTo", [] => return .typ (← ptrTo t)
    | "NumElem", [] => return .int (← tq (Ty.numElem · t))
    | "FieldType", [i] => return .typ (← tq (Ty.fieldType · t (← lift (← eval sc i).asInt).toNat))
    | "FieldOff", [i] => return .int (← tq (Ty.fieldOff · t (← lift (← eval sc i).asInt).toNat))
    | "IsComplex", [] => return .bool (← tq (Ty.isComplex · t))
    | "IsPtrShaped", [] => return .bool (← tq (Ty.isPtrShaped · t))
    | "IsSigned", [] => return .bool (← tq (Ty.isSigned · t))
    | "IsInteger", [] => return .bool (← tq (Ty.isInteger · t))
    | "IsSlice", [] => return .bool (← tq (Ty.isKind .SLICE · t))
    | "IsInterface", [] => return .bool (← tq (Ty.isKind .INTER · t))
    | "IsString", [] => return .bool (← tq (Ty.isKind .STRING · t))
    | "IsArray", [] => return .bool (← tq (Ty.isKind .ARRAY · t))
    | "IsBoolean", [] => return .bool (← tq (Ty.isKind .BOOL · t))
    | "IsStruct", [] => return .bool (← tq (Ty.isKind .STRUCT · t))
    | "IsSIMD", [] => return .bool false
    | "Compare", [u] =>
      let u ← lift (← eval sc u).asTyp
      return .int (match (← read).typeOrder.compare t u with
        | .lt => -1 | .eq => 0 | .gt => 1)
    | n, _ => throw s!"unsupported method *types.Type.{n}"
  | .rsv .fe =>
    match name, args with
    | "Debug_checknil", [] => return .bool (← read).debugNil
    | "StringData", [s] => return .aux (some (← stringData (← lift (← eval sc s).asStr)))
    | n, _ => throw s!"unsupported method Frontend.{n}"
  | _ => throw s!"unsupported method {name}"

/-- A call of a package-level function. -/
partial def call (sc : Scope) (fn : String) (args : List Expr) (_ty : GoTy) : RwM GVal := do
  let ev (e : Expr) : RwM GVal := eval sc e
  let int (e : Expr) : RwM Int := do lift (← ev e).asInt
  let vl (e : Expr) : RwM ID := do lift (← ev e).asVal
  let tp (e : Expr) : RwM TypeRef := do lift (← ev e).asTyp
  let ax (e : Expr) : RwM (Option AuxRef) := do lift (← ev e).asAux
  let env ← read
  let f ← getF
  let tabs ← tables
  match fn, args with
  | "shiftIsBounded", [v] => return .bool ((f.getV (← vl v)).auxInt != 0)
  | "isSamePtr", [p, q] => return .bool (Ptr.isSamePtr f Ptr.fuel0 (← vl p) (← vl q))
  | "disjoint", [p1, n1, p2, n2] =>
    let p1 ← vl p1; let n1 ← int n1; let p2 ← vl p2; let n2 ← int n2
    return .bool (← lift (Ptr.disjoint f tabs env.ptrSize p1 n1 p2 n2))
  | "isStackPtr", [v] => return .bool (Ptr.isStackPtr f Ptr.fuel0 (← vl v))
  | "isVolatile", [v] => return .bool (Ptr.isVolatile f Ptr.fuel0 (← vl v))
  | "isNonNegative", [v] => return .bool (← lift (Ptr.isNonNegative f tabs Ptr.fuel0 (← vl v)))
  | "isConstZero", [v] => return .bool (Ptr.isConstZero f Ptr.fuel0 (← vl v))
  | "canRotate", [_, bits] =>
    let bits ← int bits
    if bits > env.ptrSize * 8 then return .bool false
    return .bool (match env.arch with
      | "386" | "amd64" | "arm64" | "loong64" | "riscv64" => true
      | "arm" | "s390x" | "ppc64" | "ppc64le" | "wasm" => bits ≥ 32
      | _ => false)
  | "hasSmallRotate", [_] => return .bool (env.arch == "amd64" || env.arch == "386")
  | "canLoadUnaligned", [_] => return .bool (env.archAlign == 1)
  | "isInlinableMemclr", [_, sz] =>
    let sz ← int sz
    if sz < 0 then return .bool false
    return .bool (match env.arch with
      | "amd64" | "arm64" => true
      | "ppc64le" | "ppc64" | "loong64" => sz < 512
      | _ => false)
  | "isInlinableMemmove", [dst, src, sz, _] =>
    let dst ← vl dst; let src ← vl src; let sz ← int sz
    let dj : Unit → RwM Bool := fun _ => lift (Ptr.disjoint f tabs env.ptrSize dst sz src sz)
    match env.arch with
    | "amd64" => return .bool (sz ≤ 16 || (sz < 1024 && (← dj ())))
    | "arm64" => return .bool (sz ≤ 64 || (sz ≤ 1024 && (← dj ())))
    | "loong64" => return .bool (sz ≤ 16 || (sz ≤ 64 && (← dj ())))
    | "386" => return .bool (sz ≤ 8)
    | "s390x" | "ppc64" | "ppc64le" => return .bool (sz ≤ 8 || (← dj ()))
    | "arm" | "mips" | "mips64" | "mipsle" | "mips64le" => return .bool (sz ≤ 4)
    | _ => return .bool false
  | "isSameCall", [a, n] =>
    let a ← ax a
    return .bool (← lift (Sym.isSameCall tabs a (← lift (← ev n).asStr)))
  | "isMalloc", [a] => return .bool (← lift (Sym.isMalloc tabs (← ax a)))
  | "isDictArgSym", [a] => return .bool (← lift (Sym.isDictArgSym tabs (← ax a)))
  | "symIsRO", [a] => return .bool (← lift (Sym.symIsRO tabs (← ax a)))
  | "symIsROZero", [a] => return .bool (← lift (Sym.symIsROZero tabs (← ax a)))
  | "read8", [a, off] =>
    let a ← ax a
    return .int (← lift (Sym.read8 tabs a (← int off)))
  | "read16", [a, off, _] =>
    let a ← ax a
    return .int (← lift (Sym.readN tabs a (← int off) 2 env.bigEndian))
  | "read32", [a, off, _] =>
    let a ← ax a
    return .int (← lift (Sym.readN tabs a (← int off) 4 env.bigEndian))
  | "read64", [a, off, _] =>
    let a ← ax a
    return .int (← lift (Sym.readN tabs a (← int off) 8 env.bigEndian))
  | "isFixedLoad", [v, a, off] =>
    let v ← vl v; let a ← ax a; let off ← int off
    let r ← lift (Sym.fixedLoad tabs (f.getV v).type a off (rtFields env.rtFields)
      env.rtElemOff)
    return .bool r.isSome
  | "rewriteFixedLoad", [v, a, sb, off] =>
    let v ← vl v; let a ← ax a; let sb ← vl sb; let off ← int off
    let r ← lift (Sym.fixedLoad tabs (f.getV v).type a off (rtFields env.rtFields)
      env.rtElemOff)
    let addrOf (s : AuxRef) : RwM GVal := do
      reset v .Addr
      modF fun f => f.modV v fun y => { y with aux := some s }
      addArg v sb
      return .val v
    let const (op : Op) (c : Int) : RwM GVal := do
      reset v op
      modF fun f => f.modV v fun y => { y with auxInt := Int64.ofInt c }
      return .val v
    -- `reflectdata.MarkTypeSymUsedInInterface(sym, curfn)`: a type or itab loaded from a
    -- dictionary, or the element type of a pointer type
    let useIface (s : AuxRef) : RwM Unit :=
      modify fun st => { st with effects := st.effects.push (.useIface s) }
    match r with
    | some (.addr name abi) =>
      let s ← symAux name (some abi) (plainSym name abi)
      let n := name.toStringLossy
      if n.startsWith "type:" || n.startsWith "go:itab" then useIface s
      addrOf s
    | some (.addrName name) => addrOf (← symAux name none (plainSym name))
    | some (.elem name) =>
      let s ← symAux name none (plainSym name)
      useIface s
      addrOf s
    | some (.constPtr c) => const (if env.ptrSize == 4 then .Const32 else .Const64) c
    | some (.const32 c) => const .Const32 c
    | some (.const8 c) => const .Const8 c
    | none => throw "fixedLoad data not known"
  | "copyCompatibleType", [t1, t2] =>
    let t1 ← tp t1; let t2 ← tp t2
    return .bool (← lift (Sym.copyCompatibleType tabs env.typeOrder.eq t1 t2))
  | "CanSSA", [t] => return .bool (← lift (canSSA tabs env.ptrSize 64 (← tp t)))
  | "registerizable", [_, t] =>
    let t ← tp t
    if (← lift (Ty.isPtrShaped tabs t)) || (← lift (Ty.isFloat tabs t)) ||
       (← lift (Ty.isKind .BOOL tabs t)) then return .bool true
    if ← lift (Ty.isInteger tabs t) then return .bool ((← lift (Ty.size tabs t)) ≤ env.regSize)
    return .bool false
  | "is64BitFloat", [t] => let t ← tp t; return .bool ((← lift (Ty.size tabs t)) == 8 && (← lift (Ty.isFloat tabs t)))
  | "is32BitFloat", [t] => let t ← tp t; return .bool ((← lift (Ty.size tabs t)) == 4 && (← lift (Ty.isFloat tabs t)))
  | "is64BitInt", [t] => let t ← tp t; return .bool ((← lift (Ty.size tabs t)) == 8 && (← lift (Ty.isInteger tabs t)))
  | "is32BitInt", [t] => let t ← tp t; return .bool ((← lift (Ty.size tabs t)) == 4 && (← lift (Ty.isInteger tabs t)))
  | "is16BitInt", [t] => let t ← tp t; return .bool ((← lift (Ty.size tabs t)) == 2 && (← lift (Ty.isInteger tabs t)))
  | "is8BitInt", [t] => let t ← tp t; return .bool ((← lift (Ty.size tabs t)) == 1 && (← lift (Ty.isInteger tabs t)))
  | "is32Bit", [n] => let n ← int n; return .bool (n == wrapInt 32 true n)
  | "isPowerOfTwo", [n] =>
    let nty := sc.tyOf n
    let (w, s) ← widthOf nty
    let x ← int n
    return .bool (x > 0 && wrapInt w s (andPred nty x) == 0)
  | "oneBit", [n] =>
    let nty := sc.tyOf n
    let (w, s) ← widthOf nty
    let x ← int n
    return .bool (wrapInt w s (andPred nty x) == 0 && x != 0)
  | "uaddOvf", [a, b] =>
    let a ← int a; let b ← int b
    let ua := a.emod (2 ^ 64); let ub := b.emod (2 ^ 64)
    return .bool ((ua + ub).emod (2 ^ 64) < ua)
  | "addToSub", [o] =>
    match ← ev o with
    | .op .Add64 => return .op .Sub64
    | .op .Add32 => return .op .Sub32
    | .op .Add16 => return .op .Sub16
    | .op .Add8 => return .op .Sub8
    | _ => throw "addToSub: unexpected op"
  | "rewriteCondSelectIntoMath", [_, o, c] =>
    let .op o ← ev o | throw "rewriteCondSelectIntoMath: expected an op"
    return .bool (rewriteCondSelectIntoMath env.arch o (← int c))
  | "modularMultiplicativeInverse", [x] =>
    return .int (← lift (Magic.modInverse ((← int x).emod (2 ^ 64)).toNat))
  | "bool2int", [x] => return .int (if ← lift (← ev x).asBool then 1 else 0)
  | "log8", [n] => return .int (bitsLen ((← int n).emod (2 ^ 8)).toNat - 1)
  | "log16", [n] => return .int (bitsLen ((← int n).emod (2 ^ 16)).toNat - 1)
  | "log32", [n] => return .int (bitsLen ((← int n).emod (2 ^ 32)).toNat - 1)
  | "log64", [n] => return .int (bitsLen ((← int n).emod (2 ^ 64)).toNat - 1)
  | "log8u", [n] | "log16u", [n] | "log32u", [n] | "log64u", [n] =>
    return .int (bitsLen (← int n).toNat - 1)
  | "ntz8", [x] => return .int (trailingZeros ((← int x).emod (2 ^ 8)).toNat 8)
  | "ntz16", [x] => return .int (trailingZeros ((← int x).emod (2 ^ 16)).toNat 16)
  | "ntz32", [x] => return .int (trailingZeros ((← int x).emod (2 ^ 32)).toNat 32)
  | "ntz64", [x] => return .int (trailingZeros ((← int x).emod (2 ^ 64)).toNat 64)
  | "nlz8", [x] => return .int (8 - bitsLen ((← int x).emod (2 ^ 8)).toNat)
  | "nlz16", [x] => return .int (16 - bitsLen ((← int x).emod (2 ^ 16)).toNat)
  | "nlz32", [x] => return .int (32 - bitsLen ((← int x).emod (2 ^ 32)).toNat)
  | "nlz64", [x] => return .int (64 - bitsLen ((← int x).emod (2 ^ 64)).toNat)
  | "bits.Len8", [x] | "bits.Len16", [x] | "bits.Len32", [x] | "bits.Len64", [x] =>
    return .int (bitsLen (← int x).toNat)
  | "bits.OnesCount8", [x] | "bits.OnesCount16", [x] | "bits.OnesCount32", [x]
  | "bits.OnesCount64", [x] => return .int (onesCount (← int x).toNat)
  | "bitsMulU64", [x, y] =>
    let p := (← int x).emod (2 ^ 64) * (← int y).emod (2 ^ 64)
    return .strct [("hi", .int (wrapInt 64 true (p / 2 ^ 64))), ("lo", .int (wrapInt 64 true p))]
  | "bitsMulU32", [x, y] =>
    let p := (← int x).emod (2 ^ 32) * (← int y).emod (2 ^ 32)
    return .strct [("hi", .int (wrapInt 32 true (p / 2 ^ 32))), ("lo", .int (wrapInt 32 true p))]
  | "bitsAdd64", [x, y, c] =>
    let s := (← int x).emod (2 ^ 64) + (← int y).emod (2 ^ 64) + (← int c).emod (2 ^ 64)
    return .strct [("sum", .int (wrapInt 64 true s)), ("carry", .int (s / 2 ^ 64))]
  | "math.IsNaN", [x] => return .bool (← lift (← ev x).asF64).isNaN
  | "math.Float64frombits", [x] => return .f64 (f64OfBits (← int x))
  | "math.Float32frombits", [x] => return .f32 (Float32.ofBits (UInt32.ofNat (← int x).toNat))
  | "math.Float64bits", [x] => return .int (← lift (← ev x).asF64).toBits.toNat
  | "math.Float32bits", [x] => return .int (f32Bits (← lift (← ev x).asF32))
  | "math.Sqrt", [x] => return .f64 (← lift (← ev x).asF64).sqrt
  | "math.Floor", [x] => return .f64 (← lift (← ev x).asF64).floor
  | "math.Ceil", [x] => return .f64 (← lift (← ev x).asF64).ceil
  | "math.Trunc", [x] => return .f64 (floatTrunc (← lift (← ev x).asF64))
  | "math.RoundToEven", [x] => return .f64 (floatRoundToEven (← lift (← ev x).asF64))
  | "reciprocalExact64", [x] =>
    let b := (← lift (← ev x).asF64).toBits.toNat
    let man := b % 2 ^ 52
    let ex := (b / 2 ^ 52) % 2 ^ 11
    return .bool (man == 0 && ex != 0 && ex != 0x7ff && ex != 0x7fe)
  | "reciprocalExact32", [x] =>
    let b := (← lift (← ev x).asF32).toBits.toNat
    let man := b % 2 ^ 23
    let ex := (b / 2 ^ 23) % 2 ^ 8
    return .bool (man == 0 && ex != 0 && ex != 0xff && ex != 0xfe)
  | "umagicOK8", [c] => return .bool (Magic.umagicOK 8 (← int c))
  | "umagicOK16", [c] => return .bool (Magic.umagicOK 16 (← int c))
  | "umagicOK32", [c] => return .bool (Magic.umagicOK 32 (← int c))
  | "umagicOK64", [c] => return .bool (Magic.umagicOK 64 (← int c))
  | "smagicOK8", [c] | "smagicOK16", [c] | "smagicOK32", [c] | "smagicOK64", [c]
  | "sdivisibleOK8", [c] | "sdivisibleOK16", [c] | "sdivisibleOK32", [c]
  | "sdivisibleOK64", [c] => return .bool (Magic.smagicOK (← int c))
  | "udivisibleOK8", [c] => return .bool (Magic.udivisibleOK 8 (← int c))
  | "udivisibleOK16", [c] => return .bool (Magic.udivisibleOK 16 (← int c))
  | "udivisibleOK32", [c] => return .bool (Magic.udivisibleOK 32 (← int c))
  | "udivisibleOK64", [c] => return .bool (Magic.udivisibleOK 64 (← int c))
  | "umagic8", [c] => return umagicVal (← lift (Magic.umagic 8 (← int c)))
  | "umagic16", [c] => return umagicVal (← lift (Magic.umagic 16 (← int c)))
  | "umagic32", [c] => return umagicVal (← lift (Magic.umagic 32 (← int c)))
  | "umagic64", [c] => return umagicVal (← lift (Magic.umagic 64 (← int c)))
  | "smagic8", [c] => return umagicVal (← lift (Magic.smagic 8 (← int c)))
  | "smagic16", [c] => return umagicVal (← lift (Magic.smagic 16 (← int c)))
  | "smagic32", [c] => return umagicVal (← lift (Magic.smagic 32 (← int c)))
  | "smagic64", [c] => return umagicVal (← lift (Magic.smagic 64 (← int c)))
  | "udivisible8", [c] => return udivisibleVal (← lift (Magic.udivisible 8 (← int c)))
  | "udivisible16", [c] => return udivisibleVal (← lift (Magic.udivisible 16 (← int c)))
  | "udivisible32", [c] => return udivisibleVal (← lift (Magic.udivisible 32 (← int c)))
  | "udivisible64", [c] => return udivisibleVal (← lift (Magic.udivisible 64 (← int c)))
  | "sdivisible8", [c] => return sdivisibleVal (← lift (Magic.sdivisible 8 (← int c)))
  | "sdivisible16", [c] => return sdivisibleVal (← lift (Magic.sdivisible 16 (← int c)))
  | "sdivisible32", [c] => return sdivisibleVal (← lift (Magic.sdivisible 32 (← int c)))
  | "sdivisible64", [c] => return sdivisibleVal (← lift (Magic.sdivisible 64 (← int c)))
  | "clobber", vs => do
    let mut ids : List ID := []
    for v in vs do ids := ids ++ [← vl v]
    return .bool (← Helpers.clobber ids)
  | "resetCopy", [v, a] => let v ← vl v; let a ← vl a; return .bool (← Helpers.resetCopy v a)
  | "warnRule", [c, _, _] => let _ ← ev c; return .bool true
  | "needRaceCleanup", [s, v] => let s ← ax s; let v ← vl v; return .bool (← Helpers.needRaceCleanup s v)
  | "rewriteStructStore", [v] => return .val (← Helpers.rewriteStructStore (← vl v))
  | "rewriteStructLoad", [v] => return .val (← Helpers.rewriteStructLoad (← vl v))
  | "imakeOfStructMake", [v] => return .val (← Helpers.imakeOfStructMake (← vl v))
  | "devirtLECall", [v, s] => let v ← vl v; let s ← ax s; return .val (← Helpers.devirtLECall v s)
  | "isDirectAndComparableType", [v] => return .bool (← isDirectAndComparableType 9 (← vl v) true)
  | "isDirectAndComparableIface", [v] => return .bool (← isDirectAndComparableIface 9 (← vl v) true)
  | f, _ => throw s!"unsupported helper {f}"

/-- `isDirectAndComparableType1` (`top = true`) / `…2` (`top = false`). -/
partial def isDirectAndComparableType (fuel : Nat) (v : ID) (top : Bool) : RwM Bool := do
  if fuel == 0 then return false
  let x ← val v
  let tabs ← tables
  if top then
    match x.op with
    | .ITab => isDirectAndComparableType (fuel - 1) x.args[0]! false
    | .Addr =>
      let s ← lift (Sym.lsym tabs x.aux)
      match s.typeInfo with
      | some t => return (← lift (Ty.isDirectIface tabs t)) && (← lift (Ty.isComparable tabs t))
      | none => return false
    | _ => return false
  else
    match x.op with
    | .IMake => isDirectAndComparableType (fuel - 1) x.args[0]! true
    | _ => return false

/-- `isDirectAndComparableIface1` (`top = true`, an itab) / `…2` (`top = false`, an interface),
with Go's depth bound. -/
partial def isDirectAndComparableIface (depth : Nat) (v : ID) (top : Bool) : RwM Bool := do
  if depth == 0 then return false
  let x ← val v
  let tabs ← tables
  if top then
    match x.op with
    | .ITab => isDirectAndComparableIface (depth - 1) x.args[0]! false
    | .Addr =>
      let s ← lift (Sym.lsym tabs x.aux)
      match s.itabInfo with
      | some t => return (← lift (Ty.isDirectIface tabs t)) && (← lift (Ty.isComparable tabs t))
      | none => return false
    | .ConstNil => return true
    | _ => return false
  else
    match x.op with
    | .IMake => isDirectAndComparableIface (depth - 1) x.args[0]! true
    | .Phi =>
      for a in x.args do
        if !(← isDirectAndComparableIface (depth - 1) a false) then return false
      return true
    | _ => return false

end

end Eval

end GoFV.Rules

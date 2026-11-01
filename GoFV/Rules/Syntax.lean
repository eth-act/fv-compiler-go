import GoFV.SSA.Op

/-!
# Rewrite rules as data

Datatypes of the generic rewrite rules exported by `tools/rules2lean` from the pinned Go
compiler's `_gen/{generic,dec,divisible,divmod}.rules` (data in `GoFV/Rules/Generated`).
`docs/contracts/rules.md` is the reference for the format and for the matching semantics an
interpreter must replicate (rule order, commutative expansion order, result construction and
value-ID allocation order).

Every Go expression of a rule (conditions, `[auxint]`/`{aux}`/`<type>` expressions, code
results) is exported type-checked: each node carries its Go type (`GoTy`), and constant
subexpressions are folded by `go/types` into `Expr.lit`/`Expr.cnst`.
-/

namespace GoFV.Rules

open GoFV.SSA

/-- Go type of an expression. Basic types are constructors; every other type is `named`
with its `go/types` spelling relative to package `ssa` (`"*Value"`, `"*types.Type"`, `"Sym"`,
`"*AuxCall"`, `"[37]*types.Type"`, ...). The untyped kinds occur only on constants that
`go/types` leaves untyped (constant shift counts). -/
inductive GoTy where
  | bool | int | int8 | int16 | int32 | int64
  | uint | uint8 | uint16 | uint32 | uint64 | uintptr
  | float32 | float64 | string
  | untypedInt | untypedBool | untypedFloat | untypedString | untypedNil
  | named (name : String)
  deriving DecidableEq, Repr, Inhabited

/-- Constant value. Integers are exact (already converted to the node's type by
`go/types`); floats are the IEEE bits of the value rounded to the node's type. -/
inductive Lit where
  | int (i : Int)
  | bool (b : Bool)
  | float32 (bits : Nat)
  | float64 (bits : Nat)
  | str (s : String)
  | nil
  deriving DecidableEq, Repr, Inhabited

/-- Names predeclared in every generated rewrite function: `v` (the value being rewritten;
absent in block rules), `b` (`v.Block`, or the block in block rules), `config`
(`b.Func.Config`), `fe` (`b.Func.fe`; absent in block rules), `typ` (`&b.Func.Config.Types`). -/
inductive Reserved where
  | v | b | config | fe | typ
  deriving DecidableEq, Repr, Inhabited

/-- Go unary operators: `-x`, `!x`, `^x`, `+x`. -/
inductive UnOp where
  | neg | not | com | plus
  deriving DecidableEq, Repr, Inhabited

/-- Go binary operators. `land`/`lor` short-circuit. Comparison results have type `bool`;
for the others the operand type is the type of the left operand (except shifts, whose right
operand has its own, possibly untyped, type). -/
inductive BinOp where
  | add | sub | mul | quo | rem | and | or | xor | shl | shr | andNot
  | land | lor | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr, Inhabited

/-- A type-checked Go expression of a rule. The last `GoTy` argument of a constructor is the
type of the node. -/
inductive Expr where
  /-- Constant (folded by `go/types`). -/
  | lit (ty : GoTy) (c : Lit)
  /-- Reference to a named constant of a named type (e.g. `types.TUINT64`), with its value. -/
  | cnst (name : String) (ty : GoTy) (c : Lit)
  /-- An `Op` constant (`OpConst64`). -/
  | op (o : Op)
  /-- Rule variable, index into `Rule.vars` / `BlockRule.vars`. -/
  | var (i : Nat)
  | rsv (r : Reserved)
  /-- Package-level variable, qualified unless in package `ssa` (`"types.Types"`). -/
  | glob (name : String) (ty : GoTy)
  /-- Field selection `x.f` (with Go's implicit pointer dereference). -/
  | field (x : Expr) (name : String) (ty : GoTy)
  /-- Call of a package-level function, qualified unless in package `ssa`
  (`"isPowerOfTwo"`, `"math.IsNaN"`, `"types.NewTuple"`). -/
  | call (fn : String) (args : List Expr) (ty : GoTy)
  /-- Method call `x.m(args)`. -/
  | method (x : Expr) (name : String) (args : List Expr) (ty : GoTy)
  /-- Builtin call (`len`, ...). -/
  | builtin (fn : String) (args : List Expr) (ty : GoTy)
  /-- Conversion `T(x)`. -/
  | conv (ty : GoTy) (x : Expr)
  /-- Type assertion `x.(T)` (panics if it fails). -/
  | assert (ty : GoTy) (x : Expr)
  | unop (o : UnOp) (x : Expr) (ty : GoTy)
  | binop (o : BinOp) (x y : Expr) (ty : GoTy)
  | index (x i : Expr) (ty : GoTy)
  | deref (x : Expr) (ty : GoTy)
  deriving Repr, Inhabited

mutual
/-- Structural equality of expressions (structural recursion, so the kernel evaluates it; the
derived `BEq` of a nested inductive does not reduce there). -/
def Expr.beq : Expr → Expr → Bool
  | .lit t c, .lit t' c' => t == t' && c == c'
  | .cnst n t c, .cnst n' t' c' => n == n' && t == t' && c == c'
  | .op o, .op o' => o == o'
  | .var i, .var i' => i == i'
  | .rsv r, .rsv r' => r == r'
  | .glob n t, .glob n' t' => n == n' && t == t'
  | .field x n t, .field x' n' t' => Expr.beq x x' && n == n' && t == t'
  | .call f as t, .call f' as' t' => f == f' && Expr.beqs as as' && t == t'
  | .method x n as t, .method x' n' as' t' =>
    Expr.beq x x' && n == n' && Expr.beqs as as' && t == t'
  | .builtin f as t, .builtin f' as' t' => f == f' && Expr.beqs as as' && t == t'
  | .conv t x, .conv t' x' => t == t' && Expr.beq x x'
  | .assert t x, .assert t' x' => t == t' && Expr.beq x x'
  | .unop o x t, .unop o' x' t' => o == o' && Expr.beq x x' && t == t'
  | .binop o x y t, .binop o' x' y' t' => o == o' && Expr.beq x x' && Expr.beq y y' && t == t'
  | .index x i t, .index x' i' t' => Expr.beq x x' && Expr.beq i i' && t == t'
  | .deref x t, .deref x' t' => Expr.beq x x' && t == t'
  | _, _ => false
/-- `Expr.beq` of two lists. -/
def Expr.beqs : List Expr → List Expr → Bool
  | [], [] => true
  | a :: as, b :: bs => Expr.beq a b && Expr.beqs as bs
  | _, _ => false
end

instance : BEq Expr := ⟨Expr.beq⟩

/-- What a rule variable is bound to: a `*Value`, a value's `Type`, or an op's AuxInt/Aux
converted by `auxIntTo<T>`/`auxTo<T>` (the variable's `GoTy` is the conversion's result). -/
inductive VarKind where
  | value | type | auxInt | aux
  deriving DecidableEq, Repr, Inhabited

structure Var where
  name : String
  kind : VarKind
  ty : GoTy
  deriving Repr, Inhabited

/-- A `<type>`, `[auxint]` or `{aux}` restriction of an op pattern. `bind x`: first
occurrence of an identifier, binds variable `x`; `eq e`: the field (converted as for `bind`)
must equal `e` (Go `==`; for types and values pointer identity). -/
inductive Field where
  | any
  | bind (x : Nat)
  | eq (e : Expr)
  deriving Repr, Inhabited

/-- Argument-count check of an op pattern. `fixed`: the op has a fixed `argLength`, no check.
`exact n`: variadic op, `len(Args) = n`. `atLeast n`: trailing `___`, `len(Args) ≥ n` (only
checked for variadic ops, and only when `n ≥ 1`). `ellipsis`: `(Op ...)` of an ellipsis rule. -/
inductive Arity where
  | fixed
  | exact (n : Nat)
  | atLeast (n : Nat)
  | ellipsis
  deriving DecidableEq, Repr, Inhabited

/-- Match pattern. `bind x`: binds variable `x` to the value; `same x`: the value must be
(pointer-)identical to variable `x`'s. `op o name ty auxInt aux arity args commute`: the value's
op is `o`; `name` binds the value itself (`x:(Op ...)`); `commute`: rulegen expands the first
two arguments of this commutative op in both orders (docs/contracts/rules.md). -/
inductive Pat where
  | wild
  | bind (x : Nat)
  | same (x : Nat)
  | op (o : Op) (name : Option Nat) (ty auxInt aux : Field) (arity : Arity) (args : List Pat)
      (commute : Bool)
  deriving Repr, Inhabited

/-- Argument of a result node: a rule variable or an earlier/later node of the same result
(index into the node list). -/
inductive RArg where
  | var (x : Nat)
  | node (j : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- A value built by a result. `ty = none` only for the top node of an in-place rewrite
without `<type>` (the value keeps its type). `auxInt`/`aux` are stored with
`<T>ToAuxInt`/`<T>ToAux` of the op's aux type. -/
structure RNode where
  op : Op
  ty : Option Expr
  auxInt : Option Expr
  aux : Option Expr
  args : List RArg
  deriving Repr, Inhabited

/-- Result of a value rule. `copy e`: `v.copyOf(e)` (a variable, `{code}` or a bare Go
expression). `build nodes`: nodes in allocation order (preorder of the result tree with
syntactically identical subtrees shared); node 0 is the top. `setOp o`: ellipsis rule,
`v.Op = o` and nothing else. -/
inductive Result where
  | copy (e : Expr)
  | build (nodes : List RNode)
  | setOp (o : Op)
  deriving Repr, Inhabited

/-- Source location: rule file (`"generic"`, `"dec"`, ...) and the line of the rule's `=>`
(rulegen's `Loc`). -/
structure Loc where
  file : String
  line : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A value rewrite rule of op `op`. `pat` is an `.op op ...` pattern. `block = some e`:
`@e` result placement (values are built in block `e` and `v` becomes a copy of the top node).
`pos`: pattern path (argument indices from the top) of the matched value whose `Pos` new
values get; `[]` is `v`. -/
structure Rule where
  loc : Loc
  op : Op
  vars : List Var
  pat : Pat
  cond : Option Expr
  block : Option Expr
  result : Result
  pos : List Nat
  deriving Repr, Inhabited

/-- Source position of a new block control value: the matched control `i`'s value at
pattern path `path` below it, or the block's position. -/
inductive CtrlPos where
  | control (i : Nat) (path : List Nat)
  | block
  deriving DecidableEq, Repr, Inhabited

/-- A new block control: an existing variable, or freshly built nodes (node 0 is the
control; no sharing between or within controls). -/
inductive NewControl where
  | var (x : Nat)
  | build (nodes : List RNode)
  deriving Repr, Inhabited

/-- A block rewrite rule. -/
structure BlockRule where
  loc : Loc
  kind : BlockKind
  vars : List Var
  controls : List Pat
  auxInt : Field
  aux : Field
  cond : Option Expr
  newKind : BlockKind
  newControls : List (NewControl × CtrlPos)
  newAuxInt : Option Expr
  newAux : Option Expr
  swapSuccs : Bool
  deriving Repr, Inhabited

/-- One rule file: value rules per op (ops sorted by Go name, as rulegen's `switch v.Op`) and
block rules per block kind, each list in matching order. `nilChecks`: rules on `NilCheck`
values tried after `values`' `NilCheck` row, which the checked rewrite validates per instance
as nil-check eliminations (issue #151; the proven-only sets only). -/
structure RuleSet where
  name : String
  values : List (Op × List Rule)
  blocks : List (BlockKind × List BlockRule)
  nilChecks : List Rule := []
  deriving Repr, Inhabited

namespace RuleSet

/-- The rules of `o`, in matching order. -/
def rulesOf (s : RuleSet) (o : Op) : List Rule :=
  match s.values.find? (·.1 == o) with
  | some (_, rs) => rs
  | none => []

/-- The block rules of `k`, in matching order. -/
def blockRulesOf (s : RuleSet) (k : BlockKind) : List BlockRule :=
  match s.blocks.find? (·.1 == k) with
  | some (_, rs) => rs
  | none => []

end RuleSet

end GoFV.Rules

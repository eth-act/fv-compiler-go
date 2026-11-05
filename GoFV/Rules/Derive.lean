import GoFV.Rules.Syntax

/-!
# Derived forms of `ARM64.rules` rules for the checked `lower` (issue #385)

Two rule shapes refer to an instance's fields the lowered obligation (`ArmRule.Sound`) cannot see,
so the proven rule set (`GoFV.Rules.ProvenARM64.lower`) lists them in a derived form that rewrites
exactly the same instances (the rewrite engine evaluates the same Go expressions on them):

* `flagSplit r`: a rule whose condition asks `flagArg(b) != nil` of a bound value `b`, and whose
  result reads `b.Op` and `flagArg(b)` (`(CondSelect x y boolval) && flagArg(boolval) != nil =>
  (CSEL [boolval.Op] x y flagArg(boolval))`, `ARM64.rules:302`), as one rule per condition op `cc`
  (`condOps`, the boolean ops of one flags argument, `CSET`): the leaf `b` becomes the named node
  `b:(cc f)` with a fresh variable `f`, `b.Op` the op `cc`, `flagArg(b)` the variable `f`, and
  the condition `flagArg(b) != nil` true. `flagArg(b)` is `b`'s argument if it is the only one
  and has flags type, which on a lowered boolean `b` is exactly `b = (cc f)`.
* `spLeaf r`: a rule whose pattern names an `SP` node (`(OffPtr [off] ptr:(SP)) && is32Bit(off) =>
  (MOVDaddr [int32(off)] ptr)`, `305`), with that node a leaf `ptr` and `ptr.Op == OpSP` added
  to the condition: `SP` is an atom of lowered SSA, which the validator matches only as a leaf.
-/

namespace GoFV.Rules.Derive

open GoFV.SSA

/-- The arm64 condition ops: a boolean of one flags argument (`CSET` of a condition). -/
def condOps : List Op :=
  [.ARM64Equal, .ARM64NotEqual, .ARM64LessThan, .ARM64LessEqual, .ARM64GreaterThan,
   .ARM64GreaterEqual, .ARM64LessThanU, .ARM64LessEqualU, .ARM64GreaterThanU,
   .ARM64GreaterEqualU, .ARM64LessThanF, .ARM64LessEqualF, .ARM64GreaterThanF,
   .ARM64GreaterEqualF, .ARM64NotLessThanF, .ARM64NotLessEqualF, .ARM64NotGreaterThanF,
   .ARM64NotGreaterEqualF, .ARM64LessThanNoov, .ARM64GreaterEqualNoov]

/-- `flagArg(var k)`. -/
def isFlagArg (k : Nat) : Expr → Bool
  | .call "flagArg" [.var x] _ => x == k
  | _ => false

mutual
/-- The variable `k` of the first `flagArg(var k)` in `e`. -/
def Expr.flagVar? : Expr → Option Nat
  | .call f as _ => if f == "flagArg" then
      match as with
      | [.var k] => some k
      | _ => Expr.flagVars? as
    else Expr.flagVars? as
  | .field x _ _ => Expr.flagVar? x
  | .method x _ as _ => (Expr.flagVar? x).orElse fun _ => Expr.flagVars? as
  | .builtin _ as _ => Expr.flagVars? as
  | .conv _ x => Expr.flagVar? x
  | .assert _ x => Expr.flagVar? x
  | .unop _ x _ => Expr.flagVar? x
  | .binop _ x y _ => (Expr.flagVar? x).orElse fun _ => Expr.flagVar? y
  | .index x i _ => (Expr.flagVar? x).orElse fun _ => Expr.flagVar? i
  | .deref x _ => Expr.flagVar? x
  | _ => none
/-- `Expr.flagVar?` of the first expression that has one. -/
def Expr.flagVars? : List Expr → Option Nat
  | [] => none
  | e :: es => (Expr.flagVar? e).orElse fun _ => Expr.flagVars? es
end

mutual
/-- `e` with `b.Op` the op `cc`, `flagArg(b)` the variable `f` and `flagArg(b) != nil` true
(`b` the variable `k`, `f` the variable `k'`). -/
def Expr.flagSub (k k' : Nat) (cc : Op) : Expr → Expr
  | .field x n t =>
    if x == .var k && n == "Op" then .op cc else .field (Expr.flagSub k k' cc x) n t
  | .call fn as t =>
    if fn == "flagArg" && as == [.var k] then .var k' else .call fn (Expr.flagSubs k k' cc as) t
  | .method x n as t => .method (Expr.flagSub k k' cc x) n (Expr.flagSubs k k' cc as) t
  | .builtin fn as t => .builtin fn (Expr.flagSubs k k' cc as) t
  | .conv t x => .conv t (Expr.flagSub k k' cc x)
  | .assert t x => .assert t (Expr.flagSub k k' cc x)
  | .unop o x t => .unop o (Expr.flagSub k k' cc x) t
  | .binop o x y t =>
    if o == .ne && isFlagArg k x && (y matches .lit _ .nil) then .lit .bool (.bool true)
    else .binop o (Expr.flagSub k k' cc x) (Expr.flagSub k k' cc y) t
  | .index x i t => .index (Expr.flagSub k k' cc x) (Expr.flagSub k k' cc i) t
  | .deref x t => .deref (Expr.flagSub k k' cc x) t
  | e => e
/-- `Expr.flagSub` of each expression. -/
def Expr.flagSubs (k k' : Nat) (cc : Op) : List Expr → List Expr
  | [] => []
  | e :: es => Expr.flagSub k k' cc e :: Expr.flagSubs k k' cc es
end

mutual
/-- The pattern with the leaf `k` the node `k:(cc k')`. -/
def Pat.flagAt (k k' : Nat) (cc : Op) : Pat → Pat
  | .bind x => if x == k then .op cc (some k) .any .any .any .fixed [.bind k'] false else .bind x
  | .op o n ty ai ax ar args c => .op o n ty ai ax ar (Pat.flagAts k k' cc args) c
  | p => p
/-- `Pat.flagAt` of each pattern. -/
def Pat.flagAts (k k' : Nat) (cc : Op) : List Pat → List Pat
  | [] => []
  | p :: ps => Pat.flagAt k k' cc p :: Pat.flagAts k k' cc ps
end

/-- A result argument with `flagArg(b)` the variable `f` (`Expr.flagSub`). -/
def RArg.flagSub (k k' : Nat) (cc : Op) : RArg → RArg
  | .expr e => if isFlagArg k e then .var k' else .expr (Expr.flagSub k k' cc e)
  | a => a

/-- A result node with `Expr.flagSub` and `RArg.flagSub`. -/
def RNode.flagSub (k k' : Nat) (cc : Op) (n : RNode) : RNode where
  op := n.op
  ty := n.ty.map (Expr.flagSub k k' cc)
  auxInt := n.auxInt.map (Expr.flagSub k k' cc)
  aux := n.aux.map (Expr.flagSub k k' cc)
  args := n.args.map (RArg.flagSub k k' cc)

/-- A condition that became `true` is none. -/
def condTrim : Option Expr → Option Expr
  | some (.lit _ (.bool true)) => none
  | c => c

/-- The form of `r` on the condition op `cc`, `b` the variable `k` (module doc). -/
def flagAt (r : Rule) (k : Nat) (cc : Op) : Rule :=
  let k' := r.vars.length
  { loc := r.loc
    op := r.op
    vars := r.vars ++ [⟨"flagArg", .value, .named "*Value"⟩]
    pat := Pat.flagAt k k' cc r.pat
    cond := condTrim (r.cond.map (Expr.flagSub k k' cc))
    block := r.block
    result := match r.result with
      | .copy e => .copy (Expr.flagSub k k' cc e)
      | .build ns => .build (ns.map (RNode.flagSub k k' cc))
      | res => res
    pos := r.pos }

/-- `r` as one rule per condition op if its condition asks `flagArg(b) != nil`, else itself
(module doc). -/
def flagSplit (r : Rule) : List Rule :=
  match r.cond.bind Expr.flagVar? with
  | some k => condOps.map (flagAt r k)
  | none => [r]

mutual
/-- The name of the first named `SP` node of the pattern. -/
def Pat.spVar? : Pat → Option Nat
  | .op .SP (some k) .any .any .any .fixed [] _ => some k
  | .op _ _ _ _ _ _ args _ => Pat.spVars? args
  | _ => none
/-- `Pat.spVar?` of the first pattern that has one. -/
def Pat.spVars? : List Pat → Option Nat
  | [] => none
  | p :: ps => (Pat.spVar? p).orElse fun _ => Pat.spVars? ps
end

mutual
/-- The pattern with the named `SP` node `k` a leaf. -/
def Pat.spAt (k : Nat) : Pat → Pat
  | .op o n ty ai ax ar args c =>
    if o == .SP && n == some k then .bind k else .op o n ty ai ax ar (Pat.spAts k args) c
  | p => p
/-- `Pat.spAt` of each pattern. -/
def Pat.spAts (k : Nat) : List Pat → List Pat
  | [] => []
  | p :: ps => Pat.spAt k p :: Pat.spAts k ps
end

/-- `k.Op == OpSP`. -/
def spCond (k : Nat) : Expr :=
  .binop .eq (.field (.var k) "Op" (.named "Op")) (.op .SP) .bool

/-- `r` with its named `SP` node a leaf checked by the condition (module doc). -/
def spLeaf (r : Rule) : Rule :=
  match Pat.spVar? r.pat with
  | some k =>
    { r with
      pat := Pat.spAt k r.pat
      cond := some (match r.cond with
        | some c => .binop .land (spCond k) c .bool
        | none => spCond k) }
  | none => r

end GoFV.Rules.Derive

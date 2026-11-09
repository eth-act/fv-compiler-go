import GoFV.Rules.Syntax
import GoFV.Rules.Helpers.ARM64
import GoFV.Rules.Generated.ARM64.Values09

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
* `ccSplit r`: a rule whose top node binds a `CCop` auxint `cc` and whose result reads
  `arm64Invert(cc)` (`(CSEL [cc] x y (InvertFlags cmp)) => (CSEL [arm64Invert(cc)] x y cmp)`,
  `1352`), as one rule per integer condition op `X` (`intCondOps`): the condition `cc == X` added,
  `arm64Invert(cc)` the op `arm64Invert(X)`. It rewrites the instances whose `cc` is an integer
  condition; on a float condition the swap does not hold under the flags semantics
  (`docs/proofs/rules.md` "Findings"). A result reading `arm64Negate(cc)` (`(CSEL [cc]
  (MOVDconst [0]) y flag) => (CSEL0 [arm64Negate(cc)] y flag)`, `1189`) is split alike over the
  condition ops `arm64Negate` maps (`negCondOps`, the integer and float ones), `arm64Negate(cc)`
  the op `arm64Negate(X)`: a negated condition holds exactly when the condition does not, float
  conditions included.

One more is no form of the same instances but rules `lower` never fires:

* `lshSplit r`: the rename `(Lsh32x<a> ...) => (Lsh64x<a> ...)` of a narrow left shift
  (`148`-`150`), which is false (`Lsh64x<a>` asks for a 64-bit operand), followed by the rules of
  `Lsh64x<a>` (`152`, `169`-`171`) with the narrow shift as their top op (`lshDerive`). `lower`
  always fires the rename first, then a rule of `Lsh64x<a>` at the same value; the validator
  replays the rename as no change and that rule as its derived form, which holds on the narrow
  shift (`GoFV.Opt.LowerCheck.lshRule`, `docs/proofs/rules.md`).
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

/-- The variable `k` of a conjunct `flagArg(var k) != nil` of a condition (through `&&`). A rule
asking `flagArg(b) == nil` (`ARM64.rules:303`) is not split: its result reads no field of `b`,
and it rewrites the booleans that are not a condition op. -/
def Expr.flagNe? : Expr → Option Nat
  | .binop .ne (.call "flagArg" [.var k] _) (.lit _ .nil) _ => some k
  | .binop .land x y _ => (Expr.flagNe? x).orElse fun _ => Expr.flagNe? y
  | _ => none

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
  match r.cond.bind Expr.flagNe? with
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

/-- The integer condition ops (`EQ` … `UGE`), which `arm64Invert` swaps among themselves. -/
def intCondOps : List Op :=
  [.ARM64Equal, .ARM64NotEqual, .ARM64LessThan, .ARM64LessEqual, .ARM64GreaterThan,
   .ARM64GreaterEqual, .ARM64LessThanU, .ARM64LessEqualU, .ARM64GreaterThanU,
   .ARM64GreaterEqualU]

/-- `k == cc`. -/
def ccCond (k : Nat) (cc : Op) : Expr := .binop .eq (.var k) (.op cc) .bool

/-- The condition ops `arm64Negate` maps: the integer ones and the eight float ones. -/
def negCondOps : List Op :=
  intCondOps ++ [.ARM64LessThanF, .ARM64LessEqualF, .ARM64GreaterThanF, .ARM64GreaterEqualF,
    .ARM64NotLessThanF, .ARM64NotLessEqualF, .ARM64NotGreaterThanF, .ARM64NotGreaterEqualF]

/-- `arm64Invert(var k)` / `arm64Negate(var k)` as the op it gives on `cc`; any other expression
unchanged. -/
def ccInvert (k : Nat) (cc : Op) : Expr → Expr
  | e@(.call fn [.var x] _) =>
    if x == k && (fn == "arm64Invert" || fn == "arm64Negate") then
      match (if fn == "arm64Invert" then Arm64.arm64Invert cc else Arm64.arm64Negate cc) with
      | .ok o => .op o
      | .error _ => e
    else e
  | e => e

/-- Some result node's auxint is `arm64Negate(…)`. -/
def negates (r : Rule) : Bool :=
  match r.result with
  | .build ns => ns.any fun n => match n.auxInt with
    | some (.call "arm64Negate" _ _) => true
    | _ => false
  | _ => false

/-- The form of `r` on the condition op `cc` of its `CCop` auxint variable `k` (module doc). -/
def ccAt (r : Rule) (k : Nat) (cc : Op) : Rule :=
  { r with
    cond := some (match r.cond with
      | some c => .binop .land (ccCond k cc) c .bool
      | none => ccCond k cc)
    result := match r.result with
      | .build ns => .build (ns.map fun n => { n with auxInt := n.auxInt.map (ccInvert k cc) })
      | res => res }

/-- `r` as one rule per condition op (`negCondOps` if it negates its condition, else
`intCondOps`) if its top node binds an auxint of Go type `Op`, else itself (module doc). -/
def ccSplit (r : Rule) : List Rule :=
  match r.pat with
  | .op _ _ _ (.bind k) _ _ _ _ =>
    if (r.vars[k]?.map (·.ty)) == some (.named "Op") then
      (if negates r then negCondOps else intCondOps).map (ccAt r k)
    else [r]
  | _ => [r]

/-- The value and amount widths of a left shift `Lsh{w}x{a}`. -/
def lshShape : Op → Option (Nat × Nat)
  | .Lsh8x8 => some (8, 8) | .Lsh8x16 => some (8, 16) | .Lsh8x32 => some (8, 32)
  | .Lsh8x64 => some (8, 64) | .Lsh16x8 => some (16, 8) | .Lsh16x16 => some (16, 16)
  | .Lsh16x32 => some (16, 32) | .Lsh16x64 => some (16, 64) | .Lsh32x8 => some (32, 8)
  | .Lsh32x16 => some (32, 16) | .Lsh32x32 => some (32, 32) | .Lsh32x64 => some (32, 64)
  | .Lsh64x8 => some (64, 8) | .Lsh64x16 => some (64, 16) | .Lsh64x32 => some (64, 32)
  | .Lsh64x64 => some (64, 64)
  | _ => none

/-- The left shift of a `w`-bit value by an `a`-bit amount (`lshShape`'s inverse). -/
def lshOp : Nat × Nat → Option Op
  | (8, 8) => some .Lsh8x8 | (8, 16) => some .Lsh8x16 | (8, 32) => some .Lsh8x32
  | (8, 64) => some .Lsh8x64 | (16, 8) => some .Lsh16x8 | (16, 16) => some .Lsh16x16
  | (16, 32) => some .Lsh16x32 | (16, 64) => some .Lsh16x64 | (32, 8) => some .Lsh32x8
  | (32, 16) => some .Lsh32x16 | (32, 32) => some .Lsh32x32 | (32, 64) => some .Lsh32x64
  | (64, 8) => some .Lsh64x8 | (64, 16) => some .Lsh64x16 | (64, 32) => some .Lsh64x32
  | (64, 64) => some .Lsh64x64
  | _ => none

/-- The 64-bit left shift `Lsh64x<a>` that `lower` renames the narrow `Lsh{8,16,32}x<a>` to
(`(Lsh32x<a> ...) => (Lsh64x<a> ...)`, `ARM64.rules:148-150`). -/
def lshWide (o : Op) : Option Op :=
  match lshShape o with
  | some (w, a) => if w < 64 then lshOp (64, a) else none
  | none => none

/-- A built `Lsh64x<b>` as the narrow left shift of `o`'s value width by `b` (`o` narrow); any
other op as it is. -/
def lshAt (o o' : Op) : Op :=
  match lshShape o, lshShape o' with
  | some (w, _), some (64, b) => if w < 64 then (lshOp (w, b)).getD o' else o'
  | _, _ => o'

/-- Rule `r` of `Lsh64x<a>` in its form on the narrow `o` renamed to it: the pattern's top op
`o`, and a built `Lsh64x<b>` (`(Lsh64x16 [b] x y) && !shiftIsBounded(v) => (Lsh64x32 [b] x
(ZeroExt16to32 y))`, `171`) the narrow `lshAt o`. -/
def lshDerive (o : Op) (r : Rule) : Rule :=
  { r with
    op := o
    pat := match r.pat with
      | .op _ n ty ai ax ar args c => .op o n ty ai ax ar args c
      | p => p
    result := match r.result with
      | .build ns => .build (ns.map fun n => { n with op := lshAt o n.op })
      | res => res }

/-- The rules of `Lsh64x<a>` in matching order (`ARM64.rules:152`, `169-171`). -/
def lshRow : Op → List Rule
  | .Lsh64x8 => Generated.ARM64.ops_Lsh64x8
  | .Lsh64x16 => Generated.ARM64.ops_Lsh64x16
  | .Lsh64x32 => Generated.ARM64.ops_Lsh64x32
  | .Lsh64x64 => Generated.ARM64.ops_Lsh64x64
  | _ => []

/-- A narrow left shift's rename `(Lsh32x<a> ...) => (Lsh64x<a> ...)` followed by the rules of
`Lsh64x<a>` in their form on the narrow shift (`lshDerive`), else `r` itself. `lower` always fires
the rename first; the derived rules are what the validator checks the later events at the renamed
value against (`GoFV.Opt.LowerCheck.lshRule`). -/
def lshSplit (r : Rule) : List Rule :=
  match r.pat, r.result with
  | .op o .., .setOp o' => if lshWide o == some o' then r :: (lshRow o').map (lshDerive o) else [r]
  | _, _ => [r]

end GoFV.Rules.Derive

import GoFV.Rules.Generated

/-!
Checks of the generated rule data (`GoFV/Rules/Generated`, docs/contracts/rules.md):
counts against the pinned compiler's generated `rewrite*.go`, and well-formedness of every
rule against the op table (`GoFV.SSA.Op`).
-/

namespace GoFVTest.Rules.Data

open GoFV.SSA GoFV.Rules GoFV.Rules.Generated

-- Rule counts after `|` expansion; `rewritegeneric.go` has 241 value rewrite functions with
-- 1651 `// match:` comments plus 3 in `rewriteBlockgeneric`.
example : Generic.counts = (1651, 3) := rfl
example : Dec.counts = (47, 0) := rfl
example : Divisible.counts = (32, 0) := rfl
example : Divmod.counts = (29, 0) := rfl
-- `rewriteARM64.go` (SIMD ops left out): 1097 value rules in functions + 171 ellipsis rules
-- (dispatch-switch cases `v.Op = OpARM64…`) + 222 block rules; `rewriteARM64latelower.go`: 82.
example : ARM64.counts = (1268, 222) := rfl
example : ARM64latelower.counts = (82, 0) := rfl

#guard Generic.ruleSet.values.length == 241
#guard (Generic.ruleSet.rulesOf .Add64).length == 23
#guard (Generic.ruleSet.rulesOf .Store).length == 21
#guard (Generic.ruleSet.blockRulesOf .If).length == 3
#guard ARM64.ruleSet.values.length == 506 && ARM64.ruleSet.blocks.length == 26
#guard match ARM64.ruleSet.rulesOf .Add64 with
  | [r] => match r.result with | .setOp .ARM64ADD => true | _ => false
  | _ => false

def ruleSets : List RuleSet :=
  [Generic.ruleSet, Dec.ruleSet, Divisible.ruleSet, Divmod.ruleSet, ARM64.ruleSet,
    ARM64latelower.ruleSet]

/-- Variable indices of an expression are in range. -/
partial def exprOk (nv : Nat) : Expr → Bool
  | .var i => i < nv
  | .field x _ _ | .conv _ x | .assert _ x | .unop _ x _ | .deref x _ => exprOk nv x
  | .binop _ x y _ | .index x y _ => exprOk nv x && exprOk nv y
  | .call _ as _ | .builtin _ as _ => as.all (exprOk nv)
  | .method x _ as _ => exprOk nv x && as.all (exprOk nv)
  | .lit .. | .cnst .. | .op _ | .rsv _ | .glob .. => true

def fieldOk (nv : Nat) : Field → Bool
  | .any => true
  | .bind x => x < nv
  | .eq e => exprOk nv e

/-- Variable indices in range; argument counts agree with the op's `argLen`; `commute` only on
commutative ops with two pattern arguments. -/
partial def patOk (nv : Nat) : Pat → Bool
  | .wild => true
  | .bind x | .same x => x < nv
  | .op o name ty ai ax arity args commute =>
    name.all (· < nv) && fieldOk nv ty && fieldOk nv ai && fieldOk nv ax &&
    (!commute || (o.commutative && args.length ≥ 2)) &&
    (match arity with
      | .fixed => o.argLen == (args.length : Int)
      | .exact n => o.argLen == -1 && n == args.length
      | .atLeast n => n == args.length
      | .ellipsis => args.isEmpty) &&
    args.all (patOk nv)

def nodesOk (nv : Nat) (ns : List RNode) : Bool :=
  ns.all fun n =>
    n.ty.all (exprOk nv) && n.auxInt.all (exprOk nv) && n.aux.all (exprOk nv) &&
    (n.op.argLen == -1 || n.op.argLen == (n.args.length : Int)) &&
    n.args.all fun
      | .var x => x < nv
      | .node j => j < ns.length
      | .expr e => exprOk nv e

def ruleOk (o : Op) (r : Rule) : Bool :=
  let nv := r.vars.length
  r.op == o && patOk nv r.pat &&
  (match r.pat with | .op o' .. => o' == o | _ => false) &&
  r.cond.all (exprOk nv) && r.block.all (exprOk nv) &&
  match r.result with
  | .copy e => exprOk nv e
  | .build ns => !ns.isEmpty && nodesOk nv ns
  | .setOp o' => o'.argLen == o.argLen || o'.argLen == -1

def blockRuleOk (k : BlockKind) (r : BlockRule) : Bool :=
  let nv := r.vars.length
  r.kind == k && r.controls.length == k.controls && r.newControls.length == r.newKind.controls &&
  r.controls.all (patOk nv) && fieldOk nv r.auxInt && fieldOk nv r.aux &&
  r.cond.all (exprOk nv) &&
  r.newControls.all fun
    | (.var x, _) => x < nv
    | (.build ns, _) => !ns.isEmpty && nodesOk nv ns

#guard ruleSets.all fun s =>
  s.values.all (fun (o, rs) => !rs.isEmpty && rs.all (ruleOk o)) &&
  s.blocks.all (fun (k, rs) => !rs.isEmpty && rs.all (blockRuleOk k))

/-- The pattern path exists below the pattern and passes no commutative node: the interpreter
finds the value at `Rule.pos` by the same argument indices under every commutative choice. -/
def posPathOk : Pat → List Nat → Bool
  | _, [] => true
  | .op _ _ _ _ _ _ args commute, i :: is =>
    !commute && match args[i]? with
      | some a => posPathOk a is
      | none => false
  | _, _ :: _ => false

#guard ruleSets.all fun s => s.values.all fun (_, rs) => rs.all fun r => posPathOk r.pat r.pos

end GoFVTest.Rules.Data

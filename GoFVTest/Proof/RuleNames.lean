import GoFV.Rules.Generated
import GoFV.Proof.Rules.Names

/-!
`GoFV.Proof.Rules.helperNames` and `typNames` (the names with a `rule_helper` lemma) are
exactly the function names the exported rules call and the `typ.<name>` fields they read.
-/

open GoFV.Rules

namespace GoFVTest.RuleNames

mutual
/-- Called function names, and `typ.<name>` fields as `"typ.<name>"`. -/
def exprCalls : Expr → List String
  | .call fn args _ => fn :: exprsCalls args
  | .field (.rsv .typ) n _ => ["typ." ++ n]
  | .field x _ _ | .conv _ x | .assert _ x | .unop _ x _ | .deref x _ => exprCalls x
  | .method x _ args _ => exprCalls x ++ exprsCalls args
  | .builtin _ args _ => exprsCalls args
  | .binop _ x y _ | .index x y _ => exprCalls x ++ exprCalls y
  | _ => []
def exprsCalls : List Expr → List String
  | [] => []
  | e :: es => exprCalls e ++ exprsCalls es
end

def fieldCalls : Field → List String
  | .eq e => exprCalls e
  | _ => []

mutual
def patCalls : Pat → List String
  | .op _ _ ty ai ax _ args _ => fieldCalls ty ++ fieldCalls ai ++ fieldCalls ax ++ patsCalls args
  | _ => []
def patsCalls : List Pat → List String
  | [] => []
  | p :: ps => patCalls p ++ patsCalls ps
end

def optCalls : Option Expr → List String
  | some e => exprCalls e
  | none => []

def nodeCalls (n : RNode) : List String := optCalls n.ty ++ optCalls n.auxInt ++ optCalls n.aux

def ruleCalls (r : Rule) : List String :=
  patCalls r.pat ++ optCalls r.cond ++ optCalls r.block ++
  match r.result with
  | .copy e => exprCalls e
  | .build ns => ns.flatMap nodeCalls
  | .setOp _ => []

def blockCalls (r : BlockRule) : List String :=
  patsCalls r.controls ++ fieldCalls r.auxInt ++ fieldCalls r.aux ++ optCalls r.cond ++
  optCalls r.newAuxInt ++ optCalls r.newAux ++
  r.newControls.flatMap fun (c, _) => match c with
    | .build ns => ns.flatMap nodeCalls
    | .var _ => []

def allCalls : List String :=
  let sets := [Generated.Generic.ruleSet, Generated.Dec.ruleSet, Generated.Divisible.ruleSet,
    Generated.Divmod.ruleSet]
  (sets.flatMap fun s => s.values.flatMap (·.2.flatMap ruleCalls) ++
    s.blocks.flatMap (·.2.flatMap blockCalls)).eraseDups

def known : List String :=
  GoFV.Proof.Rules.helperNames ++ GoFV.Proof.Rules.typNames.map ("typ." ++ ·)

#guard allCalls.all known.contains
#guard known.all allCalls.contains

end GoFVTest.RuleNames

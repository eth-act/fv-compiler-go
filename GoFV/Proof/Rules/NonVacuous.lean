import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values00

/-!
# Non-vacuity of `Rule.Sound` (`docs/proofs/rules.md`, "Non-vacuity")

`Rule.Sound` is one definition for all rules, so its non-vacuity is shown once and per op
family rather than per lemma:

* `Rule.Inst r e or`: `e`, `or` instantiate `r` so that every hypothesis of `Rule.Sound r`
  holds and the matched value is not `poison`; on such an instance `Rule.Sound r` asserts a
  non-trivial equation (`Rule.Sound.refines`), and an instance whose result does not refine
  the matched value refutes it (`Rule.not_sound`).
* `mut646_not_sound`: a mutated rule (`(Add16 (Const16 [1]) x) => x`) is not sound.
* `inst_*`: instances of representative proven rules of each op family.
* `lake exe rule-sat` (`GoFVTest/Proof/RuleSat.lean`, `scripts/rule-proofs.py sat`) finds an
  instance for every proven rule at run time.
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

/-- `e`, `or` instantiate `r`: every hypothesis of `Rule.Sound r` holds and the matched value
is not `poison`. -/
def Rule.Inst (r : Rule) (e : PEnv) (or : Oracle) : Prop :=
  Pat.wf e [] r.pat ∧
  Pat.cons (evalE (r.vars.map (·.ty)) (sigma e r.pat) or e (Pat.den e [] r.pat)) (sigma e r.pat)
    e [] r.pat ∧
  condHolds (evalE (r.vars.map (·.ty)) (sigma e r.pat) or e (Pat.den e [] r.pat)) r.cond ∧
  (Pat.raw e r.pat).hasTy (e.ty []) = true ∧
  Pat.raw e r.pat ≠ .poison

/-- The result value of `r` at an instance. -/
noncomputable def Rule.res (r : Rule) (e : PEnv) (or : Oracle) : Val :=
  resDen (evalE (r.vars.map (·.ty)) (sigma e r.pat) or e (Pat.den e [] r.pat)) or
    (sigma e r.pat) (e.ty []) r.result

/-- On an instance, `Rule.Sound r` says that the result equals the (non-poison) matched
value. -/
theorem Rule.Sound.refines {r : Rule} (h : Rule.Sound r) {e : PEnv} {or : Oracle}
    (hi : Rule.Inst r e or) : Refines (Pat.raw e r.pat) (Rule.res r e or) :=
  h.2 e or hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1

/-- An instance on which the result does not refine the matched value refutes `Rule.Sound`. -/
theorem Rule.not_sound {r : Rule} {e : PEnv} {or : Oracle} (hi : Rule.Inst r e or)
    (hn : ¬ Refines (Pat.raw e r.pat) (Rule.res r e or)) : ¬ Rule.Sound r :=
  fun h => hn (h.refines hi)

/-- The entry of `p` in a table, else `d`. -/
noncomputable def tbl {α : Type} (l : List (Path × α)) (d : α) (p : Path) : α :=
  match l with
  | [] => d
  | (q, a) :: l => if p = q then a else tbl l d p

/-- An instance from finite tables (missing entries: `poison`, `dflt`, `0`, no aux). -/
noncomputable def PEnv.ofLists (leaf : List (Path × Val)) (ty : List (Path × Ty)) (dflt : Ty)
    (auxInt : List (Path × Int64)) : PEnv where
  leaf := tbl leaf .poison
  ty := tbl ty dflt
  auxInt := tbl auxInt 0
  aux _ := none

/-- The oracle answering `b` for every unmodelled boolean atom. -/
noncomputable def Oracle.const (b : Bool) : Oracle where
  dv _ := .bool b
  ty _ := .other
  auxInt _ := 0
  aux _ := none
  val _ := .poison

/-- Evaluate `Rule.Inst`/`Rule.res` on a concrete rule and instance. -/
macro "rule_eval" : tactic => `(tactic| (
  simp (config := { decide := true }) only [Rule.Inst, Rule.res, PEnv.ofLists, Oracle.const,
    Pat.den, Pat.dens, Pat.raw, sigma, Pat.binds, Pat.bindss, Pat.cons, Pat.conss, Pat.wf,
    Pat.wfs, auxIntOk, Field.bindDV, condHolds, resDen, nodeDen, List.length,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.map, reduceEvalPure, reduceAuxType,
    evalE, evalEs, auxIntDV, List.lookup, toAuxIntD, Option.getD, List.cons_append,
    List.nil_append, intBin, binDV, binE, GoFV.Rules.wrapTo, reduceIntInfo, litDV,
    fieldE, indexE, convE, callE, callH, methodE, builtinE, unDV, fieldDV, DV.valOr, typesShape,
    shapeSize, Option.map, exprTy, List.getD, rule_helper, rule_sem, Option.getD_some,
    Option.getD_none, reduceCtorEq, ne_eq, not_false_eq_true, and_true, true_and, and_self,
    beq_self_eq_true, Bool.and_true, Bool.true_and, Bool.or_true, Bool.true_or,
    Bool.cond_true, Bool.cond_false, Option.elim_none, Option.elim_some, Val.hasTy,
    refines_int_int, decide_eq_true_eq, BitVec.reduceAdd, BitVec.reduceShiftLeft,
    BitVec.reduceUShiftRight, BitVec.ofInt_ofNat, GoFV.Rules.wrapInt, Int64.reduceToInt,
    Int.reduceBmod, Int.reduceMod, Nat.reducePow, Nat.reduceAdd, tbl, reduceIte, ite_true,
    ite_false, List.cons.injEq, Nat.reduceBEq, Nat.reduceBNe, List.zip_cons_cons, List.zip_nil_left,
    List.zip_nil_right, BitVec.reduceToNat, BitVec.reduceShiftLeftShiftLeft,
    bne_self_eq_false, Bool.or_false, Bool.false_or]))

/-! ## A mutated rule is not sound -/

/-- `generic.rules:646` with the constant changed: `(Add16 (Const16 [1]) x) => x`. -/
noncomputable def mut646 : Rule :=
  { GoFV.Rules.Generated.Generic.r_generic_646 with
    pat := .op .Add16 none .any .any .any .fixed
      [.op .Const16 none .any (.eq (.lit .int16 (.int 1))) .any .fixed [] false, .bind 0] true }

theorem mut646_not_sound : ¬ Rule.Sound mut646 := by
  apply Rule.not_sound (e := PEnv.ofLists [([1], .i16 5)] [] (.int .w16) [([0], 1)])
    (or := Oracle.const true)
  · simp [mut646, GoFV.Rules.Generated.Generic.r_generic_646]
    rule_eval
  · simp [mut646, GoFV.Rules.Generated.Generic.r_generic_646]
    rule_eval

/-! ## Instances of representative proven rules (`Add`) -/

/-- `generic.rules:675`: `(Add16 (Sub16 x t) (Add16 t y)) => (Add16 x y)` at `x = 7`,
`t = 3`, `y = 5`. -/
theorem inst_r_generic_675 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_675
    (PEnv.ofLists [([0, 0], .i16 7), ([1, 0], .i16 3), ([0, 1], .i16 3), ([1, 1], .i16 5)] []
      (.int .w16) [])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_675]
  rule_eval

/-- `generic.rules:2185`: the rotate rule `(Add32 left:(Lsh32x64 x y) right:(Rsh32Ux64 x
(Sub64 (Const64 [32]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) &&
canRotate(config, 32) => (RotateLeft32 x y)` at `x = 5`, `y = 3`, `left` bounded. -/
theorem inst_r_generic_2185 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_2185
    (PEnv.ofLists [([0, 0], .i32 5), ([1, 0], .i64 3), ([0, 1], .i32 5), ([1, 1, 1], .i64 3)]
      [([1, 1], .int .w64), ([0, 1, 1], .int .w64)] (.int .w32) [([0], 1), ([0, 1, 1], 32)])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_2185]
  rule_eval

end GoFV.Proof.Rules

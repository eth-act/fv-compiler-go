import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values00
import GoFV.Rules.Generated.Generic.Values02
import GoFV.Rules.Generated.Generic.Values03
import GoFV.Rules.Generated.Generic.Values07
import GoFV.Rules.Generated.Generic.Values08
import GoFV.Rules.Generated.Generic.Values04
import GoFV.Rules.Generated.Generic.Values05
import GoFV.Rules.Generated.Generic.Values06
import GoFV.Rules.Generated.Generic.Values10
import GoFV.Rules.Generated.Generic.Values11
import GoFV.Rules.Generated.Generic.Values12
import GoFV.Rules.Generated.Generic.Values13
import GoFV.Rules.Generated.Generic.Values14

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
  Oracle.BoolTyped or ∧
  Pat.wf e [] r.pat ∧
  Pat.cons (evalE (r.vars.map (·.ty)) (sigma e r.pat) or e (Pat.den e [] r.pat)) (sigma e r.pat)
    e [] r.pat ∧
  condHolds (evalE (r.vars.map (·.ty)) (sigma e r.pat) or e (Pat.den e [] r.pat)) r.cond ∧
  (Pat.raw e r.pat).hasTy (e.ty []) = true ∧
  Pat.typed e [] r.pat ∧
  Pat.raw e r.pat ≠ .poison

/-- The result value of `r` at an instance. -/
noncomputable def Rule.res (r : Rule) (e : PEnv) (or : Oracle) : Val :=
  resDen (evalE (r.vars.map (·.ty)) (sigma e r.pat) or e (Pat.den e [] r.pat)) or
    (sigma e r.pat) (e.ty []) r.result

/-- On an instance, `Rule.Sound r` says that the result equals the (non-poison) matched
value. -/
theorem Rule.Sound.refines {r : Rule} (h : Rule.Sound r) {e : PEnv} {or : Oracle}
    (hi : Rule.Inst r e or) : Refines (Pat.raw e r.pat) (Rule.res r e or) :=
  h.2 e or hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi.2.2.2.2.2.1

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

/-- An oracle answering every expression with the boolean `b` (`Oracle.const b` once
unfolded) is `BoolTyped`. -/
@[rule_eval] theorem Oracle.boolTyped_const_dv (b : Bool) (t : Expr → Ty) (a : Expr → Int64)
    (x : Expr → Option AuxRef) (v : Expr → Val) :
    Oracle.BoolTyped ⟨fun _ => .bool b, t, a, x, v⟩ :=
  fun _ _ => ⟨b, rfl⟩

@[simp] theorem Oracle.const_boolTyped (b : Bool) : Oracle.BoolTyped (Oracle.const b) :=
  Oracle.boolTyped_const_dv b _ _ _ _

-- The evaluation of `Rule.Inst`/`Rule.res` on a concrete rule and instance (`rule_eval`).
attribute [rule_eval] Rule.Inst Rule.res PEnv.ofLists Oracle.const Pat.den Pat.dens Pat.raw sigma
  Pat.binds Pat.bindss Pat.cons Pat.conss Pat.wf Pat.wfs Pat.typed Pat.typeds auxIntOk Field.bindDV condHolds resDen
  nodeDen List.length List.getElem?_cons_zero List.getElem?_cons_succ List.map reduceEvalPure
  reduceAuxType evalE evalEs auxIntDV List.lookup toAuxIntD Option.getD List.cons_append
  List.nil_append intBin binDV binE GoFV.Rules.wrapTo reduceIntInfo litDV fieldE indexE convE
  callE callH methodE builtinE unDV fieldDV DV.valOr typesShape shapeSize Option.map exprTy
  List.getD Option.getD_some Option.getD_none reduceCtorEq ne_eq not_false_eq_true and_true
  true_and and_self beq_self_eq_true Bool.and_true Bool.true_and Bool.or_true Bool.true_or
  Bool.cond_true Bool.cond_false Option.elim_none Option.elim_some Val.hasTy refines_int_int
  decide_eq_true_eq BitVec.reduceAdd BitVec.reduceShiftLeft BitVec.reduceUShiftRight
  BitVec.ofInt_ofNat GoFV.Rules.wrapInt Int64.reduceToInt Int.reduceBmod Int.reduceMod
  Nat.reducePow Nat.reduceAdd tbl reduceIte ite_true ite_false List.cons.injEq Nat.reduceBEq
  Nat.reduceBNe List.zip_cons_cons List.zip_nil_left List.zip_nil_right BitVec.reduceToNat
  BitVec.reduceShiftLeftShiftLeft bne_self_eq_false Bool.or_false Bool.false_or

/-- Evaluate `Rule.Inst`/`Rule.res` on a concrete rule and instance. -/
macro "rule_eval" : tactic => `(tactic|
  simp (config := { decide := true }) only [rule_eval, rule_helper, rule_sem])

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
      [([1, 1], .int .w64), ([0, 1, 1], .int .w64), ([1, 0], .int .w64), ([1, 1, 1], .int .w64)]
      (.int .w32) [([0], 1), ([0, 1, 1], 32)])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_2185]
  rule_eval

/-! ## Instances of representative rules of the `RotateLeft`, `Lsh`, `Rsh`, `Less`, `Leq` families -/

/-- `generic.rules:479`: `(RotateLeft16 x (Const16 [c])) && c%16 == 0 => x` at `x = 5`,
`c = 32`. -/
theorem inst_r_generic_479 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_479
    (PEnv.ofLists [([0], .i16 5)] [] (.int .w16) [([1], 32)]) (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_479]
  rule_eval
  simp [GoFV.Rules.goRem]

/-- `generic.rules:453`: `(Lsh16x8 x (Const8 [c])) => (Lsh16x64 x (Const64 <…> [int64(uint8(c))]))`
at `x = 3`, `c = 2`. -/
theorem inst_r_generic_453 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_453
    (PEnv.ofLists [([0], .i16 3)] [([1], .int .w8)] (.int .w16) [([1], 2)]) (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_453]
  rule_eval

/-- `generic.rules:232`: `(Rsh16x64 (Const16 [c]) (Const64 [d])) => (Const16 [c >> uint64(d)])`
at `c = -8`, `d = 1`. -/
theorem inst_r_generic_232 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_232
    (PEnv.ofLists [] [([1], .int .w64)] (.int .w16) [([0], -8), ([1], 1)]) (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_232]
  rule_eval

/-- `generic.rules:716`: `(Less16U x (Const16 <t> [1])) => (Eq16 x (Const16 <t> [0]))` at
`x = 0`. -/
theorem inst_r_generic_716 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_716
    (PEnv.ofLists [([0], .i16 0)] [([], .bool)] (.int .w16) [([1], 1)]) (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_716]
  rule_eval

/-- `generic.rules:714`: `(Leq16U x c:(Const16 [0])) => (Eq16 x c)` at `x = 7`. -/
theorem inst_r_generic_714 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_714
    (PEnv.ofLists [([0], .i16 7)] [([], .bool)] (.int .w16) []) (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_714]
  rule_eval

/-- `generic.rules:103`: `(ZeroExt16to32 (Const16 [c])) => (Const32 [int32(uint16(c))])` at
`c = -1`. -/
theorem inst_r_generic_103 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_103
    (PEnv.ofLists [] [([0], .int .w16)] (.int .w32) [([0], -1)]) (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_103]
  rule_eval

/-- `generic.rules:108`: `(SignExt8to64 (Const8 [c])) => (Const64 [int64(c)])` at `c = -3`. -/
theorem inst_r_generic_108 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_108
    (PEnv.ofLists [] [([0], .int .w8)] (.int .w64) [([0], -3)]) (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_108]
  rule_eval

/-- `generic.rules:752`: `(Trunc16to8 (And16 (Const16 [y]) x)) && y&0xFF == 0xFF =>
(Trunc16to8 x)` at `y = 0x1FF`, `x = 0x1234`. -/
theorem inst_r_generic_752 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_752
    (PEnv.ofLists [([1, 0], .i16 0x1234)] [([], .int .w8)] (.int .w16) [([0, 0], 0x1FF)])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_752]
  rule_eval
  simp only [GoFV.Rules.bitwise, DV.bool.injEq]
  rfl

/-- `generic.rules:400`: `(Not (Less64 x y)) => (Leq64 y x)` at `x = 1`, `y = 2`. -/
theorem inst_r_generic_400 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_400
    (PEnv.ofLists [([0, 0], .i64 1), ([1, 0], .i64 2)] [([0, 0], .int .w64), ([1, 0], .int .w64)]
      .bool []) (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_400]
  rule_eval

/-- `generic.rules:284`: `(EqB (Not x) y) => (NeqB x y)` at `x = true`, `y = false`. -/
theorem inst_r_generic_284 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_284
    (PEnv.ofLists [([0, 0], .bool true), ([1], .bool false)] [] .bool []) (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_284]
  rule_eval

/-- `generic.rules:290`: `(NeqB (Not x) y) => (EqB x y)` at `x = y = true`. -/
theorem inst_r_generic_290 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_290
    (PEnv.ofLists [([0, 0], .bool true), ([1], .bool true)] [] .bool []) (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_290]
  rule_eval

/-- `generic.rules:173`: `(Div16 (Const16 [c]) (Const16 [d])) && d != 0 => (Const16 [c/d])` at
`c = -7`, `d = 2`. -/
theorem inst_r_generic_173 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_173
    (PEnv.ofLists [] [([0], .int .w16), ([1], .int .w16)] (.int .w16) [([0], -7), ([1], 2)])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_173]
  rule_eval
  simp

/-- `generic.rules:1142`: `(Mod16 <t> n (Const16 [c])) && c < 0 && c != -1<<15 =>
(Mod16 <t> n (Const16 <t> [-c]))` at `n = -100`, `c = -7`. -/
theorem inst_r_generic_1142 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_1142
    (PEnv.ofLists [([0], .i16 (-100))] [([1], .int .w16)] (.int .w16) [([1], -7)])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_1142]
  rule_eval
  simp

end GoFV.Proof.Rules

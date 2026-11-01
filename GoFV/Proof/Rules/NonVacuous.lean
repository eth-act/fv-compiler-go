import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values00
import GoFV.Rules.Generated.Generic.Values02
import GoFV.Rules.Generated.Generic.Values03
import GoFV.Rules.Generated.Generic.Values07
import GoFV.Rules.Generated.Generic.Values08
import GoFV.Rules.Generated.Generic.Values09
import GoFV.Rules.Generated.Generic.Values04
import GoFV.Rules.Generated.Generic.Values05
import GoFV.Rules.Generated.Generic.Values06
import GoFV.Rules.Generated.Generic.Values10
import GoFV.Rules.Generated.Generic.Values11
import GoFV.Rules.Generated.Generic.Values12
import GoFV.Rules.Generated.Generic.Values13
import GoFV.Rules.Generated.Generic.Values14
import GoFV.Rules.Generated.Divisible.Values00

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
  Pat.argsOK e.ty [] r.pat = true ∧
  Pat.raw e r.pat ≠ .poison

/-- The result value of `r` at an instance. -/
noncomputable def Rule.res (r : Rule) (e : PEnv) (or : Oracle) : Val :=
  resDen (evalE (r.vars.map (·.ty)) (sigma e r.pat) or e (Pat.den e [] r.pat)) or
    (sigma e r.pat) (e.ty []) r.result

/-- On an instance, `Rule.Sound r` says that the result equals the (non-poison) matched
value. -/
theorem Rule.Sound.refines {r : Rule} (h : Rule.Sound r) {e : PEnv} {or : Oracle}
    (hi : Rule.Inst r e or) : Refines (Pat.raw e r.pat) (Rule.res r e or) :=
  h.2 e or hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi.2.2.2.2.2.1 hi.2.2.2.2.2.2.1

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

/-- `false` at a literal, else `true`. -/
def litAtom : Expr → Bool
  | .lit _ _ => false
  | _ => true

/-- The oracle answering `false` for an unmodelled literal and `true` for every other
unmodelled atom, so that an unmodelled string differs from a literal
(`v.Block.Func.pass.name != "opt"`). -/
noncomputable def Oracle.litFalse : Oracle where
  dv x := .bool (litAtom x)
  ty _ := .other
  auxInt _ := 0
  aux _ := none
  val _ := .poison

/-- An oracle answering every expression with a boolean is `BoolTyped`. -/
@[rule_eval] theorem Oracle.boolTyped_bool_dv (f : Expr → Bool) (t : Expr → Ty)
    (a : Expr → Int64) (x : Expr → Option AuxRef) (v : Expr → Val) :
    Oracle.BoolTyped ⟨fun y => .bool (f y), t, a, x, v⟩ :=
  fun y _ => ⟨f y, rfl⟩

-- The evaluation of `Rule.Inst`/`Rule.res` on a concrete rule and instance (`rule_eval`).
attribute [rule_eval] Rule.Inst Rule.res PEnv.ofLists Oracle.const Oracle.litFalse litAtom
  Pat.argsOK Pat.argsOKs argShapeOk isPtrTy isInt64Ty convArgOk Pat.den
  Pat.dens Pat.raw sigma
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

/-- `generic.rules:1097`: `(Div8u n (Const8 [c])) && isPowerOfTwo(uint8(c)) =>
(Rsh8Ux64 n (Const64 <typ.UInt64> [log8u(uint8(c))]))` at `n = 100`, `c = 4`. -/
theorem inst_r_generic_1097 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_1097
    (PEnv.ofLists [([0], .i8 100)] [([1], .int .w8)] (.int .w8) [([1], 4)])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_1097]
  rule_eval
  rfl

/-- `divisible.rules:17`: `(Eq16 x (Mul16 (Div16u x (Const16 [c])) (Const16 [c]))) &&
isPowerOfTwo(c) => (Eq16 (And16 x (Const16 [c-1])) (Const16 [0]))` at `x = 12`, `c = 4`. -/
theorem inst_r_divisible_17 : Rule.Inst GoFV.Rules.Generated.Divisible.r_divisible_17
    (PEnv.ofLists [([0], .i16 12), ([0, 0, 1], .i16 12)] [([], .bool)] (.int .w16)
      [([1, 0, 1], 4), ([1, 1], 4)])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Divisible.r_divisible_17]
  rule_eval
  rfl

/-- `generic.rules:1112`: `(Mul64 <t> x (Const64 [c])) && isPowerOfTwo(uint64(c)) &&
v.Block.Func.pass.name != "opt" => (Lsh64x64 <t> x (Const64 <typ.UInt64> [log64u(uint64(c))]))`
at `x = 5`, `c = 8`. -/
theorem inst_r_generic_1112 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_1112
    (PEnv.ofLists [([0], .i64 5)] [] (.int .w64) [([1], 8)])
    Oracle.litFalse := by
  simp [GoFV.Rules.Generated.Generic.r_generic_1112]
  rule_eval
  rfl

/-- `generic.rules:1120`: `(Mul64 <t> x (Const64 [c])) && isPowerOfTwo(uint64(-c)) &&
v.Block.Func.pass.name != "opt" => (Neg64 (Lsh64x64 <t> x (Const64 <typ.UInt64>
[log64u(uint64(-c))])))` at `x = 5`, `c = -8`. -/
theorem inst_r_generic_1120 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_1120
    (PEnv.ofLists [([0], .i64 5)] [] (.int .w64) [([1], -8)])
    Oracle.litFalse := by
  simp [GoFV.Rules.Generated.Generic.r_generic_1120]
  rule_eval
  rfl

/-- `generic.rules:964`: `(OffPtr (OffPtr p [y]) [x]) => (OffPtr p [x+y])` at a heap pointer
`p` (offset 8), `y = 16`, `x = 8`, every node pointer-typed (`Pat.argsOK`). -/
theorem inst_r_generic_964 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_964
    (PEnv.ofLists [([0, 0], .ptr ⟨.heap 0, 8⟩)] [] (.ptr none) [([0], 16), ([], 8)])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_964]
  rule_eval
  simp [PtrOps.offPtr, Val.retype, PtrOps.ptrRes, Ptr.add, Ptr.inWindow, Blk.window?]

/-- `generic.rules:970`: `(PtrIndex <t> ptr idx) && config.PtrSize == 8 => (AddPtr ptr (Mul64
<typ.Int> idx (Const64 <typ.Int> [t.Elem().Size()])))` at a heap pointer, `idx = 3`, element
size 8. -/
theorem inst_r_generic_970 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_970
    (PEnv.ofLists [([0], .ptr ⟨.heap 0, 0⟩), ([1], .i64 3)] [([1], .int .w64)] (.ptr (some 8)) [])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_970]
  rule_eval
  simp [PtrOps.ptrIndex, asOffset, PtrOps.ptrRes, Ptr.add, Ptr.inWindow, Blk.window?]

/-- `generic.rules:126`: `(AddPtr <t> x (Const64 [c])) => (OffPtr <t> x [c])` at a heap pointer,
`c = 24`. -/
theorem inst_r_generic_126 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_126
    (PEnv.ofLists [([0], .ptr ⟨.heap 0, 8⟩)] [([1], .int .w64)] (.ptr none) [([1], 24)])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_126]
  rule_eval
  simp [PtrOps.addPtr, asOffset, PtrOps.ptrRes, Ptr.add, Ptr.inWindow, Blk.window?]

end GoFV.Proof.Rules

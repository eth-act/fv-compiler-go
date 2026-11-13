import GoFV.Proof.Rules.NonVacuous
import GoFV.Proof.Rules.SoundW
import GoFV.Proof.Retype
import GoFV.Rules.Generated.Generic.Values06
import GoFV.Rules.Generated.Generic.Values07
import GoFV.Rules.Generated.Generic.Values11

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: the overflow-checked multiplication by 1 and the selections of a `MakeTuple`

`generic.rules:193` (`(Mul64uover <t> (Const64 [1]) x) => (MakeTuple x (ConstBool
<t.FieldType(1)> [false]))`, and its `Mul32uover` form) and `:1339`/`:1340`
(`(Select0 (MakeTuple x y)) => x`, `(Select1 (MakeTuple x y)) => y`): together they fold the
overflow check of `math/bits.Mul64(1, x)` (`runtime/internal/math.MulUintptr` of an element size
1, issue #69).

Their tops are a tuple and selections of one, which no `RewriteCheck.topAll` shape covers, so the
checker accepts them at any top type (`anyTop`) and their obligation is `Rule.SoundW`. The
checker's argument shapes (`argShapeOk`) give what the lemmas need: a `Mul<w>uover` has the
tuple shape `(int w, bool)`, a `MakeTuple` the two-component tuple shape of its arguments' shapes,
and a `Select0`/`Select1` the shape of the selected component. `t.FieldType(1)` of the tuple shape
is `bool` (`methodE`), so the built flag is `false`, as `x * 1` does not overflow.
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem

/-- `argShapeOk` of both arguments of a `MakeTuple`: its shape is the tuple of theirs. -/
theorem makeTuple_ty {T a b : Ty} (ha : argShapeOk .MakeTuple T 0 a = true)
    (hb : argShapeOk .MakeTuple T 1 b = true) : T = .tuple [a, b] := by
  unfold argShapeOk tupleCompOk at ha hb
  cases T with
  | tuple ts =>
    match ts with
    | [t0, t1] =>
      simp only [List.length_cons, List.length_nil, beq_self_eq_true, Bool.true_and,
        List.getElem?_cons_zero, List.getElem?_cons_succ, Option.any_some] at ha hb
      rw [Ty.eq_of_beq ha, Ty.eq_of_beq hb]
    | [] | [_] | _ :: _ :: _ :: _ => simp at ha
  | _ => simp at ha

/-- `argShapeOk` of a `Select0`: the selected component's shape is the selection's. -/
theorem select0_ty {t a b : Ty} (h : argShapeOk .Select0 t 0 (.tuple [a, b]) = true) : a = t := by
  unfold argShapeOk tupleCompOk at h
  simp only [bne_self_eq_false, Bool.false_or, List.getElem?_cons_zero, Option.any_some] at h
  exact Ty.eq_of_beq h

/-- `argShapeOk` of a `Select1`: the selected component's shape is the selection's. -/
theorem select1_ty {t a b : Ty} (h : argShapeOk .Select1 t 0 (.tuple [a, b]) = true) : b = t := by
  unfold argShapeOk tupleCompOk at h
  simp only [bne_self_eq_false, Bool.false_or, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.any_some] at h
  exact Ty.eq_of_beq h

/-- A selection of a `MakeTuple` retyped at a two-component tuple shape. -/
theorem select_make_retype (a b : Ty) (x y : Val) (i : Nat) :
    Tuple.select i [Val.retype (.tuple [a, b]) (Tuple.make [x, y])] =
      [x.retype a, y.retype b].getD i .poison := by
  simp [Tuple.make, Tuple.select, Val.retype, Val.retypePre]

/-- The constant 1 read at any shape is, as an integer of its width, 1. -/
theorem asInt_retype_one (w : Width) (T : Ty) {p : BitVec w.bits}
    (h : ((Val.int w 1).retype T).asInt w = some p) : p = 1 := by
  cases T with
  | int w' => cases w <;> cases w' <;> simp_all [Val.retype, Val.asInt, Width.bits]
  | _ => cases w <;> simp_all [Val.retype, Val.asInt]

/-- `Mul<w>uover 1 x` is `(x, false)` at the tuple shape `(int w, bool)`, or `poison`. -/
theorem mulover_one (w : Width) (T : Ty) (x : Val) :
    Refines ((Sem.Int.mulover w [(Val.int w 1).retype T, x]).retype (.tuple [.int w, .bool]))
      ((Tuple.make [x, Val.bool false]).retype (.tuple [.int w, .bool])) := by
  unfold Sem.Int.mulover GoFV.SSA.Sem.int2
  cases ha : ((Val.int w 1).retype T).asInt w with
  | none => simp only [ha]; exact .poison _
  | some p =>
    cases hx : x.asInt w with
    | none => simp only [ha, hx]; exact .poison _
    | some q =>
      have hp := asInt_retype_one w T ha
      subst hp
      simp only [ha, hx]
      have hxq : x = .int w q := by
        cases x with
        | int w' y =>
          simp only [Val.asInt] at hx
          split at hx
          · rename_i h; subst h; cases hx; rfl
          · cases hx
        | _ => simp [Val.asInt] at hx
      subst hxq
      have h1 : (1 : BitVec w.bits).toNat = 1 := by cases w <;> rfl
      have hq : ¬ 2 ^ w.bits ≤ 1 * q.toNat := by rw [Nat.one_mul]; exact Nat.not_le.2 q.isLt
      have hm : (1 : BitVec w.bits) * q = q := by cases w <;> simp
      rw [h1, hm]
      simp only [hq, decide_false, Tuple.make]
      exact Refines.refl _

/-- `generic.rules:193`: `(Mul32uover <t> (Const32 [1]) x) => (MakeTuple x (ConstBool <t.FieldType(1)> [false]))` -/
theorem r_generic_193_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_193 :=
  Rule.soundW_of_pure rfl (by
    refine ⟨rfl, ?_⟩
    intro e or _
    dsimp only [GoFV.Rules.Generated.Generic.r_generic_193, rule_unfold_ds]
    simp only [rule_helper, rule_unfold_s]
    intro _ hc _ _ hat _
    simp only [Pat.argsOK, Pat.argsOKs, argShapeOk, Bool.and_eq_true] at hat
    rw [Ty.eq_of_beq hat.1.1]
    simp only [DV.int.injEq] at hc
    rw [const_w32, hc]
    exact mulover_one .w32 _ _)

/-- `generic.rules:193`: `(Mul64uover <t> (Const64 [1]) x) => (MakeTuple x (ConstBool <t.FieldType(1)> [false]))` -/
theorem r_generic_193_2_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_193_2 :=
  Rule.soundW_of_pure rfl (by
    refine ⟨rfl, ?_⟩
    intro e or _
    dsimp only [GoFV.Rules.Generated.Generic.r_generic_193_2, rule_unfold_ds]
    simp only [rule_helper, rule_unfold_s]
    intro _ hc _ _ hat _
    simp only [Pat.argsOK, Pat.argsOKs, argShapeOk, Bool.and_eq_true] at hat
    rw [Ty.eq_of_beq hat.1.1]
    simp only [DV.int.injEq] at hc
    rw [const_w64, hc]
    exact mulover_one .w64 _ _)

/-- `generic.rules:1339`: `(Select0 (MakeTuple x y)) => x` -/
theorem r_generic_1339_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1339 :=
  Rule.soundW_of_pure rfl (by
    refine ⟨rfl, ?_⟩
    intro e or _
    dsimp only [GoFV.Rules.Generated.Generic.r_generic_1339, rule_unfold_ds]
    simp only [rule_helper, rule_unfold_s]
    intro _ _ _ hlt hat _
    simp only [Pat.argsOK, Pat.argsOKs, Bool.and_eq_true] at hat
    obtain ⟨⟨h0, ⟨hA, -⟩, ⟨hB, -⟩, -⟩, -⟩ := hat
    rw [makeTuple_ty hA hB] at h0 ⊢
    rw [select_make_retype, ← select0_ty h0]
    simp only [List.getD_cons_zero]
    rw [Val.retype_idem, Val.retype_of_hasTy hlt.1]
    exact Refines.refl _)

/-- `generic.rules:1340`: `(Select1 (MakeTuple x y)) => y` -/
theorem r_generic_1340_sound : Rule.SoundW GoFV.Rules.Generated.Generic.r_generic_1340 :=
  Rule.soundW_of_pure rfl (by
    refine ⟨rfl, ?_⟩
    intro e or _
    dsimp only [GoFV.Rules.Generated.Generic.r_generic_1340, rule_unfold_ds]
    simp only [rule_helper, rule_unfold_s]
    intro _ _ _ hlt hat _
    simp only [Pat.argsOK, Pat.argsOKs, Bool.and_eq_true] at hat
    obtain ⟨⟨h0, ⟨hA, -⟩, ⟨hB, -⟩, -⟩, -⟩ := hat
    rw [makeTuple_ty hA hB] at h0 ⊢
    rw [select_make_retype, ← select1_ty h0]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [Val.retype_idem, Val.retype_of_hasTy hlt.2]
    exact Refines.refl _)

/-! ## Non-vacuity -/

/-- `generic.rules:193` at `Mul64uover (Const64 [1]) 5` (the result `(5, false)`). -/
theorem inst_r_generic_193_2 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_193_2
    (PEnv.ofLists [([1], .int .w64 5)] [([], .tuple [.int .w64, .bool]), ([0], .int .w64),
      ([1], .int .w64)] (.int .w64) [([0], 1)])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_193_2]
  rule_eval
  simp [Val.hasTyPre, Val.hasTy]

/-- `generic.rules:1339` at `Select0 (MakeTuple 5 false)` (the result `5`). -/
theorem inst_r_generic_1339 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_1339
    (PEnv.ofLists [([0, 0], .int .w64 5), ([1, 0], .bool false)]
      [([], .int .w64), ([0], .tuple [.int .w64, .bool]), ([0, 0], .int .w64), ([1, 0], .bool)]
      (.int .w64) [])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_1339]
  rule_eval
  simp [Val.retypePre, Val.retype, Val.hasTy, Width.bits]

/-- `generic.rules:1340` at `Select1 (MakeTuple 5 false)` (the result `false`). -/
theorem inst_r_generic_1340 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_1340
    (PEnv.ofLists [([0, 0], .int .w64 5), ([1, 0], .bool false)]
      [([], .bool), ([0], .tuple [.int .w64, .bool]), ([0, 0], .int .w64), ([1, 0], .bool)]
      (.bool) [])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_1340]
  rule_eval
  simp [Val.retypePre, Val.retype, Val.hasTy, Width.bits]

end GoFV.Proof.Rules

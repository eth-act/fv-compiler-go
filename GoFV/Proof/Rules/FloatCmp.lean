import GoFV.Proof.Rules.Tactic

/-!
# Float comparisons (`docs/proofs/rules.md`, #69)

Facts about `GoFV.IEEE.compare` (`FPCompare`): swapping the operands swaps `lt`/`gt`
(`compare_swap`), a non-NaN is `eq` to itself (`compare_self`), a NaN operand gives `un`;
`FPAbs` keeps NaN-ness (`isNaN_abs`). The float ops of `GoFV.SSA.Sem.FOps` as `int1`/`int2` of
their width for `rule_sem` (`Eq`/`Neq` drop `ordered`: they are symmetric). `float_cmp` closes
the Boolean goals the `OrB (Neq x x) …` rules (`generic.rules:375–386`) leave.
-/

namespace GoFV.Proof.Rules.FloatCmp
open GoFV.IEEE

/-- The result of `FPCompare` with the operands swapped. -/
def swapCmp : Cmp → Cmp
  | .lt => .gt
  | .gt => .lt
  | c => c

theorem signed_not (s : Bool) (m : Nat) : signed (!s) m = -signed s m := by
  cases s <;> simp [signed]

theorem ordOf_swap (a b : Int) :
    (if b + -a < 0 then Ordering.lt else if b + -a = 0 then .eq else .gt) =
      (if a + -b < 0 then Ordering.lt else if a + -b = 0 then .eq else .gt).swap := by
  by_cases h1 : b + -a < 0
  · rw [if_pos h1, if_neg (by omega), if_neg (by omega)]; rfl
  · rw [if_neg h1]
    by_cases h2 : b + -a = 0
    · rw [if_pos h2, if_neg (by omega), if_pos (by omega)]; rfl
    · rw [if_neg h2, if_pos (by omega)]; rfl

theorem cmpVal_swap (t1 : FPType) (s1 : Bool) (m1 : Nat) (e1 : Int)
    (t2 : FPType) (s2 : Bool) (m2 : Nat) (e2 : Int) :
    cmpVal t2 s2 m2 e2 t1 s1 m1 e1 = (cmpVal t1 s1 m1 e1 t2 s2 m2 e2).swap := by
  unfold cmpVal addExact
  cases (t1 == .infinity) <;> cases (t2 == .infinity) <;> simp only
  all_goals first
    | (cases s1 <;> cases s2 <;> rfl)
    | (rw [Int.min_comm e2 e1, signed_not, signed_not]; exact ordOf_swap _ _)

theorem compare_swap (f : Fmt) (a b : Bits f) : IEEE.compare f b a = swapCmp (IEEE.compare f a b) := by
  unfold IEEE.compare
  simp only
  by_cases h : (unpack f a).1.isNaN ∨ (unpack f b).1.isNaN
  · rw [if_pos h.symm, if_pos h]; rfl
  · rw [if_neg (fun h' => h h'.symm), if_neg h, cmpVal_swap]
    cases cmpVal _ _ _ _ _ _ _ _ <;> rfl

theorem cmpVal_self (t : FPType) (s : Bool) (m : Nat) (e : Int) : cmpVal t s m e t s m e = .eq := by
  unfold cmpVal addExact
  cases (t == .infinity) <;> simp only [Int.min_self, signed_not, ite_true]
  rw [if_neg (by omega), if_pos (by omega)]

theorem compare_self (f : Fmt) (a : Bits f) (h : isNaN f a = false) : IEEE.compare f a a = .eq := by
  unfold IEEE.compare isNaN typeOf at *
  simp only
  rw [if_neg (by simp [h]), cmpVal_self]

theorem compare_nan_left (f : Fmt) (a b : Bits f) (h : isNaN f a = true) : IEEE.compare f a b = .un := by
  unfold IEEE.compare isNaN typeOf at *
  simp only
  rw [if_pos (Or.inl h)]

theorem compare_nan_right (f : Fmt) (a b : Bits f) (h : isNaN f b = true) : IEEE.compare f a b = .un := by
  unfold IEEE.compare isNaN typeOf at *
  simp only
  rw [if_pos (Or.inr h)]

theorem compare_ne_un (f : Fmt) (a b : Bits f) (ha : isNaN f a = false) (hb : isNaN f b = false) :
    IEEE.compare f a b ≠ .un := by
  unfold IEEE.compare isNaN typeOf at *
  simp only
  rw [if_neg (by simp [ha, hb])]
  split <;> simp_all

theorem expOf_abs (f : Fmt) (a : Bits f) : expOf f (abs f a) = expOf f a := by
  unfold expOf abs
  have h : 2 ^ (f.E + f.F) - 1 < 2 ^ (1 + f.E + f.F) := by
    have := Nat.pow_lt_pow_right (a := 2) (by decide) (show f.E + f.F < 1 + f.E + f.F by omega)
    have := Nat.two_pow_pos (f.E + f.F)
    omega
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.and_two_pow_sub_one_eq_mod,
    Nat.pow_add, Nat.mul_comm, Nat.mod_mul_right_div_self, Nat.mod_mod]

theorem fracOf_abs (f : Fmt) (a : Bits f) : fracOf f (abs f a) = fracOf f a := by
  unfold fracOf abs
  have h : 2 ^ (f.E + f.F) - 1 < 2 ^ (1 + f.E + f.F) := by
    have := Nat.pow_lt_pow_right (a := 2) (by decide) (show f.E + f.F < 1 + f.E + f.F by omega)
    have := Nat.two_pow_pos (f.E + f.F)
    omega
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

theorem isNaN_abs (f : Fmt) (a : Bits f) : isNaN f (abs f a) = isNaN f a := by
  unfold isNaN typeOf unpack
  simp only [expOf_abs, fracOf_abs]
  split <;> (try split) <;> (try split) <;> (try split) <;> rfl

/-- `ordered` under a condition that does not see the operand order. -/
theorem ordered_cmp (f : Fmt) (c : Cmp → Bool) (hc : ∀ k, c (swapCmp k) = c k) (x y : Bits f) :
    GoFV.SSA.Sem.FOps.ordered (fun a b => c (IEEE.compare f a b)) x y = c (IEEE.compare f x y) := by
  unfold GoFV.SSA.Sem.FOps.ordered
  split
  · rw [compare_swap, hc]
  · rfl

open GoFV.SSA GoFV.SSA.Sem

@[rule_sem] theorem fops_eq64 (a b : Val) :
    FOps.eq .w64 [a, b] = int2 .w64 (fun x y => .bool (IEEE.compare .b64 x y == .eq)) [a, b] := by
  simp only [FOps.eq, FOps.cmpC, ordered_cmp _ (· == .eq) (fun k => by cases k <;> rfl)]

@[rule_sem] theorem fops_neq64 (a b : Val) :
    FOps.neq .w64 [a, b] = int2 .w64 (fun x y => .bool (IEEE.compare .b64 x y != .eq)) [a, b] := by
  simp only [FOps.neq, FOps.cmpC, ordered_cmp _ (· != .eq) (fun k => by cases k <;> rfl)]

@[rule_sem] theorem fops_eq32 (a b : Val) :
    FOps.eq .w32 [a, b] = int2 .w32 (fun x y => .bool (IEEE.compare .b32 x y == .eq)) [a, b] := by
  simp only [FOps.eq, FOps.cmpC, ordered_cmp _ (· == .eq) (fun k => by cases k <;> rfl)]

@[rule_sem] theorem fops_neq32 (a b : Val) :
    FOps.neq .w32 [a, b] = int2 .w32 (fun x y => .bool (IEEE.compare .b32 x y != .eq)) [a, b] := by
  simp only [FOps.neq, FOps.cmpC, ordered_cmp _ (· != .eq) (fun k => by cases k <;> rfl)]

@[rule_sem] theorem fops_less64 (a b : Val) :
    FOps.less .w64 [a, b] = int2 .w64 (fun x y => .bool (IEEE.compare .b64 x y == .lt)) [a, b] := rfl

@[rule_sem] theorem fops_leq64 (a b : Val) :
    FOps.leq .w64 [a, b] =
      int2 .w64 (fun x y => .bool (IEEE.compare .b64 x y == .lt || IEEE.compare .b64 x y == .eq))
        [a, b] := rfl

@[rule_sem] theorem fops_less32 (a b : Val) :
    FOps.less .w32 [a, b] = int2 .w32 (fun x y => .bool (IEEE.compare .b32 x y == .lt)) [a, b] := rfl

@[rule_sem] theorem fops_leq32 (a b : Val) :
    FOps.leq .w32 [a, b] =
      int2 .w32 (fun x y => .bool (IEEE.compare .b32 x y == .lt || IEEE.compare .b32 x y == .eq))
        [a, b] := rfl

@[rule_sem] theorem fops_abs64 (a : Val) :
    FOps.abs .w64 [a] = int1 .w64 (fun x => .int .w64 (IEEE.abs .b64 x)) [a] := rfl

@[rule_sem] theorem fops_const64 (a : Int64) : FOps.const64 a = .int .w64 (BitVec.ofInt 64 a.toInt) := rfl

/-- A comparison of non-NaN encodings by its result. -/
theorem compare_cases (f : Fmt) (a b : Bits f) (ha : isNaN f a = false) (hb : isNaN f b = false) :
    IEEE.compare f a b = .lt ∨ IEEE.compare f a b = .eq ∨ IEEE.compare f a b = .gt := by
  have := compare_ne_un f a b ha hb
  revert this
  cases IEEE.compare f a b <;> simp

open Lean in
/-- The closed `IEEE.compare` applications of `e`. -/
partial def collectCmp (e : Lean.Expr) (acc : Array Lean.Expr) : Array Lean.Expr :=
  let acc := if e.isAppOfArity ``IEEE.compare 3 && !e.hasLooseBVars && !acc.contains e then
    acc.push e else acc
  match e with
  | .app f a => collectCmp a (collectCmp f acc)
  | .lam _ t b _ | .forallE _ t b _ => collectCmp b (collectCmp t acc)
  | .letE _ t v b _ => collectCmp b (collectCmp v (collectCmp t acc))
  | .mdata _ b | .proj _ _ b => collectCmp b acc
  | _ => acc

open Lean Meta Elab Tactic in
/-- Close a goal about `OrB (Neq x x) (cmp x c)`-style Boolean combinations of `IEEE.compare`
on a leaf `x` (or `abs x`) and constants that are not NaN (`hwf`): a NaN `x` makes every
comparison `un`; otherwise the self-comparison is `eq`, comparisons with `x` second are
swapped to have it first, and the remaining comparisons are split by their result. -/
elab "float_cmp" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let leaf? (a : Lean.Expr) : Option Lean.Expr :=
    if a.isFVar then some a
    else if a.isAppOfArity ``IEEE.abs 2 && (a.getArg! 1).isFVar then some (a.getArg! 1)
    else none
  let some t := tgt.find? fun t => t.isAppOfArity ``IEEE.compare 3 &&
      ((leaf? (t.getArg! 1)).isSome || (leaf? (t.getArg! 2)).isSome)
    | throwError "float_cmp: no comparison with a leaf"
  let some xe := (leaf? (t.getArg! 1)).orElse fun _ => leaf? (t.getArg! 2) | unreachable!
  let f ← Term.exprToSyntax (t.getArg! 0)
  let x ← Term.exprToSyntax xe
  let hnan := mkIdent `hnan
  evalTactic (← `(tactic| (
    cases $hnan:ident : IEEE.isNaN $f $x <;> first
    | simp only [GoFV.Proof.Rules.FloatCmp.compare_self $f $x $hnan:ident,
        GoFV.Proof.Rules.FloatCmp.compare_self $f (IEEE.abs $f $x)
          ((GoFV.Proof.Rules.FloatCmp.isNaN_abs $f $x).trans $hnan:ident),
        GoFV.Proof.Rules.FloatCmp.compare_swap $f $x,
        GoFV.Proof.Rules.FloatCmp.compare_swap $f (IEEE.abs $f $x)]
    | simp only [GoFV.Proof.Rules.FloatCmp.compare_nan_left $f _ _ $hnan:ident,
        GoFV.Proof.Rules.FloatCmp.compare_nan_right $f _ _ $hnan:ident,
        GoFV.Proof.Rules.FloatCmp.compare_nan_left $f _ _
          ((GoFV.Proof.Rules.FloatCmp.isNaN_abs $f $x).trans $hnan:ident),
        GoFV.Proof.Rules.FloatCmp.compare_nan_right $f _ _
          ((GoFV.Proof.Rules.FloatCmp.isNaN_abs $f $x).trans $hnan:ident)])))
  let mut out := #[]
  for g in ← getGoals do
    setGoals [g]
    let tgt ← instantiateMVars (← getMainTarget)
    let cs := collectCmp tgt #[]
    for c in cs do
      let fc ← Term.exprToSyntax (c.getArg! 0)
      let a ← Term.exprToSyntax (c.getArg! 1)
      let b ← Term.exprToSyntax (c.getArg! 2)
      evalTactic (← `(tactic| all_goals (try (
        rcases GoFV.Proof.Rules.FloatCmp.compare_cases $fc $a $b
          (by simp only [GoFV.Proof.Rules.FloatCmp.isNaN_abs]; assumption)
          (by simp only [GoFV.Proof.Rules.FloatCmp.isNaN_abs]; assumption) with hk | hk | hk <;>
        simp only [hk]))))
    out := out ++ (← getGoals)
  setGoals out.toList

end GoFV.Proof.Rules.FloatCmp

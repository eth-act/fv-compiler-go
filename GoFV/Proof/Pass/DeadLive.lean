import GoFV.Proof.Pass.DeadRel
import GoFV.Proof.Pass.DeadReach
import Std.Tactic.Do

/-!
# The liveness roots of `liveValuesOrder`

`live_root`: a value of a listed reachable block whose op calls, has side effects or is a nil
check is live (`liveValuesOrder` marks it while scanning the roots, and `live` only ever gets
`set! _ true`); `panicking_root`: every `Panicking` op is such a root. So deadcode drops no
value that may panic.
-/

open Std.Do

set_option mvcgen.warning false

namespace GoFV.Proof.Dead

open GoFV.SSA

/-- The `live` array has size `n` and, if `P`, marks `x`. -/
def Lv (n : Nat) (x : ID) (P : Prop) (a : Array Bool) : Prop :=
  a.size = n ∧ (P → a.getD x false = true)

/-- `a'` arises from `a` by marking: same size, `x` stays marked. -/
def Mono (n : Nat) (x : ID) (a a' : Array Bool) : Prop :=
  a.size = n → a'.size = n ∧ (a.getD x false = true → a'.getD x false = true)

theorem getD_set_true {a : Array Bool} {c y : Nat} (h : a.getD y false = true) :
    (a.set! c true).getD y false = true := by
  rw [Array.getD_eq_getD_getElem?] at h ⊢
  rw [Array.set!_eq_setIfInBounds]
  by_cases hcy : c = y
  · subst hcy
    by_cases hc : c < a.size
    · rw [Array.getElem?_setIfInBounds_self_of_lt hc]; rfl
    · rw [Array.getElem?_eq_none (Nat.le_of_not_lt hc)] at h; cases h
  · rw [Array.getElem?_setIfInBounds_ne hcy]; exact h

theorem getD_set_self {a : Array Bool} {c : Nat} (h : c < a.size) :
    (a.set! c true).getD c false = true := by
  rw [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds_self_of_lt h]
  rfl

theorem getD_of_true {a : Array Bool} {c : Nat} (h : c < a.size) (ht : a.getD c true = true) :
    a.getD c false = true := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h] at ht ⊢
  exact ht

theorem Mono.refl {n : Nat} {x : ID} {a : Array Bool} : Mono n x a a := fun h => ⟨h, id⟩

theorem Mono.set {n : Nat} {x : ID} {a a' : Array Bool} {c : Nat} (h : Mono n x a a') :
    Mono n x a (a'.set! c true) := fun hs =>
  ⟨by rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact (h hs).1,
    fun hx => getD_set_true ((h hs).2 hx)⟩

theorem Lv.mono {n : Nat} {x : ID} {P : Prop} {a a' : Array Bool} (h : Lv n x P a)
    (hm : Mono n x a a') : Lv n x P a' :=
  ⟨(hm h.1).1, fun hp => (hm h.1).2 (h.2 hp)⟩

theorem Lv.weaken {n : Nat} {x : ID} {P Q : Prop} {a : Array Bool} (h : Lv n x P a)
    (hq : Q → P) : Lv n x Q a :=
  ⟨h.1, fun hp => h.2 (hq hp)⟩

/-- The value step marking `cur`. -/
theorem vals_hit {n : Nat} {x cur : ID} {A B : Prop} {pref : List ID} {a a' : Array Bool}
    (h : Lv n x (A ∨ (B ∧ x ∈ pref)) a) (hxn : x < n) (hm : Mono n x (a.set! cur true) a') :
    Lv n x (A ∨ (B ∧ x ∈ pref ++ [cur])) a' := by
  have hs1 : (a.set! cur true).size = n := by
    rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact h.1
  refine ⟨(hm hs1).1, fun hp => (hm hs1).2 ?_⟩
  by_cases hc : cur = x
  · subst hc; exact getD_set_self (h.1 ▸ hxn)
  · refine getD_set_true (h.2 ?_)
    rcases hp with hp | ⟨hb, hp⟩
    · exact .inl hp
    · rcases List.mem_append.1 hp with hp | hp
      · exact .inr ⟨hb, hp⟩
      · exact absurd (List.mem_singleton.1 hp).symm hc

/-- A value step that does not mark `cur` (then `cur`, if it is `x`, is already marked). -/
theorem vals_miss {n : Nat} {x cur : ID} {A B : Prop} {pref : List ID} {a a' : Array Bool}
    (h : Lv n x (A ∨ (B ∧ x ∈ pref)) a) (hxn : x < n) (hgood : cur = x → a.getD x true = true)
    (hm : Mono n x a a') : Lv n x (A ∨ (B ∧ x ∈ pref ++ [cur])) a' := by
  refine ⟨(hm h.1).1, fun hp => (hm h.1).2 ?_⟩
  by_cases hc : cur = x
  · exact getD_of_true (h.1 ▸ hxn) (hgood hc)
  · refine h.2 ?_
    rcases hp with hp | ⟨hb, hp⟩
    · exact .inl hp
    · rcases List.mem_append.1 hp with hp | hp
      · exact .inr ⟨hb, hp⟩
      · exact absurd (List.mem_singleton.1 hp).symm hc

theorem miss_good {f : Func} {x cur : ID} {v w : Value} {a : Array Bool}
    (hw : f.value? cur = some w) (hv : f.value? x = some v)
    (hop : (v.op.call || v.op.hasSideEffects || v.op.nilCheck) = true)
    (hc : ¬((w.op.call || w.op.hasSideEffects || w.op.nilCheck) && !a.getD cur true) = true) :
    cur = x → a.getD x true = true := by
  intro hcx
  subst hcx
  rw [hv] at hw
  cases hw
  rw [hop, Bool.true_and] at hc
  simpa using hc

theorem miss_none {f : Func} {x cur : ID} {v : Value} {a : Array Bool} {o : Option Value}
    (ho : ∀ w, o = some w → False) (hw : f.value? cur = o) (hv : f.value? x = some v) :
    cur = x → a.getD x true = true := by
  intro hcx
  subst hcx
  exact (ho v (hw ▸ hv)).elim

theorem skip_unreach {n : Nat} {x bid cur : ID} {r : Array Bool} {pref : List ID}
    {a : Array Bool} (h : Lv n x (bid ∈ pref) a) (hr : r.getD bid false = true)
    (hc : (!r.getD cur false) = true) : Lv n x (bid ∈ pref ++ [cur]) a := by
  refine h.weaken fun hp => ?_
  rcases List.mem_append.1 hp with hp | hp
  · exact hp
  · have := List.mem_singleton.1 hp
    subst this
    rw [hr] at hc; cases hc

theorem skip_none {n : Nat} {x bid cur : ID} {f : Func} {b : Block} {pref : List ID}
    {a : Array Bool} {o : Option Block} (h : Lv n x (bid ∈ pref) a) (hb : f.block? bid = some b)
    (ho : ∀ blk, o = some blk → False) (hc : f.block? cur = o) :
    Lv n x (bid ∈ pref ++ [cur]) a := by
  refine h.weaken fun hp => ?_
  rcases List.mem_append.1 hp with hp | hp
  · exact hp
  · rw [List.mem_singleton.1 hp] at hb; exact (ho b (hc ▸ hb)).elim

theorem blk_done {n : Nat} {x bid cur : ID} {f : Func} {b blk : Block} {pref : List ID}
    {a : Array Bool} (h : Lv n x (bid ∈ pref ∨ (cur = bid ∧ x ∈ blk.values.toList)) a)
    (hb : f.block? bid = some b) (hx : x ∈ b.values) (hblk : f.block? cur = some blk) :
    Lv n x (bid ∈ pref ++ [cur]) a := by
  refine h.weaken fun hp => ?_
  rcases List.mem_append.1 hp with hp | hp
  · exact .inl hp
  · have hcb := (List.mem_singleton.1 hp).symm
    subst hcb
    rw [hb] at hblk; cases hblk
    exact .inr ⟨rfl, Array.mem_toList_iff.2 hx⟩

theorem lt_of_value? {f : Func} {x : ID} {v : Value} (h : f.value? x = some v) :
    x < f.valueTab.size := by
  unfold Func.value? at h
  cases hx : f.valueTab[x]? with
  | none => rw [hx] at h; cases h
  | some _ => exact (Array.getElem?_eq_some_iff.1 hx).1

/-- **Liveness roots.** A call, side-effecting or nil-check value of a listed reachable block
is live. -/
theorem live_root {f : Func} {t : Tables} {r : Array Bool}
    (hsize : f.valueTab.size ≤ f.vidLast + 1) {bid : ID} (hbm : bid ∈ f.blocks)
    (hr : r.getD bid false = true) {b : Block} (hb : f.block? bid = some b) {x : ID}
    (hx : x ∈ b.values) {v : Value} (hv : f.value? x = some v)
    (hop : (v.op.call || v.op.hasSideEffects || v.op.nilCheck) = true) :
    (f.liveValuesOrder t r).1.getD x false = true := by
  have hxn : x < f.vidLast + 1 := Nat.lt_of_lt_of_le (lt_of_value? hv) hsize
  apply Id.of_wp_run_eq (x := f.liveValuesOrder t r) rfl (fun p => p.1.getD x false = true)
  mvcgen
  case inv1 => exact ⇓ _ => ⌜True⌝
  case inv2 => exact ⇓ _ => ⌜True⌝
  case inv3 => exact ⇓⟨cur, live, _⟩ => ⌜Lv (f.vidLast + 1) x (bid ∈ cur.prefix) live⌝
  case inv4 =>
    rename_i pre _ _ _ _ _ _ _ _ _ _ _ _
    exact ⇓⟨_, live, _⟩ => ⌜Lv (f.vidLast + 1) x (bid ∈ pre) live⌝
  case inv5 =>
    rename_i pre bid' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    exact ⇓⟨cur, live, _⟩ =>
      ⌜Lv (f.vidLast + 1) x (bid ∈ pre ∨ (bid' = bid ∧ x ∈ cur.prefix)) live⌝
  case inv6 => exact ⇓⟨_, live, _⟩ => ⌜Lv (f.vidLast + 1) x True live⌝
  case inv7 => exact ⇓⟨_, live, _⟩ => ⌜Lv (f.vidLast + 1) x True live⌝
  all_goals mleave
  all_goals first
    | trivial
    | (rename_i h
       first
        | exact Lv.mono h (by first | exact Mono.refl | exact Mono.set Mono.refl)
        | exact vals_hit h hxn (by first | exact Mono.refl | exact Mono.set Mono.refl)
        | exact vals_miss h hxn (miss_good ‹_› hv hop ‹_›)
            (by first | exact Mono.refl | exact Mono.set Mono.refl)
        | exact vals_miss h hxn (miss_none ‹_› ‹_› hv) Mono.refl
        | exact skip_unreach h hr ‹_›
        | exact skip_none h hb ‹_› ‹_›
        | exact blk_done h hb hx ‹_›
        | exact h.weaken fun hp => hp.resolve_right fun h' => List.not_mem_nil h'.2
        | exact h.weaken fun _ => Array.mem_toList_iff.2 hbm
        | exact h.2 trivial
        | exact ⟨Array.size_replicate .., fun hp => absurd hp List.not_mem_nil⟩)

/-- Every op that may panic is a liveness root. -/
theorem panicking_root {op : Op} (h : Panicking op) :
    (op.call || op.hasSideEffects || op.nilCheck) = true := by
  rcases h with h | rfl
  · simp [h]
  · decide

end GoFV.Proof.Dead

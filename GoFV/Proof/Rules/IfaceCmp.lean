import GoFV.Proof.Rules.Tactic
import GoFV.Proof.Rules.NonVacuous
import GoFV.Rules.Generated.Generic.Values03
import GoFV.Rules.Generated.Generic.Values07
import GoFV.Rules.Generated.Generic.Values08

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: interface and slice comparisons (`generic.rules:790–793`)

`(EqInter x y) => (EqPtr (ITab x) (ITab y))`, `(EqSlice x y) => (EqPtr (SlicePtr x) (SlicePtr
y))` and their negations. `EqInter`/`EqSlice` compare the first words of two aggregates as
pointer words (`PtrOps.eqFirst`); the result compares the same words after `ITab`'s `uintptr`
or `SlicePtr`'s `*byte` retype (`eqFirst_refines`). A retype to a pointer shape keeps the pointer
of a word inside its window (`Val.asPtrWord_retype_ptr`), which every pointer of an operand's
first word is (it has a shape, `first_ptr_held`); a retype to the 64-bit integer shape keeps a
word of that shape (an integer or a pointer without a concrete address), and `argShapeOk` gives
the itab word of an `EqInter` operand that shape (`ifaceArgOk`, `first_hasTy_int64`). Without it
a struct operand whose first word is a pointer with an address would become that address, and
`Ptr.ofAddr` of it is a different pointer unless the pointer is `Ptr.convertible`.
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

/-- `EqInter`/`EqSlice` (and their negations) compare the first words as `EqPtr` of the
retyped first components when retyping keeps every word's pointer (`hx`, `hy`). -/
theorem eqFirst_refines (neg : Bool) (t T : Ty) (x y : Val)
    (hx : ∀ a as, x = .agg (a :: as) → a.asPtrWord.isSome → (a.retype t).asPtrWord = a.asPtrWord)
    (hy : ∀ b bs, y = .agg (b :: bs) → b.asPtrWord.isSome → (b.retype t).asPtrWord = b.asPtrWord)
    (hT : (PtrOps.eqFirst neg [x, y]).hasTy T = true) :
    Refines (PtrOps.eqFirst neg [x, y])
      ((PtrOps.eqPtr neg [(Comp.select 0 [x]).retype t, (Comp.select 0 [y]).retype t]).retype T) := by
  unfold PtrOps.eqFirst at hT ⊢
  split
  · rename_i _ a as b bs heq
    simp only [List.cons.injEq, and_true] at heq
    obtain ⟨rfl, rfl⟩ := heq
    split
    · rename_i p q hp hq
      have ea := hx a as rfl (by simp [hp])
      have eb := hy b bs rfl (by simp [hq])
      rw [hp] at ea; rw [hq] at eb
      simp only [hp, hq] at hT
      simp only [Comp.select, List.getD_cons_zero, PtrOps.eqPtr, ea, eb]
      exact refines_retype_of_hasTy hT
    · exact Refines.poison _
  · exact Refines.poison _

/-- A pointer that is the first component of a value of some shape is held as a pointer. -/
theorem first_ptr_held {x : Val} {t : Ty} (hx : x.hasTy t = true) {a : Val} {as : List Val}
    (he : x = .agg (a :: as)) : ∀ p, a = .ptr p → p.held = true := by
  rintro p rfl
  subst he
  cases t with
  | agg fs n =>
    cases fs with
    | nil => simp [Val.hasTy, Val.hasTyList] at hx
    | cons f fs =>
      have hx' : Val.hasTyList (Val.ptr p :: as) ((f :: fs).map (·.2)) = true := hx
      simp only [List.map_cons, Val.hasTyList, Bool.and_eq_true] at hx'
      exact Ptr.held_of_hasTy hx'.1
  | str =>
    obtain ⟨q, l, h, hq, -⟩ := Val.hasTy_agg_str.1 hx
    cases h; simpa [Val.isPtrWord] using hq
  | slice e =>
    obtain ⟨q, l, c, h, hq, -⟩ := Val.hasTy_agg_slice.1 hx
    cases h; simpa [Val.isPtrWord] using hq
  | _ => simp [Val.hasTy] at hx

theorem asPtrWord_retype_int64 (a : Val) (h : a.hasTy (.int .w64) = true) :
    (a.retype (.int .w64)).asPtrWord = a.asPtrWord := by
  rw [Val.retype_of_hasTy h]

/-- The first component of an operand `ifaceArgOk` accepts has the 64-bit integer shape. -/
theorem first_hasTy_int64 {x : Val} {t : Ty} (hx : x.hasTy t = true)
    (ht : (match fieldShape? t 0 with | some f => isInt64Ty f | none => true) = true)
    {a : Val} {as : List Val} (he : x = .agg (a :: as)) : a.hasTy (.int .w64) = true := by
  subst he
  cases t with
  | agg fs n =>
    cases fs with
    | nil => simp [Val.hasTy, Val.hasTyList] at hx
    | cons f fs =>
      simp only [Val.hasTy, List.map_cons, Val.hasTyList, Bool.and_eq_true] at hx
      simp only [fieldShape?, Ty.asAgg, List.getElem?_cons_zero, Option.map_some] at ht
      rw [isInt64Ty_iff] at ht
      rw [← ht]; exact hx.1
  | str | slice _ => simp [fieldShape?, Ty.asAgg, Ty.strAgg, Ty.sliceAgg, isInt64Ty] at ht
  | _ => simp [Val.hasTy] at hx

/-- `generic.rules:790`: `(EqInter x y) => (EqPtr (ITab x) (ITab y))` -/
theorem r_generic_790_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_790 := by
  rule_unfold
  exact eqFirst_refines _ _ _ _ _
    (fun a as he _ => asPtrWord_retype_int64 a (first_hasTy_int64 hlt.1 hat.1 he))
    (fun a as he _ => asPtrWord_retype_int64 a (first_hasTy_int64 hlt.2 hat.2 he)) hty

/-- `generic.rules:791`: `(NeqInter x y) => (NeqPtr (ITab x) (ITab y))` -/
theorem r_generic_791_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_791 := by
  rule_unfold
  exact eqFirst_refines _ _ _ _ _
    (fun a as he _ => asPtrWord_retype_int64 a (first_hasTy_int64 hlt.1 hat.1 he))
    (fun a as he _ => asPtrWord_retype_int64 a (first_hasTy_int64 hlt.2 hat.2 he)) hty

/-- `generic.rules:792`: `(EqSlice x y) => (EqPtr (SlicePtr x) (SlicePtr y))` -/
theorem r_generic_792_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_792 := by
  rule_unfold
  exact eqFirst_refines _ _ _ _ _
    (fun a as he _ => Val.asPtrWord_retype_ptr _
      fun p hp => Ptr.inWindow_of_held (first_ptr_held hlt.1 he p hp))
    (fun a as he _ => Val.asPtrWord_retype_ptr _
      fun p hp => Ptr.inWindow_of_held (first_ptr_held hlt.2 he p hp)) hty

/-- `generic.rules:793`: `(NeqSlice x y) => (NeqPtr (SlicePtr x) (SlicePtr y))` -/
theorem r_generic_793_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_793 := by
  rule_unfold
  exact eqFirst_refines _ _ _ _ _
    (fun a as he _ => Val.asPtrWord_retype_ptr _
      fun p hp => Ptr.inWindow_of_held (first_ptr_held hlt.1 he p hp))
    (fun a as he _ => Val.asPtrWord_retype_ptr _
      fun p hp => Ptr.inWindow_of_held (first_ptr_held hlt.2 he p hp)) hty

/-! Non-vacuity (`rule-sat` draws no aggregate leaves): instances at the interface shape (two
itab words, equal for `:790`, different for `:791`) and at the shape of `[]int64` (the same and
different globals). -/

/-- `generic.rules:790` at two interfaces with the same itab word. -/
theorem inst_r_generic_790 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_790
    (PEnv.ofLists [([0], .agg [.int .w64 8, .ptr ⟨.global "g", 0⟩]),
        ([1], .agg [.int .w64 8, .ptr ⟨.global "h", 0⟩])]
      [([], .bool)] (.agg [(0, .int .w64), (8, .ptr (some 1))] 16) [])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_790]
  rule_eval
  simp [PtrOps.eqFirst, Val.asPtrWord, Ptr.eq]

/-- `generic.rules:791` at two interfaces with different itab words. -/
theorem inst_r_generic_791 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_791
    (PEnv.ofLists [([0], .agg [.int .w64 8, .ptr ⟨.global "g", 0⟩]),
        ([1], .agg [.int .w64 16, .ptr ⟨.global "h", 0⟩])]
      [([], .bool)] (.agg [(0, .int .w64), (8, .ptr (some 1))] 16) [])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_791]
  rule_eval
  simp [PtrOps.eqFirst, Val.asPtrWord, Ptr.eq]

/-- `generic.rules:792` at two slices of the same global. -/
theorem inst_r_generic_792 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_792
    (PEnv.ofLists [([0], .agg [.ptr ⟨.global "g", 0⟩, .int .w64 1, .int .w64 1]),
        ([1], .agg [.ptr ⟨.global "g", 0⟩, .int .w64 1, .int .w64 1])]
      [([], .bool)] (.agg [(0, .ptr (some 8)), (8, .int .w64), (16, .int .w64)] 24) [])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_792]
  rule_eval
  simp [PtrOps.eqFirst, Val.asPtrWord, Ptr.eq]

/-- `generic.rules:793` at two slices of different globals. -/
theorem inst_r_generic_793 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_793
    (PEnv.ofLists [([0], .agg [.ptr ⟨.global "g", 0⟩, .int .w64 1, .int .w64 1]),
        ([1], .agg [.ptr ⟨.global "h", 0⟩, .int .w64 1, .int .w64 1])]
      [([], .bool)] (.agg [(0, .ptr (some 8)), (8, .int .w64), (16, .int .w64)] 24) [])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_793]
  rule_eval
  simp [PtrOps.eqFirst, Val.asPtrWord, Ptr.eq]

end GoFV.Proof.Rules

import GoFV.Proof.ValRefine
import GoFV.SSA.Sem.Pure

/-!
# The pure ops are monotone in refinement (`docs/plans/semantics.md` §3.5)

`evalPure_mono`: refined arguments give a refined result. Each family of `Sem/Pure` has its
lemma; an argument the family reads as an integer, boolean or pointer is refined only by
itself unless it is `poison`, which gives `poison`.
-/

namespace GoFV.SSA.Sem

open GoFV.SSA

variable {a b : Val} {as bs : List Val}

/-! ## Reading arguments -/

theorem Refines.asInt {w : Width} {x : BitVec w.bits} (h : Refines a b) (hx : a.asInt w = some x) :
    b.asInt w = some x := by cases h <;> simp_all [Val.asInt]

theorem Refines.asNat {x : Nat} (h : Refines a b) (hx : a.asNat = some x) : b.asNat = some x := by
  cases h <;> simp_all [Val.asNat]

theorem Refines.asBool {x : Bool} (h : Refines a b) (hx : a.asBool = some x) :
    b.asBool = some x := by cases h <;> simp_all [Val.asBool]

theorem Refines.asPtrWord {x : Ptr} (h : Refines a b) (hx : a.asPtrWord = some x) :
    b.asPtrWord = some x := by cases h <;> simp_all [Val.asPtrWord]

theorem Refines.asOffset {x : BitVec 64} (h : Refines a b) (hx : asOffset a = some x) :
    asOffset b = some x := by cases h <;> simp_all [asOffset]

/-- A refined argument that is an integer, boolean, pointer or empty value is unchanged. -/
theorem Refines.eq_int {w : Width} {x : BitVec w.bits} (h : Refines (.int w x) b) : b = .int w x := by
  cases h; rfl

theorem Refines.eq_ptr {p : Ptr} (h : Refines (.ptr p) b) : b = .ptr p := by cases h; rfl

theorem RefinesList.getD : ∀ (i : Nat) {as bs : List Val}, RefinesList as bs →
    Refines (as.getD i .poison) (bs.getD i .poison)
  | _, _, _, .nil => .poison _
  | 0, _, _, .cons h _ => by simpa using h
  | i + 1, _, _, .cons _ t => by simpa using RefinesList.getD i t

/-! ## Combinators -/

theorem int1_mono (w : Width) (f : BitVec w.bits → Val) :
    RefinesList as bs → Refines (int1 w f as) (int1 w f bs)
  | .nil => .poison _
  | .cons (a := a) h .nil => by
    simp only [int1]
    cases ha : a.asInt w with
    | none => exact .poison _
    | some x => rw [h.asInt ha]; exact Refines.refl _
  | .cons _ (.cons _ _) => .poison _

theorem int2_mono (w : Width) (f : BitVec w.bits → BitVec w.bits → Val) :
    RefinesList as bs → Refines (int2 w f as) (int2 w f bs)
  | .nil => .poison _
  | .cons _ .nil => .poison _
  | .cons (a := a) h (.cons (a := c) h' .nil) => by
    simp only [int2]
    cases ha : a.asInt w with
    | none => exact .poison _
    | some x =>
      cases hc : c.asInt w with
      | none => exact .poison _
      | some y => rw [h.asInt ha, h'.asInt hc]; exact Refines.refl _
  | .cons _ (.cons _ (.cons _ _)) => .poison _

theorem int3_mono (w : Width) (f : BitVec w.bits → BitVec w.bits → BitVec w.bits → Val) :
    RefinesList as bs → Refines (int3 w f as) (int3 w f bs)
  | .nil => .poison _
  | .cons _ .nil => .poison _
  | .cons _ (.cons _ .nil) => .poison _
  | .cons (a := a) h (.cons (a := c) h' (.cons (a := d) h'' .nil)) => by
    simp only [int3]
    cases ha : a.asInt w with
    | none => exact .poison _
    | some x =>
      cases hc : c.asInt w with
      | none => exact .poison _
      | some y =>
        cases hd : d.asInt w with
        | none => exact .poison _
        | some z => rw [h.asInt ha, h'.asInt hc, h''.asInt hd]; exact Refines.refl _
  | .cons _ (.cons _ (.cons _ (.cons _ _))) => .poison _

theorem bool1_mono (f : Bool → Bool) : RefinesList as bs → Refines (bool1 f as) (bool1 f bs)
  | .nil => .poison _
  | .cons (a := a) h .nil => by
    simp only [bool1]
    cases ha : a.asBool with
    | none => exact .poison _
    | some x => rw [h.asBool ha]; exact Refines.refl _
  | .cons _ (.cons _ _) => .poison _

theorem bool2_mono (f : Bool → Bool → Bool) :
    RefinesList as bs → Refines (bool2 f as) (bool2 f bs)
  | .nil => .poison _
  | .cons _ .nil => .poison _
  | .cons (a := a) h (.cons (a := c) h' .nil) => by
    simp only [bool2]
    cases ha : a.asBool with
    | none => exact .poison _
    | some x =>
      cases hc : c.asBool with
      | none => exact .poison _
      | some y => rw [h.asBool ha, h'.asBool hc]; exact Refines.refl _
  | .cons _ (.cons _ (.cons _ _)) => .poison _

theorem Shift.shift_mono (w s : Width) (bd : Bool) (f : BitVec w.bits → Nat → BitVec w.bits) :
    RefinesList as bs → Refines (Shift.shift w s bd f as) (Shift.shift w s bd f bs)
  | .nil => .poison _
  | .cons _ .nil => .poison _
  | .cons (a := a) h (.cons (a := c) h' .nil) => by
    simp only [Shift.shift]
    cases ha : a.asInt w with
    | none => exact .poison _
    | some x =>
      cases hc : c.asInt s with
      | none => exact .poison _
      | some y => rw [h.asInt ha, h'.asInt hc]; exact Refines.refl _
  | .cons _ (.cons _ (.cons _ _)) => .poison _

theorem Int.rotateLeft_mono (w : Width) : RefinesList as bs → Refines (Int.rotateLeft w as) (Int.rotateLeft w bs)
  | .nil => .poison _
  | .cons _ .nil => .poison _
  | .cons (a := a) h (.cons (a := c) h' .nil) => by
    simp only [Int.rotateLeft]
    cases ha : a.asInt w with
    | none => exact .poison _
    | some x =>
      cases hc : c.asNat with
      | none => exact .poison _
      | some y => rw [h.asInt ha, h'.asNat hc]; exact Refines.refl _
  | .cons _ (.cons _ (.cons _ _)) => .poison _

/-! ## Selections and composites -/

theorem Cmp.condSelect_mono : RefinesList as bs → Refines (Cmp.condSelect as) (Cmp.condSelect bs)
  | .nil => by simp only [Cmp.condSelect]; exact .poison _
  | .cons _ .nil => by simp only [Cmp.condSelect]; exact .poison _
  | .cons _ (.cons _ .nil) => by simp only [Cmp.condSelect]; exact .poison _
  | .cons hx (.cons hy (.cons (a := c) hc .nil)) => by
    simp only [Cmp.condSelect]
    cases h : c.asBool with
    | none => exact .poison _
    | some x =>
      rw [hc.asBool h]
      cases x
      · exact hy
      · exact hx
  | .cons _ (.cons _ (.cons _ (.cons _ _))) => by simp only [Cmp.condSelect]; exact .poison _

theorem Conv.boolToUint8_mono : RefinesList as bs → Refines (Conv.boolToUint8 as) (Conv.boolToUint8 bs)
  | .nil => .poison _
  | .cons (a := a) h .nil => by
    simp only [Conv.boolToUint8]
    cases ha : a.asBool with
    | none => exact .poison _
    | some x => rw [h.asBool ha]; exact Refines.refl _
  | .cons _ (.cons _ _) => .poison _

theorem Cmp.inBounds_mono (sl : Bool) : RefinesList as bs → Refines (Cmp.inBounds sl as) (Cmp.inBounds sl bs)
  | .nil => by simp only [Cmp.inBounds]; exact .poison _
  | .cons _ .nil => by simp only [Cmp.inBounds]; exact .poison _
  | .cons (a := a) h (.cons (a := c) h' .nil) => by
    cases h with
    | int w i =>
      simp only [Cmp.inBounds]
      cases hc : c.asInt w with
      | none => exact .poison _
      | some y => rw [h'.asInt hc]; exact Refines.refl _
    | poison => exact .poison _
    | _ => exact .poison _
  | .cons _ (.cons _ (.cons _ _)) => by simp only [Cmp.inBounds]; exact .poison _

theorem Cmp.spectreIndex_mono (sl : Bool) :
    RefinesList as bs → Refines (Cmp.spectreIndex sl as) (Cmp.spectreIndex sl bs)
  | .nil => by simp only [Cmp.spectreIndex]; exact .poison _
  | .cons _ .nil => by simp only [Cmp.spectreIndex]; exact .poison _
  | .cons (a := a) h (.cons (a := c) h' .nil) => by
    cases h with
    | int w i =>
      simp only [Cmp.spectreIndex]
      cases hc : c.asInt w with
      | none => exact .poison _
      | some y => rw [h'.asInt hc]; exact Refines.refl _
    | poison => exact .poison _
    | _ => exact .poison _
  | .cons _ (.cons _ (.cons _ _)) => by simp only [Cmp.spectreIndex]; exact .poison _

theorem Tuple.select_mono (i : Nat) : RefinesList as bs → Refines (Tuple.select i as) (Tuple.select i bs)
  | .nil => by simp only [Tuple.select]; exact .poison _
  | .cons h .nil => by
    cases h with
    | tuple ht => simp only [Tuple.select]; exact ht.getD i
    | poison => exact .poison _
    | _ => exact .poison _
  | .cons _ (.cons _ _) => by simp only [Tuple.select]; exact .poison _

theorem Refines.asBool_cases (h : Refines a b) : a.asBool = none ∨ b.asBool = a.asBool := by
  cases h <;> simp [Val.asBool]

/-- The parallel `AndB`/`OrB` (`Cmp.andB`, `Cmp.orB`): every combination of the operands'
booleans, the source's `none` refined by any target operand. -/
theorem Cmp.andB_mono : RefinesList as bs → Refines (Cmp.andB as) (Cmp.andB bs)
  | .nil => .poison _
  | .cons _ .nil => .poison _
  | .cons (a := a) (b := a') ha (.cons (a := b) (b := b') hb .nil) => by
    simp only [Cmp.andB]
    rcases ha.asBool_cases with hA | hA <;> rcases hb.asBool_cases with hB | hB <;> rw [hA, hB] <;>
      generalize a.asBool = x <;> generalize b.asBool = y <;> generalize a'.asBool = x' <;>
      generalize b'.asBool = y' <;>
      rcases x with _ | _ | _ <;> rcases y with _ | _ | _ <;> rcases x' with _ | _ | _ <;>
      rcases y' with _ | _ | _ <;> first | exact Refines.refl _ | exact .poison _
  | .cons _ (.cons _ (.cons _ _)) => .poison _

theorem Cmp.orB_mono : RefinesList as bs → Refines (Cmp.orB as) (Cmp.orB bs)
  | .nil => .poison _
  | .cons _ .nil => .poison _
  | .cons (a := a) (b := a') ha (.cons (a := b) (b := b') hb .nil) => by
    simp only [Cmp.orB]
    rcases ha.asBool_cases with hA | hA <;> rcases hb.asBool_cases with hB | hB <;> rw [hA, hB] <;>
      generalize a.asBool = x <;> generalize b.asBool = y <;> generalize a'.asBool = x' <;>
      generalize b'.asBool = y' <;>
      rcases x with _ | _ | _ <;> rcases y with _ | _ | _ <;> rcases x' with _ | _ | _ <;>
      rcases y' with _ | _ | _ <;> first | exact Refines.refl _ | exact .poison _
  | .cons _ (.cons _ (.cons _ _)) => .poison _

theorem Tuple.selectN_mono (k : Int64) :
    RefinesList as bs → Refines (Tuple.selectN k as) (Tuple.selectN k bs)
  | .nil => by simp only [Tuple.selectN]; exact .poison _
  | .cons h .nil => by
    cases h with
    | tuple ht =>
      simp only [Tuple.selectN]
      split
      · exact .poison _
      · exact ht.getD _
    | poison => exact .poison _
    | _ => exact .poison _
  | .cons _ (.cons _ _) => by simp only [Tuple.selectN]; exact .poison _

theorem RefinesList.getLast? : {as bs : List Val} → RefinesList as bs →
    (as.getLast? = none ∧ bs.getLast? = none) ∨
      ∃ a b, as.getLast? = some a ∧ bs.getLast? = some b ∧ Refines a b
  | _, _, .nil => .inl ⟨rfl, rfl⟩
  | _, _, .cons h .nil => .inr ⟨_, _, rfl, rfl, h⟩
  | _, _, .cons _ (.cons h' t) => by
    simpa [List.getLast?_cons_cons] using RefinesList.getLast? (.cons h' t)

theorem RefinesList.getElem? : ∀ (i : Nat) {as bs : List Val}, RefinesList as bs →
    (as[i]? = none ∧ bs[i]? = none) ∨ ∃ a b, as[i]? = some a ∧ bs[i]? = some b ∧ Refines a b
  | _, _, _, .nil => .inl ⟨rfl, rfl⟩
  | 0, _, _, .cons h _ => .inr ⟨_, _, rfl, rfl, h⟩
  | i + 1, _, _, .cons _ t => by simpa using RefinesList.getElem? i t

theorem Tuple.selectNAddr_mono (k : Int64) :
    RefinesList as bs → Refines (Tuple.selectNAddr k as) (Tuple.selectNAddr k bs)
  | .nil => by simp only [Tuple.selectNAddr]; exact .poison _
  | .cons h .nil => by
    cases h with
    | tuple ht =>
      simp only [Tuple.selectNAddr]
      rcases ht.getLast? with ⟨h1, h2⟩ | ⟨x, y, h1, h2, hxy⟩
      · rw [h1]; exact .poison _
      · rw [h1, h2]
        cases hxy with
        | agg hl =>
          dsimp only
          split
          · exact .poison _
          · rcases hl.getElem? k.toInt.toNat with ⟨h3, h4⟩ | ⟨p, q, h3, h4, hpq⟩
            · rw [h3]; exact .poison _
            · rw [h3, h4]
              cases hpq with
              | ptr p => exact Refines.refl _
              | _ => exact .poison _
        | _ => exact .poison _
    | poison => exact .poison _
    | _ => exact .poison _
  | .cons _ (.cons _ _) => by simp only [Tuple.selectNAddr]; exact .poison _

theorem Tuple.make_mono : RefinesList as bs → Refines (Tuple.make as) (Tuple.make bs)
  | .nil => by simp only [Tuple.make]; exact .poison _
  | .cons _ .nil => by simp only [Tuple.make]; exact .poison _
  | .cons h (.cons h' .nil) => .tuple (.cons h (.cons h' .nil))
  | .cons _ (.cons _ (.cons _ _)) => by simp only [Tuple.make]; exact .poison _

theorem Comp.select_mono (i : Nat) : RefinesList as bs → Refines (Comp.select i as) (Comp.select i bs)
  | .nil => by simp only [Comp.select]; exact .poison _
  | .cons h .nil => by
    cases h with
    | agg ht => simp only [Comp.select]; exact ht.getD i
    | poison => exact .poison _
    | _ => exact .poison _
  | .cons _ (.cons _ _) => by simp only [Comp.select]; exact .poison _

theorem Comp.selectAux_mono (k : Int64) (h : RefinesList as bs) :
    Refines (Comp.selectAux k as) (Comp.selectAux k bs) := by
  unfold Comp.selectAux
  split
  · exact .poison _
  · exact Comp.select_mono _ h

/-! ## Pointers and memory -/

theorem PtrOps.offPtr_mono (k : Int64) : RefinesList as bs → Refines (PtrOps.offPtr k as) (PtrOps.offPtr k bs)
  | .nil => by simp only [PtrOps.offPtr]; exact .poison _
  | .cons h .nil => by
    cases h with
    | ptr p => exact Refines.refl _
    | int w x => exact Refines.refl _
    | poison => exact .poison _
    | _ => exact .poison _
  | .cons _ (.cons _ _) => by simp only [PtrOps.offPtr]; exact .poison _

theorem PtrOps.addPtr_mono : RefinesList as bs → Refines (PtrOps.addPtr as) (PtrOps.addPtr bs)
  | .nil => by simp only [PtrOps.addPtr]; exact .poison _
  | .cons _ .nil => by simp only [PtrOps.addPtr]; exact .poison _
  | .cons h (.cons (a := c) h' .nil) => by
    cases h with
    | ptr p =>
      simp only [PtrOps.addPtr]
      cases hc : asOffset c with
      | none => exact .poison _
      | some k => rw [h'.asOffset hc]; exact Refines.refl _
    | int w x =>
      cases w <;> simp only [PtrOps.addPtr]
      all_goals first
        | exact .poison _
        | (cases hc : asOffset c with
            | none => exact .poison _
            | some k => rw [h'.asOffset hc]; exact Refines.refl _)
    | poison => exact .poison _
    | _ => exact .poison _
  | .cons _ (.cons _ (.cons _ _)) => by simp only [PtrOps.addPtr]; exact .poison _

theorem PtrOps.ptrIndex_mono (e : Option Nat) :
    RefinesList as bs → Refines (PtrOps.ptrIndex e as) (PtrOps.ptrIndex e bs)
  | .nil => by simp only [PtrOps.ptrIndex]; exact .poison _
  | .cons _ .nil => by simp only [PtrOps.ptrIndex]; exact .poison _
  | .cons h (.cons (a := c) h' .nil) => by
    cases h with
    | ptr p =>
      simp only [PtrOps.ptrIndex]
      cases e with
      | none => exact .poison _
      | some e =>
        cases hc : asOffset c with
        | none => exact .poison _
        | some k => rw [h'.asOffset hc]; exact Refines.refl _
    | poison => exact .poison _
    | _ => exact .poison _
  | .cons _ (.cons _ (.cons _ _)) => by simp only [PtrOps.ptrIndex]; exact .poison _

theorem PtrOps.subPtr_mono : RefinesList as bs → Refines (PtrOps.subPtr as) (PtrOps.subPtr bs)
  | .nil => by simp only [PtrOps.subPtr]; exact .poison _
  | .cons _ .nil => by simp only [PtrOps.subPtr]; exact .poison _
  | .cons h (.cons h' .nil) => by
    cases h with
    | ptr p =>
      cases h' with
      | ptr q => exact Refines.refl _
      | poison => exact .poison _
      | _ => exact .poison _
    | poison => exact .poison _
    | _ => exact .poison _
  | .cons _ (.cons _ (.cons _ _)) => by simp only [PtrOps.subPtr]; exact .poison _

theorem PtrOps.eqPtr_mono (neg : Bool) : RefinesList as bs → Refines (PtrOps.eqPtr neg as) (PtrOps.eqPtr neg bs)
  | .nil => .poison _
  | .cons _ .nil => .poison _
  | .cons (a := a) h (.cons (a := c) h' .nil) => by
    simp only [PtrOps.eqPtr]
    cases ha : a.asPtrWord with
    | none => exact .poison _
    | some x =>
      cases hc : c.asPtrWord with
      | none => exact .poison _
      | some y => rw [h.asPtrWord ha, h'.asPtrWord hc]; exact Refines.refl _
  | .cons _ (.cons _ (.cons _ _)) => .poison _

theorem PtrOps.isNonNil_mono : RefinesList as bs → Refines (PtrOps.isNonNil as) (PtrOps.isNonNil bs)
  | .nil => by simp only [PtrOps.isNonNil]; exact .poison _
  | .cons h .nil => by
    cases h with
    | ptr p => exact Refines.refl _
    | int w x => exact Refines.refl _
    | poison => exact .poison _
    | _ => exact .poison _
  | .cons _ (.cons _ _) => by simp only [PtrOps.isNonNil]; exact .poison _

theorem PtrOps.convert_mono (t : Ty) : RefinesList as bs → Refines (PtrOps.convert t as) (PtrOps.convert t bs)
  | .nil => by simp only [PtrOps.convert]; exact .poison _
  | .cons _ .nil => by simp only [PtrOps.convert]; exact .poison _
  | .cons h (.cons _ .nil) => by
    cases h with
    | poison =>
      have : ∀ y : Val, PtrOps.convert t [.poison, y] = .poison := by
        intro y; cases t <;> try rfl
        all_goals (rename_i w; cases w <;> rfl)
      rw [this]; exact .poison _
    | ptr p => exact Refines.refl _
    | int w x => exact Refines.refl _
    | bool => exact Refines.refl _
    | empty => exact Refines.refl _
    | mem hm =>
      have : ∀ (m : Mem) (y : Val), PtrOps.convert t [.mem m, y] = .mem m := by
        intro m y; cases t <;> try rfl
        all_goals (rename_i w; cases w <;> rfl)
      rw [this, this]; exact .mem hm
    | tuple ht =>
      have : ∀ (vs : List Val) (y : Val), PtrOps.convert t [.tuple vs, y] = .tuple vs := by
        intro vs y; cases t <;> try rfl
        all_goals (rename_i w; cases w <;> rfl)
      rw [this, this]; exact .tuple ht
    | agg ht =>
      have : ∀ (vs : List Val) (y : Val), PtrOps.convert t [.agg vs, y] = .agg vs := by
        intro vs y; cases t <;> try rfl
        all_goals (rename_i w; cases w <;> rfl)
      rw [this, this]; exact .agg ht
    | blob hb =>
      have : ∀ (bs : List Byte) (y : Val), PtrOps.convert t [.blob bs, y] = .blob bs := by
        intro bs y; cases t <;> try rfl
        all_goals (rename_i w; cases w <;> rfl)
      rw [this, this]; exact .blob hb
  | .cons _ (.cons _ (.cons _ _)) => by simp only [PtrOps.convert]; exact .poison _

theorem PtrOps.eqFirst_mono (neg : Bool) : RefinesList as bs → Refines (PtrOps.eqFirst neg as) (PtrOps.eqFirst neg bs)
  | .nil => by simp only [PtrOps.eqFirst]; exact .poison _
  | .cons _ .nil => by simp only [PtrOps.eqFirst]; exact .poison _
  | .cons h (.cons h' .nil) => by
    cases h with
    | agg hl =>
      cases hl with
      | nil => exact .poison _
      | @cons a _ _ _ ha _ =>
        cases h' with
        | agg hl' =>
          cases hl' with
          | nil => exact .poison _
          | @cons c _ _ _ hc _ =>
            simp only [PtrOps.eqFirst]
            cases hpa : a.asPtrWord with
            | none => exact .poison _
            | some x =>
              cases hpc : c.asPtrWord with
              | none => exact .poison _
              | some y => rw [ha.asPtrWord hpa, hc.asPtrWord hpc]; exact Refines.refl _
        | poison => exact .poison _
        | _ => exact .poison _
    | poison => exact .poison _
    | _ => exact .poison _
  | .cons _ (.cons _ (.cons _ _)) => by simp only [PtrOps.eqFirst]; exact .poison _

theorem loadOp_mono (t : Ty) : RefinesList as bs → Refines (loadOp t as) (loadOp t bs)
  | .nil => by simp only [loadOp]; exact .poison _
  | .cons _ .nil => by simp only [loadOp]; exact .poison _
  | .cons h (.cons h' .nil) => by
    cases h with
    | ptr p =>
      cases h' with
      | mem hm => exact load_mono hm t p
      | poison => exact .poison _
      | _ => exact .poison _
    | poison => exact .poison _
    | _ => exact .poison _
  | .cons _ (.cons _ (.cons _ _)) => by simp only [loadOp]; exact .poison _

theorem atomicLoad_mono (t : Ty) : RefinesList as bs → Refines (atomicLoad t as) (atomicLoad t bs)
  | .nil => by simp only [atomicLoad]; exact .poison _
  | .cons _ .nil => by simp only [atomicLoad]; exact .poison _
  | .cons h (.cons h' .nil) => by
    cases h with
    | ptr p =>
      cases h' with
      | @mem m m' hm =>
        simp only [atomicLoad]
        split
        · next vt =>
          refine .tuple (.cons ?_ (.cons (.mem hm) .nil))
          split
          · exact .poison _
          · exact load_mono hm vt p
        · exact .poison _
      | poison => exact .poison _
      | _ => exact .poison _
    | poison => exact .poison _
    | _ => exact .poison _
  | .cons _ (.cons _ (.cons _ _)) => by simp only [atomicLoad]; exact .poison _

theorem wbOp_mono (n : Int64) : RefinesList as bs → Refines (wbOp n as) (wbOp n bs)
  | .nil => by simp only [wbOp]; exact .poison _
  | .cons h .nil => by
    cases h with
    | @mem m m' hm =>
      simp only [wbOp, Mem.wbAlloc]
      exact .tuple (.cons (.ptr _) (.cons (.mem (hm.set _ (Alloc.Refines.refl _))) .nil))
    | poison => exact .poison _
    | _ => exact .poison _
  | .cons _ (.cons _ _) => by simp only [wbOp]; exact .poison _

theorem memEq_mono : RefinesList as bs → Refines (memEq as) (memEq bs)
  | .nil => by simp only [memEq]; exact .poison _
  | .cons _ .nil => by simp only [memEq]; exact .poison _
  | .cons _ (.cons _ .nil) => by simp only [memEq]; exact .poison _
  | .cons _ (.cons _ (.cons _ .nil)) => by simp only [memEq]; exact .poison _
  | .cons h1 (.cons h2 (.cons h3 (.cons h4 .nil))) => by
    cases h1 with
    | ptr p =>
      cases h2 with
      | ptr q =>
        cases h3 with
        | int w n =>
          cases h4 with
          | @mem m m' hm =>
            simp only [memEq]
            cases ha : m.read p n.toNat with
            | none => exact .poison _
            | some x =>
              cases hb : m.read q n.toNat with
              | none => exact .poison _
              | some y =>
                obtain ⟨x', hx', hxr⟩ := hm.read ha
                obtain ⟨y', hy', hyr⟩ := hm.read hb
                rw [hx', hy']
                dsimp only
                by_cases hp : (x.any (· == .poison) || y.any (· == .poison)) = true
                · simp only [hp, ite_true]; exact .poison _
                · have hpx : ∀ z ∈ x.toList, z ≠ .poison := by
                    intro z hz hzp; subst hzp
                    exact hp (by simp only [Bool.or_eq_true, Array.any_eq_true']; exact .inl ⟨_, by simpa using hz, rfl⟩)
                  have hpy : ∀ z ∈ y.toList, z ≠ .poison := by
                    intro z hz hzp; subst hzp
                    exact hp (by simp only [Bool.or_eq_true, Array.any_eq_true']; exact .inr ⟨_, by simpa using hz, rfl⟩)
                  rw [← hxr.eq hpx, ← hyr.eq hpy]
                  exact Refines.refl _
          | poison => exact .poison _
          | _ => exact .poison _
        | poison => exact .poison _
        | _ => exact .poison _
      | poison => exact .poison _
      | _ => exact .poison _
    | poison => exact .poison _
    | _ => exact .poison _
  | .cons _ (.cons _ (.cons _ (.cons _ (.cons _ _)))) => by simp only [memEq]; exact .poison _

/-! ## `evalPure` -/

theorem slicemask_case (h : RefinesList as bs) {o : Option Width} :
    Refines (match o with | some w => Int.slicemask w as | none => .poison)
      (match o with | some w => Int.slicemask w bs | none => .poison) := by
  cases o with
  | none => exact .poison _
  | some w => exact int1_mono _ _ h

theorem copy_case : RefinesList as bs →
    Refines (match as with | [x] => x | _ => .poison) (match bs with | [x] => x | _ => .poison)
  | .nil => .poison _
  | .cons h .nil => h
  | .cons _ (.cons _ _) => .poison _

/-- **The pure ops are monotone**: refined arguments give a refined result. -/
theorem evalPure_mono (op : Op) (ty : Ty) (auxInt : Int64) (aux : Option AuxRef)
    (h : RefinesList as bs) : Refines (evalPure op ty auxInt aux as) (evalPure op ty auxInt aux bs) := by
  cases op
  case Add8 => exact int2_mono _ _ h
  case Sub8 => exact int2_mono _ _ h
  case Mul8 => exact int2_mono _ _ h
  case And8 => exact int2_mono _ _ h
  case Or8 => exact int2_mono _ _ h
  case Xor8 => exact int2_mono _ _ h
  case Neg8 => exact int1_mono _ _ h
  case Com8 => exact int1_mono _ _ h
  case Add16 => exact int2_mono _ _ h
  case Sub16 => exact int2_mono _ _ h
  case Mul16 => exact int2_mono _ _ h
  case And16 => exact int2_mono _ _ h
  case Or16 => exact int2_mono _ _ h
  case Xor16 => exact int2_mono _ _ h
  case Neg16 => exact int1_mono _ _ h
  case Com16 => exact int1_mono _ _ h
  case Add32 => exact int2_mono _ _ h
  case Sub32 => exact int2_mono _ _ h
  case Mul32 => exact int2_mono _ _ h
  case And32 => exact int2_mono _ _ h
  case Or32 => exact int2_mono _ _ h
  case Xor32 => exact int2_mono _ _ h
  case Neg32 => exact int1_mono _ _ h
  case Com32 => exact int1_mono _ _ h
  case Add64 => exact int2_mono _ _ h
  case Sub64 => exact int2_mono _ _ h
  case Mul64 => exact int2_mono _ _ h
  case And64 => exact int2_mono _ _ h
  case Or64 => exact int2_mono _ _ h
  case Xor64 => exact int2_mono _ _ h
  case Neg64 => exact int1_mono _ _ h
  case Com64 => exact int1_mono _ _ h
  case Hmul32 => exact int2_mono _ _ h
  case Hmul32u => exact int2_mono _ _ h
  case Mul32uhilo => exact int2_mono _ _ h
  case Mul32uover => exact int2_mono _ _ h
  case Hmul64 => exact int2_mono _ _ h
  case Hmul64u => exact int2_mono _ _ h
  case Mul64uhilo => exact int2_mono _ _ h
  case Mul64uover => exact int2_mono _ _ h
  case Avg64u => exact int2_mono _ _ h
  case Div8 => exact int2_mono _ _ h
  case Div8u => exact int2_mono _ _ h
  case Mod8 => exact int2_mono _ _ h
  case Mod8u => exact int2_mono _ _ h
  case Div16 => exact int2_mono _ _ h
  case Div16u => exact int2_mono _ _ h
  case Mod16 => exact int2_mono _ _ h
  case Mod16u => exact int2_mono _ _ h
  case Div32 => exact int2_mono _ _ h
  case Div32u => exact int2_mono _ _ h
  case Mod32 => exact int2_mono _ _ h
  case Mod32u => exact int2_mono _ _ h
  case Div64 => exact int2_mono _ _ h
  case Div64u => exact int2_mono _ _ h
  case Mod64 => exact int2_mono _ _ h
  case Mod64u => exact int2_mono _ _ h
  case Div128u => exact int3_mono _ _ h
  case Lsh8x8 => exact Shift.shift_mono _ _ _ _ h
  case Rsh8x8 => exact Shift.shift_mono _ _ _ _ h
  case Rsh8Ux8 => exact Shift.shift_mono _ _ _ _ h
  case Lsh8x16 => exact Shift.shift_mono _ _ _ _ h
  case Rsh8x16 => exact Shift.shift_mono _ _ _ _ h
  case Rsh8Ux16 => exact Shift.shift_mono _ _ _ _ h
  case Lsh8x32 => exact Shift.shift_mono _ _ _ _ h
  case Rsh8x32 => exact Shift.shift_mono _ _ _ _ h
  case Rsh8Ux32 => exact Shift.shift_mono _ _ _ _ h
  case Lsh8x64 => exact Shift.shift_mono _ _ _ _ h
  case Rsh8x64 => exact Shift.shift_mono _ _ _ _ h
  case Rsh8Ux64 => exact Shift.shift_mono _ _ _ _ h
  case Lsh16x8 => exact Shift.shift_mono _ _ _ _ h
  case Rsh16x8 => exact Shift.shift_mono _ _ _ _ h
  case Rsh16Ux8 => exact Shift.shift_mono _ _ _ _ h
  case Lsh16x16 => exact Shift.shift_mono _ _ _ _ h
  case Rsh16x16 => exact Shift.shift_mono _ _ _ _ h
  case Rsh16Ux16 => exact Shift.shift_mono _ _ _ _ h
  case Lsh16x32 => exact Shift.shift_mono _ _ _ _ h
  case Rsh16x32 => exact Shift.shift_mono _ _ _ _ h
  case Rsh16Ux32 => exact Shift.shift_mono _ _ _ _ h
  case Lsh16x64 => exact Shift.shift_mono _ _ _ _ h
  case Rsh16x64 => exact Shift.shift_mono _ _ _ _ h
  case Rsh16Ux64 => exact Shift.shift_mono _ _ _ _ h
  case Lsh32x8 => exact Shift.shift_mono _ _ _ _ h
  case Rsh32x8 => exact Shift.shift_mono _ _ _ _ h
  case Rsh32Ux8 => exact Shift.shift_mono _ _ _ _ h
  case Lsh32x16 => exact Shift.shift_mono _ _ _ _ h
  case Rsh32x16 => exact Shift.shift_mono _ _ _ _ h
  case Rsh32Ux16 => exact Shift.shift_mono _ _ _ _ h
  case Lsh32x32 => exact Shift.shift_mono _ _ _ _ h
  case Rsh32x32 => exact Shift.shift_mono _ _ _ _ h
  case Rsh32Ux32 => exact Shift.shift_mono _ _ _ _ h
  case Lsh32x64 => exact Shift.shift_mono _ _ _ _ h
  case Rsh32x64 => exact Shift.shift_mono _ _ _ _ h
  case Rsh32Ux64 => exact Shift.shift_mono _ _ _ _ h
  case Lsh64x8 => exact Shift.shift_mono _ _ _ _ h
  case Rsh64x8 => exact Shift.shift_mono _ _ _ _ h
  case Rsh64Ux8 => exact Shift.shift_mono _ _ _ _ h
  case Lsh64x16 => exact Shift.shift_mono _ _ _ _ h
  case Rsh64x16 => exact Shift.shift_mono _ _ _ _ h
  case Rsh64Ux16 => exact Shift.shift_mono _ _ _ _ h
  case Lsh64x32 => exact Shift.shift_mono _ _ _ _ h
  case Rsh64x32 => exact Shift.shift_mono _ _ _ _ h
  case Rsh64Ux32 => exact Shift.shift_mono _ _ _ _ h
  case Lsh64x64 => exact Shift.shift_mono _ _ _ _ h
  case Rsh64x64 => exact Shift.shift_mono _ _ _ _ h
  case Rsh64Ux64 => exact Shift.shift_mono _ _ _ _ h
  case Eq8 => exact int2_mono _ _ h
  case Neq8 => exact int2_mono _ _ h
  case Less8 => exact int2_mono _ _ h
  case Less8U => exact int2_mono _ _ h
  case Leq8 => exact int2_mono _ _ h
  case Leq8U => exact int2_mono _ _ h
  case Eq16 => exact int2_mono _ _ h
  case Neq16 => exact int2_mono _ _ h
  case Less16 => exact int2_mono _ _ h
  case Less16U => exact int2_mono _ _ h
  case Leq16 => exact int2_mono _ _ h
  case Leq16U => exact int2_mono _ _ h
  case Eq32 => exact int2_mono _ _ h
  case Neq32 => exact int2_mono _ _ h
  case Less32 => exact int2_mono _ _ h
  case Less32U => exact int2_mono _ _ h
  case Leq32 => exact int2_mono _ _ h
  case Leq32U => exact int2_mono _ _ h
  case Eq64 => exact int2_mono _ _ h
  case Neq64 => exact int2_mono _ _ h
  case Less64 => exact int2_mono _ _ h
  case Less64U => exact int2_mono _ _ h
  case Leq64 => exact int2_mono _ _ h
  case Leq64U => exact int2_mono _ _ h
  case AndB => exact Cmp.andB_mono h
  case OrB => exact Cmp.orB_mono h
  case EqB => exact bool2_mono _ h
  case NeqB => exact bool2_mono _ h
  case Not => exact bool1_mono _ h
  case CondSelect => exact Cmp.condSelect_mono h
  case IsInBounds => exact Cmp.inBounds_mono _ h
  case IsSliceInBounds => exact Cmp.inBounds_mono _ h
  case SpectreIndex => exact Cmp.spectreIndex_mono _ h
  case SpectreSliceIndex => exact Cmp.spectreIndex_mono _ h
  case Ctz8 => exact int1_mono _ _ h
  case Ctz8NonZero => exact int1_mono _ _ h
  case BitLen8 => exact int1_mono _ _ h
  case PopCount8 => exact int1_mono _ _ h
  case BitRev8 => exact int1_mono _ _ h
  case RotateLeft8 => exact Int.rotateLeft_mono _ h
  case Ctz16 => exact int1_mono _ _ h
  case Ctz16NonZero => exact int1_mono _ _ h
  case BitLen16 => exact int1_mono _ _ h
  case PopCount16 => exact int1_mono _ _ h
  case BitRev16 => exact int1_mono _ _ h
  case RotateLeft16 => exact Int.rotateLeft_mono _ h
  case Bswap16 => exact int1_mono _ _ h
  case Ctz32 => exact int1_mono _ _ h
  case Ctz32NonZero => exact int1_mono _ _ h
  case BitLen32 => exact int1_mono _ _ h
  case PopCount32 => exact int1_mono _ _ h
  case BitRev32 => exact int1_mono _ _ h
  case RotateLeft32 => exact Int.rotateLeft_mono _ h
  case Bswap32 => exact int1_mono _ _ h
  case Ctz64 => exact int1_mono _ _ h
  case Ctz64NonZero => exact int1_mono _ _ h
  case BitLen64 => exact int1_mono _ _ h
  case PopCount64 => exact int1_mono _ _ h
  case BitRev64 => exact int1_mono _ _ h
  case RotateLeft64 => exact Int.rotateLeft_mono _ h
  case Bswap64 => exact int1_mono _ _ h
  case Min64 => exact int2_mono _ _ h
  case Min64u => exact int2_mono _ _ h
  case Max64 => exact int2_mono _ _ h
  case Max64u => exact int2_mono _ _ h
  case Add64carry => exact int3_mono _ _ h
  case Sub64borrow => exact int3_mono _ _ h
  case Slicemask => exact slicemask_case h
  case SignExt8to16 => exact int1_mono _ _ h
  case ZeroExt8to16 => exact int1_mono _ _ h
  case SignExt8to32 => exact int1_mono _ _ h
  case ZeroExt8to32 => exact int1_mono _ _ h
  case SignExt8to64 => exact int1_mono _ _ h
  case ZeroExt8to64 => exact int1_mono _ _ h
  case SignExt16to32 => exact int1_mono _ _ h
  case ZeroExt16to32 => exact int1_mono _ _ h
  case SignExt16to64 => exact int1_mono _ _ h
  case ZeroExt16to64 => exact int1_mono _ _ h
  case SignExt32to64 => exact int1_mono _ _ h
  case ZeroExt32to64 => exact int1_mono _ _ h
  case Trunc16to8 => exact int1_mono _ _ h
  case Trunc32to8 => exact int1_mono _ _ h
  case Trunc32to16 => exact int1_mono _ _ h
  case Trunc64to8 => exact int1_mono _ _ h
  case Trunc64to16 => exact int1_mono _ _ h
  case Trunc64to32 => exact int1_mono _ _ h
  case CvtBoolToUint8 => exact Conv.boolToUint8_mono h
  case Const8 => exact Refines.refl _
  case Const16 => exact Refines.refl _
  case Const32 => exact Refines.refl _
  case Const64 => exact Refines.refl _
  case ConstBool => exact Refines.refl _
  case Select0 => exact Tuple.select_mono _ h
  case SelectN => exact Tuple.selectN_mono _ h
  case SelectNAddr => exact Tuple.selectNAddr_mono _ h
  case Select1 => exact Tuple.select_mono _ h
  case MakeTuple => exact Tuple.make_mono h
  case Copy => exact copy_case h
  case MakeResult => exact .tuple h
  case OffPtr => exact PtrOps.offPtr_mono _ h
  case AddPtr => exact PtrOps.addPtr_mono h
  case PtrIndex => exact PtrOps.ptrIndex_mono _ h
  case SubPtr => exact PtrOps.subPtr_mono h
  case EqPtr => exact PtrOps.eqPtr_mono _ h
  case NeqPtr => exact PtrOps.eqPtr_mono _ h
  case IsNonNil => exact PtrOps.isNonNil_mono h
  case Convert => exact PtrOps.convert_mono _ h
  case EqInter => exact PtrOps.eqFirst_mono _ h
  case NeqInter => exact PtrOps.eqFirst_mono _ h
  case EqSlice => exact PtrOps.eqFirst_mono _ h
  case NeqSlice => exact PtrOps.eqFirst_mono _ h
  case StringMake => exact .agg h
  case SliceMake => exact .agg h
  case IMake => exact .agg h
  case ComplexMake => exact .agg h
  case StructMake => exact .agg h
  case ArrayMake1 => exact .agg h
  case StringPtr => exact Comp.select_mono _ h
  case SlicePtr => exact Comp.select_mono _ h
  case SlicePtrUnchecked => exact Comp.select_mono _ h
  case ITab => exact Comp.select_mono _ h
  case ComplexReal => exact Comp.select_mono _ h
  case StringLen => exact Comp.select_mono _ h
  case SliceLen => exact Comp.select_mono _ h
  case IData => exact Comp.select_mono _ h
  case ComplexImag => exact Comp.select_mono _ h
  case SliceCap => exact Comp.select_mono _ h
  case StructSelect => exact Comp.selectAux_mono _ h
  case ArraySelect => exact Comp.selectAux_mono _ h
  case ConstNil => exact Refines.refl _
  case ConstSlice => exact Refines.refl _
  case ConstInterface => exact Refines.refl _
  case Empty => exact Refines.refl _
  case HasCPUFeature => exact Refines.refl _
  case GetG => exact Refines.refl _
  case Load => exact loadOp_mono _ h
  case Dereference => exact loadOp_mono _ h
  case MemEq => exact memEq_mono h
  case AtomicLoadAcq64 => exact atomicLoad_mono _ h
  case WB => exact wbOp_mono _ h
  case AtomicLoad8 => exact atomicLoad_mono _ h
  case AtomicLoad32 => exact atomicLoad_mono _ h
  case AtomicLoad64 => exact atomicLoad_mono _ h
  case AtomicLoadPtr => exact atomicLoad_mono _ h
  case AtomicLoadAcq32 => exact atomicLoad_mono _ h
  case Add32F => exact int2_mono _ _ h
  case Add64F => exact int2_mono _ _ h
  case Sub32F => exact int2_mono _ _ h
  case Sub64F => exact int2_mono _ _ h
  case Mul32F => exact int2_mono _ _ h
  case Mul64F => exact int2_mono _ _ h
  case Div32F => exact int2_mono _ _ h
  case Div64F => exact int2_mono _ _ h
  case Eq32F => exact int2_mono _ _ h
  case Eq64F => exact int2_mono _ _ h
  case Neq32F => exact int2_mono _ _ h
  case Neq64F => exact int2_mono _ _ h
  case Less32F => exact int2_mono _ _ h
  case Less64F => exact int2_mono _ _ h
  case Leq32F => exact int2_mono _ _ h
  case Leq64F => exact int2_mono _ _ h
  case Min32F => exact int2_mono _ _ h
  case Min64F => exact int2_mono _ _ h
  case Max32F => exact int2_mono _ _ h
  case Max64F => exact int2_mono _ _ h
  case Copysign => exact int2_mono _ _ h
  case Neg32F => exact int1_mono _ _ h
  case Neg64F => exact int1_mono _ _ h
  case Sqrt => exact int1_mono _ _ h
  case Sqrt32 => exact int1_mono _ _ h
  case Floor => exact int1_mono _ _ h
  case Ceil => exact int1_mono _ _ h
  case Trunc => exact int1_mono _ _ h
  case Round => exact int1_mono _ _ h
  case RoundToEven => exact int1_mono _ _ h
  case Abs => exact int1_mono _ _ h
  case Round32F => exact int1_mono _ _ h
  case Round64F => exact int1_mono _ _ h
  case Cvt32to32F => exact int1_mono _ _ h
  case Cvt32to64F => exact int1_mono _ _ h
  case Cvt64to32F => exact int1_mono _ _ h
  case Cvt64to64F => exact int1_mono _ _ h
  case Cvt32Uto32F => exact int1_mono _ _ h
  case Cvt32Uto64F => exact int1_mono _ _ h
  case Cvt64Uto32F => exact int1_mono _ _ h
  case Cvt64Uto64F => exact int1_mono _ _ h
  case Cvt32Fto32 => exact int1_mono _ _ h
  case Cvt32Fto64 => exact int1_mono _ _ h
  case Cvt64Fto32 => exact int1_mono _ _ h
  case Cvt64Fto64 => exact int1_mono _ _ h
  case Cvt32Fto32U => exact int1_mono _ _ h
  case Cvt32Fto64U => exact int1_mono _ _ h
  case Cvt64Fto32U => exact int1_mono _ _ h
  case Cvt64Fto64U => exact int1_mono _ _ h
  case Cvt32Fto64F => exact int1_mono _ _ h
  case Cvt64Fto32F => exact int1_mono _ _ h
  case FMA => exact int3_mono _ _ h
  case Const32F => exact Refines.refl _
  case Const64F => exact Refines.refl _
  all_goals exact .poison _

end GoFV.SSA.Sem

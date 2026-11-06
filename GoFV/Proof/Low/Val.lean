import GoFV.Proof.Low.ValReplay

/-!
# Soundness of the lowering validator at the term level (issue #385)

`validateL_termRef`: if `GoFV.Opt.LowerCheck.validateL` accepts the output `g` of a lowering
rewrite run with the table of a sound lowering rule set (`ArmRuleSet.AllSound`) on `f`, then the
arguments of `g`'s atoms refine, as terms over the atoms in lowered mode, those of the atoms of `f`
they correspond to (`AtomArgsRefL`), and `g`'s terminators refine `f`'s as functions of their
controls' terms (`TermStepRefL`): the premises of the atom simulation. `validateL_parts`: the
other facts `validateL` checks.

Proof (as Phase 1's `GoFV.Proof.Pass.Rewrite.validate_termRef`): `f` is read in its own mode
(`f.lowered`); the valuation `midVal` shapes `f`'s atoms by `Val.retypeL` at their lowered shapes,
so that `f`'s denotations refine their lowered reading (`bridge_den`: `shapesOK` makes the
shapes agree, `retype_le_retypeL`). Along the replay the listed values of `f` keep refining
lowered denotations (`replayL_inv`); the final definitions and terminators are `g`'s up to copies
(`finalOKL`), whose lowered denotation over the listed values of `g` refines theirs
(`final_denL`); `midVal` at an atom listed in `g` is refined by the target valuation, since the
atom of `g` has the type of `f`'s (`atomsOKL`, `mid_le_target`).
-/

namespace GoFV.Proof.Low.Val

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Opt.RewriteCheck GoFV.Opt.LowerCheck GoFV.Proof.Term
open GoFV.Proof.Low
open GoFV.Proof.Pass.Rewrite (LM Marked listedMarks_sound listedDefs_of_marked closedOK_facts
  marked_closed zip_all_get zip_all_get' refinesList_idx toList_of_size_one)

/-! ## `atomsOKL`, `liveOKL`, `finalOKL` -/

theorem termVL_congr {tabs : Tables} {u m : Value} (hop : u.op = m.op) (hai : u.auxInt = m.auxInt)
    (hax : u.aux = m.aux) : termVL tabs u = termVL tabs m := by
  unfold termVL; rw [hop, hai, hax]

/-! ## An extension's argument through a narrowing copy (`truncReachL`) -/

/-- The low `k ≤ w` bits of a `w`-bit truncation are the value's. -/
theorem and_mask_setWidth {n : Nat} (k w : Nat) (hk : k ≤ w) (x : BitVec n) :
    (x.setWidth w).setWidth 64 &&& Arm64.mask k = x.setWidth 64 &&& Arm64.mask k := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_setWidth, Arm64.mask, ← BitVec.getLsbD_eq_getElem]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one]
  by_cases hik : i < k
  · have : i < w := by omega
    simp [this, hik]
  · simp [hik]

/-- Zero-extending to `w ≥ n` bits, then to 64, is zero-extending to 64. -/
theorem setWidth_setWidth_wide {n : Nat} (w m : Nat) (hn : n ≤ w) (x : BitVec n) :
    (x.setWidth w).setWidth m = x.setWidth m := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_setWidth]
  by_cases h : i < w
  · simp [h]
  · have : x.getLsbD i = false := BitVec.getLsbD_of_ge x i (by omega)
    simp [h, this]

/-- An extension of the low `k ≤ w` bits reads the same bits of a `w`-bit truncation. -/
theorem ext_setWidth {n : Nat} (s : Bool) (k w : Nat) (hk : k ≤ w) (x : BitVec n) :
    Arm64.ext s k ((x.setWidth w).setWidth 64) = Arm64.ext s k (x.setWidth 64) := by
  unfold Arm64.ext Arm64.sext
  rw [and_mask_setWidth k w hk]

/-- **An extension of the low `k` bits of a register refines through a narrowing to `w ≥ k`
bits** (`Val.retypeL` at `int w`, `w < 64`: the value's low `w` bits, `poison` for a pointer). -/
theorem op1_ext_retypeL (s : Bool) (k : Nat) {w : Width} (hk : k ≤ w.bits) (hw : w ≠ .w64)
    (ty : Ty) (B : Val) :
    Sem.Refines (Arm64.op1 ty (Arm64.ext s k) [B.retypeL (.int w)])
      (Arm64.op1 ty (Arm64.ext s k) [B]) := by
  cases B with
  | int w' x =>
    by_cases hlt : w'.bits < w.bits
    · have : (Val.int w' x).retypeL (.int w) = .int w (x.setWidth w.bits) := by
        unfold Val.retypeL Val.widen
        rw [if_pos hlt]
        unfold Val.retype
        rw [if_pos (Nat.le_refl _), BitVec.setWidth_eq]
      rw [this]
      simp only [Arm64.op1, Arm64.reg]
      rw [setWidth_setWidth_wide _ _ (by omega)]
      exact Sem.Refines.refl _
    · have hle : w.bits ≤ w'.bits := by omega
      have : (Val.int w' x).retypeL (.int w) = .int w (x.setWidth w.bits) := by
        unfold Val.retypeL Val.widen
        rw [if_neg hlt]
        unfold Val.retype
        rw [if_pos hle]
      rw [this]
      simp only [Arm64.op1, Arm64.reg]
      rw [ext_setWidth s k w.bits hk]
      exact Sem.Refines.refl _
  | bool b =>
    have : (Val.bool b).retypeL (.int w) = .int w (if b then 1 else 0) := by
      simp [Val.retypeL, Val.widen, Val.retype]
    rw [this]
    cases w <;> cases b <;> first | exact absurd rfl hw | exact Sem.Refines.refl _
  | ptr p =>
    have : (Val.ptr p).retypeL (.int w) = .poison := by
      cases w <;> simp_all [Val.retypeL, Val.widen, Val.retype]
    rw [this]; exact .poison _
  | _ => simp [Val.retypeL, Val.widen, Val.retype, Arm64.op1, Arm64.reg]; exact .poison _

theorem extReadW_mem {o : Op} {k : Nat} (h : extReadW o = some k) :
    (o = .ARM64MOVBreg ∧ k = 8) ∨ (o = .ARM64MOVBUreg ∧ k = 8) ∨ (o = .ARM64MOVHreg ∧ k = 16) ∨
      (o = .ARM64MOVHUreg ∧ k = 16) ∨ (o = .ARM64MOVWreg ∧ k = 32) ∨ (o = .ARM64MOVWUreg ∧ k = 32) := by
  unfold extReadW at h
  split at h <;> simp_all

theorem extReadW_cases {o : Op} {k : Nat} (h : extReadW o = some k) :
    ∃ s, (∀ ty ai (ax : Option AuxRef) args,
        Arm64.evalPure o ty ai ax args = Arm64.op1 ty (Arm64.ext s k) args) ∧
      o.generic = false ∧ (o == .ARM64MOVDaddr) = false ∧ ldOp? o = none ∧
      (GoFV.Opt.LowerTerm.armTerm o && !GoFV.Opt.LowerTerm.actOp o && !isRoot o) = true := by
  rcases extReadW_mem h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩
  · exact ⟨true, fun _ _ _ _ => rfl, by decide, by decide, by decide, by decide⟩
  · exact ⟨false, fun _ _ _ _ => rfl, by decide, by decide, by decide, by decide⟩
  · exact ⟨true, fun _ _ _ _ => rfl, by decide, by decide, by decide, by decide⟩
  · exact ⟨false, fun _ _ _ _ => rfl, by decide, by decide, by decide, by decide⟩
  · exact ⟨true, fun _ _ _ _ => rfl, by decide, by decide, by decide, by decide⟩
  · exact ⟨false, fun _ _ _ _ => rfl, by decide, by decide, by decide, by decide⟩

/-- An extension is a term (`armTerm`), whose `opValL` is `Arm64.ext` of its register. -/
theorem opValL_ext {o : Op} {k : Nat} (h : extReadW o = some k) :
    ∃ s, ∀ tabs ty ai ax args, opValL tabs o ty ai ax args = Arm64.op1 ty (Arm64.ext s k) args := by
  obtain ⟨s, he, hg, hm, hl, -⟩ := extReadW_cases h
  exact ⟨s, fun tabs ty ai ax args => by
    simp only [opValL, hg, hm, hl, Bool.false_eq_true, ite_false]; exact he ty ai ax args⟩

theorem termVL_ext {tabs : Tables} {v : Value} {k : Nat} (h : extReadW v.op = some k) :
    termVL tabs v = true := by
  obtain ⟨-, -, hg, hm, hl, ht⟩ := extReadW_cases h
  have hact : GoFV.Opt.LowerTerm.actOp v.op = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at ht; exact ht.1.2
  simp only [termVL, hg, hm, hl, pureActOp_of_act hact, Option.isSome_none, Bool.false_eq_true,
    ite_false, ht]

theorem w32Op_mem {o : Op} (h : w32Op o = true) :
    o = .ARM64MULW ∨ o = .ARM64MNEGW ∨ o = .ARM64DIVW ∨ o = .ARM64UDIVW ∨ o = .ARM64MODW ∨
      o = .ARM64UMODW ∨ o = .ARM64RORW ∨ o = .ARM64RORWconst ∨ o = .ARM64EXTRWconst ∨
      o = .ARM64CLZW ∨ o = .ARM64RBITW ∨ o = .ARM64REVW ∨ o = .ARM64REV16W ∨ o = .ARM64CMPW ∨
      o = .ARM64CMPWconst ∨ o = .ARM64CMNW ∨ o = .ARM64CMNWconst ∨ o = .ARM64TSTW ∨
      o = .ARM64TSTWconst := by
  unfold w32Op at h
  split at h <;> simp_all

/-- A `W` op is no extension and a term (`armTerm`) whose `opValL` is `Arm64.evalPure`. -/
theorem w32Op_cases {o : Op} (h : w32Op o = true) :
    extReadW o = none ∧ o.generic = false ∧ (o == .ARM64MOVDaddr) = false ∧ ldOp? o = none ∧
      (GoFV.Opt.LowerTerm.armTerm o && !GoFV.Opt.LowerTerm.actOp o && !isRoot o) = true := by
  rcases w32Op_mem h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨rfl, by decide, by decide, by decide, by decide⟩

theorem opValL_w32 {o : Op} (h : w32Op o = true) (tabs : Tables) (ty : Ty) (ai : Int64)
    (ax : Option AuxRef) (args : List Val) :
    opValL tabs o ty ai ax args = Arm64.evalPure o ty ai ax args := by
  obtain ⟨-, hg, hm, hl, -⟩ := w32Op_cases h
  simp only [opValL, hg, hm, hl, Bool.false_eq_true, ite_false]

theorem narrowReadW_cases {o : Op} {i k : Nat} (h : narrowReadW o i = some k) :
    (extReadW o = some k ∧ i = 0) ∨ (w32Op o = true ∧ k = 32) := by
  unfold narrowReadW at h
  cases he : extReadW o with
  | some k' =>
    rw [he] at h
    by_cases hi : i = 0
    · subst hi; cases h; exact .inl ⟨rfl, rfl⟩
    · simp [hi] at h
  | none =>
    rw [he] at h
    cases hw : w32Op o
    · simp [hw] at h
    · simp only [hw, ite_true, Option.some.injEq] at h
      exact .inr ⟨rfl, h.symm⟩

/-- An op reading narrow bits of an argument (`narrowReadW`) is a term. -/
theorem termVL_narrow {tabs : Tables} {v : Value} {i k : Nat} (h : narrowReadW v.op i = some k) :
    termVL tabs v = true := by
  rcases narrowReadW_cases h with ⟨hk, -⟩ | ⟨hw, -⟩
  · exact termVL_ext hk
  · obtain ⟨-, hg, hm, hl, ht⟩ := w32Op_cases hw
    have hact : GoFV.Opt.LowerTerm.actOp v.op = false := by
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at ht; exact ht.1.2
    simp only [termVL, hg, hm, hl, pureActOp_of_act hact, Option.isSome_none, Bool.false_eq_true,
      ite_false, ht]

/-- What `truncReachL` says. -/
theorem truncReachL_cases {tabs : Tables} {M : Defs} {n : Nat} {o : Op} {i : Nat} {a a' : ID}
    (h : truncReachL tabs M n o i a a' = true) :
    ∃ k c w, narrowReadW o i = some k ∧ M.get? a = some c ∧ c.op = .Copy ∧ c.args.size = 1 ∧
      shpL tabs c.type = .int w ∧ k ≤ w.bits ∧ w ≠ .w64 ∧
      copyReachL tabs M n c.args[0]! a' = true := by
  unfold truncReachL at h
  simp only [Option.any_eq_true] at h
  obtain ⟨k, hk, h⟩ := h
  split at h
  · rename_i c hc
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hop, hsz⟩, hsh⟩, hr⟩ := h
    split at hsh
    · rename_i w hw
      simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hsh
      exact ⟨k, c, w, hk, hc, hop, hsz, hw, hsh.1, hsh.2, hr⟩
    · cases hsh
  · cases h

/-! ## A `W` op reads the low 32 bits of each argument -/

/-- `b`'s `W` register is `a`'s wherever `a` has one. -/
def R32 (a b : Val) : Prop := ∀ x, Arm64.reg32 a = some x → Arm64.reg32 b = some x

/-- `R32` pairwise. -/
inductive R32List : List Val → List Val → Prop
  | nil : R32List [] []
  | cons {a b : Val} {as bs : List Val} : R32 a b → R32List as bs → R32List (a :: as) (b :: bs)

theorem r32List_idx {α β : Type} {F : α → Val} {G : β → Val} :
    ∀ {l : List α} {m : List β}, l.length = m.length →
      (∀ j (h1 : j < l.length) (h2 : j < m.length), R32 (F l[j]) (G m[j])) →
      R32List (l.map F) (m.map G)
  | [], [], _, _ => .nil
  | _ :: _, _ :: _, hl, h => .cons (h 0 (by simp) (by simp))
      (r32List_idx (by simpa using hl) fun j h1 h2 => h (j + 1) (by simpa using h1) (by simpa using h2))
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => by simp at hl

/-- A narrowing to 32 bits keeps the `W` register. -/
theorem reg32_retypeL_w32 {X : Val} {x : BitVec 32}
    (h : Arm64.reg32 (X.retypeL (.int .w32)) = some x) : Arm64.reg32 X = some x := by
  cases X with
  | int w v =>
    cases w <;> simp_all [Val.retypeL, Val.widen, Val.retype, Arm64.reg32, Arm64.reg, Width.bits,
      setWidth_setWidth_wide, BitVec.setWidth_setWidth_of_le]
  | bool b => cases b <;> simp_all [Val.retypeL, Val.widen, Val.retype, Arm64.reg32, Arm64.reg]
  | _ => simp [Val.retypeL, Val.widen, Val.retype, Arm64.reg32, Arm64.reg] at h

section
variable {as bs : List Val}

theorem op1w_r32 (ty : Ty) (f : BitVec 32 → BitVec 32) :
    R32List as bs → Sem.Refines (Arm64.op1w ty f as) (Arm64.op1w ty f bs)
  | .nil => .poison _
  | .cons (a := a) h .nil => by
    simp only [Arm64.op1w]
    cases ha : Arm64.reg32 a with
    | none => exact .poison _
    | some x => rw [h x ha]; exact Sem.Refines.refl _
  | .cons _ (.cons _ _) => .poison _

theorem op2w_r32 (ty : Ty) (f : BitVec 32 → BitVec 32 → BitVec 32) :
    R32List as bs → Sem.Refines (Arm64.op2w ty f as) (Arm64.op2w ty f bs)
  | .nil => .poison _
  | .cons _ .nil => .poison _
  | .cons (a := a) h (.cons (a := c) h' .nil) => by
    simp only [Arm64.op2w]
    cases ha : Arm64.reg32 a with
    | none => exact .poison _
    | some x =>
      cases hc : Arm64.reg32 c with
      | none => exact .poison _
      | some y => rw [h x ha, h' y hc]; exact Sem.Refines.refl _
  | .cons _ (.cons _ (.cons _ _)) => .poison _

theorem cmp1w_r32 (f : BitVec 32 → BitVec 32 × Flags) :
    R32List as bs → Sem.Refines (Arm64.cmp1w f as) (Arm64.cmp1w f bs)
  | .nil => .poison _
  | .cons (a := a) h .nil => by
    simp only [Arm64.cmp1w]
    cases ha : Arm64.reg32 a with
    | none => exact .poison _
    | some x => rw [h x ha]; exact Sem.Refines.refl _
  | .cons _ (.cons _ _) => .poison _

theorem cmp2w_r32 (f : BitVec 32 → BitVec 32 → BitVec 32 × Flags) :
    R32List as bs → Sem.Refines (Arm64.cmp2w f as) (Arm64.cmp2w f bs)
  | .nil => .poison _
  | .cons _ .nil => .poison _
  | .cons (a := a) h (.cons (a := c) h' .nil) => by
    simp only [Arm64.cmp2w]
    cases ha : Arm64.reg32 a with
    | none => exact .poison _
    | some x =>
      cases hc : Arm64.reg32 c with
      | none => exact .poison _
      | some y => rw [h x ha, h' y hc]; exact Sem.Refines.refl _
  | .cons _ (.cons _ (.cons _ _)) => .poison _

theorem flags1w_r32 (f : BitVec 32 → Flags) :
    R32List as bs → Sem.Refines (Arm64.flags1w f as) (Arm64.flags1w f bs)
  | .nil => .poison _
  | .cons (a := a) h .nil => by
    simp only [Arm64.flags1w]
    cases ha : Arm64.reg32 a with
    | none => exact .poison _
    | some x => rw [h x ha]; exact Sem.Refines.refl _
  | .cons _ (.cons _ _) => .poison _

theorem flags2w_r32 (f : BitVec 32 → BitVec 32 → Flags) :
    R32List as bs → Sem.Refines (Arm64.flags2w f as) (Arm64.flags2w f bs)
  | .nil => .poison _
  | .cons _ .nil => .poison _
  | .cons (a := a) h (.cons (a := c) h' .nil) => by
    simp only [Arm64.flags2w]
    cases ha : Arm64.reg32 a with
    | none => exact .poison _
    | some x =>
      cases hc : Arm64.reg32 c with
      | none => exact .poison _
      | some y => rw [h x ha, h' y hc]; exact Sem.Refines.refl _
  | .cons _ (.cons _ (.cons _ _)) => .poison _

/-- **A `W` op is monotone in the low 32 bits of its arguments' registers.** -/
theorem w32_mono {o : Op} (ho : w32Op o = true) (ty : Ty) (k : Int64) (ax : Option AuxRef)
    (h : R32List as bs) : Sem.Refines (Arm64.evalPure o ty k ax as) (Arm64.evalPure o ty k ax bs) := by
  rcases w32Op_mem ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact op2w_r32 ty _ h
  · exact op2w_r32 ty _ h
  · exact op2w_r32 ty _ h
  · exact op2w_r32 ty _ h
  · exact op2w_r32 ty _ h
  · exact op2w_r32 ty _ h
  · exact op2w_r32 ty _ h
  · exact op1w_r32 ty _ h
  · exact op2w_r32 ty _ h
  · exact op1w_r32 ty _ h
  · exact op1w_r32 ty _ h
  · exact op1w_r32 ty _ h
  · exact op1w_r32 ty _ h
  · exact cmp2w_r32 _ h
  · exact cmp1w_r32 _ h
  · exact cmp2w_r32 _ h
  · exact cmp1w_r32 _ h
  · exact flags2w_r32 _ h
  · exact flags1w_r32 _ h

end

theorem atomsOKL_facts {tabs : Tables} {f g : Func} (h : atomsOKL tabs f g = true) :
    f.blocks = g.blocks ∧ ∀ b ∈ g.blocks, ∀ gb, g.block? b = some gb → ∃ fb, f.block? b = some fb ∧
      fb.id = gb.id ∧ ∀ x ∈ gb.values, ∀ w, g.value? x = some w → termVL tabs w = false →
        x ∈ fb.values ∧ ∃ u, f.value? x = some u ∧ atomPair tabs u w = true ∧
          pbConstOK tabs f u w = true ∧ termVL tabs u = false := by
  unfold atomsOKL at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨-, hbl⟩, -⟩, h⟩ := h
  refine ⟨hbl, fun b hb gb hgb => ?_⟩
  have := (Array.all_eq_true_iff_forall_mem.1 h) b (hbl ▸ hb)
  rw [hgb] at this
  split at this
  · rename_i fb gb' hfb hgb'
    obtain rfl := Option.some.inj hgb'
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at this
    obtain ⟨hid, ⟨hag, -⟩, -⟩ := this
    refine ⟨fb, hfb, hid, fun x hx w hw hwt => ?_⟩
    have hxa : x ∈ atomsOfL tabs g gb := by
      simp only [atomsOfL, List.mem_filter, Array.mem_toList_iff, hw, isAtomL, hwt]
      exact ⟨hx, rfl⟩
    have := hag x hxa
    simp only [List.contains_iff_mem] at this
    obtain ⟨hxf, hfd⟩ := this
    simp only [atomsOfL, List.mem_filter, Array.mem_toList_iff] at hxf
    obtain ⟨hxf, hat⟩ := hxf
    refine ⟨hxf, ?_⟩
    rw [hw] at hfd
    split at hfd
    · rename_i u w' hu hw'
      obtain rfl := Option.some.inj hw'
      rw [hu] at hat
      simp only [isAtomL, Bool.not_eq_true'] at hat
      simp only [Bool.and_eq_true] at hfd
      exact ⟨u, hu, hfd.1, hfd.2, hat⟩
    · cases hfd
  · cases this

theorem atomPair_type {tabs : Tables} {u w : Value} (h : atomPair tabs u w = true) :
    u.type = w.type := by
  unfold atomPair at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.2

/-- `x` is marked by `liveMarksL tabs h` (read by the output). -/
def LiveL (tabs : Tables) (h : Func) (x : ID) : Prop := (liveMarksL tabs h)[x]? = some true

theorem liveOKL_facts {tabs : Tables} {h : Func} {L : Array Bool} (hl : liveOKL tabs h L = true) :
    ∀ b ∈ h.blocks, ∀ hb, h.block? b = some hb → (∀ c ∈ hb.controls, L[c]? = some true) ∧
      ∀ x ∈ hb.values, ∀ u, h.value? x = some u → (termVL tabs u = false ∨ L[x]? = some true) →
        ∀ a ∈ u.args, L[a]? = some true := by
  intro b hb hbk hbb
  unfold liveOKL at hl
  have := (Array.all_eq_true_iff_forall_mem.1 hl) b hb
  simp only [hbb, Bool.and_eq_true] at this
  obtain ⟨h1, h2⟩ := this
  refine ⟨fun c hc => ?_, fun x hx u hu hlx a ha => ?_⟩
  · simpa using (Array.all_eq_true_iff_forall_mem.1 h1) c hc
  · have := (Array.all_eq_true_iff_forall_mem.1 h2) x hx
    simp only [hu, Option.all_some, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    rcases this with ⟨ht, hn⟩ | hall
    · rcases hlx with hlx | hlx
      · rw [hlx] at ht; cases ht
      · exact absurd hlx hn
    · simpa using (Array.all_eq_true_iff_forall_mem.1 hall) a ha

theorem finalOKL_facts {tabs : Tables} {f g : Func} {M : Defs} {B : BMapL}
    (h : finalOKL tabs f g M B = true) : liveOKL tabs g (liveMarksL tabs g) = true ∧
    ∀ b ∈ g.blocks, ∀ gb, g.block? b = some gb → ∃ st fb, bstateL f B b = some st ∧
      f.block? b = some fb ∧ gb.kind = st.kind ∧ gb.auxInt = st.auxInt ∧
      gb.succs = (if st.swapped then swapS fb.succs else fb.succs) ∧
      (st.swapped = true → fb.succs.size = 2) ∧ gb.controls.size = st.ctrls.size ∧
      (∀ k (h1 : k < st.ctrls.size) (h2 : k < gb.controls.size),
        copyReachL tabs M M.size st.ctrls[k] gb.controls[k] = true) ∧
      ∀ x ∈ gb.values, (LiveL tabs g x ∨ ∀ u, g.value? x = some u → termVL tabs u = false) →
        ∃ m u, M.get? x = some m ∧ g.value? x = some u ∧ u.type = m.type ∧ u.auxInt = m.auxInt ∧
        ((u.op = m.op ∧ u.aux = m.aux ∧ u.args.size = m.args.size ∧
          ∀ j (h1 : j < m.args.size) (h2 : j < u.args.size),
            copyReachL tabs M M.size m.args[j] u.args[j] = true ∨
              truncReachL tabs M M.size m.op j m.args[j] u.args[j] = true) ∨
         (m.op = .ARM64LoweredPanicBoundsRR ∧ m.args.size = 3 ∧ (f.value? x).any (pbLower · u) ∧
          ∃ ks, pbKeep u.op = some ks ∧ u.args.size = ks.length ∧
            ∀ j (h : j < ks.length), copyReachL tabs M M.size m.args[ks[j]]! u.args[j]! = true)) := by
  unfold finalOKL at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hlive, h⟩ := h
  refine ⟨hlive, fun b hb gb hgb => ?_⟩
  have := (Array.all_eq_true_iff_forall_mem.1 h) b hb
  split at this
  · rename_i st fb gb' hst hfb hgb'
    rw [hgb] at hgb'; obtain rfl := Option.some.inj hgb'
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    obtain ⟨⟨⟨⟨⟨hk, hai⟩, hsu⟩, hsz⟩, hc⟩, hv⟩ := this
    have hsu' : gb.succs = (if st.swapped then swapS fb.succs else fb.succs) ∧
        (st.swapped = true → fb.succs.size = 2) := by
      cases hsw : st.swapped <;> simp only [hsw, ite_true, ite_false, Bool.false_eq_true] at hsu ⊢
      · exact ⟨beq_iff_eq.1 hsu, fun h => h.elim⟩
      · simp only [Bool.and_eq_true, beq_iff_eq] at hsu
        exact ⟨hsu.2, fun _ => hsu.1⟩
    refine ⟨st, fb, hst, hfb, hk, hai, hsu'.1, hsu'.2, hsz, fun k h1 h2 => ?_, fun x hx hrd => ?_⟩
    · have := zip_all_get' (f := fun x : ID × ID => copyReachL tabs M M.size x.1 x.2) hc k
        (by simpa using h1) (by simpa using h2)
      simpa using this
    · have := (Array.all_eq_true_iff_forall_mem.1 hv) x hx
      split at this
      · rename_i m u hm hu
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at this
        rcases this with (this | ⟨ht, hr⟩) | hpb
        · obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, hop⟩, hty⟩, hai⟩, hax⟩, hsz⟩, hargs⟩ := this
          refine ⟨m, u, hm, hu, hty, hai, .inl ⟨hop, hax, hsz, fun j h1 h2 => ?_⟩⟩
          have := List.all_eq_true.1 hargs j (List.mem_range.2 h1)
          simpa [getElem!_pos m.args j h1, getElem!_pos u.args j h2] using this
        · rcases hrd with hrd | hrd
          · exact absurd hrd hr
          · rw [hrd u hu] at ht; cases ht
        · unfold pbFinal at hpb
          simp only [Bool.and_eq_true, beq_iff_eq] at hpb
          obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, hop⟩, hty⟩, hai⟩, hm3⟩, hpl⟩, hk⟩ := hpb
          refine ⟨m, u, hm, hu, hty, hai, .inr ⟨hop, hm3, hpl, ?_⟩⟩
          split at hk
          · rename_i ks hks
            simp only [Bool.and_eq_true, beq_iff_eq] at hk
            obtain ⟨hsz, hargs⟩ := hk
            refine ⟨ks, hks, hsz, fun j hj => ?_⟩
            have hj' : j < u.args.size := hsz ▸ hj
            have := zip_all_get (f := fun x : Nat × ID => copyReachL tabs M M.size m.args[x.1]! x.2)
              hargs (by simp [hsz]) j hj (by simpa using hj')
            simpa [getElem!_pos u.args j hj'] using this
          · cases hk
      · cases this
  · cases this

/-! ## The final definitions -/

/-- The replayed definitions refine, in lowered mode, those listed in `g` and read by `g` (up to
the copies `finalOKL` allows), for valuations related at `g`'s listed atoms. -/
theorem final_denL {tabs : Tables} {f g : Func} {M : Defs} {B : BMapL}
    (hfin : finalOKL tabs f g M B = true) (hcg : closedOK g = true) {ρ ρ' : ID → Val}
    (hρ : ∀ a u, listedDefs g a = some u → termVL tabs u = false → Sem.Refines (ρ a) (ρ' a))
    (hT : TypedL true M.get? tabs ρ) :
    ∀ n x, LM g x → LiveL tabs g x →
      Sem.Refines (denL true M.get? tabs ρ n x) (denL true (listedDefs g) tabs ρ' n x)
  | 0, _, _, _ => .poison _
  | n + 1, x, hx, hr => by
    have hmk := listedMarks_sound g x hx
    obtain ⟨b, hb, gb, hgb, hxv, -, -, -⟩ := id hmk
    obtain ⟨hlive, hfacts⟩ := finalOKL_facts hfin
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hvals⟩ := hfacts b hb gb hgb
    obtain ⟨m, u, hm, hu, hty, hai, hcase⟩ := hvals x hxv (.inl hr)
    have hL : listedDefs g x = some u := by rw [listedDefs_of_marked hmk, hu]
    rcases hcase with ⟨hop, hax, hsz, hargs⟩ | ⟨hop, -, -, ks, hks, -, -⟩
    case inr =>
      -- a bounds panic with constant operands: an atom on both sides
      have h1 : ¬ IsTermL tabs M.get? x := fun ⟨w, hw, hw'⟩ => by
        rw [Option.some.inj (hw.symm.trans hm),
          termVL_pb tabs m (o := .ARM64LoweredPanicBoundsRR) rfl hop] at hw'
        cases hw'
      have hut := termVL_pbKeep tabs u hks rfl
      have h2 : ¬ IsTermL tabs (listedDefs g) x := fun ⟨w, hw, hw'⟩ => by
        rw [hL] at hw; cases hw; rw [hut] at hw'; cases hw'
      rw [denL_succ_atom h1, denL_succ_atom h2]
      exact hρ x u hL hut
    have hcl := (closedOK_facts hcg b hb gb hgb).2 x hxv u hu
    have htt := termVL_congr (tabs := tabs) hop hai hax
    by_cases ht : termVL tabs m = true
    · rw [denT_succ hm ht, denT_succ hL (htt ▸ ht), hop, hty, hai, hax]
      apply retypeL_mono
      have hrec : ∀ j (h2 : j < u.args.size), Sem.Refines (denL true M.get? tabs ρ n u.args[j])
          (denL true (listedDefs g) tabs ρ' n u.args[j]) := fun j h2 =>
        final_denL hfin hcg hρ hT n _ (hcl _ (Array.getElem_mem h2))
          ((liveOKL_facts hlive) b hb gb hgb |>.2 x hxv u hu (.inr hr) _ (Array.getElem_mem h2))
      by_cases hall : ∀ j (h1 : j < m.args.size) (h2 : j < u.args.size),
          copyReachL tabs M M.size m.args[j] u.args[j] = true
      · apply opValL_mono_term ht
        refine refinesList_idx (by simp [hsz]) fun j h1 h2 => ?_
        simp only [Array.getElem_toList]
        exact (copyReachL_den hT _ _ _ (hall j (by simpa using h1) (by simpa using h2)) n).trans
          (hrec j (by simpa using h2))
      · -- an extension or `W` op with an argument a narrowing `Copy` (`truncReachL`)
        simp only [Classical.not_forall] at hall
        obtain ⟨j, h1, h2, hj⟩ := hall
        obtain ⟨k, c, w, hk, hc, hcop, hcsz, hsh, hkw, hw64, hcr⟩ :=
          truncReachL_cases ((hargs j h1 h2).resolve_left (by simpa using hj))
        rcases narrowReadW_cases hk with ⟨hk, -⟩ | ⟨hw, -⟩
        rotate_left
        · -- a `W` op: each argument copy-reached or a narrowing `Copy` to 32 bits
          rw [opValL_w32 hw, opValL_w32 hw]
          apply w32_mono hw
          refine r32List_idx (by simp [hsz]) fun i i1 i2 => ?_
          simp only [Array.length_toList] at i1 i2
          simp only [Array.getElem_toList]
          rcases hargs i i1 i2 with hcp | htr
          · exact fun x hx => Mono.reg32_of ((copyReachL_den hT _ _ _ hcp n).trans (hrec i i2)) hx
          · obtain ⟨k', c', w', hk', hc', hcop', hcsz', hsh', hkw', hw64', hcr'⟩ :=
              truncReachL_cases htr
            have hk32 : k' = 32 := by
              rcases narrowReadW_cases hk' with ⟨he, -⟩ | ⟨-, h32⟩
              · rw [(w32Op_cases hw).1] at he; cases he
              · exact h32
            subst hk32
            have hw32 : w' = .w32 := by
              cases w' <;> first | rfl | exact absurd rfl hw64' | simp [Width.bits] at hkw'
            subst hw32
            cases n with
            | zero => exact fun x hx => by cases hx
            | succ n =>
              have hct : termVL tabs c' = true := termVL_of_copy hcop'
              have hcl1 : c'.args.toList = [c'.args[0]!] := toList_of_size_one hcsz'
              have hden : denL true M.get? tabs ρ (n + 1) m.args[i] =
                  (denL true M.get? tabs ρ n c'.args[0]!).retypeL (.int .w32) := by
                rw [denT_succ hc' hct, hcl1, hcop', hsh']
                simp only [List.map_cons, List.map_nil, opValL_copy]
              rw [hden]
              have hX : Sem.Refines (denL true M.get? tabs ρ n c'.args[0]!)
                  (denL true (listedDefs g) tabs ρ' (n + 1) u.args[i]) :=
                (denL_fuel_mono true M.get? tabs ρ n (n + 1) _ (by omega)).trans
                  ((copyReachL_den hT _ _ _ hcr' (n + 1)).trans (hrec i i2))
              exact fun x hx => Mono.reg32_of hX (reg32_retypeL_w32 hx)
        obtain ⟨s, hs⟩ := opValL_ext hk
        by_cases hsz1 : m.args.size = 1
        · have hj0 : j = 0 := by omega
          subst hj0
          have hl : m.args.toList = [m.args[0]!] := toList_of_size_one hsz1
          have hl' : u.args.toList = [u.args[0]!] := toList_of_size_one (hsz.trans hsz1)
          rw [getElem!_pos m.args 0 h1] at hl
          rw [getElem!_pos u.args 0 h2] at hl'
          rw [hl, hl']
          simp only [List.map_cons, List.map_nil]
          cases n with
          | zero =>
            rw [hs, hs]
            show Sem.Refines (Arm64.op1 _ _ [.poison]) _
            exact .poison _
          | succ n =>
            have hct : termVL tabs c = true := termVL_of_copy hcop
            have hcl1 : c.args.toList = [c.args[0]!] := toList_of_size_one hcsz
            have hden : denL true M.get? tabs ρ (n + 1) m.args[0] =
                (denL true M.get? tabs ρ n c.args[0]!).retypeL (.int w) := by
              rw [denT_succ hc hct, hcl1, hcop, hsh]
              simp only [List.map_cons, List.map_nil, opValL_copy]
            rw [hden]
            have hX : Sem.Refines (denL true M.get? tabs ρ n c.args[0]!)
                (denL true (listedDefs g) tabs ρ' (n + 1) u.args[0]) :=
              (denL_fuel_mono true M.get? tabs ρ n (n + 1) _ (by omega)).trans
                ((copyReachL_den hT _ _ _ hcr (n + 1)).trans (hrec 0 h2))
            refine (opValL_mono_term ht _ (.cons (retypeL_mono _ hX) .nil)).trans ?_
            rw [hs, hs]
            exact op1_ext_retypeL s k hkw hw64 _ _
        · rw [hs, hs]
          have hlen : (m.args.toList.map (denL true M.get? tabs ρ n)).length ≠ 1 := by
            simpa using hsz1
          generalize m.args.toList.map (denL true M.get? tabs ρ n) = l at hlen
          rcases l with _ | ⟨a, _ | ⟨a', l⟩⟩
          · exact .poison _
          · exact absurd rfl hlen
          · exact .poison _
    · have hmf : termVL tabs m = false := by simpa using ht
      have h1 : ¬ IsTermL tabs M.get? x := fun ⟨w, hw, hw'⟩ => by
        rw [hm] at hw; cases hw; exact ht hw'
      have h2 : ¬ IsTermL tabs (listedDefs g) x := fun ⟨w, hw, hw'⟩ => by
        rw [hL] at hw; cases hw; rw [htt] at hw'; exact ht hw'
      rw [denL_succ_atom h1, denL_succ_atom h2]
      exact hρ x u hL (htt ▸ hmf)

/-! ## From `f`'s mode to lowered mode -/

/-- The valuation of `f`'s atoms read in lowered mode: shaped by `Val.retypeL` at their lowered
shapes. -/
def midVal (tabs : Tables) (f : Func) (ρ : ID → Val) (a : ID) : Val :=
  match f.value? a with
  | some u => if termVL tabs u then ρ a else (ρ a).retypeL (shpL tabs u.type)
  | none => ρ a

theorem shapesOK_get {tabs : Tables} {f : Func} (h : shapesOK tabs f = true) {x : ID} {v : Value}
    (hv : f.value? x = some v) : shpL tabs v.type = tabs.ty v.type := by
  unfold Func.value? at hv
  have ho : f.valueTab[x]? = some (some v) := Option.join_eq_some_iff.1 hv
  have hm := Array.mem_of_getElem? ho
  have := (Array.all_eq_true_iff_forall_mem.1 h) _ hm
  exact GoFV.Proof.Pass.Rewrite.tyEq_sound this

theorem mid_typed (tabs : Tables) (f : Func) (ρ : ID → Val) :
    TypedL true f.value? tabs (midVal tabs f ρ) := by
  intro a ha hsome
  cases hu : f.value? a with
  | none => rw [hu] at hsome; cases hsome
  | some u =>
    have hut : termVL tabs u = false := by
      cases h : termVL tabs u
      · rfl
      · exact absurd ⟨u, hu, h⟩ ha
    rw [shapeL_of hu]
    simp only [midVal, hu, hut, Bool.false_eq_true, ite_false]
    exact retypeL_idem _ _

/-- `midVal` keeps the frame addresses of `f`'s `LocalAddr`s (`FrameVals`): `poison` and an
address word at a word shape are fixed by `retypeL` there. -/
theorem mid_frame {tabs : Tables} {f : Func} {ρ : ID → Val} {act : Nat}
    (hF : FrameVals tabs act f.value? ρ) : FrameVals tabs act f.value? (midVal tabs f ρ) := by
  intro a l n hl hop hax
  have hlt : termVL tabs l = false := termVL_localAddr tabs l hop
  simp only [midVal, hl, hlt, Bool.false_eq_true, ite_false]
  rcases hF a l n hl hop hax with h | ⟨h, hw⟩
  · exact .inl (by rw [h]; exact retypeL_poison _)
  · exact .inr ⟨by rw [h]; exact word_retypeL (wordShape_cases hw) _, hw⟩

theorem mid_le {tabs : Tables} {f : Func} {ρ : ID → Val}
    (hsh : f.lowered = true ∨ shapesOK tabs f = true) (hT : TypedL f.lowered f.value? tabs ρ) :
    ∀ a, ¬ IsTermL tabs f.value? a → Sem.Refines (ρ a) (midVal tabs f ρ a) := by
  intro a ha
  cases hu : f.value? a with
  | none => simp only [midVal, hu]; exact Sem.Refines.refl _
  | some u =>
    have hut : termVL tabs u = false := by
      cases h : termVL tabs u
      · rfl
      · exact absurd ⟨u, hu, h⟩ ha
    simp only [midVal, hu, hut, Bool.false_eq_true, ite_false]
    have h1 := hT a ha (by rw [hu]; rfl)
    simp only [shapeL, hu, Option.map_some, Option.getD_some] at h1
    cases hl : f.lowered
    · rw [hl] at h1
      have hs : shpL tabs u.type = tabs.ty u.type := by
        rcases hsh with h | h
        · rw [hl] at h; cases h
        · exact shapesOK_get h hu
      rw [hs]
      have h1' : (ρ a).retype (tabs.ty u.type) = ρ a := h1
      conv => lhs; rw [← h1']
      exact retype_le_retypeL _ _
    · rw [hl] at h1
      have h1' : (ρ a).retypeL (shpL tabs u.type) = ρ a := h1
      rw [h1']; exact Sem.Refines.refl _

/-- **The bridge**: `f`'s terms in its own mode refine their lowered reading under `midVal`. -/
theorem bridge_den {tabs : Tables} {f : Func} {ρ : ID → Val}
    (hsh : f.lowered = true ∨ shapesOK tabs f = true) (hT : TypedL f.lowered f.value? tabs ρ) :
    ∀ n x, Sem.Refines (denL f.lowered f.value? tabs ρ n x)
      (denL true f.value? tabs (midVal tabs f ρ) n x)
  | 0, _ => .poison _
  | n + 1, x => by
    by_cases ht : IsTermL tabs f.value? x
    · obtain ⟨v, hv, hvt⟩ := ht
      rw [denL_succ_term hv hvt, denT_succ hv hvt]
      have hshp : shp f.lowered tabs v.type = shpL tabs v.type := by
        unfold shp
        cases hl : f.lowered
        · rcases hsh with h | h
          · rw [hl] at h; cases h
          · exact (shapesOK_get h hv).symm
        · rfl
      rw [hshp]
      have hargs := opValL_mono_term hvt (shpL tabs v.type)
        (GoFV.Proof.AtomSim.refinesList_map (l := v.args.toList)
          fun a _ => bridge_den hsh hT n a)
      unfold rty
      revert hargs
      cases f.lowered <;> intro hargs <;> simp only [Bool.false_eq_true, ite_false, ite_true]
      · exact (retype_mono _ hargs).trans (retype_le_retypeL _ _)
      · exact retypeL_mono _ hargs
    · rw [denL_succ_atom ht, denL_succ_atom ht]
      exact mid_le hsh hT x ht

/-- `midVal` at an atom listed in `g` is refined by a target valuation fixed at `g`'s atoms. -/
theorem mid_le_target {tabs : Tables} {f g : Func} (hA : atomsOKL tabs f g = true)
    {ρ ρ' : ID → Val} (hρ : ValRef ρ ρ') (hT' : TypedL true (listedDefs g) tabs ρ') :
    ∀ a u, listedDefs g a = some u → termVL tabs u = false →
      Sem.Refines (midVal tabs f ρ a) (ρ' a) := by
  intro a u hL hut
  unfold listedDefs at hL
  cases hg : g.value? a with
  | none => rw [hg] at hL; cases hL
  | some w =>
    rw [hg] at hL
    simp only [Option.filter, Bool.and_eq_true, List.contains_iff_mem] at hL
    split at hL
    · rename_i hc
      have hwu := Option.some.inj hL
      subst hwu
      obtain ⟨hb, hbv⟩ := hc
      have hb' : w.block ∈ g.blocks := by simpa using hb
      cases hgb : g.block? w.block with
      | none => rw [hgb] at hbv; cases hbv
      | some gb =>
        rw [hgb] at hbv
        simp only [Option.any_some, Array.contains_iff_mem] at hbv
        obtain ⟨fb, -, -, hat⟩ := (atomsOKL_facts hA).2 w.block hb' gb hgb
        obtain ⟨-, u', hu', hp, -, hu't⟩ := hat a hbv w hg hut
        have hty := atomPair_type hp
        simp only [midVal, hu', hu't, Bool.false_eq_true, ite_false]
        have hL' : listedDefs g a = some w := by
          simp [listedDefs, hg, Option.filter, hb, hb', hgb, hbv]
        have hnt : ¬ IsTermL tabs (listedDefs g) a := fun ⟨y, hy, hy'⟩ => by
          rw [hL'] at hy; cases hy; rw [hut] at hy'; cases hy'
        have h1 := hT' a hnt (by rw [hL']; rfl)
        rw [shapeL_of hL'] at h1
        have h1' : (ρ' a).retypeL (shpL tabs w.type) = ρ' a := h1
        rw [hty, ← h1']
        exact retypeL_mono _ (hρ a)
    · cases hL

/-! ## The theorems -/

/-- The facts `validateL` checks besides the replay. -/
theorem _root_.GoFV.Proof.Low.validateL_parts {tabs : Tables} {t : GoFV.Rules.Interp.Table}
    {f g : Func} {log : Array RwEvent} (hv : validateL tabs t f g log = true) :
    g.lowered = true ∧ (f.lowered = true ∨ shapesOK tabs f = true) ∧
    atomsOKL tabs f g = true ∧ closedOK f = true ∧ closedOK g = true := by
  unfold validateL at hv
  simp only [Bool.and_eq_true, Bool.or_eq_true] at hv
  obtain ⟨⟨⟨⟨⟨hg, hf⟩, hA⟩, hcf⟩, hcg⟩, -⟩ := hv
  exact ⟨hg, hf, hA, hcf, hcg⟩

/-- **Validator soundness (term level)**: an output accepted by `validateL` with the table of a
sound lowering rule set has the arguments of its atoms refining, as lowered terms over the atoms,
those of the input's corresponding atoms, and its terminators refining the input's as functions
of their controls' terms. -/
theorem _root_.GoFV.Proof.Low.validateL_termRef {s : RuleSet} (hs : ArmRuleSet.AllSound s)
    {tabs : Tables} {f g : Func} {log : Array RwEvent}
    (hv : validateL tabs (GoFV.Rules.Interp.Table.ofRuleSet s) f g log = true) :
    AtomArgsRefL tabs f g ∧ TermStepRefL tabs f g := by
  obtain ⟨hgl, hsh, hA, hcf, hcg⟩ := validateL_parts hv
  unfold validateL at hv
  simp only [Bool.and_eq_true] at hv
  obtain ⟨-, hv⟩ := hv
  obtain ⟨hbl, hAf⟩ := atomsOKL_facts hA
  split at hv
  · rename_i M B hrep
    obtain ⟨C, hI, hB⟩ := replayL_inv (D₀ := f.value?) (C₀ := LM f) hs (fun _ => rfl) log.toList
      _ M _ B _ hrep (ReplayInvL.init (marked_closed hcf)) (BInvL.init tabs f (LM f))
    obtain ⟨hlive, hfacts⟩ := finalOKL_facts hv
    have hTM : ∀ ρ, TypedL true M.get? tabs (midVal tabs f ρ) :=
      fun ρ => hI.typed _ (mid_typed tabs f ρ)
    constructor
    · intro b hb gb hgb a ha u hu hat
      obtain ⟨fb, hfb, -, hatoms⟩ := hAf b hb gb hgb
      obtain ⟨haf, u', hu', hp, hpc, hu't⟩ := hatoms a ha u hu hat
      refine ⟨u', hu', hp, hpc, ?_⟩
      have hbf : b ∈ f.blocks := hbl ▸ hb
      have hargsf := (closedOK_facts hcf b hbf fb hfb).2 a haf u' hu'
      obtain ⟨a'', ha'', -, hrest⟩ := hI.atoms a u' hu' hu't hargsf
      obtain ⟨-, -, -, -, -, -, -, -, -, -, hvals⟩ := hfacts b hb gb hgb
      obtain ⟨m, w, hm, hw, -, hai, hcase⟩ := hvals a ha
        (.inr fun w hw => by rw [hu] at hw; cases hw; exact hat)
      have hma : m = a'' := Option.some.inj (hm.symm.trans ha'')
      subst hma
      have huw : u = w := Option.some.inj (hu.symm.trans hw)
      subst huw
      rcases hcase with ⟨hop, hax, hszw, hargs⟩ | ⟨hmop, hm3, hpl, ks, hks, hszk, hargs⟩
      case inr =>
        -- a bounds panic with constant operands: the kept arguments of the replayed
        -- `LoweredPanicBoundsRR`, which are `f`'s (`argIx`)
        rw [hu'] at hpl
        have hpl' : pbLower u' u = true := by simpa using hpl
        rcases hrest with hfree | ⟨hsz'', hrest⟩
        · rw [(argFree_cases hfree).1] at hmop; cases hmop
        have hu'op := (pbLower_cases hpl').1
        refine .inr fun i hi => ?_
        have hik : i < ks.length := hszk ▸ hi
        have hix := argIx_of_pb hpl' hks hik
        have hk3 := pbKeep_lt hks hik
        have hk' : ks[i] < u'.args.size := by omega
        have hcopy := hargs i hik
        rw [getElem!_pos u.args i hi] at hcopy
        have hmark := (closedOK_facts hcg b hb gb hgb).2 a ha u hu u.args[i] (Array.getElem_mem hi)
        have hlv : LiveL tabs g u.args[i] :=
          (liveOKL_facts hlive) b hb gb hgb |>.2 a ha u hu (.inl hat) _ (Array.getElem_mem hi)
        intro n
        obtain ⟨k, hk⟩ := (hrest ks[i] hk').2 n
        refine ⟨k, fun ρ ρ' hρ hT hT' hF => ?_⟩
        rw [hgl] at hT'
        rw [hgl, getElem!_pos u.args i hi, hix, stArg_of_ne (by rw [hu'op]; decide)]
        have h1 := hk (midVal tabs f ρ) (mid_typed tabs f ρ) (mid_frame hF)
        rw [stArg_of_ne (by rw [hu'op]; decide)] at h1
        exact ArgRel.trans_left (bridge_den hsh hT n _) (h1.trans_right
          ((copyReachL_den (hTM ρ) _ _ _ hcopy k).trans
            (final_denL hv hcg (mid_le_target hA hρ hT') (hTM ρ) k _ hmark hlv)))
      rcases hrest with hfree | ⟨hsz'', hrest⟩
      · exact .inl (by rw [argFree_congr hop hax]; exact hfree)
      have hnpb : pbLower u' u = false := by
        cases hpb : pbLower u' u
        · rfl
        · exfalso
          obtain ⟨-, h3, -, ks, hks, hsk⟩ := pbLower_cases hpb
          have := pbKeep_len hks
          omega
      refine .inr fun i hi => ?_
      rw [argIx_of_not hnpb]
      have hi' : i < u'.args.size := by omega
      have hcopy := (hargs i (by omega) hi).resolve_right fun htr => by
        obtain ⟨k, -, -, hk, -⟩ := truncReachL_cases htr
        rw [← hop] at hk
        rw [termVL_narrow hk] at hat; cases hat
      have hmark := (closedOK_facts hcg b hb gb hgb).2 a ha u hu u.args[i] (Array.getElem_mem hi)
      have hlv : LiveL tabs g u.args[i] :=
        (liveOKL_facts hlive) b hb gb hgb |>.2 a ha u hu (.inl hat) _ (Array.getElem_mem hi)
      intro n
      obtain ⟨k, hk⟩ := (hrest i hi').2 n
      refine ⟨k, fun ρ ρ' hρ hT hT' hF => ?_⟩
      rw [hgl] at hT'
      rw [hgl, getElem!_pos u.args i hi]
      have h1 := hk (midVal tabs f ρ) (mid_typed tabs f ρ) (mid_frame hF)
      rw [getElem!_pos m.args i (by omega),
        stArg_congr (u := u') (i := i) hop.symm hai.symm hax.symm] at h1
      exact ArgRel.trans_left (bridge_den hsh hT n _) (h1.trans_right
        ((copyReachL_den (hTM ρ) _ _ _ hcopy k).trans
          (final_denL hv hcg (mid_le_target hA hρ hT') (hTM ρ) k _ hmark hlv)))
    · intro b hb fb gb hfb hgb
      obtain ⟨fb', hfb', hid, -⟩ := hAf b hb gb hgb
      rw [hfb] at hfb'; obtain rfl := Option.some.inj hfb'
      obtain ⟨st, fb'', hst, hfb'', hk, hai, hsu, -, hsz, hctl, -⟩ := hfacts b hb gb hgb
      rw [hfb] at hfb''; obtain rfl := Option.some.inj hfb''
      have hbf : b ∈ f.blocks := hbl ▸ hb
      obtain ⟨hsw, -, hrel⟩ := hB b fb st hfb (closedOK_facts hcf b hbf fb hfb).1 hst
      refine ⟨fun e he => ?_, fun n => ?_⟩
      · rw [hsu]
        cases hs2 : st.swapped
        · simpa using he
        · have h2 := hsw hs2
          obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 he
          simp only [ite_true, swapS, List.mem_toArray, List.mem_cons, List.mem_singleton,
            List.not_mem_nil, or_false]
          have : j = 0 ∨ j = 1 := by omega
          rcases this with rfl | rfl
          · right; rw [getElem!_pos fb.succs 0 hj]
          · left; rw [getElem!_pos fb.succs 1 hj]
      · obtain ⟨m, hm⟩ := hrel n
        refine ⟨m, fun ρ ρ' hρ hT hT' hF => ?_⟩
        rw [hgl] at hT' ⊢
        refine Res.Rel.trans_next (stepValsL_mono rfl rfl rfl rfl
          (GoFV.Proof.AtomSim.refinesList_map fun c _ => bridge_den hsh hT n c)) ?_
        refine Res.Rel.trans_next (hm (midVal tabs f ρ) (mid_typed tabs f ρ) (mid_frame hF))
          (stepValsL_mono (b := stBlockL fb st) hk hai hsu hid.symm ?_)
        refine refinesList_idx (by simp [hsz]) fun k h1 h2 => ?_
        simp only [Array.getElem_toList]
        have h1' : k < st.ctrls.size := by simpa using h1
        have h2' : k < gb.controls.size := by simpa using h2
        exact (copyReachL_den (hTM ρ) _ _ _ (hctl k h1' h2') m).trans
          (final_denL hv hcg (mid_le_target hA hρ hT') (hTM ρ) m _
            ((closedOK_facts hcg b hb gb hgb).1 _ (Array.getElem_mem h2'))
            ((liveOKL_facts hlive) b hb gb hgb |>.1 _ (Array.getElem_mem h2')))
  · cases hv

end GoFV.Proof.Low.Val

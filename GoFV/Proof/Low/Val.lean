import GoFV.Proof.Low.ValReplay

variable [GoFV.SSA.Sem.Addrs]

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
atom of `g` has the type of `f`'s (`atomsOKL`, `mid_le_target`), or, at a lowered frame address
where `f` has a term (`frameAtomG`), is `f`'s own valuation there. Such an atom is related to the
replayed `ADDconst [0]` of the frame address (`frameFinal`): `poison` or the variable's word
(`FrameVals`), which the target valuation holds (`FrameValsL`).
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

/-- What `truncFitL` says. -/
theorem truncFitL_cases {tabs : Tables} {M : Defs} {n : Nat} {v : Value} {i : Nat} {a a' : ID}
    (h : truncFitL tabs M n v i a a' = true) :
    ∃ w', argFitTy tabs v i = some (.int w') ∧ truncFromL tabs M n w'.bits a a' = true := by
  unfold truncFitL at h
  split at h
  · rename_i w' hw'
    exact ⟨w', hw', h⟩
  · cases h

/-- A lowered call (one `callFitTy` fits an argument of) is an atom. -/
theorem termVL_callFit {tabs : Tables} {v : Value} {i : Nat} {t : Ty}
    (h : callFitTy tabs v i = some t) : termVL tabs v = false := by
  unfold callFitTy at h
  cases hk : callLead v.op with
  | none => rw [hk] at h; cases h
  | some k =>
    rcases callLead_some hk with ⟨hv, -⟩ | ⟨hv, -⟩ | ⟨hv, -⟩ <;>
      (rw [termVL_arm (by decide) (by decide) (by decide) (by decide) hv]; decide)

/-- A narrow integer store (one `stFitTy` fits the value of) is an atom. -/
theorem termVL_stFit {tabs : Tables} {v : Value} {i : Nat} {t : Ty}
    (h : stFitTy v.op i = some t) : termVL tabs v = false := by
  rcases stFitTy_ops h with hv | hv | hv | hv | hv | hv | hv | hv <;>
    (rw [termVL_arm (by decide) (by decide) (by decide) (by decide) hv]; decide)

/-! ## The ops reading the low bits of their arguments at a narrow shape (`lowReachL`) -/

/-- `b` has a register holding `a`'s low `w` bits wherever `a` has one, and neither is a pointer
(`ADD`, `SUB` and `addK` add registers then, `Arm64.add`). -/
def RLow (w : Nat) (a b : Val) : Prop :=
  (∀ p, a ≠ .ptr p) ∧ ∀ x, Arm64.reg a = some x →
    ∃ y, Arm64.reg b = some y ∧ (∀ p, b ≠ .ptr p) ∧ x.setWidth w = y.setWidth w

/-- A function of the low `w` bits. -/
def LowFun (w : Nat) (f : BitVec 64 → BitVec 64) : Prop :=
  ∀ x y : BitVec 64, x.setWidth w = y.setWidth w → (f x).setWidth w = (f y).setWidth w

/-- A binary function of the low `w` bits. -/
def LowFun2 (w : Nat) (f : BitVec 64 → BitVec 64 → BitVec 64) : Prop :=
  ∀ x y x' y' : BitVec 64, x.setWidth w = x'.setWidth w → y.setWidth w = y'.setWidth w →
    (f x y).setWidth w = (f x' y').setWidth w

section LowFun
variable {w : Nat} (hw : w ≤ 64)
include hw

theorem lowFun2_add : LowFun2 w (· + ·) := fun x y x' y' h1 h2 => by
  simp only [BitVec.setWidth_add _ _ hw, h1, h2]

theorem lowFun2_mul : LowFun2 w (· * ·) := fun x y x' y' h1 h2 => by
  simp only [BitVec.setWidth_mul _ _ hw, h1, h2]

theorem lowFun_neg : LowFun w (- ·) := fun x y h => by
  simp only [BitVec.setWidth_neg_of_le hw, h]

theorem lowFun_not : LowFun w (~~~ ·) := fun x y h => by
  simp only [BitVec.setWidth_not hw, h]

theorem lowFun2_sub : LowFun2 w (· - ·) := fun x y x' y' h1 h2 => by
  simp only [BitVec.sub_eq_add_neg]
  exact lowFun2_add hw x (-y) x' (-y') h1 (lowFun_neg hw y y' h2)

theorem lowFun2_mneg : LowFun2 w (fun x y => -(x * y)) := fun x y x' y' h1 h2 =>
  lowFun_neg hw _ _ (lowFun2_mul hw x y x' y' h1 h2)

end LowFun

theorem lowFun2_and (w : Nat) : LowFun2 w (· &&& ·) := fun x y x' y' h1 h2 => by
  simp only [BitVec.setWidth_and, h1, h2]

theorem lowFun2_or (w : Nat) : LowFun2 w (· ||| ·) := fun x y x' y' h1 h2 => by
  simp only [BitVec.setWidth_or, h1, h2]

theorem lowFun2_xor (w : Nat) : LowFun2 w (· ^^^ ·) := fun x y x' y' h1 h2 => by
  simp only [BitVec.setWidth_xor, h1, h2]

theorem lowFun2_bic {w : Nat} (hw : w ≤ 64) : LowFun2 w (fun x y => x &&& ~~~y) :=
  fun x y x' y' h1 h2 => lowFun2_and w x (~~~y) x' (~~~y') h1 (lowFun_not hw y y' h2)

theorem lowFun_const {w : Nat} {f : BitVec 64 → BitVec 64 → BitVec 64} (hf : LowFun2 w f)
    (c : BitVec 64) : LowFun w (f · c) := fun x y h => hf x c y c h rfl

/-- A 64-bit register result read at a narrow integer shape: its low bits. -/
theorem res_retypeL_narrow {w : Width} (hw : w ≠ .w64) (r : BitVec 64) :
    (Arm64.res (.int w) r).retypeL (.int w) = .int w (r.setWidth w.bits) := by
  cases w <;> first | exact absurd rfl hw | simp [Arm64.res, Val.retypeL, Val.widen, Val.retype, Width.bits]

section LowOps
variable {w : Width} (hw : w ≠ .w64)
include hw

theorem op1_low {f : BitVec 64 → BitVec 64} (hf : LowFun w.bits f) {a b : Val}
    (h : RLow w.bits a b) :
    Sem.Refines ((Arm64.op1 (.int w) f [a]).retypeL (.int w))
      ((Arm64.op1 (.int w) f [b]).retypeL (.int w)) := by
  simp only [Arm64.op1]
  cases ha : Arm64.reg a with
  | none => exact refines_poison_retypeL _ _
  | some x =>
    obtain ⟨y, hb, -, hxy⟩ := h.2 x ha
    rw [hb, res_retypeL_narrow hw, res_retypeL_narrow hw, hf x y hxy]
    exact Sem.Refines.refl _

theorem op2_low {f : BitVec 64 → BitVec 64 → BitVec 64} (hf : LowFun2 w.bits f) {a a' b b' : Val}
    (h : RLow w.bits a b) (h' : RLow w.bits a' b') :
    Sem.Refines ((Arm64.op2 (.int w) f [a, a']).retypeL (.int w))
      ((Arm64.op2 (.int w) f [b, b']).retypeL (.int w)) := by
  simp only [Arm64.op2]
  cases ha : Arm64.reg a with
  | none => exact refines_poison_retypeL _ _
  | some x =>
    cases ha' : Arm64.reg a' with
    | none => exact refines_poison_retypeL _ _
    | some x' =>
      obtain ⟨y, hb, -, hxy⟩ := h.2 x ha
      obtain ⟨y', hb', -, hxy'⟩ := h'.2 x' ha'
      rw [hb, hb', res_retypeL_narrow hw, res_retypeL_narrow hw, hf x x' y y' hxy hxy']
      exact Sem.Refines.refl _

end LowOps

/-- `ADD` adds registers when neither argument is a pointer. -/
theorem add_noPtr (T : Ty) {a b : Val} (ha : ∀ p, a ≠ .ptr p) (hb : ∀ p, b ≠ .ptr p) :
    Arm64.add T [a, b] = Arm64.op2 T (· + ·) [a, b] := by
  cases a <;> cases b <;> first | rfl | exact absurd rfl (ha _) | exact absurd rfl (hb _)

/-- `SUB` subtracts registers when neither argument is a pointer. -/
theorem sub_noPtr (T : Ty) {a b : Val} (ha : ∀ p, a ≠ .ptr p) (hb : ∀ p, b ≠ .ptr p) :
    Arm64.sub T [a, b] = Arm64.op2 T (· - ·) [a, b] := by
  cases a <;> cases b <;> first | rfl | exact absurd rfl (ha _) | exact absurd rfl (hb _)

/-- `addK` adds to a register when its argument is no pointer. -/
theorem addK_noPtr (T : Ty) (k : BitVec 64) {a : Val} (ha : ∀ p, a ≠ .ptr p) :
    Arm64.addK T k [a] = Arm64.op1 T (· + k) [a] := by
  cases a <;> first | rfl | exact absurd rfl (ha _)

/-- `regVal` of a value that is no pointer: its register. -/
theorem regVal_noPtr (T : Ty) {a : Val} (ha : ∀ p, a ≠ .ptr p) :
    Arm64.regVal T a = Arm64.op1 T id [a] := by
  cases a <;> first | rfl | exact absurd rfl (ha _)

theorem RLow.noPtr {w : Nat} {a b : Val} (h : RLow w a b) {x : BitVec 64}
    (ha : Arm64.reg a = some x) : ∀ p, b ≠ .ptr p := by
  obtain ⟨_, -, hb, -⟩ := h.2 x ha
  exact hb

theorem add_low {w : Width} (hw : w ≠ .w64) {a a' b b' : Val} (h : RLow w.bits a b)
    (h' : RLow w.bits a' b') :
    Sem.Refines ((Arm64.add (.int w) [a, a']).retypeL (.int w))
      ((Arm64.add (.int w) [b, b']).retypeL (.int w)) := by
  rw [add_noPtr _ h.1 h'.1]
  cases ha : Arm64.reg a with
  | none => simp only [Arm64.op2, ha]; exact refines_poison_retypeL _ _
  | some x =>
    cases ha' : Arm64.reg a' with
    | none => simp only [Arm64.op2, ha, ha']; exact refines_poison_retypeL _ _
    | some x' =>
      rw [add_noPtr _ (h.noPtr ha) (h'.noPtr ha')]
      exact op2_low hw (lowFun2_add (width_bits_le w)) h h'

theorem sub_low {w : Width} (hw : w ≠ .w64) {a a' b b' : Val} (h : RLow w.bits a b)
    (h' : RLow w.bits a' b') :
    Sem.Refines ((Arm64.sub (.int w) [a, a']).retypeL (.int w))
      ((Arm64.sub (.int w) [b, b']).retypeL (.int w)) := by
  rw [sub_noPtr _ h.1 h'.1]
  cases ha : Arm64.reg a with
  | none => simp only [Arm64.op2, ha]; exact refines_poison_retypeL _ _
  | some x =>
    cases ha' : Arm64.reg a' with
    | none => simp only [Arm64.op2, ha, ha']; exact refines_poison_retypeL _ _
    | some x' =>
      rw [sub_noPtr _ (h.noPtr ha) (h'.noPtr ha')]
      exact op2_low hw (lowFun2_sub (width_bits_le w)) h h'

theorem addK_low {w : Width} (hw : w ≠ .w64) (k : BitVec 64) {a b : Val} (h : RLow w.bits a b) :
    Sem.Refines ((Arm64.addK (.int w) k [a]).retypeL (.int w))
      ((Arm64.addK (.int w) k [b]).retypeL (.int w)) := by
  rw [addK_noPtr _ k h.1]
  cases ha : Arm64.reg a with
  | none => simp only [Arm64.op1, ha]; exact refines_poison_retypeL _ _
  | some x =>
    rw [addK_noPtr _ k (h.noPtr ha)]
    exact op1_low hw (lowFun_const (lowFun2_add (width_bits_le w)) k) h

theorem regVal_low {w : Width} (hw : w ≠ .w64) {a b : Val} (h : RLow w.bits a b) :
    Sem.Refines ((Arm64.regVal (.int w) a).retypeL (.int w))
      ((Arm64.regVal (.int w) b).retypeL (.int w)) := by
  rw [regVal_noPtr _ h.1]
  cases ha : Arm64.reg a with
  | none => simp only [Arm64.op1, ha]; exact refines_poison_retypeL _ _
  | some x =>
    rw [regVal_noPtr _ (h.noPtr ha)]
    exact op1_low hw (fun x y h => h) h

theorem csel_low {w : Width} (hw : w ≠ .w64) (k : Int64) {a a' f b b' f' : Val}
    (h : RLow w.bits a b) (h' : RLow w.bits a' b') (hf : Sem.Refines f f') :
    Sem.Refines ((Arm64.csel (.int w) k none [a, a', f]).retypeL (.int w))
      ((Arm64.csel (.int w) k none [b, b', f']).retypeL (.int w)) := by
  simp only [Arm64.csel]
  cases hc : Arm64.condOn k f with
  | none => exact refines_poison_retypeL _ _
  | some c =>
    rw [Mono.condOn_of k hf hc]
    cases c
    · exact regVal_low hw h'
    · exact regVal_low hw h

theorem lowOpArgs_cases {o : Op} {d : Nat} (h : lowOpArgs o = some d) :
    ((o = .ARM64ADD ∨ o = .ARM64SUB ∨ o = .ARM64MUL ∨ o = .ARM64MNEG ∨ o = .ARM64AND ∨
        o = .ARM64OR ∨ o = .ARM64XOR ∨ o = .ARM64BIC) ∧ d = 2) ∨ (o = .ARM64CSEL ∧ d = 2) ∨
      ((o = .ARM64ADDconst ∨ o = .ARM64SUBconst ∨ o = .ARM64NEG ∨ o = .ARM64MVN ∨
        o = .ARM64ANDconst ∨ o = .ARM64ORconst ∨ o = .ARM64XORconst) ∧ d = 1) := by
  unfold lowOpArgs at h
  split at h <;> simp_all

theorem op1_len (T : Ty) (g : BitVec 64 → BitVec 64) :
    ∀ l : List Val, l.length ≠ 1 → Arm64.op1 T g l = .poison
  | [], _ => rfl
  | [_], h => absurd rfl h
  | _ :: _ :: _, _ => rfl

theorem op2_len (T : Ty) (g : BitVec 64 → BitVec 64 → BitVec 64) :
    ∀ l : List Val, l.length ≠ 2 → Arm64.op2 T g l = .poison
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], h => absurd rfl h
  | _ :: _ :: _ :: _, _ => rfl

theorem addK_len (T : Ty) (k : BitVec 64) :
    ∀ l : List Val, l.length ≠ 1 → Arm64.addK T k l = .poison
  | [], _ => rfl
  | [_], h => absurd rfl h
  | _ :: _ :: _, _ => rfl

theorem add_len (T : Ty) : ∀ l : List Val, l.length ≠ 2 → Arm64.add T l = .poison
  | [], _ => rfl
  | [a], _ => by cases a <;> rfl
  | [_, _], h => absurd rfl h
  | a :: b :: _ :: _, _ => by cases a <;> cases b <;> rfl

theorem sub_len (T : Ty) : ∀ l : List Val, l.length ≠ 2 → Arm64.sub T l = .poison
  | [], _ => rfl
  | [a], _ => by cases a <;> rfl
  | [_, _], h => absurd rfl h
  | a :: b :: _ :: _, _ => by cases a <;> cases b <;> rfl

theorem csel_len (T : Ty) (k : Int64) (g : Option (BitVec 64 → BitVec 64)) :
    ∀ l : List Val, l.length ≠ 3 → Arm64.csel T k g l = .poison
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | [_, _, _], h => absurd rfl h
  | _ :: _ :: _ :: _ :: _, _ => rfl

section Arity
variable {w : Width} {F : List Val → Val} {as bs : List Val} (hl : as.length = bs.length)
include hl

theorem low_unary (hF : ∀ l : List Val, l.length ≠ 1 → F l = .poison)
    (h1 : ∀ a b, RLow w.bits a b → Sem.Refines ((F [a]).retypeL (.int w)) ((F [b]).retypeL (.int w)))
    (hlow : ∀ j (h1 : j < as.length) (h2 : j < bs.length), j < 1 → RLow w.bits as[j] bs[j]) :
    Sem.Refines ((F as).retypeL (.int w)) ((F bs).retypeL (.int w)) := by
  match as, bs, hl with
  | [a], [b], _ => exact h1 a b (hlow 0 (by simp) (by simp) (by omega))
  | [], _, _ => rw [hF [] (by simp)]; exact refines_poison_retypeL _ _
  | _ :: _ :: _, _, _ => rw [hF _ (by simp)]; exact refines_poison_retypeL _ _

theorem low_binary (hF : ∀ l : List Val, l.length ≠ 2 → F l = .poison)
    (h2 : ∀ a a' b b', RLow w.bits a b → RLow w.bits a' b' →
      Sem.Refines ((F [a, a']).retypeL (.int w)) ((F [b, b']).retypeL (.int w)))
    (hlow : ∀ j (h1 : j < as.length) (h2 : j < bs.length), j < 2 → RLow w.bits as[j] bs[j]) :
    Sem.Refines ((F as).retypeL (.int w)) ((F bs).retypeL (.int w)) := by
  match as, bs, hl with
  | [a, a'], [b, b'], _ =>
    exact h2 a a' b b' (hlow 0 (by simp) (by simp) (by omega)) (hlow 1 (by simp) (by simp) (by omega))
  | [], _, _ => rw [hF [] (by simp)]; exact refines_poison_retypeL _ _
  | [_], _, _ => rw [hF _ (by simp)]; exact refines_poison_retypeL _ _
  | _ :: _ :: _ :: _, _, _ => rw [hF _ (by simp)]; exact refines_poison_retypeL _ _

theorem low_ternary (hF : ∀ l : List Val, l.length ≠ 3 → F l = .poison)
    (h3 : ∀ a a' f b b' f', RLow w.bits a b → RLow w.bits a' b' → Sem.Refines f f' →
      Sem.Refines ((F [a, a', f]).retypeL (.int w)) ((F [b, b', f']).retypeL (.int w)))
    (hlow : ∀ j (h1 : j < as.length) (h2 : j < bs.length), j < 2 → RLow w.bits as[j] bs[j])
    (hrest : ∀ j (h1 : j < as.length) (h2 : j < bs.length), 2 ≤ j → Sem.Refines as[j] bs[j]) :
    Sem.Refines ((F as).retypeL (.int w)) ((F bs).retypeL (.int w)) := by
  match as, bs, hl with
  | [a, a', f], [b, b', f'], _ =>
    exact h3 a a' f b b' f' (hlow 0 (by simp) (by simp) (by omega))
      (hlow 1 (by simp) (by simp) (by omega)) (hrest 2 (by simp) (by simp) (by omega))
  | [], _, _ => rw [hF [] (by simp)]; exact refines_poison_retypeL _ _
  | [_], _, _ => rw [hF _ (by simp)]; exact refines_poison_retypeL _ _
  | [_, _], _, _ => rw [hF _ (by simp)]; exact refines_poison_retypeL _ _
  | _ :: _ :: _ :: _ :: _, _, _ => rw [hF _ (by simp)]; exact refines_poison_retypeL _ _

end Arity

/-- **An op of `lowOpArgs` at a narrow integer shape refines on arguments whose low bits its
data arguments keep** (`RLow`; the others refined). -/
theorem lowOp_mono {o : Op} {d : Nat} (ho : lowOpArgs o = some d) {w : Width} (hw : w ≠ .w64)
    (k : Int64) (ax : Option AuxRef) {as bs : List Val} (hl : as.length = bs.length)
    (hlow : ∀ j (h1 : j < as.length) (h2 : j < bs.length), j < d → RLow w.bits as[j] bs[j])
    (hrest : ∀ j (h1 : j < as.length) (h2 : j < bs.length), d ≤ j → Sem.Refines as[j] bs[j]) :
    Sem.Refines ((Arm64.evalPure o (.int w) k ax as).retypeL (.int w))
      ((Arm64.evalPure o (.int w) k ax bs).retypeL (.int w)) := by
  have hb := width_bits_le w
  rcases lowOpArgs_cases ho with ⟨h | h | h | h | h | h | h | h, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨h | h | h | h | h | h | h, rfl⟩ <;> try subst h
  · exact low_binary (F := Arm64.add (.int w)) hl (add_len _)
      (fun _ _ _ _ h h' => add_low hw h h') hlow
  · exact low_binary (F := Arm64.sub (.int w)) hl (sub_len _)
      (fun _ _ _ _ h h' => sub_low hw h h') hlow
  · exact low_binary (F := Arm64.op2 (.int w) (· * ·)) hl (op2_len _ _)
      (fun _ _ _ _ h h' => op2_low hw (lowFun2_mul hb) h h') hlow
  · exact low_binary (F := Arm64.op2 (.int w) (fun x y => -(x * y))) hl (op2_len _ _)
      (fun _ _ _ _ h h' => op2_low hw (lowFun2_mneg hb) h h') hlow
  · exact low_binary (F := Arm64.op2 (.int w) (· &&& ·)) hl (op2_len _ _)
      (fun _ _ _ _ h h' => op2_low hw (lowFun2_and _) h h') hlow
  · exact low_binary (F := Arm64.op2 (.int w) (· ||| ·)) hl (op2_len _ _)
      (fun _ _ _ _ h h' => op2_low hw (lowFun2_or _) h h') hlow
  · exact low_binary (F := Arm64.op2 (.int w) (· ^^^ ·)) hl (op2_len _ _)
      (fun _ _ _ _ h h' => op2_low hw (lowFun2_xor _) h h') hlow
  · exact low_binary (F := Arm64.op2 (.int w) (fun x y => x &&& ~~~y)) hl (op2_len _ _)
      (fun _ _ _ _ h h' => op2_low hw (lowFun2_bic hb) h h') hlow
  · exact low_ternary (F := Arm64.csel (.int w) k none) hl (csel_len _ _ _)
      (fun _ _ _ _ _ _ h h' hf => csel_low hw k h h' hf) hlow hrest
  · exact low_unary (F := Arm64.addK (.int w) (Arm64.imm k)) hl (addK_len _ _)
      (fun _ _ h => addK_low hw _ h) hlow
  · exact low_unary (F := Arm64.addK (.int w) (-Arm64.imm k)) hl (addK_len _ _)
      (fun _ _ h => addK_low hw _ h) hlow
  · exact low_unary (F := Arm64.op1 (.int w) (- ·)) hl (op1_len _ _)
      (fun _ _ h => op1_low hw (lowFun_neg hb) h) hlow
  · exact low_unary (F := Arm64.op1 (.int w) (~~~ ·)) hl (op1_len _ _)
      (fun _ _ h => op1_low hw (lowFun_not hb) h) hlow
  · exact low_unary (F := Arm64.op1 (.int w) (· &&& Arm64.imm k)) hl (op1_len _ _)
      (fun _ _ h => op1_low hw (lowFun_const (lowFun2_and _) _) h) hlow
  · exact low_unary (F := Arm64.op1 (.int w) (· ||| Arm64.imm k)) hl (op1_len _ _)
      (fun _ _ h => op1_low hw (lowFun_const (lowFun2_or _) _) h) hlow
  · exact low_unary (F := Arm64.op1 (.int w) (· ^^^ Arm64.imm k)) hl (op1_len _ _)
      (fun _ _ h => op1_low hw (lowFun_const (lowFun2_xor _) _) h) hlow

theorem lowOp_facts {o : Op} {d : Nat} (h : lowOpArgs o = some d) :
    o.generic = false ∧ (o == .ARM64MOVDaddr) = false ∧ ldAny o = false ∧ extReadW o = none ∧
      w32Op o = false ∧ callLead o = none ∧ o ≠ .Phi ∧ o ≠ .MakeResult := by
  rcases lowOpArgs_cases h with ⟨h | h | h | h | h | h | h | h, -⟩ | ⟨h, -⟩ |
      ⟨h | h | h | h | h | h | h, -⟩ <;> subst h <;> decide

/-- An op of `lowOpArgs` is a term. -/
theorem termVL_low {tabs : Tables} {v : Value} {d : Nat} (h : lowOpArgs v.op = some d) :
    termVL tabs v = true := by
  rcases lowOpArgs_cases h with ⟨h | h | h | h | h | h | h | h, -⟩ | ⟨h, -⟩ |
      ⟨h | h | h | h | h | h | h, -⟩ <;>
    (rw [termVL_arm (by decide) (by decide) (by decide) (by decide) h]; decide)

theorem opValL_low {o : Op} {d : Nat} (h : lowOpArgs o = some d) (tabs : Tables) (ty : Ty)
    (ai : Int64) (ax : Option AuxRef) (args : List Val) :
    opValL tabs o ty ai ax args = Arm64.evalPure o ty ai ax args := by
  obtain ⟨hg, hm, hl, -⟩ := lowOp_facts h
  simp only [opValL, hg, hm, (ldAny_false hl).1, (ldAny_false hl).2, Bool.false_eq_true, ite_false]

theorem narrowReadW_low {o : Op} {d : Nat} (h : lowOpArgs o = some d) (ai : Int64) (i : Nat) :
    narrowReadW o ai i = none := by
  obtain ⟨-, -, -, he, hw, -⟩ := lowOp_facts h
  have ht : (o == .ARM64TSTWconst) = false := by
    cases hb : (o == .ARM64TSTWconst)
    · rfl
    · rw [beq_iff_eq.1 hb] at h; cases h
  simp [narrowReadW, he, hw, ht]

theorem argFitTy_low {tabs : Tables} {v : Value} {d : Nat} (h : lowOpArgs v.op = some d)
    (i : Nat) : argFitTy tabs v i = none := by
  obtain ⟨-, -, -, -, -, hc, hp, hr⟩ := lowOp_facts h
  have hs : ∀ j, stFitTy v.op j = none := fun j => by
    cases hw : stFitTy v.op j with
    | none => rfl
    | some w =>
      rcases stFitTy_ops hw with ho | ho | ho | ho | ho | ho | ho | ho <;> rw [ho] at h <;> cases h
  simp [argFitTy, atomFitTy, hc, hp, hr, hs]

/-- What `lowShape` says. -/
theorem lowShape_cases {tabs : Tables} {M : Defs} {m : Value} {k : Nat}
    (h : lowShape tabs M m = some k) :
    ∃ w d, shpL tabs m.type = .int w ∧ lowOpArgs m.op = some d ∧ w ≠ .w64 ∧ k = w.bits ∧
      d ≤ m.args.size ∧ ∀ j < d, ∃ y w', M.get? m.args[j]! = some y ∧ shpL tabs y.type = .int w' ∧
        w' ≠ .w64 := by
  unfold lowShape at h
  split at h
  · rename_i w d hsh hd
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, List.all_eq_true,
        List.mem_range] at hc
      obtain ⟨⟨hw, hdsz⟩, hall⟩ := hc
      refine ⟨w, d, hsh, hd, hw, rfl, hdsz, fun j hj => ?_⟩
      have := hall j hj
      cases hy : M.get? m.args[j]! with
      | none => rw [hy] at this; cases this
      | some y =>
        rw [hy] at this
        simp only [Option.any_some] at this
        split at this
        · rename_i w' hw'
          exact ⟨y, w', rfl, hw', by simpa using this⟩
        · cases this
    · cases h
  · cases h

/-- What `lowReachL` says, `m`'s `lowShape` given. -/
theorem lowReachL_cases {tabs : Tables} {M : Defs} {n : Nat} {m : Value} {j k : Nat} {a a' : ID}
    (hs : lowShape tabs M m = some k) (h : lowReachL tabs M n m j a a' = true) :
    truncFromL tabs M n k a a' = true := by
  simp only [lowReachL, hs, Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- `lowReachL` needs `m`'s `lowShape`. -/
theorem lowReachL_none {tabs : Tables} {M : Defs} {n : Nat} {m : Value} {j : Nat} {a a' : ID}
    (hs : lowShape tabs M m = none) : lowReachL tabs M n m j a a' = false := by
  simp [lowReachL, hs]

/-- A narrow integer refined: its register, as `b`'s. -/
theorem rlow_of_narrow {k : Nat} {a b : Val} {w : Width} (h : a.hasTy (.int w) = true)
    (hw : w ≠ .w64) (hab : Sem.Refines a b) : RLow k a b := by
  cases a with
  | poison => exact ⟨fun _ h => (by cases h), fun x hx => (by simp [Arm64.reg] at hx)⟩
  | int v x =>
    cases hab
    exact ⟨fun _ h => (by cases h), fun y hy => ⟨y, hy, fun _ h => (by cases h), rfl⟩⟩
  | ptr p => cases w <;> simp_all [Val.hasTy]
  | _ => simp [Val.hasTy] at h

/-- `RLow` of a value refining another: `poison`, or the same register. -/
theorem rlow_of_le {k : Nat} {a a' b : Val} (h : Sem.Refines a a') (h' : RLow k a' b) :
    RLow k a b :=
  ⟨fun p hp => by subst hp; cases h; exact h'.1 p rfl,
    fun x hx => h'.2 x (Mono.reg_of h hx)⟩

/-- **A narrowing `Copy` keeps the low `k` bits it is at least as wide as** (`lowReachL`). -/
theorem rlow_retypeL {k : Nat} {w : Width} (hk : k ≤ w.bits) (hw : w ≠ .w64) {X B : Val}
    (h : Sem.Refines X B) : RLow k (X.retypeL (.int w)) B := by
  have hb := width_bits_le w
  rcases retypeL_narrow_cases hw X with he | ⟨v, x, rfl, he⟩ | ⟨b, rfl, he⟩ <;> rw [he]
  · exact ⟨fun _ h => (by cases h), fun x hx => (by simp [Arm64.reg] at hx)⟩
  · cases h
    refine ⟨fun _ h => (by cases h), fun y hy => ⟨x.setWidth 64, rfl, fun _ h => (by cases h), ?_⟩⟩
    simp only [Arm64.reg, Option.some.injEq] at hy
    subst hy
    rw [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_setWidth_of_le _ hk,
      BitVec.setWidth_setWidth_of_le _ (by omega)]
  · cases h
    refine ⟨fun _ h => (by cases h), fun y hy => ⟨if b then 1 else 0, rfl, fun _ h => (by cases h), ?_⟩⟩
    simp only [Arm64.reg, Option.some.injEq] at hy
    subst hy
    have h1 : 1 ≤ w.bits := by cases w <;> decide
    cases b
    · simp
    · simp only [ite_true]
      exact setWidth_one_low (by omega) h1 (by omega)

/-- `opValL` of `MakeResult`: the tuple of its arguments. -/
theorem opValL_makeResult (tabs : Tables) (ty : Ty) (ai : Int64) (ax : Option AuxRef)
    (args : List Val) : opValL tabs .MakeResult ty ai ax args = .tuple args := by
  simp only [opValL, show Op.MakeResult.generic = true by decide, ite_true]
  rfl

theorem refinesList_of_idx : ∀ {as bs : List Val}, as.length = bs.length →
    (∀ i (h1 : i < as.length) (h2 : i < bs.length), Sem.Refines as[i] bs[i]) → RefinesList as bs
  | [], [], _, _ => .nil
  | _ :: _, _ :: _, hl, h => .cons (h 0 (by simp) (by simp))
      (refinesList_of_idx (by simpa using hl) fun i h1 h2 =>
        h (i + 1) (by simpa using h1) (by simpa using h2))
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => by simp at hl

theorem retypePre_fit : ∀ (ts : List Ty) {as bs : List Val}, as.length = bs.length →
    (∀ i (h1 : i < as.length) (h2 : i < bs.length),
      (∀ t, ts[i]? = some t → Sem.Refines (as[i].retypeL t) (bs[i].retypeL t)) ∧
      (ts[i]? = none → Sem.Refines as[i] bs[i])) →
    ∀ vs, Val.retypePre ts (Val.widenList ts as) = some vs →
      ∃ vs', Val.retypePre ts (Val.widenList ts bs) = some vs' ∧ RefinesList vs vs'
  | [], as, bs, hl, h, vs, hv => by
    have e1 : Val.widenList [] as = as := by cases as <;> rfl
    have e2 : Val.widenList [] bs = bs := by cases bs <;> rfl
    rw [e1] at hv
    rw [e2]
    simp only [Val.retypePre, Option.some.injEq] at hv
    subst hv
    exact ⟨bs, rfl, refinesList_of_idx hl fun i h1 h2 => (h i h1 h2).2 (by simp)⟩
  | _ :: _, [], [], _, _, vs, hv => by simp [Val.widenList, Val.retypePre] at hv
  | t :: ts, a :: as, b :: bs, hl, h, vs, hv => by
    simp only [Val.widenList, Val.retypePre, Option.map_eq_some_iff] at hv ⊢
    obtain ⟨vs0, h0, rfl⟩ := hv
    obtain ⟨vs1, h1, hr⟩ := retypePre_fit ts (by simpa using hl)
      (fun i h1 h2 => h (i + 1) (by simpa using h1) (by simpa using h2)) vs0 h0
    exact ⟨_, ⟨vs1, h1, rfl⟩, .cons ((h 0 (by simp) (by simp)).1 t rfl) hr⟩
  | _ :: _, [], _ :: _, hl, _, _, _ | _ :: _, _ :: _, [], hl, _, _, _ => by simp at hl

/-- A tuple read at a tuple shape: componentwise (`Val.retypePre`), the components beyond the
shapes unchanged. -/
theorem tuple_retypeL_fit {ts : List Ty} {as bs : List Val} (hl : as.length = bs.length)
    (h : ∀ i (h1 : i < as.length) (h2 : i < bs.length),
      (∀ t, ts[i]? = some t → Sem.Refines (as[i].retypeL t) (bs[i].retypeL t)) ∧
      (ts[i]? = none → Sem.Refines as[i] bs[i])) :
    Sem.Refines ((Val.tuple as).retypeL (.tuple ts)) ((Val.tuple bs).retypeL (.tuple ts)) := by
  show Sem.Refines (Val.retype (.tuple ts) (Val.widen (.tuple ts) (.tuple as)))
    (Val.retype (.tuple ts) (Val.widen (.tuple ts) (.tuple bs)))
  simp only [Val.widen, Val.retype]
  cases hv : Val.retypePre ts (Val.widenList ts as) with
  | none => exact .poison _
  | some vs =>
    obtain ⟨vs', h', hr⟩ := retypePre_fit ts hl h vs hv
    rw [h']
    exact .tuple hr

/-- A tuple read at a shape that is no tuple: `poison`. -/
theorem tuple_retypeL_other {T : Ty} (hT : ∀ ts, T ≠ .tuple ts) (as : List Val) :
    (Val.tuple as).retypeL T = .poison := by
  cases T <;> first | exact absurd rfl (hT _) | simp [Val.retypeL, Val.widen, Val.retype]

theorem atomsOKL_facts {tabs : Tables} {f g : Func} (h : atomsOKL tabs f g = true) :
    f.blocks = g.blocks ∧ ∀ b ∈ g.blocks, ∀ gb, g.block? b = some gb → ∃ fb, f.block? b = some fb ∧
      fb.id = gb.id ∧ ∀ x ∈ gb.values, ∀ w, g.value? x = some w → termVL tabs w = false →
        (x ∈ fb.values ∧ ∃ u, f.value? x = some u ∧ atomPair tabs u w = true ∧
          pbConstOK tabs f u w = true ∧ termVL tabs u = false) ∨ frameAtomG tabs f x w = true := by
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
    simp only [Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem] at this
    rcases this with ⟨hxf, hfd⟩ | hfa
    · left
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
    · right
      rw [hw] at hfa
      simpa using hfa
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

/-- What `frameFinal` says. -/
theorem frameFinal_cases {tabs : Tables} {f : Func} {M : Defs} {x : ID} {m u : Value}
    (h : frameFinal tabs f M x m u = true) :
    u.id = x ∧ u.op = .ARM64MOVDaddr ∧ termVL tabs u = false ∧ u.args.size = 1 ∧
      termVL tabs m = true ∧ u.type = m.type ∧ u.auxInt = m.auxInt ∧
      wordShape (shpL tabs u.type) = true ∧ ∃ a l v, frameAddr tabs M x = some (a, l) ∧
        l.aux = u.aux ∧ f.value? a = some v ∧ v.op = .LocalAddr ∧ v.aux = u.aux := by
  unfold frameFinal at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, ?_⟩
  cases hfa : frameAddr tabs M x with
  | none => rw [hfa] at h9; cases h9
  | some p =>
    obtain ⟨a, l⟩ := p
    rw [hfa] at h9
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h9
    obtain ⟨hl, hv⟩ := h9
    cases hfv : f.value? a with
    | none => rw [hfv] at hv; cases hv
    | some v =>
      rw [hfv] at hv
      simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at hv
      exact ⟨a, l, v, rfl, hl, hfv, hv.1, hv.2⟩

/-- What `spFinal` says. -/
theorem spFinal_cases {f : Func} {M : Defs} {x : ID} {m u : Value}
    (h : spFinal f M x m u = true) :
    u.id = x ∧ m.op = .OffPtr ∧ u.op = .ARM64MOVDaddr ∧ u.aux = none ∧ u.type = m.type ∧
      u.auxInt = m.auxInt ∧ m.args.size = 1 ∧ u.args = m.args ∧
      (∃ s, M.get? m.args[0]! = some s ∧ s.op = .SP) ∧
      ∃ s, f.value? m.args[0]! = some s ∧ s.op = .SP := by
  unfold spFinal at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, ?_, ?_⟩
  · cases hs : M.get? m.args[0]! with
    | none => rw [hs] at h9; cases h9
    | some s => rw [hs] at h9; exact ⟨s, by simp [hs], by simpa using h9⟩
  · cases hs : f.value? m.args[0]! with
    | none => rw [hs] at h10; cases h10
    | some s => rw [hs] at h10; exact ⟨s, by simp [hs], by simpa using h10⟩

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
              truncReachL tabs M M.size m.op m.auxInt j m.args[j] u.args[j] = true ∨
              truncFitL tabs M M.size m j m.args[j] u.args[j] = true ∨
              lowReachL tabs M M.size m j m.args[j] u.args[j] = true) ∨
         (m.op = .ARM64LoweredPanicBoundsRR ∧ m.args.size = 3 ∧ (f.value? x).any (pbLower · u) ∧
          ∃ ks, pbKeep u.op = some ks ∧ u.args.size = ks.length ∧
            ∀ j (h : j < ks.length), copyReachL tabs M M.size m.args[ks[j]]! u.args[j]! = true) ∨
         frameFinal tabs f M x m u = true ∨ spFinal f M x m u = true) := by
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
        rcases this with (((this | ⟨ht, hr⟩) | hpb) | hff) | hsp
        · obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, hop⟩, hty⟩, hai⟩, hax⟩, hsz⟩, hargs⟩ := this
          refine ⟨m, u, hm, hu, hty, hai, .inl ⟨hop, hax, hsz, fun j h1 h2 => ?_⟩⟩
          have := List.all_eq_true.1 hargs j (List.mem_range.2 h1)
          simpa [getElem!_pos m.args j h1, getElem!_pos u.args j h2, or_assoc] using this
        · rcases hrd with hrd | hrd
          · exact absurd hrd hr
          · rw [hrd u hu] at ht; cases ht
        · unfold pbFinal at hpb
          simp only [Bool.and_eq_true, beq_iff_eq] at hpb
          obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, hop⟩, hty⟩, hai⟩, hm3⟩, hpl⟩, hk⟩ := hpb
          refine ⟨m, u, hm, hu, hty, hai, .inr (.inl ⟨hop, hm3, hpl, ?_⟩)⟩
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
        · obtain ⟨-, -, -, -, -, hty, hai, -⟩ := frameFinal_cases hff
          exact ⟨m, u, hm, hu, hty, hai, .inr (.inr (.inl hff))⟩
        · obtain ⟨-, -, -, -, hty, hai, -⟩ := spFinal_cases hsp
          exact ⟨m, u, hm, hu, hty, hai, .inr (.inr (.inr hsp))⟩
      · cases this
  · cases this

/-! ## The final definitions -/

theorem narrowReadW_makeResult (ai : Int64) (i : Nat) : narrowReadW .MakeResult ai i = none := by
  have he : extReadW .MakeResult = none := by decide
  have hw : w32Op .MakeResult = false := by decide
  simp [narrowReadW, he, hw]

/-- `OffPtr [k]` of `poison` or the stack pointer's word is refined by `MOVDaddr [k]` without aux
of a refinement (`spFinal`): both move the stack pointer by `k`, inside the outgoing-arguments
block's window (`Ptr.ofAddr_add_of_inWindow`), or `OffPtr` gives `poison`. -/
private theorem offPtr_sp_le (tabs : Tables) (T : Ty) (k : Int64) {a b : Val}
    (ha : a = .poison ∨ a = (spPtr 0).word) (hab : Sem.Refines a b) :
    Sem.Refines ((PtrOps.offPtr k [a]).retypeL T) ((movAddr tabs k none [b]).retypeL T) := by
  rcases ha with rfl | rfl
  · rw [show PtrOps.offPtr k [.poison] = .poison from rfl, retypeL_poison]; exact .poison _
  · have hb : b = (spPtr 0).word := asPtrWord_of_refines hab (Ptr.word_asPtrWord rfl)
    subst hb
    cases hq : (spPtr 0).convertible
    · have hw : (spPtr 0).word = .ptr (spPtr 0) := by
        rcases Ptr.word_cases (spPtr 0) with ⟨-, h⟩ | ⟨hc, -⟩ | ⟨hw', -⟩
        · exact h
        · rw [hq] at hc; cases hc
        · exact absurd hw' (by decide)
      rw [hw]
      exact Sem.Refines.refl _
    obtain ⟨X, hX⟩ : ∃ X, (spPtr 0).addr? = some X :=
      Option.isSome_iff_exists.1 (Ptr.addr?_isSome_of_convertible hq)
    have hw : (spPtr 0).word = .int .w64 X := by unfold Ptr.word; rw [hq, hX]
    have hoX : Ptr.ofAddr X = spPtr 0 := Ptr.ofAddr_addr hq hX
    rw [hw]
    have hl : PtrOps.offPtr k [.int .w64 X] = PtrOps.ptrRes ((spPtr 0).add (BitVec.ofInt 64 k.toInt)) :=
      PtrOps.wordRes_addr hq hX _
    have hr : movAddr tabs k none [.int .w64 X] =
        PtrOps.ptrRes (Ptr.ofAddr (X + BitVec.ofInt 64 k.toInt)) := rfl
    rw [hl, hr]
    by_cases hin : ((spPtr 0).add (BitVec.ofInt 64 k.toInt)).inWindow = true
    · rw [Ptr.ofAddr_add_of_inWindow (by rw [hoX]; exact hin), hoX]
      exact Sem.Refines.refl _
    · rw [show PtrOps.ptrRes ((spPtr 0).add (BitVec.ofInt 64 k.toInt)) = .poison by
        unfold PtrOps.ptrRes; rw [if_neg hin], retypeL_poison]
      exact .poison _

/-- The replayed definitions refine, in lowered mode, those listed in `g` and read by `g` (up to
the copies `finalOKL` allows), for valuations related at `g`'s listed atoms and holding the frame
addresses and the stack pointer of activation 0 (`FrameVals` of `f`'s `LocalAddr`s, which `M`
keeps as atoms, `FrameValsL` of `g`'s lowered frame addresses: `frameFinal`; `SPVals` of `f`'s
`SP`: `spFinal`). -/
theorem final_denL {tabs : Tables} {f g : Func} {M : Defs} {B : BMapL}
    (hfin : finalOKL tabs f g M B = true) (hcg : closedOK g = true) {ρ ρ' : ID → Val}
    (hρ : ∀ a u, listedDefs g a = some u → termVL tabs u = false → Sem.Refines (ρ a) (ρ' a))
    (hT : TypedL true M.get? tabs ρ) (hF : FrameVals tabs 0 f.value? ρ)
    (hS : SPVals tabs 0 f.value? ρ) (hFT : FrameValsL tabs 0 (listedDefs g) ρ') :
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
    rcases hcase with ⟨hop, hax, hsz, hargs⟩ | ⟨hop, -, -, ks, hks, -, -⟩ | hff | hsp
    case inr.inr.inr =>
      -- the stack pointer moved by an offset where the replay keeps `OffPtr` of it (`spFinal`):
      -- `OffPtr` of `poison` or the stack pointer's word (`SPVals`), refined by the output's
      -- `MOVDaddr` of a refinement
      obtain ⟨-, hmop, huop, hux, hty', hai', hm1, hua, ⟨s, hs, hsop⟩, s', hs', hs'op⟩ :=
        spFinal_cases hsp
      have hmt : termVL tabs m = true := by rw [termVL_gen (by decide) hmop]; decide
      have hut : termVL tabs u = true := by
        rw [termVL_movDaddr huop, hux]; simp [GoFV.Opt.LowerTerm.auxIsName]
      have hst : termVL tabs s = false := by rw [termVL_gen (by decide) hsop]; decide
      have hm0 : m.args[0]! ∈ u.args := by
        rw [hua, getElem!_pos m.args 0 (by omega)]; exact Array.getElem_mem _
      have hrec := final_denL hfin hcg hρ hT hF hS hFT n m.args[0]!
        ((closedOK_facts hcg b hb gb hgb).2 x hxv u hu _ hm0)
        ((liveOKL_facts hlive) b hb gb hgb |>.2 x hxv u hu (.inr hr) _ hm0)
      have hsp0 : denL true M.get? tabs ρ n m.args[0]! = .poison ∨
          denL true M.get? tabs ρ n m.args[0]! = (spPtr 0).word := by
        cases n with
        | zero => exact .inl rfl
        | succ k =>
          have hnt : ¬ IsTermL tabs M.get? m.args[0]! := fun ⟨w, hw, hw'⟩ => by
            rw [hs] at hw; cases hw; rw [hst] at hw'; cases hw'
          rw [denL_succ_atom hnt]
          rcases hS _ s' hs' hs'op with h | ⟨h, -⟩
          · exact .inl h
          · exact .inr h
      have hop1 : ∀ T ai ax args, opValL tabs .OffPtr T ai ax args = PtrOps.offPtr ai args :=
        fun T ai ax args => by
          simp only [opValL, show Op.OffPtr.generic = true from rfl, ite_true]
          rw [GoFV.Proof.Rules.opVal_pure (by decide)]; rfl
      rw [denT_succ hm hmt, denT_succ hL hut, hmop, huop, hux, hty', hai', hua,
        toList_of_size_one hm1]
      simp only [List.map_cons, List.map_nil]
      rw [hop1, opValL_movDaddr]
      exact offPtr_sp_le tabs _ _ hsp0 hrec
    case inr.inr.inl =>
      -- a lowered frame address where the replay keeps `ADDconst [0]` of it (`frameFinal`):
      -- `poison` or the frame variable's address word, which the output's atom holds
      obtain ⟨-, huop, hut, husz, -, -, -, huw, a, l, v, hfa, hlax, hv, hvop, hvax⟩ :=
        frameFinal_cases hff
      obtain ⟨n0, hn0⟩ : ∃ n0, u.aux = some n0 := by
        cases hux : u.aux with
        | none =>
          have := (movDaddr_atom huop hut).1
          rw [hux] at this
          simp [GoFV.Opt.LowerTerm.auxIsName] at this
        | some n0 => exact ⟨n0, rfl⟩
      have h2 : ¬ IsTermL tabs (listedDefs g) x := fun ⟨w, hw, hw'⟩ => by
        rw [hL] at hw; cases hw; rw [hut] at hw'; cases hw'
      rw [denL_succ_atom h2, hFT x u n0 hL huop hn0 hut husz huw]
      rcases frameAddr_den (D₀ := f.value?) (fun _ => rfl) hfa hv hvop (hvax.trans hn0)
          (hlax.trans hn0) hF (n + 1) with h | h <;> rw [h]
      · exact .poison _
      · exact Sem.Refines.refl _
    case inr.inl =>
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
      have hrec : ∀ j (h2 : j < u.args.size), Sem.Refines (denL true M.get? tabs ρ n u.args[j])
          (denL true (listedDefs g) tabs ρ' n u.args[j]) := fun j h2 =>
        final_denL hfin hcg hρ hT hF hS hFT n _ (hcl _ (Array.getElem_mem h2))
          ((liveOKL_facts hlive) b hb gb hgb |>.2 x hxv u hu (.inr hr) _ (Array.getElem_mem h2))
      -- an argument through a narrowing `Copy` (`truncFromL`): the output's argument narrowed
      have hnarrow : ∀ j (h1 : j < m.args.size) (h2 : j < u.args.size) {k : Nat},
          truncFromL tabs M M.size k m.args[j] u.args[j] = true → ∃ w : Width, k ≤ w.bits ∧
            w ≠ .w64 ∧ Sem.Refines (denL true M.get? tabs ρ n m.args[j])
              ((denL true (listedDefs g) tabs ρ' n u.args[j]).retypeL (.int w)) := by
        intro j h1 h2 k htf
        obtain ⟨w, hkw, hw64, hd⟩ := truncFrom_den hT htf
        exact ⟨w, hkw, hw64, (hd n).trans (retypeL_mono _ (hrec j h2))⟩
      cases hlw : lowShape tabs M m
      case some k =>
        -- an op of `lowOpArgs` at a narrow shape: its data arguments' low bits (`lowReachL`)
        obtain ⟨w, d, hsh, hd, hw64, rfl, -, hnar⟩ := lowShape_cases hlw
        have hno : ∀ j (h1 : j < m.args.size) (h2 : j < u.args.size),
            copyReachL tabs M M.size m.args[j] u.args[j] = true ∨
              lowReachL tabs M M.size m j m.args[j] u.args[j] = true := fun j h1 h2 => by
          rcases hargs j h1 h2 with h | h | h | h
          · exact .inl h
          · obtain ⟨k, hk, -⟩ := truncReachL_cases h
            rw [narrowReadW_low hd] at hk; cases hk
          · obtain ⟨_, hf, -⟩ := truncFitL_cases h
            rw [argFitTy_low hd] at hf; cases hf
          · exact .inr h
        rw [hsh, opValL_low hd, opValL_low hd]
        refine lowOp_mono hd hw64 _ _ (by simp [hsz]) (fun j h1 h2 hj => ?_) (fun j h1 h2 hj => ?_)
        all_goals
          simp only [List.length_map, Array.length_toList] at h1 h2
          simp only [List.getElem_map, Array.getElem_toList]
        · rcases hno j h1 h2 with hcp | hlr
          · obtain ⟨y, w', hy, hyw, hw'⟩ := hnar j hj
            rw [getElem!_pos m.args j h1] at hy
            exact rlow_of_narrow (by rw [← hyw]; exact den_hasTyL hT n hy) hw'
              ((copyReachL_den hT _ _ _ hcp n).trans (hrec j h2))
          · obtain ⟨w', hkw, hw64', hd'⟩ := hnarrow j h1 h2 (lowReachL_cases hlw hlr)
            exact rlow_of_le hd' (rlow_retypeL hkw hw64' (Sem.Refines.refl _))
        · rcases hno j h1 h2 with hcp | hlr
          · exact (copyReachL_den hT _ _ _ hcp n).trans (hrec j h2)
          · simp only [lowReachL, hlw, hd, Option.any_some, Option.getD_some, Bool.and_eq_true,
              decide_eq_true_eq] at hlr
            omega
      by_cases hmr : m.op = .MakeResult
      · -- a `MakeResult`: its tuple read at its shape, each leaf through a copy or a narrowing
        -- `Copy` at least as wide (`truncFitL`)
        rw [hmr, opValL_makeResult, opValL_makeResult]
        cases hs : shpL tabs m.type
        case tuple ts =>
          refine tuple_retypeL_fit (by simp [hsz]) fun i h1 h2 => ?_
          simp only [List.length_map, Array.length_toList] at h1 h2
          simp only [List.getElem_map, Array.getElem_toList]
          rcases hargs i h1 h2 with hcp | htr | hfit | hlr
          · have := (copyReachL_den hT _ _ _ hcp n).trans (hrec i h2)
            exact ⟨fun t _ => retypeL_mono t this, fun _ => this⟩
          · obtain ⟨k, hk, -⟩ := truncReachL_cases htr
            rw [hmr, narrowReadW_makeResult] at hk; cases hk
          · obtain ⟨w', hf, htf⟩ := truncFitL_cases hfit
            have hti : ts[i]? = some (.int w') := by
              rcases argFitTy_cases hf with ⟨hk, -⟩ | ⟨hp, -⟩ | ⟨-, ts', hts', hti⟩ | ⟨-, hst⟩
              · rw [hmr] at hk; cases hk
              · rw [hmr] at hp; cases hp
              · rw [hs] at hts'; cases hts'; exact hti
              · rcases stFitTy_ops hst with h | h | h | h | h | h | h | h <;> rw [hmr] at h <;>
                  cases h
            refine ⟨fun t ht => ?_, fun h => by rw [hti] at h; cases h⟩
            rw [hti] at ht; cases ht
            obtain ⟨w, hww, hw64, hd'⟩ := hnarrow i h1 h2 htf
            exact (retypeL_mono _ hd').trans (retypeL_narrow_twice hww hw64 _)
          · rw [lowReachL_none hlw] at hlr; cases hlr
        all_goals
          rw [tuple_retypeL_other (fun _ h => by cases h), tuple_retypeL_other (fun _ h => by cases h)]
          exact .poison _
      apply retypeL_mono
      by_cases hall : ∀ j (h1 : j < m.args.size) (h2 : j < u.args.size),
          copyReachL tabs M M.size m.args[j] u.args[j] = true
      · apply opValL_mono_term ht
        refine refinesList_idx (by simp [hsz]) fun j h1 h2 => ?_
        simp only [Array.getElem_toList]
        exact (copyReachL_den hT _ _ _ (hall j (by simpa using h1) (by simpa using h2)) n).trans
          (hrec j (by simpa using h2))
      · -- an extension, `TSTWconst` or a `W` op with arguments through narrowing copies
        -- (`truncReachL`, `opValL_narrow_mono`); a lowered call and a `Phi` are no terms
        -- (`termVL_callFit`, `termVL_phi`), and an op without a `lowShape` reaches no argument by
        -- `lowReachL`
        replace hargs : ∀ j (h1 : j < m.args.size) (h2 : j < u.args.size),
            copyReachL tabs M M.size m.args[j] u.args[j] = true ∨
              truncReachL tabs M M.size m.op m.auxInt j m.args[j] u.args[j] = true :=
            fun j h1 h2 => by
          rcases hargs j h1 h2 with h | h | h | h
          · exact .inl h
          · exact .inr h
          · obtain ⟨_, hf, -⟩ := truncFitL_cases h
            rcases argFitTy_cases hf with ⟨-, hcf⟩ | ⟨hp, -⟩ | ⟨hr, -⟩ | ⟨-, hst⟩
            · rw [termVL_callFit hcf] at ht; cases ht
            · rw [termVL_phi hp] at ht; cases ht
            · exact absurd hr hmr
            · rw [termVL_stFit hst] at ht; cases ht
          · rw [lowReachL_none hlw] at h; cases h
        simp only [Classical.not_forall] at hall
        obtain ⟨j, h1, h2, hj⟩ := hall
        obtain ⟨k, hk, -⟩ := truncReachL_cases ((hargs j h1 h2).resolve_left (by simpa using hj))
        refine opValL_narrow_mono hk _ _ (by simp [hsz]) fun i i1 i2 => ?_
        simp only [List.length_map, Array.length_toList] at i1 i2
        simp only [List.getElem_map, Array.getElem_toList]
        rcases hargs i i1 i2 with hcp | htr
        · exact .inl ((copyReachL_den hT _ _ _ hcp n).trans (hrec i i2))
        · obtain ⟨k', hk', htf⟩ := truncReachL_cases htr
          obtain ⟨w, hkw, hw64, hd'⟩ := hnarrow i i1 i2 htf
          exact .inr ⟨k', w, hk', hkw, hw64, hd'⟩
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

theorem mid_sp {tabs : Tables} {f : Func} {ρ : ID → Val} {act : Nat}
    (hS : SPVals tabs act f.value? ρ) : SPVals tabs act f.value? (midVal tabs f ρ) := by
  intro a s hs hop
  have hst : termVL tabs s = false := by rw [termVL_gen (by decide) hop]; decide
  simp only [midVal, hs, hst, Bool.false_eq_true, ite_false]
  rcases hS a s hs hop with h | ⟨h, hw⟩
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
        rcases hat a hbv w hg hut with ⟨-, u', hu', hp, -, hu't⟩ | hfa
        · have hty := atomPair_type hp
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
        · -- a lowered frame address where `f` has a term: `midVal` keeps the term's valuation
          unfold frameAtomG at hfa
          simp only [Bool.and_eq_true] at hfa
          cases hu' : f.value? a with
          | none => rw [hu'] at hfa; simp at hfa
          | some u' =>
            rw [hu'] at hfa
            simp only [Option.any_some] at hfa
            simp only [midVal, hu', hfa.2, ite_true]
            exact hρ a
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
      rcases hatoms a ha u hu hat with ⟨haf, u', hu', hp, hpc, hu't⟩ | hfa
      case inr => exact .inl hfa
      refine .inr ⟨u', hu', hp, hpc, ?_⟩
      have hbf : b ∈ f.blocks := hbl ▸ hb
      have hargsf := (closedOK_facts hcf b hbf fb hfb).2 a haf u' hu'
      obtain ⟨a'', ha'', ha''t, hrest⟩ := hI.atoms a u' hu' hu't hargsf
      obtain ⟨-, -, -, -, -, -, -, -, -, -, hvals⟩ := hfacts b hb gb hgb
      obtain ⟨m, w, hm, hw, hwty, hai, hcase⟩ := hvals a ha
        (.inr fun w hw => by rw [hu] at hw; cases hw; exact hat)
      have hma : m = a'' := Option.some.inj (hm.symm.trans ha'')
      subst hma
      have huw : u = w := Option.some.inj (hu.symm.trans hw)
      subst huw
      rcases hcase with ⟨hop, hax, hszw, hargs⟩ | ⟨hmop, hm3, hpl, ks, hks, hszk, hargs⟩ | hff | hsp
      case inr.inr.inl =>
        -- a lowered frame address relates to a replayed term, not to `f`'s atom
        rw [(frameFinal_cases hff).2.2.2.2.1] at ha''t; cases ha''t
      case inr.inr.inr =>
        -- the stack pointer moved by an offset is a term, not an atom
        obtain ⟨-, -, huop, hux, -⟩ := spFinal_cases hsp
        rw [termVL_movDaddr huop, hux] at hat; simp [GoFV.Opt.LowerTerm.auxIsName] at hat
      case inr.inl =>
        -- a bounds panic with constant operands: the kept arguments of the replayed
        -- `LoweredPanicBoundsRR`, which are `f`'s (`argIx`)
        rw [hu'] at hpl
        have hpl' : pbLower u' u = true := by simpa using hpl
        rcases hrest with hfree | ⟨hsz'', hrest, -⟩ | hidx | hmv
        · rw [(argFree_cases hfree).1] at hmop; cases hmop
        rotate_left
        · obtain ⟨⟨p, s⟩, hio⟩ := Option.isSome_iff_exists.1 hidx.2.2.1
          rw [hmop] at hio; cases hio
        · have := hmv.2.2.1; rw [hmop] at this; cases this
        have hu'op := (pbLower_cases hpl').1
        have hnix : idxLower tabs u' u = false := by
          cases hix : idxLower tabs u' u
          · rfl
          · rw [(idxLower_cases hix).1] at hu'op; cases hu'op
        have hnmq : moveQLower tabs u' u = false := by
          cases hq : moveQLower tabs u' u
          · rfl
          · unfold moveQLower at hq; simp only [Bool.and_eq_true, beq_iff_eq] at hq
            rw [hq.1.1.1.1] at hu'op; cases hu'op
        refine .inr (.inl ⟨hnix, hnmq, fun i hi => ?_⟩)
        have hik : i < ks.length := hszk ▸ hi
        have hix := argIx_of_pb hpl' hks hik
        have hk3 := pbKeep_lt hks hik
        have hk' : ks[i] < u'.args.size := by omega
        have hcopy := hargs i hik
        rw [getElem!_pos u.args i hi] at hcopy
        have hmark := (closedOK_facts hcg b hb gb hgb).2 a ha u hu u.args[i] (Array.getElem_mem hi)
        have hlv : LiveL tabs g u.args[i] :=
          (liveOKL_facts hlive) b hb gb hgb |>.2 a ha u hu (.inl hat) _ (Array.getElem_mem hi)
        left
        intro n
        obtain ⟨k, hk⟩ := (hrest ks[i] hk').2 n
        refine ⟨k, fun ρ ρ' hρ hT hT' hF hS hFT => ?_⟩
        rw [hgl] at hT'
        rw [hgl, getElem!_pos u.args i hi, hix, stArg_of_ne (by rw [hu'op]; decide)]
        have h1 := hk (midVal tabs f ρ) (mid_typed tabs f ρ) (mid_frame hF)
        rw [stArg_of_ne (by rw [hu'op]; decide)] at h1
        exact ArgRel.trans_left (bridge_den hsh hT n _) (h1.trans_right
          ((copyReachL_den (hTM ρ) _ _ _ hcopy k).trans
            (final_denL hv hcg (mid_le_target hA hρ hT') (hTM ρ) (mid_frame hF) (mid_sp hS) hFT k _ hmark hlv)))
      have hcopy : ∀ j (h1 : j < m.args.size) (h2 : j < u.args.size),
          copyReachL tabs M M.size m.args[j] u.args[j] = true ∨
            truncFitL tabs M M.size m j m.args[j] u.args[j] = true := fun j h1 h2 => by
        rcases hargs j h1 h2 with h | h | h | h
        · exact .inl h
        · obtain ⟨k, hk, -⟩ := truncReachL_cases h
          rw [← hop] at hk
          rw [termVL_narrow hk] at hat; cases hat
        · exact .inr h
        · cases hlw : lowShape tabs M m with
          | none => rw [lowReachL_none hlw] at h; cases h
          | some k =>
            obtain ⟨-, d, -, hd, -⟩ := lowShape_cases hlw
            rw [← hop] at hd
            rw [termVL_low hd] at hat; cases hat
      rcases hrest with hfree | ⟨hsz'', hrest, hq3⟩ | ⟨h3, h4, hixs, hC, hAd, hV⟩ |
          ⟨hmvop, hm3, hmq, hm3', hmC, hmA, hmV, hmM⟩
      · exact .inl (by rw [argFree_congr hop hax]; exact hfree)
      rotate_left
      · -- a `Store` lowered to an indexed store: the address from the base and the index, the
        -- value and the memory
        obtain ⟨⟨p, s⟩, hio⟩ := Option.isSome_iff_exists.1 hixs
        have hix : idxLower tabs u' u = true := by
          have hpa := hp
          unfold atomPair at hpa
          simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hpa
          rcases hpa.1.1.1 with (((⟨-, hs⟩ | hal) | hpb) | hx) | hmq'
          · omega
          · have := (addrLower_cases hal).2.2.2.2.2; omega
          · obtain ⟨-, -, -, ks, hks, -⟩ := pbLower_cases hpb
            rw [hop, (idxStore_facts hio).2.2.2.2.2.2.1] at hks; cases hks
          · exact hx
          · have := (qStore_st (moveQLower_qStore hmq').2.2).2
            rw [hop, hio] at this; cases this
        have hden : ∀ j (h1 : j < m.args.size) (h2 : j < u.args.size), j ≠ 2 → ∀ (k : Nat)
            (ρ ρ' : ID → Val), ValRef ρ ρ' → TypedL true (listedDefs g) tabs ρ' →
            FrameVals tabs 0 f.value? ρ → SPVals tabs 0 f.value? ρ →
            FrameValsL tabs 0 (listedDefs g) ρ' →
            Sem.Refines (denL true M.get? tabs (midVal tabs f ρ) k m.args[j]!)
              (denL true (listedDefs g) tabs ρ' k u.args[j]!) :=
            fun j h1 h2 hj k ρ ρ' hρ hT' hF hS hFT => by
          rw [getElem!_pos m.args j h1, getElem!_pos u.args j h2]
          have hc := (hcopy j h1 h2).resolve_right fun hfit => by
            obtain ⟨w', hcf, -⟩ := truncFitL_cases hfit
            rcases argFitTy_cases hcf with ⟨hk, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hst⟩
            · obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hk
              rcases callLead_some hk with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at hio <;> cases hio
            · rw [h] at hio; cases hio
            · rw [h] at hio; cases hio
            · obtain ⟨w0, -, ⟨-, hw''⟩ | ⟨rfl, -⟩⟩ := stFitTy_cases hst
              · rcases stValW_some hw'' with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at hio <;>
                  cases hio
              · exact hj rfl
          exact (copyReachL_den (hTM ρ) _ _ _ hc k).trans
            (final_denL hv hcg (mid_le_target hA hρ hT') (hTM ρ) (mid_frame hF) (mid_sp hS) hFT k _
              ((closedOK_facts hcg b hb gb hgb).2 a ha u hu u.args[j] (Array.getElem_mem h2))
              ((liveOKL_facts hlive) b hb gb hgb |>.2 a ha u hu (.inl hat) _
                (Array.getElem_mem h2)))
        have hmark2 := (closedOK_facts hcg b hb gb hgb).2 a ha u hu u.args[2]
          (Array.getElem_mem (by omega))
        have hlv2 : LiveL tabs g u.args[2] :=
          (liveOKL_facts hlive) b hb gb hgb |>.2 a ha u hu (.inl hat) _ (Array.getElem_mem (by omega))
        refine .inr (.inr (.inl ⟨hix, fun n => ?_, ?_, fun n => ?_⟩))
        · obtain ⟨k, hk⟩ := hAd n
          refine ⟨k, fun ρ ρ' hρ hT hT' hF hS hFT => ?_⟩
          rw [hgl] at hT'
          rw [hgl, hop]
          have h1 := hk (midVal tabs f ρ) (mid_typed tabs f ρ) (mid_frame hF)
          exact ArgRel.trans_left (o := some (0, none)) (bridge_den hsh hT n _)
            (ArgRel.trans_right (o := some (0, none)) h1 (idxAddr_mono _
              (hden 0 (by omega) (by omega) (by omega) k ρ ρ' hρ hT' hF hS hFT)
              (hden 1 (by omega) (by omega) (by omega) k ρ ρ' hρ hT' hF hS hFT)))
        · rcases hcopy 2 (by omega) (by omega) with hc2 | hfit2
          · left
            intro n
            obtain ⟨k, hk⟩ := hV 0 (by omega) n
            refine ⟨k, fun ρ ρ' hρ hT hT' hF hS hFT => ?_⟩
            rw [hgl] at hT'
            rw [hgl, getElem!_pos u.args 2 (by omega)]
            have h1 := hk (midVal tabs f ρ) (mid_typed tabs f ρ) (mid_frame hF)
            rw [getElem!_pos m.args 2 (by omega)] at h1
            exact ArgRel.trans_left (bridge_den hsh hT n _) (h1.trans_right
              ((copyReachL_den (hTM ρ) _ _ _ hc2 k).trans
                (final_denL hv hcg (mid_le_target hA hρ hT') (hTM ρ) (mid_frame hF) (mid_sp hS) hFT k _ hmark2
                  hlv2)))
          · -- the value through a narrowing `Copy` of at least the store's width
            right
            obtain ⟨w', hcf, htf⟩ := truncFitL_cases hfit2
            have hcfu : argFitTy tabs u 2 = some (.int w') := by
              rw [← hcf]; unfold argFitTy atomFitTy stFitTy callFitTy callIns; rw [hop, hax, hwty]
            refine ⟨.int w', hcfu, fun n => ?_⟩
            obtain ⟨k, hk⟩ := hV 0 (by omega) n
            refine ⟨k, fun ρ ρ' hρ hT hT' hF hS hFT => ?_⟩
            rw [hgl] at hT'
            rw [hgl, getElem!_pos u.args 2 (by omega)]
            have h1 := hk (midVal tabs f ρ) (mid_typed tabs f ρ) (mid_frame hF)
            rw [getElem!_pos m.args 2 (by omega)] at h1
            have h1' : Sem.Refines _ _ := h1
            obtain ⟨w, hww, hw64, hd⟩ := truncFrom_den (hTM ρ) htf
            have h2 := (bridge_den hsh hT n _).trans (h1'.trans (hd k))
            exact (fitPiece_mono _ h2).trans ((fitPiece_retypeL hww hw64 _).trans (fitPiece_mono _
              (final_denL hv hcg (mid_le_target hA hρ hT') (hTM ρ) (mid_frame hF) (mid_sp hS) hFT k _
                hmark2 hlv2)))
        · obtain ⟨k, hk⟩ := hV 1 (by omega) n
          refine ⟨k, fun ρ ρ' hρ hT hT' hF hS hFT => ?_⟩
          rw [hgl] at hT'
          rw [hgl]
          have h1 := hk (midVal tabs f ρ) (mid_typed tabs f ρ) (mid_frame hF)
          exact ArgRel.trans_left (bridge_den hsh hT n _)
            (h1.trans_right (hden 3 (by omega) (by omega) (by omega) k ρ ρ' hρ hT' hF hS hFT))
      · -- a `Move` lowered to a 128-bit store: the address at the store's offset and aux, the
        -- halves the `Move` copies and the memory
        have hdenM : ∀ j (h1 : j < m.args.size) (h2 : j < u.args.size) (k : Nat)
            (ρ ρ' : ID → Val), ValRef ρ ρ' → TypedL true (listedDefs g) tabs ρ' →
            FrameVals tabs 0 f.value? ρ → SPVals tabs 0 f.value? ρ →
            FrameValsL tabs 0 (listedDefs g) ρ' →
            Sem.Refines (denL true M.get? tabs (midVal tabs f ρ) k m.args[j]!)
              (denL true (listedDefs g) tabs ρ' k u.args[j]!) :=
            fun j h1 h2 k ρ ρ' hρ hT' hF hS hFT => by
          rw [getElem!_pos m.args j h1, getElem!_pos u.args j h2]
          have hc := (hcopy j h1 h2).resolve_right fun hfit => by
            obtain ⟨w', hcf, -⟩ := truncFitL_cases hfit
            rw [argFitTy_qStore hmq] at hcf; cases hcf
          exact (copyReachL_den (hTM ρ) _ _ _ hc k).trans
            (final_denL hv hcg (mid_le_target hA hρ hT') (hTM ρ) (mid_frame hF) (mid_sp hS) hFT k _
              ((closedOK_facts hcg b hb gb hgb).2 a ha u hu u.args[j] (Array.getElem_mem h2))
              ((liveOKL_facts hlive) b hb gb hgb |>.2 a ha u hu (.inl hat) _
                (Array.getElem_mem h2)))
        refine .inr (.inr (.inr ⟨atomPair_moveQ hp hmvop (by rw [hop]; exact hmq), fun n => ?_,
          fun i hi n => ?_, fun n => ?_⟩))
        · obtain ⟨k, hk⟩ := hmA n
          refine ⟨k, fun ρ ρ' hρ hT hT' hF hS hFT => ?_⟩
          rw [hgl] at hT'
          rw [hgl, hai, hax]
          have h1 := hk (midVal tabs f ρ) (mid_typed tabs f ρ) (mid_frame hF)
          exact ArgRel.trans_left (o := some (m.auxInt, m.aux)) (bridge_den hsh hT n _)
            (ArgRel.trans_right (o := some (m.auxInt, m.aux)) h1
              (hdenM 0 (by omega) (by omega) k ρ ρ' hρ hT' hF hS hFT))
        · obtain ⟨k, hk⟩ := hmV i (by omega) n
          refine ⟨k, fun ρ ρ' hρ hT hT' hF hS hFT => ?_⟩
          rw [hgl] at hT'
          rw [hgl]
          have h1 := hk (midVal tabs f ρ) (mid_typed tabs f ρ) (mid_frame hF)
          exact (qPart_mono i (bridge_den hsh hT n _) (bridge_den hsh hT n _)).trans
            (h1.trans (hdenM (i + 1) (by omega) (by omega) k ρ ρ' hρ hT' hF hS hFT))
        · obtain ⟨k, hk⟩ := hmM n
          refine ⟨k, fun ρ ρ' hρ hT hT' hF hS hFT => ?_⟩
          rw [hgl] at hT'
          rw [hgl, show u.args.size - 1 = m.args.size - 1 by omega]
          have h1 := hk (midVal tabs f ρ) (mid_typed tabs f ρ) (mid_frame hF)
          exact (bridge_den hsh hT n _).trans
            (h1.trans (hdenM _ (by omega) (by omega) k ρ ρ' hρ hT' hF hS hFT))
      have hnpb : pbLower u' u = false := by
        cases hpb : pbLower u' u
        · rfl
        · exfalso
          obtain ⟨-, h3, -, ks, hks, hsk⟩ := pbLower_cases hpb
          have := pbKeep_len hks
          omega
      have hnix : idxLower tabs u' u = false := by
        cases hix : idxLower tabs u' u
        · rfl
        · obtain ⟨-, h3, h4, -⟩ := idxLower_cases hix
          omega
      have hnmq : moveQLower tabs u' u = false := by
        cases hq : moveQLower tabs u' u
        · rfl
        · obtain ⟨hu'm, -, hqu⟩ := moveQLower_qStore hq
          rw [hop, hq3 hu'm] at hqu; cases hqu
      refine .inr (.inl ⟨hnix, hnmq, fun i hi => ?_⟩)
      rw [argIx_of_not hnpb]
      have hi' : i < u'.args.size := by omega
      have hmark := (closedOK_facts hcg b hb gb hgb).2 a ha u hu u.args[i] (Array.getElem_mem hi)
      have hlv : LiveL tabs g u.args[i] :=
        (liveOKL_facts hlive) b hb gb hgb |>.2 a ha u hu (.inl hat) _ (Array.getElem_mem hi)
      rcases hcopy i (by omega) hi with hcopy | hcall
      · left
        intro n
        obtain ⟨k, hk⟩ := (hrest i hi').2 n
        refine ⟨k, fun ρ ρ' hρ hT hT' hF hS hFT => ?_⟩
        rw [hgl] at hT'
        rw [hgl, getElem!_pos u.args i hi]
        have h1 := hk (midVal tabs f ρ) (mid_typed tabs f ρ) (mid_frame hF)
        rw [getElem!_pos m.args i (by omega),
          stArg_congr (u := u') (i := i) hop.symm hai.symm hax.symm] at h1
        exact ArgRel.trans_left (bridge_den hsh hT n _) (h1.trans_right
          ((copyReachL_den (hTM ρ) _ _ _ hcopy k).trans
            (final_denL hv hcg (mid_le_target hA hρ hT') (hTM ρ) (mid_frame hF) (mid_sp hS) hFT k _ hmark hlv)))
      · -- an argument through a narrowing `Copy` of the leaf a lowered call, a `Phi` or a narrow
        -- integer store reads it at (a `MakeResult` is no atom)
        obtain ⟨w', hcf, htf⟩ := truncFitL_cases hcall
        have hcfu : argFitTy tabs u i = some (.int w') := by
          rw [← hcf]; unfold argFitTy atomFitTy stFitTy callFitTy callIns; rw [hop, hax, hwty]
        have hsa : ∀ x : Value, stArg x m i = none := by
          rcases argFitTy_cases hcf with ⟨hk, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hs1⟩
          · obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hk
            have hst : stSize m.op = none := by
              rcases callLead_some hk with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl
            exact fun x => stArg_none hst
          · exact fun x => stArg_none (by rw [h]; rfl)
          · rw [← hop] at h; rw [termVL_makeResult h] at hat; cases hat
          · obtain ⟨w0, -, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ := stFitTy_cases hs1
            · exact fun x => stArg_succ x m 0
            · exact fun x => stArg_succ x m 1
        right
        refine ⟨.int w', hcfu, fun n => ?_⟩
        obtain ⟨k, hk⟩ := (hrest i hi').2 n
        refine ⟨k, fun ρ ρ' hρ hT hT' hF hS hFT => ?_⟩
        rw [hgl] at hT'
        rw [hgl, getElem!_pos u.args i hi]
        have h1 := hk (midVal tabs f ρ) (mid_typed tabs f ρ) (mid_frame hF)
        rw [getElem!_pos m.args i (by omega), hsa] at h1
        have h1' : Sem.Refines _ _ := h1
        obtain ⟨w, hww, hw64, hd⟩ := truncFrom_den (hTM ρ) htf
        have h2 := (bridge_den hsh hT n _).trans (h1'.trans (hd k))
        exact (fitPiece_mono _ h2).trans ((fitPiece_retypeL hww hw64 _).trans (fitPiece_mono _
          (final_denL hv hcg (mid_le_target hA hρ hT') (hTM ρ) (mid_frame hF) (mid_sp hS) hFT k _ hmark
            hlv)))
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
        refine ⟨m, fun ρ ρ' hρ hT hT' hF hS hFT => ?_⟩
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
          (final_denL hv hcg (mid_le_target hA hρ hT') (hTM ρ) (mid_frame hF) (mid_sp hS) hFT m _
            ((closedOK_facts hcg b hb gb hgb).1 _ (Array.getElem_mem h2'))
            ((liveOKL_facts hlive) b hb gb hgb |>.1 _ (Array.getElem_mem h2')))
  · cases hv

end GoFV.Proof.Low.Val

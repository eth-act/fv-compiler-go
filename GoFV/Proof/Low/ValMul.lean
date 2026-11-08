import GoFV.Proof.Low.ValStep
import GoFV.Proof.Retype
import GoFV.Proof.PtrAddr

/-!
# A strength-reduced multiplication by a constant (issue #385)

`GoFV.Opt.LowerCheck.mulOKL` checks a rule event whose result is `mulStrengthReduce{,32}(v, x, c)`
(`ARM64.rules:1043`, `1044`) by its effect: `v`, a `MUL` or `MULW` of an operand `a` and a
`MOVDconst [c]` at an integer shape, becomes a `Copy` of a fresh value `m`, and the fresh values
`bs` the event built are linear combinations (`comboFn`) of `a` and values of `bs`.

`mul_step`: on a set closed under arguments, every lowered denotation after the event refines the
one before, with the fuel multiplied by the number of values the event defines. The source
multiplies the registers of `a`'s value `X` and of the constant. A pointer `X` is held as a
pointer (its shape, F1+F2 of #385), has no register, and the product is `poison`
(`mul_src`). Otherwise each built value is the integer whose bits are the multiple of `X`'s
register by its multiplier (`mulCoef`) in the bits of the shape (`combo_val`: each op is linear
and reads its arguments' low bits only, `comboFn_lin`), and the copy at `v` is `c` times it
there, as the product is.
-/

namespace GoFV.Proof.Low.Val

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Opt.LowerCheck GoFV.Proof.Low
open GoFV.Proof.Pass.Rewrite (putAll get?_putAll_not get?_putAll_mem get?_put defIds DefClosed)

/-! ## The linear combinations on registers -/

private theorem shifted_def (k : Int64) (b : BitVec 64) :
    Arm64.shifted .ll k b = b <<< (Arm64.amt k % 64) := rfl

private theorem shifted_mul (k : Int64) (c r : BitVec 64) :
    Arm64.shifted .ll k (c * r) = Arm64.shifted .ll k c * r := by
  simp only [shifted_def, BitVec.shiftLeft_eq_mul_twoPow]
  rw [BitVec.mul_assoc, BitVec.mul_comm r, ← BitVec.mul_assoc]

private theorem shifted_low {n : Nat} (hn : n ≤ 64) (k : Int64) {a b : BitVec 64}
    (h : a.setWidth n = b.setWidth n) :
    (Arm64.shifted .ll k a).setWidth n = (Arm64.shifted .ll k b).setWidth n := by
  simp only [shifted_def, BitVec.setWidth_shiftLeft_of_le hn, h]

private theorem add_low {n : Nat} (hn : n ≤ 64) {a a' b b' : BitVec 64}
    (ha : a.setWidth n = a'.setWidth n) (hb : b.setWidth n = b'.setWidth n) :
    (a + b).setWidth n = (a' + b').setWidth n := by
  rw [BitVec.setWidth_add _ _ hn, BitVec.setWidth_add _ _ hn, ha, hb]

private theorem neg_low {n : Nat} (hn : n ≤ 64) {a a' : BitVec 64}
    (ha : a.setWidth n = a'.setWidth n) : (-a).setWidth n = (-a').setWidth n := by
  rw [BitVec.setWidth_neg_of_le hn, BitVec.setWidth_neg_of_le hn, ha]

private theorem sub_mul' (a b r : BitVec 64) : a * r - b * r = (a - b) * r := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_mul, BitVec.neg_mul]

/-- **The combinations are linear and read their arguments' low bits only**: on registers equal
in their low `n` bits to multiples of `r` by the multipliers `cs`, `comboFn` is the multiple of
`r` by its value on `cs` there. -/
theorem comboFn_lin {n : Nat} (hn : n ≤ 64) {o : Op} {k : Int64} {cs zs : List (BitVec 64)}
    {c : BitVec 64} (r : BitVec 64) (h : comboFn o k cs = some c)
    (hz : List.Forall₂ (fun z c => z.setWidth n = (c * r).setWidth n) zs cs) :
    ∃ z, comboFn o k zs = some z ∧ z.setWidth n = (c * r).setWidth n := by
  match zs, cs, hz with
  | [z1, z2], [a, b], .cons h1 (.cons h2 .nil) =>
    unfold comboFn at h ⊢
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      refine ⟨_, rfl, ?_⟩
    · rw [add_low hn h1 h2, BitVec.add_mul]
    · rw [BitVec.sub_eq_add_neg, add_low hn h1 (neg_low hn h2), ← BitVec.sub_eq_add_neg, sub_mul']
    · rw [add_low hn h1 (shifted_low hn k h2), shifted_mul, BitVec.add_mul]
    · rw [add_low hn h1 (neg_low hn (shifted_low hn k h2)), shifted_mul, ← BitVec.neg_mul,
        BitVec.add_mul]
  | [z1], [a], .cons h1 .nil =>
    unfold comboFn at h ⊢
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      refine ⟨_, rfl, ?_⟩
    · rw [neg_low hn h1, BitVec.neg_mul]
    · rw [shifted_low hn k h1, shifted_mul]
    · rw [neg_low hn (shifted_low hn k h1), shifted_mul, BitVec.neg_mul]
  | [], [], .nil => simp [comboFn] at h
  | _ :: _ :: _ :: _, _ :: _ :: _ :: _, .cons _ (.cons _ (.cons _ _)) => simp [comboFn] at h

/-! ## Registers and values -/

theorem bits_le64 (w : Width) : w.bits ≤ 64 := by cases w <;> decide

/-- `V` is a value without provenance whose register is `c` times `r` in its low `n` bits. -/
def LinV (n : Nat) (r c : BitVec 64) (V : Val) : Prop :=
  (∀ p, V ≠ .ptr p) ∧ ∃ z, Arm64.reg V = some z ∧ z.setWidth n = (c * r).setWidth n

/-- A 64-bit register result at an integer shape is its low bits. -/
theorem retypeL_res_int (w : Width) (z : BitVec 64) :
    (Arm64.res (.int w) z).retypeL (.int w) = .int w (z.setWidth w.bits) := by
  cases w <;> simp [Arm64.res, Val.retypeL, Val.widen, Val.retype, Width.bits]

/-- An integer at its own width is fixed by `retypeL`. -/
theorem retypeL_int_self (w : Width) (y : BitVec w.bits) :
    (Val.int w y).retypeL (.int w) = .int w y := by
  cases w <;> simp [Val.retypeL, Val.widen, Val.retype, Width.bits]

theorem LinV.of_int {w : Width} {r c : BitVec 64} :
    LinV w.bits r c (.int w ((c * r).setWidth w.bits)) := by
  refine ⟨fun p h => by cases h, _, rfl, ?_⟩
  rw [BitVec.setWidth_setWidth_of_le _ (bits_le64 w), BitVec.setWidth_eq]

/-- The pure arm64 ops other than loads and `MOVDaddr` evaluate as `Arm64.evalPure`. -/
theorem opValL_evalPure {o : Op} (hg : o.generic = false) (hm : (o == .ARM64MOVDaddr) = false)
    (hl : ldOp? o = none) (tabs : Tables) (ty : Ty) (ai : Int64) (ax : Option AuxRef)
    (args : List Val) : opValL tabs o ty ai ax args = Arm64.evalPure o ty ai ax args := by
  simp only [opValL, hg, hm, hl, Bool.false_eq_true, ite_false]

private theorem add_np (T : Ty) {a b : Val} (ha : ∀ p, a ≠ .ptr p) (hb : ∀ p, b ≠ .ptr p) :
    Arm64.add T [a, b] = Arm64.op2 T (· + ·) [a, b] := by
  unfold Arm64.add; split <;> simp_all

private theorem sub_np (T : Ty) {a b : Val} (ha : ∀ p, a ≠ .ptr p) :
    Arm64.sub T [a, b] = Arm64.op2 T (· - ·) [a, b] := by
  unfold Arm64.sub; split <;> simp_all

private theorem addP_np (T : Ty) {a : Val} (ha : ∀ p, a ≠ .ptr p) (k : BitVec 64) :
    Arm64.addP T a k = match Arm64.reg a with
      | some x => Arm64.res T (x + k)
      | none => .poison := by
  unfold Arm64.addP; split
  · exact absurd rfl (ha _)
  · rfl

/-- **A built combination** of values whose registers are multiples of `r` (`LinV`), at an
integer shape: the integer whose bits are the multiple of `r` by its multiplier. -/
theorem combo_val {tabs : Tables} {w : Width} {o : Op} {k : Int64} {ax : Option AuxRef}
    {cs : List (BitVec 64)} {c r : BitVec 64} (h : comboFn o k cs = some c) {Vs : List Val}
    (hV : List.Forall₂ (fun V c => LinV w.bits r c V) Vs cs) :
    (opValL tabs o (.int w) k ax Vs).retypeL (.int w) = .int w ((c * r).setWidth w.bits) := by
  have hn := bits_le64 w
  match Vs, cs, hV with
  | [V1, V2], [a, b], .cons ⟨hp1, z1, hr1, hl1⟩ (.cons ⟨hp2, z2, hr2, hl2⟩ .nil) =>
    obtain ⟨z, hz, hzl⟩ := comboFn_lin hn r h (.cons hl1 (.cons hl2 .nil))
    have hev : Arm64.evalPure o (.int w) k ax [V1, V2] = Arm64.res (.int w) z := by
      unfold comboFn at hz
      split at hz <;> simp only [Option.some.injEq, reduceCtorEq] at hz <;> subst hz
      · show Arm64.add _ [V1, V2] = _
        rw [add_np _ hp1 hp2]; simp only [Arm64.op2, hr1, hr2]
      · show Arm64.sub _ [V1, V2] = _
        rw [sub_np _ hp1]; simp only [Arm64.op2, hr1, hr2, BitVec.sub_eq_add_neg]
      · show Arm64.addSh _ .ll k [V1, V2] = _
        simp only [Arm64.addSh, hr2, addP_np _ hp1, hr1]
      · show Arm64.subSh _ .ll k [V1, V2] = _
        simp only [Arm64.subSh, hr2, addP_np _ hp1, hr1]
    have hpure : ∀ o', comboFn o' k [a, b] = some c → o' = o → o'.generic = false ∧
        (o' == .ARM64MOVDaddr) = false ∧ ldOp? o' = none := by
      intro o' h' _
      unfold comboFn at h'
      split at h' <;> simp only [reduceCtorEq] at h' <;> exact ⟨rfl, rfl, rfl⟩
    obtain ⟨hg, hm, hl⟩ := hpure o h rfl
    rw [opValL_evalPure hg hm hl, hev, retypeL_res_int, hzl]
  | [V1], [a], .cons ⟨hp1, z1, hr1, hl1⟩ .nil =>
    obtain ⟨z, hz, hzl⟩ := comboFn_lin hn r h (.cons hl1 .nil)
    have hev : Arm64.evalPure o (.int w) k ax [V1] = Arm64.res (.int w) z := by
      unfold comboFn at hz
      split at hz <;> simp only [Option.some.injEq, reduceCtorEq] at hz <;> subst hz
      · show Arm64.op1 _ (- ·) [V1] = _
        simp only [Arm64.op1, hr1]
      · show Arm64.op1 _ (Arm64.Shift.apply .ll · (Arm64.amt k)) [V1] = _
        simp only [Arm64.op1, hr1]; rfl
      · show Arm64.op1 _ (fun x => -(Arm64.shifted .ll k x)) [V1] = _
        simp only [Arm64.op1, hr1]
    have hpure : o.generic = false ∧ (o == .ARM64MOVDaddr) = false ∧ ldOp? o = none := by
      unfold comboFn at h
      split at h <;> simp only [reduceCtorEq] at h <;> exact ⟨rfl, rfl, rfl⟩
    rw [opValL_evalPure hpure.1 hpure.2.1 hpure.2.2, hev, retypeL_res_int, hzl]
  | [], [], .nil => simp [comboFn] at h
  | _ :: _ :: _ :: _, _ :: _ :: _ :: _, .cons _ (.cons _ (.cons _ _)) => simp [comboFn] at h

/-! ## The source product -/

/-- A pointer of some shape has no register: it is held as a pointer (F1+F2 of #385), so it does
not convert to the address `Arm64.ptrReg` reads. -/
theorem reg_ptr_none {T : Ty} {p : Ptr} (h : (Val.ptr p).hasTy T = true) :
    Arm64.reg (.ptr p) = none := by
  have hc := Ptr.not_convertible_of_held (Ptr.held_of_hasTy h)
  show Arm64.ptrReg p = none
  unfold Arm64.ptrReg
  split
  · split
    · rename_i he; rw [← he, Ptr.convertible_ofAddr] at hc; cases hc
    · rfl
  · rfl

/-- A constant register read at a shape holding at least `n` low bits: `poison`, or a register
with the constant's low `n` bits. -/
private theorem res_reg_low {T : Ty} {n : Nat} (hn' : n ≤ 64) (h : n ≤ argWidth T)
    (k : BitVec 64) : (Arm64.res T k).retypeL T = .poison ∨
      ∃ y, Arm64.reg ((Arm64.res T k).retypeL T) = some y ∧ y.setWidth n = k.setWidth n := by
  cases T with
  | int w =>
    right
    simp only [argWidth] at h
    cases w <;> simp only [Width.bits] at h <;>
      refine ⟨_, rfl, ?_⟩ <;>
      simp [Arm64.res, Val.retypeL, Val.widen, Val.retype, Width.bits,
        BitVec.setWidth_setWidth_of_le _ h]
  | bool =>
    simp only [argWidth] at h
    by_cases h0 : n = 0
    · subst h0; right
      cases hb : k.getLsbD 0 <;>
        exact ⟨_, rfl, by apply BitVec.eq_of_getLsbD_eq; intro i hi; omega⟩
    have : n = 1 := by omega
    subst this
    right
    refine ⟨_, rfl, ?_⟩
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have : i = 0 := by omega
    subst this
    cases hb : k.getLsbD 0 <;> simp [Arm64.res, Val.retypeL, Val.widen, Val.retype, hb] <;>
      simpa using hb
  | ptr e => right; exact ⟨k, rfl, rfl⟩
  | agg fs m => left; rfl
  | _ => simp [argWidth] at h; right; refine ⟨k, ?_, ?_⟩ <;> first | omega | rfl

/-- **The source product**: `MUL` (or `MULW` at most 32 bits wide) at an integer shape of `X`
and a constant `c` read at a shape holding the shape's bits, in either order, is `poison` or, for
`X` without provenance and with register `r`, the integer whose bits are `c` times `r`. -/
theorem mul_src {tabs : Tables} {w : Width} {o : Op}
    (ho : o = .ARM64MUL ∨ (o = .ARM64MULW ∧ w.bits ≤ 32)) {ai : Int64} {ax : Option AuxRef}
    {X K : Val} {Tx Tk : Ty} (hX : X.hasTy Tx = true) {c : BitVec 64} (hw : w.bits ≤ argWidth Tk)
    (hK : K = .poison ∨ K = (Arm64.res Tk c).retypeL Tk) {Vs : List Val}
    (hVs : Vs = [X, K] ∨ Vs = [K, X]) :
    (opValL tabs o (.int w) ai ax Vs).retypeL (.int w) = .poison ∨
      ((∀ p, X ≠ .ptr p) ∧ ∃ r, Arm64.reg X = some r ∧
        (opValL tabs o (.int w) ai ax Vs).retypeL (.int w) = .int w ((c * r).setWidth w.bits)) := by
  have hn := bits_le64 w
  have hpure : o.generic = false ∧ (o == .ARM64MOVDaddr) = false ∧ ldOp? o = none := by
    rcases ho with rfl | ⟨rfl, -⟩ <;> exact ⟨rfl, rfl, rfl⟩
  rw [opValL_evalPure hpure.1 hpure.2.1 hpure.2.2]
  -- the constant's register
  have hKr : Arm64.reg K = none ∨ ∃ y, Arm64.reg K = some y ∧
      y.setWidth w.bits = c.setWidth w.bits := by
    rcases hK with rfl | rfl
    · exact .inl rfl
    · rcases res_reg_low hn hw c with h | h
      · rw [h]; exact .inl rfl
      · exact .inr h
  -- the operand's register
  have hXr : Arm64.reg X = none ∨ ((∀ p, X ≠ .ptr p) ∧ ∃ r, Arm64.reg X = some r) := by
    cases X with
    | ptr p => exact .inl (reg_ptr_none hX)
    | _ =>
      cases h : Arm64.reg _ with
      | none => exact .inl rfl
      | some r => exact .inr ⟨fun p hp => by cases hp, r, rfl⟩
  rcases hXr with hXn | ⟨hXp, r, hXr⟩
  · left
    rcases ho with rfl | ⟨rfl, -⟩ <;> rcases hVs with rfl | rfl <;>
      first
      | (show (Arm64.op2 _ _ _).retypeL _ = _
         simp only [Arm64.op2, hXn]; split <;> simp_all [retypeL_poison])
      | (show (Arm64.op2w _ _ _).retypeL _ = _
         simp only [Arm64.op2w, Arm64.reg32, hXn]; split <;> simp_all [retypeL_poison])
  rcases hKr with hKn | ⟨y, hKy, hyl⟩
  · left
    rcases ho with rfl | ⟨rfl, -⟩ <;> rcases hVs with rfl | rfl <;>
      first
      | (show (Arm64.op2 _ _ _).retypeL _ = _
         simp only [Arm64.op2, hKn]; split <;> simp_all [retypeL_poison])
      | (show (Arm64.op2w _ _ _).retypeL _ = _
         simp only [Arm64.op2w, Arm64.reg32, hKn]; split <;> simp_all [retypeL_poison])
  right
  refine ⟨hXp, r, hXr, ?_⟩
  have hcr : (c * r).setWidth w.bits = (y * r).setWidth w.bits := by
    rw [BitVec.setWidth_mul _ _ hn, BitVec.setWidth_mul _ _ hn, hyl]
  rw [hcr]
  rcases ho with rfl | ⟨rfl, h32⟩
  · rcases hVs with rfl | rfl
    · show (Arm64.op2 _ _ [X, K]).retypeL _ = _
      simp only [Arm64.op2, hXr, hKy, retypeL_res_int, BitVec.mul_comm r]
    · show (Arm64.op2 _ _ [K, X]).retypeL _ = _
      simp only [Arm64.op2, hXr, hKy, retypeL_res_int]
  · have hlow : ∀ a b : BitVec 64,
        (((a.setWidth 32) * (b.setWidth 32)).setWidth 64).setWidth w.bits =
          (a * b).setWidth w.bits := fun a b => by
      rw [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_mul _ _ h32,
        BitVec.setWidth_setWidth_of_le _ h32, BitVec.setWidth_setWidth_of_le _ h32,
        ← BitVec.setWidth_mul _ _ hn]
    rcases hVs with rfl | rfl
    · show (Arm64.op2w _ _ [X, K]).retypeL _ = _
      simp only [Arm64.op2w, Arm64.reg32, hXr, hKy, Option.map_some, Arm64.res32,
        retypeL_res_int, hlow, BitVec.mul_comm r]
    · show (Arm64.op2w _ _ [K, X]).retypeL _ = _
      simp only [Arm64.op2w, Arm64.reg32, hXr, hKy, Option.map_some, Arm64.res32,
        retypeL_res_int, hlow]

/-! ## The event -/

private theorem mapM_forall₂ {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → List.Forall₂ (fun a b => f a = some b) l l'
  | [], l', h => by simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst h; exact .nil
  | a :: l, l', h => by
    cases ha : f a with
    | none => simp [List.mapM_cons, ha] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [List.mapM_cons, ha, hl] at h
      | some bs =>
        simp only [List.mapM_cons, ha, hl, Option.bind_eq_bind, Option.bind_some, pure,
          Option.some.injEq] at h
        subst h
        exact .cons ha (mapM_forall₂ hl)

private theorem forall₂_map {α β γ : Type} {R : α → β → Prop} {S : γ → β → Prop} {f : α → γ}
    (hRS : ∀ a b, R a b → S (f a) b) :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → List.Forall₂ S (l.map f) l'
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h t => .cons (hRS _ _ h) (forall₂_map hRS t)

/-- One step of `mulCoef`: `a`'s multiplier 1, or a value of `bs` whose op combines its
arguments' multipliers. -/
theorem mulCoef_succ {bs : List Value} {a : ID} {j : Nat} {y : ID} {c : BitVec 64}
    (h : mulCoef bs a (j + 1) y = some c) : (y = a ∧ c = 1) ∨ (y ≠ a ∧ ∃ u ∈ bs, u.id = y ∧
      ∃ cs, List.Forall₂ (fun z c => mulCoef bs a j z = some c) u.args.toList cs ∧
        comboFn u.op u.auxInt cs = some c) := by
  rw [mulCoef] at h
  by_cases hya : y = a
  · subst hya
    simp only [beq_self_eq_true, ite_true, Option.some.injEq] at h
    exact .inl ⟨rfl, h.symm⟩
  · right
    simp only [show (y == a) = false from beq_false_of_ne hya, Bool.false_eq_true, ite_false] at h
    split at h
    · rename_i u hu
      refine ⟨hya, u, List.mem_of_find?_eq_some hu, by simpa using List.find?_some hu, ?_⟩
      cases hm : u.args.toList.mapM (fun z => mulCoef bs a j z) with
      | none => rw [hm] at h; cases h
      | some cs => rw [hm] at h; exact ⟨cs, mapM_forall₂ hm, h⟩
    · cases h

/-- A non-`poison` value without provenance is refined only by itself. -/
private theorem refines_eq_of_reg {X Y : Val} (h : Sem.Refines X Y) {r : BitVec 64}
    (hr : Arm64.reg X = some r) : Y = X := by
  cases h <;> first | rfl | simp [Arm64.reg] at hr

/-- **The built values**: with `a`'s denotation `X` (without provenance, register `r`) from the
fuel `B` on, a value `mulCoef` gives the multiplier `c` within `j` steps denotes, at fuel `B + j`,
`X` (at `a`) or the integer whose bits are `c` times `r`. -/
theorem mul_claim {tabs : Tables} {M' : Defs} {bs : List Value} {a : ID} {w : Width}
    {ρ : ID → Val} {B : Nat} {X : Val} {r : BitVec 64} (hXp : ∀ p, X ≠ .ptr p)
    (hXr : Arm64.reg X = some r) (hXa : ∀ j, denL true M'.get? tabs ρ (B + j) a = X)
    (hbs : ∀ u ∈ bs, M'.get? u.id = some u ∧ termVL tabs u = true ∧ shpL tabs u.type = .int w) :
    ∀ j y c, mulCoef bs a j y = some c →
      LinV w.bits r c (denL true M'.get? tabs ρ (B + j) y) ∧
      (y = a ∨ denL true M'.get? tabs ρ (B + j) y = .int w ((c * r).setWidth w.bits))
  | 0, y, c, h => by simp [mulCoef] at h
  | j + 1, y, c, h => by
    rcases mulCoef_succ h with ⟨rfl, rfl⟩ | ⟨-, u, hu, rfl, cs, hcs, hc⟩
    · refine ⟨?_, .inl rfl⟩
      rw [hXa]
      exact ⟨hXp, r, hXr, by rw [BitVec.one_mul]⟩
    · obtain ⟨hget, ht, hshp⟩ := hbs u hu
      have hval : denL true M'.get? tabs ρ (B + (j + 1)) u.id =
          .int w ((c * r).setWidth w.bits) := by
        rw [show B + (j + 1) = (B + j) + 1 by omega, denT_succ hget ht, hshp]
        exact combo_val hc (forall₂_map (fun z c' hz => (mul_claim hXp hXr hXa hbs j z c' hz).1)
          hcs)
      exact ⟨hval ▸ LinV.of_int, .inr hval⟩

/-- The two arguments of a value with two arguments. -/
private theorem args_toList_two {y : Value} (h : y.args.size = 2) :
    y.args.toList = [y.args[0]!, y.args[1]!] := by
  rcases hy' : y.args with ⟨l⟩
  rw [hy'] at h
  match l, h with
  | [a, b], _ => rfl

/-- What `mulOKL` establishes: `v`'s term `x` on two arguments, one choice of operand and
constant. -/
theorem mulOKL_facts {tabs : Tables} {M : Defs} {v : ID} {defs ds : List Value}
    (h : mulOKL tabs M v defs = some ds) :
    ∃ x a k, M.get? v = some x ∧ x.id = v ∧ termVL tabs x = true ∧
      (x.args.toList = [a, k] ∨ x.args.toList = [k, a]) ∧ mulOKL1 tabs M x a k defs = some ds := by
  unfold mulOKL at h
  split at h
  · rename_i x hx
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨hid, ht⟩, hsz⟩ := hc
      have hl := args_toList_two hsz
      split at h
      · rename_i ds' h1
        cases h
        exact ⟨x, _, _, hx, hid, ht, .inl hl, h1⟩
      · exact ⟨x, _, _, hx, hid, ht, .inr hl, h⟩
    · cases h
  · cases h

/-- What `mulOKL1` establishes. -/
theorem mulOKL1_facts {tabs : Tables} {M : Defs} {x : Value} {a k : ID} {defs ds : List Value}
    (h : mulOKL1 tabs M x a k defs = some ds) :
    ∃ w kd u bs m cm, shpL tabs x.type = .int w ∧ M.get? k = some kd ∧
      kd.op = .ARM64MOVDconst ∧ termVL tabs kd = true ∧ kd.args.isEmpty = true ∧
      w.bits ≤ argWidth (shpL tabs kd.type) ∧
      (x.op = .ARM64MUL ∨ (x.op = .ARM64MULW ∧ w.bits ≤ 32)) ∧
      ds = u :: bs ∧ u.id = x.id ∧ u.op = .Copy ∧ u.type = x.type ∧ u.args.toList = [m] ∧
      (bs.map (·.id)).Nodup ∧ x.id ∉ bs.map (·.id) ∧ (∀ b ∈ bs, M.get? b.id = none) ∧
      (∀ b ∈ bs, termVL tabs b = true ∧ b.type = x.type ∧
        ∀ y ∈ b.args, y = a ∨ y ∈ bs.map (·.id)) ∧
      m ∈ bs.map (·.id) ∧ mulCoef bs a bs.length m = some cm ∧
      cm.setWidth w.bits = (Arm64.imm kd.auxInt).setWidth w.bits := by
  unfold mulOKL1 at h
  split at h
  · rename_i w kd u rest hT hk _
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq,
        Bool.not_eq_true', List.all_eq_true, List.contains_iff_mem] at hc
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hop, ht⟩, hemp⟩, hw⟩, hx⟩, hid⟩, hcop⟩, hty⟩, -⟩, -⟩, hnd⟩, hnv⟩,
        hall⟩, hm⟩ := hc
      split at hm
      · rename_i m hum
        simp only [Bool.and_eq_true, List.contains_iff_mem, Option.any_eq_true, beq_iff_eq] at hm
        obtain ⟨hmem, cm, hcm, hcml⟩ := hm
        refine ⟨w, kd, u, _, m, cm, hT, hk, hop, ht, hemp, hw, ?_, rfl, hid, hcop, hty, hum, hnd,
          ?_, ?_, ?_, hmem, hcm, hcml⟩
        · rcases hx with h | ⟨h1, h2⟩
          · exact .inl h
          · exact .inr ⟨h1, h2⟩
        · simpa using hnv
        · intro b hb
          simp only [List.mem_filter, Option.isNone_iff_eq_none] at hb
          exact hb.2
        · intro b hb
          obtain ⟨⟨hbt, hbty⟩, hba⟩ := hall b hb
          refine ⟨hbt, hbty, fun y hy => ?_⟩
          have := hba y (Array.mem_toList_iff.2 hy)
          simpa [List.contains_iff_mem] using this
      · cases hm
    · cases h
  · cases h

section Step

variable {tabs : Tables} {M : Defs} {v : ID} {defs ds : List Value}

/-- The event's definitions: `v` (a term before) and fresh IDs, each a term whose arguments are
`v`'s or defined by the event. -/
theorem mul_frame (h : mulOKL tabs M v defs = some ds) :
    (∃ x, M.get? v = some x ∧ termVL tabs x = true) ∧
    (∀ y, y ∉ defIds ds → (putAll M ds).get? y = M.get? y) ∧
    (∀ y ∈ defIds ds, y = v ∨ M.get? y = none) ∧
    (∀ y ∈ defIds ds, ∃ u, (putAll M ds).get? y = some u ∧ termVL tabs u = true ∧
      ∀ z ∈ u.args, (∃ x, M.get? v = some x ∧ z ∈ x.args) ∨ z ∈ defIds ds) := by
  obtain ⟨x, a, k, hx, hxid, hxt, hargs, h1⟩ := mulOKL_facts h
  obtain ⟨w, kd, u, bs, m, cm, -, -, -, -, -, -, -, rfl, huid, huop, -, huargs, hnd, hvn, hfresh,
    hbs, hm, -, -⟩ := mulOKL1_facts h1
  rw [hxid] at huid hvn
  have hndAll : ((u :: bs).map (·.id)).Nodup := by
    simp only [List.map_cons, List.nodup_cons]; exact ⟨huid ▸ hvn, hnd⟩
  have ha : a ∈ x.args := by
    rw [← Array.mem_toList_iff]; rcases hargs with h | h <;> simp [h]
  refine ⟨⟨x, hx, hxt⟩, fun y hy => get?_putAll_not _ M y hy, fun y hy => ?_, fun y hy => ?_⟩
  · simp only [defIds, List.map_cons, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact .inl huid
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
      exact .inr (hfresh b hb)
  · simp only [defIds, List.map_cons, List.mem_cons] at hy
    rcases hy with rfl | hy
    · refine ⟨u, get?_putAll_mem _ M u hndAll List.mem_cons_self, termVL_of_copy huop,
        fun z hz => .inr ?_⟩
      rw [← Array.mem_toList_iff, huargs, List.mem_singleton] at hz
      subst hz
      exact List.mem_cons_of_mem _ hm
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
      obtain ⟨hbt, -, hba⟩ := hbs b hb
      refine ⟨b, get?_putAll_mem _ M b hndAll (List.mem_cons_of_mem _ hb), hbt, fun z hz => ?_⟩
      rcases hba z hz with rfl | hz'
      · exact .inl ⟨x, hx, ha⟩
      · exact .inr (List.mem_cons_of_mem _ hz')

/-- **One multiplication event**: on a set closed under arguments, the lowered denotations after
the event refine those before, with the fuel multiplied by the number of values it defines. -/
theorem mul_step (h : mulOKL tabs M v defs = some ds) {C : ID → Prop} (hC : DefClosed M C)
    {ρ : ID → Val} (hT : TypedL true M.get? tabs ρ) :
    ∀ n y, C y → Sem.Refines (denL true M.get? tabs ρ n y)
      (denL true (putAll M ds).get? tabs ρ (n * ds.length) y) := by
  obtain ⟨x, a, k, hx, hxid, hxt, hargs, h1⟩ := mulOKL_facts h
  obtain ⟨w, kd, u, bs, m, cm, hshp, hk, hkop, hkt, -, hkw, hop, rfl, huid, huop, huty, huargs,
    hnd, hvn, hfresh, hbs, hm, hcm, hcml⟩ := mulOKL1_facts h1
  rw [hxid] at huid hvn
  have hn := bits_le64 w
  have hndAll : ((u :: bs).map (·.id)).Nodup := by
    simp only [List.map_cons, List.nodup_cons]; exact ⟨huid ▸ hvn, hnd⟩
  have hkeep : ∀ y, C y → y ≠ v → (putAll M (u :: bs)).get? y = M.get? y := by
    intro y hy hyv
    apply get?_putAll_not
    simp only [List.map_cons, List.mem_cons, not_or]
    refine ⟨fun h => hyv (h.trans huid), fun h => ?_⟩
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 h
    obtain ⟨m0, hm0, -⟩ := hC _ hy
    rw [hfresh b hb] at hm0; cases hm0
  have hbs' : ∀ b ∈ bs, (putAll M (u :: bs)).get? b.id = some b ∧ termVL tabs b = true ∧
      shpL tabs b.type = .int w := fun b hb => by
    obtain ⟨hbt, hbty, -⟩ := hbs b hb
    exact ⟨get?_putAll_mem _ M b hndAll (List.mem_cons_of_mem _ hb), hbt, by rw [hbty, hshp]⟩
  have hlen : (u :: bs).length = bs.length + 1 := rfl
  rw [hlen]
  intro n
  induction n with
  | zero => intro y _; exact .poison _
  | succ n ih =>
    intro y hy
    by_cases hyv : y = v
    · rw [hyv] at hy ⊢
      obtain ⟨x0, hx0, hxa⟩ := hC _ hy
      rw [hx] at hx0; cases hx0
      have hmemA : a ∈ x0.args := by
        rw [← Array.mem_toList_iff]; rcases hargs with h | h <;> simp [h]
      have ha : C a := hxa a hmemA
      obtain ⟨ya, hya, -⟩ := hC a ha
      have hX := den_hasTyL hT n hya
      have hKv : denL true M.get? tabs ρ n k = .poison ∨ denL true M.get? tabs ρ n k =
          (Arm64.res (shpL tabs kd.type) (Arm64.imm kd.auxInt)).retypeL (shpL tabs kd.type) := by
        cases n with
        | zero => exact .inl rfl
        | succ n' =>
          right
          have hg : kd.op.generic = false := by rw [hkop]; rfl
          have hmd : (kd.op == .ARM64MOVDaddr) = false := by rw [hkop]; rfl
          have hl : ldOp? kd.op = none := by rw [hkop]; rfl
          rw [denT_succ hk hkt, opValL_evalPure hg hmd hl, hkop]
          rfl
      rw [denT_succ hx hxt, hshp]
      rcases mul_src (tabs := tabs) (ai := x0.auxInt) (ax := x0.aux) hop hX hkw hKv
          (Vs := x0.args.toList.map (denL true M.get? tabs ρ n))
          (by rcases hargs with h | h <;> simp [h]) with hp | ⟨hXp, r, hXr, hval⟩
      · rw [hp]; exact .poison _
      rw [hval]
      -- `a`'s denotation after the event, from the fuel `n * (bs.length + 1)` on
      have hXa : ∀ j, denL true (putAll M (u :: bs)).get? tabs ρ (n * (bs.length + 1) + j) a =
          denL true M.get? tabs ρ n a := fun j => by
        have h0 := refines_eq_of_reg (ih a ha) hXr
        have h1 := denL_fuel_mono true (putAll M (u :: bs)).get? tabs ρ _ _ a
          (Nat.le_add_right (n * (bs.length + 1)) j)
        rw [h0] at h1
        exact refines_eq_of_reg h1 hXr
      obtain ⟨-, hmv⟩ := mul_claim hXp hXr hXa hbs' bs.length m cm hcm
      have hma : m ≠ a := fun hma => by
        obtain ⟨b, hb, hbm⟩ := List.mem_map.1 hm
        rw [← hma, ← hbm, hfresh b hb] at hya; cases hya
      have hK2 : (n + 1) * (bs.length + 1) = (n * (bs.length + 1) + bs.length) + 1 := by
        rw [Nat.succ_mul]; omega
      have hu : (putAll M (u :: bs)).get? v = some u := by
        rw [← huid]; exact get?_putAll_mem _ M u hndAll List.mem_cons_self
      rw [hK2, denT_succ hu (termVL_of_copy huop), huargs, huty, hshp, huop]
      simp only [List.map_cons, List.map_nil, opValL_copy, hmv.resolve_left hma, retypeL_int_self]
      rw [BitVec.setWidth_mul _ _ hn, BitVec.setWidth_mul _ _ hn, hcml]
      exact Sem.Refines.refl _
    · obtain ⟨m0, hm0, hargs0⟩ := hC y hy
      have hkp : (putAll M (u :: bs)).get? y = some m0 := by rw [hkeep y hy hyv, hm0]
      have hK2 : (n + 1) * (bs.length + 1) = (n * (bs.length + 1) + bs.length) + 1 := by
        rw [Nat.succ_mul]; omega
      rw [hK2]
      by_cases ht : termVL tabs m0 = true
      · rw [denT_succ hm0 ht, denT_succ hkp ht]
        exact retypeL_mono _ (opValL_mono_term ht _ (GoFV.Proof.AtomSim.refinesList_map fun z hz =>
          (ih z (hargs0 z (Array.mem_toList_iff.1 hz))).trans
            (denL_fuel_mono _ _ _ _ _ _ _ (by omega))))
      · have h1 : ¬ IsTermL tabs M.get? y := fun ⟨u', hu', hu''⟩ => by
          rw [hm0] at hu'; cases hu'; exact ht hu''
        have h2 : ¬ IsTermL tabs (putAll M (u :: bs)).get? y := fun ⟨u', hu', hu''⟩ => by
          rw [hkp] at hu'; cases hu'; exact ht hu''
        rw [denL_succ_atom h1, denL_succ_atom h2]; exact Sem.Refines.refl _

end Step

end GoFV.Proof.Low.Val

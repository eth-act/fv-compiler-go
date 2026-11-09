import GoFV.SSA.Sem.Layout

/-!
# `Val.retype` gives a value of the shape

`Val.retype_hasTy`: `(v.retype t).hasTy t` for every value and shape (#108): a misfit becomes
`poison`; a pointer becomes its word (`Ptr.word`: its address if it converts back to itself,
`poison` outside its window), which both word shapes accept (#290). `Val.retype_of_hasTy`: a
value of the shape is unchanged; so `retype` is idempotent (`Val.retype_idem`). The two word
shapes have the same values and retype alike (`Val.hasTy_ptr_eq_i64`, `Val.retype_ptr_eq_i64`).
-/

namespace GoFV.SSA.Sem

section

variable [Addrs]

/-! ## Words -/

/-- A pointer that converts to an integer has a concrete address. -/
theorem Ptr.addr?_isSome_of_convertible {p : Ptr} (h : p.convertible = true) :
    p.addr?.isSome = true := by
  unfold Ptr.convertible at h
  split at h
  · rename_i x hx; rw [hx]; rfl
  · cases h

/-- A pointer that converts to an integer lies inside its window (it is the pointer at its
address, `Addrs.decode_inWindow`). -/
theorem Ptr.inWindow_of_convertible {p : Ptr} (h : p.convertible = true) :
    p.inWindow = true := by
  unfold Ptr.convertible at h
  split at h
  · rw [← beq_iff_eq.1 h]; exact Addrs.decode_inWindow _
  · cases h

/-- A pointer at offset 0 lies inside its window (every window is positive). -/
theorem Ptr.inWindow_zero (b : Blk) : (⟨b, 0⟩ : Ptr).inWindow = true := by
  cases b <;> rfl

theorem Ptr.held_iff {p : Ptr} : p.held = true ↔ p.convertible = false ∧ p.inWindow = true := by
  simp [Ptr.held]

/-- A pointer held as a pointer does not convert. -/
theorem Ptr.not_convertible_of_held {p : Ptr} (h : p.held = true) : p.convertible = false :=
  (Ptr.held_iff.1 h).1

/-- A pointer held as a pointer lies inside its window. -/
theorem Ptr.inWindow_of_held {p : Ptr} (h : p.held = true) : p.inWindow = true :=
  (Ptr.held_iff.1 h).2

/-- A pointer that has some shape is held as a pointer (only the word shapes have pointers). -/
theorem Ptr.held_of_hasTy {p : Ptr} {t : Ty} (h : (Val.ptr p).hasTy t = true) : p.held = true := by
  cases t with
  | int w => cases w <;> simp_all [Val.hasTy]
  | ptr _ => simpa [Val.hasTy] using h
  | _ => simp [Val.hasTy] at h

/-- A pointer's word: the pointer if it is held as one (`Ptr.held`), its address if it converts
back to itself, `poison` outside its window. -/
theorem Ptr.word_cases (p : Ptr) :
    (p.held = true ∧ p.word = .ptr p) ∨
      (p.convertible = true ∧ ∃ a, p.addr? = some a ∧ p.word = .int .w64 a) ∨
      (p.inWindow = false ∧ p.word = .poison) := by
  cases hc : p.convertible with
  | false =>
    cases hw : p.inWindow with
    | false => exact .inr (.inr ⟨rfl, by simp [Ptr.word, hc, hw]⟩)
    | true => exact .inl ⟨by simp [Ptr.held, hc, hw], by simp [Ptr.word, hc, hw]⟩
  | true =>
    have hs := Ptr.addr?_isSome_of_convertible hc
    cases ha : p.addr? with
    | none => rw [ha] at hs; cases hs
    | some a => exact .inr (.inl ⟨rfl, a, rfl, by simp [Ptr.word, hc, ha]⟩)

/-- A pointer's word is a 64-bit integer or a pointer. -/
theorem Ptr.word_eq_int {p : Ptr} {w : Width} {y : BitVec w.bits} (h : p.word = .int w y) :
    w = .w64 := by
  rcases Ptr.word_cases p with ⟨-, h'⟩ | ⟨-, a, -, h'⟩ | ⟨-, h'⟩ <;> rw [h'] at h
  · cases h
  · cases h; rfl
  · cases h

@[simp] theorem Ptr.word_ne_bool (p : Ptr) (b : Bool) : p.word ≠ .bool b := by
  rcases Ptr.word_cases p with ⟨-, h⟩ | ⟨-, a, -, h⟩ | ⟨-, h⟩ <;> rw [h] <;> nofun

@[simp] theorem Ptr.word_ne_poison {p : Ptr} (hw : p.inWindow = true) : p.word ≠ .poison := by
  rcases Ptr.word_cases p with ⟨-, h⟩ | ⟨-, a, -, h⟩ | ⟨h', -⟩
  · rw [h]; nofun
  · rw [h]; nofun
  · rw [hw] at h'; cases h'

@[simp] theorem Ptr.word_ne_mem (p : Ptr) (m : Mem) : p.word ≠ .mem m := by
  rcases Ptr.word_cases p with ⟨-, h⟩ | ⟨-, a, -, h⟩ | ⟨-, h⟩ <;> rw [h] <;> nofun

@[simp] theorem Ptr.word_ne_agg (p : Ptr) (vs : List Val) : p.word ≠ .agg vs := by
  rcases Ptr.word_cases p with ⟨-, h⟩ | ⟨-, a, -, h⟩ | ⟨-, h⟩ <;> rw [h] <;> nofun

@[simp] theorem Ptr.word_ne_tuple (p : Ptr) (vs : List Val) : p.word ≠ .tuple vs := by
  rcases Ptr.word_cases p with ⟨-, h⟩ | ⟨-, a, -, h⟩ | ⟨-, h⟩ <;> rw [h] <;> nofun

/-- The nil pointer's word is address 0. -/
theorem Ptr.null_word : Ptr.null.word = .int .w64 0 := by
  simp [Ptr.word, Ptr.null, Ptr.addr?]

/-- A pointer held as a pointer is its own word. -/
theorem Ptr.word_of_held {p : Ptr} (h : p.held = true) : p.word = .ptr p := by
  obtain ⟨hc, hw⟩ := Ptr.held_iff.1 h
  simp [Ptr.word, hc, hw]

/-- A pointer outside its window has the word `poison`. -/
theorem Ptr.word_of_not_inWindow {p : Ptr} (h : p.inWindow = false) : p.word = .poison := by
  have hc : p.convertible = false := by
    cases hc : p.convertible
    · rfl
    · rw [Ptr.inWindow_of_convertible hc] at h; cases h
  simp [Ptr.word, hc, h]

/-- A pointer's word is a word: a 64-bit integer, a pointer held as one, or `poison`. -/
theorem Ptr.isPtrWord_word (p : Ptr) : p.word.isPtrWord = true := by
  rcases Ptr.word_cases p with ⟨hc, h⟩ | ⟨-, a, -, h⟩ | ⟨-, h⟩
  · simp [h, Val.isPtrWord, hc]
  · simp [h, Val.isPtrWord]
  · simp [h, Val.isPtrWord]

theorem Ptr.word_hasTy_ptr (p : Ptr) (e : Option Nat) : p.word.hasTy (.ptr e) = true := by
  rcases Ptr.word_cases p with ⟨hc, h⟩ | ⟨-, a, -, h⟩ | ⟨-, h⟩
  · simp [h, Val.hasTy, hc]
  · simp [h, Val.hasTy]
  · simp [h, Val.hasTy]

theorem Ptr.word_hasTy_i64 (p : Ptr) : p.word.hasTy (.int .w64) = true := by
  rcases Ptr.word_cases p with ⟨hc, h⟩ | ⟨-, a, -, h⟩ | ⟨-, h⟩
  · simp [h, Val.hasTy, hc]
  · simp [h, Val.hasTy]
  · simp [h, Val.hasTy]

theorem Val.retypePtr_eq (e : Option Nat) (v : Val) : v.retypePtr = v.retype (.ptr e) := by
  cases v with
  | int w x => cases w <;> rfl
  | _ => rfl

theorem Val.retypeI64_eq (v : Val) : v.retypeI64 = v.retype (.int .w64) := by
  cases v <;> rfl

/-- **The two word shapes have the same values** (#290). -/
theorem Val.hasTy_ptr_eq_i64 (v : Val) (e : Option Nat) :
    v.hasTy (.ptr e) = v.hasTy (.int .w64) := by
  cases v with
  | int w x => cases w <;> rfl
  | _ => rfl

/-- **The two word shapes retype alike** (#290). -/
theorem Val.retype_ptr_eq_i64 (v : Val) (e : Option Nat) :
    v.retype (.ptr e) = v.retype (.int .w64) := by
  cases v with
  | int w x => cases w <;> simp [Val.retype, BitVec.setWidth_eq, Width.bits]
  | _ => rfl

/-- The components of a string value with a valid length. -/
theorem Val.strOK_iff {vs : List Val} : Val.strOK vs = true ↔
    ∃ p l, vs = [p, .int .w64 l] ∧ l.msb = false := by
  constructor
  · intro h
    unfold Val.strOK at h
    split at h
    · simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h
      exact ⟨_, _, rfl, h⟩
    · cases h
  · rintro ⟨p, l, rfl, hl⟩
    simp [Val.strOK, hl]

/-- The components of a slice value with valid lengths. -/
theorem Val.sliceOK_iff {vs : List Val} : Val.sliceOK vs = true ↔
    ∃ p l c, vs = [p, .int .w64 l, .int .w64 c] ∧ l.msb = false ∧ c.msb = false ∧
      l.toNat ≤ c.toNat := by
  constructor
  · intro h
    unfold Val.sliceOK at h
    split at h
    · simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, BitVec.ule,
        decide_eq_true_eq] at h
      exact ⟨_, _, _, rfl, h.1.1, h.1.2, h.2⟩
    · cases h
  · rintro ⟨p, l, c, rfl, hl, hc, hlc⟩
    simp [Val.sliceOK, hl, hc, BitVec.ule, hlc]

/-- A value of the string shape that is an aggregate. -/
theorem Val.hasTy_agg_str {vs : List Val} : Val.hasTy (.agg vs) .str = true ↔
    ∃ p l, vs = [p, .int .w64 l] ∧ p.isPtrWord = true ∧ l.msb = false := by
  simp only [Val.hasTy, Bool.and_eq_true, Val.strOK_iff]
  constructor
  · rintro ⟨⟨p, l, rfl, hl⟩, hp⟩
    exact ⟨p, l, rfl, by simpa using hp, hl⟩
  · rintro ⟨p, l, rfl, hp, hl⟩
    exact ⟨⟨p, l, rfl, hl⟩, by simpa using hp⟩

/-- A value of a slice shape that is an aggregate. -/
theorem Val.hasTy_agg_slice {vs : List Val} {e : Option Nat} :
    Val.hasTy (.agg vs) (.slice e) = true ↔
    ∃ p l c, vs = [p, .int .w64 l, .int .w64 c] ∧ p.isPtrWord = true ∧ l.msb = false ∧
      c.msb = false ∧ l.toNat ≤ c.toNat := by
  simp only [Val.hasTy, Bool.and_eq_true, Val.sliceOK_iff]
  constructor
  · rintro ⟨⟨p, l, c, rfl, hl, hc, hlc⟩, hp⟩
    exact ⟨p, l, c, rfl, by simpa using hp, hl, hc, hlc⟩
  · rintro ⟨p, l, c, rfl, hp, hl, hc, hlc⟩
    exact ⟨⟨p, l, c, rfl, hl, hc, hlc⟩, by simpa using hp⟩

theorem Val.isPtrWord_retypePtr (v : Val) : v.retypePtr.isPtrWord = true := by
  cases v with
  | int w x => cases w <;> rfl
  | ptr p => exact Ptr.isPtrWord_word p
  | _ => rfl

theorem Val.ofStr_hasTy (p l : Val) : (Val.ofStr [p.retypePtr, l]).hasTy .str = true := by
  unfold Val.ofStr; split
  · next h =>
    simp only [Val.hasTy, h, Bool.true_and]
    simp [Val.isPtrWord_retypePtr]
  · rfl

theorem Val.ofSlice_hasTy (e : Option Nat) (p l c : Val) :
    (Val.ofSlice [p.retypePtr, l, c]).hasTy (.slice e) = true := by
  unfold Val.ofSlice; split
  · next h =>
    simp only [Val.hasTy, h, Bool.true_and]
    simp [Val.isPtrWord_retypePtr]
  · rfl

theorem Val.ofStr_of_ok {vs : List Val} (h : Val.strOK vs = true) : Val.ofStr vs = .agg vs := by
  simp [Val.ofStr, h]

theorem Val.ofSlice_of_ok {vs : List Val} (h : Val.sliceOK vs = true) :
    Val.ofSlice vs = .agg vs := by
  simp [Val.ofSlice, h]

theorem Val.retypePtr_of_isPtrWord {p : Val} (h : p.isPtrWord = true) :
    p.retypePtr = p := by
  cases p with
  | int w x => cases w <;> simp_all [Val.isPtrWord, Val.retypePtr]
  | ptr q =>
    simp only [Val.isPtrWord] at h
    exact Ptr.word_of_held h
  | _ => simp_all [Val.isPtrWord, Val.retypePtr]

theorem Val.ofStr_hasTy_of {p : Val} (hp : p.isPtrWord = true) (l : Val) :
    (Val.ofStr [p, l]).hasTy .str = true := by
  rw [← Val.retypePtr_of_isPtrWord hp]; exact Val.ofStr_hasTy p l

theorem Val.ofSlice_hasTy_of {p : Val} (hp : p.isPtrWord = true) (e : Option Nat) (l c : Val) :
    (Val.ofSlice [p, l, c]).hasTy (.slice e) = true := by
  rw [← Val.retypePtr_of_isPtrWord hp]; exact Val.ofSlice_hasTy e p l c

theorem Val.retypeI64_int (l : BitVec 64) : (Val.int .w64 l).retypeI64 = .int .w64 l := by
  simp [Val.retypeI64, BitVec.setWidth_eq]

/-- **Lengths of strings are nonnegative**: a non-`poison` value of the string shape (every
register of a string type holds one, `Val.retype_hasTy`) has a length that is a nonnegative
signed `int`, the `StringLen` of it. -/
theorem Val.hasTy_str {v : Val} (h : v.hasTy .str = true) :
    v = .poison ∨ ∃ p l, v = .agg [p, .int .w64 l] ∧ l.msb = false ∧ 0 ≤ l.toInt := by
  cases v with
  | poison => exact .inl rfl
  | agg vs =>
    obtain ⟨p, l, rfl, -, hl⟩ := Val.hasTy_agg_str.1 h
    exact .inr ⟨p, l, rfl, hl, by rw [BitVec.toInt_eq_toNat_of_msb hl]; omega⟩
  | _ => simp [Val.hasTy] at h

/-- **Lengths and capacities of slices are nonnegative**: a non-`poison` value of a slice
shape has `0 ≤ len ≤ cap` as signed `int`s (`SliceLen` is component 1, `SliceCap` 2). -/
theorem Val.hasTy_slice {v : Val} {e : Option Nat} (h : v.hasTy (.slice e) = true) :
    v = .poison ∨ ∃ p l c, v = .agg [p, .int .w64 l, .int .w64 c] ∧ l.msb = false ∧
      c.msb = false ∧ 0 ≤ l.toInt ∧ l.toInt ≤ c.toInt := by
  cases v with
  | poison => exact .inl rfl
  | agg vs =>
    obtain ⟨p, l, c, rfl, -, hl, hc, hlc⟩ := Val.hasTy_agg_slice.1 h
    refine .inr ⟨p, l, c, rfl, hl, hc, ?_, ?_⟩
    · rw [BitVec.toInt_eq_toNat_of_msb hl]; omega
    · rw [BitVec.toInt_eq_toNat_of_msb hl, BitVec.toInt_eq_toNat_of_msb hc]; omega
  | _ => simp [Val.hasTy] at h

mutual
/-- **Every retyped value has the shape.** -/
theorem Val.retype_hasTy : ∀ (t : Ty) (v : Val), (v.retype t).hasTy t = true
  | t, .poison => by cases t <;> rfl
  | .int w', .int w x => by
    unfold Val.retype
    split
    · simp [Val.hasTy]
    · rfl
  | .int w', .ptr p => by
    cases w' with
    | w64 => exact Ptr.word_hasTy_i64 p
    | _ => rfl
  | .ptr e, .int w x => by cases w <;> rfl
  | .ptr e, .ptr p => Ptr.word_hasTy_ptr p e
  | .bool, .bool b => rfl
  | .mem, .mem m => rfl
  | .tuple ts, .tuple vs => by
    unfold Val.retype
    cases h : Val.retypePre ts vs with
    | none => rfl
    | some vs' => simp only [Val.hasTy]; exact Val.retypePre_hasTy ts vs vs' h
  | .agg fs n, .agg vs => by
    unfold Val.retype
    cases h : Val.retypeFields fs vs with
    | none => rfl
    | some vs' => simp only [Val.hasTy]; exact Val.retypeFields_hasTy fs vs vs' h
  | .blob n, .blob bs => by
    unfold Val.retype
    split
    · rename_i hl; simpa [Val.hasTy] using hl
    · rfl
  | .empty, .empty => rfl
  | .str, .agg vs => by
    match vs with
    | [p, l] => exact Val.ofStr_hasTy p _
    | [] | [_] | _ :: _ :: _ :: _ => rfl
  | .slice e, .agg vs => by
    match vs with
    | [p, l, c] => exact Val.ofSlice_hasTy e p _ _
    | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ => rfl
  | .str, .int _ _ | .str, .bool _ | .str, .mem _ | .str, .tuple _ | .str, .ptr _
  | .str, .blob _ | .str, .empty => rfl
  | .slice _, .int _ _ | .slice _, .bool _ | .slice _, .mem _ | .slice _, .tuple _
  | .slice _, .ptr _ | .slice _, .blob _ | .slice _, .empty => rfl
  | .int _, .bool _ | .int _, .mem _ | .int _, .tuple _ | .int _, .agg _ | .int _, .blob _
  | .int _, .empty => rfl
  | .bool, .int _ _ | .bool, .mem _ | .bool, .tuple _ | .bool, .ptr _ | .bool, .agg _
  | .bool, .blob _ | .bool, .empty => rfl
  | .mem, .int _ _ | .mem, .bool _ | .mem, .tuple _ | .mem, .ptr _ | .mem, .agg _
  | .mem, .blob _ | .mem, .empty => rfl
  | .tuple _, .int _ _ | .tuple _, .bool _ | .tuple _, .mem _ | .tuple _, .ptr _
  | .tuple _, .agg _ | .tuple _, .blob _ | .tuple _, .empty => rfl
  | .other, .int _ _ | .other, .bool _ | .other, .mem _ | .other, .tuple _ | .other, .ptr _
  | .other, .agg _ | .other, .blob _ | .other, .empty => rfl
  | .ptr _, .bool _ | .ptr _, .mem _ | .ptr _, .tuple _ | .ptr _, .agg _ | .ptr _, .blob _
  | .ptr _, .empty => rfl
  | .agg _ _, .int _ _ | .agg _ _, .bool _ | .agg _ _, .mem _ | .agg _ _, .tuple _
  | .agg _ _, .ptr _ | .agg _ _, .blob _ | .agg _ _, .empty => rfl
  | .blob _, .int _ _ | .blob _, .bool _ | .blob _, .mem _ | .blob _, .tuple _
  | .blob _, .ptr _ | .blob _, .agg _ | .blob _, .empty => rfl
  | .empty, .int _ _ | .empty, .bool _ | .empty, .mem _ | .empty, .tuple _ | .empty, .ptr _
  | .empty, .agg _ | .empty, .blob _ => rfl
  | .opaque _, .int _ _ | .opaque _, .bool _ | .opaque _, .mem _ | .opaque _, .tuple _
  | .opaque _, .ptr _ | .opaque _, .agg _ | .opaque _, .blob _ | .opaque _, .empty => rfl

theorem Val.retypePre_hasTy : ∀ (ts : List Ty) (vs vs' : List Val),
    Val.retypePre ts vs = some vs' → Val.hasTyPre vs' ts = true
  | [], _, vs', _ => by cases vs' <;> rfl
  | _ :: _, [], _, h => by simp [Val.retypePre] at h
  | t :: ts, v :: vs, vs', h => by
    unfold Val.retypePre at h
    cases h' : Val.retypePre ts vs with
    | none => rw [h'] at h; cases h
    | some ws =>
      rw [h'] at h; cases h
      simp only [Val.hasTyPre, Val.retype_hasTy t v, Val.retypePre_hasTy ts vs ws h',
        Bool.and_self]

theorem Val.retypeFields_hasTy : ∀ (fs : List (Nat × Ty)) (vs vs' : List Val),
    Val.retypeFields fs vs = some vs' → Val.hasTyList vs' (fs.map (·.2)) = true
  | [], [], vs', h => by cases h; rfl
  | [], _ :: _, _, h => by simp [Val.retypeFields] at h
  | _ :: _, [], _, h => by simp [Val.retypeFields] at h
  | (o, t) :: fs, v :: vs, vs', h => by
    unfold Val.retypeFields at h
    cases h' : Val.retypeFields fs vs with
    | none => rw [h'] at h; cases h
    | some ws =>
      rw [h'] at h; cases h
      simp only [List.map_cons, Val.hasTyList, Val.retype_hasTy t v,
        Val.retypeFields_hasTy fs vs ws h', Bool.and_self]
end

mutual
/-- **A value of the shape is unchanged.** -/
theorem Val.retype_of_hasTy : ∀ {t : Ty} {v : Val}, v.hasTy t = true → v.retype t = v
  | t, .poison, _ => by cases t <;> rfl
  | .int w', .int w x, h => by
    simp only [Val.hasTy, beq_iff_eq] at h; subst h
    simp [Val.retype, BitVec.setWidth_eq]
  | .int w', .ptr p, h => by
    cases w' with
    | w64 =>
      simp only [Val.hasTy] at h
      exact Ptr.word_of_held h
    | _ => simp [Val.hasTy] at h
  | .ptr _, .ptr _, h => by
    simp only [Val.hasTy] at h
    exact Ptr.word_of_held h
  | .bool, .bool _, _ => rfl
  | .mem, .mem _, _ => rfl
  | .tuple ts, .tuple vs, h => by
    simp only [Val.hasTy] at h
    unfold Val.retype; rw [Val.retypePre_of_hasTy h]
  | .agg fs n, .agg vs, h => by
    simp only [Val.hasTy] at h
    unfold Val.retype; rw [Val.retypeFields_of_hasTy h]
  | .blob n, .blob bs, h => by
    simp only [Val.hasTy] at h
    unfold Val.retype; simp [h]
  | .empty, .empty, _ => rfl
  | .str, .agg vs, h => by
    obtain ⟨p, l, rfl, hp, hl⟩ := Val.hasTy_agg_str.1 h
    simp only [Val.retype, Val.retypePtr_of_isPtrWord hp, Val.retypeI64_int]
    exact Val.ofStr_of_ok (Val.strOK_iff.2 ⟨p, l, rfl, hl⟩)
  | .slice _, .agg vs, h => by
    obtain ⟨p, l, c, rfl, hp, hl, hc, hlc⟩ := Val.hasTy_agg_slice.1 h
    simp only [Val.retype, Val.retypePtr_of_isPtrWord hp, Val.retypeI64_int]
    exact Val.ofSlice_of_ok (Val.sliceOK_iff.2 ⟨p, l, c, rfl, hl, hc, hlc⟩)
  | .str, .int _ _, h | .str, .bool _, h | .str, .mem _, h | .str, .tuple _, h
  | .str, .ptr _, h | .str, .blob _, h | .str, .empty, h => by simp [Val.hasTy] at h
  | .slice _, .int _ _, h | .slice _, .bool _, h | .slice _, .mem _, h | .slice _, .tuple _, h
  | .slice _, .ptr _, h | .slice _, .blob _, h | .slice _, .empty, h => by simp [Val.hasTy] at h
  | .int _, .bool _, h | .int _, .mem _, h | .int _, .tuple _, h | .int _, .agg _, h
  | .int _, .blob _, h | .int _, .empty, h => by simp [Val.hasTy] at h
  | .bool, .int _ _, h | .bool, .mem _, h | .bool, .tuple _, h | .bool, .ptr _, h
  | .bool, .agg _, h | .bool, .blob _, h | .bool, .empty, h => by simp [Val.hasTy] at h
  | .mem, .int _ _, h | .mem, .bool _, h | .mem, .tuple _, h | .mem, .ptr _, h
  | .mem, .agg _, h | .mem, .blob _, h | .mem, .empty, h => by simp [Val.hasTy] at h
  | .tuple _, .int _ _, h | .tuple _, .bool _, h | .tuple _, .mem _, h | .tuple _, .ptr _, h
  | .tuple _, .agg _, h | .tuple _, .blob _, h | .tuple _, .empty, h => by simp [Val.hasTy] at h
  | .other, .int _ _, h | .other, .bool _, h | .other, .mem _, h | .other, .tuple _, h
  | .other, .ptr _, h | .other, .agg _, h | .other, .blob _, h | .other, .empty, h => by
    simp [Val.hasTy] at h
  | .ptr _, .int w _, h => by cases w <;> first | rfl | simp [Val.hasTy] at h
  | .ptr _, .bool _, h | .ptr _, .mem _, h | .ptr _, .tuple _, h
  | .ptr _, .agg _, h | .ptr _, .blob _, h | .ptr _, .empty, h => by simp [Val.hasTy] at h
  | .agg _ _, .int _ _, h | .agg _ _, .bool _, h | .agg _ _, .mem _, h | .agg _ _, .tuple _, h
  | .agg _ _, .ptr _, h | .agg _ _, .blob _, h | .agg _ _, .empty, h => by simp [Val.hasTy] at h
  | .blob _, .int _ _, h | .blob _, .bool _, h | .blob _, .mem _, h | .blob _, .tuple _, h
  | .blob _, .ptr _, h | .blob _, .agg _, h | .blob _, .empty, h => by simp [Val.hasTy] at h
  | .empty, .int _ _, h | .empty, .bool _, h | .empty, .mem _, h | .empty, .tuple _, h
  | .empty, .ptr _, h | .empty, .agg _, h | .empty, .blob _, h => by simp [Val.hasTy] at h
  | .opaque _, .int _ _, h | .opaque _, .bool _, h | .opaque _, .mem _, h
  | .opaque _, .tuple _, h | .opaque _, .ptr _, h | .opaque _, .agg _, h
  | .opaque _, .blob _, h | .opaque _, .empty, h => by simp [Val.hasTy] at h

theorem Val.retypePre_of_hasTy : ∀ {ts : List Ty} {vs : List Val},
    Val.hasTyPre vs ts = true → Val.retypePre ts vs = some vs
  | [], _, _ => rfl
  | _ :: _, [], h => by simp [Val.hasTyPre] at h
  | t :: ts, v :: vs, h => by
    simp only [Val.hasTyPre, Bool.and_eq_true] at h
    simp only [Val.retypePre, Val.retypePre_of_hasTy h.2, Option.map_some,
      Val.retype_of_hasTy h.1]

theorem Val.retypeFields_of_hasTy : ∀ {fs : List (Nat × Ty)} {vs : List Val},
    Val.hasTyList vs (fs.map (·.2)) = true → Val.retypeFields fs vs = some vs
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [Val.hasTyList] at h
  | _ :: _, [], h => by simp [Val.hasTyList] at h
  | (o, t) :: fs, v :: vs, h => by
    simp only [List.map_cons, Val.hasTyList, Bool.and_eq_true] at h
    simp only [Val.retypeFields, Val.retypeFields_of_hasTy h.2, Option.map_some,
      Val.retype_of_hasTy h.1]
end

theorem Val.retype_idem (t : Ty) (v : Val) : (v.retype t).retype t = v.retype t :=
  Val.retype_of_hasTy (Val.retype_hasTy t v)

/-- A pointer's word is a value of either word shape (it retypes to itself). -/
theorem Ptr.word_retype_ptr (p : Ptr) (e : Option Nat) : p.word.retype (.ptr e) = p.word :=
  Val.retype_of_hasTy (Ptr.word_hasTy_ptr p e)

theorem Ptr.word_retype_i64 (p : Ptr) : p.word.retype (.int .w64) = p.word :=
  Val.retype_of_hasTy (Ptr.word_hasTy_i64 p)

/-- A pointer without a concrete address inside its window is its own word. -/
theorem Ptr.word_of_addr_none {p : Ptr} (h : p.addr? = none) (hw : p.inWindow = true) :
    p.word = .ptr p := by
  simp [Ptr.word, h, hw]

end

/-! ## Witnesses -/

open scoped Fixed

/-- `Val.hasTy_str` applies to a defined string of length 3 (and a negative length is not a
string: it retypes to `poison`). -/
example : ∃ p l, Val.agg [.ptr ⟨.global "s", 0⟩, .int .w64 3] = .agg [p, .int .w64 l] ∧
    l.msb = false ∧ 0 ≤ l.toInt :=
  (Val.hasTy_str (v := .agg [.ptr ⟨.global "s", 0⟩, .int .w64 3]) (by decide)).resolve_left nofun

example : (Val.agg [.ptr Ptr.null, .int .w64 (-1)]).retype .str = .poison := rfl

/-- `Val.hasTy_slice` applies to a defined slice with `len 2 ≤ cap 5`. -/
example : ∃ p l c, Val.agg [.int .w64 0, .int .w64 2, .int .w64 5] =
    .agg [p, .int .w64 l, .int .w64 c] ∧ l.msb = false ∧ c.msb = false ∧ 0 ≤ l.toInt ∧
    l.toInt ≤ c.toInt :=
  (Val.hasTy_slice (v := .agg [.int .w64 0, .int .w64 2, .int .w64 5]) (e := some 8)
    (by decide)).resolve_left nofun

example : (Val.agg [.ptr Ptr.null, .int .w64 5, .int .w64 2]).retype (.slice (some 8)) =
    .poison := rfl

/-- A convertible pointer retypes to its address at a pointer shape (`⟨heap 0, 8⟩` is at
`2^40 + 8`), and a global stays a pointer at both word shapes. -/
example : (Val.ptr ⟨.heap 0, 8⟩).retype (.ptr none) = .int .w64 (2 ^ 40 + 8) := by
  simp [Val.retype, Ptr.word, Ptr.addr?]; decide

example : (Val.ptr ⟨.global "s", 0⟩).retype (.int .w64) = .ptr ⟨.global "s", 0⟩ := rfl

end GoFV.SSA.Sem

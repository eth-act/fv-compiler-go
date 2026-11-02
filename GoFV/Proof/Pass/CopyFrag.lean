import GoFV.Proof.WF
import GoFV.Opt.CopyElim
import GoFV.SSA.Sem.Layout
import GoFV.Proof.Retype

/-!
# The copy graph and copyelim's input condition `CopyFrag`

`cstep V x` is the copy edge out of `x` in the value table `V` (`none`: `x` is not a copy;
`some none`: a copy without exactly one argument). `Src V x r n`: following copy edges from
`x` reaches the non-copy `r` in `n` steps. `CopyFrag tabs f` is what `copyelim_rel`
(`GoFV.Proof.Pass.CopyElimLoop`) assumes beyond `check`: value IDs below `vid.last + 1`, copy
arguments, and arguments of phis that phielim may turn into copies, whose values keep their
value at the copy's type shape (`RetypeInto`: the shapes retype alike, `RetypeEq`, equal up to
pointer and slice element sizes, which `Val.retype` ignores; or the argument's shape is
`other`, whose values are all `poison`; a `Stable` phi, two of whose arguments' copy chains end
at distinct non-phis, is never turned into a copy and is exempt), no zero-size aggregate
copies, and no copy cycle reachable from a listed value. `copyFrag` decides it
(`copyFrag_sound`); `lake exe copyrel-probe` counts the corpus sections that satisfy it.
-/

namespace GoFV.Proof.CopyElim

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof

/-- The copy edge out of `x`. -/
def cstep (V : ID → Option Value) (x : ID) : Option (Option ID) :=
  match V x with
  | some u => if u.op = .Copy then some (if u.args.size = 1 then u.args[0]? else none) else none
  | none => none

/-- From `x`, `n` copy edges lead to the non-copy `r`. -/
inductive Src (V : ID → Option Value) : ID → ID → Nat → Prop where
  | sink {x : ID} : cstep V x = none → Src V x x 0
  | step {x y r : ID} {n : Nat} : cstep V x = some (some y) → Src V y r n → Src V x r (n + 1)

/-- `x`'s copy chain ends within `n` values. -/
def chainEnds (V : ID → Option Value) : Nat → ID → Bool
  | 0, _ => false
  | n + 1, x =>
    match cstep V x with
    | none => true
    | some (some y) => chainEnds V n y
    | some none => false

theorem chainEnds_sound {V : ID → Option Value} :
    ∀ {n x}, chainEnds V n x = true → ∃ r m, Src V x r m
  | 0, _, h => nomatch h
  | n + 1, x, h => by
    unfold chainEnds at h
    split at h
    · exact ⟨x, 0, .sink ‹_›⟩
    · obtain ⟨r, m, hs⟩ := chainEnds_sound h
      exact ⟨r, m + 1, .step ‹_› hs⟩
    · cases h

/-- `t1` and `t2` retype every value alike (`Val.retype` ignores pointer element sizes and is
the identity on shapes other than integers and pointers). -/
def RetypeEq (t1 t2 : Ty) : Prop := ∀ v : Val, v.retype t1 = v.retype t2

theorem RetypeEq.refl (t : Ty) : RetypeEq t t := fun _ => rfl

/-- Values of shape `t1` keep their value at shape `t2` (retyping to `t1` and then to `t2` is
retyping to `t1`): what a copy of shape `t2` of a value of shape `t1` needs. -/
def RetypeInto (t1 t2 : Ty) : Prop := ∀ v : Val, (v.retype t1).retype t2 = v.retype t1

theorem RetypeInto.refl (t : Ty) : RetypeInto t t := Val.retype_idem t

theorem RetypeInto.of_eq {t1 t2 : Ty} (h : t1 = t2) : RetypeInto t1 t2 := h ▸ RetypeInto.refl t1

theorem RetypeInto.trans {t1 t2 t3 : Ty} (h1 : RetypeInto t1 t2) (h2 : RetypeInto t2 t3) :
    RetypeInto t1 t3 := fun v => by
  have h := h2 (v.retype t1)
  rw [h1 v] at h
  exact h

/-- A register of shape `t1` keeps its value at `t2`. -/
theorem RetypeInto.apply {t1 t2 : Ty} (h : RetypeInto t1 t2) {y : Val} (hy : y.retype t1 = y) :
    y.retype t2 = y := by
  have h' := h y
  rw [hy] at h'
  exact h'

theorem RetypeEq.into {t1 t2 : Ty} (h : RetypeEq t1 t2) : RetypeInto t1 t2 := fun v => by
  rw [← h (v.retype t1), Val.retype_idem]

/-- Every value of shape `other` is `poison`. -/
theorem retypeInto_other (t : Ty) : RetypeInto .other t := fun v => by
  have h : v.retype .other = .poison := by cases v <;> rfl
  rw [h]
  cases t <;> rfl

mutual
/-- Shapes that `Val.retype` does not tell apart: equal up to pointers' and slices' element
sizes and composites' sizes. -/
def retypeEqB : Ty → Ty → Bool
  | .int w, .int w' => w == w'
  | .bool, .bool | .mem, .mem | .other, .other | .empty, .empty | .ptr _, .ptr _ | .str, .str
  | .slice _, .slice _ => true
  | .tuple ts, .tuple ts' => retypeEqListB ts ts'
  | .agg fs _, .agg fs' _ => retypeEqFieldsB fs fs'
  | .blob n, .blob n' => n == n'
  | .opaque _, .opaque _ => true
  | _, _ => false
def retypeEqListB : List Ty → List Ty → Bool
  | [], [] => true
  | t :: ts, t' :: ts' => retypeEqB t t' && retypeEqListB ts ts'
  | _, _ => false
def retypeEqFieldsB : List (Nat × Ty) → List (Nat × Ty) → Bool
  | [], [] => true
  | (_, t) :: fs, (_, t') :: fs' => retypeEqB t t' && retypeEqFieldsB fs fs'
  | _, _ => false
end

mutual
theorem retypeEqB_sound : ∀ {t1 t2 : Ty}, retypeEqB t1 t2 = true → RetypeEq t1 t2
  | .int w, .int w', h => by simp only [retypeEqB, beq_iff_eq] at h; subst h; exact RetypeEq.refl _
  | .bool, .bool, _ | .mem, .mem, _ | .other, .other, _ | .empty, .empty, _ | .str, .str, _ =>
    RetypeEq.refl _
  | .slice _, .slice _, _ => fun v => by
    cases v with
    | agg vs => rcases vs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;> rfl
    | _ => rfl
  | .ptr _, .ptr _, _ => fun v => by cases v with
    | int w _ => cases w <;> rfl
    | _ => rfl
  | .opaque _, .opaque _, _ => fun v => by cases v <;> rfl
  | .blob _, .blob _, h => by simp only [retypeEqB, beq_iff_eq] at h; subst h; exact RetypeEq.refl _
  | .tuple ts, .tuple ts', h => fun v => by
    simp only [retypeEqB] at h
    cases v with
    | tuple vs => unfold Val.retype; rw [retypePre_eq h vs]
    | int w _ => cases w <;> rfl
    | _ => rfl
  | .agg fs _, .agg fs' _, h => fun v => by
    simp only [retypeEqB] at h
    cases v with
    | agg vs => unfold Val.retype; rw [retypeFields_eq h vs]
    | int w _ => cases w <;> rfl
    | _ => rfl
  | .int _, .bool, h | .int _, .mem, h | .int _, .tuple _, h | .int _, .other, h
  | .int _, .ptr _, h | .int _, .agg _ _, h | .int _, .blob _, h | .int _, .empty, h
  | .int _, .opaque _, h | .bool, .int _, h | .bool, .mem, h | .bool, .tuple _, h
  | .bool, .other, h | .bool, .ptr _, h | .bool, .agg _ _, h | .bool, .blob _, h
  | .bool, .empty, h | .bool, .opaque _, h | .mem, .int _, h | .mem, .bool, h
  | .mem, .tuple _, h | .mem, .other, h | .mem, .ptr _, h | .mem, .agg _ _, h
  | .mem, .blob _, h | .mem, .empty, h | .mem, .opaque _, h | .tuple _, .int _, h
  | .tuple _, .bool, h | .tuple _, .mem, h | .tuple _, .other, h | .tuple _, .ptr _, h
  | .tuple _, .agg _ _, h | .tuple _, .blob _, h | .tuple _, .empty, h
  | .tuple _, .opaque _, h | .other, .int _, h | .other, .bool, h | .other, .mem, h
  | .other, .tuple _, h | .other, .ptr _, h | .other, .agg _ _, h | .other, .blob _, h
  | .other, .empty, h | .other, .opaque _, h | .ptr _, .int _, h | .ptr _, .bool, h
  | .ptr _, .mem, h | .ptr _, .tuple _, h | .ptr _, .other, h | .ptr _, .agg _ _, h
  | .ptr _, .blob _, h | .ptr _, .empty, h | .ptr _, .opaque _, h | .agg _ _, .int _, h
  | .agg _ _, .bool, h | .agg _ _, .mem, h | .agg _ _, .tuple _, h | .agg _ _, .other, h
  | .agg _ _, .ptr _, h | .agg _ _, .blob _, h | .agg _ _, .empty, h
  | .agg _ _, .opaque _, h | .blob _, .int _, h | .blob _, .bool, h | .blob _, .mem, h
  | .blob _, .tuple _, h | .blob _, .other, h | .blob _, .ptr _, h | .blob _, .agg _ _, h
  | .blob _, .empty, h | .blob _, .opaque _, h | .empty, .int _, h | .empty, .bool, h
  | .empty, .mem, h | .empty, .tuple _, h | .empty, .other, h | .empty, .ptr _, h
  | .empty, .agg _ _, h | .empty, .blob _, h | .empty, .opaque _, h
  | .opaque _, .int _, h | .opaque _, .bool, h | .opaque _, .mem, h
  | .opaque _, .tuple _, h | .opaque _, .other, h | .opaque _, .ptr _, h
  | .opaque _, .agg _ _, h | .opaque _, .blob _, h | .opaque _, .empty, h => by
    simp [retypeEqB] at h
theorem retypePre_eq : ∀ {ts ts' : List Ty}, retypeEqListB ts ts' = true →
    ∀ vs, Val.retypePre ts vs = Val.retypePre ts' vs
  | [], [], _, _ => rfl
  | t :: ts, t' :: ts', h, vs => by
    simp only [retypeEqListB, Bool.and_eq_true] at h
    cases vs with
    | nil => rfl
    | cons v vs => simp only [Val.retypePre, retypeEqB_sound h.1 v, retypePre_eq h.2 vs]
  | [], _ :: _, h, _ | _ :: _, [], h, _ => by simp [retypeEqListB] at h
theorem retypeFields_eq : ∀ {fs fs' : List (Nat × Ty)}, retypeEqFieldsB fs fs' = true →
    ∀ vs, Val.retypeFields fs vs = Val.retypeFields fs' vs
  | [], [], _, _ => rfl
  | (_, t) :: fs, (_, t') :: fs', h, vs => by
    simp only [retypeEqFieldsB, Bool.and_eq_true] at h
    cases vs with
    | nil => rfl
    | cons v vs => simp only [Val.retypeFields, retypeEqB_sound h.1 v, retypeFields_eq h.2 vs]
  | [], _ :: _, h, _ | _ :: _, [], h, _ => by simp [retypeEqFieldsB] at h
end

/-- Decides a sufficient condition for `RetypeInto` (`retypeIntoB_sound`): the argument's
shape is `other`, or the shapes retype alike. -/
def retypeIntoB (t1 t2 : Ty) : Bool :=
  (match t1 with
   | .other => true
   | _ => false) || retypeEqB t1 t2

theorem retypeIntoB_sound {t1 t2 : Ty} (h : retypeIntoB t1 t2 = true) : RetypeInto t1 t2 := by
  unfold retypeIntoB at h
  split at h
  · exact retypeInto_other t2
  · exact (retypeEqB_sound (by simpa using h)).into

/-- `t` is a zero-size struct or array type (as `phielim` decides it). -/
def zeroSize (tabs : Tables) (t : TypeRef) : Prop := zeroSizeAggregate tabs t = .ok true

def zeroSizeB (tabs : Tables) (t : TypeRef) : Bool :=
  match zeroSizeAggregate tabs t with
  | .ok true => true
  | _ => false

theorem zeroSizeB_eq_false {tabs : Tables} {t : TypeRef} (h : zeroSizeB tabs t = false) :
    ¬ zeroSize tabs t := by
  unfold zeroSizeB at h; unfold zeroSize
  split at h
  · cases h
  · rename_i hne; exact hne

/-- `r` is no `Phi` of `f`. -/
def NotPhi (f : Func) (r : ID) : Prop := ∀ rv, f.value? r = some rv → rv.op ≠ .Phi

/-- Two arguments of `v` have copy chains ending at distinct non-phis: as long as those stay
non-copies, `phielim` never turns `v` into a copy (`inv_phielim`). -/
def Stable (f : Func) (v : Value) : Prop :=
  ∃ a₁ ∈ v.args, ∃ a₂ ∈ v.args, ∃ r₁ r₂ n₁ n₂, Src f.value? a₁ r₁ n₁ ∧ Src f.value? a₂ r₂ n₂ ∧
    r₁ ≠ r₂ ∧ NotPhi f r₁ ∧ NotPhi f r₂

/-- The end of `x`'s copy chain within `n` copy edges. -/
def chainEnd (V : ID → Option Value) : Nat → ID → Option ID
  | 0, _ => none
  | n + 1, x =>
    match cstep V x with
    | none => some x
    | some (some y) => chainEnd V n y
    | some none => none

theorem chainEnd_sound {V : ID → Option Value} :
    ∀ {n x r}, chainEnd V n x = some r → ∃ m, Src V x r m
  | 0, _, _, h => nomatch h
  | n + 1, x, r, h => by
    unfold chainEnd at h
    split at h
    · cases h; exact ⟨0, .sink ‹_›⟩
    · obtain ⟨m, hs⟩ := chainEnd_sound h
      exact ⟨m + 1, .step ‹_› hs⟩
    · cases h

/-- The chain ends of `v`'s arguments that are no `Phi`s. -/
def stableEnds (f : Func) (v : Value) : List ID :=
  v.args.toList.filterMap fun a => (chainEnd f.value? (f.valueTab.size + 1) a).filter
    fun r => (f.value? r).all (·.op != .Phi)

/-- Decides a sufficient condition for `Stable` (`stableB_sound`). -/
def stableB (f : Func) (v : Value) : Bool :=
  (stableEnds f v).any fun r => (stableEnds f v).any (· != r)

theorem stableEnds_mem {f : Func} {v : Value} {r : ID} (h : r ∈ stableEnds f v) :
    ∃ a ∈ v.args, ∃ n, Src f.value? a r n ∧ NotPhi f r := by
  unfold stableEnds at h
  obtain ⟨a, ha, he⟩ := List.mem_filterMap.1 h
  obtain ⟨hc, hp⟩ := Option.filter_eq_some_iff.1 he
  obtain ⟨n, hs⟩ := chainEnd_sound hc
  refine ⟨a, Array.mem_toList_iff.1 ha, n, hs, fun rv hrv => ?_⟩
  rw [hrv] at hp
  simpa using hp

theorem stableB_sound {f : Func} {v : Value} (h : stableB f v = true) : Stable f v := by
  unfold stableB at h
  obtain ⟨r₁, h₁, h⟩ := List.any_eq_true.1 h
  obtain ⟨r₂, h₂, hne⟩ := List.any_eq_true.1 h
  obtain ⟨a₁, ha₁, n₁, hs₁, hp₁⟩ := stableEnds_mem h₁
  obtain ⟨a₂, ha₂, n₂, hs₂, hp₂⟩ := stableEnds_mem h₂
  exact ⟨a₁, ha₁, a₂, ha₂, r₁, r₂, n₁, n₂, hs₁, hs₂, fun he => by simp [he] at hne, hp₁, hp₂⟩

/-- What `copyelim_rel` assumes of copyelim's input beyond `check`. -/
structure CopyFrag (tabs : Tables) (f : Func) : Prop where
  /-- Value IDs are below `vid.last + 1` (bounds the loops of `chase`, `copySource`, `phielim`). -/
  size : f.valueTab.size ≤ f.vidLast + 1
  /-- Arguments of listed copies and of listed phis that may become copies (not `Stable`)
  keep their value at the value's shape (`RetypeInto`). -/
  shape : ∀ x, Listed f x → ∀ v, f.value? x = some v → (v.op = .Copy ∨ v.op = .Phi ∧ ¬ Stable f v) →
    ∀ a ∈ v.args, ∃ w, f.value? a = some w ∧ RetypeInto (tabs.ty w.type) (tabs.ty v.type)
  /-- No listed copy has a zero-size struct or array type. -/
  copyNZ : ∀ x, Listed f x → ∀ v, f.value? x = some v → v.op = .Copy → ¬ zeroSize tabs v.type
  /-- The copy chain of every listed value ends (no copy cycle). -/
  acyclic : ∀ x, Listed f x → ∃ r n, Src f.value? x r n

/-- The checks of one listed value. -/
def valueOK (tabs : Tables) (f : Func) (x : ID) : Bool :=
  match f.value? x with
  | none => true
  | some v =>
    ((v.op != .Copy && v.op != .Phi) || (v.op == .Phi && stableB f v) ||
      v.args.all fun a => (f.value? a).any fun w => retypeIntoB (tabs.ty w.type) (tabs.ty v.type)) &&
    (v.op != .Copy || !zeroSizeB tabs v.type) &&
    chainEnds f.value? (f.valueTab.size + 1) x

/-- Decides `CopyFrag` (`copyFrag_sound`). -/
def copyFrag (tabs : Tables) (f : Func) : Bool :=
  decide (f.valueTab.size ≤ f.vidLast + 1) &&
  f.blocks.all fun bid => (((f.block? bid).map (·.values)).getD #[]).all (valueOK tabs f)

theorem copyFrag_sound {tabs : Tables} {f : Func} (h : copyFrag tabs f = true) :
    CopyFrag tabs f := by
  unfold copyFrag at h
  rw [Bool.and_eq_true, decide_eq_true_iff, Array.all_eq_true'] at h
  have hv : ∀ x, Listed f x → valueOK tabs f x = true := by
    rintro x ⟨bid, b, ⟨hm, hb⟩, hx⟩
    have := h.2 bid hm
    rw [hb, Option.map_some, Option.getD_some, Array.all_eq_true'] at this
    exact this x hx
  have hv' : ∀ x, Listed f x → ∀ v, f.value? x = some v →
      (((v.op != .Copy && v.op != .Phi) = true) ∨ (v.op == .Phi && stableB f v) = true ∨
        ∀ a ∈ v.args, (f.value? a).any (fun w => retypeIntoB (tabs.ty w.type) (tabs.ty v.type)) = true) ∧
      ((v.op != .Copy) = true ∨ zeroSizeB tabs v.type = false) ∧
      chainEnds f.value? (f.valueTab.size + 1) x = true := by
    intro x hx v hxv
    have := hv x hx
    unfold valueOK at this
    rw [hxv] at this
    simp only [Bool.and_eq_true, Bool.or_eq_true, Array.all_eq_true', Bool.not_eq_true'] at this
    obtain ⟨⟨h1, h2⟩, h3⟩ := this
    refine ⟨?_, h2, h3⟩
    rcases h1 with (h1 | h1) | h1
    · exact .inl (by simpa only [Bool.and_eq_true] using h1)
    · exact .inr (.inl (by simpa only [Bool.and_eq_true] using h1))
    · exact .inr (.inr h1)
  refine ⟨h.1, ?_, ?_, ?_⟩
  · intro x hx v hxv hop a ha
    rcases (hv' x hx v hxv).1 with h1 | h1 | h1
    · rcases hop with hop | ⟨hop, -⟩ <;> simp [hop] at h1
    · rcases hop with hop | ⟨-, hns⟩
      · simp [hop] at h1
      · simp only [Bool.and_eq_true] at h1
        exact absurd (stableB_sound h1.2) hns
    · have := h1 a ha
      cases hw : f.value? a with
      | none => rw [hw] at this; cases this
      | some w =>
        rw [hw] at this
        exact ⟨w, rfl, retypeIntoB_sound (by simpa using this)⟩
  · intro x hx v hxv hop
    rcases (hv' x hx v hxv).2.1 with h1 | h1
    · simp [hop] at h1
    · exact zeroSizeB_eq_false h1
  · intro x hx
    cases hxv : f.value? x with
    | none => exact ⟨x, 0, .sink (by unfold cstep; rw [hxv])⟩
    | some v => exact chainEnds_sound (hv' x hx v hxv).2.2

end GoFV.Proof.CopyElim

import GoFV.Proof.WF
import GoFV.Opt.CopyElim
import GoFV.SSA.Sem.Layout

/-!
# The copy graph and copyelim's input condition `CopyFrag`

`cstep V x` is the copy edge out of `x` in the value table `V` (`none`: `x` is not a copy;
`some none`: a copy without exactly one argument). `Src V x r n`: following copy edges from
`x` reaches the non-copy `r` in `n` steps. `CopyFrag tabs f` is what `copyelim_rel`
(`GoFV.Proof.Pass.CopyElimLoop`) assumes beyond `check`: value IDs below `vid.last + 1`, copy and
phi arguments of the value's type shape, no zero-size aggregate copies, and no copy cycle
reachable from a listed value. `copyFrag` decides it (`copyFrag_sound`); `lake exe
copyrel-probe` counts the corpus sections that satisfy it.
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

mutual
/-- Equality of type shapes (`Ty` derives no `DecidableEq`). -/
def tyEq : Ty → Ty → Bool
  | .int w, .int w' => w == w'
  | .bool, .bool => true
  | .mem, .mem => true
  | .tuple ts, .tuple ts' => tysEq ts ts'
  | .other, .other => true
  | .ptr e, .ptr e' => e == e'
  | .agg fs n, .agg fs' n' => fieldsEq fs fs' && n == n'
  | .blob n, .blob n' => n == n'
  | .empty, .empty => true
  | .opaque n, .opaque n' => n == n'
  | _, _ => false

def tysEq : List Ty → List Ty → Bool
  | [], [] => true
  | t :: ts, t' :: ts' => tyEq t t' && tysEq ts ts'
  | _, _ => false

def fieldsEq : List (Nat × Ty) → List (Nat × Ty) → Bool
  | [], [] => true
  | (o, t) :: fs, (o', t') :: fs' => o == o' && tyEq t t' && fieldsEq fs fs'
  | _, _ => false
end

mutual
theorem tyEq_sound : ∀ {a b : Ty}, tyEq a b = true → a = b
  | .int w, .int w', h => by
    have : w = w' := by simpa [tyEq] using h
    rw [this]
  | .bool, .bool, _ => rfl
  | .mem, .mem, _ => rfl
  | .tuple ts, .tuple ts', h => by
    have : ts = ts' := tysEq_sound (by simpa only [tyEq] using h)
    rw [this]
  | .other, .other, _ => rfl
  | .ptr e, .ptr e', h => by
    have : e = e' := by simpa [tyEq] using h
    rw [this]
  | .agg fs n, .agg fs' n', h => by
    simp only [tyEq, Bool.and_eq_true, beq_iff_eq] at h
    rw [fieldsEq_sound h.1, h.2]
  | .blob n, .blob n', h => by
    have : n = n' := by simpa [tyEq] using h
    rw [this]
  | .empty, .empty, _ => rfl
  | .opaque n, .opaque n', h => by
    have : n = n' := by simpa [tyEq] using h
    rw [this]
  | .int _, .bool, h | .int _, .mem, h | .int _, .tuple _, h | .int _, .other, h
  | .int _, .ptr _, h | .int _, .agg _ _, h | .int _, .blob _, h | .int _, .empty, h
  | .int _, .opaque _, h | .bool, .int _, h | .bool, .mem, h | .bool, .tuple _, h
  | .bool, .other, h | .bool, .ptr _, h | .bool, .agg _ _, h | .bool, .blob _, h
  | .bool, .empty, h | .bool, .opaque _, h | .mem, .int _, h | .mem, .bool, h | .mem, .tuple _, h
  | .mem, .other, h | .mem, .ptr _, h | .mem, .agg _ _, h | .mem, .blob _, h | .mem, .empty, h
  | .mem, .opaque _, h | .tuple _, .int _, h | .tuple _, .bool, h | .tuple _, .mem, h
  | .tuple _, .other, h | .tuple _, .ptr _, h | .tuple _, .agg _ _, h | .tuple _, .blob _, h
  | .tuple _, .empty, h | .tuple _, .opaque _, h | .other, .int _, h | .other, .bool, h
  | .other, .mem, h | .other, .tuple _, h | .other, .ptr _, h | .other, .agg _ _, h
  | .other, .blob _, h | .other, .empty, h | .other, .opaque _, h | .ptr _, .int _, h
  | .ptr _, .bool, h | .ptr _, .mem, h | .ptr _, .tuple _, h | .ptr _, .other, h
  | .ptr _, .agg _ _, h | .ptr _, .blob _, h | .ptr _, .empty, h | .ptr _, .opaque _, h
  | .agg _ _, .int _, h | .agg _ _, .bool, h | .agg _ _, .mem, h | .agg _ _, .tuple _, h
  | .agg _ _, .other, h | .agg _ _, .ptr _, h | .agg _ _, .blob _, h | .agg _ _, .empty, h
  | .agg _ _, .opaque _, h | .blob _, .int _, h | .blob _, .bool, h | .blob _, .mem, h
  | .blob _, .tuple _, h | .blob _, .other, h | .blob _, .ptr _, h | .blob _, .agg _ _, h
  | .blob _, .empty, h | .blob _, .opaque _, h | .empty, .int _, h | .empty, .bool, h
  | .empty, .mem, h | .empty, .tuple _, h | .empty, .other, h | .empty, .ptr _, h
  | .empty, .agg _ _, h | .empty, .blob _, h | .empty, .opaque _, h | .opaque _, .int _, h
  | .opaque _, .bool, h | .opaque _, .mem, h | .opaque _, .tuple _, h | .opaque _, .other, h
  | .opaque _, .ptr _, h | .opaque _, .agg _ _, h | .opaque _, .blob _, h | .opaque _, .empty, h => by
    simp [tyEq] at h

theorem tysEq_sound : ∀ {a b : List Ty}, tysEq a b = true → a = b
  | [], [], _ => rfl
  | t :: ts, t' :: ts', h => by
    simp only [tysEq, Bool.and_eq_true] at h
    rw [tyEq_sound h.1, tysEq_sound h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [tysEq] at h

theorem fieldsEq_sound : ∀ {a b : List (Nat × Ty)}, fieldsEq a b = true → a = b
  | [], [], _ => rfl
  | (o, t) :: fs, (o', t') :: fs', h => by
    simp only [fieldsEq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1.1, tyEq_sound h.1.2, fieldsEq_sound h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [fieldsEq] at h
end

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

/-- What `copyelim_rel` assumes of copyelim's input beyond `check`. -/
structure CopyFrag (tabs : Tables) (f : Func) : Prop where
  /-- Value IDs are below `vid.last + 1` (bounds the loops of `chase`, `copySource`, `phielim`). -/
  size : f.valueTab.size ≤ f.vidLast + 1
  /-- Arguments of listed copies and phis have the value's type shape. -/
  shape : ∀ x, Listed f x → ∀ v, f.value? x = some v → (v.op = .Copy ∨ v.op = .Phi) →
    ∀ a ∈ v.args, ∃ w, f.value? a = some w ∧ tabs.ty w.type = tabs.ty v.type
  /-- No listed copy has a zero-size struct or array type. -/
  copyNZ : ∀ x, Listed f x → ∀ v, f.value? x = some v → v.op = .Copy → ¬ zeroSize tabs v.type
  /-- The copy chain of every listed value ends (no copy cycle). -/
  acyclic : ∀ x, Listed f x → ∃ r n, Src f.value? x r n

/-- The checks of one listed value. -/
def valueOK (tabs : Tables) (f : Func) (x : ID) : Bool :=
  match f.value? x with
  | none => true
  | some v =>
    ((v.op != .Copy && v.op != .Phi) ||
      v.args.all fun a => (f.value? a).any fun w => tyEq (tabs.ty w.type) (tabs.ty v.type)) &&
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
      (((v.op != .Copy && v.op != .Phi) = true) ∨
        ∀ a ∈ v.args, (f.value? a).any (fun w => tyEq (tabs.ty w.type) (tabs.ty v.type)) = true) ∧
      ((v.op != .Copy) = true ∨ zeroSizeB tabs v.type = false) ∧
      chainEnds f.value? (f.valueTab.size + 1) x = true := by
    intro x hx v hxv
    have := hv x hx
    unfold valueOK at this
    rw [hxv] at this
    simpa only [Bool.and_eq_true, Bool.or_eq_true, Array.all_eq_true', Bool.not_eq_true',
      and_assoc] using this
  refine ⟨h.1, ?_, ?_, ?_⟩
  · intro x hx v hxv hop a ha
    rcases (hv' x hx v hxv).1 with h1 | h1
    · rcases hop with hop | hop <;> simp [hop] at h1
    · have := h1 a ha
      cases hw : f.value? a with
      | none => rw [hw] at this; cases this
      | some w =>
        rw [hw] at this
        exact ⟨w, rfl, tyEq_sound (by simpa using this)⟩
  · intro x hx v hxv hop
    rcases (hv' x hx v hxv).2.1 with h1 | h1
    · simp [hop] at h1
    · exact zeroSizeB_eq_false h1
  · intro x hx
    cases hxv : f.value? x with
    | none => exact ⟨x, 0, .sink (by unfold cstep; rw [hxv])⟩
    | some v => exact chainEnds_sound (hv' x hx v hxv).2.2

end GoFV.Proof.CopyElim

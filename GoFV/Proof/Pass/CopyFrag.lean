import GoFV.Proof.WF
import GoFV.Opt.CopyElim
import GoFV.SSA.Sem.Layout

/-!
# The copy graph and copyelim's input condition `CopyFrag`

`cstep V x` is the copy edge out of `x` in the value table `V` (`none`: `x` is not a copy;
`some none`: a copy without exactly one argument). `Src V x r n`: following copy edges from
`x` reaches the non-copy `r` in `n` steps. `CopyFrag tabs f` is what `copyelim_rel`
(`GoFV.Proof.Pass.CopyElimLoop`) assumes beyond `check`: value IDs below `vid.last + 1`, copy and
phi arguments whose type shape retypes like the value's (`RetypeEq`: equal up to pointer element
sizes, which `Val.retype` ignores), no zero-size aggregate copies, and no copy cycle
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

/-- `t1` and `t2` retype every value alike (`Val.retype` ignores pointer element sizes and is
the identity on shapes other than integers and pointers). -/
def RetypeEq (t1 t2 : Ty) : Prop := ∀ v : Val, v.retype t1 = v.retype t2

theorem RetypeEq.refl (t : Ty) : RetypeEq t t := fun _ => rfl

theorem RetypeEq.symm {t1 t2 : Ty} (h : RetypeEq t1 t2) : RetypeEq t2 t1 := fun v => (h v).symm

theorem RetypeEq.trans {t1 t2 t3 : Ty} (h1 : RetypeEq t1 t2) (h2 : RetypeEq t2 t3) :
    RetypeEq t1 t3 := fun v => (h1 v).trans (h2 v)

theorem RetypeEq.of_eq {t1 t2 : Ty} (h : t1 = t2) : RetypeEq t1 t2 := h ▸ RetypeEq.refl t1

/-- Decides a sufficient condition for `RetypeEq` (`retypeEqB_sound`). -/
def retypeEqB : Ty → Ty → Bool
  | .int w, .int w' => w == w'
  | .int _, _ => false
  | _, .int _ => false
  | .ptr _, .ptr _ => true
  | .ptr _, _ => false
  | _, .ptr _ => false
  | _, _ => true

/-- Neither an integer nor a pointer shape. -/
def plainB : Ty → Bool
  | .int _ => false
  | .ptr _ => false
  | _ => true

theorem retype_plain {t : Ty} (h : plainB t = true) (v : Val) : v.retype t = v := by
  cases t with
  | int _ => cases h
  | ptr _ => cases h
  | _ =>
    cases v with
    | int w _ => cases w <;> rfl
    | _ => rfl

theorem retype_ptr (e e' : Option Nat) (v : Val) : v.retype (.ptr e) = v.retype (.ptr e') := by
  cases v with
  | int w _ => cases w <;> rfl
  | _ => rfl

theorem retypeEqB_sound {t1 t2 : Ty} (h : retypeEqB t1 t2 = true) : RetypeEq t1 t2 := by
  intro v
  cases t1 with
  | int w =>
    cases t2 with
    | int w' =>
      have : w = w' := by simpa [retypeEqB] using h
      rw [this]
    | _ => simp [retypeEqB] at h
  | ptr e =>
    cases t2 with
    | ptr e' => exact retype_ptr e e' v
    | _ => simp [retypeEqB] at h
  | _ =>
    cases t2 with
    | int _ => simp [retypeEqB] at h
    | ptr _ => simp [retypeEqB] at h
    | _ => exact (retype_plain (by rfl) v).trans (retype_plain (by rfl) v).symm

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
  /-- Arguments of listed copies and phis retype like the value (`RetypeEq`). -/
  shape : ∀ x, Listed f x → ∀ v, f.value? x = some v → (v.op = .Copy ∨ v.op = .Phi) →
    ∀ a ∈ v.args, ∃ w, f.value? a = some w ∧ RetypeEq (tabs.ty w.type) (tabs.ty v.type)
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
      v.args.all fun a => (f.value? a).any fun w => retypeEqB (tabs.ty w.type) (tabs.ty v.type)) &&
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
        ∀ a ∈ v.args, (f.value? a).any (fun w => retypeEqB (tabs.ty w.type) (tabs.ty v.type)) = true) ∧
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
        exact ⟨w, rfl, retypeEqB_sound (by simpa using this)⟩
  · intro x hx v hxv hop
    rcases (hv' x hx v hxv).2.1 with h1 | h1
    · simp [hop] at h1
    · exact zeroSizeB_eq_false h1
  · intro x hx
    cases hxv : f.value? x with
    | none => exact ⟨x, 0, .sink (by unfold cstep; rw [hxv])⟩
    | some v => exact chainEnds_sound (hv' x hx v hxv).2.2

end GoFV.Proof.CopyElim

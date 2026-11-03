import GoFV.Opt.RegallocCheck
import GoFV.Proof.RetypeL

/-!
# Regalloc checker soundness, stages 1–2: locations and shapes (`docs/plans/regalloc-check.md` §6)

**Locations.** `LocState.at s l`: what location `l` of the `runLoc` state holds (a register, a
stack slot, the memory, the flags). The checker's reads (`readLoc`) and writes (`writeLocs`,
`killLocs`, `killLoc`, `clobberFacts`) are those of `LocState.raw`/`write`/`clobber`:

* `raw_loc`, `raw_zero`, `raw_tuple`, `raw_ok`: a read is the location's contents, the zero of
  the reader's shape, or a tuple of its components' locations;
* `at_write`, `at_write_other`: a write puts component `j` (`comp`) of the result in each
  location of `writeLocs`, and leaves every location that clashes with none unchanged;
* `at_clobber`: the facts `clobberFacts` keeps are at locations a value's clobbers leave alone.

**Shapes.** `LMode.retype` at word shapes is one function (`retype_shapeEq`); integer narrowing
composes (`retype_composes` for every value, `retype_composesAt` for values of the narrower
shape).
-/

namespace GoFV.Proof.RA

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RegallocCheck

/-! ## Locations -/

/-- What location `l` holds (`avail` is no location). -/
def _root_.GoFV.SSA.Sem.LocState.at (s : LocState) : Loc → Val
  | .reg r => s.regs[r]?.getD .poison
  | .slot k => (s.slots.lookup k).getD .poison
  | .mem => s.mem
  | .flags => s.flags
  | .avail => .poison

/-- Component `j` of `x` (`none`: `x` itself); `poison` if `x` is no tuple or too short. -/
def comp : Option Nat → Val → Val
  | none, x => x
  | some j, .tuple xs => xs.getD j .poison
  | some _, _ => .poison

/-- `x` has a component for every shape of the tuple shape `t` (a value written at `t`). -/
def TupleFits : Ty → Val → Prop
  | .tuple ts, .tuple xs => ts.length ≤ xs.length
  | _, _ => True

/-- The register file has its size. -/
def RegsOK (s : LocState) : Prop := s.regs.size = ARM64.registers.size

/-! ## Helpers: register, slot and tuple-component writes -/

private theorem retypePre_length : ∀ {ts : List Ty} {vs vs' : List Val},
    Val.retypePre ts vs = some vs' → ts.length ≤ vs'.length
  | [], _, _, _ => Nat.zero_le _
  | _ :: _, _ :: _, _, h => by
    simp only [Val.retypePre, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    simpa using retypePre_length ha
  | _ :: _, [], _, h => by simp [Val.retypePre] at h

private theorem tupleFits_retype' (t : Ty) (y : Val) : TupleFits t (y.retype t) := by
  cases t with
  | tuple ts =>
    cases y with
    | tuple vs =>
      simp only [Val.retype]
      split
      · rename_i vs' h
        exact retypePre_length h
      · trivial
    | _ => trivial
  | _ => trivial

private theorem regLoc_some {r : Nat} {l : Loc} (h : regLoc r = some l) :
    l = .reg r ∧ r ≠ zeroReg ∧ r < ARM64.registers.size := by
  unfold regLoc at h
  split at h
  · cases h
  · rename_i hc
    cases h
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or, Nat.not_le] at hc
    exact ⟨rfl, hc.1, hc.2⟩

private theorem regLoc_none {r : Nat} (h : regLoc r = none) :
    r = zeroReg ∨ ARM64.registers.size ≤ r := by
  unfold regLoc at h
  split at h
  · rename_i hc
    simpa only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, ge_iff_le] using hc
  · cases h

private theorem setReg_size (s : LocState) (r : Nat) (x : Val) :
    (s.setReg r x).regs.size = s.regs.size := by
  unfold LocState.setReg
  split <;> simp

private theorem setReg_of_none {s : LocState} (hs : RegsOK s) {r : Nat} (h : regLoc r = none)
    (x : Val) : s.setReg r x = s := by
  unfold RegsOK at hs
  unfold LocState.setReg
  have : (r < s.regs.size && r != zeroReg) = false := by
    rcases regLoc_none h with h | h
    · simp [h]
    · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      left; omega
  simp only [this, Bool.false_eq_true, ite_false]

private theorem at_setReg_self {s : LocState} (hs : RegsOK s) {r : Nat} {l : Loc}
    (h : regLoc r = some l) (x : Val) : (s.setReg r x).at l = x := by
  obtain ⟨rfl, hz, hr⟩ := regLoc_some h
  unfold RegsOK at hs
  have hr' : r < s.regs.size := by omega
  have : (r < s.regs.size && r != zeroReg) = true := by simp [hr', hz]
  simp only [LocState.setReg, this, ite_true, LocState.at, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds_self_of_lt hr', Option.getD_some]

private theorem at_setReg_ne (s : LocState) {r : Nat} {l : Loc} (h : l ≠ .reg r) (x : Val) :
    (s.setReg r x).at l = s.at l := by
  cases l with
  | reg r' =>
    have : r ≠ r' := fun e => h (e ▸ rfl)
    simp only [LocState.setReg, LocState.at]
    split <;> simp [Array.getElem?_setIfInBounds_ne this]
  | _ => rfl

private theorem at_setFlags {s : LocState} {l : Loc} (h : l ≠ .flags) (x : Val) :
    ({ s with flags := x } : LocState).at l = s.at l := by
  cases l <;> first | rfl | exact absurd rfl h

private theorem at_setMem {s : LocState} {l : Loc} (h : l ≠ .mem) (x : Val) :
    ({ s with mem := x } : LocState).at l = s.at l := by
  cases l <;> first | rfl | exact absurd rfl h

private theorem clashes_self (tabs : Tables) (l : Loc) : clashes tabs l l = true := by
  cases l <;> simp [clashes]

private theorem compLocs_cons {t : Ty} (ht : t ≠ .mem) (ts : List Ty) (rs : List (Option Nat))
    (j : Nat) : compLocs (t :: ts) rs j =
      if t.isFlags then (.flags, j) :: compLocs ts rs (j + 1)
      else match rs with
        | some r :: rs => ((regLoc r).toList.map (·, j)) ++ compLocs ts rs (j + 1)
        | none :: rs => compLocs ts rs (j + 1)
        | [] => compLocs ts [] (j + 1) := by
  cases t <;> first | exact absurd rfl ht | rfl

private theorem readParts_cons {t : Ty} (ht : t ≠ .mem) (s : LocState) (ts : List Ty)
    (rs : List (Option Nat)) : s.readParts (t :: ts) rs =
      if t.isFlags then s.flags :: s.readParts ts rs
      else match rs with
        | some r :: rs => s.reg t r :: s.readParts ts rs
        | none :: rs => .poison :: s.readParts ts rs
        | [] => .poison :: s.readParts ts [] := by
  cases t <;> first | exact absurd rfl ht | rfl

private theorem writeParts_cons {t : Ty} (ht : t ≠ .mem) (s : LocState) (ts : List Ty) (x : Val)
    (xs : List Val) (rs : List (Option Nat)) : s.writeParts (t :: ts) (x :: xs) rs =
      if t.isFlags then ({ s with flags := x } : LocState).writeParts ts xs rs
      else match rs with
        | some r :: rs => (s.setReg r x).writeParts ts xs rs
        | none :: rs => s.writeParts ts xs rs
        | [] => s.writeParts ts xs [] := by
  cases t <;> first | exact absurd rfl ht | rfl

private theorem readParts_length (s : LocState) : ∀ (ts : List Ty) (rs : List (Option Nat)),
    (s.readParts ts rs).length = ts.length
  | [], _ => rfl
  | t :: ts, rs => by
    by_cases hm : t = .mem
    · subst hm
      simp [LocState.readParts, readParts_length s ts rs]
    · rw [readParts_cons hm]
      split
      · simp [readParts_length s ts rs]
      · rcases rs with _ | ⟨_ | r, rs⟩ <;> simp [readParts_length]

private theorem mem_compLocs_ge : ∀ {ts : List Ty} {rs : List (Option Nat)} {j : Nat} {l : Loc}
    {i : Nat}, (l, i) ∈ compLocs ts rs j → j ≤ i
  | [], _, _, _, _, h => by simp [compLocs] at h
  | t :: ts, rs, j, l, i, h => by
    by_cases hm : t = .mem
    · subst hm
      simp only [compLocs, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨_, rfl⟩ | h
      · exact Nat.le_refl _
      · have := mem_compLocs_ge h; omega
    · rw [compLocs_cons hm] at h
      split at h
      · simp only [List.mem_cons, Prod.mk.injEq] at h
        rcases h with ⟨_, rfl⟩ | h
        · exact Nat.le_refl _
        · have := mem_compLocs_ge h; omega
      · rcases rs with _ | ⟨_ | r, rs⟩
        · have := mem_compLocs_ge h; omega
        · have := mem_compLocs_ge h; omega
        · simp only [List.mem_append, List.mem_map, Option.mem_toList, Prod.mk.injEq] at h
          rcases h with ⟨_, _, _, rfl⟩ | h
          · exact Nat.le_refl _
          · have := mem_compLocs_ge h; omega

/-- A tuple read: component `i - j` is the contents of its location. -/
private theorem readParts_compLocs (s : LocState) : ∀ {ts : List Ty} {rs : List (Option Nat)}
    {j : Nat} {l : Loc} {i : Nat}, (l, i) ∈ compLocs ts rs j →
    (s.readParts ts rs)[i - j]? = some (s.at l)
  | [], _, _, _, _, h => by simp [compLocs] at h
  | t :: ts, rs, j, l, i, h => by
    by_cases hm : t = .mem
    · subst hm
      simp only [compLocs, List.mem_cons, Prod.mk.injEq] at h
      simp only [LocState.readParts]
      rcases h with ⟨rfl, rfl⟩ | h
      · simp [LocState.at]
      · have := mem_compLocs_ge h
        rw [show i - j = (i - (j + 1)) + 1 by omega, List.getElem?_cons_succ]
        exact readParts_compLocs s h
    · rw [compLocs_cons hm] at h
      rw [readParts_cons hm]
      split at h
      · rename_i hf
        simp only [hf, ite_true]
        simp only [List.mem_cons, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩ | h
        · simp [LocState.at]
        · have := mem_compLocs_ge h
          rw [show i - j = (i - (j + 1)) + 1 by omega, List.getElem?_cons_succ]
          exact readParts_compLocs s h
      · rename_i hf
        simp only [hf, Bool.false_eq_true, ite_false]
        rcases rs with _ | ⟨_ | r, rs⟩
        · have := mem_compLocs_ge h
          rw [show i - j = (i - (j + 1)) + 1 by omega, List.getElem?_cons_succ]
          exact readParts_compLocs s h
        · have := mem_compLocs_ge h
          rw [show i - j = (i - (j + 1)) + 1 by omega, List.getElem?_cons_succ]
          exact readParts_compLocs s h
        · simp only [List.mem_append, List.mem_map, Option.mem_toList, Prod.mk.injEq] at h
          rcases h with ⟨l0, hl0, rfl, rfl⟩ | h
          · obtain ⟨rfl, hz, -⟩ := regLoc_some hl0
            have : (r == zeroReg) = false := by simpa using hz
            simp [LocState.at, LocState.reg, this]
          · have := mem_compLocs_ge h
            rw [show i - j = (i - (j + 1)) + 1 by omega, List.getElem?_cons_succ]
            exact readParts_compLocs s h

private theorem writeParts_size : ∀ (s : LocState) (ts : List Ty) (xs : List Val)
    (rs : List (Option Nat)), (s.writeParts ts xs rs).regs.size = s.regs.size
  | _, [], _, _ => rfl
  | _, _ :: _, [], _ => by simp [LocState.writeParts]
  | s, t :: ts, x :: xs, rs => by
    by_cases hm : t = .mem
    · subst hm
      simp only [LocState.writeParts]
      exact writeParts_size _ ts xs rs
    · rw [writeParts_cons hm]
      split
      · exact writeParts_size _ ts xs rs
      · rcases rs with _ | ⟨_ | r, rs⟩
        · exact writeParts_size _ ts xs []
        · exact writeParts_size _ ts xs rs
        · exact (writeParts_size _ ts xs rs).trans (setReg_size s r x)

private theorem writeParts_fr : ∀ (s : LocState) (ts : List Ty) (xs : List Val)
    (rs : List (Option Nat)), (s.writeParts ts xs rs).fr = s.fr
  | _, [], _, _ => rfl
  | _, _ :: _, [], _ => by simp [LocState.writeParts]
  | s, t :: ts, x :: xs, rs => by
    by_cases hm : t = .mem
    · subst hm
      simp only [LocState.writeParts]
      exact writeParts_fr _ ts xs rs
    · rw [writeParts_cons hm]
      split
      · exact writeParts_fr _ ts xs rs
      · rcases rs with _ | ⟨_ | r, rs⟩
        · exact writeParts_fr _ ts xs []
        · exact writeParts_fr _ ts xs rs
        · exact writeParts_fr _ ts xs rs

/-- A tuple write leaves every location outside its components' locations unchanged. -/
private theorem at_writeParts_other : ∀ (s : LocState) (ts : List Ty) (xs : List Val)
    (rs : List (Option Nat)) (j : Nat), RegsOK s → ∀ {l : Loc},
    l ∉ (compLocs ts rs j).map (·.1) → (s.writeParts ts xs rs).at l = s.at l
  | _, [], _, _, _, _, _, _ => rfl
  | _, _ :: _, [], _, _, _, _, _ => by simp [LocState.writeParts]
  | s, t :: ts, x :: xs, rs, j, hs, l, hl => by
    by_cases hm : t = .mem
    · subst hm
      simp only [compLocs, List.map_cons, List.mem_cons, not_or] at hl
      simp only [LocState.writeParts]
      rw [at_writeParts_other ({ s with mem := x } : LocState) ts xs rs (j + 1) hs hl.2, at_setMem hl.1]
    · rw [compLocs_cons hm] at hl
      rw [writeParts_cons hm]
      split
      · rename_i hf
        simp only [hf, ite_true, List.map_cons, List.mem_cons, not_or] at hl
        rw [at_writeParts_other ({ s with flags := x } : LocState) ts xs rs (j + 1) hs hl.2, at_setFlags hl.1]
      · rename_i hf
        simp only [hf, Bool.false_eq_true, ite_false] at hl
        rcases rs with _ | ⟨_ | r, rs⟩ <;> dsimp only
        · exact at_writeParts_other _ ts xs [] (j + 1) hs hl
        · exact at_writeParts_other _ ts xs rs (j + 1) hs hl
        · simp only [List.map_append, List.mem_append, not_or] at hl
          have hs' : RegsOK (s.setReg r x) := (setReg_size s r x).trans hs
          rw [at_writeParts_other (s.setReg r x) ts xs rs (j + 1) hs' hl.2]
          rcases hr : regLoc r with _ | l0
          · rw [setReg_of_none hs hr]
          · obtain ⟨rfl, -, -⟩ := regLoc_some hr
            simp only [hr, Option.toList_some, List.map_cons, List.map_nil, List.mem_singleton]
              at hl
            exact at_setReg_ne s hl.1 x

/-- A tuple write puts component `i - j` in the location of component `i`. -/
private theorem at_writeParts : ∀ (s : LocState) (ts : List Ty) (xs : List Val)
    (rs : List (Option Nat)) (j : Nat), RegsOK s → ts.length ≤ xs.length →
    ((compLocs ts rs j).map (·.1)).Nodup → ∀ {l : Loc} {i : Nat}, (l, i) ∈ compLocs ts rs j →
    (s.writeParts ts xs rs).at l = xs.getD (i - j) .poison
  | _, [], _, _, _, _, _, _, _, _, h => by simp [compLocs] at h
  | _, _ :: _, [], _, _, _, hlen, _, _, _, _ => by simp at hlen
  | s, t :: ts, x :: xs, rs, j, hs, hlen, hnd, l, i, h => by
    have hlen' : ts.length ≤ xs.length := by simpa using hlen
    by_cases hm : t = .mem
    · subst hm
      simp only [compLocs, List.map_cons, List.nodup_cons, List.mem_cons, Prod.mk.injEq] at h hnd
      simp only [LocState.writeParts]
      rcases h with ⟨rfl, rfl⟩ | h
      · rw [at_writeParts_other ({ s with mem := x } : LocState) ts xs rs _ hs hnd.1]
        simp [LocState.at]
      · have := mem_compLocs_ge h
        rw [at_writeParts ({ s with mem := x } : LocState) ts xs rs (j + 1) hs hlen' hnd.2 h,
          show i - j = (i - (j + 1)) + 1 by omega, List.getD_cons_succ]
    · rw [compLocs_cons hm] at h hnd
      rw [writeParts_cons hm]
      split
      · rename_i hf
        simp only [hf, ite_true, List.map_cons, List.nodup_cons, List.mem_cons, Prod.mk.injEq]
          at h hnd
        rcases h with ⟨rfl, rfl⟩ | h
        · rw [at_writeParts_other ({ s with flags := x } : LocState) ts xs rs _ hs hnd.1]
          simp [LocState.at]
        · have := mem_compLocs_ge h
          rw [at_writeParts ({ s with flags := x } : LocState) ts xs rs (j + 1) hs hlen' hnd.2 h,
            show i - j = (i - (j + 1)) + 1 by omega, List.getD_cons_succ]
      · rename_i hf
        simp only [hf, Bool.false_eq_true, ite_false] at h hnd
        rcases rs with _ | ⟨_ | r, rs⟩ <;> dsimp only
        · have := mem_compLocs_ge h
          rw [at_writeParts _ ts xs [] (j + 1) hs hlen' hnd h,
            show i - j = (i - (j + 1)) + 1 by omega, List.getD_cons_succ]
        · have := mem_compLocs_ge h
          rw [at_writeParts _ ts xs rs (j + 1) hs hlen' hnd h,
            show i - j = (i - (j + 1)) + 1 by omega, List.getD_cons_succ]
        · have hs' : RegsOK (s.setReg r x) := (setReg_size s r x).trans hs
          rcases hr : regLoc r with _ | l0
          · simp only [hr, Option.toList_none, List.map_nil, List.nil_append] at h hnd
            rw [setReg_of_none hs hr]
            have := mem_compLocs_ge h
            rw [at_writeParts _ ts xs rs (j + 1) hs hlen' hnd h,
              show i - j = (i - (j + 1)) + 1 by omega, List.getD_cons_succ]
          · simp only [hr, Option.toList_some, List.map_cons, List.map_nil, List.cons_append,
              List.nil_append, List.nodup_cons, List.mem_cons, Prod.mk.injEq] at h hnd
            rcases h with ⟨rfl, rfl⟩ | h
            · rw [at_writeParts_other (s.setReg r x) ts xs rs _ hs' hnd.1, at_setReg_self hs hr]
              simp
            · have := mem_compLocs_ge h
              rw [at_writeParts (s.setReg r x) ts xs rs (j + 1) hs' hlen' hnd.2 h,
                show i - j = (i - (j + 1)) + 1 by omega, List.getD_cons_succ]

private theorem getD_replicate_poison : ∀ (n i : Nat),
    (List.replicate n Val.poison).getD i .poison = .poison
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | n + 1, i + 1 => getD_replicate_poison n i

private theorem comp_some (i : Nat) (x : Val) (n : Nat) :
    comp (some i) x = (x.partsOf n).getD i .poison := by
  cases x with
  | tuple xs => rfl
  | _ => exact (getD_replicate_poison n i).symm

private theorem partsOf_length {t : Ty} {ts : List Ty} (ht : t = .tuple ts) {x : Val}
    (hx : TupleFits t x) : ts.length ≤ (x.partsOf ts.length).length := by
  subst ht
  cases x with
  | tuple xs => exact hx
  | _ => simp [Val.partsOf]

private theorem map_fst_comp (ls : List (Loc × Nat)) :
    ((ls.map fun (l, j) => (l, some j)).map (·.1)) = ls.map (·.1) := by
  simp only [List.map_map]
  rfl

/-- `LocState.raw` by the location `readLoc` gives. -/
private theorem raw_cases (lc : LocCtx) (s : LocState) (a : ID) :
    (∃ k, readLoc (lc.home a) (lc.ty a) = some (.loc (.slot k)) ∧
      s.raw lc a = .ok ((s.slots.lookup k).getD .poison)) ∨
    (∃ ts rs, lc.ty a = .tuple ts ∧ readLoc (lc.home a) (lc.ty a) = some (.tuple (compLocs ts rs 0)) ∧
      s.raw lc a = .ok (.tuple (s.readParts ts rs))) ∨
    (∃ r, readLoc (lc.home a) (lc.ty a) = (if r == zeroReg then some .zero else
        match regLoc r with
        | some l => some (.loc l)
        | none => some .poison) ∧ s.raw lc a = .ok (s.reg (lc.ty a) r)) ∨
    (readLoc (lc.home a) (lc.ty a) = some .poison ∧ s.raw lc a = .ok .poison) ∨
    (readLoc (lc.home a) (lc.ty a) = some (.loc .mem) ∧ s.raw lc a = .ok s.mem) ∨
    (readLoc (lc.home a) (lc.ty a) = (if (lc.ty a).isFlags then some (.loc .flags) else none) ∧
      ((lc.ty a).isFlags = true → s.raw lc a = .ok s.flags)) := by
  unfold readLoc LocState.raw
  generalize lc.home a = hm
  generalize lc.ty a = t
  rcases hm with _ | ⟨r | k | ⟨p, q⟩ | rs⟩ <;> cases t <;>
    first
    | exact Or.inl ⟨_, rfl, rfl⟩
    | exact Or.inr <| Or.inl ⟨_, _, rfl, rfl, rfl⟩
    | exact Or.inr <| Or.inr <| Or.inl ⟨_, rfl, rfl⟩
    | exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, rfl⟩
    | exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, rfl⟩
    | exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨rfl, fun hf => ite_eq_left hf⟩

/-- `LocState.write` by the locations `writeLocs` gives. -/
private theorem write_cases (lc : LocCtx) (s : LocState) (id : ID) (x : Val) :
    (∃ k, writeLocs (lc.home id) (lc.ty id) = [(.slot k, none)] ∧
      s.write lc id x = s.setSlot lc.ctx.tabs k x) ∨
    (∃ ts rs, lc.ty id = .tuple ts ∧
      writeLocs (lc.home id) (lc.ty id) = (compLocs ts rs 0).map (fun (l, j) => (l, some j)) ∧
      s.write lc id x = s.writeParts ts (x.partsOf ts.length) rs) ∨
    (∃ r, writeLocs (lc.home id) (lc.ty id) = (regLoc r).toList.map (·, none) ∧
      s.write lc id x = s.setReg r x) ∨
    (writeLocs (lc.home id) (lc.ty id) = [(.mem, none)] ∧ s.write lc id x = { s with mem := x }) ∨
    (writeLocs (lc.home id) (lc.ty id) = (if (lc.ty id).isFlags then [(.flags, none)] else []) ∧
      s.write lc id x = if (lc.ty id).isFlags then { s with flags := x } else s) := by
  unfold writeLocs LocState.write
  generalize lc.home id = hm
  generalize lc.ty id = t
  rcases hm with _ | ⟨r | k | ⟨p, q⟩ | rs⟩ <;> cases t <;>
    first
    | exact Or.inl ⟨_, rfl, rfl⟩
    | exact Or.inr <| Or.inl ⟨_, _, rfl, rfl, rfl⟩
    | exact Or.inr <| Or.inr <| Or.inl ⟨_, rfl, rfl⟩
    | exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, rfl⟩
    | exact Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨rfl, rfl⟩

private theorem lookup_filter {k : SlotKey} {p : SlotKey × Val → Bool} (hp : ∀ v, p (k, v) = true) :
    ∀ (l : List (SlotKey × Val)), (l.filter p).lookup k = l.lookup k
  | [] => rfl
  | (k₀, v₀) :: l => by
    by_cases hk : k = k₀
    · subst hk
      simp [List.filter, hp, List.lookup]
    · have hb : (k == k₀) = false := by simpa using hk
      simp only [List.filter]
      split <;> simp [List.lookup, hb, lookup_filter hp l]

private theorem lookup_setSlot {tabs : Tables} {s : LocState} {k k' : SlotKey} (x : Val)
    (h : clashes tabs (.slot k) (.slot k') = false) :
    (s.setSlot tabs k x).slots.lookup k' = s.slots.lookup k' := by
  simp only [clashes, Bool.or_eq_false_iff] at h
  obtain ⟨hk, ho⟩ := h
  unfold LocState.setSlot
  simp only [List.lookup, hk]
  refine lookup_filter (fun _ => ?_) s.slots
  unfold slotOverlaps at ho
  rw [Bool.not_eq_eq_eq_not, Bool.not_true]
  exact ho

private theorem not_mem_of_clashes {tabs : Tables} {L : List Loc} {l' : Loc}
    (hl : ∀ l ∈ L, clashes tabs l l' = false) : l' ∉ L := fun h => by
  have := hl l' h
  rw [clashes_self] at this
  cases this

/-- A property of states every clobber preserves. -/
private theorem clobber_preserves (P : LocState → Prop)
    (hm : ∀ s m, P s → P (s.clobberMask m)) (hr : ∀ s r, P s → P (s.setReg r .poison))
    (hf : ∀ s : LocState, P s → P { s with flags := .poison }) (lc : LocCtx) (v : Value)
    {s : LocState} (hs : P s) : P (s.clobber lc v) := by
  have harg : ∀ (b : Bool) (o : Option Nat) (s' : LocState), P s' →
      P (if !b then s' else match o with
        | some r => s'.setReg r .poison
        | none => s') := by
    intro b o s' h
    cases b
    · exact h
    · cases o
      · exact h
      · exact hr _ _ h
  have htemp : ∀ (o : Option Nat) (s' : LocState), P s' →
      P (match o with
        | some r => s'.setReg r .poison
        | none => s') := by
    intro o s' h
    cases o
    · exact h
    · exact hr _ _ h
  have hflag : ∀ (c : Bool) (s' : LocState), P s' →
      P (if c then { s' with flags := .poison } else s') := by
    intro c s' h
    cases c
    · exact h
    · exact hf _ h
  unfold LocState.clobber
  apply hflag
  apply htemp
  apply harg
  apply harg
  exact hm _ _ hs

/-- The facts `S'` are facts of `S` at locations where `s'` and `s` agree. -/
private def Keeps (S : Facts) (s : LocState) (S' : Facts) (s' : LocState) : Prop :=
  ∀ F ∈ S', F ∈ S ∧ s'.at F.1 = s.at F.1

private theorem keeps_mask {S : Facts} {s : LocState} {S' : Facts} {s' : LocState}
    (h : Keeps S s S' s') (m : RegMask) :
    Keeps S s (if m.isEmpty then S' else S'.filter fun (l, _) => match l with
      | .reg r => !m.hasReg r
      | _ => true) (s'.clobberMask m) := by
  intro F hF
  by_cases he : m.isEmpty = true
  · rw [ite_eq_left he] at hF
    have : s'.clobberMask m = s' := by unfold LocState.clobberMask; rw [ite_eq_left he]
    rw [this]
    exact h F hF
  · rw [ite_eq_right he, List.mem_filter] at hF
    obtain ⟨hF, hk⟩ := hF
    obtain ⟨h1, h2⟩ := h F hF
    refine ⟨h1, ?_⟩
    rw [← h2]
    obtain ⟨l, o⟩ := F
    cases l with
    | reg r =>
      have hk' : m.hasReg r = false := by simpa using hk
      simp only [LocState.clobberMask, he, Bool.false_eq_true, ite_false, LocState.at,
        Array.getElem?_mapIdx]
      cases s'.regs[r]? <;> simp [hk']
    | _ =>
      unfold LocState.clobberMask
      rw [ite_eq_right he]
      rfl

private theorem keeps_killR {S : Facts} {s : LocState} {S' : Facts} {s' : LocState}
    (h : Keeps S s S' s') (r : Nat) :
    Keeps S s (S'.filter (·.1 != .reg r)) (s'.setReg r .poison) := by
  intro F hF
  rw [List.mem_filter, bne_iff_ne] at hF
  obtain ⟨h1, h2⟩ := h F hF.1
  exact ⟨h1, (at_setReg_ne s' hF.2 _).trans h2⟩

private theorem keeps_arg {S : Facts} {s : LocState} {S' : Facts} {s' : LocState}
    (h : Keeps S s S' s') (b : Bool) (o : Option Nat) :
    Keeps S s (if !b then S' else match o with
        | some r => S'.filter (·.1 != .reg r)
        | none => S')
      (if !b then s' else match o with
        | some r => s'.setReg r .poison
        | none => s') := by
  cases b
  · exact h
  · cases o
    · exact h
    · exact keeps_killR h _

private theorem keeps_temps {S : Facts} {s : LocState} {S' : Facts} {s' : LocState}
    (h : Keeps S s S' s') (o : Option Nat) :
    Keeps S s (match o with
        | some r => S'.filter (·.1 != .reg r)
        | none => S')
      (match o with
        | some r => s'.setReg r .poison
        | none => s') := by
  cases o
  · exact h
  · exact keeps_killR h _

private theorem keeps_flags {S : Facts} {s : LocState} {S' : Facts} {s' : LocState}
    (h : Keeps S s S' s') (c : Bool) :
    Keeps S s (if c then S'.filter (·.1 != .flags) else S')
      (if c then { s' with flags := .poison } else s') := by
  cases c
  · exact h
  · intro F hF
    rw [ite_eq_left rfl, List.mem_filter, bne_iff_ne] at hF
    obtain ⟨h1, h2⟩ := h F hF.1
    exact ⟨h1, (at_setFlags hF.2 _).trans h2⟩

theorem tupleFits_retype (md : LMode) (t : Ty) (x : Val) : TupleFits t (md.retype t x) := by
  unfold LMode.retype
  split
  · exact tupleFits_retype' t _
  · exact tupleFits_retype' t _

theorem raw_loc {lc : LocCtx} {s : LocState} {a : ID} {l : Loc}
    (h : readLoc (lc.home a) (lc.ty a) = some (.loc l)) : s.raw lc a = .ok (s.at l) := by
  rcases raw_cases lc s a with ⟨k, hr, hraw⟩ | ⟨ts, rs, -, hr, -⟩ | ⟨r, hr, hraw⟩ | ⟨hr, -⟩ |
      ⟨hr, hraw⟩ | ⟨hr, hraw⟩ <;> rw [hr] at h
  · cases h; exact hraw
  · cases h
  · split at h
    · cases h
    · split at h
      · rename_i l0 hl0
        cases h
        obtain ⟨rfl, hz, -⟩ := regLoc_some hl0
        have : (r == zeroReg) = false := by simpa using hz
        rw [hraw]
        simp [LocState.reg, LocState.at, this]
      · cases h
  · cases h
  · cases h; exact hraw
  · split at h
    · rename_i hf
      cases h; exact hraw hf
    · cases h

theorem raw_zero {lc : LocCtx} {s : LocState} {a : ID}
    (h : readLoc (lc.home a) (lc.ty a) = some .zero) :
    s.raw lc a = .ok ((Arm64.res (lc.ty a) 0).retypeL (lc.ty a)) := by
  rcases raw_cases lc s a with ⟨k, hr, -⟩ | ⟨ts, rs, -, hr, -⟩ | ⟨r, hr, hraw⟩ | ⟨hr, -⟩ |
      ⟨hr, -⟩ | ⟨hr, -⟩ <;> rw [hr] at h
  · cases h
  · cases h
  · split at h
    · rename_i hz
      rw [hraw]
      simp [LocState.reg, hz]
    · split at h <;> cases h
  · cases h
  · cases h
  · split at h <;> cases h

/-- A tuple read: the components with a location are those locations' contents. -/
theorem raw_tuple {lc : LocCtx} {s : LocState} {a : ID} {ls : List (Loc × Nat)}
    (h : readLoc (lc.home a) (lc.ty a) = some (.tuple ls)) :
    ∃ ts xs, lc.ty a = .tuple ts ∧ s.raw lc a = .ok (.tuple xs) ∧ xs.length = ts.length ∧
      ∀ l j, (l, j) ∈ ls → xs[j]? = some (s.at l) := by
  rcases raw_cases lc s a with ⟨k, hr, -⟩ | ⟨ts, rs, hty, hr, hraw⟩ | ⟨r, hr, -⟩ | ⟨hr, -⟩ |
      ⟨hr, -⟩ | ⟨hr, -⟩ <;> rw [hr] at h
  · cases h
  · cases h
    refine ⟨ts, _, hty, hraw, readParts_length s ts rs, fun l j hl => ?_⟩
    simpa using readParts_compLocs s hl
  · split at h
    · cases h
    · split at h <;> cases h
  · cases h
  · cases h
  · split at h <;> cases h

theorem raw_ok {lc : LocCtx} {s : LocState} {a : ID} {r : RLoc}
    (h : readLoc (lc.home a) (lc.ty a) = some r) : ∃ x, s.raw lc a = .ok x := by
  rcases raw_cases lc s a with ⟨k, hr, hraw⟩ | ⟨ts, rs, -, hr, hraw⟩ | ⟨r, hr, hraw⟩ |
      ⟨hr, hraw⟩ | ⟨hr, hraw⟩ | ⟨hr, hraw⟩
  · exact ⟨_, hraw⟩
  · exact ⟨_, hraw⟩
  · exact ⟨_, hraw⟩
  · exact ⟨_, hraw⟩
  · exact ⟨_, hraw⟩
  · rw [hr] at h
    split at h
    · rename_i hf
      exact ⟨_, hraw hf⟩
    · cases h

theorem regsOK_write {lc : LocCtx} {s : LocState} (hs : RegsOK s) (id : ID) (x : Val) :
    RegsOK (s.write lc id x) := by
  unfold RegsOK at hs ⊢
  rcases write_cases lc s id x with ⟨k, -, hw⟩ | ⟨ts, rs, -, -, hw⟩ | ⟨r, -, hw⟩ | ⟨-, hw⟩ |
      ⟨-, hw⟩ <;> rw [hw]
  all_goals first | exact hs | (rw [writeParts_size]; exact hs) | (rw [setReg_size]; exact hs) |
    (split <;> exact hs)

theorem regsOK_clobber {lc : LocCtx} {s : LocState} (hs : RegsOK s) (v : Value) :
    RegsOK (s.clobber lc v) :=
  clobber_preserves RegsOK
    (fun s m h => by
      unfold RegsOK at h ⊢
      unfold LocState.clobberMask
      split
      · exact h
      · simpa using h)
    (fun s r h => (setReg_size s r _).trans h) (fun _ h => h) lc v hs

theorem write_fr (lc : LocCtx) (s : LocState) (id : ID) (x : Val) : (s.write lc id x).fr = s.fr := by
  rcases write_cases lc s id x with ⟨k, -, hw⟩ | ⟨ts, rs, -, -, hw⟩ | ⟨r, -, hw⟩ | ⟨-, hw⟩ |
      ⟨-, hw⟩ <;> rw [hw]
  all_goals first | rfl | exact writeParts_fr _ _ _ _ | (split <;> rfl)

theorem clobber_fr (lc : LocCtx) (s : LocState) (v : Value) : (s.clobber lc v).fr = s.fr :=
  clobber_preserves (fun s' => s'.fr = s.fr)
    (fun s m h => by
      unfold LocState.clobberMask
      split
      · exact h
      · exact h)
    (fun _ _ h => h) (fun _ h => h) lc v rfl

/-- A write puts component `j` of its value in each location `writeLocs` gives it. -/
theorem at_write {lc : LocCtx} {s : LocState} (hs : RegsOK s) {id : ID} {x : Val}
    (hnd : writesNodup (lc.home id) (lc.ty id) = true) (hx : TupleFits (lc.ty id) x)
    {l : Loc} {j : Option Nat} (hl : (l, j) ∈ writeLocs (lc.home id) (lc.ty id)) :
    (s.write lc id x).at l = comp j x := by
  unfold writesNodup at hnd
  rcases write_cases lc s id x with ⟨k, hwl, hw⟩ | ⟨ts, rs, hty, hwl, hw⟩ | ⟨r, hwl, hw⟩ |
      ⟨hwl, hw⟩ | ⟨hwl, hw⟩ <;> rw [hwl] at hl hnd <;> rw [hw]
  · simp only [List.mem_singleton, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    simp [LocState.setSlot, LocState.at, comp]
  · simp only [List.mem_map, Prod.mk.injEq] at hl
    obtain ⟨⟨l0, i⟩, hi, rfl, rfl⟩ := hl
    rw [map_fst_comp] at hnd
    rw [at_writeParts s ts _ rs 0 hs (partsOf_length hty hx) (by simpa using hnd) hi,
      Nat.sub_zero, comp_some i x ts.length]
  · rcases hr : regLoc r with _ | l0 <;> simp only [hr, Option.toList_none, Option.toList_some,
      List.map_nil, List.map_cons, List.mem_singleton, List.not_mem_nil, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    exact at_setReg_self hs hr x
  · simp only [List.mem_singleton, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    rfl
  · split at hl
    · rename_i hf
      simp only [hf, ite_true]
      simp only [List.mem_singleton, Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      rfl
    · simp at hl

/-- A write leaves every location that clashes with none of its locations unchanged. -/
theorem at_write_other {lc : LocCtx} {s : LocState} (hs : RegsOK s) {id : ID} {x : Val} {l' : Loc}
    (hl : ∀ l ∈ killLocs (lc.home id) (lc.ty id), clashes lc.ctx.tabs l l' = false) :
    (s.write lc id x).at l' = s.at l' := by
  unfold killLocs at hl
  rcases write_cases lc s id x with ⟨k, hwl, hw⟩ | ⟨ts, rs, hty, hwl, hw⟩ | ⟨r, hwl, hw⟩ |
      ⟨hwl, hw⟩ | ⟨hwl, hw⟩ <;> rw [hwl] at hl <;> rw [hw]
  · have h1 := hl (.slot k) (by simp)
    cases l' with
    | slot k' =>
      show ((s.setSlot _ k x).slots.lookup k').getD _ = _
      rw [lookup_setSlot x h1]
      rfl
    | _ => rfl
  · rw [map_fst_comp] at hl
    exact at_writeParts_other s ts _ rs 0 hs (not_mem_of_clashes hl)
  · rcases hr : regLoc r with _ | l0
    · rw [setReg_of_none hs hr]
    · obtain ⟨rfl, -, -⟩ := regLoc_some hr
      simp only [hr, Option.toList_some, List.map_cons, List.map_nil] at hl
      have := not_mem_of_clashes hl
      simp only [List.mem_singleton] at this
      exact at_setReg_ne s this x
  · have := not_mem_of_clashes hl
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at this
    exact at_setMem this x
  · split
    · rename_i hf
      simp only [hf, ite_true, List.map_cons, List.map_nil] at hl
      have := not_mem_of_clashes hl
      simp only [List.mem_singleton] at this
      exact at_setFlags this x
    · rfl

theorem mem_killLoc {tabs : Tables} {l : Loc} {S : Facts} {F : Fact} (h : F ∈ killLoc tabs l S) :
    F ∈ S ∧ clashes tabs l F.1 = false := by
  unfold killLoc at h
  simp only [List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  exact h

/-- The facts that survive the write of a value of home `h` and shape `t`. -/
theorem mem_killLocs {tabs : Tables} {h : Option Location} {t : Ty} {S : Facts} {F : Fact}
    (hF : F ∈ (killLocs h t).foldl (fun S l => killLoc tabs l S) S) :
    F ∈ S ∧ ∀ l ∈ killLocs h t, clashes tabs l F.1 = false := by
  suffices ∀ (L : List Loc) (S : Facts), F ∈ L.foldl (fun S l => killLoc tabs l S) S →
      F ∈ S ∧ ∀ l ∈ L, clashes tabs l F.1 = false from this _ _ hF
  intro L
  induction L with
  | nil => intro S h; exact ⟨h, fun _ h => by cases h⟩
  | cons l L ih =>
    intro S h
    obtain ⟨h1, h2⟩ := ih _ h
    obtain ⟨h3, h4⟩ := mem_killLoc h1
    refine ⟨h3, fun l' hl' => ?_⟩
    rcases List.mem_cons.mp hl' with rfl | hl'
    · exact h4
    · exact h2 l' hl'

/-- The facts `clobberFacts` keeps are facts of `S` at locations the clobbers leave alone. -/
theorem at_clobber {cx : Cx} {S : Facts} {w : Value} {F : Fact} (hF : F ∈ clobberFacts cx S w)
    (s : LocState) : F ∈ S ∧ (s.clobber cx.lc w).at F.1 = s.at F.1 := by
  have : Keeps S s (clobberFacts cx S w) (s.clobber cx.lc w) := by
    unfold clobberFacts LocState.clobber
    apply keeps_flags
    apply keeps_temps
    apply keeps_arg
    apply keeps_arg
    apply keeps_mask
    exact fun F hF => ⟨hF, rfl⟩
  exact this F hF

/-! ## Shapes -/

theorem retype_shapeEq (md : LMode) {t t' : Ty} (h : shapeEq t t' = true) (x : Val) :
    md.retype t x = md.retype t' x := by
  unfold shapeEq at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have key : ∀ {u : Ty}, isWord u = true → md.retype u x = md.retype (.int .w64) x := by
      intro u hu
      unfold isWord at hu
      split at hu
      · rename_i e
        unfold LMode.retype
        split
        · unfold Val.retypeL
          have : x.widen (.ptr e) = x.widen (.int .w64) := by
            cases x with
            | int w y => cases w <;> rfl
            | _ => rfl
          rw [this, Val.retype_ptr_eq_i64]
        · exact Val.retype_ptr_eq_i64 x e
      · rfl
      · cases hu
    rw [key h1, key h2]
  · rw [Ty.eq_of_beq h]

/-- Narrowing an integer read: `retypeL (int w) ∘ retypeL (int w') = retypeL (int w)` for
`w ≤ w' < 64`. -/
private theorem retypeL_int_int {w w' : Width} (h1 : w.bits ≤ w'.bits) (h2 : w'.bits < 64)
    (x : Val) : (x.retypeL (.int w')).retypeL (.int w) = x.retypeL (.int w) := by
  cases w <;> cases w' <;> simp only [Width.bits] at h1 h2 <;> (try omega) <;>
  cases x with
  | int v y => cases v <;> simp [Val.retypeL, Val.widen, Val.retype, Width.bits]
  | bool b => cases b <;> simp [Val.retypeL, Val.widen, Val.retype, Width.bits] <;> decide
  | _ => rfl

theorem retype_composes {md : LMode} {t t' : Ty} (h : composes md.low t t' = true) (x : Val) :
    md.retype t (md.retype t' x) = md.retype t x := by
  unfold composes at h
  rcases Bool.or_eq_true_iff.mp h with h' | h'
  · rw [← retype_shapeEq md h' x, LMode.retype_idem]
  · clear h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨hlow, h'⟩ := h'
    obtain ⟨w, rfl⟩ : ∃ w, t = .int w := by
      cases t <;> first | exact ⟨_, rfl⟩ | (cases t' <;> simp at h')
    obtain ⟨w', rfl⟩ : ∃ w', t' = .int w' := by
      cases t' <;> first | exact ⟨_, rfl⟩ | simp at h'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
    simp only [LMode.retype, hlow, ite_true]
    exact retypeL_int_int h'.1 h'.2 x

theorem retype_composesAt {md : LMode} {t t' : Ty} (h : composesAt md.low t t' = true) {x : Val}
    (hx : md.retype t x = x) : md.retype t (md.retype t' x) = x := by
  unfold composesAt at h
  rcases Bool.or_eq_true_iff.mp h with h' | h'
  · rw [← retype_shapeEq md h' x, hx, hx]
  · clear h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨hlow, h'⟩ := h'
    obtain ⟨w, rfl⟩ : ∃ w, t = .int w := by
      cases t <;> first | exact ⟨_, rfl⟩ | (cases t' <;> simp at h')
    obtain ⟨w', rfl⟩ : ∃ w', t' = .int w' := by
      cases t' <;> first | exact ⟨_, rfl⟩ | simp at h'
    simp only [decide_eq_true_eq] at h'
    simp only [LMode.retype, hlow, ite_true] at hx ⊢
    by_cases hw : w = w'
    · subst hw
      rw [hx, hx]
    · have h2 : w.bits < w'.bits := by
        cases w <;> cases w' <;> simp only [Width.bits] at h' ⊢ <;> first | omega | exact absurd rfl hw
      have ht := Val.retypeL_hasTy (.int w) x
      rw [hx] at ht
      cases x with
      | poison => rfl
      | int v y =>
        simp only [Val.hasTy, beq_iff_eq] at ht
        subst ht
        cases v <;> cases w' <;> simp only [Width.bits] at h2 <;> (try omega) <;>
          simp [Val.retypeL, Val.widen, Val.retype, Width.bits]
      | ptr p =>
        cases w <;> cases w' <;> simp only [Width.bits] at h2 <;> (try omega) <;>
          simp [Val.hasTy] at ht
      | _ => simp [Val.hasTy] at ht

end GoFV.Proof.RA

import GoFV.Proof.WF
import GoFV.SSA.Live
import Std.Tactic.Do

variable [GoFV.SSA.Sem.Addrs]

/-!
# Soundness of `reachableBlocks`

`reachable_spec`: the entry is marked, marked blocks are listed, and every successor a marked
block runs to (all of them, only the first for a `First` block) is marked. The worklist loop
keeps `OInv`: marked blocks are listed, stack entries are marked, a marked block off the stack
has all its run successors marked, and (until the stack empties) iterations done plus stack
size are at most the number of marked entries, at most `n`, so the stack is empty once the
`n + 1` iterations are spent. `IInv` is the same during the successor loop of a popped block.
-/

open Std.Do

set_option mvcgen.warning false

namespace GoFV.Proof.Dead

open GoFV.SSA GoFV.Proof

/-- The successors the loop follows from `blk` (the first only for a `First` block). -/
def runSuccs (blk : Block) : Array Edge :=
  if (blk.kind == BlockKind.First) = true then blk.succs.extract 0 1 else blk.succs

/-- Number of marked entries. -/
def cnt (r : Array Bool) : Nat := r.toList.count true

/-- All run successors of `b` are marked in `r`. -/
def Closed (f : Func) (r : Array Bool) (b : ID) : Prop :=
  ∀ blk, f.block? b = some blk → ∀ e ∈ runSuccs blk, r.getD e.b false = true

/-- Invariant of the outer loop after `t` iterations with state `(r, stack)`. -/
structure OInv (f : Func) (t : Nat) (r : Array Bool) (stack : Array ID) : Prop where
  size : r.size = f.bidLast + 1
  entry : r.getD f.entry false = true
  listed : ∀ b, r.getD b false = true → b ∈ f.blocks
  stk : ∀ x ∈ stack, r.getD x false = true
  closed : ∀ b, r.getD b false = true → b ∈ stack ∨ Closed f r b
  count : stack = #[] ∨ stack.size + t ≤ cnt r

/-- Invariant of the successor loop of the popped block `b0` (iteration `t` of the outer loop),
after the successors `pre`. -/
structure IInv (f : Func) (t : Nat) (b0 : ID) (pre : List Edge) (r : Array Bool)
    (stack : Array ID) : Prop where
  size : r.size = f.bidLast + 1
  entry : r.getD f.entry false = true
  listed : ∀ b, r.getD b false = true → b ∈ f.blocks
  stk : ∀ x ∈ stack, r.getD x false = true
  home : b0 ∈ f.blocks
  closed : ∀ b, r.getD b false = true → b ∈ stack ∨ Closed f r b ∨ b = b0
  pre : ∀ e ∈ pre, r.getD e.b false = true
  count : stack.size + t + 1 ≤ cnt r

/-! ## Arrays -/

theorem getD_irrel {r : Array Bool} {i : Nat} (h : i < r.size) (d d' : Bool) :
    r.getD i d = r.getD i d' := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getD_getElem?,
    Array.getD_getElem?, dite_eq_left h, dite_eq_left h]

theorem lt_of_marked {r : Array Bool} {i : Nat} (h : r.getD i false = true) : i < r.size := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_getElem?] at h
  split at h
  · assumption
  · cases h

theorem getD_set {r : Array Bool} {i x : Nat} (hi : i < r.size) :
    (r.set! i true).getD x false = true ↔ x = i ∨ r.getD x false = true := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds]
  by_cases h : i = x
  · subst h; simp [hi]
  · simp [h, Ne.symm h]

theorem getD_replicate {n x : Nat} : (Array.replicate n false).getD x false = false := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

theorem cnt_set {r : Array Bool} {i : Nat} (hi : i < r.size) (h0 : r.getD i true = false) :
    cnt (r.set! i true) = cnt r + 1 := by
  have hr : r[i] = false := by
    rw [Array.getD_eq_getD_getElem?, Array.getD_getElem?, dite_eq_left hi] at h0
    exact h0
  unfold cnt
  rw [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds,
    List.count_set (by simpa using hi)]
  simp [hr]

theorem cnt_le (r : Array Bool) : cnt r ≤ r.size := by
  unfold cnt; rw [← Array.length_toList]; exact List.count_le_length

theorem cnt_pos {r : Array Bool} {i : Nat} (h : r.getD i false = true) : 0 < cnt r := by
  have hi := lt_of_marked h
  rw [Array.getD_eq_getD_getElem?, Array.getD_getElem?, dite_eq_left hi] at h
  unfold cnt
  rw [List.count_pos_iff, ← h]
  exact Array.getElem_mem_toList hi

theorem mem_of_back? {s : Array ID} {b : ID} (hb : s.back? = some b) : b ∈ s := by
  rw [Array.back?_eq_getElem?] at hb
  exact Array.mem_iff_getElem?.2 ⟨_, hb⟩

theorem mem_of_mem_pop {s : Array ID} {x : ID} (h : x ∈ s.pop) : x ∈ s := by
  obtain ⟨i, hi⟩ := Array.mem_iff_getElem?.1 h
  rw [Array.getElem?_pop] at hi
  split at hi
  · exact Array.mem_iff_getElem?.2 ⟨i, hi⟩
  · cases hi

theorem mem_pop_or {s : Array ID} {b x : ID} (hb : s.back? = some b) (hx : x ∈ s) :
    x ∈ s.pop ∨ x = b := by
  obtain ⟨i, hi⟩ := Array.mem_iff_getElem?.1 hx
  have hlt : i < s.size := by
    rw [Array.getElem?_eq_some_iff] at hi; exact hi.1
  by_cases h : i < s.size - 1
  · refine .inl (Array.mem_iff_getElem?.2 ⟨i, ?_⟩)
    rw [Array.getElem?_pop, ite_eq_left h]; exact hi
  · rw [Array.back?_eq_getElem?, show s.size - 1 = i by omega, hi] at hb
    exact .inr (Option.some.inj hb)

theorem mem_of_split {α : Type} {xs : Array α} {pre suff : List α} {e : α}
    (h : xs.toList = pre ++ e :: suff) : e ∈ xs := by
  rw [Array.mem_def, h]; simp

theorem range_length (m : Nat) : [:m].toList.length = m := by
  simp [Std.Legacy.Range.toList]

/-! ## Run successors -/

theorem mem_runSuccs {blk : Block} {e : Edge} (h : e ∈ runSuccs blk) :
    ∃ j : Nat, blk.succs[j]? = some e := by
  unfold runSuccs at h
  split at h
  · obtain ⟨i, hi⟩ := Array.mem_iff_getElem?.1 h
    rw [Array.getElem?_extract] at hi
    split at hi
    · exact ⟨0 + i, hi⟩
    · cases hi
  · exact Array.mem_iff_getElem?.1 h

theorem runSuccs_of {blk : Block} {k : Nat} {e : Edge} (h : blk.succs[k]? = some e)
    (hk : blk.kind = .First → k = 0) : e ∈ runSuccs blk := by
  unfold runSuccs
  split
  · next hf =>
    have hk0 : k = 0 := hk (by simpa using hf)
    subst hk0
    have hpos : 0 < blk.succs.size := by
      rw [Array.getElem?_eq_some_iff] at h; exact h.1
    refine Array.mem_iff_getElem?.2 ⟨0, ?_⟩
    rw [Array.getElem?_extract, ite_eq_left (by omega)]
    exact h
  · exact Array.mem_iff_getElem?.2 ⟨k, h⟩

section
variable {ce : CheckEnv} {f : Func}

theorem reach_succ_ok (hwf : WF ce f) (hbid : ∀ b ∈ f.blocks, b ≤ f.bidLast) {b0 : ID} {blk : Block}
    {e : Edge} (hb0 : b0 ∈ f.blocks) (hblk : f.block? b0 = some blk) (he : e ∈ runSuccs blk) :
    e.b ∈ f.blocks ∧ e.b < f.bidLast + 1 := by
  obtain ⟨j, hj⟩ := mem_runSuccs he
  have hm := (hwf.succLink b0 blk ⟨hb0, hblk⟩ j e hj).1
  exact ⟨hm, Nat.lt_succ_of_le (hbid _ hm)⟩

theorem Closed.mono {r r' : Array Bool} {b : ID} (h : Closed f r b)
    (hm : ∀ x, r.getD x false = true → r'.getD x false = true) : Closed f r' b :=
  fun blk hblk e he => hm _ (h blk hblk e he)

/-! ## Loop steps -/

theorem init_outer (hwf : WF ce f) (hbid : ∀ b ∈ f.blocks, b ≤ f.bidLast) :
    OInv f 0 ((Array.replicate (f.bidLast + 1) false).set! f.entry true) #[f.entry] := by
  have hsz : f.entry < (Array.replicate (f.bidLast + 1) false).size := by
    rw [Array.size_replicate]; exact Nat.lt_succ_of_le (hbid _ hwf.entry)
  have hr : ∀ x, ((Array.replicate (f.bidLast + 1) false).set! f.entry true).getD x false = true
      ↔ x = f.entry := by
    intro x; rw [getD_set hsz, getD_replicate]; simp
  have he := (hr f.entry).2 rfl
  exact {
    size := by rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, Array.size_replicate]
    entry := he
    listed := fun x hx => by rw [(hr x).1 hx]; exact hwf.entry
    stk := fun x hx => by
      rw [Array.mem_singleton] at hx; rw [hx]; exact he
    closed := fun x hx => .inl (by rw [(hr x).1 hx]; exact Array.mem_singleton.2 rfl)
    count := .inr (cnt_pos he) }

theorem init_inner {t : Nat} {r : Array Bool} {s : Array ID} {b0 : ID} (hI : OInv f t r s)
    (hb : s.back? = some b0) : IInv f t b0 [] r s.pop where
  size := hI.size
  entry := hI.entry
  listed := hI.listed
  stk x hx := hI.stk x (mem_of_mem_pop hx)
  home := hI.listed _ (hI.stk _ (mem_of_back? hb))
  closed x hx := by
    rcases hI.closed x hx with h | h
    · rcases mem_pop_or hb h with h | h
      · exact .inl h
      · exact .inr (.inr h)
    · exact .inr (.inl h)
  pre e he := by cases he
  count := by
    rcases hI.count with h | h
    · rw [Array.back?_eq_none_iff.2 h] at hb; cases hb
    · have := Array.size_pos_of_mem (mem_of_back? hb)
      rw [Array.size_pop]; omega

theorem mark_step (hwf : WF ce f) (hbid : ∀ b ∈ f.blocks, b ≤ f.bidLast) {t : Nat} {b0 : ID}
    {blk : Block} {pre : List Edge} {e : Edge} {r : Array Bool} {s : Array ID}
    (hblk : f.block? b0 = some blk) (he : e ∈ runSuccs blk) (hm : (!r.getD e.b true) = true)
    (hI : IInv f t b0 pre r s) :
    IInv f t b0 (pre ++ [e]) (r.set! e.b true) (s.push e.b) := by
  obtain ⟨hlist, hlt⟩ := reach_succ_ok hwf hbid hI.home hblk he
  have hlt' : e.b < r.size := hI.size ▸ hlt
  have hg := fun x => getD_set (x := x) hlt'
  have h0 : r.getD e.b true = false := by simpa using hm
  have mono : ∀ x, r.getD x false = true → (r.set! e.b true).getD x false = true :=
    fun x h => (hg x).2 (.inr h)
  exact {
    size := by rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact hI.size
    entry := mono _ hI.entry
    listed := fun x hx => by
      rcases (hg x).1 hx with rfl | h
      · exact hlist
      · exact hI.listed x h
    stk := fun x hx => by
      rcases Array.mem_push.1 hx with h | rfl
      · exact mono _ (hI.stk x h)
      · exact (hg _).2 (.inl rfl)
    home := hI.home
    closed := fun x hx => by
      rcases (hg x).1 hx with rfl | h
      · exact .inl (Array.mem_push.2 (.inr rfl))
      · rcases hI.closed x h with h | h | h
        · exact .inl (Array.mem_push.2 (.inl h))
        · exact .inr (.inl (h.mono mono))
        · exact .inr (.inr h)
    pre := fun x hx => by
      rcases List.mem_append.1 hx with h | h
      · exact mono _ (hI.pre x h)
      · rw [List.mem_singleton.1 h]; exact (hg _).2 (.inl rfl)
    count := by rw [cnt_set hlt' h0, Array.size_push]; have := hI.count; omega }

theorem skip_step (hwf : WF ce f) (hbid : ∀ b ∈ f.blocks, b ≤ f.bidLast) {t : Nat} {b0 : ID}
    {blk : Block} {pre : List Edge} {e : Edge} {r : Array Bool} {s : Array ID}
    (hblk : f.block? b0 = some blk) (he : e ∈ runSuccs blk) (hm : ¬(!r.getD e.b true) = true)
    (hI : IInv f t b0 pre r s) : IInv f t b0 (pre ++ [e]) r s := by
  obtain ⟨-, hlt⟩ := reach_succ_ok hwf hbid hI.home hblk he
  have hlt' : e.b < r.size := hI.size ▸ hlt
  have h1 : r.getD e.b false = true := by
    rw [getD_irrel hlt' false true]; simpa using hm
  exact { hI with
    pre := fun x hx => by
      rcases List.mem_append.1 hx with h | h
      · exact hI.pre x h
      · rw [List.mem_singleton.1 h]; exact h1 }

theorem done_inner {t t' : Nat} {b0 : ID} {blk : Block} {r : Array Bool} {s : Array ID}
    (hblk : f.block? b0 = some blk) (hI : IInv f t b0 (runSuccs blk).toList r s)
    (ht : t' = t + 1) : OInv f t' r s where
  size := hI.size
  entry := hI.entry
  listed := hI.listed
  stk := hI.stk
  closed x hx := by
    rcases hI.closed x hx with h | h | rfl
    · exact .inl h
    · exact .inr h
    · refine .inr fun blk' hblk' e he => ?_
      rw [hblk] at hblk'; cases hblk'
      exact hI.pre e (Array.mem_def.1 he)
  count := .inr (by have := hI.count; omega)

theorem some_block (hwf : WF ce f) {t : Nat} {r : Array Bool} {s : Array ID} {b0 : ID}
    (hI : OInv f t r s) (hb : s.back? = some b0) : ∃ blk, f.block? b0 = some blk :=
  let ⟨blk, h, _⟩ := hwf.blockId b0 (hI.listed _ (hI.stk _ (mem_of_back? hb)))
  ⟨blk, h⟩

theorem break_step {t t' : Nat} {r : Array Bool} {s : Array ID} (hI : OInv f t r s)
    (hs : s = #[]) : OInv f t' r s :=
  { hI with count := .inl hs }

/-! ## The loop -/

theorem reach_inv (hwf : WF ce f) (hbid : ∀ b ∈ f.blocks, b ≤ f.bidLast) :
    ∃ t s, OInv f t f.reachableBlocks s ∧ f.bidLast + 1 + 1 ≤ t := by
  generalize h : f.reachableBlocks = res
  unfold Func.reachableBlocks at h
  apply Id.of_wp_run_eq h
  mvcgen
  case inv2 =>
    rename_i pref _ _ _ _ _ _ b0 _ _ _ _ _
    exact ⇓⟨cur, st⟩ => ⌜IInv f pref.length b0 cur.prefix st.1 st.2⌝
  case inv1 => exact ⇓⟨cur, st⟩ => ⌜OInv f cur.prefix.length st.1 st.2⌝
  case vc1 =>
    rename_i b0 _ _ blk hblk _ _ _ _ hsplit _ _ _ hm hI
    exact mark_step hwf hbid hblk (mem_of_split (xs := runSuccs blk) hsplit) hm hI
  case vc2 =>
    rename_i b0 _ _ blk hblk _ _ _ _ hsplit _ _ _ hm hI
    exact skip_step hwf hbid hblk (mem_of_split (xs := runSuccs blk) hsplit) hm hI
  case vc3 =>
    rename_i _ _ _ _ _ _ _ _ hback _ _ _ hI
    exact init_inner hI hback
  case vc4 =>
    rename_i _ _ _ _ _ _ _ _ _ _ _ hblk _ _ hI
    exact done_inner hblk hI (by simp)
  case vc5 =>
    rename_i _ _ _ _ _ _ _ _ hback _ _ hnone heq hI
    obtain ⟨blk, hblk⟩ := some_block hwf hI hback
    exact (hnone blk (heq.symm.trans hblk)).elim
  case vc6 =>
    rename_i _ _ _ _ _ _ _ ob hnone heq hI
    refine break_step hI (Array.back?_eq_none_iff.1 ?_)
    rw [heq]
    rcases ob with _ | b
    · rfl
    · exact (hnone b rfl).elim
  case vc7 => exact init_outer hwf hbid
  case vc8 =>
    rename_i st hI
    exact ⟨_, _, hI, Nat.le_of_eq (range_length _).symm⟩

/-- Soundness of `reachableBlocks`: the entry is marked, marked blocks are listed, and the run
successors of marked blocks are marked. -/
theorem reachable_spec (hwf : WF ce f) (hbid : ∀ b ∈ f.blocks, b ≤ f.bidLast) :
    f.reachableBlocks.getD f.entry false = true ∧
    (∀ b, f.reachableBlocks.getD b false = true → b ∈ f.blocks) ∧
    (∀ b blk, f.reachableBlocks.getD b false = true → f.block? b = some blk →
      ∀ (k : Nat) (e : Edge), blk.succs[k]? = some e → (blk.kind = .First → k = 0) →
        f.reachableBlocks.getD e.b false = true) := by
  obtain ⟨t, s, hI, ht⟩ := reach_inv hwf hbid
  have hs : s = #[] := by
    rcases hI.count with h | h
    · exact h
    · have := cnt_le f.reachableBlocks
      rw [hI.size] at this; omega
  refine ⟨hI.entry, hI.listed, ?_⟩
  intro b blk hb hblk k e hk hfirst
  rcases hI.closed b hb with h | h
  · rw [hs] at h; cases h; contradiction
  · exact h blk hblk e (runSuccs_of hk hfirst)

end

end GoFV.Proof.Dead

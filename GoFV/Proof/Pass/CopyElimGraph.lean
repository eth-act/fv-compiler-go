import GoFV.Proof.Pass.CopyFrag

variable [GoFV.SSA.Sem.Addrs]

/-!
# Copy chains (`Src`) under copyelim's edits

`Src V x r n` is functional; its chain nodes `node V k x` are distinct, so a chain is shorter
than the value table. The edits of copyelim change `Src` in three ways: not at all (a non-copy
changes, `src_congr`), not as a relation (a copy is pointed further down its own chain,
`src_retarget`), or by linking a non-copy `v` to a non-copy `w` (`src_link`: chains ending in
`v` now end in `w`). `Join V a c`: `a` and `c` reach the same non-copy.
-/

namespace GoFV.Proof.CopyElim

open GoFV.SSA

variable {V V' : ID → Option Value}

/-- `a` and `c` lead to the same non-copy. -/
def Join (V : ID → Option Value) (a c : ID) : Prop := ∃ r n m, Src V a r n ∧ Src V c r m

theorem Src.end : ∀ {x r n}, Src V x r n → cstep V r = none
  | _, _, _, .sink h => h
  | _, _, _, .step _ h => h.end

theorem Src.unique : ∀ {x r r' n n'}, Src V x r n → Src V x r' n' → r = r' ∧ n = n'
  | _, _, _, _, _, .sink h, .sink _ => ⟨rfl, rfl⟩
  | _, _, _, _, _, .sink h, .step h' _ => by rw [h] at h'; cases h'
  | _, _, _, _, _, .step h' _, .sink h => by rw [h] at h'; cases h'
  | _, _, _, _, _, .step h1 s1, .step h2 s2 => by
    rw [h1] at h2; cases h2
    obtain ⟨rfl, rfl⟩ := s1.unique s2
    exact ⟨rfl, rfl⟩

theorem Src.of_sink {x r n} (hx : cstep V x = none) (h : Src V x r n) : r = x ∧ n = 0 :=
  (h.unique (.sink hx)).imp id id

theorem Src.self {r} (h : cstep V r = none) : Src V r r 0 := .sink h

theorem Join.of_src {a c r n m} (h1 : Src V a r n) (h2 : Src V c r m) : Join V a c :=
  ⟨r, n, m, h1, h2⟩

/-- `Join` with a non-copy is a chain to it. -/
theorem Join.sink {a w} (h : Join V a w) (hw : cstep V w = none) : ∃ n, Src V a w n := by
  obtain ⟨r, n, m, h1, h2⟩ := h
  obtain ⟨rfl, -⟩ := h2.of_sink hw
  exact ⟨n, h1⟩

/-- Moving along a chain keeps `Join`. -/
theorem Join.trans_src {a c w k} (h : Join V a c) (hc : Src V c w k) : Join V a w := by
  obtain ⟨r, n, m, h1, h2⟩ := h
  obtain ⟨rfl, -⟩ := h2.unique hc
  exact ⟨r, n, 0, h1, .self hc.end⟩

/-! ## Chain nodes -/

/-- The copy successor (`x` itself if there is none). -/
def nxt (V : ID → Option Value) (x : ID) : ID :=
  match cstep V x with
  | some (some y) => y
  | _ => x

/-- The `k`th node of `x`'s chain. -/
def node (V : ID → Option Value) : Nat → ID → ID
  | 0, x => x
  | k + 1, x => node V k (nxt V x)

theorem nxt_of {x y} (h : cstep V x = some (some y)) : nxt V x = y := by
  unfold nxt; rw [h]

theorem node_succ (k : Nat) : ∀ x, node V (k + 1) x = nxt V (node V k x) := by
  induction k with
  | zero => intro x; rfl
  | succ k ih => intro x; exact ih (nxt V x)

theorem Src.atNode : ∀ {x r n}, Src V x r n → ∀ k ≤ n, Src V (node V k x) r (n - k)
  | _, _, _, .sink h, k, hk => by cases Nat.le_zero.1 hk; exact .sink h
  | _, _, _, .step (y := y) (n := n) hxy hs, k, hk => by
    cases k with
    | zero => exact .step hxy hs
    | succ k =>
      show Src V (node V k (nxt V _)) _ _
      rw [nxt_of hxy, show n + 1 - (k + 1) = n - k by omega]
      exact hs.atNode k (by omega)

theorem Src.pt_last {x r n} (h : Src V x r n) : node V n x = r := by
  have := h.atNode n (Nat.le_refl _)
  rw [Nat.sub_self] at this
  cases this with
  | sink _ => rfl

theorem Src.pt_step {x r n} (h : Src V x r n) {k} (hk : k < n) :
    cstep V (node V k x) = some (some (node V (k + 1) x)) := by
  have := h.atNode k (Nat.le_of_lt hk)
  obtain ⟨m, hm⟩ : ∃ m, n - k = m + 1 := ⟨n - k - 1, by omega⟩
  rw [hm] at this
  cases this with
  | step hxy _ => rw [node_succ, nxt_of hxy]; exact hxy

/-- The nodes of a chain are distinct. -/
theorem Src.pt_inj {x r n} (h : Src V x r n) {i j} (hi : i ≤ n) (hj : j ≤ n)
    (he : node V i x = node V j x) : i = j := by
  have h1 := h.atNode i hi
  have h2 := h.atNode j hj
  rw [he] at h1
  have := (h1.unique h2).2
  omega

/-- A chain whose nodes are all in the value table is shorter than the table. -/
theorem Src.length_lt {N x r n} (h : Src V x r n) (hN : ∀ k ≤ n, node V k x < N) : n < N := by
  have hnd : ((List.range (n + 1)).map fun k => node V k x).Nodup := by
    refine List.pairwise_map.2 (List.nodup_range.imp_of_mem ?_)
    intro i j hi hj hne he
    exact hne (h.pt_inj (by simp at hi; omega) (by simp at hj; omega) he)
  have hsub : ((List.range (n + 1)).map fun k => node V k x) ⊆ List.range N := by
    intro y hy
    simp only [List.mem_map, List.mem_range] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    exact List.mem_range.2 (hN k (by omega))
  have := hnd.length_le_of_subset hsub
  simp at this
  omega

/-! ## Edits -/

theorem src_congr (h : ∀ x, cstep V' x = cstep V x) :
    ∀ {x r n}, Src V x r n → Src V' x r n
  | _, _, _, .sink hx => .sink (by rw [h]; exact hx)
  | _, _, _, .step hx hs => .step (by rw [h]; exact hx) (src_congr h hs)

/-- Pointing the copy `v` at the end `w` of its own chain changes no chain's end. -/
theorem src_retarget {v w : ID} {k : Nat} (hvw : Src V v w (k + 1))
    (h' : cstep V' v = some (some w)) (ho : ∀ x, x ≠ v → cstep V' x = cstep V x) {x r : ID} :
    (∃ n, Src V' x r n) ↔ (∃ n, Src V x r n) := by
  have hwv : w ≠ v := by
    rintro rfl
    have hend := hvw.end
    cases hvw with
    | step hx hs => rw [hend] at hx; cases hx
  have hw' : cstep V' w = none := by rw [ho w hwv]; exact hvw.end
  constructor
  · rintro ⟨n, hs⟩
    induction hs with
    | @sink x hx =>
      refine ⟨0, .sink ?_⟩
      by_cases hxv : x = v
      · subst hxv; rw [h'] at hx; cases hx
      · rw [← ho x hxv]; exact hx
    | @step x y r n hx hs ih =>
      by_cases hxv : x = v
      · subst hxv
        rw [h'] at hx; cases hx
        obtain ⟨rfl, -⟩ := hs.of_sink hw'
        exact ⟨_, hvw⟩
      · obtain ⟨m, hm⟩ := ih
        exact ⟨m + 1, .step (by rw [← ho x hxv]; exact hx) hm⟩
  · rintro ⟨n, hs⟩
    induction hs with
    | @sink x hx =>
      refine ⟨0, .sink ?_⟩
      by_cases hxv : x = v
      · subst hxv
        cases hvw with
        | step hy _ => rw [hx] at hy; cases hy
      · rw [ho x hxv]; exact hx
    | @step x y r n hx hs ih =>
      by_cases hxv : x = v
      · subst hxv
        obtain ⟨rfl, -⟩ := (Src.step hx hs).unique hvw
        exact ⟨1, .step h' (.sink hw')⟩
      · obtain ⟨m, hm⟩ := ih
        exact ⟨m + 1, .step (by rw [ho x hxv]; exact hx) hm⟩

theorem join_retarget {v w : ID} {k : Nat} (hvw : Src V v w (k + 1))
    (h' : cstep V' v = some (some w)) (ho : ∀ x, x ≠ v → cstep V' x = cstep V x) {a c : ID}
    (h : Join V a c) : Join V' a c := by
  obtain ⟨r, n, m, h1, h2⟩ := h
  obtain ⟨n', h1'⟩ := (src_retarget hvw h' ho).2 ⟨n, h1⟩
  obtain ⟨m', h2'⟩ := (src_retarget hvw h' ho).2 ⟨m, h2⟩
  exact ⟨r, n', m', h1', h2'⟩

/-- Linking the non-copy `v` to the non-copy `w`: chains ending in `v` now end in `w`. -/
theorem src_link {v w : ID} (hv : cstep V v = none) (hw : cstep V w = none) (hne : w ≠ v)
    (h' : cstep V' v = some (some w)) (ho : ∀ x, x ≠ v → cstep V' x = cstep V x) :
    ∀ {x r n}, Src V x r n → ∃ n', Src V' x (if r = v then w else r) n'
  | _, _, _, .sink (x := x) hx => by
    by_cases hxv : x = v
    · subst hxv
      rw [ite_eq_left (Eq.refl _)]
      exact ⟨1, .step h' (.sink (by rw [ho w hne]; exact hw))⟩
    · rw [ite_eq_right hxv]
      exact ⟨0, .sink (by rw [ho x hxv]; exact hx)⟩
  | _, _, _, .step (x := x) hx hs => by
    have hxv : x ≠ v := by rintro rfl; rw [hv] at hx; cases hx
    obtain ⟨n', h⟩ := src_link hv hw hne h' ho hs
    exact ⟨n' + 1, .step (by rw [ho x hxv]; exact hx) h⟩

theorem join_link {v w : ID} (hv : cstep V v = none) (hw : cstep V w = none) (hne : w ≠ v)
    (h' : cstep V' v = some (some w)) (ho : ∀ x, x ≠ v → cstep V' x = cstep V x) {a c : ID}
    (h : Join V a c) : Join V' a c := by
  obtain ⟨r, n, m, h1, h2⟩ := h
  obtain ⟨n', h1'⟩ := src_link hv hw hne h' ho h1
  obtain ⟨m', h2'⟩ := src_link hv hw hne h' ho h2
  exact ⟨_, n', m', h1', h2'⟩

end GoFV.Proof.CopyElim

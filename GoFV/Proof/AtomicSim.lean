import GoFV.Proof.Eval

/-!
# Atomic roots on related memories (`Sem/Atomic.lean`)

`atomicRoot_sim`: for any relation `R` on memories that keeps loads from and writes to the
blocks `G` alike (`AtomicSimRel`), an atomic root that returns on memory `M` returns on a related
memory `M'` with the same value and related memories, when its pointer arguments point into
`G`. dead auto elim (`Mem.EqOff`) and the extra-temporaries tables check (`EqX`) instantiate it.
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

/-- `R` relates memories that load alike from the blocks `G` and stay related under the same
write into `G`. -/
structure AtomicSimRel (R : Mem → Mem → Prop) (G : Blk → Prop) : Prop where
  load : ∀ {m m' : Mem} (t : Ty) (p : Ptr), R m m' → G p.blk → m'.load t p = m.load t p
  write : ∀ {m m' m1 : Mem} (p : Ptr) (bs : Array Byte), R m m' → G p.blk →
    m.write p bs = some m1 → ∃ m1', m'.write p bs = some m1' ∧ R m1 m1'

/-- The results of an atomic root on related memories: memories, or a value and memories. -/
def AtomicSame (R : Mem → Mem → Prop) (y y' : Val) : Prop :=
  ∃ m1 m1', R m1 m1' ∧
    ((y = .mem m1 ∧ y' = .mem m1') ∨ ∃ z, y = .tuple [z, .mem m1] ∧ y' = .tuple [z, .mem m1'])

theorem atomicResult_same {R : Mem → Mem → Prop} (r : Option Val) {m m' : Mem} (hm : R m m') :
    AtomicSame R (Atomic.result r m) (Atomic.result r m') := by
  cases r with
  | none => exact ⟨m, m', hm, .inl ⟨rfl, rfl⟩⟩
  | some z => exact ⟨m, m', hm, .inr ⟨z, rfl, rfl⟩⟩

variable {R : Mem → Mem → Prop} {G : Blk → Prop}

theorem atomicRmw_sim (hR : AtomicSimRel R G) {v : Value} {k : Atomic.Kind} {t : Ty} {p : Ptr}
    {x : Val} {m m' : Mem} {y : Val} (hp : G p.blk) (hm : R m m')
    (h : Atomic.rmw v k t p x m = .ok y) :
    ∃ y', Atomic.rmw v k t p x m' = .ok y' ∧ AtomicSame R y y' := by
  unfold Atomic.rmw at h ⊢
  rw [hR.load t p hm hp]
  by_cases ha : Atomic.aligned p t.size = true
  · simp only [ha, ↓reduceIte] at h ⊢
    cases hw : m.write p (encode t (Atomic.step k (Atomic.width t) (m.load t p) x).1) with
    | none => rw [hw] at h; cases h
    | some m1 =>
      rw [hw] at h
      cases h
      obtain ⟨m1', hw', hm1⟩ := hR.write p _ hm hp hw
      rw [hw']
      exact ⟨_, rfl, atomicResult_same _ hm1⟩
  · simp only [ha, Bool.false_eq_true, ↓reduceIte] at h; cases h

theorem atomicCas_sim (hR : AtomicSimRel R G) {v : Value} {w : Width} {p : Ptr} {o n : Val}
    {m m' : Mem} {y : Val} (hp : G p.blk) (hm : R m m') (h : Atomic.cas v w p o n m = .ok y) :
    ∃ y', Atomic.cas v w p o n m' = .ok y' ∧ AtomicSame R y y' := by
  unfold Atomic.cas at h ⊢
  rw [hR.load _ p hm hp]
  revert h
  generalize (m.load (.int w) p).asInt w = a
  generalize o.asInt w = b
  intro h
  by_cases ha : Atomic.aligned p w.bytes = true
  · simp only [ha, ↓reduceIte] at h ⊢
    cases a with
    | none => cases h
    | some cur =>
      cases b with
      | none => cases h
      | some old =>
        dsimp only at h ⊢
        by_cases he : cur = old
        · simp only [he, ↓reduceIte] at h ⊢
          cases hw : m.write p (encode (.int w) n) with
          | none => rw [hw] at h; cases h
          | some m1 =>
            rw [hw] at h
            cases h
            obtain ⟨m1', hw', hm1⟩ := hR.write p _ hm hp hw
            rw [hw']
            exact ⟨_, rfl, m1, m1', hm1, .inr ⟨_, rfl, rfl⟩⟩
        · simp only [he, ↓reduceIte] at h ⊢
          cases h
          exact ⟨_, rfl, m, m', hm, .inr ⟨_, rfl, rfl⟩⟩
  · simp only [ha, Bool.false_eq_true, ↓reduceIte] at h; cases h

/-- An atomic root returns only on a memory last argument. -/
theorem atomicRoot_ok_mem {v : Value} {L : List Val} {w y : Val}
    (h : atomicRoot v (L ++ [w]) = .ok y) : ∃ m, w = .mem m := by
  rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, L⟩⟩⟩⟩ <;>
    simp only [List.nil_append, List.cons_append, atomicRoot] at h
  · unfold Atomic.barrier at h; split at h
    · exact ⟨_, rfl⟩
    · cases h
  · unfold Atomic.prefetch at h; split at h
    · exact ⟨_, rfl⟩
    · cases h
  · unfold Atomic.rmwRoot at h; split at h
    · exact ⟨_, rfl⟩
    · cases h
  · unfold Atomic.casRoot at h; split at h
    · exact ⟨_, rfl⟩
    · cases h
  · rcases L with _ | ⟨e, L⟩ <;> cases h

/-- **An atomic root on related memories** returns alike when its pointer arguments point into
`G`. -/
theorem atomicRoot_sim (hR : AtomicSimRel R G) {v : Value} {L : List Val} {M M' : Mem} {y : Val}
    (hL : ∀ p, Val.ptr p ∈ L → G p.blk) (hm : R M M')
    (h : atomicRoot v (L ++ [.mem M]) = .ok y) :
    ∃ y', atomicRoot v (L ++ [.mem M']) = .ok y' ∧ AtomicSame R y y' := by
  rcases L with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, L⟩⟩⟩⟩ <;>
    simp only [List.nil_append, List.cons_append, atomicRoot] at h ⊢
  · unfold Atomic.barrier at h ⊢
    by_cases hp : v.op = .PubBarrier <;> simp only [hp, ↓reduceIte] at h ⊢
    · cases h; exact ⟨_, rfl, M, M', hm, .inl ⟨rfl, rfl⟩⟩
    · cases h
  · unfold Atomic.prefetch at h ⊢
    by_cases hp : v.op = .PrefetchCache ∨ v.op = .PrefetchCacheStreamed <;>
      simp only [hp, ↓reduceIte] at h ⊢
    · cases h; exact ⟨_, rfl, M, M', hm, .inl ⟨rfl, rfl⟩⟩
    · cases h
  · unfold Atomic.rmwRoot at h ⊢
    cases a with
    | ptr p =>
      dsimp only at h ⊢
      cases hi : Atomic.info? v.op with
      | none => simp only [hi, Atomic.unmodelled] at h; cases h
      | some kt =>
        obtain ⟨k, t⟩ := kt
        simp only [hi] at h ⊢
        exact atomicRmw_sim hR (hL p (by simp)) hm h
    | _ => simp only [Atomic.unmodelled] at h; cases h
  · unfold Atomic.casRoot at h ⊢
    cases a with
    | ptr p =>
      dsimp only at h ⊢
      cases hc : Atomic.casWidth? v.op with
      | none => simp only [hc, Atomic.unmodelled] at h; cases h
      | some cw =>
        simp only [hc] at h ⊢
        exact atomicCas_sim hR (hL p (by simp)) hm h
    | _ => simp only [Atomic.unmodelled] at h; cases h
  · rcases L with _ | ⟨e, L⟩ <;> cases h

/-- `atomicRoot` of an op it does not model is `stuck`. -/
theorem atomicRoot_unmodelled {v : Value} (h : Atomic.modelled v.op = false) (argv : List Val) :
    ∃ msg, atomicRoot v argv = .stuck msg := by
  simp only [Atomic.modelled, Bool.or_eq_false_iff, Option.isSome_eq_false_iff,
    Option.isNone_iff_eq_none, beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨hi, hc⟩, hb⟩, hp1⟩, hp2⟩ := h
  unfold atomicRoot Atomic.barrier Atomic.prefetch Atomic.rmwRoot Atomic.casRoot
  split
  · split <;> simp [hb, Atomic.unmodelled]
  · split <;> simp [hp1, hp2, Atomic.unmodelled]
  · split <;> simp [hi, Atomic.unmodelled]
  · split <;> simp [hc, Atomic.unmodelled]
  · simp [Atomic.unmodelled]

end GoFV.Proof

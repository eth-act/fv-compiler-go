import GoFV.Proof.Pass.MemCombineSplit
import GoFV.Proof.Pass.MemCombineBytes

/-!
# memcombine: descriptions as byte lists (issue #35)

`bytesOf w X`: the `w.bytes` little-endian bytes of an integer, determined by them
(`bytesOf_inj`). The integer ops `symOp` follows act on them as list operations: `|||` bytewise,
shifts by whole bytes as `replicate`/`take`/`drop`, `setWidth` as padding or `take`, `bswapNat`
as `reverse`, constants as `litBytes`, concrete memory bytes as `decodeInt`.

`semL V bs`: the bytes a description stands for (`SB.sem` of each, all defined), which commutes
with the same list operations (`semL_append`, `orBytes_sem`, …).
-/

namespace GoFV.Proof.MemCombine

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.MemCombine.Check

/-! ## Integers as byte lists -/

/-- The `w.bytes` little-endian bytes of `X`. -/
def bytesOf (w : Width) (X : BitVec w.bits) : List (BitVec 8) :=
  (List.range w.bytes).map (byteOf X.toNat)

@[simp] theorem bytesOf_length (w : Width) (X : BitVec w.bits) : (bytesOf w X).length = w.bytes := by
  simp [bytesOf]

theorem bytesOf_getElem {w : Width} {X : BitVec w.bits} {k : Nat} (h : k < (bytesOf w X).length) :
    (bytesOf w X)[k] = byteOf X.toNat k := by
  simp [bytesOf]

theorem bytesOf_inj {w : Width} {X Y : BitVec w.bits} (h : bytesOf w X = bytesOf w Y) : X = Y :=
  bitvec_eq_of_bytes fun k hk => by
    have h1 : k < (bytesOf w X).length := by simp [hk]
    have h2 : k < (bytesOf w Y).length := by simp [hk]
    rw [← bytesOf_getElem h1, ← bytesOf_getElem h2]
    simp only [h]

theorem bytes_pos (w : Width) : 0 < w.bytes := by cases w <;> decide

theorem bytes_le_eight (w : Width) : w.bytes ≤ 8 := by cases w <;> decide

theorem bits_le_of_bytes {w w' : Width} (h : w.bytes ≤ w'.bytes) : w.bits ≤ w'.bits := by
  have := width_bits_eq w; have := width_bits_eq w'; omega

theorem width_eq_of_bytes {w w' : Width} (h : w.bytes = w'.bytes) : w = w' := by
  cases w <;> cases w' <;> first | rfl | exact absurd h (by decide)

theorem bytesOf_or {w : Width} (X Y : BitVec w.bits) :
    bytesOf w (X ||| Y) = List.zipWith (· ||| ·) (bytesOf w X) (bytesOf w Y) := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  rw [List.getElem_zipWith, bytesOf_getElem, bytesOf_getElem, bytesOf_getElem]
  exact byteOf_or X Y k

theorem bytesOf_shl {w : Width} (X : BitVec w.bits) {j : Nat} (hj : j ≤ w.bytes) :
    bytesOf w (X <<< (8 * j)) = List.replicate j 0 ++ (bytesOf w X).take (w.bytes - j) := by
  have hb := width_bits_eq w
  apply List.ext_getElem (by simp; omega)
  intro k h1 h2
  simp only [bytesOf_length] at h1
  rw [bytesOf_getElem, byteOf_shl X j k (by omega) (by omega), List.getElem_append]
  by_cases hk : k < j
  · simp [hk]
  · simp only [hk, ↓reduceIte, List.length_replicate, dite_false, List.getElem_take]
    rw [bytesOf_getElem]

theorem bytesOf_ushr {w : Width} (X : BitVec w.bits) {j : Nat} (hj : j ≤ w.bytes) :
    bytesOf w (X >>> (8 * j)) = (bytesOf w X).drop j ++ List.replicate j 0 := by
  have hb := width_bits_eq w
  apply List.ext_getElem (by simp; omega)
  intro k h1 h2
  simp only [bytesOf_length] at h1
  rw [bytesOf_getElem, byteOf_ushr X j k (by omega), List.getElem_append]
  by_cases hk : k < w.bytes - j
  · simp only [List.length_drop, bytesOf_length, hk, dite_true, List.getElem_drop]
    rw [bytesOf_getElem, if_pos (by omega), Nat.add_comm]
  · simp only [List.length_drop, bytesOf_length, hk, dite_false, List.getElem_replicate]
    rw [if_neg (by omega)]

theorem bytesOf_zext {w w' : Width} (X : BitVec w.bits) (h : w.bytes ≤ w'.bytes) :
    bytesOf w' (X.setWidth w'.bits) =
      bytesOf w X ++ List.replicate (w'.bytes - w.bytes) 0 := by
  have hb := width_bits_eq w
  have hb' := width_bits_eq w'
  apply List.ext_getElem (by simp; omega)
  intro k h1 h2
  simp only [bytesOf_length] at h1
  rw [bytesOf_getElem, List.getElem_append]
  by_cases hk : k < w.bytes
  · simp only [bytesOf_length, hk, dite_true]
    rw [bytesOf_getElem, byteOf_setWidth X _ k (by omega)]
  · simp only [bytesOf_length, hk, dite_false, List.getElem_replicate]
    rw [byteOf_setWidth X _ k (by omega)]
    exact byteOf_high X k (by omega)

theorem bytesOf_trunc {w w' : Width} (X : BitVec w.bits) (h : w'.bytes ≤ w.bytes) :
    bytesOf w' (X.setWidth w'.bits) = (bytesOf w X).take w'.bytes := by
  have hb' := width_bits_eq w'
  apply List.ext_getElem (by simp; omega)
  intro k h1 h2
  simp only [bytesOf_length] at h1
  rw [bytesOf_getElem, List.getElem_take, bytesOf_getElem, byteOf_setWidth X _ k (by omega)]

theorem bytesOf_bswap {w : Width} (X : BitVec w.bits) :
    bytesOf w (BitVec.ofNat w.bits (Int.bswapNat (w.bits / 8) X.toNat)) = (bytesOf w X).reverse := by
  have hb := width_bits_eq w
  have h8 : w.bits / 8 = w.bytes := by omega
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [bytesOf_length] at h1
  rw [bytesOf_getElem, List.getElem_reverse, bytesOf_getElem, BitVec.toNat_ofNat, h8,
    byteOf_mod_two_pow (by omega), byteOf_bswapNat _ _ _ h1]
  simp only [bytesOf_length]

/-! ## Descriptions as byte lists -/

/-- The bytes a description stands for, if all are defined. -/
def semL (V : ID → Val) : List SB → Option (List (BitVec 8))
  | [] => some []
  | s :: l => (s.sem V).bind fun b => (semL V l).map (b :: ·)

@[simp] theorem semL_nil (V : ID → Val) : semL V [] = some [] := rfl

theorem semL_cons {V : ID → Val} {s : SB} {l : List SB} {C : List (BitVec 8)} :
    semL V (s :: l) = some C ↔ ∃ b L, s.sem V = some b ∧ semL V l = some L ∧ C = b :: L := by
  simp only [semL]
  cases hs : s.sem V with
  | none => simp
  | some b =>
    cases hl : semL V l with
    | none => simp
    | some L => simp [eq_comm]

theorem semL_length {V : ID → Val} : ∀ {l : List SB} {C : List (BitVec 8)}, semL V l = some C →
    C.length = l.length
  | [], C, h => by cases h; rfl
  | s :: l, C, h => by
    obtain ⟨b, L, -, hl, rfl⟩ := semL_cons.1 h
    simp [semL_length hl]

theorem semL_append {V : ID → Val} : ∀ {a b : List SB} {C : List (BitVec 8)},
    semL V (a ++ b) = some C ↔ ∃ A B, semL V a = some A ∧ semL V b = some B ∧ C = A ++ B
  | [], b, C => by simp
  | s :: a, b, C => by
    rw [List.cons_append, semL_cons]
    constructor
    · rintro ⟨x, L, hx, hl, rfl⟩
      obtain ⟨A, B, ha, hb, rfl⟩ := semL_append.1 hl
      exact ⟨x :: A, B, semL_cons.2 ⟨x, A, hx, ha, rfl⟩, hb, rfl⟩
    · rintro ⟨A, B, ha, hb, rfl⟩
      obtain ⟨x, A', hx, ha', rfl⟩ := semL_cons.1 ha
      exact ⟨x, A' ++ B, hx, semL_append.2 ⟨A', B, ha', hb, rfl⟩, rfl⟩

theorem semL_take_drop {V : ID → Val} : ∀ {l : List SB} {C : List (BitVec 8)} (k : Nat),
    semL V l = some C → semL V (l.take k) = some (C.take k) ∧ semL V (l.drop k) = some (C.drop k)
  | l, C, 0, h => by simp [h]
  | [], C, k + 1, h => by
    simp only [semL_nil, Option.some.injEq] at h; subst h; simp
  | s :: l, C, k + 1, h => by
    obtain ⟨x, L, hx, hl, rfl⟩ := semL_cons.1 h
    obtain ⟨h1, h2⟩ := semL_take_drop k hl
    exact ⟨semL_cons.2 ⟨x, _, hx, h1, rfl⟩, h2⟩

theorem semL_reverse {V : ID → Val} : ∀ {l : List SB} {C : List (BitVec 8)}, semL V l = some C →
    semL V l.reverse = some C.reverse
  | [], C, h => by cases h; rfl
  | s :: l, C, h => by
    obtain ⟨x, L, hx, hl, rfl⟩ := semL_cons.1 h
    rw [List.reverse_cons, List.reverse_cons]
    exact semL_append.2 ⟨_, _, semL_reverse hl, semL_cons.2 ⟨x, [], hx, rfl, rfl⟩, rfl⟩

theorem semL_zeros (V : ID → Val) : ∀ k, semL V (zeros k) = some (List.replicate k 0)
  | 0 => rfl
  | k + 1 => semL_cons.2 ⟨0, _, rfl, semL_zeros V k, rfl⟩

theorem semL_map_range {V : ID → Val} {n : Nat} (F : Nat → SB) (G : Nat → BitVec 8)
    (h : ∀ k < n, (F k).sem V = some (G k)) :
    semL V ((List.range n).map F) = some ((List.range n).map G) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_append]
    exact semL_append.2 ⟨_, _, ih fun k hk => h k (by omega),
      semL_cons.2 ⟨G n, [], h n (by omega), rfl, rfl⟩, rfl⟩

theorem semL_lits (V : ID → Val) (w : Width) (c : _root_.Int) :
    semL V (litBytes w.bytes c) = some (bytesOf w (BitVec.ofInt w.bits c)) := by
  unfold litBytes bytesOf
  exact semL_map_range _ _ fun k _ => by rw [byteOf_ofInt_eq]; rfl

/-- The bytes of a defined description determine it at each index. -/
theorem semL_getElem? {V : ID → Val} : ∀ {l : List SB} {C : List (BitVec 8)}, semL V l = some C →
    ∀ (k : Nat) (s : SB), l[k]? = some s → ∃ c, s.sem V = some c ∧ C[k]? = some c
  | [], _, _, _, _, h => by simp at h
  | s :: l, C, h, k, t, hk => by
    obtain ⟨x, L, hx, hl, rfl⟩ := semL_cons.1 h
    cases k with
    | zero => simp at hk; subst hk; exact ⟨x, hx, rfl⟩
    | succ k => exact semL_getElem? hl k t (by simpa using hk)

/-- A description whose bytes are each defined is defined. -/
theorem semL_of_forall {V : ID → Val} : ∀ {l : List SB}, (∀ s ∈ l, ∃ c, s.sem V = some c) →
    ∃ C, semL V l = some C
  | [], _ => ⟨[], rfl⟩
  | s :: l, h => by
    obtain ⟨x, hx⟩ := h s List.mem_cons_self
    obtain ⟨L, hl⟩ := semL_of_forall fun t ht => h t (List.mem_cons_of_mem _ ht)
    exact ⟨x :: L, semL_cons.2 ⟨x, L, hx, hl, rfl⟩⟩

/-- Defined bytes stay defined where the values they read are refined. -/
theorem sem_mono' {V V' : ID → Val} {s : SB} (h : ∀ y ∈ s.ids, Sem.Refines (V y) (V' y))
    {b : BitVec 8} (hs : s.sem V = some b) : s.sem V' = some b := by
  let V'' : ID → Val := fun y => if y ∈ s.ids then V' y else V y
  have h1 : ∀ y, Sem.Refines (V y) (V'' y) := fun y => by
    by_cases hy : y ∈ s.ids
    · simp only [V'', hy, ite_true]; exact h y hy
    · simp only [V'', hy, ite_false]; exact Sem.Refines.refl _
  have h2 := sem_mono h1 hs
  have h3 : s.sem V'' = s.sem V' := by
    cases s with
    | lit c => rfl
    | vb y k => simp [SB.sem, V'', SB.ids]
    | mb m b i o =>
      cases i <;> simp [SB.sem, V'', SB.ids, idxVal]
  rw [← h3]; exact h2

theorem semL_mono' {V V' : ID → Val} : ∀ {l : List SB},
    (∀ s ∈ l, ∀ y ∈ s.ids, Sem.Refines (V y) (V' y)) → ∀ {C : List (BitVec 8)},
    semL V l = some C → semL V' l = some C
  | [], _, _, h => h
  | s :: l, hr, C, h => by
    obtain ⟨x, L, hx, hl, rfl⟩ := semL_cons.1 h
    exact semL_cons.2 ⟨x, L, sem_mono' (hr s List.mem_cons_self) hx,
      semL_mono' (fun t ht => hr t (List.mem_cons_of_mem _ ht)) hl, rfl⟩

/-! ## `Or` of descriptions -/

theorem orSB_sem {V : ID → Val} {a b c : SB} (h : orSB a b = some c) {A B : BitVec 8}
    (ha : a.sem V = some A) (hb : b.sem V = some B) : c.sem V = some (A ||| B) := by
  unfold orSB at h
  split at h
  · cases h; cases ha; cases hb; rfl
  · split at h
    · cases h; rename_i hx; subst hx; cases ha; rw [hb]; simp
    · cases h
  · split at h
    · cases h; rename_i hy; subst hy; cases hb; rw [ha]; simp
    · cases h
  · cases h

theorem orSB_def {V : ID → Val} {a b c : SB} (h : orSB a b = some c) {C : BitVec 8}
    (hc : c.sem V = some C) : ∃ A B, a.sem V = some A ∧ b.sem V = some B := by
  unfold orSB at h
  split at h
  · exact ⟨_, _, rfl, rfl⟩
  · split at h
    · cases h; exact ⟨_, _, rfl, hc⟩
    · cases h
  · split at h
    · cases h; exact ⟨_, _, hc, rfl⟩
    · cases h
  · cases h

theorem orBytes_sem {V : ID → Val} : ∀ {a b c : List SB}, orBytes a b = some c →
    ∀ {A B : List (BitVec 8)}, semL V a = some A → semL V b = some B →
    semL V c = some (List.zipWith (· ||| ·) A B)
  | [], [], c, h, A, B, ha, hb => by
    cases h; cases ha; cases hb; rfl
  | x :: a, y :: b, c, h, A, B, ha, hb => by
    simp only [orBytes, bind, Option.bind] at h
    cases hxy : orSB x y with
    | none => rw [hxy] at h; cases h
    | some z =>
      rw [hxy] at h
      cases hab : orBytes a b with
      | none => rw [hab] at h; cases h
      | some cs =>
        rw [hab] at h
        cases h
        obtain ⟨X, A', hx, ha', rfl⟩ := semL_cons.1 ha
        obtain ⟨Y, B', hy, hb', rfl⟩ := semL_cons.1 hb
        exact semL_cons.2 ⟨_, _, orSB_sem hxy hx hy, orBytes_sem hab ha' hb', rfl⟩
  | [], _ :: _, c, h, _, _, _, _ => by cases h
  | _ :: _, [], c, h, _, _, _, _ => by cases h

theorem orBytes_def {V : ID → Val} : ∀ {a b c : List SB}, orBytes a b = some c →
    ∀ {C : List (BitVec 8)}, semL V c = some C → ∃ A B, semL V a = some A ∧ semL V b = some B
  | [], [], c, h, C, hc => ⟨[], [], rfl, rfl⟩
  | x :: a, y :: b, c, h, C, hc => by
    simp only [orBytes, bind, Option.bind] at h
    cases hxy : orSB x y with
    | none => rw [hxy] at h; cases h
    | some z =>
      rw [hxy] at h
      cases hab : orBytes a b with
      | none => rw [hab] at h; cases h
      | some cs =>
        rw [hab] at h
        cases h
        obtain ⟨Z, L, hz, hl, rfl⟩ := semL_cons.1 hc
        obtain ⟨X, Y, hx, hy⟩ := orSB_def hxy hz
        obtain ⟨A, B, ha, hb⟩ := orBytes_def hab hl
        exact ⟨X :: A, Y :: B, semL_cons.2 ⟨X, A, hx, ha, rfl⟩, semL_cons.2 ⟨Y, B, hy, hb, rfl⟩⟩
  | [], _ :: _, c, h, _, _ => by cases h
  | _ :: _, [], c, h, _, _ => by cases h

theorem orBytes_ids : ∀ {a b c : List SB}, orBytes a b = some c →
    ∀ s ∈ c, s ∈ a ∨ s ∈ b ∨ ∃ x, s = .lit x
  | [], [], c, h => by cases h; simp
  | x :: a, y :: b, c, h => by
    simp only [orBytes, bind, Option.bind] at h
    cases hxy : orSB x y with
    | none => rw [hxy] at h; cases h
    | some z =>
      rw [hxy] at h
      cases hab : orBytes a b with
      | none => rw [hab] at h; cases h
      | some cs =>
        rw [hab] at h
        cases h
        intro s hs
        rcases List.mem_cons.1 hs with rfl | hs
        · unfold orSB at hxy
          split at hxy
          · cases hxy; exact .inr (.inr ⟨_, rfl⟩)
          · split at hxy
            · cases hxy; exact .inr (.inl List.mem_cons_self)
            · cases hxy
          · split at hxy
            · cases hxy; exact .inl List.mem_cons_self
            · cases hxy
          · cases hxy
        · rcases orBytes_ids hab s hs with h | h | h
          · exact .inl (List.mem_cons_of_mem _ h)
          · exact .inr (.inl (List.mem_cons_of_mem _ h))
          · exact .inr (.inr h)
  | [], _ :: _, c, h => by cases h
  | _ :: _, [], c, h => by cases h

end GoFV.Proof.MemCombine

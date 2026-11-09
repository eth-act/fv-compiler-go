import GoFV.Proof.Pass.MemCombineBytes
import GoFV.Proof.ABIBytes
import GoFV.Proof.ValRefine

variable [GoFV.SSA.Sem.Addrs]

/-!
# Struct-store splits: memory (issue #151)

A `Store {agg fs n} p (StructMake …)` writes `encode (agg fs n) (agg vs)`: the fields' bytes put
one after the other into `n` `poison` bytes (`encodeFields`). The split writes each field's bytes
at `p + oᵢ`, first to last, into the memory as it is. `split_mem`: if the struct write succeeds on
`M` and `M'` refines `M`, the field writes (of values refining the fields') succeed on `M'` and
their result refines the struct write's (the padding is `poison` in the source).

The steps: a write of `poison` bytes is refined by the memory before it (`write_poison_left`); a
write at `p + o` of bytes inside a written buffer is the write of the buffer with them put in
(`write_putBytes`); and the refinement of writes (`Mem.Refines.write`).
-/

namespace GoFV.Proof.StructStore

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof.MemCombine GoFV.Proof.DSE GoFV.Proof.ABI GoFV.Proof.CSE.Mem

/-- A write succeeds alike for every byte array of the same size. -/
theorem write_size_congr {m m1 : Mem} {p : Ptr} {bs bs' : Array Byte} (hw : m.write p bs = some m1)
    (hs : bs'.size = bs.size) : ∃ m2, m.write p bs' = some m2 := by
  by_cases h0 : bs.size = 0
  · refine ⟨m, ?_⟩
    have he : bs'.isEmpty = true := Array.isEmpty_iff_size_eq_zero.2 (by omega)
    unfold Mem.write
    simp only [he, ite_true]; rfl
  · obtain ⟨a, ha⟩ := write_find hw (by omega)
    obtain ⟨-, hv⟩ := write_spec ha hw
    obtain ⟨h1, h2, h3, h4⟩ := hv (by omega)
    exact ⟨_, write_of_valid ha (by omega) h1 (by omega) (by omega) (by rw [hs]; exact h4)⟩

theorem putBytes_getElem? {d src : Array Byte} {off : Nat} (h : off + src.size ≤ d.size) (j : Nat) :
    (putBytes d off src)[j]? = if off ≤ j ∧ j < off + src.size then src[j - off]? else d[j]? := by
  split
  · rename_i hj
    have := putBytes_agree h (j - off) (by omega)
    rw [show off + (j - off) = j by omega, Nat.zero_add] at this
    exact this
  · rename_i hj
    exact putBytes_getElem?_out (by omega)

theorem putBytes_empty (d : Array Byte) (off : Nat) {src : Array Byte} (h : src.size = 0) :
    putBytes d off src = d := by
  unfold putBytes; rw [h]; rfl

/-- **A write inside a written buffer** is the write of the buffer with the bytes put in. -/
theorem write_putBytes {m m1 : Mem} {p : Ptr} {buf E : Array Byte} {o : Nat}
    (hw : m.write p buf = some m1) (ho : o + E.size ≤ buf.size) :
    ∃ m2, m1.write (p.add (BitVec.ofNat 64 o)) E = some m2 ∧
      m.write p (putBytes buf o E) = some m2 := by
  by_cases hE : E.size = 0
  · refine ⟨m1, ?_, by rw [putBytes_empty _ _ hE]; exact hw⟩
    have he : E.isEmpty = true := Array.isEmpty_iff_size_eq_zero.2 hE
    unfold Mem.write
    simp only [he, ite_true]; rfl
  obtain ⟨a, ha⟩ := write_find hw (by omega)
  obtain ⟨rfl, hv⟩ := write_spec ha hw
  obtain ⟨hwr, h2, h3, h4⟩ := hv (by omega)
  have hps : (putBytes buf o E).size = buf.size := putBytes_size _ _ _
  have hoff : (p.add (BitVec.ofNat 64 o)).off.toNat = p.off.toNat + o := by
    rw [Ptr.add_off, toNat_add_ofNat, Nat.mod_eq_of_lt (by omega)]
  generalize hD1 : (List.range buf.size).foldl (fun d i => d.set! (p.off.toNat + i) buf[i]!) a.data
    = D1
  have hD1s : D1.size = a.data.size := by rw [← hD1, foldl_set_size]
  have hf1 : (m.set p.blk { a with data := D1 }).find? (p.add (BitVec.ofNat 64 o)).blk =
      some { a with data := D1 } := by
    rw [Ptr.add_blk, find?_set, ite_eq_left rfl]
  refine ⟨_, write_of_valid hf1 (by omega) hwr (by rw [hoff, hD1s]; omega) (by rw [hoff]; omega)
    (by rw [Ptr.add_blk, hoff]; exact endsInWindow_mono h4 (by omega)), ?_⟩
  rw [write_of_valid ha (by omega) hwr (by rw [hps]; omega) (by rw [hps]; omega)
    (by rw [hps]; exact h4), Ptr.add_blk, set_set]
  refine congrArg (fun d => some (m.set p.blk { a with data := d })) ?_
  apply Array.ext_getElem?
  intro j
  rw [foldl_set_getElem? _ _ _ _ (Nat.le_refl _) (by rw [hps]; omega),
    foldl_set_getElem? _ _ _ _ (Nat.le_refl _) (by rw [hoff, hD1s]; omega), hoff, ← hD1,
    foldl_set_getElem? _ _ _ _ (Nat.le_refl _) (by omega), hps]
  by_cases hj : p.off.toNat ≤ j ∧ j < p.off.toNat + buf.size
  · rw [ite_eq_left hj, putBytes_getElem? ho]
    by_cases hj' : p.off.toNat + o ≤ j ∧ j < p.off.toNat + o + E.size
    · rw [ite_eq_left hj', ite_eq_left ⟨by omega, by omega⟩]; congr 1; omega
    · rw [ite_eq_right hj', ite_eq_right (by omega), ite_eq_left hj]
  · rw [ite_eq_right hj, ite_eq_right (by omega), ite_eq_right hj]

theorem foldl_set_self (off e : Nat) (d : Array Byte) (he : e ≤ d.size) :
    ∀ (l : List Nat), (∀ i ∈ l, off + i < e) →
      l.foldl (fun d' i => d'.set! (off + i) (d.extract off e)[i]!) d = d
  | [], _ => rfl
  | i :: l, h => by
    rw [List.foldl_cons]
    have hi := h i List.mem_cons_self
    have : d.set! (off + i) (d.extract off e)[i]! = d := by
      apply Array.ext_getElem?
      intro j
      simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
      split
      · rename_i hj
        subst hj
        rw [Array.getElem?_eq_getElem (by omega), getElem!_pos _ i (by simp; omega),
          Array.getElem_extract]
        simp [show off + i < d.size by omega]
      · rfl
    rw [this]
    exact foldl_set_self off e d he l fun i hi => h i (List.mem_cons_of_mem _ hi)

/-- **A write of `poison` bytes** is refined by the memory before it. -/
theorem write_poison_left {m m' m1 : Mem} (h : Mem.Refines m m') {p : Ptr} {n : Nat}
    (hw : m.write p (Array.replicate n .poison) = some m1) : Mem.Refines m1 m' := by
  by_cases hn : n = 0
  · subst hn
    unfold Mem.write at hw; simp at hw; subst hw; exact h
  obtain ⟨a, ha⟩ := write_find hw (by simp; omega)
  obtain ⟨rfl, hv⟩ := write_spec ha hw
  obtain ⟨-, h2, -, -⟩ := hv (by simp; omega)
  simp only [Array.size_replicate] at h2
  obtain ⟨a', ha', har⟩ := h.find?_some ha
  have hsz := har.size_eq
  conv => rhs; rw [← set_self ha']
  refine h.set _ ⟨har.writable, ?_⟩
  have hfold := Mem.Refines.write_fold p.off.toNat
    (bs := Array.replicate n .poison) (bs' := a'.data.extract p.off.toNat (p.off.toNat + n))
    (BytesRefineA.replicate_poison n (by simp; omega)) (List.range n) har.data
  simp only [Array.size_replicate] at hfold ⊢
  rwa [foldl_set_self _ _ _ (by omega) _ fun i hi => by have := List.mem_range.1 hi; omega]
    at hfold

/-- The field writes of a split: the bytes of each value at its offset from `p`, in order. -/
def fieldWrites (p : Ptr) (m : Mem) : List ((Nat × Ty) × Val) → Option Mem
  | [] => some m
  | ((o, t), v) :: ws =>
    match m.write (p.add (BitVec.ofNat 64 o)) (encode t v) with
    | some m' => fieldWrites p m' ws
    | none => none

theorem fieldWrites_aux {M : Mem} {P : Ptr} {n : Nat} :
    ∀ (fs : List (Nat × Ty)) (vs vs' : List Val) (buf : Array Byte) (MB M' : Mem),
      (∀ f ∈ fs, f.1 + f.2.size ≤ n) → buf.size = n → RefinesList vs vs' →
      vs.length = fs.length → M.write P buf = some MB → Mem.Refines MB M' →
      ∃ MS MT, M.write P (encodeFields buf fs vs) = some MS ∧
        fieldWrites P M' (fs.zip vs') = some MT ∧ Mem.Refines MS MT
  | [], _, vs', buf, MB, M', _, _, _, _, hw, hr => by
    refine ⟨MB, M', hw, ?_, hr⟩
    simp [fieldWrites]
  | (o, t) :: fs, vs, vs', buf, MB, M', hin, hb, hv, hl, hw, hr => by
    cases hv with
    | nil => cases hl
    | cons hx hv' =>
      rename_i x x' xs xs'
      have ho : o + (encode t x).size ≤ buf.size := by
        rw [Sem.encode_size, hb]; exact hin _ List.mem_cons_self
      obtain ⟨MB', hw1, hw2⟩ := write_putBytes hw ho
      obtain ⟨MT1, hwT, hrT⟩ := hr.write (encode_mono t hx) hw1
      obtain ⟨MS, MT, h1, h2, h3⟩ := fieldWrites_aux fs xs xs' _ MB' MT1
        (fun f hf => hin f (List.mem_cons_of_mem _ hf)) (by rw [putBytes_size, hb]) hv'
        (by simpa using hl) hw2 hrT
      refine ⟨MS, MT, by simpa [encodeFields] using h1, ?_, h3⟩
      simp only [List.zip_cons_cons, fieldWrites, hwT]
      exact h2

/-- **The split's memory.** If the struct write of `agg vs` at `P` succeeds on `M` (every field
inside the `n` bytes) and `M'` refines `M`, the field writes of values `vs'` refining `vs` succeed
on `M'` and refine it. -/
theorem split_mem {M M' MS : Mem} {P : Ptr} {fs : List (Nat × Ty)} {n : Nat} {vs vs' : List Val}
    (hin : ∀ f ∈ fs, f.1 + f.2.size ≤ n) (hl : vs.length = fs.length) (hv : RefinesList vs vs')
    (hM : Mem.Refines M M') (hw : M.write P (encode (.agg fs n) (.agg vs)) = some MS) :
    ∃ MT, fieldWrites P M' (fs.zip vs') = some MT ∧ Mem.Refines MS MT := by
  have hw' : M.write P (encodeFields (Array.replicate n .poison) fs vs) = some MS := by
    simpa [encode] using hw
  obtain ⟨MB, hMB⟩ := write_size_congr hw' (bs' := Array.replicate n .poison)
    (by rw [Sem.encodeFields_size])
  obtain ⟨MS', MT, h1, h2, h3⟩ := fieldWrites_aux fs vs vs' _ MB M' hin (by simp) hv hl hMB
    (write_poison_left hM hMB)
  rw [hw'] at h1; cases h1
  exact ⟨MT, h2, h3⟩

/-- A pointer moved inside the bytes of a successful write stays inside its block's window. -/
theorem inWindow_of_write {M M1 : Mem} {P : Ptr} {bs : Array Byte} (hw : M.write P bs = some M1)
    {o : Nat} (ho : o < bs.size) : (P.add (BitVec.ofNat 64 o)).inWindow = true := by
  obtain ⟨a, ha⟩ := write_find hw (by omega)
  obtain ⟨-, hv⟩ := write_spec ha hw
  obtain ⟨-, -, h3, h4⟩ := hv (by omega)
  have hoff : (P.add (BitVec.ofNat 64 o)).off.toNat = P.off.toNat + o := by
    rw [Ptr.add_off, toNat_add_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold Ptr.inWindow
  rw [Ptr.add_blk, hoff]
  unfold Blk.endsInWindow at h4
  cases hw' : P.blk.window? with
  | none => rfl
  | some w => rw [hw'] at h4; simp only [decide_eq_true_eq] at h4 ⊢; omega

/-- The fields written one more. -/
theorem encodeFields_take_succ : ∀ (k : Nat) (buf : Array Byte) (fs : List (Nat × Ty))
    (vs : List Val) (o : Nat) (t : Ty) (v : Val), fs[k]? = some (o, t) → vs[k]? = some v →
    encodeFields buf (fs.take (k + 1)) (vs.take (k + 1)) =
      putBytes (encodeFields buf (fs.take k) (vs.take k)) o (encode t v)
  | 0, buf, (o', t') :: fs, v' :: vs, o, t, v, hf, hv => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hf hv
    obtain ⟨rfl, rfl⟩ := hf; subst hv
    simp [encodeFields]
  | k + 1, buf, (o', t') :: fs, v' :: vs, o, t, v, hf, hv => by
    simp only [List.take_succ_cons, encodeFields]
    exact encodeFields_take_succ k _ fs vs o t v (by simpa using hf) (by simpa using hv)
  | _, _, [], _, _, _, _, hf, _ => by simp at hf
  | _, _, _ :: _, [], _, _, _, _, hv => by simp at hv

end GoFV.Proof.StructStore

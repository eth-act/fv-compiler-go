import GoFV.Proof.MemRefine
import GoFV.SSA.Sem.Layout

/-!
# Encoding, decoding and retyping are monotone in refinement

`decode` of refined bytes refines (`decode_mono`), `encode` of a refined value gives refined
bytes (`encode_mono`), `Mem.load` of a refined memory refines (`load_mono`), `Val.retype`
preserves refinement (`retype_mono`). A poison-free value is only refined by itself up to
memories (`Refines.noPoison`).
-/

namespace GoFV.SSA.Sem

open GoFV.SSA

/-! ## Bytes without poison -/

/-- A byte list that contains a poison byte. -/
def HasPoisonByte (bs : Array Byte) : Prop := ∃ b ∈ bs.toList, b = .poison

theorem bytesRefine_eq_or_poison {bs bs' : Array Byte} (h : BytesRefineA bs bs') :
    bs = bs' ∨ HasPoisonByte bs := by
  by_cases hp : ∀ x ∈ bs.toList, x ≠ .poison
  · exact .inl (h.eq hp)
  · obtain ⟨x, hx⟩ := Classical.not_forall.1 hp
    by_cases h1 : x ∈ bs.toList
    · exact .inr ⟨x, h1, Classical.byContradiction fun h2 => hx fun _ => h2⟩
    · exact absurd (fun h => absurd h h1) hx

theorem bytesNat?_list : ∀ (l : List Byte), (∃ b ∈ l, b = .poison) →
    l.foldr (fun b acc => match b, acc with
      | .b x, some n => some (x.toNat + 256 * n)
      | _, _ => none) (some 0) = none
  | [], ⟨_, h, _⟩ => absurd h List.not_mem_nil
  | b :: l, ⟨c, hc, hcp⟩ => by
    rcases List.mem_cons.1 hc with rfl | hc
    · subst hcp; simp
    · rw [List.foldr_cons, bytesNat?_list l ⟨c, hc, hcp⟩]
      cases b <;> rfl

theorem bytesNat?_poison {bs : Array Byte} (h : HasPoisonByte bs) : bytesNat? bs = none := by
  unfold bytesNat?
  rw [← Array.foldr_toList]
  exact bytesNat?_list _ h

theorem bytesPtr?_poison {bs : Array Byte} (h : HasPoisonByte bs) : bytesPtr? bs = none := by
  obtain ⟨b, hb, rfl⟩ := h
  obtain ⟨j, hj, hjb⟩ := List.getElem_of_mem hb
  unfold bytesPtr?
  split
  · next p h0 =>
    split
    · next hall =>
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hall
      have hj8 : j < 8 := by simpa [hall.1] using hj
      have := hall.2 j hj8
      simp only [Array.length_toList] at hj
      rw [Array.getElem?_eq_getElem hj] at this
      simp only [Array.getElem_toList] at hjb
      rw [hjb] at this
      simp at this
    · rfl
  · rfl

theorem decodeInt_poison {w : Width} {bs : Array Byte} (h : HasPoisonByte bs) :
    decodeInt w bs = .poison := by
  unfold decodeInt
  rw [bytesNat?_poison h, bytesPtr?_poison h]
  cases w <;> rfl

theorem decodePtr_poison {bs : Array Byte} (h : HasPoisonByte bs) : decodePtr bs = .poison := by
  unfold decodePtr
  rw [bytesPtr?_poison h, bytesNat?_poison h]

/-! ## Decoding -/

mutual
theorem decode_mono {bs bs' : Array Byte} (h : BytesRefineA bs bs') (off : Nat) :
    (t : Ty) → Refines (decode bs off t) (decode bs' off t)
  | .int w => by
    simp only [decode]
    rcases bytesRefine_eq_or_poison (h.extract off (off + w.bytes)) with he | hp
    · rw [he]; exact Refines.refl _
    · rw [decodeInt_poison hp]; exact .poison _
  | .bool => by
    simp only [decode]
    rcases h.getElem? off with ⟨h1, h2⟩ | ⟨x, y, h1, h2, hxy⟩
    · rw [h1, h2]; exact .poison _
    · rw [h1, h2]
      cases hxy with
      | poison => exact .poison _
      | refl => exact Refines.refl _
  | .ptr _ => by
    simp only [decode]
    rcases bytesRefine_eq_or_poison (h.extract off (off + 8)) with he | hp
    · rw [he]; exact Refines.refl _
    · rw [decodePtr_poison hp]; exact .poison _
  | .agg fs _ => by
    simp only [decode]
    exact .agg (decodeFields_mono h off fs)
  | .blob n => by
    simp only [decode]
    exact .blob (h.extract off (off + n))
  | .empty => by simp only [decode]; exact .empty
  | .opaque _ => by simp only [decode]; exact .poison _
  | .other => by simp only [decode]; exact .poison _
  | .mem => by simp only [decode]; exact .poison _
  | .tuple _ => by simp only [decode]; exact .poison _
theorem decodeFields_mono {bs bs' : Array Byte} (h : BytesRefineA bs bs') (off : Nat) :
    (fs : List (Nat × Ty)) → RefinesList (decodeFields bs off fs) (decodeFields bs' off fs)
  | [] => by simp only [decodeFields]; exact .nil
  | (o, t) :: fs => by
    simp only [decodeFields]
    exact .cons (decode_mono h (off + o) t) (decodeFields_mono h off fs)
end

/-! ## Encoding -/

theorem putBytes_mono {d d' src src' : Array Byte} (hd : BytesRefineA d d')
    (hs : BytesRefineA src src') (off : Nat) :
    BytesRefineA (putBytes d off src) (putBytes d' off src') := by
  unfold putBytes
  rw [← hs.size_eq]
  generalize List.range src.size = l
  induction l generalizing d d' with
  | nil => exact hd
  | cons i l ih =>
    simp only [List.foldl_cons]
    apply ih
    rw [← hd.size_eq]
    split
    · exact hd.set! _ (hs.getElem! i)
    · exact hd

theorem putBytes_size (d : Array Byte) (off : Nat) (src : Array Byte) :
    (putBytes d off src).size = d.size := by
  unfold putBytes
  generalize List.range src.size = l
  induction l generalizing d with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldl_cons]
    rw [ih]
    split <;> simp

theorem encode_blob (t : Ty) (bs : List Byte) :
    encode t (.blob bs) = if bs.length == t.size then bs.toArray else Array.replicate t.size .poison := by
  cases t with
  | int w => cases w <;> simp [encode]
  | _ => simp [encode]

theorem encode_poison (t : Ty) : encode t .poison = Array.replicate t.size .poison := by
  cases t with
  | int w => cases w <;> simp [encode]
  | _ => simp [encode]

theorem encode_mem (t : Ty) (m : Mem) : encode t (.mem m) = Array.replicate t.size .poison := by
  cases t with
  | int w => cases w <;> simp [encode]
  | _ => simp [encode]

theorem encode_tuple (t : Ty) (vs : List Val) :
    encode t (.tuple vs) = Array.replicate t.size .poison := by
  cases t with
  | int w => cases w <;> simp [encode]
  | _ => simp [encode]

mutual
theorem encode_size : (t : Ty) → (v : Val) → (encode t v).size = t.size
  | .int w, .int w' x => by
    simp only [encode]; split <;> simp [intBytes, Ty.size]
  | .agg fs n, .agg vs => by
    simp only [encode, Ty.size]; rw [encodeFields_size]; simp
  | t, .blob bs => by rw [encode_blob]; split <;> simp_all
  | t, .poison => by rw [encode_poison]; simp
  | t, .mem m => by rw [encode_mem]; simp
  | t, .tuple vs => by rw [encode_tuple]; simp
  | .int w, .bool _ | .int w, .agg _ | .int w, .empty => by cases w <;> simp [encode]
  | .int w, .ptr p => by cases w <;> simp [encode, ptrBytes, Ty.size, Width.bytes, Width.bits]
  | .bool, .bool _ => by simp [encode, Ty.size]
  | .ptr _, .ptr _ => by simp [encode, ptrBytes, Ty.size]
  | .ptr _, .int w x => by cases w <;> simp [encode, intBytes, Ty.size]
  | .bool, .int _ _ | .bool, .ptr _ | .bool, .agg _ | .bool, .empty
  | .ptr _, .bool _ | .ptr _, .agg _ | .ptr _, .empty
  | .agg _ _, .int _ _ | .agg _ _, .bool _ | .agg _ _, .ptr _ | .agg _ _, .empty
  | .mem, .int _ _ | .mem, .bool _ | .mem, .ptr _ | .mem, .agg _ | .mem, .empty
  | .tuple _, .int _ _ | .tuple _, .bool _ | .tuple _, .ptr _ | .tuple _, .agg _
  | .tuple _, .empty
  | .other, .int _ _ | .other, .bool _ | .other, .ptr _ | .other, .agg _ | .other, .empty
  | .blob _, .int _ _ | .blob _, .bool _ | .blob _, .ptr _ | .blob _, .agg _ | .blob _, .empty
  | .empty, .int _ _ | .empty, .bool _ | .empty, .ptr _ | .empty, .agg _ | .empty, .empty
  | .opaque _, .int _ _ | .opaque _, .bool _ | .opaque _, .ptr _ | .opaque _, .agg _
  | .opaque _, .empty => by simp [encode]
theorem encodeFields_size (buf : Array Byte) :
    (fs : List (Nat × Ty)) → (vs : List Val) → (encodeFields buf fs vs).size = buf.size
  | (o, t) :: fs, v :: vs => by
    simp only [encodeFields]; rw [encodeFields_size, putBytes_size]
  | [], _ => by simp [encodeFields]
  | _ :: _, [] => by simp [encodeFields]
end

mutual
theorem encode_mono (t : Ty) : {v v' : Val} → Refines v v' → BytesRefineA (encode t v) (encode t v')
  | _, v', .poison _ => by
    rw [encode_poison]; exact BytesRefineA.replicate_poison _ (encode_size t v')
  | _, _, .int _ _ => BytesRefineA.refl _
  | _, _, .bool _ => BytesRefineA.refl _
  | _, _, .ptr _ => BytesRefineA.refl _
  | _, _, .empty => BytesRefineA.refl _
  | _, _, .mem _ => by rw [encode_mem, encode_mem]; exact BytesRefineA.refl _
  | _, _, .tuple _ => by rw [encode_tuple, encode_tuple]; exact BytesRefineA.refl _
  | _, _, .blob h => by
    rw [encode_blob, encode_blob, ← h.length_eq]
    split
    · simpa [BytesRefineA] using h
    · exact BytesRefineA.refl _
  | _, _, .agg h => by
    cases t with
    | agg fs n =>
      simp only [encode]
      exact encodeFields_mono (BytesRefineA.refl _) fs h
    | int w => cases w <;> simp only [encode] <;> exact BytesRefineA.refl _
    | _ => simp only [encode]; exact BytesRefineA.refl _
theorem encodeFields_mono {buf buf' : Array Byte} (hb : BytesRefineA buf buf') :
    (fs : List (Nat × Ty)) → {vs vs' : List Val} → RefinesList vs vs' →
      BytesRefineA (encodeFields buf fs vs) (encodeFields buf' fs vs')
  | (o, t) :: fs, _, _, .cons h t' => by
    simp only [encodeFields]
    exact encodeFields_mono (putBytes_mono hb (encode_mono t h) o) fs t'
  | [], _, _, _ => by simp only [encodeFields]; exact hb
  | _ :: _, _, _, .nil => by simp only [encodeFields]; exact hb
end

/-! ## Loads and retyping -/

theorem load_mono {m m' : Mem} (h : Mem.Refines m m') (t : Ty) (p : Ptr) :
    Refines (m.load t p) (m'.load t p) := by
  unfold Mem.load
  split
  · exact .empty
  · exact .poison _
  · exact .poison _
  · exact .poison _
  · cases hr : m.read p t.size with
    | none => exact .poison _
    | some bs =>
      obtain ⟨bs', hr', hb⟩ := h.read hr
      rw [hr']
      exact decode_mono hb 0 t

theorem retype_mono (t : Ty) {v v' : Val} (h : Refines v v') :
    Refines (v.retype t) (v'.retype t) := by
  cases h with
  | poison v' =>
    have : Val.retype t .poison = .poison := by cases t <;> rfl
    rw [this]; exact .poison _
  | int w x => exact Refines.refl _
  | bool b => exact Refines.refl _
  | ptr p => exact Refines.refl _
  | empty => exact Refines.refl _
  | mem h => cases t <;> exact .mem h
  | tuple h => cases t <;> exact .tuple h
  | agg h => cases t <;> exact .agg h
  | blob h => cases t <;> exact .blob h

end GoFV.SSA.Sem

import GoFV.Proof.MemRefine
import GoFV.SSA.Sem.Layout
import GoFV.Proof.Retype

/-!
# Encoding, decoding and retyping are monotone in refinement

`decode` of refined bytes refines (`decode_mono`), and so does a `Load`'s `decodeLoad`
(`decodeLoad_mono`), `encode` of a refined value gives refined
bytes (`encode_mono`), `Mem.load` of a refined memory refines (`load_mono`), `Val.retype`
preserves refinement (`retype_mono`). A poison-free value is only refined by itself up to
memories (`Refines.noPoison`).
-/

namespace GoFV.SSA.Sem

open GoFV.SSA

/-! ## Transitivity -/

mutual
theorem Refines.trans : {a b c : Val} → Refines a b → Refines b c → Refines a c
  | _, _, _, .poison _, _ => .poison _
  | _, _, _, .int _ _, h => h
  | _, _, _, .bool _, h => h
  | _, _, _, .mem h1, .mem h2 => .mem (h1.trans h2)
  | _, _, _, .tuple h1, .tuple h2 => .tuple (RefinesList.trans h1 h2)
  | _, _, _, .ptr _, h => h
  | _, _, _, .agg h1, .agg h2 => .agg (RefinesList.trans h1 h2)
  | _, _, _, .blob h1, .blob h2 => .blob (h1.trans h2)
  | _, _, _, .empty, h => h
theorem RefinesList.trans : {a b c : List Val} → RefinesList a b → RefinesList b c →
    RefinesList a c
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h1 t1, .cons h2 t2 => .cons (Refines.trans h1 h2) (RefinesList.trans t1 t2)
end

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

theorem decodeInt_mono {bs bs' : Array Byte} (h : BytesRefineA bs bs') (w : Width) (a b : Nat) :
    Refines (decodeInt w (bs.extract a b)) (decodeInt w (bs'.extract a b)) := by
  rcases bytesRefine_eq_or_poison (h.extract a b) with he | hp
  · rw [he]; exact Refines.refl _
  · rw [decodeInt_poison hp]; exact .poison _

theorem decodePtr_mono {bs bs' : Array Byte} (h : BytesRefineA bs bs') (a b : Nat) :
    Refines (decodePtr (bs.extract a b)) (decodePtr (bs'.extract a b)) := by
  rcases bytesRefine_eq_or_poison (h.extract a b) with he | hp
  · rw [he]; exact Refines.refl _
  · rw [decodePtr_poison hp]; exact .poison _

/-- A string built from refined components refines (the length check is monotone). -/
theorem ofStr_mono {vs vs' : List Val} (h : RefinesList vs vs') :
    Refines (Val.ofStr vs) (Val.ofStr vs') := by
  unfold Val.ofStr
  by_cases hs : Val.strOK vs = true
  · obtain ⟨p, l, rfl, hl⟩ := Val.strOK_iff.1 hs
    rcases h with _ | ⟨hp, _ | ⟨hl', h3⟩⟩
    cases hl'; cases h3
    rw [if_pos hs, if_pos (by simp [Val.strOK, hl])]
    exact .agg (.cons hp (.cons (.int _ _) .nil))
  · rw [if_neg hs]; exact .poison _

/-- A slice built from refined components refines. -/
theorem ofSlice_mono {vs vs' : List Val} (h : RefinesList vs vs') :
    Refines (Val.ofSlice vs) (Val.ofSlice vs') := by
  unfold Val.ofSlice
  by_cases hs : Val.sliceOK vs = true
  · obtain ⟨p, l, c, rfl, hl, hc, hlc⟩ := Val.sliceOK_iff.1 hs
    rcases h with _ | ⟨hp, _ | ⟨hl', _ | ⟨hc', h4⟩⟩⟩
    cases hl'; cases hc'; cases h4
    rw [if_pos hs, if_pos (by simp [Val.sliceOK, hl, hc, BitVec.ule, hlc])]
    exact .agg (.cons hp (.cons (.int _ _) (.cons (.int _ _) .nil)))
  · rw [if_neg hs]; exact .poison _

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
  | .str => by
    simp only [decode]
    exact ofStr_mono (.cons (decodePtr_mono h _ _) (.cons (decodeInt_mono h _ _ _) .nil))
  | .slice _ => by
    simp only [decode]
    exact ofSlice_mono (.cons (decodePtr_mono h _ _)
      (.cons (decodeInt_mono h _ _ _) (.cons (decodeInt_mono h _ _ _) .nil)))
theorem decodeFields_mono {bs bs' : Array Byte} (h : BytesRefineA bs bs') (off : Nat) :
    (fs : List (Nat × Ty)) → RefinesList (decodeFields bs off fs) (decodeFields bs' off fs)
  | [] => by simp only [decodeFields]; exact .nil
  | (o, t) :: fs => by
    simp only [decodeFields]
    exact .cons (decode_mono h (off + o) t) (decodeFields_mono h off fs)
end

theorem BytesRefine.allPoison : ∀ {a b : List Byte}, BytesRefine a b →
    b.all (· matches .poison) = true → a.all (· matches .poison) = true
  | _, _, .nil, _ => rfl
  | _, _, .cons h t, hb => by
    simp only [List.all_cons, Bool.and_eq_true] at hb ⊢
    refine ⟨?_, BytesRefine.allPoison t hb.2⟩
    cases h with
    | poison => rfl
    | refl => exact hb.1

/-- Refined bytes are all `poison` where the refining ones are. -/
theorem allPoison_mono {bs bs' : Array Byte} (h : BytesRefineA bs bs') (off n : Nat)
    (hp : allPoison bs' off n = true) : allPoison bs off n = true := by
  unfold allPoison at hp ⊢
  simp only [Bool.and_eq_true] at hp ⊢
  refine ⟨hp.1, ?_⟩
  rw [← Array.all_toList] at hp ⊢
  exact BytesRefine.allPoison (h.extract _ _) hp.2

mutual
theorem decodeLoad_mono {bs bs' : Array Byte} (h : BytesRefineA bs bs') (off : Nat) :
    (t : Ty) → Refines (decodeLoad bs off t) (decodeLoad bs' off t)
  | .agg fs n => by
    simp only [decodeLoad]
    by_cases hp : allPoison bs off n = true
    · rw [if_pos hp]; exact .poison _
    · rw [if_neg hp, if_neg fun h' => hp (allPoison_mono h off n h')]
      exact .agg (decodeLoadFields_mono h off fs)
  | .int w => by simp only [decodeLoad]; exact decode_mono h off _
  | .bool => by simp only [decodeLoad]; exact decode_mono h off _
  | .ptr _ => by simp only [decodeLoad]; exact decode_mono h off _
  | .blob _ => by simp only [decodeLoad]; exact decode_mono h off _
  | .opaque _ => by simp only [decodeLoad]; exact decode_mono h off _
  | .empty => by simp only [decodeLoad]; exact .empty
  | .other => by simp only [decodeLoad]; exact .poison _
  | .mem => by simp only [decodeLoad]; exact .poison _
  | .tuple _ => by simp only [decodeLoad]; exact .poison _
  | .str => by
    simp only [decodeLoad]
    by_cases hp : allPoison bs off 16 = true
    · rw [if_pos hp]; exact .poison _
    · rw [if_neg hp, if_neg fun h' => hp (allPoison_mono h off 16 h')]
      exact decode_mono h off _
  | .slice _ => by
    simp only [decodeLoad]
    by_cases hp : allPoison bs off 24 = true
    · rw [if_pos hp]; exact .poison _
    · rw [if_neg hp, if_neg fun h' => hp (allPoison_mono h off 24 h')]
      exact decode_mono h off _
theorem decodeLoadFields_mono {bs bs' : Array Byte} (h : BytesRefineA bs bs') (off : Nat) :
    (fs : List (Nat × Ty)) → RefinesList (decodeLoadFields bs off fs) (decodeLoadFields bs' off fs)
  | [] => by simp only [decodeLoadFields]; exact .nil
  | (o, t) :: fs => by
    simp only [decodeLoadFields]
    exact .cons (decodeLoad_mono h (off + o) t) (decodeLoadFields_mono h off fs)
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

theorem encodeWord_eq (e : Option Nat) (v : Val) : encodeWord v = encode (.ptr e) v := by
  cases v with
  | int w x => cases w <;> rfl
  | _ => rfl

theorem encodeWord_eq_i64 (v : Val) : encodeWord v = encode (.int .w64) v := by
  cases v with
  | int w x => cases w <;> rfl
  | _ => rfl

/-- `encodeWords` is `encodeFields` at word fields. -/
theorem encodeWords_eq (buf : Array Byte) (os : List Nat) (ts : List Ty) (vs : List Val)
    (hl : os.length = ts.length)
    (ht : ∀ t ∈ ts, ∀ v, encodeWord v = encode t v) :
    encodeWords buf os vs = encodeFields buf (os.zip ts) vs := by
  induction os generalizing buf ts vs with
  | nil => simp [encodeWords, encodeFields]
  | cons o os ih =>
    cases ts with
    | nil => simp at hl
    | cons t ts =>
      cases vs with
      | nil => simp [encodeWords, encodeFields]
      | cons v vs =>
        simp only [encodeWords, List.zip_cons_cons, encodeFields]
        rw [ht t (List.mem_cons_self ..) v]
        exact ih _ ts vs (by simpa using hl) fun t' h' => ht t' (List.mem_cons_of_mem _ h')

/-- A string is encoded as the aggregate of its fields. -/
theorem encode_str_agg (vs : List Val) :
    encode .str (.agg vs) = encodeFields (Array.replicate 16 .poison)
      [(0, .ptr (some 1)), (8, .int .w64)] vs := by
  simp only [encode]
  exact encodeWords_eq _ [0, 8] [.ptr (some 1), .int .w64] vs rfl (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro t (rfl | rfl) v
    · exact encodeWord_eq _ v
    · exact encodeWord_eq_i64 v)

/-- A slice is encoded as the aggregate of its fields. -/
theorem encode_slice_agg (e : Option Nat) (vs : List Val) :
    encode (.slice e) (.agg vs) = encodeFields (Array.replicate 24 .poison)
      [(0, .ptr e), (8, .int .w64), (16, .int .w64)] vs := by
  simp only [encode]
  exact encodeWords_eq _ [0, 8, 16] [.ptr e, .int .w64, .int .w64] vs rfl (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro t (rfl | rfl | rfl) v
    · exact encodeWord_eq _ v
    · exact encodeWord_eq_i64 v
    · exact encodeWord_eq_i64 v)

theorem encodeWords_size (buf : Array Byte) :
    (os : List Nat) → (vs : List Val) → (encodeWords buf os vs).size = buf.size
  | o :: os, v :: vs => by
    simp only [encodeWords]; rw [encodeWords_size, putBytes_size]
  | [], _ => by simp [encodeWords]
  | _ :: _, [] => by simp [encodeWords]

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
  | .str, .agg vs => by simp only [encode, Ty.size]; rw [encodeWords_size]; simp
  | .slice _, .agg vs => by simp only [encode, Ty.size]; rw [encodeWords_size]; simp
  | .str, .int _ _ | .str, .bool _ | .str, .ptr _ | .str, .empty
  | .slice _, .int _ _ | .slice _, .bool _ | .slice _, .ptr _ | .slice _, .empty => by
    simp [encode]
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
    | str =>
      rw [encode_str_agg, encode_str_agg]
      exact encodeFields_mono (BytesRefineA.refl _) _ h
    | slice e =>
      rw [encode_slice_agg, encode_slice_agg]
      exact encodeFields_mono (BytesRefineA.refl _) _ h
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

/-- `retype` at the string shape: the fields' retyping, then the length check. -/
theorem retype_str_agg (vs : List Val) :
    Val.retype .str (.agg vs) =
      match Val.retypeFields [(0, .ptr (some 1)), (8, .int .w64)] vs with
      | some vs' => Val.ofStr vs'
      | none => .poison := by
  match vs with
  | [p, l] =>
    show Val.ofStr [p.retypePtr, l.retypeI64] =
      Val.ofStr [p.retype (.ptr (some 1)), l.retype (.int .w64)]
    rw [Val.retypePtr_eq (some 1), Val.retypeI64_eq]
  | [] | [_] | _ :: _ :: _ :: _ => rfl

/-- `retype` at a slice shape: the fields' retyping, then the length check. -/
theorem retype_slice_agg (e : Option Nat) (vs : List Val) :
    Val.retype (.slice e) (.agg vs) =
      match Val.retypeFields [(0, .ptr e), (8, .int .w64), (16, .int .w64)] vs with
      | some vs' => Val.ofSlice vs'
      | none => .poison := by
  match vs with
  | [p, l, c] =>
    show Val.ofSlice [p.retypePtr, l.retypeI64, c.retypeI64] =
      Val.ofSlice [p.retype (.ptr e), l.retype (.int .w64), c.retype (.int .w64)]
    rw [Val.retypePtr_eq e, Val.retypeI64_eq, Val.retypeI64_eq]
  | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ => rfl

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
      exact decodeLoad_mono hb 0 t

mutual
theorem retype_mono : ∀ (t : Ty) {v v' : Val}, Refines v v' → Refines (v.retype t) (v'.retype t)
  | t, _, _, .poison v' => by
    have : Val.retype t .poison = .poison := by cases t <;> rfl
    rw [this]; exact .poison _
  | _, _, _, .int w x => Refines.refl _
  | _, _, _, .bool b => Refines.refl _
  | _, _, _, .ptr p => Refines.refl _
  | _, _, _, .empty => Refines.refl _
  | t, _, _, .mem h => by cases t <;> first | exact .mem h | exact .poison _
  | t, .tuple vs, .tuple vs', .tuple h => by
    cases t with
    | tuple ts =>
      unfold Val.retype
      have hr := retypePre_mono ts h
      cases ha : Val.retypePre ts vs <;> cases hb : Val.retypePre ts vs' <;> rw [ha, hb] at hr
      · exact .poison _
      · cases hr
      · cases hr
      · cases hr with | some hw => exact .tuple hw
    | _ => exact .poison _
  | t, .agg vs, .agg vs', .agg h => by
    cases t with
    | agg fs n =>
      unfold Val.retype
      have hr := retypeFields_mono fs h
      cases ha : Val.retypeFields fs vs <;> cases hb : Val.retypeFields fs vs' <;> rw [ha, hb] at hr
      · exact .poison _
      · cases hr
      · cases hr
      · cases hr with | some hw => exact .agg hw
    | str =>
      rw [retype_str_agg, retype_str_agg]
      have hr := retypeFields_mono [(0, .ptr (some 1)), (8, .int .w64)] h
      cases ha : Val.retypeFields [(0, .ptr (some 1)), (8, .int .w64)] vs <;>
        cases hb : Val.retypeFields [(0, .ptr (some 1)), (8, .int .w64)] vs' <;>
        rw [ha, hb] at hr
      · exact .poison _
      · cases hr
      · cases hr
      · cases hr with | some hw => exact ofStr_mono hw
    | slice e =>
      rw [retype_slice_agg, retype_slice_agg]
      have hr := retypeFields_mono [(0, .ptr e), (8, .int .w64), (16, .int .w64)] h
      cases ha : Val.retypeFields [(0, .ptr e), (8, .int .w64), (16, .int .w64)] vs <;>
        cases hb : Val.retypeFields [(0, .ptr e), (8, .int .w64), (16, .int .w64)] vs' <;>
        rw [ha, hb] at hr
      · exact .poison _
      · cases hr
      · cases hr
      · cases hr with | some hw => exact ofSlice_mono hw
    | _ => exact .poison _
  | t, .blob bs, .blob bs', .blob h => by
    cases t with
    | blob n =>
      unfold Val.retype
      rw [← BytesRefine.length_eq h]
      split
      · exact .blob h
      · exact .poison _
    | _ => exact .poison _

theorem retypePre_mono : ∀ (ts : List Ty) {vs vs' : List Val}, RefinesList vs vs' →
    Option.Rel RefinesList (Val.retypePre ts vs) (Val.retypePre ts vs')
  | [], _, _, h => .some h
  | _ :: _, _, _, .nil => .none
  | t :: ts, _, _, .cons ha hs => by
    simp only [Val.retypePre]
    have hr := retypePre_mono ts hs
    revert hr
    cases Val.retypePre ts _ <;> cases Val.retypePre ts _ <;> intro hr
    · exact .none
    · cases hr
    · cases hr
    · cases hr with | some hw => exact .some (.cons (retype_mono t ha) hw)

theorem retypeFields_mono : ∀ (fs : List (Nat × Ty)) {vs vs' : List Val}, RefinesList vs vs' →
    Option.Rel RefinesList (Val.retypeFields fs vs) (Val.retypeFields fs vs')
  | [], _, _, .nil => .some .nil
  | [], _, _, .cons _ _ => .none
  | _ :: _, _, _, .nil => .none
  | (_, t) :: fs, _, _, .cons ha hs => by
    simp only [Val.retypeFields]
    have hr := retypeFields_mono fs hs
    revert hr
    cases Val.retypeFields fs _ <;> cases Val.retypeFields fs _ <;> intro hr
    · exact .none
    · cases hr
    · cases hr
    · cases hr with | some hw => exact .some (.cons (retype_mono t ha) hw)
end

/-! ## Strings and slices as aggregates

Encoding, decoding, loading and retyping at a string or slice shape are those at its aggregate
layout (`Ty.asAgg`) followed by the length check (`Val.checkLen`), which only adds `poison`
(`Val.checkLen_refines`) and is monotone (`Val.checkLen_mono`). Proofs about aggregates so
carry over to strings and slices. -/

theorem Ty.size_asAgg (t : Ty) : t.asAgg.size = t.size := by cases t <;> rfl

theorem Ty.asAgg_asAgg (t : Ty) : t.asAgg.asAgg = t.asAgg := by cases t <;> rfl

/-- The length check keeps a value or makes it `poison`. -/
theorem Val.checkLen_eq_or (t : Ty) (v : Val) : Val.checkLen t v = v ∨ Val.checkLen t v = .poison := by
  cases t <;> cases v <;> first
    | exact .inl rfl
    | (simp only [Val.checkLen, Val.ofStr, Val.ofSlice]; split
       · exact .inl rfl
       · exact .inr rfl)

theorem Val.checkLen_poison (t : Ty) : Val.checkLen t .poison = .poison := by cases t <;> rfl

/-- The length check only makes a value `poison`. -/
theorem Val.checkLen_refines (t : Ty) (v : Val) : Refines (Val.checkLen t v) v := by
  cases t <;> cases v <;> first
    | exact Refines.refl _
    | (simp only [Val.checkLen, Val.ofStr, Val.ofSlice]; split
       · exact Refines.refl _
       · exact .poison _)

theorem Val.checkLen_mono (t : Ty) {v v' : Val} (h : Refines v v') :
    Refines (Val.checkLen t v) (Val.checkLen t v') := by
  cases h with
  | poison v' => rw [Val.checkLen_poison]; exact .poison _
  | agg hl =>
    cases t
    case str => exact ofStr_mono hl
    case slice => exact ofSlice_mono hl
    all_goals exact .agg hl
  | mem h => cases t <;> exact .mem h
  | tuple h => cases t <;> exact .tuple h
  | blob h => cases t <;> exact .blob h
  | int w x => cases t <;> exact Refines.refl _
  | bool b => cases t <;> exact Refines.refl _
  | ptr p => cases t <;> exact Refines.refl _
  | empty => cases t <;> exact Refines.refl _

theorem decode_asAgg (bs : Array Byte) (off : Nat) (t : Ty) :
    decode bs off t = Val.checkLen t (decode bs off t.asAgg) := by
  cases t
  case str =>
    simp only [decode, decodeFields, Ty.asAgg, Ty.strAgg, Val.checkLen, Nat.add_zero,
      Width.bytes, Width.bits, Nat.add_assoc]
  case slice e =>
    simp only [decode, decodeFields, Ty.asAgg, Ty.sliceAgg, Val.checkLen, Nat.add_zero,
      Width.bytes, Width.bits, Nat.add_assoc]
  all_goals rfl

theorem decodeLoad_asAgg (bs : Array Byte) (off : Nat) (t : Ty) :
    decodeLoad bs off t = Val.checkLen t (decodeLoad bs off t.asAgg) := by
  cases t
  case str =>
    simp only [decodeLoad, Ty.asAgg, Ty.strAgg, decodeLoadFields]
    split
    · rfl
    · rw [decode_asAgg]; rfl
  case slice e =>
    simp only [decodeLoad, Ty.asAgg, Ty.sliceAgg, decodeLoadFields]
    split
    · rfl
    · rw [decode_asAgg]; rfl
  all_goals rfl

theorem load_asAgg (m : Mem) (t : Ty) (p : Ptr) :
    m.load t p = Val.checkLen t (m.load t.asAgg p) := by
  cases t
  case str =>
    simp only [Mem.load, Ty.asAgg, Ty.strAgg, Ty.size]
    cases m.read p 16 with
    | none => rfl
    | some bs => exact decodeLoad_asAgg bs 0 .str
  case slice e =>
    simp only [Mem.load, Ty.asAgg, Ty.sliceAgg, Ty.size]
    cases m.read p 24 with
    | none => rfl
    | some bs => exact decodeLoad_asAgg bs 0 (.slice e)
  all_goals rfl

theorem encode_asAgg (t : Ty) (v : Val) : encode t v = encode t.asAgg v := by
  cases t
  case str =>
    cases v
    case agg vs => exact encode_str_agg vs
    all_goals simp [encode, Ty.asAgg, Ty.strAgg, Ty.size]
  case slice e =>
    cases v
    case agg vs => exact encode_slice_agg e vs
    all_goals simp [encode, Ty.asAgg, Ty.sliceAgg, Ty.size]
  all_goals rfl

theorem retype_asAgg (t : Ty) (v : Val) : v.retype t = Val.checkLen t (v.retype t.asAgg) := by
  cases t
  case str =>
    cases v
    case agg vs =>
      rw [retype_str_agg]
      simp only [Ty.asAgg, Ty.strAgg, Val.retype]
      split <;> rename_i h <;> rw [h] <;> rfl
    all_goals rfl
  case slice e =>
    cases v
    case agg vs =>
      rw [retype_slice_agg]
      simp only [Ty.asAgg, Ty.sliceAgg, Val.retype]
      split <;> rename_i h <;> rw [h] <;> rfl
    all_goals rfl
  all_goals rfl

/-- A value of a shape has the shape's aggregate layout. -/
theorem Val.hasTy_asAgg {v : Val} {t : Ty} (h : v.hasTy t = true) :
    v.hasTy t.asAgg = true := by
  cases t
  case str =>
    cases v with
    | poison => rfl
    | agg vs =>
      obtain ⟨p, l, rfl, hp, -⟩ := Val.hasTy_agg_str.1 h
      cases p <;> simp_all [Val.isPtrOrPoison, Val.hasTy, Ty.asAgg, Ty.strAgg, Val.hasTyList]
    | _ => simp [Val.hasTy] at h
  case slice e =>
    cases v with
    | poison => rfl
    | agg vs =>
      obtain ⟨p, l, c, rfl, hp, -⟩ := Val.hasTy_agg_slice.1 h
      cases p <;> simp_all [Val.isPtrOrPoison, Val.hasTy, Ty.asAgg, Ty.sliceAgg, Val.hasTyList]
    | _ => simp [Val.hasTy] at h
  all_goals exact h

/-- The length check of a value of a shape's aggregate layout has the shape. -/
theorem Val.checkLen_hasTy {v : Val} {t : Ty} (h : v.hasTy t.asAgg = true) :
    (Val.checkLen t v).hasTy t = true := by
  cases t
  case str =>
    cases v with
    | poison => rfl
    | agg vs =>
      simp only [Val.checkLen, Val.ofStr]
      split
      · next hs =>
        obtain ⟨p, l, rfl, -⟩ := Val.strOK_iff.1 hs
        cases p <;> simp_all [Val.isPtrOrPoison, Val.hasTy, Ty.asAgg, Ty.strAgg, Val.hasTyList]
      · rfl
    | _ => simp [Val.hasTy, Ty.asAgg, Ty.strAgg] at h
  case slice e =>
    cases v with
    | poison => rfl
    | agg vs =>
      simp only [Val.checkLen, Val.ofSlice]
      split
      · next hs =>
        obtain ⟨p, l, c, rfl, -⟩ := Val.sliceOK_iff.1 hs
        cases p <;> simp_all [Val.isPtrOrPoison, Val.hasTy, Ty.asAgg, Ty.sliceAgg, Val.hasTyList]
      · rfl
    | _ => simp [Val.hasTy, Ty.asAgg, Ty.sliceAgg] at h
  all_goals exact h

/-- The length check keeps a value of the shape. -/
theorem Val.checkLen_of_hasTy {v : Val} {t : Ty} (h : v.hasTy t = true) : Val.checkLen t v = v := by
  cases t
  case str =>
    cases v with
    | agg vs => exact Val.ofStr_of_ok (by simp only [Val.hasTy, Bool.and_eq_true] at h; exact h.1)
    | _ => rfl
  case slice e =>
    cases v with
    | agg vs => exact Val.ofSlice_of_ok (by simp only [Val.hasTy, Bool.and_eq_true] at h; exact h.1)
    | _ => rfl
  all_goals rfl

/-- A string or slice value refines when its aggregate does: the source's length check only adds
`poison`, the target's is monotone. -/
theorem retype_checkLen_refines {t : Ty} {L R : Val}
    (h : Refines (L.retype t.asAgg) (R.retype t.asAgg)) :
    Refines ((Val.checkLen t L).retype t) (R.retype t) := by
  rw [retype_asAgg t, retype_asAgg t R]
  exact Val.checkLen_mono t ((retype_mono _ (Val.checkLen_refines t L)).trans h)

end GoFV.SSA.Sem

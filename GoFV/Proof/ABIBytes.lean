import GoFV.Proof.ABIBuild

/-!
# Byte facts for the ABI round trip (#28)

`Agree bs o bs' o' n`: two buffers hold the same `n` bytes from `o` and `o'`. `decode` of a
well-formed shape reads only its own bytes (`decode_agree`); `putBytes` and `encodeFields`
write where they should (`putBytes_agree`, `putBytes_getElem?_out`, `encodeFields_agree`,
`encodeFields_getElem?_lt`); a register piece survives `encode` then `decode` exactly
(`decode_encode_atom`, from `bytesNat?_intBytes` and the pointer-byte lemmas).
-/

namespace GoFV.Proof.ABI

open GoFV.SSA.Sem

/-! ## Agreeing byte ranges -/

/-- `bs` from `o` and `bs'` from `o'` hold the same `n` bytes (out of range alike). -/
def Agree (bs : Array Byte) (o : Nat) (bs' : Array Byte) (o' : Nat) (n : Nat) : Prop :=
  ∀ k, k < n → bs[o + k]? = bs'[o' + k]?

theorem Agree.refl (bs : Array Byte) (o n : Nat) : Agree bs o bs o n := fun _ _ => rfl

theorem Agree.trans {a b c : Array Byte} {x y z n : Nat} (h1 : Agree a x b y n)
    (h2 : Agree b y c z n) : Agree a x c z n := fun k hk => (h1 k hk).trans (h2 k hk)

theorem Agree.sub {a b : Array Byte} {x y n : Nat} (h : Agree a x b y n) {o m : Nat}
    (hm : o + m ≤ n) : Agree a (x + o) b (y + o) m := fun k hk => by
  have := h (o + k) (by omega)
  simpa [Nat.add_assoc] using this

theorem getElem?_extract_add (bs : Array Byte) (o n i : Nat) :
    (bs.extract o (o + n))[i]? = if i < n then bs[o + i]? else none := by
  rw [Array.getElem?_extract]
  have h1 := Nat.min_le_left (o + n) bs.size
  have h2 := Nat.min_le_right (o + n) bs.size
  have h3 : min (o + n) bs.size = o + n ∨ min (o + n) bs.size = bs.size := by
    rw [Nat.min_def]; split <;> simp
  by_cases hi : i < min (o + n) bs.size - o
  · simp only [hi, show i < n by omega, ↓reduceIte]
  · simp only [hi, ↓reduceIte]
    split
    · exact (Array.getElem?_eq_none (by omega)).symm
    · rfl

theorem extract_agree {bs bs' : Array Byte} {o o' n : Nat} (h : Agree bs o bs' o' n) :
    bs.extract o (o + n) = bs'.extract o' (o' + n) :=
  Array.ext_getElem? fun i => by
    rw [getElem?_extract_add, getElem?_extract_add]
    split
    · exact h i ‹_›
    · rfl

/-! ## `decode` reads only its own bytes -/

mutual
theorem decode_agree : (t : Ty) → {bs bs' : Array Byte} → {o o' : Nat} → wf t = true →
    Agree bs o bs' o' t.size → decode bs o t = decode bs' o' t
  | .int w, _, _, _, _, _, h => by
    simp only [decode]; rw [extract_agree (n := w.bytes) h]
  | .bool, bs, bs', o, o', _, h => by
    have e : bs[o]? = bs'[o']? := h 0 (by decide)
    simp only [decode]; rw [e]
  | .ptr _, _, _, _, _, _, h => by
    simp only [decode]; rw [extract_agree (n := 8) h]
  | .agg fs n, _, _, _, _, hw, h => by
    simp only [decode]; rw [decodeFields_agree fs n 0 hw h]
  | .empty, _, _, _, _, _, _ | .opaque _, _, _, _, _, _, _ => rfl
  | .blob _, _, _, _, _, hw, _ | .mem, _, _, _, _, hw, _ | .tuple _, _, _, _, _, hw, _
  | .other, _, _, _, _, hw, _ => nomatch hw
theorem decodeFields_agree : (fs : List (Nat × Ty)) → (n s : Nat) → {bs bs' : Array Byte} →
    {o o' : Nat} → wfFields fs n s = true → Agree bs o bs' o' n →
    decodeFields bs o fs = decodeFields bs' o' fs
  | [], _, _, _, _, _, _, _, _ => rfl
  | (fo, ft) :: fs, n, s, _, _, _, _, hw, h => by
    simp only [wfFields, Bool.and_eq_true] at hw
    have hle := wfFields_le hw.2
    simp only [decodeFields]
    rw [decode_agree ft hw.1.2 (h.sub hle), decodeFields_agree fs n _ hw.2 h]
end

/-! ## Writing bytes -/

/-- One step of `putBytes`. -/
def pstep (off : Nat) (src : Array Byte) (d : Array Byte) (i : Nat) : Array Byte :=
  if off + i < d.size then d.set! (off + i) src[i]! else d

theorem putBytes_eq (dst : Array Byte) (off : Nat) (src : Array Byte) :
    putBytes dst off src = (List.range src.size).foldl (pstep off src) dst := (rfl)

theorem pstep_size (off : Nat) (src d : Array Byte) (i : Nat) :
    (pstep off src d i).size = d.size := by
  unfold pstep; split <;> simp

theorem foldl_pstep_size (off : Nat) (src : Array Byte) :
    (l : List Nat) → (d : Array Byte) → (l.foldl (pstep off src) d).size = d.size
  | [], _ => rfl
  | i :: l, d => by rw [List.foldl_cons, foldl_pstep_size off src l, pstep_size]

theorem foldl_pstep_out (off : Nat) (src : Array Byte) (j : Nat) :
    (l : List Nat) → (d : Array Byte) → (∀ i ∈ l, off + i ≠ j) →
      (l.foldl (pstep off src) d)[j]? = d[j]?
  | [], _, _ => rfl
  | i :: l, d, h => by
    rw [List.foldl_cons, foldl_pstep_out off src j l _ fun i' hi' => h i' (List.mem_cons_of_mem _ hi')]
    unfold pstep
    split
    · have hne : ¬off + i = j := h i List.mem_cons_self
      simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hne, ↓reduceIte]
    · rfl

theorem foldl_pstep_in (off : Nat) (src : Array Byte) (j : Nat) :
    (l : List Nat) → (d : Array Byte) → (∃ i ∈ l, off + i = j) → j < d.size →
      (l.foldl (pstep off src) d)[j]? = some src[j - off]!
  | [], _, ⟨_, hi, _⟩, _ => absurd hi List.not_mem_nil
  | i :: l, d, h, hj => by
    rw [List.foldl_cons]
    by_cases hl : ∃ i' ∈ l, off + i' = j
    · exact foldl_pstep_in off src j l _ hl (by rw [pstep_size]; exact hj)
    · have hl' : ∀ i' ∈ l, off + i' ≠ j := fun i' hi' e => hl ⟨i', hi', e⟩
      rw [foldl_pstep_out off src j l _ hl']
      obtain ⟨i'', hi'', e⟩ := h
      have hi : off + i = j := by
        rcases List.mem_cons.1 hi'' with rfl | hi''
        · exact e
        · exact absurd e (hl' i'' hi'')
      subst hi
      unfold pstep
      simp only [hj, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, ↓reduceIte,
        Nat.add_sub_cancel_left]

theorem putBytes_getElem?_out {dst src : Array Byte} {off j : Nat}
    (h : j < off ∨ off + src.size ≤ j) : (putBytes dst off src)[j]? = dst[j]? := by
  rw [putBytes_eq]
  exact foldl_pstep_out off src j _ dst fun i hi => by
    have := List.mem_range.1 hi
    omega

theorem putBytes_agree {dst src : Array Byte} {off : Nat} (h : off + src.size ≤ dst.size) :
    Agree (putBytes dst off src) off src 0 src.size := fun k hk => by
  rw [putBytes_eq, foldl_pstep_in off src (off + k) _ dst ⟨k, List.mem_range.2 hk, rfl⟩
    (by omega), Nat.add_sub_cancel_left, Nat.zero_add, getElem!_pos src k hk,
    Array.getElem?_eq_getElem hk]

theorem encodeFields_getElem?_lt : (fs : List (Nat × Ty)) → (vs : List Val) →
    (buf : Array Byte) → (n s j : Nat) → wfFields fs n s = true → buf.size = n → j < s →
    (encodeFields buf fs vs)[j]? = buf[j]?
  | [], _, _, _, _, _, _, _, _ => rfl
  | _ :: _, [], _, _, _, _, _, _, _ => rfl
  | (o, t) :: fs, v :: vs, buf, n, s, j, hw, hb, hj => by
    simp only [wfFields, Bool.and_eq_true, decide_eq_true_eq] at hw
    simp only [encodeFields]
    rw [encodeFields_getElem?_lt fs vs _ n (o + t.size) j hw.2 (by rw [putBytes_size, hb])
      (by omega), putBytes_getElem?_out (.inl (by omega))]

/-- In `encodeFields`, a field's bytes are its value's encoding. -/
theorem encodeFields_agree {o : Nat} {t : Ty} {fs : List (Nat × Ty)} {v : Val} {vs : List Val}
    {buf : Array Byte} {n s : Nat} (hw : wfFields ((o, t) :: fs) n s = true) (hb : buf.size = n) :
    Agree (encodeFields buf ((o, t) :: fs) (v :: vs)) o (encode t v) 0 t.size := fun k hk => by
  simp only [wfFields, Bool.and_eq_true, decide_eq_true_eq] at hw
  have hle := wfFields_le hw.2
  simp only [encodeFields]
  rw [encodeFields_getElem?_lt fs vs _ n (o + t.size) (o + k) hw.2 (by rw [putBytes_size, hb])
    (by omega)]
  exact putBytes_agree (by rw [encode_size, hb]; omega) k (by rw [encode_size]; exact hk)

/-! ## Register pieces survive `encode` and `decode` -/

theorem pow8_succ (n : Nat) : 2 ^ (8 * (n + 1)) = 256 * 2 ^ (8 * n) := by
  rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]

theorem bytesNat?_intBytes_list : (n x : Nat) →
    ((List.range n).map fun i => Byte.b (BitVec.ofNat 8 (x / 2 ^ (8 * i)))).foldr
      (fun b acc => match b, acc with
        | .b x, some n => some (x.toNat + 256 * n)
        | _, _ => none) (some 0) = some (x % 2 ^ (8 * n))
  | 0, x => by simp [Nat.mod_one]
  | n + 1, x => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.foldr_cons]
    have e : ((fun i => Byte.b (BitVec.ofNat 8 (x / 2 ^ (8 * i)))) ∘ Nat.succ) =
        fun i => Byte.b (BitVec.ofNat 8 (x / 256 / 2 ^ (8 * i))) := by
      funext i
      show Byte.b (BitVec.ofNat 8 (x / 2 ^ (8 * (i + 1)))) = _
      rw [pow8_succ, Nat.div_div_eq_div_mul]
    rw [e, bytesNat?_intBytes_list n (x / 256)]
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, BitVec.toNat_ofNat]
    rw [pow8_succ, Nat.mod_mul]

theorem bytesNat?_intBytes (n x : Nat) : bytesNat? (intBytes n x) = some (x % 2 ^ (8 * n)) := by
  unfold bytesNat? intBytes
  rw [← Array.foldr_toList, Array.toList_map, List.toList_toArray]
  exact bytesNat?_intBytes_list n x

theorem bytesNat?_ptrBytes (q : Ptr) : bytesNat? (ptrBytes q) = none := by
  unfold bytesNat? ptrBytes; rw [← Array.foldr_toList]; simp [List.range_succ]

theorem bytesPtr?_ptrBytes (q : Ptr) : bytesPtr? (ptrBytes q) = some q := by
  unfold bytesPtr? ptrBytes; simp [List.range_succ]

theorem ofNat_toNat_mod (w : Width) (x : BitVec w.bits) :
    BitVec.ofNat w.bits (x.toNat % 2 ^ (8 * w.bytes)) = x := by
  have e : 8 * w.bytes = w.bits := by cases w <;> rfl
  rw [e, Nat.mod_eq_of_lt x.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem hasPoisonByte_replicate {n : Nat} (h : 0 < n) :
    HasPoisonByte (Array.replicate n Byte.poison) :=
  ⟨.poison, by simp; omega, rfl⟩

theorem width_bytes_pos (w : Width) : 0 < w.bytes := by cases w <;> decide

/-- A register piece is decoded from its encoding as it was. -/
theorem decode_encode_atom : (t : Ty) → (p : Val) → atom t = true → p.hasTy t = true →
    decode (encode t p) 0 t = p
  | .int w, p, _, hp => by
    have hs : (encode (.int w) p).size ≤ 0 + w.bytes := by rw [encode_size]; simp [Ty.size]
    show decodeInt w ((encode (.int w) p).extract 0 (0 + w.bytes)) = p
    rw [Array.extract_eq_self_of_le hs]
    cases p with
    | poison =>
      rw [encode_poison]
      exact decodeInt_poison (hasPoisonByte_replicate (width_bytes_pos w))
    | int w' x =>
      simp only [Val.hasTy, beq_iff_eq] at hp
      subst hp
      simp only [encode, beq_self_eq_true, ↓reduceIte]
      unfold decodeInt
      rw [bytesNat?_intBytes]
      simp only [ofNat_toNat_mod]
    | ptr q =>
      cases w with
      | w64 =>
        simp only [Val.hasTy, Option.isNone_iff_eq_none] at hp
        show decodeInt .w64 (ptrBytes q) = .ptr q
        unfold decodeInt
        rw [bytesNat?_ptrBytes, bytesPtr?_ptrBytes]
        simp only [hp]
      | _ => simp [Val.hasTy] at hp
    | _ => simp [Val.hasTy] at hp
  | .bool, p, _, hp => by
    cases p with
    | poison => rw [encode_poison]; rfl
    | bool b => cases b <;> rfl
    | _ => simp [Val.hasTy] at hp
  | .ptr e, p, _, hp => by
    cases p with
    | poison =>
      rw [encode_poison]
      show decodePtr ((Array.replicate 8 Byte.poison).extract 0 (0 + 8)) = .poison
      rw [Array.extract_eq_self_of_le (by simp)]
      exact decodePtr_poison (hasPoisonByte_replicate (by decide))
    | ptr q =>
      show decodePtr ((ptrBytes q).extract 0 (0 + 8)) = .ptr q
      rw [Array.extract_eq_self_of_le (by simp [ptrBytes]), decodePtr, bytesPtr?_ptrBytes]
    | _ => simp [Val.hasTy] at hp
  | .opaque _, p, _, hp => by
    cases p with
    | poison => rfl
    | _ => simp [Val.hasTy] at hp
  | .agg _ _, _, h, _ | .empty, _, h, _ | .blob _, _, h, _ | .mem, _, h, _ | .tuple _, _, h, _
  | .other, _, h, _ => nomatch h

/-- A register piece is decoded from bytes that agree with its encoding as it was. -/
theorem decode_atom {t : Ty} {p : Val} {bs : Array Byte} {o : Nat} (ht : atom t = true)
    (hp : p.hasTy t = true) (h : Agree bs o (encode t p) 0 t.size) : decode bs o t = p := by
  rw [decode_agree t (wf_atom ht) h, decode_encode_atom t p ht hp]

end GoFV.Proof.ABI

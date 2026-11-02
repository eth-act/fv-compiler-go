import GoFV.Proof.Pass.CSEMemBytes
import GoFV.Proof.ValRefine
import GoFV.Proof.ABIBytes
import GoFV.Opt.RewriteCheck

/-!
# Load-of-Store forwarding: a read after a write (issue #151)

`read_write_self`: reading the bytes just written at the same pointer gives them back.
`decode_encode`: at an integer, boolean or pointer shape (`RewriteCheck.scalarTy`), decoding
the encoding of a value of that shape (fixed by `Val.retype`) gives the value back, or `poison`
(for `poison`). `decodeLoad_encode`: so does a `Load`'s `decodeLoad` at a shape `fwdTy`, also an
aggregate of non-overlapping such fields (`fields_encode`; a `poison` aggregate is all `poison`
bytes, which `decodeLoad` reads as `poison`). `load_write`: a `Load` of shape `t` at `p` after a
`Store` of `x` at `p` with shape `t` reads `x` back.
-/

namespace GoFV.Proof.Pass.LoadFwd

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof.CSE.Mem

/-- The byte loop of `Mem.write` puts `bs[i]` at `off + i`. -/
theorem foldl_set_put (off : Nat) (bs : Array Byte) (i : Nat) :
    ∀ (l : List Nat) (d : Array Byte), l.Nodup → i ∈ l → off + i < d.size →
      (l.foldl (fun d i => d.set! (off + i) bs[i]!) d)[off + i]? = some bs[i]!
  | [], _, _, hi, _ => absurd hi List.not_mem_nil
  | j :: l, d, hnd, hi, hlt => by
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hi with rfl | hi'
    · rw [foldl_set_get off bs (off + i) l _ fun k hk he => (List.nodup_cons.1 hnd).1 (by
        have : k = i := by omega
        exact this ▸ hk)]
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hlt]
    · exact foldl_set_put off bs i l _ (List.nodup_cons.1 hnd).2 hi' (by simp; exact hlt)

/-- **A read of what was just written.** -/
theorem read_write_self {m m' : Mem} {p : Ptr} {bs : Array Byte} (hw : m.write p bs = some m') :
    m'.read p bs.size = some bs := by
  unfold Mem.write at hw
  by_cases he : bs.isEmpty
  · have h0 : bs.size = 0 := by simpa [Array.isEmpty_iff_size_eq_zero] using he
    unfold Mem.read
    rw [h0]
    simp only [beq_self_eq_true, ite_true]
    rw [Array.eq_empty_of_size_eq_zero h0]; rfl
  simp only [he, Bool.false_eq_true, ite_false] at hw
  have hsz : bs.size ≠ 0 := by simpa [Array.isEmpty_iff_size_eq_zero] using he
  cases ha : m.find? p.blk with
  | none => rw [ha] at hw; cases hw
  | some a =>
    rw [ha] at hw
    simp only [Option.bind_eq_bind, Option.bind_some] at hw
    split at hw
    · rename_i hok
      cases hw
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      unfold Mem.read
      simp only [beq_iff_eq, hsz, ite_false]
      rw [find?_set]
      simp only [ite_true, Option.bind_eq_bind, Option.bind_some, foldl_set_size]
      simp only [hok.1.1.2, hok.1.2, hok.2, and_self, ↓reduceIte]
      congr 1
      apply Array.ext
      · rw [Array.size_extract, foldl_set_size]; omega
      · intro j h1 h2
        rw [Array.size_extract, foldl_set_size] at h1
        simp only [Array.getElem_extract]
        have hj : j < bs.size := by omega
        have := foldl_set_put p.off.toNat bs j (List.range bs.size) a.data List.nodup_range
          (List.mem_range.2 hj) (by omega)
        rw [Array.getElem?_eq_getElem (by rw [foldl_set_size]; omega)] at this
        rw [Option.some.inj this, getElem!_pos bs j hj]
    · cases hw

/-! ## Decoding an encoding -/

theorem bytesNat?_range' (x : Nat) : ∀ (n s : Nat),
    ((List.range' s n).map fun i => Byte.b (BitVec.ofNat 8 (x / 2 ^ (8 * i)))).foldr
      (fun b acc => match b, acc with
        | .b x, some n => some (x.toNat + 256 * n)
        | _, _ => none) (some 0) = some (x / 2 ^ (8 * s) % 2 ^ (8 * n))
  | 0, s => by simp [Nat.mod_one]
  | n + 1, s => by
    rw [List.range'_succ, List.map_cons, List.foldr_cons, bytesNat?_range' x n (s + 1)]
    simp only [BitVec.toNat_ofNat, Option.some.injEq]
    have h1 : x / 2 ^ (8 * (s + 1)) = x / 2 ^ (8 * s) / 256 := by
      rw [Nat.div_div_eq_div_mul]
      congr 1
      rw [show 8 * (s + 1) = 8 * s + 8 by omega, Nat.pow_add]
    rw [h1, show 2 ^ (8 * (n + 1)) = 256 * 2 ^ (8 * n) by
      rw [show 8 * (n + 1) = 8 + 8 * n by omega, Nat.pow_add], Nat.mod_mul]

theorem bytesNat?_intBytes (n x : Nat) : bytesNat? (intBytes n x) = some (x % 2 ^ (8 * n)) := by
  have := bytesNat?_range' x n 0
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one] at this
  unfold bytesNat? intBytes
  rw [← Array.foldr_toList, Array.toList_map, List.toList_toArray, List.range_eq_range']
  exact this

theorem width_bits (w : Width) : w.bits = 8 * w.bytes := by cases w <;> rfl

theorem intBytes_size (n x : Nat) : (intBytes n x).size = n := by simp [intBytes]

theorem bytesPtr?_ptrBytes (p : Ptr) : bytesPtr? (ptrBytes p) = some p := by
  simp [bytesPtr?, ptrBytes, List.range, List.range.loop]

theorem bytesNat?_ptrBytes (p : Ptr) : bytesNat? (ptrBytes p) = none := by
  simp [bytesNat?, ptrBytes, List.range, List.range.loop]

theorem ptrBytes_size (p : Ptr) : (ptrBytes p).size = 8 := by simp [ptrBytes]

theorem decode_poison_int (w : Width) :
    decode (Array.replicate w.bytes Byte.poison) 0 (.int w) = .poison := by
  cases w <;> rfl

/-- **Decoding an encoding** at a shape `scalarTy` gives a value of that shape back. -/
theorem decode_encode {t : Ty} (ht : GoFV.Opt.RewriteCheck.scalarTy t = true) {x : Val}
    (hx : x.retype t = x) : Sem.Refines (decode (encode t x) 0 t) x := by
  cases t with
  | int w =>
    cases x with
    | poison =>
      have : decode (encode (.int w) .poison) 0 (.int w) = .poison := by cases w <;> rfl
      rw [this]; exact .poison _
    | int w' v =>
      simp only [Val.retype] at hx
      split at hx
      · rename_i hle
        injection hx with hw hv
        subst hw
        have hv' : v = v.setWidth w.bits := (eq_of_heq hv).symm
        simp only [encode, beq_self_eq_true, ite_true, decode, decodeInt]
        rw [Array.extract_eq_self_of_le (by rw [intBytes_size]; omega), bytesNat?_intBytes,
          ← width_bits]
        dsimp only
        rw [Nat.mod_eq_of_lt v.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        exact Sem.Refines.refl _
      · cases hx
    | ptr p =>
      cases w with
      | w64 =>
        simp only [Val.retype] at hx
        split at hx
        · cases hx
        · rename_i hp
          simp only [encode, decode, decodeInt, Nat.zero_add]
          rw [Array.extract_eq_self_of_le (by rw [ptrBytes_size]; exact Nat.le_refl _),
            bytesNat?_ptrBytes]
          simp only [bytesPtr?_ptrBytes, hp]
          exact Sem.Refines.refl _
      | _ => simp [Val.retype] at hx
    | _ => simp [Val.retype] at hx
  | bool =>
    cases x with
    | poison => exact .poison _
    | bool b => cases b <;> exact Sem.Refines.refl _
    | _ => simp [Val.retype] at hx
  | ptr e =>
    cases x with
    | poison => exact .poison _
    | ptr p =>
      simp only [encode, decode, decodePtr, Nat.zero_add]
      rw [Array.extract_eq_self_of_le (by rw [ptrBytes_size]; exact Nat.le_refl _),
        bytesPtr?_ptrBytes]
      exact Sem.Refines.refl _
    | int w v =>
      cases w with
      | w64 =>
        simp only [encode, decode, decodePtr, Nat.zero_add]
        rw [Array.extract_eq_self_of_le (by rw [intBytes_size]; exact Nat.le_refl _),
          GoFV.Proof.ABI.bytesPtr?_intBytes, bytesNat?_intBytes]
        dsimp only
        rw [Nat.mod_eq_of_lt v.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        exact Sem.Refines.refl _
      | _ => simp [Val.retype] at hx
    | _ => simp [Val.retype] at hx
  | _ => simp [GoFV.Opt.RewriteCheck.scalarTy] at ht

/-- `fwdFields` are laid out as `ABI.wfFields` says. -/
theorem fwdFields_wf {n : Nat} : ∀ {lo : Nat} {fs : List (Nat × Ty)},
    GoFV.Opt.RewriteCheck.fwdFields n lo fs = true → lo ≤ n → GoFV.Proof.ABI.wfFields fs n lo = true
  | _, [], _, hl => by simpa [GoFV.Proof.ABI.wfFields] using hl
  | _, (o, t) :: fs, h, _ => by
    simp only [GoFV.Opt.RewriteCheck.fwdFields, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hs, hlo⟩, hon⟩, hf⟩ := h
    simp only [GoFV.Proof.ABI.wfFields, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨hlo, ?_⟩, fwdFields_wf hf hon⟩
    cases t <;> first | rfl | simp [GoFV.Opt.RewriteCheck.scalarTy] at hs

/-- A `scalarTy` shape loads as it decodes. -/
theorem decodeLoad_scalar {t : Ty} (ht : GoFV.Opt.RewriteCheck.scalarTy t = true)
    (bs : Array Byte) (o : Nat) : decodeLoad bs o t = decode bs o t := by
  cases t <;> first | rfl | simp [GoFV.Opt.RewriteCheck.scalarTy] at ht

/-- The fields of an `encodeFields` of retype-fixed values at `fwdFields` decode back. -/
theorem fields_encode {n : Nat} {B : Array Byte} : ∀ {lo : Nat} {fs : List (Nat × Ty)}
    {vs : List Val} {buf : Array Byte}, GoFV.Opt.RewriteCheck.fwdFields n lo fs = true →
    lo ≤ n → buf.size = n → Val.retypeFields fs vs = some vs → B = encodeFields buf fs vs →
    Sem.RefinesList (decodeLoadFields B 0 fs) vs
  | _, [], [], _, _, _, _, _, _ => by simp only [decodeLoadFields]; exact .nil
  | _, [], _ :: _, _, _, _, _, hr, _ => by simp [Val.retypeFields] at hr
  | _, _ :: _, [], _, _, _, _, hr, _ => by simp [Val.retypeFields] at hr
  | lo, (o, t) :: fs, v :: vs, buf, h, hlo, hb, hr, hB => by
    have hw := fwdFields_wf h hlo
    have hag := GoFV.Proof.ABI.encodeFields_agree (v := v) (vs := vs) hw hb
    rw [← hB] at hag
    simp only [Val.retypeFields, Option.map_eq_some_iff, List.cons.injEq] at hr
    obtain ⟨vs', hvs', hv, rfl⟩ := hr
    simp only [GoFV.Opt.RewriteCheck.fwdFields, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hs, -⟩, hon⟩, hf⟩ := h
    simp only [decodeLoadFields, Nat.zero_add]
    refine .cons ?_ (fields_encode (buf := putBytes buf o (encode t v)) hf hon
      (by rw [putBytes_size, hb]) hvs' (by rw [hB]; rfl))
    rw [decodeLoad_scalar hs, GoFV.Proof.ABI.decode_agree t (by
      cases t <;> first | rfl | simp [GoFV.Opt.RewriteCheck.scalarTy] at hs) hag]
    exact decode_encode hs hv

/-- `n ≠ 0` `poison` bytes are `allPoison`. -/
theorem allPoison_replicate {n : Nat} (hn : n ≠ 0) :
    allPoison (Array.replicate n Byte.poison) 0 n = true := by
  unfold allPoison
  rw [Nat.zero_add, Array.extract_eq_self_of_le (by simp), ← Array.all_toList,
    Array.toList_replicate]
  simp [hn]

/-- `decodeLoad_encode` at a `fwdAgg` aggregate layout. -/
private theorem decodeLoad_encode_agg {t : Ty} (ht : GoFV.Opt.RewriteCheck.fwdAgg t = true)
    (hA : t.asAgg = t) {x : Val} (hx : x.retype t = x) :
    Sem.Refines (decodeLoad (encode t x) 0 t) x := by
  cases t with
  | agg fs n =>
    simp only [GoFV.Opt.RewriteCheck.fwdAgg, Ty.asAgg, Bool.and_eq_true, bne_iff_ne,
      ne_eq] at ht
    cases x with
    | poison =>
      rw [encode_poison]
      simp only [decodeLoad, Ty.size, allPoison_replicate ht.1, ite_true]
      exact .poison _
    | agg vs =>
      simp only [Val.retype] at hx
      split at hx
      · rename_i vs' hr
        injection hx with hx
        subst hx
        simp only [decodeLoad]
        split
        · exact .poison _
        · exact .agg (fields_encode (buf := Array.replicate n .poison) ht.2 (Nat.zero_le _)
            (by simp) hr (by simp only [encode]))
      · cases hx
    | _ => simp [Val.retype] at hx
  | _ => simp [GoFV.Opt.RewriteCheck.fwdAgg, Ty.asAgg, Ty.strAgg, Ty.sliceAgg] at ht hA

/-- **Decoding a `Load` of an encoding** at a shape `fwdTy` gives a value of that shape back. -/
theorem decodeLoad_encode {t : Ty} (ht : GoFV.Opt.RewriteCheck.fwdTy t = true) {x : Val}
    (hx : x.retype t = x) : Sem.Refines (decodeLoad (encode t x) 0 t) x := by
  rcases Bool.or_eq_true_iff.1 ht with hs | ha
  · rw [decodeLoad_scalar hs]
    exact decode_encode hs hx
  -- through the aggregate layout and the length check (`Val.checkLen`)
  have hx' : x.retype t.asAgg = x := by
    rw [retype_asAgg] at hx
    rcases Val.checkLen_eq_or t (x.retype t.asAgg) with h | h
    · rwa [h] at hx
    · rw [h] at hx; subst hx; cases t.asAgg <;> rfl
  have hc : Val.checkLen t x = x := by rwa [retype_asAgg, hx'] at hx
  have ha' : GoFV.Opt.RewriteCheck.fwdAgg t.asAgg = true := by
    rwa [GoFV.Opt.RewriteCheck.fwdAgg, Ty.asAgg_asAgg]
  have := Val.checkLen_mono t (decodeLoad_encode_agg ha' (Ty.asAgg_asAgg t) hx')
  rwa [hc, ← decodeLoad_asAgg, ← encode_asAgg] at this

/-- **A `Load` after a `Store` at the same pointer** reads the stored value back (or `poison`). -/
theorem load_write {t : Ty} (ht : GoFV.Opt.RewriteCheck.fwdTy t = true) {x : Val}
    (hx : x.retype t = x) {m m' : Mem} {p : Ptr} (hw : m.write p (encode t x) = some m') :
    Sem.Refines (m'.load t p) x := by
  have hr := read_write_self hw
  rw [Sem.encode_size] at hr
  have hl : m'.load t p = decodeLoad (encode t x) 0 t := by
    unfold Mem.load
    cases t <;> simp_all [GoFV.Opt.RewriteCheck.fwdTy, GoFV.Opt.RewriteCheck.scalarTy,
      GoFV.Opt.RewriteCheck.fwdAgg, Ty.asAgg]
  rw [hl]
  exact decodeLoad_encode ht hx

/-! ## A read inside a read (`generic.rules:827`) -/

/-- A valid non-empty read: inside its allocation, below `2^64`, inside its window, the bytes
there. -/
theorem read_some {m : Mem} {p : Ptr} {n : Nat} {bs : Array Byte} (hn : n ≠ 0)
    (h : m.read p n = some bs) : ∃ a, m.find? p.blk = some a ∧ p.off.toNat + n ≤ a.data.size ∧
      p.off.toNat + n < 2 ^ 64 ∧ p.blk.endsInWindow (p.off.toNat + n) = true ∧
      bs = a.data.extract p.off.toNat (p.off.toNat + n) := by
  unfold Mem.read at h
  simp only [beq_iff_eq, hn, ite_false] at h
  cases ha : m.find? p.blk with
  | none => rw [ha] at h; cases h
  | some a =>
    rw [ha] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · rename_i hc
      cases h
      exact ⟨a, rfl, hc.1, hc.2.1, hc.2.2, rfl⟩
    · cases h

theorem read_size {m : Mem} {p : Ptr} {n : Nat} {bs : Array Byte} (hn : n ≠ 0)
    (h : m.read p n = some bs) : bs.size = n := by
  obtain ⟨a, -, h1, -, -, rfl⟩ := read_some hn h
  simp only [Array.size_extract]
  omega

theorem endsInWindow_mono {b : Blk} {e e' : Nat} (h : e ≤ e') (h' : b.endsInWindow e' = true) :
    b.endsInWindow e = true := by
  unfold Blk.endsInWindow at h' ⊢
  cases hw : b.window? with
  | none => rfl
  | some w =>
    rw [hw] at h'
    simp only [decide_eq_true_eq] at h' ⊢
    omega

theorem ptr_add_ofNat_toNat {p : Ptr} {o : Nat} (h : p.off.toNat + o < 2 ^ 64) :
    (p.add (BitVec.ofNat 64 o)).off.toNat = p.off.toNat + o := by
  simp only [Ptr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show o < 2 ^ 64 by omega), Nat.mod_eq_of_lt h]

/-- **A read inside a valid read** reads its sub-range. -/
theorem read_sub {m : Mem} {s : Ptr} {n : Nat} {bs : Array Byte} (hr : m.read s n = some bs)
    {o k : Nat} (hk : 0 < k) (hok : o + k ≤ n) :
    m.read (s.add (BitVec.ofNat 64 o)) k = some (bs.extract o (o + k)) := by
  obtain ⟨a, ha, h1, h2, h3, rfl⟩ := read_some (by omega) hr
  have hoff := ptr_add_ofNat_toNat (p := s) (o := o) (by omega)
  have hblk : (s.add (BitVec.ofNat 64 o)).blk = s.blk := rfl
  unfold Mem.read
  simp only [beq_iff_eq, show k ≠ 0 by omega, ite_false, hblk, ha, Option.bind_eq_bind,
    Option.bind_some, hoff]
  rw [if_pos ⟨by omega, by omega, endsInWindow_mono (by omega) h3⟩, Array.extract_extract]
  congr 2 <;> omega

/-- A pointer inside a valid read is inside its window. -/
theorem read_inWindow {m : Mem} {s : Ptr} {n : Nat} {bs : Array Byte} (hr : m.read s n = some bs)
    {o : Nat} (ho : o < n) : (s.add (BitVec.ofNat 64 o)).inWindow = true := by
  obtain ⟨a, -, -, h2, h3, -⟩ := read_some (by omega) hr
  have hoff := ptr_add_ofNat_toNat (p := s) (o := o) (by omega)
  have hblk : (s.add (BitVec.ofNat 64 o)).blk = s.blk := rfl
  unfold Ptr.inWindow
  unfold Blk.endsInWindow at h3
  rw [hblk, hoff]
  cases hw : s.blk.window? with
  | none => rfl
  | some w =>
    rw [hw] at h3
    simp only [decide_eq_true_eq] at h3 ⊢
    omega

/-- `Load`s of equal bytes are equal. -/
theorem load_congr_read {m m' : Mem} {p q : Ptr} {t : Ty}
    (h : m.read p t.size = m'.read q t.size) : m.load t p = m'.load t q := by
  unfold Mem.load
  split <;> first | rfl | rw [h]

end GoFV.Proof.Pass.LoadFwd

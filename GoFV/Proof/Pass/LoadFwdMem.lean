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
      cases w <;> simp [Val.retype] at hx
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

/-- **Decoding a `Load` of an encoding** at a shape `fwdTy` gives a value of that shape back. -/
theorem decodeLoad_encode {t : Ty} (ht : GoFV.Opt.RewriteCheck.fwdTy t = true) {x : Val}
    (hx : x.retype t = x) : Sem.Refines (decodeLoad (encode t x) 0 t) x := by
  rcases Bool.or_eq_true_iff.1 ht with hs | ha
  · rw [decodeLoad_scalar hs]
    exact decode_encode hs hx
  cases t with
  | agg fs n =>
    simp only [GoFV.Opt.RewriteCheck.fwdAgg, Bool.and_eq_true, bne_iff_ne, ne_eq] at ha
    cases x with
    | poison =>
      rw [encode_poison]
      simp only [decodeLoad, Ty.size, allPoison_replicate ha.1, ite_true]
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
        · exact .agg (fields_encode (buf := Array.replicate n .poison) ha.2 (Nat.zero_le _)
            (by simp) hr (by simp only [encode]))
      · cases hx
    | _ => simp [Val.retype] at hx
  | _ => simp [GoFV.Opt.RewriteCheck.fwdAgg] at ha

/-- **A `Load` after a `Store` at the same pointer** reads the stored value back (or `poison`). -/
theorem load_write {t : Ty} (ht : GoFV.Opt.RewriteCheck.fwdTy t = true) {x : Val}
    (hx : x.retype t = x) {m m' : Mem} {p : Ptr} (hw : m.write p (encode t x) = some m') :
    Sem.Refines (m'.load t p) x := by
  have hr := read_write_self hw
  rw [Sem.encode_size] at hr
  have hl : m'.load t p = decodeLoad (encode t x) 0 t := by
    unfold Mem.load
    cases t <;> simp_all [GoFV.Opt.RewriteCheck.fwdTy, GoFV.Opt.RewriteCheck.scalarTy,
      GoFV.Opt.RewriteCheck.fwdAgg]
  rw [hl]
  exact decodeLoad_encode ht hx

end GoFV.Proof.Pass.LoadFwd

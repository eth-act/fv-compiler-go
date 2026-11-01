import GoFV.Proof.ABIBytes

/-!
# The ABI round trip of register-assigned values (#28)

For a well-formed register shape `t` (`wf t`) and a value `v` of shape `t`:

* `toPieces_eq_leafVals`: the semantics' register pieces (`toPieces`: encode, then decode at
  each leaf) are what selector chains compute (`leafVals`);
* `ofPieces_eq_build`: assembling typed pieces through a buffer (`ofPieces`) is what a Make-tree
  builds (`build`);
* `roundtrip`, `ofPieces_leafVals`: decoding an encoding, and assembling the pieces again,
  give back a refinement of `v` (equal up to poison inside composites);
* `decode_hasTy`, `build_decode`: decoding gives a value of shape `t`, and is `build` of the
  leaves' decodings.

Byte facts in `GoFV.Proof.ABIBytes`, the byte-free ones in `GoFV.Proof.ABIBuild`.
-/

namespace GoFV.Proof.ABI

open GoFV.SSA.Sem

/-! ## `decode` gives a value of its shape -/

theorem decodeInt_hasTy (w : Width) (bs : Array Byte) : (decodeInt w bs).hasTy (.int w) = true := by
  unfold decodeInt
  split
  · simp [Val.hasTy]
  · split
    · split
      · simp [Val.hasTy]
      · next h => simp [Val.hasTy, h]
    · rfl

theorem decodePtr_hasTy (e : Option Nat) (bs : Array Byte) :
    (decodePtr bs).hasTy (.ptr e) = true := by
  unfold decodePtr
  split
  · rfl
  · split <;> rfl

mutual
theorem decode_hasTy_aux : (t : Ty) → (bs : Array Byte) → (o : Nat) → wf t = true →
    (decode bs o t).hasTy t = true
  | .int w, _, _, _ => decodeInt_hasTy w _
  | .bool, bs, o, _ => by
    simp only [decode]
    split
    · split <;> rfl
    · rfl
  | .ptr e, _, _, _ => decodePtr_hasTy e _
  | .agg fs n, bs, o, h => decodeFields_hasTy fs n 0 bs o h
  | .empty, _, _, _ | .opaque _, _, _, _ => rfl
  | .blob _, _, _, h | .mem, _, _, h | .tuple _, _, _, h | .other, _, _, h => nomatch h
theorem decodeFields_hasTy : (fs : List (Nat × Ty)) → (n s : Nat) → (bs : Array Byte) →
    (o : Nat) → wfFields fs n s = true →
    Val.hasTyList (decodeFields bs o fs) (fs.map (·.2)) = true
  | [], _, _, _, _, _ => rfl
  | (fo, ft) :: fs, n, s, bs, o, h => by
    simp only [wfFields, Bool.and_eq_true] at h
    simp only [decodeFields, List.map_cons, Val.hasTyList, Bool.and_eq_true]
    exact ⟨decode_hasTy_aux ft bs (o + fo) h.1.2, decodeFields_hasTy fs n _ bs o h.2⟩
end

/-- 1. Decoding gives a value of the decoded shape. -/
theorem decode_hasTy {t : Ty} {bs : Array Byte} {o : Nat} (h : wf t = true) :
    (decode bs o t).hasTy t = true :=
  decode_hasTy_aux t bs o h

/-! ## `toPieces` is `leafVals` -/

mutual
theorem leaves_decode_encode : (t : Ty) → (v : Val) → {buf : Array Byte} → {b : Nat} →
    wf t = true → v.hasTy t = true → Agree buf b (encode t v) 0 t.size →
    (leaves t).map (fun x => decode buf (b + x.1) x.2) = leafVals t v
  | .int _, v, _, _, _, hv, h | .bool, v, _, _, _, hv, h | .ptr _, v, _, _, _, hv, h
  | .opaque _, v, _, _, _, hv, h => by
    rw [leaves_atom rfl, leafVals_atom rfl, Val.retype_of_hasTy hv]
    simp only [List.map_cons, List.map_nil, Nat.add_zero]
    rw [decode_atom rfl hv h]
  | .empty, _, _, _, _, _, _ => rfl
  | .agg fs n, v, buf, b, hw, hv, h => by
    cases v with
    | poison =>
      rw [leafVals_agg_of_ne (v := .poison) fun _ e => nomatch e]
      rw [encode_poison] at h
      change Agree buf b (Array.replicate n .poison) 0 n at h
      apply List.map_congr_left
      intro x hx
      obtain ⟨hb, ha⟩ := mem_leaves hw hx
      change x.1 + x.2.size ≤ n at hb
      apply decode_atom ha (rfl : Val.hasTy .poison x.2 = true)
      rw [encode_poison]
      intro k hk
      have hn : x.1 + k < n := by omega
      have := h (x.1 + k) hn
      rw [← Nat.add_assoc] at this
      rw [this, Array.getElem?_replicate, Array.getElem?_replicate]
      simp only [Nat.zero_add, hn, hk, ↓reduceIte]
    | agg vs =>
      exact leavesFields_decode_encode fs vs n 0 (buf0 := Array.replicate n .poison) hw hv
        (by simp) h
    | _ => simp [Val.hasTy] at hv
  | .blob _, _, _, _, h, _, _ | .mem, _, _, _, h, _, _ | .tuple _, _, _, _, h, _, _
  | .other, _, _, _, h, _, _ => nomatch h
theorem leavesFields_decode_encode : (fs : List (Nat × Ty)) → (vs : List Val) → (n s : Nat) →
    {buf buf0 : Array Byte} → {b : Nat} → wfFields fs n s = true →
    Val.hasTyList vs (fs.map (·.2)) = true → buf0.size = n →
    Agree buf b (encodeFields buf0 fs vs) 0 n →
    (leaves.leavesFields fs).map (fun x => decode buf (b + x.1) x.2) = leafValsFields fs vs
  | [], [], _, _, _, _, _, _, _, _, _ => rfl
  | (o, t) :: fs, v :: vs, n, s, buf, buf0, b, hw, hv, hb, h => by
    have hreg : Agree (encodeFields buf0 ((o, t) :: fs) (v :: vs)) o (encode t v) 0 t.size :=
      encodeFields_agree hw hb
    simp only [wfFields, Bool.and_eq_true, decide_eq_true_eq] at hw
    simp only [List.map_cons, Val.hasTyList, Bool.and_eq_true] at hv
    have hle := wfFields_le hw.2
    rw [leavesFields_cons, List.map_append, List.map_map, leafValsFields_cons,
      Val.retype_of_hasTy hv.1]
    have e : ((fun x : Nat × Ty => decode buf (b + x.1) x.2) ∘ fun x : Nat × Ty => (o + x.1, x.2)) =
        fun x : Nat × Ty => decode buf (b + o + x.1) x.2 := by
      funext x; simp [Nat.add_assoc]
    have h1 : Agree buf (b + o) (encode t v) 0 t.size := by
      have := h.sub (o := o) (m := t.size) hle
      rw [Nat.zero_add] at this
      exact this.trans hreg
    rw [e, leaves_decode_encode t v hw.1.2 hv.1 h1,
      leavesFields_decode_encode fs vs n _ (buf0 := putBytes buf0 o (encode t v)) hw.2 hv.2
        (by rw [putBytes_size, hb]) h]
  | [], _ :: _, _, _, _, _, _, _, hv, _, _ | _ :: _, [], _, _, _, _, _, _, hv, _, _ => by
    simp [Val.hasTyList] at hv
end

/-- 9. The semantics' register pieces of a value are its selector chains' values. -/
theorem toPieces_eq_leafVals {t : Ty} {v : Val} (hw : wf t = true) (hv : v.hasTy t = true) :
    toPieces t v = leafVals t v := by
  have := leaves_decode_encode t v (buf := encode t v) (b := 0) hw hv (Agree.refl _ 0 _)
  simp only [Nat.zero_add] at this
  exact this

/-! ## `ofPieces` is `build` -/

/-- `ofPieces`' fold step. -/
def ostep (buf : Array Byte) (x : (Nat × Ty) × Val) : Array Byte :=
  putBytes buf x.1.1 (encode x.1.2 x.2)

theorem ofPieces_eq (t : Ty) (ps : List Val) :
    ofPieces t ps = decode (((leaves t).zip ps).foldl ostep (Array.replicate t.size .poison)) 0 t :=
  (rfl)

theorem foldl_ostep_lt : (L : List (Nat × Ty)) → (ps : List Val) → (buf : Array Byte) →
    (n s j : Nat) → wfFields L n s = true → buf.size = n → j < s →
    ((L.zip ps).foldl ostep buf)[j]? = buf[j]?
  | [], _, _, _, _, _, _, _, _ => rfl
  | _ :: _, [], _, _, _, _, _, _, _ => rfl
  | (o, lt) :: L, p :: ps, buf, n, s, j, hw, hb, hj => by
    simp only [wfFields, Bool.and_eq_true, decide_eq_true_eq] at hw
    rw [List.zip_cons_cons, List.foldl_cons,
      foldl_ostep_lt L ps _ n (o + lt.size) j hw.2 (by rw [ostep, putBytes_size, hb]) (by omega)]
    show (putBytes buf o (encode lt p))[j]? = buf[j]?
    exact putBytes_getElem?_out (.inl (by omega))

theorem foldl_ostep_decode : {ps : List Val} → {L : List (Nat × Ty)} →
    List.Forall₂ (fun p (l : Nat × Ty) => p.hasTy l.2 = true) ps L → (buf : Array Byte) →
    (n s : Nat) → wfFields L n s = true → (∀ x ∈ L, atom x.2 = true) → buf.size = n →
    L.map (fun x => decode ((L.zip ps).foldl ostep buf) x.1 x.2) = ps
  | _, _, .nil, _, _, _, _, _, _ => rfl
  | p :: ps, (o, lt) :: L, .cons hp hf, buf, n, s, hw, ha, hb => by
    simp only [wfFields, Bool.and_eq_true, decide_eq_true_eq] at hw
    have hle := wfFields_le hw.2
    have hb1 : (ostep buf ((o, lt), p)).size = n := by rw [ostep, putBytes_size, hb]
    simp only [List.zip_cons_cons, List.foldl_cons, List.map_cons]
    have hhead : decode ((L.zip ps).foldl ostep (ostep buf ((o, lt), p))) o lt = p := by
      apply decode_atom (t := lt) (ha (o, lt) List.mem_cons_self) hp
      intro k hk
      rw [foldl_ostep_lt L ps _ n (o + lt.size) (o + k) hw.2 hb1 (by omega)]
      show (putBytes buf o (encode lt p))[o + k]? = (encode lt p)[0 + k]?
      exact putBytes_agree (by rw [encode_size, hb]; omega) k (by rw [encode_size]; exact hk)
    rw [hhead, foldl_ostep_decode hf _ n _ hw.2 (fun x hx => ha x (List.mem_cons_of_mem _ hx)) hb1]

/-- 7. Assembling typed register pieces through a buffer is what a Make-tree builds. -/
theorem ofPieces_eq_build {t : Ty} {ps : List Val} (hw : wf t = true)
    (hp : List.Forall₂ (fun p (l : Nat × Ty) => p.hasTy l.2 = true) ps (leaves t)) :
    ofPieces t ps = build t ps := by
  rw [ofPieces_eq, ← build_decode_aux t _ 0 hw]
  congr 1
  have := foldl_ostep_decode hp (Array.replicate t.size .poison) t.size 0 (leaves_wfFields hw)
    (fun x hx => (mem_leaves hw hx).2) (by simp)
  simp only [Nat.zero_add]
  exact this

/-! ## Round trips -/

/-- 10. Decoding the encoding of a value of a well-formed shape refines it. -/
theorem roundtrip {t : Ty} {v : Val} (hw : wf t = true) (hv : v.hasTy t = true) :
    Refines v (decode (encode t v) 0 t) := by
  rw [← build_decode_aux t (encode t v) 0 hw,
    leaves_decode_encode t v (buf := encode t v) (b := 0) hw hv (Agree.refl _ 0 _)]
  exact build_leafVals hw hv

/-- 11. Assembling a value's selector-chain pieces again refines it. -/
theorem ofPieces_leafVals {t : Ty} {v : Val} (hw : wf t = true) (hv : v.hasTy t = true) :
    Refines v (ofPieces t (leafVals t v)) := by
  rw [ofPieces_eq_build hw (leafVals_hasTy hw)]
  exact build_leafVals hw hv

/-! ## Non-vacuity: a slice -/

/-- The shape of a slice of `int64` (`tyOf`, `.SLICE`). -/
def sliceTy : Ty := .agg [(0, .ptr (some 8)), (8, .int .w64), (16, .int .w64)] 24

/-- A slice value: a heap pointer, length 2, capacity 3. -/
def sliceVal : Val := .agg [.ptr ⟨.heap 0, 0⟩, .int .w64 2, .int .w64 3]

theorem sliceTy_wf : wf sliceTy = true ∧ sliceVal.hasTy sliceTy = true := ⟨rfl, rfl⟩

/-- The round trips at the slice: its three pieces and back, exactly. -/
theorem slice_roundtrip :
    toPieces sliceTy sliceVal = [.ptr ⟨.heap 0, 0⟩, .int .w64 2, .int .w64 3] ∧
      ofPieces sliceTy (leafVals sliceTy sliceVal) = build sliceTy (leafVals sliceTy sliceVal) ∧
      Refines sliceVal (decode (encode sliceTy sliceVal) 0 sliceTy) ∧
      Refines sliceVal (ofPieces sliceTy (leafVals sliceTy sliceVal)) :=
  ⟨by rw [toPieces_eq_leafVals sliceTy_wf.1 sliceTy_wf.2]; rfl,
    ofPieces_eq_build sliceTy_wf.1 (leafVals_hasTy sliceTy_wf.1),
    roundtrip sliceTy_wf.1 sliceTy_wf.2, ofPieces_leafVals sliceTy_wf.1 sliceTy_wf.2⟩

end GoFV.Proof.ABI

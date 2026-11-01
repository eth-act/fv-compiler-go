import GoFV.Proof.Pass.ECDefs
import GoFV.Proof.Pass.ECShape
import GoFV.Proof.ABI

/-!
# `expand calls`: the `Ret` outcomes (issue #28)

`finish_ecRR`: the source's results `rs` (one per result of the function, each of its shape)
and the target's register pieces `rs'` refining theirs, retyped at the register shapes (`ecRR`),
finish alike. The source takes `goResults`' Go-typed path and decodes `encode t r` (= `r` for a
poison-free result); the target takes the register path, where each result is `ofPieces t` of
its retyped pieces (= `r`: the leaf shape decodes a retyped piece's encoding as the piece, also
for a 64-bit integer in a pointer register, `ecf_decode_reg`), or the Go-typed path, which it
can only take when every result has a single leaf of an atom shape.

`ret_result`: a `Ret` of a converted `MakeResult` relates the outcomes by `ecRR`, for
poison-free source results (otherwise `finish` is stuck); the register shapes are the target
`MakeResult`'s (`regTupleOf`).
-/

namespace GoFV.Proof.EC

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.ECCheck GoFV.Proof.ABI

/-! ## Poison-free values of well-formed shapes -/

theorem ecf_anyPoison_append (l l' : List Val) :
    Val.anyPoison (l ++ l') = (Val.anyPoison l || Val.anyPoison l') := by
  rw [← Val.any_hasPoison, ← Val.any_hasPoison, ← Val.any_hasPoison, List.any_append]

private theorem eq_base {t : Ty} (ht : wf t = true) {a b : Val} (h : Sem.Refines a b)
    (hp : a.hasPoison = false) (hy : a.hasTy t = true)
    (hagg : ∀ as bs, a = .agg as → b = .agg bs → Sem.RefinesList as bs → as = bs) : a = b := by
  cases h with
  | poison => simp [Val.hasPoison] at hp
  | int | bool | ptr | empty => rfl
  | mem => cases t <;> simp_all [Val.hasTy, wf]
  | tuple => cases t <;> simp_all [Val.hasTy, wf]
  | blob => cases t <;> simp_all [Val.hasTy, wf]
  | agg hl => rw [hagg _ _ rfl rfl hl]

mutual
/-- A poison-free value of a well-formed shape is refined only by itself. -/
theorem ecf_refines_eq : (t : Ty) → wf t = true → {a b : Val} → Sem.Refines a b →
    a.hasPoison = false → a.hasTy t = true → a = b
  | .agg fs n, ht, _, _, h, hp, hy => eq_base ht h hp hy fun as bs ha hb hl => by
      subst ha hb
      simp only [Val.hasPoison] at hp
      simp only [Val.hasTy] at hy
      exact ecf_refinesList_eq fs n 0 ht hl hp hy
  | .str, ht, _, _, h, hp, hy => eq_base ht h hp hy fun as bs ha hb hl => by
      subst ha hb
      obtain ⟨p, l, rfl, hpp, -⟩ := Val.hasTy_agg_str.1 hy
      rcases hl with _ | ⟨h1, _ | ⟨h2, h3⟩⟩
      cases h3; cases h2
      cases h1 <;> simp_all [Val.hasPoison, Val.anyPoison, Val.isPtrOrPoison]
  | .slice _, ht, _, _, h, hp, hy => eq_base ht h hp hy fun as bs ha hb hl => by
      subst ha hb
      obtain ⟨p, l, c, rfl, hpp, -⟩ := Val.hasTy_agg_slice.1 hy
      rcases hl with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, h4⟩⟩⟩
      cases h4; cases h3; cases h2
      cases h1 <;> simp_all [Val.hasPoison, Val.anyPoison, Val.isPtrOrPoison]
  | .int _, ht, _, _, h, hp, hy | .bool, ht, _, _, h, hp, hy | .ptr _, ht, _, _, h, hp, hy
  | .opaque _, ht, _, _, h, hp, hy | .empty, ht, _, _, h, hp, hy | .blob _, ht, _, _, h, hp, hy
  | .mem, ht, _, _, h, hp, hy | .tuple _, ht, _, _, h, hp, hy | .other, ht, _, _, h, hp, hy =>
    eq_base ht h hp hy fun _ _ ha _ _ => by subst ha; simp [Val.hasTy] at hy
theorem ecf_refinesList_eq : (fs : List (Nat × Ty)) → (n s : Nat) → wfFields fs n s = true →
    {as bs : List Val} → Sem.RefinesList as bs → Val.anyPoison as = false →
    Val.hasTyList as (fs.map (·.2)) = true → as = bs
  | [], _, _, _, _, _, .nil, _, _ => rfl
  | [], _, _, _, _, _, .cons _ _, _, hy => by simp [Val.hasTyList] at hy
  | _ :: _, _, _, _, _, _, .nil, _, hy => by simp [Val.hasTyList] at hy
  | (_, t) :: fs, n, _, hw, _, _, .cons h hl, hp, hy => by
    simp only [wfFields, Bool.and_eq_true] at hw
    simp only [Val.anyPoison, Bool.or_eq_false_iff] at hp
    simp only [List.map_cons, Val.hasTyList, Bool.and_eq_true] at hy
    rw [ecf_refines_eq t hw.1.2 h hp.1 hy.1, ecf_refinesList_eq fs n _ hw.2 hl hp.2 hy.2]
end

mutual
/-- The register pieces of a poison-free value are poison-free. -/
theorem ecf_leafVals_np : (t : Ty) → wf t = true → {v : Val} → v.hasPoison = false →
    v.hasTy t = true → Val.anyPoison (leafVals t v) = false
  | .int _, _, v, hp, hy | .bool, _, v, hp, hy | .ptr _, _, v, hp, hy | .opaque _, _, v, hp, hy => by
    rw [leafVals_atom rfl, Val.retype_of_hasTy hy]
    simp [Val.anyPoison, hp]
  | .empty, _, _, _, _ => rfl
  | .agg fs n, hw, v, hp, hy => by
    cases v with
    | agg vs =>
      simp only [Val.hasPoison] at hp
      simp only [Val.hasTy] at hy
      exact ecf_leafValsFields_np fs vs n 0 hw hp hy
    | poison => simp [Val.hasPoison] at hp
    | _ => simp [Val.hasTy] at hy
  | .str, _, v, hp, hy => by
    cases v with
    | agg vs =>
      obtain ⟨p, l, rfl, hpp, -⟩ := Val.hasTy_agg_str.1 hy
      cases p <;> simp_all [leafVals, Val.retype, Val.hasPoison, Val.anyPoison, Val.isPtrOrPoison]
    | poison => simp [Val.hasPoison] at hp
    | _ => simp [Val.hasTy] at hy
  | .slice _, _, v, hp, hy => by
    cases v with
    | agg vs =>
      obtain ⟨p, l, c, rfl, hpp, -⟩ := Val.hasTy_agg_slice.1 hy
      cases p <;> simp_all [leafVals, Val.retype, Val.hasPoison, Val.anyPoison, Val.isPtrOrPoison]
    | poison => simp [Val.hasPoison] at hp
    | _ => simp [Val.hasTy] at hy
  | .blob _, h, _, _, _ | .mem, h, _, _, _ | .tuple _, h, _, _, _ | .other, h, _, _, _ => nomatch h
theorem ecf_leafValsFields_np : (fs : List (Nat × Ty)) → (vs : List Val) → (n s : Nat) →
    wfFields fs n s = true → Val.anyPoison vs = false → Val.hasTyList vs (fs.map (·.2)) = true →
    Val.anyPoison (leafValsFields fs vs) = false
  | [], _, _, _, _, _, _ => rfl
  | _ :: _, [], _, _, _, _, hy => by simp [Val.hasTyList] at hy
  | (o, t) :: fs, v :: vs, n, s, hw, hp, hy => by
    simp only [wfFields, Bool.and_eq_true] at hw
    simp only [Val.anyPoison, Bool.or_eq_false_iff] at hp
    simp only [List.map_cons, Val.hasTyList, Bool.and_eq_true] at hy
    rw [leafValsFields_cons, Val.retype_of_hasTy hy.1, ecf_anyPoison_append,
      ecf_leafVals_np t hw.1.2 hp.1 hy.1, ecf_leafValsFields_np fs vs n _ hw.2 hp.2 hy.2]
    rfl
end

/-! ## `goResults` of the source's results and of their pieces -/

/-- The `goResults` entry of a result. -/
abbrev ecfOut (tabs : Tables) (p : ABIParam) : Option AuxRef × Ty × Nat :=
  (p.name, tabs.ty p.type, p.regs.size)

/-- The facts of the `v1` fragment about one result. -/
def ecfReg (tabs : Tables) (p : ABIParam) : Prop :=
  p.regs.isEmpty = false ∧ wf (tabs.ty p.type) = true ∧ (leaves (tabs.ty p.type)).length = p.regs.size

theorem ecf_reg_of {tabs : Tables} {ps : List ABIParam} (h : regParamsOK tabs ps = true) :
    ∀ p ∈ ps, ecfReg tabs p := by
  intro p hp
  have := List.all_eq_true.1 h p hp
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- `decode (encode t r) 0 t = r` for the results. -/
theorem ecf_decode_encode {tabs : Tables} :
    {ps : List ABIParam} → {rs : List Val} →
      List.Forall₂ (fun (p : ABIParam) (r : Val) => r.hasTy (tabs.ty p.type) = true) ps rs →
      (∀ p ∈ ps, ecfReg tabs p) → Val.anyPoison rs = false →
      (((rs.zip (ps.map (ecfOut tabs))).map fun (v, (_, t, _)) => encode t v).zip
        (ps.map (ecfOut tabs))).map (fun (bs, (_, t, _)) => decode bs 0 t) = rs
  | _, _, .nil, _, _ => rfl
  | p :: ps, r :: rs, .cons hr hf, hreg, hp => by
    simp only [Val.anyPoison, Bool.or_eq_false_iff] at hp
    simp only [List.map_cons, List.zip_cons_cons, List.cons.injEq]
    have hw := (hreg p List.mem_cons_self).2.1
    exact ⟨(ecf_refines_eq _ hw (roundtrip hw hr) hp.1 hr).symm,
      ecf_decode_encode hf (fun q hq => hreg q (List.mem_cons_of_mem _ hq)) hp.2⟩

theorem ecf_forall₂_length {α β : Type} {R : α → β → Prop} :
    {l : List α} → {l' : List β} → List.Forall₂ R l l' → l'.length = l.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => congrArg (· + 1) (ecf_forall₂_length h)

theorem ecf_all_hasTy {tabs : Tables} :
    {ps : List ABIParam} → {rs : List Val} →
      List.Forall₂ (fun (p : ABIParam) (r : Val) => r.hasTy (tabs.ty p.type) = true) ps rs →
      ((rs.zip (ps.map (ecfOut tabs))).all fun (v, (_, t, _)) => v.hasTy t) = true
  | _, _, .nil => rfl
  | _, _, .cons hr hf => by
    simp only [List.map_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true]
    exact ⟨hr, ecf_all_hasTy hf⟩

/-- **The source's `goResults`**: the Go-typed path gives the results back. -/
theorem ecf_goResults_src {tabs : Tables} {ps : List ABIParam} {rs : List Val}
    {outs : Array (Option AuxRef × Ty × Nat)} (houts : outs.toList = ps.map (ecfOut tabs))
    (hf : List.Forall₂ (fun (p : ABIParam) (r : Val) => r.hasTy (tabs.ty p.type) = true) ps rs)
    (hreg : ∀ p ∈ ps, ecfReg tabs p) (hp : Val.anyPoison rs = false) (act : Nat) (m : Mem) :
    goResults outs act rs m = .ok rs := by
  unfold goResults
  dsimp only
  rw [houts, ecf_all_hasTy hf, ecf_forall₂_length hf, List.length_map, beq_self_eq_true,
    Bool.true_and]
  simp only [↓reduceIte]
  show (if _ then _ else _) = _
  rw [ecf_decode_encode hf hreg hp, Val.any_hasPoison, hp]
  rfl


/-- The register pieces of the results. -/
abbrev ecfPieces (tabs : Tables) (ps : List ABIParam) (rs : List Val) : List Val :=
  (ps.zip rs).flatMap fun (p, r) => leafVals (tabs.ty p.type) r

theorem ecf_pieces_np {tabs : Tables} :
    {ps : List ABIParam} → {rs : List Val} →
      List.Forall₂ (fun (p : ABIParam) (r : Val) => r.hasTy (tabs.ty p.type) = true) ps rs →
      (∀ p ∈ ps, ecfReg tabs p) → Val.anyPoison rs = false → Val.anyPoison (ecfPieces tabs ps rs) = false
  | _, _, .nil, _, _ => rfl
  | p :: ps, r :: rs, .cons hr hf, hreg, hp => by
    simp only [Val.anyPoison, Bool.or_eq_false_iff] at hp
    simp only [ecfPieces, List.zip_cons_cons, List.flatMap_cons]
    rw [ecf_anyPoison_append, ecf_leafVals_np _ (hreg p List.mem_cons_self).2.1 hp.1 hr,
      ecf_pieces_np hf (fun q hq => hreg q (List.mem_cons_of_mem _ hq)) hp.2]
    rfl

/-! ## The target's pieces: retyped at their registers' shapes -/

private theorem ecf_ofNat_add_eq {x : BitVec 64} {base r : Nat} (h : base + r = x.toNat) :
    BitVec.ofNat 64 base + BitVec.ofNat 64 r = x := by
  rw [BitVec.ofNat_add_ofNat, h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The pointer at an address has that address. -/
private theorem ecf_addr_ofAddr (x : BitVec 64) : (Ptr.ofAddr x).addr? = some x := by
  have hx : x.toNat < 18446744073709551616 := x.isLt
  unfold Ptr.ofAddr
  dsimp only
  split
  · simp [Ptr.addr?, Blk.base?]
  · split
    · simp only [Ptr.addr?, Blk.base?, Option.map_some, Option.some.injEq]
      apply ecf_ofNat_add_eq
      omega
    · split <;> simp only [Ptr.addr?, Blk.base?, Option.map_some, Option.some.injEq] <;>
        apply ecf_ofNat_add_eq <;> simp only [beq_iff_eq] at * <;> omega

/-- A poison-free piece of shape `lt` retyped at a register shape `rt` holding it: itself, or
(a 64-bit integer in a pointer register) the pointer at its address. -/
theorem ecf_retype_reg {rt lt : Ty} (h : regShapeOK rt lt = true) {p : Val}
    (hy : p.hasTy lt = true) (hp : p.hasPoison = false) :
    p.retype rt = p ∨ ∃ a, lt = .int .w64 ∧ p = .int .w64 a ∧ p.retype rt = .ptr (Ptr.ofAddr a) := by
  unfold regShapeOK at h
  cases hb : Ty.beq rt lt with
  | true => rw [Ty.eq_of_beq hb]; exact .inl (Val.retype_of_hasTy hy)
  | false =>
    rw [hb, Bool.false_or] at h
    split at h
    · cases p with
      | ptr q => exact .inl rfl
      | poison => simp [Val.hasPoison] at hp
      | _ => simp [Val.hasTy] at hy
    · cases p with
      | ptr q => exact .inl rfl
      | int w a =>
        simp only [Val.hasTy, beq_iff_eq] at hy
        subst hy
        exact .inr ⟨a, rfl, rfl, rfl⟩
      | poison => simp [Val.hasPoison] at hp
      | _ => simp [Val.hasTy] at hy
    · cases h

theorem ecf_retype_reg_np {rt lt : Ty} (h : regShapeOK rt lt = true) {p : Val}
    (hy : p.hasTy lt = true) (hp : p.hasPoison = false) : (p.retype rt).hasPoison = false := by
  rcases ecf_retype_reg h hy hp with e | ⟨a, -, -, e⟩
  · rw [e]; exact hp
  · rw [e]; rfl

/-- The leaf shape decodes a retyped piece's encoding as the piece. -/
theorem ecf_decode_reg {rt lt : Ty} (h : regShapeOK rt lt = true) (hl : atom lt = true) {p : Val}
    (hy : p.hasTy lt = true) (hp : p.hasPoison = false) :
    decode (encode lt (p.retype rt)) 0 lt = p := by
  rcases ecf_retype_reg h hy hp with e | ⟨a, rfl, rfl, e⟩
  · rw [e]; exact decode_encode_atom lt p hl hy
  · rw [e]
    show decodeInt .w64 ((ptrBytes (Ptr.ofAddr a)).extract 0 (0 + 8)) = .int .w64 a
    rw [Array.extract_eq_self_of_le (by simp [ptrBytes])]
    unfold decodeInt
    rw [bytesNat?_ptrBytes, bytesPtr?_ptrBytes]
    simp only [ecf_addr_ofAddr]

/-- Decoding the leaves of a buffer assembled from retyped pieces gives the pieces back. -/
theorem ecf_foldl_decode_reg : {ps : List Val} → {L : List (Nat × Ty)} →
    List.Forall₂ (fun p (l : Nat × Ty) => p.hasTy l.2 = true) ps L → Val.anyPoison ps = false →
    {rts : List Ty} → List.Forall₂ (fun lt rt => regShapeOK rt lt = true) (L.map (·.2)) rts →
    (buf : Array Byte) → (n s : Nat) → wfFields L n s = true → (∀ x ∈ L, atom x.2 = true) →
    buf.size = n →
    L.map (fun x => decode ((L.zip (List.zipWith Val.retype rts ps)).foldl ostep buf) x.1 x.2) = ps
  | _, _, .nil, _, _, _, _, _, _, _, _, _ => rfl
  | p :: ps, (o, lt) :: L, .cons hp hf, hnp, rts, hrts, buf, n, s, hw, ha, hb => by
    rw [List.map_cons] at hrts
    cases hrts with
    | @cons _ rt _ rts hr hrs =>
      simp only [Val.anyPoison, Bool.or_eq_false_iff] at hnp
      simp only [wfFields, Bool.and_eq_true, decide_eq_true_eq] at hw
      have hle := wfFields_le hw.2
      have hat := ha (o, lt) List.mem_cons_self
      have hb1 : (ostep buf ((o, lt), p.retype rt)).size = n := by rw [ostep, putBytes_size, hb]
      simp only [List.zipWith_cons_cons, List.zip_cons_cons, List.foldl_cons, List.map_cons]
      have hhead : decode ((L.zip (List.zipWith Val.retype rts ps)).foldl ostep
          (ostep buf ((o, lt), p.retype rt))) o lt = p := by
        have hag : Agree ((L.zip (List.zipWith Val.retype rts ps)).foldl ostep
            (ostep buf ((o, lt), p.retype rt))) o (encode lt (p.retype rt)) 0 lt.size := by
          intro k hk
          rw [foldl_ostep_lt L _ _ n (o + lt.size) (o + k) hw.2 hb1 (by omega)]
          show (putBytes buf o (encode lt (p.retype rt)))[o + k]? = (encode lt (p.retype rt))[0 + k]?
          exact putBytes_agree (by rw [encode_size, hb]; omega) k (by rw [encode_size]; exact hk)
        rw [decode_agree lt (wf_atom hat) hag]
        exact ecf_decode_reg hr hat hp hnp.1
      rw [hhead, ecf_foldl_decode_reg hf hnp.2 hrs _ n _ hw.2
        (fun x hx => ha x (List.mem_cons_of_mem _ hx)) hb1]

/-- Assembling a value's pieces, retyped at registers holding them, gives the value back. -/
theorem ecf_ofPieces_reg {t : Ty} (hw : wf t = true) {r : Val} (hr : r.hasTy t = true)
    (hp : r.hasPoison = false) {rts : List Ty}
    (hrts : List.Forall₂ (fun lt rt => regShapeOK rt lt = true) ((leaves t).map (·.2)) rts) :
    ofPieces t (List.zipWith Val.retype rts (leafVals t r)) = r := by
  rw [ofPieces_eq, ← build_decode_aux t _ 0 hw]
  have := ecf_foldl_decode_reg (leafVals_hasTy hw) (ecf_leafVals_np t hw hp hr) hrts
    (Array.replicate t.size .poison) t.size 0 (leaves_wfFields hw) (fun x hx => (mem_leaves hw hx).2)
    (by simp)
  simp only [Nat.zero_add]
  rw [this]
  exact (ecf_refines_eq t hw (build_leafVals hw hr) hp hr).symm

theorem ecf_forall₂_snd {xs : List Val} :
    {ls : List (Nat × Ty)} → List.Forall₂ (fun p (l : Nat × Ty) => p.hasTy l.2 = true) xs ls →
      List.Forall₂ (fun p (t : Ty) => p.hasTy t = true) xs (ls.map (·.2))
  | _, .nil => .nil
  | _, .cons h t => .cons h (ecf_forall₂_snd t)

/-- The pieces have the leaf shapes. -/
theorem ecf_pieces_hasTy {tabs : Tables} :
    {ps : List ABIParam} → {rs : List Val} → rs.length = ps.length → (∀ p ∈ ps, ecfReg tabs p) →
      List.Forall₂ (fun p (t : Ty) => p.hasTy t = true) (ecfPieces tabs ps rs) (leafTys tabs ps)
  | [], [], _, _ => .nil
  | _ :: _, [], hl, _ | [], _ :: _, hl, _ => by simp at hl
  | p :: ps, r :: rs, hl, hreg => by
    simp only [ecfPieces, leafTys, List.zip_cons_cons, List.flatMap_cons]
    exact List.Forall₂.append (ecf_forall₂_snd (leafVals_hasTy (hreg p List.mem_cons_self).2.1))
      (ecf_pieces_hasTy (by simpa using hl) (fun q hq => hreg q (List.mem_cons_of_mem _ hq)))

/-- The register pieces of the results, retyped at the register shapes `rts`. -/
abbrev ecfRegs (tabs : Tables) (ps : List ABIParam) (rs : List Val) (rts : List Ty) : List Val :=
  List.zipWith Val.retype rts (ecfPieces tabs ps rs)

theorem ecf_forall₂_append_left {α β : Type} {R : α → β → Prop} : {A B : List α} → {l : List β} →
    List.Forall₂ R (A ++ B) l → ∃ l1 l2, l = l1 ++ l2 ∧ List.Forall₂ R A l1 ∧ List.Forall₂ R B l2
  | [], _, _, h => ⟨[], _, rfl, .nil, h⟩
  | _ :: _, _, _, .cons h t => by
    obtain ⟨l1, l2, rfl, h1, h2⟩ := ecf_forall₂_append_left t
    exact ⟨_ :: l1, l2, rfl, .cons h h1, h2⟩

theorem ecf_leafTys_cons (tabs : Tables) (p : ABIParam) (ps : List ABIParam) :
    leafTys tabs (p :: ps) = (leaves (tabs.ty p.type)).map (·.2) ++ leafTys tabs ps := by
  simp only [leafTys, List.flatMap_cons]

/-- The retyped pieces of the first result, then of the others. -/
theorem ecf_regs_cons {tabs : Tables} {p : ABIParam} {ps : List ABIParam} {r : Val} {rs : List Val}
    (hw : wf (tabs.ty p.type) = true) {rts : List Ty}
    (h : List.Forall₂ (fun lt rt => regShapeOK rt lt = true) (leafTys tabs (p :: ps)) rts) :
    ∃ r1 r2,
      List.Forall₂ (fun lt rt => regShapeOK rt lt = true) ((leaves (tabs.ty p.type)).map (·.2)) r1 ∧
      List.Forall₂ (fun lt rt => regShapeOK rt lt = true) (leafTys tabs ps) r2 ∧
      ecfRegs tabs (p :: ps) (r :: rs) rts =
        List.zipWith Val.retype r1 (leafVals (tabs.ty p.type) r) ++ ecfRegs tabs ps rs r2 := by
  rw [ecf_leafTys_cons] at h
  obtain ⟨r1, r2, rfl, h1, h2⟩ := ecf_forall₂_append_left h
  refine ⟨r1, r2, h1, h2, ?_⟩
  simp only [ecfRegs, ecfPieces, List.zip_cons_cons, List.flatMap_cons]
  rw [List.zipWith_append (by rw [ecf_forall₂_length h1, List.length_map, leafVals_length hw])]

theorem ecf_regs_length {tabs : Tables} {ps : List ABIParam} {rs : List Val} {rts : List Ty}
    (hl : rs.length = ps.length) (hreg : ∀ p ∈ ps, ecfReg tabs p)
    (h : List.Forall₂ (fun lt rt => regShapeOK rt lt = true) (leafTys tabs ps) rts) :
    (ecfRegs tabs ps rs rts).length = (ecfPieces tabs ps rs).length := by
  rw [List.length_zipWith, ecf_forall₂_length h, ecf_forall₂_length (ecf_pieces_hasTy hl hreg),
    Nat.min_self]

theorem ecf_zipWith_np : {P : List Val} → {L : List Ty} →
    List.Forall₂ (fun p (t : Ty) => p.hasTy t = true) P L → Val.anyPoison P = false →
    {rts : List Ty} → List.Forall₂ (fun lt rt => regShapeOK rt lt = true) L rts →
    Val.anyPoison (List.zipWith Val.retype rts P) = false
  | _, _, .nil, _, _, .nil => rfl
  | _ :: _, _ :: _, .cons hy hf, hp, _ :: _, .cons hr hrs => by
    simp only [Val.anyPoison, Bool.or_eq_false_iff] at hp
    simp only [List.zipWith_cons_cons, Val.anyPoison, Bool.or_eq_false_iff]
    exact ⟨ecf_retype_reg_np hr hy hp.1, ecf_zipWith_np hf hp.2 hrs⟩

/-- The retyped pieces of poison-free results are poison-free. -/
theorem ecf_regs_np {tabs : Tables} {ps : List ABIParam} {rs : List Val}
    (hf : List.Forall₂ (fun (p : ABIParam) (r : Val) => r.hasTy (tabs.ty p.type) = true) ps rs)
    (hreg : ∀ p ∈ ps, ecfReg tabs p) (hp : Val.anyPoison rs = false) {rts : List Ty}
    (h : List.Forall₂ (fun lt rt => regShapeOK rt lt = true) (leafTys tabs ps) rts) :
    Val.anyPoison (ecfRegs tabs ps rs rts) = false :=
  ecf_zipWith_np (ecf_pieces_hasTy (ecf_forall₂_length hf) hreg) (ecf_pieces_np hf hreg hp) h

/-- **The register path of `goResults`** on the retyped pieces: each result back. -/
theorem ecf_post_reg {tabs : Tables} (act : Nat) (m : Mem) :
    {ps : List ABIParam} → {rs : List Val} →
      List.Forall₂ (fun (p : ABIParam) (r : Val) => r.hasTy (tabs.ty p.type) = true) ps rs →
      (∀ p ∈ ps, ecfReg tabs p) → Val.anyPoison rs = false → {rts : List Ty} →
      List.Forall₂ (fun lt rt => regShapeOK rt lt = true) (leafTys tabs ps) rts →
      ∃ bufs, goResults.post act m (ecfRegs tabs ps rs rts) (ps.map (ecfOut tabs)) = .ok bufs ∧
        (bufs.zip (ps.map (ecfOut tabs))).map (fun (bs, (_, t, _)) => decode bs 0 t) = rs
  | _, _, .nil, _, _, _, _ => ⟨[], by
      simp only [ecfRegs, ecfPieces, List.zip_nil_left, List.flatMap_nil, List.zipWith_nil_right]
      unfold goResults.post; rfl, rfl⟩
  | p :: ps, r :: rs, .cons hr hf, hreg, hp, rts, hrts => by
    simp only [Val.anyPoison, Bool.or_eq_false_iff] at hp
    obtain ⟨hne, hw, hlen⟩ := hreg p List.mem_cons_self
    obtain ⟨r1, r2, h1, h2, hQ⟩ := ecf_regs_cons (rs := rs) (r := r) hw hrts
    obtain ⟨bufs, hb, hd⟩ :=
      ecf_post_reg act m hf (fun q hq => hreg q (List.mem_cons_of_mem _ hq)) hp.2 h2
    have hk : p.regs.size ≠ 0 := by
      intro h0; rw [Array.isEmpty_iff_size_eq_zero.2 h0] at hne; cases hne
    have hlv : (List.zipWith Val.retype r1 (leafVals (tabs.ty p.type) r)).length = p.regs.size := by
      rw [List.length_zipWith, leafVals_length hw, ecf_forall₂_length h1, List.length_map,
        Nat.min_self, hlen]
    refine ⟨((leaves (tabs.ty p.type)).zip (List.zipWith Val.retype r1 (leafVals (tabs.ty p.type) r))).foldl
      (fun buf ((o, lt), v) => putBytes buf o (encode lt v))
      (Array.replicate (tabs.ty p.type).size Byte.poison) :: bufs, ?_, ?_⟩
    · rw [hQ, List.map_cons]
      unfold goResults.post
      simp only [beq_iff_eq, hk, ↓reduceIte, hlen, bne_self_eq_false, List.length_append,
        Bool.false_or, decide_eq_true_eq]
      have hnl : ¬ (List.zipWith Val.retype r1 (leafVals (tabs.ty p.type) r)).length +
          (ecfRegs tabs ps rs r2).length < p.regs.size := by omega
      simp only [hnl, ↓reduceIte]
      rw [List.take_left' hlv, List.drop_left' hlv, hb]
      rfl
    · simp only [List.map_cons, List.zip_cons_cons, List.cons.injEq]
      refine ⟨?_, hd⟩
      show ofPieces (tabs.ty p.type) (List.zipWith Val.retype r1 (leafVals (tabs.ty p.type) r)) = r
      exact ecf_ofPieces_reg hw hr hp.1 h1

theorem ecf_atom_agg {l : Ty} (hl : atom l = true) {x : Val} (hx : x.hasTy l = true)
    {fs : List (Nat × Ty)} {n : Nat} (hxa : x.hasTy (.agg fs n) = true) (hp : x.hasPoison = false) :
    False := by
  cases x with
  | poison => simp [Val.hasPoison] at hp
  | agg vs => cases l <;> simp [Val.hasTy, atom] at hx hl
  | _ => simp [Val.hasTy] at hxa

theorem ecf_forall₂_single {x : Val} {rt : Ty} {L : List (Nat × Ty)}
    (h1 : List.Forall₂ (fun p (l : Nat × Ty) => p.hasTy l.2 = true) [x] L)
    (h2 : List.Forall₂ (fun lt rt => regShapeOK rt lt = true) (L.map (·.2)) [rt]) :
    ∃ l ∈ L, x.hasTy l.2 = true ∧ regShapeOK rt l.2 = true := by
  cases h1 with
  | cons h t =>
    cases t
    simp only [List.map_cons, List.map_nil] at h2
    cases h2 with
    | cons h' _ => exact ⟨_, List.mem_singleton_self _, h, h'⟩

/-- A result whose single register piece, retyped at its register, has the result's shape: the
result's shape decodes that piece's encoding as the result. -/
theorem ecf_single_reg {t : Ty} (hw : wf t = true) {r x : Val} (hr : r.hasTy t = true)
    (hp : r.hasPoison = false) (hl : leafVals t r = [x]) {rt : Ty}
    (hrt : List.Forall₂ (fun lt rt => regShapeOK rt lt = true) ((leaves t).map (·.2)) [rt])
    (hx : (x.retype rt).hasTy t = true) : decode (encode t (x.retype rt)) 0 t = r := by
  have hxp : x.hasPoison = false := by
    have := ecf_leafVals_np t hw hp hr
    rw [hl] at this
    simpa [Val.anyPoison] using this
  have hF := leafVals_hasTy (v := r) hw
  rw [hl] at hF
  obtain ⟨l, hlm, hxl, hrl⟩ := ecf_forall₂_single hF hrt
  have hla := mem_leaves_atom t hw l hlm
  cases t with
  | int | bool | ptr | «opaque» =>
    rw [leafVals_atom rfl, List.cons.injEq] at hl
    rw [leaves_atom rfl, List.mem_singleton] at hlm
    subst hlm
    rw [← hl.1, Val.retype_of_hasTy hr]
    exact ecf_decode_reg hrl rfl hr hp
  | agg fs n =>
    rcases ecf_retype_reg hrl hxl hxp with e | ⟨a, -, -, e⟩
    · rw [e] at hx; exact (ecf_atom_agg hla hxl hx hxp).elim
    · rw [e] at hx; simp [Val.hasTy] at hx
  | empty => simp [leafVals] at hl
  | str | slice => cases r <;> simp [leafVals] at hl
  | blob | mem | tuple | other => simp [wf] at hw

theorem ecf_pieces_length_ge {tabs : Tables} :
    {ps : List ABIParam} → {rs : List Val} →
      List.Forall₂ (fun (p : ABIParam) (r : Val) => r.hasTy (tabs.ty p.type) = true) ps rs →
      (∀ p ∈ ps, ecfReg tabs p) → ps.length ≤ (ecfPieces tabs ps rs).length
  | _, _, .nil, _ => Nat.le_refl _
  | p :: ps, r :: rs, .cons _ hf, hreg => by
    obtain ⟨hne, hw, hlen⟩ := hreg p List.mem_cons_self
    have hk : p.regs.size ≠ 0 := by
      intro h0; rw [Array.isEmpty_iff_size_eq_zero.2 h0] at hne; cases hne
    have := ecf_pieces_length_ge hf (fun q hq => hreg q (List.mem_cons_of_mem _ hq))
    simp only [ecfPieces, List.zip_cons_cons, List.flatMap_cons, List.length_append,
      List.length_cons] at this ⊢
    rw [leafVals_length hw, hlen]
    omega

/-- The Go-typed path on the retyped pieces: each result is decoded back. -/
theorem ecf_pre_reg {tabs : Tables} :
    {ps : List ABIParam} → {rs : List Val} →
      List.Forall₂ (fun (p : ABIParam) (r : Val) => r.hasTy (tabs.ty p.type) = true) ps rs →
      (∀ p ∈ ps, ecfReg tabs p) → Val.anyPoison rs = false → {rts : List Ty} →
      List.Forall₂ (fun lt rt => regShapeOK rt lt = true) (leafTys tabs ps) rts →
      (ecfRegs tabs ps rs rts).length = ps.length →
      (((ecfRegs tabs ps rs rts).zip (ps.map (ecfOut tabs))).all fun (v, (_, t, _)) => v.hasTy t) = true →
      ((((ecfRegs tabs ps rs rts).zip (ps.map (ecfOut tabs))).map fun (v, (_, t, _)) => encode t v).zip
        (ps.map (ecfOut tabs))).map (fun (bs, (_, t, _)) => decode bs 0 t) = rs
  | _, _, .nil, _, _, _, _, _, _ => by simp only [List.map_nil, List.zip_nil_right]
  | p :: ps, r :: rs, .cons hr hf, hreg, hp, rts, hrts, hl, ha => by
    simp only [Val.anyPoison, Bool.or_eq_false_iff] at hp
    obtain ⟨hne, hw, hlen⟩ := hreg p List.mem_cons_self
    have hk : p.regs.size ≠ 0 := by
      intro h0; rw [Array.isEmpty_iff_size_eq_zero.2 h0] at hne; cases hne
    have hreg' : ∀ q ∈ ps, ecfReg tabs q := fun q hq => hreg q (List.mem_cons_of_mem _ hq)
    obtain ⟨r1, r2, h1, h2, hQ⟩ := ecf_regs_cons (rs := rs) (r := r) hw hrts
    have hge := ecf_pieces_length_ge hf hreg'
    have hl2 := ecf_regs_length (ecf_forall₂_length hf) hreg' h2
    have hz1 : (List.zipWith Val.retype r1 (leafVals (tabs.ty p.type) r)).length = p.regs.size := by
      rw [List.length_zipWith, leafVals_length hw, ecf_forall₂_length h1, List.length_map,
        Nat.min_self, hlen]
    rw [hQ] at hl ha ⊢
    rw [List.length_append, List.length_cons] at hl
    have htl : (ecfRegs tabs ps rs r2).length = ps.length := by omega
    have h1len : r1.length = 1 := by
      rw [ecf_forall₂_length h1, List.length_map, hlen]; omega
    have hxlen : (leafVals (tabs.ty p.type) r).length = 1 := by
      rw [leafVals_length hw, hlen]; omega
    obtain ⟨rt, rfl⟩ := List.length_eq_one_iff.1 h1len
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 hxlen
    rw [hx] at ha ⊢
    simp only [List.zipWith_cons_cons, List.zipWith_nil_left, List.cons_append, List.nil_append,
      List.map_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at ha ⊢
    rw [List.cons.injEq]
    exact ⟨ecf_single_reg hw hr hp.1 hx h1 ha.1, ecf_pre_reg hf hreg' hp.2 h2 htl ha.2⟩

/-- **The target's `goResults`** on the retyped pieces: the results. -/
theorem ecf_goResults_reg {tabs : Tables} {ps : List ABIParam} {rs : List Val}
    {outs : Array (Option AuxRef × Ty × Nat)} (houts : outs.toList = ps.map (ecfOut tabs))
    (hf : List.Forall₂ (fun (p : ABIParam) (r : Val) => r.hasTy (tabs.ty p.type) = true) ps rs)
    (hreg : ∀ p ∈ ps, ecfReg tabs p) (hp : Val.anyPoison rs = false) {rts : List Ty}
    (hrts : List.Forall₂ (fun lt rt => regShapeOK rt lt = true) (leafTys tabs ps) rts)
    (act : Nat) (m : Mem) :
    goResults outs act (ecfRegs tabs ps rs rts) m = .ok rs := by
  unfold goResults
  dsimp only
  rw [houts]
  by_cases hpre : ((ecfRegs tabs ps rs rts).length == (ps.map (ecfOut tabs)).length &&
      ((ecfRegs tabs ps rs rts).zip (ps.map (ecfOut tabs))).all fun (v, (_, t, _)) => v.hasTy t) = true
  · simp only [hpre, ↓reduceIte]
    simp only [Bool.and_eq_true, beq_iff_eq, List.length_map] at hpre
    show (if _ then _ else _) = _
    rw [ecf_pre_reg hf hreg hp hrts hpre.1 hpre.2, Val.any_hasPoison, hp]
    rfl
  · simp only [hpre, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨bufs, hb, hd⟩ := ecf_post_reg act m hf hreg hp hrts
    rw [hb]
    show (if _ then _ else _) = _
    rw [hd, Val.any_hasPoison, hp]
    rfl

/-! ## `finish` -/

theorem ecf_outs (tabs : Tables) (f : Func) :
    (Ctx.make tabs f).outs.toList = (ownOuts tabs f).map (ecfOut tabs) := by
  simp [Ctx.make, ownOuts]

/-- **`finish` relates `ecRR` outcomes.** -/
theorem finish_ecRR {tabs : Tables} {f : Func} (hreg : regParamsOK tabs (ownOuts tabs f) = true) :
    ∀ rs m rs' m', ecRR tabs f rs m rs' m' →
      (finish (Ctx.make tabs f).outs 0 (.returned rs m)).Defined →
      OutcomeRefines 0 (finish (Ctx.make tabs f).outs 0 (.returned rs m))
        (finish (Ctx.make tabs f).outs 0 (.returned rs' m')) := by
  intro rs m rs' m' ⟨hf, rts, hrts, hP, hm⟩ hd
  have hreg' := ecf_reg_of hreg
  have hp : Val.anyPoison rs = false := by
    cases h : Val.anyPoison rs
    · rfl
    · simp only [finish, h, ↓reduceIte] at hd; exact hd.elim
  have hPp := ecf_regs_np hf hreg' hp hrts
  have hsrc : finish (Ctx.make tabs f).outs 0 (.returned rs m) = .returned rs (m.freeFrame 0) := by
    simp only [finish, hp, Bool.false_eq_true, ↓reduceIte,
      ecf_goResults_src (ecf_outs tabs f) hf hreg' hp 0 m]
  have hmid : finish (Ctx.make tabs f).outs 0 (.returned (ecfRegs tabs (ownOuts tabs f) rs rts) m) =
      .returned rs (m.freeFrame 0) := by
    simp only [finish, hPp, Bool.false_eq_true, ↓reduceIte,
      ecf_goResults_reg (ecf_outs tabs f) hf hreg' hp hrts 0 m]
  have h1 : OutcomeRefines 0 (finish (Ctx.make tabs f).outs 0 (.returned rs m))
      (finish (Ctx.make tabs f).outs 0 (.returned (ecfRegs tabs (ownOuts tabs f) rs rts) m)) := by
    rw [hsrc, hmid]; exact OutcomeRefines.refl trivial
  have h2 := finish_refines (outs := (Ctx.make tabs f).outs) (act := 0) (k := 0)
    (by rw [hmid]; trivial) (OutcomeRefines.returned hP hm)
  exact h1.trans h2

/-! ## The `Ret` control: a `MakeResult` -/

theorem ecf_valueTy (tabs : Tables) (v : Value) :
    valueTy (typeShapes tabs) (some v) = tabs.ty v.type := typeShapes_getD tabs v.type

/-- The results of a source `MakeResult` tuple have their shapes. -/
theorem ecf_hasTyPre_results {tabs : Tables} {mv : Val} :
    {ps : List ABIParam} → {rs : List Val} → {us : List Ty} → rs.length = ps.length →
      Val.hasTyPre (rs ++ [mv]) us = true → us.length = ps.length + 1 →
      ((ps.map (tabs.ty ·.type)).zip us).all (fun (a, b) => eqE b a) = true →
      List.Forall₂ (fun (p : ABIParam) (r : Val) => r.hasTy (tabs.ty p.type) = true) ps rs
  | [], [], _, _, _, _, _ => .nil
  | p :: ps, r :: rs, u :: us, hl, hy, hu, he => by
    simp only [List.cons_append, Val.hasTyPre, Bool.and_eq_true] at hy
    simp only [List.map_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at he
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl hu
    exact .cons (by rw [← eqE_hasTy he.1]; exact hy.1) (ecf_hasTyPre_results hl hy.2 hu he.2)
  | _ :: _, _ :: _, [], _, _, hu, _ => by simp at hu
  | [], _ :: _, _, hl, _, _, _ | _ :: _, [], _, hl, _, _, _ => by simp at hl

theorem ecf_refinesList_append_inv : {a b c : List Val} → Sem.RefinesList (a ++ b) c →
    ∃ c1 c2, c = c1 ++ c2 ∧ Sem.RefinesList a c1 ∧ Sem.RefinesList b c2
  | [], _, _, h => ⟨[], _, rfl, .nil, h⟩
  | _ :: _, _, _, .cons h t => by
    obtain ⟨c1, c2, rfl, h1, h2⟩ := ecf_refinesList_append_inv t
    exact ⟨_ :: c1, c2, rfl, .cons h h1, h2⟩

theorem ecf_retOf {P : List Val} (hp : Val.anyPoison P = false) (m : Mem) :
    retOf (.tuple (P ++ [.mem m])) = some (P, m) := by
  unfold retOf
  dsimp only
  rw [List.getLast?_concat, List.dropLast_concat]
  dsimp only
  split
  · next h =>
    obtain ⟨x, hx, hxp⟩ := List.any_eq_true.1 h
    have := List.any_eq_false.1 (by rw [Val.any_hasPoison]; exact hp) x hx
    cases x <;> simp_all [Val.hasPoison]
  · rfl

theorem ecf_retOf_inv {vs rs : List Val} {m : Mem} (h : retOf (.tuple vs) = some (rs, m)) :
    vs = rs ++ [.mem m] := by
  unfold retOf at h
  dsimp only at h
  split at h
  · next m0 hl =>
    split at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 hl
      rw [List.dropLast_concat]
  · cases h

theorem ecf_tupleOf {ts : List Ty} {t : Ty} (h : tupleOf ts t = true) :
    ∃ us, t = .tuple us ∧ us.length = ts.length + 1 ∧ (ts.zip us).all (fun (a, b) => eqE b a) = true ∧
      us.getLast? = some .mem := by
  unfold tupleOf at h
  split at h
  · next us =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    refine ⟨us, rfl, h.1.1, h.1.2, ?_⟩
    have h2 := h.2
    split at h2
    · next e => exact e
    · cases h2
  · cases h

theorem ecf_forall₂_regShape : {lts rts : List Ty} → lts.length = rts.length →
    (lts.zip rts).all (fun (lt, rt) => regShapeOK rt lt) = true →
    List.Forall₂ (fun lt rt => regShapeOK rt lt = true) lts rts
  | [], [], _, _ => .nil
  | _ :: _, _ :: _, hl, h => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h
    exact .cons h.1 (ecf_forall₂_regShape (by simpa using hl) h.2)
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => by simp at hl

theorem ecf_regTupleOf {lts : List Ty} {t : Ty} (h : regTupleOf lts t = true) :
    ∃ rts, t = .tuple (rts ++ [.mem]) ∧ List.Forall₂ (fun lt rt => regShapeOK rt lt = true) lts rts := by
  unfold regTupleOf at h
  split at h
  · next us =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hl, ha⟩, h2⟩ := h
    have hlast : us.getLast? = some .mem := by
      split at h2
      · next e => exact e
      · cases h2
    obtain ⟨rts, rfl⟩ := List.getLast?_eq_some_iff.1 hlast
    refine ⟨rts, rfl, ?_⟩
    rw [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hl
    have hz : lts.zip (rts ++ [Ty.mem]) = lts.zip rts := by
      conv => lhs; rw [← List.append_nil lts]
      rw [List.zip_append hl.symm, List.zip_nil_left, List.append_nil]
    rw [hz] at ha
    exact ecf_forall₂_regShape hl.symm ha
  · cases h

theorem ecf_retypePre_zip {t : Ty} {v : Val} : {rts : List Ty} → {P : List Val} →
    rts.length = P.length →
    Val.retypePre (rts ++ [t]) (P ++ [v]) = some (List.zipWith Val.retype rts P ++ [v.retype t])
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [List.cons_append, Val.retypePre, List.zipWith_cons_cons,
      ecf_retypePre_zip (by simpa using h), Option.map_some]
  | [], _ :: _, h | _ :: _, [], h => by simp at h

/-- The target's register tuple retypes the pieces at the register shapes. -/
theorem ecf_retype_tuple {rts : List Ty} {P : List Val} (h : rts.length = P.length) (m : Mem) :
    Val.retype (.tuple (rts ++ [.mem])) (.tuple (P ++ [.mem m])) =
      .tuple (List.zipWith Val.retype rts P ++ [.mem m]) := by
  show (match Val.retypePre (rts ++ [.mem]) (P ++ [.mem m]) with
    | some vs' => Val.tuple vs'
    | none => Val.poison) = _
  rw [ecf_retypePre_zip h]
  rfl

theorem ecf_not_invalidated {g : Func} {c : ID} {w : Value} (hw : g.value? c = some w)
    (hop : w.op ≠ .Invalid) : invalidated g c = false := by
  unfold invalidated
  rw [hw]
  simpa using hop

theorem ecc_cv_result {tabs : Tables} {f g : Func} {c : ID} {u : Value} (hu : f.value? c = some u)
    (hop : u.op = .MakeResult) (hinv : invalidated g c = false) (y : Val) :
    ecCv tabs f g c y = (convTuple tabs (ownOuts tabs f) y).retype (shapeOf (typeShapes tabs) g c) := by
  unfold ecCv
  simp only [hinv, hu, hop, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem ecf_convTuple {tabs : Tables} {ps : List ABIParam} {rs : List Val} (hl : rs.length = ps.length)
    (x : Val) : convTuple tabs ps (.tuple (rs ++ [x])) = .tuple (ecfPieces tabs ps rs ++ [x]) := by
  unfold convTuple
  dsimp only
  have hz : ps.zip (rs ++ [x]) = ps.zip rs := by
    conv => lhs; rw [← List.append_nil ps]
    rw [List.zip_append hl.symm, List.zip_nil_left, List.append_nil]
  rw [hz, List.drop_left' hl]

/-- **The `Ret` control of `expand calls`** (a converted `MakeResult`): the target returns the
register pieces of the source's results, retyped at the target `MakeResult`'s register shapes
(`regTupleOf`). Extra premise: the source's results are poison-free (else `finish` is stuck;
`CvBlock.ret` provides it). -/
theorem ret_result {tabs : Tables} {f g : Func} {c : ID} {u w : Value}
    (hu : f.value? c = some u) (hw : g.value? c = some w) (hop : u.op = .MakeResult)
    (hok : resultOK tabs (typeShapes tabs) f g u w = true)
    (hreg : regParamsOK tabs (ownOuts tabs f) = true) :
    ∀ y y', RegOK (Ctx.make tabs f) c y → Sem.Refines (ecCv tabs f g c y) y' →
      ∀ rs m, retOf y = some (rs, m) → Val.anyPoison rs = false →
        ∃ rs' m', retOf y' = some (rs', m') ∧ ecRR tabs f rs m rs' m' := by
  intro y y' hry hyy rs m hro hp
  have hreg' := ecf_reg_of hreg
  unfold resultOK at hok
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hwop, hn⟩, -⟩, -⟩, -⟩, -⟩, htup⟩, hrt⟩ := hok
  obtain ⟨us, hus, husl, hue, -⟩ := ecf_tupleOf htup
  obtain ⟨rts, hus', hrts⟩ := ecf_regTupleOf hrt
  -- the source's register
  obtain ⟨hty, hlen, -⟩ := hry
  rw [tys_of_value hu, Option.getD_some, ← ecf_valueTy, hus] at hty
  cases y with
  | tuple vs =>
    have hvs := hlen u vs hu hop rfl
    -- `vs = rs ++ [.mem m]`
    have hvs' : vs = rs ++ [.mem m] := ecf_retOf_inv hro
    subst hvs'
    have hrl : rs.length = (ownOuts tabs f).length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at hvs; omega
    have hF := ecf_hasTyPre_results (tabs := tabs) hrl hty (by rw [husl, List.length_map]) hue
    -- the conversion
    have hPt := ecf_pieces_hasTy (tabs := tabs) hrl hreg'
    have hlen' : rts.length = (ecfPieces tabs (ownOuts tabs f) rs).length :=
      (ecf_forall₂_length hrts).trans (ecf_forall₂_length hPt)
    rw [ecc_cv_result hu hop (ecf_not_invalidated hw (by rw [hwop]; decide)), ecf_convTuple hrl,
      shapeOf, hw, hus', ecf_retype_tuple hlen'] at hyy
    cases hyy with
    | tuple hl =>
      obtain ⟨c1, c2, rfl, h1, h2⟩ := ecf_refinesList_append_inv hl
      cases h2 with
      | cons hm hnil =>
        cases hnil
        cases hm with
        | mem hm =>
          have hQp := ecf_regs_np hF hreg' hp hrts
          exact ⟨c1, _, ecf_retOf ((h1.noPoison hQp).1) _, hF, rts, hrts, h1, hm⟩
  | _ => simp [retOf] at hro

end GoFV.Proof.EC

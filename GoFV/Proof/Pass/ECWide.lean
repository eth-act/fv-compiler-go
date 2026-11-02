import GoFV.Proof.Pass.ECStackRes
import GoFV.Proof.Pass.StructStoreMem

/-!
# `expand calls`: wide call results stored to memory, the memory (issue #28)

A register-assigned call result `x = SelectN [i] c` that is not SSA-able and only stored
(`Store {T} p x mem`) is stored leaf by leaf after `expand calls` (`rewriteWideSelectToStores`):
a chain of `Store {lt} (OffPtr [o] p) (SelectN [k] c)` on `mem`, one per leaf `(o, lt)` of `T`.

`ecw_split`: for a well-formed shape `t` and a value `v` of shape `t`, if the write of `encode t v`
at `q` succeeds on `M` and `M'` refines `M`, the writes of pieces refining `v`'s register pieces
(`leafVals t v`) at `q + o` succeed on `M'` and refine the whole write (padding is `poison` in
the source; `StructStore.write_poison_left`, `StructStore.write_putBytes`). Strings and slices
are encoded as their aggregates (`encode_asAgg`); a `poison` aggregate as an aggregate of
`poison`s.
-/

namespace GoFV.Proof.EC

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.ECCheck GoFV.Proof.ABI GoFV.Proof.CSE.Mem
  GoFV.Proof.StructStore GoFV.Proof.AtomSim

/-- The writes of the pieces `xs` at their leaves' offsets `L` from `q`. -/
def ecwLeafWrites (q : Ptr) (L : List (Nat × Ty)) (xs : List Val) : List (Ptr × Array Byte) :=
  (L.zip xs).map fun e => (q.add (BitVec.ofNat 64 e.1.1), encode e.1.2 e.2)

/-- The leaf writes of pieces refining a value's register pieces refine the write of its
encoding at shape `t`. -/
def EcwSplit (t : Ty) : Prop :=
  ∀ v, v.hasTy t = true → ∀ (q : Ptr) (M M' M1 : Mem) (xs : List Val), Mem.Refines M M' →
    M.write q (encode t v) = some M1 → RefinesList (leafVals t v) xs →
    ∃ MT, writeAll M' (ecwLeafWrites q (leaves t) xs) = some MT ∧ Mem.Refines M1 MT

theorem ecw_add_zero (q : Ptr) : q.add (BitVec.ofNat 64 0) = q := by
  cases q; simp [Ptr.add]

theorem ecw_add_add (q : Ptr) (o o' : Nat) :
    (q.add (BitVec.ofNat 64 o)).add (BitVec.ofNat 64 o') = q.add (BitVec.ofNat 64 (o + o')) := by
  cases q; simp [Ptr.add, BitVec.ofNat_add, BitVec.add_assoc]

theorem ecw_leafWrites_shift (q : Ptr) (o : Nat) :
    ∀ (L : List (Nat × Ty)) (xs : List Val),
      ecwLeafWrites q (L.map fun x => (o + x.1, x.2)) xs =
        ecwLeafWrites (q.add (BitVec.ofNat 64 o)) L xs
  | [], _ => rfl
  | _ :: _, [] => rfl
  | e :: L, x :: xs => by
    simp only [ecwLeafWrites, List.map_cons, List.zip_cons_cons] at *
    rw [ecw_add_add]
    exact congrArg _ (ecw_leafWrites_shift q o L xs)

theorem ecw_leafWrites_append (q : Ptr) {L1 L2 : List (Nat × Ty)} {xs1 xs2 : List Val}
    (h : L1.length = xs1.length) :
    ecwLeafWrites q (L1 ++ L2) (xs1 ++ xs2) = ecwLeafWrites q L1 xs1 ++ ecwLeafWrites q L2 xs2 := by
  simp [ecwLeafWrites, List.zip_append h]

/-! ## Leaves -/

theorem ecw_split_atom {t : Ty} (ht : atom t = true) : EcwSplit t := by
  intro v hv q M M' M1 xs hM hw hx
  rw [leafVals_atom ht, Val.retype_of_hasTy hv] at hx
  obtain ⟨x, rfl, h⟩ : ∃ x, xs = [x] ∧ Sem.Refines v x := by
    cases hx with
    | cons h t => cases t; exact ⟨_, rfl, h⟩
  obtain ⟨MT, hMT, hr⟩ := hM.write (encode_mono t h) hw
  refine ⟨MT, ?_, hr⟩
  rw [leaves_atom ht]
  simp [ecwLeafWrites, writeAll, ecw_add_zero, hMT]

theorem ecw_split_empty : EcwSplit .empty := by
  intro v _ q M M' M1 xs hM hw hx
  have hl : leafVals .empty v = [] := rfl
  rw [hl] at hx
  cases hx
  have he : (encode .empty v).isEmpty = true := by
    rw [Array.isEmpty_iff_size_eq_zero, Sem.encode_size]; rfl
  unfold Mem.write at hw
  simp only [he, ite_true] at hw
  cases hw
  exact ⟨M', rfl, hM⟩

/-! ## Aggregates -/

theorem ecw_split_fields {M : Mem} {q : Ptr} {n : Nat} :
    ∀ (fs : List (Nat × Ty)) (vs xs : List Val) (buf : Array Byte) (MB M' : Mem),
      (∀ f ∈ fs, f.1 + f.2.size ≤ n ∧ wf f.2 = true ∧ EcwSplit f.2) → buf.size = n →
      Val.hasTyList vs (fs.map (·.2)) = true →
      M.write q buf = some MB → Mem.Refines MB M' → RefinesList (leafValsFields fs vs) xs →
      ∃ MS MT, M.write q (encodeFields buf fs vs) = some MS ∧
        writeAll M' (ecwLeafWrites q (leaves.leavesFields fs) xs) = some MT ∧ Mem.Refines MS MT
  | [], vs, xs, buf, MB, M', _, _, _, hw, hr, hx => by
    have hl : leafValsFields [] vs = [] := rfl
    rw [hl] at hx
    cases hx
    refine ⟨MB, M', ?_, rfl, hr⟩
    cases vs <;> exact hw
  | (_, _) :: _, [], _, _, _, _, _, _, hv, _, _, _ => by simp [Val.hasTyList] at hv
  | (o, t) :: fs, v :: vs, xs, buf, MB, M', hf, hb, hv, hw, hr, hx => by
    simp only [List.map_cons, Val.hasTyList, Bool.and_eq_true] at hv
    obtain ⟨hon, hwt, hS⟩ := hf (o, t) List.mem_cons_self
    rw [leafValsFields_cons, Val.retype_of_hasTy hv.1] at hx
    obtain ⟨xs1, xs2, rfl, hx1, hx2⟩ := ecs_rl_split hx
    have ho : o + (encode t v).size ≤ buf.size := by rw [Sem.encode_size, hb]; exact hon
    obtain ⟨MB', hw1, hw2⟩ := write_putBytes hw ho
    obtain ⟨MT1, hMT1, hr1⟩ := hS v hv.1 _ MB M' MB' xs1 hr hw1 hx1
    obtain ⟨MS, MT, h1, h2, h3⟩ := ecw_split_fields fs vs xs2 _ MB' MT1
      (fun f hf' => hf f (List.mem_cons_of_mem _ hf')) (by rw [putBytes_size, hb]) hv.2 hw2 hr1 hx2
    refine ⟨MS, MT, by simpa [encodeFields] using h1, ?_, h3⟩
    have hlen : ((leaves t).map fun x => (o + x.1, x.2)).length = xs1.length := by
      rw [List.length_map, ← leafVals_length hwt (v := v)]; exact ecs_rl_length hx1
    rw [leavesFields_cons, ecw_leafWrites_append _ hlen, ecw_leafWrites_shift, writeAll_append hMT1]
    exact h2

theorem ecw_putBytes_poison {n o k : Nat} (h : o + k ≤ n) :
    putBytes (Array.replicate n .poison) o (Array.replicate k .poison) = Array.replicate n .poison := by
  apply Array.ext_getElem?
  intro j
  rw [putBytes_getElem? (by simpa using h)]
  split
  · rename_i hj
    simp only [Array.size_replicate] at hj
    rw [Array.getElem?_replicate, Array.getElem?_replicate, if_pos (by omega), if_pos (by omega)]
  · rfl

theorem ecw_encodeFields_poison {n : Nat} :
    ∀ (fs : List (Nat × Ty)), (∀ f ∈ fs, f.1 + f.2.size ≤ n) →
      encodeFields (Array.replicate n .poison) fs (fs.map fun _ => .poison) =
        Array.replicate n .poison
  | [], _ => rfl
  | (o, t) :: fs, h => by
    simp only [List.map_cons, encodeFields, encode_poison]
    rw [ecw_putBytes_poison (h (o, t) List.mem_cons_self)]
    exact ecw_encodeFields_poison fs fun f hf => h f (List.mem_cons_of_mem _ hf)

theorem ecw_hasTyList_poison : ∀ (ts : List Ty),
    Val.hasTyList (ts.map fun _ => .poison) ts = true
  | [] => rfl
  | _ :: ts => by simp [Val.hasTyList, Val.hasTy, ecw_hasTyList_poison ts]

/-- The register pieces of `poison` are `poison`s. -/
theorem ecw_leafVals_poison {t : Ty} (hw : wf t = true) :
    leafVals t .poison = (leaves t).map fun _ => .poison := by
  cases t with
  | agg fs n => exact leafVals_agg_of_ne fun _ h => by cases h
  | blob _ => cases hw
  | _ => rfl

theorem ecw_leafValsFields_poison : ∀ (fs : List (Nat × Ty)) (n s : Nat), wfFields fs n s = true →
    leafValsFields fs (fs.map fun _ => .poison) = (leaves.leavesFields fs).map fun _ => .poison
  | [], _, _, _ => rfl
  | (o, t) :: fs, n, s, hw => by
    simp only [wfFields, Bool.and_eq_true] at hw
    simp only [List.map_cons, leafValsFields_cons, leavesFields_cons, List.map_append,
      List.map_map]
    rw [ecA_retype_poison, ecw_leafVals_poison hw.1.2, ecw_leafValsFields_poison fs n _ hw.2]
    rfl

theorem ecw_split_agg {fs : List (Nat × Ty)} {n : Nat} (hwf : wfFields fs n 0 = true)
    (hS : ∀ f ∈ fs, EcwSplit f.2) : EcwSplit (.agg fs n) := by
  intro v hv q M M' M1 xs hM hw hx
  obtain ⟨vs, hvs, henc, hlv⟩ : ∃ vs, Val.hasTyList vs (fs.map (·.2)) = true ∧
      encode (.agg fs n) v = encodeFields (Array.replicate n .poison) fs vs ∧
      leafVals (.agg fs n) v = leafValsFields fs vs := by
    cases v with
    | agg vs => exact ⟨vs, hv, rfl, rfl⟩
    | poison =>
      refine ⟨fs.map fun _ => .poison, ?_, ?_, ?_⟩
      · have := ecw_hasTyList_poison (fs.map (·.2))
        simpa [List.map_map, Function.comp_def] using this
      · rw [encode_poison, ecw_encodeFields_poison fs fun f hf => (wfFields_mem hwf f hf).2.1]
        rfl
      · rw [ecw_leafValsFields_poison fs n 0 hwf]
        exact leafVals_agg_of_ne fun _ h => by cases h
    | _ => simp [Val.hasTy] at hv
  rw [henc] at hw
  rw [hlv] at hx
  obtain ⟨MB, hMB⟩ := write_size_congr hw (bs' := Array.replicate n .poison)
    (by rw [Sem.encodeFields_size])
  obtain ⟨MS, MT, h1, h2, h3⟩ := ecw_split_fields fs vs xs _ MB M'
    (fun f hf => ⟨(wfFields_mem hwf f hf).2.1, (wfFields_mem hwf f hf).2.2, hS f hf⟩) (by simp)
    hvs hMB (write_poison_left hM hMB) hx
  rw [hw] at h1
  cases h1
  exact ⟨MT, h2, h3⟩

/-! ## Strings and slices -/

theorem ecw_split_str : EcwSplit .str := by
  intro v hv q M M' M1 xs hM hw hx
  have hS : EcwSplit Ty.strAgg := ecw_split_agg rfl (by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl <;> exact ecw_split_atom rfl)
  rw [encode_asAgg] at hw
  obtain ⟨hl, hv'⟩ : leafVals .str v = leafVals Ty.strAgg v ∧ v.hasTy Ty.strAgg = true := by
    cases v with
    | poison => exact ⟨rfl, rfl⟩
    | agg vs =>
      obtain ⟨p, l, rfl, hp, -⟩ := Val.hasTy_agg_str.1 hv
      refine ⟨?_, ?_⟩
      · simp [leafVals, leafValsFields, Ty.strAgg, Val.retype_idem]
      · cases p with
        | int w x => cases w <;> simp_all [Val.hasTy, Val.hasTyList, Ty.strAgg, Val.isPtrWord]
        | _ => simp_all [Val.hasTy, Val.hasTyList, Ty.strAgg, Val.isPtrWord]
    | _ => simp [Val.hasTy] at hv
  rw [hl] at hx
  exact hS v hv' q M M' M1 xs hM hw hx

theorem ecw_split_slice (e : Option Nat) : EcwSplit (.slice e) := by
  intro v hv q M M' M1 xs hM hw hx
  have hS : EcwSplit (Ty.sliceAgg e) := ecw_split_agg rfl (by
    intro f hf
    simp only [Ty.sliceAgg, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl <;> exact ecw_split_atom rfl)
  rw [encode_asAgg] at hw
  obtain ⟨hl, hv'⟩ : leafVals (.slice e) v = leafVals (Ty.sliceAgg e) v ∧
      v.hasTy (Ty.sliceAgg e) = true := by
    cases v with
    | poison => exact ⟨rfl, rfl⟩
    | agg vs =>
      obtain ⟨p, l, c, rfl, hp, -⟩ := Val.hasTy_agg_slice.1 hv
      refine ⟨?_, ?_⟩
      · simp [leafVals, leafValsFields, Ty.sliceAgg, Val.retype_idem]
      · cases p with
        | int w x => cases w <;> simp_all [Val.hasTy, Val.hasTyList, Ty.sliceAgg, Val.isPtrWord]
        | _ => simp_all [Val.hasTy, Val.hasTyList, Ty.sliceAgg, Val.isPtrWord]
    | _ => simp [Val.hasTy] at hv
  rw [hl] at hx
  exact hS v hv' q M M' M1 xs hM hw hx

mutual
/-- **The leaf writes of a well-formed shape refine the write of its encoding.** -/
theorem ecw_split : (t : Ty) → wf t = true → EcwSplit t
  | .int _, _ | .bool, _ | .ptr _, _ | .opaque _, _ => ecw_split_atom rfl
  | .empty, _ => ecw_split_empty
  | .str, _ => ecw_split_str
  | .slice e, _ => ecw_split_slice e
  | .agg fs n, hw => ecw_split_agg hw (ecw_splitFields fs n 0 hw)
  | .blob _, h | .mem, h | .tuple _, h | .other, h => nomatch h
theorem ecw_splitFields : (fs : List (Nat × Ty)) → (n s : Nat) → wfFields fs n s = true →
    ∀ f ∈ fs, EcwSplit f.2
  | [], _, _, _, _, hf => absurd hf List.not_mem_nil
  | (o, t) :: fs, n, s, hw, f, hf => by
    simp only [wfFields, Bool.and_eq_true] at hw
    rcases List.mem_cons.1 hf with rfl | hf
    · exact ecw_split t hw.1.2
    · exact ecw_splitFields fs n _ hw.2 f hf
end

/-! ## Shapes up to pointers' element sizes -/

mutual
theorem ecw_encode_erase : (t : Ty) → (v : Val) → encode (erase t) v = encode t v
  | .agg fs n, v => by
    cases v with
    | agg vs =>
      simp only [erase, encode]
      exact ecw_encodeFields_erase fs _ vs
    | _ => rfl
  | .ptr _, v => by
    cases v with
    | int w x => cases w <;> rfl
    | _ => rfl
  | .slice _, v => by cases v <;> rfl
  | .tuple _, v => by cases v <;> rfl
  | .int _, _ | .bool, _ | .mem, _ | .other, _ | .blob _, _ | .empty, _ | .opaque _, _
  | .str, _ => rfl
theorem ecw_encodeFields_erase : (fs : List (Nat × Ty)) → (buf : Array Byte) → (vs : List Val) →
    encodeFields buf (eraseFields fs) vs = encodeFields buf fs vs
  | [], _, _ => rfl
  | (_, _) :: _, _, [] => rfl
  | (o, t) :: fs, buf, v :: vs => by
    simp only [eraseFields, encodeFields]
    rw [ecw_encode_erase t v, ecw_encodeFields_erase fs _ vs]
end

theorem ecw_encode_eqE {s t : Ty} (h : eqE s t = true) (v : Val) : encode s v = encode t v := by
  rw [← ecw_encode_erase s, Ty.eq_of_beq h, ecw_encode_erase]

/-! ## Memories -/

/-- A write that succeeds was a writable range. -/
theorem ecw_canWrite_of_write {m m' : Mem} {p : Ptr} {bs : Array Byte}
    (h : m.write p bs = some m') : m.canWrite p bs.size = true := by
  by_cases he : bs.size = 0
  · unfold Mem.canWrite; simp [he]
  rw [ecs_canWrite_pos he]
  have hne : bs.isEmpty = false := by simp [Array.isEmpty, he]
  unfold Mem.write at h
  simp only [hne, Bool.false_eq_true, ite_false] at h
  cases ha : m.find? p.blk with
  | none => rw [ha] at h; cases h
  | some a =>
    rw [ha] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · rename_i hc
      simpa [Bool.and_eq_true, decide_eq_true_eq] using hc
    · cases h

/-- A `Store` never panics. -/
theorem ecw_memRoot_store {ctx : Ctx} {u : Value} {argv : List Val} {e : Panic} {m : Mem}
    (hu : u.op = .Store) : memRoot ctx u argv ≠ .panic e m := by
  intro h
  unfold memRoot at h
  rw [hu] at h
  split at h
  all_goals first
    | contradiction
    | (simp only [writeRes] at h; split at h <;> cases h)
    | (split at h <;> first | (simp only [writeRes] at h; split at h <;> cases h) | cases h)
    | (simp only at h; split at h <;> cases h)

theorem ecw_store_not_panic {env : Env} {ctx : Ctx} {fr : Frame} {u : Value} {e : Panic} {m : Mem}
    (hu : u.op = .Store) : evalValue env ctx fr u ≠ .panic e m := by
  intro h
  have hr := regs_of_panic h
  rw [evalValue_of_regs hr] at h
  have he : evalOp env ctx fr u (u.args.toList.map (rv fr)) (ctx.tys[u.id]?.getD .other) =
      memRoot ctx u (u.args.toList.map (rv fr)) := by
    unfold evalOp; rw [hu]
  rw [he] at h
  cases hm : memRoot ctx u (u.args.toList.map (rv fr)) with
  | ok r => rw [hm] at h; cases h
  | panic e' m' => exact ecw_memRoot_store hu hm
  | stuck s => rw [hm] at h; cases h

/-! ## Chains of leaf stores -/

/-- The pointer a pointer word reads as (`Ptr.null` for other values). -/
def ecwPtr (v : Val) : Ptr := v.asPtrWord.getD Ptr.null

/-- The write of `Store` node `z` of `g` in frame `T`. -/
def ecwW (tabs : Tables) (g : Func) (T : Frame) (z : ID) : Ptr × Array Byte :=
  match g.value? z with
  | some w => (ecwPtr (rv T w.args[0]!), encode (auxTy tabs w.aux) (rv T w.args[1]!))
  | none => (Ptr.null, #[])

/-- **A chain of new `Store`s of shape `mem`** writes, from the memory `M` of its bottom, its
stores' writes in order. -/
theorem ecw_chain {env : Env} {tabs : Tables} {f g : Func} {T : Frame} {E L : ID → Prop}
    (hNC : NewCons env (Ctx.make tabs g) (isNewB f) T E)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true → L a) :
    ∀ (n : Nat) {z b : ID} {zs : List ID}, storeChain g (isNewB f) n z b = some zs →
      (zs ≠ [] → E z ∧ L z) → (∀ z' ∈ zs, shapeOf (typeShapes tabs) g z' = .mem) →
      ∀ M, rv T b = .mem M → ∃ M', rv T z = .mem M' ∧
        writeAll M (zs.map (ecwW tabs g T)) = some M' ∧
        ∀ z' ∈ zs, ∀ wz, g.value? z' = some wz →
          (rv T wz.args[0]!).asPtrWord = some (ecwPtr (rv T wz.args[0]!))
  | 0, _, _, _, h, _, _, _, _ => by simp [storeChain] at h
  | n + 1, z, b, zs, h, hEL, hsh, M, hM => by
    rcases ecs_storeChain_step h with ⟨rfl, rfl⟩ | ⟨w, zs', -, hw, -, hop, hsz, hc, rfl⟩
    · exact ⟨M, hM, rfl, fun _ h => absurd h List.not_mem_nil⟩
    obtain ⟨hEz, hLz⟩ := hEL (by simp)
    obtain ⟨-, w', y, hw', hcl, hy, hev⟩ := hNC z hEz
    change g.value? z = some w' at hw'
    rw [hw] at hw'; cases hw'
    obtain ⟨hwid, hLcl⟩ := hL z hLz w hw
    have hargs := ecs_args_three hsz
    have hm2 : w.args[2]! ∈ w.args := by rw [← Array.mem_toList_iff, hargs]; simp
    have hty : (Ctx.make tabs g).tys[w.id]?.getD .other = .mem := by
      rw [hwid, ← shapeOf_eq]; exact hsh z (by simp)
    obtain ⟨P, M0, M1, hP, hM0, hW, rfl⟩ := ecs_store_val hop hargs hty hev
    have hEL' : zs' ≠ [] → E w.args[2]! ∧ L w.args[2]! := fun hne => by
      have hn := ecs_storeChain_new hc hne
      exact ⟨hcl _ hm2 hn, hLcl _ hm2 hn⟩
    obtain ⟨M0', hM0', hW', hpt⟩ := ecw_chain hNC hL n hc hEL'
      (fun z' hz' => hsh z' (List.mem_append_left _ hz')) M hM
    rw [hM0] at hM0'; cases hM0'
    refine ⟨M1, rv_of hy, ?_, ?_⟩
    · rw [List.map_append]
      refine writeAll_snoc hW' ?_
      simp only [ecwW, hw, hP, ecwPtr, Option.getD_some]
      exact hW
    · intro z' hz' wz hwz
      rcases List.mem_append.1 hz' with hz' | hz'
      · exact hpt z' hz' wz hwz
      · rw [List.mem_singleton.1 hz', hw] at hwz; cases hwz; simp only [ecwPtr, hP, Option.getD_some]

/-- The facts of the leaf stores of a wide store. -/
theorem ecw_wideLeaves_get {tabs : Tables} {sh : Array Ty} {g : Func} {nw : ID → Bool} {p c : ID}
    {first : Nat} :
    ∀ {j : Nat} {ls : List (Nat × Ty)} {zs : List ID}, wideLeavesOK tabs sh g nw p c first j ls zs = true →
      ls.length = zs.length ∧ ∀ k z, zs[k]? = some z → ∃ o lt zw, ls[k]? = some (o, lt) ∧
        g.value? z = some zw ∧ 0 < lt.size ∧ eqE (auxTy tabs zw.aux) lt = true ∧
        shapeOf sh g z = .mem ∧ wideAddrOK sh g nw p o zw.args[0]! = true ∧
        wideValOK sh g nw c (first + (j + k)) lt zw.args[1]! = true
  | _, [], [], _ => ⟨rfl, fun _ _ h => by simp at h⟩
  | _, [], _ :: _, h | _, _ :: _, [], h => by simp [wideLeavesOK] at h
  | j, (o, lt) :: ls, z :: zs, h => by
    simp only [wideLeavesOK, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨hl, hg⟩ := ecw_wideLeaves_get h2
    refine ⟨by simp [hl], fun k z' hk => ?_⟩
    cases k with
    | zero =>
      cases hk
      cases hz : g.value? z with
      | none => rw [hz] at h1; cases h1
      | some zw =>
        rw [hz] at h1
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
        obtain ⟨⟨⟨⟨hpos, haux⟩, hsh⟩, ha⟩, hv⟩ := h1
        refine ⟨o, lt, zw, rfl, rfl, hpos, haux, ?_, ha, by simpa using hv⟩
        split at hsh
        · assumption
        · cases hsh
    | succ k =>
      obtain ⟨o', lt', zw, h1, h2, h3, h4, h5, h6, h7⟩ := hg k z' hk
      exact ⟨o', lt', zw, h1, h2, h3, h4, h5, h6, by rw [show j + (k + 1) = j + 1 + k by omega]; exact h7⟩

/-- The address of a leaf store, when the store's address `p` holds `q`: `q + o`, or its
`ptrRes`. -/
theorem ecw_addr {env : Env} {tabs : Tables} {f g : Func} {T : Frame} {E L : ID → Prop}
    (hNC : NewCons env (Ctx.make tabs g) (isNewB f) T E)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true → L a)
    {p a : ID} {o : Nat} {q : Ptr}
    (hok : wideAddrOK (typeShapes tabs) g (isNewB f) p o a = true)
    (hp : (rv T p).asPtrWord = some q) (hEa : isNewB f a = true → E a ∧ L a) :
    (rv T a).asPtrWord = some (q.add (BitVec.ofNat 64 o)) ∨
      (rv T a).asPtrWord = q.step? (BitVec.ofNat 64 o) := by
  unfold wideAddrOK at hok
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hok
  rcases hok with ⟨rfl, rfl⟩ | ⟨hn, hm⟩
  · exact .inl (by rw [hp, ecw_add_zero])
  · right
    obtain ⟨hEa, hLa⟩ := hEa hn
    obtain ⟨-, aw, ya, haw, -, hya, hev⟩ := hNC a hEa
    change g.value? a = some aw at haw
    rw [haw] at hm
    dsimp only at hm
    simp only [Bool.and_eq_true, beq_iff_eq] at hm
    obtain ⟨⟨⟨hop, hai⟩, hargs⟩, hsh⟩ := hm
    have hid := (hL a hLa aw haw).1
    have hv := evalValue_term (by rw [hop]; decide) hev
    rw [hop, GoFV.Proof.Rules.opVal_pure (by decide), hargs, hid, ← shapeOf_eq] at hv
    simp only [List.map_cons, List.map_nil] at hv
    change ya = (PtrOps.offPtr aw.auxInt [rv T p]).retype (shapeOf (typeShapes tabs) g a) at hv
    rw [rv_of hya, hv]
    split at hsh
    · next e he =>
      rw [he, Val.asPtrWord_retype_ptr, PtrOps.offPtr_asPtrWord, hp, Option.bind_some]
      simp only [hai, BitVec.ofInt_natCast]
    · cases hsh

/-! ## The register pieces of the wide result -/

/-- **Piece `k` of register-assigned call result `i`** in the target (`SelectN` of the call's
register tuple, at a shape of leaf `k`) refines leaf `k` of the source's result. -/
theorem ecw_piece {tabs : Tables} {f g : Func} {c : ID} {cu cw : Value}
    (hcu : f.value? c = some cu) (hcw : g.value? c = some cw)
    (hcall : (callOpMap cu.op).isSome = true)
    (hcok : callOK tabs (typeShapes tabs) f g cu cw = true) {yc yc' : Val}
    (hyc : yc.hasTy (shapeOf (typeShapes tabs) f c) = true)
    (hR : Sem.Refines (ecCv tabs f g c yc) yc') {ai : Int64} (hai0 : 0 ≤ ai.toInt) {pp : ABIParam}
    (hp : (callOuts tabs cu.aux)[ai.toInt.toNat]? = some pp) (hpr : pp.regs.isEmpty = false)
    {s : Ty} (hs : eqE s (tabs.ty pp.type) = true) :
    ∀ k a, (leafVals (tabs.ty pp.type) ((Tuple.selectN ai [yc]).retype s))[k]? = some a →
      ∀ o lt, (leaves (tabs.ty pp.type))[k]? = some (o, lt) → ∀ (bi : Int64) (s' : Ty),
        bi.toInt = (((leafTys tabs ((callOuts tabs cu.aux).take ai.toInt.toNat)).length + k : Nat) : Int) →
        eqE s' lt = true → Sem.Refines a ((Tuple.selectN bi [yc']).retype s') := by
  intro k a ha o lt he bi s' hbi hs'
  obtain ⟨hinvc, hoo, htup, hrtup⟩ := ecA_callOK_facts hcw hcok
  have hwfo := ec_outsOK_wf hoo
  rw [ecA_cv_call hcu hcall hinvc, ecT_shapeOf_value hcw] at hR
  obtain ⟨us, hus, husl, huse, -⟩ := ecA_tupleOf_get htup
  obtain ⟨rus, hrus, hrusl, hrusr, -⟩ := ecA_regTupleOf_get hrtup
  rw [hrus] at hR
  rw [List.length_map] at husl
  have hycT : yc.hasTy (.tuple us) = true := by
    rw [ecT_shapeOf_value hcu] at hyc; rw [← hus]; exact hyc
  have hwf := hwfo pp (List.mem_of_getElem? hp) hpr
  have hi : ai.toInt = ((ai.toInt.toNat : Nat) : Int) := by omega
  rcases ecA_tuple_cases hycT with rfl | ⟨vs, rfl, hvs⟩
  · rw [ecA_selectN_poison, ecA_retype_poison, ecw_leafVals_poison hwf, List.getElem?_map] at ha
    cases h : (leaves (tabs.ty pp.type))[k]? with
    | none => rw [h] at ha; cases ha
    | some _ => rw [h] at ha; cases ha; exact .poison _
  obtain ⟨hl, hget⟩ := ecA_hasTyPre_get hvs
  rw [ecA_convTuple_eq] at hR
  have hCl := ecA_convList_length tabs _ vs hwfo (by omega)
  obtain ⟨C', hC', hg⟩ := ecA_retypePre_get (ts := rus)
    (vs := ecA_convList tabs (callOuts tabs cu.aux) vs) (by
      rw [hCl, hrusl]
      omega)
  have hre : (Val.tuple (ecA_convList tabs (callOuts tabs cu.aux) vs)).retype (.tuple rus) =
      .tuple C' := by simp only [Val.retype, hC']
  rw [hre] at hR
  obtain ⟨D, rfl, hRL⟩ : ∃ D, yc' = .tuple D ∧ RefinesList C' D := by
    cases hR with
    | tuple h => exact ⟨_, rfl, h⟩
  have hilt := ecA_lt_of_getElem? hp
  obtain ⟨v, hv⟩ : ∃ v, vs[ai.toInt.toNat]? = some v :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨ui, hui⟩ : ∃ ui, us[ai.toInt.toNat]? = some ui :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hvt : v.hasTy (tabs.ty pp.type) = true := by
    rw [← eqE_hasTy (huse _ _ _ (by rw [List.getElem?_map, hp]; rfl) hui)]
    exact hget _ _ _ hui hv
  rw [ecA_selectN_tuple hi, List.getD_eq_getElem?_getD, hv, Option.getD_some, eqE_retype hs,
    Val.retype_of_hasTy hvt] at ha
  have hklt : k < (leaves (tabs.ty pp.type)).length := ecA_lt_of_getElem? he
  have hC := ecA_convList_piece tabs _ _ vs pp v hwfo hp hv hpr k hklt
  rw [ha] at hC
  have hlt := ecA_leafTys_piece tabs _ _ pp hp hpr k hklt
  rw [List.getElem?_map, he] at hlt
  have hb' : (leafTys tabs (List.take ai.toInt.toNat (callOuts tabs cu.aux))).length + k <
      rus.length := by
    have := ecA_lt_of_getElem? hlt
    omega
  obtain ⟨rt, hrt⟩ : ∃ rt, rus[(leafTys tabs (List.take ai.toInt.toNat
      (callOuts tabs cu.aux))).length + k]? = some rt := ⟨_, List.getElem?_eq_getElem hb'⟩
  have hreg := hrusr _ _ _ hlt hrt
  obtain ⟨d, hd, hRd⟩ := ecT_refinesList_get hRL _ _ (hg _ _ _ hrt hC)
  have hat : a.hasTy lt = true := by
    obtain ⟨b', hb'', hh⟩ := ecT_forall₂_get (leafVals_hasTy hwf (v := v)) k a ha
    rw [he] at hb''
    cases hb''
    exact hh
  rw [ecA_selectN_tuple hbi, List.getD_eq_getElem?_getD, hd, Option.getD_some, eqE_retype hs']
  have := Sem.retype_mono lt hRd
  rw [ecA_regShape hreg hat] at this
  exact this

/-! ## The checker's facts -/

theorem ecw_wideSel {f g : Func} {x : ID} (h : wideSel f g x = true) :
    ∃ u w, f.value? x = some u ∧ g.value? x = some w ∧ u.op = .SelectN ∧ u.args.size = 1 ∧
      converted f u.args[0]! = true ∧ w.op = .SelectN := by
  unfold wideSel at h
  split at h
  · next u w hu hw =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨u, w, hu, hw, h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2⟩
  · cases h

theorem ecw_wideChain {f g : Func} {u w : Value} {zs : List ID} (h : wideChain f g u w = some zs) :
    u.op = .Store ∧ w.op = .Copy ∧ u.args.size = 3 ∧ w.args.size = 1 ∧
      storeChain g (isNewB f) (g.valueTab.size + 1) w.args[0]! u.args[2]! = some zs := by
  unfold wideChain at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact ⟨hc.1.1.1, hc.1.1.2, hc.1.2, hc.2, h⟩
  · cases h

/-- What `wideStoreOK` checks. -/
theorem ecw_wideStoreOK {tabs : Tables} {f g : Func} {u w : Value}
    (h : wideStoreOK tabs (typeShapes tabs) f g u w = true) :
    w.type = u.type ∧ valueTy (typeShapes tabs) (some u) = .mem ∧ wideSel f g u.args[1]! = true ∧
      special f g u.args[0]! = false ∧ special f g u.args[2]! = false ∧
      ∃ zs xu cu pp, wideChain f g u w = some zs ∧ f.value? u.args[1]! = some xu ∧
        f.value? xu.args[0]! = some cu ∧ (callOpMap cu.op).isSome = true ∧ 0 ≤ xu.auxInt.toInt ∧
        (callOuts tabs cu.aux)[xu.auxInt.toInt.toNat]? = some pp ∧ pp.regs.isEmpty = false ∧
        wf (tabs.ty pp.type) = true ∧ eqE (auxTy tabs u.aux) (tabs.ty pp.type) = true ∧
        eqE (shapeOf (typeShapes tabs) f u.args[1]!) (tabs.ty pp.type) = true ∧
        wideLeavesOK tabs (typeShapes tabs) g (isNewB f) u.args[0]! xu.args[0]!
          (leafTys tabs ((callOuts tabs cu.aux).take xu.auxInt.toInt.toNat)).length 0
          (leaves (tabs.ty pp.type)) zs = true := by
  unfold wideStoreOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hty, hm⟩, hws⟩, hs0⟩, hs2⟩, h⟩ := h
  refine ⟨beq_iff_eq.1 hty, ?_, hws, by simpa using hs0, by simpa using hs2, ?_⟩
  · split at hm
    · assumption
    · cases hm
  · split at h
    · rename_i zs xu hzs hxu
      split at h
      · rename_i cu hcu
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨hcall, hi0⟩, h⟩ := h
        split at h
        · rename_i pp hpp
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
          obtain ⟨⟨⟨⟨hr, hwf⟩, he1⟩, he2⟩, hl⟩ := h
          exact ⟨zs, xu, cu, pp, hzs, hxu, hcu, hcall, hi0, hpp, hr, hwf, he1, he2, hl⟩
        · cases h
      · cases h
    · cases h

/-! ## The obligations -/

/-- **The obligation of a wide call result** (`wideSel`, conversion `poison`): both forms
evaluate a `SelectN`. -/
theorem obl_wideSel {tabs : Tables} {f g : Func} {x : ID} {HS HT : ID → Prop}
    (h : wideSel f g x = true) :
    Obl tabs f g (ecCv tabs f g) (isNewB f) (ecFront f g x) HS HT x := by
  obtain ⟨u, w, hu, hw, hop, -, -, hwop⟩ := ecw_wideSel h
  intro u' w' hu' hw' env _ frS T _ _ E _ _ hRT hRS _ _ _
  rw [hu] at hu'; cases hu'
  rw [hw] at hw'; cases hw'
  rw [ecT_eval_selectN hop hRS, ecT_eval_selectN hwop hRT]
  exact .ok (by rw [ecCv_wideSel h]; exact .poison _)

/-- The store `u` of `f` is not converted. -/
theorem ecw_store_not_special {f g : Func} {x : ID} {u w : Value} (hu : f.value? x = some u)
    (hw : g.value? x = some w) (hop : u.op = .Store) (hwop : w.op = .Copy) :
    special f g x = false := by
  unfold special converted invalidated
  rw [hu, hw, ecA_not_wideSel hu (by rw [hop]; decide)]
  dsimp only
  rw [hop, hwop]
  rfl

/-- The facts of the source store `u` that the source evaluated: its address, memory and
write. -/
theorem ecw_store_src {env : Env} {tabs : Tables} {f : Func} {x : ID} {u : Value} {G : Frame}
    {y : Val} (hu : f.value? x = some u) (huid : u.id = x) (hop : u.op = .Store)
    (hus : u.args.size = 3) (hvm : valueTy (typeShapes tabs) (some u) = .mem)
    (hy : evalValue env (Ctx.make tabs f) G u = .ok y) :
    ∃ q M M1, (rv G u.args[0]!).asPtrWord = some q ∧ rv G u.args[2]! = .mem M ∧
      M.write q (encode (auxTy tabs u.aux) (rv G u.args[1]!)) = some M1 ∧ y = .mem M1 := by
  have htyu : (Ctx.make tabs f).tys[u.id]?.getD .other = .mem := by
    rw [huid, ← shapeOf_eq, ecT_shapeOf_value hu]; exact hvm
  obtain ⟨q, M, M1, h1, h2, h3, h4⟩ := ecs_store_val hop (ecs_args_three hus) htyu hy
  rw [show (Ctx.make tabs f).tabs = tabs from rfl] at h3
  exact ⟨q, M, M1, h1, h2, h3, h4⟩

/-- The target's register of the store's address (memory) reads as the source's pointer
(a refinement of its memory). -/
theorem ecw_front_ptr {tabs : Tables} {f g : Func} {a : ID} {G T : Frame} {q : Ptr}
    (hs : special f g a = false) (hG : (rv G a).asPtrWord = some q) (hr : Reg G a)
    (hfr : ∀ y, G.regs[a]? = some (some y) →
      ∃ y', T.regs[a]? = some (some y') ∧ Sem.Refines (ecCv tabs f g a y) y') :
    (rv T a).asPtrWord = some q := by
  obtain ⟨y', hy', hr'⟩ := hfr _ (reg_rv hr)
  rw [ecCv_of_not_special hs] at hr'
  rw [rv_of hy']
  exact hr'.asPtrWord hG

theorem ecw_front_mem {tabs : Tables} {f g : Func} {a : ID} {G T : Frame} {M : Mem}
    (hs : special f g a = false) (hG : rv G a = .mem M) (hr : Reg G a)
    (hfr : ∀ y, G.regs[a]? = some (some y) →
      ∃ y', T.regs[a]? = some (some y') ∧ Sem.Refines (ecCv tabs f g a y) y') :
    ∃ M', rv T a = .mem M' ∧ Mem.Refines M M' := by
  obtain ⟨y', hy', hr'⟩ := hfr _ (reg_rv hr)
  rw [ecCv_of_not_special hs, hG] at hr'
  cases hr' with
  | mem h => exact ⟨_, rv_of hy', h⟩

theorem ecw_mem_three {arr : Array ID} (h : arr.size = 3) (i : Nat) (hi : i < 3) : arr[i]! ∈ arr := by
  rw [← Array.mem_toList_iff, ecs_args_three h]
  match i, hi with
  | 0, _ | 1, _ | 2, _ => simp

/-- **The obligation of a leaf store of a wide store** `x` (`NewObl`, anchored at `x`): once the
source has reached `x`, its write of the whole value succeeded, so the target's address is in
bounds and the range of the leaf is writable in the target's memory below the leaf. -/
theorem ecw_storeObl {tabs : Tables} {f g : Func} {x z : ID} {u w : Value} {HS HT : ID → Prop}
    (hu : f.value? x = some u) (huid : u.id = x) (hw : g.value? x = some w)
    (hok : wideStoreOK tabs (typeShapes tabs) f g u w = true)
    {zs : List ID} (hzs : wideChain f g u w = some zs) (hz : z ∈ zs) (L : ID → Prop)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true → L a)
    (hLz : L z) :
    NewObl tabs f g (ecCv tabs f g) (isNewB f) [u.args[0]!, u.args[2]!] HS HT x z := by
  intro wz hwz env G T _ E hNC hEw hRw hfront _ _ hreach _
  obtain ⟨-, hvm, -, hs0, hs2, zs0, xu, cu, pp, hzs0, -, -, -, -, -, -, hwf, he1, -, hl⟩ :=
    ecw_wideStoreOK hok
  rw [hzs] at hzs0; cases hzs0
  obtain ⟨hop, -, hus, -, hch⟩ := ecw_wideChain hzs
  -- the source reached the store: its write succeeded
  obtain ⟨y, hy⟩ : ∃ y, evalValue env (Ctx.make tabs f) G u = .ok y := by
    rcases hreach u hu with h | ⟨e, m, h⟩
    · exact h
    · exact absurd h (ecw_store_not_panic hop)
  obtain ⟨q, M, M1, hq, hM, hW, -⟩ := ecw_store_src hu huid hop hus hvm hy
  have hregG := regs_of_ok hy
  have hpT := ecw_front_ptr hs0 hq (hregG _ (ecw_mem_three hus 0 (by decide)))
    (hfront _ (by simp))
  obtain ⟨M', hMT, hMR⟩ := ecw_front_mem hs2 hM (hregG _ (ecw_mem_three hus 2 (by decide)))
    (hfront _ (by simp))
  -- `z` in the chain
  obtain ⟨wz', n', zs', hwz', -, hzop, hzsz, hc, rest, hsplit⟩ := ecs_chain_mem hch hz
  rw [hwz] at hwz'; cases hwz'
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hz
  obtain ⟨-, hget⟩ := ecw_wideLeaves_get hl
  obtain ⟨o, lt, zw, hle, hzw, hpos, haux, hsh, haddr, -⟩ := hget k z hk
  rw [hwz] at hzw; cases hzw
  obtain ⟨hwid, hLcl⟩ := hL z hLz wz hwz
  have hzargs := ecs_args_three hzsz
  -- the stores below `z`
  have hEL : zs' ≠ [] → E wz.args[2]! ∧ L wz.args[2]! := fun hne => by
    have hn := ecs_storeChain_new hc hne
    exact ⟨hEw _ (ecw_mem_three hzsz 2 (by decide)) hn,
      hLcl _ (ecw_mem_three hzsz 2 (by decide)) hn⟩
  have hshs' : ∀ z' ∈ zs', shapeOf (typeShapes tabs) g z' = .mem := fun z' hz' => by
    obtain ⟨k', hk'⟩ := List.getElem?_of_mem (show z' ∈ zs by rw [hsplit]; simp [hz'])
    obtain ⟨_, _, _, _, _, _, _, h, _⟩ := hget k' z' hk'
    exact h
  obtain ⟨Mb, hMb, hWb, -⟩ := ecw_chain hNC hL n' hc hEL hshs' M' hMT
  -- the leaf's range is writable
  have hcw0 := ecw_canWrite_of_write hW
  rw [Sem.encode_size, ecT_eqE_size he1, ← hMR.canWrite,
    ← ecs_canWrite_congr (writeAll_attr hWb)] at hcw0
  have hol : o + lt.size ≤ (tabs.ty pp.type).size :=
    (mem_leaves hwf (List.mem_of_getElem? hle)).1
  have hq' : q = ⟨q.blk, BitVec.ofNat 64 q.off.toNat⟩ := by cases q; simp
  rw [hq'] at hcw0
  have hcw := ecs_canWrite_sub (k := o) (l := lt.size) hol hcw0 q.off.isLt
  have hqa : q.add (BitVec.ofNat 64 o) = ⟨q.blk, BitVec.ofNat 64 (q.off.toNat + o)⟩ := by
    cases q; simp [Ptr.add, BitVec.ofNat_add]
  -- the leaf's address
  have hwin : (q.add (BitVec.ofNat 64 o)).inWindow = true :=
    inWindow_of_write hW (by rw [Sem.encode_size, ecT_eqE_size he1]; omega)
  have ha : (rv T wz.args[0]!).asPtrWord = some (q.add (BitVec.ofNat 64 o)) := by
    rcases ecw_addr hNC hL haddr hpT (fun hn => ⟨hEw _ (ecw_mem_three hzsz 0 (by decide)) hn,
      hLcl _ (ecw_mem_three hzsz 0 (by decide)) hn⟩) with h | h
    · exact h
    · rw [h]; unfold Ptr.step?; rw [if_pos hwin]
  -- the write
  have hsz' : (encode (auxTy tabs wz.aux) (rv T wz.args[1]!)).size = lt.size := by
    rw [Sem.encode_size, ecT_eqE_size haux]
  obtain ⟨M2, hW2⟩ := ecs_write_of_canWrite (m := Mb) (p := q.add (BitVec.ofNat 64 o))
    (bs := encode (auxTy tabs wz.aux) (rv T wz.args[1]!)) (by rw [hsz', hqa]; exact hcw)
  have htyz : (Ctx.make tabs g).tys[wz.id]?.getD .other = .mem := by
    rw [hwid, ← shapeOf_eq]; exact hsh
  exact ⟨_, ecs_store_eval hzop hRw hzargs htyz ha hMb hW2⟩

/-- The address of a leaf store reads as `q + o` (it evaluated to a pointer word). -/
theorem ecw_ptr_eq {v : Val} {q : Ptr} {o : Nat}
    (h : v.asPtrWord = some (q.add (BitVec.ofNat 64 o)) ∨ v.asPtrWord = q.step? (BitVec.ofNat 64 o))
    (hp : v.asPtrWord = some (ecwPtr v)) : ecwPtr v = q.add (BitVec.ofNat 64 o) := by
  rcases h with h | h
  · rw [h] at hp; exact (Option.some.inj hp).symm
  · rw [h] at hp
    unfold Ptr.step? at hp
    split at hp
    · exact (Option.some.inj hp).symm
    · cases hp

/-- **The obligation of a wide store**: the source stores the wide call result `a = SelectN [i] c`
at `p`; the target writes the register pieces `SelectN [first + k] c` leaf by leaf at `p + o`
(`ecw_chain`), which refine the source's write (`ecw_split`, `ecw_piece`). -/
theorem obl_wideStore {tabs : Tables} {f g : Func} {x : ID} {u w : Value} {HS HT : ID → Prop}
    (hu : f.value? x = some u) (hw : g.value? x = some w) (huid : u.id = x)
    (hok : wideStoreOK tabs (typeShapes tabs) f g u w = true)
    (hcall : ∀ xu cu, f.value? u.args[1]! = some xu → f.value? xu.args[0]! = some cu →
      (callOpMap cu.op).isSome = true →
      ∃ cw, g.value? xu.args[0]! = some cw ∧ callOK tabs (typeShapes tabs) f g cu cw = true)
    (L : ID → Prop) (hLx : L x)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true → L a)
    (hHa : HS u.args[1]!) :
    Obl tabs f g (ecCv tabs f g) (isNewB f) (ecFront f g x) HS HT x := by
  intro u' w' hu' hw' env _ frS T _ hRegs E hN hEw hRT hRS hfr hSH _
  rw [hu] at hu'; cases hu'
  rw [hw] at hw'; cases hw'
  obtain ⟨hty, hvm, hws, hs0, hs2, zs, xu, cu, pp, hzs, hxu, hcu, hcallc, hi0, hpp, hpr, hwf, he1,
    he2, hl⟩ := ecw_wideStoreOK hok
  obtain ⟨hop, hwop, hus, hws1, hch⟩ := ecw_wideChain hzs
  have hinv : invalidated g x = false := by unfold invalidated; rw [hw]; dsimp only; rw [hwop]; rfl
  have hfd : frameDet f g x = false := frameDet_of_src hu (by rw [hop]; decide)
  obtain ⟨cw, hcw, hcok⟩ := hcall xu cu hxu hcu hcallc
  rw [funext (ecCv_of_not_special (tabs := tabs) (ecw_store_not_special hu hw hop hwop))]
  cases hS : evalValue env (Ctx.make tabs f) frS u with
  | stuck msg => exact .stuck msg _
  | panic e m => exact absurd hS (ecw_store_not_panic hop)
  | ok y =>
  obtain ⟨q, M, M1, hq, hM, hW, rfl⟩ := ecw_store_src hu huid hop hus hvm hS
  have hpT := ecw_front_ptr hs0 hq (hRS _ (ecw_mem_three hus 0 (by decide)))
    (hfr _ (ecFront_src hinv hfd hu (ecw_mem_three hus 0 (by decide)) (ec_not_invalidated hs0)))
  obtain ⟨M', hMT, hMR⟩ := ecw_front_mem hs2 hM (hRS _ (ecw_mem_three hus 2 (by decide)))
    (hfr _ (ecFront_src hinv hfd hu (ecw_mem_three hus 2 (by decide)) (ec_not_invalidated hs2)))
  -- the target's chain of leaf stores
  have hw0 : w.args[0]! ∈ w.args := by rw [← Array.mem_toList_iff, ec_args_one hws1]; simp
  have hwid := (hL x hLx w hw).1
  have hEL : zs ≠ [] → E w.args[0]! ∧ L w.args[0]! := fun hne => by
    have hn := ecs_storeChain_new hch hne
    exact ⟨hEw _ hw0 hn, (hL x hLx w hw).2 _ hw0 hn⟩
  obtain ⟨hlen, hget⟩ := ecw_wideLeaves_get hl
  have hshs : ∀ z ∈ zs, shapeOf (typeShapes tabs) g z = .mem := fun z hz => by
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hz
    obtain ⟨_, _, _, _, _, _, _, h, _⟩ := hget k z hk
    exact h
  obtain ⟨MT, hMTT, hWT, hpt⟩ := ecw_chain hN hL _ hch hEL hshs M' hMT
  have hEz := ecs_chain_E hN hL _ hch hEL
  -- the target's `Copy` of the chain's top
  have htyw : (Ctx.make tabs g).tys[w.id]?.getD .other = .mem := by
    rw [hwid, ← shapeOf_eq, ecT_shapeOf_value hw]
    simp only [valueTy] at hvm ⊢
    rw [hty]; exact hvm
  rw [ecT_eval_term (by rw [hwop]; decide) (by rw [hwop]; decide) hRT, hwop, ec_args_one hws1, htyw]
  simp only [List.map_cons, List.map_nil, hMTT]
  refine .ok (.mem ?_)
  -- the source's wide result
  obtain ⟨xu', -, hxu', -, hxop, hxsz, -, -⟩ := ecw_wideSel hws
  rw [hxu] at hxu'; cases hxu'
  obtain ⟨hxid, ya, hya, heva⟩ := hSH _ hHa xu hxu
  have hra := regs_of_ok heva
  have hxargs := ec_args_one hxsz
  have hc : xu.args[0]! ∈ xu.args := by rw [← Array.mem_toList_iff, hxargs]; simp
  rw [ecT_eval_selectN hxop hra, hxargs, hxid, ← shapeOf_eq] at heva
  simp only [List.map_cons, List.map_nil] at heva
  cases heva
  have hva := rv_of hya
  have hvT : (rv frS u.args[1]!).hasTy (tabs.ty pp.type) = true := by
    have := (hRegs _ _ hya).1
    rw [← shapeOf_eq, eqE_hasTy he2] at this
    rw [hva]; exact this
  have hyc := (hRegs _ _ (reg_rv (hra _ hc))).1
  rw [← shapeOf_eq] at hyc
  obtain ⟨yc', hyc', hR⟩ := hfr _ (ecFront_wide hinv hfd hu (ecw_mem_three hus 1 (by decide)) hws hxu hc) _
    (reg_rv (hra _ hc))
  -- the pieces the leaf stores write refine the source's leaves
  have hxs : RefinesList (leafVals (tabs.ty pp.type) (rv frS u.args[1]!))
      (zs.map fun z => rv T (storeVal g z)) := by
    refine ecT_refinesList_of_get (by rw [leafVals_length hwf, List.length_map, hlen]) ?_
    intro k a' b ha hb
    rw [List.getElem?_map] at hb
    cases hk : zs[k]? with
    | none => rw [hk] at hb; cases hb
    | some z =>
      rw [hk] at hb
      cases hb
      obtain ⟨o, lt, zw, hle, hzw, -, -, -, -, hval⟩ := hget k z hk
      have hsv : storeVal g z = zw.args[1]! := by unfold storeVal; rw [hzw]; rfl
      show Sem.Refines a' (rv T (storeVal g z))
      rw [hsv]
      unfold wideValOK at hval
      simp only [Bool.and_eq_true] at hval
      obtain ⟨hqn, hm⟩ := hval
      cases hqw : g.value? zw.args[1]! with
      | none => rw [hqw] at hm; cases hm
      | some qw =>
      rw [hqw] at hm
      dsimp only at hm
      simp only [Bool.and_eq_true, beq_iff_eq] at hm
      obtain ⟨⟨⟨hqop, hqargs⟩, hqai⟩, hqsh⟩ := hm
      obtain ⟨hEzz, hLzz⟩ := hEz z (List.mem_of_getElem? hk)
      obtain ⟨zw', -, -, hzw', -, -, hzsz, -⟩ := ecs_chain_mem hch (List.mem_of_getElem? hk)
      rw [hzw] at hzw'; cases hzw'
      have hq1 := ecw_mem_three hzsz 1 (by decide)
      obtain ⟨-, zw', yz, hzw'', hcl, -, -⟩ := hN z hEzz
      change g.value? z = some zw' at hzw''
      rw [hzw] at hzw''; cases hzw''
      obtain ⟨-, qw', yq, hqw', -, hyq, hevq⟩ := hN _ (hcl _ hq1 hqn)
      change g.value? zw.args[1]! = some qw' at hqw'
      rw [hqw] at hqw'; cases hqw'
      have hqid := (hL _ ((hL z hLzz zw hzw).2 _ hq1 hqn) qw hqw).1
      rw [ecT_eval_selectN hqop (regs_of_ok hevq), hqargs, hqid, ← shapeOf_eq] at hevq
      simp only [List.map_cons, List.map_nil, rv_of hyc'] at hevq
      cases hevq
      rw [rv_of hyq]
      rw [hva] at ha
      exact ecw_piece hcu hcw hcallc hcok hyc hR hi0 hpp hpr he2 k a' ha o lt hle qw.auxInt _
        (by rw [hqai, Nat.zero_add]) hqsh
  -- the target's writes are the leaf writes
  have hlist : zs.map (ecwW tabs g T) =
      ecwLeafWrites q (leaves (tabs.ty pp.type)) (zs.map fun z => rv T (storeVal g z)) := by
    apply List.ext_getElem?
    intro k
    unfold ecwLeafWrites
    rw [List.getElem?_map, List.getElem?_map]
    cases hk : zs[k]? with
    | none =>
      have hn : ((leaves (tabs.ty pp.type)).zip (zs.map fun z => rv T (storeVal g z)))[k]? = none := by
        rw [List.getElem?_eq_none_iff] at hk ⊢
        simp only [List.length_zip, List.length_map]
        omega
      rw [hn]; rfl
    | some z =>
      obtain ⟨o, lt, zw, hle, hzw, -, haux, -, haddr, -⟩ := hget k z hk
      have hz : ((leaves (tabs.ty pp.type)).zip (zs.map fun z => rv T (storeVal g z)))[k]? =
          some ((o, lt), rv T (storeVal g z)) :=
        List.getElem?_zip_eq_some.2 ⟨hle, by rw [List.getElem?_map, hk]; rfl⟩
      rw [hz]
      simp only [Option.map_some, ecwW, hzw]
      have hsv : storeVal g z = zw.args[1]! := by unfold storeVal; rw [hzw]; rfl
      obtain ⟨hEzz, hLzz⟩ := hEz z (List.mem_of_getElem? hk)
      obtain ⟨zw', -, -, hzw', -, -, hzsz, -⟩ := ecs_chain_mem hch (List.mem_of_getElem? hk)
      rw [hzw] at hzw'; cases hzw'
      obtain ⟨-, zw', -, hzw'', hcl, -, -⟩ := hN z hEzz
      change g.value? z = some zw' at hzw''
      rw [hzw] at hzw''; cases hzw''
      have hq0 := ecw_mem_three hzsz 0 (by decide)
      have hP := ecw_ptr_eq (ecw_addr hN hL haddr hpT fun hn =>
        ⟨hcl _ hq0 hn, (hL z hLzz zw hzw).2 _ hq0 hn⟩) (hpt z (List.mem_of_getElem? hk) zw hzw)
      rw [hP, hsv, ecw_encode_eqE haux]
  have hW' : M.write q (encode (tabs.ty pp.type) (rv frS u.args[1]!)) = some M1 := by
    rw [← ecw_encode_eqE he1]; exact hW
  obtain ⟨MT', hMT', hR'⟩ := ecw_split _ hwf _ hvT q M M' M1 _ hMR hW' hxs
  rw [← hlist, hWT] at hMT'
  cases hMT'
  exact hR'

end GoFV.Proof.EC

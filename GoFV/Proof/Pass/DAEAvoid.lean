import GoFV.Proof.Pass.DAEMem
import GoFV.Opt.DeadAutosCheck

/-!
# dead auto elim: values and memories without pointers into `U`

`Val.Avoids U`/`Mem.Avoids U` (`Sem/FrameSafe`) are kept by the operations of the semantics when
`U` holds only frame temporaries (`TempU`): encoding an avoiding value gives avoiding bytes,
decoding avoiding bytes an avoiding value (an integer converts to no frame temporary,
`Ptr.ofAddr_ne_temp`), writes of avoiding bytes, `poisonBlock` and `Mem.set` of avoiding
allocations keep a memory avoiding, and so does `Val.retype`. A value of a shape that holds no
pointer (`DAE.noPtrTy`) avoids every `U` of frame temporaries.
-/

namespace GoFV.Proof.DAE

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof.DSE GoFV.Opt.DAE

/-! ## Lists of values and bytes -/

theorem avoidsList_iff {U : Blk → Prop} : {vs : List Val} →
    Val.AvoidsList U vs ↔ ∀ v ∈ vs, Val.Avoids U v
  | [] => by simp [Val.AvoidsList]
  | v :: vs => by simp [Val.AvoidsList, avoidsList_iff (vs := vs)]

/-- All bytes of an array avoid `U`. -/
def BAv (U : Blk → Prop) (bs : Array Byte) : Prop := ∀ x ∈ bs.toList, Byte.Avoids U x

theorem bav_replicate_poison (U : Blk → Prop) (n : Nat) : BAv U (Array.replicate n .poison) := by
  intro x hx
  simp only [Array.toList_replicate, List.mem_replicate] at hx
  rw [hx.2]; trivial

theorem bav_get! {U : Blk → Prop} {bs : Array Byte} (h : BAv U bs) (i : Nat) :
    Byte.Avoids U bs[i]! := by
  by_cases hi : i < bs.size
  · rw [getElem!_pos bs i hi]
    exact h _ (Array.getElem_mem_toList hi)
  · rw [getElem!_neg bs i hi]; trivial

theorem bav_set! {U : Blk → Prop} {d : Array Byte} (h : BAv U d) (i : Nat) {x : Byte}
    (hx : Byte.Avoids U x) : BAv U (d.set! i x) := by
  intro y hy
  simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds] at hy
  rcases List.mem_or_eq_of_mem_set hy with h' | h'
  · exact h y h'
  · rw [h']; exact hx

theorem bav_extract {U : Blk → Prop} {d : Array Byte} (h : BAv U d) (i j : Nat) :
    BAv U (d.extract i j) := by
  intro y hy
  simp only [Array.toList_extract] at hy
  exact h y (List.mem_of_mem_drop (List.mem_of_mem_take hy))

/-- The byte loop of `Mem.write`. -/
theorem bav_writeLoop {U : Blk → Prop} {bs : Array Byte} (hb : BAv U bs) (off : Nat) :
    ∀ (l : List Nat) (d : Array Byte), BAv U d →
      BAv U (l.foldl (fun d i => d.set! (off + i) bs[i]!) d)
  | [], _, h => h
  | i :: l, d, h => bav_writeLoop hb off l _ (bav_set! h _ (bav_get! hb i))

theorem bav_putBytes {U : Blk → Prop} {d src : Array Byte} (hd : BAv U d) (hs : BAv U src)
    (off : Nat) : BAv U (putBytes d off src) := by
  unfold putBytes
  generalize List.range src.size = l
  induction l generalizing d with
  | nil => exact hd
  | cons i l ih =>
    simp only [List.foldl_cons]
    apply ih
    split
    · exact bav_set! hd _ (bav_get! hs i)
    · exact hd

/-! ## Decoding -/

theorem bytesPtr?_mem {bs : Array Byte} {p : Ptr} (h : bytesPtr? bs = some p) :
    Byte.frag p 0 ∈ bs.toList := by
  unfold bytesPtr? at h
  split at h
  · rename_i q hq
    split at h
    · cases h
      exact Array.mem_toList_iff.2 (Array.mem_of_getElem? hq)
    · cases h
  · cases h

theorem decodeInt_avoids {U : Blk → Prop} {bs : Array Byte} (h : BAv U bs) (w : Width) :
    Val.Avoids U (decodeInt w bs) := by
  unfold decodeInt
  split
  · trivial
  · split
    · rename_i p hp
      split
      · trivial
      · exact h _ (bytesPtr?_mem hp)
    · trivial

theorem ofAddr_notU {U : Blk → Prop} (hU : TempU U) (x : BitVec 64) : ¬ U (Ptr.ofAddr x).blk := by
  intro hu
  obtain ⟨n, hn⟩ := hU _ hu
  exact Ptr.ofAddr_ne_temp x 0 n hn

theorem decodePtr_avoids {U : Blk → Prop} (hU : TempU U) {bs : Array Byte} (h : BAv U bs) :
    Val.Avoids U (decodePtr bs) := by
  unfold decodePtr
  split
  · rename_i p hp
    exact h _ (bytesPtr?_mem hp)
  · split
    · exact ofAddr_notU hU _
    · trivial

mutual
theorem decode_avoids {U : Blk → Prop} (hU : TempU U) {bs : Array Byte} (h : BAv U bs)
    (off : Nat) : (t : Ty) → Val.Avoids U (decode bs off t)
  | .int w => by simp only [decode]; exact decodeInt_avoids (bav_extract h _ _) w
  | .bool => by
    simp only [decode]
    split
    · split <;> trivial
    · trivial
  | .ptr _ => by simp only [decode]; exact decodePtr_avoids hU (bav_extract h _ _)
  | .agg fs _ => by
    simp only [decode, Val.Avoids]
    exact decodeFields_avoids hU h off fs
  | .blob n => by
    simp only [decode, Val.Avoids]
    exact bav_extract h _ _
  | .empty => by simp only [decode]; trivial
  | .opaque _ => by simp only [decode]; trivial
  | .other => by simp only [decode]; trivial
  | .mem => by simp only [decode]; trivial
  | .tuple _ => by simp only [decode]; trivial
theorem decodeFields_avoids {U : Blk → Prop} (hU : TempU U) {bs : Array Byte} (h : BAv U bs)
    (off : Nat) : (fs : List (Nat × Ty)) → Val.AvoidsList U (decodeFields bs off fs)
  | [] => by simp only [decodeFields]; trivial
  | (o, t) :: fs => by
    simp only [decodeFields]
    exact ⟨decode_avoids hU h (off + o) t, decodeFields_avoids hU h off fs⟩
end

/-! ## Encoding -/

theorem bav_intBytes (U : Blk → Prop) (n x : Nat) : BAv U (intBytes n x) := by
  intro y hy
  simp [intBytes] at hy
  obtain ⟨_, _, rfl⟩ := hy
  trivial

theorem bav_ptrBytes {U : Blk → Prop} {p : Ptr} (hp : ¬ U p.blk) : BAv U (ptrBytes p) := by
  intro y hy
  simp [ptrBytes] at hy
  obtain ⟨_, _, rfl⟩ := hy
  exact hp

mutual
theorem encode_avoids {U : Blk → Prop} : (t : Ty) → {v : Val} → Val.Avoids U v →
    BAv U (encode t v)
  | t, .poison, _ => by rw [encode_poison]; exact bav_replicate_poison _ _
  | t, .mem m, _ => by rw [encode_mem]; exact bav_replicate_poison _ _
  | t, .tuple vs, _ => by rw [encode_tuple]; exact bav_replicate_poison _ _
  | t, .blob bs, h => by
    rw [encode_blob]
    split
    · intro x hx; exact h x (by simpa using hx)
    · exact bav_replicate_poison _ _
  | .int w, .int w' x, _ => by
    simp only [encode]; split
    · exact bav_intBytes _ _ _
    · exact bav_replicate_poison _ _
  | .int w, .ptr p, h => by
    cases w <;> simp only [encode]
    all_goals first | exact bav_ptrBytes h | exact bav_replicate_poison _ _
  | .ptr _, .ptr p, h => by simp only [encode]; exact bav_ptrBytes h
  | .ptr _, .int w x, _ => by
    cases w <;> simp only [encode]
    all_goals first | exact bav_intBytes _ _ _ | exact bav_replicate_poison _ _
  | .bool, .bool b, _ => by
    simp only [encode]; intro y hy; simp at hy; rw [hy]; trivial
  | .agg fs n, .agg vs, h => by
    simp only [encode]
    exact encodeFields_avoids (bav_replicate_poison _ _) fs h
  | .int w, .bool _, _ | .int w, .agg _, _ | .int w, .empty, _ => by
    cases w <;> simp only [encode] <;> exact bav_replicate_poison _ _
  | .bool, .int _ _, _ | .bool, .ptr _, _ | .bool, .agg _, _ | .bool, .empty, _
  | .ptr _, .bool _, _ | .ptr _, .agg _, _ | .ptr _, .empty, _
  | .agg _ _, .int _ _, _ | .agg _ _, .bool _, _ | .agg _ _, .ptr _, _ | .agg _ _, .empty, _
  | .mem, .int _ _, _ | .mem, .bool _, _ | .mem, .ptr _, _ | .mem, .agg _, _ | .mem, .empty, _
  | .tuple _, .int _ _, _ | .tuple _, .bool _, _ | .tuple _, .ptr _, _ | .tuple _, .agg _, _
  | .tuple _, .empty, _
  | .other, .int _ _, _ | .other, .bool _, _ | .other, .ptr _, _ | .other, .agg _, _
  | .other, .empty, _
  | .blob _, .int _ _, _ | .blob _, .bool _, _ | .blob _, .ptr _, _ | .blob _, .agg _, _
  | .blob _, .empty, _
  | .empty, .int _ _, _ | .empty, .bool _, _ | .empty, .ptr _, _ | .empty, .agg _, _
  | .empty, .empty, _
  | .opaque _, .int _ _, _ | .opaque _, .bool _, _ | .opaque _, .ptr _, _ | .opaque _, .agg _, _
  | .opaque _, .empty, _ => by simp only [encode]; exact bav_replicate_poison _ _
theorem encodeFields_avoids {U : Blk → Prop} {buf : Array Byte} (hb : BAv U buf) :
    (fs : List (Nat × Ty)) → {vs : List Val} → Val.AvoidsList U vs →
      BAv U (encodeFields buf fs vs)
  | (o, t) :: fs, v :: vs, ⟨h1, h2⟩ => by
    simp only [encodeFields]
    exact encodeFields_avoids (bav_putBytes hb (encode_avoids t h1) o) fs h2
  | [], _, _ => by simp only [encodeFields]; exact hb
  | _ :: _, [], _ => by simp only [encodeFields]; exact hb
end

/-! ## Memories -/

theorem mem_setL {b : Blk} {a : Alloc} {e : Blk × Alloc} : ∀ {l : List (Blk × Alloc)},
    e ∈ setL b a l → e = (b, a) ∨ e ∈ l
  | [], h => by simp [DSE.setL] at h; exact .inl h
  | e' :: l, h => by
    unfold DSE.setL at h
    split at h
    · rcases List.mem_cons.1 h with h | h
      · exact .inl h
      · exact .inr (List.mem_cons_of_mem _ h)
    · rcases List.mem_cons.1 h with h | h
      · exact .inr (h ▸ List.mem_cons_self)
      · rcases mem_setL h with h | h
        · exact .inl h
        · exact .inr (List.mem_cons_of_mem _ h)

theorem memAvoids_set {U : Blk → Prop} {m : Mem} (h : m.Avoids U) {b : Blk} {a : Alloc}
    (ha : ¬ U b → BAv U a.data) : (m.set b a).Avoids U := by
  intro b' a' hm hu
  rw [set_toList] at hm
  rcases mem_setL hm with he | he
  · cases he; exact ha hu
  · exact h b' a' he hu

theorem find?_mem {m : Mem} {b : Blk} {a : Alloc} (h : m.find? b = some a) :
    (b, a) ∈ m.blocks.toList := by
  rw [find?_toList] at h
  cases he : m.blocks.toList.find? (·.1 == b) with
  | none => rw [he] at h; cases h
  | some e =>
    rw [he] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hb0 : (e.1 == b) = true := List.find?_some (p := fun x : Blk × Alloc => x.fst == b) he
    have hb := beq_iff_eq.1 hb0
    have hm := List.mem_of_find?_eq_some he
    obtain ⟨b', a'⟩ := e
    simp only at h hb
    subst h hb
    exact hm

theorem memAvoids_find {U : Blk → Prop} {m : Mem} (h : m.Avoids U) {b : Blk} {a : Alloc}
    (ha : m.find? b = some a) (hu : ¬ U b) : BAv U a.data :=
  h b a (find?_mem ha) hu

theorem memAvoids_write {U : Blk → Prop} {m m1 : Mem} (h : m.Avoids U) {p : Ptr} {bs : Array Byte}
    (hw : m.write p bs = some m1) (hb : ¬ U p.blk → BAv U bs) : m1.Avoids U := by
  unfold Mem.write at hw
  by_cases he : bs.isEmpty = true
  · simp only [he, ite_true] at hw; cases hw; exact h
  simp only [he, Bool.false_eq_true, ite_false] at hw
  cases ha : m.find? p.blk with
  | none => rw [ha] at hw; cases hw
  | some a =>
    rw [ha] at hw
    simp only [Option.bind_eq_bind, Option.bind_some] at hw
    split at hw
    · cases hw
      exact memAvoids_set h fun hu =>
        bav_writeLoop (hb hu) _ _ _ (memAvoids_find h ha hu)
    · cases hw

theorem memAvoids_poison {U : Blk → Prop} {m : Mem} (h : m.Avoids U) (b : Blk) :
    (m.poisonBlock b).Avoids U := by
  unfold Mem.poisonBlock
  split
  · exact memAvoids_set h fun _ => bav_replicate_poison _ _
  · exact h

theorem read_avoids {U : Blk → Prop} {m : Mem} (h : m.Avoids U) {p : Ptr} {n : Nat}
    {bs : Array Byte} (hr : m.read p n = some bs) (hu : ¬ U p.blk) : BAv U bs := by
  unfold Mem.read at hr
  by_cases hn : (n == 0) = true
  · simp only [hn, ite_true] at hr; cases hr; intro x hx; simp at hx
  simp only [hn, Bool.false_eq_true, ite_false] at hr
  cases ha : m.find? p.blk with
  | none => rw [ha] at hr; cases hr
  | some a =>
    rw [ha] at hr
    simp only [Option.bind_eq_bind, Option.bind_some] at hr
    split at hr
    · cases hr; exact bav_extract (memAvoids_find h ha hu) _ _
    · cases hr

theorem load_avoids {U : Blk → Prop} (hU : TempU U) {m : Mem} (h : m.Avoids U) (t : Ty) {p : Ptr}
    (hu : ¬ U p.blk) : Val.Avoids U (m.load t p) := by
  unfold Mem.load
  split
  · trivial
  · trivial
  · trivial
  · trivial
  · split
    · rename_i bs hr; exact decode_avoids hU (read_avoids h hr hu) 0 _
    · trivial

/-! ## Retyping and shapes -/

theorem addr_none_notU {U : Blk → Prop} (hU : TempU U) {p : Ptr} (h : p.addr? = none) :
    ¬ U p.blk := by
  intro hu
  obtain ⟨n, hn⟩ := hU _ hu
  simp [Ptr.addr?, hn, Blk.base?] at h

mutual
theorem retype_avoids {U : Blk → Prop} (hU : TempU U) :
    ∀ (t : Ty) {v : Val}, Val.Avoids U v → Val.Avoids U (v.retype t)
  | t, .poison, _ => by cases t <;> trivial
  | .int w', .int w x, _ => by unfold Val.retype; split <;> trivial
  | .int w', .ptr p, h => by
    cases w' with
    | w64 =>
      unfold Val.retype
      split
      · trivial
      · exact h
    | _ => trivial
  | .ptr _, .int w x, _ => by
    cases w
    all_goals first | exact ofAddr_notU hU _ | trivial
  | .ptr _, .ptr p, h => h
  | .bool, .bool _, _ => trivial
  | .mem, .mem _, h => h
  | .tuple ts, .tuple vs, h => by
    unfold Val.retype
    cases hr : Val.retypePre ts vs with
    | none => trivial
    | some ws => exact retypePre_avoids hU ts h hr
  | .agg fs n, .agg vs, h => by
    unfold Val.retype
    cases hr : Val.retypeFields fs vs with
    | none => trivial
    | some ws => exact retypeFields_avoids hU fs h hr
  | .blob n, .blob bs, h => by
    unfold Val.retype
    split
    · exact h
    · trivial
  | .empty, .empty, _ => trivial
  | .int _, .bool _, _ | .int _, .mem _, _ | .int _, .tuple _, _ | .int _, .agg _, _
  | .int _, .blob _, _ | .int _, .empty, _ => trivial
  | .bool, .int _ _, _ | .bool, .mem _, _ | .bool, .tuple _, _ | .bool, .ptr _, _
  | .bool, .agg _, _ | .bool, .blob _, _ | .bool, .empty, _ => trivial
  | .mem, .int _ _, _ | .mem, .bool _, _ | .mem, .tuple _, _ | .mem, .ptr _, _
  | .mem, .agg _, _ | .mem, .blob _, _ | .mem, .empty, _ => trivial
  | .tuple _, .int _ _, _ | .tuple _, .bool _, _ | .tuple _, .mem _, _ | .tuple _, .ptr _, _
  | .tuple _, .agg _, _ | .tuple _, .blob _, _ | .tuple _, .empty, _ => trivial
  | .other, .int _ _, _ | .other, .bool _, _ | .other, .mem _, _ | .other, .tuple _, _
  | .other, .ptr _, _ | .other, .agg _, _ | .other, .blob _, _ | .other, .empty, _ => trivial
  | .ptr _, .bool _, _ | .ptr _, .mem _, _ | .ptr _, .tuple _, _ | .ptr _, .agg _, _
  | .ptr _, .blob _, _ | .ptr _, .empty, _ => trivial
  | .agg _ _, .int _ _, _ | .agg _ _, .bool _, _ | .agg _ _, .mem _, _ | .agg _ _, .tuple _, _
  | .agg _ _, .ptr _, _ | .agg _ _, .blob _, _ | .agg _ _, .empty, _ => trivial
  | .blob _, .int _ _, _ | .blob _, .bool _, _ | .blob _, .mem _, _ | .blob _, .tuple _, _
  | .blob _, .ptr _, _ | .blob _, .agg _, _ | .blob _, .empty, _ => trivial
  | .empty, .int _ _, _ | .empty, .bool _, _ | .empty, .mem _, _ | .empty, .tuple _, _
  | .empty, .ptr _, _ | .empty, .agg _, _ | .empty, .blob _, _ => trivial
  | .opaque _, .int _ _, _ | .opaque _, .bool _, _ | .opaque _, .mem _, _
  | .opaque _, .tuple _, _ | .opaque _, .ptr _, _ | .opaque _, .agg _, _
  | .opaque _, .blob _, _ | .opaque _, .empty, _ => trivial
theorem retypePre_avoids {U : Blk → Prop} (hU : TempU U) :
    ∀ (ts : List Ty) {vs ws : List Val}, Val.AvoidsList U vs → Val.retypePre ts vs = some ws →
      Val.AvoidsList U ws
  | [], _, _, h, hr => by cases hr; exact h
  | _ :: _, [], _, _, hr => by simp [Val.retypePre] at hr
  | t :: ts, v :: vs, ws, ⟨h1, h2⟩, hr => by
    unfold Val.retypePre at hr
    cases h' : Val.retypePre ts vs with
    | none => rw [h'] at hr; cases hr
    | some ws' =>
      rw [h'] at hr; cases hr
      exact ⟨retype_avoids hU t h1, retypePre_avoids hU ts h2 h'⟩
theorem retypeFields_avoids {U : Blk → Prop} (hU : TempU U) :
    ∀ (fs : List (Nat × Ty)) {vs ws : List Val}, Val.AvoidsList U vs →
      Val.retypeFields fs vs = some ws → Val.AvoidsList U ws
  | [], [], _, _, hr => by cases hr; trivial
  | [], _ :: _, _, _, hr => by simp [Val.retypeFields] at hr
  | _ :: _, [], _, _, hr => by simp [Val.retypeFields] at hr
  | (o, t) :: fs, v :: vs, ws, ⟨h1, h2⟩, hr => by
    unfold Val.retypeFields at hr
    cases h' : Val.retypeFields fs vs with
    | none => rw [h'] at hr; cases hr
    | some ws' =>
      rw [h'] at hr; cases hr
      exact ⟨retype_avoids hU t h1, retypeFields_avoids hU fs h2 h'⟩
end

mutual
/-- **A value of a pointer-free shape avoids every set of frame temporaries.** -/
theorem noPtr_avoids {U : Blk → Prop} (hU : TempU U) :
    ∀ {t : Ty} {v : Val}, v.hasTy t = true → noPtrTy t = true → Val.Avoids U v
  | _, .poison, _, _ => trivial
  | .int _, .int _ _, _, _ => trivial
  | .int w, .ptr p, h, _ => by
    cases w <;> simp only [Val.hasTy, reduceCtorEq] at h
    exact addr_none_notU hU (Option.isNone_iff_eq_none.1 h)
  | .bool, .bool _, _, _ => trivial
  | .empty, .empty, _, _ => trivial
  | .agg fs _, .agg vs, h, hn => by
    simp only [Val.hasTy] at h
    simp only [noPtrTy] at hn
    exact noPtrFields_avoids hU fs h hn
  | .ptr _, _, _, hn | .mem, _, _, hn | .tuple _, _, _, hn | .blob _, _, _, hn => by
    simp [noPtrTy] at hn
  | .int _, .bool _, h, _ | .int _, .mem _, h, _ | .int _, .tuple _, h, _
  | .int _, .agg _, h, _ | .int _, .blob _, h, _ | .int _, .empty, h, _
  | .bool, .int _ _, h, _ | .bool, .mem _, h, _ | .bool, .tuple _, h, _ | .bool, .ptr _, h, _
  | .bool, .agg _, h, _ | .bool, .blob _, h, _ | .bool, .empty, h, _
  | .empty, .int _ _, h, _ | .empty, .bool _, h, _ | .empty, .mem _, h, _
  | .empty, .tuple _, h, _ | .empty, .ptr _, h, _ | .empty, .agg _, h, _ | .empty, .blob _, h, _
  | .other, .int _ _, h, _ | .other, .bool _, h, _ | .other, .mem _, h, _
  | .other, .tuple _, h, _ | .other, .ptr _, h, _ | .other, .agg _, h, _ | .other, .blob _, h, _
  | .other, .empty, h, _
  | .opaque _, .int _ _, h, _ | .opaque _, .bool _, h, _ | .opaque _, .mem _, h, _
  | .opaque _, .tuple _, h, _ | .opaque _, .ptr _, h, _ | .opaque _, .agg _, h, _
  | .opaque _, .blob _, h, _ | .opaque _, .empty, h, _
  | .agg _ _, .int _ _, h, _ | .agg _ _, .bool _, h, _ | .agg _ _, .mem _, h, _
  | .agg _ _, .tuple _, h, _ | .agg _ _, .ptr _, h, _ | .agg _ _, .blob _, h, _
  | .agg _ _, .empty, h, _ => by simp [Val.hasTy] at h
theorem noPtrFields_avoids {U : Blk → Prop} (hU : TempU U) :
    ∀ (fs : List (Nat × Ty)) {vs : List Val}, Val.hasTyList vs (fs.map (·.2)) = true →
      noPtrFields fs = true → Val.AvoidsList U vs
  | [], [], _, _ => trivial
  | [], _ :: _, h, _ => by simp [Val.hasTyList] at h
  | _ :: _, [], h, _ => by simp [Val.hasTyList] at h
  | (o, t) :: fs, v :: vs, h, hn => by
    simp only [List.map_cons, Val.hasTyList, Bool.and_eq_true] at h
    simp only [noPtrFields, Bool.and_eq_true] at hn
    exact ⟨noPtr_avoids hU h.1 hn.1, noPtrFields_avoids hU fs h.2 hn.2⟩
end

end GoFV.Proof.DAE

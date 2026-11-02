import GoFV.Proof.Retype
import GoFV.Proof.PtrAddr
import GoFV.Opt.RewriteCheck

/-!
# Struct-load expansions: a struct's bytes are its fields' bytes (issue #151)

`decode_congr`: decoding a shape whose fields lie inside it (`RewriteCheck.layoutOK`) reads only
its own bytes. `read_sub`: a valid read covers every sub-range, read at the pointer moved by the
sub-range's offset (the read ends below `2^64` and inside the block's window). `load_field`: so
a `Load` of a field at its offset reads what decoding the struct's bytes gives for that field.
`structLoad_ref`: `Load <agg fs n> p m`, as `Sem.loadOp` and retyped at the shape, is refined by
`StructMake` of the field `Load`s at `OffPtr [oᵢ] p` (the denotation of `rewriteStructLoad`'s
result), whatever `p` and `m` are.
-/

namespace GoFV.Proof.Pass.StructLoad

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck

theorem getElem?_extract_add (bs : Array Byte) (o k i : Nat) :
    (bs.extract o (o + k))[i]? = if i < k then bs[o + i]? else none := by
  rw [Array.getElem?_extract]
  by_cases hi : i < k
  · by_cases hs : o + i < bs.size
    · simp only [hi, ite_true]
      rw [if_pos (by omega)]
    · simp only [hi, ite_true]
      rw [if_neg (by omega), Array.getElem?_eq_none (by omega)]
  · simp only [hi, ite_false]
    rw [if_neg (by omega)]

theorem extract_congr {bs bs' : Array Byte} {o o' k : Nat}
    (h : ∀ i, i < k → bs[o + i]? = bs'[o' + i]?) :
    bs.extract o (o + k) = bs'.extract o' (o' + k) := by
  apply Array.ext_getElem?
  intro i
  rw [getElem?_extract_add, getElem?_extract_add]
  by_cases hi : i < k
  · simp only [hi, ite_true]; exact h i hi
  · simp only [hi, ite_false]

/-- The `k` bytes at `o + a` agree when the `n ≥ a + k` bytes at `o` do. -/
theorem extract_congr_at {bs bs' : Array Byte} {o o' n : Nat} (a k : Nat) (hk : a + k ≤ n)
    (h : ∀ i, i < n → bs[o + i]? = bs'[o' + i]?) :
    bs.extract (o + a) (o + a + k) = bs'.extract (o' + a) (o' + a + k) :=
  extract_congr fun i hi => by rw [Nat.add_assoc, Nat.add_assoc]; exact h (a + i) (by omega)

mutual
/-- Decoding a well-laid-out shape reads only its own bytes. -/
theorem decode_congr {bs bs' : Array Byte} {o o' : Nat} : (t : Ty) → layoutOK t = true →
    (∀ i, i < t.size → bs[o + i]? = bs'[o' + i]?) → decode bs o t = decode bs' o' t
  | .int w, _, h => by
    simp only [decode]; rw [extract_congr (k := w.bytes) h]
  | .bool, _, h => by
    have h0 := h 0 (by simp [Ty.size])
    simp only [Nat.add_zero] at h0
    simp only [decode, h0]
  | .ptr _, _, h => by
    simp only [decode]; rw [extract_congr (k := 8) h]
  | .agg fs n, hl, h => by
    simp only [decode]
    rw [decodeFields_congr n fs (by simpa only [layoutOK] using hl) h]
  | .blob n, _, h => by
    simp only [decode]; rw [extract_congr (k := n) h]
  | .empty, _, _ => rfl
  | .opaque _, _, _ => rfl
  | .other, _, _ => rfl
  | .mem, _, _ => rfl
  | .tuple _, _, _ => rfl
  | .str, _, h => by
    simp only [decode]
    have h0 := extract_congr_at 0 8 (by simp [Ty.size]) h
    have h8 := extract_congr_at 8 8 (by simp [Ty.size]) h
    simp only [Nat.add_zero] at h0
    rw [show o + 16 = o + 8 + 8 by omega, show o' + 16 = o' + 8 + 8 by omega, h0, h8]
  | .slice _, _, h => by
    simp only [decode]
    have h0 := extract_congr_at 0 8 (by simp [Ty.size]) h
    have h8 := extract_congr_at 8 8 (by simp [Ty.size]) h
    have h16 := extract_congr_at 16 8 (by simp [Ty.size]) h
    simp only [Nat.add_zero] at h0
    rw [show o + 16 = o + 8 + 8 by omega, show o' + 16 = o' + 8 + 8 by omega, h0, h8,
      show o + 8 + 8 = o + 16 by omega, show o' + 8 + 8 = o' + 16 by omega,
      show o + 24 = o + 16 + 8 by omega, show o' + 24 = o' + 16 + 8 by omega, h16]
theorem decodeFields_congr {bs bs' : Array Byte} {o o' : Nat} (n : Nat) :
    (fs : List (Nat × Ty)) → layoutsOK n fs = true →
    (∀ i, i < n → bs[o + i]? = bs'[o' + i]?) → decodeFields bs o fs = decodeFields bs' o' fs
  | [], _, _ => rfl
  | (p, t) :: fs, hl, h => by
    simp only [layoutsOK, Bool.and_eq_true, decide_eq_true_eq] at hl
    simp only [decodeFields]
    rw [decode_congr (bs := bs) (bs' := bs') (o := o + p) (o' := o' + p) t hl.1.2
      (fun i hi => by
        rw [Nat.add_assoc, Nat.add_assoc]
        exact h (p + i) (by omega)), decodeFields_congr n fs hl.2 h]
end

theorem decode_extract (bs : Array Byte) (o : Nat) {t : Ty} (hl : layoutOK t = true) :
    decode (bs.extract o (o + t.size)) 0 t = decode bs o t :=
  decode_congr t hl fun i hi => by
    rw [Nat.zero_add, getElem?_extract_add]
    simp only [hi, ite_true]

theorem allPoison_congr {bs bs' : Array Byte} {o o' n : Nat}
    (h : ∀ i, i < n → bs[o + i]? = bs'[o' + i]?) : allPoison bs o n = allPoison bs' o' n := by
  unfold allPoison; rw [extract_congr h]

mutual
/-- `decodeLoad` of a well-laid-out shape reads only its own bytes. -/
theorem decodeLoad_congr {bs bs' : Array Byte} {o o' : Nat} : (t : Ty) → layoutOK t = true →
    (∀ i, i < t.size → bs[o + i]? = bs'[o' + i]?) → decodeLoad bs o t = decodeLoad bs' o' t
  | .agg fs n, hl, h => by
    simp only [decodeLoad]
    rw [allPoison_congr (n := n) h,
      decodeLoadFields_congr n fs (by simpa only [layoutOK] using hl) h]
  | .int w, hl, h => by simp only [decodeLoad]; exact decode_congr _ hl h
  | .bool, hl, h => by simp only [decodeLoad]; exact decode_congr _ hl h
  | .ptr _, hl, h => by simp only [decodeLoad]; exact decode_congr _ hl h
  | .blob _, hl, h => by simp only [decodeLoad]; exact decode_congr _ hl h
  | .opaque _, _, _ => rfl
  | .empty, _, _ => rfl
  | .other, _, _ => rfl
  | .mem, _, _ => rfl
  | .tuple _, _, _ => rfl
  | .str, hl, h => by
    simp only [decodeLoad]
    rw [allPoison_congr (n := 16) h, decode_congr _ hl h]
  | .slice _, hl, h => by
    simp only [decodeLoad]
    rw [allPoison_congr (n := 24) h, decode_congr _ hl h]
theorem decodeLoadFields_congr {bs bs' : Array Byte} {o o' : Nat} (n : Nat) :
    (fs : List (Nat × Ty)) → layoutsOK n fs = true →
    (∀ i, i < n → bs[o + i]? = bs'[o' + i]?) →
      decodeLoadFields bs o fs = decodeLoadFields bs' o' fs
  | [], _, _ => rfl
  | (p, t) :: fs, hl, h => by
    simp only [layoutsOK, Bool.and_eq_true, decide_eq_true_eq] at hl
    simp only [decodeLoadFields]
    rw [decodeLoad_congr (bs := bs) (bs' := bs') (o := o + p) (o' := o' + p) t hl.1.2
      (fun i hi => by
        rw [Nat.add_assoc, Nat.add_assoc]
        exact h (p + i) (by omega)), decodeLoadFields_congr n fs hl.2 h]
end

theorem decodeLoad_extract (bs : Array Byte) (o : Nat) {t : Ty} (hl : layoutOK t = true) :
    decodeLoad (bs.extract o (o + t.size)) 0 t = decodeLoad bs o t :=
  decodeLoad_congr t hl fun i hi => by
    rw [Nat.zero_add, getElem?_extract_add]
    simp only [hi, ite_true]

/-- What a valid non-empty read says about its pointer. -/
theorem read_facts {m : Mem} {p : Ptr} {n : Nat} {bs : Array Byte} (hr : m.read p n = some bs)
    (hn : n ≠ 0) : ∃ a, m.find? p.blk = some a ∧ p.off.toNat + n ≤ a.data.size ∧
      p.off.toNat + n < 2 ^ 64 ∧ p.blk.endsInWindow (p.off.toNat + n) = true ∧
      bs = a.data.extract p.off.toNat (p.off.toNat + n) := by
  unfold Mem.read at hr
  simp only [beq_iff_eq, hn, ite_false] at hr
  cases ha : m.find? p.blk with
  | none => rw [ha] at hr; cases hr
  | some a =>
    rw [ha] at hr
    simp only [Option.bind_eq_bind, Option.bind_some] at hr
    split at hr
    · rename_i hok
      cases hr
      exact ⟨a, rfl, hok.1, hok.2.1, hok.2.2, rfl⟩
    · cases hr

theorem off_add {p : Ptr} {n o : Nat} (hlt : p.off.toNat + n < 2 ^ 64) (ho : o ≤ n) :
    (p.add (BitVec.ofNat 64 o)).off.toNat = p.off.toNat + o := by
  simp only [Ptr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- **A sub-range of a valid read** is read at the pointer moved by its offset. -/
theorem read_sub {m : Mem} {p : Ptr} {n : Nat} {bs : Array Byte} (hr : m.read p n = some bs)
    {o k : Nat} (hk : o + k ≤ n) :
    m.read (p.add (BitVec.ofNat 64 o)) k = some (bs.extract o (o + k)) := by
  by_cases hk0 : k = 0
  · subst hk0
    unfold Mem.read
    simp only [beq_self_eq_true, ite_true, Nat.add_zero]
    simp only [pure, Option.some.injEq]
    apply Array.ext_getElem?
    intro i
    rw [Array.getElem?_extract]
    simp
    intro h
    omega
  have hn : n ≠ 0 := by omega
  obtain ⟨a, ha, h1, h2, h3, rfl⟩ := read_facts hr hn
  have hoff := off_add h2 (o := o) (by omega)
  unfold Mem.read
  simp only [beq_iff_eq, hk0, ite_false]
  have hblk : (p.add (BitVec.ofNat 64 o)).blk = p.blk := rfl
  rw [hblk, ha]
  simp only [Option.bind_eq_bind, Option.bind_some, hoff]
  have hw : p.blk.endsInWindow (p.off.toNat + o + k) = true := by
    unfold Blk.endsInWindow at h3 ⊢
    split
    · rename_i w hw
      rw [hw] at h3
      simp only [decide_eq_true_eq] at h3 ⊢
      omega
    · rfl
  rw [if_pos ⟨by omega, by omega, hw⟩, Array.extract_extract]
  congr 2
  omega

/-- **A field `Load`** at its offset reads what `decodeLoad` of the struct's bytes gives. -/
theorem load_field {m : Mem} {p : Ptr} {n : Nat} {bs : Array Byte} (hr : m.read p n = some bs)
    {o : Nat} {t : Ty} (hl : layoutOK t = true) (hk : o + t.size ≤ n) :
    m.load t (p.add (BitVec.ofNat 64 o)) = decodeLoad bs o t := by
  have h := read_sub hr hk
  cases t with
  | empty => rfl
  | other => rfl
  | mem => rfl
  | tuple _ => rfl
  | _ =>
    unfold Mem.load
    simp only [h]
    exact decodeLoad_extract bs o hl

theorem ofInt_toInt_ofNat (o : Nat) : BitVec.ofInt 64 (Int64.ofNat o).toInt = BitVec.ofNat 64 o := by
  rw [show (Int64.ofNat o).toInt = (Int64.ofNat o).toBitVec.toInt from rfl, BitVec.ofInt_toInt]
  rfl

/-- A field of a struct-load expansion: `Load <t> (OffPtr <pt> [o] p) m`, retyped as `den` does. -/
def fieldVal (P Mv : Val) (o : Nat) (pt t : Ty) : Val :=
  (loadOp t [(PtrOps.offPtr (Int64.ofNat o) [P]).retype pt, Mv]).retype t

/-- `R` relates the values to the fields pointwise (equal lengths). -/
def Fields (R : Val → Nat × Ty → Prop) : List Val → List (Nat × Ty) → Prop
  | [], [] => True
  | v :: vs, f :: fs => R v f ∧ Fields R vs fs
  | _, _ => False

theorem retypeFields_decode (bs : Array Byte) : ∀ (fs : List (Nat × Ty)) (vs : List Val),
    Fields (fun v f => v = (decodeLoad bs f.1 f.2).retype f.2) vs fs →
    Val.retypeFields fs (decodeLoadFields bs 0 fs) = Val.retypeFields fs vs
  | [], [], _ => rfl
  | (o, t) :: fs, v :: vs, ⟨h, hs⟩ => by
    simp only [decodeLoadFields, Val.retypeFields, h, Nat.zero_add, Val.retype_idem]
    rw [retypeFields_decode bs fs vs hs]
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem Fields.imp_mem {R S : Val → Nat × Ty → Prop} : ∀ {vs : List Val} {fs : List (Nat × Ty)},
    (∀ v f, f ∈ fs → R v f → S v f) → Fields R vs fs → Fields S vs fs
  | [], [], _, _ => trivial
  | _ :: _, _ :: _, h, ⟨hr, hs⟩ => ⟨h _ _ List.mem_cons_self hr,
      Fields.imp_mem (fun v f hf => h v f (List.mem_cons_of_mem _ hf)) hs⟩
  | [], _ :: _, _, h | _ :: _, [], _, h => h.elim

theorem layouts_mem {n : Nat} : ∀ {fs : List (Nat × Ty)}, layoutsOK n fs = true →
    ∀ f ∈ fs, layoutOK f.2 = true ∧ f.1 + f.2.size ≤ n
  | [], _, f, hf => by cases hf
  | (o, t) :: gs, hl, f, hf => by
    simp only [layoutsOK, Bool.and_eq_true, decide_eq_true_eq] at hl
    rcases List.mem_cons.1 hf with rfl | hf
    · exact ⟨hl.1.2, hl.1.1⟩
    · exact layouts_mem hl.2 f hf

/-- **A struct `Load` is refined by `StructMake` of its field `Load`s** (`rewriteStructLoad`), for
any pointer and memory values, when the fields lie inside the struct at offsets below its size. -/
theorem structLoad_ref {fs : List (Nat × Ty)} {n : Nat} (hl : layoutsOK n fs = true)
    (ho : ∀ f ∈ fs, f.1 < n) (P Mv : Val) {vs : List Val}
    (hvs : Fields (fun v f => ∃ e, v = fieldVal P Mv f.1 (.ptr e) f.2) vs fs) :
    Refines ((loadOp (.agg fs n) [P, Mv]).retype (.agg fs n))
      ((Comp.make vs).retype (.agg fs n)) := by
  by_cases hP : ∃ p m, P.asPtrWord = some p ∧ Mv = .mem m
  · obtain ⟨p, m, hp, rfl⟩ := hP
    have hl0 : loadOp (.agg fs n) [P, .mem m] = m.load (.agg fs n) p := by
      simp only [loadOp, hp]
    rw [hl0]
    unfold Mem.load
    simp only
    cases hr : m.read p (Ty.agg fs n).size with
    | none => exact .poison _
    | some bs =>
      simp only [Ty.size] at hr
      have hfields : Fields (fun v f => v = (decodeLoad bs f.1 f.2).retype f.2) vs fs := by
        refine Fields.imp_mem (fun v f hf ⟨e, he⟩ => ?_) hvs
        obtain ⟨hlo, hle⟩ := layouts_mem hl f hf
        have hon := ho f hf
        obtain ⟨a, _, _, h2, h3, _⟩ := read_facts hr (by omega)
        have hin : ∀ w, p.blk.window? = some w → p.off.toNat + f.1 < w := by
          intro w hw
          unfold Blk.endsInWindow at h3
          rw [hw] at h3
          simp only [decide_eq_true_eq] at h3
          omega
        have hwin : (p.add (BitVec.ofNat 64 f.1)).inWindow = true := by
          unfold Ptr.inWindow
          rw [off_add h2 (Nat.le_of_lt hon)]
          show (match p.blk.window? with
            | some w => decide (p.off.toNat + f.1 < w)
            | none => true) = true
          split
          · rename_i w hw
            exact decide_eq_true (hin w hw)
          · rfl
        -- the field's address, a pointer or (for an integer word) the integer moved by `f.1`
        have hq : ∃ Q, PtrOps.offPtr (Int64.ofNat f.1) [P] = Q ∧ Q.retype (.ptr e) = Q ∧
            Q.asPtrWord = some (p.add (BitVec.ofNat 64 f.1)) := by
          rcases P with ⟨_ | _ | _ | _, x⟩ | _ | _ | _ | q | _ | _ | _ | _ <;>
            simp only [Val.asPtrWord, reduceCtorEq] at hp
          · simp only [Option.some.injEq] at hp; subst hp
            have hq : PtrOps.offPtr (Int64.ofNat f.1) [.int .w64 x] =
                .int .w64 (x + BitVec.ofNat 64 f.1) := by
              show PtrOps.wordRes x (BitVec.ofInt 64 (Int64.ofNat f.1).toInt) = _
              rw [ofInt_toInt_ofNat]
              unfold PtrOps.wordRes
              rw [if_pos hwin]
            refine ⟨_, hq, rfl, ?_⟩
            simp only [Val.asPtrWord, Ptr.ofAddr_add_of_inWindow hwin]
          · simp only [Option.some.injEq] at hp; subst hp
            have hq : PtrOps.offPtr (Int64.ofNat f.1) [.ptr q] =
                (q.add (BitVec.ofNat 64 f.1)).word := by
              show PtrOps.ptrRes (q.add (BitVec.ofInt 64 (Int64.ofNat f.1).toInt)) = _
              rw [ofInt_toInt_ofNat]
              unfold PtrOps.ptrRes
              rw [if_pos hwin]
            exact ⟨_, hq, Ptr.word_retype_ptr _ e, Ptr.word_asPtrWord _⟩
        obtain ⟨Q, hQ, hQr, hQp⟩ := hq
        unfold fieldVal at he
        rw [he, hQ, hQr]
        show (loadOp f.2 [Q, .mem m]).retype f.2 = _
        simp only [loadOp, hQp]
        rw [load_field hr hlo hle]
      dsimp only
      by_cases hap : allPoison bs 0 n = true
      · have : decodeLoad bs 0 (.agg fs n) = .poison := by simp only [decodeLoad, hap, ite_true]
        rw [this]; exact .poison _
      have : decodeLoad bs 0 (.agg fs n) = .agg (decodeLoadFields bs 0 fs) := by
        simp only [decodeLoad]; rw [ite_eq_right_iff.2 (fun h => absurd h hap)]
      rw [this]
      simp only [Comp.make, Val.retype]
      rw [retypeFields_decode bs fs vs hfields]
      exact Refines.refl _
  · have : loadOp (.agg fs n) [P, Mv] = .poison := by
      unfold loadOp
      split
      · rename_i a m h
        simp only [List.cons.injEq, and_true] at h
        obtain ⟨rfl, rfl⟩ := h
        split
        · rename_i p hp
          exact absurd ⟨p, m, hp, rfl⟩ hP
        · rfl
      · rfl
    rw [this]
    exact .poison _

end GoFV.Proof.Pass.StructLoad

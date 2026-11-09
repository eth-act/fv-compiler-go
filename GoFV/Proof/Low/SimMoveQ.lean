import GoFV.Proof.Low.SimBase
import GoFV.Proof.PtrAddr
import GoFV.Proof.Pass.MemCombineBytes

variable [GoFV.SSA.Sem.Addrs]

/-!
# A 128-bit store lowering a `Move` refines it (issue #385)

`ARM64.rules:418` lowers `(Move [16] dst src mem)` to `(FMOVQstore dst (FMOVQload src mem) mem)`
and `426` `(Move [32] dst src mem)` to `(FSTPQ dst (Select0 (FLDPQ src mem)) (Select1 (FLDPQ src
mem)) mem)`; `779`, `782`, `909`, `913` fold an offset and a symbol or frame variable into the
store (`moveQLower`). `moveQ_lower_eval`: when the store's address (`Sem.symAddr` at its offset
and aux) is the `Move`'s destination (`AddrRef`), its values refine the 16-byte halves the `Move`
copies (`qPart`) and its memory refines the `Move`'s, the store refines the generic `Move`
(`memRoot`: the read of `n` bytes at the source, then their write at the destination), both
shaped (`rty`).

* The halves are sub-reads of the `Move`'s read (`read_extract`), so the stored bytes refine the
  copied ones.
* `FSTPQ`'s second address (`pairAddr`, offset `+16`) is its first moved by 16: on a symbol or a
  pointer base by the offsets, on an integer base because the `Move`'s 32-byte write stays inside
  the destination's window (`Ptr.ofAddr_add_of_inWindow`; `symAddr_add`).
* Two adjacent writes are the write of their concatenation (`write_append`).

The module sits below `SimMem.lean`, whose `atomPair` simulation uses `moveQ_lower_eval`.
-/

namespace GoFV.Proof.Low.Sim

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof GoFV.Proof.Low GoFV.Proof.MemCombine GoFV.Proof.CSE.Mem

/-! ## Memory -/

/-- **Adjacent writes**: a write of `A ++ B` at `p` is the write of `A` at `p`, then of `B`
`A.size` bytes higher. -/
private theorem write_append {m m2 : Mem} {p : Ptr} {A B : Array Byte} (hA : 0 < A.size)
    (hB : 0 < B.size) (h : m.write p (A ++ B) = some m2) :
    (m.write p A).bind (·.write (p.add (BitVec.ofNat 64 A.size)) B) = some m2 := by
  have hpos : 0 < (A ++ B).size := by rw [Array.size_append]; omega
  obtain ⟨a, ha⟩ := write_find h hpos
  obtain ⟨rfl, hv⟩ := write_spec ha h
  obtain ⟨hwr, h1, h2, h3⟩ := hv hpos
  rw [Array.size_append] at h1 h2 h3
  rw [write_of_valid ha hA hwr (by omega) (by omega) (endsInWindow_mono h3 (by omega)),
    Option.bind_some]
  generalize hD1 : (List.range A.size).foldl (fun d i => d.set! (p.off.toNat + i) A[i]!) a.data
    = D1
  have hs1 : D1.size = a.data.size := by rw [← hD1, foldl_set_size]
  have hoff : (p.add (BitVec.ofNat 64 A.size)).off.toNat = p.off.toNat + A.size := by
    rw [Ptr.add_off, toNat_add_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hf : (m.set p.blk { a with data := D1 }).find? (p.add (BitVec.ofNat 64 A.size)).blk =
      some { a with data := D1 } := by
    rw [find?_set, Ptr.add_blk, ite_eq_left rfl]
  rw [write_of_valid hf hB hwr (by rw [hoff, hs1]; omega) (by rw [hoff]; omega)
    (by rw [hoff, Ptr.add_blk]; exact endsInWindow_mono h3 (by omega)), Ptr.add_blk, set_set]
  congr 3
  apply Array.ext_getElem?
  intro j
  rw [hoff, foldl_set_getElem? _ B D1 _ (Nat.le_refl _) (by omega) j,
    foldl_set_getElem? _ (A ++ B) a.data _ (Nat.le_refl _) (by rw [Array.size_append]; omega) j,
    ← hD1, foldl_set_getElem? _ A a.data _ (Nat.le_refl _) (by omega) j, Array.size_append]
  by_cases hj1 : p.off.toNat ≤ j ∧ j < p.off.toNat + A.size
  · rw [ite_eq_right (by omega), ite_eq_left hj1, ite_eq_left (by omega),
      Array.getElem?_append_left (by omega)]
  · by_cases hj2 : p.off.toNat + A.size ≤ j ∧ j < p.off.toNat + A.size + B.size
    · rw [ite_eq_left hj2, ite_eq_left (by omega), Array.getElem?_append_right (by omega)]
      congr 1
      omega
    · rw [ite_eq_right hj2, ite_eq_right hj1, ite_eq_right (by omega)]

/-- The size of a read. -/
private theorem read_size16 {m : Mem} {p : Ptr} {n : Nat} {bs : Array Byte} (hn : n ≠ 0)
    (h : m.read p n = some bs) : bs.size = n := by
  obtain ⟨al, -, h1, -, -, rfl⟩ := (read_eq_some hn).1 h
  rw [Array.size_extract]
  omega

/-- A valid non-empty write at `P` ending `e` bytes higher: `P` moved by `k < e` lies in its
window. -/
private theorem inWindow_of_write {m m1 : Mem} {P : Ptr} {bs : Array Byte}
    (hw : m.write P bs = some m1) {k : Nat} (hk : k < bs.size) :
    (P.add (BitVec.ofNat 64 k)).inWindow = true := by
  obtain ⟨a, ha⟩ := write_find hw (by omega)
  obtain ⟨-, -, h2, h3⟩ := (write_spec ha hw).2 (by omega)
  unfold Ptr.inWindow
  unfold Blk.endsInWindow at h3
  rw [Ptr.add_blk, Ptr.add_off, toNat_add_ofNat, Nat.mod_eq_of_lt (by omega)]
  cases hwin : P.blk.window? with
  | none => rfl
  | some w =>
    rw [hwin] at h3
    simp only [decide_eq_true_eq] at h3 ⊢
    omega

/-! ## Addresses -/

private theorem off_add (k : Int64) (n : Nat) :
    BitVec.ofInt 64 (k + Int64.ofNat n).toInt = BitVec.ofInt 64 k.toInt + BitVec.ofNat 64 n := by
  rw [← Int64.toInt_toBitVec, ← Int64.toInt_toBitVec, BitVec.ofInt_toInt, BitVec.ofInt_toInt,
    Int64.toBitVec_add]
  rfl

/-- `Sem.symAddr` at the offset moved by `n` is the address moved by `n`, if that stays inside
its window: on a symbol or pointer base by the offsets, on an integer base by `Ptr.ofAddr`'s
windows. -/
private theorem symAddr_add {ctx : Ctx} {v : Value} {a : Val} {P : Ptr} {n : Nat}
    (hP : symAddr ctx v a = some P) (hw : (P.add (BitVec.ofNat 64 n)).inWindow = true) :
    symAddr ctx { v with auxInt := v.auxInt + Int64.ofNat n } a =
      some (P.add (BitVec.ofNat 64 n)) := by
  unfold symAddr at hP ⊢
  dsimp only at hP ⊢
  rw [off_add]
  split at hP
  · split at hP
    · cases hP; rfl
    · cases hP; rfl
    · cases hP
  · unfold Arm64.addr at hP ⊢
    cases a with
    | ptr p => cases hP; simp only [Ptr.add, BitVec.add_assoc]
    | _ =>
      simp only [Option.map_eq_some_iff] at hP ⊢
      obtain ⟨x, hx, rfl⟩ := hP
      exact ⟨x, hx, by rw [← BitVec.add_assoc]; exact Ptr.ofAddr_add_of_inWindow hw⟩

/-! ## The ops -/

/-- `moveQLower`: a `Move [16]` lowered to `FMOVQstore` (three arguments) or a `Move [32]` to
`FSTPQ` (four). -/
theorem moveQLower_cases {tabs : Tables} {u w : Value} (h : moveQLower tabs u w = true) :
    u.op = .Move ∧ ((u.auxInt = 16 ∧ w.op = .ARM64FMOVQstore ∧ w.args.size = 3) ∨
      (u.auxInt = 32 ∧ w.op = .ARM64FSTPQ ∧ w.args.size = 4)) := by
  unfold moveQLower moveQOp at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hu, -⟩, -⟩, -⟩, h⟩ := h
  refine ⟨hu, ?_⟩
  split at h
  · rename_i h16
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h
    exact .inl ⟨by simpa using h16, h⟩
  · split at h
    · rename_i h32
      simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h
      exact .inr ⟨by simpa using h32, h⟩
    · simp at h

/-- `FMOVQstore` writes the 16 bytes of its value at `symAddr`. -/
private theorem evalOpL_fmovq {env : Env} {ctx : Ctx} {fr : Frame} {w : Value} {ty : Ty}
    (hw : w.op = .ARM64FMOVQstore) {a x : Val} {m : Mem} {p : Ptr}
    (hp : symAddr ctx w a = some p) :
    ∃ what, evalOpL false env ctx fr w [a, x, .mem m] ty =
      writeRes what (Arm64.storeN 16 p x m) := by
  have h0 : nilFaults false ctx w [a, x, .mem m] = none := rfl
  refine ⟨s!"v{w.id}: {w.op.name}", ?_⟩
  unfold evalOpL
  rw [hw, ite_eq_right (by decide)]
  dsimp only
  unfold arm64Op
  rw [h0]
  dsimp only
  rw [hw]
  dsimp only
  rw [hp]

/-- `FSTPQ` writes its two values at the pair's addresses (`pairAddr`). -/
private theorem evalOpL_fstpq {env : Env} {ctx : Ctx} {fr : Frame} {w : Value} {ty : Ty}
    (hw : w.op = .ARM64FSTPQ) {a x y : Val} {m : Mem} {p q : Ptr}
    (hpq : pairAddr ctx w 16 a = some (p, q)) :
    ∃ what, evalOpL false env ctx fr w [a, x, y, .mem m] ty =
      writeRes what (Arm64.storePair 16 p q x y m) := by
  have h0 : nilFaults false ctx w [a, x, y, .mem m] = none := rfl
  refine ⟨s!"v{w.id}: {w.op.name}", ?_⟩
  unfold evalOpL
  rw [hw, ite_eq_right (by decide)]
  dsimp only
  unfold arm64Op
  rw [h0]
  dsimp only
  rw [hw]
  dsimp only
  rw [hpq]

/-- A generic `Move` that does not get stuck read its `n` bytes and wrote them. -/
private theorem memRoot_move_inv {ctx : Ctx} {u : Value} (hu : u.op = .Move) (argv : List Val) :
    (∃ msg, memRoot ctx u argv = .stuck msg) ∨
      ∃ a b mm P S bs m1, argv = [a, b, .mem mm] ∧ a.asPtrWord = some P ∧
        b.asPtrWord = some S ∧ mm.read S u.auxInt.toInt.toNat = some bs ∧
        mm.write P bs = some m1 ∧ memRoot ctx u argv = .ok (.mem m1) := by
  unfold memRoot
  rw [hu]
  split
  all_goals first
    | (rename_i h; exact absurd h (by decide))
    | skip
  case h_3 =>
    rename_i a b mm _
    dsimp only
    cases hP : a.asPtrWord with
    | none => exact .inl ⟨_, rfl⟩
    | some P =>
      cases hS : b.asPtrWord with
      | none => exact .inl ⟨_, rfl⟩
      | some S =>
        dsimp only
        cases hr : mm.read S u.auxInt.toInt.toNat with
        | none => exact .inl ⟨_, rfl⟩
        | some bs =>
          dsimp only
          cases hw : mm.write P bs with
          | none => exact .inl ⟨_, rfl⟩
          | some m1 => exact .inr ⟨a, b, mm, P, S, bs, m1, rfl, hP, hS, hr, hw, rfl⟩
  all_goals
    left
    dsimp only
    split <;> exact ⟨_, rfl⟩

/-- A value refining a 16-byte blob stores bytes refining the blob's. -/
private theorem storeBytes_blob {L : List Byte} (hL : L.length = 16) {x : Val}
    (h : Sem.Refines (.blob L) x) : BytesRefine L (Arm64.storeBytes 16 x).toList := by
  cases h with
  | blob hb =>
    have hl := hb.length_eq
    unfold Arm64.storeBytes
    simp only [← hl, hL, beq_self_eq_true, ite_true, List.toList_toArray]
    exact hb

/-- The half `i` of a `Move`'s read. -/
private theorem qPart_read {s : Val} {S : Ptr} (hS : s.asPtrWord = some S) {mm : Mem} {n : Nat}
    {bs : Array Byte} (hr : mm.read S n = some bs) {i : Nat} (hi : 16 * i + 16 ≤ n) :
    qPart i s (.mem mm) = .blob (bs.extract (16 * i) (16 * i + 16)).toList := by
  unfold qPart
  rw [hS]
  dsimp only
  unfold Arm64.load16
  rw [read_extract hr hi]

/-- The bytes a value refining half `i` of a `Move`'s read stores refine the half. -/
private theorem half_ref {s : Val} {S : Ptr} (hS : s.asPtrWord = some S) {mm : Mem} {n : Nat}
    {bs : Array Byte} (hr : mm.read S n = some bs) (hn : bs.size = n) {i : Nat}
    (hi : 16 * i + 16 ≤ n) {x : Val} (hx : Sem.Refines (qPart i s (.mem mm)) x) :
    BytesRefineA (bs.extract (16 * i) (16 * i + 16)) (Arm64.storeBytes 16 x) := by
  rw [qPart_read hS hr hi] at hx
  exact storeBytes_blob (by simp only [Array.length_toList, Array.size_extract]; omega) hx

/-! ## The lowering -/

/-- **`Move [16]`/`Move [32]` lowered to `FMOVQstore`/`FSTPQ`** (`ARM64.rules:418`, `426`; an
offset folded, `779`, `782`, a symbol or frame variable, `909`, `913`): on a destination whose
store address is the `Move`'s (`AddrRef`), values refining the 16-byte halves the `Move` copies
(`qPart`) and a refined memory, the 128-bit store refines the generic `Move` (both shaped). -/
theorem moveQ_lower_eval {env : Env} {ctx ctx' : Ctx} {fr fr' : Frame} {u w : Value}
    (hq : moveQLower ctx'.tabs u w = true) {ty : Ty} (lS : Bool) {d s m d' m' : Val}
    {xs : List Val} (hd : AddrRef ctx'.tabs ctx'.act w.aux w.auxInt d d')
    (hm : Sem.Refines m m') (hlen : xs.length + 2 = w.args.size)
    (hx : ∀ i x, xs[i]? = some x → Sem.Refines (qPart i s m) x) :
    Res.Refines ((evalOp env ctx fr u [d, s, m] ty).bind fun r => .ok (rty lS ty r))
      ((evalOpL false env ctx' fr' w (d' :: xs ++ [m']) ty).bind fun r => .ok (rty true ty r)) := by
  obtain ⟨hu, hc⟩ := moveQLower_cases hq
  have hS : evalOp env ctx fr u [d, s, m] ty = memRoot ctx u [d, s, m] := by
    unfold evalOp; rw [hu]
  rw [hS]
  refine Res.Rel.bind ?_ fun x y hxy => .ok (rty_le (fun _ => rfl) ty hxy)
  rcases memRoot_move_inv (ctx := ctx) hu [d, s, m] with ⟨msg, hst⟩ |
    ⟨a, b, mm, P, S, bs, m1, harg, hP, hSp, hr, hw, hres⟩
  · rw [hst]; exact .stuck _ _
  simp only [List.cons.injEq, and_true] at harg
  obtain ⟨rfl, rfl, rfl⟩ := harg
  rw [hres]
  cases hm with | @mem _ mm' hmm =>
  have hdP : symAddr ctx' w d' = some P := (show symAddr ctx' w d' =
    addrAt ctx'.tabs ctx'.act w.aux w.auxInt d' by unfold symAddr addrAt; rfl).trans (hd P hP)
  rcases hc with ⟨hn, hwo, hsz⟩ | ⟨hn, hwo, hsz⟩
  · -- `FMOVQstore`
    have hn' : u.auxInt.toInt.toNat = 16 := by rw [hn]; decide
    rw [hn'] at hr
    have hbs := read_size16 (by decide) hr
    rcases xs with _ | ⟨x0, _ | ⟨x1, l⟩⟩
    · simp at hlen; omega
    · have h0 := half_ref hSp hr hbs (i := 0) (by decide) (hx 0 x0 rfl)
      have he : bs.extract (16 * 0) (16 * 0 + 16) = bs := by
        simp only [Nat.mul_zero, Nat.zero_add]
        rw [Array.extract_eq_self_iff]
        omega
      rw [he] at h0
      obtain ⟨m2, hw2, hm2⟩ := hmm.write h0 hw
      obtain ⟨what, he2⟩ := evalOpL_fmovq (env := env) (fr := fr') (ty := ty) (x := x0) (m := mm')
        hwo hdP
      simp only [List.cons_append, List.nil_append]
      rw [he2]
      simp only [writeRes, Arm64.storeN, hw2]
      exact .ok (.mem hm2)
    · simp at hlen; omega
  · -- `FSTPQ`
    have hn' : u.auxInt.toInt.toNat = 32 := by rw [hn]; decide
    rw [hn'] at hr
    have hbs := read_size16 (by decide) hr
    rcases xs with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, l⟩⟩⟩
    · simp at hlen; omega
    · simp at hlen; omega
    · have h0 := half_ref hSp hr hbs (i := 0) (by decide) (hx 0 x0 rfl)
      have h1 := half_ref hSp hr hbs (i := 1) (by decide) (hx 1 x1 rfl)
      have he : bs = bs.extract (16 * 0) (16 * 0 + 16) ++ bs.extract (16 * 1) (16 * 1 + 16) := by
        rw [Array.extract_append_extract]
        simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one]
        rw [eq_comm, Array.extract_eq_self_iff]
        omega
      have hb : BytesRefineA bs (Arm64.storeBytes 16 x0 ++ Arm64.storeBytes 16 x1) := by
        rw [he]
        simp only [BytesRefineA, Array.toList_append]
        exact BytesRefine.append h0 h1
      have hs0 : (Arm64.storeBytes 16 x0).size = 16 := by
        rw [← h0.size_eq, Array.size_extract]; omega
      have hs1 : (Arm64.storeBytes 16 x1).size = 16 := by
        rw [← h1.size_eq, Array.size_extract]; omega
      obtain ⟨m2, hw2, hm2⟩ := hmm.write hb hw
      have hpair := write_append (by omega) (by omega) hw2
      rw [hs0] at hpair
      have hQ := symAddr_add (n := 16) hdP (inWindow_of_write hw (k := 16) (by omega))
      have hpq : pairAddr ctx' w 16 d' = some (P, P.add (BitVec.ofNat 64 16)) := by
        unfold pairAddr
        rw [hdP]
        simp only [Option.bind_some, hQ, Option.map_some]
      obtain ⟨what, he2⟩ := evalOpL_fstpq (env := env) (fr := fr') (ty := ty) (x := x0) (y := x1)
        (m := mm') hwo hpq
      simp only [List.cons_append, List.nil_append]
      rw [he2]
      simp only [writeRes, Arm64.storePair, hpair]
      exact .ok (.mem hm2)
    · simp at hlen; omega

end GoFV.Proof.Low.Sim

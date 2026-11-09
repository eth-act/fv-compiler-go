import GoFV.Proof.Low.DenL
import GoFV.Proof.Pass.MemCombineBytes
import GoFV.Proof.PtrAddr

variable [GoFV.SSA.Sem.Addrs]

/-!
# The 16-byte halves a `Move` copies, read by 128-bit loads (issue #385)

`ARM64.rules:418` lowers `(Move [16] dst src mem)` to `(FMOVQstore dst (FMOVQload src mem) mem)`
and `426` `(Move [32] dst src mem)` to `(FSTPQ dst (Select0 (FLDPQ src mem)) (Select1 (FLDPQ src
mem)) mem)`. The validator replays the event with fresh load terms of the `Move`'s source and
memory (`GoFV.Opt.LowerCheck.moveDef`); their values refine the halves the `Move` copies
(`qPart`): `qPart_ld16` for `FMOVQload`, `qPart_ldPair` for the components of `FLDPQ`, whose second
address (the source moved by 16) is the half's wherever that half is read (a read stays in its
block's window, `Ptr.ofAddr_add_of_inWindow`).
-/

namespace GoFV.Proof.Low

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof GoFV.Proof.MemCombine

/-- `qPart` is monotone. -/
theorem qPart_mono (i : Nat) {s s' m m' : Val} (hs : Sem.Refines s s') (hm : Sem.Refines m m') :
    Sem.Refines (qPart i s m) (qPart i s' m') := by
  unfold qPart
  cases hp : s.asPtrWord with
  | none => exact .poison _
  | some p =>
    rw [asPtrWord_of_refines hs hp, hp]
    cases hm with
    | mem h => exact Mono.load16_mono h _
    | _ => first | exact .poison _ | exact Sem.Refines.refl _

/-- A 16-byte read gives 16 bytes. -/
theorem read16_size {m : Mem} {p : Ptr} {bs : Array Byte} (h : m.read p 16 = some bs) :
    bs.size = 16 := by
  obtain ⟨al, -, h1, -, -, rfl⟩ := (read_eq_some (by decide)).1 h
  rw [Array.size_extract]
  omega

/-- A 16-byte load refines its refinement shaped as a `Vec128` (`blob 16`). -/
theorem load16_retypeL {m m' : Mem} (h : Mem.Refines m m') (p : Ptr) :
    Sem.Refines (Arm64.load16 m p) ((Arm64.load16 m' p).retypeL (.blob 16)) := by
  unfold Arm64.load16
  cases hr : m.read p 16 with
  | none => exact .poison _
  | some bs =>
    obtain ⟨bs', hr', hb⟩ := h.read hr
    have hs : bs'.size = 16 := by rw [← hb.size_eq]; exact read16_size hr
    rw [hr']
    simp only [Val.retypeL, Val.widen, Val.retype, Array.length_toList, hs, beq_self_eq_true,
      ite_true]
    exact .blob hb

/-- `Select0`/`Select1` of a pair at the shape of two `Vec128`s, shaped as a `Vec128`. -/
theorem select_pair_retypeL (tabs : Tables) {o : Op} {i : Nat}
    (ho : (o = .Select0 ∧ i = 0) ∨ (o = .Select1 ∧ i = 1)) (x y : Val) :
    (opValL tabs o (.blob 16) 0 none
        [(Val.tuple [x, y]).retypeL (.tuple [.blob 16, .blob 16])]).retypeL (.blob 16) =
      ((if i = 0 then x else y).retype (.blob 16)).retypeL (.blob 16) := by
  rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- Shaping as a `Vec128` twice is shaping once. -/
theorem retype_blob_retypeL (v : Val) :
    (v.retype (.blob 16)).retypeL (.blob 16) = v.retypeL (.blob 16) := by
  cases v with
  | blob bs =>
    by_cases hb : bs.length = 16
    · have : (Val.blob bs).retype (.blob 16) = .blob bs := by
        show (if bs.length == 16 then Val.blob bs else Val.poison) = _
        rw [if_pos (by simpa using hb)]
      rw [this]
    · have : (Val.blob bs).retype (.blob 16) = .poison := by
        show (if bs.length == 16 then Val.blob bs else Val.poison) = _
        rw [if_neg (by simpa using hb)]
      rw [this]
      show Val.poison = (if bs.length == 16 then Val.blob bs else Val.poison)
      rw [if_neg (by simpa using hb)]
  | _ => rfl

/-- **The half `0` a `Move` copies is refined by an `FMOVQload` of its source and memory** at
offset 0 without aux, shaped as a `Vec128`. -/
theorem qPart_ld16 (tabs : Tables) {s s' m m' : Val} (hs : Sem.Refines s s')
    (hm : Sem.Refines m m') :
    Sem.Refines (qPart 0 s m)
      ((opValL tabs .ARM64FMOVQload (.blob 16) 0 none [s', m']).retypeL (.blob 16)) := by
  rw [opValL_ldQ (show ldQ? .ARM64FMOVQload = some 16 from rfl)]
  unfold qPart
  cases hp : s.asPtrWord with
  | none => exact .poison _
  | some p =>
    rw [asPtrWord_of_refines hs hp]
    cases hm with
    | mem h =>
      have ha : symPtr tabs 0 none s = some p := by
        unfold symPtr
        rw [show BitVec.ofInt 64 (0 : Int64).toInt = 0 by decide]
        exact addr_of_asPtrWord hp
      simp only [ldQVal, show ((16 : Nat) = 32) = False by decide, ite_false, ha, Option.elim]
      rw [show p.add (BitVec.ofNat 64 (16 * 0)) = p by simp [Ptr.add]]
      exact load16_retypeL h p
    | _ => first | exact .poison _ | exact Sem.Refines.refl _

/-- A 16-byte read at `P` moved by 16 keeps that address in its window. -/
theorem inWindow_of_read16 {m : Mem} {P : Ptr} {bs : Array Byte}
    (h : m.read (P.add (BitVec.ofNat 64 16)) 16 = some bs) :
    (P.add (BitVec.ofNat 64 16)).inWindow = true := by
  obtain ⟨-, -, -, -, h3, -⟩ := (read_eq_some (by decide)).1 h
  unfold Ptr.inWindow
  unfold Blk.endsInWindow at h3
  cases hw : (P.add (BitVec.ofNat 64 16)).blk.window? with
  | none => rfl
  | some w =>
    rw [hw] at h3
    simp only [decide_eq_true_eq] at h3 ⊢
    omega

/-- The second address of an `FLDPQ` at offset 0 without aux of `s`: `s`'s pointer word moved by
16, where the half `1` of `s` reads something. -/
theorem symPtr_pair2 (tabs : Tables) {s : Val} {P : Ptr} (hP : s.asPtrWord = some P) :
    ∃ Q, symPtr tabs ((0 : Int64) + Int64.ofNat 16) none s = some Q ∧
      ((P.add (BitVec.ofNat 64 16)).inWindow = true → Q = P.add (BitVec.ofNat 64 16)) := by
  unfold symPtr
  rw [show BitVec.ofInt 64 ((0 : Int64) + Int64.ofNat 16).toInt = BitVec.ofNat 64 16 by decide]
  cases s with
  | ptr p =>
    simp only [Val.asPtrWord, Option.some.injEq] at hP
    subst hP
    exact ⟨_, rfl, fun _ => rfl⟩
  | int w x =>
    cases w <;> simp only [Val.asPtrWord, reduceCtorEq] at hP
    simp only [Option.some.injEq] at hP
    subst hP
    refine ⟨_, rfl, fun hw => ?_⟩
    exact Ptr.ofAddr_add_of_inWindow hw
  | _ => simp [Val.asPtrWord] at hP

/-- **The halves a `Move [32]` copies are refined by `Select0` and `Select1` of an `FLDPQ` of its
source and memory** at offset 0 without aux, the pair shaped as two `Vec128`s and each component
as one. -/
theorem qPart_ldPair (tabs : Tables) {o : Op} {i : Nat}
    (ho : (o = .Select0 ∧ i = 0) ∨ (o = .Select1 ∧ i = 1)) {s s' m m' : Val}
    (hs : Sem.Refines s s') (hm : Sem.Refines m m') :
    Sem.Refines (qPart i s m)
      ((opValL tabs o (.blob 16) 0 none
        [(opValL tabs .ARM64FLDPQ (.tuple [.blob 16, .blob 16]) 0 none [s', m']).retypeL
          (.tuple [.blob 16, .blob 16])]).retypeL (.blob 16)) := by
  rw [opValL_ldQ (show ldQ? .ARM64FLDPQ = some 32 from rfl)]
  unfold qPart
  cases hp : s.asPtrWord with
  | none => exact .poison _
  | some p =>
    rw [asPtrWord_of_refines hs hp]
    cases hm with
    | @mem mm mm' h =>
      have ha : symPtr tabs 0 none s = some p := by
        unfold symPtr
        rw [show BitVec.ofInt 64 (0 : Int64).toInt = 0 by decide]
        exact addr_of_asPtrWord hp
      obtain ⟨Q, hQ, hQw⟩ := symPtr_pair2 tabs hp
      simp only [ldQVal, ite_true, ha, hQ, Arm64.loadPair, Arm64.tupleTy, List.getD_cons_zero,
        List.getD_cons_succ, Arm64.loadElt]
      rw [select_pair_retypeL tabs ho]
      rw [retype_blob_retypeL]
      rcases ho with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · simp only [ite_true]
        rw [show p.add (BitVec.ofNat 64 (16 * 0)) = p by simp [Ptr.add]]
        exact load16_retypeL h p
      · simp only [show (1 : Nat) ≠ 0 by decide, ite_false]
        unfold Arm64.load16
        cases hr : mm.read (p.add (BitVec.ofNat 64 (16 * 1))) 16 with
        | none => exact .poison _
        | some bs =>
          rw [hQw (inWindow_of_read16 hr)]
          have := load16_retypeL h (p.add (BitVec.ofNat 64 (16 * 1)))
          unfold Arm64.load16 at this
          rw [hr] at this
          exact this
    | _ => first | exact .poison _ | exact Sem.Refines.refl _

/-! ## Parts at an offset (two-store forms) -/

theorem ofInt_ofNat_lt {n : Nat} (hn : n < 2 ^ 63) :
    BitVec.ofInt 64 (Int64.ofNat n).toInt = BitVec.ofNat 64 n := by
  rw [Int64.toInt_ofNat_of_lt hn]
  apply BitVec.eq_of_toNat_eq
  simp

/-- A 16-byte read at `P` moved by `k` keeps that address in its window. -/
theorem inWindow_of_read16_at {m : Mem} {P : Ptr} {k : BitVec 64} {bs : Array Byte}
    (h : m.read (P.add k) 16 = some bs) : (P.add k).inWindow = true := by
  obtain ⟨-, -, -, -, h3, -⟩ := (read_eq_some (by decide)).1 h
  unfold Ptr.inWindow
  unfold Blk.endsInWindow at h3
  cases hw : (P.add k).blk.window? with
  | none => rfl
  | some w =>
    rw [hw] at h3
    simp only [decide_eq_true_eq] at h3 ⊢
    omega

/-- The address of a load at offset `n` without aux of `s`: `s`'s pointer word moved by `n`, where
that stays in its window. -/
theorem symPtr_at (tabs : Tables) {s : Val} {P : Ptr} (hP : s.asPtrWord = some P) {n : Nat}
    (hn : n < 2 ^ 63) :
    ∃ Q, symPtr tabs (Int64.ofNat n) none s = some Q ∧
      ((P.add (BitVec.ofNat 64 n)).inWindow = true → Q = P.add (BitVec.ofNat 64 n)) := by
  unfold symPtr
  rw [ofInt_ofNat_lt hn]
  cases s with
  | ptr p =>
    simp only [Val.asPtrWord, Option.some.injEq] at hP
    subst hP
    exact ⟨_, rfl, fun _ => rfl⟩
  | int w x =>
    cases w <;> simp only [Val.asPtrWord, reduceCtorEq] at hP
    simp only [Option.some.injEq] at hP
    subst hP
    exact ⟨_, rfl, fun hw => Ptr.ofAddr_add_of_inWindow hw⟩
  | _ => simp [Val.asPtrWord] at hP

/-- A 16-byte load at `Q`, where the read at `P` succeeding implies `Q = P`, refines that at `P`. -/
private theorem load16_at {mm mm' : Mem} (h : Mem.Refines mm mm') {P Q : Ptr}
    (hQ : P.inWindow = true → Q = P) :
    Sem.Refines (Arm64.load16 mm P) ((Arm64.load16 mm' Q).retypeL (.blob 16)) := by
  unfold Arm64.load16
  cases hr : mm.read P 16 with
  | none => exact .poison _
  | some bs =>
    have hw : P.inWindow = true := by
      have := inWindow_of_read16_at (P := P) (k := 0) (by simpa [Ptr.add] using hr)
      simpa [Ptr.add] using this
    rw [hQ hw]
    have := load16_retypeL h P
    unfold Arm64.load16 at this
    rw [hr] at this
    exact this

/-- **The 16 bytes `k` bytes into a `Move`'s copy are refined by an `FMOVQload [k]` of its source
and memory** without aux, shaped as a `Vec128`. -/
theorem qAt_ld16 (tabs : Tables) {k : Nat} (hk : k < 2 ^ 63) {s s' m m' : Val}
    (hs : Sem.Refines s s') (hm : Sem.Refines m m') :
    Sem.Refines (qAt k s m)
      ((opValL tabs .ARM64FMOVQload (.blob 16) (Int64.ofNat k) none [s', m']).retypeL
        (.blob 16)) := by
  rw [opValL_ldQ (show ldQ? .ARM64FMOVQload = some 16 from rfl)]
  unfold qAt
  cases hp : s.asPtrWord with
  | none => exact .poison _
  | some p =>
    obtain rfl := asPtrWord_of_refines hs hp
    cases hm with
    | mem h =>
      obtain ⟨Q, hQ, hQw⟩ := symPtr_at tabs hp hk
      simp only [ldQVal, show ((16 : Nat) = 32) = False by decide, ite_false, hQ, Option.elim]
      exact load16_at h hQw
    | _ => first | exact .poison _ | exact Sem.Refines.refl _

/-- **The 32 bytes `k` bytes into a `Move`'s copy are refined by `Select0` and `Select1` of an
`FLDPQ [k]` of its source and memory** without aux, the pair shaped as two `Vec128`s and each
component as one. -/
theorem qAt_ldPair (tabs : Tables) {o : Op} {i : Nat}
    (ho : (o = .Select0 ∧ i = 0) ∨ (o = .Select1 ∧ i = 1)) {k : Nat} (hk : k + 16 < 2 ^ 63)
    {s s' m m' : Val} (hs : Sem.Refines s s') (hm : Sem.Refines m m') :
    Sem.Refines (qAt (k + 16 * i) s m)
      ((opValL tabs o (.blob 16) 0 none
        [(opValL tabs .ARM64FLDPQ (.tuple [.blob 16, .blob 16]) (Int64.ofNat k) none
          [s', m']).retypeL (.tuple [.blob 16, .blob 16])]).retypeL (.blob 16)) := by
  rw [opValL_ldQ (show ldQ? .ARM64FLDPQ = some 32 from rfl)]
  unfold qAt
  cases hp : s.asPtrWord with
  | none => exact .poison _
  | some p =>
    obtain rfl := asPtrWord_of_refines hs hp
    cases hm with
    | @mem mm mm' h =>
      obtain ⟨Q0, hQ0, hQ0w⟩ := symPtr_at tabs hp (n := k) (by omega)
      obtain ⟨Q1, hQ1, hQ1w⟩ := symPtr_at tabs hp (n := k + 16) hk
      have e16 : Int64.ofNat k + Int64.ofNat 16 = Int64.ofNat (k + 16) := by
        rw [Int64.ofNat_add]
      simp only [ldQVal, ite_true, hQ0, e16, hQ1, Arm64.loadPair, Arm64.tupleTy,
        List.getD_cons_zero, List.getD_cons_succ, Arm64.loadElt]
      rw [select_pair_retypeL tabs ho, retype_blob_retypeL]
      rcases ho with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · simp only [ite_true, Nat.mul_zero, Nat.add_zero]
        exact load16_at h hQ0w
      · simp only [show (1 : Nat) ≠ 0 by decide, ite_false, Nat.mul_one]
        exact load16_at h hQ1w
    | _ => first | exact .poison _ | exact Sem.Refines.refl _

end GoFV.Proof.Low

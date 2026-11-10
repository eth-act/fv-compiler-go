import GoFV.SSA.Sem.LocMatch
import GoFV.SSA.Sem.FrameSafe
import GoFV.Proof.PtrAddr
import GoFV.Gen.Check

variable [GoFV.SSA.Sem.Addrs]

/-!
# Values and registers under `LocMatch` in slice G1 (`docs/plans/proofs3.md` §3)

`AddrAgree ι`: the injection puts every block that has an address (`Blk.base?`, under the address
assignment `Addrs`) other than a frame temporary at that address. Every block an integer converts
back to is one (`Ptr.ofAddr_ne_temp`), so a convertible pointer's injected address is its address,
the second disjunct of `ValRel` at `.int .w64` collapses to the first, `Ptr.word` relates like the
pointer, and Phase 2's register arithmetic on pointer words (`Arm64.reg` reads a convertible
pointer as its address) is the machine's. A frame temporary may sit anywhere (slice G6 puts the
current activation's at their frame operands): no integer is its address. An assignment that
puts the running activation's frame at the machine's `SP + frameOff` (`docs/plans/proofs3.md`
§8) makes the injection agree on those blocks too.

`Fits c v`: a register content of width class `c` (`GoFV.Gen.Check.cls`). Reading it at a shape
of class `c` (`Val.retypeL`) keeps `ValRel` (`valRel_retypeL`); a narrower content read at a wider
shape would be zero-extended by `retypeL` while the machine's upper bits are arbitrary, which the
validator's one-class-per-register rule excludes.

`FitsW c v` (the class tables of G3 on): a register content that can be read at class `c`
(`GoFV.Gen.Check.kNarrow`): `Fits c v`, an integer or pointer content of at least `c ≥ 8` bits
(read at `c`, its low bits), or a boolean (0 or 1 in the whole register) read at an integer class.
Reading it at a shape of class `c` keeps `ValRel` (`valRel_retypeLW`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check

/-- The block is no frame temporary. -/
def NotTemp (b : Blk) : Prop := ∀ a n, b ≠ .temp a n

/-- Every block with an address other than a frame temporary sits at that address. -/
def AddrAgree (ι : Blk → Option (BitVec 64)) : Prop :=
  ∀ b n a, b.base? = some n → ι b = some a → NotTemp b → a = BitVec.ofNat 64 n

theorem notTemp_ofAddr (x : BitVec 64) : NotTemp (Ptr.ofAddr x).blk :=
  fun a n => Ptr.ofAddr_ne_temp x a n

theorem notTemp_of_convertible {p : Ptr} (h : p.convertible = true) : NotTemp p.blk := by
  intro a n hb
  obtain ⟨b, o⟩ := p
  simp only at hb; subst hb
  simp at h

/-- A register content of width class `c`. -/
def Fits (c : Nat) : Val → Prop
  | .poison => True
  | .int w _ => w.bits = c
  | .ptr _ => c = 64
  | .bool _ => c = 1
  | _ => False

variable {ι : Blk → Option (BitVec 64)}

/-- The injected address of a pointer with a Phase 1 address, not into a frame temporary, is that
address. -/
theorem ptrRel_addr (hA : AddrAgree ι) {p : Ptr} {r a : BitVec 64} (h : PtrRel ι p r)
    (ha : p.addr? = some a) (ht : NotTemp p.blk) : r = a := by
  obtain ⟨base, hb, rfl⟩ := h
  unfold Ptr.addr? at ha
  cases hn : p.blk.base? with
  | none => rw [hn] at ha; cases ha
  | some n =>
    rw [hn] at ha
    cases ha
    rw [hA _ _ _ hn hb ht]

/-- `Ptr.word` relates like the pointer. -/
theorem valRel_word (hA : AddrAgree ι) {p : Ptr} {r : BitVec 64} (h : PtrRel ι p r) :
    ValRel ι p.word r := by
  unfold Ptr.word
  split
  · rename_i a hc ha
    exact Or.inl (ptrRel_addr hA h ha (notTemp_of_convertible hc))
  · split
    · exact h
    · trivial

/-- Under `AddrAgree`, a 64-bit integer relates to exactly its own word. -/
theorem valRel_i64 (hA : AddrAgree ι) {x r : BitVec 64} (h : ValRel ι (.int .w64 x) r) :
    r = x := by
  rcases h with h | ⟨_, h⟩
  · exact h
  · exact ptrRel_addr hA h (Ptr.addr?_ofAddr x) (notTemp_ofAddr x)

/-- A register content read at a shape of its class keeps its relation. -/
theorem valRel_retypeL (hA : AddrAgree ι) {c : Nat} {t : Ty} {v : Val} {r : BitVec 64}
    (hc : cls t = some c) (hf : Fits c v) (hv : ValRel ι v r) : ValRel ι (v.retypeL t) r := by
  cases t with
  | int w' =>
    simp only [cls, Option.some.injEq] at hc
    subst hc
    cases v with
    | poison => exact trivial
    | int w x =>
      cases w <;> cases w' <;> (try simp [Fits, Width.bits] at hf) <;>
        simpa [Val.retypeL, Val.widen, Val.retype] using hv
    | ptr p =>
      cases w' <;> (try simp [Fits, Width.bits] at hf)
      exact (valRel_word hA hv : ValRel ι p.word r)
    | bool b => cases w' <;> simp [Fits, Width.bits] at hf
    | _ => simp [Fits] at hf
  | ptr e =>
    simp only [cls, Option.some.injEq] at hc
    subst hc
    cases v with
    | poison => exact trivial
    | int w x =>
      cases w <;> (try simp [Fits, Width.bits] at hf)
      exact hv
    | ptr p => exact (valRel_word hA hv : ValRel ι p.word r)
    | bool b => simp [Fits] at hf
    | _ => simp [Fits] at hf
  | bool =>
    simp only [cls, Option.some.injEq] at hc
    subst hc
    cases v with
    | poison => exact trivial
    | int w x => cases w <;> simp [Fits, Width.bits] at hf
    | bool b => exact hv
    | ptr p => simp [Fits] at hf
    | _ => simp [Fits] at hf
  | _ => simp [cls] at hc

/-- Whatever `retypeL` gives at a shape of class `c` fits class `c`. -/
theorem fits_retypeL {c : Nat} {t : Ty} (hc : cls t = some c) (v : Val) : Fits c (v.retypeL t) := by
  cases t with
  | int w' =>
    simp only [cls, Option.some.injEq] at hc
    subst hc
    cases v with
    | int w x =>
      simp only [Val.retypeL, Val.widen]
      split <;> simp only [Val.retype] <;> split <;> trivial
    | bool b => simp only [Val.retypeL, Val.widen, Val.retype, Nat.le_refl, ↓reduceIte]; rfl
    | ptr p =>
      simp only [Val.retypeL, Val.widen]
      cases w' <;> simp only [Val.retype] <;> try trivial
      unfold Ptr.word; split <;> (try split) <;> first | rfl | trivial
    | _ => simp only [Val.retypeL, Val.widen, Val.retype] <;> trivial
  | ptr e =>
    simp only [cls, Option.some.injEq] at hc
    subst hc
    cases v with
    | int w x =>
      simp only [Val.retypeL, Val.widen]
      cases w <;> simp only [Val.retype, ↓reduceIte] <;> first | rfl | trivial | decide
    | bool b => simp only [Val.retypeL, Val.widen, Val.retype]; rfl
    | ptr p =>
      simp only [Val.retypeL, Val.widen, Val.retype]; unfold Ptr.word
      split <;> (try split) <;> first | rfl | trivial
    | _ => simp only [Val.retypeL, Val.widen, Val.retype] <;> trivial
  | bool =>
    simp only [cls, Option.some.injEq] at hc
    subst hc
    cases v <;> simp only [Val.retypeL, Val.widen, Val.retype] <;> trivial
  | _ => simp [cls] at hc

/-- A register content that can be read at class `c` (`kNarrow` of its class). -/
def FitsW (c : Nat) : Val → Prop
  | .poison => True
  | .int w _ => kNarrow c w.bits = true
  | .ptr _ => kNarrow c 64 = true
  | .bool _ => kNarrow c 1 = true
  | _ => False

theorem kNarrow_refl (c : Nat) : kNarrow c c = true := by simp [kNarrow]

theorem kNarrow_trans {a b c : Nat} (h1 : kNarrow a b = true) (h2 : kNarrow b c = true) :
    kNarrow a c = true := by
  simp only [kNarrow, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at *
  omega

theorem fitsW_of_fits {c : Nat} {v : Val} (h : Fits c v) : FitsW c v := by
  cases v with
  | poison => trivial
  | int w x =>
    have h : w.bits = c := h
    subst h; exact kNarrow_refl _
  | ptr p =>
    have h : c = 64 := h
    subst h; exact kNarrow_refl _
  | bool b =>
    have h : c = 1 := h
    subst h; exact kNarrow_refl _
  | _ => simp [Fits] at h

/-- A content that can be read at class `c'` can be read at any class `c'` allows. -/
theorem FitsW.narrow {c c' : Nat} {v : Val} (hf : FitsW c' v) (h : kNarrow c c' = true) :
    FitsW c v := by
  cases v with
  | poison => trivial
  | int w x => exact kNarrow_trans h hf
  | ptr p => exact kNarrow_trans h hf
  | bool b => exact kNarrow_trans h hf
  | _ => exact hf

/-- An integer read at a shape of at most its width: its low bits. -/
theorem retypeL_int_low {w w' : Width} (x : BitVec w.bits) (hle : w'.bits ≤ w.bits) :
    (Val.int w x).retypeL (.int w') = .int w' (x.setWidth w'.bits) := by
  cases w <;> cases w' <;> simp [Width.bits] at hle <;>
    simp [Val.retypeL, Val.widen, Val.retype, Width.bits]

/-- An integer register content read at a class it allows: its low bits. -/
private theorem valRel_int_low (hA : AddrAgree ι) {w w' : Width} {x : BitVec w.bits}
    {r : BitVec 64} (hle : w'.bits ≤ w.bits) (hv : ValRel ι (.int w x) r) :
    ValRel ι (.int w' (x.setWidth w'.bits)) r := by
  cases w
  case w64 =>
    have hr := valRel_i64 hA hv
    subst hr
    cases w'
    case w64 => exact Or.inl (BitVec.setWidth_eq _).symm
    all_goals exact rfl
  all_goals
    have hv' : r.setWidth _ = x := hv
    cases w'
    case w64 => exact absurd hle (by decide)
    all_goals
      show r.setWidth _ = x.setWidth _
      rw [← hv', BitVec.setWidth_setWidth_of_le _ hle]

/-- A register content read at a shape of a class it allows keeps its relation. -/
theorem valRel_retypeLW (hA : AddrAgree ι) {c : Nat} {t : Ty} {v : Val} {r : BitVec 64}
    (hc : cls t = some c) (hf : FitsW c v) (hv : ValRel ι v r) : ValRel ι (v.retypeL t) r := by
  cases t with
  | int w' =>
    simp only [cls, Option.some.injEq] at hc
    subst hc
    cases v with
    | poison => exact trivial
    | int w x =>
      have hle : w'.bits ≤ w.bits := by
        have hf : kNarrow w'.bits w.bits = true := hf
        revert hf; cases w <;> cases w' <;> decide
      rw [retypeL_int_low x hle]
      exact valRel_int_low hA hle hv
    | ptr p =>
      cases w' with
      | w64 => exact (valRel_word hA hv : ValRel ι p.word r)
      | _ => exact trivial
    | bool b =>
      have hv : r = if b then 1 else 0 := hv
      subst hv
      simp only [Val.retypeL, Val.widen, Val.retype, Nat.le_refl, ↓reduceIte]
      cases w' <;> cases b <;> simp [ValRel, Width.bits]
    | _ => exact absurd hf id
  | ptr e =>
    simp only [cls, Option.some.injEq] at hc
    subst hc
    cases v with
    | poison => exact trivial
    | int w x =>
      have hf : kNarrow 64 w.bits = true := hf
      cases w <;> simp [kNarrow, Width.bits] at hf
      exact hv
    | ptr p => exact (valRel_word hA hv : ValRel ι p.word r)
    | bool b =>
      have hv : r = if b then 1 else 0 := hv
      subst hv
      simp only [Val.retypeL, Val.widen, Val.retype]
      exact Or.inl rfl
    | _ => exact absurd hf id
  | bool =>
    simp only [cls, Option.some.injEq] at hc
    subst hc
    cases v with
    | poison => exact trivial
    | int w x =>
      have hf : kNarrow 1 w.bits = true := hf
      cases w <;> simp [kNarrow, Width.bits] at hf
    | bool b => exact hv
    | ptr p =>
      have hf : kNarrow 1 64 = true := hf
      simp [kNarrow] at hf
    | _ => exact absurd hf id
  | _ => simp [cls] at hc

/-! ## Registers -/

theorem objX?_some {r : Nat} {k : GoFV.Arm64.Reg} (h : objX? r = some k) :
    r < 29 ∧ k.toNat = (if r < 18 then r else if r < 26 then r + 1 else r + 2) := by
  unfold objX? at h
  split at h
  · cases h; refine ⟨by omega, ?_⟩; simp [*]; omega
  · split at h
    · cases h; refine ⟨by omega, ?_⟩; simp [*]; omega
    · split at h
      · cases h; refine ⟨by omega, ?_⟩; simp [*]; omega
      · cases h

theorem objX?_inj {r r' : Nat} {k : GoFV.Arm64.Reg} (h : objX? r = some k)
    (h' : objX? r' = some k) : r = r' := by
  obtain ⟨h1, h2⟩ := objX?_some h
  obtain ⟨h1', h2'⟩ := objX?_some h'
  rw [h2] at h2'
  split at h2' <;> split at h2' <;> (try split at h2') <;> (try split at h2') <;> omega

theorem objV?_lt {r : Nat} {k : GoFV.Arm64.Reg} (h : objV? r = some k) : 31 ≤ r := by
  unfold objV? at h
  split at h
  · omega
  · cases h

/-- The X register (index `k`, `31`: `ZR`) of a register G1 writes. -/
theorem objOf?_dest {r k : Nat} (hk : k < 32) (h : objOf? r = some (GoFV.Asm.ARM64.REG_R0 + k))
    (hd : destOK r = true) :
    (r = zeroReg ∧ k = 31) ∨ (r < 26 ∧ k < 27 ∧ objX? r = some (BitVec.ofNat 5 k)) := by
  unfold objOf? at h
  by_cases hz : r = zeroReg
  · subst hz
    simp only [↓reduceIte, Option.some.injEq] at h
    left; refine ⟨rfl, ?_⟩
    have : GoFV.Asm.ARM64.REGZERO = 8223 := rfl
    have : GoFV.Asm.ARM64.REG_R0 = 8192 := rfl
    omega
  · simp only [hz, ↓reduceIte, Option.map_eq_some_iff] at h
    obtain ⟨kk, hkk, he⟩ := h
    have hr : r < 26 := by simp [destOK, hz] at hd; omega
    have hk' : kk.toNat = k := by have : GoFV.Asm.ARM64.REG_R0 = 8192 := rfl; omega
    obtain ⟨-, h2⟩ := objX?_some hkk
    right
    refine ⟨hr, ?_, ?_⟩
    · split at h2 <;> (try split at h2) <;> omega
    · rw [hkk]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega

/-- Writing a register G1 may write (`setReg` on `runLoc`'s side, `wX` on the machine's) with
related values keeps `LocMatch`, at any PC. -/
theorem locMatch_setReg {E : MatchEnv} {s : LocState} {b : ID} {i : Nat} {m : GoFV.Arm64.MState}
    (h : LocMatch E s b i m) {r k : Nat} {x : Val} {val : BitVec 64} (hk : k < 32)
    (hrk : objOf? r = some (GoFV.Asm.ARM64.REG_R0 + k)) (hd : destOK r = true)
    (hx : ValRel E.ι x val) {b' : ID} {i' : Nat} :
    LocMatch E (s.setReg r x) b' i' { m.wX (BitVec.ofNat 5 k) val with pc := E.pcOf b' i' } := by
  rcases objOf?_dest hk hrk hd with ⟨rfl, rfl⟩ | ⟨hr, hk27, hobj⟩
  · -- `ZERO`: nothing changes
    have hs : s.setReg zeroReg x = s := by simp [LocState.setReg]
    have hm : m.wX (BitVec.ofNat 5 31) val = m := by simp [GoFV.Arm64.MState.wX]
    rw [hs, hm]
    exact { h with pc := rfl }
  · have hk31 : (BitVec.ofNat 5 k : GoFV.Arm64.Reg) ≠ 31 := by
      intro he; have := congrArg BitVec.toNat he; simp at this; omega
    have hw : m.wX (BitVec.ofNat 5 k) val =
        { m with x := fun i => if i = BitVec.ofNat 5 k then val else m.x i } := by
      unfold GoFV.Arm64.MState.wX; exact if_neg hk31
    rw [hw]
    have hx' : ∀ j, ({ { m with x := fun i => if i = BitVec.ofNat 5 k then val else m.x i } with
        pc := E.pcOf b' i' } : GoFV.Arm64.MState).x j = if j = BitVec.ofNat 5 k then val else m.x j :=
      fun _ => rfl
    have hne : ∀ j : Nat, 28 ≤ j → j < 32 → (BitVec.ofNat 5 j : GoFV.Arm64.Reg) ≠ BitVec.ofNat 5 k := by
      intro j hj1 hj2 he; have := congrArg BitVec.toNat he; simp at this; omega
    refine ⟨?_, ?_, ?_, ?_, ?_, rfl⟩
    · intro r' v hv
      have hrz : r ≠ zeroReg := by unfold zeroReg; omega
      by_cases hrr : r' = r
      · subst hrr
        simp only [LocState.setReg] at hv
        split at hv
        · rename_i hlt
          simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hlt
          rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hlt.1] at hv
          simp only [Option.some.injEq] at hv
          subst hv
          refine ⟨fun k' hk' => ?_, fun k' hk' => absurd (objV?_lt hk') (by omega)⟩
          rw [hobj] at hk'; cases hk'
          rw [hx']; simp [hx]
        · rename_i hlt
          simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_and,
            Decidable.not_not] at hlt
          have := (Array.getElem?_eq_some_iff.1 hv).1
          exact absurd (hlt this) hrz
      · have hv' : s.regs[r']? = some v := by
          simp only [LocState.setReg] at hv
          split at hv
          · rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm hrr)] at hv
            exact hv
          · exact hv
        obtain ⟨h1, h2⟩ := h.regs r' v hv'
        refine ⟨fun k' hk' => ?_, fun k' hk' => h2 k' hk'⟩
        rw [hx']
        have : k' ≠ BitVec.ofNat 5 k := by
          intro he; subst he; exact hrr (objX?_inj hk' hobj)
        simp only [this, ↓reduceIte]
        exact h1 k' hk'
    · exact h.flags
    · exact h.slots
    · exact h.mem
    · obtain ⟨h1, h2, h3, h4⟩ := h.frame
      refine ⟨h1, ?_, ?_, ?_⟩
      · rw [hx']; simp only [show (28 : GoFV.Arm64.Reg) = BitVec.ofNat 5 28 from rfl,
          hne 28 (by omega) (by omega), ↓reduceIte]; exact h2
      · intro hf
        obtain ⟨a1, a2, a3⟩ := h3 hf
        refine ⟨?_, a2, a3⟩
        rw [hx']; simp only [show (29 : GoFV.Arm64.Reg) = BitVec.ofNat 5 29 from rfl,
          hne 29 (by omega) (by omega), ↓reduceIte]; exact a1
      · intro hf
        obtain ⟨a1, a2⟩ := h4 hf
        refine ⟨?_, ?_⟩
        · rw [hx']; simp only [show (29 : GoFV.Arm64.Reg) = BitVec.ofNat 5 29 from rfl,
            hne 29 (by omega) (by omega), ↓reduceIte]; exact a1
        · rw [hx']; simp only [show (30 : GoFV.Arm64.Reg) = BitVec.ofNat 5 30 from rfl,
            hne 30 (by omega) (by omega), ↓reduceIte]; exact a2

end GoFV.Proof.Gen

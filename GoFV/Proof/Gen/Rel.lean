import GoFV.SSA.Sem.LocMatch
import GoFV.Proof.PtrAddr
import GoFV.Gen.Check

/-!
# Values and registers under `LocMatch` in slice G1 (`docs/plans/proofs3.md` §3)

`AddrAgree ι`: the injection puts every block that has a Phase 1 address (`Blk.base?`) at that
address. Then a pointer's injected address is its Phase 1 address, so the second disjunct of
`ValRel` at `.int .w64` collapses to the first, `Ptr.word` relates like the pointer, and Phase 2's
register arithmetic on pointer words (`Arm64.reg` reads a convertible pointer as its address) is
the machine's.

`Fits c v`: a register content of width class `c` (`GoFV.Gen.Check.cls`). Reading it at a shape
of class `c` (`Val.retypeL`) keeps `ValRel` (`valRel_retypeL`); a narrower content read at a wider
shape would be zero-extended by `retypeL` while the machine's upper bits are arbitrary, which the
validator's one-class-per-register rule excludes.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check

/-- Every block with a Phase 1 address sits at that address. -/
def AddrAgree (ι : Blk → Option (BitVec 64)) : Prop :=
  ∀ b n a, b.base? = some n → ι b = some a → a = BitVec.ofNat 64 n

/-- A register content of width class `c`. -/
def Fits (c : Nat) : Val → Prop
  | .poison => True
  | .int w _ => w.bits = c
  | .ptr _ => c = 64
  | .bool _ => c = 1
  | _ => False

variable {ι : Blk → Option (BitVec 64)}

/-- The injected address of a pointer with a Phase 1 address is that address. -/
theorem ptrRel_addr (hA : AddrAgree ι) {p : Ptr} {r a : BitVec 64} (h : PtrRel ι p r)
    (ha : p.addr? = some a) : r = a := by
  obtain ⟨base, hb, rfl⟩ := h
  unfold Ptr.addr? at ha
  cases hn : p.blk.base? with
  | none => rw [hn] at ha; cases ha
  | some n =>
    rw [hn] at ha
    cases ha
    rw [hA _ _ _ hn hb]

/-- `Ptr.word` relates like the pointer. -/
theorem valRel_word (hA : AddrAgree ι) {p : Ptr} {r : BitVec 64} (h : PtrRel ι p r) :
    ValRel ι p.word r := by
  unfold Ptr.word
  split
  · rename_i a _ ha
    exact Or.inl (ptrRel_addr hA h ha)
  · exact h

/-- Under `AddrAgree`, a 64-bit integer relates to exactly its own word. -/
theorem valRel_i64 (hA : AddrAgree ι) {x r : BitVec 64} (h : ValRel ι (.int .w64 x) r) :
    r = x := by
  rcases h with h | ⟨_, h⟩
  · exact h
  · exact ptrRel_addr hA h (Ptr.addr?_ofAddr x)

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
      unfold Ptr.word; split <;> rfl
    | _ => simp only [Val.retypeL, Val.widen, Val.retype] <;> trivial
  | ptr e =>
    simp only [cls, Option.some.injEq] at hc
    subst hc
    cases v with
    | int w x =>
      simp only [Val.retypeL, Val.widen]
      cases w <;> simp only [Val.retype, ↓reduceIte] <;> first | rfl | trivial | decide
    | bool b => simp only [Val.retypeL, Val.widen, Val.retype]; rfl
    | ptr p => simp only [Val.retypeL, Val.widen, Val.retype]; unfold Ptr.word; split <;> rfl
    | _ => simp only [Val.retypeL, Val.widen, Val.retype] <;> trivial
  | bool =>
    simp only [cls, Option.some.injEq] at hc
    subst hc
    cases v <;> simp only [Val.retypeL, Val.widen, Val.retype] <;> trivial
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

import GoFV.Opt.MemCombine.Sym
import GoFV.Proof.AtomSimDen
import GoFV.Proof.MemRefine

variable [GoFV.SSA.Sem.Addrs]

/-!
# memcombine: what a symbolic byte means (issue #35)

`SB.sem V s`: the byte a symbolic byte stands for when the values are `V` — a constant, byte `k`
of an integer value, or the byte at `base + idx + off` in a memory value (`ptrAt`, `base` read as
a pointer word, `Val.asPtrWord`), read as a one-byte access that must be valid and concrete.
`LoadOK V r`: the load `r` of a description reads, through its pointer (which reads as
`base + idx + off`), `r.size` concrete bytes.

Both are monotone in `V` (`sem_mono`, `loadOK_mono`): a refinement of the values keeps every
defined byte. `splitP_sound` (`MemCombineSplit`): a pointer `splitP` takes apart is, when it
reads as a pointer, `base + idx + off`.
-/

namespace GoFV.Proof.MemCombine

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.MemCombine.Check GoFV.Proof.Term GoFV.Proof.AtomSim

/-- Byte `k` of an integer value. -/
def byte? : Val → Nat → Option (BitVec 8)
  | .int w x, k => if k < w.bytes then some (byteOf x.toNat k) else none
  | _, _ => none

/-- `base + idx + off`. -/
def ptrAt (P : Ptr) (I : BitVec 64) (o : Int) : Ptr := ⟨P.blk, P.off + I + BitVec.ofInt 64 o⟩

/-- The value of an index (`0` without one). -/
def idxVal (V : ID → Val) : Option ID → Option (BitVec 64)
  | none => some 0
  | some i => asOffset (V i)

/-- The concrete byte of a one-byte read. -/
def byteAt (M : Mem) (p : Ptr) : Option (BitVec 8) :=
  match M.read p 1 with
  | some bs => match (bs[0]? : Option Byte) with
    | some (.b x) => some x
    | _ => none
  | none => none

/-- **The byte a symbolic byte stands for.** -/
def _root_.GoFV.Opt.MemCombine.Check.SB.sem (V : ID → Val) : SB → Option (BitVec 8)
  | .lit b => some b
  | .vb y k => byte? (V y) k
  | .mb m b i o =>
    match V m, (V b).asPtrWord, idxVal V i with
    | .mem M, some P, some I => byteAt M (ptrAt P I o)
    | _, _, _ => none

/-- All bytes of an array are concrete. -/
def Concrete (bs : Array Byte) : Prop := ∀ x ∈ bs.toList, ∃ b, x = .b b

/-- **A load of a description**: its pointer reads as `base + idx + off` (pointer words,
`Val.asPtrWord`) and reads `size` concrete bytes of its memory. -/
def LoadOK (V : ID → Val) (r : LoadRec) : Prop :=
  ∃ M P I bs, V r.mem = .mem M ∧ (V r.base).asPtrWord = some P ∧ idxVal V r.idx = some I ∧
    (V r.ptr).asPtrWord = some (ptrAt P I r.off) ∧ M.read (ptrAt P I r.off) r.size = some bs ∧
    Concrete bs

/-! ## Monotonicity -/

theorem refines_int {w : Width} {x : BitVec w.bits} {v : Val} (h : Sem.Refines (.int w x) v) :
    v = .int w x := by cases h; rfl

theorem refines_ptr {p : Ptr} {v : Val} (h : Sem.Refines (.ptr p) v) : v = .ptr p := by
  cases h; rfl

theorem refines_mem {M : Mem} {v : Val} (h : Sem.Refines (.mem M) v) :
    ∃ M', v = .mem M' ∧ Mem.Refines M M' := by
  cases h with
  | mem h => exact ⟨_, rfl, h⟩

theorem byte?_mono {v v' : Val} (h : Sem.Refines v v') {k : Nat} {b : BitVec 8}
    (hb : byte? v k = some b) : byte? v' k = some b := by
  cases v with
  | int w x => rw [refines_int h]; exact hb
  | _ => simp [byte?] at hb

theorem asOffset_mono {v v' : Val} (h : Sem.Refines v v') {I : BitVec 64}
    (hI : asOffset v = some I) : asOffset v' = some I := by
  cases v with
  | int w x => rw [refines_int h]; exact hI
  | _ => simp [asOffset] at hI

theorem idxVal_mono {V V' : ID → Val} (h : ∀ y, Sem.Refines (V y) (V' y)) {i : Option ID}
    {I : BitVec 64} (hI : idxVal V i = some I) : idxVal V' i = some I := by
  cases i with
  | none => exact hI
  | some j => exact asOffset_mono (h j) hI

/-- A concrete byte of a read stays in a refined memory. -/
theorem byteAt_mono {M M' : Mem} (h : Mem.Refines M M') {p : Ptr} {b : BitVec 8}
    (hb : byteAt M p = some b) : byteAt M' p = some b := by
  unfold byteAt at hb ⊢
  cases hr : M.read p 1 with
  | none => rw [hr] at hb; cases hb
  | some bs =>
    rw [hr] at hb
    obtain ⟨bs', hr', hbs⟩ := Mem.Refines.read h hr
    rw [hr']
    dsimp only at hb ⊢
    rcases BytesRefineA.getElem? hbs 0 with ⟨hx, -⟩ | ⟨x, y, hx, hy, hxy⟩
    · rw [hx] at hb; cases hb
    · rw [hx] at hb
      rw [hy]
      cases x with
      | b x =>
        cases hxy
        exact hb
      | _ => cases hb

theorem sem_mono {V V' : ID → Val} (h : ∀ y, Sem.Refines (V y) (V' y)) {s : SB}
    {b : BitVec 8} (hs : s.sem V = some b) : s.sem V' = some b := by
  cases s with
  | lit c => exact hs
  | vb y k => exact byte?_mono (h y) hs
  | mb m bb i o =>
    simp only [SB.sem] at hs ⊢
    cases hm : V m with
    | mem M =>
      rw [hm] at hs
      cases hp : (V bb).asPtrWord with
      | some P =>
        rw [hp] at hs
        cases hI : idxVal V i with
        | none => rw [hI] at hs; cases hs
        | some I =>
          rw [hI] at hs
          have h1 : Sem.Refines (.mem M) (V' m) := hm ▸ h m
          obtain ⟨M', hm', hM⟩ := refines_mem h1
          rw [hm', (h bb).asPtrWord hp, idxVal_mono h hI]
          exact byteAt_mono hM hs
      | none => rw [hp] at hs; cases hs
    | _ => rw [hm] at hs; cases hs

theorem concrete_mono {bs bs' : Array Byte} (h : BytesRefineA bs bs') (hc : Concrete bs) :
    bs' = bs := (BytesRefineA.eq h fun x hx => by
  obtain ⟨b, rfl⟩ := hc x hx; nofun).symm

theorem loadOK_mono {V V' : ID → Val} (h : ∀ y, Sem.Refines (V y) (V' y)) {r : LoadRec}
    (hr : LoadOK V r) : LoadOK V' r := by
  obtain ⟨M, P, I, bs, hm, hp, hI, hq, hrd, hc⟩ := hr
  have h1 : Sem.Refines (.mem M) (V' r.mem) := hm ▸ h r.mem
  obtain ⟨M', hm', hM⟩ := refines_mem h1
  obtain ⟨bs', hrd', hbs⟩ := Mem.Refines.read hM hrd
  refine ⟨M', P, I, bs', hm', (h r.base).asPtrWord hp, idxVal_mono h hI, (h r.ptr).asPtrWord hq,
    hrd', ?_⟩
  rw [concrete_mono hbs hc]; exact hc

end GoFV.Proof.MemCombine

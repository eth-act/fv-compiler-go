import GoFV.Proof.Obj.Words
import GoFV.Proof.Obj.Spec

/-!
# The prologue and the epilogue (`checkPrologue`, `retOK`; `docs/plans/proofs3.md` §2, row C6/D3)

`obj_entry`: from a call of the function (`MachEntry` at `base`), when the stack check passes
(`CheckPasses`: the limit above `stackguard0`), the prologue runs to the body's first offset in a
state with the frame of `BodyEntry` (`SP` lowered by `autosize`, the caller's `LR` and `FP`
saved, `R29 = SP − 8`); registers but the stack check's (`R16`, `R17`), the large-frame scratch
`R20`, `R27` and `R29` are unchanged, and memory outside the two saved words.

`obj_exit`: from a state at the offset of a P0 `RET` (without operand), the epilogue pops the
frame (`SP` raised by `autosize`), restores `R29` (a leaf recomputes it, others reload it from
`-8(SP)`) and returns through `R30` (a non-leaf reloads it from `0(SP)` first).
-/

namespace GoFV.Proof.Obj

open GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj
open GoFV.SSA.Sem (MStar)

/-- The stack check with frame size `az` reading `gOff(g)` passes from `s`: the limit (`SP`,
or `SP − (az − StackSmall)` above `StackSmall`) is above the guard, unsigned. -/
def CheckPasses (az : Int) (gOff : Nat) (s : MState) : Prop :=
  (readMem s.mem (s.x 28 + BitVec.ofNat 64 gOff) 8).toNat <
    (if az ≤ 128 then s.sp else s.sp + BitVec.ofInt 64 (-(az - 128))).toNat

theorem obj_entry {ps : Array Prog} {spills : Array Spill} {o : ObjIn} {tab : Tab}
    {base : BitVec 64} {sym : Nat → BitVec 64} {code : Code} {H : Hooks} {retM : BitVec 64}
    {room : Nat} {s0 : MState}
    (hc : checkObj ps spills o = .ok tab) (hlink : linkCode base sym o.text o.relocs.toList = .ok code)
    (hsz : o.text.size ≤ 2 ^ 64) (hret : code retM = none)
    (hE : MachEntry code base room s0) (hroom : tab.autosize + 8 ≤ room)
    (hg : (s0.x 28).toNat + 32 ≤ 2 ^ 64)
    (hpass : ∀ ce tail gOff, tab.check = some (ce, tail, gOff) → CheckPasses tab.autosize gOff s0) :
    ∃ s1, MStar H code retM s0 s1 ∧ BodyEntry tab.autosize.toNat s0 s1 ∧
      s1.pc = base + BitVec.ofNat 64 (tab.offs[0]!) ∧
      (∀ k : Reg, k ≠ 16 → k ≠ 17 → k ≠ 20 → k ≠ 27 → k ≠ 29 → s1.x k = s0.x k) ∧
      s1.v = s0.v ∧ (∀ a, 16 ≤ (a - (s1.sp - 8)).toNat → s1.mem a = s0.mem a) := by
  sorry

theorem obj_exit {ps : Array Prog} {spills : Array Spill} {o : ObjIn} {tab : Tab}
    {base : BitVec 64} {sym : Nat → BitVec 64} {code : Code} {H : Hooks} {retM : BitVec 64}
    {k : Nat} {t : MState}
    (hc : checkObj ps spills o = .ok tab) (hlink : linkCode base sym o.text o.relocs.toList = .ok code)
    (hsz : o.text.size ≤ 2 ^ 64) (hret : code retM = none) (hk : k < ps.size)
    (hr : ps[k].as = .RET) (hto : ps[k].to.type = .NONE) (hnosym : ps[k].to.sym = none)
    (hpc : t.pc = base + BitVec.ofNat 64 (tab.offs[k]!))
    (hsp : 4096 + 8 ≤ t.sp.toNat ∧ t.sp.toNat + 8 ≤ 2 ^ 64) :
    ∃ t', MStar H code retM t t' ∧
      t'.pc = (if tab.autosize = 0 ∨ tab.leaf then t.x 30 else t.word t.sp) ∧
      t'.x 30 = (if tab.autosize = 0 ∨ tab.leaf then t.x 30 else t.word t.sp) ∧
      t'.sp = t.sp + BitVec.ofInt 64 tab.autosize ∧
      t'.x 29 = (if tab.autosize = 0 then t.x 29
        else if tab.leaf then t.sp + BitVec.ofInt 64 (tab.autosize - 8) else t.word (t.sp - 8)) ∧
      (∀ r : Reg, r ≠ 27 → r ≠ 29 → r ≠ 30 → t'.x r = t.x r) ∧ t'.v = t.v ∧ t'.mem = t.mem ∧
      t'.nzcv = t.nzcv := by
  sorry

end GoFV.Proof.Obj

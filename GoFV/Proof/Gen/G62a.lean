import GoFV.Proof.Gen.Spec62
import GoFV.Proof.Gen.G61e

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G62: an incoming stack argument (`docs/plans/proofs3.md` §4)

An `Arg {x} [off]` of a parameter the ABI assigns to the stack (`VK62.arg`) runs as
`argVal`: piece `off` of `x`'s image, at the value's shape, written to its home, the slot `k` of
the piece (`stepLoc_arg`). Genssa emits no code for it: the caller stored the argument in its own
frame, at `k`'s `NAME_PARAM` operand, before the call. The machine does not step; the run premise
`ArgOK` is the caller's side of the ABI: the machine's bytes at `k`'s frame address hold the
piece as a spill slot holds a value (`SlotRel`). Then `g62_arg` gives `LocMatch` with the new
slot, every other slot and register unchanged, at either mode `osp`. The class table is unchanged
(`kStep_arg`) and the upper-bit table is empty after it (`uStep35_arg`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-- **The caller's stack argument** (the run premise of slice G62): when `v` is an `Arg {x} [off]`
homed in a slot `k` at frame offset `o`, the machine's bytes at `SP + o` hold `argVal`'s piece of
`x` at the value's shape, as a spill slot holds a value (`SlotRel`). The caller of an `ABI0`
function stores each stack-assigned argument at `8(RSP)` and up before the `CALL`, which is the
callee's `NAME_PARAM` operand `x+off(FP)`. -/
def ArgOK (E : MatchEnv) (lc : LocCtx) (s : LocState) (v : Value) (m : MState) : Prop :=
  v.op = .Arg → ∀ x k o y, v.aux = some x → lc.home v.id = some (.slot k) → E.slot k = some o →
    argVal lc.ctx s.fr x v.auxInt.toInt (lc.ty v.id) = .ok y →
    SlotRel E.ι (E.lc.slotTy k) (y.retypeL (lc.ty v.id)) m.mem (E.sp + BitVec.ofInt 64 o)

section
variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

/-- `Arg {x} [off]`: `argVal`'s piece of `x` at the value's shape, written to its home. -/
theorem stepLoc_arg (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .Arg) {x : AuxRef} (hx : v.aux = some x) (h : stepLoc env lc s v = .ok s') :
    ∃ y, argVal lc.ctx s.fr x v.auxInt.toInt (lc.ty v.id) = .ok y ∧
      s' = s.write lc v.id (y.retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, -, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
  have he : evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) =
      argVal lc.ctx s.fr x v.auxInt.toInt (lc.ty v.id) := by
    have hg : Op.Arg.generic = true := by decide
    unfold evalOpL evalOp; rw [hop]; simp [hx, hg]
  rw [he] at hr
  exact ⟨r, hr, rfl⟩

end

/-- An `Arg` homed in a slot leaves the class table. -/
theorem kStep_arg {lc : LocCtx} {K : KMap} {v : Value} {k : SlotKey} (hop : v.op = .Arg)
    (hh : lc.home v.id = some (.slot k)) : kStep lc K v = K := by
  simp [kStep, hop, hh]

/-- The upper-bit table is empty after an `Arg`. -/
theorem uStep35_arg {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value}
    (hop : v.op = .Arg) : uStep35 lc L v = [] := by
  have hl : loadOp? v.op = none := by rw [hop]; rfl
  have hi : loadIdxOp? v.op = none := by rw [hop]; rfl
  have hp : pairOp35 lc v = false := by simp [pairOp35, hop]
  have hk : keep34 v = false := by simp [keep34, keep31, keepOp31, keepOp34, hop]
  have hk31 : keep31 v = false := by simp [keep31, keepOp31, hop]
  have hue : uEntry lc v = none := by
    have : narrowLd? lc v = none := by
      unfold narrowLd?
      rw [hl, hi]
    simp only [uEntry, this]
  rw [uStep35_other (ldEntry35_none hl) hp (by rw [hop]; nofun), uStep34_other hk,
    uStep31_other hk31,
    uStepL_other hue (by rw [hop]; nofun) (by rw [hop]; nofun)]

/-- **An incoming stack argument** (`VK62.arg`, G66's narrow ones): no code; under `ArgOK` the slot
of its piece holds it in the machine, so the match and the invariants hold after it at either
mode `osp`. -/
theorem g62_arg {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {osp : Bool} {x : AuxRef} {o : Int} {c : Nat}
    (hE : G2Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (hl : lc.ctx.f.lowered = true)
    (hvs : VStep2 ps .none j j')
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s osp)
    (htemp : (lc.temps[v.id]?).join = none) (hop : v.op = .Arg) (hx : v.aux = some x)
    (hcf : checkFrame lc g = .ok ()) (hcv : cls (lc.ty v.id) = some c)
    (hh : lc.home v.id = some (.slot (argKey x v.type v.auxInt.toInt)))
    (hso : g.slotOp (argKey x v.type v.auxInt.toInt) = some (.PARAM, o))
    (harg : ArgOK E lc s v m) (hs : stepLoc env lc s v = .ok s') :
    PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m ∧
      LocMatch E s' bid (i + 1) m ∧ G3Inv E lc (kStep lc K v) s' osp := by
  obtain ⟨y, hy, rfl⟩ := stepLoc_arg hl htemp hop hx hs
  rw [write_slot hh, kStep_arg hop hh]
  have hk := hE.slot _ (mem_homeSlots hh) .PARAM o hso
  have hrel := harg hop x _ _ y hx hh hk hy
  have hpc : E.pcOf bid (i + 1) = m.pc := by
    rw [hj', show j' = j from hvs, ← hj]; exact hm.pc.symm
  refine ⟨.refl, ⟨hm.regs, hm.flags, ?_, hm.mem, hm.frame, hpc.symm⟩, ⟨hinv.core.regs, ?_⟩, ?_⟩
  · intro k' v' hk'
    rcases lookup_setSlot hk' with ⟨rfl, rfl⟩ | ⟨-, hold⟩
    · exact ⟨_, hk, hrel⟩
    · exact hm.slots k' v' hold
  · exact hinv.core.mem
  · intro k' v' hk'
    rcases lookup_setSlot hk' with ⟨rfl, rfl⟩ | ⟨-, hold⟩
    · exact ⟨by rw [slotCls_home hcf hh hcv]; exact fits_retypeL hcv _, v.id, hh⟩
    · exact hinv.slots k' v' hold

end GoFV.Proof.Gen

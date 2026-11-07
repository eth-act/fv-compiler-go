import GoFV.Proof.Gen.Progs
import GoFV.Arm64.Exec

/-!
# The branches of slice G1 (`docs/plans/proofs3.md` §3)

`progStep` of the branch Progs the genssa validator accepts (`B<cond>`, `JMP`, `CBZ`/`CBNZ` to a
Prog of the list), and the agreement of `runLoc`'s branch decision with the machine's: a flags
block kind's condition (`Arm64.taken`, `Cond.onVal`) on flags related to `NZCV` (`FlagsRel`) is
the machine's `ConditionHolds` (`onVal_holds`), and the opcodes `condBr` gives a kind test that
condition and its negation (`condBr_spec`).
-/

namespace GoFV.Proof.Gen

open GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64 GoFV.Gen.Check GoFV.SSA GoFV.SSA.Sem

variable {L : Link} {p : Prog} {s : MState} {next t : BitVec 64}

/-- `B<cond> target`: the target if the condition holds, else the fall-through. -/
theorem progStep_bcond {c : Cond} {tid : Nat} (hn : L.nextAddr p.id = some next)
    (hc : condAs p.as = some c) (ht : p.to = brA tid) (hL : L.addr tid = some t) :
    progStep L p s = .ok { s with pc := if c.holds s.nzcv then t else next } := by
  sorry

/-- `JMP target`. -/
theorem progStep_jmp {tid : Nat} (hn : L.nextAddr p.id = some next) (has : p.as = .JMP)
    (ht : p.to = brA tid) (hL : L.addr tid = some t) :
    progStep L p s = .ok { s with pc := t } := by
  sorry

/-- `CBZ Rk, target` / `CBNZ Rk, target` on a 64-bit register (`k = 31`: `ZR`). -/
theorem progStep_cbz {k tid : Nat} (hk : k < 32) (hn : L.nextAddr p.id = some next)
    (has : p.as = .CBZ ∨ p.as = .CBNZ) (hf : p.from_ = regA (REG_R0 + k)) (ht : p.to = brA tid)
    (hL : L.addr tid = some t) :
    progStep L p s = .ok { s with
      pc := if (s.rX (BitVec.ofNat 5 k) == 0) = (p.as == .CBZ) then t else next } := by
  sorry

/-- A condition defined on flags related to `NZCV` is the machine's `ConditionHolds`. -/
theorem onVal_holds {c : Cond} {f : Val} {nz : Flags} {b : Bool} (h : FlagsRel f nz)
    (hc : c.onVal f = some b) : c.holds nz = b := by
  sorry

/-- The opcodes of a flags block kind: the first tests the kind's condition (`Arm64.taken`), the
second its negation. -/
theorem condBr_spec {k : BlockKind} {asm inv : As} (h : condBr k = some (asm, inv)) :
    ∃ c c', condAs asm = some c ∧ condAs inv = some c' ∧ (∀ a x, Arm64.taken k a x = c.onVal x) ∧
      ∀ f, c'.holds f = !c.holds f := by
  sorry

/-- The opcodes of a register test block kind: `Z` branches on zero with `CBZ`, `NZ` with
`CBNZ`; the second opcode is the other one. -/
theorem zeroBr_spec {k : BlockKind} {asm inv : As} (h : zeroBr k = some (asm, inv)) :
    (k = .ARM64Z ∧ asm = .CBZ ∧ inv = .CBNZ) ∨ (k = .ARM64NZ ∧ asm = .CBNZ ∧ inv = .CBZ) := by
  sorry

end GoFV.Proof.Gen

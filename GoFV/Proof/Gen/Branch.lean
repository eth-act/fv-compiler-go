import GoFV.Proof.Gen.Progs
import GoFV.Arm64.Exec

variable [GoFV.SSA.Sem.Addrs]

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

/-- A Prog whose effect is a branch to `t` taken when `b`. -/
private theorem progStep_br {b : Bool} (hn : L.nextAddr p.id = some next) (hs : p.isSkip = false)
    (he : progEffect ⟨L, s, p⟩ = .ok (if b then { pc := some t } else {})) :
    progStep L p s = .ok { s with pc := if b then t else next } := by
  rw [progStep_eq hn hs he (by cases b <;> rfl)]
  cases b <;> rfl

set_option hygiene false in
/-- One opcode `B<cond>` of `progStep_bcond` (`has : p.as = op`, `op` named `n`). -/
local macro "bcond_case " op:term:max n:str : tactic => `(tactic| (
  cases hc
  have hname : As.name $op = $n := rfl
  apply progStep_br hn (by simp [Prog.isSkip, has])
  unfold progEffect
  simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
    ProgOp.movMem, ProgOp.pairOp, ProgOp.rmw, ProgOp.bcond, ProgOp.startsS, ht, brA, hT]
  rfl))

/-- `B<cond> target`: the target if the condition holds, else the fall-through. -/
theorem progStep_bcond {c : Cond} {tid : Nat} (hn : L.nextAddr p.id = some next)
    (hc : condAs p.as = some c) (ht : p.to = brA tid) (hL : L.addr tid = some t) :
    progStep L p s = .ok { s with pc := if c.holds s.nzcv then t else next } := by
  have hT := ctx_target (c := ⟨L, s, p⟩) hL
  simp only [brA] at hT
  unfold condAs at hc
  split at hc
  next has => bcond_case As.BEQ "BEQ"
  next has => bcond_case As.BNE "BNE"
  next has => bcond_case As.BLT "BLT"
  next has => bcond_case As.BGE "BGE"
  next has => bcond_case As.BLE "BLE"
  next has => bcond_case As.BGT "BGT"
  next has => bcond_case As.BLO "BLO"
  next has => bcond_case As.BHS "BHS"
  next has => bcond_case As.BLS "BLS"
  next has => bcond_case As.BHI "BHI"
  next => cases hc

/-- `JMP target`. -/
theorem progStep_jmp {tid : Nat} (hn : L.nextAddr p.id = some next) (has : p.as = .JMP)
    (ht : p.to = brA tid) (hL : L.addr tid = some t) :
    progStep L p s = .ok { s with pc := t } := by
  have hname : As.name .JMP = "JMP" := rfl
  have he : progEffect ⟨L, s, p⟩ = .ok { pc := some t } := by
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
      ProgOp.movMem, ProgOp.pairOp, ProgOp.rmw, ProgOp.bcond, ProgOp.startsS, ht, brA]
    have hT := ctx_target (c := ⟨L, s, p⟩) hL
    simp only [brA] at hT
    simp only [hT]
    rfl
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he rfl]
  rfl

/-- `CBZ Rk, target` / `CBNZ Rk, target` on a 64-bit register (`k = 31`: `ZR`). -/
theorem progStep_cbz {k tid : Nat} (hk : k < 32) (hn : L.nextAddr p.id = some next)
    (has : p.as = .CBZ ∨ p.as = .CBNZ) (hf : p.from_ = regA (REG_R0 + k)) (ht : p.to = brA tid)
    (hL : L.addr tid = some t) :
    progStep L p s = .ok { s with
      pc := if (s.rX (BitVec.ofNat 5 k) == 0) = (p.as == .CBZ) then t else next } := by
  have hT := ctx_target (c := ⟨L, s, p⟩) hL
  simp only [brA] at hT
  rcases has with has | has
  · have hname : As.name .CBZ = "CBZ" := rfl
    have h := progStep_br (b := (s.rX (BitVec.ofNat 5 k) == 0)) (s := s) (t := t) hn
      (by simp [Prog.isSkip, has]) ?_
    · rw [h]
      simp [has]
    · unfold progEffect
      simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
        ProgOp.movMem, ProgOp.pairOp, ProgOp.rmw, ProgOp.bcond, ProgOp.startsS, ht, brA, hT, hf,
        regA, ctx_x_r0 hk, ProgOp.endsS, ProgOp.trunc]
      simp only [show "CBZ".toList.isPrefixOf "CBZ".toList = true by decide]
      simp
      rfl
  · have hname : As.name .CBNZ = "CBNZ" := rfl
    have h := progStep_br (b := !(s.rX (BitVec.ofNat 5 k) == 0)) (s := s) (t := t) hn
      (by simp [Prog.isSkip, has]) ?_
    · rw [h, has, show (As.CBNZ == As.CBZ) = false by decide]
      simp
    · unfold progEffect
      simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
        ProgOp.movMem, ProgOp.pairOp, ProgOp.rmw, ProgOp.bcond, ProgOp.startsS, ht, brA, hT, hf,
        regA, ctx_x_r0 hk, ProgOp.endsS, ProgOp.trunc]
      simp only [show "CBZ".toList.isPrefixOf "CBNZ".toList = false by decide]
      simp
      rfl

private theorem bitRel_flagBit {x : Val} {b : Bool} (h : BitRel x b) :
    x.flagBit = some b ∨ x.flagBit = none := by
  cases x <;> simp_all [BitRel, Val.flagBit]

private theorem eval_some {c : Cond} {n z cf v : Option Bool} {fn fz fc fv b : Bool}
    (hn : n = some fn ∨ n = none) (hz : z = some fz ∨ z = none)
    (hc : cf = some fc ∨ cf = none) (hv : v = some fv ∨ v = none)
    (h : c.eval n z cf v = some b) : c.eval (some fn) (some fz) (some fc) (some fv) = some b := by
  cases c <;>
    rcases hn with rfl | rfl <;> rcases hz with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hv with rfl | rfl <;> simp_all [Cond.eval]

/-- A condition defined on flags related to `NZCV` is the machine's `ConditionHolds`. -/
theorem onVal_holds {c : Cond} {f : Val} {nz : Flags} {b : Bool} (h : FlagsRel f nz)
    (hc : c.onVal f = some b) : c.holds nz = b := by
  unfold Cond.onVal at hc
  split at hc
  · obtain ⟨hn, hz, hcf, hv⟩ := h
    simp only [Cond.holds, eval_some (bitRel_flagBit hn) (bitRel_flagBit hz) (bitRel_flagBit hcf)
      (bitRel_flagBit hv) hc, Option.getD_some]
  · cases hc

/-- The opcodes of a flags block kind: the first tests the kind's condition (`Arm64.taken`), the
second its negation. -/
theorem condBr_spec {k : BlockKind} {asm inv : As} (h : condBr k = some (asm, inv)) :
    ∃ c c', condAs asm = some c ∧ condAs inv = some c' ∧ (∀ a x, Arm64.taken k a x = c.onVal x) ∧
      ∀ f, c'.holds f = !c.holds f := by
  unfold condBr at h
  split at h <;> (try cases h) <;>
    exact ⟨_, _, rfl, rfl, fun _ _ => rfl, fun ⟨n, z, c, v⟩ => by
      cases n <;> cases z <;> cases c <;> cases v <;> rfl⟩

/-- The opcodes of a register test block kind: `Z` branches on zero with `CBZ`, `NZ` with
`CBNZ`; the second opcode is the other one. -/
theorem zeroBr_spec {k : BlockKind} {asm inv : As} (h : zeroBr k = some (asm, inv)) :
    (k = .ARM64Z ∧ asm = .CBZ ∧ inv = .CBNZ) ∨ (k = .ARM64NZ ∧ asm = .CBNZ ∧ inv = .CBZ) := by
  unfold zeroBr at h
  split at h <;> (try cases h)
  · exact .inl ⟨rfl, rfl, rfl⟩
  · exact .inr ⟨rfl, rfl, rfl⟩

end GoFV.Proof.Gen

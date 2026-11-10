import GoFV.Proof.Gen.G53S
import GoFV.Proof.Witness.SepFromW
import GoFV.Proof.Witness.GenG53

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity of the separation of mode `outSP` (issue #553, `docs/plans/proofs3.md` §8 item 7)

A framed activation `Ew` whose `outargs 0` block (`SepFromW.wm`: 16 `poison` bytes) sits at its
`SP` = `4096` (`outSP`), the Go register `SP` holding `SP`'s value: G3's invariant holds in the
mode `true` (`SepAt true`, `SepFromW`) and `SPInv` holds, while the invariant of the mode `false`
(`SepFrom`, every statement before G48b) fails, the saved `LR` word being the block's first word.
`CallOKAt true` holds at a value that is no call. `g53_valueS` applies to G53's witness
(`GenG53.genG53_witness`, mode `false`: `E.outSP = false`).
-/

namespace GoFV.Proof.Witness.OutSP

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Proof.Gen
open GoFV.Proof.Witness.SepFromW (wι wm keys wm_mem)

/-- A context with no values (activation `0`). -/
def lcW : LocCtx := { ctx := default, homes := #[], temps := #[] }

/-- A framed activation with `SP` = `4096`, `outargs 0` there (`outSP`). -/
def Ew : MatchEnv :=
  { lc := lcW, ι := wι, sp := 4096, slot := fun _ => none, g := 0, lr := 0, fp := 0,
    framed := true, pcOf := fun _ _ => 0, outSP := true }

/-- The `runLoc` state: `SP`'s value `⟨outargs 0, 0⟩` in the Go register `SP` (`spReg`, 30), the
others `poison`, the memory `wm`. -/
def sW : LocState :=
  { fr := { regs := #[], args := [], mem0 := wm }, regs := (Array.replicate 30 Val.poison).push (.ptr ⟨.outargs 0, 0⟩),
    flags := .poison, slots := [], mem := .mem wm }

theorem sW_regs {r : Nat} {x : Val} (h : sW.regs[r]? = some x) :
    (r = spReg ∧ x = .ptr ⟨.outargs 0, 0⟩) ∨ x = .poison := by
  by_cases hr : r < 30
  · right
    simp only [sW, Array.getElem?_push, Array.size_replicate] at h
    rw [if_neg (by omega), Array.getElem?_replicate, if_pos hr] at h
    exact (Option.some.inj h).symm
  · left
    simp only [sW, Array.getElem?_push, Array.size_replicate] at h
    by_cases h30 : r = 30
    · subst h30
      exact ⟨rfl, (Option.some.inj (by simpa using h)).symm⟩
    · rw [if_neg h30, Array.getElem?_replicate, if_neg hr] at h
      cases h

theorem sepW_Ew : SepFromW wι (StkAt Ew) wm := by
  intro b al a hb ha y hy i hi he
  obtain ⟨rfl, rfl⟩ := wm_mem hb
  obtain rfl : a = 4096 := (Option.some.inj ha).symm
  rcases hy with ⟨-, -, hlt⟩ | ⟨k, off, hk, -⟩
  · have h4 : (4096 : BitVec 64).toNat = 4096 := rfl
    have hsp : Ew.sp.toNat = 4096 := rfl
    exact ⟨by simp only [Blk.writableFrom]; omega, by simp⟩
  · cases hk

/-- **The invariant of mode `outSP` holds**: G3's invariant in the mode `true` and `SPInv`. -/
theorem inv_true : G3Inv Ew lcW (#[] : KMap) sW true ∧ SPInv Ew sW := by
  refine ⟨⟨⟨fun r v c _ hv hc => ?_, wm, rfl, keys, sepW_Ew⟩, fun k v h => by simp [sW] at h⟩,
    fun _ => ⟨rfl, fun x hx => ?_⟩⟩
  · rcases sW_regs hv with ⟨rfl, -⟩ | rfl
    · simp [KMap.get] at hc
    · trivial
  · rcases sW_regs hx with ⟨-, rfl⟩ | rfl
    · exact ⟨4096, rfl, by simp [Ew]⟩
    · trivial

/-- **The invariant of mode `false` fails**: the saved `LR` word at `SP` is a byte of a live block. -/
theorem not_inv_false : ¬ G3Inv Ew lcW (#[] : KMap) sW := fun h => by
  obtain ⟨mm, hmm, -, hsep⟩ := h.core.mem
  obtain rfl : mm = wm := by simp [sW] at hmm; exact hmm.symm
  exact hsep (.outargs 0) { data := Array.replicate 16 .poison } 4096 (by simp [wm]) rfl 4096
    (Or.inl ⟨rfl, by decide, by decide⟩) ⟨Nat.le_refl _, by simp⟩

/-- `CallOKAt true` (`CallOKS`) at a value that is no static call. -/
theorem callOKS_noCall {H : GoFV.Arm64.Hooks} {g : G2In} {L : GoFV.Arm64.Link}
    {s s' : LocState} {v : Value} {m : GoFV.Arm64.MState} (hop : v.op ≠ .ARM64CALLstatic) :
    CallOKAt true H Ew g L lcW s s' v m :=
  fun h => absurd h hop

section

open GenG53

/-- **`g53_valueS` on G53's witness** (`GenG53.genG53_witness`, `E.outSP = false`): the step of
`v10` relates to the machine with `SPInv` kept. -/
theorem g53S_witness :
    ∃ s1 E1 m1, stepLoc GenG2.env GenG53.lc GenG53.s0 (GenG53.val 10) = .ok s1 ∧
      GenG53.E.Extends E1 ∧ PStar GenG2.H0 GenG53.L GenG53.ps.toList 0 GenG53.m0 m1 ∧
      LocMatch E1 s1 1 5 m1 ∧ SPInv E1 s1 := by
  obtain ⟨hl, hc, -, hav, hsl, hm1, hb, hv10, hi4, hop, ha0, ha1, hn, hk0, hk1, hu4, hr5, hr9,
    hpd, hps, hmv, hrun⟩ := facts
  obtain ⟨s1, hs1, -⟩ := GenG1.okThen_spec hrun
  have hE := g53Env hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64LoweredMove → (val 10).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  have hm0 : 1 ∈ lc0.ctx.f.blocks.toList := by rw [← liveCtx_ctx (lc := lc0)]; exact hm1
  have hb0 : lc0.ctx.f.block? 1 = some blk := by rw [← liveCtx_ctx (lc := lc0)]; exact hb
  have hv0 : lc0.ctx.f.value? 10 = some (val 10) := by rw [← liveCtx_ctx (lc := lc0)]; exact hv10
  have hfalse : E.outSP = false := rfl
  obtain ⟨E1, m1, hx1, -, hp1, hm1', -, hsp1, -⟩ := g53_valueS (H := GenG2.H0) (env := GenG2.env)
    hc hE hm0 hb0 hi4 hv0 (by rw [hop]; rfl) locMatch0 (g53Inv0 hk0 hk1)
    (fun h => absurd (hfalse.symm.trans h) (by decide))
    (fun h => absurd (hfalse.symm.trans h) (by decide))
    (by change UOKL m0 (uL35 lc (uIn35 lc 1) blk 4); rw [hu4]; intro e he; cases he)
    ⟨pre51 hop, pre53 ha0 ha1 hn hr5 hr9 hpd hps hmv⟩
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide))) hs1
  exact ⟨s1, E1, m1, hs1, hx1, hp1, hm1', hsp1⟩

end

end GoFV.Proof.Witness.OutSP

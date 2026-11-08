import GoFV.Proof.Pass.CSELPass
import GoFV.Proof.Witness.LowCong
import GoFV.Proof.Witness.CopyElim
import GoFV.Proof.Witness.Util
import Std.Data.String.ToInt

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: lowered cse on lowered `clamp` with a repeated compare

`clampCse` is lowered `clamp` (`clampL`) with `v25 = ARM64CMP v10 v8` in the entry block `b1`,
the compare `hi - x` that `b2`'s `ARM64LT` control `v14 = ARM64CMP v10 v8` repeats. `lowered cse`
(`loweredCsePass`) merges `v14` into `v25` (`b1` dominates `b2`), so `b2` branches on `v25`. By
kernel evaluation: the input and the output pass `check`, the lowered checker `CSEL.crel`
accepts the merge (`CSEL.frag`), and the input returns `clamp(12, 0, 10) = 10` under `runL`
(the path through `b2`'s `LT`); by `loweredCse_refinesL` the output does too.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof

/-- The values of `clampCse`: `clampL`'s, with `v25 = ARM64CMP v10 v8` in `b1`. -/
def clampCseValues : Array (Option Value) :=
  let t := clampLValues.push none
  let t := t.set! 8 (some (mkVI 8 .ArgIntReg 2 0 (some 7) (pos 2 22 7 0) 4 #[] 1))
  let t := t.set! 10 (some (mkVI 10 .ArgIntReg 2 2 (some 9) (pos 2 22 7 0) 3 #[] 1))
  t.set! 25 (some (mkV 25 .ARM64CMP 29 none (pos 2 22 7 0) 0 #[10, 8] 1))

/-- The blocks of `clampCse`: `v25` listed in the entry block. -/
def clampCseBlocks : Array (Option Block) :=
  clampLBlocks.set! 1
    (some (mkB 1 .ARM64GT (pos 2 22 7 0) #[22] #[⟨3, 0⟩, ⟨2, 0⟩] #[] #[1, 8, 9, 10, 25, 22]))

/-- Lowered `clamp` with a repeated compare. -/
def clampCse : Func :=
  { clampL with vidLast := 25, valueTab := clampCseValues, blockTab := clampCseBlocks }

/-- `check`'s environment. -/
def clampCseCheckEnv : CheckEnv := { clampCheckEnv with tabs := clampLTabs }

/-- What `lowered cse` reads of the environment. -/
def clampCsePassEnv : PassEnv :=
  { clampLPassEnv "lowered cse" with
    config := #[("ptrsize", #[.word "8"])], typs := #[("Mem", 28)] }

/-- `cseCtx clampCsePassEnv`. -/
def clampCseCtx : CSE.Ctx :=
  { tabs := clampLTabs, order := default, isMem := clampLTabs.isMemory 28, ptrSize := 8 }

theorem clampCse_ctx_match (h1 : String → Except String CSE.Ctx)
    (h2 : Option (Array Token) → Except String CSE.Ctx) :
    cseCtx.match_3 (fun _ => Except String CSE.Ctx) (some #[Token.word "8"]) h1 h2 = h1 "8" :=
  rfl

theorem clampCse_ctx : cseCtx clampCsePassEnv = .ok clampCseCtx := by
  have h8 : "8".toInt? = some 8 := by
    rw [show "8" = Nat.repr 8 by decide +kernel]; exact Nat.toInt?_repr 8
  have hm : clampCsePassEnv.typ? "Mem" = some 28 := by decide +kernel
  have hp : clampCsePassEnv.config? "ptrsize" = some #[.word "8"] := rfl
  unfold cseCtx
  rw [hm]
  dsimp only
  rw [hp, clampCse_ctx_match, h8]
  rfl

/-- The kernel-evaluated facts: `clampCse` passes `check`, is lowered, returns
`clamp(12, 0, 10) = 10` under `runL`; cse's result passes `check`, the lowered checker accepts it,
`v14` is replaced by `v25` and `b2` branches on `v25`. -/
theorem clampCse_facts :
    (check clampCseCheckEnv clampCse).toBool = true ∧ clampCse.lowered = true ∧
    returnsInt (runL Env.p1 clampLTabs clampCse (clampArgs 12) {} 3) 10 = true ∧
    ((cseRw clampCseCtx clampCse).toOption.map fun (g, rw) =>
      decide ((check clampCseCheckEnv g).toBool = true ∧ CSEL.crel clampLTabs clampCse g rw = true ∧
        rw[14]? = some (some 25) ∧ (g.block? 2).map (·.controls) = some #[25] ∧
        (clampCse.block? 2).map (·.controls) = some #[14])) = some true := by
  decide +kernel

/-- **`lowered cse` on `clampCse`**: it merges the repeated compare (`b2` branches on `v25`), and
its output returns `clamp(12, 0, 10) = 10` under `runL` (`loweredCse_refinesL`). -/
theorem loweredCse_witness :
    ∃ out, loweredCsePass clampCsePassEnv clampCse = .ok out ∧
      (out.func.block? 2).map (·.controls) = some #[25] ∧
      ∃ fuel m, runL Env.p1 out.tables out.func (clampArgs 12) {} fuel = .returned [.i64 10] m := by
  obtain ⟨h1, -, h3, h4⟩ := clampCse_facts
  obtain ⟨m, hm⟩ := returnsInt_iff.1 h3
  have hf : check clampCseCheckEnv clampCse = .ok () := ok_of_toBool h1
  cases hr : cseRw clampCseCtx clampCse with
  | error e => rw [hr] at h4; cases h4
  | ok p =>
    obtain ⟨g, rw⟩ := p
    rw [hr] at h4
    simp only [Except.toOption, Option.map_some, Option.some.injEq, decide_eq_true_eq] at h4
    obtain ⟨hg, hcr, -, hctl, -⟩ := h4
    have hp : loweredCsePass clampCsePassEnv clampCse =
        .ok { func := g, tables := clampCsePassEnv.tables } := by
      simp only [loweredCsePass, Pass.ofFunc, clampCse_ctx, cse, hr, bind, Except.bind, pure,
        Except.pure, Functor.map, Except.map]
    have hfrag : CSEL.frag clampCsePassEnv clampCse = true := by
      simp only [CSEL.frag, clampCse_ctx, hr]
      exact hcr
    refine ⟨_, hp, hctl, ?_⟩
    obtain ⟨fuel, m', h⟩ := RefinesL.returned_int
      (CSEL.loweredCse_refinesL hp hf (ok_of_toBool hg) hfrag) hm
    exact ⟨fuel, m', h⟩

end GoFV.Proof.Witness

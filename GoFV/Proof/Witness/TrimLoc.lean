import GoFV.Proof.Pass.TrimLoc
import GoFV.Proof.Witness.LoopRotateLoc

/-!
# Non-vacuity witness: `trim` under `runLoc`

The output of `loop rotate` on `loopL` (`GoFV.Proof.Witness.LoopRotateLoc`), blocks
`b1 b3 b2 b5 b4`, is `trim`'s input, as in the pipeline. `b5` (`v34 = ADDconst [7] v30`, `Plain`)
is the only predecessor of `b4`, so `trim` splices the non-empty block `b5` into `b4`: `b2`'s
false edge goes to `b4`, whose values become `v34 v33`; the blocks are `b1 b3 b2 b4`. The input
and output are in `trimRelB` (`trimL_pass_facts`, by kernel evaluation), so `trim_refinesLoc`
applies, and with `loopRotate_refinesLoc` the two-pass tail returns 7 under `runLoc`, as `loopL`
does (`trimLoc_witness`).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof

/-- A pass environment for `loopL` (`trim`). -/
def trimLPassEnv : PassEnv := { loopLPassEnv with passName := "trim" }

/-- `trim` removes `b5` from `loop rotate`'s output, in `trimRelB`. -/
theorem trimL_pass_facts :
    ((loopRotate loopLPassEnv loopL).toOption.bind fun g => (trim g).toOption.map fun h =>
      TrimLoc.trimRelB g h && h.blocks == #[1, 3, 2, 4] &&
        ((h.block? 4).map (·.values)) == some #[34, 33]) = some true := by
  decide +kernel

private theorem refinesLoc_returned_int' {tabs tabs' : Tables} {f f' : Func}
    (h : RefinesLoc tabs' f' tabs f) {env : Env} {args : List Val} {mem m : Mem} {fuel : Nat}
    {w : Width} {x : BitVec w.bits} (hs : runLoc env tabs f args mem fuel = .returned [.int w x] m) :
    ∃ fuel' m', runLoc env tabs' f' args mem fuel' = .returned [.int w x] m' := by
  obtain ⟨fuel', ho⟩ := h env args mem fuel (by rw [hs]; trivial)
  rw [hs] at ho
  refine ⟨fuel', ?_⟩
  generalize runLoc env tabs' f' args mem fuel' = o at ho ⊢
  cases ho with
  | @returned _ _ _ m' hl _ =>
    cases hl with
    | cons h1 t =>
      cases t
      cases h1
      exact ⟨m', rfl⟩

/-- **`trim_refinesLoc` is not vacuous**: after `loop rotate`, `trim` merges `loopL`'s non-empty
block `b5` into its successor, its input and output are in `trimRelB`, and the output returns 7
under `runLoc`, as `loopL` does. -/
theorem trimLoc_witness :
    ∃ out1 out2, loopRotatePass loopLPassEnv loopL = .ok out1 ∧
      trimPass trimLPassEnv out1.func = .ok out2 ∧ TrimLoc.trimRelB out1.func out2.func = true ∧
      out2.func.blocks = #[1, 3, 2, 4] ∧
      ∃ fuel m, runLoc Env.p1 out2.tables out2.func (clampArgs 3) {} fuel = .returned [.i64 7] m := by
  obtain ⟨m, hm⟩ := returnsInt_iff.1 loopL_run
  have hf := trimL_pass_facts
  cases hc : loopRotate loopLPassEnv loopL with
  | error e => rw [hc] at hf; cases hf
  | ok g =>
    rw [hc] at hf
    simp only [Except.toOption, Option.bind_some] at hf
    cases ht : trim g with
    | error e => rw [ht] at hf; cases hf
    | ok h =>
      rw [ht] at hf
      simp only [Option.map_some, Option.some.injEq, Bool.and_eq_true, beq_iff_eq] at hf
      obtain ⟨⟨hrel, hb⟩, -⟩ := hf
      have hp1 : loopRotatePass loopLPassEnv loopL = .ok { func := g, tables := clampLTabs } := by
        simp only [loopRotatePass, Pass.ofFunc, hc]
        rfl
      have hp2 : trimPass trimLPassEnv g = .ok { func := h, tables := clampLTabs } := by
        simp only [trimPass, Pass.ofFunc, ht]
        rfl
      refine ⟨_, _, hp1, hp2, hrel, hb, ?_⟩
      -- each part by `have` first: an argument elaborated against `RefinesLoc ?_ ?_ …` failed a
      -- 4.5 s unification
      have h1 := loopRotate_refinesLoc hp1
      have h2 := trim_refinesLoc hp2 hrel
      have hr := h1.trans h2
      exact refinesLoc_returned_int' hr hm

end GoFV.Proof.Witness

import GoFV.Proof.Pass.DAE
import GoFV.Proof.Witness.StackF0
import GoFV.Proof.Witness.Util

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: dead auto elim on `f0` of `test/stack`

dead auto elim turns `f0`'s `VarDef`s and `Zero [3000]`s of the inlined results `~r0` (frame
temporaries: `PAUTO`s whose address is not taken) into `Copy`. By kernel evaluation: the pass
succeeds, its checker `DAE.arel` accepts the result (so `f0` is in `daeFrag`), input and output
pass `check`, `v8` (`Zero (LocalAddr {~r0}) …`) became `Copy`, and the input returns (no
results). `Env.p1` is frame-safe (its contracts panic on the memory they are given) and the
empty memory holds no pointer, so `dead_auto_elim_refines` gives that the output returns too.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof

/-- The outcome returns no results. -/
def returnsNil : Outcome → Bool
  | .returned [] _ => true
  | _ => false

/-! ## Certificates (kernel evaluation) -/

theorem stackF0_run : returnsNil (run Env.p1 stackF0Tabs stackF0 [] {} 1) = true := by
  decide +kernel

theorem stackF0_pass :
    ((elimDeadAutosPass stackF0PassEnv stackF0).toOption.map fun o =>
      (check stackF0CheckEnv o.func).toBool && (o.func.value? 8).map (·.op) == some .Copy) =
      some true := by
  decide +kernel

theorem stackF0_checks :
    (check stackF0CheckEnv stackF0).toBool = true ∧ daeFrag stackF0PassEnv stackF0 = true ∧
      (stackF0.value? 8).map (·.op) = some .Zero ∧ stackF0Tabs.forgeable 3 = false := by
  decide +kernel

/-! ## The environment and the inputs -/

/-- **`Env.p1` is frame-safe**: its contracts panic on the memory they are given. -/
theorem p1_frameSafe : Env.p1.FrameSafe := by
  intro name c hc U _ args clo m m' _ _ hm hmm
  unfold Env.p1 at hc
  simp only at hc
  split at hc
  all_goals first
    | (cases hc; exact ⟨rfl, trivial, hm, hmm⟩)
    | cases hc

/-- **The defer entry points of a call from activation 0 over `Env.p1` are frame-safe**
(`Env.FrameSafe.atAct`); the environment has them (`deferproc`). -/
theorem p1_atAct_frameSafe : (Env.p1.atAct 0).FrameSafe ∧
    (Env.p1.atAct 0).extern "runtime.deferproc" = some (deferproc 0) :=
  ⟨p1_frameSafe.atAct 0, rfl⟩

theorem stackF0_initAvoids : InitAvoids Env.p1 [] {} := by
  intro a n
  refine ⟨fun _ h => absurd h List.not_mem_nil, fun _ _ h => ?_, rfl, fun _ h => ?_,
    fun _ h => nomatch h⟩
  · simp at h
  · simp [Env.p1] at h

/-- `Env.p1` with a closure context: a pointer to a heap object (a funcval). -/
def p1Clo : Env := { Env.p1 with closure := some (.ptr ⟨.heap 0, 0⟩) }

/-- **The closure conjunct of `InitAvoids` is not vacuous** (#705): a closure context pointing to
a heap object avoids every frame temporary; outside a closure (`Env.p1`) `InitAvoids` is the
condition on the arguments, the memory and the global image (`initAvoids_iff_of_none`). -/
theorem initAvoids_closure_witness :
    InitAvoids p1Clo [] {} ∧
      ∀ a n, (∀ v ∈ ([] : List Val), v.Avoids (· = .temp a n)) ∧
        (({} : Mem)).Avoids (· = .temp a n) ∧ ({} : Mem).find? (.temp a n) = none ∧
        ∀ g ∈ Env.p1.globals, ∀ x ∈ g.2.data.toList, Byte.Avoids (· = .temp a n) x := by
  refine ⟨fun a n => ?_, (initAvoids_iff_of_none rfl).1 stackF0_initAvoids⟩
  refine ⟨fun _ h => absurd h List.not_mem_nil, fun _ _ h => ?_, rfl, fun _ h => ?_,
    fun c h => ?_⟩
  · simp at h
  · simp [p1Clo, Env.p1] at h
  · cases h; intro h; cases h

/-- **`entryFrame_closure` and `entryFrame_of_none` are not vacuous**: the entry frame of `f0`
under `p1Clo` has its closure context, under `Env.p1` none. -/
theorem entryFrame_closure_witness :
    (entryFrame p1Clo (Ctx.make stackF0Tabs stackF0) [] {}).closure = some (.ptr ⟨.heap 0, 0⟩) ∧
      (entryFrame Env.p1 (Ctx.make stackF0Tabs stackF0) [] {}).closure = none :=
  ⟨entryFrame_closure _ _ _ _, by rw [entryFrame_of_none rfl]⟩

/-! ## The witness -/

/-- **Non-vacuity of `dead_auto_elim_refines`**: dead auto elim eliminates `f0`'s `Zero` `v8`
into the frame temporary `~r0` (`a3`, not `Tables.forgeable`), and the output returns, as the
source does. -/
theorem dead_auto_elim_witness :
    ∃ out, elimDeadAutosPass stackF0PassEnv stackF0 = .ok out ∧
      (stackF0.value? 8).map (·.op) = some .Zero ∧ stackF0Tabs.forgeable 3 = false ∧
      (out.func.value? 8).map (·.op) = some .Copy ∧
      ∃ fuel m, run Env.p1 out.tables out.func [] {} fuel = .returned [] m := by
  obtain ⟨hc, hfrag, hz, hfg⟩ := stackF0_checks
  have hp := stackF0_pass
  cases hpe : elimDeadAutosPass stackF0PassEnv stackF0 with
  | error e => rw [hpe] at hp; cases hp
  | ok out =>
    rw [hpe] at hp
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Bool.and_eq_true,
      beq_iff_eq] at hp
    obtain ⟨hcg, hcopy⟩ := hp
    refine ⟨out, rfl, hz, hfg, hcopy, ?_⟩
    have hr := GoFV.Proof.DAE.dead_auto_elim_refines hpe (ok_of_toBool hc) (ok_of_toBool hcg)
      hfrag
    have hrun := stackF0_run
    generalize hs : run Env.p1 stackF0Tabs stackF0 [] {} 1 = o at hrun
    match o, hrun with
    | .returned [] m, _ =>
      obtain ⟨fuel', ho⟩ := hr Env.p1 [] {} ⟨p1_frameSafe, stackF0_initAvoids⟩ 1
        (by rw [show stackF0PassEnv.tables = stackF0Tabs from rfl, hs]; trivial)
      rw [show stackF0PassEnv.tables = stackF0Tabs from rfl, hs] at ho
      refine ⟨fuel', ?_⟩
      generalize run Env.p1 out.tables out.func [] {} fuel' = o' at ho ⊢
      cases ho with
      | @returned _ rs' _ m' hl _ =>
        cases hl
        exact ⟨m', rfl⟩

end GoFV.Proof.Witness

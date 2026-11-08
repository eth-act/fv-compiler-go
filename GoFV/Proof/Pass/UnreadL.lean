import GoFV.Proof.Pass.UnreadLSim
import GoFV.Proof.CheckFacts
import GoFV.Proof.DomCert

variable [GoFV.SSA.Sem.Addrs]

/-!
# elim unread autos refines its input under `runL`

`elim unread autos` turns symbol stores (`MOV*store`/`FMOV*store`/`STP*`) and `VarDef`s of
frame variables nothing reads into `Copy mem`. On an input in `unreadLFrag` (the pass fails,
changes nothing, or the checker `UnreadL.urel` accepts its result: every eliminated variable is a
frame temporary `Blk.temp` no kept value names, and the kept values with memory- or
tuple-shaped operands have ops the proof covers), the result is related to the input by `URel`
(`urel_sound`), and `URel` gives refinement under `runL` for environments whose contracts are
frame-safe and inputs holding no pointer into a frame temporary (`refinesL_of_urel`): the
precondition of Phase 1's dead auto elim (`DAE.dead_auto_elim_refines`).
-/

namespace GoFV.Proof.UnreadL

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.SSA.DomCert Dom

/-- **elim unread autos refines its input under `runL`** (on inputs in `unreadLFrag`, for
frame-safe environments and inputs that hold no pointer into a frame temporary). -/
theorem elimUnreadAutos_refinesL {penv : PassEnv} {f : Func} {out : PassOut}
    {ce ce' : CheckEnv} (h : elimUnreadAutosPass penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) (hfrag : unreadLFrag penv f = true) :
    RefinesLFrom (fun env args mem => env.FrameSafe ∧ InitAvoids env args mem)
      out.tables out.func penv.tables f := by
  unfold unreadLFrag at hfrag
  rw [h] at hfrag
  have ht : out.tables = penv.tables := by
    simp only [elimUnreadAutosPass, Pass.ofFunc, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · cases h; rfl
  rw [ht]
  simp only at hfrag
  simp only [Bool.or_eq_true, beq_iff_eq] at hfrag
  rcases hfrag with heq | hu
  · rw [heq]; exact RefinesLFrom.refl _ _ _
  · exact refinesL_of_urel (check_wf hf) (certOK_of_check (check_domCert hf)) (urel_sound hu)

end GoFV.Proof.UnreadL

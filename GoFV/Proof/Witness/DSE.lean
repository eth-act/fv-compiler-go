import GoFV.Proof.Pass.DSE
import GoFV.Proof.Witness.DSECert

/-!
# Non-vacuity witness: dse on `f10` of `test/initialize`

dse turns `f10`'s `v8 = Zero [16] (LocalAddr {~r0}) v7`, whose 16 bytes the two `Store`s of `s`
overwrite, into `Copy v7` (`f10Out`). By kernel evaluation: dse's result is `f10Out`, its checker
`DSE.drel` accepts it (so `f10` is in `dseFrag`), input and output pass `check`, and the input
returns `[2]*S{s, s}` (the 16 bytes of `s` twice). `dse_refines` then gives that the output
returns the same.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof

/-- The outcome returns the one value `.blob bs`. -/
def returnsBlob : Outcome → List Byte → Bool
  | .returned [.blob bs] _, v => bs == v
  | _, _ => false

theorem returnsBlob_iff {o : Outcome} {v : List Byte} :
    returnsBlob o v = true ↔ ∃ m, o = .returned [.blob v] m := by
  constructor
  · intro h
    match o, h with
    | .returned [.blob bs] m, h =>
      simp only [returnsBlob, beq_iff_eq] at h
      exact ⟨m, by rw [h]⟩
  · rintro ⟨m, rfl⟩
    simp [returnsBlob]

/-! ## The run (kernel evaluation) -/

/-- The input returns `[2]*S{s, s}` (one block entry). -/
theorem f10_run :
    returnsBlob (run Env.p1 f10Tabs f10 f10Args {} 1)
      (ptrBytes ⟨.heap 0, 0⟩ ++ ptrBytes ⟨.heap 0, 0⟩).toList = true := by
  decide +kernel

/-! ## The pass -/

theorem ok_of_toBool' {e : Except String Unit} (h : e.toBool = true) : e = .ok () := by
  revert h; cases e <;> simp [Except.toBool]

theorem f10_dse_ok : dse f10Tabs 31 f10 = .ok f10Out := by
  have h := f10_dse
  generalize dse f10Tabs 31 f10 = r at h ⊢
  cases r <;> simp_all [Except.toOption]

theorem f10_mem : f10PassEnv.typ? "Mem" = some 31 := by decide +kernel

theorem f10_dsePass : dsePass f10PassEnv f10 = .ok { func := f10Out, tables := f10Tabs } := by
  simp only [dsePass, Pass.ofFunc, f10_mem, bind, Except.bind, pure, Except.pure]
  rw [show f10PassEnv.tables = f10Tabs from rfl, f10_dse_ok]

theorem f10_dseFrag : dseFrag f10PassEnv f10 = true := by
  simp only [dseFrag, f10_mem]
  rw [show f10PassEnv.tables = f10Tabs from rfl, f10_dse_ok]
  exact f10_checks.2.2

/-- A source run returning values without poison gives a target run returning them, with the
same memory. -/
theorem Refines.returned_noPoison {tabs tabs' : Tables} {f f' : Func} (h : Refines tabs' f' tabs f)
    {env : Env} {args : List Val} {mem m : Mem} {fuel : Nat} {rs : List Val}
    (hp : Val.anyPoison rs = false) (hs : run env tabs f args mem fuel = .returned rs m) :
    ∃ fuel', run env tabs' f' args mem fuel' = .returned rs m := by
  obtain ⟨fuel', ho⟩ := h env args mem fuel (by rw [hs]; trivial)
  rw [hs] at ho
  refine ⟨fuel', ?_⟩
  generalize run env tabs' f' args mem fuel' = o at ho ⊢
  cases ho with
  | returned hl => rw [← GoFV.Proof.Sem.RefinesList.eq_of_noPoison hl hp]

/-! ## The witness -/

/-- **Non-vacuity of `dse_refines`**: dse eliminates `f10`'s `Zero` `v8`, and the output
returns the source's result `[2]*S{s, s}`. -/
theorem dse_witness :
    ∃ out, dsePass f10PassEnv f10 = .ok out ∧ (out.func.value? 8).map (·.op) = some .Copy ∧
      ∃ fuel m, run Env.p1 out.tables out.func f10Args {} fuel =
        .returned [.blob (ptrBytes ⟨.heap 0, 0⟩ ++ ptrBytes ⟨.heap 0, 0⟩).toList] m := by
  obtain ⟨h1, h2, -⟩ := f10_checks
  obtain ⟨m, hm⟩ := returnsBlob_iff.1 f10_run
  refine ⟨_, f10_dsePass, f10_elim.2, ?_⟩
  obtain ⟨fuel, h⟩ := Refines.returned_noPoison
    (GoFV.Proof.DSE.dse_refines f10_dsePass (ok_of_toBool' h1) (ok_of_toBool' h2) f10_dseFrag)
    (by decide +kernel) hm
  exact ⟨fuel, m, h⟩

end GoFV.Proof.Witness

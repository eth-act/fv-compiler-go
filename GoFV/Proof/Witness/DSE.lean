import GoFV.Proof.Pass.DSE
import GoFV.Proof.Witness.DSECert
import GoFV.Proof.Witness.Util

/-!
# Non-vacuity witness: dse on `f10` of `test/initialize`

dse turns `f10`'s `v8 = Zero [16] (LocalAddr {~r0}) v7`, whose 16 bytes the two `Store`s of `s`
overwrite, into `Copy v7` (`f10Out`). By kernel evaluation: dse's result is `f10Out`, its checker
`DSE.drel` accepts it (so `f10` is in `dseFrag`), input and output pass `check`, and the input
returns `[2]*S{s, s}` (the 16 bytes of `s` twice: `s` is a heap pointer, stored as its address
word, `Ptr.word`). `dse_refines` then gives that the output returns the same.
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

/-- The input returns `[2]*S{s, s}` (one block entry, address `2^40`). -/
theorem f10_run :
    returnsBlob (run Env.p1 f10Tabs f10 f10Args {} 1)
      (intBytes 8 (2 ^ 40) ++ intBytes 8 (2 ^ 40)).toList = true := by
  decide +kernel

/-! ## The pass -/

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

/-- Bytes without `poison` are refined only by themselves. -/
theorem BytesRefine.eq_of_noPoison : {as bs : List Byte} → BytesRefine as bs →
    as.contains .poison = false → as = bs
  | _, _, .nil, _ => rfl
  | _, _, .cons (.poison _) _, hp => by simp at hp
  | _, _, .cons (.refl _) t, hp => by
    rw [List.contains_cons, Bool.or_eq_false_iff] at hp
    rw [BytesRefine.eq_of_noPoison t hp.2]

/-- A source run returning one blob without `poison` bytes gives a target run returning it. -/
theorem Refines.returned_blob {tabs tabs' : Tables} {f f' : Func} (h : Refines tabs' f' tabs f)
    {env : Env} {args : List Val} {mem m : Mem} {fuel : Nat} {bs : List Byte}
    (hp : bs.contains .poison = false) (hs : run env tabs f args mem fuel = .returned [.blob bs] m) :
    ∃ fuel' m', run env tabs' f' args mem fuel' = .returned [.blob bs] m' := by
  obtain ⟨fuel', ho⟩ := h env args mem fuel (by rw [hs]; trivial)
  rw [hs] at ho
  refine ⟨fuel', ?_⟩
  generalize run env tabs' f' args mem fuel' = o at ho ⊢
  cases ho with
  | @returned _ _ _ m' hl _ =>
    cases hl with
    | cons h1 t =>
      cases t
      cases h1 with
      | blob hb => exact ⟨m', by rw [BytesRefine.eq_of_noPoison hb hp]⟩

/-! ## The witness -/

/-- **Non-vacuity of `dse_refines`**: dse eliminates `f10`'s `Zero` `v8`, and the output
returns the source's result `[2]*S{s, s}`. -/
theorem dse_witness :
    ∃ out, dsePass f10PassEnv f10 = .ok out ∧ (out.func.value? 8).map (·.op) = some .Copy ∧
      ∃ fuel m, run Env.p1 out.tables out.func f10Args {} fuel =
        .returned [.blob (intBytes 8 (2 ^ 40) ++ intBytes 8 (2 ^ 40)).toList] m := by
  obtain ⟨h1, h2, -⟩ := f10_checks
  obtain ⟨m, hm⟩ := returnsBlob_iff.1 f10_run
  refine ⟨_, f10_dsePass, f10_elim.2, ?_⟩
  exact Refines.returned_blob
    (GoFV.Proof.DSE.dse_refines f10_dsePass (ok_of_toBool h1) (ok_of_toBool h2) f10_dseFrag)
    (by decide +kernel) hm

end GoFV.Proof.Witness

import GoFV.Proof.Pass.CSE
import GoFV.SSA.Check
import GoFV.Proof.Witness.DecodedLenCse
import Std.Data.String.ToInt

/-!
# Non-vacuity witness: generic cse on `decodedLen`

generic cse merges `decodedLen`'s second `n/4` (`v12 = Div64 v7 v13`) into the first
(`v14 = Div64 v7 v13`, same block), so `v23 = Mul64 v12 v13` becomes `Mul64 v13 v14` (its
arguments swapped into class order), as stock Go does. By kernel evaluation: cse succeeds, its
checker `CSE.crel` accepts the result (also with `strict`, so the input is in `cseFrag`), input
and output pass `check`, and the output returns `decodedLen(10, NoPadding) = 7`, as the source
does (`decodedLenCse_run`). `cseCtx` parses the `ptrsize` config with `String.toInt?`, which
the kernel cannot evaluate; `dlCse_ctx` proves its result with `Nat.toInt?_repr` instead.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt

/-- The `typeorder` line of the export file (no `typecmp` exceptions). -/
def dlOrder : TypeOrder := TypeOrder.ofGroups
  #[#[5], #[9], #[6], #[10], #[3, 7], #[11], #[8], #[12], #[2], #[15], #[16], #[26], #[27], #[13],
    #[14], #[4], #[18], #[19, 34], #[20], #[21], #[22], #[23], #[24], #[25], #[1], #[17], #[28],
    #[29], #[31], #[30], #[32], #[33], #[35]]

/-- `check`'s environment: the `Config.Types` of the export (as `GoFV.Proof.Witness.ZCSE`). -/
def dlCseCheckEnv : CheckEnv :=
  { tabs := dlTabs, typs := #[("Int", 2), ("Mem", 29), ("Bool", 4)] }

/-- What `generic cse` reads of the export's environment. -/
def dlCsePassEnv : PassEnv where
  passName := "generic cse"
  pkg := GoStr.ofString "encoding/base64"
  funcName := GoStr.ofString "decodedLen"
  abi := 1
  nosplit := false
  pgohot := false
  config := #[("ptrsize", #[.word "8"])]
  typs := #[("Int", 2), ("Mem", 29), ("Bool", 4)]
  typeOrder := dlOrder
  tables := dlTabs

/-- `cseCtx dlCsePassEnv`. -/
def dlCseCtx : CSE.Ctx :=
  { tabs := dlTabs, order := dlOrder, isMem := dlTabs.isMemory 29, ptrSize := 8 }

/-- `cseCtx`'s `ptrsize` match on this environment's literal (the match has no equation
lemmas: Lean cannot generate them for its array pattern). -/
theorem dlCse_ctx_match (h1 : String → Except String CSE.Ctx)
    (h2 : Option (Array Token) → Except String CSE.Ctx) :
    cseCtx.match_3 (fun _ => Except String CSE.Ctx) (some #[Token.word "8"]) h1 h2 = h1 "8" :=
  rfl

theorem dlCse_ctx : cseCtx dlCsePassEnv = .ok dlCseCtx := by
  have h8 : "8".toInt? = some 8 := by
    rw [show "8" = Nat.repr 8 by decide +kernel]; exact Nat.toInt?_repr 8
  have hm : dlCsePassEnv.typ? "Mem" = some 29 := by decide +kernel
  have hp : dlCsePassEnv.config? "ptrsize" = some #[.word "8"] := rfl
  unfold cseCtx
  rw [hm]
  dsimp only
  rw [hp, dlCse_ctx_match, h8]
  rfl

/-! ## Leaf certificates (kernel evaluation) -/

theorem decodedLenCse_check : (check dlCseCheckEnv decodedLenCse).toBool = true := by
  decide +kernel

/-- cse's result and substitution are the transcribed section 10 (`decodedLenCseOut`). -/
theorem decodedLenCse_cseRw : cseRw dlCseCtx decodedLenCse = .ok (decodedLenCseOut, dlCseRw) := by
  have h : (cseRw dlCseCtx decodedLenCse).toOption = some (decodedLenCseOut, dlCseRw) := by
    decide +kernel
  generalize cseRw dlCseCtx decodedLenCse = r at h ⊢
  cases r <;> simp_all [Except.toOption]

theorem decodedLenCseOut_check : (check dlCseCheckEnv decodedLenCseOut).toBool = true := by
  decide +kernel

/-- The checker accepts cse's result, also strictly (one certificate: the two runs share most
of their evaluation). -/
theorem decodedLenCse_crel_both :
    (CSE.crel dlTabs false decodedLenCse decodedLenCseOut dlCseRw &&
      CSE.crel dlTabs true decodedLenCse decodedLenCseOut dlCseRw) = true := by
  decide +kernel

theorem decodedLenCse_crel : CSE.crel dlTabs false decodedLenCse decodedLenCseOut dlCseRw = true :=
  (Bool.and_eq_true _ _ ▸ decodedLenCse_crel_both).1

theorem decodedLenCse_crel_strict :
    CSE.crel dlTabs true decodedLenCse decodedLenCseOut dlCseRw = true :=
  (Bool.and_eq_true _ _ ▸ decodedLenCse_crel_both).2

/-- The merge: `v12` is replaced by `v14`, and `v23`, which read `v12`, now reads `v14`. -/
theorem decodedLenCse_merge :
    dlCseRw[12]? = some (some 14) ∧
      (decodedLenCse.value? 23).map (·.args) = some #[12, 13] ∧
      (decodedLenCseOut.value? 23).map (·.args) = some #[13, 14] := by
  decide +kernel

/-! ## The pass -/

theorem ok_of_toBool {e : Except String Unit} (h : e.toBool = true) : e = .ok () := by
  revert h; cases e <;> simp [Except.toBool]

/-- `csePass` keeps a result its checker accepts (with `cseRw` abstract, so the kernel never
evaluates it here). -/
theorem csePass_of_crel {env : PassEnv} {f g : Func} {c : CSE.Ctx} {rw : Array (Option ID)}
    (hc : cseCtx env = .ok c) (hrw : cseRw c f = .ok (g, rw))
    (hcr : CSE.crel c.tabs false f g rw = true) :
    csePass env f = .ok { func := g, tables := env.tables } := by
  simp only [csePass, Pass.ofFunc, cseChecked, hc, hrw, hcr, bind, Except.bind, pure, Except.pure,
    ite_true]

/-- An input whose cse result passes the strict checker is in the fragment. -/
theorem cseFrag_of_crel {env : PassEnv} {f g : Func} {c : CSE.Ctx} {rw : Array (Option ID)}
    (hc : cseCtx env = .ok c) (hrw : cseRw c f = .ok (g, rw))
    (hs : CSE.crel c.tabs true f g rw = true) : cseFrag env f = true := by
  simp only [cseFrag, hc, CSE.inFrag, hrw, hs, Bool.or_true]

theorem decodedLenCse_csePass :
    csePass dlCsePassEnv decodedLenCse = .ok { func := decodedLenCseOut, tables := dlTabs } :=
  csePass_of_crel dlCse_ctx decodedLenCse_cseRw decodedLenCse_crel

theorem decodedLenCse_cseFrag : cseFrag dlCsePassEnv decodedLenCse = true :=
  cseFrag_of_crel dlCse_ctx decodedLenCse_cseRw decodedLenCse_crel_strict

/-- Everything `cse_refines` needs, the visible merge, and the output's run, for `csePass` on
`decodedLen`. -/
theorem decodedLenCse_pass :
    ∃ out, csePass dlCsePassEnv decodedLenCse = .ok out ∧
      check dlCseCheckEnv decodedLenCse = .ok () ∧ check dlCseCheckEnv out.func = .ok () ∧
      cseFrag dlCsePassEnv decodedLenCse = true ∧
      (out.func.value? 23).map (·.args) = some #[13, 14] ∧
      returnsInt (run Env.p1 out.tables out.func dlArgs {} 2) 7 = true :=
  ⟨_, decodedLenCse_csePass, ok_of_toBool decodedLenCse_check,
    ok_of_toBool decodedLenCseOut_check, decodedLenCse_cseFrag, decodedLenCse_merge.2.2,
    decodedLenCseOut_run⟩

/-! ## The witness -/

/-- **Non-vacuity of `cse_refines`**: cse merges `decodedLen`'s two `Div64 v7 v13` (`v23`
becomes `Mul64 v13 v14`), and the validated output returns the source's result. -/
theorem cse_witness :
    ∃ out, csePass dlCsePassEnv decodedLenCse = .ok out ∧
      (out.func.value? 23).map (·.args) = some #[13, 14] ∧
      ∃ fuel m, run Env.p1 out.tables out.func dlArgs {} fuel = .returned [.i64 7] m := by
  obtain ⟨m, hm⟩ := returnsInt_iff.1 decodedLenCse_run
  refine ⟨_, decodedLenCse_csePass, decodedLenCse_merge.2.2, ?_⟩
  obtain ⟨fuel, m', h⟩ := Refines.returned_int
    (GoFV.Proof.CSE.cse_refines decodedLenCse_csePass (ok_of_toBool decodedLenCse_check)
      (ok_of_toBool decodedLenCseOut_check) decodedLenCse_cseFrag) hm
  exact ⟨fuel, m', h⟩

end GoFV.Proof.Witness

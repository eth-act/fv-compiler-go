import GoFV.Proof.Witness.LowerNarrowArgs

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower`'s `AndB`: `andb` (hand-written, issue #385)

A function of the global `g` of `LowerNarrowArgs` (`narFunc`, `narMem`: `g` holds
`0x1_0000_019a`):

* `andb() int { x := int64(g); return int(b2i(5 < x && x < 1<<33)) }` with the `&&` branch-free
  (`AndB`, as Go's `phiopt` makes it): `lower` gives
  `v6 = GreaterThan v15` and `v8 = LessThan v14` (the compares against 5 and `2^33`, `v15`/`v14`
  `CMPconst` of `v4`) and `v9 = AND v6 v8` (`(AndB ...) => (AND ...)`, `ARM64.rules:133`), the
  lowered `AND` at the `bool` shape (`Arm64.and`, `docs/plans/semantics2.md` §3).

By `lower_refines` every returning or panicking `run` of it is, up to refinement, a `runL` of the
result; it returns 1.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- `andb`. -/
def andbFunc : Func := narFunc 12 12 #[none,
  some (mkV 1 .InitMem 28 none p0 2 #[] 1),
  some (mkV 2 .SB 4 none p0 1 #[] 1),
  some (mkV 3 .Addr 3 (some 4) p0 1 #[2] 1),
  some (mkV 4 .Load 2 none p0 2 #[3, 1] 1),
  some (mkVI 5 .Const64 2 5 none p0 1 #[] 1),
  some (mkV 6 .Less64 7 none p0 1 #[5, 4] 1),
  some (mkVI 7 .Const64 2 8589934592 none p0 1 #[] 1),
  some (mkV 8 .Less64 7 none p0 1 #[4, 7] 1),
  some (mkV 9 .AndB 7 none p0 1 #[6, 8] 1),
  some (mkV 10 .CvtBoolToUint8 6 none p0 1 #[9] 1),
  some (mkV 11 .ZeroExt8to64 2 none p0 1 #[10] 1),
  some (mkV 12 .MakeResult 33 none p0 1 #[11, 1] 1)]

theorem andb_generic : andbFunc.lowered = false := by decide +kernel

/-- `andb` has no fused multiply-add shape: its contraction is itself. -/
theorem andb_noFma : GoFV.Opt.FmaContract.contractAll andbFunc = andbFunc := by decide +kernel

/-- The values of `andb`'s lowered result: the two conditions and their `AND`. -/
def andbShow (f : Func) : List (Option (Op × Int64 × Array ID)) :=
  [6, 8, 9].map fun i => (f.value? i).map fun v => (v.op, v.auxInt, v.args)

set_option synthInstance.maxSize 2048 in
/-- By kernel evaluation: the checked lower keeps a lowered result of `andb` whose `v6`, `v8`, `v9`
are `GreaterThan v15`, `LessThan v14` and `AND v6 v8`, and `andb` returns 1 under `run` of the
input and `runL` of the result. -/
theorem andb_checks :
    (lowerChecked (narPassEnv "andb") andbFunc).toOption.map (fun o =>
      (andbShow o.func, o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] narMem 1) 1)) =
      some ([some (.ARM64GreaterThan, 0, #[15]), some (.ARM64LessThan, 0, #[14]),
        some (.ARM64AND, 0, #[6, 8])], true, true) ∧
    returnsInt (run Env.p1 narTabs andbFunc [] narMem 1) 1 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on `AndB`: on `andb`, the
checked lower's `v9` is `AND v6 v8` (`ARM64.rules:133`, `GoFV.Proof.Low.Rules.r_ARM64_133_sound`),
and every returning or panicking `run` of `andb` is, up to refinement, a `runL` of the result. -/
theorem andb_lower :
    ∃ out, lowerChecked (narPassEnv "andb") andbFunc = .ok out ∧ out.func.lowered = true ∧
      andbShow out.func = [some (.ARM64GreaterThan, 0, #[15]), some (.ARM64LessThan, 0, #[14]),
        some (.ARM64AND, 0, #[6, 8])] ∧
      (∃ f', GoFV.Proof.Low.Contract andbFunc f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func (narPassEnv "andb").tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env narTabs andbFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env narTabs andbFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := andb_checks
  cases hc : lowerChecked (narPassEnv "andb") andbFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨hv, hl, -⟩ := h1
    exact ⟨out, rfl, hl, hv, GoFV.Proof.Low.lower_refines hc andb_generic,
      fun env hE args mem fuel hd => GoFV.Proof.Low.lower_refines_run hc andb_generic andb_noFma hE hd⟩

end GoFV.Proof.Witness

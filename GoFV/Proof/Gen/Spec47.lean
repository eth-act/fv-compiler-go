import GoFV.Gen.Check47
import GoFV.Proof.Gen.Spec46

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `checkG47` accepted (`GoFV/Gen/Check47.lean`)

`VK47`: G46's kinds (`VK46`, through `vkind46`) and G47's static calls (`callKind47_spec`),
interface and closure calls (`icallKind47_spec`) and selects in an `F` register
(`selKind47_spec`); on `InitMem`, `vkind47` is `vkind46` (`vkind47_initMem`), and so on an op
that is neither a call nor `SelectN` (`vkind47_eq46`). `checkG47L_spec` is
`checkG46L_spec` with `vkind47`, and `checkG47_spec` splits off `refsLive`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind47` accepted of a value that is not an entry value, and what it emits. -/
inductive VK47 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G46. -/
  | g46 {kd : VKind2} : VK46 lc g v kd → VK47 lc g v kd
  /-- A static call as `VK15.call`, with ABI registers in `R0`–`R15` or `F0`–`F15` and the
  arguments in `F` registers at float shapes. -/
  | call {name : GoStr} {abi : Nat} {cabi : CallABI} {ins outs : List Nat} {mem : ID} :
      v.op = .ARM64CALLstatic → callOf? lc.ctx.tabs v.aux = some (name, abi, cabi) →
      callRegsZ lc.ctx.tabs cabi = .ok (ins, outs) → outs.Nodup → v.args.back? = some mem →
      memTy (lc.ty mem) = true → lc.home mem = none →
      (∀ r ∈ ins ++ outs, r < 16 ∨ (31 ≤ r ∧ r < 47)) →
      v.args.toList.dropLast.length = ins.length →
      (∀ a r, (a, r) ∈ v.args.toList.dropLast.zip ins → lc.home a = some (.reg r)) →
      (∀ a r, (a, r) ∈ v.args.toList.dropLast.zip ins → 31 ≤ r → fTy (lc.ty a) = true) →
      (lc.home v.id = some (.results (outs.map some).toArray) ∨ (lc.home v.id = none ∧ outs = [])) →
      callTy outs.length (lc.ty v.id) = true → VK47 lc g v (.prog (callPat g name abi))
  /-- An interface or closure call as `VK10.icall`, with ABI registers in `R0`–`R15` or
  `F0`–`F15` and the arguments in `F` registers at float shapes. -/
  | icall {k : Nat} {cabi : CallABI} {ins outs : List Nat} {mem a0 rc : Nat} {o : Int} :
      icallLead v.op = some k → callABI? lc.ctx.tabs v.aux = some cabi →
      callRegs cabi = .ok (ins, outs) → outs.Nodup → k < v.args.size → v.args.back? = some mem →
      memTy (lc.ty mem) = true → lc.home mem = none →
      (∀ r ∈ ins ++ outs, r < 16 ∨ (31 ≤ r ∧ r < 47)) →
      v.args[0]? = some a0 → lc.home a0 = some (.reg rc) → rc < 26 →
      (cls (lc.ty a0)).isSome = true → objOf? rc = some o →
      (k = 2 → ∃ a1, v.args[1]? = some a1 ∧ lc.home a1 = some (.reg ctxReg) ∧
        (cls (lc.ty a1)).isSome = true) →
      (v.args.toList.drop k).dropLast.length = ins.length →
      (∀ a r, (a, r) ∈ (v.args.toList.drop k).dropLast.zip ins → lc.home a = some (.reg r)) →
      (∀ a r, (a, r) ∈ (v.args.toList.drop k).dropLast.zip ins → 31 ≤ r →
        fTy (lc.ty a) = true) →
      (lc.home v.id = some (.results (outs.map some).toArray) ∨ (lc.home v.id = none ∧ outs = [])) →
      callTy outs.length (lc.ty v.id) = true → VK47 lc g v (.prog (icallPat o))
  /-- Result `i` of a static, interface or closure call, homed in the call's result register `i`,
  an `F` register, at a float shape. -/
  | selF {c : ID} {u : Value} {ts : List Ty} {r : Nat} {rs : Array (Option Nat)} {t : Ty} :
      v.op = .SelectN → v.args.size = 1 → v.args[0]? = some c → lc.ctx.f.value? c = some u →
      (u.op = .ARM64CALLstatic ∨ (icallLead u.op).isSome = true) → lc.ty c = .tuple ts →
      callTy (ts.length - 1) (.tuple ts) = true → 0 ≤ v.auxInt.toInt →
      lc.home v.id = some (.reg r) → 31 ≤ r → r < 47 →
      v.auxInt.toInt.toNat + 1 < ts.length → ts[v.auxInt.toInt.toNat]? = some t →
      cls t = cls (lc.ty v.id) → fTy t = true → fTy (lc.ty v.id) = true →
      lc.home c = some (.results rs) → rs[v.auxInt.toInt.toNat]? = some (some r) →
      VK47 lc g v .none

section Helpers

variable {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}

theorem abiRegOK_spec {r : Nat} (h : abiRegOK r = true) : r < 16 ∨ (31 ≤ r ∧ r < 47) := by
  simpa [abiRegOK] using h

theorem fArgsOK_spec {as : List ID} {rs : List Nat} (h : fArgsOK lc as rs = true) :
    ∀ a r, (a, r) ∈ as.zip rs → 31 ≤ r → fTy (lc.ty a) = true := by
  intro a r har hr
  have := (List.all_eq_true.mp h) (a, r) har
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  rcases this with h1 | h1
  · omega
  · exact h1

private theorem nb {b : Bool} (h : ¬ ((!b) = true)) : b = true := by
  cases b <;> simp_all

/-- What `callKind47` accepted: `VK47.call`. -/
theorem callKind47_spec (hop : v.op = .ARM64CALLstatic) (h : callKind47 lc g v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK47 lc g v kd := by
  unfold callKind47 at h
  by_cases ht : (lc.temps[v.id]?).join = none
  · simp only [ht, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
    refine ⟨ht, ?_⟩
    split at h
    next name abi cabi hcall =>
      obtain ⟨⟨ins, outs⟩, hcr, h⟩ := ex_bind_eq_ok h
      obtain ⟨hnd, h⟩ := ex_guard h
      simp only [decide_eq_true_eq] at hnd
      split at h
      next m hm =>
        obtain ⟨hmem, h⟩ := ex_guard h
        obtain ⟨h16, h⟩ := ex_guard h
        obtain ⟨hlen, h⟩ := ex_guard h
        obtain ⟨hargs, h⟩ := ex_guard h
        obtain ⟨hfa, h⟩ := ex_guard h
        simp only [Bool.and_eq_true, beq_iff_eq] at hmem hlen
        have hab : ∀ r ∈ ins ++ outs, r < 16 ∨ (31 ≤ r ∧ r < 47) :=
          fun r hr => abiRegOK_spec ((List.all_eq_true.mp h16) r hr)
        have hfa' := fArgsOK_spec hfa
        have hargs' : ∀ a r, (a, r) ∈ v.args.toList.dropLast.zip ins →
            lc.home a = some (.reg r) := by
          intro a r har
          have := (List.all_eq_true.mp hargs) (a, r) har
          simpa only [beq_iff_eq, regHome?_eq] using this
        have hres : lc.home v.id = some (.results (outs.map some).toArray) ∨
            (lc.home v.id = none ∧ outs = []) := by
          split at h
          next rs hrs =>
            obtain ⟨hc, -⟩ := ex_guard h
            simp only [beq_iff_eq] at hc
            left
            rw [hrs, ← hc]
          next hn =>
            obtain ⟨hc, -⟩ := ex_guard h
            exact Or.inr ⟨hn, List.isEmpty_iff.mp hc⟩
          next => simp [ex_throw, ex_bind_error] at h
        split at h
        all_goals first
          | (simp [ex_throw, ex_bind_error] at h; done)
          | (obtain ⟨-, h⟩ := ex_guard h
             obtain ⟨hct, h⟩ := ex_guard h
             obtain ⟨-, h⟩ := ex_guard h
             cases h)
        all_goals exact VK47.call hop hcall hcr hnd hm hmem.1 hmem.2 hab hlen hargs' hfa' hres hct
      next => simp [ex_throw] at h
    next => simp [ex_throw] at h
  · simp [ht, ex_throw, ex_bind_error] at h

/-- What `icallErr47` accepted. -/
theorem icallErr47_spec {k : Nat} {ins outs : List Nat} {a0 rc : Nat}
    (h : icallErr47 lc v k ins outs a0 rc = none) :
    outs.Nodup ∧ k < v.args.size ∧ memLast lc v = true ∧
      (∀ r ∈ ins ++ outs, r < 16 ∨ (31 ≤ r ∧ r < 47)) ∧
      rc < 26 ∧ (cls (lc.ty a0)).isSome = true ∧ (k = 2 → ctxOK lc v = true) ∧
      (v.args.toList.drop k).dropLast.length = ins.length ∧
      (∀ a r, (a, r) ∈ (v.args.toList.drop k).dropLast.zip ins → lc.home a = some (.reg r)) ∧
      (∀ a r, (a, r) ∈ (v.args.toList.drop k).dropLast.zip ins → 31 ≤ r →
        fTy (lc.ty a) = true) ∧
      resHome lc v outs = true ∧ callTy outs.length (lc.ty v.id) = true := by
  have hr : icallRegErr47 lc v k ins outs a0 rc = none ∧ icallArgErr47 lc v k ins outs = none := by
    unfold icallErr47 at h
    cases h1 : icallRegErr47 lc v k ins outs a0 rc <;> simp_all [Option.or]
  obtain ⟨hreg, harg⟩ := hr
  unfold icallRegErr47 at hreg
  split at hreg
  · cases hreg
  rename_i h1
  split at hreg
  · cases hreg
  rename_i h2
  split at hreg
  · cases hreg
  rename_i h3
  split at hreg
  · cases hreg
  rename_i h4
  split at hreg
  · cases hreg
  rename_i h5
  unfold icallArgErr47 at harg
  simp only at harg
  split at harg
  · cases harg
  rename_i h6
  split at harg
  · cases harg
  rename_i h7
  split at harg
  · cases harg
  rename_i h8
  split at harg
  · cases harg
  rename_i h9
  split at harg
  · cases harg
  rename_i h10
  have h1 := nb h1
  have h2 := nb h2
  have h3 := nb h3
  have h4 := nb h4
  have h5 := nb h5
  have h6 := nb h6
  have h7 := nb h7
  have h8 := nb h8
  have h9 := nb h9
  have h10 := nb h10
  simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne,
    ne_eq, beq_iff_eq] at h1 h2 h4 h5 h6
  refine ⟨h1, h2.1, h2.2, fun r hr => abiRegOK_spec ((List.all_eq_true.mp h3) r hr), h4.1, h4.2,
    fun hk => ?_, h6, fun a r har => ?_, fArgsOK_spec h8, h9, h10⟩
  · rcases h5 with h5 | h5
    · exact absurd hk h5
    · exact h5
  · have := (List.all_eq_true.mp h7) (a, r) har
    simpa only [beq_iff_eq, regHome?_eq] using this

/-- What `icallKind47` accepted: `VK47.icall`. -/
theorem icallKind47_spec {k : Nat} (h : icallKind47 lc v k = .ok kd) (hk : icallLead v.op = some k) :
    (lc.temps[v.id]?).join = none ∧ VK47 lc g v kd := by
  unfold icallKind47 at h
  by_cases ht : (lc.temps[v.id]?).join = none
  · simp only [ht, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
    refine ⟨ht, ?_⟩
    split at h
    next => cases h
    next cabi hcabi =>
      split at h
      next => cases h
      next ins outs hcr =>
        split at h
        next => cases h
        next a0 ha0 =>
          split at h
          next => cases h
          next rc hrc =>
            split at h
            next => cases h
            next o ho =>
              split at h
              next => cases h
              next herr =>
                cases h
                obtain ⟨hnd, hlt, hml, h16, hrc26, hcl0, hctx, hlen, hargs, hfa, hres, hct⟩ :=
                  icallErr47_spec herr
                obtain ⟨m, hm, hmt, hmh⟩ := memLast_spec hml
                exact VK47.icall hk hcabi hcr hnd hlt hm hmt hmh h16 ha0 (regHome?_eq.mp hrc) hrc26
                  hcl0 ho (fun h2 => ctxOK_spec (hctx h2)) hlen hargs hfa (resHome_spec hres) hct
  · have hne : ((lc.temps[v.id]?).join != none) = true := by simpa using ht
    simp only [hne, ↓reduceIte] at h
    cases h

private theorem callTy_tuple47 {n : Nat} {t : Ty} (h : callTy n t = true) :
    t = .tuple (tupleTys t) := by
  cases t <;> first | rfl | simp [callTy] at h

/-- What `selKind47` accepted: `VK47.selF`. -/
theorem selKind47_spec {c : ID} {u : Value} (h : selKind47 lc v c = .ok kd) (hop : v.op = .SelectN)
    (hc0 : v.args[0]? = some c) (hu : lc.ctx.f.value? c = some u)
    (hi : u.op = .ARM64CALLstatic ∨ (icallLead u.op).isSome = true) :
    (lc.temps[v.id]?).join = none ∧ VK47 lc g v kd := by
  unfold selKind47 at h
  by_cases ht : (lc.temps[v.id]?).join = none
  · simp only [ht, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
    refine ⟨ht, ?_⟩
    obtain ⟨hsz, h⟩ := ex_guard h
    obtain ⟨hct, h⟩ := ex_guard h
    simp only [beq_iff_eq] at hsz
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hct
    obtain ⟨ts, hts⟩ : ∃ ts, lc.ty c = .tuple ts := ⟨_, callTy_tuple47 hct.1⟩
    simp only [hts, tupleTys] at hct h
    split at h
    next r hr =>
      obtain ⟨hc, h⟩ := ex_guard h
      obtain ⟨hf, h⟩ := ex_guard h
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at hc hf
      obtain ⟨h31, h47, hlt, hcl⟩ := hc
      obtain ⟨t, htt⟩ : ∃ t, ts[v.auxInt.toInt.toNat]? = some t :=
        ⟨ts[v.auxInt.toInt.toNat], List.getElem?_eq_getElem (by omega)⟩
      rw [htt] at hcl hf
      simp only [Option.bind_some, Option.map_some, Option.some.injEq] at hcl hf
      split at h
      next rs hrs =>
        obtain ⟨hrr, h⟩ := ex_guard h
        cases h
        simp only [beq_iff_eq] at hrr
        exact VK47.selF hop hsz hc0 hu hi hts hct.1 hct.2 (regHome?_eq.mp hr) h31 h47 hlt htt
          hcl hf.2 hf.1 hrs hrr
      next => simp [ex_throw] at h
    next => simp [ex_throw] at h
  · simp [ht, ex_throw, ex_bind_error] at h

end Helpers

/-- What `fcall47` accepted: no temporary, and one of `VK47`'s calls or selects. -/
theorem fcall47_spec {lc : LocCtx} {g : G2In} {v : Value} {e : String} {kd : VKind2}
    (h : fcall47 lc g v e = .ok kd) : (lc.temps[v.id]?).join = none ∧ VK47 lc g v kd := by
  unfold fcall47 at h
  split at h
  next hop => exact callKind47_spec hop h
  next =>
    split at h
    next k hk => exact icallKind47_spec h hk
    next =>
      split at h
      next hop =>
        split at h
        next c hc0 =>
          split at h
          next u hu =>
            split at h
            next hi => exact selKind47_spec h hop hc0 hu hi
            next => cases h
          next => cases h
        next => cases h
      next => cases h

/-- What `vkind47` accepted of a value that is not an entry value: no temporary, and `VK47`. -/
theorem vkind47_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind47 lc g v = .ok kd) (hen : entryOp24 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK47 lc g v kd := by
  unfold vkind47 at h
  cases h46 : vkind46 lc g v with
  | ok kd' =>
    rw [h46] at h
    cases h
    obtain ⟨ht, hVK⟩ := vkind46_spec h46 hen
    exact ⟨ht, .g46 hVK⟩
  | error e =>
    rw [h46] at h
    exact fcall47_spec h

/-- On `InitMem`, `vkind47` is `vkind46`. -/
theorem vkind47_initMem {lc : LocCtx} {g : G2In} {v : Value} (hop : v.op = .InitMem) :
    vkind47 lc g v = vkind46 lc g v := by
  unfold vkind47
  cases vkind46 lc g v with
  | ok _ => rfl
  | error e => simp [fcall47, hop, icallLead]

/-- On an op that is neither a static, interface or closure call nor `SelectN`, `vkind47` is
`vkind46`. -/
theorem vkind47_eq46 {lc : LocCtx} {g : G2In} {v : Value} (h1 : v.op ≠ .ARM64CALLstatic)
    (h2 : icallLead v.op = none) (h3 : v.op ≠ .SelectN) : vkind47 lc g v = vkind46 lc g v := by
  unfold vkind47
  cases vkind46 lc g v with
  | ok _ => rfl
  | error e => simp [fcall47, h1, h2, h3]

/-- On a function with no arm64 op, G47's check is G33. -/
theorem checkG33_of_47L {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG47L lc ps bstart g = r) : checkG33 lc ps bstart g = r := by
  simpa [checkG33, checkG47L, hl] using h

/-- What `checkG47L` accepted of a function with an arm64 op: G46's facts with G47's value
check. -/
theorem checkG47L_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG47L lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind47 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK35 lc = true ∧ uEdgesOK35 lc = true := by
  simp only [checkG47L, hl, ↓reduceIte] at h
  obtain ⟨tab', hb, h⟩ := ex_bind_eq_ok h
  obtain ⟨hpb, h⟩ := ex_guard h
  obtain ⟨hmovd, h⟩ := ex_guard h
  simp only [Bool.and_eq_true] at hmovd
  cases hf : List.find? (fun x => !homeOK10 lc x) (List.range lc.homes.size) with
  | some i =>
    rw [hf] at h
    exact (ex_throw_bind h).elim
  | none =>
    rw [hf] at h
    obtain ⟨-, h⟩ := ex_guard h
    obtain ⟨⟨⟩, hfr, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨⟩, -, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨⟩, hk, h⟩ := ex_bind_eq_ok h
    obtain ⟨hids, h⟩ := ex_guard h
    simp only [ex_pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hids
    refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, hl, fun i => ?_, hfr, hk,
      fun p hp => hids.1 _ (List.mem_map_of_mem hp), hids.2, hb, hpb, hmovd.1, hmovd.2⟩
    by_cases hi : i < lc.homes.size
    · have := List.find?_eq_none.mp hf i (List.mem_range.mpr hi)
      simpa using this
    · have hh : lc.home i = none := by
        simp only [LocCtx.home]
        rw [getElem?_neg lc.homes i hi]
        rfl
      unfold homeOK10 homeOK4 homeOK3 homeOK2 homeOK
      rw [hh]
      rfl

/-- What `checkG47` accepted: `refsLive`, and G47's check on the context without the removed
homes. -/
theorem checkG47_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : PcTab × KTab} (h : checkG47 lc ps bstart g = .ok r) :
    refsLive lc = true ∧ checkG47L (liveCtx lc) ps bstart g = .ok r := by
  unfold checkG47 at h
  cases hr : refsLive lc with
  | false => simp [hr] at h; cases h
  | true => simp only [hr] at h; exact ⟨rfl, by simpa using h⟩

end GoFV.Gen.Check

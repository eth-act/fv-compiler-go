import GoFV.Gen.Check10
import GoFV.Proof.Gen.Spec9

variable [GoFV.SSA.Sem.Addrs]

/-!
# What the genssa validator's slice G10 accepted (`docs/plans/proofs3.md` §4)

`checkG10 lc ps bstart g = .ok (tab, kt)` unfolded into the facts the soundness proof
(`GoFV/Proof/Gen/G10.lean`) uses (`checkG10_spec`): G9's (`Spec9.lean`) with G10's value check
(`vkind10_spec`, `VK10`: G9's values, the interface and closure calls, and the selects of such a
call) and its homes (`homeOK10`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind10` accepted of a value that is not an entry value, and what it emits. -/
inductive VK10 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G9. -/
  | g9 {kd : VKind2} : VK9 lc g v kd → VK10 lc g v kd
  /-- An interface or closure call with `k` leading arguments: the code pointer in `Rn`, the
  closure context in `R26`, the register arguments in their ABI registers, the results in distinct
  ABI result registers at register shapes, then the memory; `CALL (Rn)`. -/
  | icall {k : Nat} {cabi : CallABI} {ins outs : List Nat} {mem a0 rc : Nat} {o : Int} :
      icallLead v.op = some k → callABI? lc.ctx.tabs v.aux = some cabi →
      callRegs cabi = .ok (ins, outs) → outs.Nodup → k < v.args.size → v.args.back? = some mem →
      memTy (lc.ty mem) = true → lc.home mem = none → (∀ r ∈ ins ++ outs, r < 16) →
      v.args[0]? = some a0 → lc.home a0 = some (.reg rc) → rc < 26 →
      (cls (lc.ty a0)).isSome = true → objOf? rc = some o →
      (k = 2 → ∃ a1, v.args[1]? = some a1 ∧ lc.home a1 = some (.reg ctxReg) ∧
        (cls (lc.ty a1)).isSome = true) →
      (v.args.toList.drop k).dropLast.length = ins.length →
      (∀ a r, (a, r) ∈ (v.args.toList.drop k).dropLast.zip ins → lc.home a = some (.reg r)) →
      (lc.home v.id = some (.results (outs.map some).toArray) ∨ (lc.home v.id = none ∧ outs = [])) →
      callTy outs.length (lc.ty v.id) = true → VK10 lc g v (.prog (icallPat o))
  /-- The memory of an interface or closure call: its last component. -/
  | selMem {c : ID} {u : Value} {ts : List Ty} : v.op = .SelectN → v.args.size = 1 →
      v.args[0]? = some c → lc.ctx.f.value? c = some u → (icallLead u.op).isSome = true →
      lc.ty c = .tuple ts → callTy (ts.length - 1) (.tuple ts) = true → 0 ≤ v.auxInt.toInt →
      memTy (lc.ty v.id) = true → lc.home v.id = none → v.auxInt.toInt.toNat + 1 = ts.length →
      VK10 lc g v .none
  /-- Result `i` of an interface or closure call, homed in the call's result register `i`. -/
  | selReg {c : ID} {u : Value} {ts : List Ty} {r : Nat} {rs : Array (Option Nat)} :
      v.op = .SelectN → v.args.size = 1 → v.args[0]? = some c → lc.ctx.f.value? c = some u →
      (icallLead u.op).isSome = true → lc.ty c = .tuple ts →
      callTy (ts.length - 1) (.tuple ts) = true → 0 ≤ v.auxInt.toInt →
      memTy (lc.ty v.id) = false → lc.home v.id = some (.reg r) → r < 16 →
      v.auxInt.toInt.toNat + 1 < ts.length →
      (ts[v.auxInt.toInt.toNat]?.bind cls) = cls (lc.ty v.id) →
      lc.home c = some (.results rs) → rs[v.auxInt.toInt.toNat]? = some (some r) →
      VK10 lc g v .none

/-- The fields of a Prog `icallPat o` accepts: `CALL (Rn)`. -/
theorem icallPat_spec {o : Int} {p : Prog} (h : (icallPat o).ok p = true) :
    p.as = .CALL ∧ p.from_ = {} ∧ p.reg = 0 ∧ p.scond = 0 ∧ p.rest.isEmpty = true ∧
      p.regTo2 = 0 ∧ p.to.type = .MEM ∧ p.to.name = .NONE ∧ p.to.reg = o := by
  obtain ⟨has, hf, hr, ht, hsc, hrest, hr2⟩ := plain_spec h
  simp only [beq_iff_eq] at hf
  simp only [Bool.and_eq_true, beq_iff_eq] at ht
  exact ⟨has, hf, hr, hsc, hrest, hr2, ht.1.1, ht.1.2, ht.2⟩

theorem icallLead_some {o : Op} {k : Nat} (h : icallLead o = some k) :
    (o = .ARM64CALLinter ∧ k = 1) ∨ (o = .ARM64CALLclosure ∧ k = 2) := by
  unfold icallLead at h
  split at h <;> simp_all

private theorem callTy_tuple10 {n : Nat} {t : Ty} (h : callTy n t = true) :
    t = .tuple (tupleTys t) := by
  cases t <;> first | rfl | simp [callTy] at h

/-- What `selKind` accepted: `VK10`'s selects. -/
theorem selKind_spec {lc : LocCtx} {g : G2In} {v : Value} {c : ID} {u : Value} {kd : VKind2}
    (h : selKind lc v c = .ok kd) (hop : v.op = .SelectN) (hc0 : v.args[0]? = some c)
    (hu : lc.ctx.f.value? c = some u) (hi : (icallLead u.op).isSome = true) :
    (lc.temps[v.id]?).join = none ∧ VK10 lc g v kd := by
  unfold selKind at h
  by_cases ht : (lc.temps[v.id]?).join = none
  · simp only [ht, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
    refine ⟨ht, ?_⟩
    obtain ⟨hsz, h⟩ := ex_guard h
    obtain ⟨hct, h⟩ := ex_guard h
    simp only [beq_iff_eq] at hsz
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hct
    obtain ⟨ts, hts⟩ : ∃ ts, lc.ty c = .tuple ts := ⟨_, callTy_tuple10 hct.1⟩
    simp only [hts, tupleTys] at hct h
    split at h
    next hm =>
      obtain ⟨hc, h⟩ := ex_guard h
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact VK10.selMem hop hsz hc0 hu hi hts hct.1 hct.2 hm hc.1 hc.2
    next hm =>
      split at h
      next r hr =>
        obtain ⟨hc, h⟩ := ex_guard h
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
        split at h
        next rs hrs =>
          obtain ⟨hrr, h⟩ := ex_guard h
          cases h
          simp only [beq_iff_eq] at hrr
          exact VK10.selReg hop hsz hc0 hu hi hts hct.1 hct.2 (by simpa using hm)
            (regHome?_eq.mp hr) hc.1.1 hc.1.2 hc.2 hrs hrr
        next => simp [ex_throw] at h
      next => simp [ex_throw] at h
  · simp [ht, ex_throw, ex_bind_error] at h

private theorem nb {b : Bool} (h : ¬ ((!b) = true)) : b = true := by
  cases b <;> simp_all

theorem memLast_spec {lc : LocCtx} {v : Value} (h : memLast lc v = true) :
    ∃ m, v.args.back? = some m ∧ memTy (lc.ty m) = true ∧ lc.home m = none := by
  unfold memLast at h
  split at h
  next m hm =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨m, hm, h.1, h.2⟩
  next => cases h

theorem resHome_spec {lc : LocCtx} {v : Value} {outs : List Nat} (h : resHome lc v outs = true) :
    lc.home v.id = some (.results (outs.map some).toArray) ∨ (lc.home v.id = none ∧ outs = []) := by
  unfold resHome at h
  split at h
  next rs hrs =>
    simp only [beq_iff_eq] at h
    left
    rw [hrs, ← h]
  next hn => exact Or.inr ⟨hn, List.isEmpty_iff.mp h⟩
  next => cases h

theorem ctxOK_spec {lc : LocCtx} {v : Value} (h : ctxOK lc v = true) :
    ∃ a1, v.args[1]? = some a1 ∧ lc.home a1 = some (.reg ctxReg) ∧
      (cls (lc.ty a1)).isSome = true := by
  unfold ctxOK at h
  split at h
  next a1 ha1 =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨a1, ha1, regHome?_eq.mp h.1, h.2⟩
  next => cases h

/-- What `icallErr` accepted. -/
theorem icallErr_spec {lc : LocCtx} {v : Value} {k : Nat} {ins outs : List Nat} {a0 rc : Nat}
    (h : icallErr lc v k ins outs a0 rc = none) :
    outs.Nodup ∧ k < v.args.size ∧ memLast lc v = true ∧ (∀ r ∈ ins ++ outs, r < 16) ∧
      rc < 26 ∧ (cls (lc.ty a0)).isSome = true ∧ (k = 2 → ctxOK lc v = true) ∧
      (v.args.toList.drop k).dropLast.length = ins.length ∧
      (∀ a r, (a, r) ∈ (v.args.toList.drop k).dropLast.zip ins → lc.home a = some (.reg r)) ∧
      resHome lc v outs = true ∧ callTy outs.length (lc.ty v.id) = true := by
  unfold icallErr at h
  simp only at h
  split at h
  · cases h
  rename_i h1
  split at h
  · cases h
  rename_i h2
  split at h
  · cases h
  rename_i h3
  split at h
  · cases h
  rename_i h4
  split at h
  · cases h
  rename_i h5
  split at h
  · cases h
  rename_i h6
  split at h
  · cases h
  rename_i h7
  split at h
  · cases h
  rename_i h8
  split at h
  · cases h
  rename_i h9
  have h1 := nb h1
  have h2 := nb h2
  have h3 := nb h3
  have h4 := nb h4
  have h5 := nb h5
  have h6 := nb h6
  have h7 := nb h7
  have h8 := nb h8
  have h9 := nb h9
  simp only [decide_eq_true_eq, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, bne_iff_ne,
    ne_eq, beq_iff_eq] at h1 h2 h3 h4 h5 h6
  refine ⟨h1, h2.1, h2.2, h3, h4.1, h4.2, fun hk => ?_, h6, fun a r har => ?_, h8, h9⟩
  · rcases h5 with h5 | h5
    · exact absurd hk h5
    · exact h5
  · have := (List.all_eq_true.mp h7) (a, r) har
    simpa only [beq_iff_eq, regHome?_eq] using this

/-- What `icallKind` accepted: `VK10.icall`. -/
theorem icallKind_spec {lc : LocCtx} {g : G2In} {v : Value} {k : Nat} {kd : VKind2}
    (h : icallKind lc v k = .ok kd) (hk : icallLead v.op = some k) :
    (lc.temps[v.id]?).join = none ∧ VK10 lc g v kd := by
  unfold icallKind at h
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
                obtain ⟨hnd, hlt, hml, h16, hrc26, hcl0, hctx, hlen, hargs, hres, hct⟩ :=
                  icallErr_spec herr
                obtain ⟨m, hm, hmt, hmh⟩ := memLast_spec hml
                exact VK10.icall hk hcabi hcr hnd hlt hm hmt hmh h16 ha0 (regHome?_eq.mp hrc) hrc26
                  hcl0 ho (fun h2 => ctxOK_spec (hctx h2)) hlen hargs (resHome_spec hres) hct
  · have hne : ((lc.temps[v.id]?).join != none) = true := by simpa using ht
    simp only [hne, ↓reduceIte] at h
    cases h

/-- What `vkind10` accepted of a value that is not an entry value: no temporary, and `VK10`. -/
theorem vkind10_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind10 lc g v = .ok kd) (hen : entryOp3 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK10 lc g v kd := by
  unfold vkind10 at h
  split at h
  next k hk => exact icallKind_spec h hk
  next =>
    have g9 : vkind9 lc g v = .ok kd → (lc.temps[v.id]?).join = none ∧ VK10 lc g v kd :=
      fun h9 => ⟨(vkind9_spec h9 hen).1, .g9 (vkind9_spec h9 hen).2⟩
    split at h
    next hop =>
      simp only [beq_iff_eq] at hop
      split at h
      next c hc0 =>
        split at h
        next u hu =>
          split at h
          next hi => exact selKind_spec h hop hc0 hu hi
          next => exact g9 h
        next => exact g9 h
      next => exact g9 h
    next => exact g9 h

/-- What `checkG10` accepted: G9's facts with G10's value check and homes. -/
theorem checkG10_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (h : checkG10 lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind10 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab := by
  unfold checkG10 at h
  obtain ⟨hl, h⟩ := ex_guard h
  obtain ⟨tab', hb, h⟩ := ex_bind_eq_ok h
  cases hf : List.find? (fun x => !homeOK10 lc x) (List.range lc.homes.size) with
  | some i =>
    rw [hf] at h
    exact (ex_throw_bind h).elim
  | none =>
    rw [hf] at h
    obtain ⟨⟨⟩, hfr, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨⟩, -, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨⟩, hk, h⟩ := ex_bind_eq_ok h
    obtain ⟨hids, h⟩ := ex_guard h
    simp only [ex_pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hids
    refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, hl, fun i => ?_, hfr, hk,
      fun p hp => hids.1 _ (List.mem_map_of_mem hp), hids.2, hb⟩
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

/-- A home G10 handles that is no `results` home and no slot of an `Arg` is one G4 handles. -/
theorem homeOK4_of_10 {lc : LocCtx} {i : Nat} (h : homeOK10 lc i = true)
    (hr : ∀ rs, lc.home i ≠ some (.results rs))
    (ha : ∀ k, lc.home i = some (.slot k) → (lc.ctx.f.value? i).map (·.op) ≠ some .Arg) :
    homeOK4 lc i = true := by
  unfold homeOK10 at h
  cases hh : lc.home i with
  | none => simpa [hh] using h
  | some l =>
    cases l with
    | results rs => exact absurd hh (hr rs)
    | slot k =>
      have hna := ha k hh
      rw [hh] at h
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      exact h.resolve_right hna
    | _ => simpa [hh] using h

end GoFV.Gen.Check

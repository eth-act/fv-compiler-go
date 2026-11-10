import GoFV.Gen.Check48
import GoFV.Proof.Gen.Spec57

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `checkG48` accepted (`GoFV/Gen/Check48.lean`)

`VK48`: G57's kinds (`VK57`, through `vkind57`), G48's static calls with stack-assigned inputs or
outputs (`callKind48_spec`, `VK48.call`), and the accesses off `SP` (`spKind48_spec`, `VKsp48`) with
their base homed in the Go register `SP` (`spBase48_spec`). On `InitMem`, `vkind48` accepts what
`vkind57` accepts (`vkind48_initMem`). `checkG48L_spec` is `checkG57L_spec` with `vkind48` and
`spHomes48`, whose meaning is `spHomes48_spec`; `checkG48_spec` splits off `refsLive`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `spKind48` accepted of an access off `SP` at `o = v.auxInt` (`o(RSP)`, `spDst48`), and
what it emits: the window `[o, o + n)` in `[8, outargsSize)` (`outWin48`). -/
inductive VKsp48 (lc : LocCtx) (v : Value) : VKind2 → Prop
  /-- `MOV{D,W,WU,H,HU,B,BU} o(RSP), Rd`. -/
  | load {as : As} {n : Nat} {sg : Bool} {c : Nat} {rd : Int} :
      loadOp? v.op = some (as, n, sg) → v.args.size = 2 → outWin48 lc v.auxInt.toInt n = true →
      memArg lc v 1 = .ok () → resObj lc v = .ok (c, rd) → (8 ≤ c ∨ c = 1 ∧ n = 1 ∧ sg = false) →
      VKsp48 lc v (.prog ⟨plain as (spDst48 v) (· == regA rd), as.name⟩)
  /-- `MOV{D,W,H,B} Rs, o(RSP)`. -/
  | store {as : As} {n cs : Nat} {rs : Int} :
      storeOp? v.op = some (as, n) → v.args.size = 3 → memTy (lc.ty v.id) = true →
      lc.home v.id = none → outWin48 lc v.auxInt.toInt n = true → argObj lc v 1 = .ok (cs, rs) →
      memArg lc v 2 = .ok () → (8 * n ≤ cs ∨ cs = 1 ∧ n = 1) →
      VKsp48 lc v (.prog ⟨plain as (· == regA rs) (spDst48 v), as.name⟩)
  /-- `STP (Rx, Ry), o(RSP)` of two 64-bit registers. -/
  | stp {rx ry : Int} :
      v.op = .ARM64STP → v.args.size = 4 → memTy (lc.ty v.id) = true → lc.home v.id = none →
      outWin48 lc v.auxInt.toInt 16 = true → argObj lc v 1 = .ok (64, rx) →
      argObj lc v 2 = .ok (64, ry) → memArg lc v 3 = .ok () →
      VKsp48 lc v (.prog (.ofShape (stpSP48 rx ry v.auxInt.toInt)))
  /-- `STPW (Rx, Ry), o(RSP)` of the low words of two registers of at least 32 bits. -/
  | stpw {cx cy : Nat} {rx ry : Int} :
      v.op = .ARM64STPW → v.args.size = 4 → memTy (lc.ty v.id) = true → lc.home v.id = none →
      outWin48 lc v.auxInt.toInt 8 = true → argObj lc v 1 = .ok (cx, rx) →
      argObj lc v 2 = .ok (cy, ry) → 32 ≤ cx → 32 ≤ cy → memArg lc v 3 = .ok () →
      VKsp48 lc v (.prog (.ofShape (stpwSP48 rx ry v.auxInt.toInt)))
  /-- `FSTPD (Fx, Fy), o(RSP)` of two 64-bit floats. -/
  | fstpd {rx ry : Int} :
      v.op = .ARM64FSTPD → v.args.size = 4 → memTy (lc.ty v.id) = true → lc.home v.id = none →
      outWin48 lc v.auxInt.toInt 16 = true → fargObj lc v 1 = .ok (64, rx) →
      fargObj lc v 2 = .ok (64, ry) → memArg lc v 3 = .ok () →
      VKsp48 lc v (.prog (.ofShape (fstpdSP48 rx ry v.auxInt.toInt)))
  /-- `FMOV{S,D} o(RSP), Fd`. -/
  | fload {c : Nat} {rd : Int} :
      (v.op = .ARM64FMOVSload ∨ v.op = .ARM64FMOVDload) → v.args.size = 2 →
      outWin48 lc v.auxInt.toInt (fBytes v.op) = true → memArg lc v 1 = .ok () →
      fresObj lc v = .ok (c, rd) → c = 8 * fBytes v.op →
      VKsp48 lc v (.prog ⟨plain (fmovAs c) (spDst48 v) (· == regA rd), (fmovAs c).name⟩)
  /-- `FMOV{S,D} Fs, o(RSP)`. -/
  | fstore {cs : Nat} {rs : Int} :
      (v.op = .ARM64FMOVSstore ∨ v.op = .ARM64FMOVDstore) → v.args.size = 3 →
      memTy (lc.ty v.id) = true → lc.home v.id = none →
      outWin48 lc v.auxInt.toInt (fBytes v.op) = true → fargObj lc v 1 = .ok (cs, rs) →
      memArg lc v 2 = .ok () → cs = 8 * fBytes v.op →
      VKsp48 lc v (.prog ⟨plain (fmovAs cs) (· == regA rs) (spDst48 v), (fmovAs cs).name⟩)

/-- What `vkind48` accepted of a value that is not an entry value, and what it emits. -/
inductive VK48 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G57. -/
  | g57 {kd : VKind2} : VK57 lc g v kd → VK48 lc g v kd
  /-- A static call as `VK47.call`, on its ABI without its stack-assigned inputs and outputs
  (`callRegsS`), with no temporary. -/
  | call {name : GoStr} {abi : Nat} {cabi : CallABI} {ins outs : List Nat} {mem : ID} :
      (lc.temps[v.id]?).join = none →
      v.op = .ARM64CALLstatic → callOf? lc.ctx.tabs v.aux = some (name, abi, cabi) →
      callRegsS cabi = .ok (ins, outs) → outs.Nodup → v.args.back? = some mem →
      memTy (lc.ty mem) = true → lc.home mem = none →
      (∀ r ∈ ins ++ outs, r < 16 ∨ (31 ≤ r ∧ r < 47)) →
      v.args.toList.dropLast.length = ins.length →
      (∀ a r, (a, r) ∈ v.args.toList.dropLast.zip ins → lc.home a = some (.reg r)) →
      (∀ a r, (a, r) ∈ v.args.toList.dropLast.zip ins → 31 ≤ r → fTy (lc.ty a) = true) →
      (lc.home v.id = some (.results (outs.map some).toArray) ∨ (lc.home v.id = none ∧ outs = [])) →
      callTy outs.length (lc.ty v.id) = true → VK48 lc g v (.prog (callPat g name abi))
  /-- An access off `SP` without an aux, its base homed in the Go register `SP` (`spBase48`), with
  no temporary. -/
  | sp {kd : VKind2} : (lc.temps[v.id]?).join = none → v.aux = none → spArg lc v = true →
      spBase48 lc v = true → VKsp48 lc v kd → VK48 lc g v kd

section Helpers

variable {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}

/-- What `callKind48` accepted: `VK48.call`. -/
theorem callKind48_spec (hop : v.op = .ARM64CALLstatic) (h : callKind48 lc g v = .ok kd) :
    VK48 lc g v kd := by
  unfold callKind48 at h
  by_cases ht : (lc.temps[v.id]?).join = none
  · simp only [ht, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
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
        all_goals
          exact VK48.call ht hop hcall hcr hnd hm hmem.1 hmem.2 hab hlen hargs' hfa' hres hct
      next => simp [ex_throw] at h
    next => simp [ex_throw] at h
  · simp [ht, ex_throw, ex_bind_error] at h

/-- What `spKind48` accepted: `VKsp48`. -/
theorem spKind48_spec (h : spKind48 lc v = .ok kd) : VKsp48 lc v kd := by
  unfold spKind48 at h
  split at h
  next as n sg hl =>
    obtain ⟨hsz, h⟩ := ex_guard h
    simp only [beq_iff_eq] at hsz
    obtain ⟨hw, h⟩ := ex_guard h
    obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
    obtain ⟨hc, h⟩ := ex_guard h
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
      Bool.not_eq_true', and_assoc] at hc
    simp only [ex_pure, Except.ok.injEq] at h
    subst h
    exact VKsp48.load hl hsz hw hma hro hc
  next =>
    split at h
    next as n hst =>
      obtain ⟨hsz, h⟩ := ex_guard h
      simp only [Bool.and_eq_true, beq_iff_eq] at hsz
      obtain ⟨⟨hsz, hmt⟩, hhn⟩ := hsz
      obtain ⟨hw, h⟩ := ex_guard h
      obtain ⟨⟨cs, rs⟩, hso, h⟩ := ex_bind_eq_ok h
      obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
      obtain ⟨hc, h⟩ := ex_guard h
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at hc
      simp only [ex_pure, Except.ok.injEq] at h
      subst h
      exact VKsp48.store hst hsz hmt hhn hw hso hma hc
    next =>
      split at h
      next hop =>
        obtain ⟨hsz, h⟩ := ex_guard h
        simp only [Bool.and_eq_true, beq_iff_eq] at hsz
        obtain ⟨⟨hsz, hmt⟩, hhn⟩ := hsz
        obtain ⟨hw, h⟩ := ex_guard h
        obtain ⟨⟨cx, rx⟩, hx, h⟩ := ex_bind_eq_ok h
        obtain ⟨⟨cy, ry⟩, hy, h⟩ := ex_bind_eq_ok h
        obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
        obtain ⟨hwd, h⟩ := ex_guard h
        simp only [Bool.and_eq_true, beq_iff_eq] at hwd
        obtain ⟨rfl, rfl⟩ := hwd
        simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte, ex_pure, Except.ok.injEq] at h
        subst h
        exact VKsp48.stp hop hsz hmt hhn hw hx hy hma
      next hop =>
        obtain ⟨hsz, h⟩ := ex_guard h
        simp only [Bool.and_eq_true, beq_iff_eq] at hsz
        obtain ⟨⟨hsz, hmt⟩, hhn⟩ := hsz
        obtain ⟨hw, h⟩ := ex_guard h
        obtain ⟨⟨cx, rx⟩, hx, h⟩ := ex_bind_eq_ok h
        obtain ⟨⟨cy, ry⟩, hy, h⟩ := ex_bind_eq_ok h
        obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
        obtain ⟨hwd, h⟩ := ex_guard h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hwd
        simp only [ex_pure, Except.ok.injEq] at h
        subst h
        exact VKsp48.stpw hop hsz hmt hhn hw hx hy hwd.1 hwd.2 hma
      next hop =>
        obtain ⟨hsz, h⟩ := ex_guard h
        simp only [Bool.and_eq_true, beq_iff_eq] at hsz
        obtain ⟨⟨hsz, hmt⟩, hhn⟩ := hsz
        obtain ⟨hw, h⟩ := ex_guard h
        obtain ⟨⟨cx, rx⟩, hx, h⟩ := ex_bind_eq_ok h
        obtain ⟨⟨cy, ry⟩, hy, h⟩ := ex_bind_eq_ok h
        obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
        obtain ⟨hwd, h⟩ := ex_guard h
        simp only [Bool.and_eq_true, beq_iff_eq] at hwd
        obtain ⟨rfl, rfl⟩ := hwd
        simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte, ex_pure, Except.ok.injEq] at h
        subst h
        exact VKsp48.fstpd hop hsz hmt hhn hw hx hy hma
      all_goals first
        | (simp [ex_throw] at h; done)
        | (rename_i hop
           obtain ⟨hsz, h⟩ := ex_guard h
           simp only [beq_iff_eq] at hsz
           obtain ⟨hw, h⟩ := ex_guard h
           obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
           obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
           obtain ⟨hc, h⟩ := ex_guard h
           simp only [beq_iff_eq] at hc
           simp only [ex_pure, Except.ok.injEq] at h
           subst h
           first
             | exact VKsp48.fload (.inl hop) hsz hw hma hro hc
             | exact VKsp48.fload (.inr hop) hsz hw hma hro hc)
        | (rename_i hop
           obtain ⟨hsz, h⟩ := ex_guard h
           simp only [Bool.and_eq_true, beq_iff_eq] at hsz
           obtain ⟨⟨hsz, hmt⟩, hhn⟩ := hsz
           obtain ⟨hw, h⟩ := ex_guard h
           obtain ⟨⟨cs, rs⟩, hso, h⟩ := ex_bind_eq_ok h
           obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
           obtain ⟨hc, h⟩ := ex_guard h
           simp only [beq_iff_eq] at hc
           simp only [ex_pure, Except.ok.injEq] at h
           subst h
           first
             | exact VKsp48.fstore (.inl hop) hsz hmt hhn hw hso hma hc
             | exact VKsp48.fstore (.inr hop) hsz hmt hhn hw hso hma hc)

end Helpers

/-- What `kind48` accepted: one of `VK48`'s calls or accesses off `SP`. -/
theorem kind48_spec {lc : LocCtx} {g : G2In} {v : Value} {e : String} {kd : VKind2}
    (h : kind48 lc g v e = .ok kd) : VK48 lc g v kd := by
  unfold kind48 at h
  split at h
  next hop => exact callKind48_spec hop h
  next =>
    split at h
    next hsp =>
      split at h
      next => cases h
      next ht =>
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at ht
        split at h
        next => cases h
        next hb =>
          simp only [Bool.not_eq_true', Bool.not_eq_false] at hb
          exact .sp ht hsp.1 hsp.2 hb (spKind48_spec h)
    next => cases h

/-- What `vkind48` accepted of a value that is not an entry value: `VK48`. -/
theorem vkind48_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind48 lc g v = .ok kd) (hen : entryOp24 v.op = false) : VK48 lc g v kd := by
  unfold vkind48 at h
  cases h57 : vkind57 lc g v with
  | ok kd' =>
    rw [h57] at h
    cases h
    exact .g57 (vkind57_spec h57 hen)
  | error e =>
    rw [h57] at h
    exact kind48_spec h

/-- On `InitMem` (no call, no access off `SP`), what `vkind48` accepted `vkind57` accepted. -/
theorem vkind48_initMem {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (hop : v.op = .InitMem)
    (h : vkind48 lc g v = .ok kd) : vkind57 lc g v = .ok kd := by
  unfold vkind48 at h
  cases h57 : vkind57 lc g v with
  | ok kd' => rw [h57] at h; exact h
  | error e =>
    rw [h57] at h
    exfalso
    simp [kind48, spKind48, hop, loadOp?, storeOp?, narrowLoad?, narrowStore?] at h
    repeat' split at h
    all_goals first | cases h | simp [ex_throw] at h

/-- On a function with no arm64 op, G48's check is G33. -/
theorem checkG33_of_48L {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG48L lc ps bstart g = r) : checkG33 lc ps bstart g = r := by
  simpa [checkG33, checkG48L, hl] using h

/-- What `checkG48L` accepted of a function with an arm64 op: G57's facts with G48's value check,
and `spHomes48`. -/
theorem checkG48L_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG48L lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind48 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK35 lc = true ∧ uEdgesOK35 lc = true ∧ loopOK lc ps tab = true ∧
      spHomes48 lc = true := by
  simp only [checkG48L, hl, ↓reduceIte] at h
  obtain ⟨tab', hb, h⟩ := ex_bind_eq_ok h
  obtain ⟨hpb, h⟩ := ex_guard h
  obtain ⟨hlp, h⟩ := ex_guard h
  obtain ⟨hmovd, h⟩ := ex_guard h
  simp only [Bool.and_eq_true] at hmovd
  cases hf : List.find? (fun x => !homeOK10 lc x) (List.range lc.homes.size) with
  | some i =>
    rw [hf] at h
    exact (ex_throw_bind h).elim
  | none =>
    rw [hf] at h
    obtain ⟨-, h⟩ := ex_guard h
    obtain ⟨hsph, h⟩ := ex_guard h
    obtain ⟨⟨⟩, hfr, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨⟩, -, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨⟩, hk, h⟩ := ex_bind_eq_ok h
    obtain ⟨hids, h⟩ := ex_guard h
    simp only [ex_pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hids
    refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, hl, fun i => ?_, hfr, hk,
      fun p hp => hids.1 _ (List.mem_map_of_mem hp), hids.2, hb, hpb, hmovd.1, hmovd.2, hlp,
      hsph⟩
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

/-- What `checkG48` accepted: `refsLive`, and `checkG48L` on `liveCtx`. -/
theorem checkG48_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : PcTab × KTab} (h : checkG48 lc ps bstart g = .ok r) :
    refsLive lc = true ∧ checkG48L (liveCtx lc) ps bstart g = .ok r := by
  unfold checkG48 at h
  cases hr : refsLive lc with
  | false => simp [hr] at h; cases h
  | true => simp only [hr] at h; exact ⟨rfl, by simpa using h⟩

/-- What `spHomes48` checks: the home of a value that lists the Go register `SP` is a `Phi`'s, or
`SP`'s own register home at a 64-bit shape with no temporary. -/
theorem spHomes48_spec {lc : LocCtx} (h : spHomes48 lc = true) :
    ∀ id v, lc.ctx.f.value? id = some v → ∀ l, lc.home v.id = some l →
      some spReg ∈ l.regList → v.op = .Phi ∨
        (l = .reg spReg ∧ v.op = .SP ∧ cls (lc.ty v.id) = some 64 ∧
          (lc.temps[v.id]?).join = none) := by
  intro i v hv l hl hin
  have hi : i < lc.ctx.f.valueTab.size := by
    refine Decidable.byContradiction fun hn => ?_
    simp only [Func.value?] at hv
    rw [getElem?_neg lc.ctx.f.valueTab i hn] at hv
    cases hv
  have := (List.all_eq_true.mp h) i (List.mem_range.mpr hi)
  rw [hv] at this
  simp only [hl, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, Bool.and_eq_true] at this
  rcases this with (h1 | h1) | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  · have : l.regList.contains (some spReg) = true := List.contains_iff_mem.mpr hin
    rw [this] at h1; cases h1
  · exact .inl h1
  · exact .inr ⟨h1, h2, h3, by simpa using h4⟩

/-- What `spBase48` checks: the first argument is homed in the Go register `SP` at a 64-bit
shape. -/
theorem spBase48_spec {lc : LocCtx} {v : Value} (h : spBase48 lc v = true) :
    ∃ a, v.args[0]? = some a ∧ lc.home a = some (.reg spReg) ∧ cls (lc.ty a) = some 64 := by
  unfold spBase48 at h
  split at h
  next a ha =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨a, ha, h.1, h.2⟩
  next => cases h

end GoFV.Gen.Check

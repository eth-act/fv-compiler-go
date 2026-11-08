import GoFV.Gen.Check22
import GoFV.Proof.Gen.Spec21

/-!
# What the genssa validator's slice G22 accepted (`docs/plans/proofs3.md` §4)

`checkG22 lc ps bstart g = .ok (tab, kt)` unfolded into the facts the soundness proof
(`GoFV/Proof/Gen/G22.lean`) uses (`checkG22_spec`): G21's (`Spec21.lean`) with G22's value check
(`vkind22_spec`, `VK22`: G21's values, and `LDP`/`STP` of a global).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind22` accepted of a value that is not an entry value, and what it emits. -/
inductive VK22 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G21 (no pair access of a global). -/
  | g21 {kd : VKind2} : globPair lc v = false → VK21 lc g v kd → VK22 lc g v kd
  /-- `LDP sym+off(SB), (Ra, Rb)`: G4's result conditions. -/
  | ldp {x a : Nat} {name : GoStr} {abi : Nat} {ra rb : Nat} {oa ob : Int} {t0 t1 : Ty}
      {c0 c1 : Nat} :
      v.op = .ARM64LDP → v.aux = some x → v.args[0]? = some a →
      (lc.ctx.f.value? a).map (·.op) = some .SB → symOf? lc.ctx.tabs x = some (name, abi) →
      v.args.size = 2 → lc.ty v.id = .tuple [t0, t1] →
      cls t0 = some c0 → cls t1 = some c1 → 8 ≤ c0 → 8 ≤ c1 → memArg lc v 1 = .ok () →
      lc.home v.id = some (.pair (some ra) (some rb)) → ra ≠ rb → ra ≠ zeroReg → rb ≠ zeroReg →
      destOK ra = true → destOK rb = true → objOf? ra = some oa → objOf? rb = some ob →
      VK22 lc g v
        (.prog ⟨plain .LDP (globA g name abi v.auxInt.toInt) (· == pairA oa ob), "LDP sym(SB)"⟩)
  /-- `STP (Rx, Ry), sym+off(SB)` of two 64-bit registers. -/
  | stp {x a : Nat} {name : GoStr} {abi : Nat} {rx ry : Int} :
      v.op = .ARM64STP → v.aux = some x → v.args[0]? = some a →
      (lc.ctx.f.value? a).map (·.op) = some .SB → symOf? lc.ctx.tabs x = some (name, abi) →
      v.args.size = 4 → memTy (lc.ty v.id) = true → lc.home v.id = none →
      argObj lc v 1 = .ok (64, rx) → argObj lc v 2 = .ok (64, ry) → memArg lc v 3 = .ok () →
      VK22 lc g v
        (.prog ⟨plain .STP (· == pairA rx ry) (globA g name abi v.auxInt.toInt), "STP sym(SB)"⟩)

/-- What `globPair` accepted: an `LDP` or `STP` with an aux, its address argument `SB`. -/
theorem globPair_spec {lc : LocCtx} {v : Value} (h : globPair lc v = true) :
    (v.op = .ARM64LDP ∨ v.op = .ARM64STP) ∧ ∃ a, v.args[0]? = some a ∧
      (lc.ctx.f.value? a).map (·.op) = some .SB := by
  simp only [globPair, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hop, -⟩, hsb⟩ := h
  refine ⟨hop, ?_⟩
  cases ha : v.args[0]? with
  | none => rw [ha] at hsb; cases hsb
  | some a =>
    rw [ha] at hsb
    exact ⟨a, rfl, by simpa [Option.bind] using hsb⟩

/-- What `globPairKind` accepted: no temporary, and `VK22`'s `ldp` or `stp`. -/
theorem globPairKind_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (hg : globPair lc v = true) (h : globPairKind lc g v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK22 lc g v kd := by
  obtain ⟨hop, a, ha, hsb⟩ := globPair_spec hg
  unfold globPairKind at h
  obtain ⟨ht, h⟩ := ex_guard h
  simp only [beq_iff_eq] at ht
  refine ⟨ht, ?_⟩
  split at h
  next x hx =>
    split at h
    next name abi hsy =>
      split at h
      next hl =>
        simp only [beq_iff_eq] at hl
        obtain ⟨hsz, h⟩ := ex_guard h
        simp only [Bool.and_eq_true, beq_iff_eq] at hsz
        obtain ⟨hsz, hpt⟩ := hsz
        obtain ⟨t0, t1, c0, c1, hty, h0, h1, h80, h81⟩ := pairTys_spec hpt
        obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
        split at h
        next ra rb hph =>
          obtain ⟨hr, h⟩ := ex_guard h
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hr
          obtain ⟨⟨⟨⟨hne, hza⟩, hzb⟩, hda⟩, hdb⟩ := hr
          split at h
          next oa hoa =>
            split at h
            next ob hob =>
              simp only [ex_pure, Except.ok.injEq] at h
              subst h
              exact VK22.ldp hl hx ha hsb hsy hsz hty h0 h1 h80 h81 hma (pairHome?_eq hph) hne hza
                hzb hda hdb hoa hob
            next => simp [ex_throw] at h
          next => simp [ex_throw] at h
        next => simp [ex_throw] at h
      next hl =>
        have hs : v.op = .ARM64STP := by
          rcases hop with h' | h'
          · exact absurd (by simp [h']) hl
          · exact h'
        obtain ⟨hsz, h⟩ := ex_guard h
        simp only [Bool.and_eq_true, beq_iff_eq] at hsz
        obtain ⟨⟨hsz, hmt⟩, hhn⟩ := hsz
        obtain ⟨⟨cx, rx⟩, hxo, h⟩ := ex_bind_eq_ok h
        obtain ⟨⟨cy, ry⟩, hyo, h⟩ := ex_bind_eq_ok h
        obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
        obtain ⟨hw, h⟩ := ex_guard h
        simp only [Bool.and_eq_true, beq_iff_eq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        simp only [ex_pure, Except.ok.injEq, beq_self_eq_true, Bool.and_self, ↓reduceIte] at h
        subst h
        exact VK22.stp hs hx ha hsb hsy hsz hmt hhn hxo hyo hma
    next => simp [ex_throw] at h
  next => simp [ex_throw] at h

/-- What `vkind22` accepted of a value that is not an entry value: no temporary, and `VK22`. -/
theorem vkind22_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind22 lc g v = .ok kd) (hen : entryOp3 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK22 lc g v kd := by
  unfold vkind22 at h
  cases hg : globPair lc v with
  | true =>
    simp only [hg, ↓reduceIte] at h
    exact globPairKind_spec hg h
  | false =>
    simp only [hg, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨ht, h21⟩ := vkind21_spec h hen
    exact ⟨ht, .g21 hg h21⟩

/-- What `checkG22` accepted: G21's facts with G22's value check. -/
theorem checkG22_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (h : checkG22 lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind22 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK lc = true := by
  unfold checkG22 at h
  obtain ⟨hl, h⟩ := ex_guard h
  obtain ⟨tab', hb, h⟩ := ex_bind_eq_ok h
  obtain ⟨hpb, h⟩ := ex_guard h
  obtain ⟨hmovd, h⟩ := ex_guard h
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
      fun p hp => hids.1 _ (List.mem_map_of_mem hp), hids.2, hb, hpb, hmovd⟩
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

end GoFV.Gen.Check

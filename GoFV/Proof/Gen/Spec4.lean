import GoFV.Gen.Check4
import GoFV.Proof.Gen.Spec3

/-!
# What the genssa validator's slice G4 accepted (`docs/plans/proofs3.md` §4)

`checkG4 lc ps bstart g = .ok (tab, kt)` unfolded into the facts the soundness proof
(`GoFV/Proof/Gen/G4.lean`) uses (`checkG4_spec`): G3's (`Spec3.lean`) with G4's value check
(`vkind4_spec`, `VK4`: G3's values, the pair load `LDP` into a register pair, the pair store `STP`,
`Select0`/`Select1` of an `LDP`) and homes (`homeOK4`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `pairTys` accepted: two component shapes of integer classes of at least 8 bits. -/
theorem pairTys_spec {t : Ty} (h : pairTys t = true) :
    ∃ t0 t1 c0 c1, t = .tuple [t0, t1] ∧ cls t0 = some c0 ∧ cls t1 = some c1 ∧ 8 ≤ c0 ∧ 8 ≤ c1 := by
  unfold pairTys at h
  split at h
  next t0 t1 =>
    simp only [Bool.and_eq_true, Option.any_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨c0, h0, h8⟩, ⟨c1, h1, h8'⟩⟩ := h
    exact ⟨t0, t1, c0, c1, rfl, h0, h1, h8, h8'⟩
  next => cases h

theorem pairHome?_eq {lc : LocCtx} {id ra rb : Nat} (h : pairHome? lc id = some (ra, rb)) :
    lc.home id = some (.pair (some ra) (some rb)) := by
  unfold pairHome? at h
  split at h
  next a b hh => cases h; exact hh
  next => cases h

/-- What `vkind4` accepted of a value that is not an entry value, and what it emits. -/
inductive VK4 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G3. -/
  | g3 {kd : VKind2} : v.op ≠ .ARM64LDP → v.op ≠ .ARM64STP → v.op ≠ .Select0 → v.op ≠ .Select1 →
      VK3 lc g v kd → VK4 lc g v kd
  /-- `LDP off(Rn), (Ra, Rb)`: the address in a 64-bit register, a pair home of two distinct
  registers G1 may write, two components of integer classes of at least 8 bits. -/
  | ldp {rn : Int} {ra rb : Nat} {oa ob : Int} {t0 t1 : Ty} {c0 c1 : Nat} :
      v.op = .ARM64LDP → v.args.size = 2 → v.aux = none → lc.ty v.id = .tuple [t0, t1] →
      cls t0 = some c0 → cls t1 = some c1 → 8 ≤ c0 → 8 ≤ c1 →
      argObj lc v 0 = .ok (64, rn) → memArg lc v 1 = .ok () →
      lc.home v.id = some (.pair (some ra) (some rb)) → ra ≠ rb → ra ≠ zeroReg → rb ≠ zeroReg →
      destOK ra = true → destOK rb = true → objOf? ra = some oa → objOf? rb = some ob →
      VK4 lc g v (.prog (.ofShape { as := .LDP, from_ := memA rn v.auxInt.toInt, to := pairA oa ob }))
  /-- `STP (Rx, Ry), off(Rn)` of two 64-bit registers, the address in a 64-bit register. -/
  | stp {rn rx ry : Int} :
      v.op = .ARM64STP → v.args.size = 4 → v.aux = none → memTy (lc.ty v.id) = true →
      lc.home v.id = none → argObj lc v 0 = .ok (64, rn) → argObj lc v 1 = .ok (64, rx) →
      argObj lc v 2 = .ok (64, ry) → memArg lc v 3 = .ok () →
      VK4 lc g v (.prog (.ofShape { as := .STP, from_ := pairA rx ry, to := memA rn v.auxInt.toInt }))
  /-- `Select0`/`Select1` of an `LDP`, homed in the register of its component: no code. -/
  | sel {c : ID} {u : Value} {ra rb i r : Nat} :
      (v.op = .Select0 ∧ i = 0 ∧ r = ra ∨ v.op = .Select1 ∧ i = 1 ∧ r = rb) →
      v.args.size = 1 → v.args[0]? = some c → lc.ctx.f.value? c = some u → u.op = .ARM64LDP →
      lc.home c = some (.pair (some ra) (some rb)) → lc.home v.id = some (.reg r) →
      (cls (lc.ty v.id)).isSome = true → ((tupleTys (lc.ty c))[i]?.bind cls) = cls (lc.ty v.id) →
      VK4 lc g v .none

private theorem none_of_forall2' {α β : Type} {o : Option (α × β)}
    (h : ∀ a b, o = some (a, b) → False) : o = none := by
  cases o with
  | none => rfl
  | some x => exact (h x.1 x.2 rfl).elim

/-- What `vkind4` accepted of a value that is not an entry value: no temporary, and `VK4`. -/
theorem vkind4_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : vkind4 lc g v = .ok kd)
    (hen : entryOp3 v.op = false) : (lc.temps[v.id]?).join = none ∧ VK4 lc g v kd := by
  have ht : (lc.temps[v.id]?).join = none := by
    by_cases ht : (lc.temps[v.id]?).join = none
    · exact ht
    · unfold vkind4 at h
      simp [ht, ex_throw, ex_bind_error] at h
  refine ⟨ht, ?_⟩
  unfold vkind4 at h
  simp only [ht, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
  split at h
  next hop =>
    obtain ⟨hsz, h⟩ := ex_guard h
    simp only [Bool.and_eq_true, beq_iff_eq] at hsz
    obtain ⟨⟨hsz, hax⟩, hpt⟩ := hsz
    obtain ⟨t0, t1, c0, c1, hty, h0, h1, h80, h81⟩ := pairTys_spec hpt
    obtain ⟨⟨ca, rn⟩, ha, h⟩ := ex_bind_eq_ok h
    obtain ⟨hca, h⟩ := ex_guard h
    simp only [beq_iff_eq] at hca
    subst hca
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
          exact VK4.ldp hop hsz hax hty h0 h1 h80 h81 ha hma (pairHome?_eq hph) hne hza hzb hda hdb
            hoa hob
        next => simp [ex_throw] at h
      next => simp [ex_throw] at h
    next => simp [ex_throw] at h
  next hop =>
    obtain ⟨hsz, h⟩ := ex_guard h
    simp only [Bool.and_eq_true, beq_iff_eq] at hsz
    obtain ⟨⟨⟨hsz, hax⟩, hmt⟩, hhn⟩ := hsz
    obtain ⟨⟨ca, rn⟩, ha, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨cx, rx⟩, hx, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨cy, ry⟩, hy, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
    obtain ⟨hw, h⟩ := ex_guard h
    simp only [Bool.and_eq_true, beq_iff_eq] at hw
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hw
    simp only [ex_pure, Except.ok.injEq] at h
    subst h
    exact VK4.stp hop hsz hax hmt hhn ha hx hy hma
  next hop =>
    split at h
    next c hc =>
      split at h
      next u hu =>
        obtain ⟨hs, h⟩ := ex_guard h
        simp only [Bool.and_eq_true, beq_iff_eq] at hs
        split at h
        next ra rb hph =>
          obtain ⟨hw, h⟩ := ex_guard h
          simp only [Bool.and_eq_true, beq_iff_eq, hop, ↓reduceIte] at hw
          simp only [ex_pure, Except.ok.injEq] at h
          subst h
          exact VK4.sel (.inl ⟨hop, rfl, rfl⟩) hs.1 hc hu hs.2 (pairHome?_eq hph) hw.1.1 hw.1.2 hw.2
        next => simp [ex_throw] at h
      next => simp [ex_throw] at h
    next => simp [ex_throw] at h
  next hop =>
    split at h
    next c hc =>
      split at h
      next u hu =>
        obtain ⟨hs, h⟩ := ex_guard h
        simp only [Bool.and_eq_true, beq_iff_eq] at hs
        split at h
        next ra rb hph =>
          obtain ⟨hw, h⟩ := ex_guard h
          simp only [Bool.and_eq_true, beq_iff_eq, hop, reduceCtorEq, ↓reduceIte] at hw
          simp only [ex_pure, Except.ok.injEq] at h
          subst h
          exact VK4.sel (.inr ⟨hop, rfl, rfl⟩) hs.1 hc hu hs.2 (pairHome?_eq hph) hw.1.1 hw.1.2 hw.2
        next => simp [ex_throw] at h
      next => simp [ex_throw] at h
    next => simp [ex_throw] at h
  next h1 h2 h3 h4 =>
    exact VK4.g3 h1 h2 h3 h4 (vkind3_spec h hen).2

/-- What `checkG4` accepted: G3's facts with G4's value check and homes. -/
theorem checkG4_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (h : checkG4 lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind4 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK4 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab := by
  unfold checkG4 at h
  obtain ⟨hl, h⟩ := ex_guard h
  obtain ⟨tab', hb, h⟩ := ex_bind_eq_ok h
  cases hf : List.find? (fun x => !homeOK4 lc x) (List.range lc.homes.size) with
  | some i =>
    rw [hf] at h
    exact (ex_throw_bind h).elim
  | none =>
    rw [hf] at h
    obtain ⟨⟨⟩, hfr, h⟩ := ex_bind_eq_ok h
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
      unfold homeOK4 homeOK3 homeOK2 homeOK
      rw [hh]

end GoFV.Gen.Check

import GoFV.Gen.Check6
import GoFV.Proof.Gen.Spec5

/-!
# What the genssa validator's slice G6 accepted (`docs/plans/proofs3.md` §4)

`checkG6 lc ps bstart g = .ok (tab, kt)` unfolded into the facts the soundness proof
(`GoFV/Proof/Gen/G6.lean`) uses (`checkG6_spec`): G5's (`Spec5.lean`) with G6's value check
(`vkind6_spec`, `VK6`: G5's values, and the accesses of frame variables, `FrameVarOK` and
`VKVar`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The fields of a Prog a plain pattern accepts. -/
theorem plain_spec {as : As} {f t : Addr → Bool} {w : String} {p : Prog}
    (h : (Pat.mk (plain as f t) w).ok p = true) :
    p.as = as ∧ f p.from_ = true ∧ p.reg = 0 ∧ t p.to = true ∧ p.scond = 0 ∧
      p.rest.isEmpty = true ∧ p.regTo2 = 0 := by
  simp only [plain, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- An access `v` of frame variable `x` at the `NAME_AUTO` operand offset `off` (`frameVar?`): the
aux names a variable whose address the function does not convert to an integer, the first
argument is `SP`, and `off` is the variable's operand offset plus the access's. -/
structure FrameVarOK (lc : LocCtx) (g : G2In) (v : Value) (x : AuxRef) (off : Int) : Prop where
  aux : v.aux = some x
  var : isVar lc x = true
  sp : spArg lc v = true
  op : ∃ o, varOp g x = some (.AUTO, o) ∧ off = o + v.auxInt.toInt
  temp : lc.ctx.tabs.forgeable x = false

theorem frameVar?_spec {lc : LocCtx} {g : G2In} {v : Value} {x : AuxRef} {off : Int}
    (h : frameVar? lc g v = .ok (some (x, off))) : FrameVarOK lc g v x off := by
  unfold frameVar? at h
  split at h
  · cases h
  · rename_i x' hx
    split at h
    · cases h
    · rename_i hv
      split at h
      · cases h
      · rename_i hs
        split at h
        · rename_i o ho
          split at h
          · cases h
          · rename_i hf
            simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            simp only [Bool.not_eq_true', Bool.not_eq_false] at hv hs
            exact ⟨hx, hv, hs, ⟨o, ho, rfl⟩, by simpa using hf⟩
        · cases h
        · cases h

/-- What `vkindVar` accepted of an access at the operand offset `off`, and what it emits. -/
inductive VKVar (lc : LocCtx) (v : Value) (off : Int) : VKind2 → Prop
  /-- `MOVD $off(RSP), Rd`: the variable's address into a 64-bit register. -/
  | addr {rd : Int} : v.op = .ARM64MOVDaddr → v.args.size = 1 → resObj lc v = .ok (64, rd) →
      VKVar lc v off (.prog ⟨plain .MOVD (addrA · off) (· == regA rd), "MOVD $var"⟩)
  /-- A load of `n` bytes at the operand. -/
  | load {as : As} {n : Nat} {sg : Bool} {c : Nat} {rd : Int} :
      loadOp? v.op = some (as, n, sg) → v.args.size = 2 → memArg lc v 1 = .ok () →
      resObj lc v = .ok (c, rd) → (8 ≤ c ∨ c = 1 ∧ n = 1 ∧ sg = false) →
      VKVar lc v off (.prog ⟨plain as (slotA · .AUTO off) (· == regA rd), as.name⟩)
  /-- A store of `n` bytes at the operand. -/
  | store {as : As} {n cs : Nat} {rs : Int} :
      storeOp? v.op = some (as, n) → v.args.size = 3 → memTy (lc.ty v.id) = true →
      lc.home v.id = none → argObj lc v 1 = .ok (cs, rs) → memArg lc v 2 = .ok () →
      (8 * n ≤ cs ∨ cs = 1 ∧ n = 1) →
      VKVar lc v off (.prog ⟨plain as (· == regA rs) (slotA · .AUTO off), as.name⟩)
  /-- `LDP off(RSP), (Ra, Rb)`. -/
  | ldp {ra rb : Nat} {oa ob : Int} {t0 t1 : Ty} {c0 c1 : Nat} :
      v.op = .ARM64LDP → v.args.size = 2 → lc.ty v.id = .tuple [t0, t1] →
      cls t0 = some c0 → cls t1 = some c1 → 8 ≤ c0 → 8 ≤ c1 → memArg lc v 1 = .ok () →
      lc.home v.id = some (.pair (some ra) (some rb)) → ra ≠ rb → ra ≠ zeroReg → rb ≠ zeroReg →
      destOK ra = true → destOK rb = true → objOf? ra = some oa → objOf? rb = some ob →
      VKVar lc v off (.prog ⟨plain .LDP (slotA · .AUTO off) (· == pairA oa ob), "LDP"⟩)
  /-- `STP (Rx, Ry), off(RSP)` of two 64-bit registers. -/
  | stp {rx ry : Int} :
      v.op = .ARM64STP → v.args.size = 4 → memTy (lc.ty v.id) = true → lc.home v.id = none →
      argObj lc v 1 = .ok (64, rx) → argObj lc v 2 = .ok (64, ry) → memArg lc v 3 = .ok () →
      VKVar lc v off (.prog ⟨plain .STP (· == pairA rx ry) (slotA · .AUTO off), "STP"⟩)

theorem vkindVar_spec {lc : LocCtx} {v : Value} {off : Int} {kd : VKind2}
    (h : vkindVar lc v off = .ok kd) : VKVar lc v off kd := by
  unfold vkindVar at h
  split at h
  next hop =>
    simp only [beq_iff_eq] at hop
    obtain ⟨hsz, h⟩ := ex_guard h
    simp only [beq_iff_eq] at hsz
    obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
    obtain ⟨hc, h⟩ := ex_guard h
    simp only [beq_iff_eq] at hc
    subst hc
    simp only [beq_self_eq_true, ↓reduceIte, ex_pure, Except.ok.injEq] at h
    subst h
    exact VKVar.addr hop hsz hro
  next =>
    split at h
    next as n sg hl =>
      obtain ⟨hsz, h⟩ := ex_guard h
      simp only [beq_iff_eq] at hsz
      obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
      obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
      obtain ⟨hc, h⟩ := ex_guard h
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
        Bool.not_eq_true', and_assoc] at hc
      simp only [ex_pure, Except.ok.injEq] at h
      subst h
      exact VKVar.load hl hsz hma hro hc
    next =>
      split at h
      next as n hst =>
        obtain ⟨hsz, h⟩ := ex_guard h
        simp only [Bool.and_eq_true, beq_iff_eq] at hsz
        obtain ⟨⟨hsz, hmt⟩, hhn⟩ := hsz
        obtain ⟨⟨cs, rs⟩, hso, h⟩ := ex_bind_eq_ok h
        obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
        obtain ⟨hc, h⟩ := ex_guard h
        simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at hc
        simp only [ex_pure, Except.ok.injEq] at h
        subst h
        exact VKVar.store hst hsz hmt hhn hso hma hc
      next =>
        split at h
        next hop =>
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
                exact VKVar.ldp hop hsz hty h0 h1 h80 h81 hma (pairHome?_eq hph) hne hza hzb hda
                  hdb hoa hob
              next => simp [ex_throw] at h
            next => simp [ex_throw] at h
          next => simp [ex_throw] at h
        next hop =>
          obtain ⟨hsz, h⟩ := ex_guard h
          simp only [Bool.and_eq_true, beq_iff_eq] at hsz
          obtain ⟨⟨hsz, hmt⟩, hhn⟩ := hsz
          obtain ⟨⟨cx, rx⟩, hx, h⟩ := ex_bind_eq_ok h
          obtain ⟨⟨cy, ry⟩, hy, h⟩ := ex_bind_eq_ok h
          obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
          obtain ⟨hw, h⟩ := ex_guard h
          simp only [Bool.and_eq_true, beq_iff_eq] at hw
          obtain ⟨rfl, rfl⟩ := hw
          simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte, ex_pure, Except.ok.injEq] at h
          subst h
          exact VKVar.stp hop hsz hmt hhn hx hy hma
        next => simp [ex_throw] at h

/-- What `vkind6` accepted of a value that is not an entry value. -/
inductive VK6 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G5. -/
  | g5 {kd : VKind2} : VK5 lc g v kd → VK6 lc g v kd
  /-- An access of frame variable `x` at the operand offset `off`. -/
  | var {x : AuxRef} {off : Int} {kd : VKind2} : FrameVarOK lc g v x off → VKVar lc v off kd →
      VK6 lc g v kd

/-- What `vkind6` accepted of a value that is not an entry value: no temporary, and `VK6`. -/
theorem vkind6_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : vkind6 lc g v = .ok kd)
    (hen : entryOp3 v.op = false) : (lc.temps[v.id]?).join = none ∧ VK6 lc g v kd := by
  unfold vkind6 at h
  split at h
  · obtain ⟨ht, h5⟩ := vkind5_spec h hen
    exact ⟨ht, .g5 h5⟩
  · split at h
    · simp [ex_throw] at h
    · rename_i ht
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at ht
      obtain ⟨o, hf, h⟩ := ex_bind_eq_ok h
      cases o with
      | none =>
        obtain ⟨-, h5⟩ := vkind5_spec h hen
        exact ⟨ht, .g5 h5⟩
      | some xo =>
        obtain ⟨x, off⟩ := xo
        exact ⟨ht, .var (frameVar?_spec hf) (vkindVar_spec h)⟩

/-- What `checkG6` accepted: G5's facts with G6's value check. -/
theorem checkG6_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (h : checkG6 lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind6 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK4 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab := by
  unfold checkG6 at h
  obtain ⟨hl, h⟩ := ex_guard h
  obtain ⟨tab', hb, h⟩ := ex_bind_eq_ok h
  cases hf : List.find? (fun x => !homeOK4 lc x) (List.range lc.homes.size) with
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
      unfold homeOK4 homeOK3 homeOK2 homeOK
      rw [hh]

end GoFV.Gen.Check

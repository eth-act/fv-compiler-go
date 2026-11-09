import GoFV.Gen.Check49
import GoFV.Proof.Gen.Spec51

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `checkG49` accepted (`GoFV/Gen/Check49.lean`)

`VK49`: G51's kinds (`VK51`, through `vkind51`) and the accesses of a frame variable in a
`Blk.local` block at its operand (`FrameVar49OK`, `VKVar49`); on `InitMem`, what `vkind49`
accepts `vkind51` accepts (`vkind49_initMem`). `checkG49L_spec` is `checkG51L_spec` with `vkind49`,
and `checkG49_spec` splits off `refsLive`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- An access `v` of frame variable `x` at the operand of class `nc` and offset `off`
(`frameVar49?`): the aux names a variable whose block is `Blk.local`, the first argument is `SP`,
the operand is `NAME_AUTO` or `NAME_PARAM`, and `off` is the variable's operand offset plus the
access's. -/
structure FrameVar49OK (lc : LocCtx) (g : G2In) (v : Value) (x : AuxRef) (nc : AddrName)
    (off : Int) : Prop where
  aux : v.aux = some x
  var : isVar lc x = true
  sp : spArg lc v = true
  loc : lc.ctx.tabs.forgeable x = true
  cls : nc = .AUTO ∨ nc = .PARAM
  op : ∃ o, varOp g x = some (nc, o) ∧ off = o + v.auxInt.toInt

theorem frameVar49?_spec {lc : LocCtx} {g : G2In} {v : Value} {x : AuxRef} {nc : AddrName}
    {off : Int} (h : frameVar49? lc g v = some (x, nc, off)) : FrameVar49OK lc g v x nc off := by
  unfold frameVar49? at h
  split at h
  · cases h
  · rename_i x' hx
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨hv, hs⟩, hf⟩ := hc
      split at h
      · rename_i o ho
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨hx, hv, hs, hf, .inl rfl, o, ho, rfl⟩
      · rename_i o ho
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨hx, hv, hs, hf, .inr rfl, o, ho, rfl⟩
      · cases h
    · cases h

/-- What `vkindVar49` accepted of an access at the operand `nc`, `off`, and what it emits: G6's
`VKVar` at the operand class `nc`. -/
inductive VKVar49 (lc : LocCtx) (v : Value) (nc : AddrName) (off : Int) : VKind2 → Prop
  /-- `MOVD $off(<nc>), Rd`: the variable's address into a 64-bit register. -/
  | addr {rd : Int} : v.op = .ARM64MOVDaddr → v.args.size = 1 → resObj lc v = .ok (64, rd) →
      VKVar49 lc v nc off (.prog ⟨plain .MOVD (addrN · nc off) (· == regA rd), "MOVD $var"⟩)
  /-- A load of `n` bytes at the operand. -/
  | load {as : As} {n : Nat} {sg : Bool} {c : Nat} {rd : Int} :
      loadOp? v.op = some (as, n, sg) → v.args.size = 2 → memArg lc v 1 = .ok () →
      resObj lc v = .ok (c, rd) → (8 ≤ c ∨ c = 1 ∧ n = 1 ∧ sg = false) →
      VKVar49 lc v nc off (.prog ⟨plain as (slotA · nc off) (· == regA rd), as.name⟩)
  /-- A store of `n` bytes at the operand. -/
  | store {as : As} {n cs : Nat} {rs : Int} :
      storeOp? v.op = some (as, n) → v.args.size = 3 → memTy (lc.ty v.id) = true →
      lc.home v.id = none → argObj lc v 1 = .ok (cs, rs) → memArg lc v 2 = .ok () →
      (8 * n ≤ cs ∨ cs = 1 ∧ n = 1) →
      VKVar49 lc v nc off (.prog ⟨plain as (· == regA rs) (slotA · nc off), as.name⟩)
  /-- `LDP off(<nc>), (Ra, Rb)`. -/
  | ldp {ra rb : Nat} {oa ob : Int} {t0 t1 : Ty} {c0 c1 : Nat} :
      v.op = .ARM64LDP → v.args.size = 2 → lc.ty v.id = .tuple [t0, t1] →
      cls t0 = some c0 → cls t1 = some c1 → 8 ≤ c0 → 8 ≤ c1 → memArg lc v 1 = .ok () →
      lc.home v.id = some (.pair (some ra) (some rb)) → ra ≠ rb → ra ≠ zeroReg → rb ≠ zeroReg →
      destOK ra = true → destOK rb = true → objOf? ra = some oa → objOf? rb = some ob →
      VKVar49 lc v nc off (.prog ⟨plain .LDP (slotA · nc off) (· == pairA oa ob), "LDP"⟩)
  /-- `STP (Rx, Ry), off(<nc>)` of two 64-bit registers. -/
  | stp {rx ry : Int} :
      v.op = .ARM64STP → v.args.size = 4 → memTy (lc.ty v.id) = true → lc.home v.id = none →
      argObj lc v 1 = .ok (64, rx) → argObj lc v 2 = .ok (64, ry) → memArg lc v 3 = .ok () →
      VKVar49 lc v nc off (.prog ⟨plain .STP (· == pairA rx ry) (slotA · nc off), "STP"⟩)

theorem vkindVar49_spec {lc : LocCtx} {v : Value} {nc : AddrName} {off : Int} {kd : VKind2}
    (h : vkindVar49 lc v nc off = .ok kd) : VKVar49 lc v nc off kd := by
  unfold vkindVar49 at h
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
    exact VKVar49.addr hop hsz hro
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
      exact VKVar49.load hl hsz hma hro hc
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
        exact VKVar49.store hst hsz hmt hhn hso hma hc
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
                exact VKVar49.ldp hop hsz hty h0 h1 h80 h81 hma (pairHome?_eq hph) hne hza hzb
                  hda hdb hoa hob
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
          exact VKVar49.stp hop hsz hmt hhn hx hy hma
        next => simp [ex_throw] at h

/-- What `vkind49` accepted of a value that is not an entry value, and what it emits. -/
inductive VK49 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G51. -/
  | g51 {kd : VKind2} : VK51 lc g v kd → VK49 lc g v kd
  /-- An access of frame variable `x` (a `Blk.local` block) at the operand `nc`, `off`. -/
  | var {x : AuxRef} {nc : AddrName} {off : Int} {kd : VKind2} :
      FrameVar49OK lc g v x nc off → VKVar49 lc v nc off kd → VK49 lc g v kd

/-- What `vkind49` accepted of a value that is not an entry value: no temporary, and `VK49`. -/
theorem vkind49_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind49 lc g v = .ok kd) (hen : entryOp24 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK49 lc g v kd := by
  unfold vkind49 at h
  cases h51 : vkind51 lc g v with
  | ok kd' =>
    rw [h51] at h
    cases h
    obtain ⟨ht, hVK⟩ := vkind51_spec h51 hen
    exact ⟨ht, .g51 hVK⟩
  | error e =>
    rw [h51] at h
    simp only at h
    split at h
    · rename_i x nc off hf
      split at h
      · cases h
      · rename_i ht
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at ht
        exact ⟨ht, .var (frameVar49?_spec hf) (vkindVar49_spec h)⟩
    · cases h

/-- On `InitMem`, what `vkind49` accepts `vkind51` accepts. -/
theorem vkind49_initMem {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (hop : v.op = .InitMem)
    (h : vkind49 lc g v = .ok kd) : vkind51 lc g v = .ok kd := by
  unfold vkind49 at h
  cases h51 : vkind51 lc g v with
  | ok _ => rw [h51] at h; exact h
  | error e =>
    rw [h51] at h
    simp only at h
    split at h
    · split at h
      · cases h
      · cases vkindVar49_spec h with
        | addr h' => rw [hop] at h'; cases h'
        | load h' => rw [hop] at h'; cases h'
        | store h' => rw [hop] at h'; cases h'
        | ldp h' => rw [hop] at h'; cases h'
        | stp h' => rw [hop] at h'; cases h'
    · cases h

/-- On a value that is no access of a frame variable in a `Blk.local` block (`frameVar49?`), for
instance one with no aux, `vkind49` is `vkind51`. -/
theorem vkind49_eq51 {lc : LocCtx} {g : G2In} {v : Value} (h : frameVar49? lc g v = none) :
    vkind49 lc g v = vkind51 lc g v := by
  unfold vkind49
  cases vkind51 lc g v with
  | ok _ => rfl
  | error e => simp only [h]

/-- A value with no aux is no access of a frame variable. -/
theorem frameVar49?_none {lc : LocCtx} {g : G2In} {v : Value} (h : v.aux = none) :
    frameVar49? lc g v = none := by
  unfold frameVar49?; rw [h]

/-- On an op that is none of G49's accesses (`MOVDaddr`, a load or store of G3, `LDP`, `STP`),
what `vkind49` accepts `vkind51` accepts. -/
theorem vkind49_ok51 {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h1 : v.op ≠ .ARM64MOVDaddr) (h2 : loadOp? v.op = none) (h3 : storeOp? v.op = none)
    (h4 : v.op ≠ .ARM64LDP) (h5 : v.op ≠ .ARM64STP) (h : vkind49 lc g v = .ok kd) :
    vkind51 lc g v = .ok kd := by
  unfold vkind49 at h
  cases h51 : vkind51 lc g v with
  | ok _ => rw [h51] at h; exact h
  | error e =>
    rw [h51] at h
    simp only at h
    split at h
    · split at h
      · cases h
      · cases vkindVar49_spec h with
        | addr h' => exact absurd h' h1
        | load h' => rw [h2] at h'; cases h'
        | store h' => rw [h3] at h'; cases h'
        | ldp h' => exact absurd h' h4
        | stp h' => exact absurd h' h5
    · cases h

/-- On a function with no arm64 op, G49's check is G33. -/
theorem checkG33_of_49L {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG49L lc ps bstart g = r) : checkG33 lc ps bstart g = r := by
  simpa [checkG33, checkG49L, hl] using h

/-- What `checkG49L` accepted of a function with an arm64 op: G51's facts with G49's value
check. -/
theorem checkG49L_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG49L lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind49 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK35 lc = true ∧ uEdgesOK35 lc = true := by
  simp only [checkG49L, hl, ↓reduceIte] at h
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

/-- What `checkG49` accepted: `refsLive`, and `checkG49L` on `liveCtx`. -/
theorem checkG49_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : PcTab × KTab} (h : checkG49 lc ps bstart g = .ok r) :
    refsLive lc = true ∧ checkG49L (liveCtx lc) ps bstart g = .ok r := by
  unfold checkG49 at h
  cases hr : refsLive lc with
  | false => simp [hr] at h; cases h
  | true => simp only [hr] at h; exact ⟨rfl, by simpa using h⟩

end GoFV.Gen.Check

import GoFV.Gen.Check50
import GoFV.Proof.Gen.Spec47

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `checkG50` accepted (`GoFV/Gen/Check50.lean`)

`VK50`: G47's kinds (`VK47`, through `vkind47`) and G50's pair loads into X registers (`ldpX`:
`LDPW`, `LDPSW`) and V registers (`ldpF`: `FLDPD`, `FLDPS`) and the selects of their components
(`selX`, `selF`); `pairOp50_cases` lists the four pair loads. On `InitMem`, `vkind50` is
`vkind47` (`vkind50_initMem`). `checkG50L_spec` is `checkG47L_spec` with `vkind50`, and
`checkG50_spec` splits off `refsLive`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind50` accepted of a value that is not an entry value, and what it emits. -/
inductive VK50 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G47. -/
  | g47 {kd : VKind2} : VK47 lc g v kd → VK50 lc g v kd
  /-- `LDPW`/`LDPSW off(Rn), (Ra, Rb)`: the address in a 64-bit register, a pair home of two
  distinct X registers G1 may write, two components of integer classes of at least 8 bits. -/
  | ldpX {as : As} {n : Nat} {sg : Bool} {rn : Int} {ra rb : Nat} {oa ob : Int} {t0 t1 : Ty}
      {c0 c1 : Nat} :
      pairOp50 v.op = some (as, n, sg, false) → v.args.size = 2 → v.aux = none →
      lc.ty v.id = .tuple [t0, t1] → cls t0 = some c0 → cls t1 = some c1 → 8 ≤ c0 → 8 ≤ c1 →
      argObj lc v 0 = .ok (64, rn) → memArg lc v 1 = .ok () →
      lc.home v.id = some (.pair (some ra) (some rb)) → ra ≠ rb → ra ≠ zeroReg → rb ≠ zeroReg →
      destOK ra = true → destOK rb = true → objOf? ra = some oa → objOf? rb = some ob →
      VK50 lc g v (.prog (.ofShape { as, from_ := memA rn v.auxInt.toInt, to := pairA oa ob }))
  /-- `FLDPD`/`FLDPS off(Rn), (Fa, Fb)` of `n`-byte elements: the address in a 64-bit register, a
  pair home of two distinct V registers, two float shapes of class `8n`. -/
  | ldpF {as : As} {n : Nat} {sg : Bool} {rn : Int} {ra rb : Nat} {oa ob : Int} {t0 t1 : Ty} :
      pairOp50 v.op = some (as, n, sg, true) → v.args.size = 2 → v.aux = none →
      lc.ty v.id = .tuple [t0, t1] → fTy t0 = true → fTy t1 = true → cls t0 = some (8 * n) →
      cls t1 = some (8 * n) → argObj lc v 0 = .ok (64, rn) → memArg lc v 1 = .ok () →
      lc.home v.id = some (.pair (some ra) (some rb)) → ra ≠ rb →
      fobjOf? ra = some oa → fobjOf? rb = some ob →
      VK50 lc g v (.prog (.ofShape { as, from_ := memA rn v.auxInt.toInt, to := pairA oa ob }))
  /-- `Select0`/`Select1` of an `LDPW`/`LDPSW`, homed in the X register of its component, a
  register G1 may write: no code. -/
  | selX {c : ID} {u : Value} {as : As} {n : Nat} {sg : Bool} {ra rb i r : Nat} :
      (v.op = .Select0 ∧ i = 0 ∧ r = ra ∨ v.op = .Select1 ∧ i = 1 ∧ r = rb) →
      v.args.size = 1 → v.args[0]? = some c → lc.ctx.f.value? c = some u →
      pairOp50 u.op = some (as, n, sg, false) → pairTys (lc.ty c) = true →
      lc.home c = some (.pair (some ra) (some rb)) → lc.home v.id = some (.reg r) →
      r ≠ zeroReg → destOK r = true → (objOf? r).isSome = true →
      (cls (lc.ty v.id)).isSome = true → ((tupleTys (lc.ty c))[i]?.bind cls) = cls (lc.ty v.id) →
      VK50 lc g v .none
  /-- `Select0`/`Select1` of an `FLDPD`/`FLDPS`, homed in the V register of its component, at a
  float shape: no code. -/
  | selF {c : ID} {u : Value} {as : As} {n : Nat} {sg : Bool} {ra rb i r : Nat} :
      (v.op = .Select0 ∧ i = 0 ∧ r = ra ∨ v.op = .Select1 ∧ i = 1 ∧ r = rb) →
      v.args.size = 1 → v.args[0]? = some c → lc.ctx.f.value? c = some u →
      pairOp50 u.op = some (as, n, sg, true) → fpairTys (lc.ty c) n = true →
      lc.home c = some (.pair (some ra) (some rb)) → lc.home v.id = some (.reg r) →
      (cls (lc.ty v.id)).isSome = true → ((tupleTys (lc.ty c))[i]?.bind cls) = cls (lc.ty v.id) →
      (fobjOf? r).isSome = true → fTy (lc.ty v.id) = true →
      VK50 lc g v .none

/-- The four pair loads of G50. -/
theorem pairOp50_cases {op : Op} {as : As} {n : Nat} {sg fp : Bool}
    (h : pairOp50 op = some (as, n, sg, fp)) :
    (op = .ARM64LDPW ∧ as = .LDPW ∧ n = 4 ∧ sg = false ∧ fp = false) ∨
      (op = .ARM64LDPSW ∧ as = .LDPSW ∧ n = 4 ∧ sg = true ∧ fp = false) ∨
      (op = .ARM64FLDPD ∧ as = .FLDPD ∧ n = 8 ∧ sg = false ∧ fp = true) ∨
      (op = .ARM64FLDPS ∧ as = .FLDPS ∧ n = 4 ∧ sg = false ∧ fp = true) := by
  unfold pairOp50 at h
  split at h
  next h1 =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact .inl ⟨h1, rfl, rfl, rfl, rfl⟩
  next =>
    split at h
    next h1 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact .inr (.inl ⟨h1, rfl, rfl, rfl, rfl⟩)
    next =>
      split at h
      next h1 =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        exact .inr (.inr (.inl ⟨h1, rfl, rfl, rfl, rfl⟩))
      next =>
        split at h
        next h1 =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact .inr (.inr (.inr ⟨h1, rfl, rfl, rfl, rfl⟩))
        next => cases h

/-- What `fpairTys` accepted: two float shapes of class `8n`. -/
theorem fpairTys_spec {t : Ty} {n : Nat} (h : fpairTys t n = true) :
    ∃ t0 t1, t = .tuple [t0, t1] ∧ fTy t0 = true ∧ fTy t1 = true ∧ cls t0 = some (8 * n) ∧
      cls t1 = some (8 * n) := by
  unfold fpairTys at h
  split at h
  next t0 t1 =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    exact ⟨t0, t1, rfl, h1, h2, h3, h4⟩
  next => cases h

/-- What `ldp50` accepted: no temporary, and `VK50.ldpX` or `VK50.ldpF`. -/
theorem ldp50_spec {lc : LocCtx} {g : G2In} {v : Value} {as : As} {n : Nat} {sg fp : Bool}
    {kd : VKind2} (hop : pairOp50 v.op = some (as, n, sg, fp)) (h : ldp50 lc v as n fp = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK50 lc g v kd := by
  unfold ldp50 at h
  obtain ⟨ht, h⟩ := ex_guard h
  simp only [beq_iff_eq] at ht
  refine ⟨ht, ?_⟩
  obtain ⟨hsz, h⟩ := ex_guard h
  simp only [Bool.and_eq_true, beq_iff_eq] at hsz
  obtain ⟨⟨hsz, hax⟩, hty⟩ := hsz
  obtain ⟨⟨ca, rn⟩, ha, h⟩ := ex_bind_eq_ok h
  obtain ⟨hca, h⟩ := ex_guard h
  simp only [beq_iff_eq] at hca
  subst hca
  obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
  split at h
  next ra rb hph =>
    obtain ⟨hne, h⟩ := ex_guard h
    simp only [bne_iff_ne, ne_eq] at hne
    cases fp with
    | true =>
      simp only [↓reduceIte] at hty h
      obtain ⟨t0, t1, hty, hf0, hf1, h0, h1⟩ := fpairTys_spec hty
      split at h
      next oa hoa =>
        split at h
        next ob hob =>
          simp only [ex_pure, Except.ok.injEq] at h
          subst h
          exact VK50.ldpF hop hsz hax hty hf0 hf1 h0 h1 ha hma (pairHome?_eq hph) hne hoa hob
        next => simp [ex_throw] at h
      next => simp [ex_throw] at h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hty h
      obtain ⟨t0, t1, c0, c1, hty, h0, h1, h80, h81⟩ := pairTys_spec hty
      obtain ⟨hr, h⟩ := ex_guard h
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hr
      obtain ⟨⟨⟨hza, hzb⟩, hda⟩, hdb⟩ := hr
      split at h
      next oa hoa =>
        split at h
        next ob hob =>
          simp only [ex_pure, Except.ok.injEq] at h
          subst h
          exact VK50.ldpX hop hsz hax hty h0 h1 h80 h81 ha hma (pairHome?_eq hph) hne hza hzb hda
            hdb hoa hob
        next => simp [ex_throw] at h
      next => simp [ex_throw] at h
  next => simp [ex_throw] at h

/-- What `sel50` accepted: no temporary, and `VK50.selX` or `VK50.selF`. -/
theorem sel50_spec {lc : LocCtx} {g : G2In} {v : Value} {c : ID} {u : Value} {as : As} {n : Nat}
    {sg fp : Bool} {kd : VKind2} (hop : v.op = .Select0 ∨ v.op = .Select1)
    (hc0 : v.args[0]? = some c) (hu : lc.ctx.f.value? c = some u)
    (hpo : pairOp50 u.op = some (as, n, sg, fp)) (h : sel50 lc v c n fp = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK50 lc g v kd := by
  unfold sel50 at h
  obtain ⟨ht, h⟩ := ex_guard h
  simp only [beq_iff_eq] at ht
  refine ⟨ht, ?_⟩
  obtain ⟨hs, h⟩ := ex_guard h
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨hsz, hty⟩ := hs
  split at h
  next ra rb hph =>
    have hhc := pairHome?_eq hph
    obtain ⟨hw, h⟩ := ex_guard h
    simp only [Bool.and_eq_true, beq_iff_eq] at hw
    obtain ⟨⟨hvh, hcs⟩, hcl⟩ := hw
    have hsel : (v.op = .Select0 ∧ (if v.op = .Select0 then 0 else 1) = 0 ∧
        (if v.op = .Select0 then ra else rb) = ra) ∨
        (v.op = .Select1 ∧ (if v.op = .Select0 then 0 else 1) = 1 ∧
        (if v.op = .Select0 then ra else rb) = rb) := by
      rcases hop with hop | hop
      · exact .inl ⟨hop, by simp [hop], by simp [hop]⟩
      · exact .inr ⟨hop, by simp [hop], by simp [hop]⟩
    cases fp with
    | true =>
      simp only [↓reduceIte] at hty h
      obtain ⟨hf, h⟩ := ex_guard h
      simp only [Bool.and_eq_true, beq_iff_eq] at hf
      simp only [ex_pure, Except.ok.injEq] at h
      subst h
      exact VK50.selF hsel hsz hc0 hu hpo hty hhc hvh hcs hcl hf.1 hf.2
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hty h
      obtain ⟨hw, h⟩ := ex_guard h
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hw
      obtain ⟨⟨hrz, hd⟩, hob⟩ := hw
      simp only [ex_pure, Except.ok.injEq] at h
      subst h
      exact VK50.selX hsel hsz hc0 hu hpo hty hhc hvh hrz hd hob hcs hcl
  next => simp [ex_throw] at h

/-- What `pair50` accepted: no temporary, and one of `VK50`'s pair loads or selects. -/
theorem pair50_spec {lc : LocCtx} {g : G2In} {v : Value} {e : String} {kd : VKind2}
    (h : pair50 lc v e = .ok kd) : (lc.temps[v.id]?).join = none ∧ VK50 lc g v kd := by
  unfold pair50 at h
  split at h
  next as n sg fp hpo => exact ldp50_spec hpo h
  next =>
    split at h
    next hop =>
      split at h
      next c hc0 =>
        split at h
        next as n sg fp hpo =>
          obtain ⟨u, hu, hpo'⟩ := Option.bind_eq_some_iff.1 hpo
          exact sel50_spec hop hc0 hu hpo' h
        next => cases h
      next => cases h
    next => cases h

/-- What `vkind50` accepted of a value that is not an entry value: no temporary, and `VK50`. -/
theorem vkind50_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind50 lc g v = .ok kd) (hen : entryOp24 v.op = false) :
    (lc.temps[v.id]?).join = none ∧ VK50 lc g v kd := by
  unfold vkind50 at h
  cases h47 : vkind47 lc g v with
  | ok kd' =>
    rw [h47] at h
    cases h
    obtain ⟨ht, hVK⟩ := vkind47_spec h47 hen
    exact ⟨ht, .g47 hVK⟩
  | error e =>
    rw [h47] at h
    exact pair50_spec h

/-- On `InitMem`, `vkind50` is `vkind47`. -/
theorem vkind50_initMem {lc : LocCtx} {g : G2In} {v : Value} (hop : v.op = .InitMem) :
    vkind50 lc g v = vkind47 lc g v := by
  unfold vkind50
  cases vkind47 lc g v with
  | ok _ => rfl
  | error e => simp [pair50, pairOp50, hop]

/-- On an op that is neither a G50 pair load nor `Select0`/`Select1`, `vkind50` is `vkind47`. -/
theorem vkind50_eq47 {lc : LocCtx} {g : G2In} {v : Value} (h1 : pairOp50 v.op = none)
    (h2 : v.op ≠ .Select0) (h3 : v.op ≠ .Select1) : vkind50 lc g v = vkind47 lc g v := by
  unfold vkind50
  cases vkind47 lc g v with
  | ok _ => rfl
  | error e => simp [pair50, h1, h2, h3]

/-- On a function with no arm64 op, G50's check is G33. -/
theorem checkG33_of_50L {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG50L lc ps bstart g = r) : checkG33 lc ps bstart g = r := by
  simpa [checkG33, checkG50L, hl] using h

/-- What `checkG50L` accepted of a function with an arm64 op: G47's facts with G50's value
check. -/
theorem checkG50L_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG50L lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind50 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK35 lc = true ∧ uEdgesOK35 lc = true := by
  simp only [checkG50L, hl, ↓reduceIte] at h
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

/-- What `checkG50` accepted: `refsLive`, and G50's check on the context without the removed
homes. -/
theorem checkG50_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : PcTab × KTab} (h : checkG50 lc ps bstart g = .ok r) :
    refsLive lc = true ∧ checkG50L (liveCtx lc) ps bstart g = .ok r := by
  unfold checkG50 at h
  cases hr : refsLive lc with
  | false => simp [hr] at h; cases h
  | true => simp only [hr] at h; exact ⟨rfl, by simpa using h⟩

end GoFV.Gen.Check

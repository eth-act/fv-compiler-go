import GoFV.Gen.Check64
import GoFV.Proof.Gen.Spec63
import GoFV.Proof.Gen.Spec57b

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `checkG64` accepted (`GoFV/Gen/Check64.lean`)

`VK64`: G63's kinds (`VK63`), or a 128-bit move: `FMOVQload` (`VK64.qload`), `FMOVQstore`
(`VK64.qstore`), `FLDPQ` (`VK64.qldp`), `FSTPQ` (`VK64.qstp`), a select of an `FLDPQ`
(`VK64.qsel`). Their memory operand is `QAccessOK`: a frame variable's (`FVar57`) or G3's
(`AccessOK`). On `InitMem`, `vkind64` is `vkind63` (`vkind64_initMem`). `checkG64L_spec` is
`checkG63L_spec` with `vkind64`, and `checkG64_spec` splits off `refsLive`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The memory operands a 128-bit access `v` may name, as `qaccessA` accepted them: a frame
variable's operand (`FVar57`), or G3's (`AccessOK`). -/
inductive QAccessOK (lc : LocCtx) (g : G2In) (v : Value) : (Addr → Prop) → Prop
  /-- `off(<nc>)` of a frame variable (G49's `Blk.local` or G6's `Blk.temp` block). -/
  | frame {nc : AddrName} {off : Int} : FVar57 lc g v nc off →
      QAccessOK lc g v (fun A => slotA A nc off = true)
  /-- `off(Rn)` or `sym+off(SB)` (`accessA`). -/
  | acc {P : Addr → Prop} : AccessOK lc g v P → QAccessOK lc g v P

/-- What `qaccessA` accepted: a `QAccessOK` form that every accepted operand has. -/
theorem qaccessA_spec {lc : LocCtx} {g : G2In} {v : Value} {src : Addr → Bool}
    (h : qaccessA lc g v = .ok src) : ∃ P, QAccessOK lc g v P ∧ ∀ A, src A = true → P A := by
  unfold qaccessA at h
  split at h
  · rename_i nc off hfv
    cases h
    exact ⟨_, .frame (fvar57?_spec hfv), fun _ hA => hA⟩
  · obtain ⟨P, hP, hPs⟩ := accessA_spec h
    exact ⟨P, .acc hP, hPs⟩

/-- What `qresObj` accepted: the value's `F` register home at the blob shape. -/
theorem qresObj_spec {lc : LocCtx} {v : Value} {o : Int} (h : qresObj lc v = .ok o) :
    ∃ r, lc.home v.id = some (.reg r) ∧ fobjOf? r = some o ∧ lc.ty v.id = .blob 16 := by
  unfold qresObj at h
  cases hr : regHome? lc v.id with
  | none => simp [hr, ex_throw] at h
  | some r =>
    cases ho : fobjOf? r with
    | none => simp [hr, ho, ex_throw] at h
    | some o' =>
      cases hb : blob16 (lc.ty v.id) with
      | false => simp [hr, ho, hb, ex_throw] at h <;> cases h
      | true =>
        simp only [hr, ho, hb, ex_pure, ↓reduceIte, Except.ok.injEq] at h
        subst h
        exact ⟨r, regHome?_eq.mp hr, ho, blob16_eq hb⟩

/-- What `qargObj` accepted: argument `i` in an `F` register at the blob shape. -/
theorem qargObj_spec {lc : LocCtx} {v : Value} {i : Nat} {o : Int} (h : qargObj lc v i = .ok o) :
    ∃ a r, v.args[i]? = some a ∧ lc.home a = some (.reg r) ∧ fobjOf? r = some o ∧
      lc.ty a = .blob 16 := by
  unfold qargObj at h
  cases ha : v.args[i]? with
  | none => simp [ha, ex_throw] at h
  | some a =>
    cases hr : regHome? lc a with
    | none => simp [ha, hr, ex_throw] at h
    | some r =>
      cases ho : fobjOf? r with
      | none => simp [ha, hr, ho, ex_throw] at h
      | some o' =>
        cases hb : blob16 (lc.ty a) with
        | false => simp [ha, hr, ho, hb, ex_throw] at h <;> cases h
        | true =>
          simp only [ha, hr, ho, hb, ex_pure, ↓reduceIte, Except.ok.injEq] at h
          subst h
          exact ⟨a, r, rfl, regHome?_eq.mp hr, ho, blob16_eq hb⟩

/-- `FLDPQ`'s pair shape: two 16-byte blobs. -/
theorem qpairTy_spec {t : Ty} (h : qpairTy t = true) : t = .tuple [.blob 16, .blob 16] := by
  unfold qpairTy at h
  split at h
  · simp only [Bool.and_eq_true] at h
    rw [blob16_eq h.1, blob16_eq h.2]
  · cases h

/-- What `vkind64` accepted of a value that is not an entry value. -/
inductive VK64 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G63. -/
  | g63 {kd : VKind2} : VK63 lc g v kd → VK64 lc g v kd
  /-- `FMOVQload`: `FMOVQ src, Fd`. -/
  | qload {rd : Int} {src : Addr → Bool} (htemp : (lc.temps[v.id]?).join = none)
      (hop : v.op = .ARM64FMOVQload) (hsz2 : v.args.size = 2) (hro : qresObj lc v = .ok rd)
      (hma : memArg lc v 1 = .ok ()) (hacc : qaccessA lc g v = .ok src) :
      VK64 lc g v (.prog ⟨plain .FMOVQ src (· == regA rd), "FMOVQ load"⟩)
  /-- `FMOVQstore`: `FMOVQ Fs, dst`. -/
  | qstore {rs : Int} {dst : Addr → Bool} (htemp : (lc.temps[v.id]?).join = none)
      (hop : v.op = .ARM64FMOVQstore) (hsz3 : v.args.size = 3) (hmt : memTy (lc.ty v.id) = true)
      (hhn : lc.home v.id = none) (hso : qargObj lc v 1 = .ok rs) (hma : memArg lc v 2 = .ok ())
      (hacc : qaccessA lc g v = .ok dst) :
      VK64 lc g v (.prog ⟨plain .FMOVQ (· == regA rs) dst, "FMOVQ store"⟩)
  /-- `FLDPQ`: `FLDPQ src, (Fa, Fb)`. -/
  | qldp {ra rb : Nat} {oa ob : Int} {src : Addr → Bool} (htemp : (lc.temps[v.id]?).join = none)
      (hop : v.op = .ARM64FLDPQ) (hsz2 : v.args.size = 2) (hpt : qpairTy (lc.ty v.id) = true)
      (hma : memArg lc v 1 = .ok ()) (hh : lc.home v.id = some (.pair (some ra) (some rb)))
      (hne : ra ≠ rb) (hoa : fobjOf? ra = some oa) (hob : fobjOf? rb = some ob)
      (hacc : qaccessA lc g v = .ok src) :
      VK64 lc g v (.prog ⟨plain .FLDPQ src (· == pairA oa ob), "FLDPQ"⟩)
  /-- `FSTPQ`: `FSTPQ (Fx, Fy), dst`. -/
  | qstp {rx ry : Int} {dst : Addr → Bool} (htemp : (lc.temps[v.id]?).join = none)
      (hop : v.op = .ARM64FSTPQ) (hsz4 : v.args.size = 4) (hmt : memTy (lc.ty v.id) = true)
      (hhn : lc.home v.id = none) (hxo : qargObj lc v 1 = .ok rx) (hyo : qargObj lc v 2 = .ok ry)
      (hma : memArg lc v 3 = .ok ()) (hacc : qaccessA lc g v = .ok dst) :
      VK64 lc g v (.prog ⟨plain .FSTPQ (· == pairA rx ry) dst, "FSTPQ"⟩)
  /-- A select of an `FLDPQ`, homed in the register of its component: no code. -/
  | qsel {c : ID} {u : Value} {ra rb r : Nat} (htemp : (lc.temps[v.id]?).join = none)
      (hop : v.op = .Select0 ∧ r = ra ∨ v.op = .Select1 ∧ r = rb) (hsz1 : v.args.size = 1)
      (hc0 : v.args[0]? = some c) (hu : lc.ctx.f.value? c = some u) (huop : u.op = .ARM64FLDPQ)
      (hpt : qpairTy (lc.ty c) = true) (hhc : lc.home c = some (.pair (some ra) (some rb)))
      (hvh : lc.home v.id = some (.reg r)) (hfo : (fobjOf? r).isSome = true)
      (hbt : blob16 (lc.ty v.id) = true) :
      VK64 lc g v .none

/-- What `qkind64` accepted. -/
theorem qkind64_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : qkind64 lc g v = .ok kd) : VK64 lc g v kd := by
  unfold qkind64 at h
  obtain ⟨ht, h⟩ := ex_guard h
  have htemp : (lc.temps[v.id]?).join = none := by simpa using ht
  split at h
  next hop =>
    obtain ⟨hsz, h⟩ := ex_guard h
    obtain ⟨rd, hro, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
    obtain ⟨src, hacc, h⟩ := ex_bind_eq_ok h
    cases h
    exact .qload htemp hop (by simpa using hsz) hro hma hacc
  next hop =>
    obtain ⟨hsz, h⟩ := ex_guard h
    simp only [Bool.and_eq_true, beq_iff_eq] at hsz
    obtain ⟨rs, hso, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
    obtain ⟨dst, hacc, h⟩ := ex_bind_eq_ok h
    cases h
    exact .qstore htemp hop hsz.1.1 hsz.1.2 hsz.2 hso hma hacc
  next hop =>
    obtain ⟨hsz, h⟩ := ex_guard h
    simp only [Bool.and_eq_true, beq_iff_eq] at hsz
    obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
    split at h
    · rename_i ra rb hph
      obtain ⟨hne, h⟩ := ex_guard h
      split at h
      · rename_i oa hoa
        split at h
        · rename_i ob hob
          obtain ⟨src, hacc, h⟩ := ex_bind_eq_ok h
          cases h
          have hh : lc.home v.id = some (.pair (some ra) (some rb)) := by
            unfold pairHome? at hph
            split at hph
            · cases hph; assumption
            · cases hph
          exact .qldp htemp hop hsz.1 hsz.2 hma hh (by simpa using hne) hoa hob hacc
        · first | exact (ex_throw_bind h).elim | simp [ex_throw] at h
      · first | exact (ex_throw_bind h).elim | simp [ex_throw] at h
    · first | exact (ex_throw_bind h).elim | simp [ex_throw] at h
  next hop =>
    obtain ⟨hsz, h⟩ := ex_guard h
    simp only [Bool.and_eq_true, beq_iff_eq] at hsz
    obtain ⟨rx, hxo, h⟩ := ex_bind_eq_ok h
    obtain ⟨ry, hyo, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨⟩, hma, h⟩ := ex_bind_eq_ok h
    obtain ⟨dst, hacc, h⟩ := ex_bind_eq_ok h
    cases h
    exact .qstp htemp hop hsz.1.1 hsz.1.2 hsz.2 hxo hyo hma hacc
  next hop =>
    split at h
    · rename_i c hc0
      split at h
      · rename_i u hu
        obtain ⟨hsz, h⟩ := ex_guard h
        simp only [Bool.and_eq_true, beq_iff_eq] at hsz
        split at h
        · rename_i ra rb hph
          obtain ⟨hhv, h⟩ := ex_guard h
          simp only [Bool.and_eq_true, beq_iff_eq] at hhv
          cases h
          have hh : lc.home c = some (.pair (some ra) (some rb)) := by
            unfold pairHome? at hph
            split at hph
            · cases hph; assumption
            · cases hph
          refine .qsel htemp ?_ hsz.1.1 hc0 hu hsz.1.2 hsz.2 hh hhv.1.1 hhv.1.2 hhv.2
          exact .inl ⟨hop, by rw [hop]; rfl⟩
        · simp [ex_throw] at h
      · simp [ex_throw] at h
    · simp [ex_throw] at h
  next hop =>
    split at h
    · rename_i c hc0
      split at h
      · rename_i u hu
        obtain ⟨hsz, h⟩ := ex_guard h
        simp only [Bool.and_eq_true, beq_iff_eq] at hsz
        split at h
        · rename_i ra rb hph
          obtain ⟨hhv, h⟩ := ex_guard h
          simp only [Bool.and_eq_true, beq_iff_eq] at hhv
          cases h
          have hh : lc.home c = some (.pair (some ra) (some rb)) := by
            unfold pairHome? at hph
            split at hph
            · cases hph; assumption
            · cases hph
          refine .qsel htemp ?_ hsz.1.1 hc0 hu hsz.1.2 hsz.2 hh hhv.1.1 hhv.1.2 hhv.2
          exact .inr ⟨hop, by rw [hop]; rfl⟩
        · simp [ex_throw] at h
      · simp [ex_throw] at h
    · simp [ex_throw] at h
  next => simp [ex_throw] at h

/-- What `vkind64` accepted of a value that is not an entry value. -/
theorem vkind64_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind64 lc g v = .ok kd) (hen : entryOp24 v.op = false) : VK64 lc g v kd := by
  unfold vkind64 at h
  cases h63 : vkind63 lc g v with
  | ok kd' =>
    rw [h63] at h
    cases h
    exact .g63 (vkind63_spec h63 hen)
  | error e =>
    rw [h63] at h
    simp only at h
    unfold vkind64a at h
    by_cases hq : qop64 v.op = true
    · simp only [hq, ↓reduceIte] at h
      cases hk : qkind64 lc g v with
      | ok kd' =>
        rw [hk] at h
        cases h
        exact qkind64_spec hk
      | error e' =>
        rw [hk] at h
        cases h
    · simp only [hq, Bool.false_eq_true, ↓reduceIte] at h
      cases h

/-- On `InitMem`, `vkind64` is `vkind63`. -/
theorem vkind64_initMem {lc : LocCtx} {g : G2In} {v : Value} (hop : v.op = .InitMem) :
    vkind64 lc g v = vkind63 lc g v := by
  have hn : vkind64a lc g v = none := by simp [vkind64a, qop64, hop]
  unfold vkind64
  cases vkind63 lc g v <;> simp [hn]

/-- Off G64's ops (`qop64`), `vkind64` is `vkind63`. -/
theorem vkind64_eq63 {lc : LocCtx} {g : G2In} {v : Value} (hq : qop64 v.op = false) :
    vkind64 lc g v = vkind63 lc g v := by
  have hn : vkind64a lc g v = none := by simp [vkind64a, hq]
  unfold vkind64
  cases vkind63 lc g v <;> simp [hn]

/-- On a function with no arm64 op, G64's check is G33. -/
theorem checkG33_of_64L {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG64L lc ps bstart g = r) : checkG33 lc ps bstart g = r := by
  simpa [checkG33, checkG64L, hl] using h

/-- What `checkG64L` accepted of a function with an arm64 op: G63's facts with G64's value check. -/
theorem checkG64L_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG64L lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind64 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK35 lc = true ∧ uEdgesOK35 lc = true ∧ loopOK lc ps tab = true ∧
      spHomes48 lc = true ∧ atomOK lc ps tab = true := by
  simp only [checkG64L, hl, ↓reduceIte] at h
  obtain ⟨tab', hb, h⟩ := ex_bind_eq_ok h
  obtain ⟨hpb, h⟩ := ex_guard h
  obtain ⟨hlp, h⟩ := ex_guard h
  obtain ⟨hat, h⟩ := ex_guard h
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
      hsph, hat⟩
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

/-- What `checkG64` accepted: `refsLive`, and `checkG64L` on `liveCtx`. -/
theorem checkG64_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : PcTab × KTab} (h : checkG64 lc ps bstart g = .ok r) :
    refsLive lc = true ∧ checkG64L (liveCtx lc) ps bstart g = .ok r := by
  unfold checkG64 at h
  cases hr : refsLive lc with
  | false => simp [hr] at h; cases h
  | true => simp only [hr] at h; exact ⟨rfl, by simpa using h⟩

end GoFV.Gen.Check

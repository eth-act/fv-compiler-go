import GoFV.Gen.Check66
import GoFV.Proof.Gen.Spec65

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `checkG66` accepted (`GoFV/Gen/Check66.lean`)

`VK66`: G65's kinds (`VK65`), a narrow spill (`VK66.nspill`: `MOVB`/`MOVH`/`MOVW Rs, off(RSP)`), a
narrow reload (`VK66.nreload`: `loadByType`'s `MOV{B,H,W}{,U} off(RSP), Rd`), a `float32` spill or
reload (`VK66.fspill`, `VK66.freload`: `FMOVS`), an incoming stack argument of any class
(`VK66.narg`) and (slice G66b) an extension genssa elides (`VK66.elideSame`: no code;
`VK66.elideMov`: `MOVD Rx, Rv`). On `InitMem`, `vkind66` is `vkind65` (`vkind66_initMem`).
`checkG66L_spec` is `checkG65L_spec` with `vkind66` and `elideOK66b`, and `checkG66_spec` splits
off `refsLive`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind66` accepted of a value that is not an entry value. -/
inductive VK66 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G65. -/
  | g65 {kd : VKind2} : VK65 lc g v kd → VK66 lc g v kd
  /-- A narrow spill of `n` bytes: `MOVB`/`MOVH`/`MOVW Rs, off(RSP)`. -/
  | nspill {k : SlotKey} {nc : AddrName} {off : Int} {rs : Int} {n c : Nat}
      (htemp : (lc.temps[v.id]?).join = none) (hop : v.op = .StoreReg)
      (hn : narrowBytes lc v.type = some n) (hh : lc.home v.id = some (.slot k))
      (hso : g.slotOp k = some (nc, off)) (hsz : v.args.size = 1) (hts : (lc.ty v.id).size = n)
      (hao : argObj lc v 0 = .ok (c, rs)) (hcv : cls (lc.ty v.id) = some c) :
      VK66 lc g v (.prog ⟨plain (nstoreAs n) (· == regA rs) (slotA · nc off), "narrow spill"⟩)
  /-- A narrow reload of `n` bytes: `loadByType`'s load by the value's signedness. -/
  | nreload {a : ID} {k : SlotKey} {nc : AddrName} {off : Int} {rd : Int} {n c : Nat}
      (htemp : (lc.temps[v.id]?).join = none) (hop : v.op = .LoadReg)
      (hn : narrowBytes lc v.type = some n) (hsz : v.args.size = 1) (ha : v.args[0]? = some a)
      (hah : lc.home a = some (.slot k)) (hso : g.slotOp k = some (nc, off))
      (hta : (lc.ty a).size = n) (hca : cls (lc.ty a) = cls (lc.ty v.id))
      (hro : resObj lc v = .ok (c, rd)) :
      VK66 lc g v (.prog ⟨plain (nloadAs n (typeSigned lc.ctx.tabs v.type)) (slotA · nc off)
        (· == regA rd), "narrow reload"⟩)
  /-- A `float32` spill: `FMOVS Fs, off(RSP)`. -/
  | fspill {k : SlotKey} {nc : AddrName} {off : Int} {rs : Int}
      (htemp : (lc.temps[v.id]?).join = none) (hop : v.op = .StoreReg)
      (hh : lc.home v.id = some (.slot k)) (hso : g.slotOp k = some (nc, off))
      (hsz : v.args.size = 1) (hft : fTy (lc.ty v.id) = true) (hcv : cls (lc.ty v.id) = some 32)
      (hao : fargObj lc v 0 = .ok (32, rs)) :
      VK66 lc g v (.prog ⟨plain .FMOVS (· == regA rs) (slotA · nc off), "FMOVS spill"⟩)
  /-- A `float32` reload: `FMOVS off(RSP), Fd`. -/
  | freload {a : ID} {k : SlotKey} {nc : AddrName} {off : Int} {rd : Int}
      (htemp : (lc.temps[v.id]?).join = none) (hop : v.op = .LoadReg) (hsz : v.args.size = 1)
      (ha : v.args[0]? = some a) (hah : lc.home a = some (.slot k))
      (hso : g.slotOp k = some (nc, off)) (hca : cls (lc.ty a) = some 32)
      (hro : fresObj lc v = .ok (32, rd)) :
      VK66 lc g v (.prog ⟨plain .FMOVS (slotA · nc off) (· == regA rd), "FMOVS reload"⟩)
  /-- An `Arg` of an incoming stack argument of class `c`: no code. -/
  | narg {x : AuxRef} {o : Int} {c : Nat} (htemp : (lc.temps[v.id]?).join = none)
      (hop : v.op = .Arg) (hsz : v.args.size = 0) (hx : v.aux = some x)
      (hsp : stackParam lc x = true) (hcv : cls (lc.ty v.id) = some c)
      (hh : lc.home v.id = some (.slot (argKey x v.type v.auxInt.toInt)))
      (hso : g.slotOp (argKey x v.type v.auxInt.toInt) = some (.PARAM, o)) : VK66 lc g v .none
  /-- An extension genssa elides (`elide66b`), of a value in its own register: no code. -/
  | elideSame {as : As} {w ca c : Nat} {sg : Bool} {r : Int}
      (htemp : (lc.temps[v.id]?).join = none) (hel : elide66b lc v = some (w, sg))
      (he : extOp? v.op = some (as, w, sg)) (hsz : v.args.size = 1)
      (hao : argObj lc v 0 = .ok (ca, r)) (hro : resObj lc v = .ok (c, r))
      (hw : w ≤ ca ∨ ca = 1) (h8 : 8 ≤ c) : VK66 lc g v .none
  /-- An extension genssa elides (`elide66b`), of a value in another register: `MOVD Rx, Rv`. -/
  | elideMov {as : As} {w ca c : Nat} {sg : Bool} {rn rd : Int}
      (htemp : (lc.temps[v.id]?).join = none) (hel : elide66b lc v = some (w, sg))
      (he : extOp? v.op = some (as, w, sg)) (hsz : v.args.size = 1)
      (hao : argObj lc v 0 = .ok (ca, rn)) (hro : resObj lc v = .ok (c, rd))
      (hw : w ≤ ca ∨ ca = 1) (h8 : 8 ≤ c) :
      VK66 lc g v (.prog (.ofShape { as := .MOVD, from_ := regA rn, to := regA rd }))

/-- `elide66b` gave the width and signedness of an extension (`extOp?`). -/
theorem elide66b_ext {lc : LocCtx} {v : Value} {w : Nat} {sg : Bool}
    (h : elide66b lc v = some (w, sg)) : ∃ as, extOp? v.op = some (as, w, sg) := by
  unfold elide66b at h
  split at h
  · rename_i as w' sg' a he ha
    split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨as, he⟩
      · cases h
    · cases h
  · cases h

/-- No extension, no `elide66b`. -/
theorem elide66b_none {lc : LocCtx} {v : Value} (h : extOp? v.op = none) : elide66b lc v = none := by
  simp [elide66b, h]

section Helpers

variable {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} {e : String}

private theorem nspill66_spec (hop : v.op = .StoreReg) (h : nspill66 lc g v e = .ok kd) :
    VK66 lc g v kd := by
  unfold nspill66 at h
  obtain ⟨-, h⟩ := ex_guard h
  split at h
  · rename_i n hn
    obtain ⟨ht, h⟩ := ex_guard h
    split at h
    · rename_i k hk
      split at h
      · rename_i nc off hso
        obtain ⟨hsz, h⟩ := ex_guard h
        simp only [Bool.and_eq_true, beq_iff_eq] at hsz
        obtain ⟨⟨c, rs⟩, hao, h⟩ := ex_bind_eq_ok h
        obtain ⟨hc, h⟩ := ex_guard h
        simp only [beq_iff_eq] at hc
        cases h
        exact .nspill (by simpa using ht) hop hn (slotHome?_eq.mp hk) hso hsz.1 hsz.2 hao hc
      · first | exact (ex_throw_bind h).elim | simp [ex_throw] at h
    · first | exact (ex_throw_bind h).elim | simp [ex_throw] at h
  · first | exact (ex_throw_bind h).elim | simp [ex_throw] at h

private theorem nreload66_spec (hop : v.op = .LoadReg) (h : nreload66 lc g v e = .ok kd) :
    VK66 lc g v kd := by
  unfold nreload66 at h
  obtain ⟨-, h⟩ := ex_guard h
  split at h
  · rename_i n hn
    obtain ⟨ht, h⟩ := ex_guard h
    split at h
    · rename_i a ha
      split at h
      · rename_i k hk
        split at h
        · rename_i nc off hso
          obtain ⟨hsz, h⟩ := ex_guard h
          simp only [Bool.and_eq_true, beq_iff_eq] at hsz
          obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
          cases h
          exact .nreload (by simpa using ht) hop hn hsz.1.1 ha (slotHome?_eq.mp hk) hso hsz.1.2
            hsz.2 hro
        · first | exact (ex_throw_bind h).elim | simp [ex_throw] at h
      · first | exact (ex_throw_bind h).elim | simp [ex_throw] at h
    · first | exact (ex_throw_bind h).elim | simp [ex_throw] at h
  · first | exact (ex_throw_bind h).elim | simp [ex_throw] at h

private theorem fspill66_spec (hop : v.op = .StoreReg) (h : fspill66 lc g v e = .ok kd) :
    VK66 lc g v kd := by
  unfold fspill66 at h
  obtain ⟨-, h⟩ := ex_guard h
  obtain ⟨ht, h⟩ := ex_guard h
  split at h
  · rename_i k hk
    split at h
    · rename_i nc off hso
      obtain ⟨hsz, h⟩ := ex_guard h
      simp only [Bool.and_eq_true, beq_iff_eq] at hsz
      obtain ⟨⟨c, rs⟩, hao, h⟩ := ex_bind_eq_ok h
      obtain ⟨hc, h⟩ := ex_guard h
      simp only [beq_iff_eq] at hc
      subst hc
      cases h
      exact .fspill (by simpa using ht) hop (slotHome?_eq.mp hk) hso hsz.1.1 hsz.1.2 hsz.2 hao
    · first | exact (ex_throw_bind h).elim | simp [ex_throw] at h
  · first | exact (ex_throw_bind h).elim | simp [ex_throw] at h

private theorem freload66_spec (hop : v.op = .LoadReg) (h : freload66 lc g v e = .ok kd) :
    VK66 lc g v kd := by
  unfold freload66 at h
  obtain ⟨-, h⟩ := ex_guard h
  obtain ⟨ht, h⟩ := ex_guard h
  split at h
  · rename_i a ha
    split at h
    · rename_i k hk
      split at h
      · rename_i nc off hso
        obtain ⟨hsz, h⟩ := ex_guard h
        simp only [Bool.and_eq_true, beq_iff_eq] at hsz
        obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
        obtain ⟨hc, h⟩ := ex_guard h
        simp only [beq_iff_eq] at hc
        subst hc
        cases h
        exact .freload (by simpa using ht) hop hsz.1 ha (slotHome?_eq.mp hk) hso hsz.2 hro
      · first | exact (ex_throw_bind h).elim | simp [ex_throw] at h
    · first | exact (ex_throw_bind h).elim | simp [ex_throw] at h
  · first | exact (ex_throw_bind h).elim | simp [ex_throw] at h

private theorem argKind66_spec (hop : v.op = .Arg) (h : argKind66 lc g v = .ok kd) :
    VK66 lc g v kd := by
  unfold argKind66 at h
  obtain ⟨ht, h⟩ := ex_guard h
  obtain ⟨hsz, h⟩ := ex_guard h
  split at h
  · rename_i x hx
    obtain ⟨hsp, h⟩ := ex_guard h
    obtain ⟨hcv, h⟩ := ex_guard h
    obtain ⟨hh, h⟩ := ex_guard h
    split at h
    · rename_i o hso
      cases h
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hcv
      exact .narg (by simpa using ht) hop (by simpa using hsz) hx hsp hc (by simpa using hh) hso
    · simp [ex_throw] at h
  · first | exact (ex_throw_bind h).elim | simp [ex_throw] at h

private theorem extElide66b_spec {w : Nat} {sg : Bool} (hel : elide66b lc v = some (w, sg))
    (h : extElide66b lc v = .ok kd) : VK66 lc g v kd := by
  obtain ⟨as, he⟩ := elide66b_ext hel
  unfold extElide66b at h
  obtain ⟨ht, h⟩ := ex_guard h
  rw [he] at h
  simp only at h
  obtain ⟨hsz, h⟩ := ex_guard h
  obtain ⟨⟨ca, rn⟩, hao, h⟩ := ex_bind_eq_ok h
  obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
  obtain ⟨hwc, h⟩ := ex_guard h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hwc
  simp only at h
  split at h
  · rename_i hrr
    obtain rfl : kd = .none := (Except.ok.inj h).symm
    have hr : rn = rd := by simpa using hrr
    rw [← hr] at hro
    exact .elideSame (by simpa using ht) hel he (by simpa using hsz) hao hro hwc.1 hwc.2
  · obtain rfl := (Except.ok.inj h).symm
    exact .elideMov (by simpa using ht) hel he (by simpa using hsz) hao hro hwc.1 hwc.2

end Helpers

/-- What `vkind66a` accepted. -/
theorem vkind66a_spec {lc : LocCtx} {g : G2In} {v : Value} {e : String} {kd : VKind2}
    {r : Except String VKind2} (hr : vkind66a lc g v e = some r) (h : r = .ok kd) :
    VK66 lc g v kd := by
  subst h
  by_cases hs : v.op = .StoreReg
  · by_cases hf : ((v.args[0]?).bind (regHome? lc) |>.bind fobjOf?).isSome = true
    · have he : vkind66a lc g v e = some (fspill66 lc g v e) := by simp [vkind66a, hs, hf]
      rw [he, Option.some.injEq] at hr
      exact fspill66_spec hs hr
    · have he : vkind66a lc g v e = some (nspill66 lc g v e) := by simp [vkind66a, hs, hf]
      rw [he, Option.some.injEq] at hr
      exact nspill66_spec hs hr
  · by_cases hl : v.op = .LoadReg
    · by_cases hf : ((regHome? lc v.id).bind fobjOf?).isSome = true
      · have he : vkind66a lc g v e = some (freload66 lc g v e) := by simp [vkind66a, hl, hf]
        rw [he, Option.some.injEq] at hr
        exact freload66_spec hl hr
      · have he : vkind66a lc g v e = some (nreload66 lc g v e) := by simp [vkind66a, hl, hf]
        rw [he, Option.some.injEq] at hr
        exact nreload66_spec hl hr
    · by_cases ha : v.op = .Arg
      · have he : vkind66a lc g v e = some (argKind66 lc g v) := by simp [vkind66a, hs, hl, ha]
        rw [he, Option.some.injEq] at hr
        exact argKind66_spec ha hr
      · have he : vkind66a lc g v e = none := by simp [vkind66a, hs, hl, ha]
        rw [he] at hr
        cases hr

/-- What `vkind66` accepted of a value that is not an entry value. -/
theorem vkind66_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind66 lc g v = .ok kd) (hen : entryOp24 v.op = false) : VK66 lc g v kd := by
  unfold vkind66 at h
  split at h
  · rename_i hel
    obtain ⟨⟨w, sg⟩, hel'⟩ := Option.isSome_iff_exists.mp hel
    exact extElide66b_spec hel' h
  cases h65 : vkind65 lc g v with
  | ok kd' =>
    rw [h65] at h
    cases h
    exact .g65 (vkind65_spec h65 hen)
  | error e =>
    rw [h65] at h
    simp only at h
    cases ha : vkind66a lc g v e with
    | none => rw [ha] at h; cases h
    | some r => rw [ha] at h; exact vkind66a_spec ha h

/-- Off `StoreReg`, `LoadReg` and `Arg`, `vkind66a` gives nothing. -/
theorem vkind66a_none {lc : LocCtx} {g : G2In} {v : Value} {e : String} (hs : v.op ≠ .StoreReg)
    (hl : v.op ≠ .LoadReg) (ha : v.op ≠ .Arg) : vkind66a lc g v e = none := by
  simp [vkind66a, hs, hl, ha]

/-- On `InitMem`, `vkind66` is `vkind65`. -/
theorem vkind66_initMem {lc : LocCtx} {g : G2In} {v : Value} (hop : v.op = .InitMem) :
    vkind66 lc g v = vkind65 lc g v := by
  have hn : ∀ e, vkind66a lc g v e = none := fun _ =>
    vkind66a_none (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
  have he : elide66b lc v = none := elide66b_none (by rw [hop]; rfl)
  unfold vkind66
  simp only [he, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  cases vkind65 lc g v <;> simp [hn]

/-- On a function with no arm64 op, G66's check is G33. -/
theorem checkG33_of_66L {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG66L lc ps bstart g = r) : checkG33 lc ps bstart g = r := by
  simpa [checkG33, checkG66L, hl] using h

/-- What `checkG66L` accepted of a function with an arm64 op: G65's facts with G66's value check
and `elideOK66b`. -/
theorem checkG66L_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG66L lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind66 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK35 lc = true ∧ uEdgesOK35 lc = true ∧ loopOK lc ps tab = true ∧
      spHomes48 lc = true ∧ atomOK lc ps tab = true ∧ elideOK66b lc = true := by
  simp only [checkG66L, hl, ↓reduceIte] at h
  obtain ⟨tab', hb, h⟩ := ex_bind_eq_ok h
  obtain ⟨hpb, h⟩ := ex_guard h
  obtain ⟨hlp, h⟩ := ex_guard h
  obtain ⟨hat, h⟩ := ex_guard h
  obtain ⟨hmovd, h⟩ := ex_guard h
  simp only [Bool.and_eq_true] at hmovd
  obtain ⟨hel, h⟩ := ex_guard h
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
      hsph, hat, hel⟩
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

/-- What `checkG66` accepted: `refsLive`, and `checkG66L` on `liveCtx`. -/
theorem checkG66_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : PcTab × KTab} (h : checkG66 lc ps bstart g = .ok r) :
    refsLive lc = true ∧ checkG66L (liveCtx lc) ps bstart g = .ok r := by
  unfold checkG66 at h
  cases hr : refsLive lc with
  | false => simp [hr] at h; cases h
  | true => simp only [hr] at h; exact ⟨rfl, by simpa using h⟩

end GoFV.Gen.Check

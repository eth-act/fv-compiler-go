import GoFV.Proof.Obj.Entry49

variable [GoFV.SSA.Sem.Addrs]

/-!
# The values the entry stores come after (`entrySkip`, `GoFV/Gen/Entry49.lean`)

Between the entry values and the entry stores genssa may place spills and values without code;
`storesFrom` steps over them (`entrySkip`: a `StoreReg` or `SB` without an aux, `SP`, `InitMem`,
in a function with an arm64 op). The whole-function simulation runs them against the memory
related but for the pending windows `W` (`Whole.lean`, `sim_entrySkip`), so `g66L_entrySkip` is
`g66L_entryStore`'s statement for them: from a relation on `{m with mem := M0}`, `M0` agreeing
with `m.mem` outside `W`, the value's Prog runs `m` to `m'` (the X registers kept) with a relation
on `{m' with mem := M'}`, `M'` agreeing with `m'.mem` outside `W`.

What `checkG66L` accepted of such a value: `vkind66` of `SP` or `SB` is `vkind64`'s
(`vkind66_eq65`, `vkind65_eq64`), and of a `StoreReg` `vkind64`'s or G66's `float32` or narrow
spill (`vkind66_spill64`: a `StoreReg` is no extension and no op of G65's); `vkind64` of a
`StoreReg`, `SP` or `SB` is `vkind28`'s or, for a `StoreReg`, G63's float spill (`vkind64_skip28`:
no op of G38's–G64's groups, and G48's `kind48` takes no call and no access off `SP`); `vkind28`
of `SP` is `vkind24`'s (`vkind28_eq24`), and of a `StoreReg` or `SB` without an aux `vkind3`'s
(`vkind28_ok3`: no op of G4's–G28's groups, and `frameVar?` is `none` without an aux). So the
value is G2's spill (`g2_spillW`), G63's float spill (`g63_fspillW`), G66's `float32` or narrow
spill (`g66_fspillW`, `g66_nspillW`), G24's `SP` (`g24_spW`), G3's `SB` (`g3_sbW`) or `InitMem`
(as `g66L_initMem`, at a clean position, `MemAt`): the spills write their slot in both memories
alike, the others run no code.

None of them panics (`stepLoc_entrySkip_ne_panic`): a `StoreReg` moves its argument, and `SP`,
`SB`, `InitMem` are generic ops that are no call and no nil check (`evalOpL_panic_op`).
-/

namespace GoFV.Proof.Obj

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64
open GoFV.Proof.Gen

/-! ## What `checkG66L` accepted of a skipped value -/

/-- What `vkind28` accepted of a `StoreReg` or `SB` without an aux, `vkind3` accepted: it is no
op of G4's–G28's groups, and `frameVar?` is `none` without an aux. -/
theorem vkind28_ok3 {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (hop : v.op = .StoreReg ∨ v.op = .SB) (hx : v.aux = none) (h : vkind28 lc g v = .ok kd) :
    vkind3 lc g v = .ok kd := by
  have h1 : logSh? v.op = none := by rcases hop with h | h <;> rw [h] <;> rfl
  have h2 : (Cond.ofOp v.op).isSome = false := by rcases hop with h | h <;> rw [h] <;> rfl
  have h3 : globPair lc v = false := by
    unfold globPair; rcases hop with h | h <;> rw [h] <;> rfl
  have h4 : pbOp v.op = false := by rcases hop with h | h <;> rw [h] <;> rfl
  have h5 : storeIdxOp? v.op = none := by rcases hop with h | h <;> rw [h] <;> rfl
  have h6 : loadIdxOp? v.op = none := by rcases hop with h | h <;> rw [h] <;> rfl
  have h7 : icallLead v.op = none := by rcases hop with h | h <;> rw [h] <;> rfl
  have h8 : markOp? v.op = none := by rcases hop with h | h <;> rw [h] <;> rfl
  have hfv : frameVar? lc g v = .ok none := by simp [frameVar?, hx]
  by_cases ht : (lc.temps[v.id]?).join = none
  · rcases hop with hop | hop <;>
    · simp only [vkind28, vkind27, vkind25, vkind24, vkind23, vkind22, vkind21, vkind20, vkind19,
        vkind18, vkind17, vkind16, vkind15, vkind14, vkind13, vkind12, vkind11, vkind10, vkind9,
        vkind8, vkind7, vkind6, vkind5, vkind4, h1, h2, h3, h4, h5, h6, h7, h8, hfv, ht]
        at h
      simp only [hop] at h
      exact h
  · exfalso
    rcases hop with hop | hop <;>
    · simp only [vkind28, vkind27, vkind25, vkind24, vkind23, vkind22, vkind21, vkind20, vkind19,
        vkind18, vkind17, vkind16, vkind15, vkind14, vkind13, vkind12, vkind11, vkind10, vkind9,
        vkind8, vkind7, vkind6, h1, h2, h3, h4, h5, h6, h7, h8] at h
      simp [hop] at h
      exact ht h.1

/-- `vkind28` of `SP` is `vkind24`'s. -/
theorem vkind28_eq24 {lc : LocCtx} {g : G2In} {v : Value} (hop : v.op = .SP) :
    vkind28 lc g v = vkind24 lc g v := by
  have h1 : logSh? v.op = none := by rw [hop]; rfl
  simp only [vkind28, vkind27, vkind25, h1]
  simp [hop]

/-- What `vkind64` accepted of a `StoreReg`, `SP` or `SB`, `vkind28` accepted, or, of a
`StoreReg`, G63's float spill: it is no op of G38's–G64's groups, and G48's `kind48` takes no call
and no access off `SP` (`VKsp48.ops`). -/
theorem vkind64_skip28 {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (hop : v.op = .StoreReg ∨ v.op = .SP ∨ v.op = .SB) (h : vkind64 lc g v = .ok kd) :
    vkind28 lc g v = .ok kd ∨ v.op = .StoreReg ∧ ∃ e, fspill63 lc g v e = .ok kd := by
  rw [vkind64_eq63 (by rcases hop with h | h | h <;> rw [h] <;> rfl)] at h
  have hint : vkind62 lc g v = .ok kd → vkind28 lc g v = .ok kd := fun h62 => by
    rw [vkind62_eq61 (by rcases hop with h | h | h <;> rw [h] <;> decide),
      vkind61_eq60 (by rcases hop with h | h | h <;> rw [h] <;> rfl)] at h62
    rcases vkind60_ok49 (by rcases hop with h | h | h <;> rw [h] <;> rfl)
      (by rcases hop with h | h | h <;> rw [h] <;> rfl)
      (by rcases hop with h | h | h <;> rw [h] <;> rfl)
      (by rcases hop with h | h | h <;> rw [h] <;> rfl)
      (by rcases hop with h | h | h <;> rw [h] <;> rfl)
      (by rcases hop with h | h | h <;> rw [h] <;> rfl)
      (by rcases hop with h | h | h <;> rw [h] <;> rfl)
      (by rcases hop with h | h | h <;> rw [h] <;> rfl)
      (by rcases hop with h | h | h <;> rw [h] <;> rfl)
      (by rcases hop with h | h | h <;> rw [h] <;> rfl) h62 with h49 | ⟨e, h48⟩
    · have h51 := vkind49_ok51 (by rcases hop with h | h | h <;> rw [h] <;> decide)
        (by rcases hop with h | h | h <;> rw [h] <;> rfl)
        (by rcases hop with h | h | h <;> rw [h] <;> rfl)
        (by rcases hop with h | h | h <;> rw [h] <;> decide)
        (by rcases hop with h | h | h <;> rw [h] <;> decide) h49
      rw [vkind51_eq50 (by rcases hop with h | h | h <;> rw [h] <;> rfl)
          (by rcases hop with h | h | h <;> rw [h] <;> rfl)
          (by rcases hop with h | h | h <;> rw [h] <;> rfl),
        vkind50_eq47 (by rcases hop with h | h | h <;> rw [h] <;> rfl)
          (by rcases hop with h | h | h <;> rw [h] <;> decide)
          (by rcases hop with h | h | h <;> rw [h] <;> decide),
        vkind47_eq46 (by rcases hop with h | h | h <;> rw [h] <;> decide)
          (by rcases hop with h | h | h <;> rw [h] <;> rfl)
          (by rcases hop with h | h | h <;> rw [h] <;> decide),
        vkind46_eq45 (by rcases hop with h | h | h <;> rw [h] <;> simp [fops46]),
        vkind45_eq44 (by rcases hop with h | h | h <;> rw [h] <;> rfl)
          (by rcases hop with h | h | h <;> rw [h] <;> rfl),
        vkind44_eq43 (by rcases hop with h | h | h <;> rw [h] <;> rfl),
        vkind43_eq42 (by rcases hop with h | h | h <;> rw [h] <;> decide),
        vkind42_eq41 (by rcases hop with h | h | h <;> rw [h] <;> decide),
        vkind41_eq40 (by rcases hop with h | h | h <;> rw [h] <;> decide)
          (by rcases hop with h | h | h <;> rw [h] <;> rfl),
        vkind40_eq38 (by rcases hop with h | h | h <;> rw [h] <;> decide),
        vkind38_eq28 (by rcases hop with h | h | h <;> rw [h] <;> rfl)
          (by rcases hop with h | h | h <;> rw [h] <;> decide)
          (by rcases hop with h | h | h <;> rw [h] <;> decide)
          (by rcases hop with h | h | h <;> rw [h] <;> decide)
          (by rcases hop with h | h | h <;> rw [h] <;> rfl)
          (by rcases hop with h | h | h <;> rw [h] <;> rfl)
          (by rcases hop with h | h | h <;> rw [h] <;> rfl)
          (by rcases hop with h | h | h <;> rw [h] <;> rfl)
          (by rcases hop with h | h | h <;> rw [h] <;> decide)
          (by rcases hop with h | h | h <;> rw [h] <;> rfl)
          (by rcases hop with h | h | h <;> rw [h] <;> rfl)
          (by rcases hop with h | h | h <;> rw [h] <;> decide)
          (by rcases hop with h | h | h <;> rw [h] <;> rfl)
          (by rcases hop with h | h | h <;> rw [h] <;> rfl)
          (by rcases hop with h | h | h <;> rw [h] <;> rfl)
          (by rcases hop with h | h | h <;> rw [h] <;> rfl)
          (by rcases hop with h | h | h <;> rw [h] <;> decide)
          (by rcases hop with h | h | h <;> rw [h] <;> rfl)
          (by rcases hop with h | h | h <;> rw [h] <;> decide)
          (by rcases hop with h | h | h <;> rw [h] <;> decide)] at h51
      exact h51
    · exfalso
      rcases kind48_cases h48 with ⟨hc, -⟩ | ⟨-, -, -, -, hsk⟩
      · rcases hop with h | h | h <;> rw [h] at hc <;> cases hc
      · have hl0 : loadOp? v.op = none := by rcases hop with h | h | h <;> rw [h] <;> rfl
        have hs0 : storeOp? v.op = none := by rcases hop with h | h | h <;> rw [h] <;> rfl
        rcases (spKind48_spec hsk).ops with ⟨x, hx⟩ | ⟨x, hx⟩ | ho | ho | ho | ho | ho | ho | ho
        · rw [hl0] at hx; cases hx
        · rw [hs0] at hx; cases hx
        all_goals rcases hop with h | h | h <;> rw [h] at ho <;> cases ho
  rcases hop with hop | hop | hop
  · unfold vkind63 at h
    cases h62 : vkind62 lc g v with
    | ok kd' =>
      rw [h62] at h
      cases h
      exact .inl (hint h62)
    | error e =>
      rw [h62] at h
      simp only [vkind63a, hop, beq_self_eq_true, ↓reduceIte] at h
      exact .inr ⟨hop, e, h⟩
  · rw [vkind63_eq62 (by rw [hop]; decide) (by rw [hop]; decide)] at h
    exact .inl (hint h)
  · rw [vkind63_eq62 (by rw [hop]; decide) (by rw [hop]; decide)] at h
    exact .inl (hint h)

/-- What `fspill63` accepted: `VK63.fspill`'s facts. -/
theorem fspill63_ok {lc : LocCtx} {g : G2In} {v : Value} {e : String} {kd : VKind2}
    (h : fspill63 lc g v e = .ok kd) :
    ∃ k nc off rs, (lc.temps[v.id]?).join = none ∧ lc.home v.id = some (.slot k) ∧
      g.slotOp k = some (nc, off) ∧ v.args.size = 1 ∧ fTy (lc.ty v.id) = true ∧
      cls (lc.ty v.id) = some 64 ∧ fargObj lc v 0 = .ok (64, rs) ∧
      kd = .prog ⟨plain .FMOVD (· == regA rs) (slotA · nc off), "FMOVD spill"⟩ := by
  unfold fspill63 at h
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
      refine ⟨k, nc, off, rs, by simpa using ht, ?_, hso, hsz.1.1, hsz.1.2, hsz.2, hao, rfl⟩
      unfold slotHome? at hk
      split at hk <;> simp_all
    · simp at h
  · simp at h

/-- What `fspill66` accepted: `VK66.fspill`'s facts. -/
theorem fspill66_ok {lc : LocCtx} {g : G2In} {v : Value} {e : String} {kd : VKind2}
    (h : fspill66 lc g v e = .ok kd) :
    ∃ k nc off rs, (lc.temps[v.id]?).join = none ∧ lc.home v.id = some (.slot k) ∧
      g.slotOp k = some (nc, off) ∧ v.args.size = 1 ∧ fTy (lc.ty v.id) = true ∧
      cls (lc.ty v.id) = some 32 ∧ fargObj lc v 0 = .ok (32, rs) ∧
      kd = .prog ⟨plain .FMOVS (· == regA rs) (slotA · nc off), "FMOVS spill"⟩ := by
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
      refine ⟨k, nc, off, rs, by simpa using ht, ?_, hso, hsz.1.1, hsz.1.2, hsz.2, hao, rfl⟩
      unfold slotHome? at hk
      split at hk <;> simp_all
    · simp at h
  · simp at h

/-- What `nspill66` accepted: `VK66.nspill`'s facts. -/
theorem nspill66_ok {lc : LocCtx} {g : G2In} {v : Value} {e : String} {kd : VKind2}
    (h : nspill66 lc g v e = .ok kd) :
    ∃ k nc off rs n c, (lc.temps[v.id]?).join = none ∧ narrowBytes lc v.type = some n ∧
      lc.home v.id = some (.slot k) ∧ g.slotOp k = some (nc, off) ∧ v.args.size = 1 ∧
      (lc.ty v.id).size = n ∧ argObj lc v 0 = .ok (c, rs) ∧ cls (lc.ty v.id) = some c ∧
      kd = .prog ⟨plain (nstoreAs n) (· == regA rs) (slotA · nc off), "narrow spill"⟩ := by
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
        refine ⟨k, nc, off, rs, n, c, by simpa using ht, hn, ?_, hso, hsz.1, hsz.2, hao, hc, rfl⟩
        unfold slotHome? at hk
        split at hk <;> simp_all
      · first | exact (ex_throw_bind h).elim | simp [ex_throw] at h
    · first | exact (ex_throw_bind h).elim | simp [ex_throw] at h
  · first | exact (ex_throw_bind h).elim | simp [ex_throw] at h

/-- What `vkind66` accepted of a `StoreReg`, `vkind64` accepted, or G66's `float32` spill
(`fspill66`) or narrow spill (`nspill66`): a `StoreReg` is no extension (`elide66b` is `none`)
and no op of G65's (`vkind65_eq64`). -/
theorem vkind66_spill64 {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (hop : v.op = .StoreReg) (h : vkind66 lc g v = .ok kd) :
    vkind64 lc g v = .ok kd ∨ ∃ e, fspill66 lc g v e = .ok kd ∨ nspill66 lc g v e = .ok kd := by
  have he : elide66b lc v = none := elide66b_none (by rw [hop]; rfl)
  unfold vkind66 at h
  simp only [he, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at h
  cases h65 : vkind65 lc g v with
  | ok kd' =>
    rw [h65] at h
    cases h
    rw [vkind65_eq64 (by rw [hop]; rfl)] at h65
    exact .inl h65
  | error e =>
    rw [h65] at h
    simp only at h
    refine .inr ⟨e, ?_⟩
    by_cases hf : ((v.args[0]?).bind (regHome? lc) |>.bind fobjOf?).isSome = true
    · have ha : vkind66a lc g v e = some (fspill66 lc g v e) := by simp [vkind66a, hop, hf]
      rw [ha] at h
      exact .inl h
    · have ha : vkind66a lc g v e = some (nspill66 lc g v e) := by simp [vkind66a, hop, hf]
      rw [ha] at h
      exact .inr h

/-- The values `entrySkip` takes. -/
theorem entrySkip_cases {lc : LocCtx} {v : Value} (h : entrySkip lc v = true) :
    lc.ctx.f.lowered = true ∧ (v.op = .SP ∨ v.op = .InitMem ∨
      v.aux = none ∧ (v.op = .StoreReg ∨ v.op = .SB)) := by
  simpa [entrySkip, or_assoc] using h

/-! ## A skipped value against a memory related but for some bytes -/

/-- **A value the entry stores come after (`entrySkip`), against a memory related but for some
bytes**: `g66L_entryStore`'s statement. From a relation on `{m with mem := M0}`, `M0` agreeing with
`m`'s memory outside `W`, a value `entrySkip` takes that `checkG66L` accepted runs its Prog (a
spill's store to its slot, or none) from `m` to `m'` (the X registers kept) with a relation on
`{m' with mem := M'}`, `M'` agreeing with `m'`'s memory outside `W`, the class map and G35's table
after the value. -/
theorem g66L_entrySkip {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {M0 : Memory} {W : BitVec 64 → Prop} {osp : Bool}
    (hc : checkG66L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hsk : entrySkip lc v = true)
    (hm : LocMatch E s bid i { m with mem := M0 }) (hW : ∀ y, ¬ W y → M0 y = m.mem y)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s osp)
    (hu : UOKL m (uL35 lc (uIn35 lc bid) blk i)) (hmi : MemAt lc bid blk i s)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ m' M', PStar H L ps.toList ret m m' ∧ m'.x = m.x ∧
      LocMatch E s' bid (i + 1) { m' with mem := M' } ∧
      G3Inv E lc (kAt lc kt bid blk (i + 1)) s' osp ∧
      UOKL m' (uL35 lc (uIn35 lc bid) blk (i + 1)) ∧ ∀ y, ¬ W y → M' y = m'.mem y := by
  obtain ⟨hl0, hops⟩ := entrySkip_cases hsk
  have hE0 := hE
  obtain ⟨⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  have hok0 := hc
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, hcf, hk, hlt, hnd, hblocks, -, -, -, -, -, -⟩ :=
    checkG66L_spec hl0 hc
  obtain ⟨b, j, js, e, next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk] at hkd
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  obtain ⟨hlcE, -, -, -, -, -, -, -, hslot, hextra, hF⟩ := hE0.env.env.env.env.env
  rw [kAt_succ hi hv, uL35_succ hl hi hv]
  -- a value with no code keeps the machine state; G35's table across it
  have hnone : ∀ (hx : v.op = .SP ∨ v.op = .SB), LocMatch E s' bid (i + 1) { m with mem := M0 } →
      CoreInv E.ι (StkAt E) (kStep c.cx.lc (kAt c.cx.lc kt bid blk i) v).get s' osp →
      SlotInv c.cx.lc s' →
      ∃ m' M', PStar H (Link.byId sym text az ez c.cx.ps.toList) c.cx.ps.toList ret m m' ∧
        m'.x = m.x ∧ LocMatch E s' bid (i + 1) { m' with mem := M' } ∧
        G3Inv E c.cx.lc (kStep c.cx.lc (kAt c.cx.lc kt bid blk i) v) s' osp ∧
        UOKL m' (uStep35 c.cx.lc (uL35 c.cx.lc (uIn35 c.cx.lc bid) blk i) v) ∧
        ∀ y, ¬ W y → M' y = m'.mem y := fun hx h1 h2 h3 =>
    ⟨m, M0, .refl, rfl, h1, ⟨h2, h3⟩, by
      rcases hx with h | h <;>
        exact uokl_xw35 hu (.inl rfl) (ldEntry35_none (by rw [h]; rfl) (by rw [h]; nofun))
          (by simp [uEntry, narrowLd?, loadOp?, narrowLoad?, loadIdxOp?, h]) (by simp [h])
          (by simp [h]) (by simp [h]) (by simp [h]), hW⟩
  rcases hops with hop | hop | ⟨hx, hop | hop⟩
  · -- `SP`
    rw [vkind66_eq65 (by rw [hop]; decide) (by rw [hop]; decide) (by rw [hop]; decide)
      (by rw [hop]; rfl), vkind65_eq64 (by rw [hop]; rfl)] at hkd
    rcases vkind64_skip28 (.inr (.inl hop)) hkd with h28 | ⟨h, -⟩
    · rw [vkind28_eq24 hop] at h28
      obtain ⟨htemp, hVK⟩ := vkind24_spec h28 (by rw [hop]; rfl)
      cases hVK with
      | g23 hne _ => exact absurd hop hne
      | sp _ _ hcl hh =>
        have hK : KNext c.cx.lc v (kAt c.cx.lc kt bid blk i).get
            (kStep c.cx.lc (kAt c.cx.lc kt bid blk i) v).get :=
          knext_kStep fun _ => by
            rcases hh with hh | hh
            · exact (hs_none hh).noRegs
            · exact (hs_reg hh).noRegs
        obtain ⟨h1, h2, h3⟩ := g24_spW F hm hinv.core hinv.slots hK hj hj' hop hcl hh hvs htemp hs
        exact hnone (.inl hop) h1 h2 h3
    · rw [hop] at h; cases h
  · -- `InitMem`
    rw [vkind66_initMem hop, vkind65_initMem hop, vkind64_initMem hop, vkind63_initMem hop,
      vkind62_initMem hop, vkind61_initMem hop,
      vkind60_initMem hop, vkind59_initMem hop, vkind58_initMem hop] at hkd
    have hkd := vkind48_initMem hop hkd
    rw [vkind57_initMem hop, vkind55_initMem hop, vkind54_initMem hop, vkind53_initMem hop,
      vkind52_initMem hop] at hkd
    have hkd := vkind49_initMem hop hkd
    rw [vkind51_initMem hop, vkind50_initMem hop, vkind47_initMem hop, vkind46_initMem hop,
      vkind45_initMem hop, vkind44_initMem hop] at hkd
    obtain ⟨-, -, ht, -, hh, hmt, rfl⟩ := vkind43_initMem hkd hop
    have hpc : E.pcOf bid (i + 1) = E.pcOf bid i := by rw [hj', hj, hvs]
    obtain ⟨hok, hcl⟩ := g66L_clean hok0 hl hbid hb hi hv hop
    have hss : s' = s := by
      rw [stepLoc_initMem hl ht hop hh hmt hs]
      exact congrArg (fun x => { s with mem := x }) (hmi hl hok hcl).symm
    subst hss
    have hK : kStep c.cx.lc (kAt c.cx.lc kt bid blk i) v = kAt c.cx.lc kt bid blk i :=
      kStep_none (by rw [hh]; nofun) (by rw [hh]; nofun) (by rw [hh]; nofun)
    refine ⟨m, M0, .refl, rfl, locMatch_pc hm (hpc.trans hm.pc.symm), by rw [hK]; exact hinv,
      ?_, hW⟩
    rw [uStep35_initMem hop]
    intro e he
    cases he
  · -- a spill
    obtain hkd | ⟨e66, hfs66 | hns66⟩ := vkind66_spill64 hop hkd
    rotate_left
    · obtain ⟨k, nc, off, rs, htemp, hh, hso, hsz1, hft, hcv, hao, rfl⟩ := fspill66_ok hfs66
      obtain ⟨m', M', h1, h2, h3, h4, h5, h6⟩ := g66_fspillW (H := H) F hF hlcE hcf hslot hextra
        hm hinv.core hinv.slots (kread_of_reads hreads)
        (knext_kStep fun _ => (hs_slot hh).noRegs) hj hj' hop hh hso hsz1 hft hcv hao hvs
        htemp hs hW
      exact ⟨m', M', h1, h5, h2, ⟨h3, h4⟩, uokl_f63 (.inl hop) h5 hu, h6⟩
    · obtain ⟨k, nc, off, rs, n, c', htemp, hn, hh, hso, hsz1, hts, hao, hcv, rfl⟩ :=
        nspill66_ok hns66
      obtain ⟨m', M', h1, h2, h3, h4, h5, h6⟩ := g66_nspillW (H := H) F hF hlcE hcf hslot hextra
        hm hinv.core hinv.slots (kread_of_reads hreads)
        (knext_kStep fun _ => (hs_slot hh).noRegs) hj hj' hop hn hh hso hsz1 hts hao hcv hvs
        htemp hs hW
      exact ⟨m', M', h1, h5, h2, ⟨h3, h4⟩, uokl_f63 (.inl hop) h5 hu, h6⟩
    rcases vkind64_skip28 (.inl hop) hkd with h28 | ⟨-, e', hfs⟩
    · obtain ⟨htemp, hVK⟩ := vkind3_spec (vkind28_ok3 (.inl hop) hx h28) (by rw [hop]; rfl)
      have hl0 : loadOp? v.op = none := by rw [hop]; rfl
      have hs0 : storeOp? v.op = none := by rw [hop]; rfl
      have he0 : extOp? v.op = none := by rw [hop]; rfl
      cases hVK with
      | g2 _ _ h2 =>
        cases h2 with
        | g1 _ _ _ hne _ _ => exact absurd hop hne
        | call hop' => rw [hop] at hop'; cases hop'
        | selMem hop' => rw [hop] at hop'; cases hop'
        | selReg hop' => rw [hop] at hop'; cases hop'
        | addr hop' => rw [hop] at hop'; cases hop'
        | reload hop' => rw [hop] at hop'; cases hop'
        | spill _ hh hso hsz1 hcv hao hpat =>
          obtain ⟨m', M', h1, h2, h3, h4, h5, h6⟩ := g2_spillW (H := H) F hF hlcE hcf hslot hextra
            hm hinv.core hinv.slots (kread_of_reads hreads)
            (knext_kStep fun _ => (hs_slot hh).noRegs) hj hj' hop hh hso hsz1 hcv hao hpat hvs
            htemp hs hW
          exact ⟨m', M', h1, h5, h2, ⟨h3, h4⟩,
            uokl_f63 (.inl hop) (fun h => by rw [hop] at h; cases h) h5 hu, h6⟩
      | load h' => rw [hl0] at h'; cases h'
      | store h' => rw [hs0] at h'; cases h'
      | sb h' => rw [hop] at h'; cases h'
      | ext h' => rw [he0] at h'; cases h'
      | aluK h' => rcases h' with ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ <;> rw [hop] at h' <;> cases h'
      | ubfx h' => rw [hop] at h'; cases h'
      | cmpw h' => rw [hop] at h'; cases h'
      | cmpwK h' => rw [hop] at h'; cases h'
    · obtain ⟨k, nc, off, rs, htemp, hh, hso, hsz1, hft, hcv, hao, rfl⟩ := fspill63_ok hfs
      obtain ⟨m', M', h1, h2, h3, h4, h5, h6⟩ := g63_fspillW (H := H) F hF hlcE hcf hslot hextra
        hm hinv.core hinv.slots (kread_of_reads hreads)
        (knext_kStep fun _ => (hs_slot hh).noRegs) hj hj' hop hh hso hsz1 hft hcv hao hvs
        htemp hs hW
      exact ⟨m', M', h1, h5, h2, ⟨h3, h4⟩,
        uokl_f63 (.inl hop) (fun h => by rw [hop] at h; cases h) h5 hu, h6⟩
  · -- `SB`
    rw [vkind66_eq65 (by rw [hop]; decide) (by rw [hop]; decide) (by rw [hop]; decide)
      (by rw [hop]; rfl), vkind65_eq64 (by rw [hop]; rfl)] at hkd
    rcases vkind64_skip28 (.inr (.inr hop)) hkd with h28 | ⟨h, -⟩
    · obtain ⟨htemp, hVK⟩ := vkind3_spec (vkind28_ok3 (.inr hop) hx h28) (by rw [hop]; rfl)
      have hl0 : loadOp? v.op = none := by rw [hop]; rfl
      have hs0 : storeOp? v.op = none := by rw [hop]; rfl
      cases hVK with
      | sb _ _ hcl hh =>
        have hK : KNext c.cx.lc v (kAt c.cx.lc kt bid blk i).get
            (kStep c.cx.lc (kAt c.cx.lc kt bid blk i) v).get :=
          knext_kStep fun _ => by
            rcases hh with hh | hh
            · exact (hs_none hh).noRegs
            · exact (hs_reg hh).noRegs
        obtain ⟨h1, h2, h3⟩ := g3_sbW F hm hinv.core hinv.slots hK hj hj' hop hcl hh hvs htemp hs
        exact hnone (.inr hop) h1 h2 h3
      | g2 hg _ _ =>
        rcases hg with ⟨-, -, hne, -⟩ | ⟨h' | h', -⟩
        · exact absurd hop hne
        all_goals rw [hop] at h'; cases h'
      | load h' => rw [hl0] at h'; cases h'
      | store h' => rw [hs0] at h'; cases h'
      | ext h' => rw [hop] at h'; cases h'
      | aluK h' => rcases h' with ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ <;> rw [hop] at h' <;> cases h'
      | ubfx h' => rw [hop] at h'; cases h'
      | cmpw h' => rw [hop] at h'; cases h'
      | cmpwK h' => rw [hop] at h'; cases h'
    · rw [hop] at h; cases h

/-! ## No skipped value panics -/

/-- `evalOpL` panics only on `PanickingL` ops (the core of `evalValueL_panic_op`). -/
theorem evalOpL_panic_op {faulting : Bool} {env : Env} {ctx : GoFV.SSA.Sem.Ctx}
    {fr : GoFV.SSA.Sem.Frame} {v : Value} {argv : List Val} {ty : Ty} {e : Panic} {m : Mem}
    (ho : evalOpL faulting env ctx fr v argv ty = .panic e m) : PanickingL faulting v.op := by
  rw [evalOpL_eq] at ho
  split at ho
  · exact .of_panicking (evalOp_panic_op ho)
  · rename_i hg
    have hg' : v.op.generic = false := by simpa using hg
    split at ho
    · exact arm64Op_panic_op hg' ho
    · split at ho
      · exact absurd ho atomicRoot_ne_panic
      · cases ho

/-- A value `entrySkip` takes does not panic: a `StoreReg` moves its argument; `SP`, `SB` and
`InitMem` are generic ops that are no call and no nil check. -/
theorem stepLoc_entrySkip_ne_panic {env : Env} {lc : LocCtx} {s : LocState} {v : Value}
    (hsk : entrySkip lc v = true) {e : Panic} {mm : Mem} : stepLoc env lc s v ≠ .panic e mm := by
  intro h
  obtain ⟨-, hops⟩ := entrySkip_cases hsk
  rcases hops with hop | hop | ⟨-, hop | hop⟩
  rotate_left 2
  · unfold stepLoc at h
    simp only [show (v.op == Op.Phi) = false by rw [hop]; rfl, Bool.false_eq_true,
      ↓reduceIte] at h
    cases hm : v.args.toList.mapM (s.read lc) with
    | panic e' m' => exact mapM_read_ne_panic _ hm
    | stuck msg => rw [hm] at h; cases h
    | ok argv =>
      rw [hm] at h
      simp only [bind, Res.bind] at h
      rw [hop] at h
      rcases argv with _ | ⟨x, _ | ⟨y, t⟩⟩ <;> simp at h
  all_goals
    obtain ⟨argv, -, ho⟩ := stepLoc_panic_eval (by rw [hop]; decide) (by rw [hop]; decide)
      (by rw [hop]; decide) (by rw [hop]; decide) (by rw [hop]; decide) h
    rcases evalOpL_panic_op ho with h' | h' | ⟨-, h'⟩ <;> rw [hop] at h' <;> cases h'

end GoFV.Proof.Obj

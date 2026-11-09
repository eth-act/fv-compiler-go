import GoFV.Proof.Gen.G33
import GoFV.Gen.Check34

variable [GoFV.SSA.Sem.Addrs]

/-!
# The values G34's upper-bit table keeps its entries across write at most their home
(`docs/plans/proofs3.md` §4)

`vk33_keep`: a value of G33's kinds (`VK33`) that `keep34` accepts runs as its slice's step, which
writes at most the X register of the value's register home (`XW`). Each `VKn` (`n` from 33 down
to 2) is a `VK(n-1)` through its `g(n-1)` constructor or one of the slice's new kinds. A new kind
`keep34` accepts is run by its case lemma, which concludes `XW` (G2's `g2_g1`, `g2_addr`,
`g2_spill`, `g2_reload`; G3's `g3_ext`, `g3_aluK`, `g3_ubfx`, `g3_cmpw`, `g3_cmpwK`; G6's
`g6_addr`; G16's `g16_addSh`; G23's `g23_cset`; G25's `g25_csel`, `g25_csel0`, `g25_tst`,
`g25_tstw`; G32's `g32_bin`, `g32_binK`, `g32_un`, `g32_csinc`; G33's `g33_un`, `g33_ubfiz`,
`g33_sra`, `g33_cmnw`). Every other new kind names an op outside `keepOps34`, the ops `keep34`
accepts (`keep34_mem`; a `MOVDload`/`MOVDstore` only without symbol, `keep34_aux`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-- The ops of the values `keep34` accepts. -/
def keepOps34 : List Op :=
  [.Phi, .ARM64ZERO, .InlMark, .Copy, .MakeResult, .ARM64MOVDconst, .ARM64ADD, .ARM64SUB,
    .ARM64ADDconst, .ARM64SUBconst, .ARM64CMP, .ARM64CMPconst, .ARM64CMPW, .ARM64CMPWconst,
    .ARM64MOVDload, .ARM64MOVDstore,
    .ARM64MOVBreg, .ARM64MOVBUreg, .ARM64MOVHreg, .ARM64MOVHUreg, .ARM64MOVWreg, .ARM64MOVWUreg,
    .ARM64ANDconst, .ARM64SLLconst, .ARM64SRLconst, .ARM64UBFX, .ARM64ADDshiftLL,
    .ARM64Equal, .ARM64NotEqual, .ARM64LessThan, .ARM64LessEqual, .ARM64GreaterThan,
    .ARM64GreaterEqual, .ARM64LessThanU, .ARM64LessEqualU, .ARM64GreaterThanU,
    .ARM64GreaterEqualU, .ARM64CSEL, .ARM64CSEL0, .ARM64TSTconst, .ARM64TSTWconst,
    .ARM64MUL, .ARM64MNEG, .ARM64AND, .ARM64OR, .ARM64XOR, .ARM64BIC, .ARM64EON, .ARM64ORN,
    .ARM64ORconst, .ARM64XORconst, .ARM64NEG, .ARM64MVN, .ARM64CSINC, .ARM64CLZ, .ARM64REV,
    .ARM64UBFIZ, .ARM64SRAconst, .ARM64CMNWconst, .LoadReg, .StoreReg, .ARM64MOVDaddr]

/-- The op of a value `keep34` accepts is in `keepOps34`. -/
theorem keep34_mem {v : Value} (h : keep34 v = true) : v.op ∈ keepOps34 := by
  simp only [keep34, keep31, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with (h | ⟨h | h, -⟩) | h
  · unfold keepOp31 at h
    split at h <;> first | exact absurd h Bool.false_ne_true | (rename_i heq; simp [keepOps34, heq])
  · rw [h]; simp [keepOps34]
  · rw [h]; simp [keepOps34]
  · unfold keepOp34 at h
    split at h <;> first | exact absurd h Bool.false_ne_true | (rename_i heq; simp [keepOps34, heq])

/-- A `MOVDload`/`MOVDstore` that `keep34` accepts has no symbol. -/
theorem keep34_aux {v : Value} (h : keep34 v = true)
    (hop : v.op = .ARM64MOVDload ∨ v.op = .ARM64MOVDstore) : v.aux = none := by
  simp only [keep34, keep31, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    Option.isNone_iff_eq_none] at h
  rcases h with (h | ⟨-, hx⟩) | h
  · rcases hop with hop | hop <;> rw [hop] at h <;> cases h
  · exact hx
  · rcases hop with hop | hop <;> rw [hop] at h <;> cases h

/-- A property every op of `keepOps34` has holds of the op of a value `keep34` accepts. -/
theorem keep34_all {v : Value} {f : Op → Bool} (hall : keepOps34.all f = true)
    (h : keep34 v = true) : f v.op = true :=
  List.all_eq_true.1 hall _ (keep34_mem h)

/-- Refutes `h' : v.op = .X` for an op `.X` outside `keepOps34`, against `hk : keep34 v = true`. -/
local macro "refute34" hk:ident h':ident : tactic => `(tactic|
  (have h1 := keep34_mem $hk; rw [$h':ident] at h1; exact absurd h1 (by decide)))

/-- One value of G33's kinds that `keep34` accepts: its step, which writes at most the X register
of its register home (`XW`). -/
theorem vk33_keep {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2}
    (hE : G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hcf : checkFrame lc g = .ok ())
    (hv : lc.ctx.f.value? id = some v) (hVK : VK33 lc g v kd) (hk : keep34 v = true)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s) (hpre : G14Pre lc s v)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E s' bid (i + 1) m' ∧ G3Inv E lc (kStep lc K v) s' ∧ XW lc v m m' := by
  obtain ⟨hlcE, -, -, -, -, hglob, -, -, hslot, hextra, hF⟩ := hE.env.env.env.env
  have hvars := hE.env.env.env.vars
  have hsz := slot_sizes hlcE hcf hinv.slots
  have hR := kread_of_reads hreads
  have fin : (∃ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E s' bid (i + 1) m' ∧ CoreInv E.ι (StkAt E) (kStep lc K v).get s' ∧
      SlotInv lc s' ∧ XW lc v m m') →
      ∃ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
        LocMatch E s' bid (i + 1) m' ∧ G3Inv E lc (kStep lc K v) s' ∧ XW lc v m m' :=
    fun ⟨m', h1, h2, h3, h4, h5⟩ => ⟨m', h1, h2, ⟨h3, h4⟩, h5⟩
  cases hVK with
  | un hop hsz hao hro h8 hca =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    exact fin (g33_un (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hro h8 hca hvs htemp hs)
  | ubfiz hop hsz hk0 hk16 hao hro h8 hw =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    exact fin (g33_ubfiz (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hk0 hk16 hao hro h8 hw hvs htemp
      hs)
  | sra hop hsz hao hro h8 hca hk0 hk' =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    exact fin (g33_sra (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hro h8 hca hk0 hk' hvs htemp
      hs)
  | cmnw hop hsz hfl hhn hao hca =>
    exact fin ((g33_cmnw (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hop hsz hfl hhn hao hca hvs htemp hs).imp
      fun _ ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, h4, .inl h5⟩)
  | g32 _ _ _ _ h32 =>
  cases h32 with
  | bin hop hsz hao hbo hro hw =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    exact fin (g32_bin (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hbo hro hw hvs htemp
      hs)
  | binK hop hsz hao hro hw =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    exact fin (g32_binK (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hro hw hvs htemp hs)
  | un hop hsz hao hro h8 hca =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    exact fin (g32_un (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hro h8 hca hvs htemp
      hs)
  | csinc hop hsz hfa hfl hhn ho hco hcc hao hbo hro h8 hca hcb =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    exact fin (g32_csinc (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hfa hfl hhn ho hco hcc hao hbo
      hro h8 hca hcb hvs htemp hs)
  | stlr h' =>
    rcases stlr?_some h' with ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ <;> refute34 hk h'
  | g28 _ _ _ _ _ h28 =>
  cases h28 with
  | memEq h' => refute34 hk h'
  | g27 _ h27 =>
  cases h27 with
  | logSh h' =>
    have := keep34_all (f := fun o => (logSh? o).isNone) (by decide) hk
    rw [h'] at this; cases this
  | g25 _ h25 =>
  cases h25 with
  | csel hop hsz hfa hfl hhn ho hco hcc hao hbo hro h8 hca hcb =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    exact fin (g25_csel (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hfa hfl hhn ho hco hcc hao hbo
      hro h8 hca hcb hvs htemp hs)
  | csel0 hop hsz hfa hfl hhn ho hco hcc hao hro h8 hca =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    exact fin (g25_csel0 (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hfa hfl hhn ho hco hcc hao hro
      h8 hca hvs htemp hs)
  | tst hop hsz1 hfl hhn hao hok =>
    exact fin (g25_tst (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hop hsz1 hfl hhn hao hok hvs htemp
      hs)
  | tstw hop hsz1 hfl hhn hao hok =>
    exact fin (g25_tstw (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hop hsz1 hfl hhn hao hok hvs htemp
      hs)
  | g24 _ _ h24 =>
  cases h24 with
  | sp h' => refute34 hk h'
  | g23 _ h23 =>
  cases h23 with
  | cset hc hcc hsz ha hfl hhn hro =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    exact fin (g23_cset (H := H) F hm hinv.core hinv.slots
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hc hcc hsz ha hfl hhn hro hvs htemp
      hs)
  | g22 _ h22 =>
  cases h22 with
  | ldp h' => refute34 hk h'
  | stp h' => refute34 hk h'
  | g21 _ h21 =>
  cases h21 with
  | regSame h' => refute34 hk h'
  | regMov h' => refute34 hk h'
  | g20 _ h20 =>
  cases h20 with
  | nop h' => refute34 hk h'
  | g19 _ h19 =>
  cases h19 with
  | pb h' =>
    have := keep34_all (f := fun o => !pbOp o) (by decide) hk
    rw [h'] at this; cases this
  | g18 _ h18 =>
  cases h18 with
  | stIdx h' =>
    have := keep34_all (f := fun o => (storeIdxOp? o).isNone) (by decide) hk
    rw [h'] at this; cases this
  | g17 h17 =>
  cases h17 with
  | getG h' => refute34 hk h'
  | g16 h16 =>
  cases h16 with
  | addSh hop hsz hk0 hk64 hao hbo hro h8 hca hcb =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    exact fin (g16_addSh (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hk0 hk64 hao hbo hro h8 hca hcb
      hvs htemp hs)
  | g15 h15 =>
  cases h15 with
  | call h' => refute34 hk h'
  | g14 _ h14 =>
  cases h14 with
  | idx h' =>
    have := keep34_all (f := fun o => (loadIdxOp? o).isNone) (by decide) hk
    rw [h'] at this; cases this
  | g13 h13 =>
  cases h13 with
  | zero h' => refute34 hk h'
  | g12 h12 =>
  cases h12 with
  | conv h' => refute34 hk h'
  | g11 h11 =>
  cases h11 with
  | clo h' => refute34 hk h'
  | g10 h10 =>
  cases h10 with
  | icall h' =>
    have := keep34_all (f := fun o => (icallLead o).isNone) (by decide) hk
    rw [h'] at this; cases this
  | selMem h' => refute34 hk h'
  | selReg h' => refute34 hk h'
  | g9 h9 =>
  cases h9 with
  | call h' => refute34 hk h'
  | g8 _ h8 =>
  cases h8 with
  | wb h' => refute34 hk h'
  | sel0 h' => refute34 hk h'
  | sel1 h' => refute34 hk h'
  | g7 h7 =>
  cases h7 with
  | nil h' => refute34 hk h'
  | g6 _ h6 =>
  cases h6 with
  | var hfv hVar =>
    have hι := var_addr hfv hv hvars
    have hx := hfv.aux
    have hvar := hfv.var
    have hf := hfv.temp
    cases hVar with
    | addr hop hsz1 hro =>
      obtain ⟨a0, ha0⟩ : ∃ a0, v.args[0]? = some a0 :=
        ⟨v.args[0]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
      exact fin (g6_addr (H := H) F hm hinv.core hinv.slots
        (knext_kStep fun _ => (hs_res hro).noRegs) hj hj' hx hvar hf hι hop hsz1 ha0 hro hvs
        htemp hs)
    | load h' =>
      have hl := keep34_all (f := fun o => (loadOp? o).isNone || o == .ARM64MOVDload) (by decide) hk
      rw [h'] at hl
      simp only [Option.isNone_some, Bool.false_or, beq_iff_eq] at hl
      rw [keep34_aux hk (.inl hl)] at hx; cases hx
    | store h' =>
      have hl := keep34_all (f := fun o => (storeOp? o).isNone || o == .ARM64MOVDstore) (by decide)
        hk
      rw [h'] at hl
      simp only [Option.isNone_some, Bool.false_or, beq_iff_eq] at hl
      rw [keep34_aux hk (.inr hl)] at hx; cases hx
    | ldp h' => refute34 hk h'
    | stp h' => refute34 hk h'
  | g5 h5 =>
  cases h5 with
  | mark h' =>
    have := keep34_all (f := fun o => (markOp? o).isNone) (by decide) hk
    rw [h'] at this; cases this
  | g4 _ h4 =>
  cases h4 with
  | ldp h' => refute34 hk h'
  | stp h' => refute34 hk h'
  | sel h' =>
    rcases h' with ⟨h', -⟩ | ⟨h', -⟩
    · refute34 hk h'
    · refute34 hk h'
  | g3 _ _ _ _ h3 =>
  have hK : v.op ≠ .ARM64CALLstatic → KNext lc v K.get (kStep lc K v).get :=
    fun hnc => knext_kStep fun hnp => (vk3_noRes h3 hnc hnp).noRegs
  cases h3 with
  | g2 hops _ h2 =>
    cases h2 with
    | g1 hnc _ _ _ _ hvk =>
      have haux : v.op = .ARM64MOVDload → v.aux = none := by
        intro hop
        rcases hops with ⟨hl0, -⟩ | ⟨-, hx⟩
        · rw [hop] at hl0; simp [loadOp?] at hl0
        · exact hx
      exact fin (g2_g1 (H := H) F hF hsz hm hinv.core hinv.slots hj hj' hvs hvk htemp
        (hpre.1.1.1.1.g1 haux) hR (hK hnc) hs)
    | call h' => refute34 hk h'
    | selMem h' => refute34 hk h'
    | selReg h' => refute34 hk h'
    | addr hop hsz1 ha0 _ hx hsym hro hpat =>
      exact fin (g2_addr (H := H) F (fun y name abi h => hglob y name abi h) hm hinv.core
        hinv.slots (hK (by rw [hop]; nofun)) hj hj' hop hsz1 ha0 hx hsym hro hpat hvs htemp
        hs)
    | spill hop hh hso hsz1 hcv hao hpat =>
      exact fin (g2_spill (H := H) F hF hlcE hcf hslot hextra hm hinv.core hinv.slots hR
        (hK (by rw [hop]; nofun)) hj hj' hop hh hso hsz1 hcv hao hpat hvs htemp hs)
    | reload hop hsz1 ha0 hah hso hca hro hpat =>
      exact fin (g2_reload (H := H) F hF hlcE hcf hslot hm hinv.core hinv.slots
        (hK (by rw [hop]; nofun)) hj hj' hop hsz1 ha0 hah hso hca hro hpat hvs htemp
        hs)
  | load hop hmovd =>
    have hl := keep34_all (f := fun o => (loadOp? o).isNone || o == .ARM64MOVDload) (by decide) hk
    rw [hop] at hl
    simp only [Option.isNone_some, Bool.false_or, beq_iff_eq] at hl
    rw [hl] at hop
    simp only [loadOp?, beq_self_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hop
    exact absurd (keep34_aux hk (.inl hl)) (hmovd hop.1.symm)
  | store hop hmovd =>
    have hl := keep34_all (f := fun o => (storeOp? o).isNone || o == .ARM64MOVDstore) (by decide)
      hk
    rw [hop] at hl
    simp only [Option.isNone_some, Bool.false_or, beq_iff_eq] at hl
    rw [hl] at hop
    simp only [storeOp?, beq_self_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hop
    exact absurd (keep34_aux hk (.inr hl)) (hmovd hop.1.symm)
  | sb hop => refute34 hk hop
  | ext he hsz1 hao hro hw h8 =>
    have hnc : v.op ≠ .ARM64CALLstatic := by
      intro h; rw [h] at he; simp [extOp?] at he
    exact fin (g3_ext (H := H) F hm hinv.core hinv.slots hR (hK hnc) hj hj' he hsz1 hao hro hw
      h8 hvs htemp hs)
  | aluK hop hsz1 hao hro h8 hca hsr hkk =>
    have hnc : v.op ≠ .ARM64CALLstatic := by
      rcases hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun
    exact fin (g3_aluK (H := H) F hm hinv.core hinv.slots hR (hK hnc) hj hj' hop hsz1 hao hro
      h8 hca hsr hkk hvs htemp hs)
  | ubfx hop hsz1 hk0 hk16 hao hro h8 hw0 hlw hpat =>
    exact fin (g3_ubfx (H := H) F hm hinv.core hinv.slots hR (hK (by rw [hop]; nofun)) hj hj'
      hop hsz1 hk0 hk16 hao hro h8 hw0 hlw hpat hvs htemp hs)
  | cmpw hop hsz2 hfl hhn hao hbo hca hcb =>
    exact fin ((g3_cmpw (H := H) F hm hinv.core hinv.slots hR
      (hK (by rw [hop]; nofun)) hj hj' hop hsz2 hfl hhn hao hbo hca hcb hvs htemp hs).imp
      fun _ ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, h4, .inl h5⟩)
  | cmpwK hop hsz1 hfl hhn hao hca =>
    exact fin ((g3_cmpwK (H := H) F hm hinv.core hinv.slots hR
      (hK (by rw [hop]; nofun)) hj hj' hop hsz1 hfl hhn hao hca hvs htemp hs).imp
      fun _ ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, h4, .inl h5⟩)

end GoFV.Proof.Gen

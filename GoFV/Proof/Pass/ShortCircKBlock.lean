import GoFV.Proof.Pass.ShortCircSpec
import GoFV.Proof.Pass.ShortCircEval

/-!
# Checked `shortcircuitBlock`: entering a checked block

`kenter`: a block `B` the checker compared (`B ∈ K`, `blockOK`) entered by the source along `iS`
and by the target along `iT` (`edgeIn`: the source's index and the facts `E` of the edge), in
frames related by `FactsRel E`, ends in frames related by the block's end facts `out`, with
controls that hold the same values; a source entry that panics panics in the target too.

The target's `Phi`s read the registers related to the source's arguments (`phisOK`); after them,
target register `w` holds the source's `a` whenever `pinRel w a` (`post_rel`). Its non-`Phi`s
evaluate against the source's final frame (`evalAll_map`), each standing for the source register
`home x`: a source non-`Phi` for itself, one of `b`'s phis that became a `Copy`, or a `Copy`
carrying the fact of one of `b`'s other phis.
-/

namespace GoFV.Proof.ShortCirc

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.ShortCircuit GoFV.Proof Dom

theorem blockOK_spec {I : Info} {f g : Func} {T : FactTab} {B : ID} {fB gB : Block}
    (hBg : B ∈ g.blocks) (hfB : f.block? B = some fB) (hgB : g.block? B = some gB)
    (h : I.blockOK f g T B = true) :
    fB.id = B ∧ gB.id = B ∧ ((gB.preds = #[] ∧ B = I.s.b) ∨
      (gB.kind = fB.kind ∧ gB.controls.size = fB.controls.size ∧
        (B ∈ I.region ∨ B = I.s.b ∨ ((I.factsOf T B).1 = I.dflt ∧ (I.factsOf T B).2 = I.dflt)) ∧
        I.newOK f fB gB = true ∧
        I.nodesOK f g fB gB (I.factsOf T B).1 (I.factsOf T B).2
          (I.region.contains B || B == I.s.b) = true ∧
        Info.schedOK f g fB gB = true ∧
        I.outOK f g fB gB (I.factsOf T B).1 (I.factsOf T B).2 = true ∧
        I.succOK fB gB B = true ∧
        (∀ (k : Nat) (c' c : ID), gB.controls[k]? = some c' → fB.controls[k]? = some c →
          I.argRel f g fB gB (I.factsOf T B).1 (I.factsOf T B).2 c' c = true) ∧
        ∀ iT, iT < max 1 gB.preds.size →
          (I.redir B iT = true ∨ fB.preds[(I.edgeIn f T B gB iT).1]? = gB.preds[iT]?) ∧
          I.phisOK f g fB gB (I.factsOf T B).1 iT (I.edgeIn f T B gB iT).1
            (I.edgeIn f T B gB iT).2 (I.region.contains B) = true)) := by
  unfold Info.blockOK at h
  rw [contains_iff.2 hBg, hfB, hgB] at h
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  rcases Bool.or_eq_true_iff.1 h3 with h3 | h3
  · simp only [Bool.and_eq_true, beq_iff_eq, Array.isEmpty_iff] at h3
    exact .inl h3
  · refine .inr ?_
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, contains_iff,
      List.all_eq_true, List.mem_range, Array.all_eq_true'] at h3
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hk, hc⟩, hd⟩, hn⟩, hno⟩, hs⟩, ho⟩, hsu⟩, hcr⟩, hph⟩ := h3
    refine ⟨hk, hc, ?_, hn, ?_, hs, ho, hsu, fun k c' c hc' hc0 => ?_, fun iT hiT => ?_⟩
    · rcases hd with (hd | hd) | ⟨hd1, hd2⟩
      · exact .inl hd
      · exact .inr (.inl hd)
      · exact .inr (.inr ⟨hd1, hd2⟩)
    · simpa [contains_iff, Bool.or_eq_true, beq_iff_eq] using hno
    · have hk1 : k < gB.controls.size := (Array.getElem?_eq_some_iff.1 hc').1
      have hk2 : k < fB.controls.size := (Array.getElem?_eq_some_iff.1 hc0).1
      have := hcr (gB.controls[k], fB.controls[k])
        (Array.mem_iff_getElem.2 ⟨k, by simp only [Array.size_zip]; omega, by simp⟩)
      rw [Array.getElem?_eq_some_iff.1 hc' |>.2, Array.getElem?_eq_some_iff.1 hc0 |>.2] at this
      exact this
    · obtain ⟨h1, h2⟩ := hph iT hiT
      refine ⟨?_, by simpa [contains_iff] using h2⟩
      rcases h1 with h1 | h1
      · exact .inl h1
      · exact .inr h1

/-- What setting a block's `Phi`s along edge `i` does (`phis_spec`). -/
structure PhiData (tabs : Tables) (h : Func) (Bk : Block) (i : Nat) (fr P : Frame) : Prop where
  frame : P = { fr with regs := P.regs }
  size : P.regs.size = fr.regs.size
  keep : ∀ z, (z ∉ Bk.values ∨ ∃ v, h.value? z = some v ∧ v.op ≠ .Phi) → P.regs[z]? = fr.regs[z]?
  phi : ∀ z ∈ Bk.values, ∀ v, h.value? z = some v → v.op = .Phi → z < fr.regs.size →
    ∃ a y, v.args[i]? = some a ∧ fr.regs[a]? = some (some y) ∧
      P.regs[z]? = some (some (y.retype (tyOf tabs h z)))

theorem phiData_of {tabs : Tables} {h : Func} {Bk : Block} {i : Nat} {fr : Frame}
    {ps : List (ID × Val)} (hnd : Bk.values.toList.Nodup)
    (hps : Bk.values.toList.filterMapM (phiStep (Ctx.make tabs h) fr i) = .ok ps) :
    PhiData tabs h Bk i fr { fr with regs := setPhis ps fr.regs } := by
  obtain ⟨h1, -, h3, h4⟩ := phis_spec hnd hps
  exact ⟨rfl, h1, h3, h4⟩

namespace SCI

variable (I : Info)

theorem vs_sub {f : Func} (hpre : I.vs = I.bvals.filter (fun x => x != I.s.ctl && isPhiIn f x)) {v : ID}
    (hv : v ∈ I.vs) : v ∈ I.bvals ∧ v ≠ I.s.ctl ∧ isPhiIn f v = true := by
  rw [hpre, Array.mem_filter] at hv
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hv
  exact ⟨hv.1, hv.2.1, hv.2.2⟩

/-- `trans`: the target register holds the source's. -/
theorem trans_rel {f : Func} {E : Facts} {frS frT : Frame} (hrel : FactsRel I f E frS frT)
    {a w : ID} (h : I.trans E a = some w) (hl : Listed f a) : frT.regs[w]? = frS.regs[a]? := by
  rcases (trans_eq_some I).1 h with ⟨-, hl'⟩ | ⟨-, hb, rfl⟩
  · exact hrel.2 a w hl'
  · exact hrel.1 _ (fun h => h.elim hb (· hl))

end SCI

/-! ## Well-formedness helpers -/

theorem listedIn_of {ce : CheckEnv} {f : Func} (hwf : WF ce f) {a : ID} (hl : Listed f a) :
    listedIn f a = true := by
  obtain ⟨v, Bk, ⟨hv, -⟩, hvb, hBk, ha, -⟩ := blockOf_listed hwf hl
  unfold listedIn; rw [hv]; simp only
  rw [hvb, valsOf_eq hBk]; exact contains_iff.2 ha

theorem listed_of_mem {ce : CheckEnv} {f : Func} (hwf : WF ce f) {B : ID} {fB : Block}
    (hBm : B ∈ f.blocks) (hfB : f.block? B = some fB) {x : ID} (hx : x ∈ fB.values) :
    Listed f x := ⟨B, fB, ⟨hBm, hfB⟩, hx⟩

theorem value_of_mem {ce : CheckEnv} {f : Func} (hwf : WF ce f) {B : ID} {fB : Block}
    (hBm : B ∈ f.blocks) (hfB : f.block? B = some fB) {x : ID} (hx : x ∈ fB.values) :
    ∃ v, f.value? x = some v ∧ v.id = x ∧ v.block = B :=
  hwf.valueId B fB ⟨hBm, hfB⟩ x hx

theorem argListed_of {ce : CheckEnv} {f : Func} (hwf : WF ce f) {B : ID} {fB : Block}
    (hBm : B ∈ f.blocks) (hfB : f.block? B = some fB) {x : ID} (hx : x ∈ fB.values) {v : Value}
    (hv : f.value? x = some v) {a : ID} (ha : a ∈ v.args) : Listed f a :=
  hwf.argListed B fB x v ⟨⟨hBm, hfB⟩, hx, hv⟩ a ha

theorem value_of_listed {ce : CheckEnv} {f : Func} (hwf : WF ce f) {a : ID} (hl : Listed f a) :
    ∃ v, f.value? a = some v := by
  obtain ⟨B, Bk, ⟨hBm, hBk⟩, ha⟩ := hl
  obtain ⟨v, hv, -⟩ := hwf.valueId B Bk ⟨hBm, hBk⟩ a ha
  exact ⟨v, hv⟩

theorem mem_nodesOf_iff {ce : CheckEnv} {h : Func} (hwf : WF ce h) {B : ID} {Bk : Block}
    (hBm : B ∈ h.blocks) (hBk : h.block? B = some Bk) {x : ID} :
    x ∈ Info.nodesOf h Bk ↔ x ∈ Bk.values ∧ ∃ v, h.value? x = some v ∧ v.op ≠ .Phi := by
  rw [mem_nodesOf]
  constructor
  · rintro ⟨hx, hp⟩
    obtain ⟨v, hv, -⟩ := value_of_mem hwf hBm hBk hx
    exact ⟨hx, v, hv, (isPhiIn_false hv).1 hp⟩
  · rintro ⟨hx, v, hv, hp⟩
    exact ⟨hx, (isPhiIn_false hv).2 hp⟩

theorem args_get_mem {v : Value} {k : Nat} {a : ID} (h : v.args[k]? = some a) : a ∈ v.args :=
  Array.mem_of_getElem? h

/-! ## The `Phi`s of a checked block -/

section Phis

variable {ce : CheckEnv} {tabs : Tables} {f g : Func} {s : Site} (S : Setup ce tabs f g s)
  {B : ID} {fB gB : Block} (hBm : B ∈ f.blocks) (hfB : f.block? B = some fB)
  (hgB : g.block? B = some gB)
  {pin : Facts} {iT iS : Nat} {E : Facts} {inR : Bool}
  (hph : (infoOf tabs f g s).phisOK f g fB gB pin iT iS E inR = true)
  {frS frT : Frame} (hrel : FactsRel (infoOf tabs f g s) f E frS frT)
  (hsrc : inR = true → SrcB (infoOf tabs f g s) frS)
  {PS : Frame} (hPS : PhiData tabs f fB iS frS PS) (hsS : frS.regs.size = f.valueTab.size)
  (hsz : frT.regs.size = frS.regs.size)
include S hBm hfB hgB hph hrel hsrc hPS hsS hsz

theorem gBm : B ∈ g.blocks := by rw [S.gblocks]; exact hBm

/-- The source's `Phi` `z` read a defined argument. -/
theorem src_phi {z : ID} (hz : z ∈ fB.values) (hp : isPhiIn f z = true) :
    ∃ fz a y, f.value? z = some fz ∧ fz.op = .Phi ∧ fz.args[iS]? = some a ∧
      frS.regs[a]? = some (some y) ∧ PS.regs[z]? = some (some (y.retype (tyOf tabs f z))) := by
  obtain ⟨fz, hfz, -⟩ := value_of_mem S.wf hBm hfB hz
  have hop := (isPhiIn_true hfz).1 hp
  obtain ⟨a, y, h1, h2, h3⟩ := hPS.phi z hz fz hfz hop (by rw [hsS]; exact lt_of_value? hfz)
  exact ⟨fz, a, y, hfz, hop, h1, h2, h3⟩

/-- **The target's `Phi`s read defined registers.** -/
theorem phisT_ok : ∃ ps, gB.values.toList.filterMapM
    (phiStep (Ctx.make tabs g) frT iT) = .ok ps := by
  have hwg := S.wfg
  have hBg := gBm S hBm hfB hgB hph hrel hsrc hPS hsS hsz
  obtain ⟨hz, -, hv⟩ := SCI.phisOK_spec _ hph
  refine filterMapM_phi_ok fun z hzm => ?_
  have hzm' := Array.mem_toList_iff.1 hzm
  obtain ⟨gz, hgz, -⟩ := value_of_mem hwg hBg hgB hzm'
  unfold phiStep
  rw [show (Ctx.make tabs g).f = g from rfl, hgz]
  simp only
  by_cases hop : gz.op = .Phi
  · simp only [hop, beq_self_eq_true, ↓reduceIte]
    have hpg : isPhiIn g z = true := (isPhiIn_true hgz).2 hop
    -- the argument along `iT` and its register
    obtain ⟨a', ha', hdef⟩ : ∃ a', gz.args[iT]? = some a' ∧ ∃ y, frT.regs[a']? = some (some y) := by
      by_cases hzf : z ∈ fB.values
      · obtain ⟨hpf, -, w, a, hw, ha, htr⟩ := (hz z hzm' hpg).1 hzf
        rw [getV_of hgz] at hw
        obtain ⟨fz, a0, y, hfz, -, ha0, hy, -⟩ := src_phi S hBm hfB hgB hph hrel hsrc hPS hsS hsz hzf hpf
        rw [getV_of hfz, ha0] at ha; cases ha
        refine ⟨w, hw, y, ?_⟩
        rw [SCI.trans_rel _ hrel htr (argListed_of S.wf hBm hfB hzf hfz (args_get_mem ha0)), hy]
      · obtain ⟨v, hvm, hvz⟩ := (hz z hzm' hpg).2 hzf
        obtain ⟨-, -, -, hinR, a', ha', hsrcv, hnsrc⟩ := (hv v hvm z hvz).1 hzm'
        rw [getV_of hgz] at ha'
        refine ⟨a', ha', ?_⟩
        by_cases hvf : v ∈ fB.values
        · obtain ⟨a, ha, htr⟩ := hsrcv hvf
          have hvp := (S.vs_mem hvm).2.2
          obtain ⟨fv, a0, y, hfv, -, ha0, hy, -⟩ :=
            src_phi S hBm hfB hgB hph hrel hsrc hPS hsS hsz hvf hvp
          rw [getV_of hfv, ha0] at ha; cases ha
          refine ⟨y, ?_⟩
          rw [SCI.trans_rel _ hrel htr (argListed_of S.wf hBm hfB hvf hfv (args_get_mem ha0)), hy]
        · have hl := hnsrc hvf
          obtain ⟨y, hy⟩ := hsrc (hinR.resolve_right hvf) v hvm
          refine ⟨y, ?_⟩
          rw [hrel.2 v a' hl, hy]
    obtain ⟨y, hy⟩ := hdef
    rw [ha']
    simp only [hy, Option.join_some]
    exact ⟨_, rfl⟩
  · simp only [show (gz.op == .Phi) = false by simpa using hop, Bool.false_eq_true, ↓reduceIte]
    exact ⟨_, rfl⟩

variable {PT : Frame} (hPT : PhiData tabs g gB iT frT PT) (htyS : Typed (Ctx.make tabs f) frS)
include hPT htyS

omit hph hrel hsrc hPS hsS hsz hPT htyS in
theorem shape_eq {x x' : ID} {h h' : Func} {v v' : Value} (hv : h.value? x = some v)
    (hv' : h'.value? x' = some v') (ht : (infoOf tabs f g s).tyEq v.type v'.type = true) :
    tyOf tabs h x = tyOf tabs h' x' := by
  rw [tyOf_shape (I := infoOf tabs f g s) (tabs := tabs) rfl hv,
    tyOf_shape (I := infoOf tabs f g s) (tabs := tabs) rfl hv', tyEq_shape ht]

theorem PT_lt {w : ID} {gw : Value} (hgw : g.value? w = some gw) : w < frT.regs.size := by
  rw [hsz, hsS, ← S.gvsize]; exact lt_of_value? hgw

/-- **The facts after the `Phi`s**: a fact's register holds the source's other phi. -/
theorem post_pin {v w : ID} (hl : (infoOf tabs f g s).look pin v = some w) :
    PT.regs[w]? = PS.regs[v]? := by
  have hBg := gBm S hBm hfB hgB hph hrel hsrc hPS hsS hsz
  have hvm := SCI.look_mem _ hl
  obtain ⟨-, -, hV⟩ := SCI.phisOK_spec _ hph
  obtain ⟨hin, hout⟩ := hV v hvm w hl
  have hvp := (S.vs_mem hvm).2.2
  obtain ⟨fv, hfv, hfvp⟩ := (isPhiIn_iff).1 hvp
  by_cases hwg : w ∈ gB.values
  · obtain ⟨hpg, -, hty, -, a', ha', hsrc1, hsrc2⟩ := hin hwg
    obtain ⟨gw, hgw, -⟩ := value_of_mem S.wfg hBg hgB hwg
    have hop := (isPhiIn_true hgw).1 hpg
    obtain ⟨a'', y, h1, h2, h3⟩ := hPT.phi w hwg gw hgw hop
      (PT_lt S hBm hfB hgB hph hrel hsrc hPS hsS hsz hPT htyS hgw)
    rw [getV_of hgw] at ha' hty
    rw [getV_of hfv] at hty
    rw [ha'] at h1; cases h1
    rw [h3, shape_eq S hBm hfB hgB hgw hfv hty]
    by_cases hvf : v ∈ fB.values
    · obtain ⟨a, ha, htr⟩ := hsrc1 hvf
      obtain ⟨fv', a0, y0, hfv', -, ha0, hy0, hPv⟩ :=
        src_phi S hBm hfB hgB hph hrel hsrc hPS hsS hsz hvf hvp
      rw [hfv] at hfv'; cases hfv'
      rw [getV_of hfv, ha0] at ha; cases ha
      rw [SCI.trans_rel _ hrel htr (argListed_of S.wf hBm hfB hvf hfv (args_get_mem ha0)), hy0] at h2
      cases h2
      rw [hPv]
    · have hE := hrel.2 v a' (hsrc2 hvf)
      rw [hE] at h2
      rw [hPS.keep v (.inl hvf), h2, typed_fix htyS h2]
  · rw [hPT.keep w (.inl hwg)]
    obtain ⟨hout1, hout2⟩ := hout hwg
    by_cases hvf : v ∈ fB.values
    · obtain ⟨a, ha, htr, hty⟩ := hout1 hvf
      obtain ⟨fv', a0, y0, hfv', -, ha0, hy0, hPv⟩ :=
        src_phi S hBm hfB hgB hph hrel hsrc hPS hsS hsz hvf hvp
      rw [hfv] at hfv'; cases hfv'
      rw [getV_of hfv, ha0] at ha; cases ha
      have hla := argListed_of S.wf hBm hfB hvf hfv (args_get_mem ha0)
      obtain ⟨fa, hfa⟩ := value_of_listed S.wf hla
      rw [getV_of hfa, getV_of hfv] at hty
      rw [SCI.trans_rel _ hrel htr hla, hy0, hPv, ← shape_eq S hBm hfB hgB hfa hfv hty,
        typed_fix htyS hy0]
    · rw [hrel.2 v w (hout2 hvf), hPS.keep v (.inl hvf)]

/-- A `Phi` of the block in both functions holds the same value after the `Phi`s. -/
theorem post_phi {a : ID} (haf : a ∈ fB.values) (hpf : isPhiIn f a = true) (hag : a ∈ gB.values)
    (hpg : isPhiIn g a = true) : PT.regs[a]? = PS.regs[a]? := by
  have hBg := gBm S hBm hfB hgB hph hrel hsrc hPS hsS hsz
  obtain ⟨hZ, -, -⟩ := SCI.phisOK_spec _ hph
  obtain ⟨-, hty, w, a0, hw, ha0, htr⟩ := (hZ a hag hpg).1 haf
  obtain ⟨ga, hga, -⟩ := value_of_mem S.wfg hBg hgB hag
  obtain ⟨fa, a1, y1, hfa, -, ha1, hy1, hPa⟩ := src_phi S hBm hfB hgB hph hrel hsrc hPS hsS hsz haf hpf
  rw [getV_of hfa, ha1] at ha0; cases ha0
  rw [getV_of hga] at hw
  rw [getV_of hga, getV_of hfa] at hty
  obtain ⟨w', y, h1, h2, h3⟩ := hPT.phi a hag ga hga ((isPhiIn_true hga).1 hpg)
    (PT_lt S hBm hfB hgB hph hrel hsrc hPS hsS hsz hPT htyS hga)
  rw [hw] at h1; cases h1
  rw [SCI.trans_rel _ hrel htr (argListed_of S.wf hBm hfB haf hfa (args_get_mem ha1)), hy1] at h2
  cases h2
  rw [h3, hPa, shape_eq S hBm hfB hgB hga hfa hty]

/-- A listed register outside `b`'s values that is no source non-`Phi` of the block holds the
same value after the `Phi`s. -/
theorem post_id {a : ID} (hab : a ∉ (infoOf tabs f g s).bvals) (hl : Listed f a)
    (hn : a ∉ Info.nodesOf f fB)
    (hnew : (infoOf tabs f g s).newOK f fB gB = true) : PT.regs[a]? = PS.regs[a]? := by
  by_cases haf : a ∈ fB.values
  · have hpf : isPhiIn f a = true := by
      rw [mem_nodesOf] at hn
      cases h : isPhiIn f a
      · exact absurd ⟨haf, h⟩ hn
      · rfl
    obtain ⟨-, hY, -⟩ := SCI.phisOK_spec _ hph
    obtain ⟨hy1, hy2⟩ := hY a haf hpf
    have hag : a ∈ gB.values := Classical.byContradiction fun h => hab (hy2 h)
    rcases hy1 hag with hpg | ⟨hb, -⟩
    · exact post_phi S hBm hfB hgB hph hrel hsrc hPS hsS hsz hPT htyS haf hpf hag hpg
    · exact absurd hb hab
  · have hag : a ∉ gB.values := fun h => by
      rcases SCI.newOK_spec _ hnew a h with h | h | h
      · exact haf h
      · exact hab h
      · rw [listedIn_of S.wf hl] at h; cases h
    rw [hPT.keep a (.inl hag), hPS.keep a (.inl haf)]
    exact hrel.1 a (fun h => h.elim hab (· hl))

/-- **After the `Phi`s**, `pinRel w a`: target register `w` holds the source's `a`. -/
theorem post_rel {w a : ID}
    (hp : (infoOf tabs f g s).pinRel f g fB gB pin w a = true) (hl : Listed f a)
    (hn : a ∉ Info.nodesOf f fB)
    (hnew : (infoOf tabs f g s).newOK f fB gB = true) : PT.regs[w]? = PS.regs[a]? := by
  rcases (SCI.pinRel_iff _).1 hp with ⟨rfl, hid⟩ | ⟨-, hlk⟩
  · rcases (SCI.idPost_iff _).1 hid with hab | ⟨hpf, hpg, haf, hag⟩
    · exact post_id S hBm hfB hgB hph hrel hsrc hPS hsS hsz hPT htyS hab hl hn hnew
    · exact post_phi S hBm hfB hgB hph hrel hsrc hPS hsS hsz hPT htyS haf hpf hag hpg
  · exact post_pin S hBm hfB hgB hph hrel hsrc hPS hsS hsz hPT htyS hlk

theorem typed_PS : Typed (Ctx.make tabs f) PS :=
  typed_phis htyS hPS.size (fun z hz => hPS.keep z hz)
    (fun z hz v hv hp hlt => hPS.phi z hz v hv hp hlt)
    (fun z hz => by
      obtain ⟨v, hv, -⟩ := value_of_mem S.wf hBm hfB hz
      rw [show (Ctx.make tabs f).f = f from rfl, hv]; rfl)

/-- `b`'s other phis hold values after the `Phi`s, in `b` and in the plan's blocks. -/
theorem pv_def (hbv : B = s.b → ∀ v ∈ (infoOf tabs f g s).vs, v ∈ fB.values) {v : ID}
    (hv : v ∈ (infoOf tabs f g s).vs) (hin : inR = true ∨ B = s.b) :
    ∃ y, PS.regs[v]? = some (some y) := by
  by_cases hvf : v ∈ fB.values
  · obtain ⟨-, -, y, -, -, -, -, h⟩ :=
      src_phi S hBm hfB hgB hph hrel hsrc hPS hsS hsz hvf (S.vs_mem hv).2.2
    exact ⟨_, h⟩
  · rcases hin with hin | hin
    · obtain ⟨y, hy⟩ := hsrc hin v hv
      exact ⟨y, by rw [hPS.keep v (.inl hvf), hy]⟩
    · exact absurd (hbv hin v hv) hvf

end Phis

theorem evalOp_invalid {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val} {ty : Ty}
    (hop : v.op = .Invalid) :
    evalOp env ctx fr v argv ty = .ok (evalPure .Invalid ty v.auxInt v.aux argv) := by
  simp only [evalOp, frameVal, hop]
  rfl

theorem evalValue_invalid {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} (hop : v.op = .Invalid)
    (ha : v.args = #[]) : ∃ y, evalValue env ctx fr v = .ok y := by
  unfold evalValue
  rw [ha]
  simp only [Array.toList_empty, List.mapM_nil, bind, Res.bind, pure]
  simp only [evalOp_invalid hop]
  exact ⟨_, rfl⟩

theorem params_eq' {tabs : Tables} {f g : Func} (h : g.ownAux = f.ownAux) :
    (Ctx.make tabs g).params = (Ctx.make tabs f).params := by
  simp only [Ctx.make, abiParams, h]

theorem home_invalid {I : Info} {f g : Func} {fB : Block} {out : Facts} {x : ID}
    (hx : ¬ (x ∈ fB.values ∧ isPhiIn f x = false)) (hop : (g.getV x).op = .Invalid) :
    I.home f g fB out x = none := by
  unfold Info.home
  have h1 : (fB.values.contains x && !isPhiIn f x) = false := by
    cases h : fB.values.contains x <;> cases h' : isPhiIn f x <;> simp_all [contains_iff]
  simp only [h1, Bool.false_eq_true, ↓reduceIte]
  simp only [hop, beq_self_eq_true, ↓reduceIte]

theorem home_phi {I : Info} {f g : Func} {fB : Block} {out : Facts} {x : ID}
    (hx : ¬ (x ∈ fB.values ∧ isPhiIn f x = false)) (hop : (g.getV x).op ≠ .Invalid)
    (hxf : x ∈ fB.values) : I.home f g fB out x = some x := by
  unfold Info.home
  have h1 : (fB.values.contains x && !isPhiIn f x) = false := by
    cases h : fB.values.contains x <;> cases h' : isPhiIn f x <;> simp_all [contains_iff]
  have h2 : ((g.getV x).op == .Invalid) = false := by simpa using hop
  simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, contains_iff.2 hxf]
  split <;> rfl

/-- Two frames of one activation: the same fields but the registers. -/
def SameAct (a b : Frame) : Prop :=
  a.args = b.args ∧ a.mem0 = b.mem0 ∧ a.images = b.images ∧ a.closure = b.closure

theorem SameAct.of {a c : Frame} (h : a = { c with regs := a.regs }) : SameAct a c := by
  rw [h]; exact ⟨rfl, rfl, rfl, rfl⟩

theorem SameAct.trans {a b c : Frame} (h1 : SameAct a b) (h2 : SameAct b c) : SameAct a c :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1, h1.2.2.2.trans h2.2.2.2⟩

theorem SameAct.symm {a b : Frame} (h : SameAct a b) : SameAct b a :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩

theorem SameAct.eq {a b : Frame} (h : SameAct a b) : a = { b with regs := a.regs } := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases a; cases b; simp_all

theorem args_one {v : Value} {w : ID} (hs : v.args.size = 1) (h : v.args[0]? = some w) :
    v.args = #[w] := by
  apply Array.ext
  · simp [hs]
  · intro i h1 h2
    have : i = 0 := by simp at h2; omega
    subst this
    simp only [List.getElem_toArray, List.getElem_cons_zero]
    exact (Array.getElem?_eq_some_iff.1 h).2

/-! ## The non-`Phi`s of a checked block -/

/-- The expected result of target value `x`: the source's register `home x` in `G`. -/
def expOf (I : Info) (f g : Func) (fB : Block) (out : Facts) (G : Frame) (x : ID) : Option Val :=
  (I.home f g fB out x).bind fun a => (G.regs[a]?).join

section Nodes

variable {ce : CheckEnv} {tabs : Tables} {f g : Func} {s : Site} (S : Setup ce tabs f g s)
  {B : ID} {fB gB : Block} (hBm : B ∈ f.blocks) (hfB : f.block? B = some fB)
  (hgB : g.block? B = some gB)
  {pin out : Facts} {iT iS : Nat} {E : Facts} {inR inRb : Bool}
  (hph : (infoOf tabs f g s).phisOK f g fB gB pin iT iS E inR = true)
  {frS frT : Frame} (hrel : FactsRel (infoOf tabs f g s) f E frS frT)
  (hsrc : inR = true → SrcB (infoOf tabs f g s) frS)
  {PS : Frame} (hPS : PhiData tabs f fB iS frS PS) (hsS : frS.regs.size = f.valueTab.size)
  (hsz : frT.regs.size = frS.regs.size)
  {PT : Frame} (hPT : PhiData tabs g gB iT frT PT) (htyS : Typed (Ctx.make tabs f) frS)
  (hnodes : (infoOf tabs f g s).nodesOK f g fB gB pin out inRb = true)
  (hnew : (infoOf tabs f g s).newOK f fB gB = true)
  (hinRb : inRb = true → inR = true ∨ B = s.b)
  (hbv : B = s.b → ∀ v ∈ (infoOf tabs f g s).vs, v ∈ fB.values)
  (hfrS : frT = { frS with regs := frT.regs })
  {env : Env} {G : Frame} {Done : ID → Prop} (hG : G = { PS with regs := G.regs })
  (hGs : G.regs.size = PS.regs.size)
  (hDone : ∀ x, Done x → x ∈ Info.nodesOf f fB)
  (hGd : ∀ x, Done x → ∃ fx y, f.value? x = some fx ∧ G.regs[x]? = some (some y) ∧
    evalValue env (Ctx.make tabs f) G fx = .ok y)
  (hGk : ∀ z, ¬ Done z → G.regs[z]? = PS.regs[z]?)
include S hBm hfB hgB hph hrel hsrc hPS hsS hsz hPT htyS hnodes hnew hinRb hbv hfrS hG hGs hDone
  hGd hGk


/-- **An argument of a target value** where the source reads `a`: its register holds `a`'s
source value. -/
theorem arg_val {gr : Frame} {x : ID} (hgr : gr = { PT with regs := gr.regs })
    (hout : ∀ a ∈ argsF g x, a ∉ Info.nodesOf g gB → gr.regs[a]? = PT.regs[a]?)
    (hin : ∀ a ∈ argsF g x, a ∈ Info.nodesOf g gB → ∃ z, gr.regs[a]? = some (some z) ∧
      ∀ y, expOf (infoOf tabs f g s) f g fB out G a = some y → z = y)
    {w a : ID} (hw : w ∈ argsF g x) (hl : Listed f a) {ya : Val}
    (hya : G.regs[a]? = some (some ya))
    (hr : (infoOf tabs f g s).argRel f g fB gB pin out w a = true) :
    gr.regs[w]? = some (some ya) := by
  rcases (SCI.argRel_iff _).1 hr with ⟨hwn, hh⟩ | ⟨hwn, han, hp⟩
  · obtain ⟨z, hz, hze⟩ := hin w hw hwn
    rw [hz, hze ya (by simp only [expOf, hh, Option.bind_some, hya, Option.join_some])]
  · rw [hout w hw hwn, post_rel S hBm hfB hgB hph hrel hsrc hPS hsS hsz hPT htyS hp hl han hnew,
      ← hGk a (fun hd => han (hDone a hd)), hya]

/-- **A source non-`Phi` of the block evaluates in the target as in the source** (its arguments
renamed, `argRel`). -/
theorem src_node_step {x : ID} (hsn : x ∈ fB.values ∧ isPhiIn f x = false) {fx : Value}
    (hfx : f.value? x = some fx)
    (hnst : ∀ msg, evalValue env (Ctx.make tabs f) G fx ≠ .stuck msg)
    {gr : Frame} (hgr : gr = { PT with regs := gr.regs })
    (hout : ∀ a ∈ argsF g x, a ∉ Info.nodesOf g gB → gr.regs[a]? = PT.regs[a]?)
    (hin : ∀ a ∈ argsF g x, a ∈ Info.nodesOf g gB → ∃ z, gr.regs[a]? = some (some z) ∧
      ∀ y, expOf (infoOf tabs f g s) f g fB out G a = some y → z = y) :
    stepV env (Ctx.make tabs g) gr x = evalValue env (Ctx.make tabs f) G fx := by
  have hBg := gBm S hBm hfB hgB hph hrel hsrc hPS hsS hsz
  have hx : x ∈ Info.nodesOf g gB := ((SCI.nodesOK_spec _ hnodes).1 x (mem_nodesOf.2 hsn)).1
  obtain ⟨gx, hgx, hgxid, -⟩ := value_of_mem S.wfg hBg hgB (mem_nodesOf.1 hx).1
  have hspec := SCI.nodeOK_spec _ ((SCI.nodesOK_spec _ hnodes).2 x hx)
  have hfr : gr = { G with regs := gr.regs } :=
    ((SameAct.of hgr).trans ((SameAct.of hPT.frame).trans ((SameAct.of hfrS).trans
      ((SameAct.of hG).trans (SameAct.of hPS.frame)).symm))).eq
  have hstep : stepV env (Ctx.make tabs g) gr x = evalValue env (Ctx.make tabs g) gr gx := by
    unfold stepV; rw [show (Ctx.make tabs g).f = g from rfl, hgx]
  rw [hstep]
  have hfxid' : fx.id = x := by
    obtain ⟨fx', hfx', h⟩ := value_of_mem S.wf hBm hfB hsn.1; rw [hfx] at hfx'; cases hfx'; exact h.1
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := SCI.sameNode_spec _ (hspec.1 hsn)
  rw [getV_of hgx, getV_of hfx] at h1 h2 h3 h4 h5 h6
  have hargs : ∀ (k : Nat) (a : ID), fx.args[k]? = some a → ∃ a' ya, gx.args[k]? = some a' ∧
      G.regs[a]? = some (some ya) ∧ gr.regs[a']? = some (some ya) := by
    intro k a ha
    obtain ⟨ya, hya⟩ := evalValue_args_def hnst a (args_get_mem ha)
    have hk : k < gx.args.size := by rw [h5]; exact (Array.getElem?_eq_some_iff.1 ha).1
    refine ⟨gx.args[k], ya, by simp [hk], hya, ?_⟩
    exact arg_val S hBm hfB hgB hph hrel hsrc hPS hsS hsz hPT htyS hnodes hnew hinRb hbv hfrS hG
      hGs hDone hGd hGk hgr (fun a ha h => hout a ha h) (fun a ha h => hin a ha h)
      (by rw [show argsF g x = gx.args.toList from argsF_of hgx]
          exact Array.mem_toList_iff.2 (Array.getElem_mem hk))
      (argListed_of S.wf hBm hfB hsn.1 hfx (args_get_mem ha)) hya
      (h6 k _ a (by simp [hk]) ha)
  have hty' : (Ctx.make tabs g).tys[fx.id]? = (Ctx.make tabs f).tys[fx.id]? := by
    rw [hfxid', tys_of_tyOf hgx, tys_of_tyOf hfx, tyOf_eq hgx, tyOf_eq hfx, h2]
  exact evalValue_eq_of_args (ctx := Ctx.make tabs f) (ctx' := Ctx.make tabs g) (fr := G)
    (fr' := gr) (v := fx) (v' := gx) h1 h3 h4 (by rw [hgxid, hfxid']) h5 hargs hfr hty' rfl
    (params_eq' (tabs := tabs) S.gownAux) rfl

/-- **Each target non-`Phi` evaluates to its expected result** (`nodeOK`). -/
theorem node_loc {x : ID} (hx : x ∈ Info.nodesOf g gB)
    (hxd : x ∈ fB.values → isPhiIn f x = false → Done x) :
    MapLoc env (Ctx.make tabs g) PT (· ∈ Info.nodesOf g gB) (expOf (infoOf tabs f g s) f g fB out G)
      x := by
  intro gr hgr hout hin
  have hBg := gBm S hBm hfB hgB hph hrel hsrc hPS hsS hsz
  obtain ⟨gx, hgx, hgxid, -⟩ := value_of_mem S.wfg hBg hgB (mem_nodesOf.1 hx).1
  have hspec := SCI.nodeOK_spec _ ((SCI.nodesOK_spec _ hnodes).2 x hx)
  have hfr : gr = { G with regs := gr.regs } :=
    ((SameAct.of hgr).trans ((SameAct.of hPT.frame).trans ((SameAct.of hfrS).trans
      ((SameAct.of hG).trans (SameAct.of hPS.frame)).symm))).eq
  have hstep : stepV env (Ctx.make tabs g) gr x = evalValue env (Ctx.make tabs g) gr gx := by
    unfold stepV; rw [show (Ctx.make tabs g).f = g from rfl, hgx]
  have hargsF : argsF (Ctx.make tabs g).f x = gx.args.toList := argsF_of hgx
  rw [hstep]
  by_cases hsn : x ∈ fB.values ∧ isPhiIn f x = false
  · -- a source non-`Phi`: the same evaluation
    obtain ⟨fx, y, hfx, hGx, hev⟩ := hGd x (hxd hsn.1 hsn.2)
    refine ⟨y, ?_, fun y' hy' => ?_⟩
    · rw [← hstep, src_node_step S hBm hfB hgB hph hrel hsrc hPS hsS hsz hPT htyS hnodes hnew hinRb
        hbv hfrS hG hGs hDone hGd hGk hsn hfx (by rw [hev]; nofun) hgr hout hin, hev]
    · have hh := ((SCI.nodesOK_spec _ hnodes).1 x ((mem_nodesOf).2 hsn)).2
      simp only [expOf, hh, Option.bind_some, hGx, Option.join_some, Option.some.injEq] at hy'
      exact hy'
  · by_cases hinv : (g.getV x).op = .Invalid
    · obtain ⟨ha, -⟩ := hspec.2.1 hsn hinv
      rw [getV_of hgx] at hinv ha
      obtain ⟨y, hy⟩ := evalValue_invalid (env := env) (ctx := Ctx.make tabs g) (fr := gr) hinv ha
      refine ⟨y, hy, fun y' hy' => ?_⟩
      have hinv' : (g.getV x).op = .Invalid := by rw [getV_of hgx]; exact hinv
      rw [expOf, home_invalid hsn hinv'] at hy'
      cases hy'
    · have hnd : ¬ Done x := fun hd => hsn ((mem_nodesOf).1 (hDone x hd))
      by_cases hxf : x ∈ fB.values
      · -- one of `b`'s phis that became a `Copy`
        have hpf : isPhiIn f x = true := by
          cases h : isPhiIn f x
          · exact absurd ⟨hxf, h⟩ hsn
          · rfl
        obtain ⟨-, hY, -⟩ := SCI.phisOK_spec _ hph
        have hxg := (mem_nodesOf.1 hx)
        rcases (hY x hxf hpf).1 hxg.1 with hpg | ⟨-, hc | ⟨hcp, hty, hs1, w, a, hw, ha, htr, hwg⟩⟩
        · rw [hxg.2] at hpg; cases hpg
        · exact absurd hc.1 hinv
        rw [getV_of hgx] at hcp hty hs1 hw
        have hargs := args_one hs1 hw
        obtain ⟨fx, a0, ya, hfx, -, ha0, hya, hPx⟩ :=
          src_phi S hBm hfB hgB hph hrel hsrc hPS hsS hsz hxf hpf
        rw [getV_of hfx, ha0] at ha; cases ha
        rw [getV_of hfx] at hty
        have hwn : w ∉ Info.nodesOf g gB := fun h => hwg (mem_nodesOf.1 h).1
        have hgw : gr.regs[w]? = some (some ya) := by
          rw [hout w (by rw [hargsF, hargs]; simp) hwn, hPT.keep w (.inl hwg),
            SCI.trans_rel _ hrel htr (argListed_of S.wf hBm hfB hxf hfx (args_get_mem ha0)), hya]
        refine ⟨_, evalValue_copy hcp hargs hgw, fun y' hy' => ?_⟩
        rw [expOf, home_phi hsn hinv hxf] at hy'
        simp only [Option.bind_some, hGk x hnd, hPx, Option.join_some, Option.some.injEq] at hy'
        rw [← hy', hgxid]
        show ya.retype (tyOf tabs g x) = _
        rw [shape_eq S hBm hfB hgB hgx hfx hty]
      · -- a carrier of a fact
        obtain ⟨v, hhv, hinb, hcp, hty, hs1, w, hw, hwn1, hwn2⟩ :=
          SCI.carrierOK_spec _ (hspec.2.2.2 hsn hinv hxf)
        rw [getV_of hgx] at hcp hty hs1 hw
        have hargs := args_one hs1 hw
        have hvm : v ∈ (infoOf tabs f g s).vs := by
          rcases SCI.home_eq_some _ hhv with ⟨h, -⟩ | ⟨-, -, ⟨h, -⟩ | ⟨-, h, -⟩⟩
          · exact absurd h hxf
          · exact absurd h hxf
          · exact h
        obtain ⟨fv, hfv, hfvp⟩ := isPhiIn_iff.1 (S.vs_mem hvm).2.2
        rw [getV_of hfv] at hty
        obtain ⟨yv, hyv⟩ := pv_def S hBm hfB hgB hph hrel hsrc hPS hsS hsz hPT htyS hbv hvm
          (hinRb hinb)
        have hvnd : ¬ Done v := fun hd => by
          have := (mem_nodesOf.1 (hDone v hd)).2
          rw [(S.vs_mem hvm).2.2] at this; cases this
        have hgw : gr.regs[w]? = some (some yv) := by
          by_cases hwn : w ∈ Info.nodesOf g gB
          · obtain ⟨z, hz, hze⟩ := hin w (by rw [hargsF, hargs]; simp) hwn
            rw [hz, hze yv (by simp only [expOf, hwn1 hwn, Option.bind_some, hGk v hvnd, hyv,
              Option.join_some])]
          · rw [hout w (by rw [hargsF, hargs]; simp) hwn,
              post_pin S hBm hfB hgB hph hrel hsrc hPS hsS hsz hPT htyS (hwn2 hwn), hyv]
        refine ⟨_, evalValue_copy hcp hargs hgw, fun y' hy' => ?_⟩
        simp only [expOf, hhv, Option.bind_some, hGk v hvnd, hyv, Option.join_some,
          Option.some.injEq] at hy'
        rw [← hy', hgxid]
        show yv.retype (tyOf tabs g x) = _
        rw [shape_eq S hBm hfB hgB hgx hfv hty]
        exact typed_fix (typed_PS S hBm hfB hgB hph hrel hsrc hPS hsS hsz hPT htyS) hyv

end Nodes

end GoFV.Proof.ShortCirc

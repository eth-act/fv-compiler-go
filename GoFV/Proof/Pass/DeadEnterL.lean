import GoFV.Proof.Pass.DeadRelL

/-!
# Removing dead values in lowered code: entering a kept block under `runL`

`GoFV.Proof.Pass.DeadEnter` over `runL`'s runner (any mode `md`, the same for source and target;
`g.lowered = f.lowered`, so both contexts give a value the same shape): `targetPreL`, `enter_okL`
and `enter_panicL` (for `md.faulting = false`: the panicking root is `PanickingL false`, so it is
kept, `DeadRelL.dropped`). A kept `MOVDreg`/`MOVDnop` reads the same sign extension of its
argument in both (`DeadRelL.op`, `evalKeptL`).
-/

namespace GoFV.Proof.Dead

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof
open GoFV.Proof.CopyElim (topoRem_append_left topoRem_at topoRem_before nodeOf_schedNodes)

variable {f g : Func} {K : ID → Prop}

namespace Setup

variable (S : Setup f g K) (L : DeadRelL f g K)

include S L in
/-- A kept non-`Phi`, in a frame agreeing with `G` on its arguments, evaluates in the target as
the source value does in `G` (`evalKept` for `runL`). -/
theorem evalKeptL (hlow : g.lowered = f.lowered) {md : LMode} {tabs : Tables} {env : Env}
    {bid : ID} (hb : K bid) {gb fb : Block}
    (hgb : g.block? bid = some gb) (hfb : f.block? bid = some fb) {x : ID} (hx : x ∈ gb.values)
    {gv fv : Value} (hgv : g.value? x = some gv) (hfv : f.value? x = some fv)
    (hgn : gv.op ≠ .Phi) {G g' : Frame} {r : Res Val}
    (hev : evalValueL md env (Ctx.makeL tabs f) G fv = r) (hr : ∀ msg, r ≠ .stuck msg)
    (hg' : g' = { G with regs := g'.regs }) (hag : ∀ a ∈ argsF g x, g'.regs[a]? = G.regs[a]?) :
    stepVL md env (Ctx.makeL tabs g) g' x = r := by
  obtain ⟨ce', hwg⟩ := S.wg
  obtain ⟨gv', fv', hgv', hfv', hgid, hfid, -, hty, -, hsame⟩ := S.value hb hgb hfb hx
  rw [hgv] at hgv'; cases hgv'
  rw [hfv] at hfv'; cases hfv'
  obtain ⟨hop, haux, hai, hargs⟩ := hsame hgn
  rw [stepVL_of (ctx := Ctx.makeL tabs g) (by rw [makeL_f]; exact hgv), ← hev]
  have hdef := evalValueL_args_def (fun msg he => hr msg (hev ▸ he))
  refine evalValueL_eq_of_args hop haux hai (hgid.trans hfid.symm) (by rw [hargs])
    (fun k a hk => ?_) hg' ?_ (by rw [tabs_makeL, tabs_makeL])
    (by rw [params_makeL, params_makeL]; exact params_eq S.rel.ownAux)
    (by rw [act_makeL, act_makeL]; rfl) ?_
  · obtain ⟨y, hy⟩ := hdef a (Array.mem_of_getElem? hk)
    refine ⟨a, y, by rw [hargs]; exact hk, hy, ?_⟩
    rw [hag a (by rw [argsF_of hgv, hargs]; exact Array.mem_toList_iff.2 (Array.mem_of_getElem? hk)),
      hy]
  · rw [hfid, tys_of_valueL hgv, tys_of_valueL hfv, hty, hlow]
  · rw [makeL_f, makeL_f]
    unfold sxOf
    rw [hargs]
    cases ha0 : fv.args[0]? with
    | none => rfl
    | some a =>
      obtain ⟨b', gb', hb', ha'⟩ : Listed g a :=
        hwg.argListed _ _ _ _ ⟨⟨S.rel.sub bid hb, hgb⟩, hx, hgv⟩ a
          (by rw [hargs]; exact Array.mem_of_getElem? ha0)
      obtain ⟨ga, hga, -, -⟩ := hwg.valueId b' gb' hb' a ha'
      obtain ⟨fa, hfa, -⟩ := L.op a ga hga
      simp only [Option.bind_some, hga, hfa, Option.map_some,
        L.signExtendsIn_eq hwg ⟨b', gb', hb', ha'⟩ hga hfa]

include S in
/-- **The target's `Phi`s and schedule** (`targetPre` for `runL`). -/
theorem targetPreL (hlow : g.lowered = f.lowered) {md : LMode} {tabs : Tables} {bid : ID} (hb : K bid) {gb fb : Block}
    (hgb : g.block? bid = some gb) (hfb : f.block? bid = some fb) {frS frT : Frame}
    {iS iT : Nat} (hA : Agree g frS frT) (hsz : frS.regs.size = f.valueTab.size)
    (hP : PhiArgs f g bid iS iT) {psS : List (ID × Val)}
    (hpsS : fb.values.toList.filterMapM (phiStepL md (Ctx.makeL tabs f) frS iS) = .ok psS)
    {oS : Array ID} (hso : schedule f fb = some oS) :
    ∃ psT oT, gb.values.toList.filterMapM (phiStepL md (Ctx.makeL tabs g) frT iT) = .ok psT ∧
      schedule g gb = some oT ∧ (setPhis psT frT.regs).size = frS.regs.size ∧
      ∀ a, Listed g a → a ∉ oT.toList →
        (setPhis psT frT.regs)[a]? = (setPhis psS frS.regs)[a]? ∧ a ∉ oS.toList := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  obtain ⟨-, -, hbf, -, -, hsub⟩ := S.blockFacts hb hgb hfb
  have hndF := hwf.valuesNodup _ _ ⟨hbf, hfb⟩
  have hbm := S.rel.sub bid hb
  have hndG := hwg.valuesNodup _ _ ⟨hbm, hgb⟩
  obtain ⟨-, -, hkeepS, hphiS⟩ := phisL_spec hndF hpsS
  rw [makeL_f] at hkeepS hphiS
  obtain ⟨-, -, omemS⟩ := schedule_topo (valuesOwn hwf hbf hfb) hndF hso
  -- a kept `Phi` reads the same register in both
  have hphiEq : ∀ z ∈ gb.values, ∀ gv fv, g.value? z = some gv → f.value? z = some fv →
      gv.op = .Phi → ∃ a y, fv.args[iS]? = some a ∧ frS.regs[a]? = some (some y) ∧
        gv.args[iT]? = some a ∧ frT.regs[a]? = some (some y) := by
    intro z hz gv fv hgv hfv hgph
    obtain ⟨gv', fv', hgv', hfv', -, -, hzf, -, hph, -⟩ := S.value hb hgb hfb hz
    rw [hgv] at hgv'; cases hgv'
    rw [hfv] at hfv'; cases hfv'
    obtain ⟨a, y, ha, hy, -⟩ := hphiS z hzf fv hfv (hph.1 hgph) (by rw [hsz]; exact lt_of_value? hfv)
    obtain ⟨fv', hfv', hga⟩ := hP gb hgb z hz gv hgv hgph
    rw [hfv] at hfv'; cases hfv'
    rw [ha] at hga
    have hl : Listed g a := hwg.argListed _ _ _ _ ⟨⟨hbm, hgb⟩, hz, hgv⟩ a (Array.mem_of_getElem? hga)
    exact ⟨a, y, ha, hy, hga, by rw [hA.2.2 a hl]; exact hy⟩
  obtain ⟨psT, hpsT⟩ : ∃ psT, gb.values.toList.filterMapM
      (phiStepL md (Ctx.makeL tabs g) frT iT) = .ok psT := by
    refine filterMapM_phiL_ok fun z hz => ?_
    rw [Array.mem_toList_iff] at hz
    obtain ⟨gv, fv, hgv, hfv, -, -, -, -, -, -⟩ := S.value hb hgb hfb hz
    by_cases hgph : gv.op = .Phi
    · obtain ⟨a, y, -, -, hga, hy⟩ := hphiEq z hz gv fv hgv hfv hgph
      refine ⟨some (z, md.retype ((Ctx.makeL tabs g).tys[z]?.getD .other) y), ?_⟩
      unfold phiStepL
      simp only [makeL_f, hgv, hgph, beq_self_eq_true, ite_true, hga, hy, Option.join]
      rfl
    · refine ⟨none, ?_⟩
      unfold phiStepL
      simp only [makeL_f, hgv, show (gv.op == .Phi) = false by simpa using hgph]
      rfl
  obtain ⟨oT, hoT⟩ := S.targetSched hb hgb hfb hso
  obtain ⟨-, -, omemT⟩ := schedule_topo (valuesOwn hwg hbm hgb) hndG hoT
  obtain ⟨hszT, -, hkeepT, hphiT⟩ := phisL_spec hndG hpsT
  rw [makeL_f] at hkeepT hphiT
  refine ⟨psT, oT, hpsT, hoT, by rw [hszT, hA.2.1], fun a hl ha => ?_⟩
  by_cases haf : a ∈ fb.values
  · have hag := S.keptIn hb hgb hfb hl haf
    obtain ⟨gv, fv, hgv, hfv, -, -, -, hty, hph, -⟩ := S.value hb hgb hfb hag
    have hgph : gv.op = .Phi := Classical.byContradiction fun hne =>
      ha ((omemT a).2 ⟨hag, gv, hgv, hne⟩)
    have hlt : a < frT.regs.size := by rw [hA.2.1, hsz]; exact lt_of_value? hfv
    obtain ⟨a', y, ha', hy, hga', hyT⟩ := hphiEq a hag gv fv hgv hfv hgph
    obtain ⟨b1, y1, hb1, hy1, hT⟩ := hphiT a hag gv hgv hgph hlt
    rw [hga'] at hb1; cases hb1
    rw [hyT] at hy1; cases hy1
    obtain ⟨b2, y2, hb2, hy2, hS⟩ := hphiS a haf fv hfv (hph.1 hgph) (by rw [← hA.2.1]; exact hlt)
    rw [ha'] at hb2; cases hb2
    rw [hy] at hy2; cases hy2
    refine ⟨by rw [hT, hS, tys_of_valueL hgv, tys_of_valueL hfv, hty, hlow], fun hm => ?_⟩
    obtain ⟨-, fv', hfv', hne⟩ := (omemS a).1 hm
    rw [hfv] at hfv'; cases hfv'
    exact hne (hph.1 hgph)
  · have hag : a ∉ gb.values := fun h => haf (hsub a h)
    refine ⟨by rw [hkeepT a (.inl hag), hkeepS a (.inl haf), hA.2.2 a hl], fun hm => ?_⟩
    exact haf ((omemS a).1 hm).1

include S L in
/-- **A block the source enters successfully is entered by the target** (`enter_ok` for
`runL`). -/
theorem enter_okL (hlow : g.lowered = f.lowered) {md : LMode} {tabs : Tables} {env : Env} {bid : ID} (hb : K bid)
    {gb fb : Block} (hgb : g.block? bid = some gb) (hfb : f.block? bid = some fb)
    {frS frT : Frame} {iS iT : Nat} (hA : Agree g frS frT) (hsz : frS.regs.size = f.valueTab.size)
    (hP : PhiArgs f g bid iS iT) {G : Frame}
    (h : enterBlockL md env (Ctx.makeL tabs f) frS fb iS = .ok G) :
    ∃ GT, enterBlockL md env (Ctx.makeL tabs g) frT gb iT = .ok GT ∧ Agree g G GT ∧
      G.regs.size = f.valueTab.size := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  obtain ⟨hgid, hfid, hbf, -, -, -⟩ := S.blockFacts hb hgb hfb
  have hndF := hwf.valuesNodup _ _ ⟨hbf, hfb⟩
  have hbm := S.rel.sub bid hb
  have hndG := hwg.valuesNodup _ _ ⟨hbm, hgb⟩
  rw [enterBlockL_eq] at h
  cases hpsS : fb.values.toList.filterMapM (phiStepL md (Ctx.makeL tabs f) frS iS) with
  | panic e m => rw [hpsS] at h; cases h
  | stuck msg => rw [hpsS] at h; cases h
  | ok psS =>
  rw [hpsS] at h
  change (Res.ofOption _ ((Ctx.makeL tabs f).sched[fb.id]?).join).bind _ = _ at h
  rw [hfid, sched_of_blockL hfb] at h
  cases hso : schedule f fb with
  | none => rw [hso] at h; cases h
  | some oS =>
  rw [hso] at h
  change evalAllL md env (Ctx.makeL tabs f) _ oS.toList = .ok G at h
  obtain ⟨psT, oT, hpsT, hoT, hszT, hagree⟩ := S.targetPreL hlow hb hgb hfb hA hsz hP hpsS hso
  obtain ⟨ond, otopo, omemS⟩ := schedule_topo (valuesOwn hwf hbf hfb) hndF hso
  obtain ⟨ondT, otopoT, omemT⟩ := schedule_topo (valuesOwn hwg hbm hgb) hndG hoT
  obtain ⟨hszP, -, -, -⟩ := phisL_spec hndF hpsS
  obtain ⟨e1, e2, e3, e4⟩ := evalAllL_spec ond (by rw [makeL_f]; exact otopo)
    (by rw [makeL_f]; simp [hszP, hsz]) h
  -- the kept values outside the target's schedule agree with `G`
  have hout : ∀ a, Listed g a → a ∉ oT.toList → (setPhis psT frT.regs)[a]? = G.regs[a]? := by
    intro a hl ha
    obtain ⟨h1, h2⟩ := hagree a hl ha
    rw [h1, e3 a h2]
  have hloc : LocalOKL md env (Ctx.makeL tabs g) G oT.toList := by
    intro x hx
    obtain ⟨hxg, gv, hgv, hgn⟩ := (omemT x).1 hx
    obtain ⟨gv', fv, hgv', hfv, -, -, hxf, -, hph, -⟩ := S.value hb hgb hfb hxg
    rw [hgv] at hgv'; cases hgv'
    obtain ⟨v, y, hv, hy, hev⟩ := e4 x ((omemS x).2 ⟨hxf, fv, hfv, fun h => hgn (hph.2 h)⟩)
    rw [makeL_f] at hv
    rw [hfv] at hv; cases hv
    exact ⟨y, hy, fun g' hg' hag =>
      S.evalKeptL L hlow hb hgb hfb hxg hgv hfv hgn hev (fun _ h => nomatch h) hg'
        (fun a ha => hag a (by rw [makeL_f]; exact ha))⟩
  have hinit : ({ frT with regs := setPhis psT frT.regs } : Frame) =
      { G with regs := setPhis psT frT.regs } :=
    (with_regs hA.1 _).trans (with_regs e1 _).symm
  obtain ⟨GT, h1, h2, h3, h4, -⟩ := evalAllL_ref
    (S := fun a => a ∉ oT.toList ∧ (setPhis psT frT.regs)[a]? = G.regs[a]?)
    (g := { frT with regs := setPhis psT frT.regs }) hloc
    (by
      rw [makeL_f]
      exact refOK_of_topo otopoT fun x hx a ha hna => by
        obtain ⟨hxg, gv, hgv, -⟩ := (omemT x).1 hx
        rw [argsF_of hgv] at ha
        exact ⟨hna, hout a (hwg.argListed _ _ _ _ ⟨⟨hbm, hgb⟩, hxg, hgv⟩ a
          (Array.mem_toList_iff.1 ha)) hna⟩)
    (fun a ha => ha.2) hinit (by rw [e2]; simpa [hszP] using hszT)
  refine ⟨GT, ?_, ⟨h2, h3, fun a hl => h4 a ?_⟩, by rw [e2]; simpa [hsz] using hszP⟩
  · rw [enterBlockL_eq, hpsT]
    change (Res.ofOption _ ((Ctx.makeL tabs g).sched[gb.id]?).join).bind _ = _
    rw [hgid, sched_of_blockL hgb, hoT]
    exact h1
  · by_cases ha : a ∈ oT.toList
    · exact .inr ha
    · exact .inl ⟨ha, hout a hl ha⟩

include S L in
/-- **A block the source panics in makes the target panic alike** (`enter_panic` for `runL`,
memory ops not faulting). -/
theorem enter_panicL (hlow : g.lowered = f.lowered) {md : LMode} (hmd : md.faulting = false) {tabs : Tables} {env : Env}
    {bid : ID} (hb : K bid) {gb fb : Block}
    (hgb : g.block? bid = some gb) (hfb : f.block? bid = some fb) {frS frT : Frame}
    {iS iT : Nat} (hA : Agree g frS frT) (hsz : frS.regs.size = f.valueTab.size)
    (hP : PhiArgs f g bid iS iT) {e : Panic} {m : Mem}
    (h : enterBlockL md env (Ctx.makeL tabs f) frS fb iS = .panic e m) :
    enterBlockL md env (Ctx.makeL tabs g) frT gb iT = .panic e m := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  obtain ⟨hgid, hfid, hbf, -, -, -⟩ := S.blockFacts hb hgb hfb
  have hownF := valuesOwn hwf hbf hfb
  have hndF := hwf.valuesNodup _ _ ⟨hbf, hfb⟩
  have hbm := S.rel.sub bid hb
  have hownG := valuesOwn hwg hbm hgb
  have hndG := hwg.valuesNodup _ _ ⟨hbm, hgb⟩
  obtain ⟨psS, oS, hpsS, hso, hev⟩ := enterBlockL_panic h
  rw [hfid, sched_of_blockL hfb] at hso
  obtain ⟨pre, r, post, Gpre, hsplit, hpre, hrp⟩ := evalAllL_panic_split hev
  obtain ⟨psT, oT, hpsT, hoT, hszT, hagree⟩ := S.targetPreL hlow hb hgb hfb hA hsz hP hpsS hso
  obtain ⟨ond, otopo, omemS⟩ := schedule_topo hownF hndF hso
  obtain ⟨ondT, otopoT, omemT⟩ := schedule_topo hownG hndG hoT
  obtain ⟨hszP, -, -, -⟩ := phisL_spec hndF hpsS
  rw [hsplit] at ond otopo
  obtain ⟨e1, e2, e3, e4⟩ := evalAllL_spec (List.nodup_append.1 ond).1
    (by rw [makeL_f]; exact topoRem_append_left otopo) (by rw [makeL_f]; simp [hszP, hsz]) hpre
  -- the panicking root is kept
  have hrS : r ∈ oS.toList := by rw [hsplit]; simp
  obtain ⟨hrf, fvr, hfvr, hrnph⟩ := (omemS r).1 hrS
  rw [stepVL_of (ctx := Ctx.makeL tabs f) (by rw [makeL_f]; exact hfvr)] at hrp
  have hrop : PanickingL false fvr.op := hmd ▸ evalValueL_panic_op hrp
  have hrg : r ∈ gb.values := Classical.byContradiction fun hn =>
    L.dropped bid hb gb fb hgb hfb r hrf hn fvr hfvr hrop
  obtain ⟨gvr, fvr', hgvr, hfvr', -, -, -, -, hphr, hsamer⟩ := S.value hb hgb hfb hrg
  rw [hfvr] at hfvr'; cases hfvr'
  have hgrn : gvr.op ≠ .Phi := fun h => hrnph (hphr.1 h)
  have hrT : r ∈ oT.toList := (omemT r).2 ⟨hrg, gvr, hgvr, hgrn⟩
  obtain ⟨pre', post', hsplitT⟩ := List.append_of_mem hrT
  -- what the target evaluates before `r`, the source evaluated before `r` (#96)
  have hk : oS.toList[pre.length]? = some r := by rw [hsplit]; simp
  have hk' : oT.toList[pre'.length]? = some r := by rw [hsplitT]; simp
  have hrnp : npIn (schedNodes g gb).toList r = true := by
    unfold npIn
    rw [nodeOf_schedNodes hownG hndG hrg hgvr hgrn, (hsamer hgrn).1]
    simpa using prio_panickingL hrop
  have htr := sched_transfer_sub (schedule_spec hso) (schedule_spec hoT) (S.subNodes hb hgb hfb)
    hk hk' hrnp
  have hinPre : ∀ x, (∃ i < pre.length, oS.toList[i]? = some x) → x ∈ pre := by
    rintro x ⟨i, hi, hix⟩
    rw [hsplit, List.getElem?_append_left hi] at hix
    exact List.mem_of_getElem? hix
  -- the kept values outside the target's schedule agree with `Gpre`
  have hout : ∀ a, Listed g a → a ∉ oT.toList → (setPhis psT frT.regs)[a]? = Gpre.regs[a]? := by
    intro a hl ha
    obtain ⟨h1, h2⟩ := hagree a hl ha
    rw [h1, e3 a fun hm => h2 (by rw [hsplit]; exact List.mem_append_left _ hm)]
  have htopoT : TopoRem (argsF g) (pre' ++ r :: post') := by
    rw [← hsplitT]; exact otopoT
  -- an argument of a target value of `pre'` (or of `r`) in the target's schedule is in `pre'`
  have hargPre : ∀ x a, (x ∈ pre' ∨ x = r) → a ∈ argsF g x → a ∈ oT.toList → a ∈ pre' := by
    intro x a hx ha haT
    rw [hsplitT] at haT
    rcases hx with hx | rfl
    · obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
      have hjl := lt_length_of_getElem? hj
      obtain ⟨i, hi, hia⟩ := topoRem_before htopoT
        (by rw [List.getElem?_append_left hjl]; exact hj) ha haT
      rw [List.getElem?_append_left (by omega)] at hia
      exact List.mem_of_getElem? hia
    · rcases List.mem_append.1 haT with h' | h'
      · exact h'
      · exact absurd h' (topoRem_at htopoT a ha)
  have hloc : LocalOKL md env (Ctx.makeL tabs g) Gpre pre' := by
    intro x hx
    have hxT : x ∈ oT.toList := by rw [hsplitT]; exact List.mem_append_left _ hx
    obtain ⟨hxg, gv, hgv, hgn⟩ := (omemT x).1 hxT
    obtain ⟨gv', fv, hgv', hfv, -, -, -, -, -, -⟩ := S.value hb hgb hfb hxg
    rw [hgv] at hgv'; cases hgv'
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
    have hjl := lt_length_of_getElem? hj
    have hjT : oT.toList[j]? = some x := by rw [hsplitT, List.getElem?_append_left hjl]; exact hj
    obtain ⟨i', hi', hix⟩ := htr j x hjl hjT
    obtain ⟨v, y, hv, hy, hevx⟩ := e4 x (hinPre x ⟨i', hi', hix⟩)
    rw [makeL_f] at hv
    rw [hfv] at hv; cases hv
    exact ⟨y, hy, fun g' hg' hag =>
      S.evalKeptL L hlow hb hgb hfb hxg hgv hfv hgn hevx (fun _ h => nomatch h) hg'
        (fun a ha => hag a (by rw [makeL_f]; exact ha))⟩
  have hinit : ({ frT with regs := setPhis psT frT.regs } : Frame) =
      { Gpre with regs := setPhis psT frT.regs } :=
    (with_regs hA.1 _).trans (with_regs e1 _).symm
  have hpanT := evalAllL_ref_panic
    (S := fun a => a ∉ oT.toList ∧ (setPhis psT frT.regs)[a]? = Gpre.regs[a]?) (post := post')
    (g := { frT with regs := setPhis psT frT.regs }) hloc
    (by
      rw [makeL_f]
      exact refOK_of_topo (topoRem_append_left htopoT) fun x hx a ha hna => by
        have haT : a ∉ oT.toList := fun h => hna (hargPre x a (.inl hx) ha h)
        obtain ⟨hxg, gv, hgv, -⟩ := (omemT x).1 (by rw [hsplitT]; exact List.mem_append_left _ hx)
        rw [argsF_of hgv] at ha
        exact ⟨haT, hout a (hwg.argListed _ _ _ _ ⟨⟨hbm, hgb⟩, hxg, hgv⟩ a
          (Array.mem_toList_iff.1 ha)) haT⟩)
    (fun a ha => ha.2) hinit (by rw [e2]; simpa [hszP] using hszT)
    (fun a ha => by
      rw [makeL_f] at ha
      by_cases haT : a ∈ oT.toList
      · exact .inr (hargPre r a (.inr rfl) ha haT)
      · rw [argsF_of hgvr] at ha
        exact .inl ⟨haT, hout a (hwg.argListed _ _ _ _ ⟨⟨hbm, hgb⟩, hrg, hgvr⟩ a
          (Array.mem_toList_iff.1 ha)) haT⟩)
    (fun g' hg' hag => S.evalKeptL L hlow hb hgb hfb hrg hgvr hfvr hgrn hrp (fun _ h => nomatch h)
      hg' (fun a ha => hag a (by rw [makeL_f]; exact ha)))
  rw [enterBlockL_eq, hpsT]
  change (Res.ofOption _ ((Ctx.makeL tabs g).sched[gb.id]?).join).bind _ = _
  rw [hgid, sched_of_blockL hgb, hoT]
  change evalAllL md env (Ctx.makeL tabs g) _ oT.toList = _
  rw [hsplitT, hpanT]

end Setup

end GoFV.Proof.Dead

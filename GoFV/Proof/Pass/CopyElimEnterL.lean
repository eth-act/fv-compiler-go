import GoFV.Proof.Pass.CopyElimBlockL
import GoFV.Proof.Pass.CopyElimEnter

variable [GoFV.SSA.Sem.Addrs]

/-!
# copyelim on `runL`: the target's evaluation of a block

`GoFV.Proof.Pass.CopyElimEnter` for `runL`. `evalSameL`: a target value that is a source
non-`Phi` evaluates, in any frame agreeing with the source's frame on its arguments, as the
source value does (`copyEqL` for its arguments; a `MOVDreg`/`MOVDnop` sees the same sign
extension, `CopyLFrag.sx`). `evalFormerL`: a `Phi` that became a copy yields the source `Phi`'s
register. `enterL_ok`, `enterL_panic`: the target enters a block as the source does.
-/

namespace GoFV.Proof.CopyElim

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt Dom

variable {md : LMode} {tabs : Tables} {f g : Func}

/-- A source non-`Phi` of a tree block and its target evaluate alike. -/
theorem evalSameL (S : SetupL md tabs f g) {env : Env} {fr : Frame} {bid : ID} {i : Nat}
    (hA : AtL md env tabs f g fr bid i) {fb : Block} (hfb : f.block? bid = some fb)
    {frPS H : Frame} {oS : Array ID} {P : List ID}
    (hM : MidL md env tabs f fr bid i fb frPS H oS P)
    {x : ID} (hx : x ∈ fb.values) {fv gv : Value} (hfv : f.value? x = some fv)
    (hgv : g.value? x = some gv) (hnph : fv.op ≠ .Phi)
    (hdep : ∀ a ∈ fv.args, a ∈ fb.values → (∃ v, f.value? a = some v ∧ v.op ≠ .Phi) → a ∈ P)
    (hdef : ∀ msg, evalValueL md env (Ctx.makeL tabs f) H fv ≠ .stuck msg)
    {g' : Frame} (hg' : g' = { H with regs := g'.regs })
    (hag : ∀ a ∈ gv.args, g'.regs[a]? = H.regs[a]?) :
    evalValueL md env (Ctx.makeL tabs g) g' gv = evalValueL md env (Ctx.makeL tabs f) H fv := by
  obtain ⟨ce, hwf⟩ := S.base.wf
  have hbt := hA.tree S
  obtain ⟨fv', gv', hfv', hgv', -, hfid, -, -, hrel, hz⟩ := S.base.value hbt hfb hx
  rw [hfv] at hfv'; cases hfv'
  rw [hgv] at hgv'; cases hgv'
  have hgid := S.base.gid hbt hfb hx hgv
  have hargsdef := evalValueL_args_def hdef
  cases hrel with
  | phi _ hph => exact absurd hph hnph
  | empty hzz hgop hgargs =>
    have he := hz hzz
    have htyf : (Ctx.makeL tabs f).tys[x]? = some .empty := by
      rw [tysL_of_value hfv, shapesL_of_empty _ he.1]
    rw [evalValueL_emptyOK he (by rw [hfid]; exact htyf) hdef]
    exact evalValueL_empty hgop hgargs (by rw [hgid, S.tys hbt hfb hx, htyf])
  | same hop haux hai hsz hargs' =>
    refine evalValueL_eq_of_args_sx hop haux hai (hgid.trans hfid.symm) hsz (fun k fa hfa => ?_)
      hg' (by rw [hfid]; exact S.tys hbt hfb hx)
      (by rw [tabs_makeL, tabs_makeL]) (by rw [params_makeL, params_makeL]; exact S.base.params)
      (by rw [act_makeL, act_makeL]; rfl)
      (fun hm => by
        rw [makeL_f, makeL_f]
        exact S.frag.sx bid hbt fb hfb x hx fv gv hfv hgv (by rw [hop]; exact hm))
    obtain ⟨ga, hga, hr⟩ := hargs' k fa hfa
    have hfam : fa ∈ fv.args := Array.mem_of_getElem? hfa
    obtain ⟨y, hy⟩ := hargsdef fa hfam
    refine ⟨ga, y, hga, hy, ?_⟩
    rw [hag ga (Array.mem_of_getElem? hga)]
    rcases hr with rfl | ⟨u, hu, hop', hargsu⟩
    · exact hy
    · have hfal : Listed f fa :=
        hwf.argListed _ _ _ _ ⟨⟨hbt.1, hfb⟩, hx, hfv⟩ fa hfam
      have hfaU : Anc (make f) (blockOf f fa) bid :=
        uses S.base.cf hbt.1 hfb hbt.2 hx hfv hnph hfam
      obtain ⟨y', h1, h2⟩ := copyEqL S hA hfb hM hfal hfaU (fun hm => by
        by_cases hph : ∃ v, f.value? fa = some v ∧ v.op = .Phi
        · exact .inl hph
        · obtain ⟨v, -, hv, -⟩ := S.base.value hbt hfb hm
          exact .inr (hdep fa hfam hm ⟨v, hv, fun hp => hph ⟨v, hv, hp⟩⟩)) hu hop' hargsu
      rw [hy] at h1; cases h1; exact h2

/-- A `Phi` that became a copy yields the source `Phi`'s register. -/
theorem evalFormerL (S : SetupL md tabs f g) {env : Env} {fr : Frame} {bid : ID} {i : Nat}
    (hA : AtL md env tabs f g fr bid i) {fb : Block} (hfb : f.block? bid = some fb)
    {frPS H : Frame} {oS : Array ID} {P : List ID}
    (hM : MidL md env tabs f fr bid i fb frPS H oS P)
    {x : ID} (hx : x ∈ fb.values) {fv gv : Value} (hfv : f.value? x = some fv)
    (hgv : g.value? x = some gv) (hph : fv.op = .Phi) (hgn : gv.op ≠ .Phi) :
    ∃ y, H.regs[x]? = some (some y) ∧ ∀ g' : Frame, g' = { H with regs := g'.regs } →
      (∀ a ∈ gv.args, g'.regs[a]? = H.regs[a]?) →
      evalValueL md env (Ctx.makeL tabs g) g' gv = .ok y := by
  have hbt := hA.tree S
  obtain ⟨fv', gv', hfv', hgv', hfvb, hfid, -, -, hrel, hz⟩ := S.base.value hbt hfb hx
  rw [hfv] at hfv'; cases hfv'
  rw [hgv] at hgv'; cases hgv'
  cases hrel with
  | same hop => exact absurd (hop.trans hph) hgn
  | empty hzz => exact absurd hph (hz hzz).not_phi
  | phi w _ hcop hw hr =>
    have hl : Listed f x := ⟨bid, fb, ⟨hbt.1, hfb⟩, hx⟩
    have hU : Anc (make f) (blockOf f x) bid := by
      unfold blockOf; rw [hfv]
      simp only [Option.map_some, Option.getD_some]
      rw [hfvb]
      exact anc_refl hbt.2
    obtain ⟨y, h1, h2⟩ := copyEqL S hA hfb hM hl hU (fun _ => .inl ⟨fv, hfv, hph⟩) hgv hcop hw
    refine ⟨y, h1, fun g' hg' hag => ?_⟩
    have hgw : g'.regs[w]? = some (some y) := by rw [hag w (by rw [hw]; simp), h2]
    rw [evalValueL_copy hcop hw hgw, S.base.gid hbt hfb hx hgv, S.tys hbt hfb hx]
    exact congrArg _ (hM.typed x y h1)

/-- Source `Phi`s of a block entered along an edge sit in a non-entry block. -/
theorem phi_not_entryL (S : SetupL md tabs f g) {env : Env} {fr : Frame} {bid : ID} {i : Nat}
    (hA : AtL md env tabs f g fr bid i) {fb : Block} (hfb : f.block? bid = some fb)
    {psS : List (ID × Val)}
    (hpsS : fb.values.toList.filterMapM (phiStepL md (Ctx.makeL tabs f) fr i) = .ok psS) :
    ∀ z ∈ fb.values, ∀ fv, f.value? z = some fv → fv.op = .Phi → bid ≠ f.entry := by
  obtain ⟨ce, hwf⟩ := S.base.wf
  have hbt := hA.tree S
  intro z hz fv hfv hph
  have hlt : z < fr.regs.size := by rw [hA.size]; exact lt_of_value? hfv
  obtain ⟨-, -, -, hphi⟩ := phisL_spec (hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩) hpsS
  obtain ⟨a, y, ha, -, -⟩ := hphi z hz fv (by rw [makeL_f]; exact hfv) hph hlt
  have hsz := hwf.phiArity bid fb z fv ⟨⟨hbt.1, hfb⟩, hz, hfv⟩ hph
  have hilt : i < fb.preds.size := by rw [← hsz]; exact (Array.getElem?_eq_some_iff.1 ha).1
  exact (hA.pred S hfb (e := fb.preds[i]) (by simp [hilt])).1

/-- **The target's `Phi`s and schedule.** The target collects its `Phi`s and has a schedule;
after its `Phi`s, it agrees with the source (after the source's `Phi`s) outside its schedule. -/
theorem targetPreL (S : SetupL md tabs f g) {env : Env} {fr : Frame} {bid : ID} {i : Nat}
    (hA : AtL md env tabs f g fr bid i) {fb : Block} (hfb : f.block? bid = some fb)
    {psS : List (ID × Val)}
    (hpsS : fb.values.toList.filterMapM (phiStepL md (Ctx.makeL tabs f) fr i) = .ok psS)
    {oS : Array ID} (hsched : schedule f fb = some oS) :
    ∃ gb psT oT, g.block? bid = some gb ∧ gb.id = bid ∧ gb.values = fb.values ∧
      gb.values.toList.filterMapM (phiStepL md (Ctx.makeL tabs g) fr i) = .ok psT ∧
      schedule g gb = some oT ∧
      (∀ z, z ∉ oT.toList → (setPhis psT fr.regs)[z]? = (setPhis psS fr.regs)[z]?) ∧
      (setPhis psT fr.regs).size = fr.regs.size := by
  obtain ⟨ce, hwf⟩ := S.base.wf
  obtain ⟨ce', hwg⟩ := S.base.wg
  have hbt := hA.tree S
  have hndF := hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩
  obtain ⟨gb, hgbb, hgid, -, -, -, hvals, -⟩ := S.base.block hbt hfb
  obtain ⟨fb', hfb', hfid⟩ := hwf.blockId bid hbt.1
  rw [hfb] at hfb'; cases hfb'
  have hbg : bid ∈ g.blocks := by rw [S.base.blocks]; exact hbt.1
  have hndG := hwg.valuesNodup _ _ ⟨hbg, hgbb⟩
  have hpe := phi_not_entryL S hA hfb hpsS
  obtain ⟨-, -, hkeepS, hphiS⟩ := phisL_spec hndF hpsS
  rw [makeL_f] at hkeepS hphiS
  -- a `Phi` of both: equal incoming registers
  have hphiEq : ∀ z ∈ fb.values, ∀ fv gv, f.value? z = some fv → g.value? z = some gv →
      fv.op = .Phi → gv.op = .Phi → z < fr.regs.size →
      ∃ a y, fv.args[i]? = some a ∧ fr.regs[a]? = some (some y) ∧
        ∃ ga, gv.args[i]? = some ga ∧ fr.regs[ga]? = some (some y) := by
    intro z hz fv gv hfv hgv hph hgph hlt
    obtain ⟨a, y, ha, hy, -⟩ := hphiS z hz fv hfv hph hlt
    obtain ⟨fv', gv', hfv', hgv', -, -, -, -, hrel, hzz⟩ := S.base.value hbt hfb hz
    rw [hfv] at hfv'; cases hfv'
    rw [hgv] at hgv'; cases hgv'
    cases hrel with
    | phi _ _ hcop => rw [hcop] at hgph; cases hgph
    | empty hzz' => exact absurd hph (hzz hzz').not_phi
    | same _ _ _ hsz hargs' =>
      obtain ⟨ga, hga, hr⟩ := hargs' i a ha
      have hsz' := hwf.phiArity bid fb z fv ⟨⟨hbt.1, hfb⟩, hz, hfv⟩ hph
      have hilt : i < fb.preds.size := by rw [← hsz']; exact (Array.getElem?_eq_some_iff.1 ha).1
      have he : fb.preds[i]? = some fb.preds[i] := by simp [hilt]
      obtain ⟨-, hpt, -, hDT⟩ := hA.pred S hfb he
      have hpu := phiUse S.base.cf hbt.1 hfb hbt.2 hz hfv hph ha he hpt
      have hla : Listed f a :=
        hwf.argListed _ _ _ _ ⟨⟨hbt.1, hfb⟩, hz, hfv⟩ a (Array.mem_of_getElem? ha)
      obtain ⟨y', h1, h2⟩ := S.argEq hDT (A := fun z => Anc (make f) z fb.preds[i].b) hpu hA.tyT
        hla hpu hr
      rw [hy] at h1; cases h1
      exact ⟨a, y, ha, hy, ga, hga, h2⟩
  -- the target collects its `Phi`s
  obtain ⟨psT, hpsT⟩ : ∃ psT, gb.values.toList.filterMapM (phiStepL md (Ctx.makeL tabs g) fr i) =
      .ok psT := by
    refine filterMapM_phiL_ok fun z hz => ?_
    rw [hvals, Array.mem_toList_iff] at hz
    obtain ⟨fv, gv, hfv, hgv, -, -, -, -, hrel, hzz⟩ := S.base.value hbt hfb hz
    by_cases hgph : gv.op = .Phi
    · have hph := valRel_phi hrel hgph
      have hlt : z < fr.regs.size := by rw [hA.size]; exact lt_of_value? hfv
      obtain ⟨a, y, -, -, ga, hga, hy⟩ := hphiEq z hz fv gv hfv hgv hph hgph hlt
      refine ⟨some (z, md.retype ((Ctx.makeL tabs g).tys[z]?.getD .other) y), ?_⟩
      unfold phiStepL
      simp only [makeL_f, hgv, hgph, beq_self_eq_true, ite_true, hga, hy, Option.join]
      rfl
    · refine ⟨none, ?_⟩
      unfold phiStepL
      simp only [makeL_f, hgv, show (gv.op == .Phi) = false by simpa using hgph]
      rfl
  -- the target has a schedule
  obtain ⟨oT, hoT⟩ := targetSched S.base hbt hfb hpe hsched hgbb hvals
  obtain ⟨-, -, omemT⟩ := schedule_topo (valuesOwn hwg hbg hgbb) hndG hoT
  obtain ⟨hszT, -, hkeepT, hphiT⟩ := phisL_spec hndG hpsT
  rw [makeL_f] at hkeepT hphiT
  refine ⟨gb, psT, oT, hgbb, hgid.trans hfid, hvals, hpsT, hoT, fun z hz => ?_, hszT⟩
  by_cases hzb : z ∈ fb.values
  · obtain ⟨fv, gv, hfv, hgv, -, -, -, -, hrel, hzz⟩ := S.base.value hbt hfb hzb
    have hgph : gv.op = .Phi := Classical.byContradiction fun hne =>
      hz ((omemT z).2 ⟨by rw [hvals]; exact hzb, gv, hgv, hne⟩)
    have hph := valRel_phi hrel hgph
    have hlt : z < fr.regs.size := by rw [hA.size]; exact lt_of_value? hfv
    obtain ⟨a, y, ha, hy, ga, hga, hgy⟩ := hphiEq z hzb fv gv hfv hgv hph hgph hlt
    obtain ⟨a', y', ha', hy', hS⟩ := hphiS z hzb fv hfv hph hlt
    rw [ha] at ha'; cases ha'
    rw [hy] at hy'; cases hy'
    obtain ⟨ga', y'', hga', hgy', hT⟩ := hphiT z (by rw [hvals]; exact hzb) gv hgv hgph hlt
    rw [hga] at hga'; cases hga'
    rw [hgy] at hgy'; cases hgy'
    rw [hT, hS, S.tys hbt hfb hzb]
  · rw [hkeepS z (.inl hzb), hkeepT z (.inl (by rw [hvals]; exact hzb))]

/-- The source state after evaluating a prefix `P` of the block's schedule. -/
theorem mid_ofL (S : SetupL md tabs f g) {env : Env} {fr : Frame} {bid : ID} {i : Nat}
    (hA : AtL md env tabs f g fr bid i) {fb : Block} (hfb : f.block? bid = some fb)
    {psS : List (ID × Val)}
    (hpsS : fb.values.toList.filterMapM (phiStepL md (Ctx.makeL tabs f) fr i) = .ok psS)
    {oS : Array ID} (hsched : schedule f fb = some oS) {P R : List ID}
    (hsplit : oS.toList = P ++ R) {H : Frame}
    (hev : evalAllL md env (Ctx.makeL tabs f) { fr with regs := setPhis psS fr.regs } P = .ok H) :
    MidL md env tabs f fr bid i fb { fr with regs := setPhis psS fr.regs } H oS P ∧
      H = { fr with regs := H.regs } ∧ H.regs.size = fr.regs.size := by
  obtain ⟨ce, hwf⟩ := S.base.wf
  have hbt := hA.tree S
  have hndF := hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩
  have hown := valuesOwn hwf hbt.1 hfb
  have hcf := makeL_f tabs f
  obtain ⟨ond, otopo, omem⟩ := schedule_topo hown hndF hsched
  rw [hsplit] at ond otopo
  obtain ⟨hszP, hall, hkeep, hphi⟩ := phisL_spec hndF hpsS
  have hty := typedL_phis (frP := { fr with regs := setPhis psS fr.regs }) hA.tyS
    (by simpa using hszP) hkeep hphi hall
  rw [hcf] at hkeep hphi
  obtain ⟨e1, e2, e3, e4⟩ := evalAllL_spec (List.nodup_append.1 ond).1
    (by rw [hcf]; exact topoRem_append_left otopo) (by simp [hszP, hA.size, hcf]) hev
  have e4' := e4
  rw [hcf] at e4'
  refine ⟨⟨hkeep, hphi, hsched, ⟨R, hsplit⟩, e3, e4', ?_⟩, by rw [e1], by rw [e2]; simpa using hszP⟩
  refine typedL_evalAll hty (fun x hx v hv => ?_) e3 e4
  have hxo : x ∈ oS.toList := by rw [hsplit]; exact List.mem_append_left _ hx
  obtain ⟨v', hv', hvid⟩ := hown x ((omem x).1 hxo).1
  rw [hcf] at hv
  rw [hv] at hv'; cases hv'; exact hvid

/-- **A block the source enters successfully is entered by the target to the same frame.** -/
theorem enterL_ok (S : SetupL md tabs f g) {env : Env} {fr : Frame} {bid : ID} {i : Nat}
    (hA : AtL md env tabs f g fr bid i) {fb : Block} (hfb : f.block? bid = some fb) {G : Frame}
    (h : enterBlockL md env (Ctx.makeL tabs f) fr fb i = .ok G) :
    ∃ gb, g.block? bid = some gb ∧ enterBlockL md env (Ctx.makeL tabs g) fr gb i = .ok G := by
  obtain ⟨ce, hwf⟩ := S.base.wf
  obtain ⟨ce', hwg⟩ := S.base.wg
  have hbt := hA.tree S
  have hcg := makeL_f tabs g
  obtain ⟨fb', hfb', hfid⟩ := hwf.blockId bid hbt.1
  rw [hfb] at hfb'; cases hfb'
  rw [enterBlockL_eq] at h
  cases hpsS : fb.values.toList.filterMapM (phiStepL md (Ctx.makeL tabs f) fr i) with
  | panic e m => rw [hpsS] at h; cases h
  | stuck msg => rw [hpsS] at h; cases h
  | ok psS =>
  rw [hpsS] at h
  change (Res.ofOption _ ((Ctx.makeL tabs f).sched[fb.id]?).join).bind _ = _ at h
  rw [hfid, sched_of_blockL hfb] at h
  cases hsched : schedule f fb with
  | none => rw [hsched] at h; cases h
  | some oS =>
  rw [hsched] at h
  change evalAllL md env (Ctx.makeL tabs f) _ oS.toList = .ok G at h
  obtain ⟨gb, psT, oT, hgbb, hgid, hvals, hpsT, hoT, hagree, hszT⟩ :=
    targetPreL S hA hfb hpsS hsched
  obtain ⟨hM, hG1, hG2⟩ := mid_ofL S hA hfb hpsS hsched (R := []) (by simp) h
  have hbg : bid ∈ g.blocks := by rw [S.base.blocks]; exact hbt.1
  have hndG := hwg.valuesNodup _ _ ⟨hbg, hgbb⟩
  obtain ⟨ondT, otopoT, omemT⟩ := schedule_topo (valuesOwn hwg hbg hgbb) hndG hoT
  obtain ⟨-, -, omem⟩ := schedule_topo (valuesOwn hwf hbt.1 hfb)
    (hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩) hsched
  -- the target's evaluation against the source's final frame
  have hloc : LocalOKL md env (Ctx.makeL tabs g) G oT.toList := by
    intro x hx
    obtain ⟨hxb, gv, hgv, hgn⟩ := (omemT x).1 hx
    rw [hvals] at hxb
    obtain ⟨fv, -, hfv, -⟩ := S.base.value hbt hfb hxb
    have hargsT : argsF (Ctx.makeL tabs g).f x = gv.args.toList := by
      rw [hcg]; exact argsF_of (f := g) hgv
    have hgv' : (Ctx.makeL tabs g).f.value? x = some gv := by rw [hcg]; exact hgv
    by_cases hph : fv.op = .Phi
    · obtain ⟨y, h1, h2⟩ := evalFormerL S hA hfb hM hxb hfv hgv hph hgn
      exact ⟨y, h1, fun g' hg' hag => by
        rw [stepVL_of hgv']
        exact h2 g' hg' fun a ha => hag a (by rw [hargsT]; exact Array.mem_toList_iff.2 ha)⟩
    · have hxS : x ∈ oS.toList := (omem x).2 ⟨hxb, fv, hfv, hph⟩
      obtain ⟨v', y, hv', hy, hev⟩ := hM.eval x (by simpa using hxS)
      rw [hfv] at hv'; cases hv'
      refine ⟨y, hy, fun g' hg' hag => ?_⟩
      rw [stepVL_of hgv', ← hev]
      exact evalSameL S hA hfb hM hxb hfv hgv hph
        (fun a _ hab han => by simpa using (omem a).2 ⟨hab, han⟩)
        (fun msg he => by rw [hev] at he; cases he) hg'
        (fun a ha => hag a (by rw [hargsT]; exact Array.mem_toList_iff.2 ha))
  have hS : ∀ a, a ∉ oT.toList → (setPhis psT fr.regs)[a]? = G.regs[a]? := by
    intro a ha
    rw [hagree a ha, hM.out a (fun hm => ha (by
      have ham : a ∈ oS.toList := by simpa using hm
      obtain ⟨hab, fv, hfv, hne⟩ := (omem a).1 ham
      obtain ⟨fv', gv, hfv', hgv, -, -, -, -, hrel, hz⟩ := S.base.value hbt hfb hab
      rw [hfv] at hfv'; cases hfv'
      exact (omemT a).2 ⟨by rw [hvals]; exact hab, gv, hgv,
        fun hp => hne (valRel_phi hrel hp)⟩))]
  obtain ⟨g'', h1, h2, -, h4, -⟩ := evalAllL_ref (S := fun a => a ∉ oT.toList)
    (g := { fr with regs := setPhis psT fr.regs }) hloc
    (refOK_prefix (L2 := []) (by rw [List.append_nil, hcg]; exact otopoT)
      (fun a ha => by simpa using ha))
    hS (by rw [hG1]) (by rw [hG2]; exact hszT)
  have hgG : g'' = G := frame_ext h2 fun a => h4 a (by
    by_cases ha : a ∈ oT.toList
    · exact .inr ha
    · exact .inl ha)
  refine ⟨gb, hgbb, ?_⟩
  rw [enterBlockL_eq, hpsT]
  change (Res.ofOption _ ((Ctx.makeL tabs g).sched[gb.id]?).join).bind _ = _
  rw [hgid, sched_of_blockL hgbb, hoT]
  change evalAllL md env (Ctx.makeL tabs g) _ oT.toList = _
  rw [h1, hgG]

/-- **A block the source panics in makes the target panic alike.** -/
theorem enterL_panic (S : SetupL md tabs f g) {env : Env} {fr : Frame} {bid : ID} {i : Nat}
    (hA : AtL md env tabs f g fr bid i) {fb : Block} (hfb : f.block? bid = some fb) {e : Panic}
    {m : Mem} (h : enterBlockL md env (Ctx.makeL tabs f) fr fb i = .panic e m) :
    ∃ gb, g.block? bid = some gb ∧ enterBlockL md env (Ctx.makeL tabs g) fr gb i = .panic e m := by
  obtain ⟨ce, hwf⟩ := S.base.wf
  obtain ⟨ce', hwg⟩ := S.base.wg
  have hbt := hA.tree S
  have hcf := makeL_f tabs f
  have hcg := makeL_f tabs g
  obtain ⟨fb', hfb', hfid⟩ := hwf.blockId bid hbt.1
  rw [hfb] at hfb'; cases hfb'
  obtain ⟨psS, oS, hpsS, hso, hev⟩ := enterBlockL_panic h
  rw [hfid, sched_of_blockL hfb] at hso
  obtain ⟨pre, r, post, Gpre, hsplit, hpre, hrp⟩ := evalAllL_panic_split hev
  obtain ⟨hM, hG1, hG2⟩ := mid_ofL S hA hfb hpsS hso hsplit hpre
  obtain ⟨gb, psT, oT, hgbb, hgid, hvals, hpsT, hoT, hagree, hszT⟩ := targetPreL S hA hfb hpsS hso
  have hbg : bid ∈ g.blocks := by rw [S.base.blocks]; exact hbt.1
  have hownF := valuesOwn hwf hbt.1 hfb
  have hndF := hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩
  have hownG := valuesOwn hwg hbg hgbb
  have hndG := hwg.valuesNodup _ _ ⟨hbg, hgbb⟩
  obtain ⟨ondT, otopoT, omemT⟩ := schedule_topo hownG hndG hoT
  obtain ⟨ond, otopo, omem⟩ := schedule_topo hownF hndF hso
  -- the panicking root
  have hrS : r ∈ oS.toList := by rw [hsplit]; simp
  obtain ⟨hrb, fvr, hfvr, hrnph⟩ := (omem r).1 hrS
  obtain ⟨fvr', gvr, hfvr', hgvr, -, hfrid, -, -, hrelr, hzr⟩ := S.base.value hbt hfb hrb
  rw [hfvr] at hfvr'; cases hfvr'
  rw [stepVL_of (by rw [hcf]; exact hfvr)] at hrp
  have hrop : PanickingL false fvr.op := by
    have := evalValueL_panic_op hrp
    rwa [S.mdFault] at this
  have hgop : gvr.op = fvr.op := by
    cases hrelr with
    | same hop => exact hop
    | phi _ hph => exact absurd hph hrnph
    | empty hzz => exact absurd (hzr hzz).prio (prio_panickingL hrop)
  have hrT : r ∈ oT.toList :=
    (omemT r).2 ⟨by rw [hvals]; exact hrb, gvr, hgvr, by rw [hgop]; exact hrnph⟩
  obtain ⟨pre', post', hsplitT⟩ := List.append_of_mem hrT
  -- what the target evaluates before `r`, the source evaluated before `r`
  have hspecS := schedule_spec hso
  have hspecT := schedule_spec hoT
  have hk : oS.toList[pre.length]? = some r := by rw [hsplit]; simp
  have hk' : oT.toList[pre'.length]? = some r := by rw [hsplitT]; simp
  -- the roots run in the same order (#96): the target reaches nothing the source did not
  have hpe := phi_not_entryL S hA hfb hpsS
  have hsame := sameNP_copy S.base hbt hfb hgbb hvals
  have hrnp : npIn (schedNodes f fb).toList r = true := by
    unfold npIn
    rw [← hfrid, nodeOf_schedNodes hownF hndF (hfrid ▸ hrb) (hfrid ▸ hfvr) hrnph]
    simpa using prio_panickingL hrop
  have hdep : ∀ x y, npIn (schedNodes f fb).toList x = true →
      npIn (schedNodes f fb).toList y = true →
      (Order.Dep (NodeIn (schedNodes f fb).toList) (argsOf (schedNodes f fb).toList) x y ↔
        Order.Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList) x y) := by
    intro x y hx _
    have hxN := (npIn_iff.1 hx).1
    constructor
    · intro hd
      refine depPres S.base hbt hfb hgbb hvals hxN (fun gx hgx hcx => ?_) y hd
      obtain ⟨hxb, fx, hfx, hfxn⟩ := (nodeIn_schedNodes hownF).1 hxN
      obtain ⟨fx', gx', hfx', hgx', -, -, -, -, hrelx, hzx⟩ := S.base.value hbt hfb hxb
      rw [hfx] at hfx'; cases hfx'
      rw [hgx] at hgx'; cases hgx'
      have hpx : prio fx.op ≠ 0 := by
        unfold npIn at hx
        rw [nodeOf_schedNodes hownF hndF hxb hfx hfxn] at hx
        simpa using hx
      cases hrelx with
      | same hop => rw [← hop, hcx] at hpx; exact hpx rfl
      | phi _ hph => exact hfxn hph
      | empty hzz => exact hpx (hzx hzz).prio
    · intro hd; exact (depBack S.base hbt hfb hpe hso hgbb hvals hd hxN).1
  have htr := sched_transfer' hspecS hspecT hsame hdep hk hk' hrnp (fun a y haN hyN hay hyT => by
    obtain ⟨hyb, fy, hfy, hfyn⟩ := (nodeIn_schedNodes hownF).1 hyN
    obtain ⟨fy', gy, hfy', hgy, -, -, -, -, hrely, hzy⟩ := S.base.value hbt hfb hyb
    rw [hfy] at hfy'; cases hfy'
    rw [argsOf_schedNodes hownF hndF hyb hfy hfyn] at hay
    obtain ⟨k, hk2⟩ := List.getElem?_of_mem hay
    have hk2' : fy.args[k]? = some a := by simpa using hk2
    cases hrely with
    | phi _ hph => exact absurd hph hfyn
    | empty hzz => rw [(hzy hzz).2.1] at hk2'; simp at hk2'
    | same hop _ _ hsz hargs' =>
      obtain ⟨w, hw, hra⟩ := hargs' k a hk2'
      have hgyn : gy.op ≠ .Phi := by rw [hop]; exact hfyn
      have hwT : w ∈ argsOf (schedNodes g gb).toList y := by
        rw [argsOf_schedNodes hownG hndG (by rw [hvals]; exact hyb) hgy hgyn]
        exact List.mem_of_getElem? (by simpa using hw)
      obtain ⟨ka, hka⟩ := List.getElem?_of_mem ((omem a).2 ((nodeIn_schedNodes hownF).1 haN))
      exact feedsOf S.base hbt hfb hso hgbb hvals hyT hwT ka a hka hra)
  -- the target's prefix agrees with the source's frame at the panic
  have hargsT : ∀ x gv, g.value? x = some gv → argsF (Ctx.makeL tabs g).f x = gv.args.toList :=
    fun x gv hgv => by rw [hcg]; exact argsF_of (f := g) hgv
  have hnotS : ∀ a, a ∉ oT.toList → a ∉ oS.toList := by
    intro a ha ham
    obtain ⟨hab, fv, hfv, hne⟩ := (omem a).1 ham
    obtain ⟨fv', gv, hfv', hgv, -, -, -, -, hrel, hz⟩ := S.base.value hbt hfb hab
    rw [hfv] at hfv'; cases hfv'
    exact ha ((omemT a).2 ⟨by rw [hvals]; exact hab, gv, hgv,
      fun hp => hne (valRel_phi hrel hp)⟩)
  have hinPre : ∀ x, x ∈ oS.toList → (∃ i < pre.length, oS.toList[i]? = some x) → x ∈ pre := by
    rintro x - ⟨i, hi, hix⟩
    rw [hsplit, List.getElem?_append_left hi] at hix
    exact List.mem_of_getElem? hix
  -- arguments of a value of `pre` (or of `r`) in the block are in `pre`
  have hdepPre : ∀ x, (∃ k ≤ pre.length, oS.toList[k]? = some x) → ∀ fv, f.value? x = some fv →
      ∀ a ∈ fv.args, a ∈ fb.values → (∃ v, f.value? a = some v ∧ v.op ≠ .Phi) → a ∈ pre := by
    rintro x ⟨k, hkl, hkx⟩ fv hfv a ha hab han
    obtain ⟨j, hj, hja⟩ := topoRem_before otopo hkx (by rw [argsF_of hfv]; simpa using ha)
      ((omem a).2 ⟨hab, han⟩)
    exact hinPre a ((omem a).2 ⟨hab, han⟩) ⟨j, by omega, hja⟩
  have hloc : LocalOKL md env (Ctx.makeL tabs g) Gpre pre' := by
    intro x hx
    have hxT : x ∈ oT.toList := by rw [hsplitT]; exact List.mem_append_left _ hx
    obtain ⟨hxb, gv, hgv, hgn⟩ := (omemT x).1 hxT
    rw [hvals] at hxb
    obtain ⟨fv, -, hfv, -⟩ := S.base.value hbt hfb hxb
    have hgv' : (Ctx.makeL tabs g).f.value? x = some gv := by rw [hcg]; exact hgv
    by_cases hph : fv.op = .Phi
    · obtain ⟨y, h1, h2⟩ := evalFormerL S hA hfb hM hxb hfv hgv hph hgn
      exact ⟨y, h1, fun g' hg' hag => by
        rw [stepVL_of hgv']
        exact h2 g' hg' fun a ha => hag a (by rw [hargsT x gv hgv]; exact Array.mem_toList_iff.2 ha)⟩
    · obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
      have hjl := lt_length_of_getElem? hj
      have hjT : oT.toList[j]? = some x := by rw [hsplitT, List.getElem?_append_left hjl]; exact hj
      obtain ⟨i', hi', hix⟩ := htr j x hjl hjT ((nodeIn_schedNodes hownF).2 ⟨hxb, fv, hfv, hph⟩)
      have hxS : x ∈ oS.toList := (omem x).2 ⟨hxb, fv, hfv, hph⟩
      have hxP := hinPre x hxS ⟨i', hi', hix⟩
      obtain ⟨v', y, hv', hy, hevx⟩ := hM.eval x hxP
      rw [hfv] at hv'; cases hv'
      refine ⟨y, hy, fun g' hg' hag => ?_⟩
      rw [stepVL_of hgv', ← hevx]
      exact evalSameL S hA hfb hM hxb hfv hgv hph
        (hdepPre x ⟨i', by omega, hix⟩ fv hfv)
        (fun msg he => by rw [hevx] at he; cases he) hg'
        (fun a ha => hag a (by rw [hargsT x gv hgv]; exact Array.mem_toList_iff.2 ha))
  have hS : ∀ a, a ∉ oT.toList → (setPhis psT fr.regs)[a]? = Gpre.regs[a]? := by
    intro a ha
    rw [hagree a ha, hM.out a (fun hm => hnotS a ha (by rw [hsplit]; exact List.mem_append_left _ hm))]
  have htopoT : TopoRem (argsF (Ctx.makeL tabs g).f) (pre' ++ r :: post') := by
    rw [hcg, ← hsplitT]; exact otopoT
  have hgvr' : (Ctx.makeL tabs g).f.value? r = some gvr := by rw [hcg]; exact hgvr
  have hpanT := evalAllL_ref_panic (S := fun a => a ∉ oT.toList) (post := post')
    (g := { fr with regs := setPhis psT fr.regs }) hloc
    (refOK_prefix htopoT (fun a ha => by rw [hsplitT]; exact ha))
    hS (by rw [hG1]) (by rw [hG2]; exact hszT)
    (fun a ha => by
      by_cases haT : a ∈ oT.toList
      · rw [hsplitT] at haT
        rcases List.mem_append.1 haT with h' | h'
        · exact .inr h'
        · exact absurd h' (topoRem_at htopoT a ha)
      · exact .inl haT)
    (fun g' hg' hag => by
      rw [stepVL_of hgvr', ← hrp]
      exact evalSameL S hA hfb hM hrb hfvr hgvr hrnph
        (hdepPre r ⟨pre.length, Nat.le_refl _, hk⟩ fvr hfvr)
        (fun msg he => by rw [hrp] at he; cases he) hg'
        (fun a ha => hag a (by rw [hargsT r gvr hgvr]; exact Array.mem_toList_iff.2 ha)))
  refine ⟨gb, hgbb, ?_⟩
  rw [enterBlockL_eq, hpsT]
  change (Res.ofOption _ ((Ctx.makeL tabs g).sched[gb.id]?).join).bind _ = _
  rw [hgid, sched_of_blockL hgbb, hoT]
  change evalAllL md env (Ctx.makeL tabs g) _ oT.toList = _
  rw [hsplitT, hpanT]

end GoFV.Proof.CopyElim

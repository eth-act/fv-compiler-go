import GoFV.Proof.Pass.ZCSEFill
import GoFV.Proof.Pass.CopyElimEnter

/-!
# zcse: one block entry

`At`: the source-side invariant at a block entry (frame size, one argument image per parameter,
`ArglessInv`, the block reached from the entry or along an edge of a tree block). `TF`: the
target's frame is the source's at the entry, `fill` of it elsewhere. `enter_ok`: a block the
source enters to frame `G` the target enters to `fill G` (its `Phi`s read related arguments,
`argRead`; its values evaluate as the source's against `fill G`, `evalSame`; the moved
representatives to their constants).
-/

namespace GoFV.Proof.ZCSE

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.ZCSE Dom
open GoFV.Proof.CopyElim (Tree refOK_prefix frame_ext stepV_of)

variable {tabs : Tables} {f g : Func}

/-- The source-side invariant at the entry of block `bid` along edge `i`. -/
structure At (env : Env) (tabs : Tables) (f : Func) (fr : Frame) (bid : ID) (i : Nat) :
    Prop where
  size : fr.regs.size = f.valueTab.size
  images : fr.images.size = (Ctx.make tabs f).params.size
  inv : ArglessInv env (Ctx.make tabs f) fr
  pre : bid = f.entry ∨ ∃ p blkp, p ∈ f.blocks ∧ f.block? p = some blkp ∧
    ((make f).depthOf p).isSome ∧ (⟨bid, i⟩ : Edge) ∈ blkp.succs

/-- The target's frame: the source's at the entry, else `fill` of it. -/
def TF (env : Env) (tabs : Tables) (f g : Func) (frS frT : Frame) (bid : ID) : Prop :=
  (bid = f.entry ∧ frT = frS) ∨ (bid ≠ f.entry ∧ frT = fill env tabs g frS)

theorem TF.frame {env : Env} {frS frT : Frame} {bid : ID} (h : TF env tabs f g frS frT bid) :
    frT = { frS with regs := frT.regs } ∧ frT.regs.size = frS.regs.size := by
  rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨fill_frame env frS, fill_size env frS⟩

theorem At.tree (S : Setup tabs f g) {env : Env} {fr : Frame} {bid : ID} {i : Nat}
    (h : At env tabs f fr bid i) : Tree f bid := by
  obtain ⟨ce, hwf⟩ := S.wf
  rcases h.pre with rfl | ⟨p, blkp, hp, hpb, hpt, he⟩
  · exact ⟨hwf.entry, by simp [entry_depth S.cf.parents]⟩
  · obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 he
    exact ⟨(hwf.succLink p blkp ⟨hp, hpb⟩ j _ hj).1, (edge S.cf hp hpb hpt he).2.1⟩

/-- **A source non-`Phi` and its target evaluate alike**, the target against `fill`. -/
theorem evalSame {env : Env} (S : Setup tabs f g) {F : Frame}
    (hinv : ArglessInv env (Ctx.make tabs f) F) (hsz : F.regs.size = f.valueTab.size)
    {b : ID} {fb : Block} (hbin : BlockIn f b fb) {x : ID} (hx : x ∈ fb.values) {fv gv : Value}
    (hfv : f.value? x = some fv) (hgv : g.value? x = some gv)
    (hdef : ∀ msg, evalValue env (Ctx.make tabs f) F fv ≠ .stuck msg)
    {g' : Frame} (hg' : g' = { F with regs := g'.regs })
    (hag : ∀ a ∈ gv.args, g'.regs[a]? = (fill env tabs g F).regs[a]?) :
    evalValue env (Ctx.make tabs g) g' gv = evalValue env (Ctx.make tabs f) F fv := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨gv', hgv', hid, hop, hax, hai, -, hsz', hrel⟩ := S.value hfv
  rw [hgv] at hgv'; cases hgv'
  obtain ⟨fv', hfv', hfid, -⟩ := hwf.valueId b fb hbin x hx
  rw [hfv] at hfv'; cases hfv'
  have hargsdef := evalValue_args_def hdef
  refine evalValue_eq_of_args hop hax hai hid hsz' (fun k fa hfa => ?_) hg'
    (by rw [hfid]; exact S.tys hfv) rfl S.params rfl
  obtain ⟨ga, hga, hr⟩ := hrel k fa hfa
  have hfam : fa ∈ fv.args := Array.mem_of_getElem? hfa
  obtain ⟨y, hy⟩ := hargsdef fa hfam
  refine ⟨ga, y, hga, hy, ?_⟩
  rw [hag ga (Array.mem_of_getElem? hga)]
  exact argRead S hinv hsz (hwf.argListed b fb x fv ⟨hbin, hx, hfv⟩ fa hfam) hy hr

/-- Source `Phi`s of a block entered successfully sit in a non-entry block. -/
theorem phi_not_entry (S : Setup tabs f g) {env : Env} {fr : Frame} {bid : ID} {i : Nat}
    (hA : At env tabs f fr bid i) {fb : Block} (hfb : f.block? bid = some fb)
    {psS : List (ID × Val)}
    (hpsS : fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) fr i) = .ok psS) :
    ∀ z ∈ fb.values, ∀ fv, f.value? z = some fv → fv.op = .Phi → bid ≠ f.entry := by
  obtain ⟨ce, hwf⟩ := S.wf
  have hbt := hA.tree S
  intro z hz fv hfv hph hbe
  have hlt : z < fr.regs.size := by rw [hA.size]; exact lt_of_value? hfv
  obtain ⟨-, -, -, hphi⟩ := phis_spec (hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩) hpsS
  obtain ⟨a, y, ha, -, -⟩ := hphi z hz fv hfv hph hlt
  have hsz := hwf.phiArity bid fb z fv ⟨⟨hbt.1, hfb⟩, hz, hfv⟩ hph
  have hilt : i < fb.preds.size := by rw [← hsz]; exact (Array.getElem?_eq_some_iff.1 ha).1
  subst hbe
  have := hwf.entryPreds fb hfb
  omega

/-- **The target's `Phi`s and schedule.** The target collects its `Phi`s and has a schedule;
after its `Phi`s, it agrees outside its schedule with `fill` of the source after its `Phi`s. -/
theorem targetPre (S : Setup tabs f g) {env : Env} {fr frT : Frame} {bid : ID} {i : Nat}
    (hA : At env tabs f fr bid i) (hT : TF env tabs f g fr frT bid) {fb : Block}
    (hfb : f.block? bid = some fb) {psS : List (ID × Val)}
    (hpsS : fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) fr i) = .ok psS)
    {oS : Array ID} (hsched : schedule f fb = some oS) :
    ∃ gb psT oT, g.block? bid = some gb ∧ gb.id = bid ∧
      gb.values.toList.filterMapM (phiStep (Ctx.make tabs g) frT i) = .ok psT ∧
      schedule g gb = some oT ∧
      (∀ z, z ∉ oT.toList → (setPhis psT frT.regs)[z]? =
        (fill env tabs g { fr with regs := setPhis psS fr.regs }).regs[z]?) ∧
      (setPhis psT frT.regs).size = fr.regs.size := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  have hbt := hA.tree S
  have hndF := hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩
  obtain ⟨gb, hgbb, hgid, -, -, -, -, hfg, hgf⟩ := S.block hbt.1 hfb
  obtain ⟨fb', hfb', hfid⟩ := hwf.blockId bid hbt.1
  rw [hfb] at hfb'; cases hfb'
  have hbg : bid ∈ g.blocks := by rw [S.blocks]; exact hbt.1
  have hndG := hwg.valuesNodup _ _ ⟨hbg, hgbb⟩
  have hpe := phi_not_entry S hA hfb hpsS
  obtain ⟨hszS, -, hkeepS, hphiS⟩ := phis_spec hndF hpsS
  obtain ⟨hTfr, hTsz⟩ := hT.frame
  -- a target `Phi` is a source `Phi` of a non-entry block, reading a related argument
  have hgphi : ∀ z ∈ gb.values, ∀ gv, g.value? z = some gv → gv.op = .Phi →
      ∃ fv, f.value? z = some fv ∧ fv.op = .Phi ∧ z ∈ fb.values ∧ bid ≠ f.entry := by
    intro z hz gv hgv hph
    have hnea : ¬ EA g z := fun hea => by
      obtain ⟨-, -, -, v, hv, -, hvn⟩ := ea_iff.1 hea
      rw [hgv] at hv; cases hv; exact hvn hph
    have hzf := (hgf z hz).resolve_right hnea
    obtain ⟨fv, hfv, -, -⟩ := hwf.valueId bid fb ⟨hbt.1, hfb⟩ z hzf
    obtain ⟨gv', hgv', -, hop, -⟩ := S.value hfv
    rw [hgv] at hgv'; cases hgv'
    exact ⟨fv, hfv, by rw [← hop]; exact hph, hzf, hpe z hzf fv hfv (by rw [← hop]; exact hph)⟩
  have hphiEq : ∀ z ∈ gb.values, ∀ gv, g.value? z = some gv → gv.op = .Phi →
      ∃ fv y, f.value? z = some fv ∧ (setPhis psS fr.regs)[z]? =
        some (some (y.retype ((Ctx.make tabs f).tys[z]?.getD .other))) ∧
        ∃ ga, gv.args[i]? = some ga ∧ frT.regs[ga]? = some (some y) := by
    intro z hz gv hgv hph
    obtain ⟨fv, hfv, hfph, hzf, hne⟩ := hgphi z hz gv hgv hph
    have hlt : z < fr.regs.size := by rw [hA.size]; exact lt_of_value? hfv
    obtain ⟨a, y, ha, hy, hP⟩ := hphiS z hzf fv hfv hfph hlt
    obtain ⟨gv', hgv', -, -, -, -, -, -, hrel⟩ := S.value hfv
    rw [hgv] at hgv'; cases hgv'
    obtain ⟨ga, hga, hr⟩ := hrel i a ha
    have hfrT : frT = fill env tabs g fr := by
      rcases hT with ⟨he, -⟩ | ⟨-, h⟩
      · exact absurd he hne
      · exact h
    refine ⟨fv, y, hfv, hP, ga, hga, ?_⟩
    rw [hfrT]
    exact argRead S hA.inv hA.size
      (hwf.argListed bid fb z fv ⟨⟨hbt.1, hfb⟩, hzf, hfv⟩ a (Array.mem_of_getElem? ha)) hy hr
  -- the target collects its `Phi`s
  obtain ⟨psT, hpsT⟩ : ∃ psT, gb.values.toList.filterMapM (phiStep (Ctx.make tabs g) frT i) =
      .ok psT := by
    refine filterMapM_phi_ok fun z hz => ?_
    rw [Array.mem_toList_iff] at hz
    obtain ⟨gv, hgv, -, -⟩ := hwg.valueId bid gb ⟨hbg, hgbb⟩ z hz
    by_cases hgph : gv.op = .Phi
    · obtain ⟨fv, y, -, -, ga, hga, hy⟩ := hphiEq z hz gv hgv hgph
      refine ⟨some (z, y.retype ((Ctx.make tabs g).tys[z]?.getD .other)), ?_⟩
      unfold phiStep
      simp only [show (Ctx.make tabs g).f = g from rfl, hgv, hgph, beq_self_eq_true, ite_true,
        hga, hy, Option.join]
      rfl
    · refine ⟨none, ?_⟩
      unfold phiStep
      simp only [show (Ctx.make tabs g).f = g from rfl, hgv,
        show (gv.op == .Phi) = false by simpa using hgph]
      rfl
  -- the target has a schedule
  obtain ⟨oT, hoT⟩ := targetSched S hbt.1 hfb hgbb hsched
  obtain ⟨-, -, omemT⟩ := schedule_topo (valuesOwn hwg hbg hgbb) hndG hoT
  obtain ⟨hszT, -, hkeepT, hphiT⟩ := phis_spec hndG hpsT
  refine ⟨gb, psT, oT, hgbb, hgid.trans hfid, hpsT, hoT, fun z hz => ?_, by
    rw [hszT, hTsz]⟩
  by_cases hzg : z ∈ gb.values ∧ ∃ gv, g.value? z = some gv ∧ gv.op = .Phi
  · obtain ⟨hzb, gv, hgv, hph⟩ := hzg
    obtain ⟨fv, y, hfv, hP, ga, hga, hy⟩ := hphiEq z hzb gv hgv hph
    have hlt : z < frT.regs.size := by rw [hTsz, hA.size]; exact lt_of_value? hfv
    obtain ⟨ga', y', hga', hy', hT'⟩ := hphiT z (by simpa using hzb) gv hgv hph hlt
    rw [hga] at hga'; cases hga'
    rw [hy] at hy'; cases hy'
    have hnea : ¬ EA g z := fun hea => by
      obtain ⟨-, -, -, v, hv, -, hvn⟩ := ea_iff.1 hea
      rw [hgv] at hv; cases hv; exact hvn hph
    rw [hT', fill_not_ea env _ hnea]
    show _ = (setPhis psS fr.regs)[z]?
    rw [hP, S.tys hfv]
  · have hkT : (setPhis psT frT.regs)[z]? = frT.regs[z]? := by
      refine hkeepT z ?_
      by_cases hzb : z ∈ gb.values
      · obtain ⟨gv, hgv, -, -⟩ := hwg.valueId bid gb ⟨hbg, hgbb⟩ z hzb
        exact .inr ⟨gv, hgv, fun hp => hzg ⟨hzb, gv, hgv, hp⟩⟩
      · exact .inl (by simpa using hzb)
    rw [hkT]
    -- the source's `Phi`s outside the target's
    have hkS : ¬ EA g z → (setPhis psS fr.regs)[z]? = fr.regs[z]? := by
      intro hnea
      refine hkeepS z ?_
      by_cases hzf : z ∈ fb.values
      · obtain ⟨fv, hfv, -, -⟩ := hwf.valueId bid fb ⟨hbt.1, hfb⟩ z hzf
        refine .inr ⟨fv, hfv, fun hp => hzg ⟨(hfg z hzf).resolve_right hnea, ?_⟩⟩
        obtain ⟨gv, hgv, -, hop, -⟩ := S.value hfv
        exact ⟨gv, hgv, by rw [hop]; exact hp⟩
      · exact .inl (by simpa using hzf)
    rcases hT with ⟨hbe, rfl⟩ | ⟨-, rfl⟩
    · by_cases hea : EA g z
      · exfalso
        apply hz
        obtain ⟨gE, hgE, hzE, v, hv, -, hvn⟩ := ea_iff.1 hea
        rw [S.entry, ← hbe, hgbb] at hgE; cases hgE
        exact (omemT z).2 ⟨hzE, v, hv, hvn⟩
      · rw [fill_not_ea env _ hea]
        exact (hkS hea).symm
    · by_cases hea : EA g z
      · exact (fill_ea_eq rfl (by simp [hszS]) hea).symm
      · rw [fill_not_ea env _ hea, fill_not_ea env _ hea]
        exact (hkS hea).symm

end GoFV.Proof.ZCSE

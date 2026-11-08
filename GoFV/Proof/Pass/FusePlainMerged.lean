import GoFV.Proof.Pass.FusePlainSetup
import GoFV.Proof.Merge

variable [GoFV.SSA.Sem.Addrs]

/-!
# fuseBlockPlain: the fused block

`targetPre`: the fused block `c` of `g` collects `b0`'s `Phi`s from the same arguments, has a
schedule, and after its `Phi`s agrees with any source frame of the run (one that differs from the
entry frame only on the run's values and holds `b0`'s `Phi`s) outside the schedule.
`merged_ok`: when the source runs the whole run, the target's fused block ends in the same frame
(`evalAll_ref`: each of its values re-evaluates to its register in the source's final frame).
-/

namespace GoFV.Proof.FusePlain

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.Fuse GoFV.Opt.Fuse.Plain
  GoFV.Proof Dom

variable {f g : Func} {run : List ID} {b0 c : ID}

namespace Setup

variable (S : Setup f g run b0 c)
include S

theorem cInG : c ∈ g.blocks := by rw [S.gblocks]; exact S.runIn S.rel.c_mem

/-- A value of a block of the run after `b0` is no `Phi`. -/
theorem later_noPhi {y : ID} (hy : y ∈ run) (hyb : y ≠ b0) {x : ID}
    (hx : x ∈ (valsOf f y).toList) {v : Value} (hv : f.value? x = some v) :
    v.op ≠ .Phi ∧ v.op ≠ .Arg ∧ v.op ≠ .ArgIntReg := by
  obtain ⟨pre, suf, hr⟩ := S.split_mem hy
  have hpre : pre ≠ [] := by
    rintro rfl
    obtain ⟨rest, hrest⟩ := S.rel.run_cons
    rw [hr] at hrest; simp only [List.nil_append, List.cons.injEq] at hrest
    exact hyb hrest.1
  obtain ⟨-, hl⟩ := S.rel.later hr hpre
  obtain ⟨v', hv', h1, h2, h3⟩ := hl x hx
  rw [hv] at hv'; cases hv'
  exact ⟨h1, h2, h3⟩

/-- The values of the fused block: the run's. -/
theorem merged_mem {C' : Block} (hC' : g.block? c = some C') (x : ID) :
    x ∈ C'.values ↔ ∃ y ∈ run, x ∈ (valsOf f y).toList := by
  obtain ⟨C, C'', oT, -, hC'', -, hv, -⟩ := S.rel.merged
  rw [hC'] at hC''; cases hC''
  rw [← Array.mem_toList_iff, hv, List.mem_flatMap]

/-- A value of the fused block that is a `Phi` in `g` is a `Phi` of `b0` in `f`. -/
theorem merged_phi {C' : Block} (hC' : g.block? c = some C') {x : ID} (hx : x ∈ C'.values)
    {gv : Value} (hgv : g.value? x = some gv) (hph : gv.op = .Phi) :
    x ∈ (valsOf f b0).toList ∧ ∃ fv, f.value? x = some fv ∧ fv.op = .Phi ∧
      SemEq (some fv) (some gv) ∧ gv.type = fv.type := by
  obtain ⟨y, hy, hxy⟩ := (S.merged_mem hC' x).1 hx
  obtain ⟨hsem, hv⟩ := S.rel.value_same x
  rw [hgv] at hsem
  cases hfv : f.value? x with
  | none => rw [hfv] at hsem; exact hsem.elim
  | some fv =>
    rw [hfv] at hsem
    obtain ⟨gv', hgv', hty, hop, -⟩ := hv fv hfv
    rw [hgv] at hgv'; cases hgv'
    have hfph : fv.op = .Phi := hop ▸ hph
    have hyb : y = b0 := Classical.byContradiction fun hne =>
      (S.later_noPhi hy hne hxy hfv).1 hfph
    subst hyb
    exact ⟨hxy, fv, rfl, hfph, hsem, hty⟩

/-- **The target's `Phi`s and schedule** at the fused block, against a source frame `H` of the
run. -/
theorem targetPre {tabs : Tables} {fr H : Frame} {i : Nat} (hfs : fr.regs.size = f.valueTab.size)
    (hHo : ∀ z, (∀ y ∈ run, z ∉ (valsOf f y).toList) → H.regs[z]? = fr.regs[z]?)
    (hHp : ∀ x ∈ (valsOf f b0).toList, ∀ v, f.value? x = some v → v.op = .Phi →
      ∃ a r, v.args[i]? = some a ∧ fr.regs[a]? = some (some r) ∧
        H.regs[x]? = some (some (r.retype ((Ctx.make tabs f).tys[x]?.getD .other)))) :
    ∃ C' psT oT, g.block? c = some C' ∧ C'.id = c ∧
      C'.values.toList.filterMapM (phiStep (Ctx.make tabs g) fr i) = .ok psT ∧
      schedule g C' = some oT ∧ oT.toList.Nodup ∧ TopoRem (argsF g) oT.toList ∧
      (∀ x, x ∈ oT.toList ↔ x ∈ C'.values ∧ ∃ gv, g.value? x = some gv ∧ gv.op ≠ .Phi) ∧
      (setPhis psT fr.regs).size = fr.regs.size ∧
      ∀ a, a ∉ oT.toList → (setPhis psT fr.regs)[a]? = H.regs[a]? := by
  obtain ⟨ce', hwg⟩ := S.wg
  obtain ⟨C, C', oT, -, hC', hid', -, -, -, -, -, hoT, -⟩ := S.rel.merged
  have hcg := S.cInG
  have hndG := hwg.valuesNodup c C' ⟨hcg, hC'⟩
  obtain ⟨ondT, otopoT, omemT⟩ := schedule_topo (valuesOwn hwg hcg hC') hndG hoT
  obtain ⟨psT, hpsT⟩ : ∃ psT, C'.values.toList.filterMapM (phiStep (Ctx.make tabs g) fr i) =
      .ok psT := by
    refine filterMapM_phi_ok fun z hz => ?_
    rw [Array.mem_toList_iff] at hz
    obtain ⟨gv, hgv, -, -⟩ := hwg.valueId c C' ⟨hcg, hC'⟩ z hz
    by_cases hgph : gv.op = .Phi
    · obtain ⟨hzb, fv, hfv, hfph, hsem, -⟩ := S.merged_phi hC' hz hgv hgph
      obtain ⟨a, y, ha, hy, -⟩ := hHp z hzb fv hfv hfph
      refine ⟨some (z, y.retype ((Ctx.make tabs g).tys[z]?.getD .other)), ?_⟩
      unfold phiStep
      simp only [show (Ctx.make tabs g).f = g from rfl, hgv, hgph, beq_self_eq_true, ite_true,
        show gv.args = fv.args from hsem.2.2.2.2, ha, hy, Option.join]
      rfl
    · refine ⟨none, ?_⟩
      unfold phiStep
      simp only [show (Ctx.make tabs g).f = g from rfl, hgv,
        show (gv.op == .Phi) = false by simpa using hgph]
      rfl
  obtain ⟨hszT, -, hkeepT, hphiT⟩ := phis_spec hndG hpsT
  refine ⟨C', psT, oT, hC', hid', hpsT, hoT, ondT, otopoT, omemT, hszT, fun a ha => ?_⟩
  by_cases haC : a ∈ C'.values
  · obtain ⟨gv, hgv, -, -⟩ := hwg.valueId c C' ⟨hcg, hC'⟩ a haC
    have hgph : gv.op = .Phi := Classical.byContradiction fun hne =>
      ha ((omemT a).2 ⟨haC, gv, hgv, hne⟩)
    obtain ⟨hab, fv, hfv, hfph, hsem, hty⟩ := S.merged_phi hC' haC hgv hgph
    have hlt : a < fr.regs.size := by rw [hfs]; exact lt_of_value? hfv
    obtain ⟨b1, y1, hb1, hy1, hT⟩ := hphiT a haC gv hgv hgph hlt
    obtain ⟨b2, y2, hb2, hy2, hS⟩ := hHp a hab fv hfv hfph
    have hb12 : b1 = b2 := by rw [hsem.2.2.2.2, hb2] at hb1; exact (Option.some.inj hb1).symm
    subst hb12
    rw [hy2] at hy1
    have hy12 : y1 = y2 := (Option.some.inj (Option.some.inj hy1)).symm
    subst hy12
    rw [hT, hS, tys_of_value hgv, tys_of_value hfv, hty]
  · rw [hkeepT a (.inl haC), hHo a fun y hy hm => haC ((S.merged_mem hC' a).2 ⟨y, hy, hm⟩)]

/-- **The fused block runs as the source's run**: from the source's entry frame at `b0`, it
ends in the source's frame after the whole run. -/
theorem merged_ok {tabs : Tables} {env : Env} {fr Gk : Frame} {i : Nat}
    (hfs : fr.regs.size = f.valueTab.size) (hA : Acc env tabs f fr i b0 run Gk) :
    ∃ C', g.block? c = some C' ∧ enterBlock env (Ctx.make tabs g) fr C' i = .ok Gk := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨hGf, hGs, hGo, hGv, hGp⟩ := hA
  obtain ⟨C', psT, oT, hC', hid', hpsT, hoT, -, otopoT, omemT, hszT, hT0⟩ :=
    S.targetPre (tabs := tabs) hfs hGo (hGp S.rel.b0_mem)
  have hargsT : ∀ x gv, g.value? x = some gv → argsF (Ctx.make tabs g).f x = gv.args.toList :=
    fun x gv hgv => argsF_of hgv
  -- every value of the schedule re-evaluates to its register in `Gk`
  have hloc : LocalOK env (Ctx.make tabs g) Gk oT.toList := by
    intro x hx
    obtain ⟨hxC, gv, hgv, hgnp⟩ := (omemT x).1 hx
    obtain ⟨y, hy, hxy⟩ := (S.merged_mem hC' x).1 hxC
    obtain ⟨Y, hY, hxY⟩ := valsOf_mem.1 hxy
    obtain ⟨fv, hfv, hfid, -⟩ := hwf.valueId y Y ⟨S.runIn hy, hY⟩ x hxY
    obtain ⟨gv', hgv', -, hop, hargs⟩ := (S.rel.value_same x).2 fv hfv
    rw [hgv] at hgv'; cases hgv'
    have hfnp : fv.op ≠ .Phi := fun h => hgnp (hop ▸ h)
    obtain ⟨r, hr, hev⟩ := hGv y hy x hxy fv hfv hfnp
    refine ⟨r, hr, fun g' hg' hag => ?_⟩
    rw [stepV_eq hgv, S.eval_same hfv hgv hfid hg' fun a ha => hag a (by
      rw [hargsT x gv hgv, hargs]; exact Array.mem_toList_iff.2 ha)]
    exact hev
  obtain ⟨g', hev, hg'f, -, h4, h5⟩ := evalAll_ref (S := fun a => a ∉ oT.toList)
    (g := { fr with regs := setPhis psT fr.regs }) hloc
    (Dead.refOK_of_topo otopoT fun _ _ _ _ hna => hna) (fun a ha => hT0 a ha)
    (by rw [hGf]) (by show (setPhis psT fr.regs).size = Gk.regs.size; rw [hszT, hGs])
  have hg'eq : g' = Gk := frame_eq hg'f fun z => by
    by_cases hz : z ∈ oT.toList
    · exact h4 z (.inr hz)
    · exact h4 z (.inl hz)
  refine ⟨C', hC', ?_⟩
  rw [enterBlock_eq, hpsT]
  change (Res.ofOption _ ((Ctx.make tabs g).sched[C'.id]?).join).bind _ = _
  rw [hid', sched_of_block hC', hoT]
  change evalAll env (Ctx.make tabs g) _ oT.toList = _
  rw [hev, hg'eq]

end Setup

end GoFV.Proof.FusePlain

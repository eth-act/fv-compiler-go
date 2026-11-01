import GoFV.Proof.Pass.PhiOptEnter

/-!
# phiopt: the target's `Phi`s and reference frame

`targetPhis`: the target collects its `Phi`s (the source's, less the rewritten ones, with the
same arguments) and, after them, agrees with the source after its `Phi`s on the listed values
of `f` other than the rewritten `Phi`s of the block. `newFrame`: a source frame of the block,
extended to the target's size, with the block's new values evaluated in a dependency order
(`Not`s, then conversions): the reference frame `H` of the target's evaluation.
-/

namespace GoFV.Proof.PhiOpt

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.PhiOpt Dom
open GoFV.Proof.CopyElim (Tree)

variable {tabs : Tables} {f g : Func}

/-- `x` is a rewritten `Phi` of the block `fb`. -/
def RwIn (f g : Func) (fb : Block) (x : ID) : Prop := x ∈ fb.values ∧ isRw f g x = true

theorem isRw_iff {x : ID} : isRw f g x = true ↔ (∃ fv, f.value? x = some fv ∧ fv.op = .Phi) ∧
    ∃ gv, g.value? x = some gv ∧ gv.op ≠ .Phi := by
  unfold isRw
  cases f.value? x <;> cases g.value? x <;> simp

theorem newOp_iff {op : Op} {x : ID} : newOp f g op x = true ↔ f.value? x = none ∧
    ∃ v, g.value? x = some v ∧ v.op = op := by
  unfold newOp
  cases f.value? x <;> cases g.value? x <;> simp

/-- **The target's `Phi`s.** -/
theorem targetPhis (S : Setup tabs f g) {env : Env} {fr frT : Frame} {bid : ID} {i : Nat}
    (hA : At env tabs f fr bid i) (hT : TR f g fr frT) {fb gb : Block}
    (hfb : f.block? bid = some fb) (hgb : g.block? bid = some gb) {psS : List (ID × Val)}
    (hpsS : fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) fr i) = .ok psS) :
    ∃ psT, gb.values.toList.filterMapM (phiStep (Ctx.make tabs g) frT i) = .ok psT ∧
      (setPhis psT frT.regs).size = g.valueTab.size ∧
      (∀ z, z ∉ gb.values ∨ (∃ gv, g.value? z = some gv ∧ gv.op ≠ .Phi) →
        (setPhis psT frT.regs)[z]? = frT.regs[z]?) ∧
      ∀ z, Listed f z → ¬ RwIn f g fb z →
        (setPhis psT frT.regs)[z]? = (setPhis psS fr.regs)[z]? := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  have hbt := hA.tree S
  have hndF := hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩
  have hbg : bid ∈ g.blocks := by rw [S.blocks]; exact hbt.1
  have hndG := hwg.valuesNodup _ _ ⟨hbg, hgb⟩
  obtain ⟨hszS, -, hkeepS, hphiS⟩ := phis_spec hndF hpsS
  obtain ⟨hTfr, hTsz, hTl⟩ := hT
  -- a target `Phi` is a source `Phi` with the same arguments
  have hgphi : ∀ z ∈ gb.values, ∀ gv, g.value? z = some gv → gv.op = .Phi →
      ∃ fv, f.value? z = some fv ∧ fv.op = .Phi ∧ z ∈ fb.values ∧ gv.args = fv.args := by
    intro z hz gv hgv hph
    obtain ⟨gv', hgv', -, hk⟩ := gval S hbt.1 hfb hgb hz
    rw [hgv] at hgv'; cases hgv'
    rcases hk with ⟨fv, hfv, hzf, -, -, ⟨hop, -, -, hargs⟩ | hr⟩ | ⟨-, -, hok⟩
    · exact ⟨fv, hfv, by rw [← hop]; exact hph, hzf, hargs⟩
    · exact absurd hph (rewriteOK_spec hr).2.1
    · exact absurd hph (newOK_not_phi hok hgv)
  have hphiEq : ∀ z ∈ gb.values, ∀ gv, g.value? z = some gv → gv.op = .Phi →
      ∃ a y, gv.args[i]? = some a ∧ frT.regs[a]? = some (some y) ∧
        (setPhis psS fr.regs)[z]? =
          some (some (y.retype ((Ctx.make tabs g).tys[z]?.getD .other))) := by
    intro z hz gv hgv hph
    obtain ⟨fv, hfv, hfph, hzf, hargs⟩ := hgphi z hz gv hgv hph
    have hlt : z < fr.regs.size := by rw [hA.size]; exact lt_of_value? hfv
    obtain ⟨a, y, ha, hy, hP⟩ := hphiS z hzf fv hfv hfph hlt
    have hal : Listed f a :=
      hwf.argListed bid fb z fv ⟨⟨hbt.1, hfb⟩, hzf, hfv⟩ a (Array.mem_of_getElem? ha)
    refine ⟨a, y, by rw [hargs]; exact ha, by rw [hTl a hal]; exact hy, ?_⟩
    rw [hP, S.tys hfv]
  obtain ⟨psT, hpsT⟩ : ∃ psT, gb.values.toList.filterMapM (phiStep (Ctx.make tabs g) frT i) =
      .ok psT := by
    refine filterMapM_phi_ok fun z hz => ?_
    rw [Array.mem_toList_iff] at hz
    obtain ⟨gv, hgv, -, -⟩ := hwg.valueId bid gb ⟨hbg, hgb⟩ z hz
    by_cases hgph : gv.op = .Phi
    · obtain ⟨a, y, ha, hy, -⟩ := hphiEq z hz gv hgv hgph
      refine ⟨some (z, y.retype ((Ctx.make tabs g).tys[z]?.getD .other)), ?_⟩
      unfold phiStep
      simp only [show (Ctx.make tabs g).f = g from rfl, hgv, hgph, beq_self_eq_true, ite_true,
        ha, hy, Option.join]
      rfl
    · refine ⟨none, ?_⟩
      unfold phiStep
      simp only [show (Ctx.make tabs g).f = g from rfl, hgv,
        show (gv.op == .Phi) = false by simpa using hgph]
      rfl
  obtain ⟨hszT, -, hkeepT, hphiT⟩ := phis_spec hndG hpsT
  refine ⟨psT, hpsT, by rw [hszT, hTsz], hkeepT, fun z hzl hrw => ?_⟩
  by_cases hzg : z ∈ gb.values ∧ ∃ gv, g.value? z = some gv ∧ gv.op = .Phi
  · obtain ⟨hzb, gv, hgv, hph⟩ := hzg
    obtain ⟨a, y, ha, hy, hP⟩ := hphiEq z hzb gv hgv hph
    have hlt : z < frT.regs.size := by rw [hTsz]; exact lt_of_value? hgv
    obtain ⟨a', y', ha', hy', hT'⟩ := hphiT z (by simpa using hzb) gv hgv hph hlt
    rw [ha] at ha'; cases ha'
    rw [hy] at hy'; cases hy'
    rw [hT', hP]
  · have hk : (setPhis psT frT.regs)[z]? = frT.regs[z]? := by
      refine hkeepT z ?_
      by_cases hzb : z ∈ gb.values
      · obtain ⟨gv, hgv, -, -⟩ := hwg.valueId bid gb ⟨hbg, hgb⟩ z hzb
        exact .inr ⟨gv, hgv, fun hp => hzg ⟨hzb, gv, hgv, hp⟩⟩
      · exact .inl hzb
    rw [hk, hTl z hzl]
    refine (hkeepS z ?_).symm
    by_cases hzf : z ∈ fb.values
    · obtain ⟨fv, hfv, -, -⟩ := hwf.valueId bid fb ⟨hbt.1, hfb⟩ z hzf
      refine .inr ⟨fv, hfv, fun hfph => ?_⟩
      obtain ⟨gb', hgb', -, -, -, -, -, hfg, -⟩ := S.block hbt.1 hfb
      rw [hgb] at hgb'; cases hgb'
      obtain ⟨gv, hgv, -, -, -, hr⟩ := S.rel.value z fv hfv
      rcases hr with ⟨hop, -⟩ | hr
      · exact hzg ⟨hfg z hzf, gv, hgv, by rw [hop]; exact hfph⟩
      · exact hrw ⟨hzf, isRw_iff.2 ⟨⟨fv, hfv, hfph⟩, gv, hgv, (rewriteOK_spec hr).2.1⟩⟩
    · exact .inl hzf

/-- A source frame extended to the target's size. -/
def ext (g : Func) (G : Frame) : Frame :=
  { G with regs := G.regs ++ Array.replicate (g.valueTab.size - G.regs.size) none }

theorem ext_lt {G : Frame} {x : ID} (h : x < G.regs.size) : (ext g G).regs[x]? = G.regs[x]? := by
  simp [ext, Array.getElem?_append_left h]

theorem ext_size {G : Frame} (h : G.regs.size ≤ g.valueTab.size) :
    (ext g G).regs.size = g.valueTab.size := by
  simp [ext]; omega

/-- **The reference frame.** -/
theorem newFrame (S : Setup tabs f g) {env : Env} {fr : Frame} {bid : ID} {i : Nat}
    (hA : At env tabs f fr bid i) {fb gb : Block} (hfb : f.block? bid = some fb)
    (hgb : g.block? bid = some gb) {Gp : Frame}
    (hsz : Gp.regs.size = f.valueTab.size)
    (hout : ∀ z, z ∉ fb.values → Gp.regs[z]? = fr.regs[z]?) :
    ∃ H : Frame, H = { Gp with regs := H.regs } ∧ H.regs.size = g.valueTab.size ∧
      (∀ x, Listed f x → H.regs[x]? = Gp.regs[x]?) ∧
      ∀ x, isNew f g bid x = true → ∀ v, g.value? x = some v →
        ∃ y, H.regs[x]? = some (some y) ∧ evalValue env (Ctx.make tabs g) H v = .ok y := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  have hbt := hA.tree S
  have hbg : bid ∈ g.blocks := by rw [S.blocks]; exact hbt.1
  have hndG := hwg.valuesNodup _ _ ⟨hbg, hgb⟩
  obtain ⟨gb', hgb', -, -, -, -, -, -, hgf⟩ := S.block hbt.1 hfb
  rw [hgb] at hgb'; cases hgb'
  let A := gb.values.toList.filter (newOp f g .Not)
  let B := gb.values.toList.filter (newOp f g .CvtBoolToUint8)
  let L := A ++ B
  have hA' : ∀ x, x ∈ A ↔ x ∈ gb.values ∧ newOp f g .Not x = true := fun x => by
    simp [A, List.mem_filter]
  have hB' : ∀ x, x ∈ B ↔ x ∈ gb.values ∧ newOp f g .CvtBoolToUint8 x = true := fun x => by
    simp [B, List.mem_filter]
  -- what a value of `L` is
  have hL : ∀ x ∈ L, ∃ nv a, g.value? x = some nv ∧ nv.args = #[a] ∧ formOp nv.op ∧
      ((nv.op = .Not ∧ avail f bid a = true) ∨
       (nv.op = .CvtBoolToUint8 ∧ (avail f bid a = true ∨ a ∈ A))) := by
    intro x hx
    have hxb : x ∈ gb.values ∧ f.value? x = none := by
      rcases List.mem_append.1 hx with h | h
      · obtain ⟨h1, h2⟩ := (hA' x).1 h; exact ⟨h1, (newOp_iff.1 h2).1⟩
      · obtain ⟨h1, h2⟩ := (hB' x).1 h; exact ⟨h1, (newOp_iff.1 h2).1⟩
    have hok : newOK f g bid x = true := by
      rcases hgf x hxb.1 with h | ⟨-, h⟩
      · obtain ⟨fv, hfv, -⟩ := hwf.valueId bid fb ⟨hbt.1, hfb⟩ x h
        rw [hxb.2] at hfv; cases hfv
      · exact h
    obtain ⟨nv, a, hnv, -, hargs, hk⟩ := newOK_spec hok
    refine ⟨nv, a, hnv, hargs, ?_, ?_⟩
    · rcases hk with ⟨h, -⟩ | ⟨h, -⟩ <;> unfold formOp <;> simp [h]
    · rcases hk with h | ⟨h1, h2 | ⟨hnew, u, c, hu, hup, -⟩⟩
      · exact .inl h
      · exact .inr ⟨h1, .inl h2⟩
      · obtain ⟨hn, blk, hblk, hm⟩ := isNew_spec hnew
        rw [hgb] at hblk; cases hblk
        exact .inr ⟨h1, .inr ((hA' a).2 ⟨hm, newOp_iff.2 ⟨hn, u, hu, hup⟩⟩)⟩
  have havL : ∀ a, avail f bid a = true → a ∉ L := fun a ha hm => by
    have : a ∈ gb.values := by
      rcases List.mem_append.1 hm with h | h
      · exact ((hA' a).1 h).1
      · exact ((hB' a).1 h).1
    exact avail_not_mem S hbt.1 hfb hgb ha this
  have hnd : L.Nodup := by
    refine List.nodup_append.2 ⟨hndG.filter _, hndG.filter _, fun a ha b hb hab => ?_⟩
    subst hab
    obtain ⟨-, v, hv, h1⟩ := newOp_iff.1 ((hA' a).1 ha).2
    obtain ⟨-, v', hv', h2⟩ := newOp_iff.1 ((hB' a).1 hb).2
    rw [hv] at hv'; cases hv'; exact absurd (h1.symm.trans h2) (by decide)
  have htopo : TopoRem (argsF g) L := by
    refine topoRem_of hnd ?_
    refine before_append (N := (· ∈ L)) (before_none fun x hx a ha hm => ?_) fun j x hj a ha hm => ?_
    · obtain ⟨nv, a', hnv, hargs, -, hk⟩ := hL x (List.mem_append_left _ hx)
      rw [argsF_of hnv, hargs] at ha
      simp only [List.mem_singleton] at ha
      subst ha
      rcases hk with ⟨-, hav⟩ | ⟨hop, -⟩
      · exact havL a hav hm
      · obtain ⟨-, v, hv, hvop⟩ := newOp_iff.1 ((hA' x).1 hx).2
        rw [hnv] at hv; cases hv; rw [hop] at hvop; cases hvop
    · obtain ⟨nv, a', hnv, hargs, -, hk⟩ := hL x (List.mem_append_right _ (List.mem_of_getElem? hj))
      rw [argsF_of hnv, hargs] at ha
      simp only [List.mem_singleton] at ha
      subst ha
      left
      rcases hk with ⟨hop, -⟩ | ⟨-, hav | hA⟩
      · obtain ⟨-, v, hv, hvop⟩ := newOp_iff.1 ((hB' x).1 (List.mem_of_getElem? hj)).2
        rw [hnv] at hv; cases hv; rw [hop] at hvop; cases hvop
      · exact absurd hm (havL a hav)
      · exact hA
  have hfl : ∀ a, avail f bid a = true → ∃ z, (ext g Gp).regs[a]? = some (some z) := by
    intro a ha
    obtain ⟨v, blk, hv, -, -, -, -, -, hnl⟩ := avail_spec ha
    obtain ⟨y, hy⟩ := hA.avail S ha
    have hlt : a < Gp.regs.size := by rw [hsz]; exact lt_of_value? hv
    exact ⟨y, by rw [ext_lt hlt, hout a (not_listedIn hfb hnl), hy]⟩
  have hEsz : (ext g Gp).regs.size = g.valueTab.size := ext_size (by rw [hsz]; exact S.gsize)
  obtain ⟨H, hH⟩ := evalAll_form_ok (env := env) (ctx := Ctx.make tabs g) (fr := ext g Gp)
    (o := L) htopo (fun x hx => by
      obtain ⟨nv, a, hnv, hargs, hop, hk⟩ := hL x hx
      refine ⟨nv, hnv, hop, fun a' ha' => ?_⟩
      rw [hargs] at ha'
      simp only [Array.mem_singleton] at ha'
      subst ha'
      rcases hk with ⟨-, hav⟩ | ⟨-, hav | hA⟩
      · exact .inr (hfl _ hav)
      · exact .inr (hfl _ hav)
      · exact .inl (List.mem_append_left _ hA)) hEsz
  obtain ⟨h1, h2, h3, h4⟩ := evalAll_spec hnd htopo hEsz hH
  refine ⟨H, by rw [h1]; rfl, by rw [h2, hEsz], fun x hx => ?_, fun x hx v hv => ?_⟩
  · obtain ⟨w, hw⟩ := listed_some hwf hx
    have hxL : x ∉ L := fun hm => by
      obtain ⟨nv, -, hnv, -⟩ := hL x hm
      have : f.value? x = none := by
        rcases List.mem_append.1 hm with h | h
        · exact (newOp_iff.1 ((hA' x).1 h).2).1
        · exact (newOp_iff.1 ((hB' x).1 h).2).1
      rw [hw] at this; cases this
    rw [h3 x hxL, ext_lt (by rw [hsz]; exact lt_of_value? hw)]
  · obtain ⟨hn, blk, hblk, hm⟩ := isNew_spec hx
    rw [hgb] at hblk; cases hblk
    have hok : newOK f g bid x = true := by
      rcases hgf x hm with h | ⟨-, h⟩
      · obtain ⟨fv, hfv, -⟩ := hwf.valueId bid fb ⟨hbt.1, hfb⟩ x h
        rw [hn] at hfv; cases hfv
      · exact h
    obtain ⟨nv, a, hnv, -, -, hk⟩ := newOK_spec hok
    rw [hv] at hnv; cases hnv
    have hxL : x ∈ L := by
      rcases hk with ⟨hop, -⟩ | ⟨hop, -⟩
      · exact List.mem_append_left _ ((hA' x).2 ⟨hm, newOp_iff.2 ⟨hn, v, hv, hop⟩⟩)
      · exact List.mem_append_right _ ((hB' x).2 ⟨hm, newOp_iff.2 ⟨hn, v, hv, hop⟩⟩)
    obtain ⟨v', y, hv', hy, hev⟩ := h4 x hxL
    change g.value? x = some v' at hv'
    rw [hv] at hv'; cases hv'
    exact ⟨y, hy, hev⟩

end GoFV.Proof.PhiOpt

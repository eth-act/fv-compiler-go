import GoFV.Proof.Pass.PhiOptCore

/-!
# phiopt: each target value evaluates to its reference register

Against the reference frame `H` of a source frame `Gp` of block `bid` (after the source's
`Phi`s and part of its schedule): a kept value evaluates as the source's (`evalSame`), a
rewritten `Phi` to the `Phi`'s value (`rwLocal`: the edge facts give the control's value on
the entry edge, `boolArm_eval`/`intForm_eval` the rest).
-/

namespace GoFV.Proof.PhiOpt

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.PhiOpt Dom
open GoFV.Proof.CopyElim (Tree)

variable {tabs : Tables} {f g : Func}

/-- **A kept value evaluates as the source's.** -/
theorem evalSame (S : Setup tabs f g) {env : Env} {Gp H : Frame} {bid : ID} {fb : Block}
    (hbin : BlockIn f bid fb) (hHG : ∀ x, Listed f x → H.regs[x]? = Gp.regs[x]?)
    {x : ID} (hx : x ∈ fb.values) {fv gv : Value} (hfv : f.value? x = some fv)
    (hgv : g.value? x = some gv) (hsame : gv.op = fv.op ∧ gv.aux = fv.aux ∧
      gv.auxInt = fv.auxInt ∧ gv.args = fv.args)
    (hdef : ∀ msg, evalValue env (Ctx.make tabs f) Gp fv ≠ .stuck msg)
    {g' : Frame} (hg' : g' = { Gp with regs := g'.regs })
    (hag : ∀ a ∈ gv.args, g'.regs[a]? = H.regs[a]?) :
    evalValue env (Ctx.make tabs g) g' gv = evalValue env (Ctx.make tabs f) Gp fv := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨gv', hgv', hid, -⟩ := S.rel.value x fv hfv
  rw [hgv] at hgv'; cases hgv'
  obtain ⟨fv', hfv', hfid, -⟩ := hwf.valueId bid fb hbin x hx
  rw [hfv] at hfv'; cases hfv'
  obtain ⟨hop, hax, hai, hargs⟩ := hsame
  have hargsdef := evalValue_args_def hdef
  refine evalValue_eq_of_args hop hax hai hid (by rw [hargs]) (fun k a ha => ?_) hg'
    (by rw [hfid]; exact S.tys hfv) rfl S.params rfl
  obtain ⟨y, hy⟩ := hargsdef a (Array.mem_of_getElem? ha)
  refine ⟨a, y, by rw [hargs]; exact ha, hy, ?_⟩
  have hal : Listed f a :=
    hwf.argListed bid fb x fv ⟨hbin, hx, hfv⟩ a (Array.mem_of_getElem? ha)
  rw [hag a (by rw [hargs]; exact Array.mem_of_getElem? ha), hHG a hal, hy]

/-- An arm of a `Phi` is a listed value without arguments when it is a constant. -/
theorem arm_argless {ce : CheckEnv} (hwf : WF ce f) {a : ID} (hal : Listed f a) {u : Value}
    (hu : f.value? a = some u) (hop : u.op.argLen = 0) : u.args = #[] ∧ u.id = a := by
  obtain ⟨b, blk, hb, hx⟩ := hal
  obtain ⟨u', hu', hid, -⟩ := hwf.valueId b blk hb a hx
  rw [hu] at hu'; cases hu'
  have := hwf.arity b blk a u ⟨hb, hx, hu⟩ (by rw [hop]; decide)
  rw [hop] at this
  exact ⟨Array.eq_empty_of_size_eq_zero (by omega), hid⟩

/-- **A rewritten `Phi` evaluates to the `Phi`'s value.** `fr`: the source frame on entry to
`bid` along `i`; `Gp`: a later source frame of the block (its `Phi`s set); `H`: `Gp`'s
reference frame. -/
theorem rwLocal (S : Setup tabs f g) {env : Env} {fr : Frame} {bid : ID} {i : Nat}
    (hA : At env tabs f fr bid i) {fb : Block} (hfb : f.block? bid = some fb)
    {Gp H : Frame} (hout : ∀ z, z ∉ fb.values → Gp.regs[z]? = fr.regs[z]?)
    (hHG : ∀ x, Listed f x → H.regs[x]? = Gp.regs[x]?)
    (hnew : ∀ x, isNew f g bid x = true → ∀ v, g.value? x = some v →
      ∃ y, H.regs[x]? = some (some y) ∧ evalValue env (Ctx.make tabs g) H v = .ok y)
    {x : ID} (hx : x ∈ fb.values) {fv gv : Value} (hfv : f.value? x = some fv)
    (hgv : g.value? x = some gv) (hr : rewriteOK tabs f g fv gv = true)
    {a : ID} {y : Val} (ha : fv.args[i]? = some a) (hy : fr.regs[a]? = some (some y))
    {g' : Frame} (hag : ∀ a ∈ gv.args, g'.regs[a]? = H.regs[a]?) :
    evalValue env (Ctx.make tabs g) g' gv =
      .ok (y.retype ((Ctx.make tabs f).tys[x]?.getD .other)) := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  have hbt := hA.tree S
  obtain ⟨fv', hfv', hfid, hfblk⟩ := hwf.valueId bid fb ⟨hbt.1, hfb⟩ x hx
  rw [hfv] at hfv'; cases hfv'
  obtain ⟨gv', hgv', hgid, hgty, -⟩ := S.rel.value x fv hfv
  rw [hgv] at hgv'; cases hgv'
  obtain ⟨-, -, -, -, hform⟩ := rewriteOK_spec hr
  rw [hfblk] at hform
  have hal : Listed f a :=
    hwf.argListed bid fb x fv ⟨⟨hbt.1, hfb⟩, hx, hfv⟩ a (Array.mem_of_getElem? ha)
  have htyS : (Ctx.make tabs f).tys[x]?.getD .other = tabs.ty fv.type := by
    rw [tys_of_value hfv]; rfl
  have htyT : (Ctx.make tabs g).tys[gv.id]?.getD .other = tabs.ty fv.type := by
    rw [hgid, hfid, tys_of_value hgv, hgty]; rfl
  -- an available value reads in `H` as on entry
  have havH : ∀ z, avail f bid z = true → H.regs[z]? = fr.regs[z]? := by
    intro z hz
    obtain ⟨v, blk, hv, hvb, hblk, hzb, -, -, hnl⟩ := avail_spec hz
    rw [hHG z ⟨v.block, blk, ⟨hvb, hblk⟩, hzb⟩, hout z (not_listedIn hfb hnl)]
  rw [htyS]
  rcases hform with ⟨hbool, c, hc0, hcav, hall⟩ | ⟨w, c, neg, hshape, hall⟩
  · obtain ⟨d, hd, harm⟩ := hall i a ha
    have hcv := hA.path c _ d hd
    have hargsav : ∀ z ∈ gv.args, avail f bid z = true := by
      rcases harm with ⟨-, hargs, -⟩ | ⟨-, hargs, -⟩ | ⟨n, -, hargs, hn, -⟩ |
        ⟨n, -, hargs, hn, -⟩ <;> rw [hargs] <;> intro z hz <;>
        simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil,
          or_false] at hz
      · subst hz; exact hcav
      · subst hz; exact hcav
      · rcases hz with rfl | rfl
        · exact hcav
        · exact hn
      · rcases hz with rfl | rfl
        · exact hcav
        · exact hn
    rw [hbool]
    refine boolArm_eval harm hcv (fun z hz => hA.avail S hz) hy (fun d' hcb => ?_)
      (fun z hz => by rw [hag z hz, havH z (hargsav z hz)]) (by rw [htyT, hbool])
    obtain ⟨u, hu, hop, hval, hty⟩ := constB_spec hcb
    obtain ⟨huargs, huid⟩ := arm_argless hwf hal hu (by rw [hop]; decide)
    rw [constBool_reg hA.inv hu hop hty huid huargs hy, hval]
  · obtain ⟨d, hd, hk⟩ := hall i a ha
    obtain ⟨u, hu, hop, hty, hai⟩ := constI_spec hk
    obtain ⟨huargs, huid⟩ := arm_argless hwf hal hu (by rw [hop]; cases w <;> decide)
    rw [constI_reg hA.inv hu hop hty huid huargs hy, hai, hshape.1]
    have hcav := hshape.2.2.1
    have hcH : H.regs[c]? = some (some (.bool d)) := by
      rw [havH c hcav]; exact hA.path c _ d hd
    rw [intForm_eval hshape hcH hnew (fun z v hv hzn => by
        obtain ⟨-, blk, hblk, hzb⟩ := isNew_spec hzn
        have hbg : bid ∈ g.blocks := by rw [S.blocks]; exact hbt.1
        obtain ⟨v', hv', hid, -⟩ := hwg.valueId bid blk ⟨hbg, hblk⟩ z hzb
        rw [hv] at hv'; cases hv'; exact hid) hag (by rw [htyT, hshape.1])]
    simp [Val.retype, BitVec.setWidth_eq]

end GoFV.Proof.PhiOpt

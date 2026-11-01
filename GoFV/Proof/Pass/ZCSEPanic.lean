import GoFV.Proof.Pass.ZCSEBlock
import GoFV.Proof.Pass.ZCSERank

/-!
# zcse: a block where the source panics

`enter_panic`: the source panics at a root `r` of its schedule after a prefix `pre`; every
source value the target evaluates before `r` is in `pre` (`schedTransfer`: the rank
tie-break keeps the roots' order, #96), the others are representatives, so the target reaches
`r` agreeing with `fill` of the source's frame and panics alike.
-/

namespace GoFV.Proof.ZCSE

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.ZCSE Dom
open GoFV.Proof.CopyElim (Tree refOK_prefix frame_ext stepV_of topoRem_at topoRem_append_left)

variable {tabs : Tables} {f g : Func}

/-- **A block the source panics in makes the target panic alike.** -/
theorem enter_panic (S : Setup tabs f g) {env : Env} {fr frT : Frame} {bid : ID} {i : Nat}
    (hA : At env tabs f fr bid i) (hT : TF env tabs f g fr frT bid) {fb : Block}
    (hfb : f.block? bid = some fb) {e : Panic} {m : Mem}
    (h : enterBlock env (Ctx.make tabs f) fr fb i = .panic e m) :
    ∃ gb, g.block? bid = some gb ∧ enterBlock env (Ctx.make tabs g) frT gb i = .panic e m := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  have hbt := hA.tree S
  have hndF := hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩
  have hownF := valuesOwn hwf hbt.1 hfb
  obtain ⟨fb', hfb', hfid⟩ := hwf.blockId bid hbt.1
  rw [hfb] at hfb'; cases hfb'
  obtain ⟨psS, oS, hpsS, hso, hev⟩ := enterBlock_panic h
  rw [hfid, sched_of_block hfb] at hso
  obtain ⟨pre, r, post, Gpre, hsplit, hpre, hrp⟩ := evalAll_panic_split hev
  obtain ⟨gb, psT, oT, hgbb, hgid, hpsT, hoT, hagree, hszT⟩ := targetPre S hA hT hfb hpsS hso
  obtain ⟨gb', hgb', -, -, -, -, -, hfg, hgf⟩ := S.block hbt.1 hfb
  rw [hgbb] at hgb'; cases hgb'
  have hbg : bid ∈ g.blocks := by rw [S.blocks]; exact hbt.1
  have hownG := valuesOwn hwg hbg hgbb
  have hndG := hwg.valuesNodup _ _ ⟨hbg, hgbb⟩
  obtain ⟨-, otopoT, omemT⟩ := schedule_topo hownG hndG hoT
  obtain ⟨ond, otopo, omem⟩ := schedule_topo hownF hndF hso
  obtain ⟨hszS, -, -, -⟩ := phis_spec hndF hpsS
  -- the source's frame at the panic
  have ond' := ond
  have otopo' := otopo
  rw [hsplit] at ond' otopo'
  obtain ⟨p1, p2, p3, p4⟩ := evalAll_spec (List.nodup_append.1 ond').1
    (topoRem_append_left otopo') (by simp [hszS, hA.size]; rfl) hpre
  have hG : Gpre = { fr with regs := Gpre.regs } := by rw [p1]
  have hszG : Gpre.regs.size = f.valueTab.size := by rw [p2, hszS, hA.size]
  have himG : Gpre.images.size = (Ctx.make tabs f).params.size := by rw [hG]; exact hA.images
  have hinvG : ArglessInv env (Ctx.make tabs f) Gpre :=
    (arglessInv_evalAll (arglessInv_phis hA.inv hndF hpsS) hpre).1
  -- the panicking root
  have hrS : r ∈ oS.toList := by rw [hsplit]; simp
  obtain ⟨hrb, fvr, hfvr, hrnph⟩ := (omem r).1 hrS
  rw [stepV_of hfvr] at hrp
  have hrop := evalValue_panic_op hrp

  have hrne := evalValue_panic_args hrp
  obtain ⟨gvr, hgvr, -, hgop, -⟩ := S.value hfvr
  have hrT : r ∈ oT.toList :=
    (omemT r).2 ⟨(hfg r hrb).resolve_right (not_ea S hfvr hrne), gvr, hgvr,
      by rw [hgop]; exact hrnph⟩
  obtain ⟨pre', post', hsplitT⟩ := List.append_of_mem hrT
  have hk : oS.toList[pre.length]? = some r := by rw [hsplit]; simp
  have hk' : oT.toList[pre'.length]? = some r := by rw [hsplitT]; simp
  have htr := schedTransfer S hbt.1 hfb hgbb hso hoT hk hk'
    ((npIn_sched hownF hndF).2 ⟨hrb, fvr, hfvr, hrnph, prio_panicking hrop⟩)
  -- the target's prefix agrees with `fill` of the source's frame at the panic
  have hargsT : ∀ x gv, g.value? x = some gv → argsF (Ctx.make tabs g).f x = gv.args.toList :=
    fun x gv hgv => argsF_of (f := g) hgv
  have hinPre : ∀ x, (∃ i < pre.length, oS.toList[i]? = some x) → x ∈ pre := by
    rintro x ⟨i, hi, hix⟩
    rw [hsplit, List.getElem?_append_left hi] at hix
    exact List.mem_of_getElem? hix
  have hloc : LocalOK env (Ctx.make tabs g) (fill env tabs g Gpre) pre' := by
    intro x hx
    have hxT : x ∈ oT.toList := by rw [hsplitT]; exact List.mem_append_left _ hx
    obtain ⟨hxb, gv, hgv, hgn⟩ := (omemT x).1 hxT
    by_cases hea : EA g x
    · obtain ⟨v, y, hv, hev, hfill⟩ := fill_ea S hszG himG hea
      rw [hgv] at hv; cases hv
      obtain ⟨-, -, -, w, hw, hwa, -⟩ := ea_iff.1 hea
      rw [hgv] at hw; cases hw
      refine ⟨y, hfill, fun g' hg' _ => ?_⟩
      rw [stepV_of (ctx := Ctx.make tabs g) hgv, evalValue_argless_regs hwa (fr := Gpre)
        (by rw [hg']; rfl)]
      exact hev
    · have hxf := (hgf x hxb).resolve_right hea
      obtain ⟨fv, hfv, -, -⟩ := hwf.valueId bid fb ⟨hbt.1, hfb⟩ x hxf
      obtain ⟨gv', hgv', -, hop, -⟩ := S.value hfv
      rw [hgv] at hgv'; cases hgv'
      have hfn : fv.op ≠ .Phi := by rw [← hop]; exact hgn
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
      have hjl := lt_length_of_getElem? hj
      have hjT : oT.toList[j]? = some x := by rw [hsplitT, List.getElem?_append_left hjl]; exact hj
      obtain ⟨i', hi', hix⟩ := htr j x hjl hjT ((nodeIn_schedNodes hownF).2 ⟨hxf, fv, hfv, hfn⟩)
      obtain ⟨v', y, hv', hy, hevx⟩ := p4 x (hinPre x ⟨i', hi', hix⟩)
      change f.value? x = some v' at hv'; rw [hfv] at hv'; cases hv'
      refine ⟨y, by rw [fill_not_ea env Gpre hea]; exact hy, fun g' hg' hag => ?_⟩
      rw [stepV_of (ctx := Ctx.make tabs g) hgv, ← hevx]
      exact evalSame S hinvG hszG ⟨hbt.1, hfb⟩ hxf hfv hgv
        (fun msg he => by rw [hevx] at he; cases he) (by rw [hg']; rfl)
        (fun a ha => hag a (by rw [hargsT x gv hgv]; exact Array.mem_toList_iff.2 ha))
  have hS : ∀ a, a ∉ oT.toList →
      (setPhis psT frT.regs)[a]? = (fill env tabs g Gpre).regs[a]? := by
    intro a ha
    rw [hagree a ha]
    by_cases hea : EA g a
    · exact (fill_ea_eq p1 (by rw [p2]) hea).symm
    · rw [fill_not_ea env _ hea, fill_not_ea env _ hea]
      refine (p3 a fun hm => ha ?_).symm
      have ham : a ∈ oS.toList := by rw [hsplit]; exact List.mem_append_left _ hm
      obtain ⟨hab, fv, hfv, hne⟩ := (omem a).1 ham
      obtain ⟨gv, hgv, -, hop, -⟩ := S.value hfv
      exact (omemT a).2 ⟨(hfg a hab).resolve_right hea, gv, hgv, by rw [hop]; exact hne⟩
  obtain ⟨hTfr, -⟩ := hT.frame
  have hframe : ({ frT with regs := setPhis psT frT.regs } : Frame) =
      { fill env tabs g Gpre with regs := setPhis psT frT.regs } := by
    apply frame_with
    · rw [hTfr, fill_frame, hG]
    · rw [hTfr, fill_frame, hG]
    · rw [hTfr, fill_frame, hG]
    · rw [hTfr, fill_frame, hG]
  have htopoT : TopoRem (argsF (Ctx.make tabs g).f) (pre' ++ r :: post') := by
    rw [← hsplitT]; exact otopoT
  have hpanT := evalAll_ref_panic (S := fun a => a ∉ oT.toList) (post := post')
    (g := { frT with regs := setPhis psT frT.regs }) hloc
    (refOK_prefix htopoT (fun a ha => by rw [hsplitT]; exact ha))
    hS hframe (by simp only [fill_size]; rw [hszT, hszG, hA.size])
    (fun a ha => by
      by_cases haT : a ∈ oT.toList
      · rw [hsplitT] at haT
        rcases List.mem_append.1 haT with h' | h'
        · exact .inr h'
        · exact absurd h' (topoRem_at htopoT a ha)
      · exact .inl haT)
    (fun g' hg' hag => by
      rw [stepV_of (ctx := Ctx.make tabs g) hgvr, ← hrp]
      exact evalSame S hinvG hszG ⟨hbt.1, hfb⟩ hrb hfvr hgvr
        (fun msg he => by rw [hrp] at he; cases he) (by rw [hg']; rfl)
        (fun a ha => hag a (by rw [hargsT r gvr hgvr]; exact Array.mem_toList_iff.2 ha)))
  refine ⟨gb, hgbb, ?_⟩
  rw [enterBlock_eq, hpsT]
  change (Res.ofOption _ ((Ctx.make tabs g).sched[gb.id]?).join).bind _ = _
  rw [hgid, sched_of_block hgbb, hoT]
  change evalAll env (Ctx.make tabs g) _ oT.toList = _
  rw [hsplitT, hpanT]

end GoFV.Proof.ZCSE

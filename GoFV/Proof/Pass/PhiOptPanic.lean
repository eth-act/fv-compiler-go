import GoFV.Proof.Pass.PhiOptBlock

/-!
# phiopt: a block where the source panics

`enter_panic`: the source panics at a root `r` of its schedule after a prefix `pre`; every
source value the target evaluates before `r` is in `pre` (`Order.transfer`: the roots of `f`'s
tree blocks are chained, target dependency chains from `r` follow the source's, `depPres`), the
others are new values and rewritten `Phi`s, so the target reaches `r` agreeing with the
reference frame of the source's frame at the panic and panics alike.
-/

namespace GoFV.Proof.PhiOpt

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.PhiOpt Dom
open GoFV.Proof.CopyElim (Tree stepV_of topoRem_at prio_panicking)
open GoFV.Proof.ZCSE (evalValue_panic_args)

variable {tabs : Tables} {f g : Func}

/-- **A block the source panics in makes the target panic alike.** -/
theorem enter_panic (S : Setup tabs f g) {env : Env} {fr frT : Frame} {bid : ID} {i : Nat}
    (hA : At env tabs f fr bid i) (hT : TR f g fr frT) {fb : Block}
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
  obtain ⟨gb, psT, oT, H, hgbb, hgid, hpsT, hoT, hH, hHsz, hHG, hagree, hframe, hsz, hrefS,
    hloc, hsame⟩ := targetRun S hA hT hfb hpsS hso hsplit hpre
  have hbg : bid ∈ g.blocks := by rw [S.blocks]; exact hbt.1
  have hownG := valuesOwn hwg hbg hgbb
  have hndG := hwg.valuesNodup _ _ ⟨hbg, hgbb⟩
  obtain ⟨-, otopoT, omemT⟩ := schedule_topo hownG hndG hoT
  obtain ⟨-, -, omem⟩ := schedule_topo hownF hndF hso
  -- the panicking root
  have hrS : r ∈ oS.toList := by rw [hsplit]; simp
  obtain ⟨hrb, fvr, hfvr, hrnph⟩ := (omem r).1 hrS
  rw [stepV_of hfvr] at hrp
  have hrop : fvr.op = .PanicBounds ∨ fvr.op = .StaticLECall ∨ fvr.op = .StaticCall := by
    rcases evalValue_panic_op hrp with h | h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr h)
    · exact absurd h (S.noNil _ _ hfvr)
  obtain ⟨gvr, hgvr, -, -, -, hr⟩ := S.rel.value r fvr hfvr
  have hrsame : gvr.op = fvr.op ∧ gvr.aux = fvr.aux ∧ gvr.auxInt = fvr.auxInt ∧
      gvr.args = fvr.args := by
    rcases hr with h | h
    · exact h
    · exact absurd (rewriteOK_spec h).1 hrnph
  have hnodeR : NodeIn (schedNodes f fb).toList r :=
    (nodeIn_schedNodes hownF).2 ⟨hrb, fvr, hfvr, hrnph⟩
  have hrT : r ∈ oT.toList :=
    (omemT r).2 ((nodeIn_schedNodes hownG).1 (fnode S hbt.1 hfb hgbb hnodeR).1)
  obtain ⟨pre', post', hsplitT⟩ := List.append_of_mem hrT
  have hspecS := schedule_spec hso
  have hspecT := schedule_spec hoT
  have hk : oS.toList[pre.length]? = some r := by rw [hsplit]; simp
  have hk' : oT.toList[pre'.length]? = some r := by rw [hsplitT]; simp
  have hfrid : fvr.id = r := by
    obtain ⟨v', hv', hid, -⟩ := hwf.valueId bid fb ⟨hbt.1, hfb⟩ r hrb
    rw [hfvr] at hv'; cases hv'; exact hid
  have hnotNil : ¬ NilIn (schedNodes f fb).toList r := by
    intro hn
    have hm : (⟨fvr.id, fvr.args, prio fvr.op⟩ : SNode) ∈ (schedNodes f fb).toList :=
      mem_schedNodes.2 ⟨r, hrb, fvr, hfvr, hrnph, rfl⟩
    have := hn _ (by rw [← hfrid]; exact nodeOf_of_mem (schedNodes_ids hownF hndF) hm)
    simp only [prio_panicking hrop] at this; omega
  have htr := Order.transfer hspecS.topo hspecS.nilFirst hspecT.topo hk hk' hnotNil
    (fun y hy hyn hyr => S.chained bid hbt.1 hbt.2 fb hfb y r hy hnodeR hyn hnotNil hyr)
    (fun y _ _ hd => depPres S hbt.1 hfb hgbb hd)
  -- the target's prefix evaluates against the reference frame
  have hL := hloc pre' (fun x hx => by rw [hsplitT]; exact List.mem_append_left _ hx)
    fun x hx hN => by
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
      have hjl : j < pre'.length := (List.getElem?_eq_some_iff.1 hj).1
      have hjT : oT.toList[j]? = some x := by
        rw [hsplitT, List.getElem?_append_left hjl]; exact hj
      obtain ⟨i', hi', hix⟩ := htr j x hjl hjT hN
      rw [hsplit, List.getElem?_append_left hi'] at hix
      exact List.mem_of_getElem? hix
  have href := refOK_of_topo (Q := fun a => Listed f a) (pre := []) otopoT
    fun x hx a ha hn => hrefS x hx a ha (by simpa using hn)
  have href' := RefOK.prefix (L2 := r :: post') (by rw [← hsplitT]; exact href)
  have htopoT : TopoRem (argsF (Ctx.make tabs g).f) (pre' ++ r :: post') := by
    rw [← hsplitT]; exact otopoT
  have hargsT : argsF (Ctx.make tabs g).f r = gvr.args.toList := argsF_of (f := g) hgvr
  have hpanT := evalAll_ref_panic (post := post') (g := { frT with regs := setPhis psT frT.regs })
    hL href' (fun a ha => by
      rcases ha with ⟨hn, hl⟩ | hm
      · exact hagree a (by simpa using hn) hl
      · cases hm) hframe hsz
    (fun a ha => by
      by_cases haT : a ∈ oT.toList
      · rw [hsplitT] at haT
        rcases List.mem_append.1 haT with h' | h'
        · exact .inr h'
        · exact absurd h' (topoRem_at htopoT a ha)
      · exact .inl (.inl ⟨by simpa using haT, hrefS r hrT a ha haT⟩))
    (fun g' hg' hag => by
      rw [stepV_of (ctx := Ctx.make tabs g) hgvr, ← hrp]
      exact hsame r fvr gvr hrb hfvr hgvr hrsame (fun msg he => by rw [hrp] at he; cases he)
        g' hg' (fun a ha => hag a (by rw [hargsT]; exact Array.mem_toList_iff.2 ha)))
  refine ⟨gb, hgbb, ?_⟩
  rw [enterBlock_eq, hpsT]
  change (Res.ofOption _ ((Ctx.make tabs g).sched[gb.id]?).join).bind _ = _
  rw [hgid, sched_of_block hgbb, hoT]
  change evalAll env (Ctx.make tabs g) _ oT.toList = _
  rw [hsplitT, hpanT]

end GoFV.Proof.PhiOpt

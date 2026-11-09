import GoFV.Proof.Pass.ZCSEEnter

variable [GoFV.SSA.Sem.Addrs]

/-!
# zcse: the target's evaluation of a block

`enter_ok`: a block the source enters to frame `G` the target enters to `fill G` (each target
value evaluates, against `fill G`, to its register there: `evalSame` for the source's values,
the constant for the representatives). `enter_panic` (`GoFV.Proof.Pass.ZCSEPanic`): a source
panic at a root is reached by the target too; the target evaluates before it only values the
source evaluated before it (`schedTransfer`) and representatives.
-/

namespace GoFV.Proof.ZCSE

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.ZCSE Dom
open GoFV.Proof.CopyElim (Tree refOK_prefix frame_ext stepV_of topoRem_at topoRem_append_left)

variable {tabs : Tables} {f g : Func}

theorem frame_with {a b : Frame} (h1 : a.args = b.args) (h2 : a.mem0 = b.mem0)
    (h3 : a.images = b.images) (h4 : a.closure = b.closure) (r : Array (Option Val)) :
    ({ a with regs := r } : Frame) = { b with regs := r } := by
  cases a; cases b; simp_all

/-- A value that panics has arguments (`PanicBounds`, calls and nil checks need them). -/
theorem evalValue_panic_args {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {e : Panic}
    {m : Mem} (h : evalValue env ctx fr v = .panic e m) : v.args ≠ #[] := by
  intro ha
  unfold evalValue at h
  rw [ha] at h
  simp only [List.mapM_nil, bind, Res.bind, pure] at h
  have he : ∃ e' m', evalOp env ctx fr v [] (ctx.tys[v.id]?.getD .other) = .panic e' m' := by
    revert h
    cases evalOp env ctx fr v [] (ctx.tys[v.id]?.getD .other) <;> simp
  obtain ⟨e', m', he⟩ := he
  unfold evalOp at he
  split at he
  all_goals first
    | cases he
    | exact absurd he argVal_not_panic
    | exact absurd he callOp_nil
    | (simp [panicBounds] at he; done)
    | (simp [memRoot] at he; done)
    | (split at he <;> first
        | cases he
        | exact absurd he argVal_not_panic
        | (split at he <;> cases he))

/-- The source frame after the `Phi`s keeps `ArglessInv`. -/
theorem arglessInv_phis {env : Env} {ctx : Ctx} {fr : Frame} {b : Block} {i : Nat}
    {ps : List (ID × Val)} (h : ArglessInv env ctx fr) (hnd : b.values.toList.Nodup)
    (hps : b.values.toList.filterMapM (phiStep ctx fr i) = .ok ps) :
    ArglessInv env ctx { fr with regs := setPhis ps fr.regs } := by
  obtain ⟨-, -, hkeep, -⟩ := phis_spec hnd hps
  exact h.frame rfl fun x v hv _ hn => hkeep x (.inr ⟨v, hv, hn⟩)

/-- **A block the source enters successfully is entered by the target, to `fill` of the
source's frame.** -/
theorem enter_ok (S : Setup tabs f g) {env : Env} {fr frT : Frame} {bid : ID} {i : Nat}
    (hA : At env tabs f fr bid i) (hT : TF env tabs f g fr frT bid) {fb : Block}
    (hfb : f.block? bid = some fb) {G : Frame}
    (h : enterBlock env (Ctx.make tabs f) fr fb i = .ok G) :
    ∃ gb, g.block? bid = some gb ∧
      enterBlock env (Ctx.make tabs g) frT gb i = .ok (fill env tabs g G) := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  have hbt := hA.tree S
  have hndF := hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩
  have hinvG := arglessInv_enter hA.inv hndF h
  obtain ⟨fb', hfb', hfid⟩ := hwf.blockId bid hbt.1
  rw [hfb] at hfb'; cases hfb'
  rw [enterBlock_eq] at h
  cases hpsS : fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) fr i) with
  | panic e m => rw [hpsS] at h; cases h
  | stuck msg => rw [hpsS] at h; cases h
  | ok psS =>
  rw [hpsS] at h
  change (Res.ofOption _ ((Ctx.make tabs f).sched[fb.id]?).join).bind _ = _ at h
  rw [hfid, sched_of_block hfb] at h
  cases hsched : schedule f fb with
  | none => rw [hsched] at h; cases h
  | some oS =>
  rw [hsched] at h
  change evalAll env (Ctx.make tabs f) _ oS.toList = .ok G at h
  obtain ⟨gb, psT, oT, hgbb, hgid, hpsT, hoT, hagree, hszT⟩ := targetPre S hA hT hfb hpsS hsched
  obtain ⟨gb', hgb', -, -, -, -, -, hfg, hgf⟩ := S.block hbt.1 hfb
  rw [hgbb] at hgb'; cases hgb'
  have hbg : bid ∈ g.blocks := by rw [S.blocks]; exact hbt.1
  have hndG := hwg.valuesNodup _ _ ⟨hbg, hgbb⟩
  obtain ⟨-, otopoT, omemT⟩ := schedule_topo (valuesOwn hwg hbg hgbb) hndG hoT
  obtain ⟨ond, otopo, omem⟩ := schedule_topo (valuesOwn hwf hbt.1 hfb) hndF hsched
  obtain ⟨hszS, -, -, -⟩ := phis_spec hndF hpsS
  obtain ⟨e1, e2, e3, e4⟩ := evalAll_spec ond (by exact otopo) (by simp [hszS, hA.size]; rfl) h
  have hG : G = { fr with regs := G.regs } := by rw [e1]
  have hszG : G.regs.size = f.valueTab.size := by rw [e2, hszS, hA.size]
  have himG : G.images.size = (Ctx.make tabs f).params.size := by rw [hG]; exact hA.images
  -- the target's evaluation against `fill G`
  have hloc : LocalOK env (Ctx.make tabs g) (fill env tabs g G) oT.toList := by
    intro x hx
    obtain ⟨hxb, gv, hgv, hgn⟩ := (omemT x).1 hx
    have hargsT : argsF (Ctx.make tabs g).f x = gv.args.toList := argsF_of (f := g) hgv
    by_cases hea : EA g x
    · obtain ⟨v, y, hv, hev, hfill⟩ := fill_ea S hszG himG hea
      rw [hgv] at hv; cases hv
      obtain ⟨-, -, -, w, hw, hwa, -⟩ := ea_iff.1 hea
      rw [hgv] at hw; cases hw
      refine ⟨y, hfill, fun g' hg' _ => ?_⟩
      rw [stepV_of (ctx := Ctx.make tabs g) hgv, evalValue_argless_regs hwa (fr := G)
        (by rw [hg']; rfl)]
      exact hev
    · have hxf := (hgf x hxb).resolve_right hea
      obtain ⟨fv, hfv, -, -⟩ := hwf.valueId bid fb ⟨hbt.1, hfb⟩ x hxf
      obtain ⟨gv', hgv', -, hop, -⟩ := S.value hfv
      rw [hgv] at hgv'; cases hgv'
      have hxS : x ∈ oS.toList := (omem x).2 ⟨hxf, fv, hfv, by rw [← hop]; exact hgn⟩
      obtain ⟨v', y, hv', hy, hev⟩ := e4 x hxS
      change f.value? x = some v' at hv'; rw [hfv] at hv'; cases hv'
      refine ⟨y, by rw [fill_not_ea env G hea]; exact hy, fun g' hg' hag => ?_⟩
      rw [stepV_of (ctx := Ctx.make tabs g) hgv, ← hev]
      exact evalSame S hinvG hszG ⟨hbt.1, hfb⟩ hxf hfv hgv
        (fun msg he => by rw [hev] at he; cases he) (by rw [hg']; rfl)
        (fun a ha => hag a (by rw [hargsT]; exact Array.mem_toList_iff.2 ha))
  have hS : ∀ a, a ∉ oT.toList → (setPhis psT frT.regs)[a]? = (fill env tabs g G).regs[a]? := by
    intro a ha
    rw [hagree a ha]
    by_cases hea : EA g a
    · exact (fill_ea_eq e1 (by rw [e2]) hea).symm
    · rw [fill_not_ea env _ hea, fill_not_ea env _ hea]
      refine (e3 a fun ham => ha ?_).symm
      obtain ⟨hab, fv, hfv, hne⟩ := (omem a).1 ham
      obtain ⟨gv, hgv, -, hop, -⟩ := S.value hfv
      exact (omemT a).2 ⟨(hfg a hab).resolve_right hea, gv, hgv, by rw [hop]; exact hne⟩
  obtain ⟨hTfr, hTsz⟩ := hT.frame
  have hframe : ({ frT with regs := setPhis psT frT.regs } : Frame) =
      { fill env tabs g G with regs := setPhis psT frT.regs } := by
    apply frame_with
    · rw [hTfr, fill_frame, hG]
    · rw [hTfr, fill_frame, hG]
    · rw [hTfr, fill_frame, hG]
    · rw [hTfr, fill_frame, hG]
  obtain ⟨g'', h1, h2, -, h4, -⟩ := evalAll_ref (S := fun a => a ∉ oT.toList)
    (g := { frT with regs := setPhis psT frT.regs }) hloc
    (refOK_prefix (L2 := []) (by rw [List.append_nil]; exact otopoT)
      (fun a ha => by simpa using ha))
    hS hframe (by simp only [fill_size]; rw [hszT, hszG, hA.size])
  have hgG : g'' = fill env tabs g G := frame_ext (h2.trans (by rw [fill_frame])) fun a =>
    h4 a (by
      by_cases ha : a ∈ oT.toList
      · exact .inr ha
      · exact .inl ha)
  refine ⟨gb, hgbb, ?_⟩
  rw [enterBlock_eq, hpsT]
  change (Res.ofOption _ ((Ctx.make tabs g).sched[gb.id]?).join).bind _ = _
  rw [hgid, sched_of_block hgbb, hoT]
  change evalAll env (Ctx.make tabs g) _ oT.toList = _
  rw [h1, hgG]

end GoFV.Proof.ZCSE

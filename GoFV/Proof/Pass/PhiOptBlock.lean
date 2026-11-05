import GoFV.Proof.Pass.PhiOptLocal
import GoFV.Proof.Pass.ZCSEBlock

/-!
# phiopt: the target's evaluation of a block

`targetRun`: after the source's `Phi`s and a prefix `pre` of its schedule (frame `Gp`), the
target has its `Phi`s and a schedule, agrees with `Gp`'s reference frame `H` outside its
schedule, and each target value whose source counterpart (if any) is in `pre` evaluates to its
register in `H` (`LocalOK`). `enter_ok`: a block the source enters to `G` the target enters to a
frame related to `G` (`TR`).
-/

namespace GoFV.Proof.PhiOpt

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.PhiOpt Dom
open GoFV.Proof.CopyElim (Tree refOK_prefix frame_ext stepV_of topoRem_append_left)
open GoFV.Proof.ZCSE (frame_with)

variable {tabs : Tables} {f g : Func}

theorem frame_trans {a b c : Frame} (h1 : a = { b with regs := a.regs })
    (h2 : b = { c with regs := b.regs }) : a = { c with regs := a.regs } := by
  cases a; cases b; cases c; simp_all

/-- **The target's evaluation of a block, against a source prefix.** -/
theorem targetRun (S : Setup tabs f g) {env : Env} {fr frT : Frame} {bid : ID} {i : Nat}
    (hA : At env tabs f fr bid i) (hT : TR f g fr frT) {fb : Block}
    (hfb : f.block? bid = some fb) {psS : List (ID × Val)}
    (hpsS : fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) fr i) = .ok psS)
    {oS : Array ID} (hsched : schedule f fb = some oS) {pre post : List ID}
    (hsplit : oS.toList = pre ++ post) {Gp : Frame}
    (hpre : evalAll env (Ctx.make tabs f) { fr with regs := setPhis psS fr.regs } pre = .ok Gp) :
    ∃ gb psT oT H, g.block? bid = some gb ∧ gb.id = bid ∧
      gb.values.toList.filterMapM (phiStep (Ctx.make tabs g) frT i) = .ok psT ∧
      schedule g gb = some oT ∧ H = { Gp with regs := H.regs } ∧
      H.regs.size = g.valueTab.size ∧ (∀ x, Listed f x → H.regs[x]? = Gp.regs[x]?) ∧
      (∀ a, a ∉ oT.toList → Listed f a → (setPhis psT frT.regs)[a]? = H.regs[a]?) ∧
      ({ frT with regs := setPhis psT frT.regs } : Frame) =
        { H with regs := setPhis psT frT.regs } ∧
      (setPhis psT frT.regs).size = H.regs.size ∧
      (∀ x ∈ oT.toList, ∀ a ∈ argsF g x, a ∉ oT.toList → Listed f a) ∧
      (∀ L : List ID, (∀ x ∈ L, x ∈ oT.toList) →
        (∀ x ∈ L, NodeIn (schedNodes f fb).toList x → x ∈ pre) →
        LocalOK env (Ctx.make tabs g) H L) ∧
      (∀ x fv gv, x ∈ fb.values → f.value? x = some fv → g.value? x = some gv →
        (gv.op = fv.op ∧ gv.aux = fv.aux ∧ gv.auxInt = fv.auxInt ∧ gv.args = fv.args) →
        (∀ msg, evalValue env (Ctx.make tabs f) Gp fv ≠ .stuck msg) →
        ∀ g' : Frame, g' = { H with regs := g'.regs } →
          (∀ a ∈ gv.args, g'.regs[a]? = H.regs[a]?) →
          evalValue env (Ctx.make tabs g) g' gv = evalValue env (Ctx.make tabs f) Gp fv) := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  have hbt := hA.tree S
  have hndF := hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩
  have hownF := valuesOwn hwf hbt.1 hfb
  obtain ⟨gb, hgbb, hgid, -, -, -, -, hfg, hgf⟩ := S.block hbt.1 hfb
  obtain ⟨fb', hfb', hfid⟩ := hwf.blockId bid hbt.1
  rw [hfb] at hfb'; cases hfb'
  have hbg : bid ∈ g.blocks := by rw [S.blocks]; exact hbt.1
  have hndG := hwg.valuesNodup _ _ ⟨hbg, hgbb⟩
  have hownG := valuesOwn hwg hbg hgbb
  obtain ⟨psT, hpsT, hszT, -, hPT⟩ := targetPhis S hA hT hfb hgbb hpsS
  obtain ⟨oT, hoT⟩ := targetSched S hbt.1 hfb hgbb hsched
  obtain ⟨-, -, omemT⟩ := schedule_topo hownG hndG hoT
  obtain ⟨ond, otopo, omem⟩ := schedule_topo hownF hndF hsched
  obtain ⟨hszS, -, hkeepS, hphiS⟩ := phis_spec hndF hpsS
  have ond' := ond
  have otopo' := otopo
  rw [hsplit] at ond' otopo'
  obtain ⟨p1, p2, p3, p4⟩ := evalAll_spec (List.nodup_append.1 ond').1
    (by exact topoRem_append_left otopo') (by simp [hszS, hA.size]; rfl) hpre
  have hpreS : ∀ x ∈ pre, x ∈ oS.toList := fun x hx => by rw [hsplit]; exact List.mem_append_left _ hx
  have hGsz : Gp.regs.size = f.valueTab.size := by rw [p2]; simp [hszS, hA.size]
  have hout : ∀ z, z ∉ fb.values → Gp.regs[z]? = fr.regs[z]? := fun z hz => by
    rw [p3 z (fun hm => hz ((omem z).1 (hpreS z hm)).1)]
    exact hkeepS z (.inl hz)
  obtain ⟨H, hH, hHsz, hHG, hnew⟩ := newFrame S hA hfb hgbb hGsz hout
  have hGfr : Gp = { fr with regs := Gp.regs } := by rw [p1]
  -- target nodes
  have hxT : ∀ x, x ∈ oT.toList ↔ x ∈ gb.values ∧ ∃ v, g.value? x = some v ∧ v.op ≠ .Phi :=
    omemT
  refine ⟨gb, psT, oT, H, hgbb, hgid.trans hfid, hpsT, hoT, hH, hHsz, hHG, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · -- agreement outside the target's schedule
    intro a ha hal
    have hnrw : ¬ RwIn f g fb a := fun ⟨haf, hrw⟩ => by
      obtain ⟨-, gv, hgv, hgn⟩ := isRw_iff.1 hrw
      exact ha ((hxT a).2 ⟨hfg a haf, gv, hgv, hgn⟩)
    rw [hPT a hal hnrw, hHG a hal]
    refine (p3 a fun hm => ha ?_).symm
    obtain ⟨haf, fv, hfv, hfn⟩ := (omem a).1 (hpreS a hm)
    obtain ⟨hN, -⟩ := fnode S hbt.1 hfb hgbb ((nodeIn_schedNodes hownF).2 ⟨haf, fv, hfv, hfn⟩)
    exact (hxT a).2 ((nodeIn_schedNodes hownG).1 hN)
  · obtain ⟨hTfr, -⟩ := hT
    apply frame_with
    · rw [hTfr, hH, hGfr]
    · rw [hTfr, hH, hGfr]
    · rw [hTfr, hH, hGfr]
    · rw [hTfr, hH, hGfr]
  · rw [hszT, hHsz]
  · -- arguments outside the target's schedule are listed in `f`
    intro x hx a ha haT
    obtain ⟨hxb, gv, hgv, hgn⟩ := (hxT x).1 hx
    rw [argsF_of hgv] at ha
    have ha' : a ∈ gv.args := Array.mem_toList_iff.1 ha
    obtain ⟨gv', hgv', -, hk⟩ := gval S hbt.1 hfb hgbb hxb
    rw [hgv] at hgv'; cases hgv'
    -- an available value is listed; a new value of the block is scheduled
    have hav : avail f bid a = true → Listed f a := fun hz => by
      obtain ⟨v, blk, -, hvb, hblk, hzb, -⟩ := avail_spec hz
      exact ⟨v.block, blk, ⟨hvb, hblk⟩, hzb⟩
    have hnewT : isNew f g bid a = true → False := fun hz => by
      obtain ⟨hn, blk, hblk, hzb⟩ := isNew_spec hz
      rw [hgbb] at hblk; cases hblk
      obtain ⟨w, hw, -, hk'⟩ := gval S hbt.1 hfb hgbb hzb
      rcases hk' with ⟨fw, hfw, -⟩ | ⟨-, -, hok⟩
      · rw [hn] at hfw; cases hfw
      · exact haT ((hxT a).2 ⟨hzb, w, hw, newOK_not_phi hok hw⟩)
    rcases hk with ⟨fv, hfv, hxf, -, -, ⟨-, -, -, hargs⟩ | hr⟩ | ⟨-, -, hok⟩
    · rw [hargs] at ha'
      exact hwf.argListed bid fb x fv ⟨⟨hbt.1, hfb⟩, hxf, hfv⟩ a ha'
    · obtain ⟨-, -, -, -, hform⟩ := rewriteOK_spec hr
      obtain ⟨fv', hfv', -, hfblk⟩ := hwf.valueId bid fb ⟨hbt.1, hfb⟩ x hxf
      rw [hfv] at hfv'; cases hfv'
      rw [hfblk] at hform
      rcases hform with ⟨-, c, -, hcav, hall⟩ | ⟨w, c, neg, hshape, -⟩
      · have h0 : fv.args[0]? = some fv.args[0]! := by
          obtain ⟨-, -, hsz2, -⟩ := rewriteOK_spec hr
          rw [getElem!_pos fv.args 0 (by omega)]; simp [hsz2]
        obtain ⟨d, -, harm⟩ := hall 0 _ h0
        rcases harm with ⟨-, hargs, -⟩ | ⟨-, hargs, -⟩ | ⟨n, -, hargs, hn, -⟩ |
          ⟨n, -, hargs, hn, -⟩ <;> rw [hargs] at ha' <;>
          simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ha'
        · subst ha'; exact hav hcav
        · subst ha'; exact hav hcav
        · rcases ha' with rfl | rfl
          · exact hav hcav
          · exact hav hn
        · rcases ha' with rfl | rfl
          · exact hav hcav
          · exact hav hn
      · obtain ⟨-, -, -, cv, -, -, hargs, hcvn, -⟩ := hshape
        rw [hargs] at ha'
        simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ha'
        subst ha'
        exact (hnewT hcvn).elim
    · obtain ⟨nv, a', hnv, -, hargs, hk⟩ := newOK_spec hok
      rw [hgv] at hnv; cases hnv
      rw [hargs] at ha'
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ha'
      subst ha'
      rcases hk with ⟨-, hz⟩ | ⟨-, hz | ⟨hz, -⟩⟩
      · exact hav hz
      · exact hav hz
      · exact (hnewT hz).elim
  · -- each target value evaluates to its register in `H`
    intro L hLT hLpre x hxL
    have hx := hLT x hxL
    obtain ⟨hxb, gv, hgv, hgn⟩ := (hxT x).1 hx
    have hargsT : argsF (Ctx.make tabs g).f x = gv.args.toList := argsF_of (f := g) hgv
    obtain ⟨gv', hgv', -, hk⟩ := gval S hbt.1 hfb hgbb hxb
    rw [hgv] at hgv'; cases hgv'
    rcases hk with ⟨fv, hfv, hxf, -, -, hsame | hr⟩ | ⟨hn, -, hok⟩
    · have hfn : fv.op ≠ .Phi := by rw [← hsame.1]; exact hgn
      have hxpre : x ∈ pre := hLpre x hxL ((nodeIn_schedNodes hownF).2 ⟨hxf, fv, hfv, hfn⟩)
      obtain ⟨v', y, hv', hy, hev⟩ := p4 x hxpre
      change f.value? x = some v' at hv'
      rw [hfv] at hv'; cases hv'
      refine ⟨y, by rw [hHG x ⟨bid, fb, ⟨hbt.1, hfb⟩, hxf⟩]; exact hy, fun g' hg' hag => ?_⟩
      rw [stepV_of (ctx := Ctx.make tabs g) hgv, ← hev]
      exact evalSame S ⟨hbt.1, hfb⟩ hHG hxf hfv hgv hsame
        (fun msg he => by rw [hev] at he; cases he) (frame_trans hg' hH)
        (fun a ha => hag a (by rw [hargsT]; exact Array.mem_toList_iff.2 ha))
    · have hfph := (rewriteOK_spec hr).1
      have hlt : x < fr.regs.size := by rw [hA.size]; exact lt_of_value? hfv
      obtain ⟨a, y, ha, hy, hP⟩ := hphiS x hxf fv hfv hfph hlt
      have hxpre : x ∉ pre := fun hm => by
        obtain ⟨-, fv', hfv', hfn⟩ := (omem x).1 (hpreS x hm)
        rw [hfv] at hfv'; cases hfv'; exact hfn hfph
      refine ⟨y.retype ((Ctx.make tabs f).tys[x]?.getD .other), ?_, fun g' hg' hag => ?_⟩
      · rw [hHG x ⟨bid, fb, ⟨hbt.1, hfb⟩, hxf⟩, p3 x hxpre]; exact hP
      · rw [stepV_of (ctx := Ctx.make tabs g) hgv]
        exact rwLocal S hA hfb hout hHG hnew hxf hfv hgv hr ha hy
          (fun a ha => hag a (by rw [hargsT]; exact Array.mem_toList_iff.2 ha))
    · have hxn : isNew f g bid x = true := by
        unfold isNew
        simp only [hn, Option.isNone_none, Bool.true_and]
        exact listedIn_iff.2 ⟨gb, hgbb, hxb⟩
      obtain ⟨y, hy, hev⟩ := hnew x hxn gv hgv
      refine ⟨y, hy, fun g' hg' hag => ?_⟩
      rw [stepV_of (ctx := Ctx.make tabs g) hgv, ← hev]
      exact (evalValue_congr hg' fun a ha =>
        (hag a (by rw [hargsT]; exact Array.mem_toList_iff.2 ha)).symm).symm
  · intro x fv gv hx hfv hgv hsame hdef g' hg' hag
    exact evalSame S ⟨hbt.1, hfb⟩ hHG hx hfv hgv hsame hdef (frame_trans hg' hH) hag

theorem RefOK.mono {D : ID → List ID} :
    ∀ {L : List ID} {S S' : ID → Prop}, (∀ a, S a → S' a) → RefOK D S L → RefOK D S' L
  | [], _, _, _, _ => trivial
  | _ :: _, _, _, h, ⟨h1, h2⟩ =>
    ⟨fun a ha => h a (h1 a ha), RefOK.mono (fun a ha => ha.imp (h a) id) h2⟩

theorem RefOK.prefix {D : ID → List ID} :
    ∀ {L1 L2 : List ID} {S : ID → Prop}, RefOK D S (L1 ++ L2) → RefOK D S L1
  | [], _, _, _ => trivial
  | _ :: L1, _, _, ⟨h1, h2⟩ => ⟨h1, RefOK.prefix (L1 := L1) h2⟩

/-- A dependency order's arguments are listed before or satisfy `Q`. -/
theorem refOK_of_topo {D : ID → List ID} {Q : ID → Prop} :
    ∀ {pre L : List ID}, TopoRem D L → (∀ x ∈ L, ∀ a ∈ D x, a ∉ pre ++ L → Q a) →
      RefOK D (fun a => (a ∉ pre ++ L ∧ Q a) ∨ a ∈ pre) L
  | _, [], _, _ => trivial
  | pre, x :: s, ⟨h1, h2⟩, h => by
    refine ⟨fun a ha => ?_, ?_⟩
    · by_cases hp : a ∈ pre
      · exact .inr hp
      · have hn : a ∉ pre ++ x :: s := fun hm => by
          rcases List.mem_append.1 hm with h' | h'
          · exact hp h'
          · exact h1 a ha h'
        exact .inl ⟨hn, h x List.mem_cons_self a ha hn⟩
    · have ih := refOK_of_topo (pre := pre ++ [x]) h2 fun y hy a ha hn =>
        h y (List.mem_cons_of_mem _ hy) a ha (by simpa using hn)
      refine RefOK.mono (fun a ha => ?_) ih
      rcases ha with ⟨hn, hq⟩ | hm
      · exact .inl (.inl ⟨by simpa using hn, hq⟩)
      · rcases List.mem_append.1 hm with h' | h'
        · exact .inl (.inr h')
        · exact .inr (by simpa using h')

/-- **A block the source enters successfully is entered by the target, to a related frame.** -/
theorem enter_ok (S : Setup tabs f g) {env : Env} {fr frT : Frame} {bid : ID} {i : Nat}
    (hA : At env tabs f fr bid i) (hT : TR f g fr frT) {fb : Block}
    (hfb : f.block? bid = some fb) {G : Frame}
    (h : enterBlock env (Ctx.make tabs f) fr fb i = .ok G) :
    ∃ gb GT, g.block? bid = some gb ∧
      enterBlock env (Ctx.make tabs g) frT gb i = .ok GT ∧ TR f g G GT := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  have hbt := hA.tree S
  have hndF := hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩
  have hownF := valuesOwn hwf hbt.1 hfb
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
  obtain ⟨gb, psT, oT, H, hgbb, hgid, hpsT, hoT, hH, hHsz, hHG, hagree, hframe, hsz, hrefS,
    hloc, -⟩ := targetRun S hA hT hfb hpsS hsched (pre := oS.toList) (post := [])
      (by simp) h
  have hbg : bid ∈ g.blocks := by rw [S.blocks]; exact hbt.1
  have hndG := hwg.valuesNodup _ _ ⟨hbg, hgbb⟩
  obtain ⟨-, otopoT, -⟩ := schedule_topo (valuesOwn hwg hbg hgbb) hndG hoT
  obtain ⟨-, -, omem⟩ := schedule_topo hownF hndF hsched
  have hL := hloc oT.toList (fun _ hx => hx) fun x _ hN =>
    (omem x).2 ((nodeIn_schedNodes hownF).1 hN)
  have href := refOK_of_topo (Q := fun a => Listed f a) (pre := []) otopoT
    fun x hx a ha hn => hrefS x hx a ha (by simpa using hn)
  obtain ⟨g'', h1, h2, h3, h4, -⟩ := evalAll_ref (g := { frT with regs := setPhis psT frT.regs })
    hL href (fun a ha => by
      rcases ha with ⟨hn, hl⟩ | hm
      · exact hagree a (by simpa using hn) hl
      · cases hm) hframe hsz
  refine ⟨gb, g'', hgbb, ?_, ?_, ?_, ?_⟩
  · rw [enterBlock_eq, hpsT]
    change (Res.ofOption _ ((Ctx.make tabs g).sched[gb.id]?).join).bind _ = _
    rw [hgid, sched_of_block hgbb, hoT]
    exact h1
  · rw [h2, hH]
  · rw [h3, hHsz]
  · intro x hx
    rw [← hHG x hx]
    by_cases hxT : x ∈ oT.toList
    · exact h4 x (.inr hxT)
    · exact h4 x (.inl (.inl ⟨by simpa using hxT, hx⟩))

end GoFV.Proof.PhiOpt

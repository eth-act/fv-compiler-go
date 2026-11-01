import GoFV.Proof.Pass.CopyElimSched

/-!
# copyelim: the target's evaluation of a block

`evalSame`: a target value that is a source non-`Phi` evaluates, in any frame agreeing with the
source's frame on its arguments, as the source value does (`copyEq` for its arguments).
`evalFormer`: a `Phi` that became a copy yields the source `Phi`'s register.
-/

namespace GoFV.Proof.CopyElim

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt Dom

variable {tabs : Tables} {f g : Func}

theorem stepV_of {env : Env} {ctx : Ctx} {fr : Frame} {x : ID} {v : Value}
    (h : ctx.f.value? x = some v) : stepV env ctx fr x = evalValue env ctx fr v := by
  unfold stepV; rw [h]

/-- A source non-`Phi` of a tree block and its target evaluate alike. -/
theorem evalSame (S : Setup tabs f g) {env : Env} {fr : Frame} {bid : ID} {i : Nat}
    (hA : At env tabs f g fr bid i) {fb : Block} (hfb : f.block? bid = some fb)
    {frPS H : Frame} {oS : Array ID} {P : List ID} (hM : Mid env tabs f fr bid i fb frPS H oS P)
    {x : ID} (hx : x ∈ fb.values) {fv gv : Value} (hfv : f.value? x = some fv)
    (hgv : g.value? x = some gv) (hnph : fv.op ≠ .Phi)
    (hdep : ∀ a ∈ fv.args, a ∈ fb.values → (∃ v, f.value? a = some v ∧ v.op ≠ .Phi) → a ∈ P)
    (hdef : ∀ msg, evalValue env (Ctx.make tabs f) H fv ≠ .stuck msg)
    {g' : Frame} (hg' : g' = { H with regs := g'.regs })
    (hag : ∀ a ∈ gv.args, g'.regs[a]? = H.regs[a]?) :
    evalValue env (Ctx.make tabs g) g' gv = evalValue env (Ctx.make tabs f) H fv := by
  obtain ⟨ce, hwf⟩ := S.wf
  have hbt := hA.tree S
  obtain ⟨fv', gv', hfv', hgv', -, hfid, -, -, hrel, hz⟩ := S.value hbt hfb hx
  rw [hfv] at hfv'; cases hfv'
  rw [hgv] at hgv'; cases hgv'
  have hgid := S.gid hbt hfb hx hgv
  have hargsdef := evalValue_args_def hdef
  cases hrel with
  | phi _ hph => exact absurd hph hnph
  | empty hzz => exact absurd hzz hz
  | same hop haux hai hsz hargs' =>
    refine evalValue_eq_of_args hop haux hai (hgid.trans hfid.symm) hsz (fun k fa hfa => ?_) hg'
      (by rw [hfid]; exact S.tys hbt hfb hx) rfl S.params
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
        uses S.cf hbt.1 hfb hbt.2 hx hfv hnph hfam
      obtain ⟨y', h1, h2⟩ := copyEq S hA hfb hM hfal hfaU (fun hm => by
        by_cases hph : ∃ v, f.value? fa = some v ∧ v.op = .Phi
        · exact .inl hph
        · obtain ⟨v, -, hv, -⟩ := S.value hbt hfb hm
          exact .inr (hdep fa hfam hm ⟨v, hv, fun hp => hph ⟨v, hv, hp⟩⟩)) hu hop' hargsu
      rw [hy] at h1; cases h1; exact h2

/-- A `Phi` that became a copy yields the source `Phi`'s register. -/
theorem evalFormer (S : Setup tabs f g) {env : Env} {fr : Frame} {bid : ID} {i : Nat}
    (hA : At env tabs f g fr bid i) {fb : Block} (hfb : f.block? bid = some fb)
    {frPS H : Frame} {oS : Array ID} {P : List ID} (hM : Mid env tabs f fr bid i fb frPS H oS P)
    {x : ID} (hx : x ∈ fb.values) {fv gv : Value} (hfv : f.value? x = some fv)
    (hgv : g.value? x = some gv) (hph : fv.op = .Phi) (hgn : gv.op ≠ .Phi) :
    ∃ y, H.regs[x]? = some (some y) ∧ ∀ g' : Frame, g' = { H with regs := g'.regs } →
      (∀ a ∈ gv.args, g'.regs[a]? = H.regs[a]?) →
      evalValue env (Ctx.make tabs g) g' gv = .ok y := by
  obtain ⟨ce, hwf⟩ := S.wf
  have hbt := hA.tree S
  obtain ⟨fv', gv', hfv', hgv', -, hfid, -, -, hrel, hz⟩ := S.value hbt hfb hx
  rw [hfv] at hfv'; cases hfv'
  rw [hgv] at hgv'; cases hgv'
  cases hrel with
  | same hop => exact absurd (hop.trans hph) hgn
  | empty hzz => exact absurd hzz hz
  | phi w _ hcop hw hr =>
    have hl : Listed f x := ⟨bid, fb, ⟨hbt.1, hfb⟩, hx⟩
    have hU : Anc (make f) (blockOf f x) bid := by
      unfold blockOf; rw [hfv]
      obtain ⟨-, -, -, -, hb, -⟩ := S.value hbt hfb hx
      simp only [Option.map_some, Option.getD_some]
      rw [show fv.block = bid from by
        obtain ⟨fv2, -, hfv2, -, hb2, -⟩ := S.value hbt hfb hx
        rw [hfv] at hfv2; cases hfv2; exact hb2]
      exact anc_refl hbt.2
    obtain ⟨y, h1, h2⟩ := copyEq S hA hfb hM hl hU (fun _ => .inl ⟨fv, hfv, hph⟩) hgv hcop hw
    refine ⟨y, h1, fun g' hg' hag => ?_⟩
    have hgw : g'.regs[w]? = some (some y) := by rw [hag w (by rw [hw]; simp), h2]
    rw [evalValue_copy hcop hw hgw, S.gid hbt hfb hx hgv, S.tys hbt hfb hx]
    exact congrArg _ (hM.typed x y h1)

/-- Source `Phi`s of a block entered along an edge sit in a non-entry block. -/
theorem phi_not_entry (S : Setup tabs f g) {env : Env} {fr : Frame} {bid : ID} {i : Nat}
    (hA : At env tabs f g fr bid i) {fb : Block} (hfb : f.block? bid = some fb)
    {psS : List (ID × Val)}
    (hpsS : fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) fr i) = .ok psS) :
    ∀ z ∈ fb.values, ∀ fv, f.value? z = some fv → fv.op = .Phi → bid ≠ f.entry := by
  obtain ⟨ce, hwf⟩ := S.wf
  have hbt := hA.tree S
  intro z hz fv hfv hph
  have hlt : z < fr.regs.size := by rw [hA.size]; exact lt_of_value? hfv
  obtain ⟨-, -, -, hphi⟩ := phis_spec (hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩) hpsS
  obtain ⟨a, y, ha, -, -⟩ := hphi z hz fv hfv hph hlt
  have hsz := hwf.phiArity bid fb z fv ⟨⟨hbt.1, hfb⟩, hz, hfv⟩ hph
  have hilt : i < fb.preds.size := by rw [← hsz]; exact (Array.getElem?_eq_some_iff.1 ha).1
  exact (hA.pred S hfb (e := fb.preds[i]) (by simp [hilt])).1

/-- **The target's `Phi`s and schedule.** The target collects its `Phi`s and has a schedule;
after its `Phi`s, it agrees with the source (after the source's `Phi`s) outside its schedule. -/
theorem targetPre (S : Setup tabs f g) {env : Env} {fr : Frame} {bid : ID} {i : Nat}
    (hA : At env tabs f g fr bid i) {fb : Block} (hfb : f.block? bid = some fb)
    {psS : List (ID × Val)}
    (hpsS : fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) fr i) = .ok psS)
    {oS : Array ID} (hsched : schedule f fb = some oS) :
    ∃ gb psT oT, g.block? bid = some gb ∧ gb.id = bid ∧ gb.values = fb.values ∧
      gb.values.toList.filterMapM (phiStep (Ctx.make tabs g) fr i) = .ok psT ∧
      schedule g gb = some oT ∧
      (∀ z, z ∉ oT.toList → (setPhis psT fr.regs)[z]? = (setPhis psS fr.regs)[z]?) ∧
      (setPhis psT fr.regs).size = fr.regs.size := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  have hbt := hA.tree S
  have hndF := hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩
  obtain ⟨gb, hgbb, hgid, -, -, -, hvals, -⟩ := S.block hbt hfb
  obtain ⟨fb', hfb', hfid⟩ := hwf.blockId bid hbt.1
  rw [hfb] at hfb'; cases hfb'
  have hbg : bid ∈ g.blocks := by rw [S.blocks]; exact hbt.1
  have hndG := hwg.valuesNodup _ _ ⟨hbg, hgbb⟩
  have hpe := phi_not_entry S hA hfb hpsS
  obtain ⟨-, -, hkeepS, hphiS⟩ := phis_spec hndF hpsS
  -- a `Phi` of both: equal incoming registers
  have hphiEq : ∀ z ∈ fb.values, ∀ fv gv, f.value? z = some fv → g.value? z = some gv →
      fv.op = .Phi → gv.op = .Phi → z < fr.regs.size →
      ∃ a y, fv.args[i]? = some a ∧ fr.regs[a]? = some (some y) ∧
        ∃ ga, gv.args[i]? = some ga ∧ fr.regs[ga]? = some (some y) := by
    intro z hz fv gv hfv hgv hph hgph hlt
    obtain ⟨a, y, ha, hy, -⟩ := hphiS z hz fv hfv hph hlt
    obtain ⟨fv', gv', hfv', hgv', -, -, -, -, hrel, hzz⟩ := S.value hbt hfb hz
    rw [hfv] at hfv'; cases hfv'
    rw [hgv] at hgv'; cases hgv'
    cases hrel with
    | phi _ _ hcop => rw [hcop] at hgph; cases hgph
    | empty hzz' => exact absurd hzz' hzz
    | same _ _ _ hsz hargs' =>
      obtain ⟨ga, hga, hr⟩ := hargs' i a ha
      have hsz' := hwf.phiArity bid fb z fv ⟨⟨hbt.1, hfb⟩, hz, hfv⟩ hph
      have hilt : i < fb.preds.size := by rw [← hsz']; exact (Array.getElem?_eq_some_iff.1 ha).1
      have he : fb.preds[i]? = some fb.preds[i] := by simp [hilt]
      obtain ⟨-, hpt, -, hDT⟩ := hA.pred S hfb he
      have hpu := phiUse S.cf hbt.1 hfb hbt.2 hz hfv hph ha he hpt
      have hla : Listed f a :=
        hwf.argListed _ _ _ _ ⟨⟨hbt.1, hfb⟩, hz, hfv⟩ a (Array.mem_of_getElem? ha)
      obtain ⟨y', h1, h2⟩ := S.argEq hDT (A := fun z => Anc (make f) z fb.preds[i].b) hpu
        hA.tyT hla hpu hr
      rw [hy] at h1; cases h1
      exact ⟨a, y, ha, hy, ga, hga, h2⟩
  -- the target collects its `Phi`s
  obtain ⟨psT, hpsT⟩ : ∃ psT, gb.values.toList.filterMapM (phiStep (Ctx.make tabs g) fr i) =
      .ok psT := by
    refine filterMapM_phi_ok fun z hz => ?_
    rw [hvals, Array.mem_toList_iff] at hz
    obtain ⟨fv, gv, hfv, hgv, -, -, -, -, hrel, hzz⟩ := S.value hbt hfb hz
    by_cases hgph : gv.op = .Phi
    · have hph := valRel_phi hrel hzz hgph
      have hlt : z < fr.regs.size := by rw [hA.size]; exact lt_of_value? hfv
      obtain ⟨a, y, -, -, ga, hga, hy⟩ := hphiEq z hz fv gv hfv hgv hph hgph hlt
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
  obtain ⟨oT, hoT⟩ := targetSched S hbt hfb hpe hsched hgbb hvals
  obtain ⟨-, -, omemT⟩ := schedule_topo (valuesOwn hwg hbg hgbb) hndG hoT
  obtain ⟨hszT, -, hkeepT, hphiT⟩ := phis_spec hndG hpsT
  refine ⟨gb, psT, oT, hgbb, hgid.trans hfid, hvals, hpsT, hoT, fun z hz => ?_, hszT⟩
  by_cases hzb : z ∈ fb.values
  · obtain ⟨fv, gv, hfv, hgv, -, -, -, -, hrel, hzz⟩ := S.value hbt hfb hzb
    have hgph : gv.op = .Phi := Classical.byContradiction fun hne =>
      hz ((omemT z).2 ⟨by rw [hvals]; exact hzb, gv, hgv, hne⟩)
    have hph := valRel_phi hrel hzz hgph
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

theorem refOK_prefix {D : ID → List ID} :
    ∀ {L1 L2 : List ID} {S : ID → Prop}, TopoRem D (L1 ++ L2) → (∀ a, a ∉ L1 ++ L2 → S a) →
      RefOK D S L1
  | [], _, _, _, _ => trivial
  | x :: L1, L2, S, ⟨h1, h2⟩, hS =>
    ⟨fun a ha => hS a (h1 a ha), refOK_prefix h2 fun a ha => by
      by_cases hax : a = x
      · exact .inr hax
      · exact .inl (hS a (fun hm => by
          rcases List.mem_cons.1 hm with h | h
          · exact hax h
          · exact ha h))⟩

theorem frame_ext {g G : Frame} (hg : g = { G with regs := g.regs })
    (h : ∀ a : ID, g.regs[a]? = G.regs[a]?) : g = G := by
  have : g.regs = G.regs := Array.ext_getElem? h
  rw [hg, this]

/-- Prefix of a dependency order. -/
theorem topoRem_append_left {D : ID → List ID} :
    ∀ {L1 L2 : List ID}, TopoRem D (L1 ++ L2) → TopoRem D L1
  | [], _, _ => trivial
  | x :: L1, L2, ⟨h1, h2⟩ =>
    ⟨fun a ha hm => h1 a ha (by
      rcases List.mem_cons.1 hm with h | h
      · exact h ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ h)), topoRem_append_left h2⟩

/-- The source state after evaluating a prefix `P` of the block's schedule. -/
theorem mid_of (S : Setup tabs f g) {env : Env} {fr : Frame} {bid : ID} {i : Nat}
    (hA : At env tabs f g fr bid i) {fb : Block} (hfb : f.block? bid = some fb)
    {psS : List (ID × Val)}
    (hpsS : fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) fr i) = .ok psS)
    {oS : Array ID} (hsched : schedule f fb = some oS) {P R : List ID}
    (hsplit : oS.toList = P ++ R) {H : Frame}
    (hev : evalAll env (Ctx.make tabs f) { fr with regs := setPhis psS fr.regs } P = .ok H) :
    Mid env tabs f fr bid i fb { fr with regs := setPhis psS fr.regs } H oS P ∧
      H = { fr with regs := H.regs } ∧ H.regs.size = fr.regs.size := by
  obtain ⟨ce, hwf⟩ := S.wf
  have hbt := hA.tree S
  have hndF := hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩
  have hown := valuesOwn hwf hbt.1 hfb
  obtain ⟨ond, otopo, omem⟩ := schedule_topo hown hndF hsched
  rw [hsplit] at ond otopo
  obtain ⟨hszP, hall, hkeep, hphi⟩ := phis_spec hndF hpsS
  obtain ⟨e1, e2, e3, e4⟩ := evalAll_spec (List.nodup_append.1 ond).1
    (topoRem_append_left otopo) (by simp [hszP, hA.size]; rfl) hev
  refine ⟨⟨hkeep, hphi, hsched, ⟨R, hsplit⟩, e3, e4, ?_⟩, by rw [e1], by rw [e2]; simpa using hszP⟩
  refine typed_evalAll (typed_phis hA.tyS (by simpa using hszP) hkeep hphi hall)
    (fun x hx v hv => ?_) e3 e4
  have hxo : x ∈ oS.toList := by rw [hsplit]; exact List.mem_append_left _ hx
  obtain ⟨v', hv', hvid⟩ := hown x ((omem x).1 hxo).1
  change f.value? x = some v at hv
  rw [hv] at hv'; cases hv'; exact hvid

/-- **A block the source enters successfully is entered by the target to the same frame.** -/
theorem enter_ok (S : Setup tabs f g) {env : Env} {fr : Frame} {bid : ID} {i : Nat}
    (hA : At env tabs f g fr bid i) {fb : Block} (hfb : f.block? bid = some fb) {G : Frame}
    (h : enterBlock env (Ctx.make tabs f) fr fb i = .ok G) :
    ∃ gb, g.block? bid = some gb ∧ enterBlock env (Ctx.make tabs g) fr gb i = .ok G := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  have hbt := hA.tree S
  obtain ⟨fb', hfb', hfid⟩ := hwf.blockId bid hbt.1
  rw [hfb] at hfb'; cases hfb'
  rw [enterBlock_eq] at h
  cases hpsS : fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) fr i) with
  | panic e m => rw [hpsS] at h; cases h
  | stuck msg => rw [hpsS] at h; cases h
  | ok psS =>
  rw [hpsS] at h
  change (Res.ofOption _ ((Ctx.make tabs f).sched[fb.id]?).join).bind _ = _ at h
  rw [hfid, sched_make hfb] at h
  cases hsched : schedule f fb with
  | none => rw [hsched] at h; cases h
  | some oS =>
  rw [hsched] at h
  change evalAll env (Ctx.make tabs f) _ oS.toList = .ok G at h
  obtain ⟨gb, psT, oT, hgbb, hgid, hvals, hpsT, hoT, hagree, hszT⟩ :=
    targetPre S hA hfb hpsS hsched
  obtain ⟨hM, hG1, hG2⟩ := mid_of S hA hfb hpsS hsched (R := []) (by simp) h
  have hbg : bid ∈ g.blocks := by rw [S.blocks]; exact hbt.1
  have hndG := hwg.valuesNodup _ _ ⟨hbg, hgbb⟩
  obtain ⟨ondT, otopoT, omemT⟩ := schedule_topo (valuesOwn hwg hbg hgbb) hndG hoT
  obtain ⟨-, -, omem⟩ := schedule_topo (valuesOwn hwf hbt.1 hfb)
    (hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩) hsched
  -- the target's evaluation against the source's final frame
  have hloc : LocalOK env (Ctx.make tabs g) G oT.toList := by
    intro x hx
    obtain ⟨hxb, gv, hgv, hgn⟩ := (omemT x).1 hx
    rw [hvals] at hxb
    obtain ⟨fv, -, hfv, -⟩ := S.value hbt hfb hxb
    have hargsT : argsF (Ctx.make tabs g).f x = gv.args.toList := argsF_of (f := g) hgv
    by_cases hph : fv.op = .Phi
    · obtain ⟨y, h1, h2⟩ := evalFormer S hA hfb hM hxb hfv hgv hph hgn
      exact ⟨y, h1, fun g' hg' hag => by
        rw [stepV_of (ctx := Ctx.make tabs g) hgv]
        exact h2 g' hg' fun a ha => hag a (by rw [hargsT]; exact Array.mem_toList_iff.2 ha)⟩
    · have hxS : x ∈ oS.toList := (omem x).2 ⟨hxb, fv, hfv, hph⟩
      obtain ⟨v', y, hv', hy, hev⟩ := hM.eval x (by simpa using hxS)
      rw [hfv] at hv'; cases hv'
      refine ⟨y, hy, fun g' hg' hag => ?_⟩
      rw [stepV_of (ctx := Ctx.make tabs g) hgv, ← hev]
      exact evalSame S hA hfb hM hxb hfv hgv hph
        (fun a _ hab han => by simpa using (omem a).2 ⟨hab, han⟩)
        (fun msg he => by rw [hev] at he; cases he) hg'
        (fun a ha => hag a (by rw [hargsT]; exact Array.mem_toList_iff.2 ha))
  have hS : ∀ a, a ∉ oT.toList → (setPhis psT fr.regs)[a]? = G.regs[a]? := by
    intro a ha
    rw [hagree a ha, hM.out a (fun hm => ha (by
      have ham : a ∈ oS.toList := by simpa using hm
      obtain ⟨hab, fv, hfv, hne⟩ := (omem a).1 ham
      obtain ⟨fv', gv, hfv', hgv, -, -, -, -, hrel, hz⟩ := S.value hbt hfb hab
      rw [hfv] at hfv'; cases hfv'
      exact (omemT a).2 ⟨by rw [hvals]; exact hab, gv, hgv,
        fun hp => hne (valRel_phi hrel hz hp)⟩))]
  obtain ⟨g'', h1, h2, -, h4, -⟩ := evalAll_ref (S := fun a => a ∉ oT.toList)
    (g := { fr with regs := setPhis psT fr.regs }) hloc
    (refOK_prefix (L2 := []) (by rw [List.append_nil]; exact otopoT)
      (fun a ha => by simpa using ha))
    hS (by rw [hG1]) (by rw [hG2]; exact hszT)
  have hgG : g'' = G := frame_ext h2 fun a => h4 a (by
    by_cases ha : a ∈ oT.toList
    · exact .inr ha
    · exact .inl ha)
  refine ⟨gb, hgbb, ?_⟩
  rw [enterBlock_eq, hpsT]
  change (Res.ofOption _ ((Ctx.make tabs g).sched[gb.id]?).join).bind _ = _
  rw [hgid, sched_make hgbb, hoT]
  change evalAll env (Ctx.make tabs g) _ oT.toList = _
  rw [h1, hgG]

end GoFV.Proof.CopyElim

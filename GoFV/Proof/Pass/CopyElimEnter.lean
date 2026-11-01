import GoFV.Proof.Pass.CopyElimRank

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
      (by rw [hfid]; exact S.tys hbt hfb hx) rfl S.params rfl
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
  rw [hfid, sched_of_block hfb] at h
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
  rw [hgid, sched_of_block hgbb, hoT]
  change evalAll env (Ctx.make tabs g) _ oT.toList = _
  rw [h1, hgG]

/-- In a dependency order, the arguments of a listed value are not at or after it. -/
theorem topoRem_at {D : ID → List ID} :
    ∀ {L1 L2 : List ID} {x : ID}, TopoRem D (L1 ++ x :: L2) → ∀ a ∈ D x, a ∉ x :: L2
  | [], _, _, ⟨h1, _⟩ => h1
  | _ :: L1, _, _, ⟨_, h2⟩ => topoRem_at (L1 := L1) h2

/-- Target dependencies on a source root are kept: a chain of source arguments from the root
becomes a chain of target arguments (through the copies' sources). -/
theorem depPres (S : Setup tabs f g) {bid : ID} (hbt : Tree f bid) {fb : Block}
    (hfb : f.block? bid = some fb) {gb : Block} (hgbb : g.block? bid = some gb)
    (hvals : gb.values = fb.values) {r : ID}
    (hrS : NodeIn (schedNodes f fb).toList r)
    (hrnc : ∀ gr, g.value? r = some gr → gr.op ≠ .Copy) :
    ∀ y, Order.Dep (NodeIn (schedNodes f fb).toList) (argsOf (schedNodes f fb).toList) r y →
      Order.Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList) r y := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  have hbg : bid ∈ g.blocks := by rw [S.blocks]; exact hbt.1
  have hownF := valuesOwn hwf hbt.1 hfb
  have hndF := hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩
  have hownG := valuesOwn hwg hbg hgbb
  have hndG := hwg.valuesNodup _ _ ⟨hbg, hgbb⟩
  let DT := Order.Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList)
  -- target nodes: the source nodes stay nodes
  have hnodeT : ∀ y, NodeIn (schedNodes f fb).toList y → NodeIn (schedNodes g gb).toList y := by
    intro y hy
    obtain ⟨hyb, fv, hfv, hne⟩ := (nodeIn_schedNodes hownF).1 hy
    obtain ⟨fv', gv, hfv', hgv, -, -, -, -, hrel, hz⟩ := S.value hbt hfb hyb
    rw [hfv] at hfv'; cases hfv'
    exact (nodeIn_schedNodes hownG).2 ⟨by rw [hvals]; exact hyb, gv, hgv,
      fun hp => hne (valRel_phi hrel hz hp)⟩
  let Q : ID → Prop := fun y => DT r y ∧
    ∀ gy w, g.value? y = some gy → gy.op = .Copy → gy.args = #[w] → w = r ∨ DT r w
  -- an argument related to a value `x` reached from `r`
  have hR : ∀ x w, (x = r ∨ Q x) → ArgRel g x w → w = r ∨ DT r w := by
    intro x w hx hr
    rcases hr with rfl | ⟨u, hu, hop, hargs⟩
    · rcases hx with rfl | hQ
      · exact .inl rfl
      · exact .inr hQ.1
    · rcases hx with rfl | hQ
      · exact absurd hop (hrnc u hu)
      · exact hQ.2 u w hu hop hargs
  have key : ∀ x y, Order.Dep (NodeIn (schedNodes f fb).toList) (argsOf (schedNodes f fb).toList)
      x y → (x = r ∨ Q x) → Q y := by
    intro x y hd
    induction hd with
    | @arg x y hx hy hxy =>
      intro hxQ
      obtain ⟨hyb, fv, hfv, hne⟩ := (nodeIn_schedNodes hownF).1 hy
      rw [argsOf_schedNodes hownF hndF hyb hfv hne] at hxy
      obtain ⟨fv', gv, hfv', hgv, -, -, -, -, hrel, hz⟩ := S.value hbt hfb hyb
      rw [hfv] at hfv'; cases hfv'
      have hgn : gv.op ≠ .Phi := fun hp => hne (valRel_phi hrel hz hp)
      have hyT := hnodeT y hy
      have hargsT : argsOf (schedNodes g gb).toList y = gv.args.toList :=
        argsOf_schedNodes hownG hndG (by rw [hvals]; exact hyb) hgv hgn
      have hrT := hnodeT r hrS
      -- the target edge into `y`
      have hedge : ∀ w, w ∈ gv.args → (w = r ∨ DT r w) → DT r y := by
        intro w hw hwr
        rcases hwr with rfl | hd
        · exact .arg hrT hyT (by rw [hargsT]; exact Array.mem_toList_iff.2 hw)
        · exact .trans hd (.arg hd.right hyT (by rw [hargsT]; exact Array.mem_toList_iff.2 hw))
      cases hrel with
      | phi _ hph => exact absurd hph hne
      | empty hzz => exact absurd hzz hz
      | same hop haux hai hsz hargs' =>
        obtain ⟨k, hk⟩ := List.getElem?_of_mem hxy
        have hk' : fv.args[k]? = some x := by simpa using hk
        obtain ⟨w, hw, hr⟩ := hargs' k x hk'
        refine ⟨hedge w (Array.mem_of_getElem? hw) (hR x w hxQ hr), fun gy w' hgy hop' hargs'' => ?_⟩
        rw [hgv] at hgy; cases hgy
        rw [hargs''] at hw
        have : k = 0 ∧ w = w' := by
          have := (Array.getElem?_eq_some_iff.1 hw)
          obtain ⟨hlt, heq⟩ := this
          simp at hlt; subst hlt; simpa using heq.symm
        obtain ⟨rfl, rfl⟩ := this
        exact hR x w hxQ hr
    | trans _ _ ih1 ih2 => exact fun h => ih2 (.inr (ih1 h))
  intro y hd
  exact (key r y hd (.inl rfl)).1

/-- **A block the source panics in makes the target panic alike.** -/
theorem enter_panic (S : Setup tabs f g) {env : Env} {fr : Frame} {bid : ID} {i : Nat}
    (hA : At env tabs f g fr bid i) {fb : Block} (hfb : f.block? bid = some fb) {e : Panic}
    {m : Mem} (h : enterBlock env (Ctx.make tabs f) fr fb i = .panic e m) :
    ∃ gb, g.block? bid = some gb ∧ enterBlock env (Ctx.make tabs g) fr gb i = .panic e m := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  have hbt := hA.tree S
  obtain ⟨fb', hfb', hfid⟩ := hwf.blockId bid hbt.1
  rw [hfb] at hfb'; cases hfb'
  obtain ⟨psS, oS, hpsS, hso, hev⟩ := enterBlock_panic h
  rw [hfid, sched_of_block hfb] at hso
  obtain ⟨pre, r, post, Gpre, hsplit, hpre, hrp⟩ := evalAll_panic_split hev
  obtain ⟨hM, hG1, hG2⟩ := mid_of S hA hfb hpsS hso hsplit hpre
  obtain ⟨gb, psT, oT, hgbb, hgid, hvals, hpsT, hoT, hagree, hszT⟩ := targetPre S hA hfb hpsS hso
  have hbg : bid ∈ g.blocks := by rw [S.blocks]; exact hbt.1
  have hownF := valuesOwn hwf hbt.1 hfb
  have hndF := hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩
  have hownG := valuesOwn hwg hbg hgbb
  have hndG := hwg.valuesNodup _ _ ⟨hbg, hgbb⟩
  obtain ⟨ondT, otopoT, omemT⟩ := schedule_topo hownG hndG hoT
  obtain ⟨ond, otopo, omem⟩ := schedule_topo hownF hndF hso
  -- the panicking root
  have hrS : r ∈ oS.toList := by rw [hsplit]; simp
  obtain ⟨hrb, fvr, hfvr, hrnph⟩ := (omem r).1 hrS
  obtain ⟨fvr', gvr, hfvr', hgvr, -, hfrid, -, -, hrelr, hzr⟩ := S.value hbt hfb hrb
  rw [hfvr] at hfvr'; cases hfvr'
  rw [stepV_of hfvr] at hrp
  have hrop := evalValue_panic_op hrp
  have hgop : gvr.op = fvr.op := by
    cases hrelr with
    | same hop => exact hop
    | phi _ hph => exact absurd hph hrnph
    | empty hzz => exact absurd hzz hzr
  have hrT : r ∈ oT.toList :=
    (omemT r).2 ⟨by rw [hvals]; exact hrb, gvr, hgvr, by rw [hgop]; exact hrnph⟩
  obtain ⟨pre', post', hsplitT⟩ := List.append_of_mem hrT
  -- what the target evaluates before `r`, the source evaluated before `r`
  have hspecS := schedule_spec hso
  have hspecT := schedule_spec hoT
  have hk : oS.toList[pre.length]? = some r := by rw [hsplit]; simp
  have hk' : oT.toList[pre'.length]? = some r := by rw [hsplitT]; simp
  have hnodeR : NodeIn (schedNodes f fb).toList r :=
    (nodeIn_schedNodes hownF).2 ⟨hrb, fvr, hfvr, hrnph⟩
  -- the roots run in the same order (#96): the target reaches nothing the source did not
  have hpe := phi_not_entry S hA hfb hpsS
  have hsame := sameNP_copy S hbt hfb hgbb hvals
  have hrnp : npIn (schedNodes f fb).toList r = true := by
    unfold npIn
    rw [← hfrid, nodeOf_schedNodes hownF hndF (hfrid ▸ hrb) (hfrid ▸ hfvr) hrnph]
    simpa using prio_panicking hrop
  have hdep : ∀ x y, npIn (schedNodes f fb).toList x = true →
      npIn (schedNodes f fb).toList y = true →
      (Order.Dep (NodeIn (schedNodes f fb).toList) (argsOf (schedNodes f fb).toList) x y ↔
        Order.Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList) x y) := by
    intro x y hx _
    have hxN := (npIn_iff.1 hx).1
    constructor
    · intro hd
      refine depPres S hbt hfb hgbb hvals hxN (fun gx hgx hcx => ?_) y hd
      obtain ⟨hxb, fx, hfx, hfxn⟩ := (nodeIn_schedNodes hownF).1 hxN
      obtain ⟨fx', gx', hfx', hgx', -, -, -, -, hrelx, hzx⟩ := S.value hbt hfb hxb
      rw [hfx] at hfx'; cases hfx'
      rw [hgx] at hgx'; cases hgx'
      have hpx : prio fx.op ≠ 0 := by
        unfold npIn at hx
        rw [nodeOf_schedNodes hownF hndF hxb hfx hfxn] at hx
        simpa using hx
      cases hrelx with
      | same hop => rw [← hop, hcx] at hpx; exact hpx rfl
      | phi _ hph => exact hfxn hph
      | empty hzz => exact hzx hzz
    · intro hd; exact (depBack S hbt hfb hpe hso hgbb hvals hd hxN).1
  have htr := sched_transfer' hspecS hspecT hsame hdep hk hk' hrnp (fun a y haN hyN hay hyT => by
    obtain ⟨hyb, fy, hfy, hfyn⟩ := (nodeIn_schedNodes hownF).1 hyN
    obtain ⟨fy', gy, hfy', hgy, -, -, -, -, hrely, hzy⟩ := S.value hbt hfb hyb
    rw [hfy] at hfy'; cases hfy'
    rw [argsOf_schedNodes hownF hndF hyb hfy hfyn] at hay
    obtain ⟨k, hk2⟩ := List.getElem?_of_mem hay
    have hk2' : fy.args[k]? = some a := by simpa using hk2
    cases hrely with
    | phi _ hph => exact absurd hph hfyn
    | empty hzz => exact absurd hzz hzy
    | same hop _ _ hsz hargs' =>
      obtain ⟨w, hw, hra⟩ := hargs' k a hk2'
      have hgyn : gy.op ≠ .Phi := by rw [hop]; exact hfyn
      have hwT : w ∈ argsOf (schedNodes g gb).toList y := by
        rw [argsOf_schedNodes hownG hndG (by rw [hvals]; exact hyb) hgy hgyn]
        exact List.mem_of_getElem? (by simpa using hw)
      obtain ⟨ka, hka⟩ := List.getElem?_of_mem ((omem a).2 ((nodeIn_schedNodes hownF).1 haN))
      exact feedsOf S hbt hfb hso hgbb hvals hyT hwT ka a hka hra)
  -- the target's prefix agrees with the source's frame at the panic
  have hargsT : ∀ x gv, g.value? x = some gv → argsF (Ctx.make tabs g).f x = gv.args.toList :=
    fun x gv hgv => argsF_of (f := g) hgv
  have hnotS : ∀ a, a ∉ oT.toList → a ∉ oS.toList := by
    intro a ha ham
    obtain ⟨hab, fv, hfv, hne⟩ := (omem a).1 ham
    obtain ⟨fv', gv, hfv', hgv, -, -, -, -, hrel, hz⟩ := S.value hbt hfb hab
    rw [hfv] at hfv'; cases hfv'
    exact ha ((omemT a).2 ⟨by rw [hvals]; exact hab, gv, hgv,
      fun hp => hne (valRel_phi hrel hz hp)⟩)
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
  have hloc : LocalOK env (Ctx.make tabs g) Gpre pre' := by
    intro x hx
    have hxT : x ∈ oT.toList := by rw [hsplitT]; exact List.mem_append_left _ hx
    obtain ⟨hxb, gv, hgv, hgn⟩ := (omemT x).1 hxT
    rw [hvals] at hxb
    obtain ⟨fv, -, hfv, -⟩ := S.value hbt hfb hxb
    by_cases hph : fv.op = .Phi
    · obtain ⟨y, h1, h2⟩ := evalFormer S hA hfb hM hxb hfv hgv hph hgn
      exact ⟨y, h1, fun g' hg' hag => by
        rw [stepV_of (ctx := Ctx.make tabs g) hgv]
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
      rw [stepV_of (ctx := Ctx.make tabs g) hgv, ← hevx]
      exact evalSame S hA hfb hM hxb hfv hgv hph
        (hdepPre x ⟨i', by omega, hix⟩ fv hfv)
        (fun msg he => by rw [hevx] at he; cases he) hg'
        (fun a ha => hag a (by rw [hargsT x gv hgv]; exact Array.mem_toList_iff.2 ha))
  have hS : ∀ a, a ∉ oT.toList → (setPhis psT fr.regs)[a]? = Gpre.regs[a]? := by
    intro a ha
    rw [hagree a ha, hM.out a (fun hm => hnotS a ha (by rw [hsplit]; exact List.mem_append_left _ hm))]
  have htopoT : TopoRem (argsF (Ctx.make tabs g).f) (pre' ++ r :: post') := by
    rw [← hsplitT]; exact otopoT
  have hpanT := evalAll_ref_panic (S := fun a => a ∉ oT.toList) (post := post')
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
      rw [stepV_of (ctx := Ctx.make tabs g) hgvr, ← hrp]
      exact evalSame S hA hfb hM hrb hfvr hgvr hrnph
        (hdepPre r ⟨pre.length, Nat.le_refl _, hk⟩ fvr hfvr)
        (fun msg he => by rw [hrp] at he; cases he) hg'
        (fun a ha => hag a (by rw [hargsT r gvr hgvr]; exact Array.mem_toList_iff.2 ha)))
  refine ⟨gb, hgbb, ?_⟩
  rw [enterBlock_eq, hpsT]
  change (Res.ofOption _ ((Ctx.make tabs g).sched[gb.id]?).join).bind _ = _
  rw [hgid, sched_of_block hgbb, hoT]
  change evalAll env (Ctx.make tabs g) _ oT.toList = _
  rw [hsplitT, hpanT]

end GoFV.Proof.CopyElim

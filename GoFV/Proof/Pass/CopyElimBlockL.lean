import GoFV.Proof.Pass.CopyElimSimL
import GoFV.Proof.Pass.CopyElimSched

/-!
# copyelim on `runL`: one block entry

`GoFV.Proof.Pass.CopyElimBlock` for `runL`. `AtL`: the simulation invariant at a block entry
(the frame is typed for both functions, `TypedL`; lemma (D) of `runL` holds for both at the
predecessor, `DInvL`). `copyEqL`: in the source's frame after any dependency-closed prefix of
the block's schedule, every available copy of `g` holds its argument's register.
-/

namespace GoFV.Proof.CopyElim

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt Dom

variable {md : LMode} {tabs : Tables} {f g : Func}

/-- The simulation invariant at the entry of block `bid` along edge `i`. -/
structure AtL (md : LMode) (env : Env) (tabs : Tables) (f g : Func) (fr : Frame) (bid : ID)
    (i : Nat) : Prop where
  size : fr.regs.size = f.valueTab.size
  tyS : TypedL md (Ctx.makeL tabs f) fr
  tyT : TypedL md (Ctx.makeL tabs g) fr
  pre : bid = f.entry ∨ ∃ p blkp, p ∈ f.blocks ∧ f.block? p = some blkp ∧
    ((make f).depthOf p).isSome ∧ (⟨bid, i⟩ : Edge) ∈ blkp.succs ∧
    DInvL md env (Ctx.makeL tabs f) (fun a => Anc (make f) a p) fr ∧
    DInvL md env (Ctx.makeL tabs g) (fun a => Anc (make f) a p) fr

namespace AtL

variable {env : Env} {fr : Frame} {bid : ID} {i : Nat}

theorem tree (S : SetupL md tabs f g) (h : AtL md env tabs f g fr bid i) : Tree f bid := by
  obtain ⟨ce, hwf⟩ := S.base.wf
  rcases h.pre with rfl | ⟨p, blkp, hp, hpb, hpt, he, -, -⟩
  · exact ⟨hwf.entry, by simp [entry_depth S.base.cp]⟩
  · obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 he
    exact ⟨(hwf.succLink p blkp ⟨hp, hpb⟩ j _ hj).1, (edge S.base.cf hp hpb hpt he).2.1⟩

theorem upS (S : SetupL md tabs f g) (h : AtL md env tabs f g fr bid i) :
    DInvL md env (Ctx.makeL tabs f) (fun a => Anc (make f) a bid ∧ a ≠ bid) fr := by
  rcases h.pre with rfl | ⟨p, blkp, hp, hpb, hpt, he, hS, -⟩
  · exact dinvL_entry S.base.cf fr
  · exact dinvL_edge S.base.cf hp hpb hpt he hS

theorem upT (S : SetupL md tabs f g) (h : AtL md env tabs f g fr bid i) :
    DInvL md env (Ctx.makeL tabs g) (fun a => Anc (make f) a bid ∧ a ≠ bid) fr := by
  rcases h.pre with rfl | ⟨p, blkp, hp, hpb, hpt, he, -, hT⟩
  · exact dinvL_entry S.base.cf fr
  · exact dinvL_edge S.base.cf hp hpb hpt he hT

/-- Predecessor `i` of the entered block is the tree block the run came from. -/
theorem pred (S : SetupL md tabs f g) (h : AtL md env tabs f g fr bid i) {fb : Block}
    (hfb : f.block? bid = some fb) {e : Edge} (he : fb.preds[i]? = some e) :
    bid ≠ f.entry ∧ ((make f).depthOf e.b).isSome ∧
      DInvL md env (Ctx.makeL tabs f) (fun a => Anc (make f) a e.b) fr ∧
      DInvL md env (Ctx.makeL tabs g) (fun a => Anc (make f) a e.b) fr := by
  obtain ⟨ce, hwf⟩ := S.base.wf
  rcases h.pre with rfl | ⟨p, blkp, hp, hpb, hpt, hin, hS, hT⟩
  · have := hwf.entryPreds fb hfb
    have := (Array.getElem?_eq_some_iff.1 he).1
    omega
  · obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 hin
    obtain ⟨-, c, hc, hcp⟩ := hwf.succLink p blkp ⟨hp, hpb⟩ j _ hj
    rw [hfb] at hc; cases hc
    rw [he] at hcp; cases hcp
    refine ⟨fun hbe => ?_, hpt, hS, hT⟩
    have := hwf.entryPreds fb (hbe ▸ hfb)
    have := (Array.getElem?_eq_some_iff.1 he).1
    omega

end AtL

/-- The source state during block `bid`: the frame `frPS` after the `Phi`s, the schedule `oS`
and the frame `H` after the prefix `P` of the schedule. -/
structure MidL (md : LMode) (env : Env) (tabs : Tables) (f : Func) (fr : Frame) (bid : ID)
    (i : Nat) (fb : Block) (frPS H : Frame) (oS : Array ID) (P : List ID) : Prop where
  keep : ∀ z, (z ∉ fb.values ∨ ∃ v, f.value? z = some v ∧ v.op ≠ .Phi) →
    frPS.regs[z]? = fr.regs[z]?
  phi : ∀ z ∈ fb.values, ∀ v, f.value? z = some v → v.op = .Phi → z < fr.regs.size →
    ∃ a y, v.args[i]? = some a ∧ fr.regs[a]? = some (some y) ∧
      frPS.regs[z]? = some (some (md.retype ((Ctx.makeL tabs f).tys[z]?.getD .other) y))
  sched : schedule f fb = some oS
  split : ∃ R, oS.toList = P ++ R
  out : ∀ z, z ∉ P → H.regs[z]? = frPS.regs[z]?
  eval : ∀ x ∈ P, ∃ v y, f.value? x = some v ∧ H.regs[x]? = some (some y) ∧
    evalValueL md env (Ctx.makeL tabs f) H v = .ok y
  typed : TypedL md (Ctx.makeL tabs f) H

/-- Cases where a copy of `g` lives outside the block or replaces one of its `Phi`s. -/
theorem copyEqBaseL (S : SetupL md tabs f g) {env : Env} {fr : Frame} {bid : ID} {i : Nat}
    (hA : AtL md env tabs f g fr bid i) {fb : Block} (hfb : f.block? bid = some fb)
    {frPS H : Frame} {oS : Array ID} {P : List ID}
    (hM : MidL md env tabs f fr bid i fb frPS H oS P)
    {u : ID} (hl : Listed f u) (hu : Anc (make f) (blockOf f u) bid)
    (hcase : blockOf f u ≠ bid ∨ ∃ v, f.value? u = some v ∧ v.op = .Phi)
    {gu : Value} {w : ID} (hgu : g.value? u = some gu) (hop : gu.op = .Copy)
    (hargs : gu.args = #[w]) : ∃ y, H.regs[u]? = some (some y) ∧ H.regs[w]? = some (some y) := by
  obtain ⟨ce, hwf⟩ := S.base.wf
  obtain ⟨b, fb', hb, hfb', hx, hbo, hbog⟩ := S.base.used hl hu
  obtain ⟨fv, gv, hfv, hgv, -, -, hgb, hty, hrel, hne⟩ := S.base.value hb hfb' hx
  rw [hgu] at hgv; cases hgv
  have hbt := hA.tree S
  -- `w` is defined in a strict dominator of the copy's block, so outside `bid` when the copy is
  have hwU : Anc (make f) (blockOf g w) b := by
    obtain ⟨gb, hgbb, -, -, -, -, hvals, -⟩ := S.base.block hb hfb'
    have hbt' := S.base.treeG hb
    have := uses S.base.cg hbt'.1 hgbb hbt'.2 (by rw [hvals]; exact hx) hgu (by rw [hop]; decide)
      (a := w) (by rw [hargs]; simp)
    rwa [S.base.mk_eq] at this
  -- values outside `bid` keep their registers
  have hnot : ∀ z, blockOf g z ≠ bid → (∃ b' fb', Tree f b' ∧ f.block? b' = some fb' ∧
      z ∈ fb'.values) → H.regs[z]? = fr.regs[z]? := by
    rintro z hz ⟨b', fb'', hb', hfb'', hz'⟩
    have hzb : z ∉ fb.values := fun hm => by
      obtain ⟨-, gz, -, hgz, hzb, -, hgzb, -⟩ := S.base.value hbt hfb hm
      apply hz; unfold blockOf; rw [hgz]; exact hgzb
    rw [hM.out z (fun hm => hzb (by
      obtain ⟨-, -, omem⟩ := schedule_topo (valuesOwn hwf hbt.1 hfb)
        (hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩) hM.sched
      obtain ⟨R, hR⟩ := hM.split
      exact ((omem z).1 (by rw [hR]; exact List.mem_append_left _ hm)).1)),
      hM.keep z (.inl hzb)]
  have hwl : Listed g w := by
    obtain ⟨ce', hwg⟩ := S.base.wg
    obtain ⟨gb, hgbb, -, -, -, -, hvals, -⟩ := S.base.block hb hfb'
    exact hwg.argListed b gb u gu ⟨⟨by rw [S.base.blocks]; exact hb.1, hgbb⟩,
      by rw [hvals]; exact hx, hgu⟩ w (by rw [hargs]; simp)
  have hgbu : blockOf g u = b := hbog
  by_cases hbb : b = bid
  · -- a `Phi` of `bid` that became a copy
    obtain rfl := hbb.symm
    rw [hfb] at hfb'; cases hfb'
    have hph : fv.op = .Phi := by
      rcases hcase with hcase | ⟨v, hv, hph⟩
      · exact absurd hbo hcase
      · rw [hfv] at hv; cases hv; exact hph
    obtain ⟨w', hw'args, hrelA⟩ : ∃ w', gu.args = #[w'] ∧ ∀ a ∈ fv.args, ArgRel g a w' := by
      cases hrel with
      | same hop' => rw [hop, hph] at hop'; cases hop'
      | phi w' _ _ ha hr => exact ⟨w', ha, hr⟩
      | empty _ he => rw [hop] at he; cases he
    have hww : w = w' := by rw [hargs] at hw'args; simpa using hw'args
    subst hww
    have hulen : u < fr.regs.size := by rw [hA.size]; exact lt_of_value? hfv
    obtain ⟨a, y, ha, hy, hP⟩ := hM.phi u hx fv hfv hph hulen
    have hsz := hwf.phiArity bid fb u fv ⟨⟨hbt.1, hfb⟩, hx, hfv⟩ hph
    have hilt : i < fb.preds.size := by rw [← hsz]; exact (Array.getElem?_eq_some_iff.1 ha).1
    have he : fb.preds[i]? = some fb.preds[i] := by simp [hilt]
    obtain ⟨hne, hpt, -, hDT⟩ := hA.pred S hfb he
    have hpu := phiUse S.base.cf hbt.1 hfb hbt.2 hx hfv hph ha he hpt
    have hla : Listed f a :=
      hwf.argListed _ _ _ _ ⟨⟨hbt.1, hfb⟩, hx, hfv⟩ a (Array.mem_of_getElem? ha)
    obtain ⟨y', h1, h2⟩ := S.argEq hDT (A := fun z => Anc (make f) z fb.preds[i].b) hpu
      hA.tyT hla hpu (hrelA a (Array.mem_of_getElem? ha))
    rw [hy] at h1; cases h1
    obtain ⟨hwU', hwne⟩ := S.base.phiOut hbt hne hfb hx hfv hgu hph hop hargs hrelA
    obtain ⟨bw, fbw, hbw, hfbw, hxw, -, -⟩ := S.base.usedG hwl hwU'
    have huP : u ∉ P := fun hm => by
      obtain ⟨-, -, omem⟩ := schedule_topo (valuesOwn hwf hbt.1 hfb)
        (hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩) hM.sched
      obtain ⟨R, hR⟩ := hM.split
      obtain ⟨-, v', hv', hne'⟩ := (omem u).1 (by rw [hR]; exact List.mem_append_left _ hm)
      rw [hfv] at hv'; cases hv'; exact hne' hph
    refine ⟨y, ?_, by rw [hnot w hwne ⟨bw, fbw, hbw, hfbw, hxw⟩, h2]⟩
    rw [hM.out u huP, hP, ← S.tys hbt hfb hx, S.copyShape hbt hfb hx hgu hop hargs (hA.tyT w y h2)]
  · -- the copy is defined in a strict dominator of `bid`
    have hcase : blockOf f u ≠ bid := by rw [hbo]; exact hbb
    rw [hbo] at hcase hu
    obtain ⟨y, h1, h2⟩ := S.argEq (hA.upT S) (A := fun z => Anc (make f) z bid ∧ z ≠ bid)
      (by rw [hbo]; exact ⟨hu, hcase⟩) hA.tyT hl (by rw [hbo]; exact hu)
      (.inr ⟨gu, hgu, hop, hargs⟩)
    have hwne : blockOf g w ≠ bid := fun he => hcase
      (Anc.antisymm S.base.cp hu (he ▸ hwU))
    obtain ⟨bw, fbw, hbw, hfbw, hxw, -, -⟩ := S.base.usedG hwl (q := b) hwU
    exact ⟨y, by rw [hnot u (by rw [hgbu]; exact hcase) ⟨b, fb', hb, hfb', hx⟩, h1],
      by rw [hnot w hwne ⟨bw, fbw, hbw, hfbw, hxw⟩, h2]⟩

/-- **Copy equations in the source frame.** In the source's frame after a prefix of the
block's schedule, every copy of `g` that is available (defined in a strict dominator, a `Phi`
of the block that became a copy, or already evaluated) holds its argument's register. -/
theorem copyEqL (S : SetupL md tabs f g) {env : Env} {fr : Frame} {bid : ID} {i : Nat}
    (hA : AtL md env tabs f g fr bid i) {fb : Block} (hfb : f.block? bid = some fb)
    {frPS H : Frame} {oS : Array ID} {P : List ID}
    (hM : MidL md env tabs f fr bid i fb frPS H oS P)
    {u : ID} (hl : Listed f u) (hu : Anc (make f) (blockOf f u) bid)
    (hav : u ∈ fb.values → (∃ v, f.value? u = some v ∧ v.op = .Phi) ∨ u ∈ P)
    {gu : Value} {w : ID} (hgu : g.value? u = some gu) (hop : gu.op = .Copy)
    (hargs : gu.args = #[w]) : ∃ y, H.regs[u]? = some (some y) ∧ H.regs[w]? = some (some y) := by
  obtain ⟨ce, hwf⟩ := S.base.wf
  have hbt := hA.tree S
  obtain ⟨-, otopo, omem⟩ := schedule_topo (valuesOwn hwf hbt.1 hfb)
    (hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩) hM.sched
  obtain ⟨R, hR⟩ := hM.split
  -- the evaluated copies, by their position in the prefix
  have main : ∀ (k : Nat) (u : ID) (gu : Value) (w : ID), P[k]? = some u →
      g.value? u = some gu → gu.op = .Copy →
      gu.args = #[w] → ∃ y, H.regs[u]? = some (some y) ∧ H.regs[w]? = some (some y) := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
    intro u gu w hk hgu hop hargs
    have huP : u ∈ P := List.mem_of_getElem? hk
    have huo : u ∈ oS.toList := by rw [hR]; exact List.mem_append_left _ huP
    obtain ⟨hub, fv, hfv, hnph⟩ := (omem u).1 huo
    obtain ⟨fv', gv, hfv', hgv, hfb', hfid, hgb, hty, hrel, -⟩ := S.base.value hbt hfb hub
    rw [hfv] at hfv'; cases hfv'
    rw [hgu] at hgv; cases hgv
    obtain ⟨hfop, fa, hfargs, hra⟩ := copyArg hrel hnph hop hargs
    obtain ⟨v', yu, hfv2, hyu, hev⟩ := hM.eval u huP
    rw [hfv] at hfv2; cases hfv2
    obtain ⟨y0, hy0, rfl⟩ := evalValueL_copy_inv hfop hfargs hev
    -- `fa` is used by `u`, so it is defined in an ancestor and listed in a tree block
    have hfaU : Anc (make f) (blockOf f fa) bid :=
      uses S.base.cf hbt.1 hfb hbt.2 hub hfv hnph (a := fa) (by rw [hfargs]; simp)
    have hfal : Listed f fa :=
      hwf.argListed _ _ _ _ ⟨⟨hbt.1, hfb⟩, hub, hfv⟩ fa (by rw [hfargs]; simp)
    -- the shape of `u` is the shape of `w`
    have hshape : ∀ y, H.regs[w]? = some (some y) →
        md.retype ((Ctx.makeL tabs f).tys[fv.id]?.getD .other) y = y := by
      intro y hy
      have hwl : Listed g w := by
        obtain ⟨ce', hwg⟩ := S.base.wg
        obtain ⟨gb, hgbb, -, -, -, -, hvals, -⟩ := S.base.block hbt hfb
        exact hwg.argListed bid gb u gu ⟨⟨by rw [S.base.blocks]; exact hbt.1, hgbb⟩,
          by rw [hvals]; exact hub, hgu⟩ w (by rw [hargs]; simp)
      have hwU : Anc (make f) (blockOf g w) bid := by
        obtain ⟨gb, hgbb, -, -, -, -, hvals, -⟩ := S.base.block hbt hfb
        have hbt' := S.base.treeG hbt
        have := uses S.base.cg hbt'.1 hgbb hbt'.2 (by rw [hvals]; exact hub) hgu
          (by rw [hop]; decide) (a := w) (by rw [hargs]; simp)
        rwa [S.base.mk_eq] at this
      obtain ⟨bw, fbw, hbw, hfbw, hxw, -, -⟩ := S.base.usedG hwl hwU
      have := hM.typed w y hy
      rw [← S.tys hbw hfbw hxw] at this
      rw [hfid, ← S.tys hbt hfb hub]
      exact S.copyShape hbt hfb hub hgu hop hargs this
    rcases hra with rfl | ⟨ufa, hufa, hopa, hargsa⟩
    · exact ⟨y0, by rw [hyu, hshape y0 hy0], hy0⟩
    · -- `fa` is itself a copy of `w`: by induction or a base case
      have hfa : ∃ y, H.regs[fa]? = some (some y) ∧ H.regs[w]? = some (some y) := by
        by_cases hcase : blockOf f fa ≠ bid ∨ ∃ v, f.value? fa = some v ∧ v.op = .Phi
        · exact copyEqBaseL S hA hfb hM hfal hfaU hcase hufa hopa hargsa
        · have hfab : blockOf f fa = bid :=
            Classical.byContradiction fun hne => hcase (.inl hne)
          obtain ⟨b', fb', hb', hfb', hx', hbo, -⟩ := S.base.used hfal hfaU
          rw [hfab] at hbo; subst hbo
          rw [hfb] at hfb'; cases hfb'
          obtain ⟨vfa, -, hvfa, -⟩ := S.base.value hbt hfb hx'
          have hfano : fa ∈ oS.toList :=
            (omem fa).2 ⟨hx', vfa, hvfa, fun hp => hcase (.inr ⟨vfa, hvfa, hp⟩)⟩
          have hku : oS.toList[k]? = some u := by
            rw [hR, List.getElem?_append_left (lt_length_of_getElem? hk)]; exact hk
          obtain ⟨j, hj, hjfa⟩ := topoRem_before otopo hku
            (by rw [argsF_of hfv, hfargs]; simp) hfano
          have hjP : P[j]? = some fa := by
            rw [hR, List.getElem?_append_left (by
              have := lt_length_of_getElem? hk; omega)] at hjfa
            exact hjfa
          exact ih j hj fa ufa w hjP hufa hopa hargsa
      obtain ⟨y1, h1, h2⟩ := hfa
      rw [hy0] at h1; cases h1
      exact ⟨y0, by rw [hyu, hshape y0 h2], h2⟩
  -- dispatch
  by_cases hcase : blockOf f u ≠ bid ∨ ∃ v, f.value? u = some v ∧ v.op = .Phi
  · exact copyEqBaseL S hA hfb hM hl hu hcase hgu hop hargs
  · have hub : blockOf f u = bid := Classical.byContradiction fun hne => hcase (.inl hne)
    obtain ⟨b', fb', hb', hfb', hx', hbo, -⟩ := S.base.used hl hu
    rw [hub] at hbo; subst hbo
    rw [hfb] at hfb'; cases hfb'
    rcases hav hx' with hph | huP
    · exact absurd (.inr hph) hcase
    · obtain ⟨k, hk⟩ := List.getElem?_of_mem huP
      exact main k u gu w hk hgu hop hargs

end GoFV.Proof.CopyElim

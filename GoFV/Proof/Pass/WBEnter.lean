import GoFV.Proof.Pass.WBEval
import GoFV.Proof.Enter

/-!
# Entering a block whose values satisfy a register property (issue #36)

`enter_Q`: a listed block of a well-formed function whose `Phi`s read arguments satisfying a
register property `Q` (after `retype`), and whose other values satisfy `LocalQ` with their
arguments outside the block in a set `S` of registers satisfying `Q`, is entered successfully;
afterwards every value of the block and of `S` holds a register satisfying `Q`, and the
registers outside the block are unchanged. `enter_Q_panic`: if the schedule is
`pre ++ r :: post`, the values of `pre` satisfy `LocalQ` and `r` panics on every frame whose
argument registers satisfy `Q`, the entry panics.
-/

namespace GoFV.Proof.WB

open GoFV.SSA GoFV.SSA.Sem

private theorem phiStep_ok {ctx : Ctx} {fr : Frame} {i : Nat} {z : ID} {v : Value}
    (hv : ctx.f.value? z = some v)
    (h : v.op = .Phi → ∃ a y, v.args[i]? = some a ∧ fr.regs[a]? = some (some y)) :
    ∃ o, phiStep ctx fr i z = .ok o := by
  unfold phiStep
  split
  · rename_i v' hv'
    rw [hv] at hv'; cases hv'
    split
    · rename_i hb
      obtain ⟨a, y, ha, hy⟩ := h (by simpa using hb)
      rw [ha]
      dsimp only
      rw [hy]
      exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · rename_i hn; rw [hv] at hn; cases hn

private theorem topoRem_suffix {D : ID → List ID} :
    ∀ {L1 L2 : List ID}, TopoRem D (L1 ++ L2) → TopoRem D L2
  | [], _, h => h
  | _ :: L1, _, ⟨_, h⟩ => topoRem_suffix (L1 := L1) h

private theorem topoRem_before {D : ID → List ID} :
    ∀ {L1 L2 : List ID}, TopoRem D (L1 ++ L2) → ∀ x ∈ L1, ∀ a ∈ D x, a ∉ L2
  | [], _, _, _, hx, _, _ => absurd hx List.not_mem_nil
  | y :: L1, L2, ⟨h1, h2⟩, x, hx, a, ha => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact fun hm => h1 a ha (List.mem_cons_of_mem _ (List.mem_append_right _ hm))
    · exact topoRem_before h2 x hx a ha

private theorem refOK_of_topoRem {D : ID → List ID} :
    ∀ {o : List ID} {S : ID → Prop}, TopoRem D o → (∀ x ∈ o, ∀ a ∈ D x, a ∉ o → S a) →
      RefOK D S o
  | [], _, _, _ => trivial
  | x :: s, S, ⟨h1, h2⟩, hS =>
    ⟨fun a ha => hS x List.mem_cons_self a ha (h1 a ha),
      refOK_of_topoRem h2 fun y hy a ha has => by
        by_cases hax : a = x
        · exact .inr hax
        · refine .inl (hS y (List.mem_cons_of_mem _ hy) a ha fun hm => ?_)
          rcases List.mem_cons.1 hm with h | h
          · exact hax h
          · exact has h⟩

/-- An argument of a scheduled value that is not scheduled is in `S` or a `Phi` of the block. -/
private theorem enter_arg {f : Func} {C : Block} {o : Array ID} {S : ID → Prop}
    (hown : ValuesOwn f C)
    (hargs : ∀ x ∈ C.values, ∀ v, f.value? x = some v → v.op ≠ .Phi →
      ∀ a ∈ v.args, a ∉ C.values → S a)
    (omem : ∀ x, x ∈ o.toList ↔ x ∈ C.values ∧ ∃ v, f.value? x = some v ∧ v.op ≠ .Phi)
    {x a : ID} (hx : x ∈ o.toList) (ha : a ∈ argsF f x) (hao : a ∉ o.toList) :
    S a ∨ (a ∈ C.values ∧ ∃ v, f.value? a = some v ∧ v.op = .Phi) := by
  obtain ⟨hxC, v, hv, hop⟩ := (omem x).1 hx
  rw [argsF_of hv] at ha
  by_cases haC : a ∈ C.values
  · obtain ⟨w, hw, -⟩ := hown a haC
    exact .inr ⟨haC, w, hw, Classical.byContradiction fun hne => hao ((omem a).2 ⟨haC, w, hw, hne⟩)⟩
  · exact .inl (hargs x hxC v hv hop a (Array.mem_toList_iff.1 ha) haC)

section
variable {ce : CheckEnv} {tabs : Tables} {g : Func} {env : Env} {fr0 : Frame}
  {Q : ID → Val → Prop}

/-- The frame after setting the `Phi`s of an entered block. -/
private theorem enter_phis (hwg : WF ce g) {cid : ID} {C : Block} (hc : cid ∈ g.blocks)
    (hC : g.block? cid = some C) {F : Frame} {e : Nat}
    (hF : F = { fr0 with regs := F.regs }) (hs : F.regs.size = g.valueTab.size)
    (hphi : ∀ x ∈ C.values, ∀ v, g.value? x = some v → v.op = .Phi →
      ∃ a z, v.args[e]? = some a ∧ F.regs[a]? = some (some z) ∧
        Q x (z.retype ((Ctx.make tabs g).tys[x]?.getD .other)))
    (S : ID → Prop) (hS : ∀ a, S a → ∃ z, F.regs[a]? = some (some z) ∧ Q a z)
    (hSC : ∀ a, S a → a ∉ C.values) :
    ∃ ps, C.values.toList.filterMapM (phiStep (Ctx.make tabs g) F e) = .ok ps ∧
      ({ F with regs := setPhis ps F.regs } : Frame) = { fr0 with regs := setPhis ps F.regs } ∧
      (setPhis ps F.regs).size = g.valueTab.size ∧
      (∀ a, (S a ∨ (a ∈ C.values ∧ ∃ v, g.value? a = some v ∧ v.op = .Phi)) →
        ∃ z, (setPhis ps F.regs)[a]? = some (some z) ∧ Q a z) ∧
      (∀ a, a ∉ C.values → (setPhis ps F.regs)[a]? = F.regs[a]?) := by
  have hnd := hwg.valuesNodup cid C ⟨hc, hC⟩
  have hown := valuesOwn hwg hc hC
  obtain ⟨ps, hps⟩ := filterMapM_phi_ok (ctx := Ctx.make tabs g) (fr := F) (i := e)
    (l := C.values.toList) fun z hz => by
      obtain ⟨v, hv, -⟩ := hown z (Array.mem_toList_iff.1 hz)
      refine phiStep_ok hv fun hop => ?_
      obtain ⟨a, y, ha, hy, -⟩ := hphi z (Array.mem_toList_iff.1 hz) v hv hop
      exact ⟨a, y, ha, hy⟩
  obtain ⟨h1, -, h3, h4⟩ := phis_spec hnd hps
  refine ⟨ps, hps, by rw [hF], by rw [h1, hs], fun a ha => ?_, fun a ha => h3 a (.inl ha)⟩
  rcases ha with ha | ⟨haC, v, hv, hop⟩
  · rw [h3 a (.inl (hSC a ha))]; exact hS a ha
  · obtain ⟨b, z, hb, hz, hQ⟩ := hphi a haC v hv hop
    obtain ⟨b', y, hb', hy, hP⟩ := h4 a haC v hv hop (hs ▸ lt_of_value? hv)
    rw [hb] at hb'; cases hb'
    rw [hz] at hy; cases hy
    exact ⟨_, hP, hQ⟩

theorem enter_Q (hwg : WF ce g) {cid : ID} {C : Block} (hc : cid ∈ g.blocks)
    (hC : g.block? cid = some C) (hsch : ∃ o, schedule g C = some o) {F : Frame} {e : Nat}
    (hF : F = { fr0 with regs := F.regs }) (hs : F.regs.size = g.valueTab.size)
    (hphi : ∀ x ∈ C.values, ∀ v, g.value? x = some v → v.op = .Phi →
      ∃ a z, v.args[e]? = some a ∧ F.regs[a]? = some (some z) ∧
        Q x (z.retype ((Ctx.make tabs g).tys[x]?.getD .other)))
    (S : ID → Prop) (hS : ∀ a, S a → ∃ z, F.regs[a]? = some (some z) ∧ Q a z)
    (hSC : ∀ a, S a → a ∉ C.values)
    (hloc : ∀ x ∈ C.values, ∀ v, g.value? x = some v → v.op ≠ .Phi →
      LocalQ env (Ctx.make tabs g) fr0 Q x)
    (hargs : ∀ x ∈ C.values, ∀ v, g.value? x = some v → v.op ≠ .Phi →
      ∀ a ∈ v.args, a ∉ C.values → S a) :
    ∃ F', enterBlock env (Ctx.make tabs g) F C e = .ok F' ∧ F' = { fr0 with regs := F'.regs } ∧
      F'.regs.size = F.regs.size ∧
      (∀ a, (S a ∨ a ∈ C.values) → ∃ z, F'.regs[a]? = some (some z) ∧ Q a z) ∧
      (∀ a, a ∉ C.values → F'.regs[a]? = F.regs[a]?) := by
  have hnd := hwg.valuesNodup cid C ⟨hc, hC⟩
  have hown := valuesOwn hwg hc hC
  obtain ⟨b', hb', hid⟩ := hwg.blockId cid hc
  rw [hC] at hb'; cases hb'
  obtain ⟨o, ho⟩ := hsch
  obtain ⟨-, otopo, omem⟩ := schedule_topo hown hnd ho
  obtain ⟨ps, hps, hP, hPs, hPQ, hPkeep⟩ := enter_phis hwg hc hC hF hs hphi S hS hSC
  have href : RefOK (argsF g)
      (fun a => S a ∨ (a ∈ C.values ∧ ∃ v, g.value? a = some v ∧ v.op = .Phi)) o.toList :=
    refOK_of_topoRem otopo fun x hx a ha hao => enter_arg hown hargs omem hx ha hao
  obtain ⟨G, h1, h2, h3, h4, h5⟩ := evalAll_Q (env := env) (ctx := Ctx.make tabs g) (fr0 := fr0)
    (Q := Q) (g := { F with regs := setPhis ps F.regs })
    (fun x hx => by
      obtain ⟨hxC, v, hv, hop⟩ := (omem x).1 hx
      exact hloc x hxC v hv hop) href hPQ hP hPs
  refine ⟨G, ?_, h2, ?_, fun a ha => ?_, fun a ha => ?_⟩
  · rw [enterBlock_eq, hps]
    change (Res.ofOption _ ((Ctx.make tabs g).sched[C.id]?).join).bind _ = _
    rw [hid, sched_of_block hC, ho]
    exact h1
  · rw [h3]; exact setPhis_size ps F.regs
  · rcases ha with ha | haC
    · exact h4 a (.inl (.inl ha))
    · obtain ⟨v, hv, -⟩ := hown a haC
      by_cases hop : v.op = .Phi
      · exact h4 a (.inl (.inr ⟨haC, v, hv, hop⟩))
      · exact h4 a (.inr ((omem a).2 ⟨haC, v, hv, hop⟩))
  · rw [h5 a (fun hm => ha ((omem a).1 hm).1)]
    exact hPkeep a ha

theorem enter_Q_panic (hwg : WF ce g) {cid : ID} {C : Block} (hc : cid ∈ g.blocks)
    (hC : g.block? cid = some C) {o : Array ID} (ho : schedule g C = some o)
    {pre post : List ID} {r : ID} (hsplit : o.toList = pre ++ r :: post) {F : Frame} {e : Nat}
    (hF : F = { fr0 with regs := F.regs }) (hs : F.regs.size = g.valueTab.size)
    (hphi : ∀ x ∈ C.values, ∀ v, g.value? x = some v → v.op = .Phi →
      ∃ a z, v.args[e]? = some a ∧ F.regs[a]? = some (some z) ∧
        Q x (z.retype ((Ctx.make tabs g).tys[x]?.getD .other)))
    (S : ID → Prop) (hS : ∀ a, S a → ∃ z, F.regs[a]? = some (some z) ∧ Q a z)
    (hSC : ∀ a, S a → a ∉ C.values)
    (hloc : ∀ x ∈ pre, LocalQ env (Ctx.make tabs g) fr0 Q x)
    (hargs : ∀ x ∈ C.values, ∀ v, g.value? x = some v → v.op ≠ .Phi →
      ∀ a ∈ v.args, a ∉ C.values → S a)
    {ep : Panic} {m : Mem}
    (hr : ∀ g' : Frame, g' = { fr0 with regs := g'.regs } →
      (∀ a ∈ argsF g r, ∃ z, g'.regs[a]? = some (some z) ∧ Q a z) →
      stepV env (Ctx.make tabs g) g' r = .panic ep m) :
    enterBlock env (Ctx.make tabs g) F C e = .panic ep m := by
  have hnd := hwg.valuesNodup cid C ⟨hc, hC⟩
  have hown := valuesOwn hwg hc hC
  obtain ⟨b', hb', hid⟩ := hwg.blockId cid hc
  rw [hC] at hb'; cases hb'
  obtain ⟨-, otopo, omem⟩ := schedule_topo hown hnd ho
  have hmo : ∀ z, z ∈ o.toList ↔ z ∈ pre ++ r :: post := fun z => by rw [hsplit]
  rw [hsplit] at otopo
  obtain ⟨ps, hps, hP, hPs, hPQ, -⟩ := enter_phis hwg hc hC hF hs hphi S hS hSC
  have href : RefOK (argsF g)
      (fun a => S a ∨ (a ∈ C.values ∧ ∃ v, g.value? a = some v ∧ v.op = .Phi)) pre :=
    refOK_of_topoRem (GoFV.Proof.topoRem_prefix otopo) fun x hx a ha hap =>
      enter_arg hown hargs omem ((hmo x).2 (List.mem_append_left _ hx)) ha fun hm => by
        rcases List.mem_append.1 ((hmo a).1 hm) with h | h
        · exact hap h
        · exact topoRem_before otopo x hx a ha h
  have hro : r ∈ o.toList := (hmo r).2 (List.mem_append_right _ List.mem_cons_self)
  have hrargs : ∀ a ∈ argsF (Ctx.make tabs g).f r,
      (S a ∨ (a ∈ C.values ∧ ∃ v, g.value? a = some v ∧ v.op = .Phi)) ∨ a ∈ pre := by
    intro a ha
    by_cases hap : a ∈ pre
    · exact .inr hap
    · refine .inl (enter_arg hown hargs omem hro ha fun hm => ?_)
      rcases List.mem_append.1 ((hmo a).1 hm) with h | h
      · exact hap h
      · exact (topoRem_suffix otopo).1 a ha h
  rw [enterBlock_eq, hps]
  change (Res.ofOption _ ((Ctx.make tabs g).sched[C.id]?).join).bind _ = _
  rw [hid, sched_of_block hC, ho]
  change evalAll env (Ctx.make tabs g) { F with regs := setPhis ps F.regs } o.toList = _
  rw [hsplit]
  exact evalAll_Q_panic hloc href hPQ hP hPs hrargs hr

end

end GoFV.Proof.WB

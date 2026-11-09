import GoFV.Proof.Avail
import GoFV.Proof.Sim

variable [GoFV.SSA.Sem.Addrs]

/-!
# What one block entry of a well-formed function does

`enter_ok_facts`: a successful `enterBlock` of a listed block changes only the block's values;
each non-`Phi` re-evaluates to its register in the final frame and each `Phi` holds its
incoming argument. `enter_panic_facts`: where a panicking `enterBlock` panics — after the
`Phi`s and a prefix of the block's schedule, at a non-`Phi` of the block.
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

theorem stepV_eq {env : Env} {ctx : Ctx} {fr : Frame} {x : ID} {v : Value}
    (h : ctx.f.value? x = some v) : stepV env ctx fr x = evalValue env ctx fr v := by
  unfold stepV; rw [h]

theorem topoRem_prefix {D : ID → List ID} :
    ∀ {L1 L2 : List ID}, TopoRem D (L1 ++ L2) → TopoRem D L1
  | [], _, _ => trivial
  | x :: L1, L2, ⟨h1, h2⟩ =>
    ⟨fun a ha hm => h1 a ha (List.mem_cons.2 ((List.mem_cons.1 hm).imp id
      fun h => List.mem_append_left _ h)), topoRem_prefix h2⟩

section
variable {ce : CheckEnv} {tabs : Tables} {f : Func} {env : Env}

theorem enter_ok_facts (hwf : WF ce f) {bid : ID} {B : Block} (hb : bid ∈ f.blocks)
    (hB : f.block? bid = some B) {fr G : Frame} {i : Nat} (hs : fr.regs.size = f.valueTab.size)
    (h : enterBlock env (Ctx.make tabs f) fr B i = .ok G) :
    G = { fr with regs := G.regs } ∧ G.regs.size = fr.regs.size ∧
    (∀ z, z ∉ B.values → G.regs[z]? = fr.regs[z]?) ∧
    (∀ x ∈ B.values, ∀ v, f.value? x = some v → v.op ≠ .Phi →
      ∃ y, G.regs[x]? = some (some y) ∧ evalValue env (Ctx.make tabs f) G v = .ok y) ∧
    (∀ x ∈ B.values, ∀ v, f.value? x = some v → v.op = .Phi →
      ∃ a y, v.args[i]? = some a ∧ fr.regs[a]? = some (some y) ∧
        G.regs[x]? = some (some (y.retype ((Ctx.make tabs f).tys[x]?.getD .other)))) := by
  have hnd := hwf.valuesNodup bid B ⟨hb, hB⟩
  have hown := valuesOwn hwf hb hB
  obtain ⟨b', hb', hid⟩ := hwf.blockId bid hb
  rw [hB] at hb'; cases hb'
  obtain ⟨frP, o, ho, hev, hP, hPs, -, hkeep, hphi⟩ := enterBlock_spec hnd h
  rw [hid, sched_of_block hB] at ho
  obtain ⟨ond, otopo, omem⟩ := schedule_topo hown hnd ho
  obtain ⟨e1, e2, e3, e4⟩ := evalAll_spec ond (by exact otopo) (by rw [hPs, hs]; rfl) hev
  refine ⟨by rw [e1, hP], by rw [e2, hPs], fun z hz => ?_, fun x hx v hv hp => ?_,
    fun x hx v hv hp => ?_⟩
  · rw [e3 z (fun hm => hz ((omem z).1 hm).1), hkeep z (.inl hz)]
  · obtain ⟨v', y, hv', hy, hev'⟩ := e4 x ((omem x).2 ⟨hx, v, hv, hp⟩)
    change f.value? x = some v' at hv'
    rw [hv] at hv'; cases hv'
    exact ⟨y, hy, hev'⟩
  · have hlt : x < fr.regs.size := hs ▸ lt_of_value? hv
    obtain ⟨a, y, ha, hy, hP'⟩ := hphi x hx v hv hp hlt
    have hxo : x ∉ o.toList := fun hm => by
      obtain ⟨-, v', hv', hne⟩ := (omem x).1 hm
      change f.value? x = some v' at hv'
      rw [hv] at hv'; cases hv'; exact hne hp
    exact ⟨a, y, ha, hy, by rw [e3 x hxo, hP']⟩

theorem enter_panic_facts (hwf : WF ce f) {bid : ID} {B : Block} (hb : bid ∈ f.blocks)
    (hB : f.block? bid = some B) {fr : Frame} {i : Nat} (hs : fr.regs.size = f.valueTab.size)
    {e : Panic} {m : Mem} (h : enterBlock env (Ctx.make tabs f) fr B i = .panic e m) :
    ∃ ps o pre r post Gpre, B.values.toList.filterMapM (phiStep (Ctx.make tabs f) fr i) = .ok ps ∧
      schedule f B = some o ∧ o.toList = pre ++ r :: post ∧
      evalAll env (Ctx.make tabs f) { fr with regs := setPhis ps fr.regs } pre = .ok Gpre ∧
      stepV env (Ctx.make tabs f) Gpre r = .panic e m ∧
      Gpre = { fr with regs := Gpre.regs } ∧ Gpre.regs.size = fr.regs.size ∧
      (∀ z, z ∉ B.values → Gpre.regs[z]? = fr.regs[z]?) ∧
      (∀ x ∈ pre, ∃ v y, f.value? x = some v ∧ Gpre.regs[x]? = some (some y) ∧
        evalValue env (Ctx.make tabs f) Gpre v = .ok y) ∧
      (∀ x ∈ B.values, ∀ v, f.value? x = some v → v.op = .Phi →
        ∃ a y, v.args[i]? = some a ∧ fr.regs[a]? = some (some y) ∧
          Gpre.regs[x]? = some (some (y.retype ((Ctx.make tabs f).tys[x]?.getD .other)))) ∧
      r ∈ B.values ∧ ∃ rv, f.value? r = some rv ∧ rv.op ≠ .Phi ∧
        Panicking rv.op := by
  have hnd := hwf.valuesNodup bid B ⟨hb, hB⟩
  have hown := valuesOwn hwf hb hB
  obtain ⟨b', hb', hid⟩ := hwf.blockId bid hb
  rw [hB] at hb'; cases hb'
  obtain ⟨ps, o, hps, ho, hev⟩ := enterBlock_panic h
  rw [hid, sched_of_block hB] at ho
  obtain ⟨pre, r, post, Gpre, hsplit, hpre, hrp⟩ := evalAll_panic_split hev
  obtain ⟨ond, otopo, omem⟩ := schedule_topo hown hnd ho
  obtain ⟨hPs, -, hkeep, hphi⟩ := phis_spec hnd hps
  rw [hsplit] at ond otopo
  obtain ⟨e1, e2, e3, e4⟩ := evalAll_spec (List.nodup_append.1 ond).1
    (by exact topoRem_prefix otopo) (by simp [hPs, hs]; rfl) hpre
  have hrS : r ∈ o.toList := by rw [hsplit]; simp
  obtain ⟨hrB, rv, hrv, hrnp⟩ := (omem r).1 hrS
  have hpo : ∀ z, z ∈ pre → z ∈ o.toList := fun z hz => by rw [hsplit]; simp [hz]
  refine ⟨ps, o, pre, r, post, Gpre, hps, ho, hsplit, hpre, hrp, by rw [e1], by rw [e2, hPs],
    fun z hz => ?_, e4, fun x hx v hv hp => ?_, hrB, rv, hrv, hrnp, ?_⟩
  · rw [e3 z (fun hm => hz ((omem z).1 (hpo z hm)).1), hkeep z (.inl hz)]
  · have hlt : x < fr.regs.size := hs ▸ lt_of_value? hv
    obtain ⟨a, y, ha, hy, hP'⟩ := hphi x hx v hv hp hlt
    have hxo : x ∉ pre := fun hm => by
      obtain ⟨-, v', hv', hne⟩ := (omem x).1 (hpo x hm)
      change f.value? x = some v' at hv'
      rw [hv] at hv'; cases hv'; exact hne hp
    exact ⟨a, y, ha, hy, by rw [e3 x hxo, hP']⟩
  · rw [stepV_eq hrv] at hrp
    exact evalValue_panic_op hrp

end

end GoFV.Proof

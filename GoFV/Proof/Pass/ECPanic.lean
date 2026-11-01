import GoFV.Proof.Pass.ECOk
import GoFV.Proof.Pass.ZCSERank

/-!
# A block entry that panics (issue #28)

`enter_panic`: if the source panics entering block `b` (at the non-pure node `r` of its
schedule, after the prefix `pre`), the target panics alike with a refined memory: both
schedules list the non-pure nodes in the same sequence, so every source value the target
evaluates before `r` the source evaluated before `r` (`Order.transfer_rank` with the `Feeds`
condition of `CvBlock`); the target evaluates that prefix (`tgt_loop` against the source's
frame at the panic) and then `r` by its obligation (`tgt_next`).
-/

namespace GoFV.Proof.EC

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Proof.AtomSim GoFV.Proof.Order

section
variable {tabs : Tables} {f g : Func} {cv : Cv} {isNew : ID → Bool} {front : ID → List ID}
  {RR : List Val → Mem → List Val → Mem → Prop} {ce ce' : CheckEnv}

/-- **A panicking block entry.** -/
theorem enter_panic (H : Hyp tabs f g cv isNew front RR ce ce') {env : Env} (hE : env.Mono)
    {frS frT : Frame} {b : ID} {i : Nat} (hA : SimAt env tabs f g cv frS frT b i)
    {fb : Block} (hfb : f.block? b = some fb) {e : Panic} {m : Mem}
    (hen : enterBlock env (Ctx.make tabs f) frS fb i = .panic e m) :
    ∃ gb m', g.block? b = some gb ∧ enterBlock env (Ctx.make tabs g) frT gb i = .panic e m' ∧
      Mem.Refines m m' := by
  obtain ⟨gb, ps, oS, og, psT, hgb, B, hbm, -, hps, hsf, hsg, hev, hpsT, hphiT, hentT⟩ :=
    block_parts H hA hfb hen nofun
  have hbm' : b ∈ g.blocks := H.blocks_eq ▸ hbm
  have hndF := H.wf.valuesNodup b fb ⟨hbm, hfb⟩
  have hndG := H.wg.valuesNodup b gb ⟨hbm', hgb⟩
  have hownF := valuesOwn H.wf hbm hfb
  obtain ⟨ofn, oft, ofm⟩ := schedule_topo hownF hndF hsf
  obtain ⟨ogn, -, ogm⟩ := schedule_topo (valuesOwn H.wg hbm' hgb) hndG hsg
  obtain ⟨pS1, -, -, -⟩ := phis_spec hndF hps
  obtain ⟨pre, r, post, G, hof, hpre, hstep⟩ := evalAll_panic_split hev
  have hpren : pre.Nodup := (List.nodup_append.1 (hof ▸ ofn)).1
  have hpret : TopoRem (argsF f) pre := topoRem_prefix (hof ▸ oft)
  obtain ⟨g1, -, g3, g4⟩ := evalAll_spec hpren hpret (by rw [pS1, hA.szS]; rfl) hpre
  have hpreo : ∀ x ∈ pre, x ∈ oS.toList := fun x hx => by
    rw [hof]; exact List.mem_append_left _ hx
  -- the panicking node
  obtain ⟨ur, hur, hevr⟩ : ∃ ur, f.value? r = some ur ∧
      evalValue env (Ctx.make tabs f) G ur = .panic e m := by
    unfold stepV at hstep
    cases h : (Ctx.make tabs f).f.value? r with
    | none => rw [h] at hstep; cases hstep
    | some ur => rw [h] at hstep; exact ⟨ur, h, hstep⟩
  have hrp : prio ur.op ≠ 0 := prio_panicking (evalValue_panic_op hevr)
  have hrof : r ∈ oS.toList := by rw [hof]; simp
  obtain ⟨hrfb, ur', hur', hrph⟩ := (ofm r).1 hrof
  rw [hur] at hur'; cases hur'
  have hnp : npIn (schedNodes f fb).toList r = true :=
    (ZCSE.npIn_sched hownF hndF).2 ⟨hrfb, ur, hur, hrph, hrp⟩
  have hseq : oS.toList.filter (npIn (schedNodes f fb).toList) =
      og.toList.filter (npIn (schedNodes f fb).toList) := by
    obtain ⟨oF, oG, h1, h2, h3⟩ := B.sched
    rw [hsf] at h1; cases h1; rw [hsg] at h2; cases h2; exact h3
  have hrog : r ∈ og.toList := by
    have : r ∈ oS.toList.filter (npIn (schedNodes f fb).toList) := List.mem_filter.2 ⟨hrof, hnp⟩
    rw [hseq] at this; exact (List.mem_filter.1 this).1
  obtain ⟨preT, postT, hogT⟩ := List.append_of_mem hrog
  -- the transfer: what the target evaluates before `r`, the source did
  have hspS := schedule_spec hsf
  have hspT := schedule_spec hsg
  have htr := transfer_rank_ex hspS.topo hspS.pureFirst hspT.topo (fun x => npIn_iff) hseq
    (k := pre.length) (k' := preT.length) (by rw [hof]; simp) (by rw [hogT]; simp) hnp
    (TgtInvalid g) (fun a b hb hab => B.invArgs a b hb hab)
    (fun a y ha hy hay hy' hyi => B.feeds a y ha hy hay hy' hyi)
  have hGk : ∀ a, a ∉ oS.toList → G.regs[a]? = (setPhis ps frS.regs)[a]? :=
    fun a ha => g3 a fun hm => ha (hpreo a hm)
  have hGok : RegsOK (Ctx.make tabs f) G :=
    regsOK_block H hbm hfb hps hA.ok (fun x hx => ((ofm x).1 (hpreo x hx)).1) hpre
  have TH := tgtHyp_of H hA hbm hfb hgb B hps hsf hsg hpsT hphiT (G := G) (by rw [g1]) hGk hGok
  -- the target's source nodes before `r` are before `r` in the source
  have hidx : ∀ x ∈ preT, isNew x = false → ¬ TgtInvalid g x →
      ∃ i < pre.length, oS.toList[i]? = some x := fun x hx hn hxi => by
    have hxog : x ∈ og.toList := by rw [hogT]; exact List.mem_append_left _ hx
    obtain ⟨hxg, w, hw, hph⟩ := (ogm x).1 hxog
    have hxf : x ∈ fb.values := Classical.byContradiction fun h => by
      rw [B.fresh x hxg h] at hn; cases hn
    obtain ⟨u, hu, -, -⟩ := H.wf.valueId b fb ⟨hbm, hfb⟩ x hxf
    have huphi : u.op ≠ .Phi := fun hp => by
      obtain ⟨⟨w', hgu, hsw⟩, -⟩ := B.phiS x hxf u hu hp
      rw [hw] at hgu; cases hgu; exact hph (hsw.1.trans hp)
    have hN : NodeIn (schedNodes f fb).toList x :=
      (nodeIn_schedNodes hownF).2 ⟨hxf, u, hu, huphi⟩
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
    have hjl : j < preT.length := (List.getElem?_eq_some_iff.1 hj).1
    exact htr j x hjl (by rw [hogT, List.getElem?_append_left hjl]; exact hj) hN hxi
  have hsrc : ∀ x ∈ preT, isNew x = false → ¬ TgtInvalid g x → ∃ u y, f.value? x = some u ∧
      G.regs[x]? = some (some y) ∧ evalValue env (Ctx.make tabs f) G u = .ok y :=
    fun x hx hn hxi => by
      obtain ⟨i', hi', hix⟩ := hidx x hx hn hxi
      rw [hof, List.getElem?_append_left hi'] at hix
      exact g4 x (List.mem_of_getElem? hix)
  -- the source arguments of a source node at or before `r` are before `r`
  have hargs : ∀ x i, oS.toList[i]? = some x → i ≤ pre.length → ∀ z, SrcArg f fb x z →
      ∃ u y, f.value? z = some u ∧ G.regs[z]? = some (some y) ∧
        evalValue env (Ctx.make tabs f) G u = .ok y := by
    intro x i hi hle z ⟨hzf, ⟨u, hu, hzu⟩, hzp⟩
    obtain ⟨uz, huz, -, -⟩ := H.wf.valueId b fb ⟨hbm, hfb⟩ z hzf
    have hNz : NodeIn (schedNodes f fb).toList z :=
      (nodeIn_schedNodes hownF).2 ⟨hzf, uz, huz, hzp uz huz⟩
    obtain ⟨hxf, u', hu', hxph⟩ := (ofm x).1 (List.mem_of_getElem? hi)
    rw [hu] at hu'; cases hu'
    have hNx : NodeIn (schedNodes f fb).toList x := (nodeIn_schedNodes hownF).2 ⟨hxf, u, hu, hxph⟩
    have harg : z ∈ argsOf (schedNodes f fb).toList x := by
      rw [argsOf_schedNodes hownF hndF hxf hu hxph]; exact Array.mem_toList_iff.2 hzu
    obtain ⟨iz, hiz⟩ := List.getElem?_of_mem ((hspS.topo.mem z).2 hNz)
    have hlt := hspS.topo.dep_lt (.arg hNz hNx harg) hiz hi
    rw [hof] at hiz
    exact g4 z (mem_of_idx_lt hiz (by omega))
  have hsrcA : ∀ x ∈ preT, isNew x = false → ¬ TgtInvalid g x → ∀ z, SrcArg f fb x z →
      ∃ u y, f.value? z = some u ∧ G.regs[z]? = some (some y) ∧
        evalValue env (Ctx.make tabs f) G u = .ok y := fun x hx hn hxi => by
    obtain ⟨i', hi', hix⟩ := hidx x hx hn hxi
    exact hargs x i' hix (by omega)
  have hrS : oS.toList[pre.length]? = some r := by rw [hof]; simp
  have hreach : ∀ c z, c ∈ fb.values → ¬ TgtInvalid g c → z ∈ preT → ∀ A P Q,
      og.toList = A ++ z :: (P ++ c :: Q) → (∀ y ∈ P, npIn (schedNodes f fb).toList y = false) →
      Reached env tabs f G c ∧ ∀ z, SrcArg f fb c z → ∃ u y, f.value? z = some u ∧
        G.regs[z]? = some (some y) ∧ evalValue env (Ctx.make tabs f) G u = .ok y := by
    intro c z hc hci hz A P Q hA hP
    obtain ⟨A', B', hpre'⟩ := List.append_of_mem hz
    have hog2 : og.toList = A' ++ z :: (B' ++ r :: postT) := by rw [hogT, hpre']; simp
    have hsuf := ecl_suffix_eq (by rw [← hA]; exact ogn) (hA.symm.trans hog2)
    have hcn : isNew c = false := (B.common c hc).2
    rcases ecl_gap hnp hsuf hP with hcB | hcr
    · have hcp : c ∈ preT := by rw [hpre']; exact List.mem_append_right _ (List.mem_cons_of_mem _ hcB)
      refine ⟨fun uc huc => ?_, hsrcA c hcp hcn hci⟩
      obtain ⟨u, y, hu, -, hev⟩ := hsrc c hcp hcn hci
      rw [huc] at hu; cases hu
      exact .inl ⟨y, hev⟩
    · subst hcr
      refine ⟨fun uc huc => ?_, hargs c pre.length hrS (Nat.le_refl _)⟩
      rw [hur] at huc; cases huc
      exact .inr ⟨e, m, hevr⟩
  obtain ⟨T, hT, hI⟩ := tgt_loop hE TH (L := preT) (M := r :: postT) hogT hsrc hsrcA hreach
  have hrn : isNew r = false := (B.common r hrfb).2
  have hob := tgt_next hE TH hogT hI hrn hur (regs_of_panic hevr) hsrc
    (hargs r pre.length hrS (Nat.le_refl _))
  rw [hevr] at hob
  generalize hT' : stepV env (Ctx.make tabs g) T r = rT at hob
  cases hob with
  | panic e hm =>
    rename_i m'
    refine ⟨gb, m', hgb, ?_, hm⟩
    rw [hentT, hogT, evalAll_append, hT]
    simp only
    rw [evalAll_cons, hT']

end

end GoFV.Proof.EC

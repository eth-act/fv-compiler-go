import GoFV.Proof.Pass.ECOk
import GoFV.Proof.Pass.ZCSERank

variable [GoFV.SSA.Sem.Addrs]

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
    (hK : env.FrameKeep) {frS frT : Frame} {b : ID} {i : Nat}
    (hA : SimAt env tabs f g cv frS frT b i)
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
  obtain ⟨g1, -, g3, g4⟩ := evalAll_spec hpren (by exact hpret) (by rw [pS1, hA.szS]; rfl) hpre
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
  -- the transfer: what the target evaluates before `r`, the source did (but values the pass
  -- invalidated or made frame-determined)
  have hspS := schedule_spec hsf
  have hspT := schedule_spec hsg
  have htr := transfer_rank_ex hspS.topo hspS.pureFirst hspT.topo (fun x => npIn_iff) hseq
    (k := pre.length) (k' := preT.length) (by rw [hof]; simp) (by rw [hogT]; simp) hnp
    (fun x => TgtInvalid g x ∨ FrameX f g x)
    (fun a b hb hab hX => hX.elim (fun hi => absurd hi (B.invArgs a b hb hab))
      (B.fxArgs a b hb hab))
    (fun a y ha hy hay hy' hyX => B.feeds a y ha hy hay hy' (fun h => hyX (.inl h))
      (fun h => hyX (.inr h)))
  -- the frame-determined values the source has not evaluated before `r`
  let U : ID → Prop := fun x => FrameX f g x ∧ x ∈ fb.values ∧ x ∉ pre
  have hUF : ∀ z, U z → FrameX f g z ∧ z ∈ gb.values := fun z hz => ⟨hz.1, (B.common z hz.2.1).1⟩
  -- no value of the target's prefix up to `r` depends on one: its first reader would be a
  -- non-pure source node reading it, before `r` in both orders
  have hUdep : ∀ a y j, U a → og.toList[j]? = some y → j ≤ preT.length →
      ¬ Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList) a y := by
    intro a y j ⟨hfx, haf, hap⟩ hj hjk hd
    obtain ⟨ua, hua, -, -⟩ := H.wf.valueId b fb ⟨hbm, hfb⟩ a haf
    have hNa : NodeIn (schedNodes f fb).toList a := by
      obtain ⟨u', -, hu', hop, -⟩ := hfx
      rw [hua] at hu'; cases hu'
      exact (nodeIn_schedNodes hownF).2 ⟨haf, ua, hua, by rw [hop]; decide⟩
    obtain ⟨b, hN'b, hab, hby⟩ := hd.first
    obtain ⟨hNb, hpb, habS⟩ := B.fxArgs a b hN'b hab hfx
    obtain ⟨jb, hjb⟩ := List.getElem?_of_mem ((hspT.topo.mem b).2 hN'b)
    have hjbj : jb ≤ j := by
      rcases hby with rfl | hby
      · exact Nat.le_of_eq (idx_unique ogn hjb hj)
      · exact Nat.le_of_lt (hspT.topo.dep_lt hby hjb hj)
    have hnb : npIn (schedNodes f fb).toList b = true := npIn_iff.2 ⟨hNb, hpb⟩
    obtain ⟨ib, hib⟩ := List.getElem?_of_mem ((hspS.topo.mem b).2 hNb)
    have hibk : ib ≤ pre.length := by
      have hrT : og.toList[preT.length]? = some r := by rw [hogT]; simp
      rcases Nat.lt_or_ge jb preT.length with hlt | hge
      · have hbb : Before (og.toList.filter (npIn (schedNodes f fb).toList)) b r :=
          (before_filter _ hnb hnp og.toList).2 ⟨jb, preT.length, hlt, hjb, hrT⟩
        rw [← hseq] at hbb
        exact Nat.le_of_lt (idx_lt_of_before ofn ((before_filter _ hnb hnp oS.toList).1 hbb) hib
          (by rw [hof]; simp))
      · have : jb = preT.length := by omega
        subst this
        rw [hrT] at hjb; cases hjb
        exact Nat.le_of_eq (idx_unique ofn hib (by rw [hof]; simp))
    obtain ⟨ia, hia⟩ := List.getElem?_of_mem ((hspS.topo.mem a).2 hNa)
    have hlt := hspS.topo.dep_lt (.arg hNa hNb habS) hia hib
    rw [hof] at hia
    exact hap (mem_of_idx_lt hia (by omega))
  have hGk : ∀ a, a ∉ oS.toList → G.regs[a]? = (setPhis ps frS.regs)[a]? :=
    fun a ha => g3 a fun hm => ha (hpreo a hm)
  have hGok : RegsOK (Ctx.make tabs f) G :=
    regsOK_block H hbm hfb hps hA.ok (fun x hx => ((ofm x).1 (hpreo x hx)).1) hpre
  have hGq := ecQ_prefix hK H.wf hbm hfb hA.slots hps (fun x hx => ((ofm x).1 (hpreo x hx)).1) hpre
  have TH := tgtHyp_of H hA hbm hfb hgb B hps hsf hsg hpsT hphiT (G := G) (by rw [g1]) hGk hGok
    (ecQ_memQ hGq)
  -- the target's source nodes before `r` are before `r` in the source (but those of `U`)
  have hidx : ∀ x ∈ preT, isNew x = false → ¬ TgtInvalid g x → ¬ U x →
      ∃ i < pre.length, oS.toList[i]? = some x := fun x hx hn hxi hxU => by
    have hxog : x ∈ og.toList := by rw [hogT]; exact List.mem_append_left _ hx
    obtain ⟨hxg, w, hw, hph⟩ := (ogm x).1 hxog
    have hxf : x ∈ fb.values := Classical.byContradiction fun h => by
      rw [B.fresh x hxg h] at hn; cases hn
    by_cases hfx : FrameX f g x
    · have hxp : x ∈ pre := Classical.byContradiction fun h => hxU ⟨hfx, hxf, h⟩
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hxp
      have hil : i < pre.length := (List.getElem?_eq_some_iff.1 hi).1
      exact ⟨i, hil, by rw [hof, List.getElem?_append_left hil]; exact hi⟩
    obtain ⟨u, hu, -, -⟩ := H.wf.valueId b fb ⟨hbm, hfb⟩ x hxf
    have huphi : u.op ≠ .Phi := fun hp => by
      obtain ⟨⟨w', hgu, hsw⟩, -⟩ := B.phiS x hxf u hu hp
      rw [hw] at hgu; cases hgu; exact hph (hsw.1.trans hp)
    have hN : NodeIn (schedNodes f fb).toList x :=
      (nodeIn_schedNodes hownF).2 ⟨hxf, u, hu, huphi⟩
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
    have hjl : j < preT.length := (List.getElem?_eq_some_iff.1 hj).1
    exact htr j x hjl (by rw [hogT, List.getElem?_append_left hjl]; exact hj) hN
      (fun h => h.elim hxi hfx)
  have hsrc : ∀ x ∈ preT, isNew x = false → ¬ TgtInvalid g x → ¬ U x → ∃ u y,
      f.value? x = some u ∧ G.regs[x]? = some (some y) ∧ evalValue env (Ctx.make tabs f) G u = .ok y :=
    fun x hx hn hxi hxU => by
      obtain ⟨i', hi', hix⟩ := hidx x hx hn hxi hxU
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
  have hsrcA : ∀ x ∈ preT, isNew x = false → ¬ TgtInvalid g x → ¬ U x → ∀ z, SrcArg f fb x z →
      ∃ u y, f.value? z = some u ∧ G.regs[z]? = some (some y) ∧
        evalValue env (Ctx.make tabs f) G u = .ok y := fun x hx hn hxi hxU => by
    obtain ⟨i', hi', hix⟩ := hidx x hx hn hxi hxU
    exact hargs x i' hix (by omega)
  have hrS : oS.toList[pre.length]? = some r := by rw [hof]; simp
  have hreach : ∀ c z, c ∈ fb.values → ¬ TgtInvalid g c → ¬ FrameX f g c → z ∈ preT → ∀ A P Q,
      og.toList = A ++ z :: (P ++ c :: Q) → (∀ y ∈ P, npIn (schedNodes f fb).toList y = false) →
      Reached env tabs f G c ∧ ∀ z, SrcArg f fb c z → ∃ u y, f.value? z = some u ∧
        G.regs[z]? = some (some y) ∧ evalValue env (Ctx.make tabs f) G u = .ok y := by
    intro c z hc hci hcx hz A P Q hA hP
    obtain ⟨A', B', hpre'⟩ := List.append_of_mem hz
    have hog2 : og.toList = A' ++ z :: (B' ++ r :: postT) := by rw [hogT, hpre']; simp
    have hsuf := ecl_suffix_eq (by rw [← hA]; exact ogn) (hA.symm.trans hog2)
    have hcn : isNew c = false := (B.common c hc).2
    have hcU : ¬ U c := fun h => hcx h.1
    rcases ecl_gap hnp hsuf hP with hcB | hcr
    · have hcp : c ∈ preT := by rw [hpre']; exact List.mem_append_right _ (List.mem_cons_of_mem _ hcB)
      refine ⟨fun uc huc => ?_, hsrcA c hcp hcn hci hcU⟩
      obtain ⟨u, y, hu, -, hev⟩ := hsrc c hcp hcn hci hcU
      rw [huc] at hu; cases hu
      exact .inl ⟨y, hev⟩
    · subst hcr
      refine ⟨fun uc huc => ?_, hargs c pre.length hrS (Nat.le_refl _)⟩
      rw [hur] at huc; cases huc
      exact .inr ⟨e, m, hevr⟩
  -- no new value of the return runs before `r` (no source non-pure node comes after one)
  have hretP : ∀ z ∈ preT, RetAnchored tabs f g cv isNew fb gb z → ∀ c, fb.controls[0]? = some c →
      EcSrcHolds env tabs f G c ∧ ∀ y, G.regs[c]? = some (some y) → ∃ rs m, retOf y = some (rs, m) := by
    intro z hz hra
    obtain ⟨-, -, -, -, -, -, -, -, hsch⟩ := hra
    obtain ⟨A', B', hpre'⟩ := List.append_of_mem hz
    have h := hsch og hsg A' (B' ++ r :: postT) (by rw [hogT, hpre']; simp) r (by simp)
    rw [hnp] at h; cases h
  obtain ⟨T, hT, hI⟩ := tgt_loop hE TH (L := preT) (M := r :: postT) hogT hUF
    (fun a y hU hy hd => by
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hy
      have hjl : j < preT.length := (List.getElem?_eq_some_iff.1 hj).1
      exact hUdep a y j hU (by rw [hogT, List.getElem?_append_left hjl]; exact hj)
        (Nat.le_of_lt hjl) hd)
    hsrc hsrcA hreach hretP
  have hrn : isNew r = false := (B.common r hrfb).2
  have hob := tgt_next hE TH hogT hI hrn hur (regs_of_panic hevr) hUF
    (fun a hU => hUdep a r preT.length hU (by rw [hogT]; simp) (Nat.le_refl _)) hsrc
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

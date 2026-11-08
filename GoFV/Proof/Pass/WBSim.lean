import GoFV.Proof.Pass.WBPanic
import GoFV.Proof.CheckFacts
import GoFV.Proof.TabsAgree

variable [GoFV.SSA.Sem.Addrs]

/-!
# writebarrier refines its input (issue #36)

Macro-step simulation (`runLoop_simIH`): one source block entry is simulated by the target's run
through the block's chain (`SimAt` at both ends). A block entry that succeeds: the chain walks
to its last segment (`walk_to`, `seg_enter`) with every value's source facts (the source
evaluated the whole block), the last segment ends like the source block (`stepTerm_same` on the
held controls), and the frames are related again (`final_held`, `lazy_after`). A block entry
that panics: `chain_panic`.

`writebarrier_refines`: on inputs whose memory holds a defined, read-only write-barrier flag and
no write-barrier buffer, and environments whose contracts keep that (`WbPre`), a result that
`writebarrierChecked` accepts refines its input.
-/

namespace GoFV.Proof.WB

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Opt GoFV.Opt.WBCheck GoFV.Proof
open GoFV.Proof.MemInv (SInv ContractsOK sinv_enter sinv_entry)

/-- The inputs of `writebarrier_refines`: the memory with the global image has a defined,
read-only write-barrier flag and no write-barrier buffer, the environment's contracts keep
that, and its write-barrier helpers are the runtime's and do not spill into the caller's frame
(`WbHelpers`, a trusted assumption). -/
def WbPre (env : Env) (_args : List Val) (mem : Mem) : Prop :=
  MemOK (addGlobals env mem) ∧ ContractsOK MemOK env ∧ WbHelpers env

/-- The global facts of an accepted `writebarrier` result. -/
structure Glob (c : WBCheck.Ctx) (ce ce' : CheckEnv) : Prop where
  ctx : ctxOf c.tabs c.f c.g = some c
  wf : WF ce c.f
  wg : WF ce' c.g
  cert : CertOK c.f
  entry : c.g.entry = c.f.entry
  own : c.g.ownAux = c.f.ownAux
  memTy : memTyOK c.tabs c.f = true
  all : ∀ b ∈ c.f.blocks, c.blockOK b = true

theorem stepTerm_ne_panic {fr : Frame} {b : Block} {e : Panic} {m : Mem} :
    stepTerm fr b ≠ .panic e m := by
  intro h
  have hsp : ∀ k, succ b k ≠ .panic e m := fun k h => by
    unfold succ at h; cases hk : b.succs[k]? <;> rw [hk] at h <;> cases h
  unfold stepTerm at h
  cases hb : b.kind <;> simp only [hb] at h
  all_goals first
    | (cases h; done)
    | exact hsp _ h
    | (cases hc0 : Sem.control fr b 0 with
        | ok v =>
          rw [hc0] at h
          simp only [bind, Res.bind] at h
          split at h <;> first | (cases h; done) | exact hsp _ h | (split at h <;> first
            | (cases h; done) | (split at h <;> cases h))
        | panic e' m' =>
          unfold Sem.control at hc0
          split at hc0
          · unfold Res.ofOption at hc0; split at hc0 <;> cases hc0
          · cases hc0
        | stuck msg => rw [hc0] at h; cases h)

theorem blockStep_ret {env : Env} {ctx : Sem.Ctx} {F F' : Frame} {bid : ID} {C : Block} {e : Nat}
    {rs : List Val} {m : Mem} (hC : ctx.f.block? bid = some C)
    (hen : enterBlock env ctx F C e = .ok F') (hst : stepTerm F' C = .ok (.ret rs m)) :
    blockStep env ctx F bid e = .ret rs m := by
  unfold blockStep
  simp only [hC, hen, hst]

theorem fr_trans {frS G T : Frame} (hT : T = { frS with regs := T.regs })
    (hG : G = { frS with regs := G.regs }) : T = { G with regs := T.regs } := by
  rw [hG]; exact hT

theorem blockOK_some {c : WBCheck.Ctx} {b : ID} (h : c.blockOK b = true) :
    ∃ B rs l, c.f.block? b = some B ∧ chainRuns? c.f c.g b = some (rs, l) := by
  unfold Ctx.blockOK at h
  split at h
  · rename_i B rs l hB hch; exact ⟨B, rs, l, hB, hch⟩
  · cases h

namespace Glob

variable {c : WBCheck.Ctx} {ce ce' : CheckEnv}

theorem setup (G : Glob c ce ce') {b : ID} (hb : b ∈ c.f.blocks) :
    ∃ B rs l, Setup c b B rs l := by
  obtain ⟨B, rs, l, hB, hch⟩ := blockOK_some (G.all b hb)
  exact ⟨B, rs, l, ⟨G.ctx, ⟨ce, G.wf⟩, ⟨ce', G.wg⟩, G.entry, G.own, G.memTy, hb, hB, hch,
    G.all b hb⟩⟩

end Glob

namespace Setup

variable {c : WBCheck.Ctx} {b : ID} {B : Block} {rs : List Run} {l : ID}

/-- A run's stores and dropped nil check: non-`Phi` values of `B`, at least one store. -/
theorem run_facts (S : Setup c b B rs l) {j : Nat} {r : Run} (hr : rs[j]? = some r) :
    0 < r.src.length ∧
    (∀ s ∈ r.src, s ∈ B.values ∧ ∀ u, c.f.value? s = some u → u.op ≠ .Phi) ∧
    (∀ n ∈ ncsOf c r, n ∈ B.values ∧ ∀ u, c.f.value? n = some u → u.op ≠ .Phi) := by
  have hok := (blockOK_spec S.ok S.hB S.ch).2.2.2.2.1 j r hr
  obtain ⟨-, -, -, -, -, -, hpos, -, -, -, -, -, -, -, -, hsrc, hnc⟩ := runOK_spec hok
  obtain ⟨-, -, -, hsrcop, -⟩ := runOf_spec ((chainRuns_spec S.ch).1 j r hr).2.2.2
  refine ⟨hpos, fun s hs => ⟨(hsrc s hs).1, fun u hu => ?_⟩, fun n hn => ?_⟩
  · obtain ⟨k, hk⟩ := List.getElem?_of_mem hs
    obtain ⟨u', hu', hop, -⟩ := hsrcop k s hk
    rw [hu] at hu'; cases hu'
    rcases hop with hop | hop | hop | hop | hop <;> rw [hop] <;> exact fun h => by cases h
  · unfold ncsOf at hn
    split at hn
    · rename_i n' hn'
      split at hn
      · simp at hn
      · rename_i hK
        simp only [List.mem_singleton] at hn
        subst hn
        obtain ⟨hB, u, hu, hop⟩ := hnc _ hn'
        exact ⟨hB.resolve_right hK,
          fun u' hu' => by rw [hu] at hu'; cases hu'; rw [hop]; exact fun h => by cases h⟩
    · simp at hn

/-- A value of `B` that is the flag address or constant is not a `Phi`. -/
theorem lazy_nonphi (S : Setup c b B rs l) {a : ID} (ha : a ∈ B.values)
    (hl : c.isWbaddr a = true ∨ c.isConst0 a = true) {u : Value} (hu : c.f.value? a = some u) :
    u.op ≠ .Phi := by
  have hcov := ((blockOK_spec S.ok S.hB S.ch).2.2.2.2.2.1 a ha)
  by_cases hK : c.K.getD a false = true
  · obtain ⟨-, -, -, hKe, -, hl'⟩ := ctxOf_spec S.ctx
    rw [hKe] at hK
    obtain ⟨u', w, hu', hw, hsame, -⟩ := keptMarks_spec hK
    rw [hu] at hu'; cases hu'
    have hop : w.op = u.op := by
      simp only [sameV, Bool.and_eq_true, beq_iff_eq] at hsame
      exact hsame.1.1.1.1.2.symm
    cases hz : c.lazy with
    | none =>
      simp only [Ctx.isWbaddr, Ctx.isConst0, hz, Option.any_none] at hl
      rcases hl with h | h <;> cases h
    | some p =>
      obtain ⟨wa, c0⟩ := p
      rw [hz] at hl'
      obtain ⟨⟨w1, hw1, hop1, -⟩, ⟨w2, hw2, hop2, -⟩, -⟩ := lazyOK_some hl'
      simp only [Ctx.isWbaddr, Ctx.isConst0, hz, Option.any_some, beq_iff_eq] at hl
      rw [← hop]
      rcases hl with rfl | rfl
      · rw [hw] at hw1; cases hw1; rw [hop1]; exact fun h => by cases h
      · rw [hw] at hw2; cases hw2; rw [hop2]; exact fun h => by cases h
  · rcases hcov.2 (by simpa using hK) with ⟨r, hr, hx⟩ | ⟨r, hr, hn⟩
    · obtain ⟨j, hj⟩ := List.getElem?_of_mem hr
      exact ((S.run_facts hj).2.1 a hx).2 u hu
    · obtain ⟨j, hj⟩ := List.getElem?_of_mem hr
      have hK' : c.K.getD a false = false := by simpa using hK
      exact ((S.run_facts hj).2.2 a (by simp [ncsOf, hn, hK'])).2 u hu

/-- **Held registers after the chain.** -/
theorem final_held (S : Setup c b B rs l) (hall : ∀ b' ∈ c.f.blocks, c.blockOK b' = true)
    {env : Env} {frS frT : Frame} {i : Nat} (hA : SimAt env c frS frT b i) {G : Frame}
    (hG : GrOK c B rs G frS) (hGo : ∀ z, z ∉ B.values → G.regs[z]? = frS.regs[z]?)
    (hdef : ∀ a ∈ B.values, ∃ y, G.regs[a]? = some (some y)) {T : Frame}
    (hR : Regs c b B rs G frS frT (rs.length + 1) T) :
    ∀ a, c.held a = true → T.regs[a]? = G.regs[a]? := by
  intro a hh
  by_cases hin : ∃ j, InSeg c b rs j a
  · obtain ⟨j, hj⟩ := hin
    have hjl : j < rs.length + 1 := by
      obtain ⟨s, hs, -⟩ := hj
      have := (List.getElem?_eq_some_iff.1 hs).1
      rw [segs_length] at this; exact this
    obtain ⟨z, hz, hq⟩ := hR.avail a (.inr (.inl ⟨j, hjl, hj⟩))
    obtain ⟨y, hy⟩ := hdef a (S.held_seg hj hh)
    rw [hz, hy, hG.held a z y hh hq hy]
  · have hnT : ∀ j, ¬ InT c rs j a := fun j h => S.held_t h hh
    have hnS : ∀ j, ¬ InSeg c b rs j a := fun j h => hin ⟨j, h⟩
    have haB : a ∉ B.values := fun h => hin (S.held_listed hall hh h)
    rw [hR.out a hnS hnT, hA.held a hh, hGo a haB]

/-- The flag address, constant and `SB` after the chain. -/
theorem lazy_after (S : Setup c b B rs l) {env : Env} {frS frT : Frame} {i : Nat}
    (hA : SimAt env c frS frT b i) {G T : Frame}
    (hR : Regs c b B rs G frS frT (rs.length + 1) T) : LazyRegs c T := by
  have hEg : ∀ a, (c.isWbaddr a = true ∨ c.isConst0 a = true ∨ c.isSb a = true) →
      c.f.entry ∈ c.g.blocks := fun a h => (S.entry_mem h).2
  have hs0 : b = c.f.entry → (segsOf b rs)[0]? = some c.f.entry := fun hb => by rw [← hb]; rfl
  have h0 : 0 < rs.length + 1 := Nat.succ_pos _
  have hnot : b ≠ c.f.entry → ∀ a, a ∈ vals c.g c.f.entry → c.f.entry ∈ c.g.blocks →
      (∀ j, ¬ InSeg c b rs j a) ∧ (∀ j, ¬ InT c rs j a) := by
    intro hb a ha hEg
    refine ⟨fun j ⟨s, hs, has⟩ => ?_, fun j ⟨r, hr, har⟩ => ?_⟩
    · obtain ⟨-, -, -, hsg, -⟩ := S.seg_block hs
      have := S.listed_once hsg hEg has ha
      exact S.entry_not_chain hb s (List.mem_append_left _ (List.mem_of_getElem? hs)) this
    · obtain ⟨-, -, -, htg, -⟩ := S.t_block hr
      have := S.listed_once htg hEg har ha
      exact S.entry_not_chain hb r.sp.t
        (List.mem_append_right _ (List.mem_map.2 ⟨r, List.mem_of_getElem? hr, rfl⟩)) this
  refine ⟨fun wa c0 hz => ?_, fun s hs => ?_⟩
  · have hwa : c.isWbaddr wa = true := by simp [Ctx.isWbaddr, hz]
    have hc0 : c.isConst0 c0 = true := by simp [Ctx.isConst0, hz]
    have hrw : c.roleOf rs wa = .wbaddr := roleOf_wbaddr hwa
    have hrc : c.roleOf rs c0 = .const0 := roleOf_const0 hc0 (isWbaddr_of_const0 S.ctx hc0)
    obtain ⟨hwaE, hc0E, hEg⟩ := S.lazy_entry hz
    by_cases hb : b = c.f.entry
    · obtain ⟨z1, hz1, hq1⟩ := hR.avail wa (.inr (.inl ⟨0, h0, _, hs0 hb, hwaE⟩))
      obtain ⟨z2, hz2, hq2⟩ := hR.avail c0 (.inr (.inl ⟨0, h0, _, hs0 hb, hc0E⟩))
      simp only [QR, hrw] at hq1
      simp only [QR, hrc] at hq2
      subst hq1; subst hq2
      exact ⟨hz1, hz2⟩
    · obtain ⟨h1, h2⟩ := (hA.lazy hb).1 wa c0 hz
      refine ⟨?_, ?_⟩
      · rw [hR.out wa (hnot hb wa hwaE hEg).1 (hnot hb wa hwaE hEg).2]; exact h1
      · rw [hR.out c0 (hnot hb c0 hc0E hEg).1 (hnot hb c0 hc0E hEg).2]; exact h2
  · have hl : c.isSb s = true := by simp [Ctx.isSb, hs]
    have hsE := (S.sb_entry hl).1
    have hEg' := hEg s (.inr (.inr hl))
    by_cases hb : b = c.f.entry
    · obtain ⟨z, hz, -⟩ := hR.avail s (.inr (.inl ⟨0, h0, _, hs0 hb, hsE⟩))
      exact ⟨z, hz⟩
    · rw [hR.out s (hnot hb s hsE hEg').1 (hnot hb s hsE hEg').2]
      exact (hA.lazy hb).2 s hs

/-- **A block entry that succeeds.** -/
theorem chain_ok (S : Setup c b B rs l) (hall : ∀ b' ∈ c.f.blocks, c.blockOK b' = true)
    {ce : CheckEnv} (hwf : WF ce c.f) (hcf : CertOK c.f) {env : Env} (hE : ContractsOK MemOK env)
    {frS frT : Frame} {i : Nat} (hA : SimAt env c frS frT b i) {G : Frame}
    (hen : enterBlock env (Ctx.make c.tabs c.f) frS B i = .ok G) :
    ∃ n F eL L T, (∀ fuel, runLoop env (Ctx.make c.tabs c.g) (fuel + n) frT b i =
        runLoop env (Ctx.make c.tabs c.g) fuel F l eL) ∧ c.g.block? l = some L ∧
      enterBlock env (Ctx.make c.tabs c.g) F L eL = .ok T ∧
      (∀ nx, stepTerm G B = .ok nx → stepTerm T L = .ok nx) ∧
      (∀ e, stepTerm G B = .ok (.goto e) → SimAt env c G T e.b e.i) := by
  obtain ⟨hGf, hGs, hGo, hGv, hGp⟩ := enter_ok_facts hwf S.hb S.hB hA.sizeS hen
  have hsinv : SInv MemOK G := sinv_enter memOK_pred hE hwf S.memTy S.hb S.hB hA.sinv hen
  have hP : ∀ x ∈ B.values, ∀ u, c.f.value? x = some u → u.op ≠ .Phi → Ev env c G x :=
    fun x hx u hu hp => by
      obtain ⟨y, hy, hev⟩ := hGv x hx u hu hp
      exact ⟨u, y, hu, hy, hev⟩
  have hvx : ∀ x ∈ B.values, ∃ u, c.f.value? x = some u := fun x hx => by
    obtain ⟨u, hu, -, -⟩ := hwf.valueId b B ⟨S.hb, S.hB⟩ x hx
    exact ⟨u, hu⟩
  have hoe : OutEv env c B G := S.outEv_of hwf hcf hA hGf hGo
  have hO : OutDef c B G := by
    rintro a - - ⟨y, hy, u, hu, hp, ha | ⟨y', hy', hy'B, u', hu', hp', ha'⟩⟩
    · obtain ⟨z, -, hev⟩ := hGv y hy u hu hp
      exact evalValue_args_def (fun msg h => by rw [hev] at h; cases h) a ha
    · obtain ⟨u'', z, hu'', -, hev⟩ := hoe y' hy'B ⟨y, hy, u, hu, hp, hy'⟩ u' hu' hp'
      rw [hu'] at hu''; cases hu''
      exact evalValue_args_def (fun msg h => by rw [hev] at h; cases h) a ha'
  have hty : Typed (Ctx.make c.tabs c.f) G := typed_enter hwf S.hb S.hB hA.sizeS hA.typed hen
  have hG : GrOK c B rs G frS := S.grOK hall hA hGf hsinv hGo
    (fun _ a ha y _ hl => by
      obtain ⟨u, hu⟩ := hvx a ha
      exact hP a ha u hu (S.lazy_nonphi ha hl hu)) hO hty
  have hdef : ∀ a ∈ B.values, ∃ y, G.regs[a]? = some (some y) := fun a ha => by
    obtain ⟨u, hu⟩ := hvx a ha
    by_cases hp : u.op = .Phi
    · obtain ⟨-, y, -, -, h⟩ := hGp a ha u hu hp; exact ⟨_, h⟩
    · obtain ⟨y, hy, -⟩ := hGv a ha u hu hp; exact ⟨y, hy⟩
  -- the runs' first stores were evaluated
  have hrun : ∀ (j : Nat) (r : Run), rs[j]? = some r →
      (∀ s ∈ r.src, s ∈ B.values ∧ ∀ u, c.f.value? s = some u → u.op ≠ .Phi) ∧
      (∀ n ∈ ncsOf c r, n ∈ B.values ∧ ∀ u, c.f.value? n = some u → u.op ≠ .Phi) :=
    fun j r hr => (S.run_facts hr).2
  have hM : ∀ j, j < rs.length → ∃ M, RunMem G rs j M := fun j hj => by
    obtain ⟨r, hr⟩ : ∃ r, rs[j]? = some r := ⟨rs[j], List.getElem?_eq_getElem hj⟩
    obtain ⟨s0, hs0⟩ : ∃ s0, r.src[0]? = some s0 :=
      ⟨_, List.getElem?_eq_getElem (S.run_facts hr).1⟩
    obtain ⟨hs0B, hs0p⟩ := (hrun j r hr).1 s0 (List.mem_of_getElem? hs0)
    obtain ⟨u, hu⟩ := hvx s0 hs0B
    exact S.runMem_of_ev hr hs0 (hP s0 hs0B u hu (hs0p u hu))
  have hcov : ∀ j x, (InSeg c b rs j x ∨ InT c rs j x) → Cov env c rs G x := by
    intro j x hx
    refine S.cov_intro (P := fun x => x ∈ B.values ∧ ∀ u, c.f.value? x = some u → u.op ≠ .Phi)
      (fun x ⟨hx, hp⟩ => by obtain ⟨u, hu⟩ := hvx x hx; exact hP x hx u hu (hp u hu))
      (fun _ a _ _ _ _ ha hap => ⟨ha, hap⟩) hoe hA.wbh ?_ ?_ ?_
    · intro hrole hK hp
      have hh : c.held x = true := by simp [Ctx.held, hK]
      rcases hx with hx | hx
      · exact ⟨S.held_seg hx hh, hp⟩
      · exact (S.held_t hx hh).elim
    · intro j' _ r hr; exact hrun j' r hr
    · intro j' hw
      obtain ⟨r, hr, -⟩ := roleOf_then (o := .WB) (j := j') (by rw [hw]; rfl)
      exact hM j' (List.getElem?_eq_some_iff.1 hr).1
  obtain ⟨n, F, eL, s, hs, hwalk, hR, hPh⟩ := S.walk_to hG (S.regs0 hall hA hG hGo)
    (S.phis0 hA hGp) rs.length (Nat.le_refl _) (fun j x _ hx => hcov j x hx) hM
  obtain ⟨L, hL, hls, hk, hctl, hsu, hheld⟩ := S.last_block
  obtain rfl : s = l := Option.some.inj (hs.symm.trans hls)
  obtain ⟨C, T, hC, henT, -, hRT⟩ := S.seg_enter hG hs hR hPh
    (fun x hx => hcov rs.length x (.inl hx))
  rw [hL] at hC; cases hC
  have hfin := S.final_held hall hA hG hGo hdef hRT
  refine ⟨n, F, eL, L, T, hwalk, hL, henT, fun nx hst => ?_, fun e hst => ?_⟩
  · exact stepTerm_same hk hctl hsu (fun x hx => hfin x (hheld x hx)) hst
  · have he : e ∈ B.succs := stepTerm_goto_mem hst
    obtain ⟨hD, -, -⟩ := dinv_enter hwf hcf S.hb S.hB hA.sizeS (pre_strict hcf hA.pre) hen
    refine ⟨.inr ⟨b, B, S.hb, S.hB, (pre_tree hwf hcf hA.pre).2, by cases e; exact he, hD⟩,
      by rw [hGs, hA.sizeS], hRT.size, fr_trans hRT.fr hGf, fun a hh => hfin a hh, hsinv,
      fun _ => S.lazy_after hA hRT, fun hent => ?_, hA.wbh, hty⟩
    exfalso
    obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 he
    obtain ⟨-, E, hE', hpe⟩ := hwf.succLink b B ⟨S.hb, S.hB⟩ j e hj
    rw [hent] at hE'
    have := hwf.entryPreds E hE'
    rw [Array.getElem?_eq_none (by omega)] at hpe
    cases hpe

end Setup

/-- The simulation relation. -/
def R (env : Env) (c : WBCheck.Ctx) (frS : Frame) (bS : ID) (iS : Nat) (frT : Frame) (bT : ID)
    (iT : Nat) : Prop :=
  bT = bS ∧ iT = iS ∧ SimAt env c frS frT bS iS

/-- **One macro step.** -/
theorem step {c : WBCheck.Ctx} {ce ce' : CheckEnv} (hGl : Glob c ce ce') {env : Env}
    (hE : ContractsOK MemOK env) (n : Nat)
    (ih : SimUpTo env (Ctx.make c.tabs c.f) (Ctx.make c.tabs c.g) (R env c) n)
    (frS : Frame) (bS : ID) (iS : Nat) (frT : Frame) (bT : ID) (iT : Nat)
    (hR : R env c frS bS iS frT bT iT)
    (hd : (runLoop env (Ctx.make c.tabs c.f) (n + 1) frS bS iS).Defined) :
    ∃ fuelT, LoopRefines Eq
      (runLoop env (Ctx.make c.tabs c.f) (n + 1) frS bS iS)
      (runLoop env (Ctx.make c.tabs c.g) fuelT frT bT iT) := by
  obtain ⟨rfl, rfl, hA⟩ := hR
  obtain ⟨hb, -⟩ := pre_tree hGl.wf hGl.cert hA.pre
  obtain ⟨B, rs, l, S⟩ := hGl.setup hb
  rw [runLoop_succ] at hd ⊢
  simp only [show (Ctx.make c.tabs c.f).f = c.f from rfl, S.hB] at hd ⊢
  cases hen : enterBlock env (Ctx.make c.tabs c.f) frS B iT with
  | stuck msg => rw [hen] at hd; exact hd.elim
  | panic e m =>
    obtain ⟨n', hn'⟩ := S.chain_panic hGl.all hGl.wf hGl.cert hE hA hen
    exact ⟨n', by rw [hn']; simp only; exact LoopRefines.panicked_refl e m⟩
  | ok G =>
    rw [hen] at hd
    simp only at hd ⊢
    obtain ⟨n', F, eL, L, T, hwalk, hL, henT, hst, hsim⟩ :=
      S.chain_ok hGl.all hGl.wf hGl.cert hE hA hen
    cases hs : stepTerm G B with
    | stuck msg => rw [hs] at hd; exact hd.elim
    | panic e m => exact absurd hs stepTerm_ne_panic
    | ok nx =>
      cases nx with
      | goto e =>
        rw [hs] at hd
        simp only at hd ⊢
        obtain ⟨fT, hfT⟩ := ih n (Nat.le_refl _) G e.b e.i T e.b e.i ⟨rfl, rfl, hsim e hs⟩ hd
        refine ⟨fT + 1 + n', ?_⟩
        rw [hwalk (fT + 1), runLoop_goto (blockStep_of (ctx := Ctx.make c.tabs c.g) hL henT
          (hst _ hs))]
        exact hfT
      | ret rs' m =>
        refine ⟨0 + 1 + n', ?_⟩
        rw [hwalk (0 + 1), runLoop_ret (blockStep_ret (ctx := Ctx.make c.tabs c.g) hL henT
          (hst _ hs))]
        exact LoopRefines.refl trivial

/-- A held value is a value of both functions. -/
private theorem held_lt {c : WBCheck.Ctx} {ce ce' : CheckEnv} (hGl : Glob c ce ce') {a : ID}
    (hh : c.held a = true) : a < c.f.valueTab.size ∧ a < c.g.valueTab.size := by
  unfold Ctx.held at hh
  simp only [Bool.or_eq_true] at hh
  rcases hh with hK | hL
  · rw [(ctxOf_spec hGl.ctx).2.2.2.1] at hK
    obtain ⟨u, w, hu, hw, -⟩ := keptMarks_spec hK
    exact ⟨lt_of_value? hu, lt_of_value? hw⟩
  · rw [(ctxOf_spec hGl.ctx).2.2.2.2.1] at hL
    obtain ⟨b, hb, rs', l', hch', r, hr, hlast⟩ := lastMarks_spec hL
    obtain ⟨B, rs, l, S⟩ := hGl.setup hb
    rw [S.ch] at hch'
    simp only [Option.some.injEq, Prod.mk.injEq] at hch'
    obtain ⟨rfl, rfl⟩ := hch'
    have bo := blockOK_spec S.ok S.hB S.ch
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hr
    obtain ⟨-, h2, -, -, -, -, -, hlv, -, -, -, -, -, -, -, hsrc, -⟩ :=
      runOK_spec (bo.2.2.2.2.1 j r hj)
    obtain ⟨-, -, hgl, -⟩ := runOf_spec ((chainRuns_spec S.ch).1 j r hj).2.2.2
    have haB : a ∈ B.values := by
      rw [← hlast]; exact (hsrc _ (List.mem_of_getLast? hgl)).1
    obtain ⟨u, hu, -⟩ := hGl.wf.valueId b B ⟨hb, S.hB⟩ a haB
    have hes : r.sp.e ∈ c.g.blocks :=
      bo.2.2.2.1 _ (List.mem_append_left _ (List.mem_of_getElem? h2))
    obtain ⟨E, hE, -⟩ := hGl.wg.blockId _ hes
    have haE : a ∈ E.values := by rw [← vals_of hE, ← hlast]; exact hlv
    obtain ⟨w, hw, -⟩ := hGl.wg.valueId _ E ⟨hes, hE⟩ a haE
    exact ⟨lt_of_value? hu, lt_of_value? hw⟩

/-- **The accepted results refine their inputs.** -/
theorem refines_of_glob {c : WBCheck.Ctx} {ce ce' : CheckEnv} (hGl : Glob c ce ce') :
    RefinesFrom WbPre c.tabs c.g c.tabs c.f := by
  have hpar : (Ctx.make c.tabs c.g).params = (Ctx.make c.tabs c.f).params := by
    simp only [Ctx.make, abiParams, hGl.own]
  have houts : (Ctx.make c.tabs c.g).outs = (Ctx.make c.tabs c.f).outs := by
    simp only [Ctx.make, abiParams, hGl.own]
  intro env args mem hpre fuel hd
  unfold run runCtx at hd ⊢
  rw [hpar]
  split
  · rename_i hn; simp only [hn] at hd; exact hd.elim
  · rename_i hn
    simp only [hn] at hd
    rw [AtomSim.entryFrame_eq hGl.own.symm, houts,
      show (Ctx.make c.tabs c.g).act = (Ctx.make c.tabs c.f).act from rfl,
      show (Ctx.make c.tabs c.g).f.entry = c.f.entry from hGl.entry]
    have hA0 : SimAt env c (entryFrame env (Ctx.make c.tabs c.f) args mem)
        { entryFrame env (Ctx.make c.tabs c.f) args mem with
          regs := Array.replicate c.g.valueTab.size none } c.f.entry 0 := by
      refine ⟨.inl rfl, by simp [entryFrame, Ctx.make], by simp, rfl, fun a hh => ?_,
        sinv_entry memOK_set hpre.1, fun h => absurd rfl h, fun _ a y h => ?_, hpre.2.2,
        typed_replicate _ _ _ rfl⟩
      · obtain ⟨h1, h2⟩ := held_lt hGl hh
        simp only [entryFrame, Ctx.make, Array.getElem?_replicate, h1, h2, ↓reduceIte]
      · simp only [entryFrame, Array.getElem?_replicate] at h
        split at h <;> simp at h
    obtain ⟨fuelT, h⟩ := runLoop_simIH (ctxS := Ctx.make c.tabs c.f) (ctxT := Ctx.make c.tabs c.g)
      (R env c) (fun n ih frS bS iS frT bT iT hR hd' =>
        step hGl hpre.2.1 n ih frS bS iS frT bT iT hR hd') fuel _ c.f.entry 0 _ c.f.entry 0
      ⟨rfl, rfl, hA0⟩ (finish_defined hd)
    exact ⟨fuelT, finish_refines hd h⟩

end GoFV.Proof.WB

namespace GoFV.Proof

open GoFV.SSA GoFV.Opt

/-- **writebarrier refines its input** on `WbPre` inputs, when the checker accepts its result
(`writebarrierChecked`) and both functions pass `check`. -/
theorem writebarrier_refines {penv : PassEnv} {f : Func} {out : PassOut} {ce ce' : CheckEnv}
    (h : writebarrierChecked penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) :
    RefinesFrom WB.WbPre out.tables out.func penv.tables f := by
  unfold writebarrierChecked at h
  cases hw : writebarrier penv f with
  | error e => simp [hw, bind, Except.bind] at h
  | ok out' =>
    simp only [hw, bind, Except.bind] at h
    split at h
    · rename_i hok
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only [Bool.and_eq_true] at hok
      obtain ⟨hta, hwb⟩ := hok
      obtain ⟨hent, hown, hmem, c, hc, hall⟩ := WB.wbOK_spec hwb
      obtain ⟨ht, hf', hg', -⟩ := WB.ctxOf_spec hc
      have hGl : WB.Glob c ce ce' := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [ht, hf', hg']; exact hc
        · rw [hf']; exact check_wf hf
        · rw [hg']; exact check_wf hg
        · rw [hf']; exact Dom.certOK_of_check (check_domCert hf)
        · rw [hf', hg']; exact hent
        · rw [hf', hg']; exact hown
        · rw [ht, hf']; exact hmem
        · rw [hf']; exact hall
      have hr := WB.refines_of_glob hGl
      rw [ht, hf', hg'] at hr
      exact refinesFrom_of_tabsAgree hta hr
    · cases h

end GoFV.Proof

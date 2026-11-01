import GoFV.Proof.Pass.WBPanic
import GoFV.Proof.CheckFacts
import GoFV.Proof.TabsAgree

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

/-- The inputs of `writebarrier_refines`: the memory with the global image has a defined,
read-only write-barrier flag and no write-barrier buffer, and the environment's contracts keep
that. -/
def WbPre (env : Env) (_args : List Val) (mem : Mem) : Prop :=
  MemOK (addGlobals env mem) ∧ ContractsOK env

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

/-- A value of `B` that is the flag address or constant is not a `Phi`. -/
theorem lazy_nonphi (S : Setup c b B rs l) {a : ID} (ha : a ∈ B.values)
    (hl : c.isWbaddr a = true ∨ c.isConst0 a = true) {u : Value} (hu : c.f.value? a = some u) :
    u.op ≠ .Phi := by
  sorry

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

/-- The flag address and constant after the chain. -/
theorem lazy_after (S : Setup c b B rs l) {env : Env} {frS frT : Frame} {i : Nat}
    (hA : SimAt env c frS frT b i) {G T : Frame}
    (hR : Regs c b B rs G frS frT (rs.length + 1) T) : LazyRegs c T := by
  sorry

/-- **A block entry that succeeds.** -/
theorem chain_ok (S : Setup c b B rs l) (hall : ∀ b' ∈ c.f.blocks, c.blockOK b' = true)
    {ce : CheckEnv} (hwf : WF ce c.f) (hcf : CertOK c.f) {env : Env} (hE : ContractsOK env)
    {frS frT : Frame} {i : Nat} (hA : SimAt env c frS frT b i) {G : Frame}
    (hen : enterBlock env (Ctx.make c.tabs c.f) frS B i = .ok G) :
    ∃ n F eL L T, (∀ fuel, runLoop env (Ctx.make c.tabs c.g) (fuel + n) frT b i =
        runLoop env (Ctx.make c.tabs c.g) fuel F l eL) ∧ c.g.block? l = some L ∧
      enterBlock env (Ctx.make c.tabs c.g) F L eL = .ok T ∧
      (∀ nx, stepTerm G B = .ok nx → stepTerm T L = .ok nx) ∧
      (∀ e, stepTerm G B = .ok (.goto e) → SimAt env c G T e.b e.i) := by
  obtain ⟨hGf, hGs, hGo, hGv, hGp⟩ := enter_ok_facts hwf S.hb S.hB hA.sizeS hen
  have hsinv : SInv G := sinv_enter hE hwf S.memTy S.hb S.hB hA.sinv hen
  have hP : ∀ x ∈ B.values, ∀ u, c.f.value? x = some u → u.op ≠ .Phi → Ev env c G x :=
    fun x hx u hu hp => by
      obtain ⟨y, hy, hev⟩ := hGv x hx u hu hp
      exact ⟨u, y, hu, hy, hev⟩
  have hvx : ∀ x ∈ B.values, ∃ u, c.f.value? x = some u := fun x hx => by
    obtain ⟨u, hu, -, -⟩ := hwf.valueId b B ⟨S.hb, S.hB⟩ x hx
    exact ⟨u, hu⟩
  have hO : OutDef c B G := by
    rintro a - - ⟨y, hy, u, hu, hp, ha⟩
    obtain ⟨z, -, hev⟩ := hGv y hy u hu hp
    exact evalValue_args_def (fun msg h => by rw [hev] at h; cases h) a ha
  have hG : GrOK c B rs G frS := S.grOK hall hA hGf hsinv hGo
    (fun _ a ha y _ hl => by
      obtain ⟨u, hu⟩ := hvx a ha
      exact hP a ha u hu (S.lazy_nonphi ha hl hu)) hO
  have hdef : ∀ a ∈ B.values, ∃ y, G.regs[a]? = some (some y) := fun a ha => by
    obtain ⟨u, hu⟩ := hvx a ha
    by_cases hp : u.op = .Phi
    · obtain ⟨-, y, -, -, h⟩ := hGp a ha u hu hp; exact ⟨_, h⟩
    · obtain ⟨y, hy, -⟩ := hGv a ha u hu hp; exact ⟨y, hy⟩
  -- the runs' first stores were evaluated
  have hrun : ∀ (j : Nat) (r : Run), rs[j]? = some r →
      (∀ s ∈ r.src, s ∈ B.values ∧ ∀ u, c.f.value? s = some u → u.op ≠ .Phi) ∧
      (∀ n ∈ ncsOf c r, n ∈ B.values ∧ ∀ u, c.f.value? n = some u → u.op ≠ .Phi) := by
    sorry
  have hM : ∀ j, j < rs.length → ∃ M, RunMem G rs j M := fun j hj => by
    obtain ⟨r, hr⟩ : ∃ r, rs[j]? = some r := ⟨rs[j], List.getElem?_eq_getElem hj⟩
    obtain ⟨s0, hs0⟩ : ∃ s0, r.src[0]? = some s0 := by
      sorry
    obtain ⟨hs0B, hs0p⟩ := (hrun j r hr).1 s0 (List.mem_of_getElem? hs0)
    obtain ⟨u, hu⟩ := hvx s0 hs0B
    exact S.runMem_of_ev hr hs0 (hP s0 hs0B u hu (hs0p u hu))
  have hcov : ∀ j x, (InSeg c b rs j x ∨ InT c rs j x) → Cov env c rs G x := by
    intro j x hx
    refine S.cov_intro (P := fun x => x ∈ B.values ∧ ∀ u, c.f.value? x = some u → u.op ≠ .Phi)
      (fun x ⟨hx, hp⟩ => by obtain ⟨u, hu⟩ := hvx x hx; exact hP x hx u hu (hp u hu))
      (fun _ a _ _ _ _ ha hap => ⟨ha, hap⟩) ?_ ?_ ?_
    · intro hrole hK hp
      have hh : c.held x = true := by simp [Ctx.held, hK]
      rcases hx with hx | hx
      · exact ⟨S.held_seg hx hh, hp⟩
      · exact (S.held_t hx hh).elim
    · intro j' _ r hr; exact hrun j' r hr
    · intro j' hw
      obtain ⟨r, hr, -⟩ := roleOf_then (o := .WB) (j := j') (by rw [hw]; rfl)
      exact hM j' (List.getElem?_eq_some_iff.1 hr).1
  obtain ⟨n, F, eL, s, hs, hwalk, hR, hPh⟩ := S.walk_to hG (S.regs0 hA hG hGo)
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
      fun _ => S.lazy_after hA hRT, fun hent => ?_⟩
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
    (hE : ContractsOK env) (n : Nat)
    (ih : SimUpTo env (Ctx.make c.tabs c.f) (Ctx.make c.tabs c.g) (R env c) n)
    (frS : Frame) (bS : ID) (iS : Nat) (frT : Frame) (bT : ID) (iT : Nat)
    (hR : R env c frS bS iS frT bT iT)
    (hd : (runLoop env (Ctx.make c.tabs c.f) (n + 1) frS bS iS).Defined) :
    ∃ fuelT, OutcomeRefines (Ctx.make c.tabs c.f).act
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
    exact ⟨n', by rw [hn']; simp only; exact OutcomeRefines.panicked_refl e m⟩
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
        exact OutcomeRefines.refl trivial

/-- **The accepted results refine their inputs.** -/
theorem refines_of_glob {c : WBCheck.Ctx} {ce ce' : CheckEnv} (hGl : Glob c ce ce') :
    RefinesFrom WbPre c.tabs c.g c.tabs c.f := by
  sorry

end GoFV.Proof.WB

namespace GoFV.Proof

open GoFV.SSA GoFV.Opt

/-- **writebarrier refines its input** on `WbPre` inputs, when the checker accepts its result
(`writebarrierChecked`) and both functions pass `check`. -/
theorem writebarrier_refines {penv : PassEnv} {f : Func} {out : PassOut} {ce ce' : CheckEnv}
    (h : writebarrierChecked penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) :
    RefinesFrom WB.WbPre out.tables out.func penv.tables f := by
  sorry

end GoFV.Proof

import GoFV.Proof.Pass.WBArgs
import GoFV.Proof.SimIH

variable [GoFV.SSA.Sem.Addrs]

/-!
# writebarrier: walking the chain of a block (issue #36)

The target runs the chain of block `b` segment by segment against a reference frame `Gr` of the
source (`GrOK`: `Gr`'s memories are `MemOK`, held registers agree with `QR`, held values
outside `B` that `B` reads have registers, its registers are typed). `Regs k F`: at the entry of
segment `k`, the target
frame `F` holds `QR`-registers for everything available there (`Avail`) and the registers
outside the chain of the target's frame `frT` at the block's entry; `Phis k F e`: the segment's
`Phi`s read `QR`-registers along edge `e`.

`seg_enter`: entering a segment whose values have their source facts (`Cov`) succeeds.
`seg_step`: a split segment and, when the flag is set, its buffer block lead to the next
segment. `walk_to`: from the block's entry the target reaches segment `k`.
-/

namespace GoFV.Proof.WB

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.WBCheck GoFV.Proof

/-- The reference frame `Gr` of the source, relative to the source's frame `fr0` at the block's
entry. -/
structure GrOK (c : WBCheck.Ctx) (B : Block) (rs : List Run) (Gr fr0 : Frame) : Prop where
  fr : Gr = { fr0 with regs := Gr.regs }
  held : HeldGr c rs Gr
  mems : MemsGr Gr
  out : OutDef c B Gr
  typed : Typed (Ctx.make c.tabs c.f) Gr

/-- The target frame `F` at the entry of segment `k` (see the module doc). -/
structure Regs (c : WBCheck.Ctx) (b : ID) (B : Block) (rs : List Run) (Gr fr0 frT : Frame)
    (k : Nat) (F : Frame) : Prop where
  fr : F = { fr0 with regs := F.regs }
  size : F.regs.size = c.g.valueTab.size
  avail : ∀ a, Avail c b B rs Gr k a → ∃ z, F.regs[a]? = some (some z) ∧ QR c rs Gr a z
  out : ∀ a, (∀ j, ¬ InSeg c b rs j a) → (∀ j, ¬ InT c rs j a) → F.regs[a]? = frT.regs[a]?

/-- The `Phi`s of segment `k` read `QR`-registers of `F` along edge `e`. -/
def Phis (c : WBCheck.Ctx) (b : ID) (rs : List Run) (Gr : Frame) (k : Nat) (F : Frame)
    (e : Nat) : Prop :=
  ∀ s, (segsOf b rs)[k]? = some s → ∀ x ∈ vals c.g s, ∀ v, c.g.value? x = some v →
    v.op = .Phi → ∃ a z, v.args[e]? = some a ∧ F.regs[a]? = some (some z) ∧
      QR c rs Gr x (z.retype ((Ctx.make c.tabs c.g).tys[x]?.getD .other))

theorem stepTerm_if {F : Frame} {C : Block} {x t e : ID} (hk : C.kind = .If)
    (hc : C.controls = #[x]) (hsu : C.succs = #[⟨t, 0⟩, ⟨e, 0⟩]) {bb : Bool}
    (hx : F.regs[x]? = some (some (.bool bb))) :
    stepTerm F C = .ok (.goto ⟨if bb then t else e, 0⟩) := by
  unfold stepTerm
  rw [hk]
  have hctl : Sem.control F C 0 = .ok (.bool bb) := by
    unfold Sem.control; rw [hc]; simp only [List.getElem?_toArray, List.getElem?_cons_zero, hx]; rfl
  simp only [hctl]
  cases bb <;> simp [succ, hsu] <;> rfl

theorem stepTerm_plain {F : Frame} {C : Block} {t : ID} (hk : C.kind = .Plain)
    (hsu : C.succs = #[⟨t, 1⟩]) : stepTerm F C = .ok (.goto ⟨t, 1⟩) := by
  unfold stepTerm
  rw [hk]
  simp [succ, hsu]
  rfl

theorem blockStep_of {env : Env} {ctx : Sem.Ctx} {F F' : Frame} {bid : ID} {C : Block} {e : Nat}
    {n : Edge} (hC : ctx.f.block? bid = some C) (hen : enterBlock env ctx F C e = .ok F')
    (hst : stepTerm F' C = .ok (.goto n)) : blockStep env ctx F bid e = .goto F' n := by
  unfold blockStep
  simp only [hC, hen, hst]

namespace Setup

variable {c : WBCheck.Ctx} {b : ID} {B : Block} {rs : List Run} {l : ID}

/-- An argument available in segment `k` is available after it. -/
theorem avail_of_availIn (S : Setup c b B rs l) {Gr fr0 : Frame} (hG : GrOK c B rs Gr fr0)
    {k : Nat} {a : ID} (h : c.availIn B (segsOf b rs) k a = true) :
    Avail c b B rs Gr (k + 1) a := by
  obtain ⟨hh, hin, hout⟩ := availIn_spec h
  by_cases haB : a ∈ B.values
  · obtain ⟨s, hs, has⟩ := hin haB
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hs
    have hjk : j < k + 1 := by
      have := (List.getElem?_eq_some_iff.1 hj).1
      simp only [List.length_take] at this; omega
    rw [List.getElem?_take_of_lt hjk] at hj
    exact .inr (.inl ⟨j, hjk, s, hj, has⟩)
  · exact .inl ⟨hh, haB, hG.out a hh haB (hout haB)⟩

/-- Run `k`'s memory in a frame of segment `k + 1`. -/
theorem mem_reg (S : Setup c b B rs l) {Gr fr0 frT : Frame} (hG : GrOK c B rs Gr fr0)
    {k : Nat} {r : Run} (hr : rs[k]? = some r) {F : Frame}
    (hR : Regs c b B rs Gr fr0 frT (k + 1) F) {M : Mem} (hM : RunMem Gr rs k M) :
    F.regs[r.sp.mem]? = some (some (.mem M)) := by
  obtain ⟨hh, ha⟩ := S.mem_held hr
  obtain ⟨z, hz, hq⟩ := hR.avail _ (S.avail_of_availIn hG ha)
  obtain ⟨r', hr', hM'⟩ := hM
  rw [hr] at hr'; cases hr'
  rw [hz, hG.held _ _ _ hh hq hM']

/-- The `Phi` of segment `k + 1` reads run `k`'s memory or the buffer block's. -/
theorem phis_next (S : Setup c b B rs l) {Gr : Frame} {k : Nat} {r : Run} (hr : rs[k]? = some r)
    {F : Frame} {e : Nat} (he : e < 2)
    (hz : ∀ a, #[r.sp.mem, r.memThen][e]? = some a →
      (r.memThen = r.sp.mem ∨ c.roleOf rs r.memThen = .sel1 k ∨
        c.roleOf rs r.memThen = .bstore k ∨ c.roleOf rs r.memThen = .seln k) →
      ∃ z, F.regs[a]? = some (some z) ∧ ∃ M m, RunMem Gr rs k M ∧ z = .mem m ∧ W M m) :
    Phis c b rs Gr (k + 1) F e := by
  intro s hs x hx v hv hp
  obtain ⟨r', hr', rfl, hrole, hargs, hty, hmt⟩ := S.phi_seg hs hx hv hp
  rw [hr] at hr'; cases hr'
  obtain ⟨a, ha⟩ : ∃ a, #[r.sp.mem, r.memThen][e]? = some a := by
    rcases e with _ | _ | e
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · omega
  obtain ⟨z, hz', M, m, hM, rfl, hW⟩ := hz a ha hmt
  refine ⟨a, .mem m, by rw [hargs]; exact ha, hz', ?_⟩
  simp only [QR, hrole]
  refine ⟨M, m, hM, ?_, hW⟩
  rw [tys_of_value hv, Option.getD_some, hty]
  rfl

/-- **Entering a segment.** -/
theorem seg_enter (S : Setup c b B rs l) {env : Env} {Gr fr0 frT : Frame}
    (hG : GrOK c B rs Gr fr0) {k : Nat} {s : ID} (hs : (segsOf b rs)[k]? = some s) {F : Frame}
    {e : Nat} (hR : Regs c b B rs Gr fr0 frT k F) (hP : Phis c b rs Gr k F e)
    (hcov : ∀ x, InSeg c b rs k x → Cov env c rs Gr x) :
    ∃ C F', c.g.block? s = some C ∧ enterBlock env (Ctx.make c.tabs c.g) F C e = .ok F' ∧
      (∀ a, a ∉ C.values → F'.regs[a]? = F.regs[a]?) ∧
      Regs c b B rs Gr fr0 frT (k + 1) F' := by
  obtain ⟨C, hC, -, hsg, hsch⟩ := S.seg_block hs
  obtain ⟨ce', hwg⟩ := S.wg
  have hv : ∀ x, x ∈ vals c.g s ↔ x ∈ C.values := fun x => by rw [vals_of hC]
  obtain ⟨F', hen, hF', hsz, hQ, hout⟩ := enter_Q (tabs := c.tabs) (env := env) (fr0 := fr0)
    (Q := QR c rs Gr) hwg hsg hC hsch hR.fr hR.size
    (fun x hx v hxv hp => hP s hs x ((hv x).2 hx) v hxv hp)
    (Avail c b B rs Gr k) hR.avail (fun a ha hm => S.avail_not_seg hs ha ((hv a).2 hm))
    (fun x hx v hxv hp => S.local_seg hG.fr hG.held hG.mems ⟨s, hs, (hv x).2 hx⟩ hxv hp
      (hcov x ⟨s, hs, (hv x).2 hx⟩))
    (fun x hx v hxv hp a ha hna =>
      S.args_seg hG.out hs ((hv x).2 hx) hxv hp ha (fun hm => hna ((hv a).1 hm)))
  refine ⟨C, F', hC, hen, hout, ⟨hF', by rw [hsz, hR.size], fun a ha => ?_, fun a h1 h2 => ?_⟩⟩
  · rcases ha with h | ⟨j, hj, hin⟩ | h
    · exact hQ a (.inl (.inl h))
    · rcases Nat.lt_or_ge j k with hjk | hjk
      · exact hQ a (.inl (.inr (.inl ⟨j, hjk, hin⟩)))
      · obtain rfl : j = k := by omega
        obtain ⟨s', hs', hin'⟩ := hin
        rw [hs] at hs'; cases hs'
        exact hQ a (.inr ((hv a).1 hin'))
    · exact hQ a (.inl (.inr (.inr h)))
  · rw [hout a (fun hm => h1 k ⟨s, hs, (hv a).2 hm⟩)]
    exact hR.out a h1 h2

/-- **A split segment**: to the next segment, through the buffer block if the flag is set. -/
theorem seg_step (S : Setup c b B rs l) {env : Env} {Gr fr0 frT : Frame}
    (hG : GrOK c B rs Gr fr0) {k : Nat} {r : Run} (hr : rs[k]? = some r) {F : Frame} {e : Nat}
    (hR : Regs c b B rs Gr fr0 frT k F) (hP : Phis c b rs Gr k F e)
    (hcov : ∀ x, (InSeg c b rs k x ∨ InT c rs k x) → Cov env c rs Gr x) {M : Mem}
    (hM : RunMem Gr rs k M) :
    ∃ n F'' e'', (∀ fuel, runLoop env (Ctx.make c.tabs c.g) (fuel + n) F r.sp.c e =
        runLoop env (Ctx.make c.tabs c.g) fuel F'' r.sp.e e'') ∧
      Regs c b B rs Gr fr0 frT (k + 1) F'' ∧ Phis c b rs Gr (k + 1) F'' e'' := by
  obtain ⟨hsc, -⟩ := S.run_seg hr
  obtain ⟨C, F', hC, hen, -, hR'⟩ := S.seg_enter hG hsc hR hP (fun x hx => hcov x (.inl hx))
  obtain ⟨C', hC', hk, hctl, hsu, hfr, hfl⟩ := S.split_block hr
  rw [hC] at hC'; cases hC'
  obtain ⟨z, hz, hq⟩ := hR'.avail r.sp.flag (.inr (.inl ⟨k, Nat.lt_succ_self k, r.sp.c, hsc, hfl⟩))
  simp only [QR, hfr] at hq
  obtain ⟨bb, rfl⟩ := hq M hM
  have hbs := blockStep_of (ctx := Ctx.make c.tabs c.g) (env := env) hC hen
    (stepTerm_if (F := F') hk hctl hsu hz)
  have hmem := S.mem_reg hG hr hR' hM
  have hMr : MemAt Gr r.sp.mem M := by
    obtain ⟨r', hr', h⟩ := hM; rw [hr] at hr'; cases hr'; exact h
  have hnob : M.find? .wbuf = none := (hG.mems _ _ hMr).nobuf
  cases bb with
  | false =>
    refine ⟨1, F', 0, fun fuel => runLoop_goto hbs, hR', S.phis_next hr (by decide) fun a ha _ => ?_⟩
    simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at ha
    subst ha
    exact ⟨_, hmem, M, M, hM, rfl, W.refl hnob⟩
  | true =>
    obtain ⟨T, hT, -, htg, hTk, hTs, hTsch⟩ := S.t_block hr
    obtain ⟨ce', hwg⟩ := S.wg
    have hv : ∀ x, x ∈ vals c.g r.sp.t ↔ x ∈ T.values := fun x => by rw [vals_of hT]
    obtain ⟨F'', hen2, hF'', hsz2, hQ2, hout2⟩ := enter_Q (tabs := c.tabs) (env := env)
      (fr0 := fr0) (Q := QR c rs Gr) hwg htg hT hTsch hR'.fr hR'.size
      (fun x hx v hxv hp => absurd hp (S.t_nophi hr ((hv x).2 hx) hxv))
      (Avail c b B rs Gr (k + 1)) hR'.avail
      (fun a ha hm => S.avail_not_t hr ha ((hv a).2 hm))
      (fun x hx v hxv _ => S.local_t hG.held hG.mems hG.typed ⟨r, hr, (hv x).2 hx⟩ hxv
        (hcov x (.inr ⟨r, hr, (hv x).2 hx⟩)))
      (fun x hx v hxv _ a ha hna =>
        S.args_t hG.out hr ((hv x).2 hx) hxv ha (fun hm => hna ((hv a).1 hm)))
    have hbs2 := blockStep_of (ctx := Ctx.make c.tabs c.g) (env := env) hT hen2
      (stepTerm_plain (F := F'') hTk hTs)
    have hR'' : Regs c b B rs Gr fr0 frT (k + 1) F'' :=
      ⟨hF'', by rw [hsz2, hR'.size], fun a ha => hQ2 a (.inl ha), fun a h1 h2 => by
        rw [hout2 a (fun hm => h2 k ⟨r, hr, (hv a).2 hm⟩)]; exact hR'.out a h1 h2⟩
    refine ⟨2, F'', 1, fun fuel => ?_, hR'', S.phis_next hr (by decide) fun a ha hmt => ?_⟩
    · rw [show fuel + 2 = (fuel + 1) + 1 from rfl, runLoop_goto hbs]
      exact runLoop_goto hbs2
    · simp only [List.getElem?_toArray, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at ha
      subst ha
      rcases hmt with heq | hmt
      · rw [heq]
        have hmn : r.sp.mem ∉ T.values := fun hm =>
          S.avail_not_t hr (S.avail_of_availIn hG (S.mem_held hr).2) ((hv _).2 hm)
        exact ⟨_, by rw [hout2 _ hmn]; exact hmem, M, M, hM, rfl, W.refl hnob⟩
      · have hin : r.memThen ∈ vals c.g r.sp.t := by
          rcases hmt with h | h | h
          · obtain ⟨r', hr', hx, -⟩ := roleOf_then (o := .Select1) (j := k) (by rw [h]; rfl)
            rw [hr] at hr'; cases hr'; exact hx
          · obtain ⟨r', hr', hx, -⟩ := roleOf_then (o := .Store) (j := k) (by rw [h]; rfl)
            rw [hr] at hr'; cases hr'; exact hx
          · obtain ⟨r', hr', hx, -⟩ := roleOf_then (o := .SelectN) (j := k) (by rw [h]; rfl)
            rw [hr] at hr'; cases hr'; exact hx
        obtain ⟨z, hz, hq⟩ := hQ2 _ (.inr ((hv _).1 hin))
        refine ⟨z, hz, ?_⟩
        have key : ∀ (z : Val) (n : Nat), (∃ r' M' m, rs[k]? = some r' ∧
            MemAt Gr r'.sp.mem M' ∧ z = Val.mem m ∧ Buf M' n m) →
            ∃ M m, RunMem Gr rs k M ∧ z = Val.mem m ∧ W M m := by
          rintro z n ⟨r', M', m, hr', hM', rfl, hB⟩
          rw [hr] at hr'; cases hr'
          rw [MemAt, hMr] at hM'; cases hM'
          exact ⟨M, m, hM, rfl, hB.w hnob⟩
        rcases hmt with h | h | h
        · simp only [QR, h] at hq; exact key z _ hq
        · simp only [QR, h] at hq; exact key z _ hq
        · simp only [QR, h] at hq
          obtain ⟨r', M', m, hr', hM', rfl, hB⟩ := hq
          rw [hr] at hr'; cases hr'
          rw [MemAt, hMr] at hM'; cases hM'
          rcases hB with ⟨n, hB⟩ | hB
          · exact ⟨M, m, hM, rfl, hB.w hnob⟩
          · rw [hB]; exact ⟨M, M, hM, rfl, W.refl hnob⟩

/-- **Walking the chain** to segment `k`. -/
theorem walk_to (S : Setup c b B rs l) {env : Env} {Gr fr0 frT : Frame}
    (hG : GrOK c B rs Gr fr0) {i : Nat} (hR0 : Regs c b B rs Gr fr0 frT 0 frT)
    (hP0 : Phis c b rs Gr 0 frT i) :
    ∀ k, k ≤ rs.length →
      (∀ j x, j < k → (InSeg c b rs j x ∨ InT c rs j x) → Cov env c rs Gr x) →
      (∀ j, j < k → ∃ M, RunMem Gr rs j M) →
      ∃ n F e s, (segsOf b rs)[k]? = some s ∧
        (∀ fuel, runLoop env (Ctx.make c.tabs c.g) (fuel + n) frT b i =
          runLoop env (Ctx.make c.tabs c.g) fuel F s e) ∧
        Regs c b B rs Gr fr0 frT k F ∧ Phis c b rs Gr k F e
  | 0, _, _, _ => ⟨0, frT, i, b, rfl, fun _ => rfl, hR0, hP0⟩
  | k + 1, hk, hcov, hM => by
    obtain ⟨n, F, e, s, hs, hrun, hR, hP⟩ := walk_to S hG hR0 hP0 k (by omega)
      (fun j x hj => hcov j x (by omega)) (fun j hj => hM j (by omega))
    obtain ⟨r, hr⟩ : ∃ r, rs[k]? = some r := ⟨rs[k], List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨hsc, hse⟩ := S.run_seg hr
    obtain rfl : s = r.sp.c := Option.some.inj (hs.symm.trans hsc)
    obtain ⟨M, hMk⟩ := hM k (by omega)
    obtain ⟨n', F', e', hrun', hR', hP'⟩ :=
      S.seg_step hG hr hR hP (fun x hx => hcov k x (by omega) hx) hMk
    refine ⟨n' + n, F', e', r.sp.e, hse, fun fuel => ?_, hR', hP'⟩
    rw [← Nat.add_assoc, hrun (fuel + n'), hrun' fuel]

end Setup

end GoFV.Proof.WB

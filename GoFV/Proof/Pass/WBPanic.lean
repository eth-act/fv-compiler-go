import GoFV.Proof.Pass.WBPanicFacts

/-!
# writebarrier: a block entry that panics (issue #36)

`chain_panic`: when the source's entry of block `b` panics at node `r`, the target's chain
panics alike. `r` is a kept node of segment `k` (a call or nil check, `panic_kept`): the target
walks to segment `k` and panics at `r` there. Or `r` is the dropped nil check of run `j`
(`panic_nc`): the target walks to segment `j`, runs it, and panics at the nil check's copy in
the buffer block (flag set) or in segment `j + 1` (flag clear), with the run's memory. Before
its panic point the target evaluates only values whose source counterparts the source evaluated
before `r` (`ord_pre`, `np_before`).
-/

namespace GoFV.Proof.WB

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Opt GoFV.Opt.WBCheck GoFV.Proof
open GoFV.Proof.MemInv (ContractsOK)

/-- The source's entry of block `b` (values `B`) panics at `r` after `pre` in frame `Gr`. -/
structure SrcPanic (env : Env) (c : WBCheck.Ctx) (B : Block) (rs : List Run) (frS : Frame)
    (i : Nat) (o : Array ID) (pre post : List ID) (r : ID) (Gr : Frame) (e : Panic) (m : Mem) :
    Prop where
  sched : schedule c.f B = some o
  split : o.toList = pre ++ r :: post
  own : ValuesOwn c.f B
  nd : B.values.toList.Nodup
  ev : ∀ x ∈ pre, Ev env c Gr x
  grOK : GrOK c B rs Gr frS
  rB : r ∈ B.values
  rnp : npOf c.f B r = true
  pan : stepV env (Ctx.make c.tabs c.f) Gr r = .panic e m
  out : ∀ z, z ∉ B.values → Gr.regs[z]? = frS.regs[z]?
  outEv : OutEv env c B Gr
  phis : ∀ x ∈ B.values, ∀ u, c.f.value? x = some u → u.op = .Phi →
    ∃ a y, u.args[i]? = some a ∧ frS.regs[a]? = some (some y) ∧
      Gr.regs[x]? = some (some (y.retype ((Ctx.make c.tabs c.f).tys[x]?.getD .other)))

theorem before_trans {o : List ID} (hn : o.Nodup) {x y z : ID} (h1 : Order.Before o x y)
    (h2 : Order.Before o y z) : Order.Before o x z := by
  obtain ⟨i1, j1, hij1, hi1, hj1⟩ := h1
  obtain ⟨i2, j2, hij2, hi2, hj2⟩ := h2
  have := Order.idx_unique hn hj1 hi2
  exact ⟨i1, j2, by omega, hi1, hj2⟩

theorem before_split {pre post : List ID} {x r : ID} (hx : x ∈ pre) :
    Order.Before (pre ++ r :: post) x r := by
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
  have hil : i < pre.length := (List.getElem?_eq_some_iff.1 hi).1
  exact ⟨i, pre.length, hil, by rw [List.getElem?_append_left hil]; exact hi, by simp⟩

theorem blockStep_panic {env : Env} {ctx : Sem.Ctx} {F : Frame} {bid : ID} {C : Block} {e : Nat}
    {ep : Panic} {m : Mem} (hC : ctx.f.block? bid = some C)
    (hen : enterBlock env ctx F C e = .panic ep m) : blockStep env ctx F bid e = .panic ep m := by
  unfold blockStep
  simp only [hC, hen]

namespace Setup

variable {c : WBCheck.Ctx} {b : ID} {B : Block} {rs : List Run} {l : ID}

theorem segOK (S : Setup c b B rs l) {j : Nat} {s x : ID} (hs : (segsOf b rs)[j]? = some s)
    (hx : x ∈ vals c.g s) : c.roleOK b B (segsOf b rs) rs false j x = true :=
  (blockOK_spec S.ok S.hB S.ch).2.2.2.2.2.2.1 j s hs x hx

theorem tOK (S : Setup c b B rs l) {j : Nat} {r : Run} (hr : rs[j]? = some r) {x : ID}
    (hx : x ∈ vals c.g r.sp.t) : c.roleOK b B (segsOf b rs) rs true j x = true := by
  obtain ⟨-, -, ⟨T, hT, -, -, -, -, -, hT'⟩, -⟩ :=
    runOK_spec ((blockOK_spec S.ok S.hB S.ch).2.2.2.2.1 j r hr)
  exact hT' x (by rw [← vals_of hT]; exact hx)

theorem gval (S : Setup c b B rs l) {s x : ID} (hsg : s ∈ c.g.blocks) (hx : x ∈ vals c.g s) :
    ∃ w, c.g.value? x = some w ∧ w.id = x := by
  obtain ⟨ce, hg⟩ := S.wg
  obtain ⟨C, hC, -⟩ := hg.blockId s hsg
  obtain ⟨w, hw, hid, -⟩ := hg.valueId s C ⟨hsg, hC⟩ x (by rw [← vals_of hC]; exact hx)
  exact ⟨w, hw, hid⟩

theorem fval (S : Setup c b B rs l) {x : ID} (hx : x ∈ B.values) :
    ∃ u, c.f.value? x = some u := by
  obtain ⟨ce, hf⟩ := S.wf
  obtain ⟨u, hu, -⟩ := hf.valueId b B ⟨S.hb, S.hB⟩ x hx
  exact ⟨u, hu⟩

/-- Ranks before the panic: what the source evaluated. -/
theorem pre_of_rank (S : Setup c b B rs l) {env : Env} {frS : Frame} {i : Nat} {o : Array ID}
    {pre post : List ID} {r : ID} {Gr : Frame} {e : Panic} {m : Mem}
    (SP : SrcPanic env c B rs frS i o pre post r Gr e m) {qr : Nat} (hr : NpRank c b rs r qr)
    {x : ID} {qx : Nat} (hx : NpRank c b rs x qx) (hxn : npOf c.f B x = true) (hlt : qx < qr) :
    x ∈ pre :=
  pre_of_before SP.own SP.nd SP.sched SP.split hxn SP.rnp (S.np_before SP.sched hx hr hxn SP.rnp hlt)

/-- A run of rank below `r`'s is evaluated. -/
theorem run_pre (S : Setup c b B rs l) {env : Env} {frS : Frame} {i : Nat} {o : Array ID}
    {pre post : List ID} {r : ID} {Gr : Frame} {e : Panic} {m : Mem}
    (SP : SrcPanic env c B rs frS i o pre post r Gr e m) {qr : Nat} (hr : NpRank c b rs r qr)
    {j : Nat} {rj : Run} (hrj : rs[j]? = some rj) (hlt : 2 * j + 1 < qr) :
    (∀ s ∈ rj.src, s ∈ pre) ∧ (∀ n ∈ ncsOf c rj, n ∈ pre) :=
  ⟨fun s hs => S.pre_of_rank SP hr (.inr ⟨j, rj, rfl, hrj, .inr hs⟩) (S.src_np hrj hs) hlt,
   fun n hn => S.pre_of_rank SP hr (.inr ⟨j, rj, rfl, hrj, .inl hn⟩) (S.ncs_np hrj hn) hlt⟩

/-- **The panic at a kept node of segment `k`.** -/
theorem panic_kept (S : Setup c b B rs l) (hall : ∀ b' ∈ c.f.blocks, c.blockOK b' = true)
    {env : Env} {frS frT : Frame} {i : Nat}
    (hA : SimAt env c frS frT b i) {o : Array ID} {pre post : List ID} {r : ID} {Gr : Frame}
    {e : Panic} {m : Mem} (SP : SrcPanic env c B rs frS i o pre post r Gr e m) {k : Nat} {s : ID}
    (hs : (segsOf b rs)[k]? = some s) (hrs : r ∈ vals c.g s) (hK : c.K.getD r false = true)
    {rv : Value} (hrv : c.f.value? r = some rv) (hrop : Panicking rv.op) :
    ∃ n, runLoop env (Ctx.make c.tabs c.g) n frT b i = .panicked e m := by
  have hrR : NpRank c b rs r (2 * k) := .inl ⟨k, rfl, ⟨s, hs, hrs⟩, hK⟩
  have hkl : k ≤ rs.length := by
    have := (List.getElem?_eq_some_iff.1 hs).1
    rw [segs_length] at this; omega
  obtain ⟨C, hC, -, hsg, oC, hoC⟩ := S.seg_block hs
  have hPcl : ∀ x a v, x ∈ pre → c.f.value? x = some v → a ∈ v.args → a ∈ B.values →
      (∀ va, c.f.value? a = some va → va.op ≠ .Phi) → a ∈ pre :=
    fun x a v hx hv ha haB hap => pre_closed SP.own SP.nd SP.sched SP.split hx hv ha haB hap
  -- the held values the target evaluates before `r`
  let A : ID → Prop := fun x => x ∈ B.values ∧ (∀ v, c.f.value? x = some v → v.op ≠ .Phi) ∧
    c.held x = true ∧ ((∃ j, j < k ∧ InSeg c b rs j x) ∨
      (x ∈ vals c.g s ∧ Order.Before oC.toList x r))
  have hApre : ∀ x, A x → x ∈ pre := by
    refine ord_pre SP.own SP.nd SP.sched SP.split SP.rnp A
      (fun x hx => ⟨hx.1, by obtain ⟨u, hu⟩ := S.fval hx.1; exact ⟨u, hu, hx.2.1 u hu⟩⟩) ?_ ?_
    · rintro x ⟨hxB, -, hh, hpos⟩ hxn
      rcases hpos with ⟨j, hj, s', hs', hxs'⟩ | ⟨hxs, hbef⟩
      · rcases S.held_rank hs' hxs' hh with hq | ⟨j'', rfl, hq⟩
        · exact S.pre_of_rank SP hrR hq hxn (by omega)
        · exact S.pre_of_rank SP hrR hq hxn (by omega)
      · rcases S.held_rank hs hxs hh with hq | ⟨j'', rfl, hq⟩
        · have hxK : c.K.getD x false = true := by
            rcases hq with ⟨s'', h1, -, hK'⟩ | ⟨j3, r3, h1, -⟩
            · exact hK'
            · omega
          exact pre_of_before SP.own SP.nd SP.sched SP.split hxn SP.rnp
            (S.np_before_seg SP.sched hs hC hoC hxK hK hxn SP.rnp hbef)
        · exact S.pre_of_rank SP hrR hq hxn (by omega)
    · rintro x ⟨hxB, hxp, hh, hpos⟩ hxn v hv a ha haB hap
      have haA : c.held a = true → (∃ j, j < k ∧ InSeg c b rs j a) ∨
          (a ∈ vals c.g s ∧ Order.Before oC.toList a r) → A a := fun h1 h2 => ⟨haB, hap, h1, h2⟩
      rcases hpos with ⟨j, hj, s', hs', hxs'⟩ | ⟨hxs, hbef⟩
      · obtain ⟨hha, j', hj', hin, -⟩ := S.held_pure_args hs' hxs' hh hxn hv (hxp v hv) ha haB hap
        exact haA hha (.inl ⟨j', by omega, hin⟩)
      · obtain ⟨hha, j', hj', ⟨s'', hs'', has⟩, hbefa⟩ :=
          S.held_pure_args hs hxs hh hxn hv (hxp v hv) ha haB hap
        rcases Nat.lt_or_ge j' k with hlt | hge
        · exact haA hha (.inl ⟨j', hlt, s'', hs'', has⟩)
        · obtain rfl : j' = k := by omega
          rw [hs] at hs''; cases hs''
          have hnd : oC.toList.Nodup := (schedule_spec hoC).topo.nodup
          exact haA hha (.inr ⟨has, before_trans hnd (hbefa rfl C oC hC hoC) hbef⟩)
  -- the runs before `r`'s segment
  have hruns : ∀ j rj, j < k → rs[j]? = some rj → (∀ s ∈ rj.src, s ∈ pre) ∧
      (∀ n ∈ ncsOf c rj, n ∈ pre) := fun j rj hj hrj => S.run_pre SP hrR hrj (by omega)
  have hcovP : ∀ x, ((∃ j, j ≤ k ∧ InSeg c b rs j x) ∨ (∃ j, j < k ∧ InT c rs j x)) →
      (c.roleOf rs x = .held → c.K.getD x false = true →
        (∀ u, c.f.value? x = some u → u.op ≠ .Phi) → x ∈ pre) → Cov env c rs Gr x :=
    fun x hpos hheld => S.cov_of_runs SP.ev hA.wbh hPcl SP.outEv hruns hpos hheld
  have hcovW : ∀ j x, j < k → (InSeg c b rs j x ∨ InT c rs j x) → Cov env c rs Gr x := by
    intro j x hj hx
    refine hcovP x (hx.elim (fun h => .inl ⟨j, by omega, h⟩) (fun h => .inr ⟨j, hj, h⟩)) ?_
    intro _ hK' hp
    have hh : c.held x = true := by simp [Ctx.held, hK']
    rcases hx with hx | hx
    · exact hApre x ⟨S.held_seg hx hh, hp, hh, .inl ⟨j, hj, hx⟩⟩
    · exact (S.held_t hx hh).elim
  have hM : ∀ j, j < k → ∃ M, RunMem Gr rs j M := by
    intro j hj
    obtain ⟨rj, hrj⟩ : ∃ rj, rs[j]? = some rj := ⟨rs[j], List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨s0, hs0⟩ : ∃ s0, rj.src[0]? = some s0 :=
      ⟨_, List.getElem?_eq_getElem (by
        obtain ⟨-, -, -, -, -, -, hpos, -⟩ :=
          runOK_spec ((blockOK_spec S.ok S.hB S.ch).2.2.2.2.1 j rj hrj)
        exact hpos)⟩
    exact S.runMem_of_ev hrj hs0 (SP.ev s0 ((hruns j rj hj hrj).1 s0 (List.mem_of_getElem? hs0)))
  obtain ⟨n, F, eF, s', hs', hwalk, hR, hPh⟩ := S.walk_to SP.grOK
    (S.regs0 hall hA SP.grOK SP.out) (S.phis0 hA SP.phis) k hkl hcovW hM
  obtain rfl : s = s' := Option.some.inj (hs.symm.trans hs')
  -- `r` in the target's schedule of segment `k`
  obtain ⟨ce', hwg⟩ := S.wg
  obtain ⟨-, -, omemC⟩ := schedule_topo (valuesOwn hwg hsg hC) (hwg.valuesNodup s C ⟨hsg, hC⟩) hoC
  have hrC : r ∈ oC.toList := by
    obtain ⟨-, -, -, hKe, -, -⟩ := ctxOf_spec S.ctx
    rw [hKe] at hK
    obtain ⟨u', w, hu', hw, hsame, -⟩ := keptMarks_spec hK
    rw [hrv] at hu'; cases hu'
    have hop : w.op = rv.op := by
      simp only [sameV, Bool.and_eq_true, beq_iff_eq] at hsame
      exact hsame.1.1.1.1.2.symm
    refine (omemC r).2 ⟨by rw [← vals_of hC]; exact hrs, w, hw, ?_⟩
    rw [hop]; intro hp; rw [hp] at hrop
    rcases hrop with h | h <;> cases h
  obtain ⟨preT, postT, hsplitT⟩ := List.append_of_mem hrC
  have hv : ∀ x, x ∈ vals c.g s ↔ x ∈ C.values := fun x => by rw [vals_of hC]
  have hen := enter_Q_panic (tabs := c.tabs) (env := env) (fr0 := frS) (Q := QR c rs Gr) hwg hsg
    hC hoC hsplitT hR.fr hR.size (fun x hx v hxv hp => hPh s hs x ((hv x).2 hx) v hxv hp)
    (Avail c b B rs Gr k) hR.avail (fun a ha hm => S.avail_not_seg hs ha ((hv a).2 hm))
    (fun x hx => by
      have hxo : x ∈ oC.toList := by rw [hsplitT]; exact List.mem_append_left _ hx
      obtain ⟨hxC, w, hw, hwp⟩ := (omemC x).1 hxo
      have hxs : x ∈ vals c.g s := (hv x).2 hxC
      refine S.local_seg SP.grOK.fr SP.grOK.held SP.grOK.mems ⟨s, hs, hxs⟩ hw hwp
        (hcovP x (.inl ⟨k, Nat.le_refl _, s, hs, hxs⟩) fun _ hK' hp => ?_)
      have hh : c.held x = true := by simp [Ctx.held, hK']
      exact hApre x ⟨S.held_seg ⟨s, hs, hxs⟩ hh, hp, hh, .inr ⟨hxs, by
        rw [hsplitT]; exact before_split hx⟩⟩)
    (fun x hx v hxv hp a ha hna =>
      S.args_seg SP.grOK.out hs ((hv x).2 hx) hxv hp ha (fun hm => hna ((hv a).1 hm)))
    (S.panic_kept_step SP.grOK ⟨s, hs, hrs⟩ hK hrv hrop SP.pan)
  exact ⟨1 + n, by
    rw [hwalk 1, runLoop_panic (blockStep_panic (ctx := Ctx.make c.tabs c.g) hC hen)]⟩

theorem npOf_true {h : Func} {C : Block} {x : ID} {v : Value} (hx : x ∈ C.values)
    (hv : h.value? x = some v) (hp : prio v.op ≠ 0) (hnp : v.op ≠ .Phi) : npOf h C x = true := by
  unfold npOf
  simp [hv, hp, hnp, hx]

theorem before_mem_pre {pre post : List ID} {y a x : ID} (hn : (pre ++ y :: post).Nodup)
    (hb : Order.Before (pre ++ y :: post) a x) (hx : x ∈ pre) : a ∈ pre := by
  obtain ⟨i1, j1, hij, hi1, hj1⟩ := hb
  obtain ⟨jx, hjx⟩ := List.getElem?_of_mem hx
  have hjxl : jx < pre.length := (List.getElem?_eq_some_iff.1 hjx).1
  have := Order.idx_unique hn hj1 (by rw [List.getElem?_append_left hjxl]; exact hjx)
  subst this
  rw [List.getElem?_append_left (by omega)] at hi1
  exact List.mem_of_getElem? hi1

/-- A held value of a segment that is not kept (a run's last store, `WBend`) is non-pure in
`g`. -/
theorem held_np_g (S : Setup c b B rs l) (hall : ∀ b' ∈ c.f.blocks, c.blockOK b' = true)
    {j : Nat} {s x : ID} (hs : (segsOf b rs)[j]? = some s) (hx : x ∈ vals c.g s)
    (hh : c.held x = true) (hK : c.K.getD x false = false) {C : Block}
    (hC : c.g.block? s = some C) : npOf c.g C x = true := by
  obtain ⟨-, -, -, hsg, -⟩ := S.seg_block hs
  obtain ⟨w, hw, -⟩ := S.gval hsg hx
  have hxC : x ∈ C.values := by rw [← vals_of hC]; exact hx
  rcases role_of_held (rs := rs) hh with hρ | hρ | hρ
  · obtain ⟨-, -, hcase⟩ := roleOK_held (S.segOK hs hx) hw hρ
    rcases hcase with ⟨hK', -⟩ | ⟨-, -, -, -, -, -, hop, -⟩
    · rw [hK] at hK'; cases hK'
    · exact npOf_true hxC hw (by rw [hop]; decide) (by rw [hop]; decide)
  · obtain ⟨-, -, -, -, -, hl⟩ := ctxOf_spec S.ctx
    have hwa : c.isWbaddr x = true := by
      unfold Ctx.roleOf at hρ
      by_cases h1 : c.isWbaddr x = true
      · exact h1
      · rw [if_neg h1] at hρ
        by_cases h2 : c.isConst0 x = true
        · rw [if_pos h2] at hρ; cases hρ
        · rw [if_neg h2, if_pos hh] at hρ; cases hρ
    unfold Ctx.isWbaddr at hwa
    cases hz : c.lazy with
    | none => rw [hz] at hwa; cases hwa
    | some p =>
      obtain ⟨wa, c0⟩ := p
      rw [hz] at hwa hl
      simp only [Option.any_some, beq_iff_eq] at hwa
      subst hwa
      obtain ⟨h1, h2⟩ := lazyOK_not_held hl
      have : c.held wa = false := by simp [Ctx.held, ← ctxOf_spec S.ctx |>.2.2.2.1, h1,
        ← ctxOf_spec S.ctx |>.2.2.2.2.1, h2]
      rw [hh] at this; cases this
  · have hc0 : c.isConst0 x = true := by
      unfold Ctx.roleOf at hρ
      by_cases h1 : c.isWbaddr x = true
      · rw [if_pos h1] at hρ; cases hρ
      · rw [if_neg h1] at hρ
        by_cases h2 : c.isConst0 x = true
        · exact h2
        · rw [if_neg h2, if_pos hh] at hρ; cases hρ
    have := (S.lazy_held hall hh (.inr hc0)).1
    rw [hK] at this; cases this

/-- **The panic at the dropped nil check of run `j0`.** -/
theorem panic_nc (S : Setup c b B rs l) (hall : ∀ b' ∈ c.f.blocks, c.blockOK b' = true)
    {env : Env} {frS frT : Frame} {i : Nat}
    (hA : SimAt env c frS frT b i) {o : Array ID} {pre post : List ID} {r : ID} {Gr : Frame}
    {e : Panic} {m : Mem} (SP : SrcPanic env c B rs frS i o pre post r Gr e m) {j0 : Nat}
    {r0 : Run} (hr0 : rs[j0]? = some r0) (hn : r0.nc = some r)
    (hK : c.K.getD r false = false) :
    ∃ n, runLoop env (Ctx.make c.tabs c.g) n frT b i = .panicked e m := by
  have hrR : NpRank c b rs r (2 * j0 + 1) :=
    .inr ⟨j0, r0, rfl, hr0, .inl (by simp [ncsOf, hn, hK])⟩
  have hj0 : j0 < rs.length := (List.getElem?_eq_some_iff.1 hr0).1
  have hM0 : RunMem Gr rs j0 m := S.runMem_of_panic hr0 hn SP.pan
  have hMr : MemAt Gr r0.sp.mem m := by
    obtain ⟨r', hr', h⟩ := hM0; rw [hr0] at hr'; cases hr'; exact h
  obtain ⟨hsc, hse⟩ := S.run_seg hr0
  obtain ⟨-, -, ⟨T, hT, -, -, -, -, hncT, -⟩, ⟨E, hE, -, hncE, hncEn⟩, -, -, -, -, -, -, -, -, -,
    -, hEro, -⟩ := runOK_spec ((blockOK_spec S.ok S.hB S.ch).2.2.2.2.1 j0 r0 hr0)
  obtain ⟨yE, hyE⟩ : ∃ y, r0.ncEnd = some y := by
    cases h : r0.ncEnd with
    | none => rw [hncEn h] at hn; cases hn
    | some y => exact ⟨y, rfl⟩
  obtain ⟨ysE, hnpE⟩ := hncE yE hyE
  obtain ⟨oE, hoE, hfE⟩ : ∃ oE, schedule c.g E = some oE ∧
      oE.toList.filter (npOf c.g E) = yE :: ysE := by
    unfold Ctx.npSeq at hnpE
    cases ho : schedule c.g E with
    | none => rw [ho] at hnpE; cases hnpE
    | some oE => rw [ho] at hnpE; exact ⟨oE, rfl, Option.some.inj hnpE⟩
  obtain ⟨preE, postE, hsplitE, hpureE⟩ := filter_first hfE
  obtain ⟨ce', hwg⟩ := S.wg
  obtain ⟨-, -, -, hEg, -⟩ := S.seg_block hse
  obtain ⟨-, -, omemE⟩ :=
    schedule_topo (valuesOwn hwg hEg hE) (hwg.valuesNodup _ E ⟨hEg, hE⟩) hoE
  have hndE : oE.toList.Nodup := (schedule_spec hoE).topo.nodup
  have hvE : ∀ x, x ∈ vals c.g r0.sp.e ↔ x ∈ E.values := fun x => by rw [vals_of hE]
  have hPcl : ∀ x a v, x ∈ pre → c.f.value? x = some v → a ∈ v.args → a ∈ B.values →
      (∀ va, c.f.value? a = some va → va.op ≠ .Phi) → a ∈ pre :=
    fun x a v hx hv ha haB hap => pre_closed SP.own SP.nd SP.sched SP.split hx hv ha haB hap
  let A : ID → Prop := fun x => x ∈ B.values ∧ (∀ v, c.f.value? x = some v → v.op ≠ .Phi) ∧
    c.held x = true ∧ ((∃ j, j ≤ j0 ∧ InSeg c b rs j x) ∨ (x ∈ vals c.g r0.sp.e ∧ x ∈ preE))
  have hApre : ∀ x, A x → x ∈ pre := by
    refine ord_pre SP.own SP.nd SP.sched SP.split SP.rnp A
      (fun x hx => ⟨hx.1, by obtain ⟨u, hu⟩ := S.fval hx.1; exact ⟨u, hu, hx.2.1 u hu⟩⟩) ?_ ?_
    · rintro x ⟨hxB, -, hh, hpos⟩ hxn
      rcases hpos with ⟨j, hj, s', hs', hxs'⟩ | ⟨hxs, hxp⟩
      · rcases S.held_rank hs' hxs' hh with hq | ⟨j'', rfl, hq⟩
        · exact S.pre_of_rank SP hrR hq hxn (by omega)
        · exact S.pre_of_rank SP hrR hq hxn (by omega)
      · exfalso
        have hpE := hpureE x hxp
        by_cases hxK : c.K.getD x false = true
        · rw [S.npOf_kept hxK hse hE ((hvE x).1 hxs), hxn] at hpE; cases hpE
        · rw [S.held_np_g hall hse hxs hh (by simpa using hxK) hE] at hpE; cases hpE
    · rintro x ⟨hxB, hxp, hh, hpos⟩ hxn v hv a ha haB hap
      have haA : c.held a = true → (∃ j, j ≤ j0 ∧ InSeg c b rs j a) ∨
          (a ∈ vals c.g r0.sp.e ∧ a ∈ preE) → A a := fun h1 h2 => ⟨haB, hap, h1, h2⟩
      rcases hpos with ⟨j, hj, s', hs', hxs'⟩ | ⟨hxs, hxpE⟩
      · obtain ⟨hha, j', hj', hin, -⟩ := S.held_pure_args hs' hxs' hh hxn hv (hxp v hv) ha haB hap
        exact haA hha (.inl ⟨j', by omega, hin⟩)
      · obtain ⟨hha, j', hj', ⟨s'', hs'', has⟩, hbefa⟩ :=
          S.held_pure_args hse hxs hh hxn hv (hxp v hv) ha haB hap
        rcases Nat.lt_or_ge j' (j0 + 1) with hlt | hge
        · exact haA hha (.inl ⟨j', by omega, s'', hs'', has⟩)
        · obtain rfl : j' = j0 + 1 := by omega
          rw [hse] at hs''; cases hs''
          refine haA hha (.inr ⟨has, ?_⟩)
          have hb := hbefa rfl E oE hE hoE
          rw [hsplitE] at hb hndE
          exact before_mem_pre hndE hb hxpE
  have hruns : ∀ j rj, j < j0 → rs[j]? = some rj → (∀ s ∈ rj.src, s ∈ pre) ∧
      (∀ n ∈ ncsOf c rj, n ∈ pre) := fun j rj hj hrj => S.run_pre SP hrR hrj (by omega)
  have hcovP : ∀ x, ((∃ j, j ≤ j0 ∧ InSeg c b rs j x) ∨ (∃ j, j < j0 ∧ InT c rs j x)) →
      (c.roleOf rs x = .held → c.K.getD x false = true →
        (∀ u, c.f.value? x = some u → u.op ≠ .Phi) → x ∈ pre) → Cov env c rs Gr x :=
    fun x hpos hheld => S.cov_of_runs SP.ev hA.wbh hPcl SP.outEv hruns hpos hheld
  have hcovS : ∀ j x, j ≤ j0 → InSeg c b rs j x → Cov env c rs Gr x := by
    intro j x hj hx
    refine hcovP x (.inl ⟨j, hj, hx⟩) fun _ hK' hp => ?_
    have hh : c.held x = true := by simp [Ctx.held, hK']
    exact hApre x ⟨S.held_seg hx hh, hp, hh, .inl ⟨j, hj, hx⟩⟩
  have hcovW : ∀ j x, j < j0 → (InSeg c b rs j x ∨ InT c rs j x) → Cov env c rs Gr x := by
    intro j x hj hx
    rcases hx with hx | hx
    · exact hcovS j x (by omega) hx
    · refine hcovP x (.inr ⟨j, hj, hx⟩) fun _ hK' _ => ?_
      exact (S.held_t hx (by simp [Ctx.held, hK'])).elim
  have hM : ∀ j, j < j0 → ∃ M, RunMem Gr rs j M := by
    intro j hj
    obtain ⟨rj, hrj⟩ : ∃ rj, rs[j]? = some rj := ⟨rs[j], List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨s0, hs0⟩ : ∃ s0, rj.src[0]? = some s0 :=
      ⟨_, List.getElem?_eq_getElem (by
        obtain ⟨-, -, -, -, -, -, hpos, -⟩ :=
          runOK_spec ((blockOK_spec S.ok S.hB S.ch).2.2.2.2.1 j rj hrj)
        exact hpos)⟩
    exact S.runMem_of_ev hrj hs0 (SP.ev s0 ((hruns j rj hj hrj).1 s0 (List.mem_of_getElem? hs0)))
  obtain ⟨n, F, eF, s', hs', hwalk, hR, hPh⟩ := S.walk_to SP.grOK
    (S.regs0 hall hA SP.grOK SP.out) (S.phis0 hA SP.phis) j0 (by omega) hcovW hM
  obtain rfl : r0.sp.c = s' := Option.some.inj (hsc.symm.trans hs')
  obtain ⟨C, F', hC, hen0, -, hR'⟩ := S.seg_enter SP.grOK hsc hR hPh
    (fun x hx => hcovS j0 x (Nat.le_refl _) hx)
  obtain ⟨C', hC', hk, hctl, hsu, hfr, hfl⟩ := S.split_block hr0
  rw [hC] at hC'; cases hC'
  obtain ⟨z, hz, hq⟩ := hR'.avail r0.sp.flag
    (.inr (.inl ⟨j0, Nat.lt_succ_self j0, r0.sp.c, hsc, hfl⟩))
  simp only [QR, hfr] at hq
  obtain ⟨bb, rfl⟩ := hq m hM0
  have hbs := blockStep_of (ctx := Ctx.make c.tabs c.g) (env := env) hC hen0
    (stepTerm_if (F := F') hk hctl hsu hz)
  have hmem := S.mem_reg SP.grOK hr0 hR' hM0
  have hmh := (S.mem_held hr0).1
  cases bb with
  | true =>
    obtain ⟨T', hT', -, hTg, hTk, hTs, -⟩ := S.t_block hr0
    rw [hT] at hT'; cases hT'
    obtain ⟨y, ys, hnpT, hyrole⟩ := hncT r hn
    obtain ⟨oT, hoT, hfT⟩ : ∃ oT, schedule c.g T = some oT ∧
        oT.toList.filter (npOf c.g T) = y :: ys := by
      unfold Ctx.npSeq at hnpT
      cases ho : schedule c.g T with
      | none => rw [ho] at hnpT; cases hnpT
      | some oT => rw [ho] at hnpT; exact ⟨oT, rfl, Option.some.inj hnpT⟩
    obtain ⟨preT, postT, hsplitT, hpureT⟩ := filter_first hfT
    obtain ⟨-, -, omemT⟩ :=
      schedule_topo (valuesOwn hwg hTg hT) (hwg.valuesNodup _ T ⟨hTg, hT⟩) hoT
    have hvT : ∀ x, x ∈ vals c.g r0.sp.t ↔ x ∈ T.values := fun x => by rw [vals_of hT]
    have hyo : y ∈ oT.toList := by rw [hsplitT]; simp
    obtain ⟨hyT, wy, hwy, -⟩ := (omemT y).1 hyo
    obtain ⟨-, -, r', n', hr', hn', hcopy⟩ := roleOK_ncThen (S.tOK hr0 ((hvT y).2 hyT)) hwy hyrole
    rw [hr0] at hr'; cases hr'
    rw [hn] at hn'; cases hn'
    have hen := enter_Q_panic (tabs := c.tabs) (env := env) (fr0 := frS) (Q := QR c rs Gr)
      (e := 0) hwg hTg hT hoT hsplitT hR'.fr hR'.size
      (fun x hx v hxv hp => absurd hp (S.t_nophi hr0 ((hvT x).2 hx) hxv))
      (Avail c b B rs Gr (j0 + 1)) hR'.avail (fun a ha hm => S.avail_not_t hr0 ha ((hvT a).2 hm))
      (fun x hx => by
        have hxo : x ∈ oT.toList := by rw [hsplitT]; exact List.mem_append_left _ hx
        obtain ⟨hxT, w, hw, -⟩ := (omemT x).1 hxo
        have hxt : x ∈ vals c.g r0.sp.t := (hvT x).2 hxT
        have hok := S.tOK hr0 hxt
        have hpx := hpureT x hx
        refine S.local_t SP.grOK.held SP.grOK.mems SP.grOK.typed ⟨r0, hr0, hxt⟩ hw
          (S.cov_intro SP.ev hPcl SP.outEv hA.wbh (fun _ hK' _ =>
            (S.held_t ⟨r0, hr0, hxt⟩ (by simp [Ctx.held, hK'])).elim) ?_ ?_)
        · rintro j' hρ r'' -
          exfalso
          rcases hρ with ⟨k', hρ⟩ | hρ | hρ | hρ
          · obtain ⟨h, -⟩ := roleOK_tgt hok hw hρ; cases h
          · obtain ⟨h, -⟩ := roleOK_ncEnd hok hw hρ; cases h
          · obtain ⟨-, -, r3, n3, -, -, u3, w3, p3, mS3, -, hw3, -, hw3op, -⟩ :=
              roleOK_ncThen hok hw hρ
            rw [hw] at hw3; cases hw3
            rw [npOf_true hxT hw (by rw [hw3op]; decide) (by rw [hw3op]; decide)] at hpx
            cases hpx
          · obtain ⟨-, -, hop, -⟩ := roleOK_call hok hw hρ
            rw [npOf_true hxT hw (by rw [hop]; decide) (by rw [hop]; decide)] at hpx
            cases hpx
        · intro j' hρ
          obtain ⟨-, rfl, -⟩ := roleOK_wb hok hw hρ
          exact ⟨m, hM0⟩)
      (fun x hx v hxv _ a ha hna =>
        S.args_t SP.grOK.out hr0 ((hvT x).2 hx) hxv ha (fun hm => hna ((hvT a).1 hm)))
      (fun g' hg' hargs' => by
        obtain ⟨u3, w3, p3, mS3, -, hw3, -, -, -, -, hw3a, -⟩ := id hcopy
        obtain ⟨z, hz', hq'⟩ := hargs' r0.sp.mem (by rw [argsF_of hw3, hw3a]; simp)
        have := SP.grOK.held r0.sp.mem z (.mem m) hmh hq' hMr
        subst this
        exact S.panic_nc_step SP.grOK hr0 hn SP.pan (.inl hcopy) g' hg' hargs' hz')
    refine ⟨2 + n, ?_⟩
    rw [hwalk 2, show (2 : Nat) = 1 + 1 from rfl, runLoop_goto hbs]
    exact runLoop_panic (blockStep_panic (ctx := Ctx.make c.tabs c.g) hT hen)
  | false =>
    have hyo : yE ∈ oE.toList := by rw [hsplitE]; simp
    obtain ⟨hyE', wy, hwy, -⟩ := (omemE yE).1 hyo
    obtain ⟨-, -, r', n', hr', hn', hcopy, -⟩ :=
      roleOK_ncEnd (S.segOK hse ((hvE yE).2 hyE')) hwy (hEro yE hyE)
    rw [hr0] at hr'; cases hr'
    rw [hn] at hn'; cases hn'
    obtain ⟨-, -, -, -, -, ⟨pv, hpv, hpvop, -⟩, hphi0⟩ :=
      runOf_spec ((chainRuns_spec S.ch).1 j0 r0 hr0).2.2.2
    have hphiE : r0.phi ∈ vals c.g r0.sp.e := Array.mem_iff_getElem?.2 ⟨0, hphi0⟩
    have hnob : m.find? .wbuf = none := (SP.grOK.mems _ _ hMr).nobuf
    have hen := enter_Q_panic (tabs := c.tabs) (env := env) (fr0 := frS)
      (Q := fun a z => QR c rs Gr a z ∧ (a = r0.phi → z = .mem m)) (e := 0) hwg
      hEg hE hoE hsplitE hR'.fr hR'.size
      (fun x hx v hxv hp => by
        obtain ⟨r', hr', rfl, hrole, hargs, hty, -⟩ := S.phi_seg hse ((hvE x).2 hx) hxv hp
        rw [hr0] at hr'; cases hr'
        have hrt : (Val.mem m).retype ((Ctx.make c.tabs c.g).tys[r0.phi]?.getD .other) =
            .mem m := by
          rw [tys_of_value hxv, Option.getD_some, hty]; rfl
        refine ⟨r0.sp.mem, .mem m, by rw [hargs]; rfl, hmem, ?_, fun _ => hrt⟩
        simp only [QR, hrole]
        exact ⟨m, m, hM0, hrt, W.refl hnob⟩)
      (Avail c b B rs Gr (j0 + 1))
      (fun a ha => by
        obtain ⟨z, hz, hq⟩ := hR'.avail a ha
        exact ⟨z, hz, hq, fun he => absurd (he ▸ hphiE) (S.avail_not_seg hse ha)⟩)
      (fun a ha hm => S.avail_not_seg hse ha ((hvE a).2 hm))
      (fun x hx => by
        have hxo : x ∈ oE.toList := by rw [hsplitE]; exact List.mem_append_left _ hx
        obtain ⟨hxE, w, hw, hwp⟩ := (omemE x).1 hxo
        have hxs : x ∈ vals c.g r0.sp.e := (hvE x).2 hxE
        have hok := S.segOK hse hxs
        have hpx := hpureE x hx
        refine localQ_mono (S.local_seg SP.grOK.fr SP.grOK.held SP.grOK.mems ⟨_, hse, hxs⟩ hw hwp
          ?_) (fun a z h => h.1) (fun z hq => ⟨hq, fun he => ?_⟩)
        · refine S.cov_intro SP.ev hPcl SP.outEv hA.wbh (fun _ hK' hp => ?_) ?_ ?_
          · have hh : c.held x = true := by simp [Ctx.held, hK']
            exact hApre x ⟨S.held_seg ⟨_, hse, hxs⟩ hh, hp, hh, .inr ⟨hxs, hx⟩⟩
          · rintro j' hρ r'' -
            exfalso
            rcases hρ with ⟨k', hρ⟩ | hρ | hρ | hρ
            · obtain ⟨-, -, r3, s3, hr3, hs3, -, ⟨u3, w3, hu3, hw3, hop3, -⟩, -⟩ :=
                roleOK_tgt hok hw hρ
              rw [hw] at hw3; cases hw3
              obtain ⟨-, -, -, hsrcop, -⟩ := runOf_spec ((chainRuns_spec S.ch).1 _ r3 hr3).2.2.2
              obtain ⟨u4, hu4, hop4, -⟩ := hsrcop _ s3 hs3
              rw [hu3] at hu4; cases hu4
              have hnp : npOf c.g E x = true := by
                rcases hop4 with h | h | h | h | h <;>
                  exact npOf_true hxE hw (by rw [hop3, h]; decide) (by rw [hop3, h]; decide)
              rw [hnp] at hpx; cases hpx
            · obtain ⟨-, -, r3, n3, -, -, ⟨u3, w3, p3, mS3, -, hw3, -, hw3op, -⟩, -⟩ :=
                roleOK_ncEnd hok hw hρ
              rw [hw] at hw3; cases hw3
              rw [npOf_true hxE hw (by rw [hw3op]; decide) (by rw [hw3op]; decide)] at hpx
              cases hpx
            · obtain ⟨h, -⟩ := roleOK_ncThen hok hw hρ; cases h
            · obtain ⟨h, -⟩ := roleOK_call hok hw hρ; cases h
          · intro j' hρ
            obtain ⟨h, -⟩ := roleOK_wb hok hw hρ; cases h
        · exfalso
          rw [he, hpv] at hw; cases hw; exact hwp hpvop)
      (fun x hx v hxv hp a ha hna =>
        S.args_seg SP.grOK.out hse ((hvE x).2 hx) hxv hp ha (fun hm => hna ((hvE a).1 hm)))
      (fun g' hg' hargs' => by
        obtain ⟨u3, w3, p3, mS3, -, hw3, -, -, -, -, hw3a, -⟩ := id hcopy
        obtain ⟨z, hz', -, hzphi⟩ := hargs' r0.phi (by rw [argsF_of hw3, hw3a]; simp)
        have := hzphi rfl
        subst this
        exact S.panic_nc_step SP.grOK hr0 hn SP.pan (.inr hcopy) g' hg'
          (fun a ha => (hargs' a ha).imp fun _ h => ⟨h.1, h.2.1⟩) hz')
    refine ⟨2 + n, ?_⟩
    rw [hwalk 2, show (2 : Nat) = 1 + 1 from rfl, runLoop_goto hbs]
    exact runLoop_panic (blockStep_panic (ctx := Ctx.make c.tabs c.g) hE hen)

/-- **A panicking block entry.** -/
theorem chain_panic (S : Setup c b B rs l) (hall : ∀ b' ∈ c.f.blocks, c.blockOK b' = true)
    {ce : CheckEnv} (hwf : WF ce c.f) (hcf : CertOK c.f) {env : Env} (hE : ContractsOK MemOK env)
    {frS frT : Frame} {i : Nat} (hA : SimAt env c frS frT b i) {e : Panic} {m : Mem}
    (hen : enterBlock env (Ctx.make c.tabs c.f) frS B i = .panic e m) :
    ∃ n, runLoop env (Ctx.make c.tabs c.g) n frT b i = .panicked e m := by
  obtain ⟨ps, o, pre, r, post, Gpre, hps, ho, hsplit, hpre, hrp, hGf, hGs, hGo, hGv, hGp, hrB, rv,
    hrv, hrnp, hrop⟩ := enter_panic_facts hwf S.hb S.hB hA.sizeS hen
  have SP : SrcPanic env c B rs frS i o pre post r Gpre e m :=
    { sched := ho, split := hsplit, own := valuesOwn hwf S.hb S.hB,
      nd := hwf.valuesNodup b B ⟨S.hb, S.hB⟩,
      ev := fun x hx => by obtain ⟨v, y, hv, hy, hev⟩ := hGv x hx; exact ⟨v, y, hv, hy, hev⟩,
      grOK := S.grOK_panic hall hwf hcf hE hA hps ho hsplit hpre hGf hGo hGv,
      rB := hrB, rnp := npOf_true hrB hrv (prio_panicking hrop) hrnp, pan := hrp, out := hGo,
      outEv := S.outEv_of hwf hcf hA hGf hGo, phis := hGp }
  have hcovB := (blockOK_spec S.ok S.hB S.ch).2.2.2.2.2.1 r hrB
  by_cases hK : c.K.getD r false = true
  · obtain ⟨s, hs, hrs⟩ := hcovB.1 hK
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hs
    exact S.panic_kept hall hA SP hk hrs hK hrv hrop
  · have hK' : c.K.getD r false = false := by simpa using hK
    rcases hcovB.2 hK' with ⟨r0, hr0, hsrc⟩ | ⟨r0, hr0, hnc⟩
    · exfalso
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hr0
      obtain ⟨k, hk⟩ := List.getElem?_of_mem hsrc
      obtain ⟨-, -, -, h, -⟩ := runOf_spec ((chainRuns_spec S.ch).1 j r0 hj).2.2.2
      obtain ⟨u, hu, hop, -⟩ := h k r hk
      rw [hrv] at hu; cases hu
      rcases hrop with h | h <;> rcases hop with h' | h' | h' | h' | h' <;> rw [h'] at h <;> cases h
    · obtain ⟨j, hj⟩ := List.getElem?_of_mem hr0
      exact S.panic_nc hall hA SP hj hnc hK'

end Setup

end GoFV.Proof.WB

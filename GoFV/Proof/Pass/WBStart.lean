import GoFV.Proof.Pass.WBWalk
import GoFV.Proof.DomCert
import GoFV.Proof.MemInv

/-!
# writebarrier: the simulation relation and the start of a chain (issue #36)

`SimAt env c frS frT b i`: the source enters block `b` along edge `i` with frame `frS` (lemma (D)
for the strict dominators, `SInv`), the target enters `b` (the first segment of its chain) with
`frT`: the source's frame but for the registers, equal on held values, with the flag address and
constant once the entry block has run.

From a reference frame `Gr` of the source after (a prefix of) block `b`: `grOK` (the facts the
chain's values read), `regs0`/`phis0` (the target at the chain's entry), `final_held` (held
registers after the chain).
-/

namespace GoFV.Proof.WB

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Opt GoFV.Opt.WBCheck GoFV.Proof
open GoFV.Proof.MemInv (SInv)

/-- The target holds the flag address and constant. -/
def LazyRegs (c : WBCheck.Ctx) (fr : Frame) : Prop :=
  ∀ wa c0, c.lazy = some (wa, c0) →
    fr.regs[wa]? = some (some (.ptr flagPtr)) ∧ fr.regs[c0]? = some (some (.int .w32 0))

/-- How the source enters block `b` along edge `i`: the entry, or a successor of a tree block `p`
after which lemma (D) holds for `p`'s ancestors. -/
def Pre (env : Env) (c : WBCheck.Ctx) (fr : Frame) (b : ID) (i : Nat) : Prop :=
  b = c.f.entry ∨ ∃ p P, p ∈ c.f.blocks ∧ c.f.block? p = some P ∧
    ((make c.f).depthOf p).isSome ∧ (⟨b, i⟩ : Edge) ∈ P.succs ∧
    DInv env (Ctx.make c.tabs c.f) (fun a => Anc (make c.f) a p) fr

/-- The simulation relation at block entries (see the module doc). -/
structure SimAt (env : Env) (c : WBCheck.Ctx) (frS frT : Frame) (b : ID) (i : Nat) : Prop where
  pre : Pre env c frS b i
  sizeS : frS.regs.size = c.f.valueTab.size
  sizeT : frT.regs.size = c.g.valueTab.size
  fr : frT = { frS with regs := frT.regs }
  held : ∀ a, c.held a = true → frT.regs[a]? = frS.regs[a]?
  sinv : SInv MemOK frS
  lazy : b ≠ c.f.entry → LazyRegs c frT
  entry : b = c.f.entry → ∀ (a : ID) (y : Val), frS.regs[a]? ≠ some (some y)

theorem pre_tree {ce : CheckEnv} {c : WBCheck.Ctx} (hwf : WF ce c.f) (hc : CertOK c.f)
    {env : Env} {fr : Frame} {b : ID} {i : Nat} (h : Pre env c fr b i) :
    b ∈ c.f.blocks ∧ ((make c.f).depthOf b).isSome := by
  rcases h with rfl | ⟨p, P, hp, hpb, hpt, he, -⟩
  · exact ⟨hwf.entry, by simp [entry_depth hc.parents]⟩
  · obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 he
    exact ⟨(hwf.succLink p P ⟨hp, hpb⟩ j _ hj).1, (edge hc hp hpb hpt he).2.1⟩

theorem pre_strict {c : WBCheck.Ctx} (hc : CertOK c.f) {env : Env} {fr : Frame} {b : ID}
    {i : Nat} (h : Pre env c fr b i) :
    DInv env (Ctx.make c.tabs c.f) (fun a => Anc (make c.f) a b ∧ a ≠ b) fr := by
  rcases h with rfl | ⟨p, P, hp, hpb, hpt, he, hd⟩
  · exact dinv_entry hc fr
  · exact hd.mono fun _ ⟨ha, hne⟩ =>
      Anc.trans hc.parents (ha.up hc.parents hne) (edge hc hp hpb hpt he).2.2

/-- The source's evaluation of a kept flag address. -/
theorem eval_wbaddr {env : Env} {tabs : Tables} {f : Func} {fr : Frame} {u : Value} {y : Val}
    (h : evalValue env (Ctx.make tabs f) fr u = .ok y) (hop : u.op = .Addr)
    (hsym : symName? tabs u.aux = some "runtime.writeBarrier")
    (hty : isPtrTy (tabs.ty u.type) = true) (hid : f.value? u.id = some u) :
    y = .ptr flagPtr := by
  obtain ⟨L, r0, -, hop0, rfl⟩ := evalValue_inv h
  rw [tys_of_value hid] at hop0 ⊢
  simp only [Option.getD_some] at hop0 ⊢
  unfold symName? at hsym
  have hfv : frameVal (Ctx.make tabs f) u = some (.ptr flagPtr) := by
    unfold frameVal
    rw [hop]
    dsimp only
    split at hsym
    · rename_i name _ _ _ he
      simp only [Ctx.make]
      rw [he]
      simp only [Option.some.injEq] at hsym
      simp [flagPtr, flagBlk, hsym]
    · cases hsym
  have hev : evalOp env (Ctx.make tabs f) fr u L (tabs.ty u.type) = .ok (.ptr flagPtr) := by
    unfold evalOp
    rw [hop]
    dsimp only
    rw [hfv]
    rfl
  rw [hev] at hop0
  cases hop0
  obtain ⟨e, he⟩ : ∃ e, tabs.ty u.type = .ptr e := by
    unfold isPtrTy at hty; split at hty
    · exact ⟨_, ‹_›⟩
    · cases hty
  rw [he]
  rfl

/-- The source's evaluation of a kept `Const32 [0]`. -/
theorem eval_const0 {env : Env} {tabs : Tables} {f : Func} {fr : Frame} {u : Value} {y : Val}
    (h : evalValue env (Ctx.make tabs f) fr u = .ok y) (hop : u.op = .Const32)
    (hai : u.auxInt = (0 : Int64)) (hty : tabs.ty u.type = .int .w32)
    (hid : f.value? u.id = some u) : y = .int .w32 0 := by
  obtain ⟨L, r0, -, hop0, rfl⟩ := evalValue_inv h
  rw [tys_of_value hid] at hop0 ⊢
  simp only [Option.getD_some] at hop0 ⊢
  rw [hty] at hop0 ⊢
  have hev : evalOp env (Ctx.make tabs f) fr u L (.int .w32) = .ok (.int .w32 0) := by
    simp only [evalOp, frameVal, hop]
    rw [hai]; rfl
  rw [hev] at hop0
  cases hop0
  rfl

private theorem sameV_parts {u w : Value} (h : sameV u w = true) :
    u.id = w.id ∧ u.op = w.op ∧ u.type = w.type ∧ u.auxInt = w.auxInt ∧ u.aux = w.aux ∧
      u.args = w.args := by
  unfold sameV at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

private theorem blockOK_some {c : WBCheck.Ctx} {b : ID} (h : c.blockOK b = true) :
    ∃ B rs l, c.f.block? b = some B ∧ chainRuns? c.f c.g b = some (rs, l) := by
  unfold Ctx.blockOK at h
  split at h
  next B rs l hB hch => exact ⟨B, rs, l, hB, hch⟩
  next => cases h

private theorem roleOK_val {c : WBCheck.Ctx} {b : ID} {B : Block} {segs : List ID}
    {rs : List Run} {inT : Bool} {j : Nat} {x : ID} (h : c.roleOK b B segs rs inT j x = true) :
    ∃ w, c.g.value? x = some w := by
  unfold Ctx.roleOK at h
  split at h
  · cases h
  · rename_i w hw
    exact ⟨w, hw⟩

private theorem lst_of_held {c : WBCheck.Ctx} {a : ID} (hh : c.held a = true)
    (hK : ¬ c.K.getD a false = true) : c.Lst.getD a false = true := by
  unfold Ctx.held at hh
  simp only [Bool.or_eq_true] at hh
  exact hh.resolve_left hK

namespace Setup

variable {c : WBCheck.Ctx} {b : ID} {B : Block} {rs : List Run} {l : ID}

/-- A held value of `B` is listed in a segment. -/
theorem held_listed (S : Setup c b B rs l) (hall : ∀ b' ∈ c.f.blocks, c.blockOK b' = true)
    {a : ID} (hh : c.held a = true) (ha : a ∈ B.values) :
    ∃ j, InSeg c b rs j a := by
  have bo := blockOK_spec S.ok S.hB S.ch
  by_cases hK : c.K.getD a false = true
  · obtain ⟨s, hs, hx⟩ := (bo.2.2.2.2.2.1 a ha).1 hK
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hs
    exact ⟨j, s, hj, hx⟩
  · have hL := lst_of_held hh hK
    rw [(ctxOf_spec S.ctx).2.2.2.2.1] at hL
    obtain ⟨b', hb', rs', l', hch', r, hr, hlast⟩ := lastMarks_spec hL
    obtain ⟨B', -, -, hB', -⟩ := blockOK_some (hall b' hb')
    have bo' := blockOK_spec (hall b' hb') hB' hch'
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hr
    obtain ⟨-, -, -, -, -, -, -, hlv, -, -, -, -, -, -, -, hsrc, -⟩ :=
      runOK_spec (bo'.2.2.2.2.1 k r hk)
    obtain ⟨-, -, hgl, -⟩ := runOf_spec ((chainRuns_spec hch').1 k r hk).2.2.2
    have has : a ∈ r.src := by rw [← hlast]; exact List.mem_of_getLast? hgl
    obtain ⟨ce, hwf⟩ := S.wf
    have hbb : b' = b := hwf.valueOnce b' B' b B ⟨hb', hB'⟩ ⟨S.hb, S.hB⟩ a (hsrc a has).1 ha
    rw [hbb, S.ch] at hch'
    simp only [Option.some.injEq, Prod.mk.injEq] at hch'
    rw [← hch'.1] at hk
    refine ⟨k + 1, r.sp.e, (run_seg S hk).2, ?_⟩
    rw [← hlast]; exact hlv

/-- A held flag address or constant is a kept value of the entry block. -/
theorem lazy_held (S : Setup c b B rs l) (hall : ∀ b' ∈ c.f.blocks, c.blockOK b' = true)
    {a : ID} (hh : c.held a = true) (hl : c.isWbaddr a = true ∨ c.isConst0 a = true) :
    c.K.getD a false = true ∧ ∃ E, c.f.block? c.f.entry = some E ∧ a ∈ E.values := by
  obtain ⟨ce, hwf⟩ := S.wf
  have hent : a ∈ vals c.g c.f.entry ∧ c.f.entry ∈ c.g.blocks := by
    rcases hl with h | h
    · obtain ⟨c0, hz⟩ := lazy_of_wbaddr h
      obtain ⟨h1, -, h3⟩ := S.lazy_entry hz
      exact ⟨h1, h3⟩
    · obtain ⟨wa, hz⟩ := lazy_of_const0 h
      obtain ⟨-, h2, h3⟩ := S.lazy_entry hz
      exact ⟨h2, h3⟩
  have hK : c.K.getD a false = true := by
    refine Classical.byContradiction fun hK => ?_
    have hL := lst_of_held hh hK
    rw [(ctxOf_spec S.ctx).2.2.2.2.1] at hL
    obtain ⟨b', hb', rs', l', hch', r, hr, hlast⟩ := lastMarks_spec hL
    obtain ⟨B', -, -, hB', -⟩ := blockOK_some (hall b' hb')
    have bo' := blockOK_spec (hall b' hb') hB' hch'
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hr
    obtain ⟨-, hseg, -, -, -, -, -, hlv, -⟩ := runOK_spec (bo'.2.2.2.2.1 k r hk)
    have hemem : r.sp.e ∈ c.g.blocks :=
      bo'.2.2.2.1 _ (List.mem_append_left _ (List.mem_of_getElem? hseg))
    have hav : a ∈ vals c.g r.sp.e := by rw [← hlast]; exact hlv
    have he := S.listed_once hemem hent.2 hav hent.1
    obtain ⟨-, -, hsp, -⟩ := (chainRuns_spec hch').1 k r hk
    obtain ⟨-, C, -, -, -, -, -, -, hne, -⟩ := splitOf_spec hsp
    exact hne (by rw [he]; exact hwf.entry)
  refine ⟨hK, ?_⟩
  have hokE := hall _ hwf.entry
  obtain ⟨E, rsE, lE, hE, hchE⟩ := blockOK_some hokE
  have hok := (blockOK_spec hokE hE hchE).2.2.2.2.2.2.1 0 c.f.entry rfl a hent.1
  obtain ⟨w, hw⟩ := roleOK_val hok
  have hρ : c.roleOf rsE a = .wbaddr ∨ c.roleOf rsE a = .const0 := by
    rcases hl with h | h
    · exact .inl (roleOf_wbaddr h)
    · exact .inr (roleOf_const0 h (isWbaddr_of_const0 S.ctx h))
  have hl' := roleOK_lazy hok hw (hρ.elim .inl (fun h => .inr (.inl h)))
  exact ⟨E, hE, hl'.2.2.2.1 hh⟩

/-- A held flag address in `Gr`. -/
private theorem gr_wbaddr (S : Setup c b B rs l) (hall : ∀ b' ∈ c.f.blocks, c.blockOK b' = true)
    {env : Env} {frS frT : Frame} {i : Nat} (hA : SimAt env c frS frT b i) {Gr : Frame}
    (hout : ∀ a, a ∉ B.values → Gr.regs[a]? = frS.regs[a]?)
    (hev : b = c.f.entry → ∀ a ∈ B.values, ∀ y, Gr.regs[a]? = some (some y) →
      (c.isWbaddr a = true ∨ c.isConst0 a = true) → Ev env c Gr a)
    {a : ID} {y : Val} (hh : c.held a = true) (hwa : c.isWbaddr a = true)
    (hy : Gr.regs[a]? = some (some y)) : y = .ptr flagPtr := by
  obtain ⟨hK, E, hE, haE⟩ := S.lazy_held hall hh (.inl hwa)
  obtain ⟨c0, hz⟩ := lazy_of_wbaddr hwa
  obtain ⟨ce, hwf⟩ := S.wf
  by_cases hb : b = c.f.entry
  · have hBE : B = E := by have := S.hB; rw [hb, hE] at this; cases this; rfl
    subst hBE
    obtain ⟨u, y', hu, hy', hev'⟩ := hev hb a haE y hy (.inl hwa)
    rw [hy] at hy'; cases hy'
    have hl := (ctxOf_spec S.ctx).2.2.2.2.2
    rw [hz] at hl
    obtain ⟨⟨w, hw, hop, hsym, hty, -⟩, -⟩ := lazyOK_some hl
    obtain ⟨u', w', hu', hw', hsame, -⟩ :=
      keptMarks_spec (by rw [← (ctxOf_spec S.ctx).2.2.2.1]; exact hK)
    rw [hu] at hu'; cases hu'
    rw [hw] at hw'; cases hw'
    obtain ⟨-, hop', hty', -, haux, -⟩ := sameV_parts hsame
    obtain ⟨v, hv, hvid, -⟩ := hwf.valueId _ _ ⟨S.hb, S.hB⟩ a haE
    rw [hu] at hv; cases hv
    exact eval_wbaddr hev' (hop'.trans hop) (by rw [haux]; exact hsym) (by rw [hty']; exact hty)
      (by rw [hvid]; exact hu)
  · have hnB : a ∉ B.values := fun haB =>
      hb (hwf.valueOnce b B c.f.entry E ⟨S.hb, S.hB⟩ ⟨hwf.entry, hE⟩ a haB haE)
    rw [hout a hnB, ← hA.held a hh, (hA.lazy hb _ _ hz).1] at hy
    cases hy
    rfl

/-- A held constant in `Gr`. -/
private theorem gr_const0 (S : Setup c b B rs l) (hall : ∀ b' ∈ c.f.blocks, c.blockOK b' = true)
    {env : Env} {frS frT : Frame} {i : Nat} (hA : SimAt env c frS frT b i) {Gr : Frame}
    (hout : ∀ a, a ∉ B.values → Gr.regs[a]? = frS.regs[a]?)
    (hev : b = c.f.entry → ∀ a ∈ B.values, ∀ y, Gr.regs[a]? = some (some y) →
      (c.isWbaddr a = true ∨ c.isConst0 a = true) → Ev env c Gr a)
    {a : ID} {y : Val} (hh : c.held a = true) (hc0 : c.isConst0 a = true)
    (hy : Gr.regs[a]? = some (some y)) : y = .int .w32 0 := by
  obtain ⟨hK, E, hE, haE⟩ := S.lazy_held hall hh (.inr hc0)
  obtain ⟨wa, hz⟩ := lazy_of_const0 hc0
  obtain ⟨ce, hwf⟩ := S.wf
  by_cases hb : b = c.f.entry
  · have hBE : B = E := by have := S.hB; rw [hb, hE] at this; cases this; rfl
    subst hBE
    obtain ⟨u, y', hu, hy', hev'⟩ := hev hb a haE y hy (.inr hc0)
    rw [hy] at hy'; cases hy'
    have hl := (ctxOf_spec S.ctx).2.2.2.2.2
    rw [hz] at hl
    obtain ⟨-, ⟨w, hw, hop, hai, -, hty⟩, -⟩ := lazyOK_some hl
    obtain ⟨u', w', hu', hw', hsame, -⟩ :=
      keptMarks_spec (by rw [← (ctxOf_spec S.ctx).2.2.2.1]; exact hK)
    rw [hu] at hu'; cases hu'
    rw [hw] at hw'; cases hw'
    obtain ⟨-, hop', hty', hai', -, -⟩ := sameV_parts hsame
    obtain ⟨v, hv, hvid, -⟩ := hwf.valueId _ _ ⟨S.hb, S.hB⟩ a haE
    rw [hu] at hv; cases hv
    exact eval_const0 hev' (hop'.trans hop) (hai'.trans hai) (by rw [hty']; exact hty)
      (by rw [hvid]; exact hu)
  · have hnB : a ∉ B.values := fun haB =>
      hb (hwf.valueOnce b B c.f.entry E ⟨S.hb, S.hB⟩ ⟨hwf.entry, hE⟩ a haB haE)
    rw [hout a hnB, ← hA.held a hh, (hA.lazy hb _ _ hz).2] at hy
    cases hy
    rfl

/-- **The reference frame's facts.** -/
theorem grOK (S : Setup c b B rs l) (hall : ∀ b' ∈ c.f.blocks, c.blockOK b' = true) {env : Env}
    {frS frT : Frame} {i : Nat} (hA : SimAt env c frS frT b i) {Gr : Frame}
    (hfr : Gr = { frS with regs := Gr.regs }) (hsinv : SInv MemOK Gr)
    (hout : ∀ a, a ∉ B.values → Gr.regs[a]? = frS.regs[a]?)
    (hev : b = c.f.entry → ∀ a ∈ B.values, ∀ y, Gr.regs[a]? = some (some y) →
      (c.isWbaddr a = true ∨ c.isConst0 a = true) → Ev env c Gr a)
    (hO : OutDef c B Gr) : GrOK c B rs Gr frS := by
  refine ⟨hfr, ?_, fun a M h => (hsinv.2 a _ h).mem, hO⟩
  intro a z y hh hq hy
  rcases role_of_held (rs := rs) hh with hρ | hρ | hρ
  · simp only [QR, hρ] at hq
    rw [hq] at hy; cases hy; rfl
  · simp only [QR, hρ] at hq
    rw [hq, S.gr_wbaddr hall hA hout hev hh (roleOf_wbaddr_inv hρ) hy]
  · simp only [QR, hρ] at hq
    rw [hq, S.gr_const0 hall hA hout hev hh (roleOf_const0_inv hρ) hy]

/-- **The target at the chain's entry.** -/
theorem regs0 (S : Setup c b B rs l) {env : Env} {frS frT : Frame} {i : Nat}
    (hA : SimAt env c frS frT b i) {Gr : Frame} (hG : GrOK c B rs Gr frS)
    (hout : ∀ a, a ∉ B.values → Gr.regs[a]? = frS.regs[a]?) :
    Regs c b B rs Gr frS frT 0 frT := by
  refine ⟨hA.fr, hA.sizeT, fun a ha => ?_, fun _ _ _ => rfl⟩
  rcases ha with ⟨hh, hnB, y, hy⟩ | ⟨j, hj, -⟩ | ⟨hb, hl⟩
  · have hT : frT.regs[a]? = some (some y) := by rw [hA.held a hh, ← hout a hnB, hy]
    refine ⟨y, hT, ?_⟩
    rcases role_of_held (rs := rs) hh with hρ | hρ | hρ
    · simp only [QR, hρ]; exact hy
    · have hq : QR c rs Gr a (.ptr flagPtr) := by simp only [QR, hρ]
      have := hG.held a _ y hh hq hy
      simp only [QR, hρ]; exact this.symm
    · have hq : QR c rs Gr a (.int .w32 0) := by simp only [QR, hρ]
      have := hG.held a _ y hh hq hy
      simp only [QR, hρ]; exact this.symm
  · exact absurd hj (Nat.not_lt_zero _)
  · have hL := hA.lazy hb
    rcases hl with h | h
    · obtain ⟨c0, hz⟩ := lazy_of_wbaddr h
      exact ⟨_, (hL _ _ hz).1, by simp only [QR, roleOf_wbaddr (rs := rs) h]⟩
    · obtain ⟨wa, hz⟩ := lazy_of_const0 h
      exact ⟨_, (hL _ _ hz).2,
        by simp only [QR, roleOf_const0 (rs := rs) h (isWbaddr_of_const0 S.ctx h)]⟩

/-- **The `Phi`s of the chain's entry** take the source's arguments. -/
theorem phis0 (S : Setup c b B rs l) {env : Env} {frS frT : Frame} {i : Nat}
    (hA : SimAt env c frS frT b i) {Gr : Frame}
    (hphi : ∀ x ∈ B.values, ∀ u, c.f.value? x = some u → u.op = .Phi →
      ∃ a y, u.args[i]? = some a ∧ frS.regs[a]? = some (some y) ∧
        Gr.regs[x]? = some (some (y.retype ((Ctx.make c.tabs c.f).tys[x]?.getD .other)))) :
    Phis c b rs Gr 0 frT i := by
  intro s hs x hx v hv hp
  obtain ⟨hρ, -, hxB, u, hu, hsame, hargs⟩ := S.phi_seg0 hs hx hv hp
  obtain ⟨-, hop, hty, -, -, hargsEq⟩ := sameV_parts hsame
  obtain ⟨a, y, ha, hy, hGx⟩ := hphi x hxB u hu (hop.trans hp)
  refine ⟨a, y, by rw [← hargsEq]; exact ha, ?_, ?_⟩
  · rw [hA.held a (hargs a (Array.mem_of_getElem? ha))]; exact hy
  · simp only [QR, hρ]
    rw [hGx, tys_of_value hu, tys_of_value hv, hty]

end Setup

end GoFV.Proof.WB

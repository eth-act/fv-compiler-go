import GoFV.Proof.Pass.SchedLWalk
import GoFV.Proof.RefineSched
import GoFV.Proof.AvailL
import GoFV.Proof.Pass.CopyElimL
import GoFV.Proof.CheckFacts

variable [GoFV.SSA.Sem.Addrs]

/-!
# `schedule` refines its input: `runSched` of the output against `runLF` of the input

`refinesSchedLF_of_rel`: if `f` passes `check` and `scheduleCheck tabs f g` holds (`SchedRel`),
every returning or panicking `runLF` of `f` (`runL`'s `kahn` order, memory ops faulting) is a
`runSched` of `g` (`b.Values` order). Lock-step simulation (`runLoopL_sim`) along the same blocks
and edges with the invariant `AtS` at each block entry: the target's frame agrees with the
source's on every value that is no nil check or `SPanchored` (`Agree`); the source's frame is
typed and has lemma (D) for the strict dominators (`DInvL`); every `Phi` argument read along the
edge has a register, a nil check's equal to its pointer's (`ncFact`, the nil-check equation at
the predecessor). Per block (`stepS`): the `Phi`s agree (`bstep`), the values run by
`walk_ok`/`walk_panic`, and the terminators read their controls bypassed by `rep`, whose
registers equal the source's (`CopyElim.stepTermL_copyRel`, `Dead.stepTermL_rel`).
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

/-- The block entries `runLoopL` (mode `md`, context `ctx`) reaches from block `b` entered along
edge `i` with frame `fr`: block steps that continue along an edge. -/
inductive ReachL (md : LMode) (env : Env) (ctx : Ctx) : Frame → ID → Nat → Frame → ID → Nat → Prop
  | refl (fr : Frame) (b : ID) (i : Nat) : ReachL md env ctx fr b i fr b i
  | step {fr fr' fr'' : Frame} {b b'' : ID} {i i'' : Nat} {e : Edge} :
      blockStepL md env ctx fr b i = .goto fr' e → ReachL md env ctx fr' e.b e.i fr'' b'' i'' →
      ReachL md env ctx fr b i fr'' b'' i''

/-- At the entry of block `b` along edge `i` with frame `fr` (mode `md`): after the block's
`Phi`s and any prefix of its `runL` order, every pointer-shaped value that a nil check of `f`
checks reads nil or a pointer that is not wild (`NilRegsOK`). -/
def NilPtrsAt (md : LMode) (env : Env) (tabs : Tables) (f : Func) (fr : Frame) (b : ID) (i : Nat) :
    Prop :=
  ∀ blk ps o k H, f.block? b = some blk →
    blk.values.toList.filterMapM (phiStepL md (Ctx.makeL tabs f) fr i) = .ok ps →
    ((Ctx.makeL tabs f).sched[b]?).join = some o →
    evalAllL md env (Ctx.makeL tabs f) { fr with regs := setPhis ps fr.regs } (o.toList.take k) =
      .ok H →
    NilRegsOK tabs f H

/-- `NilPtrsAt` at every block entry reached from `(fr, b, i)`. -/
def NilPtrsFrom (md : LMode) (env : Env) (tabs : Tables) (f : Func) (fr : Frame) (b : ID)
    (i : Nat) : Prop :=
  ∀ fr' b' i', ReachL md env (Ctx.makeL tabs f) fr b i fr' b' i' → NilPtrsAt md env tabs f fr' b' i'

/-- **Checked pointers are valid** (`docs/plans/semantics2.md` §6): on the input `args`, `mem`,
in every state `runLF` of `f` reaches (a block entry, after its `Phi`s and any prefix of its
order), every pointer-shaped value (`.ptr`) that a nil check of `f` checks reads nil or a pointer
that is not wild, once it has a register. A Go-level assumption: a Go pointer is nil or points
into an allocated object (the runtime throws on a pointer in the nil page, `invalid pointer found
on stack`); `unsafe` code that forges a wild pointer is outside the model. It covers only checked
pointers: a compiler-made `nil + k` (an offset from a nil base) may be computed before the check
of the base panics. `schedule` may move a nil check of such a value before a fault on the same
memory (`ScheduleCheck.nilPtrSwap`). -/
def NilPtrsOK (tabs : Tables) (f : Func) (env : Env) (args : List Val) (mem : Mem) : Prop :=
  NilPtrsFrom ⟨f.lowered, true⟩ env tabs f (entryFrame env (Ctx.makeL tabs f) args mem) f.entry 0

/-- `NilRegsOK` holds in every frame when no nil check of `f` checks a pointer-shaped value. -/
theorem nilRegsOK_of_none {tabs : Tables} {f : Func}
    (h : f.valueTab.all (fun o => o.all fun v => !v.op.nilCheck ||
      (v.args[0]?.all fun q => !GoFV.Opt.ScheduleCheck.ptrShape
        ((Ctx.makeL tabs f).tys[q]?.getD .other))) = true)
    (fr : Frame) : NilRegsOK tabs f fr := by
  intro y vy q hy hnc hq hsh z _
  simp only [Func.value?, Option.join_eq_some_iff] at hy
  obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.1 hy
  have h1 := Array.all_eq_true.1 h y hlt
  rw [hget] at h1
  simp [hnc, hq, hsh] at h1

/-- `NilPtrsOK` holds when no nil check of `f` checks a pointer-shaped value. -/
theorem nilPtrsOK_of_none {tabs : Tables} {f : Func}
    (h : f.valueTab.all (fun o => o.all fun v => !v.op.nilCheck ||
      (v.args[0]?.all fun q => !GoFV.Opt.ScheduleCheck.ptrShape
        ((Ctx.makeL tabs f).tys[q]?.getD .other))) = true)
    (env : Env) (args : List Val) (mem : Mem) : NilPtrsOK tabs f env args mem :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ => nilRegsOK_of_none h _

end GoFV.Proof

namespace GoFV.Proof.SchedL

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.ScheduleCheck GoFV.Proof Dom

variable {tabs : Tables} {f g : Func} {md : LMode} {env : Env}

/-- `f` is checked (well formed, certified dominator tree) and `g` is a scheduling of it. -/
structure Setup (tabs : Tables) (f g : Func) : Prop where
  wf : ∃ ce, WF ce f
  cf : CertOK f
  rel : SchedRel tabs f g

/-- The simulation invariant at the entry of block `bid` along edge `i`: source frame `frS`,
target frame `frT`. -/
structure AtS (md : LMode) (env : Env) (tabs : Tables) (f : Func) (frS frT : Frame) (bid : ID)
    (i : Nat) : Prop where
  tree : bid ∈ f.blocks ∧ ((make f).depthOf bid).isSome
  size : frS.regs.size = f.valueTab.size
  sizeT : frT.regs.size = frS.regs.size
  frEq : frT = { frS with regs := frT.regs }
  typed : TypedL md (Ctx.makeL tabs f) frS
  up : DInvL md env (Ctx.makeL tabs f) (fun a => Anc (make f) a bid ∧ a ≠ bid) frS
  agree : Agree f frS frT
  phi : ∀ blk z v a, f.block? bid = some blk → z ∈ blk.values → f.value? z = some v →
    v.op = .Phi → v.args[i]? = some a →
    (∃ y, frS.regs[a]? = some (some y)) ∧ (isNC f a = true → frS.regs[rep f a]? = frS.regs[a]?)
  /-- An image per parameter (`argOK` pieces evaluate). -/
  img : frS.images.size = (Ctx.makeL tabs f).params.size
  /-- No closure context (`GetClosurePtr` is `poison`). -/
  clo : frS.closure = none
  /-- The pointer-shaped parameter pieces read nil or pointers that are not wild. -/
  argPtr : ArgPtrsAt md env tabs f frS
  /-- Checked pointer-shaped values read nil or pointers that are not wild from here on. -/
  nilPtr : NilPtrsFrom md env tabs f frS bid i

/-! ## Facts of `f` -/

theorem placed_id {ce : CheckEnv} (hwf : WF ce f) {a : ID} {v : Value} (h : Placed f a v) :
    v.id = a := by
  obtain ⟨hv, hb, blk, hblk, hx⟩ := h
  obtain ⟨v', hv', hid, -⟩ := hwf.valueId _ blk ⟨hb, hblk⟩ a hx
  rw [hv] at hv'; cases hv'; exact hid

theorem placed_listed {ce : CheckEnv} (hwf : WF ce f) {a : ID} (ha : Listed f a) :
    ∃ v, Placed f a v ∧ blockOf f a = v.block := by
  obtain ⟨bid, b, ⟨hbm, hbb⟩, hab⟩ := ha
  obtain ⟨v, hp, -, -⟩ := placed_of_mem hwf hbm hbb hab
  exact ⟨v, hp, by unfold blockOf; rw [hp.1]; rfl⟩

theorem phi_not_nc {a : ID} {v : Value} (hv : f.value? a = some v) (hp : v.op = .Phi) :
    isNC f a = false := by
  rw [isNC_of hv, hp]; rfl

theorem phi_not_spa {a : ID} {v : Value} (hv : f.value? a = some v) (hp : v.op = .Phi) :
    isSPA f a = false := by
  rw [isSPA_of hv, hp]; rfl

/-- **A bypass step stays in a set of tree blocks closed under ancestors**: a value placed in such
a block bypasses (`rep1`) to a value placed in one (an argument of a non-`Phi` value is placed in
an ancestor of its block). -/
theorem rep1_placed {ce : CheckEnv} (hwf : WF ce f) (hc : CertOK f) {A : ID → Prop}
    (hAc : ∀ b b', A b' → Anc (make f) b b' → A b) (hAt : ∀ b, A b → ((make f).depthOf b).isSome)
    {z : ID} {vz : Value} (hpz : Placed f z vz) (hA : A vz.block) :
    ∃ vp, Placed f (rep1 f z) vp ∧ A vp.block := by
  by_cases hra : rep1 f z = z
  · exact ⟨vz, by rw [hra]; exact hpz, hA⟩
  · have hm : rep1 f z ∈ vz.args := Array.mem_of_getElem? (rep1_arg0 hpz.1 hra)
    have hanp : vz.op ≠ .Phi := fun hp =>
      hra (rep1_self (phi_not_nc hpz.1 hp) (phi_not_spa hpz.1 hp))
    obtain ⟨hvbm, blk, hblk, hab⟩ := hpz.2
    have hanc2 := hc.domRel.uses hvbm hblk (hAt _ hA) hab hpz.1 hanp hm
    obtain ⟨vr, hpr, hbr⟩ := placed_listed hwf
      (hwf.argListed vz.block blk z vz ⟨⟨hvbm, hblk⟩, hab, hpz.1⟩ _ hm)
    rw [hbr] at hanc2
    exact ⟨vr, hpr, hAc _ _ hA hanc2⟩

/-- The strict ancestors of a block are closed under ancestors. -/
theorem sanc_closed (hc : CertOK f) {bid : ID} (b b' : ID)
    (h : Anc (make f) b' bid ∧ b' ≠ bid) (hb : Anc (make f) b b') :
    Anc (make f) b bid ∧ b ≠ bid :=
  ⟨hc.domRel.trans hb h.1, fun he => h.2 (by rw [he] at hb; exact hc.domRel.antisymm h.1 hb)⟩

/-- **A nil check available in a frame holds its chain's end's register** (lemma (D) along the
chain, whose values are placed in ancestors, and the shape condition of its use). -/
theorem ncFact {ce : CheckEnv} (hwf : WF ce f) (hc : CertOK f) {A : ID → Prop} {fr : Frame}
    (hAc : ∀ b b', A b' → Anc (make f) b b' → A b) (hAt : ∀ b, A b → ((make f).depthOf b).isSome)
    (hD : DInvL md env (Ctx.makeL tabs f) A fr) (ht : TypedL md (Ctx.makeL tabs f) fr)
    {a : ID} {va : Value} (hpa : Placed f a va) (hA : A va.block) {user : Option Value} {k : Nat}
    (hu : useOK tabs (Ctx.makeL tabs f).tys f user k a = true) (hnc : isNC f a = true) :
    fr.regs[rep f a]? = fr.regs[a]? := by
  refine ncEq (env := env) (fun z => ∃ vz, Placed f z vz ∧ A vz.block)
    (fun z ⟨vz, hpz, hAz⟩ hzn => ?_) ht
    _ a (use_chain hu hnc) (Nat.le_refl _) ⟨va, hpa, hA⟩ hnc
  obtain ⟨y, hy, hev⟩ := hD z vz (by rw [makeL_f]; exact hpz) hAz
  have hnp : vz.op ≠ .Phi := fun h => by rw [phi_not_nc hpz.1 h] at hzn; cases hzn
  exact ⟨⟨vz, y, hpz.1, placed_id hwf hpz, hy, hev hnp⟩, rep1_placed hwf hc hAc hAt hpz hAz⟩

/-- **A nil check available in a frame holds a pointer outside the nil block.** -/
theorem ncFactNN {ce : CheckEnv} (hwf : WF ce f) {A : ID → Prop} {fr : Frame}
    (hD : DInvL md env (Ctx.makeL tabs f) A fr) (ht : TypedL md (Ctx.makeL tabs f) fr)
    {a : ID} {va : Value} (hpa : Placed f a va) (hA : A va.block) {user : Option Value} {k : Nat}
    (hu : useOK tabs (Ctx.makeL tabs f).tys f user k a = true) (hnc : isNC f a = true) :
    ∀ z, fr.regs[a]? = some (some z) → NonNil z := by
  obtain ⟨y, hy, hev⟩ := hD a va (by rw [makeL_f]; exact hpa) hA
  have hnp : va.op ≠ .Phi := fun h => by rw [phi_not_nc hpa.1 h] at hnc; cases hnc
  obtain ⟨hne, hsh⟩ := nc_step1 hu hnc
  exact ncNonNil hpa.1 (placed_id hwf hpa) hnc ⟨y, hy, hev hnp⟩ ht hsh hne

theorem symAddrOp_phi : symAddrOp .Phi = false := by decide

/-! ## Block entries -/

private theorem enterBlockL_ok_split' {ctx : Ctx} {fr fr' : Frame} {b : Block} {i : Nat}
    (h : enterBlockL md env ctx fr b i = .ok fr') :
    ∃ ps o, b.values.toList.filterMapM (phiStepL md ctx fr i) = .ok ps ∧
      (ctx.sched[b.id]?).join = some o ∧
      evalAllL md env ctx { fr with regs := setPhis ps fr.regs } o.toList = .ok fr' := by
  rw [enterBlockL_eq] at h
  cases hps : b.values.toList.filterMapM (phiStepL md ctx fr i) with
  | panic e m => rw [hps] at h; cases h
  | stuck msg => rw [hps] at h; cases h
  | ok ps =>
    rw [hps] at h
    change (Res.ofOption _ (ctx.sched[b.id]?).join).bind _ = _ at h
    cases ho : (ctx.sched[b.id]?).join with
    | none => rw [ho] at h; cases h
    | some o =>
      rw [ho] at h
      exact ⟨ps, o, rfl, rfl, h⟩

private theorem enterBlockL_of' {ctx : Ctx} {fr : Frame} {b : Block} {i : Nat}
    {ps : List (ID × Val)} {o : Array ID}
    (hps : b.values.toList.filterMapM (phiStepL md ctx fr i) = .ok ps)
    (ho : (ctx.sched[b.id]?).join = some o) :
    enterBlockL md env ctx fr b i =
      evalAllL md env ctx { fr with regs := setPhis ps fr.regs } o.toList := by
  rw [enterBlockL_eq, hps]
  change (Res.ofOption _ (ctx.sched[b.id]?).join).bind _ = _
  rw [ho]
  rfl

/-- **The `Phi`s of a block entry agree**, and the block's orders and frames after them are a
`BStep`. -/
theorem bstep (Su : Setup tabs f g) {frS frT : Frame} {bid : ID} {i : Nat}
    (hA : AtS md env tabs f frS frT bid i) {fb gb : Block} (hfb : f.block? bid = some fb)
    (hgb : g.block? bid = some gb)
    (hperm : gb.values.toList.Perm (fb.values.toList.filter (!isSPA f ·)))
    {oS oT : Array ID} (hsS : schedule f fb = some oS)
    (hoT : oT.toList = gb.values.toList.filter (!isPhi g ·)) (htopoT : topoB g oT.toList = true)
    (hord : orderOK tabs (Ctx.makeL tabs f).params (Ctx.makeL tabs f).tys f f.valueTab.size oS oT =
      true)
    {ps : List (ID × Val)}
    (hps : fb.values.toList.filterMapM (phiStepL md (Ctx.makeL tabs f) frS i) = .ok ps) :
    ∃ psT, gb.values.toList.filterMapM (phiStepL md (Ctx.makeSched tabs g) frT i) = .ok psT ∧
      BStep tabs f g md oS.toList oT.toList { frS with regs := setPhis ps frS.regs }
        { frT with regs := setPhis psT frT.regs } := by
  obtain ⟨ce, hwf⟩ := Su.wf
  have S := Su.rel
  have hc := Su.cf
  obtain ⟨hb, htr⟩ := hA.tree
  have hnd := hwf.valuesNodup bid fb ⟨hb, hfb⟩
  have hown := valuesOwn hwf hb hfb
  obtain ⟨ond, otopo, omem⟩ := schedule_topo hown hnd hsS
  have hcF : (Ctx.makeL tabs f).f = f := makeL_f tabs f
  have hcG : (Ctx.makeSched tabs g).f = g := makeSched_f tabs g
  have hfv : ∀ z ∈ fb.values, ∃ v, f.value? z = some v ∧ v.id = z ∧ v.block = bid :=
    fun z hz => hwf.valueId bid fb ⟨hb, hfb⟩ z hz
  have hgmem : ∀ z, z ∈ gb.values ↔ z ∈ fb.values ∧ isSPA f z = false := fun z => by
    rw [← Array.mem_toList_iff, hperm.mem_iff, List.mem_filter, Array.mem_toList_iff]
    simp
  have hndT : gb.values.toList.Nodup := hperm.nodup_iff.2 (hnd.filter _)
  -- the source's `Phi`s
  obtain ⟨-, hsome, hall⟩ := filterMapM_phiL hps
  have hphiS : ∀ z ∈ fb.values, ∀ v, f.value? z = some v → v.op = .Phi →
      ∃ a y, v.args[i]? = some a ∧ frS.regs[a]? = some (some y) := by
    intro z hz v hv hp
    rcases hall z (Array.mem_toList_iff.2 hz) with ⟨p, hp', rfl⟩ | hn
    · obtain ⟨-, v', a, y, hv', -, ha, hy, -⟩ := phiStepL_some (hsome p hp')
      rw [hcF, hv] at hv'; cases hv'
      exact ⟨a, y, ha, hy⟩
    · obtain ⟨v', hv', hne⟩ := phiStepL_none hn
      rw [hcF, hv] at hv'; cases hv'; exact absurd hp hne
  -- a `Phi`'s argument, bypassed, holds the source's register in the target
  have hphiArg : ∀ z ∈ fb.values, ∀ v, f.value? z = some v → v.op = .Phi → ∀ a,
      v.args[i]? = some a → frT.regs[rep f a]? = frS.regs[a]? := by
    intro z hz v hv hp a ha
    have hu := S.argUse hv ha
    obtain ⟨hrn, hrs, hspa, -⟩ := use_rep hu
    have hsa : isSPA f a = false := by
      cases h : isSPA f a
      · rfl
      · obtain ⟨-, hsym, -⟩ := hspa h
        simp [hp, symAddrOp_phi] at hsym
    rw [hA.agree _ hrn hrs]
    cases hn : isNC f a
    · rw [rep_self hn hsa]
    · exact (hA.phi fb z v a hfb hz hv hp ha).2 hn
  -- the target's `Phi`s
  have hstepT : ∀ z ∈ gb.values.toList, ∃ o, phiStepL md (Ctx.makeSched tabs g) frT i z = .ok o := by
    intro z hz
    obtain ⟨hzf, hzs⟩ := (hgmem z).1 (Array.mem_toList_iff.1 hz)
    obtain ⟨fv, hfv', -, -⟩ := hfv z hzf
    obtain ⟨gv, hgv, hr⟩ := S.fval hfv' (fun h => by rw [isSPA_of hfv', h] at hzs; cases hzs)
    unfold phiStepL
    rw [hcG, hgv]
    dsimp only
    split
    · rename_i hph
      have hp : fv.op = .Phi := by rw [← hr.op]; simpa using hph
      obtain ⟨a, y, ha, hy⟩ := hphiS z hzf fv hfv' hp
      have heq := hphiArg z hzf fv hfv' hp a ha
      have hga : gv.args[i]? = some (rep f a) := (argsF_g hgv hr ha).1
      simp only [hga, heq, hy, Option.join_some]
      exact ⟨_, rfl⟩
    · exact ⟨none, rfl⟩
  obtain ⟨psT, hpsT⟩ := filterMapM_phiL_ok hstepT
  obtain ⟨-, -, hTkeep, hTphi⟩ := phisL_spec hndT hpsT
  obtain ⟨-, hSall, hSkeep, hSphi⟩ := phisL_spec hnd hps
  -- the frames after the `Phi`s agree
  have hagree : Agree f { frS with regs := setPhis ps frS.regs }
      { frT with regs := setPhis psT frT.regs } := by
    intro a hn hs
    show (setPhis psT frT.regs)[a]? = (setPhis ps frS.regs)[a]?
    by_cases hph : a ∈ fb.values ∧ ∃ v, f.value? a = some v ∧ v.op = .Phi
    · obtain ⟨haf, v, hv, hp⟩ := hph
      obtain ⟨gv, hgv, hr⟩ := S.fval hv (fun h => by rw [hp] at h; cases h)
      have hlt : a < frS.regs.size := by rw [hA.size]; exact lt_of_value? hv
      obtain ⟨x, y, hx, hy, hS⟩ := hSphi a haf v (by rw [hcF]; exact hv) hp hlt
      have heq := hphiArg a haf v hv hp x hx
      have hltT : a < frT.regs.size := by rw [hA.sizeT]; exact hlt
      obtain ⟨x', y', hx', hy', hT⟩ := hTphi a ((hgmem a).2 ⟨haf, hs⟩) gv
        (by rw [hcG]; exact hgv) (by rw [hr.op]; exact hp) hltT
      have hxx : x' = rep f x := by rw [(argsF_g hgv hr hx).1] at hx'; cases hx'; rfl
      subst hxx
      rw [heq, hy] at hy'; cases hy'
      have hty : gv.type = v.type := hr.type.resolve_left (by rw [hp]; decide)
      rw [hS, hT, tys_eq S hv hgv hty]
    · have hkS : (setPhis ps frS.regs)[a]? = frS.regs[a]? := hSkeep a (by
        by_cases haf : a ∈ fb.values
        · obtain ⟨v, hv, -, -⟩ := hfv a haf
          exact .inr ⟨v, by rw [hcF]; exact hv, fun hp => hph ⟨haf, v, hv, hp⟩⟩
        · exact .inl haf)
      have hkT : (setPhis psT frT.regs)[a]? = frT.regs[a]? := hTkeep a (by
        by_cases hag : a ∈ gb.values
        · obtain ⟨haf, -⟩ := (hgmem a).1 hag
          obtain ⟨v, hv, -, -⟩ := hfv a haf
          obtain ⟨gv, hgv, hr⟩ := S.fval hv (fun h => by rw [isSPA_of hv, h] at hs; cases hs)
          exact .inr ⟨gv, by rw [hcG]; exact hgv, fun hp => hph ⟨haf, v, hv, by rw [← hr.op]; exact hp⟩⟩
        · exact .inl hag)
      rw [hkS, hkT, hA.agree a hn hs]
  -- the arguments from outside the block
  have hout : Out (Ctx.makeL tabs f).tys f oS.toList { frS with regs := setPhis ps frS.regs } := by
    intro x hx a ha haS
    obtain ⟨hxf, v, hv, hnp⟩ := (omem x).1 hx
    have hav : a ∈ v.args := by rw [argsF_of hv] at ha; exact Array.mem_toList_iff.1 ha
    obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 hav
    have hu := S.argUse hv hk
    have hanc := hc.domRel.uses hb hfb htr hxf hv hnp hav
    obtain ⟨va, hpa, hba⟩ := placed_listed hwf (hwf.argListed bid fb x v ⟨⟨hb, hfb⟩, hxf, hv⟩ a hav)
    rw [hba] at hanc
    have hnotin : ∀ z (vz : Value), Placed f z vz → vz.block ≠ bid → z ∉ fb.values :=
      fun z vz hpz hne hzf => by
        obtain ⟨vz', hvz', -, hvzb⟩ := hfv z hzf
        rw [hpz.1] at hvz'; cases hvz'; exact hne hvzb
    have hkeep : ∀ z (vz : Value), Placed f z vz → vz.block ≠ bid →
        (setPhis ps frS.regs)[z]? = frS.regs[z]? :=
      fun z vz hpz hne => hSkeep z (.inl (hnotin z vz hpz hne))
    by_cases hvb : va.block = bid
    · -- a `Phi` of the block
      have haf : a ∈ fb.values := by
        obtain ⟨-, -, blk, hblk, hab⟩ := hpa
        rw [hvb, hfb] at hblk; cases hblk; exact hab
      have hap : va.op = .Phi := by
        by_cases hp : va.op = .Phi
        · exact hp
        · exact absurd ((omem a).2 ⟨haf, va, hpa.1, hp⟩) haS
      have hn := phi_not_nc hpa.1 hap
      have hs := phi_not_spa hpa.1 hap
      rw [rep_self hn hs]
      have hlt : a < frS.regs.size := by rw [hA.size]; exact lt_of_value? hpa.1
      obtain ⟨-, y, -, -, hS⟩ := hSphi a haf va (by rw [hcF]; exact hpa.1) hap hlt
      have hnn : isNN (Ctx.makeL tabs f).tys f a = false := by
        cases h : isNN (Ctx.makeL tabs f).tys f a
        · rfl
        · obtain ⟨v', hv', hcs⟩ := isNN_cases h
          rw [hpa.1] at hv'; cases hv'
          rcases hcs with h' | hop | ⟨hop, -⟩
          · exact absurd (hn.symm.trans h') (by decide)
          · rw [hap] at hop; cases hop
          · rcases hop with h' | h' <;> rw [hap] at h' <;> cases h'
      exact ⟨⟨_, hS⟩, haS, ⟨_, hS⟩, fun h => absurd (hn.symm.trans h) (by decide),
        fun h => absurd (hnn.symm.trans h) (by decide)⟩
    · -- a value of a strict dominator
      have hstrict : Anc (make f) va.block bid ∧ va.block ≠ bid := ⟨hanc, hvb⟩
      obtain ⟨y, hy, -⟩ := hA.up a va (by rw [hcF]; exact hpa) hstrict
      have hcl : ∀ z (vz : Value), Placed f z vz → Anc (make f) vz.block bid ∧ vz.block ≠ bid →
          ∃ vp, Placed f (rep1 f z) vp ∧ Anc (make f) vp.block bid ∧ vp.block ≠ bid :=
        fun _ _ hpz hAz => rep1_placed hwf hc (sanc_closed hc) (fun _ h => hc.domRel.left h.1)
          hpz hAz
      have hrep : ∃ vr, Placed f (rep f a) vr ∧ Anc (make f) vr.block bid ∧ vr.block ≠ bid := by
        by_cases hs : isSPA f a = true
        · rw [(use_spa hu hs).2.2.2.2.2.2]; exact hcl _ _ hpa hstrict
        · cases hn : isNC f a
          · rw [rep_self hn (by simpa using hs)]; exact ⟨va, hpa, hstrict⟩
          · exact chain_closed
              (fun z => ∃ vz, Placed f z vz ∧ Anc (make f) vz.block bid ∧ vz.block ≠ bid)
              (fun z ⟨vz, hpz, hAz⟩ _ => hcl _ _ hpz hAz) _ a (use_chain hu hn) (Nat.le_refl _)
              ⟨va, hpa, hstrict⟩ hn
      obtain ⟨vr, hpr, hancr, hner⟩ := hrep
      obtain ⟨yr, hyr, -⟩ := hA.up (rep f a) vr (by rw [hcF]; exact hpr) ⟨hancr, hner⟩
      refine ⟨⟨y, by rw [hkeep a va hpa hvb, hy]⟩, fun hm => hnotin _ vr hpr hner ((omem _).1 hm).1,
        ⟨yr, by rw [hkeep _ vr hpr hner, hyr]⟩, fun hn => ?_, fun hn z hz => ?_⟩
      · show (setPhis ps frS.regs)[rep f a]? = (setPhis ps frS.regs)[a]?
        rw [hkeep _ vr hpr hner, hkeep a va hpa hvb]
        exact ncFact hwf hc (sanc_closed hc) (fun _ h => hc.domRel.left h.1) hA.up hA.typed hpa
          hstrict hu hn
      · have hz' : frS.regs[a]? = some (some z) := by
          rw [← hkeep a va hpa hvb]; exact hz
        obtain ⟨va', hva', hcs⟩ := isNN_cases hn
        rw [hpa.1] at hva'; cases hva'
        rcases hcs with hnc | hop | ⟨hop, hw⟩
        · exact (ncFactNN hwf hA.up hA.typed hpa hstrict hu hnc z hz').not_nilBase
        · have hnp : va.op ≠ .Phi := by rw [hop]; decide
          obtain ⟨y', hy', hev⟩ := hA.up a va (by rw [hcF]; exact hpa) hstrict
          rw [hz'] at hy'; cases hy'
          exact evalValueL_clo hop hA.clo (hev hnp)
        · have hnp : va.op ≠ .Phi := by rcases hop with h | h <;> rw [h] <;> decide
          obtain ⟨y', hy', hev⟩ := hA.up a va (by rw [hcF]; exact hpa) hstrict
          rw [hz'] at hy'; cases hy'
          exact (evalValueL_spg hop (by rw [placed_id hwf hpa]; exact hw) (hev hnp)).not_nilBase
  -- the pointer-shaped parameter pieces from outside the block
  have hargOut : ∀ x ∈ oS.toList, ∀ a ∈ argsF f x, a ∉ oS.toList →
      argPtr tabs (Ctx.makeL tabs f).params (Ctx.makeL tabs f).tys f a = true →
      ∀ z, (setPhis ps frS.regs)[a]? = some (some z) → PtrOK z := by
    intro x hx a ha haS hap z hz
    obtain ⟨hxf, v, hv, hnp⟩ := (omem x).1 hx
    have hav : a ∈ v.args := by rw [argsF_of hv] at ha; exact Array.mem_toList_iff.1 ha
    have hanc := hc.domRel.uses hb hfb htr hxf hv hnp hav
    obtain ⟨va, hpa, hba⟩ := placed_listed hwf (hwf.argListed bid fb x v ⟨⟨hb, hfb⟩, hxf, hv⟩ a hav)
    rw [hba] at hanc
    have hop : va.op = .ArgIntReg := by
      unfold argPtr at hap
      rw [hpa.1] at hap
      simp only [argOK, Bool.and_eq_true, beq_iff_eq] at hap
      exact hap.1.1.1
    have hnp' : va.op ≠ .Phi := by rw [hop]; decide
    have haf : a ∉ fb.values := fun haf => haS ((omem a).2 ⟨haf, va, hpa.1, hnp'⟩)
    have hvb : va.block ≠ bid := fun hvb => by
      obtain ⟨-, -, blk, hblk, hab⟩ := hpa
      rw [hvb, hfb] at hblk; cases hblk; exact haf hab
    obtain ⟨y, hy, hev⟩ := hA.up a va (by rw [hcF]; exact hpa) ⟨hanc, hvb⟩
    rw [hSkeep a (.inl haf), hy] at hz
    cases hz
    exact hA.argPtr a va hpa.1 hap z (hev hnp')
  -- the target order's members
  have htmem : ∀ x, x ∈ oT.toList ↔ x ∈ oS.toList ∧ isSPA f x = false := by
    intro x
    rw [hoT, List.mem_filter, Array.mem_toList_iff, hgmem, omem]
    constructor
    · rintro ⟨⟨hxf, hs⟩, hph⟩
      obtain ⟨v, hv, -, -⟩ := hfv x hxf
      obtain ⟨gv, hgv, hr⟩ := S.fval hv (fun h => by rw [isSPA_of hv, h] at hs; cases hs)
      refine ⟨⟨hxf, v, hv, fun hp => ?_⟩, hs⟩
      unfold isPhi at hph; rw [hgv] at hph; simp [hr.op, hp] at hph
    · rintro ⟨⟨hxf, v, hv, hnp⟩, hs⟩
      obtain ⟨gv, hgv, hr⟩ := S.fval hv (fun h => by rw [isSPA_of hv, h] at hs; cases hs)
      refine ⟨⟨hxf, hs⟩, ?_⟩
      unfold isPhi; rw [hgv]; simp [hr.op, hnp]
  refine ⟨psT, hpsT, ond, otopo, fun x hx v hv => ?_, fun x hx => ?_, ?_, topoB_iff htopoT, htmem,
    by rw [hA.frEq], by simp [setPhis_size, hA.sizeT], by simp [setPhis_size, hA.size], hagree, ?_,
    hout, fun i j x y hij hy hx hfy hfx k l hkl hxk hyl => orderOK_swap hord ond
      (fun z hz => by obtain ⟨-, v, hv, -⟩ := (omem z).1 hz; exact lt_of_value? hv)
      hij hy hx hfy hfx hkl hxk hyl,
    fun z hz => by obtain ⟨-, v, hv, -⟩ := (omem z).1 hz; exact lt_of_value? hv, hA.img, hA.clo,
    hargOut⟩
  · obtain ⟨hxf, -⟩ := (omem x).1 hx
    obtain ⟨v', hv', hid⟩ := hown x hxf
    rw [hv] at hv'; cases hv'; exact hid
  · obtain ⟨-, v, hv, -⟩ := (omem x).1 hx; exact ⟨v, hv⟩
  · rw [hoT]; exact hndT.filter _
  · exact typedL_phis hA.typed (by simp [setPhis_size]) hSkeep hSphi hSall

/-! ## The block step -/

/-- **One block step of `schedule`'s simulation.** -/
theorem stepS (Su : Setup tabs f g) (hmd : md.faulting = true) {frS frT : Frame} {bid : ID}
    {i : Nat} (hA : AtS md env tabs f frS frT bid i) :
    StepSim (fun frS frT b i => AtS md env tabs f frS frT b i)
      (blockStepL md env (Ctx.makeL tabs f) frS bid i)
      (blockStepL md env (Ctx.makeSched tabs g) frT bid i) := by
  obtain ⟨ce, hwf⟩ := Su.wf
  have S := Su.rel
  have hc := Su.cf
  obtain ⟨hb, htr⟩ := hA.tree
  unfold blockStepL
  rw [makeL_f, makeSched_f]
  cases hfb : f.block? bid with
  | none => exact True.intro
  | some fb =>
  obtain ⟨gb, hgb, hgid, hk, hai, hsu, -, hct, hperm⟩ := S.fblock hfb
  obtain ⟨fb', hfb', hfid⟩ := hwf.blockId bid hb
  rw [hfb] at hfb'; cases hfb'
  obtain ⟨oS, oT, gb', hsS, hsT, hgb', hoT, htopoT, hord⟩ := S.order hfb
  rw [hgb] at hgb'; cases hgb'
  have hsS' : schedule f fb = some oS := by rw [← sched_of_blockL (tabs := tabs) hfb]; exact hsS
  have hsSid : ((Ctx.makeL tabs f).sched[fb.id]?).join = some oS := by rw [hfid]; exact hsS
  have hsTid : ((Ctx.makeSched tabs g).sched[gb.id]?).join = some oT := by
    rw [hgid, hfid]; exact hsT
  rw [hgb]
  dsimp only
  cases hen : enterBlockL md env (Ctx.makeL tabs f) frS fb i with
  | stuck msg => exact True.intro
  | panic e m =>
    obtain ⟨ps, o, hps, ho, hev⟩ := enterBlockL_panic hen
    rw [hsSid] at ho; cases ho
    obtain ⟨psT, hpsT, B⟩ := bstep Su hA hfb hgb hperm hsS' hoT htopoT hord hps
    have hT := walk_panic S hmd B (hA.argPtr.regs rfl)
      (fun k H hk => hA.nilPtr _ _ _ (.refl _ _ _) fb ps oS k H hfb hps hsS hk) hev
    rw [enterBlockL_of' hpsT hsTid, hT]
    all_goals rfl
  | ok GS =>
    obtain ⟨ps, o, hps, ho, hev⟩ := enterBlockL_ok_split' hen
    rw [hsSid] at ho; cases ho
    obtain ⟨psT, hpsT, B⟩ := bstep Su hA hfb hgb hperm hsS' hoT htopoT hord hps
    have hcF : (Ctx.makeL tabs f).f = f := makeL_f tabs f
    obtain ⟨e1, e2, e3, e4⟩ := evalAllL_spec (ctx := Ctx.makeL tabs f) B.sNodup
      (by rw [hcF]; exact B.sTopo) (by rw [hcF]; exact B.sizeS) hev
    have hty := typedL_evalAll B.typed
      (fun x hx v hv => B.sOwn x hx v (by rw [hcF] at hv; exact hv)) e3 e4
    rw [hcF] at e4
    have Sr : Src tabs f md env _ GS oS.toList := ⟨e1, e2, e3, e4, hty⟩
    obtain ⟨GT, hGT, I⟩ := walk_ok S hmd B Sr oT.toList.length (Nat.le_refl _)
    rw [List.take_length] at hGT I
    have hTen : enterBlockL md env (Ctx.makeSched tabs g) frT gb i = .ok GT := by
      rw [enterBlockL_of' hpsT hsTid, hGT]
    rw [hTen]
    dsimp only
    -- after the block
    obtain ⟨hD, -, hGSsz⟩ := dinvL_enter hwf hc hb hfb hA.size hA.up hen
    have hGSty := typedL_enter hwf hb hfb hA.size hA.typed hen
    have hagree : Agree f GS GT := by
      intro a hn hs
      by_cases haT : a ∈ oT.toList
      · exact I.inP a haT ((B.tMem a).1 haT).1 hn
      · have haS : a ∉ oS.toList := fun h => haT ((B.tMem a).2 ⟨h, hs⟩)
        rw [I.out a haT, e3 a haS]; exact B.agree a hn hs
    have hGTfr : GT = { GS with regs := GT.regs } := frame_eq B.frT Sr.frH I.frT
    have hGTsz : GT.regs.size = GS.regs.size := by rw [I.size, B.size, e2]
    -- the controls, bypassed, hold the source's registers
    have hctl : ∀ c ∈ fb.controls, isNC f (rep f c) = false ∧ isSPA f (rep f c) = false ∧
        GS.regs[rep f c]? = GS.regs[c]? := by
      intro c hcm
      have hu := S.ctrlUse hfb hcm
      obtain ⟨hrn, hrs, hspa, -⟩ := use_rep hu
      refine ⟨hrn, hrs, ?_⟩
      have hsc : isSPA f c = false := by
        cases h : isSPA f c
        · rfl
        · obtain ⟨-, hsym, -⟩ := hspa h; simp at hsym
      cases hn : isNC f c
      · rw [rep_self hn hsc]
      · obtain ⟨vc, hpc, hbc⟩ := placed_listed hwf (hwf.ctrlListed bid fb ⟨hb, hfb⟩ c hcm)
        have hancc := hc.domRel.ctrlUse hb hfb htr hcm
        rw [hbc] at hancc
        exact ncFact hwf hc (fun _ _ h hb => hc.domRel.trans hb h) (fun _ h => hc.domRel.left h)
          hD hGSty hpc hancc hu hn
    cases hst : stepTermL GS fb with
    | stuck msg => exact True.intro
    | panic e m => exact absurd hst Dead.stepTermL_not_panic
    | ok n =>
    have hcs : ∀ (k : Nat) (c : ID) (y : Val), fb.controls[k]? = some c →
        GS.regs[c]? = some (some y) → ∃ c', gb.controls[k]? = some c' ∧
          GS.regs[c']? = some (some y) :=
      fun k c y hk' hy => ⟨rep f c, by rw [hct, Array.getElem?_map, hk']; rfl,
        by rw [(hctl c (Array.mem_of_getElem? hk')).2.2, hy]⟩
    have hstG := CopyElim.stepTermL_copyRel hk hsu hgid hai hcs hst
    have hag : ∀ c ∈ gb.controls, GT.regs[c]? = GS.regs[c]? := by
      intro c hc'
      rw [hct] at hc'
      obtain ⟨c0, hc0, rfl⟩ := Array.mem_map.1 hc'
      obtain ⟨hrn, hrs, -⟩ := hctl c0 hc0
      exact hagree _ hrn hrs
    rcases Dead.stepTermL_rel (b := gb) (b' := gb) (.inl rfl) rfl rfl hag hstG with
      ⟨k, e, rfl, he, -, hst'⟩ | ⟨rs, m, rfl, hst'⟩
    · have hgo : stepTermL GT gb = .ok (.goto e) := by rw [hst']; unfold succ; rw [he]; rfl
      rw [hgo]
      have hem : e ∈ fb.succs := by rw [← hsu]; exact Array.mem_of_getElem? he
      obtain ⟨kk, hkk⟩ := Array.mem_iff_getElem?.1 hem
      obtain ⟨heb, cblk, hcblk, hcp⟩ := hwf.succLink bid fb ⟨hb, hfb⟩ kk e hkk
      have hedge := Dom.edge hc hb hfb htr hem
      have himg : GS.images = frS.images := by rw [e1]
      have hbs : blockStepL md env (Ctx.makeL tabs f) frS bid i = .goto GS e := by
        unfold blockStepL
        rw [makeL_f, hfb]
        simp only [hen, hst]
      have hclo : GS.closure = frS.closure := by rw [e1]
      refine ⟨GT, rfl, ⟨heb, hedge.2.1⟩, by rw [hGSsz, hA.size], hGTsz, hGTfr, hGSty,
        dinvL_edge hc hb hfb htr hem hD, hagree, ?_, by rw [himg]; exact hA.img,
        by rw [hclo]; exact hA.clo, hA.argPtr.regs (by rw [e1]),
        fun fr' b' i' hr => hA.nilPtr fr' b' i' (.step hbs hr)⟩
      intro blk z v a hblk hz hv hp ha
      rw [hcblk] at hblk; cases hblk
      have hanc := hc.domRel.phiUse heb hcblk hedge.2.1 hz hv hp ha hcp htr
      obtain ⟨va, hpa, hba⟩ := placed_listed hwf
        (hwf.argListed e.b cblk z v ⟨⟨heb, hcblk⟩, hz, hv⟩ a (Array.mem_of_getElem? ha))
      rw [hba] at hanc
      obtain ⟨y, hy, -⟩ := hD a va (by rw [makeL_f]; exact hpa) hanc
      exact ⟨⟨y, hy⟩, fun hn => ncFact hwf hc (fun _ _ h hb => hc.domRel.trans hb h)
        (fun _ h => hc.domRel.left h) hD hGSty hpa hanc (S.argUse hv ha) hn⟩
    · rw [hst']
      exact ⟨rs, rfl, RefinesList.refl rs⟩

/-! ## Refinement -/

private theorem paramTys_makeL' (tabs : Tables) (f : Func) :
    (Ctx.makeL tabs f).paramTys = (Ctx.make tabs f).paramTys := by
  unfold Ctx.makeL; split <;> rfl

private theorem locals_makeL' (tabs : Tables) (f : Func) :
    (Ctx.makeL tabs f).locals = (Ctx.make tabs f).locals := by
  unfold Ctx.makeL; split <;> rfl

private theorem defers_makeL' (tabs : Tables) (f : Func) :
    (Ctx.makeL tabs f).defers = (Ctx.make tabs f).defers := by
  unfold Ctx.makeL; split <;> rfl

theorem entryFrame_sched (S : SchedRel tabs f g) (env : Env) (args : List Val) (mem : Mem) :
    entryFrame env (Ctx.makeSched tabs g) args mem = entryFrame env (Ctx.makeL tabs f) args mem := by
  have hpt : (Ctx.makeSched tabs g).paramTys = (Ctx.makeL tabs f).paramTys := by
    show (Ctx.makeL tabs g).paramTys = _
    rw [paramTys_makeL', paramTys_makeL']; simp only [Ctx.make, abiParams, S.ownAux]
  have hloc : (Ctx.makeSched tabs g).locals = (Ctx.makeL tabs f).locals := by
    show (Ctx.makeL tabs g).locals = _
    rw [locals_makeL', locals_makeL']; simp only [Ctx.make, abiParams, S.ownAux]
  have hsz : (Ctx.makeSched tabs g).f.valueTab.size = (Ctx.makeL tabs f).f.valueTab.size := by
    rw [makeSched_f, makeL_f, S.vsize]
  have hact : (Ctx.makeSched tabs g).act = (Ctx.makeL tabs f).act := act_eq
  unfold entryFrame frameMem frameAllocs
  rw [hpt, hloc, hsz, makeSched_tabs, tabs_makeL, hact]

/-- The invariant at the entry block (`hn`: `runCtxL`'s arity check). -/
theorem atS_entry (Su : Setup tabs f g) (env : Env) {args : List Val} (mem : Mem)
    (hn : args.length = (Ctx.makeL tabs f).params.size) (ha : ArgPtrsOK tabs f env args mem)
    (hnp : NilPtrsOK tabs f env args mem) :
    AtS ⟨f.lowered, true⟩ env tabs f (entryFrame env (Ctx.makeL tabs f) args mem)
      (entryFrame env (Ctx.makeL tabs f) args mem) f.entry 0 := by
  obtain ⟨ce, hwf⟩ := Su.wf
  have hps : (Ctx.makeL tabs f).paramTys.size = (Ctx.makeL tabs f).params.size := by
    unfold Ctx.makeL; split <;> simp [Ctx.make]
  have himg : (entryFrame env (Ctx.makeL tabs f) args mem).images.size =
      (Ctx.makeL tabs f).params.size := by
    simp only [entryFrame, Array.size_map, Array.size_zip, List.size_toArray, hps, hn,
      Nat.min_self]
  refine ⟨⟨hwf.entry, Su.cf.domRel.entry⟩, by simp [entryFrame, makeL_f], rfl, rfl,
    typedL_replicate _ _ _ _ rfl, dinvL_entry Su.cf _, fun _ _ _ => rfl, ?_, himg, rfl, ha, hnp⟩
  intro blk z v a hblk hz hv hp ha
  have h1 := hwf.phiArity _ _ _ _ ⟨⟨hwf.entry, hblk⟩, hz, hv⟩ hp
  have h2 := hwf.entryPreds blk hblk
  rw [Array.getElem?_eq_none (by omega)] at ha; cases ha

/-- **A scheduling validated by `scheduleCheck` refines its checked input**: every returning or
panicking `runLF` of `f` on an input whose pointer-shaped parameter pieces are nil or not wild
(`ArgPtrsOK`) and whose checked pointer-shaped values are (`NilPtrsOK`) is matched by a
`runSched` of `g`. -/
theorem refinesSchedLF_of_rel (Su : Setup tabs f g) :
    RefinesSchedLFFrom (fun env args mem => ArgPtrsOK tabs f env args mem ∧
      NilPtrsOK tabs f env args mem) tabs g tabs f := by
  have S := Su.rel
  intro env args mem ⟨ha, hnp⟩ fuel hd
  refine ⟨fuel, ?_⟩
  unfold runLF runCtxL at hd
  unfold runLF runSched runCtxL LMode.sched
  rw [S.lowered, params_eq S]
  split
  · rename_i hn; simp only [hn] at hd; exact hd.elim
  · rename_i hn
    simp only [hn] at hd
    try simp only [hn]
    have hlen : args.length = (Ctx.makeL tabs f).params.size := by simpa using hn
    have hout : (Ctx.makeSched tabs g).outs = (Ctx.makeL tabs f).outs := by
      show (Ctx.makeL tabs g).outs = _
      rw [outs_makeL, outs_makeL]; simp only [Ctx.make, abiParams, S.ownAux]
    have hdef : (Ctx.makeSched tabs g).defers = (Ctx.makeL tabs f).defers := by
      show (Ctx.makeL tabs g).defers = _
      rw [defers_makeL', defers_makeL']; rfl
    have hent : (Ctx.makeSched tabs g).f.entry = (Ctx.makeL tabs f).f.entry := by
      rw [makeSched_f, makeL_f]; exact S.entry
    have hact : (Ctx.makeSched tabs g).act = (Ctx.makeL tabs f).act := act_eq
    rw [entryFrame_sched S, hout, hdef, hact, hent]
    exact finish_refines hd (runLoopL_sim
      (fun frS frT b i => AtS ⟨f.lowered, true⟩ env tabs f frS frT b i)
      (fun _ _ _ _ hR => stepS Su rfl hR) fuel _ _ _ _
      (by rw [makeL_f]; exact atS_entry Su env mem hlen ha hnp) (finish_defined hd))

end GoFV.Proof.SchedL

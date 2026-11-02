import GoFV.Proof.Pass.SegRel
import GoFV.Proof.Pass.LoadFwdPtr
import GoFV.Proof.RoImage

/-!
# Segments: a `Move` from a read-only zero symbol (issue #151)

`generic.rules:1743`: `(Move {t} [n] dst (Addr {sym} (SB)) mem) && symIsROZero(sym) =>
(Zero {t} [n] dst mem)`. The segment layer takes the event (`RewriteCheck.roSeg?`: the anchor
redefined in place, nothing dropped or fresh), and `RewriteCheck.roSegsOK` checks that the symbol
is one of the read-only symbols `ro` of the precondition (`RoImage`) whose bytes are all zero and
that `f`'s values of memory shape are memory ops (`WBCheck.memTyOK`).

The source run's memories then have the symbols of `ro` (`RoQ`, a memory invariant kept by the
contracts, `roQ_pred`, `roQ_contracts`): the `Move` read zero bytes, which the `Zero` writes at
the same pointer, so the anchor's memories are equal (`roSeg_sound`).
-/

namespace GoFV.Proof.Seg

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.RewriteCheck
open GoFV.Proof.CSE.Mem (Avail)
open GoFV.Proof.AtomSim (Reg rv evalValue_of_regs regs_of_ok rv_of)

/-- The segment layer's source memory invariant: the read-only symbols `ro`, for an `f` whose
values of memory shape are memory ops (`WBCheck.memTyOK`; else no invariant). -/
def RoQ (tabs : Tables) (ro : List (String × Alloc)) (f : Func) : Mem → Prop :=
  fun m => WBCheck.memTyOK tabs f = true → RoMem ro m

variable {tabs : Tables} {ro : List (String × Alloc)} {f g : Func}

theorem roQ_pred : MemInv.MemPred (RoQ tabs ro f) := (roMem_pred ro).imp

theorem roQ_contracts {env : Env} (hK : env.KeepsRo) : MemInv.ContractsOK (RoQ tabs ro f) env :=
  MemInv.ContractsOK.imp fun _ => hK.contractsOK ro

/-- The source's entry frame has the invariant. -/
theorem roQ_entry {env : Env} (h : RoImage ro env mem) (args : List Val) :
    MemInv.SInv (RoQ tabs ro f) (entryFrame env (Ctx.make tabs f) args mem) :=
  MemInv.sinv_entry (fun a h hg hw hc => roMem_set a (h hc) hg hw) fun _ => h.2

/-- A block entry keeps the invariant. -/
theorem roQ_enter {env : Env} (hK : env.KeepsRo) {ce : CheckEnv} (hwf : WF ce f) {b : ID}
    {B : Block} (hb : b ∈ f.blocks) (hB : f.block? b = some B) {fr fr' : Frame} {i : Nat}
    (hs : MemInv.SInv (RoQ tabs ro f) fr) (h : enterBlock env (Ctx.make tabs f) fr B i = .ok fr') :
    MemInv.SInv (RoQ tabs ro f) fr' := by
  by_cases hm : WBCheck.memTyOK tabs f = true
  · exact MemInv.sinv_enter roQ_pred (roQ_contracts hK) hwf hm hb hB hs h
  · exact MemInv.SInv.of_not hm fr'

/-- The values of a block keep the invariant. -/
theorem roQ_evalAll {env : Env} (hK : env.KeepsRo) {ce : CheckEnv} (hwf : WF ce f) {o : List ID}
    (ho : ∀ x ∈ o, ∃ b ∈ f.blocks, x ∈ WBCheck.vals f b) {fr fr' : Frame}
    (hs : MemInv.SInv (RoQ tabs ro f) fr) (h : evalAll env (Ctx.make tabs f) fr o = .ok fr') :
    MemInv.SInv (RoQ tabs ro f) fr' := by
  by_cases hm : WBCheck.memTyOK tabs f = true
  · exact MemInv.sinv_evalAll roQ_pred (roQ_contracts hK) hwf hm ho hs h
  · exact MemInv.SInv.of_not hm fr'

/-! ## The segment -/

theorem roSeg_spec {fv gv : Value} {D N : List ID} (h : roSeg? tabs f fv gv = some (D, N)) :
    D = [] ∧ N = [] ∧ fv.op = .Move ∧ ∃ d s m, fv.args.toList = [d, s, m] ∧ gv.op = .Zero ∧
      gv.args = #[d, m] ∧ gv.auxInt = fv.auxInt ∧
      ∃ sv, f.value? s = some sv ∧ sv.op = .Addr := by
  unfold roSeg? at h
  split at h
  · rename_i d s m hop hargs
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq, Option.any_eq_true] at hc
      obtain ⟨⟨⟨hz, ha⟩, hai⟩, sv, hsv, hsa, -⟩ := hc
      exact ⟨rfl, rfl, hop, d, s, m, hargs, hz, ha, hai, sv, hsv, hsa⟩
    · cases h
  · cases h

theorem roSrcOK_spec {fv : Value} {d s m : ID} (h : roSrcOK tabs ro f fv = true)
    (hargs : fv.args.toList = [d, s, m]) :
    ∃ sv n a, f.value? s = some sv ∧ WBCheck.symName? tabs sv.aux = some n ∧ (n, a) ∈ ro ∧
      ∀ b ∈ a.data, b = .b 0 := by
  unfold roSrcOK at h
  rw [hargs] at h
  simp only [Option.any_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
    Array.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨sv, hsv, n, hn, ⟨n', a⟩, hm, rfl, hz⟩ := h
  refine ⟨sv, n', a, hsv, hn, hm, fun b hb => ?_⟩
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hb
  exact hz i hi

/-- An `Addr` of a symbol evaluates to the symbol's block. -/
theorem frameVal_addr {ctx : Ctx} {v : Value} (hop : v.op = .Addr) {n : String}
    (hn : WBCheck.symName? ctx.tabs v.aux = some n) :
    frameVal ctx v = some (.ptr ⟨.global n, 0⟩) := by
  unfold WBCheck.symName? at hn
  unfold frameVal
  rw [hop]
  dsimp only
  split at hn
  · rename_i name _ _ _ _ _ _ _ _ _ _ hx
    cases hn
    rw [hx]
  · cases hn

/-- The bytes a read of zero bytes returns are zero. -/
theorem read_zeros {M : Mem} {n : String} {a : Alloc} (hf : M.find? (.global n) = some a)
    (hz : ∀ b ∈ a.data, b = .b 0) {k : Nat} {bs : Array Byte}
    (hr : M.read ⟨.global n, 0⟩ k = some bs) : bs = Array.replicate k (.b 0) := by
  unfold Mem.read at hr
  by_cases hk : k = 0
  · subst hk; simp at hr; subst hr; rfl
  · simp only [beq_iff_eq, hk, ↓reduceIte, hf] at hr
    dsimp only [bind, Option.bind] at hr
    split at hr
    · rename_i hc
      cases hr
      have h0 : BitVec.toNat (0 : BitVec 64) = 0 := rfl
      simp only [h0, Nat.zero_add] at hc ⊢
      apply Array.ext
      · simp; omega
      · intro i h1 h2
        simp only [Array.getElem_extract, Nat.zero_add, Array.getElem_replicate]
        exact hz _ (Array.getElem_mem _)
    · cases hr

private theorem evalOp_memRoot {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} (hop : v.op = .Zero ∨ v.op = .Move) :
    evalOp env ctx fr v argv ty = memRoot ctx v argv := by
  rcases hop with hop | hop <;> simp only [evalOp, hop]

/-- A global pointer, retyped at any shape, reads as itself where it reads as a pointer (it has
no address to become an integer). -/
theorem retype_global_asPtrWord {n : String} {t : Ty} {Q : Ptr}
    (h : ((Val.ptr ⟨.global n, 0⟩).retype t).asPtrWord = some Q) : Q = ⟨.global n, 0⟩ := by
  cases t with
  | int w => cases w <;> simp_all [Val.retype, Val.asPtrWord, Ptr.addr?, Blk.base?]
  | _ => simp_all [Val.retype, Val.asPtrWord]

/-- A `Move` that returns read its source and wrote the bytes at its destination (both
pointer words). -/
theorem memRoot_move {ctx : Ctx} {v : Value} (hop : v.op = .Move) {a b c r : Val}
    (h : memRoot ctx v [a, b, c] = .ok r) :
    ∃ D Q M bs M', a.asPtrWord = some D ∧ b.asPtrWord = some Q ∧ c = .mem M ∧
      M.read Q v.auxInt.toInt.toNat = some bs ∧ M.write D bs = some M' ∧ r = .mem M' := by
  unfold memRoot at h
  rw [hop] at h
  split at h
  case h_3 =>
    rename_i _ _ a' b' M _ hargs
    simp only [List.cons.injEq, and_true] at hargs
    obtain ⟨rfl, rfl, rfl⟩ := hargs
    dsimp only at h
    split at h
    · rename_i D Q hD hQ
      split at h
      · rename_i bs hbs
        unfold writeRes at h
        split at h
        · rename_i M' hw
          cases h
          exact ⟨D, Q, M, bs, M', hD, hQ, rfl, hbs, hw, rfl⟩
        · cases h
      · cases h
    · cases h
  all_goals first
    | (rename_i h1 _; cases h1; done)
    | (rename_i _ h2; cases h2; done)
    | (dsimp only at h; split at h <;> cases h)

/-- What `roSegsOK` says of a segment whose anchor is a `Move`. -/
theorem roSegsOK_spec (h : roSegsOK tabs ro f g = true) {x : ID} {D N : List ID}
    (hs : segOK tabs f g x = some (D, N)) {fv : Value} (hfv : f.value? x = some fv)
    (hop : fv.op = .Move) : WBCheck.memTyOK tabs f = true ∧ roSrcOK tabs ro f fv = true := by
  unfold roSegsOK at h
  have hx : (x, D, N) ∈ (segList (segArr tabs f g)).filter
      (fun s => (f.value? s.1).any (·.op == .Move)) :=
    List.mem_filter.2 ⟨mem_segList.2 hs, by simp [hfv, hop]⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true] at h
  rcases h with h | ⟨hm, hall⟩
  · rw [List.isEmpty_iff] at h; rw [h] at hx; cases hx
  · have := hall _ hx
    simp only [hfv, Option.all_some] at this
    exact ⟨hm, this⟩

/-- **The read-only segment is sound**: in a source frame whose memories have the read-only
symbols, a `Move` from a symbol whose bytes are zero wrote what the `Zero` writes. -/
theorem roSeg_sound {x : ID} {fv gv : Value} {D N : List ID} (hfv : f.value? x = some fv)
    (hgv : g.value? x = some gv) (hgid : gv.id = x) (hty : gv.type = fv.type)
    (h : roSeg? tabs f fv gv = some (D, N)) (hro : roSrcOK tabs ro f fv = true)
    (hm : WBCheck.memTyOK tabs f = true) (env : Env) :
    SegSound (RoQ tabs ro f) env tabs f g x D N := by
  obtain ⟨rfl, rfl, hop, d, s, m, hfa, hgop, hga, hai, sv, hsv, hsa⟩ := roSeg_spec h
  obtain ⟨sv', n, a, hsv', hn, hna, hz⟩ := roSrcOK_spec hro hfa
  rw [hsv] at hsv'; cases hsv'
  have hnphi : fv.op ≠ .Phi := by rw [hop]; decide
  have hroot : CSE.rootNode f x = true := by
    simp only [CSE.rootNode, hfv, Option.map_some, Option.getD_some, hop]; decide
  refine ⟨fun z hz _ zv fr e mm hzv hpan => ?_, fun S A hA hT hinv hid hsz hroots => ?_⟩
  · simp only [List.nil_append, List.mem_singleton] at hz
    subst hz
    rw [hfv] at hzv; cases hzv
    rcases evalValue_panic_op hpan with hc | hc <;> rw [hop] at hc <;> revert hc <;> decide
  have hAx : A x := hroots x (by simp) hroot
  have hmem : ∀ a ∈ [d, s, m], A a := fun a ha =>
    hA.cl x fv hAx hfv hnphi a (by rw [Array.mem_def, hfa]; exact ha)
  obtain ⟨yd, hyd⟩ := hA.reg (hmem d (by simp))
  obtain ⟨ys, hys⟩ := hA.reg (hmem s (by simp))
  obtain ⟨ym, hym⟩ := hA.reg (hmem m (by simp))
  obtain ⟨y, hy⟩ := hA.reg hAx
  -- the source's `Move`
  have hev := hA.eval hAx hfv hnphi hy
  rw [evalValue_of_regs (regs_of_ok hev), evalOp_memRoot (.inr hop), hfa] at hev
  simp only [List.map_cons, List.map_nil, rv_of hyd, rv_of hys, rv_of hym] at hev
  cases hmr : memRoot (Ctx.make tabs f) fv [yd, ys, ym] with
  | panic e mm => rw [hmr] at hev; cases hev
  | stuck msg => rw [hmr] at hev; cases hev
  | ok r =>
  rw [hmr] at hev; cases hev
  obtain ⟨P, Q, M, bs, M', hPw, hQw, rfl, hrd, hw, rfl⟩ := memRoot_move hop hmr
  -- the source pointer is the symbol's block
  have hsnp : sv.op ≠ .Phi := by rw [hsa]; decide
  have hevs := hA.eval (hmem s (by simp)) hsv hsnp hys
  rw [evalValue_of_regs (regs_of_ok hevs),
    CSE.Mem.evalOp_frameVal (.inl hsa) (frameVal_addr hsa hn)] at hevs
  have hQ : Q = ⟨.global n, 0⟩ := by
    simp only [Res.bind_ok, Res.ok.injEq] at hevs
    rw [← hevs] at hQw
    exact retype_global_asPtrWord hQw
  subst hQ
  -- the memory has the symbol: the bytes read are zero
  have hRo : RoMem ro M := hinv m _ hym M (by simp [Val.mems]) hm
  have hbs := read_zeros (hRo n a hna).2 hz hrd
  subst hbs
  -- the target's `Zero` writes the same bytes
  have htg : (Ctx.make tabs g).tys[gv.id]?.getD .other = tabs.ty gv.type := by
    rw [hgid, tys_of_value hgv]; rfl
  have hreg : ∀ a ∈ gv.args, Reg S a := by
    rw [hga]; intro a ha
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact ⟨_, hyd⟩
    · exact ⟨_, hym⟩
  have he : evalValue env (Ctx.make tabs g) S gv = .ok ((Val.mem M').retype (tabs.ty gv.type)) := by
    rw [evalValue_of_regs hreg, htg, evalOp_memRoot (.inl hgop), hga]
    show (memRoot _ gv [rv S d, rv S m]).bind _ = _
    rw [rv_of hyd, rv_of hym]
    simp only [memRoot, hgop, hai, hPw, hw, writeRes]
    rfl
  have hf : (Ctx.make tabs g).f = g := rfl
  refine ⟨{ S with regs := S.regs.set! x (some ((Val.mem M').retype (tabs.ty gv.type))) }, ?_,
    fun _ => ⟨_, (Val.mem M').retype (tabs.ty gv.type), hy, ?_, ?_⟩⟩
  · simp only [List.nil_append, evalAll, hf, hgv, he]
  · simp only [Array.set!_eq_setIfInBounds]
    exact Array.getElem?_setIfInBounds_self_of_lt (Nat.lt_of_lt_of_le (lt_of_value? hgv) hsz)
  · have hfid := hid x fv hAx hfv
    rw [hfid, tys_of_value hfv, Option.getD_some, hty]
    exact Sem.Refines.refl _

end GoFV.Proof.Seg

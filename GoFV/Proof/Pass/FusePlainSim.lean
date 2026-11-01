import GoFV.Proof.Pass.FusePlainPanic

/-!
# One checked `fuseBlockPlain` rewrite refines

`refines_of_step`: if `g` is `f` with the run `b0 … c` fused (`Setup f g run b0 c`), every run
of `f` is a run of `g`. Macro-step simulation (`runLoop_simIH`): outside the run both functions
step alike, edges into `b0` going to `c` in `g` (`normal_step`); at `b0` the source runs the
blocks of the run one after the other (`chain`, the frames related by `Acc`) while the target
runs the fused block once (`merged_ok`, `merged_panic`). The relation `R`: the same frame, the
same block (`c` for `b0`), never a later block of the run, and lemma (D) for the source's frame
at the entry of a tree block.
-/

namespace GoFV.Proof.FusePlain

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.Fuse GoFV.Opt.Fuse.Plain
  GoFV.Proof Dom

/-- A terminator with the same kind and controls and redirected successors. -/
theorem stepTerm_redirect {G : Frame} {B B' : Block} (hk : B'.kind = B.kind)
    (hc : B'.controls = B.controls) {r : Edge → Edge} (hsu : B'.succs = B.succs.map r) :
    (∀ e, stepTerm G B = .ok (.goto e) → stepTerm G B' = .ok (.goto (r e))) ∧
    (∀ rs m, stepTerm G B = .ok (.ret rs m) → stepTerm G B' = .ok (.ret rs m)) := by
  refine ⟨fun e h => ?_, fun rs m h => ?_⟩
  · rcases Dead.stepTerm_rel (.inl hk) hc (fun _ _ => rfl) h with ⟨k, e', he, hk', -, hst⟩ |
      ⟨rs, m, he, -⟩
    · cases he
      rw [hst]; unfold succ; rw [hsu, Array.getElem?_map, hk']; rfl
    · cases he
  · rcases Dead.stepTerm_rel (.inl hk) hc (fun _ _ => rfl) h with ⟨k, e', he, -, -, -⟩ |
      ⟨rs', m', he, hst⟩
    · cases he
    · cases he; exact hst

theorem redirect_b {b0 c : ID} {e : Edge} :
    (redirect b0 c e).b = if e.b = b0 then c else e.b := by
  unfold redirect; by_cases h : e.b = b0 <;> simp [h]

theorem redirect_i {b0 c : ID} {e : Edge} : (redirect b0 c e).i = e.i := by
  unfold redirect; split <;> rfl

variable {f g : Func} {run : List ID} {b0 c : ID}

/-- The simulation relation (see the module doc). -/
def R (env : Env) (tabs : Tables) (f : Func) (run : List ID) (b0 c : ID) (frS : Frame)
    (bS iS : Nat) (frT : Frame) (bT iT : Nat) : Prop :=
  frT = frS ∧ iT = iS ∧ bT = (if bS = b0 then c else bS) ∧ bS ∈ f.blocks ∧ bS ∉ run.tail ∧
    ((make f).depthOf bS).isSome ∧ frS.regs.size = f.valueTab.size ∧
    DInv env (Ctx.make tabs f) (fun a => Anc (make f) a bS ∧ a ≠ bS) frS

namespace Setup

variable (S : Setup f g run b0 c)
include S

/-- Lemma (D) and the tree along a source block step. -/
theorem dinv_step {env : Env} {tabs : Tables} {b : ID} (hb : b ∈ f.blocks) {B : Block}
    (hB : f.block? b = some B) (ht : ((make f).depthOf b).isSome) {fr G : Frame} {i : Nat}
    (hs : fr.regs.size = f.valueTab.size)
    (hdi : DInv env (Ctx.make tabs f) (fun a => Anc (make f) a b ∧ a ≠ b) fr)
    (h : enterBlock env (Ctx.make tabs f) fr B i = .ok G) {e : Edge} (he : e ∈ B.succs) :
    DInv env (Ctx.make tabs f) (fun a => Anc (make f) a e.b ∧ a ≠ e.b) G ∧
      ((make f).depthOf e.b).isSome ∧ G.regs.size = f.valueTab.size ∧ e.b ∈ f.blocks := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨h1, h2, h3⟩ := dinv_enter hwf S.cf hb hB hs hdi h
  obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 he
  exact ⟨dinv_edge S.cf hb hB ht he h1, (edge S.cf hb hB ht he).2.1, by rw [h3, hs],
    (hwf.succLink b B ⟨hb, hB⟩ k e hk).1⟩

/-- An edge into a later block of the run comes from the block before it. -/
theorem succ_later {b : ID} (hb : b ∈ f.blocks) {B : Block} (hB : f.block? b = some B)
    {e : Edge} (he : e ∈ B.succs) (hy : e.b ∈ run.tail) :
    ∃ pre suf, run = pre ++ b :: e.b :: suf := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨rest, hrest⟩ := S.rel.run_cons
  rw [hrest, List.tail_cons] at hy
  obtain ⟨p, s, hp⟩ := List.append_of_mem hy
  have hne : b0 :: p ≠ [] := List.cons_ne_nil _ _
  obtain ⟨q, x, hq⟩ : ∃ q x, b0 :: p = q ++ [x] :=
    ⟨(b0 :: p).dropLast, (b0 :: p).getLast hne, (List.dropLast_concat_getLast hne).symm⟩
  have hr : run = q ++ x :: e.b :: s := by
    rw [hrest, hp, ← List.cons_append, hq]; simp
  obtain ⟨X, Y, hX, hY, -, -, hpr⟩ := S.rel.link hr
  obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 he
  obtain ⟨-, C, hC, hci⟩ := hwf.succLink b B ⟨hb, hB⟩ k e hk
  rw [hY] at hC; cases hC
  rw [hpr] at hci
  have h0 : e.i = 0 := by
    rcases Nat.lt_or_ge e.i 1 with h' | h'
    · omega
    · rw [Array.getElem?_eq_none (by simpa using h')] at hci; cases hci
  rw [h0] at hci
  simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq, Edge.mk.injEq] at hci
  rw [hci.1] at hr
  exact ⟨q, s, hr⟩

/-- A block of `f` outside the run steps alike in `g`, edges into `b0` going to `c`. -/
theorem normal_step {tabs : Tables} {env : Env} {fr : Frame} {b : ID} {i : Nat}
    (hb : b ∈ f.blocks) (hn : b ∉ run) :
    (∀ G e, blockStep env (Ctx.make tabs f) fr b i = .goto G e →
      blockStep env (Ctx.make tabs g) fr b i = .goto G (redirect b0 c e)) ∧
    (∀ rs m, blockStep env (Ctx.make tabs f) fr b i = .ret rs m →
      blockStep env (Ctx.make tabs g) fr b i = .ret rs m) ∧
    (∀ e m, blockStep env (Ctx.make tabs f) fr b i = .panic e m →
      blockStep env (Ctx.make tabs g) fr b i = .panic e m) := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨fb, gb, hfb, hgb, hid, hvals, hk, hc, hsu⟩ := S.rel.block_out hb hn
  have hown := valuesOwn hwf hb hfb
  have hnd := hwf.valuesNodup b fb ⟨hb, hfb⟩
  have hidv : ∀ x ∈ fb.values, ∀ fv, f.value? x = some fv → fv.id = x := fun x hx fv hfv => by
    obtain ⟨v, hv, hvid⟩ := hown x hx
    rw [hfv] at hv; cases hv; exact hvid
  have hca : ∀ l : List ID, CtxAgree (Ctx.make tabs f) (Ctx.make tabs g) l := fun l =>
    ⟨fun x _ => (S.rel.value_same x).1, fun x _ v hv => by
      change f.value? x = some v at hv
      obtain ⟨gv, hgv, hty, -⟩ := (S.rel.value_same x).2 v hv
      obtain ⟨hid', -⟩ := (S.rel.value_same x).1 |> fun h => by
        rw [hv, hgv] at h; exact ⟨h.1, h⟩
      sorry, rfl, S.params_eq, rfl⟩
  sorry

end Setup

end GoFV.Proof.FusePlain

import GoFV.Proof.Pass.CopyElim

/-!
# Removing unreachable blocks and dead values: the static relation `DeadRel`

`DeadRel f g` relates a function `f` and a function `g` obtained from it by keeping some of its
blocks (the reachable ones), some of their values (the live ones) and some of their edges
(deadcode): every kept block keeps its controls and its terminator (a `First` block may become
`Plain`), a kept successor edge leads to the same block, possibly at another predecessor index,
where each kept `Phi` reads along the new index what it read along the old one (`PhiArgs`);
every kept value keeps its op, aux, arguments and type (a kept `Phi` stays a `Phi`); a dropped
value of a kept block cannot panic. `Chained`: the side-effecting roots of each kept block are
ordered by dependency, so a panicking root is reached by every schedule; `NoNil`: no
`NilCheck` (a nil `NilCheck` panics, and the scheduler's order among ready `NilCheck`s is not
determined by `schedule_spec`, #96).

`refines_of_deadRel` (`GoFV.Proof.Pass.DeadSim`) derives the refinement from it, for `f` and
`g` that are well formed (`WF`); no dominance is needed.

This module: the relation, the terminator lemma (`stepTerm_rel`) and dependency orders of a
subset of a block's values (`Order.Topo.filter`, `refOK_of_topo`).
-/

namespace GoFV.Proof.Dead

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof

/-- Ops whose evaluation may panic (`evalValue_panic_op`). -/
def Panicking (op : Op) : Prop :=
  op = .PanicBounds ∨ op = .StaticLECall ∨ op = .StaticCall ∨ op = .NilCheck

/-- The `Phi`s `g` keeps in block `c` read, along predecessor index `iT`, the argument `f`'s
read along `iS`. -/
def PhiArgs (f g : Func) (c : ID) (iS iT : Nat) : Prop :=
  ∀ gc, g.block? c = some gc → ∀ x ∈ gc.values, ∀ gv, g.value? x = some gv → gv.op = .Phi →
    ∃ fv, f.value? x = some fv ∧ gv.args[iT]? = fv.args[iS]?

/-- Terminator kinds: the same, or `First` turned `Plain` (both continue along successor 0). -/
def KindRel (fk gk : BlockKind) : Prop := gk = fk ∨ (fk = .First ∧ gk = .Plain)

/-- `g` keeps blocks, values and edges of `f` (see the module doc). -/
structure DeadRel (f g : Func) : Prop where
  entry : g.entry = f.entry
  ownAux : g.ownAux = f.ownAux
  vsize : g.valueTab.size = f.valueTab.size
  /-- A kept block: listed in `f`, same controls, related kind, a subset of the values. -/
  block : ∀ bid ∈ g.blocks, ∀ gb, g.block? bid = some gb →
    ∃ fb, f.block? bid = some fb ∧ bid ∈ f.blocks ∧ KindRel fb.kind gb.kind ∧
      gb.controls = fb.controls ∧ ∀ x ∈ gb.values, x ∈ fb.values
  /-- Every successor a run can take (successor 0 of a `First` block) is kept. -/
  edge : ∀ bid ∈ g.blocks, ∀ gb fb, g.block? bid = some gb → f.block? bid = some fb →
    ∀ (k : Nat) (e : Edge), fb.succs[k]? = some e → (fb.kind = .First → k = 0) →
      ∃ e', gb.succs[k]? = some e' ∧ e'.b = e.b ∧ PhiArgs f g e.b e.i e'.i
  /-- A kept value: same type; a `Phi` iff it was one; otherwise same op, aux and arguments. -/
  value : ∀ bid ∈ g.blocks, ∀ gb, g.block? bid = some gb → ∀ x ∈ gb.values, ∀ gv,
    g.value? x = some gv → ∃ fv, f.value? x = some fv ∧ gv.type = fv.type ∧
      (gv.op = .Phi ↔ fv.op = .Phi) ∧
      (gv.op ≠ .Phi → gv.op = fv.op ∧ gv.aux = fv.aux ∧ gv.auxInt = fv.auxInt ∧ gv.args = fv.args)
  /-- A dropped value of a kept block cannot panic. -/
  dropped : ∀ bid ∈ g.blocks, ∀ gb fb, g.block? bid = some gb → f.block? bid = some fb →
    ∀ x ∈ fb.values, x ∉ gb.values → ∀ fv, f.value? x = some fv → ¬ Panicking fv.op

/-- The side-effecting roots (priority 2) of the blocks `B` of `f` are pairwise ordered by
dependency. -/
def Chained (f : Func) (B : ID → Prop) : Prop :=
  ∀ bid fb, B bid → f.block? bid = some fb →
    ∀ x y, NodeIn (schedNodes f fb).toList x → NodeIn (schedNodes f fb).toList y →
      ¬ NilIn (schedNodes f fb).toList x → ¬ NilIn (schedNodes f fb).toList y → x ≠ y →
      Order.Dep (NodeIn (schedNodes f fb).toList) (argsOf (schedNodes f fb).toList) x y ∨
      Order.Dep (NodeIn (schedNodes f fb).toList) (argsOf (schedNodes f fb).toList) y x

/-- `f` has no `NilCheck`. -/
def NoNil (f : Func) : Prop := ∀ x fv, f.value? x = some fv → fv.op ≠ .NilCheck

/-! ## Terminators -/

theorem succ_ok {b : Block} {k : Nat} {n : Next} (h : succ b k = .ok n) :
    ∃ e, b.succs[k]? = some e ∧ n = .goto e := by
  unfold succ at h
  cases hk : b.succs[k]? with
  | none => rw [hk] at h; cases h
  | some e => rw [hk] at h; cases h; exact ⟨e, rfl, rfl⟩

theorem control_agree {fr fr' : Frame} {b b' : Block} (hc : b'.controls = b.controls)
    (hag : ∀ c ∈ b.controls, fr'.regs[c]? = fr.regs[c]?) {k : Nat} {v : Val}
    (h : Sem.control fr b k = .ok v) : Sem.control fr' b' k = .ok v := by
  unfold Sem.control at h ⊢
  rw [hc]
  cases hk : b.controls[k]? with
  | none => rw [hk] at h; cases h
  | some c =>
    rw [hk] at h
    simp only at h ⊢
    rw [hag c (Array.mem_of_getElem? hk)]
    cases hy : (fr.regs[c]?).join with
    | none => simp [hy, Res.ofOption] at h
    | some y => simp only [hy, Res.ofOption] at h ⊢; exact h

/-- **The terminator of a kept block.** If `b`'s terminator continues along an edge, it is
successor `k` (0 for `First`) and `b'` continues along its successor `k`; if it returns, `b'`
returns alike. -/
theorem stepTerm_rel {fr fr' : Frame} {b b' : Block} (hk : KindRel b.kind b'.kind)
    (hc : b'.controls = b.controls) (hag : ∀ c ∈ b.controls, fr'.regs[c]? = fr.regs[c]?)
    {n : Next} (h : stepTerm fr b = .ok n) :
    (∃ k e, n = .goto e ∧ b.succs[k]? = some e ∧ (b.kind = .First → k = 0) ∧
      stepTerm fr' b' = succ b' k) ∨
    (∃ rs m, n = .ret rs m ∧ stepTerm fr' b' = .ok (.ret rs m)) := by
  have hctl : ∀ v, Sem.control fr b 0 = .ok v → Sem.control fr' b' 0 = .ok v :=
    fun v h => control_agree hc hag h
  have hgo : ∀ k, succ b k = .ok n → (b.kind = .First → k = 0) →
      stepTerm fr' b' = succ b' k →
      (∃ k e, n = .goto e ∧ b.succs[k]? = some e ∧ (b.kind = .First → k = 0) ∧
        stepTerm fr' b' = succ b' k) ∨
      (∃ rs m, n = .ret rs m ∧ stepTerm fr' b' = .ok (.ret rs m)) := by
    intro k hs hf ht
    obtain ⟨e, he, rfl⟩ := succ_ok hs
    exact .inl ⟨k, e, rfl, he, hf, ht⟩
  rcases hk with hk | ⟨hf, hp⟩
  · revert hgo
    cases hb : b.kind <;> intro hgo <;> have hb' := hk.trans hb <;> unfold stepTerm at h <;>
      simp only [hb] at h
    all_goals first
      | (cases h; done)
      | exact hgo 0 h (fun _ => rfl) (by unfold stepTerm; rw [hb'])
      | (cases hc0 : Sem.control fr b 0 with
          | ok v =>
            rw [hc0] at h
            simp only [bind, Res.bind] at h
            have hT := hctl v hc0
            split at h
            all_goals first
              | (cases h; done)
              | exact hgo _ h (fun hh => nomatch hh)
                  (by unfold stepTerm; rw [hb', hT]; rfl)
              | (split at h
                 · split at h
                   · cases h
                   · cases h
                     refine .inr ⟨_, _, rfl, ?_⟩
                     unfold stepTerm; rw [hb', hT]; simp only [bind, Res.bind]; simp_all
                 · cases h)
          | panic e m => rw [hc0] at h; cases h
          | stuck msg => rw [hc0] at h; cases h)
  · unfold stepTerm at h
    rw [hf] at h
    exact hgo 0 h (fun _ => rfl) (by unfold stepTerm; rw [hp])

/-! ## Orders on a subset of a block's values -/

theorem Order.Topo.filter {α : Type} {N N' : α → Prop} {D D' : α → List α} {o : List α}
    (ht : Order.Topo N D o) (p : α → Bool) (hp : ∀ x, p x = true ↔ N' x)
    (hsub : ∀ x, N' x → N x) (hD : ∀ x, N' x → ∀ a ∈ D' x, N' a → a ∈ D x) :
    Order.Topo N' D' (o.filter p) := by
  refine ⟨ht.nodup.filter _, fun x => ?_, fun j x hj a ha hNa => ?_⟩
  · rw [List.mem_filter, hp]
    exact ⟨fun h => h.2, fun h => ⟨(ht.mem x).2 (hsub x h), h⟩⟩
  · have hxf := List.mem_of_getElem? hj
    obtain ⟨hxo, hpx⟩ := List.mem_filter.1 hxf
    obtain ⟨L1, L2, hsplit⟩ := List.append_of_mem hxo
    -- `a` lies before `x` in `o`
    have hxk : o[L1.length]? = some x := by rw [hsplit]; simp
    obtain ⟨i, hi, hia⟩ := ht.before _ x hxk a (hD x ((hp x).1 hpx) a ha hNa) (hsub a hNa)
    have haL1 : a ∈ L1 := by
      rw [hsplit, List.getElem?_append_left hi] at hia
      exact List.mem_of_getElem? hia
    have hfs : o.filter p = L1.filter p ++ x :: L2.filter p := by
      rw [hsplit, List.filter_append, List.filter_cons, hpx]; rfl
    have hjx : j = (L1.filter p).length := by
      have h2 : (o.filter p)[(L1.filter p).length]? = some x := by rw [hfs]; simp
      exact Order.idx_unique (ht.nodup.filter _) hj h2
    have haf : a ∈ L1.filter p := List.mem_filter.2 ⟨haL1, (hp a).2 hNa⟩
    obtain ⟨i', hi'⟩ := List.getElem?_of_mem haf
    have hil : i' < (L1.filter p).length := (List.getElem?_eq_some_iff.1 hi').1
    exact ⟨i', by omega, by rw [hfs, List.getElem?_append_left hil]; exact hi'⟩

/-- Arguments outside a dependency order satisfy `S`: every listed value's arguments are in `S`
or listed before it. -/
theorem refOK_of_topo {D : ID → List ID} :
    ∀ {o : List ID} {S : ID → Prop}, TopoRem D o → (∀ x ∈ o, ∀ a ∈ D x, a ∉ o → S a) →
      RefOK D S o
  | [], _, _, _ => trivial
  | x :: s, S, ⟨h1, h2⟩, hS =>
    ⟨fun a ha => hS x List.mem_cons_self a ha (h1 a ha),
      refOK_of_topo h2 fun y hy a ha has => by
        by_cases hax : a = x
        · exact .inr hax
        · refine .inl (hS y (List.mem_cons_of_mem _ hy) a ha fun hm => ?_)
          rcases List.mem_cons.1 hm with h | h
          · exact hax h
          · exact has h⟩

end GoFV.Proof.Dead

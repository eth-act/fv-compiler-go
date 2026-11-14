import GoFV.Proof.AtomSimRef
import GoFV.Proof.AtomSimOK
import GoFV.Proof.PhiMono

variable [GoFV.SSA.Sem.Addrs]

/-!
# One value or terminator of the atom simulation (issue #113)

* `atom_eval_mono`: an atom of `g` with the fields of an atom of `f` (`SameAtom`), on refined
  argument registers, evaluates to a refinement (`evalOp_mono` under `Env.Mono`);
* `evalOp_safe`: an op that is neither a root nor `Arg`/`ArgIntReg` never gets stuck or panics;
* `stepTerm_mono2`: the terminators of two blocks with the same kind, successors and ID on
  refined controls.
-/

namespace GoFV.Proof.AtomSim

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck GoFV.Proof.Term

theorem refinesList_idx {F G : ID → Val} :
    ∀ {l l' : List ID}, l.length = l'.length →
      (∀ (i : Nat) a a', l[i]? = some a → l'[i]? = some a' → Sem.Refines (F a) (G a')) →
      RefinesList (l.map F) (l'.map G)
  | [], [], _, _ => .nil
  | a :: l, a' :: l', hl, h =>
    .cons (h 0 a a' rfl rfl) (refinesList_idx (by simpa using hl) fun i b b' hb hb' => h (i + 1) b b' hb hb')
  | [], _ :: _, hl, _ => nomatch hl
  | _ :: _, [], hl, _ => nomatch hl

/-- **An atom on refined arguments.** -/
theorem atom_eval_mono {env : Env} (hE : env.Mono) {ctxS ctxT : Ctx}
    (hctx : ctxT = { ctxS with f := ctxT.f, sched := ctxT.sched, tys := ctxT.tys })
    {GS GT : Frame} (hfr : GT = { GS with regs := GT.regs }) {u w : Value} (hsame : SameAtom u w)
    (hty : ctxT.tys[w.id]?.getD .other = ctxS.tys[u.id]?.getD .other)
    (hregS : ∀ a ∈ u.args, Reg GS a) (hregT : ∀ a ∈ w.args, Reg GT a)
    (hargs : ∀ i < u.args.size, Sem.Refines (rv GS u.args[i]!) (rv GT w.args[i]!)) :
    Res.Refines (evalValue env ctxS GS u) (evalValue env ctxT GT w) := by
  obtain ⟨hop, -, hai, hax, hsz, -, hid⟩ := hsame
  rw [evalValue_of_regs hregS, evalValue_of_regs hregT, hty]
  have hl : RefinesList (u.args.toList.map (rv GS)) (w.args.toList.map (rv GT)) := by
    refine refinesList_idx (by simp [hsz]) fun i a a' ha ha' => ?_
    rw [Array.getElem?_toList] at ha ha'
    obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.1 ha
    obtain ⟨hi', rfl⟩ := Array.getElem?_eq_some_iff.1 ha'
    have := hargs i hi
    rwa [getElem!_pos u.args i hi, getElem!_pos w.args i hi'] at this
  have hmono := evalOp_mono env hE ctxS ctxT hctx GS GT (by rw [hfr]) (by rw [hfr]) (by rw [hfr])
    (by rw [hfr]) u (ctxS.tys[u.id]?.getD .other) hl
  rw [← evalOp_congr (ctx := ctxT) (ctx' := ctxT) (fr := GT) (v := u) (v' := w) hop.symm hax.symm
    hai.symm hid.symm rfl rfl rfl] at hmono
  exact Res.Rel.bind hmono fun x y hxy => .ok (retype_mono _ hxy)

/-- `callOp` reads its context only through the tables and the activation. -/
theorem callOp_ctx {env : Env} {ctx ctx' : Ctx} (ht : ctx'.tabs = ctx.tabs) (ha : ctx'.act = ctx.act)
    (v : Value) (argv : List Val) : callOp env ctx' v argv = callOp env ctx v argv := by
  have hc : callTarget ctx' v argv = callTarget ctx v argv := by unfold callTarget; rw [ht]
  unfold callOp
  rw [hc, ht, ha]

/-- **A devirtualised interface call** (`DvAtom`) on refined arguments (the source's from its
second on, `rest`), whose source code pointer `c` points to no function but the one the aux
calls, evaluates to a refinement (`callOp_devirt`). -/
theorem atom_eval_devirt {env : Env} (hE : env.Mono) {ctxS ctxT : Ctx}
    (htabs : ctxT.tabs = ctxS.tabs) (hact : ctxT.act = ctxS.act)
    {GS GT : Frame} {u w : Value} (hdv : DvAtom u w)
    (hty : ctxT.tys[w.id]?.getD .other = ctxS.tys[u.id]?.getD .other)
    (hregS : ∀ a ∈ u.args, Reg GS a) (hregT : ∀ a ∈ w.args, Reg GT a)
    {c : ID} {rest : List ID} (hsplit : u.args.toList = c :: rest)
    (hcode : ∀ s, codeTarget? (rv GS c) = some s → w.aux.bind ctxS.tabs.callee? = some s)
    (hargs : ∀ (i : Nat) a a', rest[i]? = some a → w.args.toList[i]? = some a' →
      Sem.Refines (rv GS a) (rv GT a')) :
    Res.Refines (evalValue env ctxS GS u) (evalValue env ctxT GT w) := by
  obtain ⟨hu, hw, -, -, hax, hsz, -, -⟩ := hdv
  rw [evalValue_of_regs hregS, evalValue_of_regs hregT, hty]
  have hS : ∀ ty, evalOp env ctxS GS u (u.args.toList.map (rv GS)) ty =
      callOp env ctxS u (u.args.toList.map (rv GS)) := fun ty => by
    unfold evalOp; simp only [hu]
  have hT : ∀ ty, evalOp env ctxT GT w (w.args.toList.map (rv GT)) ty =
      callOp env ctxT w (w.args.toList.map (rv GT)) := fun ty => by
    unfold evalOp; simp only [hw]
  rw [hS, hT, callOp_ctx htabs hact, hsplit, List.map_cons]
  have hlen : rest.length = w.args.toList.length := by
    have := congrArg List.length hsplit
    simp only [Array.length_toList, List.length_cons] at this
    simp only [Array.length_toList]; omega
  have hl : RefinesList (rest.map (rv GS)) (w.args.toList.map (rv GT)) :=
    refinesList_idx hlen hargs
  exact Res.Rel.bind (callOp_devirt hE ctxS hu hw hax.symm hcode hl)
    fun x y hxy => .ok (retype_mono _ hxy)

/-- An op that is neither a root nor `Arg`/`ArgIntReg` evaluates. -/
theorem evalOp_safe {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val} {ty : Ty}
    (hr : isRoot v.op = false) (ha : v.op ≠ .Arg) (hai : v.op ≠ .ArgIntReg) :
    ∃ y, evalOp env ctx fr v argv ty = .ok y := by
  unfold evalOp
  split
  all_goals first
    | exact ⟨_, rfl⟩
    | (rename_i h; exact absurd h ha)
    | (rename_i h; exact absurd h hai)
    | (rename_i h; rw [h] at hr; exact absurd hr (by decide))
    | (split
       · exact ⟨_, rfl⟩
       · simp only [hr, Bool.false_eq_true, ↓reduceIte]; exact ⟨_, rfl⟩)

/-! ## Terminators -/

theorem stepTerm_mono2 {fr fr' : Frame} {b b' : Block} (hk : b'.kind = b.kind)
    (hs : b'.succs = b.succs) (hid : b'.id = b.id)
    (hc : ∀ k, Res.Refines (Sem.control fr b k) (Sem.control fr' b' k)) :
    Res.Rel Next.Refines (stepTerm fr b) (stepTerm fr' b') := by
  have hsucc : ∀ k, Sem.succ b' k = Sem.succ b k := fun k => by unfold Sem.succ; rw [hs, hid]
  unfold stepTerm
  rw [hk]
  simp only [hsucc, hid]
  split
  · exact succ_refl b 0
  · exact succ_refl b 0
  · refine Res.Rel.bind (hc 0) fun x y hxy => ?_
    cases hxy with
    | bool c => cases c <;> exact succ_refl b _
    | _ => exact .stuck _ _
  · refine Res.Rel.bind (hc 0) fun x y hxy => ?_
    cases hxy with
    | int w x => exact succ_refl b _
    | _ => exact .stuck _ _
  · refine Res.Rel.bind (hc 0) fun x y hxy => ?_
    cases hxy with
    | tuple hl =>
      dsimp only
      rcases hl.getLast? with ⟨h1, h2⟩ | ⟨a, a', h1, h2, ha⟩
      · rw [h1]; exact .stuck _ _
      · rw [h1, h2]
        cases ha with
        | mem hm =>
          dsimp only
          split
          · exact .stuck _ _
          · next hp =>
            have hq := RefinesList.any_false ?pf hl.dropLast (Bool.eq_false_iff.2 hp)
            case pf => intro a b hab ha; cases hab <;> simp_all
            simp only [hq, Bool.false_eq_true, ↓reduceIte]
            exact .ok (.ret hl.dropLast hm)
        | _ => exact .stuck _ _
    | _ => exact .stuck _ _
  · exact .stuck _ _
  · exact succ_refl b 0
  · exact .stuck _ _

end GoFV.Proof.AtomSim

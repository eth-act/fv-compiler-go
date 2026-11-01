import GoFV.Proof.AtomSimSet

/-!
# The target's schedule against a source reference frame (issue #113)

`tgt_atom_ref`: an atom of `g` evaluated in the target frame `T` refines the atom of `f` with
the same ID evaluated in the source frame `G`, when both frames' registers are their terms'
values over the atoms (`DenOK`) and the atoms both hold are refined.

`tgt_loop`: the target evaluates a prefix `L` of its schedule from `T0`: term nodes always
evaluate (`evalPure`), atoms the source evaluated (`P`) evaluate to refinements of the source's
registers in `G`, other atoms are ops that never get stuck. Afterwards `DenOK` holds of `L` and
the atoms both frames hold are refined.
-/

namespace GoFV.Proof.AtomSim

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Proof.Dom GoFV.Opt.RewriteCheck GoFV.Proof.Term

theorem res_ok_of_refines {y : Val} {r : Res Val} (h : Res.Refines (.ok y) r) :
    ∃ y', r = .ok y' ∧ Sem.Refines y y' := by
  cases h with
  | ok h => exact ⟨_, rfl, h⟩

theorem res_panic_of_refines {e : Panic} {m : Mem} {r : Res Val} (h : Res.Refines (.panic e m) r) :
    ∃ m', r = .panic e m' ∧ Mem.Refines m m' := by
  cases h with
  | panic e hm => exact ⟨_, rfl, hm⟩

theorem getElem!_mem' {a : Array ID} {i : Nat} (h : i < a.size) : a[i]! ∈ a := by
  rw [getElem!_pos a i h]; exact Array.getElem_mem h

theorem typed_set {ctx : Ctx} {T : Frame} {x : ID} {y : Val} (ht : Proof.Typed ctx T)
    (hy : y.retype (ctx.tys[x]?.getD .other) = y) : Proof.Typed ctx (T.set x y) := by
  intro z y' hz
  by_cases hxz : x = z
  · subst hxz
    by_cases hlt : x < T.regs.size
    · rw [Frame.set_regs_self hlt] at hz; cases hz; exact hy
    · have : (T.set x y).regs = T.regs := by
        simp [Frame.set, Array.set!_eq_setIfInBounds, Array.setIfInBounds, hlt]
      rw [this] at hz; exact ht x y' hz
  · rw [Frame.set_regs_ne hxz] at hz; exact ht z y' hz

theorem rv_set_ne {T : Frame} {x a : ID} {y : Val} (h : x ≠ a) : rv (T.set x y) a = rv T a := by
  unfold rv; rw [Frame.set_regs_ne h]

/-- **One atom against the reference frame.** -/
theorem tgt_atom_ref {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} {I : SrcInv tabs f} (H : Hyp tabs f g ce ce' I)
    {env : Env} (hE : env.Mono) {G T : Frame} {VS VT : ID → Prop}
    (hfr : T = { G with regs := T.regs })
    (hDS : DenOK f.value? tabs G VS) (hMS : MemDefs f.value? tabs G VS)
    (hDT : DenOK (listedDefs g) tabs T VT)
    (hVT : ∀ a, VT a → ∃ w, Placed g a w)
    (hrel : ∀ a, VT a → VS a → ¬ IsTerm f.value? a → ¬ IsTerm (listedDefs g) a →
      Sem.Refines (rv G a) (rv T a))
    (htyS : Proof.Typed (Ctx.make tabs f) G) (htyT : Proof.Typed (Ctx.make tabs g) T)
    {x : ID} {u w : Value} (hpw : Placed g x w) (hu : f.value? x = some u) (hs : SameAtom u w)
    (ht : termOp w.op = false) (hnp : w.op ≠ .Phi) (hargsS : ∀ a ∈ u.args, VS a)
    (hargsT : ∀ a ∈ w.args, VT a)
    (hinv : ∀ a, I.P w.block a (rv G a)) (hq : I.Q w.block (rv G))
    (hSV : ∀ a, SAnc f w.block a → VS a) :
    Res.Refines (evalValue env (Ctx.make tabs f) G u) (evalValue env (Ctx.make tabs g) T w) := by
  obtain ⟨hw, hbm, blk, hblk, hx⟩ := hpw
  obtain ⟨u', hu', -, -, -, -, -, hTR⟩ := H.args w.block hbm blk hblk x hx w hw ht
  rw [hu] at hu'; cases hu'
  obtain ⟨w', hw', hwid, -⟩ := H.wg.valueId w.block blk ⟨hbm, hblk⟩ x hx
  rw [hw] at hw'; cases hw'
  have huid : u.id = x := hs.2.2.2.2.2.2.trans hwid
  have htyS' : ∀ a, VS a → ¬ IsTerm f.value? a →
      (rv G a).retype (shape f.value? tabs a) = rv G a := fun a ha _ => by
    rw [← tys_shape]; exact htyS a _ (reg_rv (hDS a ha).1)
  have hshT : ∀ a, VT a → shape (listedDefs g) tabs a = shape g.value? tabs a := fun a ha => by
    obtain ⟨v, hp⟩ := hVT a ha
    simp [shape, placed_listed hp, hp.1]
  refine atom_eval_mono hE (ctx_eq H.ok.ownAux) hfr hs ?_ (fun a ha => (hDS a (hargsS a ha)).1)
    (fun a ha => (hDT a (hargsT a ha)).1) fun i hi => ?_
  · rw [hwid, huid, tys_of_value hw, tys_of_value hu, hs.2.1]
  · have hi' : i < w.args.size := hs.2.2.2.2.1 ▸ hi
    refine termRef_apply ((hTR i hi').1 hnp) hDS (hargsS _ (getElem!_mem' hi)) hDT
      (hargsT _ (getElem!_mem' hi')) (fun a h1 h2 h3 h4 => hrel a h3 h1 h2 h4) htyS'
      (fun a ha _ => by rw [hshT a ha, ← tys_shape]; exact htyT a _ (reg_rv (hDT a ha).1))
      (fun a ha hat hat' hdef _ => ?_) hinv (I.poisonAtom _) hSV
      (fun ρ hρ => I.qpois _ _ ρ hq hρ) hMS
    rw [shape_atom_def H hat' hdef]; exact htyS' a ha hat

/-- Induction along `evalAll` with an invariant of the evaluated prefix. -/
theorem evalAll_induct {env : Env} {ctx : Ctx} (L : List ID) (Inv : List ID → Frame → Prop)
    (hstep : ∀ d x s T, L = d ++ x :: s → Inv d T →
      ∃ y, stepV env ctx T x = .ok y ∧ Inv (d ++ [x]) (T.set x y)) :
    ∀ s d T, L = d ++ s → Inv d T → ∃ T', evalAll env ctx T s = .ok T' ∧ Inv L T'
  | [], d, T, hL, hI => ⟨T, rfl, by rw [hL, List.append_nil]; exact hI⟩
  | x :: s, d, T, hL, hI => by
    obtain ⟨y, hy, hI'⟩ := hstep d x s T hL hI
    rw [evalAll_cons, hy]
    exact evalAll_induct L Inv hstep s (d ++ [x]) _ (by rw [hL]; simp) hI'

/-- The loop invariant. -/
def LoopInv (tabs : Tables) (g : Func) (G T0 : Frame) (VS VT1 : ID → Prop) (D : ID → Option Value)
    (d : List ID) (T : Frame) : Prop :=
  T = { T0 with regs := T.regs } ∧ T.regs.size = T0.regs.size ∧
    Proof.Typed (Ctx.make tabs g) T ∧ DenOK (listedDefs g) tabs T (fun a => VT1 a ∨ a ∈ d) ∧
    (∀ a, a ∉ d → T.regs[a]? = T0.regs[a]?) ∧
    (∀ a, (VT1 a ∨ a ∈ d) → VS a → ¬ IsTerm D a → ¬ IsTerm (listedDefs g) a →
      Sem.Refines (rv G a) (rv T a))

/-- **The target's schedule prefix `L`.** -/
theorem tgt_loop {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} {I : SrcInv tabs f} (H : Hyp tabs f g ce ce' I)
    {env : Env} (hE : env.Mono) {G T0 : Frame} {VS VT1 : ID → Prop} {og L M P : List ID}
    (hog : og = L ++ M) (hfr : T0 = { G with regs := T0.regs })
    (hsz : T0.regs.size = g.valueTab.size)
    (htyS : Proof.Typed (Ctx.make tabs f) G) (htyT : Proof.Typed (Ctx.make tabs g) T0)
    (hDS : DenOK f.value? tabs G VS) (hMS : MemDefs f.value? tabs G VS)
    (hDT : DenOK (listedDefs g) tabs T0 VT1)
    (hVT1 : ∀ a, VT1 a → ∃ w, Placed g a w) (hdisj : ∀ x ∈ og, ¬ VT1 x)
    (hrel0 : ∀ a, VT1 a → VS a → ¬ IsTerm f.value? a → ¬ IsTerm (listedDefs g) a →
      Sem.Refines (rv G a) (rv T0 a))
    (hnd : og.Nodup) (htopo : TopoRem (argsF g) og)
    {b : ID} (hplaced : ∀ x ∈ og, ∃ w, Placed g x w ∧ w.id = x ∧ w.op ≠ .Phi ∧ w.block = b)
    (hinv : ∀ a, I.P b a (rv G a)) (hq : I.Q b (rv G)) (hSV : ∀ a, SAnc f b a → VS a)
    (hargsT : ∀ x ∈ og, ∀ w, g.value? x = some w → ∀ a ∈ w.args, VT1 a ∨ a ∈ og)
    (hVSog : ∀ a ∈ og, VS a → ¬ IsTerm (listedDefs g) a → a ∈ P)
    (hatom : ∀ x ∈ L, ∀ w, g.value? x = some w → termOp w.op = false →
      ∃ u, f.value? x = some u ∧ SameAtom u w ∧
        (x ∈ P → (∀ a ∈ u.args, VS a) ∧
          ∃ y, G.regs[x]? = some (some y) ∧ evalValue env (Ctx.make tabs f) G u = .ok y) ∧
        (x ∉ P → isRoot w.op = false ∧ w.op ≠ .Arg ∧ w.op ≠ .ArgIntReg)) :
    ∃ T', evalAll env (Ctx.make tabs g) T0 L = .ok T' ∧
      LoopInv tabs g G T0 VS VT1 f.value? L T' := by
  refine evalAll_induct L (LoopInv tabs g G T0 VS VT1 f.value?) ?_ L [] T0 rfl
    ⟨by cases T0; rfl, rfl, htyT, hDT.iff fun a => ⟨.inl, fun h => h.elim id fun h => absurd h List.not_mem_nil⟩,
      fun _ _ => rfl, fun a ha => hrel0 a (ha.elim id fun h => absurd h List.not_mem_nil)⟩
  intro d x s T hL ⟨hTf, hTs, hTt, hTD, hTk, hTr⟩
  have hog' : og = d ++ x :: (s ++ M) := by rw [hog, hL]; simp
  have hxog : x ∈ og := by rw [hog']; simp
  have hxL : x ∈ L := by rw [hL]; simp
  have hxd : x ∉ d := fun hm => by
    rw [hog'] at hnd
    exact (List.nodup_append.1 hnd).2.2 x hm x List.mem_cons_self rfl
  have hxV : ¬ (VT1 x ∨ x ∈ d) := fun h => h.elim (hdisj x hxog) hxd
  obtain ⟨w, hpw, hwid, hwphi, hwb⟩ := hplaced x hxog
  have hw := hpw.1
  have hxlt : x < T.regs.size := by rw [hTs, hsz]; exact lt_of_value? hw
  have hargs : ∀ a ∈ w.args, VT1 a ∨ a ∈ d := fun a ha => by
    rcases hargsT x hxog w hw a ha with h | h
    · exact .inl h
    · rw [hog'] at htopo h
      exact .inr (topoRem_before htopo (by rw [argsF_of hw]; exact Array.mem_toList_iff.2 ha) h)
  have hreg : ∀ a ∈ w.args, Reg T a := fun a ha => (hTD a (hargs a ha)).1
  have hstepV : stepV env (Ctx.make tabs g) T x = evalValue env (Ctx.make tabs g) T w := by
    unfold stepV; rw [show (Ctx.make tabs g).f = g from rfl, hw]
  have hty : (Ctx.make tabs g).tys[w.id]?.getD .other = tabs.ty w.type := by
    rw [hwid, tys_of_value hw]; rfl
  -- the common part of the invariant after setting `x`
  have common : ∀ y, y.retype (tabs.ty w.type) = y →
      (T.set x y = { T0 with regs := (T.set x y).regs }) ∧ (T.set x y).regs.size = T0.regs.size ∧
      Proof.Typed (Ctx.make tabs g) (T.set x y) ∧
      (∀ a, a ∉ d ++ [x] → (T.set x y).regs[a]? = T0.regs[a]?) := fun y hy => by
    refine ⟨by rw [hTf]; rfl, by simp [Frame.set, hTs], typed_set hTt (by rw [← hwid, hty]; exact hy),
      fun a ha => ?_⟩
    have hxa : x ≠ a := fun he => ha (by simp [he])
    rw [Frame.set_regs_ne hxa]; exact hTk a (fun hm => ha (by simp [hm]))
  have hkeep : ∀ y a, (VT1 a ∨ a ∈ d) → (T.set x y).regs[a]? = T.regs[a]? := fun y a ha =>
    Frame.set_regs_ne fun he => hxV (he ▸ ha)
  have hiff : ∀ a, ((VT1 a ∨ a ∈ d) ∨ a = x) ↔ (VT1 a ∨ a ∈ d ++ [x]) := fun a => by
    simp only [List.mem_append, List.mem_singleton, or_assoc]
  cases hterm : termOp w.op with
  | true =>
    have hev : evalValue env (Ctx.make tabs g) T w =
        .ok ((GoFV.Proof.Rules.opVal tabs w.op (tabs.ty w.type) w.auxInt w.aux (w.args.toList.map (rv T))).retype
          (tabs.ty w.type)) := by
      rw [evalValue_of_regs hreg, evalOp_term hterm, hty]; rfl
    refine ⟨_, by rw [hstepV, hev], ?_⟩
    obtain ⟨c1, c2, c3, c4⟩ := common _ (retype_idem _ _)
    refine ⟨c1, c2, c3, ?_, c4, fun a ha hVS hatD hatE => ?_⟩
    · exact (hTD.term (hkeep _) hxV (placed_listed hpw) hterm hargs
        (Frame.set_regs_self hxlt)).iff hiff
    · have hax : x ≠ a := fun he => hatE (he ▸ ⟨w, placed_listed hpw, hterm⟩)
      rw [rv_set_ne hax]
      refine hTr a ?_ hVS hatD hatE
      rcases (hiff a).2 ha with h | h
      · exact h
      · exact absurd h.symm hax
  | false =>
    have hatE : ¬ IsTerm (listedDefs g) x := fun ⟨w', hw', ht'⟩ => by
      rw [placed_listed hpw] at hw'; cases hw'; rw [hterm] at ht'; cases ht'
    obtain ⟨u, hu, hs, hin, hout⟩ := hatom x hxL w hw hterm
    -- the target's value and its refinement where the source evaluated `x`
    obtain ⟨y', hev, hy'⟩ : ∃ y', evalValue env (Ctx.make tabs g) T w = .ok y' ∧
        (x ∈ P → ∃ y, G.regs[x]? = some (some y) ∧ Sem.Refines y y') := by
      by_cases hxP : x ∈ P
      · obtain ⟨hargsS, y, hGy, hevS⟩ := hin hxP
        have hVTd : ∀ a, (VT1 a ∨ a ∈ d) → ∃ w, Placed g a w := fun a ha => by
          rcases ha with ha | ha
          · exact hVT1 a ha
          · obtain ⟨w, hp, -⟩ := hplaced a (by rw [hog']; exact List.mem_append_left _ ha)
            exact ⟨w, hp⟩
        have hr := tgt_atom_ref H hE (by rw [hTf, hfr]) hDS hMS hTD hVTd
          (fun a h1 h2 h3 h4 => hTr a h1 h2 h3 h4) htyS hTt hpw hu hs hterm hwphi hargsS hargs
          (hwb ▸ hinv) (hwb ▸ hq) (hwb ▸ hSV)
        rw [hevS] at hr
        obtain ⟨y', hT, hyy⟩ := res_ok_of_refines hr
        exact ⟨y', hT, fun _ => ⟨y, hGy, hyy⟩⟩
      · obtain ⟨hr, ha, hai⟩ := hout hxP
        obtain ⟨r, hr'⟩ := evalOp_safe (env := env) (ctx := Ctx.make tabs g) (fr := T)
          (argv := w.args.toList.map (rv T)) (ty := (Ctx.make tabs g).tys[w.id]?.getD .other) hr ha hai
        refine ⟨r.retype ((Ctx.make tabs g).tys[w.id]?.getD .other), ?_, fun h => absurd h hxP⟩
        rw [evalValue_of_regs hreg, hr']; rfl
    refine ⟨y', by rw [hstepV, hev], ?_⟩
    have hyt : y'.retype (tabs.ty w.type) = y' := by rw [← hty]; exact evalValue_typed hev
    obtain ⟨c1, c2, c3, c4⟩ := common y' hyt
    refine ⟨c1, c2, c3, ?_, c4, fun a ha hVS hatD hatE' => ?_⟩
    · exact (hTD.extend (W := fun a => a = x) (hkeep _) fun a ha _ => by
        subst ha; exact ⟨hatE, _, Frame.set_regs_self hxlt⟩).iff hiff
    · by_cases hax : x = a
      · subst hax
        obtain ⟨y, hGy, hyy⟩ := hy' (hVSog x hxog hVS hatE)
        rw [rv_of hGy, rv_of (Frame.set_regs_self hxlt)]; exact hyy
      · rw [rv_set_ne hax]
        refine hTr a ?_ hVS hatD hatE'
        rcases (hiff a).2 ha with h | h
        · exact h
        · exact absurd h.symm hax

end GoFV.Proof.AtomSim

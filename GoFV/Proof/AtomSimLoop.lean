import GoFV.Proof.AtomSimSet

/-!
# The target's schedule against a source reference frame (issue #113)

`tgt_atom_ref`: an atom of `g` evaluated in the target frame `T` refines the atom of `f` with
the same ID evaluated in the source frame `G`, when both frames' registers are their terms'
values over the atoms (`DenOK`) and the atoms both hold are refined; a changed `Store`
(`AtomArgsRefX`, issue #35) by `chgRef_apply`.

`tgt_loop`: the target evaluates a prefix `L` of its schedule from `T0`: term nodes always
evaluate (`evalPure`), atoms the source evaluated (`P`) evaluate to refinements of the source's
registers in `G`, other atoms are ops that never get stuck. Afterwards `DenOK` holds of `L` and
the atoms both frames hold are refined.
-/

-- Parallel elaboration (-j4) wrote this module's constants in a different order on every build
-- (3 builds, 3 hashes), so importers missed the shared cache (#1; LEARNINGS.md).
set_option Elab.async false

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

/-- A `Store`'s write on refined arguments succeeds with a refined memory. -/
theorem memDef_store_mono {tabs : Tables} {v : Value} (hop : v.op = .Store) {as bs : List Val}
    (h : RefinesList as bs) {y : Val} (hy : memDef tabs v as = some y) :
    ∃ y', memDef tabs v bs = some y' ∧ Sem.Refines y y' := by
  obtain ⟨a, q, x, m0, M', rfl, hq, hw, rfl⟩ : ∃ a q x m0 M', as = [a, x, .mem m0] ∧
      a.asPtrWord = some q ∧ m0.write q (encode (auxTy tabs v.aux) x) = some M' ∧ y = .mem M' := by
    match as with
    | [a, b, c] =>
      cases c <;> try (simp [memDef, hop] at hy; done)
      simp only [memDef, hop, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hy
      obtain ⟨q, hq, M', hw, rfl⟩ := hy
      exact ⟨_, _, _, _, M', rfl, hq, hw, rfl⟩
    | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ => simp [memDef, hop] at hy
  obtain ⟨_, _, rfl, h1, h⟩ := h.cons_inv
  obtain ⟨_, _, rfl, h2, h⟩ := h.cons_inv
  obtain ⟨_, _, rfl, h3, h⟩ := h.cons_inv
  cases h.nil_inv; cases h3 with | mem hm =>
  obtain ⟨M'', hw', hMM⟩ := hm.write (encode_mono _ h2) hw
  exact ⟨.mem M'', by simp [memDef, hop, h1.asPtrWord hq, hw'], .mem hMM⟩

/-- A `Store` whose write succeeds evaluates to it. -/
theorem memRoot_of_memDef_store {ctx : Ctx} {v : Value} (hop : v.op = .Store) {argv : List Val}
    {y : Val} (h : memDef ctx.tabs v argv = some y) : memRoot ctx v argv = .ok y := by
  match argv with
  | [a, b, c] =>
    cases c <;> try (simp [memDef, hop] at h; done)
    simp only [memDef, hop, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨q, hq, M', hw, rfl⟩ := h
    simp [memRoot, hop, hq, hw, writeRes]
  | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ => simp [memDef, hop] at h

/-- A `Move`'s copy on refined arguments succeeds with a refined memory. -/
theorem memDef_move_mono {tabs : Tables} {v : Value} (hop : v.op = .Move) {as bs : List Val}
    (h : RefinesList as bs) {y : Val} (hy : memDef tabs v as = some y) :
    ∃ y', memDef tabs v bs = some y' ∧ Sem.Refines y y' := by
  obtain ⟨a, b, d, s, m0, cs, M', rfl, hd, hs, hr, hw, rfl⟩ : ∃ a b d s m0 cs M',
      as = [a, b, .mem m0] ∧ a.asPtrWord = some d ∧ b.asPtrWord = some s ∧
      m0.read s v.auxInt.toInt.toNat = some cs ∧ m0.write d cs = some M' ∧ y = .mem M' := by
    match as with
    | [a, b, c] =>
      cases c <;> try (simp [memDef, hop] at hy; done)
      simp only [memDef, hop, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hy
      obtain ⟨d, hd, s, hs, cs, hr, M', hw, rfl⟩ := hy
      exact ⟨_, _, _, _, _, cs, M', rfl, hd, hs, hr, hw, rfl⟩
    | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ => simp [memDef, hop] at hy
  obtain ⟨_, _, rfl, h1, h⟩ := h.cons_inv
  obtain ⟨_, _, rfl, h2, h⟩ := h.cons_inv
  obtain ⟨_, _, rfl, h3, h⟩ := h.cons_inv
  cases h.nil_inv; cases h3 with | mem hm =>
  obtain ⟨cs', hr', hcs⟩ := hm.read hr
  obtain ⟨M'', hw', hMM⟩ := hm.write hcs hw
  exact ⟨.mem M'', by simp [memDef, hop, h1.asPtrWord hd, h2.asPtrWord hs, hr', hw',
    -Int64.toNat_toInt], .mem hMM⟩

/-- A `Move` whose copy succeeds evaluates to it. -/
theorem memRoot_of_memDef_move {ctx : Ctx} {v : Value} (hop : v.op = .Move) {argv : List Val}
    {y : Val} (h : memDef ctx.tabs v argv = some y) : memRoot ctx v argv = .ok y := by
  match argv with
  | [a, b, c] =>
    cases c <;> try (simp [memDef, hop] at h; done)
    simp only [memDef, hop, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨d, hd, s, hs, cs, hr, M', hw, rfl⟩ := h
    simp [memRoot, hop, hd, hs, hr, hw, writeRes, -Int64.toNat_toInt]
  | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ => simp [memDef, hop] at h

theorem memDef_chg_mono {tabs : Tables} {v : Value} (hop : v.op = .Store ∨ v.op = .Move)
    {as bs : List Val} (h : RefinesList as bs) {y : Val} (hy : memDef tabs v as = some y) :
    ∃ y', memDef tabs v bs = some y' ∧ Sem.Refines y y' :=
  hop.elim (fun hop => memDef_store_mono hop h hy) fun hop => memDef_move_mono hop h hy

theorem memRoot_of_memDef_chg {ctx : Ctx} {v : Value} (hop : v.op = .Store ∨ v.op = .Move)
    {argv : List Val} {y : Val} (h : memDef ctx.tabs v argv = some y) : memRoot ctx v argv = .ok y :=
  hop.elim (fun hop => memRoot_of_memDef_store hop h) fun hop => memRoot_of_memDef_move hop h

/-- **`ChgRefP` on registers**: if the source's `Store` (`Move`) `u` writes on its arguments'
registers (their terms' values over the atoms, `DenOK`), the target's `Store` (`Move`) `w` writes a
refined memory on its arguments' registers. The valuations are those of `termRef_apply`. -/
theorem chgRef_apply {D E : ID → Option Value} {tabs : Tables} {u w : Value}
    (hC : ChgRefP D tabs u E w) (hws : w.op = .Store ∨ w.op = .Move) {FS FT : Frame}
    {VS VT : ID → Prop}
    (hS : DenOK D tabs FS VS) (hG : DenOK E tabs FT VT)
    (hrel : ∀ a, VS a → ¬ IsTerm D a → VT a → ¬ IsTerm E a → Sem.Refines (rv FS a) (rv FT a))
    (htyS : ∀ a, VS a → ¬ IsTerm D a → (rv FS a).retype (shape D tabs a) = rv FS a)
    (htyT : ∀ a, VT a → ¬ IsTerm E a → (rv FT a).retype (shape E tabs a) = rv FT a)
    (hsh : ∀ a, VS a → ¬ IsTerm D a → ¬ IsTerm E a → (E a).isSome → ¬ VT a →
      (rv FS a).retype (shape E tabs a) = rv FS a)
    (hMS : MemDefs D tabs FS VS) (huS : ∀ a ∈ u.args, VS a) (hwT : ∀ a ∈ w.args, VT a) {y : Val}
    (hy : memDef tabs u (u.args.toList.map (rv FS)) = some y) :
    ∃ y', memDef tabs w (w.args.toList.map (rv FT)) = some y' ∧ Sem.Refines y y' := by
  classical
  let ρ : ID → Val := fun a => if VS a ∧ ¬ IsTerm D a then rv FS a else .poison
  let ρ' : ID → Val := fun a => if VT a ∧ ¬ IsTerm E a then rv FT a else ρ a
  have hval : ValRef ρ ρ' := fun a => by
    by_cases h1 : VT a ∧ ¬ IsTerm E a
    · by_cases h2 : VS a ∧ ¬ IsTerm D a
      · simp only [ρ', ρ, h1, h2]
        exact hrel a h2.1 h2.2 h1.1 h1.2
      · simp only [ρ', ρ, h1, h2, ite_false]
        exact .poison _
    · simp only [ρ', h1, ite_false]; exact Sem.Refines.refl _
  have htD : Term.Typed D tabs ρ := fun a hat _ => by
    by_cases h2 : VS a
    · simp only [ρ, h2, hat, not_false_eq_true, and_self, ite_true]; exact htyS a h2 hat
    · simp only [ρ, h2, false_and, ite_false]; exact retype_poison _
  have htE : Term.Typed E tabs ρ' := fun a hat hdef => by
    by_cases h1 : VT a
    · simp only [ρ', h1, hat, not_false_eq_true, and_self, ite_true]; exact htyT a h1 hat
    · simp only [ρ', h1, false_and, ite_false]
      by_cases h2 : VS a ∧ ¬ IsTerm D a
      · simp only [ρ, h2]; exact hsh a h2.1 h2.2 hat hdef h1
      · simp only [ρ, h2, ite_false]; exact retype_poison _
  have hMA : MemAtoms D tabs ρ := memAtoms_of hS hMS (fun a ha hat => by simp [ρ, ha, hat])
    fun a hat hne => by
      by_cases h2 : VS a ∧ ¬ IsTerm D a
      · exact h2.1
      · exact absurd (ite_eq_right h2) hne
  obtain ⟨N, hN⟩ := hS.list (ρ := ρ) (fun a ha hat => by simp [ρ, ha, hat]) (l := u.args.toList)
    fun a ha => huS a (Array.mem_toList_iff.1 ha)
  obtain ⟨m, y', hy', hyy⟩ := hC ρ ρ' hval htD htE hMA N y (by rw [hN N (Nat.le_refl N)]; exact hy)
  obtain ⟨M, hM⟩ := hG.list (ρ := ρ') (fun a ha hat => by simp [ρ', ha, hat]) (l := w.args.toList)
    fun a ha => hwT a (Array.mem_toList_iff.1 ha)
  have hl : RefinesList (w.args.toList.map (den E tabs ρ' m)) (w.args.toList.map (rv FT)) := by
    rw [← hM (max m M) (Nat.le_max_right m M)]
    exact refinesList_map fun a _ => den_fuel_mono E tabs ρ' m (max m M) a (Nat.le_max_left m M)
  obtain ⟨y'', h1, h2⟩ := memDef_chg_mono hws hl hy'
  exact ⟨y'', h1, hyy.trans h2⟩

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
    {x : ID} {u w : Value} (hpw : Placed g x w) (hu : f.value? x = some u) (hs : SameAtomX u w)
    (ht : termOp w.op = false) (hnp : w.op ≠ .Phi) (hargsS : ∀ a ∈ u.args, VS a)
    (hargsT : ∀ a ∈ w.args, VT a)
    (hinv : ∀ a, I.P w.block a (rv G a)) (hq : I.Q w.block (rv G))
    (hSV : ∀ a, SAnc f w.block a → VS a) :
    Res.Refines (evalValue env (Ctx.make tabs f) G u) (evalValue env (Ctx.make tabs g) T w) := by
  obtain ⟨hw, hbm, blk, hblk, hx⟩ := hpw
  obtain ⟨w', hw', hwid, -⟩ := H.wg.valueId w.block blk ⟨hbm, hblk⟩ x hx
  rw [hw] at hw'; cases hw'
  have huid : u.id = x := hs.2.2.2.2.2.2.trans hwid
  have htyS' : ∀ a, VS a → ¬ IsTerm f.value? a →
      (rv G a).retype (shape f.value? tabs a) = rv G a := fun a ha _ => by
    rw [← tys_shape]; exact htyS a _ (reg_rv (hDS a ha).1)
  have hshT : ∀ a, VT a → shape (listedDefs g) tabs a = shape g.value? tabs a := fun a ha => by
    obtain ⟨v, hp⟩ := hVT a ha
    simp [shape, placed_listed hp, hp.1]
  have hty : (Ctx.make tabs g).tys[w.id]?.getD .other = (Ctx.make tabs f).tys[u.id]?.getD .other := by
    rw [hwid, huid, tys_of_value hw, tys_of_value hu, hs.2.1]
  rcases H.args w.block hbm blk hblk x hx w hw ht with ⟨u', hu', -, -, -, hax, -, hTR⟩ |
    ⟨u', hu', hus, hws, hC⟩
  · rw [hu] at hu'; cases hu'
    refine atom_eval_mono hE (ctx_eq H.ok.ownAux) hfr
      ⟨hs.1, hs.2.1, hs.2.2.1, hax, hs.2.2.2.2⟩ hty (fun a ha => (hDS a (hargsS a ha)).1)
      (fun a ha => (hDT a (hargsT a ha)).1) fun i hi => ?_
    have hi' : i < w.args.size := hs.2.2.2.2.1 ▸ hi
    refine termRef_apply ((hTR i hi').1 hnp) hDS (hargsS _ (getElem!_mem' hi)) hDT
      (hargsT _ (getElem!_mem' hi')) (fun a h1 h2 h3 h4 => hrel a h3 h1 h2 h4) htyS'
      (fun a ha _ => by rw [hshT a ha, ← tys_shape]; exact htyT a _ (reg_rv (hDT a ha).1))
      (fun a ha hat hat' hdef _ => ?_) hinv (I.poisonAtom _) hSV
      (fun ρ hρ => I.qpois _ _ ρ hq hρ) hMS
    rw [shape_atom_def H hat' hdef]; exact htyS' a ha hat
  · -- a changed store or `Move`: the source's write, refined by the target's (`chgRef_apply`)
    rw [hu] at hu'; cases hu'
    have hmw : memOp w.op = true := by rcases hws with h | h <;> rw [h] <;> rfl
    cases hev : evalValue env (Ctx.make tabs f) G u with
    | stuck msg => exact .stuck _ _
    | panic e m =>
      have := evalValue_panic_op hev
      rw [hus] at this
      rcases hws with h' | h' <;> rw [h'] at this <;> rcases this with h | h <;> cases h
    | ok y =>
      obtain ⟨r, hr, rfl⟩ := evalValue_memOp rfl (by rw [hus]; exact hmw) hev
      obtain ⟨r', hr', hrr⟩ := chgRef_apply hC hws hDS hDT (fun a h1 h2 h3 h4 => hrel a h3 h1 h2 h4)
        htyS' (fun a ha _ => by rw [hshT a ha, ← tys_shape]; exact htyT a _ (reg_rv (hDT a ha).1))
        (fun a ha hat hat' hdef _ => by rw [shape_atom_def H hat' hdef]; exact htyS' a ha hat)
        hMS hargsS hargsT hr
      rw [evalValue_of_regs (fun a ha => (hDT a (hargsT a ha)).1),
        evalOp_memOp hmw (by rcases hws with h | h <;> rw [h] <;> decide),
        memRoot_of_memDef_chg (ctx := Ctx.make tabs g) hws hr', hty]
      exact .ok (retype_mono _ hrr)

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
      ∃ u, f.value? x = some u ∧ SameAtomX u w ∧
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

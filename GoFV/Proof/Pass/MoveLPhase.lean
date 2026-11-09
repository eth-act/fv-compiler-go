import GoFV.Proof.Pass.MoveLPair
import GoFV.Proof.SimL

variable [GoFV.SSA.Sem.Addrs]

/-!
# Evaluating a block's values on one side, the other side fixed

Inside a block, the source and the target evaluate their schedules in different orders (values
moved in or out, clones, copies). `phaseS` runs the source's list with the target's frame fixed,
`phaseT` the target's with the source's fixed; each keeps lemma (D) by IDs (`Av`), closure
under arguments (`Closed`) and agreement of related registers (`Agree`). The lists are
dependency orders (`Ready`, from `ready_of`).
-/

namespace GoFV.Proof.MoveL

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof

variable {pr : Bool} {ok : Array Bool} {f g : Func} {tabs : Tables} {md : LMode} {env : Env}

/-- The selectors of `g`'s pair loads have the shape of their component of the pair load's
two-component tuple shape (`selShapesB`). -/
def SelShapes (tabs : Tables) (g : Func) : Prop :=
  ∀ x gv i l lv, g.value? x = some gv → selIdx gv.op = some i → gv.args.toList = [l] →
    g.value? l = some lv → pairLoadOp lv.op = true →
    ∃ c0 c1, shapeL tabs lv.type = .tuple [c0, c1] ∧ [c0, c1].getD i .other = shapeL tabs gv.type

/-- What `refinesL_of_move` assumes of the pair beyond the blocks. -/
structure Hyp (pr : Bool) (ok : Array Bool) (f g : Func) (tabs : Tables) (md : LMode) : Prop where
  cert : certValid pr ok f g = true
  own : g.ownAux = f.ownAux
  low : g.lowered = f.lowered
  nf : md.faulting = false
  sel : pr = true → md.low = true ∧ g.lowered = true ∧ SelShapes tabs g

/-- The values `X` have registers, and the non-`Phi`s re-evaluate to them (lemma (D) by IDs). -/
def Av (md : LMode) (env : Env) (ctx : Ctx) (X : ID → Prop) (fr : Frame) : Prop :=
  ∀ x, X x → ∃ v r, ctx.f.value? x = some v ∧ v.id = x ∧ fr.regs[x]? = some (some r) ∧
    (v.op ≠ .Phi → evalValueL md env ctx fr v = .ok r)

/-- `X` is closed under the arguments of its non-`Phi`s. -/
def Closed (h : Func) (X : ID → Prop) : Prop :=
  ∀ x v, X x → h.value? x = some v → v.op ≠ .Phi → ∀ a ∈ v.args, X a

/-- Related values of `XT` (target) and `XS` (source) hold the same registers. -/
def Agree (pr : Bool) (ok : Array Bool) (f g : Func) (XT XS : ID → Prop) (frT frS : Frame) :
    Prop :=
  ∀ x y, XT x → XS y → Rel pr ok f g x y → frT.regs[x]? = frS.regs[y]?

/-- `l` is a dependency order after `X`: each element satisfies `P`, is new, and has its
arguments (`D`) among `X` and the earlier elements. -/
def Ready (D : ID → List ID) (P : ID → Prop) : (ID → Prop) → List ID → Prop
  | _, [] => True
  | X, y :: l => P y ∧ ¬ X y ∧ (∀ a ∈ D y, X a) ∧ Ready D P (fun a => X a ∨ a = y) l

theorem ready_of {D : ID → List ID} {P : ID → Prop} :
    ∀ {l : List ID} {X : ID → Prop}, l.Nodup → TopoRem D l → (∀ y ∈ l, ∀ a ∈ D y, X a ∨ a ∈ l) →
      (∀ y ∈ l, ¬ X y) → (∀ y ∈ l, P y) → Ready D P X l
  | [], _, _, _, _, _, _ => trivial
  | y :: l, X, hnd, ht, ha, hn, hp => by
    refine ⟨hp y List.mem_cons_self, hn y List.mem_cons_self, fun a hd => ?_, ?_⟩
    · rcases ha y List.mem_cons_self a hd with h | h
      · exact h
      · exact absurd h (ht.1 a hd)
    · refine ready_of (List.nodup_cons.1 hnd).2 ht.2 (fun y' hy' a hd => ?_) (fun y' hy' hx => ?_)
        (fun y' hy' => hp y' (List.mem_cons_of_mem _ hy'))
      · rcases ha y' (List.mem_cons_of_mem _ hy') a hd with h | h
        · exact .inl (.inl h)
        · rcases List.mem_cons.1 h with rfl | h
          · exact .inl (.inr rfl)
          · exact .inr h
      · rcases hx with hx | rfl
        · exact hn y' (List.mem_cons_of_mem _ hy') hx
        · exact (List.nodup_cons.1 hnd).1 hy'

/-- A prefix of a ready list is ready, and the next element's arguments are available. -/
theorem ready_split {D : ID → List ID} {P : ID → Prop} :
    ∀ {pre : List ID} {r : ID} {post : List ID} {X : ID → Prop},
      Ready D P X (pre ++ r :: post) →
      Ready D P X pre ∧ P r ∧ ¬ (X r ∨ r ∈ pre) ∧ ∀ a ∈ D r, X a ∨ a ∈ pre
  | [], r, post, X, h => ⟨trivial, h.1, fun h' => h'.elim h.2.1 (by simp), fun a ha => .inl (h.2.2.1 a ha)⟩
  | y :: pre, r, post, X, h => by
    obtain ⟨hp, hn, ha, hr⟩ := h
    obtain ⟨h1, h2, h3, h4⟩ := ready_split hr
    refine ⟨⟨hp, hn, ha, h1⟩, h2, fun h' => ?_, fun a hd => ?_⟩
    · rcases h' with h' | h'
      · exact h3 (.inl (.inl h'))
      · rcases List.mem_cons.1 h' with rfl | h'
        · exact h3 (.inl (.inr rfl))
        · exact h3 (.inr h')
    · rcases h4 a hd with (h | rfl) | h
      · exact .inl h
      · exact .inr List.mem_cons_self
      · exact .inr (List.mem_cons_of_mem _ h)

private theorem pred_cons (X : ID → Prop) (y : ID) (l : List ID) :
    (fun a => (X a ∨ a = y) ∨ a ∈ l) = (fun a => X a ∨ a ∈ y :: l) := by
  funext a
  apply propext
  simp only [List.mem_cons]
  constructor
  · rintro ((h | h) | h)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr h)
  · rintro (h | h | h)
    · exact .inl (.inl h)
    · exact .inl (.inr h)
    · exact .inr h

/-! ## Shapes and arguments -/

theorem tys_eq (H : Hyp pr ok f g tabs md) {x y : ID} {gv fv : Value} (hg : g.value? x = some gv)
    (hf : f.value? y = some fv) (hty : gv.type = fv.type) :
    (Ctx.makeL tabs g).tys[x]? = (Ctx.makeL tabs f).tys[y]? := by
  rw [tysL_of_value hg, tysL_of_value hf, H.low, hty]

/-- Corresponding arguments hold equal registers. -/
theorem argsAgree {XT XS : ID → Prop} {frT frS : Frame} (hag : Agree pr ok f g XT XS frT frS)
    {gv fv : Value} (hsz : gv.args.size = fv.args.size)
    (hrel : ∀ (k : Nat) (hk : k < gv.args.size) (hk' : k < fv.args.size),
      Rel pr ok f g gv.args[k] fv.args[k])
    (hT : ∀ a ∈ gv.args, XT a) (hS : ∀ b ∈ fv.args, XS b)
    (hdef : ∀ b ∈ fv.args, ∃ z, frS.regs[b]? = some (some z)) :
    ∀ (k : Nat) (a : ID), gv.args[k]? = some a →
      ∃ b z, fv.args[k]? = some b ∧ frT.regs[a]? = some (some z) ∧ frS.regs[b]? = some (some z) := by
  intro k a ha
  obtain ⟨hk, rfl⟩ := Array.getElem?_eq_some_iff.1 ha
  have hk' : k < fv.args.size := hsz ▸ hk
  have hbm : fv.args[k] ∈ fv.args := Array.getElem_mem hk'
  obtain ⟨z, hz⟩ := hdef _ hbm
  refine ⟨fv.args[k], z, by simp [hk'], ?_, hz⟩
  rw [hag _ _ (hT _ (Array.getElem_mem hk)) (hS _ hbm) (hrel k hk hk'), hz]

theorem clone_rel {gv fv : Value} (hargs : gv.args = fv.args) (hok : ∀ a ∈ gv.args, okAt ok a = true) :
    ∀ (k : Nat) (hk : k < gv.args.size) (hk' : k < fv.args.size), Rel pr ok f g gv.args[k] fv.args[k] := by
  intro k hk hk'
  have : fv.args[k] = gv.args[k] := by simp [hargs]
  rw [this]
  exact rel_ident (hok _ (Array.getElem_mem hk))

/-! ## `pair`'s cases -/

/-- With `pr`, a target value's shape is its type's lowered shape. -/
theorem tysT_of (H : Hyp pr ok f g tabs md) (hpr : pr = true) {x : ID} {v : Value}
    (hv : g.value? x = some v) : (Ctx.makeL tabs g).tys[x]?.getD .other = shapeL tabs v.type := by
  rw [tysL_of_value hv, (H.sel hpr).2.1]
  rfl

theorem pairRel_ne_phi {m : Nat} {gv fv : Value}
    (hs : SelRel pr ok f g m gv fv ∨ StRel pr ok f g m gv fv ∨ RevRel pr ok f g m gv fv) :
    gv.op ≠ .Phi ∧ fv.op ≠ .Phi := by
  rcases hs with ⟨i, -, -, w, pop, -, -, -, -, hi, -, hw, -⟩ |
    ⟨w, pop, -, -, -, -, -, -, -, -, -, -, hw, -, -, -, hop, -⟩ |
    ⟨w, pop, -, -, -, -, -, -, -, -, -, -, hw, -, -, -, hop, -⟩
  · exact ⟨selIdx_ne_phi hi, ldPairOf_ne_phi hw⟩
  · exact ⟨hop ▸ stPairOf_pop_ne_phi hw, stPairOf_ne_phi hw⟩
  · exact ⟨hop ▸ stPairOf_pop_ne_phi hw, stPairOf_ne_phi hw⟩

/-- **`relB`'s pair cases evaluate alike**: a selector of a pair load, or a pair store (in order
or reversed), whose arguments are available in the target evaluates as the related source value
whose arguments are available in the source. -/
theorem pair_eval (H : Hyp pr ok f g tabs md) {XT XS : ID → Prop} {frT frS : Frame}
    (hAvT : Av md env (Ctx.makeL tabs g) XT frT) (hclT : Closed g XT)
    (hAvS : Av md env (Ctx.makeL tabs f) XS frS) (hclS : Closed f XS)
    (hag : Agree pr ok f g XT XS frT frS) {x y : ID} {gv fv : Value} {m : Nat}
    (hgv : g.value? x = some gv) (hgid : gv.id = x) (hfv : f.value? y = some fv)
    (hfid : fv.id = y) (hpr : pr = true) (hty : gv.type = fv.type)
    (hs : SelRel pr ok f g m gv fv ∨ StRel pr ok f g m gv fv ∨ RevRel pr ok f g m gv fv)
    (hT : ∀ a ∈ gv.args, XT a) (hS : ∀ b ∈ fv.args, XS b) {w : Val}
    (hev : evalValueL md env (Ctx.makeL tabs f) frS fv = .ok w) :
    evalValueL md env (Ctx.makeL tabs g) frT gv = .ok w := by
  have hcG : (Ctx.makeL tabs g).f = g := makeL_f tabs g
  have hcF : (Ctx.makeL tabs f).f = f := makeL_f tabs f
  have htabs : (Ctx.makeL tabs g).tabs = (Ctx.makeL tabs f).tabs := by
    rw [tabs_makeL, tabs_makeL]
  have hact : (Ctx.makeL tabs g).act = (Ctx.makeL tabs f).act := by
    rw [act_makeL, act_makeL]; rfl
  have pairReg : ∀ a b, XT a → XS b → relB pr ok f g m a b = true →
      ∃ z, frT.regs[a]? = some (some z) ∧ frS.regs[b]? = some (some z) := fun a b ha hb hr => by
    obtain ⟨-, z, -, -, hz, -⟩ := hAvS b hb
    exact ⟨z, (hag a b ha hb ⟨m, hr⟩).trans hz, hz⟩
  have memL : ∀ {l : List ID} {a : ID} {arr : Array ID}, arr.toList = l → a ∈ l → a ∈ arr :=
    fun h ha => by rw [← Array.mem_toList_iff, h]; exact ha
  have hty' : (Ctx.makeL tabs g).tys[gv.id]? = (Ctx.makeL tabs f).tys[fv.id]? := by
    rw [hgid, hfid]; exact tys_eq H hgv hfv hty
  rcases hs with ⟨i, l, lv, wd, pop, p', m', p, mm, hsel, hgl, hld, hlv, hlop, haux, hai, hla, hfa,
      hrp, hrm⟩ |
    ⟨wd, pop, p', a', b', m', p, b, ym, mv, a, mm, hw, hga, hfa, hmv, hop, hmop, hmaux, hgaux,
      hgai, hfai, hma, h1, h2, h3, h4⟩ |
    ⟨wd, pop, p', a', b', m', p, a, ym, mv, b, mm, hw, hga, hfa, hmv, hop, hmop, hmaux, hgaux,
      hgai, hmai, hma, h1, h2, h3, h4⟩
  · obtain ⟨hlow, -, hsh⟩ := H.sel hpr
    have hlx : XT l := hT l (memL hgl (by simp))
    obtain ⟨lv', rl, hlv', hlid, hrl, hrle⟩ := hAvT l hlx
    rw [hcG, hlv] at hlv'; cases hlv'
    have hpl : pairLoadOp lv.op = true := hlop ▸ ldPairOf_pairLoadOp hld
    have hlph : lv.op ≠ .Phi := pairLoadOp_ne_phi hpl
    have hTl := hclT l lv hlx hlv hlph
    obtain ⟨zp, hzp, hzp'⟩ :=
      pairReg p' p (hTl p' (memL hla (by simp))) (hS p (memL hfa (by simp))) hrp
    obtain ⟨zm, hzm, hzm'⟩ :=
      pairReg m' mm (hTl m' (memL hla (by simp))) (hS mm (memL hfa (by simp))) hrm
    obtain ⟨c0, c1, hc, hci⟩ := hsh x gv i l lv hgv hsel hgl hlv hpl
    rw [← hev]
    refine evalValueL_selPair hlow H.nf htabs hact hsel hgl hld hlop haux hai hla hfa
      (c0 := c0) (c1 := c1) ?_ ?_ ?_ hrl (hrle hlph) hzp hzp' hzm hzm'
    · rw [hlid, tysT_of H hpr hlv, hc]
    · rw [hgid, tysT_of H hpr hgv, hci]
    · rw [hty']
  · have hymS : XS ym := hS ym (memL hfa (by simp))
    obtain ⟨mv', rm, hmv', -, hrm, hrme⟩ := hAvS ym hymS
    rw [hcF, hmv] at hmv'; cases hmv'
    have hmph : mv.op ≠ .Phi := hmop ▸ stPairOf_ne_phi hw
    have hSm := hclS ym mv hymS hmv hmph
    obtain ⟨zp, hzp, hzp'⟩ :=
      pairReg p' p (hT p' (memL hga (by simp))) (hS p (memL hfa (by simp))) h1
    obtain ⟨za, hza, hza'⟩ :=
      pairReg a' a (hT a' (memL hga (by simp))) (hSm a (memL hma (by simp))) h2
    obtain ⟨zb, hzb, hzb'⟩ :=
      pairReg b' b (hT b' (memL hga (by simp))) (hS b (memL hfa (by simp))) h3
    obtain ⟨zm, hzm, hzm'⟩ :=
      pairReg m' mm (hT m' (memL hga (by simp))) (hSm mm (memL hma (by simp))) h4
    exact evalValueL_stPair H.nf htabs hact hw hga hfa hop hmop hmaux hgaux hgai hfai hma hty'
      hzp hzp' hza hza' hzb hzb' hzm hzm' hrm (hrme hmph) hev
  · have hymS : XS ym := hS ym (memL hfa (by simp))
    obtain ⟨mv', rm, hmv', -, hrm, hrme⟩ := hAvS ym hymS
    rw [hcF, hmv] at hmv'; cases hmv'
    have hmph : mv.op ≠ .Phi := hmop ▸ stPairOf_ne_phi hw
    have hSm := hclS ym mv hymS hmv hmph
    obtain ⟨zp, hzp, hzp'⟩ :=
      pairReg p' p (hT p' (memL hga (by simp))) (hS p (memL hfa (by simp))) h1
    obtain ⟨za, hza, hza'⟩ :=
      pairReg a' a (hT a' (memL hga (by simp))) (hS a (memL hfa (by simp))) h2
    obtain ⟨zb, hzb, hzb'⟩ :=
      pairReg b' b (hT b' (memL hga (by simp))) (hSm b (memL hma (by simp))) h3
    obtain ⟨zm, hzm, hzm'⟩ :=
      pairReg m' mm (hT m' (memL hga (by simp))) (hSm mm (memL hma (by simp))) h4
    exact evalValueL_stPairRev H.nf htabs hact hw hga hfa hop hmop hmaux hgaux hgai hmai hma
      hty' hzp hzp' hza hza' hzb hzb' hzm hzm' hrm (hrme hmph) hev

/-! ## The source evaluates a value -/

/-- A value `y` the source evaluates to `w`: every related target value already available holds
`w`. -/
theorem agree_stepS (H : Hyp pr ok f g tabs md) {XT XS : ID → Prop} {frT frS : Frame}
    (hfr : frT = { frS with regs := frT.regs }) (hAv : Av md env (Ctx.makeL tabs g) XT frT)
    (hcl : Closed g XT) (hAvS : Av md env (Ctx.makeL tabs f) XS frS) (hclS : Closed f XS)
    (hag : Agree pr ok f g XT XS frT frS) {y : ID} {fv : Value} {w : Val}
    (hfv : f.value? y = some fv) (hid : fv.id = y) (hph : fv.op ≠ .Phi)
    (hargs : ∀ b ∈ fv.args, XS b) (hev : evalValueL md env (Ctx.makeL tabs f) frS fv = .ok w) :
    ∀ n x, XT x → relB pr ok f g n x y = true → frT.regs[x]? = some (some w) := by
  have hdef : ∀ b ∈ fv.args, ∃ z, frS.regs[b]? = some (some z) :=
    evalValueL_args_def (by rw [hev]; nofun)
  have hcf : (Ctx.makeL tabs g).f = g := makeL_f tabs g
  -- identity and clone
  have base : ∀ x, XT x → ((x = y ∧ okAt ok x = true) ∨
      (∃ gv fv', g.value? x = some gv ∧ f.value? y = some fv' ∧ cloneB ok f g gv fv' = true)) →
      frT.regs[x]? = some (some w) := by
    intro x hx hc
    rcases hc with ⟨rfl, hok⟩ | ⟨gv, fv', hgv, hfv', hc⟩
    · obtain ⟨gv, fv', hgv, hfv', hop, hty, hsz, hrel, -, hrest⟩ :=
        okLocal_spec (okLocal_of H.cert hok)
      rw [hfv] at hfv'; cases hfv'
      obtain ⟨gv', r, hgv', hgid, hr, hre⟩ := hAv x hx
      rw [hcf, hgv] at hgv'; cases hgv'
      have hgph : gv.op ≠ .Phi := hop ▸ hph
      obtain ⟨haux, hai, hsx⟩ := hrest hgph
      have he := evalValueL_ident (md := md) (env := env) (tabs := tabs) hfr hop haux hai
        (hgid.trans hid.symm) hsz
        (argsAgree hag hsz hrel (fun a ha => hcl x gv hx hgv hgph a ha) hargs hdef)
        (by rw [hgid, hid]; exact tys_eq H hgv hfv hty) hsx H.own
      rw [hre hgph, hev] at he
      cases he; exact hr
    · rw [hfv] at hfv'; cases hfv'
      obtain ⟨ht, hop, hty, haux, hai, hargs', hok, hsx⟩ := cloneB_spec hc
      obtain ⟨gv', r, hgv', hgid, hr, hre⟩ := hAv x hx
      rw [hcf, hgv] at hgv'; cases hgv'
      have hgph := totalOp_ne_phi ht
      have he := evalValueL_clone (md := md) (env := env) (tabs := tabs) H.nf hfr (hop ▸ ht) hop
        haux hai (by rw [hargs'])
        (argsAgree hag (by rw [hargs']) (clone_rel hargs' hok)
          (fun a ha => hcl x gv hx hgv hgph a ha) hargs hdef)
        (by rw [hgid, hid]; exact tys_eq H hgv hfv hty) hsx H.own
      rw [hre hgph, hev] at he
      cases he; exact hr
  intro n
  induction n with
  | zero =>
    intro x hx hr
    rcases relB_cases hr with h | h | ⟨-, -, -, m, -, -, -, -, -, -, hm, -⟩ |
      ⟨-, -, m, -, -, -, -, hm, -⟩
    · exact base x hx (.inl h)
    · exact base x hx (.inr h)
    · cases hm
    · cases hm
  | succ n ih =>
    intro x hx hr
    rcases relB_cases hr with h | h | ⟨gv, fv', z, m, hgv, hfv', hcp, -, hty, hz, hm, hrz⟩ |
      ⟨gv, fv', m, hgv, hfv', hpr, hty, -, hs⟩
    · exact base x hx (.inl h)
    · exact base x hx (.inr h)
    · rw [hfv] at hfv'; cases hfv'
      cases hm
      have hgph : gv.op ≠ .Phi := by rw [hcp]; decide
      have hzm : z ∈ gv.args := by rw [← Array.mem_toList_iff, hz]; exact List.mem_cons_self
      have hzw := ih z (hcl x gv hx hgv hgph z hzm) hrz
      obtain ⟨gv', r, hgv', hgid, hr, hre⟩ := hAv x hx
      rw [hcf, hgv] at hgv'; cases hgv'
      have he := hre hgph
      rw [evalValueL_copy hcp hz hzw] at he
      cases he
      rw [hr, hgid, tys_eq (tabs := tabs) H hgv hfv hty, ← hid, evalValueL_retype hev]
    · rw [hfv] at hfv'; cases hfv'
      obtain ⟨gv', r, hgv', hgid, hr, hre⟩ := hAv x hx
      rw [hcf, hgv] at hgv'; cases hgv'
      have hgph := (pairRel_ne_phi hs).1
      have he := pair_eval H hAv hcl hAvS hclS hag hgv hgid hfv hid hpr hty hs
        (hcl x gv hx hgv hgph) hargs hev
      rw [hre hgph] at he
      cases he; exact hr

/-- **The source evaluates `l`**, the target's frame fixed. -/
theorem phaseS (H : Hyp pr ok f g tabs md) {XT : ID → Prop} {frT : Frame}
    (hAvT : Av md env (Ctx.makeL tabs g) XT frT) (hclT : Closed g XT) :
    ∀ {l : List ID} {XS : ID → Prop} {frS frS' : Frame},
      Ready (argsF f) (fun y => ∃ fv, f.value? y = some fv ∧ fv.id = y ∧ fv.op ≠ .Phi) XS l →
      frS.regs.size = f.valueTab.size → frT = { frS with regs := frT.regs } →
      Av md env (Ctx.makeL tabs f) XS frS → Closed f XS → Agree pr ok f g XT XS frT frS →
      evalAllL md env (Ctx.makeL tabs f) frS l = .ok frS' →
      Av md env (Ctx.makeL tabs f) (fun a => XS a ∨ a ∈ l) frS' ∧
        Closed f (fun a => XS a ∨ a ∈ l) ∧ Agree pr ok f g XT (fun a => XS a ∨ a ∈ l) frT frS' ∧
        frS' = { frS with regs := frS'.regs } ∧ frS'.regs.size = frS.regs.size
  | [], XS, frS, frS', _, _, _, hAv, hcl, hag, h => by
    cases h
    have e : (fun a => XS a ∨ a ∈ ([] : List ID)) = XS := by funext a; simp
    rw [e]; exact ⟨hAv, hcl, hag, rfl, rfl⟩
  | y :: l, XS, frS, frS', ⟨⟨fv, hfv, hid, hph⟩, hnew, hargs, hr⟩, hs, hfr, hAv, hcl, hag, h => by
    have hcf : (Ctx.makeL tabs f).f = f := makeL_f tabs f
    rw [evalAllL_cons, stepVL_of (by rw [hcf]; exact hfv)] at h
    cases hev : evalValueL md env (Ctx.makeL tabs f) frS fv with
    | panic e m => rw [hev] at h; cases h
    | stuck msg => rw [hev] at h; cases h
    | ok w =>
    rw [hev] at h
    have hargs' : ∀ b ∈ fv.args, XS b := fun b hb =>
      hargs b (by rw [argsF_of hfv]; exact Array.mem_toList_iff.2 hb)
    have hylt : y < frS.regs.size := hs ▸ lt_of_value? hfv
    have hne : ∀ a, XS a → y ≠ a := fun a ha he => hnew (he ▸ ha)
    have hfr' : frS.set y w = { frS with regs := (frS.set y w).regs } := rfl
    have hAv' : Av md env (Ctx.makeL tabs f) (fun a => XS a ∨ a = y) (frS.set y w) := by
      intro a ha
      rcases ha with ha | rfl
      · obtain ⟨v, r, hv, hvid, hr, hre⟩ := hAv a ha
        refine ⟨v, r, hv, hvid, by rw [Frame.set_regs_ne (hne a ha)]; exact hr, fun hp => ?_⟩
        rw [← hre hp]
        refine (evalValueL_congr hfr' fun b hb => ?_).symm
        rw [Frame.set_regs_ne (hne b (hcl a v ha (by rw [hcf] at hv; exact hv) hp b hb))]
      · refine ⟨fv, w, by rw [hcf]; exact hfv, hid, Frame.set_regs_self hylt, fun _ => ?_⟩
        rw [← hev]
        refine (evalValueL_congr hfr' fun b hb => ?_).symm
        rw [Frame.set_regs_ne (hne b (hargs' b hb))]
    have hcl' : Closed f (fun a => XS a ∨ a = y) := by
      intro a v ha hv hp b hb
      rcases ha with ha | rfl
      · exact .inl (hcl a v ha hv hp b hb)
      · rw [hfv] at hv; cases hv; exact .inl (hargs' b hb)
    have hag' : Agree pr ok f g XT (fun a => XS a ∨ a = y) frT (frS.set y w) := by
      intro x a hx ha hrel
      rcases ha with ha | rfl
      · rw [Frame.set_regs_ne (hne a ha)]; exact hag x a hx ha hrel
      · obtain ⟨n, hn⟩ := hrel
        rw [Frame.set_regs_self hylt]
        exact agree_stepS H hfr hAvT hclT hAv hcl hag hfv hid hph hargs' hev n x hx hn
    obtain ⟨h1, h2, h3, h4, h5⟩ := phaseS H hAvT hclT hr (by simp [Frame.set, hs])
      (by rw [hfr]; rfl) hAv' hcl' hag' h
    rw [pred_cons] at h1 h2 h3
    exact ⟨h1, h2, h3, by rw [h4]; rfl, by rw [h5]; simp [Frame.set]⟩

/-! ## The target evaluates a value -/

/-- A value `x` the target evaluates: it is `.ok`, and every related source value available
holds its result. It is total, or related to a source value available (identity in the
certificate, or `pair`'s pair store for its second store). -/
theorem stepT (H : Hyp pr ok f g tabs md) {XT XS : ID → Prop} {frT GS : Frame}
    (hfr : frT = { GS with regs := frT.regs }) (hAvT : Av md env (Ctx.makeL tabs g) XT frT)
    (hclT : Closed g XT) (hAvS : Av md env (Ctx.makeL tabs f) XS GS) (hclS : Closed f XS)
    (hag : Agree pr ok f g XT XS frT GS) {x : ID} {gv : Value} (hgv : g.value? x = some gv)
    (hid : gv.id = x) (hph : gv.op ≠ .Phi) (hargs : ∀ a ∈ gv.args, XT a)
    (hok : totalOp gv.op = true ∨ ∃ y, XS y ∧ Rel pr ok f g x y) :
    ∃ r, evalValueL md env (Ctx.makeL tabs g) frT gv = .ok r ∧
      ∀ y, XS y → Rel pr ok f g x y → GS.regs[y]? = some (some r) := by
  have hcf : (Ctx.makeL tabs f).f = f := makeL_f tabs f
  have hdefS : ∀ y fv, XS y → f.value? y = some fv → fv.op ≠ .Phi →
      ∀ b ∈ fv.args, ∃ z, GS.regs[b]? = some (some z) := fun y fv hy hfv hp b hb => by
    obtain ⟨-, z, -, -, hz, -⟩ := hAvS b (hclS y fv hy hfv hp b hb)
    exact ⟨z, hz⟩
  have base : ∀ y, XS y → ((x = y ∧ okAt ok x = true) ∨
      (∃ gv' fv, g.value? x = some gv' ∧ f.value? y = some fv ∧ cloneB ok f g gv' fv = true)) →
      ∃ r', GS.regs[y]? = some (some r') ∧ evalValueL md env (Ctx.makeL tabs g) frT gv = .ok r' := by
    intro y hy hc
    obtain ⟨fv', r', hfv', hfid, hr', hre'⟩ := hAvS y hy
    rw [hcf] at hfv'
    rcases hc with ⟨rfl, hok⟩ | ⟨gv', fv, hgv', hfv, hc⟩
    · obtain ⟨gv', fv, hgv', hfv, hop, hty, hsz, hrel, -, hrest⟩ :=
        okLocal_spec (okLocal_of H.cert hok)
      rw [hgv] at hgv'; cases hgv'
      have e : fv = fv' := Option.some.inj (hfv.symm.trans hfv'); subst e
      obtain ⟨haux, hai, hsx⟩ := hrest hph
      have hfph : fv.op ≠ .Phi := hop ▸ hph
      refine ⟨r', hr', ?_⟩
      rw [← hre' hfph]
      exact evalValueL_ident hfr hop haux hai (hid.trans hfid.symm) hsz
        (argsAgree hag hsz hrel hargs (hclS x fv hy hfv hfph) (hdefS x fv hy hfv hfph))
        (by rw [hid, hfid]; exact tys_eq H hgv hfv hty) hsx H.own
    · rw [hgv] at hgv'; cases hgv'
      have e : fv = fv' := Option.some.inj (hfv.symm.trans hfv'); subst e
      obtain ⟨ht, hop, hty, haux, hai, hargs', hok, hsx⟩ := cloneB_spec hc
      have hfph : fv.op ≠ .Phi := hop ▸ totalOp_ne_phi ht
      refine ⟨r', hr', ?_⟩
      rw [← hre' hfph]
      exact evalValueL_clone H.nf hfr (hop ▸ ht) hop haux hai (by rw [hargs'])
        (argsAgree hag (by rw [hargs']) (clone_rel hargs' hok) hargs (hclS y fv hy hfv hfph)
          (hdefS y fv hy hfv hfph))
        (by rw [hid, hfid]; exact tys_eq H hgv hfv hty) hsx H.own
  have pairY : ∀ y fv m, XS y → f.value? y = some fv → pr = true → gv.type = fv.type →
      (SelRel pr ok f g m gv fv ∨ StRel pr ok f g m gv fv ∨ RevRel pr ok f g m gv fv) →
      ∃ w, GS.regs[y]? = some (some w) ∧ evalValueL md env (Ctx.makeL tabs g) frT gv = .ok w := by
    intro y fv m hy hfv hpr hty hs
    obtain ⟨fv', w, hfv', hfid, hw, hwe⟩ := hAvS y hy
    rw [hcf, hfv] at hfv'; cases hfv'
    have hfph := (pairRel_ne_phi hs).2
    exact ⟨w, hw, pair_eval H hAvT hclT hAvS hclS hag hgv hid hfv hfid hpr hty hs hargs
      (hclS y fv hy hfv hfph) (hwe hfph)⟩
  have hex : ∃ r, evalValueL md env (Ctx.makeL tabs g) frT gv = .ok r := by
    by_cases ht : totalOp gv.op = true
    · unfold evalValueL
      obtain ⟨argv, hm⟩ := mapM_ofOption_ok (m := fun a => s!"v{gv.id}: argument v{a} has no value")
        (r := fun a => (frT.regs[a]?).join) (l := gv.args.toList) fun a ha => by
          obtain ⟨-, z, -, -, hz, -⟩ := hAvT a (hargs a (Array.mem_toList_iff.1 ha))
          exact ⟨z, by simp [hz]⟩
      rw [hm, H.nf]
      obtain ⟨r, h1, -⟩ := totalOp_ok (env := env) (ctx := Ctx.makeL tabs g) (fr := frT) (argv := argv)
        (ty := (Ctx.makeL tabs g).tys[gv.id]?.getD .other) ht
      change ∃ r', (evalOpL false env _ frT gv argv _).bind _ = _
      rw [h1]
      exact ⟨_, rfl⟩
    · rcases hok with ht' | ⟨y, hy, n, hn⟩
      · exact absurd ht' ht
      · rcases relB_cases hn with h | ⟨gv', fv, hgv', -, hc⟩ | ⟨gv', fv, z, m, hgv', -, hc, -⟩ |
          ⟨gv', fv, m, hgv', hfv, hpr, hty, -, hs⟩
        · obtain ⟨r', -, h⟩ := base y hy (.inl h)
          exact ⟨r', h⟩
        · rw [hgv] at hgv'; cases hgv'
          exact absurd (cloneB_spec hc).1 ht
        · rw [hgv] at hgv'; cases hgv'
          exact absurd (by rw [hc]; rfl) ht
        · rw [hgv] at hgv'; cases hgv'
          obtain ⟨w, -, h⟩ := pairY y fv m hy hfv hpr hty hs
          exact ⟨w, h⟩
  obtain ⟨r, hr⟩ := hex
  refine ⟨r, hr, fun y hy ⟨n, hn⟩ => ?_⟩
  rcases relB_cases hn with h | h | ⟨gv', fv, z, m, hgv', hfv, hcp, hfph, hty, hz, -, hrz⟩ |
    ⟨gv', fv, m, hgv', hfv, hpr, hty, -, hs⟩
  · obtain ⟨r', h1, h2⟩ := base y hy (.inl h)
    rw [hr] at h2; cases h2; exact h1
  · obtain ⟨r', h1, h2⟩ := base y hy (.inr h)
    rw [hr] at h2; cases h2; exact h1
  · rw [hgv] at hgv'; cases hgv'
    have hzm : z ∈ gv.args := by rw [← Array.mem_toList_iff, hz]; exact List.mem_cons_self
    obtain ⟨fv', r', hfv', hfid, hr', hre'⟩ := hAvS y hy
    rw [hcf, hfv] at hfv'; cases hfv'
    have hzr := (hag z y (hargs z hzm) hy ⟨m, hrz⟩).trans hr'
    rw [evalValueL_copy hcp hz hzr] at hr
    cases hr
    rw [hr', hid, tys_eq (tabs := tabs) H hgv hfv hty, ← hfid, evalValueL_retype (hre' hfph)]
  · rw [hgv] at hgv'; cases hgv'
    obtain ⟨w, hw, h⟩ := pairY y fv m hy hfv hpr hty hs
    rw [hr] at h; cases h; exact hw

/-- **The target evaluates `l`**, the source's frame fixed: it does not panic or get stuck. -/
theorem phaseT (H : Hyp pr ok f g tabs md) {XS : ID → Prop} {GS : Frame}
    (hAvS : Av md env (Ctx.makeL tabs f) XS GS) (hclS : Closed f XS) :
    ∀ {l : List ID} {XT : ID → Prop} {frT : Frame},
      Ready (argsF g) (fun x => ∃ gv, g.value? x = some gv ∧ gv.id = x ∧ gv.op ≠ .Phi ∧
        (totalOp gv.op = true ∨ ∃ y, XS y ∧ Rel pr ok f g x y)) XT l →
      frT.regs.size = g.valueTab.size → frT = { GS with regs := frT.regs } →
      Av md env (Ctx.makeL tabs g) XT frT → Closed g XT → Agree pr ok f g XT XS frT GS →
      ∃ frT', evalAllL md env (Ctx.makeL tabs g) frT l = .ok frT' ∧
        Av md env (Ctx.makeL tabs g) (fun a => XT a ∨ a ∈ l) frT' ∧
        Closed g (fun a => XT a ∨ a ∈ l) ∧ Agree pr ok f g (fun a => XT a ∨ a ∈ l) XS frT' GS ∧
        frT' = { frT with regs := frT'.regs } ∧ frT'.regs.size = frT.regs.size
  | [], XT, frT, _, _, _, hAv, hcl, hag => by
    have e : (fun a => XT a ∨ a ∈ ([] : List ID)) = XT := by funext a; simp
    rw [e]; exact ⟨frT, rfl, hAv, hcl, hag, rfl, rfl⟩
  | x :: l, XT, frT, ⟨⟨gv, hgv, hid, hph, hok⟩, hnew, hargs, hr⟩, hs, hfr, hAv, hcl, hag => by
    have hcg : (Ctx.makeL tabs g).f = g := makeL_f tabs g
    have hargs' : ∀ a ∈ gv.args, XT a := fun a ha =>
      hargs a (by rw [argsF_of hgv]; exact Array.mem_toList_iff.2 ha)
    obtain ⟨w, hev, hagx⟩ := stepT H hfr hAv hcl hAvS hclS hag hgv hid hph hargs' hok
    have hxlt : x < frT.regs.size := hs ▸ lt_of_value? hgv
    have hne : ∀ a, XT a → x ≠ a := fun a ha he => hnew (he ▸ ha)
    have hfr' : frT.set x w = { frT with regs := (frT.set x w).regs } := rfl
    have hAv' : Av md env (Ctx.makeL tabs g) (fun a => XT a ∨ a = x) (frT.set x w) := by
      intro a ha
      rcases ha with ha | rfl
      · obtain ⟨v, r, hv, hvid, hr, hre⟩ := hAv a ha
        refine ⟨v, r, hv, hvid, by rw [Frame.set_regs_ne (hne a ha)]; exact hr, fun hp => ?_⟩
        rw [← hre hp]
        refine (evalValueL_congr hfr' fun b hb => ?_).symm
        rw [Frame.set_regs_ne (hne b (hcl a v ha (by rw [hcg] at hv; exact hv) hp b hb))]
      · refine ⟨gv, w, by rw [hcg]; exact hgv, hid, Frame.set_regs_self hxlt, fun _ => ?_⟩
        rw [← hev]
        refine (evalValueL_congr hfr' fun b hb => ?_).symm
        rw [Frame.set_regs_ne (hne b (hargs' b hb))]
    have hcl' : Closed g (fun a => XT a ∨ a = x) := by
      intro a v ha hv hp b hb
      rcases ha with ha | rfl
      · exact .inl (hcl a v ha hv hp b hb)
      · rw [hgv] at hv; cases hv; exact .inl (hargs' b hb)
    have hag' : Agree pr ok f g (fun a => XT a ∨ a = x) XS (frT.set x w) GS := by
      intro a y ha hy hrel
      rcases ha with ha | rfl
      · rw [Frame.set_regs_ne (hne a ha)]; exact hag a y ha hy hrel
      · rw [Frame.set_regs_self hxlt, hagx y hy hrel]
    obtain ⟨frT', h0, h1, h2, h3, h4, h5⟩ := phaseT H hAvS hclS hr (by simp [Frame.set, hs])
      (by rw [hfr]; rfl) hAv' hcl' hag'
    rw [pred_cons] at h1 h2 h3
    refine ⟨frT', ?_, h1, h2, h3, by rw [h4]; rfl, by rw [h5]; simp [Frame.set]⟩
    rw [evalAllL_cons, stepVL_of (by rw [hcg]; exact hgv), hev]
    exact h0

end GoFV.Proof.MoveL

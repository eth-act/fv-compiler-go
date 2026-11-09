import GoFV.Proof.Pass.CopyFragL
import GoFV.Proof.AvailL

variable [GoFV.SSA.Sem.Addrs]

/-!
# copyelim on `runL`: setup

`SetupL md tabs f g`: Phase 1's `Setup` (both functions checked, `CopyRel`, `EmptyFrag`), the
two functions lowered alike (so `runL` runs both in one mode `md`, `⟨f.lowered, false⟩`) and the
fragment `CopyLFrag`. The value facts of `GoFV.Proof.Pass.CopyElimSim` for `evalValueL`: a copy
yields its argument at its shape (`evalValueL_copy`), an `EmptyOK` value `.empty`
(`evalValueL_emptyOK`), a copy of `g` keeps a register of its argument's shape at its own
(`SetupL.copyShape`: `CopyLFrag.shape` in lowered code, `CopyRel.copyShape` otherwise), and an
argument and its `ArgRel`-related target value hold the same register (`SetupL.argEq`).
-/

namespace GoFV.Proof.CopyElim

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt Dom

/-! ## Values -/

theorem evalValueL_copy {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {w : ID}
    {y : Val} (hop : v.op = .Copy) (ha : v.args = #[w]) (hw : fr.regs[w]? = some (some y)) :
    evalValueL md env ctx fr v = .ok (md.retype (ctx.tys[v.id]?.getD .other) y) := by
  unfold evalValueL
  rw [ha]
  simp only [List.mapM_cons, List.mapM_nil, hw, Option.join, bind, Res.bind, Res.ofOption, pure]
  rw [show (some (some y)).bind id = some y from rfl]
  simp only [evalOpL_generic _ _ _ _ _ _ (show v.op.generic = true by rw [hop]; rfl),
    evalOp_copy hop]
  rfl

theorem evalValueL_copy_inv {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {w : ID} {y : Val} (hop : v.op = .Copy) (ha : v.args = #[w])
    (h : evalValueL md env ctx fr v = .ok y) :
    ∃ y0, fr.regs[w]? = some (some y0) ∧ y = md.retype (ctx.tys[v.id]?.getD .other) y0 := by
  cases hw : fr.regs[w]? with
  | some o =>
    cases o with
    | some y0 =>
      rw [evalValueL_copy hop ha hw] at h
      cases h; exact ⟨y0, rfl, rfl⟩
    | none =>
      unfold evalValueL at h
      rw [ha] at h
      simp only [List.mapM_cons, List.mapM_nil, hw, Option.join, bind, Res.bind,
        Res.ofOption] at h
      cases h
  | none =>
    unfold evalValueL at h
    rw [ha] at h
    simp only [List.mapM_cons, List.mapM_nil, hw, Option.join, bind, Res.bind,
      Res.ofOption] at h
    cases h

/-- A generic value whose shape `md` reads as Phase 1 does evaluates as in Phase 1. -/
theorem evalValueL_eq_evalValue {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    (hg : v.op.generic = true)
    (hty : ∀ r, md.retype (ctx.tys[v.id]?.getD .other) r = r.retype (ctx.tys[v.id]?.getD .other)) :
    evalValueL md env ctx fr v = evalValue env ctx fr v := by
  simp only [evalValueL, evalValue, evalOpL_generic _ _ _ _ _ _ hg, hty]

theorem LMode.retype_empty (md : LMode) (r : Val) : md.retype .empty r = r.retype .empty := by
  unfold LMode.retype Val.retypeL
  split
  · cases r <;> rfl
  · rfl

/-- An `Empty` without arguments evaluates to `.empty` at shape `empty`. -/
theorem evalValueL_empty {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {gv : Value}
    (hop : gv.op = .Empty) (hargs : gv.args = #[]) (hty : ctx.tys[gv.id]? = some .empty) :
    evalValueL md env ctx fr gv = .ok .empty := by
  rw [evalValueL_eq_evalValue (by rw [hop]; rfl) (by rw [hty]; exact LMode.retype_empty md)]
  exact evalValue_empty hop hargs hty

/-- An `EmptyOK` value evaluates to `.empty` wherever it is defined. -/
theorem evalValueL_emptyOK {md : LMode} {tabs : Tables} {env : Env} {ctx : Ctx} {fr : Frame}
    {fv : Value} (he : EmptyOK tabs fv) (hty : ctx.tys[fv.id]? = some .empty)
    (hdef : ∀ msg, evalValueL md env ctx fr fv ≠ .stuck msg) :
    evalValueL md env ctx fr fv = .ok .empty := by
  have hg : fv.op.generic = true := by rcases he.2.2 with h | ⟨h, -⟩ <;> rw [h] <;> rfl
  have heq := evalValueL_eq_evalValue (md := md) (env := env) (fr := fr) hg
    (by rw [hty]; exact LMode.retype_empty md)
  rw [heq] at hdef ⊢
  exact evalValue_emptyOK he hty hdef

/-- A zero-size shape is zero-size in lowered code too. -/
theorem tyOfL_of_empty {tabs : Tables} :
    ∀ (n : Nat) (t : TypeRef), tyOf tabs n t = .empty → tyOfL tabs n t = .empty
  | 0, _, h => by simp [tyOf] at h
  | n + 1, t, h => by
    unfold tyOfL
    have h' := h
    unfold tyOf at h'
    cases hd : tabs.type? t with
    | none => rw [hd] at h'; cases h'
    | some d =>
      simp only [hd] at h' ⊢
      cases hk : d.kind <;> simp only [hk] at h' ⊢ <;>
        first | exact h | (split at h' <;> cases h')

theorem shapesL_of_empty {tabs : Tables} {t : TypeRef} (low : Bool) (h : tabs.ty t = .empty) :
    (shapesL low tabs)[t]?.getD .other = .empty := by
  unfold shapesL
  split
  · unfold typeShapesL
    rw [Array.getElem?_map]
    by_cases ht : t < tabs.types.size
    · simp only [List.getElem?_toArray, List.getElem?_range ht, Option.map_some,
        Option.getD_some]
      exact tyOfL_of_empty 32 t h
    · exfalso
      rw [← typeShapes_getD] at h
      unfold typeShapes at h
      rw [Array.getElem?_map] at h
      simp [ht] at h
  · rw [typeShapes_getD]; exact h

theorem prio_panickingL {op : Op} (h : PanickingL false op) : prio op ≠ 0 := by
  rcases h with h | h | ⟨h, -⟩
  · rw [prio_call h]; decide
  · simp [prio, h]
  · cases h

/-! ## Setup -/

/-- Everything copyelim's simulation on `runL` uses about its input `f` and output `g`, run in
mode `md`. -/
structure SetupL (md : LMode) (tabs : Tables) (f g : Func) : Prop where
  base : Setup tabs f g
  low : g.lowered = f.lowered
  mdLow : md.low = f.lowered
  mdFault : md.faulting = false
  frag : CopyLFrag tabs f g

variable {md : LMode} {tabs : Tables} {f g : Func}

namespace SetupL

variable (S : SetupL md tabs f g)
include S

/-- The target's lowered shapes agree with the source's on values of tree blocks. -/
theorem tys {b : ID} (hb : Tree f b) {fb : Block} (hfb : f.block? b = some fb) {x : ID}
    (hx : x ∈ fb.values) : (Ctx.makeL tabs g).tys[x]? = (Ctx.makeL tabs f).tys[x]? := by
  obtain ⟨fv, gv, hfv, hgv, -, -, -, hty, -⟩ := S.base.value hb hfb hx
  rw [tysL_of_value hfv, tysL_of_value hgv, hty, S.low]

/-- **A copy of `g` keeps a register of its argument's shape.** -/
theorem copyShape {b : ID} (hb : Tree f b) {fb : Block} (hfb : f.block? b = some fb) {x : ID}
    (hx : x ∈ fb.values) {gv : Value} {w : ID} (hgv : g.value? x = some gv) (hop : gv.op = .Copy)
    (hargs : gv.args = #[w]) {y : Val}
    (hy : md.retype ((Ctx.makeL tabs g).tys[w]?.getD .other) y = y) :
    md.retype ((Ctx.makeL tabs g).tys[x]?.getD .other) y = y := by
  cases hl : f.lowered with
  | true =>
    rw [← S.frag.shape (S.low.trans hl) b hb fb hfb x hx gv w hgv hop hargs]
    exact hy
  | false =>
    have hmk : Ctx.makeL tabs g = Ctx.make tabs g := Ctx.makeL_of_generic (S.low.trans hl)
    have hmd : ∀ t r, md.retype t r = r.retype t := fun t r => by
      simp only [LMode.retype, S.mdLow, hl, Bool.false_eq_true, ite_false]
    obtain ⟨wv, hwv, hsh⟩ := S.base.rel.copyShape b hb.1 hb.2 fb hfb x hx gv w hgv hop hargs
    rw [hmk, hmd] at hy ⊢
    rw [tys_of_value hwv] at hy
    rw [tys_of_value hgv]
    simp only [Option.getD_some] at hy ⊢
    exact hsh.apply hy

/-- In a frame satisfying lemma (D) of `g` at `p`, a value used at `p` and its `ArgRel`-related
target value hold the same register. -/
theorem argEq {env : Env} {fr : Frame} {A : ID → Prop} {q a w : ID}
    (hD : DInvL md env (Ctx.makeL tabs g) A fr) (hAa : A (blockOf f a))
    (hT : TypedL md (Ctx.makeL tabs g) fr) (hl : Listed f a) (ha : Anc (make f) (blockOf f a) q)
    (hr : ArgRel g a w) : ∃ y, fr.regs[a]? = some (some y) ∧ fr.regs[w]? = some (some y) := by
  obtain ⟨b, fb, hb, hfb, hx, hbo, hbog⟩ := S.base.used hl ha
  obtain ⟨fv, gv, hfv, hgv, -, -, hgb, -, -, -⟩ := S.base.value hb hfb hx
  obtain ⟨hpl, -⟩ := S.base.placedG hb hfb hx hgv
  obtain ⟨y, hy, hev⟩ := hD a gv (by rw [makeL_f]; exact hpl) (by rw [hgb, ← hbo]; exact hAa)
  rcases hr with rfl | ⟨u, hu, hop, hargs⟩
  · exact ⟨y, hy, hy⟩
  · rw [hgv] at hu; cases hu
    have hgid : gv.id = a := S.base.gid hb hfb hx hgv
    obtain ⟨y0, hy0, rfl⟩ := evalValueL_copy_inv hop hargs (hev (by rw [hop]; decide))
    refine ⟨y0, ?_, hy0⟩
    rw [hy, hgid, S.copyShape hb hfb hx hgv hop hargs (hT w y0 hy0)]

end SetupL

end GoFV.Proof.CopyElim

import GoFV.Opt.CSE
import GoFV.Proof.WF
import GoFV.Proof.DomCert
import GoFV.Proof.Pass.CopyElimSim

variable [GoFV.SSA.Sem.Addrs]

/-!
# cse's output relation

`CRel tabs f g rw`, the declarative form of the strict checker `GoFV.Opt.CSE.crel tabs true`
(`crel_sound`): `g` has `f`'s control-flow graph, block kinds and values; every value keeps its
ID, op, aux, auxint, type and block, its arguments become their representatives (`rep rw`), the
first two of a commutative op possibly swapped; each control is kept or becomes its
representative; every substitution `x ↦ r` is sound (`Subst`); and every block of `g` with a
source schedule has one listing the roots (`rootNode f`) in the source's order.
-/

namespace GoFV.Proof.CSE

open GoFV.SSA GoFV.Opt GoFV.Opt.CSE GoFV.Proof.CopyElim

/-- `g`'s arguments `ga` are `f`'s `fa` through `rep rw`, the first two possibly swapped. -/
def ArgsRel (rw : Array (Option ID)) (op : Op) (fa ga : Array ID) : Prop :=
  ga = fa.map (rep rw) ∨ (op.commutative = true ∧ 2 ≤ fa.size ∧
    ga = (fa.swapIfInBounds 0 1).map (rep rw))

/-- The congruence of a replaced value `fx` (target `gx`) and its representative `fr` (`gr`). -/
def Congr (tabs : Tables) (rw : Array (Option ID)) (f : Func) (fx fr gx gr : Value) : Prop :=
  fr.op = fx.op ∧ fr.aux = fx.aux ∧ fr.auxInt = fx.auxInt ∧ tabs.ty fr.type = tabs.ty fx.type ∧
    (gx.args = gr.args ∨ gx.args.size = gr.args.size ∧ gx.args[0]? = gr.args[0]? ∧
      ((fx.op = .LocalAddr ∧ fx.aux.isSome) ∨ fx.op = .NilCheck ∨
        (fx.op = .Load ∧ loadOK tabs rw f fx fr = true)))

/-- A sound substitution `x ↦ r`. -/
def Subst (tabs : Tables) (rw : Array (Option ID)) (f g : Func) (x r : ID) : Prop :=
  rw.getD r none = none ∧ ∃ fx fr gx gr, f.value? x = some fx ∧ f.value? r = some fr ∧
    g.value? x = some gx ∧ g.value? r = some gr ∧ Congr tabs rw f fx fr gx gr ∧
    (Sem.isRoot fx.op = false ∨ fx.op = .NilCheck) ∧ (fx.op = .Phi → fr.block = fx.block) ∧
    (DomCert.make f).anc fr.block fx.block = true ∧ fr.block ∈ f.blocks ∧ ∃ blk, f.block? fr.block = some blk ∧ r ∈ blk.values

/-- The declarative output relation. -/
structure CRel (tabs : Tables) (f g : Func) (rw : Array (Option ID)) : Prop where
  cfg : DomCert.cfgView g = DomCert.cfgView f
  ownAux : g.ownAux = f.ownAux
  vsize : g.valueTab.size = f.valueTab.size
  block : ∀ bid ∈ f.blocks, ∀ fb, f.block? bid = some fb → ∃ gb, g.block? bid = some gb ∧
    gb.kind = fb.kind ∧ gb.values = fb.values ∧ gb.controls.size = fb.controls.size ∧
    ∀ (k : Nat) (c : ID), fb.controls[k]? = some c →
      gb.controls[k]? = some c ∨ gb.controls[k]? = some (rep rw c)
  value : ∀ x fv, f.value? x = some fv → ∃ gv, g.value? x = some gv ∧ gv.id = fv.id ∧
    gv.op = fv.op ∧ gv.aux = fv.aux ∧ gv.auxInt = fv.auxInt ∧ gv.type = fv.type ∧
    gv.block = fv.block ∧ ArgsRel rw fv.op fv.args gv.args
  subst : ∀ x r, rw.getD x none = some r → Subst tabs rw f g x r
  sched : ∀ bid ∈ f.blocks, ∀ fb gb, f.block? bid = some fb → g.block? bid = some gb →
    ∀ oS, Sem.schedule f fb = some oS → ∃ oT, Sem.schedule g gb = some oT ∧
      oT.toList.filter (rootNode f) = oS.toList.filter (rootNode f)

/-! ## Soundness of the checker -/

mutual
theorem tyEq_sound : ∀ {a b : Sem.Ty}, tyEq a b = true → a = b
  | .int w, .int w', h => by simp only [tyEq, beq_iff_eq] at h; rw [h]
  | .bool, .bool, _ | .mem, .mem, _ | .other, .other, _ | .empty, .empty, _ => rfl
  | .tuple ts, .tuple ts', h => by
    simp only [tyEq] at h; rw [tysEq_sound h]
  | .ptr e, .ptr e', h => by simp only [tyEq, beq_iff_eq] at h; rw [h]
  | .agg fs n, .agg fs' n', h => by
    simp only [tyEq, Bool.and_eq_true, beq_iff_eq] at h; rw [fieldsEq_sound h.1, h.2]
  | .blob n, .blob n', h => by simp only [tyEq, beq_iff_eq] at h; rw [h]
  | .opaque n, .opaque n', h => by simp only [tyEq, beq_iff_eq] at h; rw [h]
  | .str, .str, _ => rfl
  | .slice e, .slice e', h => by simp only [tyEq, beq_iff_eq] at h; rw [h]
  | .str, .int _, h | .str, .bool, h | .str, .mem, h | .str, .tuple _, h | .str, .other, h
  | .str, .ptr _, h | .str, .agg _ _, h | .str, .blob _, h | .str, .empty, h
  | .str, .opaque _, h | .str, .slice _, h
  | .slice _, .int _, h | .slice _, .bool, h | .slice _, .mem, h | .slice _, .tuple _, h
  | .slice _, .other, h | .slice _, .ptr _, h | .slice _, .agg _ _, h | .slice _, .blob _, h
  | .slice _, .empty, h | .slice _, .opaque _, h | .slice _, .str, h
  | .int _, .str, h | .bool, .str, h | .mem, .str, h | .tuple _, .str, h | .other, .str, h
  | .ptr _, .str, h | .agg _ _, .str, h | .blob _, .str, h | .empty, .str, h
  | .opaque _, .str, h
  | .int _, .slice _, h | .bool, .slice _, h | .mem, .slice _, h | .tuple _, .slice _, h
  | .other, .slice _, h | .ptr _, .slice _, h | .agg _ _, .slice _, h | .blob _, .slice _, h
  | .empty, .slice _, h | .opaque _, .slice _, h => by simp [tyEq] at h
  | .int _, .bool, h | .int _, .mem, h | .int _, .tuple _, h | .int _, .other, h
  | .int _, .ptr _, h | .int _, .agg _ _, h | .int _, .blob _, h | .int _, .empty, h
  | .int _, .opaque _, h
  | .bool, .int _, h | .bool, .mem, h | .bool, .tuple _, h | .bool, .other, h
  | .bool, .ptr _, h | .bool, .agg _ _, h | .bool, .blob _, h | .bool, .empty, h
  | .bool, .opaque _, h
  | .mem, .int _, h | .mem, .bool, h | .mem, .tuple _, h | .mem, .other, h
  | .mem, .ptr _, h | .mem, .agg _ _, h | .mem, .blob _, h | .mem, .empty, h
  | .mem, .opaque _, h
  | .tuple _, .int _, h | .tuple _, .bool, h | .tuple _, .mem, h | .tuple _, .other, h
  | .tuple _, .ptr _, h | .tuple _, .agg _ _, h | .tuple _, .blob _, h | .tuple _, .empty, h
  | .tuple _, .opaque _, h
  | .other, .int _, h | .other, .bool, h | .other, .mem, h | .other, .tuple _, h
  | .other, .ptr _, h | .other, .agg _ _, h | .other, .blob _, h | .other, .empty, h
  | .other, .opaque _, h
  | .ptr _, .int _, h | .ptr _, .bool, h | .ptr _, .mem, h | .ptr _, .tuple _, h
  | .ptr _, .other, h | .ptr _, .agg _ _, h | .ptr _, .blob _, h | .ptr _, .empty, h
  | .ptr _, .opaque _, h
  | .agg _ _, .int _, h | .agg _ _, .bool, h | .agg _ _, .mem, h | .agg _ _, .tuple _, h
  | .agg _ _, .other, h | .agg _ _, .ptr _, h | .agg _ _, .blob _, h | .agg _ _, .empty, h
  | .agg _ _, .opaque _, h
  | .blob _, .int _, h | .blob _, .bool, h | .blob _, .mem, h | .blob _, .tuple _, h
  | .blob _, .other, h | .blob _, .ptr _, h | .blob _, .agg _ _, h | .blob _, .empty, h
  | .blob _, .opaque _, h
  | .empty, .int _, h | .empty, .bool, h | .empty, .mem, h | .empty, .tuple _, h
  | .empty, .other, h | .empty, .ptr _, h | .empty, .agg _ _, h | .empty, .blob _, h
  | .empty, .opaque _, h
  | .opaque _, .int _, h | .opaque _, .bool, h | .opaque _, .mem, h | .opaque _, .tuple _, h
  | .opaque _, .other, h | .opaque _, .ptr _, h | .opaque _, .agg _ _, h
  | .opaque _, .blob _, h | .opaque _, .empty, h => by simp [tyEq] at h

theorem tysEq_sound : ∀ {a b : List Sem.Ty}, tysEq a b = true → a = b
  | [], [], _ => rfl
  | t :: ts, t' :: ts', h => by
    simp only [tysEq, Bool.and_eq_true] at h
    rw [tyEq_sound h.1, tysEq_sound h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [tysEq] at h

theorem fieldsEq_sound : ∀ {a b : List (Nat × Sem.Ty)}, fieldsEq a b = true → a = b
  | [], [], _ => rfl
  | (o, t) :: fs, (o', t') :: fs', h => by
    simp only [fieldsEq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1.1, tyEq_sound h.1.2, fieldsEq_sound h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [fieldsEq] at h
end

theorem lt_of_value? {f : Func} {x : ID} {v : Value} (h : f.value? x = some v) :
    x < f.valueTab.size := by
  unfold Func.value? at h
  rcases Nat.lt_or_ge x f.valueTab.size with hx | hx
  · exact hx
  · rw [Array.getElem?_eq_none hx] at h; cases h

theorem lt_of_getD_some {rw : Array (Option ID)} {x r : ID} (h : rw.getD x none = some r) :
    x < rw.size := by
  rcases Nat.lt_or_ge x rw.size with hx | hx
  · exact hx
  · simp [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hx] at h

theorem congr_sound {tabs : Tables} {rw : Array (Option ID)} {f : Func} {fx fr gx gr : Value}
    (h : GoFV.Opt.CSE.congr tabs true rw f fx fr gx gr = true) : Congr tabs rw f fx fr gx gr := by
  unfold GoFV.Opt.CSE.congr at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.true_and,
    Bool.not_true, Bool.false_or] at h
  obtain ⟨⟨⟨⟨hop, hax⟩, hai⟩, hty⟩, hargs⟩ := h
  refine ⟨hop, hax, hai, ?_, ?_⟩
  · rcases hty with h | h
    · rw [h]
    · exact tyEq_sound h
  · rcases hargs with h | ⟨⟨h1, h2⟩, h3⟩
    · exact .inl h
    · refine .inr ⟨h1, h2, ?_⟩
      rcases h3 with (⟨h4, h5⟩ | h4) | ⟨h4, h5⟩
      · exact .inl ⟨h4, h5⟩
      · exact .inr (.inl h4)
      · exact .inr (.inr ⟨h4, h5⟩)

/-- **The strict checker is sound.** -/
theorem crel_sound {tabs : Tables} {f g : Func} {rw : Array (Option ID)}
    (h : crel tabs true f g rw = true) : CRel tabs f g rw := by
  unfold crel at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨hcfg, hown⟩, hsz⟩, hblk⟩, hval⟩, hsub⟩, hsch⟩ := h
  refine ⟨hcfg, hown, hsz, fun bid hb fb hfb => ?_, fun x fv hfv => ?_, fun x r hr => ?_,
    fun bid hb fb gb hfb hgb oS hoS => ?_⟩
  · have := hblk bid hb
    unfold blockOK at this
    rw [hfb] at this
    cases hgb : g.block? bid with
    | none => rw [hgb] at this; cases this
    | some gb =>
      rw [hgb] at this
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
        Bool.or_eq_true] at this
      obtain ⟨⟨⟨hk, hv⟩, hcs⟩, hc⟩ := this
      refine ⟨gb, rfl, hk, hv, hcs, fun k c hkc => ?_⟩
      have hk' : k < fb.controls.size := (Array.getElem?_eq_some_iff.1 hkc).1
      have hc' : fb.controls[k]! = c := by
        rw [getElem!_pos fb.controls k hk']; exact (Array.getElem?_eq_some_iff.1 hkc).2
      have hkg : k < gb.controls.size := hcs ▸ hk'
      rw [Array.getElem?_eq_getElem hkg]
      rcases hc k hk' with h1 | h1
      · left; rw [← getElem!_pos gb.controls k hkg, h1, hc']
      · right; rw [← getElem!_pos gb.controls k hkg, h1, hc']
  · have := hval x (lt_of_value? hfv)
    unfold GoFV.Opt.CSE.valueOK at this
    rw [hfv] at this
    cases hgv : g.value? x with
    | none => rw [hgv] at this; cases this
    | some gv =>
      rw [hgv] at this
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      obtain ⟨⟨⟨⟨⟨⟨hid, hop⟩, hax⟩, hai⟩, hty⟩, hbl⟩, hargs⟩ := this
      refine ⟨gv, rfl, hid, hop, hax, hai, hty, hbl, ?_⟩
      unfold argsOK swappable at hargs
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hargs
      rcases hargs with h1 | ⟨⟨h1, h2⟩, h3⟩
      · exact .inl h1
      · exact .inr ⟨h1, h2, h3⟩
  · have := hsub x (lt_of_getD_some hr)
    unfold substOK at this
    rw [hr] at this
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at this
    obtain ⟨hrr, hrest⟩ := this
    refine ⟨hrr, ?_⟩
    cases hfx : f.value? x with
    | none => rw [hfx] at hrest; cases hrest
    | some fx =>
    cases hfr : f.value? r with
    | none => rw [hfx, hfr] at hrest; cases hrest
    | some fr =>
    cases hgx : g.value? x with
    | none => rw [hfx, hfr, hgx] at hrest; cases hrest
    | some gx =>
    cases hgr : g.value? r with
    | none => rw [hfx, hfr, hgx, hgr] at hrest; cases hrest
    | some gr =>
    rw [hfx, hfr, hgx, hgr] at hrest
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq,
      bne_iff_ne, ne_eq] at hrest
    obtain ⟨⟨⟨⟨⟨hc, hroot⟩, hphi⟩, hanc⟩, hmem⟩, hlist⟩ := hrest
    refine ⟨fx, fr, gx, gr, rfl, rfl, rfl, rfl, congr_sound hc, hroot, fun hp => ?_,
      hanc, by simpa using hmem, ?_⟩
    · rcases hphi with h1 | h1
      · exact absurd hp h1
      · exact h1
    · cases hb : f.block? fr.block with
      | none => rw [hb] at hlist; cases hlist
      | some blk =>
        rw [hb] at hlist
        exact ⟨blk, rfl, by simpa using hlist⟩
  · have := hsch bid hb
    unfold schedOK at this
    rw [hfb, hgb] at this
    simp only [hoS] at this
    cases hoT : Sem.schedule g gb with
    | none => rw [hoT] at this; cases this
    | some oT =>
      rw [hoT] at this
      simp only [Bool.not_true, Bool.false_and, Bool.or_false, beq_iff_eq] at this
      exact ⟨oT, rfl, this⟩

end GoFV.Proof.CSE

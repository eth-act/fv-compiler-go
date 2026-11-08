import GoFV.Proof.Pass.CSERel
import GoFV.Proof.Pass.CSELOp

variable [GoFV.SSA.Sem.Addrs]

/-!
# lowered cse's output relation

`CRelL tabs f g rw`, the declarative form of the checker `GoFV.Opt.CSEL.crel` (`crel_sound`):
`g` has `f`'s control-flow graph, block kinds, `auxInt`s and values, is lowered as `f`; every
value keeps its ID, op, aux, auxint, type and block, its arguments become their representatives
(`rep rw`), the first two of a commutative op possibly swapped (`CSE.ArgsRel`), and it reads in
`g` what it reads in `f` of its first argument's producer (`sxOf`, unless commutative); each
control is kept or becomes its representative; every substitution `x ↦ r` is sound (`SubstL`:
`r` is not replaced, sits in a dominator of `x`'s block, in `x`'s block for a `Phi`) and
congruent (`cong`: the same op, aux, auxint, lowered shape and arguments in `g`, an op of
`CSEL.substOp`); and every block of `g` with a source schedule has one listing the roots in the
source's order.
-/

namespace GoFV.Proof.CSEL

open GoFV.SSA GoFV.Opt GoFV.Opt.CSE GoFV.Proof.CSE

/-- A sound substitution `x ↦ r` (`CSE.Subst` without the congruence, see `CRelL.cong`). -/
def SubstL (rw : Array (Option ID)) (f g : Func) (x r : ID) : Prop :=
  rw.getD r none = none ∧ ∃ fx fr gx gr, f.value? x = some fx ∧ f.value? r = some fr ∧
    g.value? x = some gx ∧ g.value? r = some gr ∧ fr.op = fx.op ∧
    (fx.op = .Phi → fr.block = fx.block) ∧
    (DomCert.make f).anc fr.block fx.block = true ∧ fr.block ∈ f.blocks ∧
    ∃ blk, f.block? fr.block = some blk ∧ r ∈ blk.values

/-- The declarative output relation of lowered cse. -/
structure CRelL (tabs : Tables) (f g : Func) (rw : Array (Option ID)) : Prop where
  cfg : DomCert.cfgView g = DomCert.cfgView f
  ownAux : g.ownAux = f.ownAux
  vsize : g.valueTab.size = f.valueTab.size
  lowered : g.lowered = f.lowered
  block : ∀ bid ∈ f.blocks, ∀ fb, f.block? bid = some fb → ∃ gb, g.block? bid = some gb ∧
    gb.kind = fb.kind ∧ gb.values = fb.values ∧ gb.controls.size = fb.controls.size ∧
    ∀ (k : Nat) (c : ID), fb.controls[k]? = some c →
      gb.controls[k]? = some c ∨ gb.controls[k]? = some (rep rw c)
  aux : ∀ bid ∈ f.blocks, ∀ fb gb, f.block? bid = some fb → g.block? bid = some gb →
    gb.auxInt = fb.auxInt
  value : ∀ x fv, f.value? x = some fv → ∃ gv, g.value? x = some gv ∧ gv.id = fv.id ∧
    gv.op = fv.op ∧ gv.aux = fv.aux ∧ gv.auxInt = fv.auxInt ∧ gv.type = fv.type ∧
    gv.block = fv.block ∧ ArgsRel rw fv.op fv.args gv.args
  sx : ∀ x fv gv, f.value? x = some fv → g.value? x = some gv →
    fv.op.commutative = true ∨ sxOf g gv = sxOf f fv
  subst : ∀ x r, rw.getD x none = some r → SubstL rw f g x r
  cong : ∀ x r, rw.getD x none = some r → ∃ fx fr gx gr, f.value? x = some fx ∧
    f.value? r = some fr ∧ g.value? x = some gx ∧ g.value? r = some gr ∧ fr.op = fx.op ∧
    fr.aux = fx.aux ∧ fr.auxInt = fx.auxInt ∧
    CSEL.shape tabs f.lowered fr.type = CSEL.shape tabs f.lowered fx.type ∧ gx.args = gr.args ∧
    CSEL.substOp fx.op = true
  sched : ∀ bid ∈ f.blocks, ∀ fb gb, f.block? bid = some fb → g.block? bid = some gb →
    ∀ oS, Sem.schedule f fb = some oS → ∃ oT, Sem.schedule g gb = some oT ∧
      oT.toList.filter (rootNode f) = oS.toList.filter (rootNode f)

theorem congr_sound {tabs : Tables} {low : Bool} {fx fr gx gr : Value}
    (h : CSEL.congr tabs low fx fr gx gr = true) :
    fr.op = fx.op ∧ fr.aux = fx.aux ∧ fr.auxInt = fx.auxInt ∧
      CSEL.shape tabs low fr.type = CSEL.shape tabs low fx.type ∧ gx.args = gr.args := by
  unfold CSEL.congr at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, ?_, h5⟩
  rcases h4 with h | h
  · rw [h]
  · exact tyEq_sound h

/-- The facts of one sound substitution. -/
theorem substOK_sound {tabs : Tables} {c : DomCert.Cert} {rw : Array (Option ID)} {f g : Func}
    {x r : ID} (h : CSEL.substOK tabs c rw f g x = true) (hr : rw.getD x none = some r) :
    (rw.getD r none).isNone = true ∧ ∃ fx fr gx gr, f.value? x = some fx ∧
      f.value? r = some fr ∧ g.value? x = some gx ∧ g.value? r = some gr ∧
      CSEL.congr tabs f.lowered fx fr gx gr = true ∧ CSEL.substOp fx.op = true ∧
      (fx.op = .Phi → fr.block = fx.block) ∧ c.anc fr.block fx.block = true ∧
      fr.block ∈ f.blocks ∧ ∃ blk, f.block? fr.block = some blk ∧ r ∈ blk.values := by
  unfold CSEL.substOK at h
  rw [hr] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hrr, hrest⟩ := h
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
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hrest
  obtain ⟨⟨⟨⟨⟨hc, hs⟩, hphi⟩, hanc⟩, hmem⟩, hlist⟩ := hrest
  refine ⟨fx, fr, gx, gr, rfl, rfl, rfl, rfl, hc, hs, fun hp => ?_, hanc, by simpa using hmem, ?_⟩
  · rcases hphi with h1 | h1
    · exact absurd hp h1
    · exact h1
  · cases hb : f.block? fr.block with
    | none => rw [hb] at hlist; cases hlist
    | some blk =>
      rw [hb] at hlist
      exact ⟨blk, rfl, by simpa using hlist⟩

/-- **The lowered checker is sound.** -/
theorem crel_sound {tabs : Tables} {f g : Func} {rw : Array (Option ID)}
    (h : CSEL.crel tabs f g rw = true) : CRelL tabs f g rw := by
  unfold CSEL.crel at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hcfg, hown⟩, hsz⟩, hlow⟩, hblk⟩, haux⟩, hval⟩, hsx⟩, hsub⟩, hsch⟩ := h
  refine ⟨hcfg, hown, hsz, hlow, fun bid hb fb hfb => ?_, fun bid hb fb gb hfb hgb => ?_,
    fun x fv hfv => ?_, fun x fv gv hfv hgv => ?_, fun x r hr => ?_, fun x r hr => ?_,
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
  · have := haux bid hb
    unfold CSEL.auxOK at this
    rw [hfb, hgb] at this
    simpa using this
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
  · have := hsx x (lt_of_value? hfv)
    unfold CSEL.sxOK at this
    rw [hfv, hgv] at this
    simp only [Bool.or_eq_true, beq_iff_eq] at this
    exact this
  · obtain ⟨hrr, fx, fr, gx, gr, hfx, hfr, hgx, hgr, hc, -, hphi, hanc, hmem, blk, hblk, hrb⟩ :=
      substOK_sound (hsub x (lt_of_getD_some hr)) hr
    exact ⟨by simpa using hrr, fx, fr, gx, gr, hfx, hfr, hgx, hgr, (congr_sound hc).1, hphi, hanc,
      hmem, blk, hblk, hrb⟩
  · obtain ⟨-, fx, fr, gx, gr, hfx, hfr, hgx, hgr, hc, hs, -⟩ :=
      substOK_sound (hsub x (lt_of_getD_some hr)) hr
    obtain ⟨hop, hax, hai, hty, hargs⟩ := congr_sound hc
    exact ⟨fx, fr, gx, gr, hfx, hfr, hgx, hgr, hop, hax, hai, hty, hargs, hs⟩
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

end GoFV.Proof.CSEL

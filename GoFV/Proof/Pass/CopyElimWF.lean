import GoFV.Proof.Pass.CopyElimLoop

variable [GoFV.SSA.Sem.Addrs]

/-!
# copyelim's output is well-formed

`copyelim_wf_of_inv`: when copyelim runs on a function `F` in the invariant `Inv tabs f F` of a
well-formed `f`, its output `g` satisfies `WF` (for every listed block) and keeps `f`'s value
table size and `vid.last`. The block list and table are `f`'s except that each control `c` of a
listed block becomes `rc G c` (`copyelim_ctl`); a replaced control is the argument of a listed
copy (`Inv.acyc`, `Inv.closed`). Values keep ID, block and type (`Inv.keep`); `Mode` gives the
op shapes (`.same`: `f`'s op, aux and arity; `.phi`: `Copy` of one argument; `.empty`: `Empty`).
-/

namespace GoFV.Proof.CopyElim

open GoFV.SSA GoFV.Opt GoFV.Proof

section
variable {tabs : Tables} {ce : CheckEnv} {f G : Func}

/-- A replaced control of a listed block is listed. -/
theorem listed_rc (hI : Inv tabs f G) {c : ID} (hc : Listed f c) : Listed f (rc G c) := by
  unfold rc
  split
  · rename_i hcop
    obtain ⟨r, n, hr⟩ := hI.acyc c hc
    cases hr with
    | sink h0 => exact absurd (by simpa using hcop) (getV_cstep_none h0)
    | @step _ y _ n hy _ =>
      obtain ⟨u, hu, -, ha⟩ := cstep_some_some hy
      rw [(getV_cstep_some hy).2]
      exact hI.closed c hc u hu y (by rw [ha]; simp)
  · exact hc

/-- The shape facts of `WF` for a value `v` of the output in mode `Mode` w.r.t. `fv`. -/
theorem mode_shape {V : ID → Option Value} {fv v : Value} (hm : Mode tabs V fv (strip v))
    (har : fv.op.argLen ≠ -1 → (fv.args.size : Int) = fv.op.argLen)
    (hba : fv.op.auxType = .Bool → 0 ≤ fv.auxInt.toInt ∧ fv.auxInt.toInt ≤ 1) :
    (v.op.argLen ≠ -1 → (v.args.size : Int) = v.op.argLen) ∧
      (v.op.auxType = .Bool → 0 ≤ v.auxInt.toInt ∧ v.auxInt.toInt ≤ 1) ∧
      (v.op = .Phi → fv.op = .Phi ∧ v.args.size = fv.args.size) := by
  cases hm with
  | same h1 h2 h3 h4 _ =>
    have h1' : v.op = fv.op := h1
    have h3' : v.auxInt = fv.auxInt := h3
    have h4' : v.args.size = fv.args.size := h4
    rw [h1', h3', h4']
    exact ⟨har, hba, fun h => ⟨h, rfl⟩⟩
  | phi w _ h2 h3 _ =>
    have h2' : v.op = .Copy := h2
    have h3' : v.args = #[w] := h3
    rw [h2', h3']
    exact ⟨fun _ => show ((1 : Nat) : Int) = Op.Copy.argLen by decide,
      fun h => absurd h (by decide), fun h => by cases h⟩
  | empty _ h2 h3 =>
    have h2' : v.op = .Empty := h2
    have h3' : v.args = #[] := h3
    rw [h2', h3']
    exact ⟨fun _ => show ((0 : Nat) : Int) = Op.Empty.argLen by decide,
      fun h => absurd h (by decide), fun h => by cases h⟩

end

/-- **copyelim from a start in the invariant gives a well-formed function** with the input's
value table size and `vid.last`. -/
theorem copyelim_wf_of_inv {ce : CheckEnv} {tabs : Tables} {f F g : Func} (hwf : WF ce f)
    (hfrag : CopyFrag tabs f) (hI : Inv tabs f F) (h : copyelim tabs F = .ok g) :
    WF ce g ∧ g.valueTab.size = f.valueTab.size ∧ g.vidLast = f.vidLast := by
  obtain ⟨G, H, names, hIG, -, hC, rfl⟩ := copyelim_ctl hwf hfrag hI h
  obtain ⟨he, -, hbs, hbt, hvl, -, hvs⟩ := skel_parts hIG
  obtain ⟨-, hvw, hcs, hblk⟩ := hC
  simp only [cskel, Prod.mk.injEq] at hcs
  obtain ⟨hce, -, hcb, -, hcv, -, hcl⟩ := hcs
  generalize hg : ({ H with names } : Func) = g
  have hgb : g.blocks = f.blocks := by rw [← hg]; exact hcb.trans hbs
  have hge : g.entry = f.entry := by rw [← hg]; exact hce.trans he
  have hgv : vw g = vw G := by rw [← hg]; exact hvw
  have hGb : ∀ bid, G.block? bid = f.block? bid := by
    intro bid; unfold Func.block?; rw [hbt]
  -- the blocks of `g`
  have hB : ∀ bid ∈ f.blocks, ∀ fb, f.block? bid = some fb →
      g.block? bid = some (setCtl (·.map (rc G)) fb) := by
    intro bid hm fb hfb
    have hmG : bid ∈ G.blocks.toList := by rw [hbs]; simpa using hm
    have := hblk bid fb (by rw [hGb]; exact hfb)
    rw [← hg]
    show H.block? bid = _
    rw [this]
    unfold ctlFn
    simp only [hmG, ite_true]
  have hB' : ∀ bid b, BlockIn g bid b → ∃ fb, BlockIn f bid fb ∧ b = setCtl (·.map (rc G)) fb := by
    rintro bid b ⟨hm, hb⟩
    rw [hgb] at hm
    obtain ⟨fb, hfb, -⟩ := hwf.blockId bid hm
    rw [hB bid hm fb hfb] at hb
    exact ⟨fb, ⟨hm, hfb⟩, (Option.some.inj hb).symm⟩
  have hL : ∀ a, Listed f a → Listed g a := by
    rintro a ⟨bid, fb, ⟨hm, hfb⟩, ha⟩
    exact ⟨bid, _, ⟨by rw [hgb]; exact hm, hB bid hm fb hfb⟩, ha⟩
  -- the values of `g`
  have hV : ∀ bid b vid v, ValueIn g bid b vid v → ∃ fb fv, BlockIn f bid fb ∧
      b = setCtl (·.map (rc G)) fb ∧ ValueIn f bid fb vid fv ∧ Mode tabs (vw G) fv (strip v) ∧
      v.block = fv.block ∧ v.id = fv.id ∧ vw G vid = some (strip v) := by
    rintro bid b vid v ⟨hbin, hvb, hv⟩
    obtain ⟨fb, hfb, rfl⟩ := hB' bid b hbin
    have hl : Listed f vid := ⟨bid, fb, hfb, hvb⟩
    have hvG : vw G vid = some (strip v) := by rw [← hgv]; exact vw_of_value? hv
    obtain ⟨fv, hfv⟩ := listed_value hwf hl
    obtain ⟨u, hu, hm⟩ := hIG.mode vid hl fv hfv
    rw [hvG] at hu; cases hu
    obtain ⟨fv', hfv', hb, -, hid⟩ := hIG.keep_some hvG
    rw [hfv] at hfv'; cases hfv'
    exact ⟨fb, fv, hfb, rfl, ⟨hfb, hvb, hfv⟩, hm, hb, hid, hvG⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- blockId
    intro bid hm
    rw [hgb] at hm
    obtain ⟨fb, hfb, hid⟩ := hwf.blockId bid hm
    exact ⟨_, hB bid hm fb hfb, hid⟩
  · -- blocksNodup
    rw [hgb]; exact hwf.blocksNodup
  · -- valueId
    intro bid b hbin vid hvid
    obtain ⟨fb, hfb, rfl⟩ := hB' bid b hbin
    obtain ⟨fv, hfv, hid, hbk⟩ := hwf.valueId bid fb hfb vid hvid
    have hl : Listed f vid := ⟨bid, fb, hfb, hvid⟩
    obtain ⟨u, hu, -⟩ := hIG.mode vid hl fv hfv
    rw [← hgv] at hu
    obtain ⟨v, hv, rfl⟩ := vw_eq_some hu
    obtain ⟨fv', hfv', hb, -, hid'⟩ := hIG.keep_some (show vw G vid = some (strip v) by
      rw [← hgv]; exact hu)
    rw [hfv] at hfv'; cases hfv'
    exact ⟨v, hv, hid'.trans hid, hb.trans hbk⟩
  · -- valuesNodup
    intro bid b hbin
    obtain ⟨fb, hfb, rfl⟩ := hB' bid b hbin
    exact hwf.valuesNodup bid fb hfb
  · -- valueOnce
    intro bid1 b1 bid2 b2 h1 h2 vid hv1 hv2
    obtain ⟨fb1, hfb1, rfl⟩ := hB' bid1 b1 h1
    obtain ⟨fb2, hfb2, rfl⟩ := hB' bid2 b2 h2
    exact hwf.valueOnce bid1 fb1 bid2 fb2 hfb1 hfb2 vid hv1 hv2
  · -- predLink
    intro bid b hbin i e he'
    obtain ⟨fb, hfb, rfl⟩ := hB' bid b hbin
    obtain ⟨hm, p, hp, hs⟩ := hwf.predLink bid fb hfb i e he'
    exact ⟨by rw [hgb]; exact hm, _, hB _ hm p hp, hs⟩
  · -- succLink
    intro bid b hbin j e he'
    obtain ⟨fb, hfb, rfl⟩ := hB' bid b hbin
    obtain ⟨hm, c, hc, hs⟩ := hwf.succLink bid fb hfb j e he'
    exact ⟨by rw [hgb]; exact hm, _, hB _ hm c hc, hs⟩
  · -- arity
    intro bid b vid v hvin
    obtain ⟨fb, fv, -, -, hfin, hm, -⟩ := hV bid b vid v hvin
    exact (mode_shape hm (hwf.arity bid fb vid fv hfin) (hwf.boolAux bid fb vid fv hfin)).1
  · -- phiArity
    intro bid b vid v hvin hop
    obtain ⟨fb, fv, -, rfl, hfin, hm, -⟩ := hV bid b vid v hvin
    obtain ⟨hfop, hsz⟩ :=
      (mode_shape hm (hwf.arity bid fb vid fv hfin) (hwf.boolAux bid fb vid fv hfin)).2.2 hop
    exact hsz.trans (hwf.phiArity bid fb vid fv hfin hfop)
  · -- boolAux
    intro bid b vid v hvin
    obtain ⟨fb, fv, -, -, hfin, hm, -⟩ := hV bid b vid v hvin
    exact (mode_shape hm (hwf.arity bid fb vid fv hfin) (hwf.boolAux bid fb vid fv hfin)).2.1
  · -- argListed
    intro bid b vid v hvin a ha
    obtain ⟨fb, fv, hfb, -, hfin, -, -, -, hvG⟩ := hV bid b vid v hvin
    exact hL a (hIG.closed vid ⟨bid, fb, hfb, hfin.2.1⟩ _ hvG a ha)
  · -- ctrlListed
    intro bid b hbin c hc
    obtain ⟨fb, hfb, rfl⟩ := hB' bid b hbin
    obtain ⟨c0, hc0, rfl⟩ := Array.mem_map.1 hc
    exact hL _ (listed_rc hIG (hwf.ctrlListed bid fb hfb c0 hc0))
  · -- entry
    rw [hgb, hge]; exact hwf.entry
  · -- entryPreds
    intro b hb
    rw [hge] at hb
    obtain ⟨fb, hfb, -⟩ := hwf.blockId f.entry hwf.entry
    rw [hB _ hwf.entry fb hfb] at hb
    cases hb
    exact hwf.entryPreds fb hfb
  · rw [← hg]; exact hcv.trans hvs
  · rw [← hg]; exact hcl.trans hvl

end GoFV.Proof.CopyElim

import GoFV.Proof.Pass.ECIdent
import GoFV.Proof.Pass.ECArgSel
import GoFV.Proof.Pass.ECCall
import GoFV.Proof.Pass.CSEOp
import GoFV.Proof.CheckFacts
import GoFV.Proof.Checked
import GoFV.Proof.Eval

/-!
# `expand calls`: the local obligation of every source value (issue #28)

`obl_invalid`: a value the pass invalidated (`OpInvalid` in the target, conversion `poison`) is
pure in the source (`valueOK`: priority 0), so its evaluation does not panic, and the target's
`Invalid` evaluates. `eco_obl` dispatches a non-`Phi` value of a block on `valueOK`'s classes
(call, `MakeResult`, call result, invalidated, parameter, identity) to the class obligations,
with the closure `L` of the target's new arguments (`x`, and new values of its block or of the
entry block) and the `held` nodes the `IMake` arguments of converted values depend on.
-/

namespace GoFV.Proof.EC

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Opt GoFV.Opt.ECCheck GoFV.Proof.AtomSim
  GoFV.Proof.Order

/-! ## Invalidated values -/

/-- **The obligation of an invalidated value**: a pure source value whose target node is
`Invalid`. -/
theorem obl_invalid {tabs : Tables} {f g : Func} {x : ID} {u w : Value} {H : ID → Prop}
    (hu : f.value? x = some u) (hw : g.value? x = some w) (hinv : w.op = .Invalid)
    (hprio : prio u.op = 0) :
    Obl tabs f g (ecCv tabs f g) (isNewB f) (ecFront f g x) H x := by
  intro u' w' hu' hw' env _ frS T _ _ E _ _ hRw _ _ _
  rw [hu] at hu'
  cases hu'
  rw [hw] at hw'
  cases hw'
  have hcv : ∀ y, ecCv tabs f g x y = .poison := fun y => by
    unfold ecCv
    rw [ite_eq_left (by unfold invalidated; rw [hw]; exact beq_iff_eq.2 hinv)]
  obtain ⟨r, hr⟩ := CSE.evalOp_total (env := env) (ctx := Ctx.make tabs g) (fr := T)
    (argv := w.args.toList.map (rv T)) (ty := (Ctx.make tabs g).tys[w.id]?.getD .other)
    (v := w) (by rw [hinv]; decide) (by rw [hinv]; decide) (by rw [hinv]; decide)
  rw [evalValue_of_regs hRw, hr]
  cases hS : evalValue env (Ctx.make tabs f) frS u with
  | ok y => exact .ok (by rw [hcv]; exact .poison _)
  | panic e m => exact absurd hprio (prio_panicking (evalValue_panic_op hS))
  | stuck msg => exact .stuck msg _

/-! ## The checker's facts -/

theorem eco_ecCheck {tabs : Tables} {f g : Func} (h : ecCheck tabs f g = true) :
    cfgView g = cfgView f ∧ g.ownAux = f.ownAux ∧ regParamsOK tabs (ownOuts tabs f) = true ∧
      ∀ bid ∈ f.blocks, blockOK tabs (typeShapes tabs) f g bid = true := by
  unfold ecCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true'] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

/-- What the dispatch reads of `blockOK`: the target block, the source's values listed in it,
`valueOK` of the non-`Phi` ones, and the new arguments of new values. -/
theorem eco_blockOK {tabs : Tables} {f g : Func} {bid : ID} {fb : Block}
    (h : blockOK tabs (typeShapes tabs) f g bid = true) (hfb : f.block? bid = some fb) :
    ∃ gb, g.block? bid = some gb ∧ (∀ x ∈ fb.values, x ∈ gb.values) ∧
      (∀ x ∈ fb.values, ∀ u, f.value? x = some u → u.op ≠ .Phi →
        valueOK tabs (typeShapes tabs) f g x = true) ∧
      (∀ z ∈ gb.values, isNewB f z = true → ∀ w, g.value? z = some w → ∀ a ∈ w.args,
        isNewB f a = true → a ∈ gb.values ∨ a ∈ valsOf g g.entry) := by
  unfold blockOK at h
  rw [hfb] at h
  cases hgb : g.block? bid with
  | none => rw [hgb] at h; cases h
  | some gb =>
    rw [hgb] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, hsub⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hval⟩, -⟩, -⟩, -⟩, hnew⟩ := h
    refine ⟨gb, rfl, fun x hx => ?_, fun x hx u hu hphi => ?_, fun z hz hzn w hw a ha han => ?_⟩
    · exact Array.contains_iff_mem.1 (Array.all_eq_true'.1 hsub x hx)
    · have := Array.all_eq_true'.1 hval x hx
      rw [hu] at this
      simp only [Bool.or_eq_true, beq_iff_eq] at this
      exact this.resolve_left hphi
    · have := Array.all_eq_true'.1 hnew z hz
      rw [hzn, hw] at this
      simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at this
      have := Array.all_eq_true'.1 this.2 a ha
      rw [han] at this
      simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, Array.contains_iff_mem] at this
      exact this

theorem eco_entryVal {g : Func} {a : ID} (h : a ∈ valsOf g g.entry) : EntryVal g a := by
  unfold valsOf at h
  cases he : g.block? g.entry with
  | none => rw [he] at h; simp at h
  | some eb => rw [he] at h; exact ⟨eb, he, h⟩

/-- A call result's Make-tree has a node at its root: not `Invalid`. -/
theorem eco_mkTree_sel {sh : Array Ty} {g : Func} {nw : ID → Bool} {x c : ID} {w : Value}
    {first : Nat} (hw : g.value? x = some w) (hinv : w.op = .Invalid) :
    ∀ {n : Nat} {t : Ty} {ls : List ID}, mkTree sh g nw n x t = some ls →
      selLeavesOK g c first 0 ls = true → False
  | 0, _, _, h, _ => by simp [mkTree] at h
  | n + 1, t, ls, h, hs => by
    simp only [mkTree, hw] at h
    split at h
    · cases h
    · split at h
      · split at h
        · rename_i hm
          have h0 : isMake Op.Invalid = false := rfl
          rw [hinv, h0, Bool.false_and] at hm
          cases hm
        · cases h
      · split at h
        · rename_i he
          rw [hinv] at he
          exact absurd he (by decide)
        · cases h
      · split at h
        · cases h
          simp only [selLeavesOK, hw, Bool.and_eq_true, beq_iff_eq] at hs
          exact absurd hs.1.1.1 (by rw [hinv]; decide)
        · cases h

/-- `selectOK`: the selected value is a call's, and the target's node is not `Invalid`. -/
theorem eco_selectOK {tabs : Tables} {f g : Func} {x c : ID} {u w cu : Value}
    (hw : g.value? x = some w) (hargs : u.args.toList = [c]) (hcu : f.value? c = some cu)
    (h : selectOK tabs (typeShapes tabs) f g x u w = true) :
    (callOpMap cu.op).isSome = true ∧ w.op ≠ .Invalid := by
  unfold selectOK at h
  rw [hargs] at h
  dsimp only at h
  rw [hcu] at h
  dsimp only at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hcall, -⟩, h⟩ := h
  refine ⟨hcall, fun hinv => ?_⟩
  split at h
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact absurd h.1.1.1 (by rw [hinv]; decide)
  · split at h
    · simp only [Bool.and_eq_true] at h
      obtain ⟨-, h⟩ := h
      split at h
      · rename_i ls hls
        simp only [Bool.and_eq_true] at h
        exact eco_mkTree_sel hw hinv hls h.2
      · cases h
    · cases h

/-! ## The dispatch -/

/-- **The local obligation of a non-`Phi` source value** of block `bid` for `expand calls`,
`held` the nodes of the target block that `x` depends on. -/
theorem eco_obl {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} {bid x : ID} {fb gb : Block}
    {u : Value}
    (hf : check ce f = .ok ()) (hg : check ce' g = .ok ())
    (hec : ecCheck tabs f g = true) (hbid : bid ∈ f.blocks)
    (hfb : f.block? bid = some fb) (hgb : g.block? bid = some gb)
    (hx : x ∈ fb.values) (hu : f.value? x = some u) (hphi : u.op ≠ .Phi)
    (hnewx : ∀ w, g.value? x = some w → ∀ a ∈ w.args, isNewB f a = true →
      a ∈ gb.values ∨ EntryVal g a)
    (himk : converted f x = true → ∀ a ∈ u.args, ∀ aw, g.value? a = some aw → aw.op = .IMake →
      Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList) a x ∧
      Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList) aw.args[1]! x ∧
      ifaceShape (shapeOf (typeShapes tabs) g a) = true) :
    Obl tabs f g (ecCv tabs f g) (isNewB f) (ecFront f g x)
      (fun z => Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList) z x) x := by
  have Wf := check_wf hf
  have Wg := check_wf hg
  obtain ⟨hcfg, hown, hreg, hblk⟩ := eco_ecCheck hec
  have hbidg : bid ∈ g.blocks := by rw [CopyElim.cfgView_blocks hcfg]; exact hbid
  obtain ⟨gb0, hgb0, hsub, hvals, hnewb⟩ := eco_blockOK (hblk bid hbid) hfb
  rw [hgb] at hgb0
  cases hgb0
  have hcommon := hsub x hx
  have hv := hvals x hx u hu hphi
  have huid : u.id = x := by
    obtain ⟨v, hv', hvid, -⟩ := Wf.valueId bid fb ⟨hbid, hfb⟩ x hx
    rw [hu] at hv'
    cases hv'
    exact hvid
  -- the closure of new arguments
  have hgid : ∀ z ∈ gb.values, ∀ w, g.value? z = some w → w.id = z := fun z hz w hw => by
    obtain ⟨v, hv', hvid, -⟩ := Wg.valueId bid gb ⟨hbidg, hgb⟩ z hz
    rw [hw] at hv'
    cases hv'
    exact hvid
  have hentry : ∀ z, EntryVal g z → isNewB f z = true → ∀ w, g.value? z = some w →
      w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true → EntryVal g a := by
    intro z ⟨eb, heb, hz⟩ hzn w hw
    have hfe : f.entry ∈ f.blocks := Wf.entry
    have hge : g.entry = f.entry := CopyElim.cfgView_entry hcfg
    obtain ⟨feb, hfeb, -⟩ := Wf.blockId f.entry hfe
    obtain ⟨eb', heb', -, -, hnE⟩ := eco_blockOK (hblk f.entry hfe) hfeb
    rw [← hge, heb] at heb'
    cases heb'
    obtain ⟨v, hv', hvid, -⟩ := Wg.valueId g.entry eb ⟨Wg.entry, heb⟩ z hz
    rw [hw] at hv'
    cases hv'
    refine ⟨hvid, fun a ha han => ?_⟩
    rcases hnE z hz hzn _ hw a ha han with h | h
    · exact ⟨eb, heb, h⟩
    · exact eco_entryVal h
  have hL : ∀ z, (z = x ∨ (isNewB f z = true ∧ (z ∈ gb.values ∨ EntryVal g z))) →
      ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true →
        (a = x ∨ (isNewB f a = true ∧ (a ∈ gb.values ∨ EntryVal g a))) := by
    rintro z (rfl | ⟨hzn, hz | hz⟩) w hw
    · exact ⟨hgid z hcommon w hw, fun a ha han => .inr ⟨han, hnewx w hw a ha han⟩⟩
    · refine ⟨hgid z hz w hw, fun a ha han => .inr ⟨han, ?_⟩⟩
      rcases hnewb z hz hzn w hw a ha han with h | h
      · exact .inl h
      · exact .inr (eco_entryVal h)
    · obtain ⟨hid, hcl⟩ := hentry z hz hzn w hw
      exact ⟨hid, fun a ha han => .inr ⟨han, .inr (hcl a ha han)⟩⟩
  have hLx : x = x ∨ (isNewB f x = true ∧ (x ∈ gb.values ∨ EntryVal g x)) := .inl rfl
  -- the classes
  unfold valueOK at hv
  rw [hu] at hv
  cases hw : g.value? x with
  | none => rw [hw] at hv; cases hv
  | some w =>
    rw [hw] at hv
    dsimp only at hv
    by_cases hc : (callOpMap u.op).isSome = true
    · rw [ite_eq_left hc] at hv
      have hconv : converted f x = true := by
        unfold converted; rw [hu]; dsimp only; rw [hc]; rfl
      exact obl_call hu hw hc hv huid _ hLx hL (himk hconv)
    rw [ite_eq_right hc] at hv
    by_cases hr : (u.op == .MakeResult) = true
    · rw [ite_eq_left hr] at hv
      have hconv : converted f x = true := by
        unfold converted; rw [hu]; dsimp only; rw [hr, Bool.or_true]
      exact obl_result hu hw (beq_iff_eq.1 hr) hv hreg huid _ hLx hL (himk hconv)
    rw [ite_eq_right hr] at hv
    by_cases hs : (u.op == .SelectN && u.args.size == 1 && converted f u.args[0]!) = true
    · rw [ite_eq_left hs] at hv
      simp only [Bool.and_eq_true, beq_iff_eq] at hs
      obtain ⟨⟨hsel, hsz⟩, hcv⟩ := hs
      have hargs : u.args.toList = [u.args[0]!] := ec_args_one hsz
      unfold converted at hcv
      cases hcu : f.value? u.args[0]! with
      | none => rw [hcu] at hcv; cases hcv
      | some cu =>
        obtain ⟨hcall, hni⟩ := eco_selectOK hw hargs hcu hv
        have hcmem : u.args[0]! ∈ u.args :=
          Array.mem_toList_iff.1 (by rw [hargs]; exact List.mem_singleton_self _)
        obtain ⟨bid', fb', ⟨hbid', hfb'⟩, hc'⟩ :=
          Wf.argListed bid fb x u ⟨⟨hbid, hfb⟩, hx, hu⟩ _ hcmem
        obtain ⟨-, -, -, hvals', -⟩ := eco_blockOK (hblk bid' hbid') hfb'
        have hcphi : cu.op ≠ .Phi := fun h => absurd hcall (by rw [h]; decide)
        have hvc := hvals' _ hc' cu hcu hcphi
        unfold valueOK at hvc
        rw [hcu] at hvc
        cases hcw : g.value? u.args[0]! with
        | none => rw [hcw] at hvc; cases hvc
        | some cw =>
          rw [hcw] at hvc
          dsimp only at hvc
          rw [ite_eq_left hcall] at hvc
          have hinv : invalidated g x = false := by
            unfold invalidated; rw [hw]; dsimp only
            exact Bool.eq_false_iff.2 fun h => hni (beq_iff_eq.1 h)
          exact obl_select hu hw hsel hargs hcu hcw hcall hvc hinv hv hown huid _ hLx hL
    rw [ite_eq_right hs] at hv
    by_cases hi : (w.op == .Invalid) = true
    · rw [ite_eq_left hi] at hv
      simp only [Bool.and_eq_true, beq_iff_eq] at hv
      exact obl_invalid hu hw (beq_iff_eq.1 hi) hv.1
    rw [ite_eq_right hi] at hv
    have hinv : invalidated g x = false := by
      unfold invalidated; rw [hw]; exact Bool.eq_false_iff.2 hi
    have hwid : w.id = x := (hL x hLx w hw).1
    by_cases ha : (u.op == .Arg && !identOK f g u w) = true
    · rw [ite_eq_left ha] at hv
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at ha
      exact obl_arg hu hw ha.1 hinv ha.2 hv hown huid _ hLx hL
    rw [ite_eq_right ha] at hv
    have hsp : special f g x = false := by
      unfold special converted
      rw [hu, hinv]
      dsimp only
      rw [Bool.eq_false_iff.2 hc, Bool.eq_false_iff.2 hr]
      rfl
    exact obl_ident hu hw huid hwid hv hsp hown

end GoFV.Proof.EC

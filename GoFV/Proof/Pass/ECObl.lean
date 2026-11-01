import GoFV.Proof.Pass.ECTyped
import GoFV.Proof.Pass.ECIdent
import GoFV.Proof.Pass.ECArgSel
import GoFV.Proof.Pass.ECStackRes
import GoFV.Proof.Pass.CSEOp
import GoFV.Proof.CheckFacts
import GoFV.Proof.Checked
import GoFV.Proof.Eval
import GoFV.Proof.AtomSimSet
import GoFV.Proof.DomCert

/-!
# `expand calls`: the local obligation of every source value (issue #28)

`obl_invalid`: a value the pass invalidated (`OpInvalid` in the target, conversion `poison`) is
pure in the source (`valueOK`: priority 0), so its evaluation does not panic, and the target's
`Invalid` evaluates. `eco_obl` dispatches a non-`Phi` value of a tree block on `valueOK`'s
classes (call, `MakeResult`, call result in registers or on the stack, invalidated, parameter,
identity) to the class obligations, with the closure `L` of the target's new arguments (the values
listed in `g`); the `IMake` arguments of converted values are held in source mode (`Held`: in the
block and depended on, or placed in a strict dominator, `AtomSim.arg_anc`) or target mode
(`HeldT`: likewise in `g`), and so are the call of a stack-assigned result (source mode) and its
leaves' source `SP`s and memories (target mode).
-/

namespace GoFV.Proof.EC

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Opt GoFV.Opt.ECCheck GoFV.Proof.AtomSim
  GoFV.Proof.Order

/-! ## Invalidated values -/

/-- **The obligation of an invalidated value**: a pure source value whose target node is
`Invalid`. -/
theorem obl_invalid {tabs : Tables} {f g : Func} {x : ID} {u w : Value} {HS HT : ID → Prop}
    (hu : f.value? x = some u) (hw : g.value? x = some w) (hinv : w.op = .Invalid)
    (hprio : prio u.op = 0) :
    Obl tabs f g (ecCv tabs f g) (isNewB f) (ecFront f g x) HS HT x := by
  intro u' w' hu' hw' env _ frS T _ _ E _ _ hRw _ _ _ _
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

/-! ## Tail calls -/

theorem tailOp_eq {op : Op} (h : tailOp op = true) : op = .TailLECall ∨ op = .TailLECallInter := by
  unfold tailOp at h
  split at h
  · exact .inl rfl
  · exact .inr rfl
  · cases h

/-- **The obligation of a tail call**: `TailLECall*` is outside the semantics' phases, so the
source's evaluation is `stuck`. -/
theorem obl_tail {tabs : Tables} {f g : Func} {x : ID} {u : Value} {HS HT : ID → Prop}
    (hu : f.value? x = some u) (hop : tailOp u.op = true) :
    Obl tabs f g (ecCv tabs f g) (isNewB f) (ecFront f g x) HS HT x := by
  intro u' w' hu' hw' env _ frS T _ _ E _ _ _ hRu _ _ _
  rw [hu] at hu'
  cases hu'
  obtain ⟨msg, hS⟩ := evalOp_tail (env := env) (ctx := Ctx.make tabs f) (fr := frS)
    (argv := u.args.toList.map (rv frS)) (ty := (Ctx.make tabs f).tys[u.id]?.getD .other)
    (tailOp_eq hop)
  rw [evalValue_of_regs hRu, hS]
  exact .stuck msg _

/-- **The obligation of a value reading a tail call**: no source register holds a tail call
(`RegOK`), so the source never evaluates it. -/
theorem obl_tailUse {tabs : Tables} {f g : Func} {x c : ID} {u cu : Value} {HS HT : ID → Prop}
    (hu : f.value? x = some u) (hc : c ∈ u.args) (hcu : f.value? c = some cu)
    (hop : tailOp cu.op = true) :
    Obl tabs f g (ecCv tabs f g) (isNewB f) (ecFront f g x) HS HT x := by
  intro u' w' hu' hw' env _ frS T _ hRS E _ _ _ hRu _ _ _
  rw [hu] at hu'
  cases hu'
  obtain ⟨y, hy⟩ := hRu c hc
  obtain ⟨h1, h2⟩ := (hRS c y hy).2.2 cu hcu
  rcases tailOp_eq hop with h | h
  · exact absurd h h1
  · exact absurd h h2

/-! ## The checker's facts -/

theorem eco_ecCheck {tabs : Tables} {f g : Func} (h : ecCheck tabs f g = true) :
    cfgView g = cfgView f ∧ g.ownAux = f.ownAux ∧ regParamsOK tabs (ownOuts tabs f) = true ∧
      ∀ bid ∈ f.blocks, blockOK tabs (typeShapes tabs) (make g).anc f g bid = true := by
  unfold ecCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true'] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

/-- What the dispatch reads of `blockOK`: the target block, the source's values listed in it,
and `valueOK` of the non-`Phi` ones. -/
theorem eco_blockOK {tabs : Tables} {anc : ID → ID → Bool} {f g : Func} {bid : ID} {fb : Block}
    (h : blockOK tabs (typeShapes tabs) anc f g bid = true) (hfb : f.block? bid = some fb) :
    ∃ gb, g.block? bid = some gb ∧ (∀ x ∈ fb.values, x ∈ gb.values) ∧
      (∀ x ∈ fb.values, ∀ u, f.value? x = some u → u.op ≠ .Phi →
        valueOK tabs (typeShapes tabs) f g x = true) := by
  unfold blockOK at h
  rw [hfb] at h
  cases hgb : g.block? bid with
  | none => rw [hgb] at h; cases h
  | some gb =>
    rw [hgb] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, hsub⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hval⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
    refine ⟨gb, rfl, fun x hx => ?_, fun x hx u hu hphi => ?_⟩
    · exact Array.contains_iff_mem.1 (Array.all_eq_true'.1 hsub x hx)
    · have := Array.all_eq_true'.1 hval x hx
      rw [hu] at this
      simp only [Bool.or_eq_true, beq_iff_eq] at this
      exact this.resolve_left hphi

/-- A Make-tree whose root's node is `Invalid` is that leaf alone. -/
theorem eco_mkTree_inv {sh : Array Ty} {g : Func} {nw : ID → Bool} {x : ID} {w : Value}
    (hw : g.value? x = some w) (hinv : w.op = .Invalid) :
    ∀ {n : Nat} {t : Ty} {ls : List ID}, mkTree sh g nw n x t = some ls → ls = [x]
  | 0, _, _, h => by simp [mkTree] at h
  | n + 1, t, ls, h => by
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
        · cases h; rfl
        · cases h

/-- A call result's Make-tree has a node at its root: not `Invalid`. -/
theorem eco_mkTree_sel {sh : Array Ty} {g : Func} {nw : ID → Bool} {x c : ID} {w : Value}
    {first : Nat} (hw : g.value? x = some w) (hinv : w.op = .Invalid) {n : Nat} {t : Ty}
    {ls : List ID} (h : mkTree sh g nw n x t = some ls) (hs : selLeavesOK g c first 0 ls = true) :
    False := by
  rw [eco_mkTree_inv hw hinv h] at hs
  simp only [selLeavesOK, hw, Bool.and_eq_true, beq_iff_eq] at hs
  exact absurd hs.1.1.1 (by rw [hinv]; decide)

/-- A stack-assigned call result's Make-tree has a node at its root: not `Invalid`. -/
theorem eco_mkTree_stk {sh : Array Ty} {g : Func} {nw : ID → Bool} {x c : ID} {w : Value}
    {k : Nat} {off : Int} {os : List (Nat × Ty)} (hw : g.value? x = some w)
    (hinv : w.op = .Invalid) {n : Nat} {t : Ty} {ls : List ID} (h : mkTree sh g nw n x t = some ls)
    (hs : stkLeavesOK sh g nw c k off os ls = true) : False := by
  rw [eco_mkTree_inv hw hinv h] at hs
  cases os with
  | nil => simp [stkLeavesOK] at hs
  | cons e os =>
    obtain ⟨o, lt⟩ := e
    simp only [stkLeavesOK, hw, Bool.and_eq_true, beq_iff_eq] at hs
    exact absurd hs.1.1.1.1 (by rw [hinv]; decide)

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
        split at h
        · exact eco_mkTree_stk hw hinv hls h.2
        · exact eco_mkTree_sel hw hinv hls h.2
      · cases h
    · cases h

/-! ## The dispatch -/

/-- An `IMake` argument of a non-`Phi` value `x` of a tree block, checked by `imkArgOK`, is held
in source mode (`Held`: a value of the block `x` depends on, or else placed in a strict
dominator, `AtomSim.arg_anc`) or in target mode (`HeldT`). -/
theorem eco_imkHeld {ce : CheckEnv} {tabs : Tables} {f g : Func} {bid x a : ID} {fb gb : Block}
    {u : Value} (Wf : WF ce f) (hc : CertOK f) (hbid : bid ∈ f.blocks)
    (hfb : f.block? bid = some fb) (hfid : fb.id = bid) (hx : x ∈ fb.values)
    (hu : f.value? x = some u) (hublk : u.block = bid) (hphi : u.op ≠ .Phi)
    (htree : ((make f).depthOf fb.id).isSome) (ha : a ∈ u.args)
    (h : EcImkOK tabs f g fb gb x a) :
    EcoImkHeld tabs f g (Held f g fb gb x) (HeldT g gb x) a := by
  intro aw haw hop
  obtain ⟨-, ⟨au, hau, hauop, hau2, haud, hi, hsp, hsh, hdep⟩ | ⟨hi, hda, hdd⟩⟩ := h aw haw hop
  · refine .inr ⟨?_, ⟨au, hau, hauop, hau2, haud⟩, hi, hsp, hsh⟩
    by_cases hafb : a ∈ fb.values
    · exact .inl ⟨hafb, hdep hafb⟩
    · have hp : Placed f x u := ⟨hu, by rw [hublk]; exact hbid, fb, by rw [hublk]; exact hfb, hx⟩
      obtain ⟨va, ⟨hva, hvb, blk, hblk, hab⟩, hanc⟩ :=
        AtomSim.arg_anc Wf hc hp (by rw [hublk, ← hfid]; exact htree) hphi ha
      rw [hau] at hva
      cases hva
      rw [hublk, ← hfid] at hanc
      refine .inr ⟨au, ⟨hau, hvb, blk, hblk, hab⟩, by rw [hauop]; decide, hanc, fun he => hafb ?_⟩
      rw [he, hfid, hfb] at hblk
      cases hblk
      exact hab
  · exact .inl ⟨hda, hdd, hi⟩

/-- **The local obligation of a non-`Phi` source value** of tree block `bid` for
`expand calls`, the source's `Held` values and the target's `HeldT` values holding their
evaluations (among them the `SP`s of a call's stack-argument stores, `hsp`, and the `SP`s and
memories of a stack-assigned result's loads, `hld`; `hdep`: `x` depends in `g` on its arguments
that are nodes of the block). -/
theorem eco_obl {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} {bid x : ID} {fb gb : Block}
    {u : Value}
    (hf : check ce f = .ok ()) (hg : check ce' g = .ok ())
    (hec : ecCheck tabs f g = true) (hbid : bid ∈ f.blocks)
    (hfb : f.block? bid = some fb) (hgb : g.block? bid = some gb)
    (htree : ((make f).depthOf fb.id).isSome)
    (hx : x ∈ fb.values) (hu : f.value? x = some u) (hphi : u.op ≠ .Phi)
    (himk : converted f x = true → ∀ a ∈ u.args, EcImkOK tabs f g fb gb x a)
    (hsp : (callOpMap u.op).isSome = true → ∀ w, g.value? x = some w → ∀ a, ecStackSP f g u w a →
      HeldT g gb x a)
    (hdep : ∀ a ∈ u.args, a ∈ fb.values → (∀ ua, f.value? a = some ua → ua.op ≠ .Phi) →
      Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList) a x)
    (hld : ∀ l ∈ stackLoads tabs (typeShapes tabs) f g x,
      (isNewB f (loadSP g l) = false → HeldT g gb x (loadSP g l)) ∧
      (isNewB f (loadMem g l) = false → HeldT g gb x (loadMem g l))) :
    Obl tabs f g (ecCv tabs f g) (isNewB f) (ecFront f g x) (Held f g fb gb x) (HeldT g gb x) x := by
  have Wf := check_wf hf
  have Wg := check_wf hg
  have hcert : CertOK f := certOK_of_check (check_domCert hf)
  obtain ⟨hcfg, hown, hreg, hblk⟩ := eco_ecCheck hec
  have hbidg : bid ∈ g.blocks := by rw [CopyElim.cfgView_blocks hcfg]; exact hbid
  obtain ⟨gb0, hgb0, hsub, hvals⟩ := eco_blockOK (hblk bid hbid) hfb
  rw [hgb] at hgb0
  cases hgb0
  have hcommon := hsub x hx
  have hv := hvals x hx u hu hphi
  obtain ⟨huid, hublk⟩ : u.id = x ∧ u.block = bid := by
    obtain ⟨v, hv', hvid, hvb⟩ := Wf.valueId bid fb ⟨hbid, hfb⟩ x hx
    rw [hu] at hv'
    cases hv'
    exact ⟨hvid, hvb⟩
  have hfid : fb.id = bid := by
    obtain ⟨b, hb, hbid'⟩ := Wf.blockId bid hbid
    rw [hfb] at hb
    cases hb
    exact hbid'
  have hH : converted f x = true → ∀ a ∈ u.args, EcoImkHeld tabs f g (Held f g fb gb x)
      (HeldT g gb x) a :=
    fun hconv a ha => eco_imkHeld Wf hcert hbid hfb hfid hx hu hublk hphi htree ha (himk hconv a ha)
  -- the closure of new arguments: the values listed in `g`
  have hL : ∀ z, Listed g z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args,
      isNewB f a = true → Listed g a := by
    intro z ⟨c, gc, hc, hz⟩ w hw
    obtain ⟨v, hv', hvid, -⟩ := Wg.valueId c gc hc z hz
    exact ⟨by rw [hw] at hv'; cases hv'; exact hvid,
      fun a ha _ => Wg.argListed c gc z w ⟨hc, hz, hw⟩ a ha⟩
  have hLx : Listed g x := ⟨bid, gb, ⟨hbidg, hgb⟩, hcommon⟩
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
      exact obl_call hu hw hc hv huid _ hLx hL (hH hconv) (hsp hc w hw)
    rw [ite_eq_right hc] at hv
    by_cases hr : (u.op == .MakeResult) = true
    · rw [ite_eq_left hr] at hv
      have hconv : converted f x = true := by
        unfold converted; rw [hu]; dsimp only; rw [hr, Bool.or_true]
      exact obl_result hu hw (beq_iff_eq.1 hr) hv hreg huid _ hLx hL (hH hconv)
    rw [ite_eq_right hr] at hv
    by_cases ht : (tailOp u.op || u.args.any (isTail f)) = true
    · rcases Bool.or_eq_true_iff.1 ht with h | h
      · exact obl_tail hu h
      · obtain ⟨c, hc, hct⟩ := Array.any_eq_true'.1 h
        unfold isTail at hct
        cases hcu : f.value? c with
        | none => rw [hcu] at hct; cases hct
        | some cu => rw [hcu] at hct; exact obl_tailUse hu hc hcu hct
    rw [ite_eq_right ht] at hv
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
        obtain ⟨-, -, -, hvals'⟩ := eco_blockOK (hblk bid' hbid') hfb'
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
          by_cases hstp : ∃ p, (callOuts tabs cu.aux)[u.auxInt.toInt.toNat]? = some p ∧
              p.regs.isEmpty = true
          · obtain ⟨p, hp, hpst⟩ := hstp
            -- the call is held in the source
            have hHc : Held f g fb gb x u.args[0]! := by
              by_cases hcf : u.args[0]! ∈ fb.values
              · exact .inl ⟨hcf, hdep _ hcmem hcf fun ua hua => by
                  rw [hcu] at hua; cases hua; exact hcphi⟩
              · have hpl : Placed f x u :=
                  ⟨hu, by rw [hublk]; exact hbid, fb, by rw [hublk]; exact hfb, hx⟩
                obtain ⟨va, ⟨hva, hvb, blk, hblk', hab⟩, hanc⟩ :=
                  AtomSim.arg_anc Wf hcert hpl (by rw [hublk, ← hfid]; exact htree) hphi hcmem
                rw [hcu] at hva
                cases hva
                rw [hublk, ← hfid] at hanc
                refine .inr ⟨cu, ⟨hcu, hvb, blk, hblk', hab⟩, hcphi, hanc, fun he => hcf ?_⟩
                rw [he, hfid, hfb] at hblk'
                cases hblk'
                exact hab
            exact obl_selectStack hu hw hsel hargs hcu hcw hcall hvc hinv hv hp hpst huid _ hLx hL
              hHc hld
          · refine obl_select hu hw hsel hargs hcu hcw hcall hvc hinv hv (fun p hp => ?_) hown huid
              _ hLx hL
            cases h : p.regs.isEmpty
            · rfl
            · exact absurd ⟨p, hp, h⟩ hstp
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

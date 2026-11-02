import GoFV.Proof.Pass.ECTyped
import GoFV.Proof.Pass.ECIdent
import GoFV.Proof.Pass.ECArgSel
import GoFV.Proof.Pass.ECOwn
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
    cfgView g = cfgView f ∧ g.ownAux = f.ownAux ∧ ownOutsOK tabs f = true ∧
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
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, hsub⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hval⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ :=
      h
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
        · rw [Bool.and_eq_true] at h
          exact eco_mkTree_stk hw hinv hls h.2.2
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
      refine .inr (.inl ⟨au, ⟨hau, hvb, blk, hblk, hab⟩, by rw [hauop]; decide, hanc, fun he => hafb ?_⟩)
      rw [he, hfid, hfb] at hblk
      cases hblk
      exact hab
  · exact .inl ⟨hda, hdd, hi⟩

/-- A converted call listed in `f` passes `callOK` with its node in `g`. -/
theorem eco_callOK {tabs : Tables} {f g : Func} {ce : CheckEnv} (hf : check ce f = .ok ())
    (hec : ecCheck tabs f g = true) {c : ID} {cu : Value}
    (hl : ∃ bid fb, (bid ∈ f.blocks ∧ f.block? bid = some fb) ∧ c ∈ fb.values)
    (hcu : f.value? c = some cu) (hcall : (callOpMap cu.op).isSome = true) :
    ∃ cw, g.value? c = some cw ∧ callOK tabs (typeShapes tabs) f g cu cw = true := by
  obtain ⟨-, -, -, hblk⟩ := eco_ecCheck hec
  obtain ⟨bid, fb, ⟨hbid, hfb⟩, hc⟩ := hl
  obtain ⟨-, -, -, hvals⟩ := eco_blockOK (hblk bid hbid) hfb
  have hcphi : cu.op ≠ .Phi := fun h => absurd hcall (by rw [h]; decide)
  have hvc := hvals _ hc cu hcu hcphi
  unfold valueOK at hvc
  rw [hcu] at hvc
  cases hcw : g.value? c with
  | none => rw [hcw] at hvc; cases hvc
  | some cw =>
    rw [hcw] at hvc
    dsimp only at hvc
    rw [ite_eq_left hcall] at hvc
    exact ⟨cw, rfl, hvc⟩

/-- **The local obligation of a non-`Phi` source value** of tree block `bid` for
`expand calls`, the source's `Held` values and the target's `HeldT` values holding their
evaluations (among them the `SP`s of a call's stack-argument stores, `hsp`, the `Dereference`
its `Move` copies, `hma`, and the `SP`s and memories of a stack-assigned result's loads, `hld`;
`hdep`: `x`, unless invalidated, depends in `g` on its arguments that are nodes of the block,
neither the `Dereference` of a `Move` nor wide call results). -/
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
    (hma : (callOpMap u.op).isSome = true → ∀ w, g.value? x = some w → ∀ a, ecMoveArg f g u w a →
      SrcArg f fb x a)
    (hdep : invalidated g x = false → frameDet f g x = false → ∀ a ∈ u.args, a ∈ fb.values →
      (∀ ua, f.value? a = some ua → ua.op ≠ .Phi) → moveArgB f g x a = false →
      wideSel f g a = false → invalidated g a = false →
      Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList) a x)
    (hld : ∀ l ∈ stackLoads tabs (typeShapes tabs) f g x,
      (isNewB f (loadSP g l) = false → HeldT g gb x (loadSP g l)) ∧
      (isNewB f (loadMem g l) = false → HeldT g gb x (loadMem g l)))
    (hsa : ∀ p ∈ selfAddrs tabs (typeShapes tabs) f g x, p ∈ fb.values →
      ¬ TgtInvalid g p ∧ SchedBefore g gb p x)
    (haddr : ∀ s ∈ addrSP tabs f g x, isNewB f s = false → HeldT g gb x s) :
    Obl tabs f g (ecCv tabs f g) (isNewB f) (ecFront f g x) (Held f g fb gb x) (HeldT g gb x) x := by
  have Wf := check_wf hf
  have Wg := check_wf hg
  have hcert : CertOK f := certOK_of_check (check_domCert hf)
  obtain ⟨hcfg, hown, hoo, hblk⟩ := eco_ecCheck hec
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
        (fun a h => .inr (.inr (.inr (hma hc w hw a h))))
    rw [ite_eq_right hc] at hv
    by_cases hr : (u.op == .MakeResult) = true
    · rw [ite_eq_left hr] at hv
      have hconv : converted f x = true := by
        unfold converted; rw [hu]; dsimp only; rw [hr, Bool.or_true]
      have hpl : Placed f x u :=
        ⟨hu, by rw [hublk]; exact hbid, fb, by rw [hublk]; exact hfb, hx⟩
      -- the self-moves' `Dereference`s and `LocalAddr`s are held in the source
      have hS : ∀ a, ecrSelfSrc tabs f g u a → Held f g fb gb x a := by
        rintro a ⟨e, he, hst, hsm, ha⟩
        obtain ⟨-, -, -, n, au, pu, -, hau, hop', hsz, -, -, -, hpu, hpop, -⟩ := ecr_selfMoveOK hsm
        have hea : e.2 ∈ u.args := by
          have h := (List.of_mem_zip he).2
          simp only [Array.toList_extract, List.extract_eq_take_drop, List.drop_zero] at h
          exact Array.mem_toList_iff.1 (List.mem_of_mem_take h)
        obtain ⟨va, ⟨hva, hvb, blk, hblk', hab⟩, hanc⟩ :=
          AtomSim.arg_anc Wf hcert hpl (by rw [hublk, ← hfid]; exact htree) hphi hea
        rw [hau] at hva
        cases hva
        rw [hublk, ← hfid] at hanc
        have hauph : au.op ≠ .Phi := by rw [hop']; decide
        rcases ha with rfl | rfl
        · by_cases haf : e.2 ∈ fb.values
          · exact .inr (.inr (.inr ⟨haf, ⟨u, hu, hea⟩, fun uz huz => by
              rw [hau] at huz; cases huz; exact hauph⟩))
          · refine .inr (.inl ⟨au, ⟨hau, hvb, blk, hblk', hab⟩, hauph, hanc, fun he' => haf ?_⟩)
            rw [he', hfid, hfb] at hblk'
            cases hblk'
            exact hab
        · have hpa : addrArg f e.2 = au.args[0]! := by unfold addrArg; rw [hau]; rfl
          rw [hpa]
          by_cases hpf : au.args[0]! ∈ fb.values
          · have hmem : au.args[0]! ∈ selfAddrs tabs (typeShapes tabs) f g x := by
              rw [← hpa]
              unfold selfAddrs
              rw [hu]
              simp only [beq_iff_eq.1 hr, beq_self_eq_true, ↓reduceIte]
              refine List.mem_map.2 ⟨e, List.mem_filter.2 ⟨?_, hsm⟩, rfl⟩
              unfold argPairs
              exact List.mem_filter.2 ⟨he, by simp [hst]⟩
            obtain ⟨hni, hsb⟩ := hsa _ hmem hpf
            exact .inr (.inr (.inl ⟨hpf, hni, not_frameX hpu (by rw [hpop]; decide), hsb⟩))
          · have hpl' : Placed f e.2 au := ⟨hau, hvb, blk, hblk', hab⟩
            have hp0 : au.args[0]! ∈ au.args := by
              rw [← Array.mem_toList_iff, ec_args_two hsz]
              simp
            obtain ⟨vp, ⟨hvp, hvpb, blkp, hblkp, habp⟩, hancp⟩ :=
              AtomSim.arg_anc Wf hcert hpl' (Anc.left hcert.parents hanc) hauph hp0
            rw [hpu] at hvp
            cases hvp
            refine .inr (.inl ⟨pu, ⟨hpu, hvpb, blkp, hblkp, habp⟩, by rw [hpop]; decide,
              Anc.trans hcert.parents hancp hanc, fun he' => hpf ?_⟩)
            rw [he', hfid, hfb] at hblkp
            cases hblkp
            exact habp
      exact obl_result hu hw (beq_iff_eq.1 hr) hv (ecr_ownOuts hoo) huid _ hLx hL (hH hconv) hS
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
    by_cases hws : wideSel f g x = true
    · exact obl_wideSel hws
    rw [ite_eq_right hws] at hv
    have hws' : wideSel f g x = false := Bool.eq_false_iff.2 hws
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
              · have hmv : moveArgB f g x u.args[0]! = false := by
                  unfold moveArgB stackMoves; rw [hu, hw]; dsimp only; rw [if_neg hc]; rfl
                exact .inl ⟨hcf, hdep hinv (frameDet_of_src hu (by rw [hsel]; decide)) _ hcmem hcf
                  (fun ua hua => by
                  rw [hcu] at hua; cases hua; exact hcphi) hmv
                  (ecA_not_wideSel hcu fun h => absurd hcall (by rw [h]; decide))
                  (ecA_callOK_facts hcw hvc).1⟩
              · have hpl : Placed f x u :=
                  ⟨hu, by rw [hublk]; exact hbid, fb, by rw [hublk]; exact hfb, hx⟩
                obtain ⟨va, ⟨hva, hvb, blk, hblk', hab⟩, hanc⟩ :=
                  AtomSim.arg_anc Wf hcert hpl (by rw [hublk, ← hfid]; exact htree) hphi hcmem
                rw [hcu] at hva
                cases hva
                rw [hublk, ← hfid] at hanc
                refine .inr (.inl ⟨cu, ⟨hcu, hvb, blk, hblk', hab⟩, hcphi, hanc, fun he => hcf ?_⟩)
                rw [he, hfid, hfb] at hblk'
                cases hblk'
                exact hab
            exact obl_selectStack hu hw hsel hargs hcu hcw hcall hvc hinv hws' hv hp hpst huid _
              hLx hL hHc hld
          · refine obl_select hu hw hsel hargs hcu hcw hcall hvc hinv hws' hv (fun p hp => ?_)
              hown huid _ hLx hL
            cases h : p.regs.isEmpty
            · rfl
            · exact absurd ⟨p, hp, h⟩ hstp
    rw [ite_eq_right hs] at hv
    by_cases hst : (u.op == .Store && w.op == .Copy) = true
    · rw [ite_eq_left hst] at hv
      obtain ⟨_, _, hwa, _, _, _, _, _, _, hzs, _⟩ := ecw_wideStoreOK hv
      obtain ⟨_, _, hus, _, _⟩ := ecw_wideChain hzs
      have ham : u.args[1]! ∈ u.args := ecw_mem_three hus 1 (by decide)
      obtain ⟨bid', fb', ⟨hbid', hfb'⟩, ha'⟩ := Wf.argListed bid fb x u ⟨⟨hbid, hfb⟩, hx, hu⟩ _ ham
      refine obl_wideStore hu hw huid hv (fun xu cu hxu hcu hcall => ?_) _ hLx hL ?_
      · obtain ⟨xu', _, hxu', _, _, hxsz, _, _⟩ := ecw_wideSel hwa
        rw [hxu] at hxu'
        cases hxu'
        have hc : xu.args[0]! ∈ xu.args := by
          rw [← Array.mem_toList_iff, ec_args_one hxsz]; simp
        exact eco_callOK hf hec (Wf.argListed bid' fb' _ xu ⟨⟨hbid', hfb'⟩, ha', hxu⟩ _ hc) hcu hcall
      · -- the wide result is held in the source
        obtain ⟨xu, -, hxu, -, hxop, -, -, -⟩ := ecw_wideSel hwa
        have hxphi : xu.op ≠ .Phi := by rw [hxop]; decide
        by_cases haf : u.args[1]! ∈ fb.values
        · exact .inr (.inr (.inr ⟨haf, ⟨u, hu, ham⟩, fun uz huz => by
            rw [hxu] at huz; cases huz; exact hxphi⟩))
        · have hpl : Placed f x u :=
            ⟨hu, by rw [hublk]; exact hbid, fb, by rw [hublk]; exact hfb, hx⟩
          obtain ⟨va, ⟨hva, hvb, blk, hblk', hab⟩, hanc⟩ :=
            AtomSim.arg_anc Wf hcert hpl (by rw [hublk, ← hfid]; exact htree) hphi ham
          rw [hxu] at hva
          cases hva
          rw [hublk, ← hfid] at hanc
          refine .inr (.inl ⟨xu, ⟨hxu, hvb, blk, hblk', hab⟩, hxphi, hanc, fun he => haf ?_⟩)
          rw [he, hfid, hfb] at hblk'
          cases hblk'
          exact hab
    rw [ite_eq_right hst] at hv
    by_cases hi : (w.op == .Invalid) = true
    · rw [ite_eq_left hi] at hv
      simp only [Bool.and_eq_true, beq_iff_eq] at hv
      exact obl_invalid hu hw (beq_iff_eq.1 hi) hv.1
    rw [ite_eq_right hi] at hv
    have hinv : invalidated g x = false := by
      unfold invalidated; rw [hw]; exact Bool.eq_false_iff.2 hi
    have hwid : w.id = x := (hL x hLx w hw).1
    have hsp : special f g x = false := by
      unfold special converted
      rw [hu, hinv, hws']
      dsimp only
      rw [Bool.eq_false_iff.2 hc, Bool.eq_false_iff.2 hr]
      rfl
    by_cases hsel : selAddr tabs f u = true
    · -- a result address: its call is held in the source, the `SP` under it in the target
      rw [if_pos hsel] at hv
      have hsel' := hsel
      unfold selAddr at hsel'
      simp only [Bool.and_eq_true, beq_iff_eq] at hsel'
      obtain ⟨⟨hop, hsz⟩, hso⟩ := hsel'
      obtain ⟨p, hst⟩ := Option.isSome_iff_exists.1 hso
      obtain ⟨cu, hcu, hcall, -, -, -⟩ := ecr_stackOut hst
      have hargs : u.args.toList = [u.args[0]!] := ec_args_one hsz
      have hcmem : u.args[0]! ∈ u.args :=
        Array.mem_toList_iff.1 (by rw [hargs]; exact List.mem_singleton_self _)
      obtain ⟨cw, hcw, hcok⟩ :=
        eco_callOK hf hec (Wf.argListed bid fb x u ⟨⟨hbid, hfb⟩, hx, hu⟩ _ hcmem) hcu hcall
      have hcphi : cu.op ≠ .Phi := fun h => absurd hcall (by rw [h]; decide)
      have hHc : Held f g fb gb x u.args[0]! := by
        by_cases hcf : u.args[0]! ∈ fb.values
        · exact .inr (.inr (.inr ⟨hcf, ⟨u, hu, hcmem⟩, fun uz huz => by
            rw [hcu] at huz; cases huz; exact hcphi⟩))
        · have hpl : Placed f x u :=
            ⟨hu, by rw [hublk]; exact hbid, fb, by rw [hublk]; exact hfb, hx⟩
          obtain ⟨va, ⟨hva, hvb, blk, hblk', hab⟩, hanc⟩ :=
            AtomSim.arg_anc Wf hcert hpl (by rw [hublk, ← hfid]; exact htree) hphi hcmem
          rw [hcu] at hva
          cases hva
          rw [hublk, ← hfid] at hanc
          refine .inr (.inl ⟨cu, ⟨hcu, hvb, blk, hblk', hab⟩, hcphi, hanc, fun he => hcf ?_⟩)
          rw [he, hfid, hfb] at hblk'
          cases hblk'
          exact hab
      exact obl_selAddr hu hw huid hop hargs hsel hst hcw hcok hcu hv hsp _ hLx hL hHc haddr
    rw [if_neg hsel] at hv
    by_cases ha : (u.op == .Arg && !identOK f g u w) = true
    · rw [ite_eq_left ha] at hv
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at ha
      exact obl_arg hu hw ha.1 hinv ha.2 hv hown huid _ hLx hL
    rw [ite_eq_right ha] at hv
    exact obl_ident hu hw huid hwid hv hsp hown

end GoFV.Proof.EC

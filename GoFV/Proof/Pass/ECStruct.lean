import GoFV.Proof.Pass.ECDefs
import GoFV.Proof.Merge
import GoFV.Proof.Avail
import GoFV.Proof.CheckFacts

/-!
# `expand calls`: the structural soundness of `blockOK` (issue #28)

A block accepted by `GoFV.Opt.ECCheck.blockOK` satisfies every field of `CvBlock` for the
conversion of `expand calls` (`ecCv`, `isNewB`, `ecFront`) except the local obligations `obl` and
the `Ret` field `ret` (`ecs_block` takes them as hypotheses): `ecs_parts` reads the checker's
conjuncts, `ecs_depB_dep` turns its dependency search `depB` into `Order.Dep` over the target's
schedule nodes, `newEval_of_newEvalB` gives `NewEval` of the new values' ops, and `ecs_imk` the
facts of the `IMake` arguments of converted values.
-/

namespace GoFV.Proof.EC

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.ECCheck GoFV.Proof.Order GoFV.SSA.DomCert

/-- The checker's nodes of block `b` of `f` (`blockOK`'s `nodeF`/`nodeG`): its non-`Phi`
values. -/
def ecs_node (f : Func) (b : Block) (x : ID) : Bool :=
  b.values.contains x &&
    match f.value? x with
    | some w => w.op != .Phi
    | none => false

theorem ecs_node_iff {f : Func} {b : Block} {x : ID} :
    ecs_node f b x = true ↔ x ∈ b.values ∧ ∃ w, f.value? x = some w ∧ w.op ≠ .Phi := by
  unfold ecs_node
  rw [Bool.and_eq_true, Array.contains_iff_mem]
  cases hx : f.value? x with
  | none => simp
  | some w => simp

theorem ecs_nodeIn {f : Func} {b : Block} (hown : ValuesOwn f b) {x : ID} :
    ecs_node f b x = true ↔ NodeIn (schedNodes f b).toList x := by
  rw [ecs_node_iff, nodeIn_schedNodes hown]

/-- The conjuncts of `blockOK`. -/
structure ecs_Parts (tabs : Tables) (sh : Array Ty) (f g : Func) (fb gb : Block) : Prop where
  kind : gb.kind = fb.kind
  controls : gb.controls = fb.controls
  common : ∀ x ∈ fb.values, x ∈ gb.values
  fresh : ∀ x ∈ gb.values, x ∈ fb.values ∨ isNewB f x = true
  phiT : ∀ x ∈ gb.values, ∀ w, g.value? x = some w → w.op = .Phi →
    x ∈ fb.values ∧ ∃ u, f.value? x = some u ∧ sameV u w = true
  phiS : ∀ x ∈ fb.values, ∀ u, f.value? x = some u → u.op = .Phi →
    (∃ w, g.value? x = some w ∧ sameV u w = true) ∧ special f g x = false ∧
      ∀ a ∈ u.args, special f g a = false
  sched : ∃ of og, schedule f fb = some of ∧ schedule g gb = some og ∧
    of.toList.filter (npOf f fb) = og.toList.filter (npOf f fb)
  reach : ∀ y ∈ fb.values, ecs_node f fb y = true → ∀ u, f.value? y = some u → ∀ a ∈ u.args,
    ecs_node f fb a = true →
      ecs_node g gb a = true ∧ depB g (ecs_node g gb) (isNewB f) (gb.values.size + 1) a y = true
  value : ∀ x ∈ fb.values, ∀ u, f.value? x = some u → u.op ≠ .Phi → valueOK tabs sh f g x = true
  imk : ∀ x ∈ fb.values, converted f x = true → ∀ u, f.value? x = some u → ∀ a ∈ u.args,
    imkArgOK sh f g fb (ecs_node g gb) (gb.values.size + 1) a x = true
  ctrl : fb.kind = .If ∨ fb.kind = .JumpTable → ∀ c ∈ fb.controls, special f g c = false
  ret : fb.kind = .Ret → ∃ c u, fb.controls[0]? = some c ∧ f.value? c = some u ∧ u.op = .MakeResult
  newv : ∀ z ∈ gb.values, ∀ w, g.value? z = some w →
    (isNewB f z = true → w.op ≠ .Phi ∧ newEvalB tabs g w = true) ∧
      ∀ a ∈ w.args, isNewB f a = true → a ∈ gb.values ∨ a ∈ valsOf g g.entry

theorem ecs_parts {tabs : Tables} {sh : Array Ty} {f g : Func} {bid : ID} {fb gb : Block}
    (hfb : f.block? bid = some fb) (hgb : g.block? bid = some gb)
    (hb : blockOK tabs sh f g bid = true) : ecs_Parts tabs sh f g fb gb := by
  unfold blockOK at hb
  rw [hfb, hgb] at hb
  simp only [Bool.and_eq_true, and_assoc] at hb
  obtain ⟨hk, hc, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hb
  have h6' : ∀ y ∈ fb.values, (!ecs_node f fb y ||
      match f.value? y with
      | some u => u.args.all fun a => !ecs_node f fb a ||
          (ecs_node g gb a && depB g (ecs_node g gb) (isNewB f) (gb.values.size + 1) a y)
      | none => false) = true := Array.all_eq_true'.1 h6
  have h8' : ∀ x ∈ fb.values, (!converted f x ||
      match f.value? x with
      | some u => u.args.all fun a => imkArgOK sh f g fb (ecs_node g gb) (gb.values.size + 1) a x
      | none => true) = true := Array.all_eq_true'.1 h8
  refine ⟨beq_iff_eq.1 hk, beq_iff_eq.1 hc,
    fun x hx => Array.contains_iff_mem.1 (Array.all_eq_true'.1 h1 x hx), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro x hx
    have := Array.all_eq_true'.1 h2 x hx
    rw [Bool.or_eq_true, Array.contains_iff_mem] at this
    exact this
  · intro x hx w hw hph
    have := Array.all_eq_true'.1 h3 x hx
    rw [hw] at this; dsimp only at this
    rw [hph, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, Array.contains_iff_mem] at this
    obtain ⟨hxf, hm⟩ := this
    refine ⟨hxf, ?_⟩
    cases hu : f.value? x with
    | none => rw [hu] at hm; dsimp only at hm; cases hm
    | some u => rw [hu] at hm; dsimp only at hm; exact ⟨u, rfl, hm⟩
  · intro x hx u hu hph
    have := Array.all_eq_true'.1 h4 x hx
    rw [hu] at this; dsimp only at this
    rw [hph, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, Bool.and_eq_true,
      Bool.not_eq_true', Array.all_eq_true'] at this
    obtain ⟨⟨hm, hs⟩, ha⟩ := this
    refine ⟨?_, hs, fun a ha' => by have := ha a ha'; rwa [Bool.not_eq_true'] at this⟩
    cases hw : g.value? x with
    | none => rw [hw] at hm; dsimp only at hm; cases hm
    | some w => rw [hw] at hm; dsimp only at hm; exact ⟨w, rfl, hm⟩
  · split at h5
    · rename_i of og hof hog
      exact ⟨of, og, hof, hog, beq_iff_eq.1 h5⟩
    · cases h5
  · intro y hy hny u hu a ha hna
    have := h6' y hy
    rw [hny, Bool.not_true, Bool.false_or, hu] at this; dsimp only at this
    rw [Array.all_eq_true'] at this
    have := this a ha
    rw [hna, Bool.not_true, Bool.false_or, Bool.and_eq_true] at this
    exact this
  · intro x hx u hu hph
    have := Array.all_eq_true'.1 h7 x hx
    rw [hu] at this; dsimp only at this
    rw [Bool.or_eq_true, beq_iff_eq] at this
    exact this.resolve_left hph
  · intro x hx hcv u hu a ha
    have := h8' x hx
    rw [hcv, Bool.not_true, Bool.false_or, hu] at this; dsimp only at this
    rw [Array.all_eq_true'] at this
    exact this a ha
  · intro hk' c hc'
    have h9' : (fb.kind != .If && fb.kind != .JumpTable) = false := by
      rcases hk' with h | h <;> rw [h] <;> decide
    rw [h9', Bool.false_or, Array.all_eq_true'] at h9
    have := h9 c hc'
    rwa [Bool.not_eq_true'] at this
  · intro hk'
    rw [hk', bne_self_eq_false, Bool.false_or] at h10
    split at h10
    · rename_i c hc0
      cases hu : f.value? c with
      | none => rw [hu] at h10; dsimp only at h10; cases h10
      | some u => rw [hu] at h10; dsimp only at h10; rw [beq_iff_eq] at h10; exact ⟨c, u, hc0, hu, h10⟩
    · cases h10
  · intro z hz w hw
    have := Array.all_eq_true'.1 h11 z hz
    rw [hw] at this; dsimp only at this
    rw [Bool.and_eq_true, Array.all_eq_true'] at this
    obtain ⟨hn, ha⟩ := this
    refine ⟨fun hzn => ?_, fun a ha' han => ?_⟩
    · rw [hzn, Bool.not_true, Bool.false_or, Bool.and_eq_true, bne_iff_ne] at hn
      exact hn
    · have := ha a ha'
      rw [han, Bool.not_true, Bool.false_or, Bool.or_eq_true, Array.contains_iff_mem,
        Array.contains_iff_mem] at this
      exact this

/-- **`depB` is a dependency** through the block's schedule nodes. -/
theorem ecs_depB_dep {g : Func} {gb : Block} (hown : ValuesOwn g gb)
    (hnd : gb.values.toList.Nodup) {nw : ID → Bool} :
    ∀ {n : Nat} {a y : ID}, depB g (ecs_node g gb) nw n a y = true →
      Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList) a y
  | 0, _, _, h => by rw [depB] at h; cases h
  | n + 1, a, y, h => by
    rw [depB, Bool.and_eq_true] at h
    obtain ⟨hy, h⟩ := h
    obtain ⟨hyb, w, hw, hph⟩ := ecs_node_iff.1 hy
    rw [hw] at h; dsimp only at h
    rw [Array.any_eq_true'] at h
    obtain ⟨z, hz, h⟩ := h
    rw [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at h
    obtain ⟨hzn, h⟩ := h
    have hyN := (ecs_nodeIn hown).1 hy
    have hzN := (ecs_nodeIn hown).1 hzn
    have hzy : z ∈ argsOf (schedNodes g gb).toList y := by
      rw [argsOf_schedNodes hown hnd hyb hw hph]; exact Array.mem_toList_iff.2 hz
    rcases h with rfl | ⟨-, h⟩
    · exact .arg hzN hyN hzy
    · exact .trans (ecs_depB_dep hown hnd h) (.arg hzN hyN hzy)

/-- An interface shape is a type word and a pointer. -/
theorem ecs_ifaceShape {t : Ty} (h : ifaceShape t = true) :
    ∃ f0 o e n, t = .agg [f0, (o, .ptr e)] n := by
  unfold ifaceShape at h
  split at h
  · exact ⟨_, _, _, _, rfl⟩
  · cases h

/-! ## `NewEval` of the new values -/

theorem ecs_params_toList (tabs : Tables) (g : Func) :
    (Ctx.make tabs g).params.toList = paramNames tabs g := by
  simp [Ctx.make, paramNames]

/-- A parameter's piece reads the parameter's image. -/
theorem ecs_argVal_ok {tabs : Tables} {g : Func} {fr : Frame} {n : AuxRef} (off : Int) (ty : Ty)
    (hn : (paramNames tabs g).contains (some n) = true)
    (himg : fr.images.size = (Ctx.make tabs g).params.size) :
    ∃ y, argVal (Ctx.make tabs g) fr n off ty = .ok y := by
  have hm : some n ∈ (Ctx.make tabs g).params := by
    rw [← Array.mem_toList_iff, ecs_params_toList]; exact List.contains_iff_mem.1 hn
  have hs : ((Ctx.make tabs g).params.findIdx? (· == some n)).isSome := by
    rw [Array.findIdx?_isSome, Array.any_eq_true']
    exact ⟨_, hm, beq_self_eq_true _⟩
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 hs
  have hlt : i < fr.images.size := himg ▸ (Array.findIdx?_eq_some_iff_findIdx_eq.1 hi).1
  unfold argVal
  rw [hi]
  simp only [Array.getElem?_eq_getElem hlt]
  split <;> exact ⟨_, rfl⟩

/-- **`NewEval` of the ops `newEvalB` accepts.** -/
theorem newEval_of_newEvalB {tabs : Tables} {g : Func} {w : Value} (h : newEvalB tabs g w = true) :
    NewEval tabs g w := by
  intro env fr argv himg
  unfold newEvalB at h
  split at h
  · rename_i hop
    unfold evalOp
    rw [hop]
    dsimp only
    rw [show (Ctx.make tabs g).tabs = tabs from rfl]
    split at h
    · rename_i n _ heq
      rw [heq]
      exact ecs_argVal_ok _ _ h himg
    · exact absurd h Bool.false_ne_true
  · rename_i hop
    unfold evalOp
    rw [hop]
    dsimp only
    split at h
    · rename_i n heq
      rw [heq]
      exact ecs_argVal_ok _ _ h himg
    · exact absurd h Bool.false_ne_true
  all_goals first
    | exact absurd h Bool.false_ne_true
    | rename_i hop
      unfold evalOp
      rw [hop]
      dsimp only
      first
        | exact ⟨_, rfl⟩
        | cases frameVal (Ctx.make tabs g) w with
          | some x => exact ⟨x, rfl⟩
          | none => exact ⟨_, ite_eq_right (by decide)⟩

/-! ## The fields of `CvBlock` -/

theorem ecs_phiSame {u w : Value} (h : sameV u w = true) : PhiSame u w := by
  unfold sameV at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- Per non-`Phi` value of an accepted block, the class check `valueOK`. -/
theorem ecs_valueOK {tabs : Tables} {f g : Func} {bid : ID} {fb gb : Block}
    (hfb : f.block? bid = some fb) (hgb : g.block? bid = some gb)
    (hb : blockOK tabs (typeShapes tabs) f g bid = true) :
    ∀ x ∈ fb.values, ∀ u, f.value? x = some u → u.op ≠ .Phi →
      valueOK tabs (typeShapes tabs) f g x = true :=
  (ecs_parts hfb hgb hb).value

/-- **The `IMake` arguments of converted values** (`imkArgOK`): source mode (the same
interface-shaped `IMake` in `f`, its data operand unconverted and a pointer or an aggregate in
both, `x` depending on it in `gb` when it is a value of `fb`) or target mode (interface-shaped in
`g`, `x` depending on it and on its data operand in `gb`). -/
theorem ecs_imk {tabs : Tables} {ce' : CheckEnv} {f g : Func} {bid : ID} {fb gb : Block}
    (hwg : WF ce' g) (hbg : bid ∈ g.blocks)
    (hfb : f.block? bid = some fb) (hgb : g.block? bid = some gb)
    (hb : blockOK tabs (typeShapes tabs) f g bid = true) :
    ∀ x ∈ fb.values, converted f x = true → ∀ u, f.value? x = some u → ∀ a ∈ u.args,
      EcImkOK tabs f g fb gb x a := by
  intro x hx hcv u hu a ha
  unfold EcImkOK
  intro aw haw hop
  have hown := valuesOwn hwg hbg hgb
  have hnd := hwg.valuesNodup bid gb ⟨hbg, hgb⟩
  have := (ecs_parts hfb hgb hb).imk x hx hcv u hu a ha
  unfold imkArgOK at this
  rw [haw] at this; dsimp only at this
  rw [hop, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at this
  obtain ⟨hsz, hm⟩ := this
  refine ⟨hsz, ?_⟩
  rcases hm with hsrc | htgt
  · unfold imkSrcOK at hsrc
    obtain ⟨au, hau⟩ : ∃ au, f.value? a = some au := by
      cases h : f.value? a with
      | none => rw [h] at hsrc; dsimp only at hsrc; cases hsrc
      | some au => exact ⟨au, rfl⟩
    rw [hau] at hsrc; dsimp only at hsrc
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.or_eq_true] at hsrc
    obtain ⟨⟨⟨⟨⟨⟨hop', hsz'⟩, hd⟩, hi⟩, hsp⟩, hshape⟩, hdep⟩ := hsrc
    have hsh : (∃ e e', shapeOf (typeShapes tabs) f aw.args[1]! = .ptr e ∧
          shapeOf (typeShapes tabs) g aw.args[1]! = .ptr e') ∨
        (∃ fs n fs' n', shapeOf (typeShapes tabs) f aw.args[1]! = .agg fs n ∧
          shapeOf (typeShapes tabs) g aw.args[1]! = .agg fs' n') := by
      split at hshape
      · rename_i e e' h1 h2; exact .inl ⟨e, e', h1, h2⟩
      · rename_i fs n fs' n' h1 h2; exact .inr ⟨fs, n, fs', n', h1, h2⟩
      · cases hshape
    refine .inl ⟨au, hau, hop', hsz', hd, hi, hsp, hsh, fun hafb => ?_⟩
    rcases hdep with hc | hd'
    · rw [Array.contains_iff_mem.2 hafb] at hc; cases hc
    · exact ecs_depB_dep hown hnd hd'
  · unfold imkTgtOK at htgt
    rw [Bool.and_eq_true, Bool.and_eq_true] at htgt
    obtain ⟨⟨hi, h1⟩, h2⟩ := htgt
    exact .inr ⟨hi, ecs_depB_dep hown hnd h1, ecs_depB_dep hown hnd h2⟩

/-- **The structural soundness of `blockOK`**: an accepted block satisfies `CvBlock` for the
conversion of `expand calls`, given its local obligations (`obl`) and its `Ret` field (`ret`). -/
theorem ecs_block {tabs : Tables} {ce ce' : CheckEnv} {f g : Func} {bid : ID} {fb gb : Block}
    (hwf : WF ce f) (hwg : WF ce' g) (hcfg : cfgView g = cfgView f) (hbm : bid ∈ f.blocks)
    (hfb : f.block? bid = some fb) (hgb : g.block? bid = some gb)
    (hb : blockOK tabs (typeShapes tabs) f g bid = true)
    (hobl : ((make f).depthOf fb.id).isSome → ∀ x ∈ fb.values, ∀ u, f.value? x = some u →
      u.op ≠ .Phi → Obl tabs f g (ecCv tabs f g) (isNewB f) (ecFront f g x) (Held f g fb gb x)
        (fun z => Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList) z x) x)
    (hret : fb.kind = .Ret → ∀ c, fb.controls[0]? = some c → ∀ y y', RegOK (Ctx.make tabs f) c y →
      Sem.Refines (ecCv tabs f g c y) y' →
      ∀ rs m, retOf y = some (rs, m) → Val.anyPoison rs = false →
        ∃ rs' m', retOf y' = some (rs', m') ∧ ecRR tabs f rs m rs' m') :
    CvBlock tabs f g (ecCv tabs f g) (isNewB f) (ecFront f g) (ecRR tabs f) fb gb := by
  have P := ecs_parts hfb hgb hb
  have hbg : bid ∈ g.blocks := by
    have hbl : (cfgView g).blocks = (cfgView f).blocks := congrArg Func.blocks hcfg
    have h : bid ∈ (cfgView f).blocks := hbm
    rw [← hbl] at h; exact h
  have hownF := valuesOwn hwf hbm hfb
  have hndF := hwf.valuesNodup bid fb ⟨hbm, hfb⟩
  have hownG := valuesOwn hwg hbg hgb
  have hndG := hwg.valuesNodup bid gb ⟨hbg, hgb⟩
  have hdefF : ∀ x ∈ fb.values, isNewB f x = false := fun x hx => by
    obtain ⟨v, hv, -, -⟩ := hwf.valueId bid fb ⟨hbm, hfb⟩ x hx
    unfold isNewB; rw [hv]; rfl
  have hdefG : ∀ x ∈ gb.values, ∃ w, g.value? x = some w := fun x hx => by
    obtain ⟨v, hv, -, -⟩ := hwg.valueId bid gb ⟨hbg, hgb⟩ x hx
    exact ⟨v, hv⟩
  refine
    { kind := P.kind
      controls := P.controls
      common := fun x hx => ⟨P.common x hx, hdefF x hx⟩
      fresh := fun x hx hn => (P.fresh x hx).resolve_left hn
      phiT := fun x hx w hw hph => by
        obtain ⟨hxf, u, hu, hs⟩ := P.phiT x hx w hw hph
        exact ⟨hxf, u, hu, ecs_phiSame hs⟩
      phiS := fun x hx u hu hph => by
        obtain ⟨⟨w, hw, hs⟩, hsx, hsa⟩ := P.phiS x hx u hu hph
        exact ⟨⟨w, hw, ecs_phiSame hs⟩, ecCv_of_not_special hsx,
          fun a ha => ecCv_of_not_special (hsa a ha)⟩
      sched := by
        obtain ⟨of, og, hof, hog, he⟩ := P.sched
        rw [npIn_schedNodes hownF hndF]
        exact ⟨of, og, hof, hog, he⟩
      feeds := fun a y ha hy hay _ => by
        obtain ⟨hyb, u, hu, hph⟩ := (nodeIn_schedNodes hownF).1 hy
        rw [argsOf_schedNodes hownF hndF hyb hu hph] at hay
        obtain ⟨hna, hd⟩ := P.reach y hyb ((ecs_nodeIn hownF).2 hy) u hu a
          (Array.mem_toList_iff.1 hay) ((ecs_nodeIn hownF).2 ha)
        exact .direct ((ecs_nodeIn hownG).1 hna) (ecs_depB_dep hownG hndG hd)
      obl := hobl
      front := fun x hx u hu hph a ha => ?_
      ctrl := fun hk c hc => ecCv_of_not_special (P.ctrl hk c hc)
      ret := hret
      newOK := fun z hz hn w hw => by
        obtain ⟨hph, he⟩ := (P.newv z hz w hw).1 hn
        exact ⟨hph, newEval_of_newEvalB he⟩
      newArgs := fun z hz w hw a ha hn => by
        rcases (P.newv z hz w hw).2 a ha hn with h | h
        · exact .inl h
        · right
          unfold valsOf at h
          cases he : g.block? g.entry with
          | none => rw [he] at h; simp at h
          | some eb => rw [he] at h; exact ⟨eb, he, h⟩ }
  have hxg := P.common x hx
  obtain ⟨w, hw⟩ := hdefG x hxg
  unfold ecFront at ha
  rw [hu, hw] at ha
  simp only [Option.map_some, Option.getD_some, List.mem_append, List.mem_filter,
    Bool.not_eq_true'] at ha
  rcases ha with ha | ⟨ha, han⟩
  · obtain ⟨bid', b', hB', hab'⟩ := hwf.argListed bid fb x u ⟨⟨hbm, hfb⟩, hx, hu⟩ a
      (Array.mem_toList_iff.1 ha)
    obtain ⟨ua, hua, -, -⟩ := hwf.valueId bid' b' hB' a hab'
    have han : isNewB f a = false := by unfold isNewB; rw [hua]; rfl
    refine ⟨han, fun hag => ?_⟩
    have haf : a ∈ fb.values :=
      (P.fresh a hag).resolve_right (by rw [han]; exact Bool.false_ne_true)
    by_cases hpa : ua.op = .Phi
    · obtain ⟨⟨wa, hwa, hs⟩, -⟩ := P.phiS a haf ua hua hpa
      exact .inl ⟨wa, hwa, (ecs_phiSame hs).1.trans hpa⟩
    · obtain ⟨-, hd⟩ := P.reach x hx (ecs_node_iff.2 ⟨hx, u, hu, hph⟩) u hu a
        (Array.mem_toList_iff.1 ha) (ecs_node_iff.2 ⟨haf, ua, hua, hpa⟩)
      exact .inr (ecs_depB_dep hownG hndG hd)
  · refine ⟨han, fun hag => ?_⟩
    obtain ⟨wa, hwa⟩ := hdefG a hag
    by_cases hpa : wa.op = .Phi
    · exact .inl ⟨wa, hwa, hpa⟩
    · have hwph : w.op ≠ .Phi := fun hp => by
        obtain ⟨-, u', hu', hs⟩ := P.phiT x hxg w hw hp
        rw [hu] at hu'; cases hu'
        exact hph ((ecs_phiSame hs).1.symm.trans hp)
      have hxN := (nodeIn_schedNodes hownG).2 ⟨hxg, w, hw, hwph⟩
      have haN := (nodeIn_schedNodes hownG).2 ⟨hag, wa, hwa, hpa⟩
      refine .inr (.arg haN hxN ?_)
      rw [argsOf_schedNodes hownG hndG hxg hw hwph]
      exact ha

end GoFV.Proof.EC

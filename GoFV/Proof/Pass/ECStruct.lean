import GoFV.Proof.Pass.ECCall
import GoFV.Proof.Merge
import GoFV.Proof.Avail
import GoFV.Proof.CheckFacts
import GoFV.Proof.Pass.CSEOp

/-!
# `expand calls`: the structural soundness of `blockOK` (issue #28)

A block accepted by `GoFV.Opt.ECCheck.blockOK` satisfies every field of `CvBlock` for the
conversion of `expand calls` (`ecCv`, `isNewB`, `ecFront`) except the local obligations `obl` and
the `Ret` field `ret` (`ecs_block` takes them as hypotheses): `ecs_parts` reads the checker's
conjuncts, `ecs_depB_dep` turns its dependency search `depB` into `Order.Dep` over the target's
schedule nodes, `newEval_of_newEvalB` gives `NewEval` of the new values' ops, `ecs_anchored`
anchors the stack-argument stores at their calls (`AnchoredAt`: `ecc_storeObl`, `gapOK` read by
`ecs_gap`), `ecs_spHeld` holds the `SP`s under them when the call is evaluated, and `ecs_imk` the
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
structure ecs_Parts (tabs : Tables) (sh : Array Ty) (anc : ID → ID → Bool) (f g : Func)
    (fb gb : Block) : Prop where
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
  reach : ∀ y ∈ fb.values, ecs_node f fb y = true → invalidated g y = false →
    ∀ u, f.value? y = some u → ∀ a ∈ u.args, ecs_node f fb a = true →
      (ecs_node g gb a = true ∧
        (depB g (ecs_node g gb) (isNewB f) (gb.values.size + 1) a y = true ∨
          depB g (ecs_node g gb) (fun _ => true) (gb.values.size + 1) a y = true)) ∨
      (moveArgB f g y a = true ∧
        throughB f g (ecs_node f fb) (ecs_node g gb) (gb.values.size + 1) a y = true)
  invArgs : ∀ z ∈ gb.values, ∀ w, g.value? z = some w → w.op ≠ .Phi → ∀ a ∈ w.args,
    invalidated g a = false
  value : ∀ x ∈ fb.values, ∀ u, f.value? x = some u → u.op ≠ .Phi → valueOK tabs sh f g x = true
  imk : ∀ x ∈ fb.values, converted f x = true → ∀ u, f.value? x = some u → ∀ a ∈ u.args,
    imkArgOK sh f g anc fb (ecs_node g gb) (gb.values.size + 1) a x = true
  ctrl : fb.kind = .If ∨ fb.kind = .JumpTable → ∀ c ∈ fb.controls, special f g c = false
  ret : fb.kind = .Ret → ∃ c u, fb.controls[0]? = some c ∧ f.value? c = some u ∧ u.op = .MakeResult
  stack : ∃ og, schedule g gb = some og ∧ ∀ x ∈ fb.values, (∀ z ∈ stackStores f g x,
    z ∈ gb.values ∧ gapOK (npOf f fb) og.toList z x = true ∧
    (isNewB f (storeSP g z) = true ∨ placedSDom g anc fb.id (storeSP g z) = true ∨
      depB g (ecs_node g gb) (fun _ => true) (gb.values.size + 1) (storeSP g z) z = true) ∧
    (callMem f x ∈ gb.values → ∀ v, g.value? (callMem f x) = some v → v.op ≠ .Phi →
      depB g (ecs_node g gb) (fun _ => true) (gb.values.size + 1) (callMem f x) z = true)) ∧
    ∀ u, f.value? x = some u → ∀ a ∈ u.args, moveArgB f g x a = true →
      a ∈ fb.values ∧ beforeB og.toList a x = true
  loads : ∀ x ∈ fb.values, ∀ l ∈ stackLoads tabs sh f g x,
    (isNewB f (loadSP g l) = true ∨ placedSDom g anc fb.id (loadSP g l) = true ∨
      depB g (ecs_node g gb) (fun _ => true) (gb.values.size + 1) (loadSP g l) x = true) ∧
    (isNewB f (loadMem g l) = true ∨ placedSDom g anc fb.id (loadMem g l) = true ∨
      depB g (ecs_node g gb) (fun _ => true) (gb.values.size + 1) (loadMem g l) x = true)
  newv : ∀ z ∈ gb.values, ∀ w, g.value? z = some w →
    (isNewB f z = true → w.op ≠ .Phi ∧
      (newEvalB tabs g w = true ∨ ∃ x ∈ fb.values, z ∈ stackStores f g x)) ∧
      ∀ a ∈ w.args, isNewB f a = true →
        a ∈ gb.values ∨ a ∈ valsOf g g.entry ∨ placedSDom g anc fb.id a = true

theorem ecs_parts {tabs : Tables} {sh : Array Ty} {anc : ID → ID → Bool} {f g : Func} {bid : ID}
    {fb gb : Block} (hfb : f.block? bid = some fb) (hgb : g.block? bid = some gb)
    (hb : blockOK tabs sh anc f g bid = true) : ecs_Parts tabs sh anc f g fb gb := by
  unfold blockOK at hb
  rw [hfb, hgb] at hb
  simp only [Bool.and_eq_true, and_assoc] at hb
  obtain ⟨hk, hc, h1, h2, h3, h4, h5, h6, h6b, h7, h8, h9, h10, hst, hld, h11⟩ := hb
  have h6' : ∀ y ∈ fb.values, (!ecs_node f fb y || invalidated g y ||
      match f.value? y with
      | some u => u.args.all fun a => !ecs_node f fb a ||
          (ecs_node g gb a && (depB g (ecs_node g gb) (isNewB f) (gb.values.size + 1) a y ||
            depB g (ecs_node g gb) (fun _ => true) (gb.values.size + 1) a y)) ||
          (moveArgB f g y a &&
            throughB f g (ecs_node f fb) (ecs_node g gb) (gb.values.size + 1) a y)
      | none => false) = true := Array.all_eq_true'.1 h6
  have h8' : ∀ x ∈ fb.values, (!converted f x ||
      match f.value? x with
      | some u => u.args.all fun a => imkArgOK sh f g anc fb (ecs_node g gb) (gb.values.size + 1) a x
      | none => true) = true := Array.all_eq_true'.1 h8
  refine ⟨beq_iff_eq.1 hk, beq_iff_eq.1 hc,
    fun x hx => Array.contains_iff_mem.1 (Array.all_eq_true'.1 h1 x hx), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro y hy hny hiy u hu a ha hna
    have := h6' y hy
    rw [hny, hiy, Bool.not_true, Bool.false_or, Bool.false_or, hu] at this; dsimp only at this
    rw [Array.all_eq_true'] at this
    have := this a ha
    rw [hna, Bool.not_true, Bool.false_or] at this
    simp only [Bool.or_eq_true, Bool.and_eq_true] at this
    exact this
  · intro z hz w hw hph a ha
    have := Array.all_eq_true'.1 h6b z hz
    rw [hw] at this; dsimp only at this
    rw [Bool.or_eq_true, beq_iff_eq, Array.all_eq_true'] at this
    have := (this.resolve_left hph) a ha
    rwa [Bool.not_eq_true'] at this
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
  · split at hst
    · rename_i og hog
      refine ⟨og, hog, fun x hx => ?_⟩
      have hx' := Array.all_eq_true'.1 hst x hx
      rw [Bool.and_eq_true] at hx'
      obtain ⟨hzs, hma⟩ := hx'
      refine ⟨fun z hz => ?_, fun u hu a ha hma' => ?_⟩
      · have := List.all_eq_true.1 hzs z hz
        simp only [Bool.and_eq_true, Bool.or_eq_true, Array.contains_iff_mem] at this
        obtain ⟨⟨⟨hzm, hgap⟩, hsp⟩, hcm⟩ := this
        refine ⟨hzm, hgap, ?_, fun hin => ?_⟩
        · rcases hsp with (h | h) | h
          · exact .inl h
          · exact .inr (.inl h)
          · exact .inr (.inr h)
        · intro v hv hpa
          rcases hcm with (h | h) | h
          · simp at h; exact absurd hin h
          · rw [hv] at h
            simp [hpa] at h
            exact absurd hin h
          · exact h
      · rw [hu] at hma; dsimp only at hma
        have := Array.all_eq_true'.1 hma a ha
        rw [hma', Bool.not_true, Bool.false_or, Bool.and_eq_true, Array.contains_iff_mem] at this
        exact this
    · cases hst
  · intro x hx l hl
    have := List.all_eq_true.1 (Array.all_eq_true'.1 hld x hx) l hl
    simp only [Bool.and_eq_true, Bool.or_eq_true] at this
    obtain ⟨h1, h2⟩ := this
    have hd : ∀ {A B C : Prop}, (A ∨ B) ∨ C → A ∨ B ∨ C := fun h => h.elim
      (fun h => h.elim .inl (fun h => .inr (.inl h))) (fun h => .inr (.inr h))
    exact ⟨hd h1, hd h2⟩
  · intro z hz w hw
    have := Array.all_eq_true'.1 h11 z hz
    rw [hw] at this; dsimp only at this
    rw [Bool.and_eq_true, Array.all_eq_true'] at this
    obtain ⟨hn, ha⟩ := this
    refine ⟨fun hzn => ?_, fun a ha' han => ?_⟩
    · rw [hzn, Bool.not_true, Bool.false_or, Bool.and_eq_true, bne_iff_ne, Bool.or_eq_true,
        List.contains_iff_mem, List.mem_flatMap] at hn
      refine ⟨hn.1, hn.2.imp_right fun ⟨x, hx, hz'⟩ => ⟨x, Array.mem_toList_iff.1 hx, hz'⟩⟩
    · have := ha a ha'
      simp only [han, Bool.not_true, Bool.false_or, Bool.or_eq_true, Array.contains_iff_mem] at this
      rcases this with (h | h) | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr h)

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
theorem ecs_valueOK {tabs : Tables} {anc : ID → ID → Bool} {f g : Func} {bid : ID} {fb gb : Block}
    (hfb : f.block? bid = some fb) (hgb : g.block? bid = some gb)
    (hb : blockOK tabs (typeShapes tabs) anc f g bid = true) :
    ∀ x ∈ fb.values, ∀ u, f.value? x = some u → u.op ≠ .Phi →
      valueOK tabs (typeShapes tabs) f g x = true :=
  (ecs_parts hfb hgb hb).value

/-- `placedSDom` with `g`'s certificate: a non-`Phi` value placed in a strict dominator. -/
theorem ecs_placedSDom {g : Func} (hcg : Dom.CertOK g) {bid z : ID}
    (h : placedSDom g (make g).anc bid z = true) :
    ∃ v, Placed g z v ∧ v.op ≠ .Phi ∧ Dom.Anc (make g) v.block bid ∧ v.block ≠ bid := by
  unfold placedSDom at h
  cases hz : g.value? z with
  | none => rw [hz] at h; cases h
  | some w =>
    rw [hz] at h; dsimp only at h
    cases hgb : g.block? w.block with
    | none => rw [hgb] at h; simp at h
    | some b =>
      rw [hgb] at h; dsimp only at h
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Array.contains_iff_mem] at h
      obtain ⟨⟨⟨⟨hph, hne⟩, hbm⟩, hb⟩, ha⟩ := h
      exact ⟨w, ⟨hz, hbm, b, hgb, hb⟩, hph, (Dom.anc_iff hcg.parents).1 ha, hne⟩

/-- **The `IMake` arguments of converted values** (`imkArgOK`): source mode (the same
interface-shaped `IMake` in `f`, its data operand unconverted and a pointer or an aggregate in
both, `x` depending on it in `gb` when it is a value of `fb`) or target mode (interface-shaped in
`g`, it and its data operand held in the target, `HeldT`: nodes of `gb` that `x` depends on or
values placed in strict dominators). -/
theorem ecs_imk {tabs : Tables} {ce' : CheckEnv} {f g : Func} {bid : ID} {fb gb : Block}
    (hwg : WF ce' g) (hcg : Dom.CertOK g) (hbg : bid ∈ g.blocks)
    (hfb : f.block? bid = some fb) (hgb : g.block? bid = some gb) (hid : fb.id = gb.id)
    (hb : blockOK tabs (typeShapes tabs) (make g).anc f g bid = true) :
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
    simp only [Bool.and_eq_true, Bool.or_eq_true] at htgt
    obtain ⟨⟨hi, h1⟩, h2⟩ := htgt
    have hT : ∀ z, (placedSDom g (make g).anc fb.id z = true ∨
        depB g (ecs_node g gb) (fun _ => true) (gb.values.size + 1) z x = true) →
        HeldT g gb x z := fun z hz => by
      rcases hz with hp | hd
      · rw [hid] at hp; exact .inr (ecs_placedSDom hcg hp)
      · exact .inl (ecs_depB_dep hown hnd hd)
    exact .inr ⟨hi, hT _ h1, hT _ h2⟩

/-! ## Stack-argument stores -/

theorem ecs_noNp {np : ID → Bool} {c : ID} : ∀ {l : List ID}, noNpUntil np l c = true →
    ∃ P Q, l = P ++ c :: Q ∧ ∀ y ∈ P, np y = false
  | [], h => by simp [noNpUntil] at h
  | y :: l, h => by
    unfold noNpUntil at h
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true'] at h
    rcases h with rfl | ⟨hy, h⟩
    · exact ⟨[], l, rfl, fun _ h => absurd h List.not_mem_nil⟩
    · obtain ⟨P, Q, rfl, hP⟩ := ecs_noNp h
      refine ⟨y :: P, Q, rfl, fun a ha => ?_⟩
      rcases List.mem_cons.1 ha with rfl | ha
      · exact hy
      · exact hP a ha

/-- `gapOK`: in a list without repetitions, `c` follows `z` with no `np` node in between. -/
theorem ecs_gap {np : ID → Bool} {z c : ID} : ∀ {A B : List ID},
    gapOK np (A ++ z :: B) z c = true → (A ++ z :: B).Nodup →
      ∃ P Q, B = P ++ c :: Q ∧ ∀ y ∈ P, np y = false
  | [], B, h, _ => by
    simp only [List.nil_append, gapOK, beq_self_eq_true, ite_true] at h
    exact ecs_noNp h
  | a :: A, B, h, hnd => by
    have ha : a ≠ z := fun he => by subst he; exact (List.nodup_cons.1 hnd).1 (by simp)
    simp only [List.cons_append, gapOK] at h
    rw [if_neg (by simpa using ha)] at h
    exact ecs_gap h (List.nodup_cons.1 hnd).2

theorem ecs_storeChain_top {g : Func} {nw : ID → Bool} {n : Nat} {top b : ID} {zs : List ID}
    (h : storeChain g nw n top b = some zs) (hne : zs ≠ []) :
    top ∈ zs ∧ ∃ w, g.value? top = some w ∧ w.op = .Store := by
  match n, h with
  | 0, h => simp [storeChain] at h
  | n + 1, h =>
    rcases ecs_storeChain_step h with ⟨-, rfl⟩ | ⟨w, zs', -, hw, -, hop, -, -, rfl⟩
    · exact absurd rfl hne
    · exact ⟨by simp, w, hw, hop⟩

/-- The stores of a chain lead to its top in the block's dependencies. -/
theorem ecs_chain_dep {g : Func} {gb : Block} (hown : ValuesOwn g gb) (hnd : gb.values.toList.Nodup)
    {nw : ID → Bool} : ∀ {n : Nat} {top b : ID} {zs : List ID}, storeChain g nw n top b = some zs →
      (∀ z ∈ zs, z ∈ gb.values) → ∀ z ∈ zs, z = top ∨
        Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList) z top
  | 0, _, _, _, h, _, _, _ => by simp [storeChain] at h
  | n + 1, top, b, zs, h, hin, z, hz => by
    rcases ecs_storeChain_step h with ⟨-, rfl⟩ | ⟨w, zs', -, hw, -, hop, hsz, hc, rfl⟩
    · exact absurd hz List.not_mem_nil
    rcases List.mem_append.1 hz with hz | hz
    · have hne : zs' ≠ [] := List.ne_nil_of_mem hz
      obtain ⟨htm, wt, hwt, hwtop⟩ := ecs_storeChain_top hc hne
      have hT : NodeIn (schedNodes g gb).toList top :=
        (nodeIn_schedNodes hown).2 ⟨hin top (by simp), w, hw, by rw [hop]; decide⟩
      have hT' : NodeIn (schedNodes g gb).toList w.args[2]! :=
        (nodeIn_schedNodes hown).2 ⟨hin _ (List.mem_append_left _ htm), wt, hwt, by rw [hwtop]; decide⟩
      have harg : w.args[2]! ∈ argsOf (schedNodes g gb).toList top := by
        rw [argsOf_schedNodes hown hnd (hin top (by simp)) hw (by rw [hop]; decide),
          ecs_args_three hsz]
        simp
      have hd : Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList) w.args[2]! top :=
        .arg hT' hT harg
      rcases ecs_chain_dep hown hnd hc (fun z' hz' => hin z' (List.mem_append_left _ hz')) z hz with
        he | hd'
      · rw [he]; exact .inr hd
      · exact .inr (hd'.trans hd)
    · exact .inl (List.mem_singleton.1 hz)

theorem ecs_callOK {tabs : Tables} {f g : Func} {x : ID} {u w : Value}
    (hv : valueOK tabs (typeShapes tabs) f g x = true) (hu : f.value? x = some u)
    (hw : g.value? x = some w) (hc : (callOpMap u.op).isSome = true) :
    callOK tabs (typeShapes tabs) f g u w = true := by
  unfold valueOK at hv
  rw [hu, hw] at hv
  dsimp only at hv
  rwa [if_pos hc] at hv

theorem ecs_callOK_facts {tabs : Tables} {sh : Array Ty} {f g : Func} {u w : Value}
    (h : callOK tabs sh f g u w = true) :
    0 < u.args.size ∧ 1 ≤ w.args.size ∧ w.op ≠ .Phi ∧ w.op ≠ .Invalid := by
  unfold callOK at h
  split at h
  · next op k abi hmap habi =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, ge_iff_le] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hwop, -⟩, hn⟩, -⟩, -⟩, -⟩, -⟩, hws⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
    obtain ⟨-, -, hpost, hinv⟩ := ecc_callOpMap hmap
    refine ⟨hn, by omega, fun hp => ?_, by rw [hwop]; exact hinv⟩
    rw [hwop] at hp
    subst hp
    simp at hpost
  · cases h

/-- The chain of stores of an accepted call, and the parameter its `Move` copies. -/
theorem ecs_callOK_stack {tabs : Tables} {sh : Array Ty} {f g : Func} {u w : Value}
    (h : callOK tabs sh f g u w = true) : ∃ zs, callStores f g u w = some zs ∧
      ∀ z, callMove f g u w = some z → ∃ p a, moveOK tabs sh f g u p a z = true := by
  unfold callOK at h
  split at h
  · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true', ge_iff_le,
      List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hstack⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
    obtain ⟨-, zs, sp0, sp1, hcs, -, -, hmv0⟩ := ecc_stackOK_inv hstack
    refine ⟨zs, hcs, fun z hz => ?_⟩
    rcases hmv0 with ⟨hn, -⟩ | ⟨z', p, a, hz', -, hm⟩
    · rw [hz] at hn; cases hn
    · rw [hz] at hz'; cases hz'; exact ⟨p, a, hm⟩
  · cases h

/-- The members of `stackStores`: the stores of a call's chain, or its `Move`. -/
theorem ecs_stackStores_mem {f g : Func} {x z : ID} (h : z ∈ stackStores f g x) :
    ∃ u w, f.value? x = some u ∧ g.value? x = some w ∧ (callOpMap u.op).isSome = true ∧
      ((∃ zs, callStores f g u w = some zs ∧ z ∈ zs) ∨ callMove f g u w = some z) := by
  unfold stackStores stackMove at h
  cases hu : f.value? x with
  | none => rw [hu] at h; simp at h
  | some u =>
  cases hw : g.value? x with
  | none => rw [hu, hw] at h; simp at h
  | some w =>
  rw [hu, hw] at h
  dsimp only at h
  by_cases hc : (callOpMap u.op).isSome = true
  · rw [if_pos hc, if_pos hc] at h
    refine ⟨u, w, rfl, rfl, hc, ?_⟩
    rcases List.mem_append.1 h with h | h
    · cases hcs : callStores f g u w with
      | none => rw [hcs] at h; cases h
      | some zs => rw [hcs] at h; exact .inl ⟨zs, rfl, h⟩
    · cases hm : callMove f g u w with
      | none => rw [hm] at h; cases h
      | some z' => rw [hm] at h; simp at h; exact .inr (by rw [h])
  · rw [if_neg hc, if_neg hc] at h; simp at h

theorem ecs_mem_stackStores {f g : Func} {x z : ID} {u w : Value} (hu : f.value? x = some u)
    (hw : g.value? x = some w) (hc : (callOpMap u.op).isSome = true)
    (h : (∃ zs, callStores f g u w = some zs ∧ z ∈ zs) ∨ callMove f g u w = some z) :
    z ∈ stackStores f g x := by
  unfold stackStores stackMove
  rw [hu, hw]
  dsimp only
  rw [if_pos hc, if_pos hc]
  rcases h with ⟨zs, hcs, hz⟩ | hm
  · rw [hcs]; exact List.mem_append_left _ hz
  · rw [hm]; simp

theorem ecs_beforeB : ∀ {l : List ID} {a y : ID}, beforeB l a y = true →
    ∃ A B, l = A ++ a :: B ∧ y ∈ B
  | [], _, _, h => by simp [beforeB] at h
  | z :: l, a, y, h => by
    unfold beforeB at h
    split at h
    · rename_i hz
      exact ⟨[], l, by rw [beq_iff_eq.1 hz]; rfl, by simpa using h⟩
    · obtain ⟨A, B, rfl, hy⟩ := ecs_beforeB h
      exact ⟨z :: A, B, rfl, hy⟩

/-- The bottom of a chain of stores, a node, leads to its top. -/
theorem ecs_chain_base_dep {g : Func} {gb : Block} (hown : ValuesOwn g gb)
    (hnd : gb.values.toList.Nodup) {nw : ID → Bool} :
    ∀ {n : Nat} {top b : ID} {zs : List ID}, storeChain g nw n top b = some zs → zs ≠ [] →
      (∀ z ∈ zs, z ∈ gb.values) → NodeIn (schedNodes g gb).toList b →
      Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList) b top
  | 0, _, _, _, h, _, _, _ => by simp [storeChain] at h
  | n + 1, top, b, zs, h, hne, hin, hb => by
    rcases ecs_storeChain_step h with ⟨-, rfl⟩ | ⟨w, zs', -, hw, -, hop, hsz, hc, rfl⟩
    · exact absurd rfl hne
    have hT : NodeIn (schedNodes g gb).toList top :=
      (nodeIn_schedNodes hown).2 ⟨hin top (by simp), w, hw, by rw [hop]; decide⟩
    have harg : w.args[2]! ∈ argsOf (schedNodes g gb).toList top := by
      rw [argsOf_schedNodes hown hnd (hin top (by simp)) hw (by rw [hop]; decide),
        ecs_args_three hsz]
      simp
    by_cases hne' : zs' = []
    · subst hne'
      rw [← ecs_storeChain_nil hc] at hb ⊢
      exact .arg hb hT harg
    · obtain ⟨htm, wt, hwt, hwtop⟩ := ecs_storeChain_top hc hne'
      have hT' : NodeIn (schedNodes g gb).toList w.args[2]! :=
        (nodeIn_schedNodes hown).2 ⟨hin _ (List.mem_append_left _ htm), wt, hwt, by rw [hwtop]; decide⟩
      exact (ecs_chain_base_dep hown hnd hc hne' (fun z hz => hin z (List.mem_append_left _ hz)) hb).trans
        (.arg hT' hT harg)

/-- The values listed in `g` are closed under their new arguments. -/
theorem ecs_listed {ce' : CheckEnv} {f g : Func} (hwg : WF ce' g) :
    ∀ z, Listed g z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args,
      isNewB f a = true → Listed g a := by
  intro z ⟨c, gc, hc, hz⟩ w hw
  obtain ⟨v, hv', hvid, -⟩ := hwg.valueId c gc hc z hz
  exact ⟨by rw [hw] at hv'; cases hv'; exact hvid,
    fun a ha _ => hwg.argListed c gc z w ⟨hc, hz, hw⟩ a ha⟩

/-- **A call depends on its stack-argument stores and `Move`** in the block. -/
theorem ecs_store_dep {tabs : Tables} {ce' : CheckEnv} {f g : Func} {bid : ID} {fb gb : Block}
    (hwg : WF ce' g) (hbg : bid ∈ g.blocks) (hfb : f.block? bid = some fb)
    (hgb : g.block? bid = some gb) (hb : blockOK tabs (typeShapes tabs) (make g).anc f g bid = true)
    {x z : ID} (hx : x ∈ fb.values) (hz : z ∈ stackStores f g x) :
    Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList) z x := by
  have P := ecs_parts hfb hgb hb
  have hownG := valuesOwn hwg hbg hgb
  have hndG := hwg.valuesNodup bid gb ⟨hbg, hgb⟩
  obtain ⟨og, -, H⟩ := P.stack
  have hin : ∀ z' ∈ stackStores f g x, z' ∈ gb.values := fun z' hz' => ((H x hx).1 z' hz').1
  obtain ⟨u, w, hu, hw, hc, hzc⟩ := ecs_stackStores_mem hz
  have hphi : u.op ≠ .Phi := fun h => by rw [h] at hc; cases hc
  have hok := ecs_callOK (P.value x hx u hu hphi) hu hw hc
  obtain ⟨-, hws, hwph, -⟩ := ecs_callOK_facts hok
  obtain ⟨zs, hcs, -⟩ := ecs_callOK_stack hok
  have hzsin : ∀ z' ∈ zs, z' ∈ gb.values := fun z' hz' =>
    hin z' (ecs_mem_stackStores hu hw hc (.inl ⟨zs, hcs, hz'⟩))
  have hxg := P.common x hx
  have hcs' := hcs
  unfold callStores at hcs'
  -- the target's memory argument, a node, leads to the call
  have htopx : NodeIn (schedNodes g gb).toList w.args[w.args.size - 1]! →
      Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList)
        w.args[w.args.size - 1]! x := by
    intro hN
    refine .arg hN ((nodeIn_schedNodes hownG).2 ⟨hxg, w, hw, hwph⟩) ?_
    rw [argsOf_schedNodes hownG hndG hxg hw hwph, getElem!_pos w.args _ (by omega)]
    exact Array.mem_toList_iff.2 (Array.getElem_mem _)
  rcases hzc with ⟨zs', hcs2, hz'⟩ | hm
  · rw [hcs] at hcs2; cases hcs2
    obtain ⟨htm, wt, hwt, hwtop⟩ := ecs_storeChain_top hcs' (List.ne_nil_of_mem hz')
    have hdx := htopx ((nodeIn_schedNodes hownG).2 ⟨hzsin _ htm, wt, hwt, by rw [hwtop]; decide⟩)
    rcases ecs_chain_dep hownG hndG hcs' hzsin z hz' with he | hd
    · rw [he]; exact hdx
    · exact hd.trans hdx
  · obtain ⟨-, mw, hmw, hmop, -, -⟩ := ecc_callMove_spec hm
    have hbase : callBase f g u w = z := by unfold callBase; rw [hm]; rfl
    rw [hbase] at hcs'
    have hNz : NodeIn (schedNodes g gb).toList z :=
      (nodeIn_schedNodes hownG).2 ⟨hin z hz, mw, hmw, by rw [hmop]; decide⟩
    by_cases hne : zs = []
    · subst hne
      have he := ecs_storeChain_nil hcs'
      rw [← he] at hNz ⊢
      exact htopx hNz
    · obtain ⟨htm, wt, hwt, hwtop⟩ := ecs_storeChain_top hcs' hne
      exact (ecs_chain_base_dep hownG hndG hcs' hne hzsin hNz).trans
        (htopx ((nodeIn_schedNodes hownG).2 ⟨hzsin _ htm, wt, hwt, by rw [hwtop]; decide⟩))

/-- **The `Dereference` a call's `Move` copies** (`ecMoveArg`) is a source argument of the call
in its block (`SrcArg`, from `blockOK`'s `stack` conjunct). -/
theorem ecs_moveArgHeld {tabs : Tables} {f g : Func} {bid : ID} {fb gb : Block}
    (hfb : f.block? bid = some fb) (hgb : g.block? bid = some gb)
    (hb : blockOK tabs (typeShapes tabs) (make g).anc f g bid = true) :
    ∀ x ∈ fb.values, ∀ u, f.value? x = some u → (callOpMap u.op).isSome = true →
      ∀ w, g.value? x = some w → ∀ a, ecMoveArg f g u w a → SrcArg f fb x a := by
  rintro x hx u hu hc w hw a ⟨hcm, ha, au, hau, hop⟩
  have hma : moveArgB f g x a = true := by
    unfold moveArgB stackMove; rw [hu, hw]; dsimp only; rw [if_pos hc, hau]; simp [hcm, hop]
  obtain ⟨og, -, H⟩ := (ecs_parts hfb hgb hb).stack
  obtain ⟨haf, -⟩ := (H x hx).2 u hu a ha hma
  exact ⟨haf, ⟨u, hu, ha⟩, fun uz huz => by rw [hau] at huz; cases huz; rw [hop]; decide⟩

/-- **A stack-argument store or `Move` is anchored at its call** (`AnchoredAt`): its obligation
(`ecc_storeObl`, `ecc_moveObl`), the call's memory (and the `Move`'s source) reaching it, and no
source non-pure node between them. -/
theorem ecs_anchored {tabs : Tables} {ce ce' : CheckEnv} {f g : Func} {bid : ID} {fb gb : Block}
    (hwf : WF ce f) (hwg : WF ce' g) (hcg : Dom.CertOK g) (hbm : bid ∈ f.blocks)
    (hbg : bid ∈ g.blocks) (hfb : f.block? bid = some fb) (hgb : g.block? bid = some gb)
    (hid : fb.id = gb.id) (hb : blockOK tabs (typeShapes tabs) (make g).anc f g bid = true)
    {z x : ID} (hx : x ∈ fb.values) (hz : z ∈ stackStores f g x) :
    AnchoredAt tabs f g (ecCv tabs f g) (isNewB f) fb gb z := by
  have P := ecs_parts hfb hgb hb
  have hownF := valuesOwn hwf hbm hfb
  have hndF := hwf.valuesNodup bid fb ⟨hbm, hfb⟩
  have hownG := valuesOwn hwg hbg hgb
  have hndG := hwg.valuesNodup bid gb ⟨hbg, hgb⟩
  obtain ⟨og, hog, H⟩ := P.stack
  obtain ⟨hzm, hgap, hsp, hcm⟩ := (H x hx).1 z hz
  obtain ⟨u, w, hu, hw, hc, hzc⟩ := ecs_stackStores_mem hz
  have hphi : u.op ≠ .Phi := fun h => by rw [h] at hc; cases hc
  have hok := ecs_callOK (P.value x hx u hu hphi) hu hw hc
  obtain ⟨hn0, -, -, hwi⟩ := ecs_callOK_facts hok
  have hcm' : callMem f x = u.args[u.args.size - 1]! := by unfold callMem; rw [hu]; rfl
  rw [hcm'] at hcm
  have hci : ¬ TgtInvalid g x := fun ⟨w', hw', hop⟩ => by rw [hw] at hw'; cases hw'; exact hwi hop
  have hm0 : u.args[u.args.size - 1]! ∈ u.args := by
    rw [getElem!_pos u.args _ (by omega)]; exact Array.getElem_mem _
  have hmemNew : isNewB f u.args[u.args.size - 1]! = false := by
    obtain ⟨bid', b', hB', hab'⟩ := hwf.argListed bid fb x u ⟨⟨hbm, hfb⟩, hx, hu⟩ _ hm0
    obtain ⟨ua, hua, -, -⟩ := hwf.valueId bid' b' hB' _ hab'
    unfold isNewB; rw [hua]; rfl
  have hmemFr : u.args[u.args.size - 1]! ∈ gb.values →
      (∃ v, g.value? u.args[u.args.size - 1]! = some v ∧ v.op = .Phi) ∨
      Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList)
        u.args[u.args.size - 1]! z := fun hag => by
    obtain ⟨v, hv, -, -⟩ := hwg.valueId bid gb ⟨hbg, hgb⟩ _ hag
    by_cases hpa : v.op = .Phi
    · exact .inl ⟨v, hv, hpa⟩
    · exact .inr (ecs_depB_dep hownG hndG (hcm hag v hv hpa))
  have hsp' : ∀ wz qw, g.value? z = some wz → g.value? wz.args[0]! = some qw →
      isNewB f qw.args[0]! = false → HeldT g gb z qw.args[0]! := by
    intro wz qw hwz hqw hn
    have hs : storeSP g z = qw.args[0]! := by unfold storeSP; rw [hwz]; simp [hqw]
    rw [hs] at hsp
    rcases hsp with h | h | h
    · rw [hn] at h; cases h
    · rw [hid] at h; exact .inr (ecs_placedSDom hcg h)
    · exact .inl (ecs_depB_dep hownG hndG h)
  have hgap' : ∀ og', schedule g gb = some og' → ∀ A B, og'.toList = A ++ z :: B →
      ∃ P Q, B = P ++ x :: Q ∧ ∀ y ∈ P, npIn (schedNodes f fb).toList y = false := by
    intro og' hog' A B hAB
    rw [hog] at hog'
    cases hog'
    rw [npIn_schedNodes hownF hndF]
    rw [hAB] at hgap
    exact ecs_gap hgap (hAB ▸ (schedule_topo hownG hndG hog).1)
  rcases hzc with ⟨zs, hcs, hzs⟩ | hzm'
  · exact ⟨x, hx, hci, [u.args[u.args.size - 1]!],
      ecc_storeObl hu hw hc hok hcs hzs (Listed g) (ecs_listed hwg) ⟨bid, gb, ⟨hbg, hgb⟩, hzm⟩ hsp',
      fun a ha => by rw [List.mem_singleton.1 ha]; exact ⟨hmemNew, hmemFr⟩, hgap'⟩
  -- the `Move`
  obtain ⟨-, mw, hmw, hmop, hmsz, -⟩ := ecc_callMove_spec hzm'
  obtain ⟨-, -, hmv⟩ := ecs_callOK_stack hok
  obtain ⟨p, a, hmok⟩ := hmv z hzm'
  obtain ⟨mw', au, hmw', -, -, -, -, -, -, -, -, -, -, -, hsn, -⟩ := ecc_moveOK_spec hmok
  rw [hmw] at hmw'; cases hmw'
  refine ⟨x, hx, hci, [u.args[u.args.size - 1]!, ecMoveSrc g z],
    ecc_moveObl hu hw hc hok hzm' (Listed g) (ecs_listed hwg) ⟨bid, gb, ⟨hbg, hgb⟩, hzm⟩ hsp' ?_,
    ?_, hgap'⟩
  · exact fun a' ha' => .inr (ecs_moveArgHeld hfb hgb hb x hx u hu hc w hw a' ha')
  · intro b hb'
    rcases List.mem_cons.1 hb' with rfl | hb'
    · exact ⟨hmemNew, hmemFr⟩
    · rw [List.mem_singleton.1 hb', ecMoveSrc_of hmw]
      refine ⟨hsn, fun hag => ?_⟩
      obtain ⟨v, hv, -, -⟩ := hwg.valueId bid gb ⟨hbg, hgb⟩ _ hag
      by_cases hpa : v.op = .Phi
      · exact .inl ⟨v, hv, hpa⟩
      · refine .inr (.arg ((nodeIn_schedNodes hownG).2 ⟨hag, v, hv, hpa⟩)
          ((nodeIn_schedNodes hownG).2 ⟨hzm, mw, hmw, by rw [hmop]; decide⟩) ?_)
        rw [argsOf_schedNodes hownG hndG hzm hmw (by rw [hmop]; decide), ecs_args_three hmsz]
        simp

/-- **The `SP`s of a call's stack-argument stores and `Move`** are held in the target when the
call is evaluated (`HeldT`): placed in a strict dominator, or the call depends on them through
its stores. -/
theorem ecs_spHeld {tabs : Tables} {ce' : CheckEnv} {f g : Func} {bid : ID} {fb gb : Block}
    (hwg : WF ce' g) (hcg : Dom.CertOK g)
    (hbg : bid ∈ g.blocks) (hfb : f.block? bid = some fb) (hgb : g.block? bid = some gb)
    (hid : fb.id = gb.id) (hb : blockOK tabs (typeShapes tabs) (make g).anc f g bid = true) :
    ∀ x ∈ fb.values, ∀ u, f.value? x = some u → (callOpMap u.op).isSome = true →
      ∀ w, g.value? x = some w → ∀ a, ecStackSP f g u w a → HeldT g gb x a := by
  intro x hx u hu hc w hw a ⟨z, hzc, wz, qw, hwz, hqw, hn, ha⟩
  subst ha
  have P := ecs_parts hfb hgb hb
  have hownG := valuesOwn hwg hbg hgb
  have hndG := hwg.valuesNodup bid gb ⟨hbg, hgb⟩
  have hz := ecs_mem_stackStores hu hw hc hzc
  obtain ⟨og, -, H⟩ := P.stack
  obtain ⟨-, -, hsp, -⟩ := (H x hx).1 z hz
  have hs : storeSP g z = qw.args[0]! := by unfold storeSP; rw [hwz]; simp [hqw]
  rw [hs] at hsp
  rcases hsp with h | h | h
  · rw [hn] at h; cases h
  · rw [hid] at h; exact .inr (ecs_placedSDom hcg h)
  exact .inl (.trans (ecs_depB_dep hownG hndG h) (ecs_store_dep hwg hbg hfb hgb hb hx hz))

/-- A source value of an accepted block depends in `g` on its arguments that are nodes of the
block (`blockOK`'s reach condition), unless the value is invalidated or the argument is the
`Dereference` a call's `Move` copies. -/
theorem ecs_argDep {tabs : Tables} {ce ce' : CheckEnv} {f g : Func} {bid : ID} {fb gb : Block}
    (hwf : WF ce f) (hwg : WF ce' g) (hbm : bid ∈ f.blocks) (hbg : bid ∈ g.blocks)
    (hfb : f.block? bid = some fb) (hgb : g.block? bid = some gb)
    (hb : blockOK tabs (typeShapes tabs) (make g).anc f g bid = true) :
    ∀ x ∈ fb.values, ∀ u, f.value? x = some u → u.op ≠ .Phi → invalidated g x = false →
      ∀ a ∈ u.args, a ∈ fb.values → (∀ ua, f.value? a = some ua → ua.op ≠ .Phi) →
      moveArgB f g x a = false →
      Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList) a x := by
  intro x hx u hu hph hxi a ha haf hpa hmv
  have P := ecs_parts hfb hgb hb
  have hownG := valuesOwn hwg hbg hgb
  have hndG := hwg.valuesNodup bid gb ⟨hbg, hgb⟩
  obtain ⟨ua, hua, -, -⟩ := hwf.valueId bid fb ⟨hbm, hfb⟩ a haf
  rcases P.reach x hx (ecs_node_iff.2 ⟨hx, u, hu, hph⟩) hxi u hu a ha
    (ecs_node_iff.2 ⟨haf, ua, hua, hpa ua hua⟩) with ⟨-, hd⟩ | ⟨hm, -⟩
  · exact hd.elim (ecs_depB_dep hownG hndG) (ecs_depB_dep hownG hndG)
  · rw [hmv] at hm; cases hm

/-- **The `SP`s and memories of a stack-assigned result's loads** are held in the target when the
result is evaluated (`HeldT`): new, placed in a strict dominator, or the result depends on them. -/
theorem ecs_loadsHeld {tabs : Tables} {ce' : CheckEnv} {f g : Func} {bid : ID} {fb gb : Block}
    (hwg : WF ce' g) (hcg : Dom.CertOK g)
    (hbg : bid ∈ g.blocks) (hfb : f.block? bid = some fb) (hgb : g.block? bid = some gb)
    (hid : fb.id = gb.id) (hb : blockOK tabs (typeShapes tabs) (make g).anc f g bid = true) :
    ∀ x ∈ fb.values, ∀ l ∈ stackLoads tabs (typeShapes tabs) f g x,
      (isNewB f (loadSP g l) = false → HeldT g gb x (loadSP g l)) ∧
      (isNewB f (loadMem g l) = false → HeldT g gb x (loadMem g l)) := by
  intro x hx l hl
  have P := ecs_parts hfb hgb hb
  have hownG := valuesOwn hwg hbg hgb
  have hndG := hwg.valuesNodup bid gb ⟨hbg, hgb⟩
  obtain ⟨h1, h2⟩ := P.loads x hx l hl
  have key : ∀ z, (isNewB f z = true ∨ placedSDom g (make g).anc fb.id z = true ∨
      depB g (ecs_node g gb) (fun _ => true) (gb.values.size + 1) z x = true) →
      isNewB f z = false → HeldT g gb x z := by
    intro z h hn
    rcases h with h | h | h
    · rw [hn] at h; cases h
    · rw [hid] at h; exact .inr (ecs_placedSDom hcg h)
    · exact .inl (ecs_depB_dep hownG hndG h)
  exact ⟨key _ h1, key _ h2⟩

private theorem ecs_invalidated_iff {g : Func} {y : ID} : invalidated g y = true ↔ TgtInvalid g y := by
  unfold invalidated TgtInvalid
  cases hw : g.value? y with
  | none => simp
  | some w => simp

/-- An argument `a` of `y` accepted by `throughB` (pure in `f`, its node arguments reaching `y`
in `g`) `Feeds` `y`. -/
private theorem ecs_through {f g : Func} {fb gb : Block} (hownF : ValuesOwn f fb)
    (hndF : fb.values.toList.Nodup) (hownG : ValuesOwn g gb) (hndG : gb.values.toList.Nodup)
    {a y : ID} {n : Nat} (ha : NodeIn (schedNodes f fb).toList a)
    (h : throughB f g (ecs_node f fb) (ecs_node g gb) n a y = true) :
    Feeds (NodeIn (schedNodes f fb).toList) (NodeIn (schedNodes g gb).toList)
      (argsOf (schedNodes f fb).toList) (argsOf (schedNodes g gb).toList)
      (PureIn (schedNodes f fb).toList) y a := by
  obtain ⟨hab, au, hau, hph⟩ := (nodeIn_schedNodes hownF).1 ha
  unfold throughB at h
  rw [hau] at h; dsimp only at h
  rw [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true'] at h
  obtain ⟨hp, hb⟩ := h
  refine .through (fun nd hn => ?_) fun b hb' hbN => ?_
  · rw [CopyElim.nodeOf_schedNodes hownF hndF hab hau hph] at hn
    cases hn; exact hp
  · rw [argsOf_schedNodes hownF hndF hab hau hph] at hb'
    have := hb b (Array.mem_toList_iff.1 hb')
    rw [(ecs_nodeIn hownF).2 hbN, Bool.not_true, Bool.false_or, Bool.and_eq_true] at this
    exact .direct ((ecs_nodeIn hownG).1 this.1) (ecs_depB_dep hownG hndG this.2)

/-- **The structural soundness of `blockOK`**: an accepted block satisfies `CvBlock` for the
conversion of `expand calls`, given its local obligations (`obl`) and its `Ret` field (`ret`). -/
theorem ecs_block {tabs : Tables} {ce ce' : CheckEnv} {f g : Func} {bid : ID} {fb gb : Block}
    (hwf : WF ce f) (hwg : WF ce' g) (hcg : Dom.CertOK g) (hcfg : cfgView g = cfgView f)
    (hbm : bid ∈ f.blocks) (hfb : f.block? bid = some fb) (hgb : g.block? bid = some gb)
    (hid : fb.id = gb.id)
    (hb : blockOK tabs (typeShapes tabs) (make g).anc f g bid = true)
    (hobl : ((make f).depthOf fb.id).isSome → ∀ x ∈ fb.values, ∀ u, f.value? x = some u →
      u.op ≠ .Phi → Obl tabs f g (ecCv tabs f g) (isNewB f) (ecFront f g x) (Held f g fb gb x)
        (HeldT g gb x) x)
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
      feeds := fun a y ha hy hay _ hyi => by
        obtain ⟨hyb, u, hu, hph⟩ := (nodeIn_schedNodes hownF).1 hy
        rw [argsOf_schedNodes hownF hndF hyb hu hph] at hay
        have hiy : invalidated g y = false :=
          Bool.eq_false_iff.2 fun h => hyi (ecs_invalidated_iff.1 h)
        rcases P.reach y hyb ((ecs_nodeIn hownF).2 hy) hiy u hu a
          (Array.mem_toList_iff.1 hay) ((ecs_nodeIn hownF).2 ha) with ⟨hna, hd⟩ | ⟨-, hth⟩
        · exact .direct ((ecs_nodeIn hownG).1 hna)
            (hd.elim (ecs_depB_dep hownG hndG) (ecs_depB_dep hownG hndG))
        · exact ecs_through hownF hndF hownG hndG ha hth
      invalid := fun x _ hxi => by
        obtain ⟨wi, hwi, hop⟩ := hxi
        refine ⟨fun y => by unfold ecCv; rw [if_pos (ecs_invalidated_iff.2 ⟨wi, hwi, hop⟩)],
          fun w hw env fr argv _ => ?_⟩
        obtain rfl := Option.some.inj (hwi.symm.trans hw)
        exact CSE.evalOp_total (by rw [hop]; decide) (by rw [hop]; decide) (by rw [hop]; decide)
      invArgs := fun a b hb' hab hai => by
        obtain ⟨hbb, wb, hwb, hph⟩ := (nodeIn_schedNodes hownG).1 hb'
        rw [argsOf_schedNodes hownG hndG hbb hwb hph] at hab
        have := P.invArgs b hbb wb hwb hph a (Array.mem_toList_iff.1 hab)
        rw [ecs_invalidated_iff.2 hai] at this; cases this
      obl := hobl
      front := fun x hx u hu hph a ha => ?_
      ctrl := fun hk c hc => ecCv_of_not_special (P.ctrl hk c hc)
      ret := hret
      newOK := fun z hz hn w hw => by
        obtain ⟨hph, he⟩ := (P.newv z hz w hw).1 hn
        refine ⟨hph, ?_⟩
        rcases he with he | ⟨x, hx, hzx⟩
        · exact .inl (newEval_of_newEvalB he)
        · exact .inr (ecs_anchored hwf hwg hcg hbm hbg hfb hgb hid hb hx hzx)
      newArgs := fun z hz w hw a ha hn => by
        rcases (P.newv z hz w hw).2 a ha hn with h | h | h
        · exact .inl h
        · refine .inr (.inl ?_)
          unfold valsOf at h
          cases he : g.block? g.entry with
          | none => rw [he] at h; simp at h
          | some eb => rw [he] at h; exact ⟨eb, he, h⟩
        · rw [hid] at h
          exact .inr (.inr (ecs_placedSDom hcg h)) }
  have hxg := P.common x hx
  obtain ⟨w, hw⟩ := hdefG x hxg
  have hwph : w.op ≠ .Phi := fun hp => by
    obtain ⟨-, u', hu', hs⟩ := P.phiT x hxg w hw hp
    rw [hu] at hu'; cases hu'
    exact hph ((ecs_phiSame hs).1.symm.trans hp)
  unfold ecFront at ha
  by_cases hinv : invalidated g x = true
  · rw [if_pos hinv] at ha; cases ha
  have hinv' : invalidated g x = false := Bool.eq_false_iff.2 hinv
  rw [if_neg hinv, hu, hw] at ha
  simp only [Option.map_some, Option.getD_some, List.mem_append, List.mem_filter,
    Bool.not_eq_true'] at ha
  rcases ha with ha | ⟨ha | ha, han⟩
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
    · rcases P.reach x hx (ecs_node_iff.2 ⟨hx, u, hu, hph⟩) hinv' u hu a
        (Array.mem_toList_iff.1 ha) (ecs_node_iff.2 ⟨haf, ua, hua, hpa⟩) with ⟨-, hd⟩ | ⟨hma, -⟩
      · exact .inr (.inl (hd.elim (ecs_depB_dep hownG hndG) (ecs_depB_dep hownG hndG)))
      · obtain ⟨og, hog, H⟩ := P.stack
        obtain ⟨-, hbf⟩ := (H x hx).2 u hu a (Array.mem_toList_iff.1 ha) hma
        refine .inr (.inr fun og' hog' => ?_)
        rw [hog] at hog'; cases hog'
        exact ecs_beforeB hbf
  · refine ⟨han, fun hag => ?_⟩
    obtain ⟨wa, hwa⟩ := hdefG a hag
    by_cases hpa : wa.op = .Phi
    · exact .inl ⟨wa, hwa, hpa⟩
    · have hxN := (nodeIn_schedNodes hownG).2 ⟨hxg, w, hw, hwph⟩
      have haN := (nodeIn_schedNodes hownG).2 ⟨hag, wa, hwa, hpa⟩
      refine .inr (.inl (.arg haN hxN ?_))
      rw [argsOf_schedNodes hownG hndG hxg hw hwph]
      exact ha
  · -- an argument of the call's `Move`
    refine ⟨han, fun hag => ?_⟩
    cases hsm : stackMove f g x with
    | none => rw [hsm] at ha; simp at ha
    | some z =>
    cases hmw : g.value? z with
    | none => rw [hsm] at ha; simp [hmw] at ha
    | some mw =>
    rw [hsm] at ha
    simp only [Option.bind_some, hmw, Option.map_some, Option.getD_some] at ha
    have hsm' := hsm
    unfold stackMove at hsm'
    rw [hu, hw] at hsm'; dsimp only at hsm'
    by_cases hc : (callOpMap u.op).isSome = true
    · rw [if_pos hc] at hsm'
      have hz := ecs_mem_stackStores hu hw hc (.inr hsm')
      have hzx := ecs_store_dep hwg hbg hfb hgb hb hx hz
      obtain ⟨og, -, H⟩ := P.stack
      have hzg := ((H x hx).1 z hz).1
      obtain ⟨-, mw', hmw', hmop, -, -⟩ := ecc_callMove_spec hsm'
      rw [hmw] at hmw'; cases hmw'
      obtain ⟨wa, hwa⟩ := hdefG a hag
      by_cases hpa : wa.op = .Phi
      · exact .inl ⟨wa, hwa, hpa⟩
      · have hzN := (nodeIn_schedNodes hownG).2 ⟨hzg, mw, hmw, by rw [hmop]; decide⟩
        have haN := (nodeIn_schedNodes hownG).2 ⟨hag, wa, hwa, hpa⟩
        refine .inr (.inl (.trans (.arg haN hzN ?_) hzx))
        rw [argsOf_schedNodes hownG hndG hzg hmw (by rw [hmop]; decide)]
        exact ha
    · rw [if_neg hc] at hsm'; cases hsm'

end GoFV.Proof.EC

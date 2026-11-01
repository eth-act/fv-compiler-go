import GoFV.Proof.Pass.ECTree
import GoFV.Proof.AtomSimOK
import GoFV.Proof.Pass.CSEMemChain

/-!
# The obligations of parameters and call results (issue #28)

`obl_arg`: an incoming parameter `Arg {n} [off]` of shape `t` becomes a Make-tree whose leaves
read the parameter's image at the leaves' offsets; the tree builds the decoded parameter
(`build_decode`). `obl_select`: a call result `SelectN [i] c` becomes a Make-tree over the
register pieces `SelectN [first + j] c` of the converted call, which build the result back
(`build_leafVals`; a register of shape `rt` holds a piece of shape `lt` without loss,
`regShapeOK`); the call's memory `SelectN [#outs] c` becomes `SelectN [#pieces] c`.

Both need, beyond `Obl`, the IDs of the values they evaluate: the source value's (`u.id = x`)
and those of the target's tree nodes, given by a predicate `L` that holds at `x` and is closed
under new arguments (`L := Listed g`, with `WF` of `g`).
-/

namespace GoFV.Proof.EC

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.ECCheck GoFV.Proof.ABI GoFV.Proof.AtomSim

theorem ecA_retype_poison (t : Ty) : Val.poison.retype t = .poison := by cases t <;> rfl

/-! ## Reading parameters -/

theorem ecA_evalOp_arg {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val} {ty : Ty}
    {n : AuxRef} (h : v.op = .Arg) (hax : v.aux = some n) :
    evalOp env ctx fr v argv ty = argVal ctx fr n v.auxInt.toInt ty := by
  unfold evalOp
  rw [h]
  dsimp only
  rw [hax]

theorem ecA_evalOp_argInt {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} {n : AuxRef} {off : Int} {ad : AuxDef} (h : v.op = .ArgIntReg)
    (had : v.aux.bind ctx.tabs.aux? = some ad) (hk : ad.kind = .nameOff n off) :
    evalOp env ctx fr v argv ty = argVal ctx fr n off ty := by
  unfold evalOp
  rw [h]
  dsimp only
  rw [had]
  obtain ⟨k, _⟩ := ad
  cases hk
  rfl

theorem ecA_evalOp_argFloat {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} {n : AuxRef} {off : Int} {ad : AuxDef} (h : v.op = .ArgFloatReg)
    (had : v.aux.bind ctx.tabs.aux? = some ad) (hk : ad.kind = .nameOff n off) :
    evalOp env ctx fr v argv ty = .ok (match argVal ctx fr n off ty with
      | .ok x => x
      | _ => .poison) := by
  unfold evalOp
  rw [h]
  dsimp only
  unfold argFloat
  rw [had]
  obtain ⟨k, _⟩ := ad
  cases hk
  rfl

/-- What `argVal` reads of a parameter's image `img`. -/
def ecA_argImg (img : Array Byte) (off : Int) (ty : Ty) : Val :=
  if off < 0 || img.size < off.toNat + ty.size then .poison else decode img off.toNat ty

theorem ecA_argVal_img {ctx : Ctx} {fr : Frame} {n : AuxRef} {off : Int} {ty : Ty} {i : Nat}
    {img : Array Byte} (hi : ctx.params.findIdx? (· == some n) = some i)
    (himg : fr.images[i]? = some img) : argVal ctx fr n off ty = .ok (ecA_argImg img off ty) := by
  unfold argVal ecA_argImg
  rw [hi]
  dsimp only
  rw [himg]
  dsimp only
  split <;> rfl

/-- A value that reads parameter `n` at `off` (`argLeavesOK`). -/
def EcAArgLeaf (tabs : Tables) (n : AuxRef) (off : Int) (w : Value) : Prop :=
  ((w.op = .ArgIntReg ∨ w.op = .ArgFloatReg) ∧
    ∃ ad, w.aux.bind tabs.aux? = some ad ∧ ad.kind = .nameOff n off) ∨
  (w.op = .Arg ∧ w.aux = some n ∧ w.auxInt.toInt = off)

theorem ecA_argLeaf_eval {env : Env} {tabs : Tables} {g : Func} {T : Frame} {n : AuxRef}
    {off : Int} {i : Nat} {img : Array Byte} {wl : Value}
    (hi : (Ctx.make tabs g).params.findIdx? (· == some n) = some i)
    (himg : T.images[i]? = some img) (hc : EcAArgLeaf tabs n off wl)
    (hr : ∀ a ∈ wl.args, Reg T a) :
    evalValue env (Ctx.make tabs g) T wl =
      .ok ((ecA_argImg img off ((Ctx.make tabs g).tys[wl.id]?.getD .other)).retype
        ((Ctx.make tabs g).tys[wl.id]?.getD .other)) := by
  rw [evalValue_of_regs hr]
  rcases hc with ⟨hop | hop, ad, had, hk⟩ | ⟨hop, hax, hoff⟩
  · rw [ecA_evalOp_argInt hop had hk, ecA_argVal_img hi himg]; rfl
  · rw [ecA_evalOp_argFloat hop had hk, ecA_argVal_img hi himg]; rfl
  · rw [ecA_evalOp_arg hop hax, ecA_argVal_img hi himg, hoff]; rfl

theorem ecA_argLeaves_forall₂ {tabs : Tables} {g : Func} {n : AuxRef} {off : Int} :
    ∀ {L : List (Nat × Ty)} {ls : List ID}, argLeavesOK tabs g n off L ls = true →
      List.Forall₂ (fun e l => ∃ wl, g.value? l = some wl ∧ EcAArgLeaf tabs n (off + e.1) wl) L ls
  | [], [], _ => .nil
  | (o, lt) :: L, l :: ls, h => by
    simp only [argLeavesOK, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    refine .cons ?_ (ecA_argLeaves_forall₂ h2)
    split at h1
    · rename_i wl hwl
      refine ⟨wl, hwl, ?_⟩
      split at h1
      · -- ArgIntReg
        rename_i hop
        split at h1
        · rename_i ad n' off' had
          simp only [Bool.and_eq_true, beq_iff_eq] at h1
          obtain ⟨rfl, rfl⟩ := h1
          exact .inl ⟨.inl hop, _, had, rfl⟩
        · cases h1
      · -- ArgFloatReg
        rename_i hop
        split at h1
        · rename_i ad n' off' had
          simp only [Bool.and_eq_true, beq_iff_eq] at h1
          obtain ⟨rfl, rfl⟩ := h1
          exact .inl ⟨.inr hop, _, had, rfl⟩
        · cases h1
      · rename_i hop
        simp only [Bool.and_eq_true, beq_iff_eq] at h1
        exact .inr ⟨hop, h1.1, h1.2⟩
      · cases h1
    · cases h1
  | [], _ :: _, h => by simp [argLeavesOK] at h
  | _ :: _, [], h => by simp [argLeavesOK] at h

/-- The leaves of the Make-tree of a parameter in range read its decoded pieces. -/
theorem ecA_arg_ys {env : Env} {tabs : Tables} {g : Func} {T : Frame} {n : AuxRef} {off : Int}
    {i : Nat} {img : Array Byte} {t : Ty} {ls : List ID} {ys : List Val}
    (hwf : wf t = true) (hoff : 0 ≤ off) (hsz : off.toNat + t.size ≤ img.size)
    (hi : (Ctx.make tabs g).params.findIdx? (· == some n) = some i)
    (himg : T.images[i]? = some img)
    (F : List.Forall₂ (EcTLeaf env tabs g T) ls ys) (S : List.Forall₂ (EcTShape tabs g) ls (leaves t))
    (A : List.Forall₂ (fun e l => ∃ wl, g.value? l = some wl ∧ EcAArgLeaf tabs n (off + e.1) wl)
      (leaves t) ls) :
    ys = (leaves t).map fun (o, lt) => decode img (off.toNat + o) lt := by
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_map]
  cases hk : ys[k]? with
  | none =>
    have hle : (leaves t).length ≤ k := by
      have := List.getElem?_eq_none_iff.1 hk
      rw [← F.length_eq, S.length_eq] at this
      exact this
    rw [List.getElem?_eq_none_iff.2 hle]
    rfl
  | some yl =>
    obtain ⟨l, hl, wl, hwl, hid, hev⟩ := ecT_forall₂_get' F k yl hk
    obtain ⟨⟨o, lt⟩, he, hsh⟩ := ecT_forall₂_get S k l hl
    obtain ⟨e', he', wl', hwl', hc⟩ := ecT_forall₂_get' A k l hl
    rw [he] at he'
    cases he'
    rw [hwl] at hwl'
    cases hwl'
    have hm := mem_leaves hwf (List.mem_of_getElem? he)
    dsimp only at hm hc
    rw [ecA_argLeaf_eval hi himg hc (regs_of_ok hev)] at hev
    cases hev
    have hty : (Ctx.make tabs g).tys[wl.id]?.getD .other = shapeOf (typeShapes tabs) g l := by
      rw [hid, shapeOf_eq]
    have hsh' : eqE (shapeOf (typeShapes tabs) g l) lt = true := hsh
    rw [hty, he]
    show some _ = some (decode img (off.toNat + o) lt)
    have hs := ecT_eqE_size hsh'
    have hto : (off + (o : Int)).toNat = off.toNat + o := by omega
    have hc' : (decide (off + (o : Int) < 0) ||
        decide (img.size < (off + (o : Int)).toNat + (shapeOf (typeShapes tabs) g l).size)) = false := by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
      omega
    unfold ecA_argImg
    simp only [hc', Bool.false_eq_true, ite_false]
    rw [hto, ecT_eqE_decode hsh', eqE_retype hsh',
      Val.retype_of_hasTy (decode_hasTy (wf_atom hm.2))]

theorem ecA_arg_not_special {f g : Func} {x : ID} {u : Value} (hu : f.value? x = some u)
    (hop : u.op = .Arg) (hinv : invalidated g x = false) : special f g x = false := by
  unfold special converted
  rw [hu, hinv]
  dsimp only
  rw [hop]
  rfl

/-- **The obligation of a parameter.** -/
theorem obl_arg {tabs : Tables} {f g : Func} {x : ID} {u w : Value} {HS HT : ID → Prop}
    (hu : f.value? x = some u) (hw : g.value? x = some w) (hop : u.op = .Arg)
    (hinv : invalidated g x = false) (hid : identOK f g u w = false)
    (hok : argOK tabs (typeShapes tabs) f g x u = true) (hown : g.ownAux = f.ownAux)
    (huid : u.id = x) (L : ID → Prop) (hLx : L x)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true → L a) :
    Obl tabs f g (ecCv tabs f g) (isNewB f) (ecFront f g x) HS HT x := by
  intro u' w' hu' hw' env _ frS T hT _ E hN hEw hRT hRS _ _ _
  rw [hu] at hu'
  cases hu'
  rw [hw] at hw'
  cases hw'
  rw [funext (ecCv_of_not_special (tabs := tabs) (ecA_arg_not_special hu hop hinv))]
  unfold argOK at hok
  cases hax : u.aux with
  | none => rw [hax] at hok; cases hok
  | some n =>
  rw [hax] at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨hwf, -⟩, hok⟩ := hok
  cases hmt : mkTree (typeShapes tabs) g (isNewB f) (tabs.types.size + 1) x
      (shapeOf (typeShapes tabs) f x) with
  | none => rw [hmt] at hok; cases hok
  | some ls =>
  rw [hmt] at hok
  have A := ecA_argLeaves_forall₂ hok
  have htS : (Ctx.make tabs f).tys[u.id]?.getD .other = shapeOf (typeShapes tabs) f x := by
    rw [huid, shapeOf_eq]
  rw [evalValue_of_regs hRS, ecA_evalOp_arg hop hax, htS]
  have hpar : (Ctx.make tabs g).params = (Ctx.make tabs f).params := by
    rw [ctx_eq (tabs := tabs) hown.symm]
  have hTi : T.images = frS.images := by rw [hT]
  cases hi : (Ctx.make tabs f).params.findIdx? (· == some n) with
  | none =>
    unfold argVal
    rw [hi]
    exact .stuck _ _
  | some i =>
  cases himg : frS.images[i]? with
  | none =>
    unfold argVal
    rw [hi]
    dsimp only
    rw [himg]
    exact .stuck _ _
  | some img =>
  rw [ecA_argVal_img hi himg]
  have hiG : (Ctx.make tabs g).params.findIdx? (· == some n) = some i := by rw [hpar]; exact hi
  have himgT : T.images[i]? = some img := by rw [hTi]; exact himg
  obtain ⟨yT, hevT⟩ := ecT_root_ok (env := env) (T := T) hmt hw hRT fun hx => by
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hx
    obtain ⟨e, -, wl, hwl, hc⟩ := ecT_forall₂_get' A k x hk
    rw [hw] at hwl
    cases hwl
    exact ⟨_, ecA_argLeaf_eval hiG himgT hc hRT⟩
  rw [hevT]
  refine .ok ?_
  obtain ⟨ys, F, S, hyT⟩ := ecT_node hN hL _ x _ ls w yT hmt hw hLx hEw hevT
  show Sem.Refines ((ecA_argImg img u.auxInt.toInt (shapeOf (typeShapes tabs) f x)).retype
    (shapeOf (typeShapes tabs) f x)) yT
  unfold ecA_argImg
  split
  · rw [ecA_retype_poison]; exact .poison _
  · rename_i hc
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Int.not_lt, Nat.not_lt] at hc
    rw [hyT, ecA_arg_ys hwf hc.1 hc.2 hiG himgT F S A, build_decode hwf]
    exact Sem.Refines.refl _

/-! ## Call results -/

/-- `convTuple`'s components (`ECDefs`): the register pieces of the results, then the rest. -/
def ecA_convList (tabs : Tables) : List ABIParam → List Val → List Val
  | [], vs => vs
  | p :: ps, v :: vs => regLeafVals tabs p v ++ ecA_convList tabs ps vs
  | _ :: _, [] => []

theorem ecA_convTuple_eq (tabs : Tables) :
    ∀ (ps : List ABIParam) (vs : List Val), convTuple tabs ps (.tuple vs) = .tuple (ecA_convList tabs ps vs)
  | [], vs => by simp [convTuple, ecA_convList]
  | p :: ps, v :: vs => by
    have ih := ecA_convTuple_eq tabs ps vs
    unfold convTuple at ih ⊢
    simp only [Val.tuple.injEq] at ih
    simp only [List.zip_cons_cons, List.flatMap_cons, List.length_cons, List.drop_succ_cons,
      List.append_assoc, ih, ecA_convList]
  | _ :: _, [] => by simp [convTuple, ecA_convList]

theorem ecA_convList_length (tabs : Tables) :
    ∀ (ps : List ABIParam) (vs : List Val), (∀ p ∈ ps, wf (tabs.ty p.type) = true) →
      ps.length ≤ vs.length →
      (ecA_convList tabs ps vs).length = (leafTys tabs ps).length + (vs.length - ps.length)
  | [], vs, _, _ => by simp [ecA_convList, leafTys]
  | p :: ps, v :: vs, hw, hl => by
    have ih := ecA_convList_length tabs ps vs (fun q hq => hw q (List.mem_cons_of_mem _ hq))
      (by simpa using hl)
    cases h : p.regs.isEmpty
    · simp only [ecA_convList, regLeafVals_reg h, leafTys_cons_reg tabs h, List.length_append,
        List.length_map, leafVals_length (hw p List.mem_cons_self), ih, List.length_cons]
      omega
    · simp only [ecA_convList, regLeafVals_stack h, leafTys_cons_stack tabs h, List.nil_append, ih,
        List.length_cons]
      omega
  | _ :: _, [], _, hl => by simp at hl

/-- The component after the pieces is the memory. -/
theorem ecA_convList_rest (tabs : Tables) :
    ∀ (ps : List ABIParam) (vs : List Val), (∀ p ∈ ps, wf (tabs.ty p.type) = true) →
      ps.length ≤ vs.length → ∀ j,
      (ecA_convList tabs ps vs)[(leafTys tabs ps).length + j]? = vs[ps.length + j]?
  | [], vs, _, _, j => by simp [ecA_convList, leafTys]
  | p :: ps, v :: vs, hw, hl, j => by
    have ih := ecA_convList_rest tabs ps vs (fun q hq => hw q (List.mem_cons_of_mem _ hq))
      (by simpa using hl) j
    cases h : p.regs.isEmpty
    · have hlv := leafVals_length (v := v) (hw p List.mem_cons_self)
      rw [ecA_convList, regLeafVals_reg h, leafTys_cons_reg tabs h, List.length_append,
        List.length_map, Nat.add_assoc, List.getElem?_append_right (by omega), hlv,
        Nat.add_sub_cancel_left, ih, List.length_cons, Nat.add_right_comm, List.getElem?_cons_succ]
    · rw [ecA_convList, regLeafVals_stack h, leafTys_cons_stack tabs h, List.nil_append, ih,
        List.length_cons, Nat.add_right_comm, List.getElem?_cons_succ]
  | _ :: _, [], _, hl, _ => by simp at hl

/-- The pieces of register-assigned result `i`. -/
theorem ecA_convList_piece (tabs : Tables) :
    ∀ (i : Nat) (ps : List ABIParam) (vs : List Val) (p : ABIParam) (v : Val),
      (∀ q ∈ ps, wf (tabs.ty q.type) = true) → ps[i]? = some p → vs[i]? = some v →
      p.regs.isEmpty = false →
      ∀ j, j < (leaves (tabs.ty p.type)).length →
      (ecA_convList tabs ps vs)[(leafTys tabs (ps.take i)).length + j]? =
        (leafVals (tabs.ty p.type) v)[j]?
  | 0, p' :: ps, v' :: vs, p, v, hw, hp, hv, hpr, j, hj => by
    cases hp
    cases hv
    have hlv := leafVals_length (v := v') (hw p' List.mem_cons_self)
    rw [ecA_convList, regLeafVals_reg hpr, List.take_zero, leafTys_nil, List.length_nil,
      Nat.zero_add, List.getElem?_append_left (by omega)]
  | i + 1, p' :: ps, v' :: vs, p, v, hw, hp, hv, hpr, j, hj => by
    have ih := ecA_convList_piece tabs i ps vs p v (fun q hq => hw q (List.mem_cons_of_mem _ hq))
      hp hv hpr j hj
    cases h : p'.regs.isEmpty
    · have hlv := leafVals_length (v := v') (hw p' List.mem_cons_self)
      rw [ecA_convList, regLeafVals_reg h, List.take_succ_cons, leafTys_cons_reg tabs h,
        List.length_append, List.length_map, Nat.add_assoc, List.getElem?_append_right (by omega),
        hlv, Nat.add_sub_cancel_left]
      exact ih
    · rw [ecA_convList, regLeafVals_stack h, List.take_succ_cons, leafTys_cons_stack tabs h,
        List.nil_append]
      exact ih
  | _, [], _, _, _, _, hp, _, _, _, _ => by simp at hp
  | 0, _ :: _, [], _, _, _, _, hv, _, _, _ => by simp at hv
  | _ + 1, _ :: _, [], _, _, _, _, hv, _, _, _ => by simp at hv

/-- The leaf shapes of register-assigned result `i`. -/
theorem ecA_leafTys_piece (tabs : Tables) :
    ∀ (i : Nat) (ps : List ABIParam) (p : ABIParam), ps[i]? = some p → p.regs.isEmpty = false →
      ∀ j, j < (leaves (tabs.ty p.type)).length →
      (leafTys tabs ps)[(leafTys tabs (ps.take i)).length + j]? =
        ((leaves (tabs.ty p.type)).map (·.2))[j]?
  | 0, p' :: ps, p, hp, hpr, j, hj => by
    cases hp
    rw [List.take_zero, leafTys_nil, List.length_nil, Nat.zero_add, leafTys_cons_reg tabs hpr]
    rw [List.getElem?_append_left (by simpa using hj)]
  | i + 1, p' :: ps, p, hp, hpr, j, hj => by
    cases h : p'.regs.isEmpty
    · rw [List.take_succ_cons, leafTys_cons_reg tabs h, leafTys_cons_reg tabs h, List.length_append,
        Nat.add_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
      exact ecA_leafTys_piece tabs i ps p hp hpr j hj
    · rw [List.take_succ_cons, leafTys_cons_stack tabs h, leafTys_cons_stack tabs h]
      exact ecA_leafTys_piece tabs i ps p hp hpr j hj
  | _, [], _, hp, _, _, _ => by simp at hp

theorem ecA_hasTyPre_get :
    ∀ {vs : List Val} {us : List Ty}, Val.hasTyPre vs us = true →
      us.length ≤ vs.length ∧ ∀ (k : Nat) (a : Ty) (b : Val), us[k]? = some a → vs[k]? = some b → b.hasTy a = true
  | _, [], _ => ⟨Nat.zero_le _, fun _ _ _ h => by simp at h⟩
  | v :: vs, u :: us, h => by
    simp only [Val.hasTyPre, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := ecA_hasTyPre_get h.2
    refine ⟨by simpa using h1, fun k a b ha hb => ?_⟩
    cases k with
    | zero => cases ha; cases hb; exact h.1
    | succ k => exact h2 k a b ha hb
  | [], _ :: _, h => by simp [Val.hasTyPre] at h

theorem ecA_retypePre_get :
    ∀ {ts : List Ty} {vs : List Val}, ts.length ≤ vs.length →
      ∃ vs', Val.retypePre ts vs = some vs' ∧
        ∀ (k : Nat) (a : Ty) (b : Val), ts[k]? = some a → vs[k]? = some b →
          vs'[k]? = some (b.retype a)
  | [], vs, _ => ⟨vs, rfl, fun _ _ _ h => by simp at h⟩
  | t :: ts, v :: vs, hl => by
    obtain ⟨vs', h, hg⟩ := ecA_retypePre_get (ts := ts) (vs := vs) (by simpa using hl)
    refine ⟨v.retype t :: vs', by simp only [Val.retypePre, h, Option.map_some], ?_⟩
    intro k a b ha hb
    cases k with
    | zero => cases ha; cases hb; rfl
    | succ k => exact hg k a b ha hb
  | _ :: _, [], hl => by simp at hl

theorem ecA_tupleOf_get {ts : List Ty} {t : Ty} (h : tupleOf ts t = true) :
    ∃ us, t = .tuple us ∧ us.length = ts.length + 1 ∧
      (∀ (k : Nat) (a b : Ty), ts[k]? = some a → us[k]? = some b → eqE b a = true) ∧ us[ts.length]? = some .mem := by
  unfold tupleOf at h
  split at h
  · rename_i us
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨hl, hz⟩, hm⟩ := h
    refine ⟨us, rfl, hl, fun k a b ha hb => ?_, ?_⟩
    · have hmem : (a, b) ∈ ts.zip us :=
        List.mem_of_getElem? (List.getElem?_zip_eq_some.2 ⟨ha, hb⟩)
      exact hz _ hmem
    · split at hm
      · rename_i hlast
        rw [List.getLast?_eq_getElem?, hl, Nat.add_sub_cancel] at hlast
        exact hlast
      · cases hm
  · cases h

theorem ecA_regTupleOf_get {lts : List Ty} {t : Ty} (h : regTupleOf lts t = true) :
    ∃ rus, t = .tuple rus ∧ rus.length = lts.length + 1 ∧
      (∀ (k : Nat) (lt rt : Ty), lts[k]? = some lt → rus[k]? = some rt →
        regShapeOK rt lt = true) ∧
      rus[lts.length]? = some .mem := by
  unfold regTupleOf at h
  split at h
  · rename_i us
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨hl, hz⟩, hm⟩ := h
    refine ⟨us, rfl, hl, fun k a b ha hb => ?_, ?_⟩
    · have hmem : (a, b) ∈ lts.zip us :=
        List.mem_of_getElem? (List.getElem?_zip_eq_some.2 ⟨ha, hb⟩)
      exact hz _ hmem
    · split at hm
      · rename_i hlast
        rw [List.getLast?_eq_getElem?, hl, Nat.add_sub_cancel] at hlast
        exact hlast
      · cases hm
  · cases h

/-- A register of shape `rt` holds a piece of shape `lt` without loss. -/
theorem ecA_regShape {rt lt : Ty} {a : Val} (h : regShapeOK rt lt = true) (ha : a.hasTy lt = true) :
    (a.retype rt).retype lt = a := by
  unfold regShapeOK at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · rw [Ty.eq_of_beq h, Val.retype_of_hasTy ha, Val.retype_of_hasTy ha]
  · split at h
    · cases a with
      | poison => rfl
      | ptr q => rfl
      | _ => simp [Val.hasTy] at ha
    · cases a with
      | poison => rfl
      | int w x =>
        simp only [Val.hasTy, beq_iff_eq] at ha
        subst ha
        show Val.retype (.int .w64) (.ptr (Ptr.ofAddr x)) = _
        simp only [Val.retype, GoFV.Proof.CSE.Mem.addr_ofAddr]
      | ptr q =>
        simp only [Val.hasTy, Option.isNone_iff_eq_none] at ha
        show Val.retype (.int .w64) (.ptr q) = _
        simp only [Val.retype, ha]
      | _ => simp [Val.hasTy] at ha
    · cases h

theorem ecA_selLeaves_get {g : Func} {c : ID} {first : Nat} :
    ∀ {j : Nat} {ls : List ID}, selLeavesOK g c first j ls = true → ∀ k l, ls[k]? = some l →
      ∃ wl, g.value? l = some wl ∧ wl.op = .SelectN ∧ wl.args.toList = [c] ∧
        wl.auxInt.toInt = ((first + (j + k) : Nat) : Int)
  | _, [], _, _, _, hl => by simp at hl
  | j, l :: ls, h, k, l', hl => by
    simp only [selLeavesOK, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases k with
    | zero =>
      cases hl
      split at h1
      · rename_i wl hwl
        simp only [Bool.and_eq_true, beq_iff_eq] at h1
        exact ⟨wl, hwl, h1.1.1, h1.1.2, by rw [h1.2]; rfl⟩
      · cases h1
    | succ k =>
      obtain ⟨wl, hwl, h⟩ := ecA_selLeaves_get h2 k l' hl
      exact ⟨wl, hwl, by rw [show j + (k + 1) = j + 1 + k by omega]; exact h⟩

theorem ecA_cv_call {tabs : Tables} {f g : Func} {c : ID} {cu : Value} (hcu : f.value? c = some cu)
    (hcall : (callOpMap cu.op).isSome = true) (hinv : invalidated g c = false) (y : Val) :
    ecCv tabs f g c y =
      (convTuple tabs (callOuts tabs cu.aux) y).retype (shapeOf (typeShapes tabs) g c) := by
  unfold ecCv
  rw [hinv, hcu]
  simp only [Bool.false_eq_true, ite_false, hcall, ite_true]

theorem ecA_callOK_facts {tabs : Tables} {f g : Func} {c : ID} {cu cw : Value}
    (hcw : g.value? c = some cw) (h : callOK tabs (typeShapes tabs) f g cu cw = true) :
    invalidated g c = false ∧ outsOK tabs (callOuts tabs cu.aux) = true ∧
      tupleOf ((callOuts tabs cu.aux).map (tabs.ty ·.type)) (valueTy (typeShapes tabs) (some cu)) = true ∧
      regTupleOf (leafTys tabs (callOuts tabs cu.aux)) (valueTy (typeShapes tabs) (some cw)) = true := by
  unfold callOK at h
  split at h
  · rename_i op k abi hop habi
    simp only [Bool.and_eq_true, and_assoc] at h
    have houts : callOuts tabs cu.aux = outsOf abi := by
      unfold callOuts; rw [habi]; rfl
    rw [houts]
    obtain ⟨hwop, -, -, -, hreg, -, -, -, -, -, -, -, -, htup, hrtup⟩ := h
    rw [beq_iff_eq] at hwop
    refine ⟨?_, hreg, htup, hrtup⟩
    unfold invalidated
    rw [hcw]
    dsimp only
    rw [hwop]
    unfold callOpMap at hop
    split at hop <;> cases hop <;> rfl
  · cases h

theorem ecA_selectN_tuple {ai : Int64} {vs : List Val} {k : Nat} (h : ai.toInt = (k : Int)) :
    Tuple.selectN ai [.tuple vs] = vs.getD k .poison := by
  have hk : ¬ ((k : Int) < 0) := by omega
  simp [Tuple.selectN, h, hk]

theorem ecA_lt_of_getElem? {α : Type} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) :
    i < l.length := by
  rcases Nat.lt_or_ge i l.length with h' | h'
  · exact h'
  · rw [List.getElem?_eq_none_iff.2 h'] at h; cases h

theorem ecA_selectN_poison (ai : Int64) : Tuple.selectN ai [.poison] = .poison := rfl

theorem ecA_tuple_cases {y : Val} {us : List Ty} (h : y.hasTy (.tuple us) = true) :
    y = .poison ∨ ∃ vs, y = .tuple vs ∧ Val.hasTyPre vs us = true := by
  cases y <;> simp_all [Val.hasTy]

theorem ecA_sel_not_special {f g : Func} {x : ID} {u : Value} (hu : f.value? x = some u)
    (hop : u.op = .SelectN) (hinv : invalidated g x = false) : special f g x = false := by
  unfold special converted
  rw [hu, hinv]
  dsimp only
  rw [hop]
  rfl

/-- **The obligation of a call result** assigned to registers (or the call's memory). -/
theorem obl_select {tabs : Tables} {f g : Func} {x : ID} {u w : Value} {c : ID} {cu cw : Value} {HS HT : ID → Prop}
    (hu : f.value? x = some u) (hw : g.value? x = some w) (hop : u.op = .SelectN)
    (hargs : u.args.toList = [c]) (hcu : f.value? c = some cu) (hcw : g.value? c = some cw)
    (hcall : (callOpMap cu.op).isSome = true)
    (hcok : callOK tabs (typeShapes tabs) f g cu cw = true)
    (hinv : invalidated g x = false) (hok : selectOK tabs (typeShapes tabs) f g x u w = true)
    (hreg : ∀ p, (callOuts tabs cu.aux)[u.auxInt.toInt.toNat]? = some p → p.regs.isEmpty = false)
    (hown : g.ownAux = f.ownAux)
    (huid : u.id = x) (L : ID → Prop) (hLx : L x)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true → L a) :
    Obl tabs f g (ecCv tabs f g) (isNewB f) (ecFront f g x) HS HT x := by
  intro u' w' hu' hw' env _ frS T _ hRegs E hN hEw hRT hRS hfr _ _
  rw [hu] at hu'
  cases hu'
  rw [hw] at hw'
  cases hw'
  rw [funext (ecCv_of_not_special (tabs := tabs) (ecA_sel_not_special hu hop hinv))]
  have hcmem : c ∈ u.args := Array.mem_toList_iff.1 (by rw [hargs]; exact List.mem_singleton.2 rfl)
  obtain ⟨yc, hyc⟩ := hRS c hcmem
  obtain ⟨yc', hyc', hR⟩ := hfr c (by simp [ecFront, hinv, hu, hargs]) yc hyc
  obtain ⟨hinvc, hoo, htup, hrtup⟩ := ecA_callOK_facts hcw hcok
  have hwfo := ec_outsOK_wf hoo
  rw [ecA_cv_call hcu hcall hinvc, ecT_shapeOf_value hcw] at hR
  obtain ⟨us, hus, husl, huse, husm⟩ := ecA_tupleOf_get htup
  obtain ⟨rus, hrus, hrusl, hrusr, hrusm⟩ := ecA_regTupleOf_get hrtup
  rw [hrus] at hR
  rw [List.length_map] at husl husm
  have hycT : yc.hasTy (.tuple us) = true := by
    have h1 := (hRegs c yc hyc).1
    rw [tys_of_value hcu, Option.getD_some] at h1
    rw [← hus]
    simpa only [valueTy, typeShapes_getD] using h1
  have hwid : w.id = x := (hL x hLx w hw).1
  have htS : (Ctx.make tabs f).tys[u.id]?.getD .other = shapeOf (typeShapes tabs) f x := by
    rw [huid, shapeOf_eq]
  rw [ecT_eval_selectN hop hRS, hargs, List.map_cons, List.map_nil, rv_of hyc, htS]
  -- the call's tuple after conversion
  have hconv : ∀ vs, Val.hasTyPre vs us = true → yc = .tuple vs → ∃ D, yc' = .tuple D ∧
      ∃ C', RefinesList C' D ∧ ∀ (k : Nat) (a : Ty) (b : Val), rus[k]? = some a →
        (ecA_convList tabs (callOuts tabs cu.aux) vs)[k]? = some b → C'[k]? = some (b.retype a) := by
    intro vs hvs hycv
    have hl := (ecA_hasTyPre_get hvs).1
    rw [hycv, ecA_convTuple_eq] at hR
    have hCl := ecA_convList_length tabs _ vs hwfo (by omega)
    obtain ⟨C', hC', hg⟩ := ecA_retypePre_get (ts := rus)
      (vs := ecA_convList tabs (callOuts tabs cu.aux) vs) (by omega)
    have hre : (Val.tuple (ecA_convList tabs (callOuts tabs cu.aux) vs)).retype (.tuple rus) =
        .tuple C' := by simp only [Val.retype, hC']
    rw [hre] at hR
    cases hR with
    | tuple hRL => exact ⟨_, rfl, C', hRL, hg⟩
  unfold selectOK at hok
  rw [hargs] at hok
  dsimp only at hok
  rw [hcu] at hok
  dsimp only at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨-, hi0⟩, hok⟩ := hok
  have hi0' : 0 ≤ u.auxInt.toInt := by simpa using hi0
  split at hok
  · -- the call's memory
    rename_i hif
    have hi : u.auxInt.toInt = ((callOuts tabs cu.aux).length : Int) := by
      have := beq_iff_eq.1 hif
      omega
    simp only [Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨⟨hwop, hwargs⟩, hwty⟩, hwai⟩ := hok
    have hty : valueTy (typeShapes tabs) (some w) = shapeOf (typeShapes tabs) f x := by
      rw [ecT_shapeOf_value hu]; simp only [valueTy, hwty]
    rw [ecT_eval_selectN hwop hRT, hwargs, List.map_cons, List.map_nil, rv_of hyc', hwid,
      ← shapeOf_eq, ecT_shapeOf_value hw, hty]
    refine .ok (Sem.retype_mono _ ?_)
    rcases ecA_tuple_cases hycT with rfl | ⟨vs, rfl, hvs⟩
    · rw [ecA_selectN_poison]; exact .poison _
    · obtain ⟨hl, hget⟩ := ecA_hasTyPre_get hvs
      obtain ⟨D, rfl, C', hRL, hg⟩ := hconv vs hvs rfl
      obtain ⟨vm, hvm⟩ : ∃ vm, vs[(callOuts tabs cu.aux).length]? = some vm :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hvmT := hget _ _ _ husm hvm
      have hC := ecA_convList_rest tabs _ vs hwfo (by omega) 0
      rw [Nat.add_zero, Nat.add_zero, hvm] at hC
      have hC' := hg _ _ _ hrusm hC
      rw [Val.retype_of_hasTy hvmT] at hC'
      obtain ⟨d, hd, hRd⟩ := ecT_refinesList_get hRL _ _ hC'
      rw [ecA_selectN_tuple hi, ecA_selectN_tuple hwai, List.getD_eq_getElem?_getD, hvm,
        List.getD_eq_getElem?_getD, hd]
      exact hRd
  · -- a result: a Make-tree of its pieces
    rename_i hif
    have hi : u.auxInt.toInt = ((u.auxInt.toInt.toNat : Nat) : Int) := by omega
    cases hp : (callOuts tabs cu.aux)[u.auxInt.toInt.toNat]? with
    | none => rw [hp] at hok; cases hok
    | some p =>
    rw [hp] at hok
    dsimp only at hok
    simp only [Bool.and_eq_true] at hok
    obtain ⟨heq, hok⟩ := hok
    cases hmt : mkTree (typeShapes tabs) g (isNewB f) (tabs.types.size + 1) x (tabs.ty p.type) with
    | none => rw [hmt] at hok; cases hok
    | some ls =>
    rw [hmt] at hok
    dsimp only at hok
    simp only [Bool.and_eq_true] at hok
    have hpr := hreg p hp
    obtain ⟨-, hsel⟩ := hok
    rw [hpr] at hsel
    simp only [Bool.false_eq_true, ↓reduceIte] at hsel
    obtain ⟨yT, hevT⟩ := ecT_root_ok (env := env) (T := T) hmt hw hRT fun hx => by
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hx
      obtain ⟨wl, hwl, hwop, -⟩ := ecA_selLeaves_get hsel k x hk
      rw [hw] at hwl
      cases hwl
      exact ⟨_, ecT_eval_selectN hwop hRT⟩
    rw [hevT]
    refine .ok ?_
    obtain ⟨ys, F, S, hyT⟩ := ecT_node hN hL _ x _ ls w yT hmt hw hLx hEw hevT
    rw [eqE_retype heq, hyT]
    have hwf := hwfo p (List.mem_of_getElem? hp)
    rcases ecA_tuple_cases hycT with rfl | ⟨vs, rfl, hvs⟩
    · rw [ecA_selectN_poison, ecA_retype_poison]; exact .poison _
    · obtain ⟨hl, hget⟩ := ecA_hasTyPre_get hvs
      obtain ⟨D, rfl, C', hRL, hg⟩ := hconv vs hvs rfl
      have hilt := ecA_lt_of_getElem? hp
      obtain ⟨v, hv⟩ : ∃ v, vs[u.auxInt.toInt.toNat]? = some v :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨ui, hui⟩ : ∃ ui, us[u.auxInt.toInt.toNat]? = some ui :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hvt : v.hasTy (tabs.ty p.type) = true := by
        rw [← eqE_hasTy (huse _ _ _ (by rw [List.getElem?_map, hp]; rfl) hui)]
        exact hget _ _ _ hui hv
      rw [ecA_selectN_tuple hi, List.getD_eq_getElem?_getD, hv, Option.getD_some,
        Val.retype_of_hasTy hvt]
      refine Sem.Refines.trans (b := (build (tabs.ty p.type) (leafVals (tabs.ty p.type) v)).retype
        (tabs.ty p.type)) ?_ (Sem.retype_mono _ (build_mono ?_))
      · have := Sem.retype_mono (tabs.ty p.type) (build_leafVals hwf hvt)
        rw [Val.retype_of_hasTy hvt] at this
        exact this
      · refine ecT_refinesList_of_get ?_ fun k a b ha hb => ?_
        · rw [leafVals_length hwf, ← S.length_eq, F.length_eq]
        obtain ⟨l, hl, wl, hwl, hid, hev⟩ := ecT_forall₂_get' F k b hb
        obtain ⟨⟨o, lt⟩, he, hsh⟩ := ecT_forall₂_get S k l hl
        have hsh' : eqE (shapeOf (typeShapes tabs) g l) lt = true := hsh
        obtain ⟨wl', hwl', hwop, hwargs, hwai⟩ := ecA_selLeaves_get hsel k l hl
        rw [hwl] at hwl'
        cases hwl'
        have hklt := ecA_lt_of_getElem? he
        have hC := ecA_convList_piece tabs _ _ vs p v hwfo hp hv hpr k hklt
        rw [ha] at hC
        have hlt := ecA_leafTys_piece tabs _ _ p hp hpr k hklt
        rw [List.getElem?_map, he] at hlt
        have hb' : (leafTys tabs (List.take u.auxInt.toInt.toNat (callOuts tabs cu.aux))).length + k <
            rus.length := by
          have := ecA_lt_of_getElem? hlt
          omega
        obtain ⟨rt, hrt⟩ : ∃ rt, rus[(leafTys tabs (List.take u.auxInt.toInt.toNat
            (callOuts tabs cu.aux))).length + k]? = some rt := ⟨_, List.getElem?_eq_getElem hb'⟩
        have hreg := hrusr _ _ _ hlt hrt
        obtain ⟨d, hd, hRd⟩ := ecT_refinesList_get hRL _ _ (hg _ _ _ hrt hC)
        have hat : a.hasTy lt = true := by
          obtain ⟨b', hb'', hh⟩ := ecT_forall₂_get (leafVals_hasTy hwf (v := v)) k a ha
          rw [he] at hb''
          cases hb''
          exact hh
        rw [ecT_eval_selectN hwop (regs_of_ok hev), hwargs, List.map_cons, List.map_nil,
          rv_of hyc', ecA_selectN_tuple (k := (leafTys tabs (List.take u.auxInt.toInt.toNat
            (callOuts tabs cu.aux))).length + k) (by rw [hwai]; congr 1; omega),
          List.getD_eq_getElem?_getD, hd, Option.getD_some, hid, ← shapeOf_eq,
          eqE_retype hsh'] at hev
        cases hev
        have := Sem.retype_mono lt hRd
        rw [ecA_regShape hreg hat] at this
        exact this

end GoFV.Proof.EC

import GoFV.Proof.Pass.ECStack
import GoFV.Proof.Pass.ECFinish
import GoFV.Proof.CallMono
import GoFV.Proof.MemRefine

/-!
# `expand calls`: the obligations of calls and `MakeResult`s (issue #28)

`obl_call`: a call on Go-typed arguments (`StaticLECall`, `ClosureLECall`, `InterLECall`)
becomes the post-`expand calls` call on their register pieces (`ec_pieces`); the target's
`decodeArgs` rebuilds arguments refining the source's (`ofPieces_leafVals`), the same callee's
contract sees refined arguments and memory (`Contract.Mono`), and the target's result pieces
(`encodeResults`, `toPieces = leafVals`) refine the conversion `convTuple` of the source's
Go-typed results. `obl_result`: a `MakeResult` of Go-typed results becomes one of their pieces.

Both are proved first in the form `EcOblImk`, `Obl` with the frame facts of the `IMake` data
shortcut (`EcImkFacts`); `obl_call`/`obl_result` are the `Obl`s when every `IMake` argument is
held (`EcoImkHeld`) in target mode (it and its data operand among the target's held values,
interface-shaped in `g`) or source mode (it among the source's held values, the same `IMake`
in `f`; `obl_of_imk`).
-/

namespace GoFV.Proof.EC

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.ECCheck GoFV.Proof.ABI GoFV.Proof.AtomSim

/-! ## Argument lists -/

private theorem lsplit {α : Type} [Inhabited α] (l : List α) (k : Nat) (h : k + 1 ≤ l.length) :
    l = List.take k l ++ List.take (l.length - 1 - k) (List.drop k l) ++ [l[l.length - 1]!] := by
  have hne : List.drop k l ≠ [] := by
    intro h0; have := congrArg List.length h0; simp at this; omega
  rw [List.append_assoc]
  conv => lhs; rw [← List.take_append_drop k l]
  congr 1
  conv => lhs; rw [← List.dropLast_concat_getLast hne]
  congr 1
  · rw [List.dropLast_eq_take, List.length_drop]; congr 1; omega
  · rw [List.getLast_eq_getElem, List.getElem_drop, getElem!_pos l _ (by omega)]
    simp only [List.length_drop, List.cons.injEq, and_true]
    congr 1
    omega

/-- A call's arguments: the leading ones, the Go-typed ones (or pieces), the memory. -/
theorem ecc_args_split (arr : Array ID) (k : Nat) (h : k + 1 ≤ arr.size) :
    arr.toList = (arr.extract 0 k).toList ++ (arr.extract k (arr.size - 1)).toList ++
      [arr[arr.size - 1]!] := by
  rcases arr with ⟨l⟩
  simp only [List.size_toArray] at h
  simp only [Array.toList_extract, List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero,
    List.getElem!_toArray, List.size_toArray]
  exact lsplit l k h

theorem ecc_args_split1 (arr : Array ID) (h : 1 ≤ arr.size) :
    arr.toList = (arr.extract 0 (arr.size - 1)).toList ++ [arr[arr.size - 1]!] := by
  have := ecc_args_split arr 0 h
  rw [this]
  simp

theorem ecc_mem_front {f g : Func} {x a : ID} {u : Value} (hu : f.value? x = some u)
    (ha : a ∈ u.args) : a ∈ ecFront f g x := by
  unfold ecFront
  rw [hu]
  exact List.mem_append_left _ (Array.mem_toList_iff.2 ha)

theorem ecc_mem_of_split {l A B : List ID} {a : ID} (h : l = A ++ B) (ha : a ∈ A) : a ∈ l := by
  rw [h]; exact List.mem_append_left _ ha

/-! ## `Obl` with the frame facts of the `IMake` shortcut -/

/-- `Obl` of `x` for `expand calls` with the extra premise `EcImkFacts` for `x`'s source
arguments, given that the target registers of the values `H` hold their evaluations. -/
def EcOblImk (tabs : Tables) (f g : Func) (H : ID → Prop) (x : ID) : Prop :=
  ∀ u w, f.value? x = some u → g.value? x = some w →
  ∀ env : Env, env.Mono → ∀ frS T : Frame, T = { frS with regs := T.regs } →
  RegsOK (Ctx.make tabs f) frS →
  ∀ E : ID → Prop, NewCons env (Ctx.make tabs g) (isNewB f) T E →
    (∀ a ∈ w.args, isNewB f a = true → E a) → (∀ a ∈ w.args, Reg T a) → (∀ a ∈ u.args, Reg frS a) →
    (∀ a ∈ ecFront f g x, ∀ y, frS.regs[a]? = some (some y) →
      ∃ y', T.regs[a]? = some (some y') ∧ Sem.Refines (ecCv tabs f g a y) y') →
    (∀ a ∈ u.args, EcImkFacts env tabs f g frS T a) → (∀ a, H a → EcTgtHolds env tabs g T a) →
    ResCv (ecCv tabs f g x) (evalValue env (Ctx.make tabs f) frS u)
      (evalValue env (Ctx.make tabs g) T w)

/-- An interface shape is a two-field aggregate with a pointer data word. -/
theorem eco_ifaceShape {t : Ty} (h : ifaceShape t = true) :
    ∃ f0 o e n, t = .agg [f0, (o, .ptr e)] n := by
  unfold ifaceShape at h
  split at h
  · exact ⟨_, _, _, _, rfl⟩
  · cases h

/-- What `obl_of_imk` needs of an argument `a` whose node in `g` is an `IMake`, in terms of the
values whose source (`HS`) or target (`HT`) registers hold their evaluations: target mode
(`a` and its data operand in `HT`, `a` interface-shaped in `g`) or source mode (`a` in `HS`, the
same `IMake` in `f`, interface-shaped in `f`, its data operand unconverted and a pointer in
both or an aggregate in both). -/
def EcoImkHeld (tabs : Tables) (f g : Func) (HS HT : ID → Prop) (a : ID) : Prop :=
  ∀ aw, g.value? a = some aw → aw.op = .IMake →
    (HT a ∧ HT aw.args[1]! ∧ ifaceShape (shapeOf (typeShapes tabs) g a) = true) ∨
    (HS a ∧
      (∃ au, f.value? a = some au ∧ au.op = .IMake ∧ au.args.size = 2 ∧ au.args[1]! = aw.args[1]!) ∧
      ifaceShape (shapeOf (typeShapes tabs) f a) = true ∧ special f g aw.args[1]! = false ∧
      ((∃ e e', shapeOf (typeShapes tabs) f aw.args[1]! = .ptr e ∧
          shapeOf (typeShapes tabs) g aw.args[1]! = .ptr e') ∨
        (∃ fs n fs' n', shapeOf (typeShapes tabs) f aw.args[1]! = .agg fs n ∧
          shapeOf (typeShapes tabs) g aw.args[1]! = .agg fs' n')))

/-- `EcOblImk` is `Obl` when each `IMake` argument is held in source or target mode and the
values `H` are among the target's held values. -/
theorem obl_of_imk {tabs : Tables} {f g : Func} {x : ID} {u : Value} {HS HT H : ID → Prop}
    (h : EcOblImk tabs f g H x) (hu : f.value? x = some u)
    (hH : ∀ a ∈ u.args, EcoImkHeld tabs f g HS HT a) (hHT : ∀ a, H a → HT a) :
    Obl tabs f g (ecCv tabs f g) (isNewB f) (ecFront f g x) HS HT x := by
  intro u' w hu' hw env hE frS T hT hRS E hNC hEw hRw hRu hfront hheldS hheldT
  rw [hu] at hu'
  cases hu'
  refine h u w hu hw env hE frS T hT hRS E hNC hEw hRw hRu hfront (fun a ha aw haw hop => ?_)
    fun a ha => hheldT a (hHT a ha)
  rcases hH a ha aw haw hop with ⟨h1, h2, h3⟩ | ⟨h1, hau, h3, hsp, hsh⟩
  · exact .inl ⟨hheldT a h1, hheldT _ h2, eco_ifaceShape h3⟩
  · exact .inr ⟨hheldS a h1, hau, eco_ifaceShape h3, hsp, hsh⟩

/-- A target argument of `x` that the source defines is in `ecFront`. -/
theorem eco_mem_front_tgt {f g : Func} {x q : ID} {w : Value} (hw : g.value? x = some w)
    (hq : q ∈ w.args) (hn : isNewB f q = false) : q ∈ ecFront f g x := by
  unfold ecFront
  rw [hw]
  exact List.mem_append_right _ (List.mem_filter.2 ⟨Array.mem_toList_iff.2 hq, by rw [hn]; rfl⟩)

/-- `EcArgRel` of the source arguments of `x` in an obligation's frames. -/
theorem ecc_argRel {tabs : Tables} {f g : Func} {x : ID} {u : Value} {frS T : Frame}
    (hu : f.value? x = some u) (hRS : RegsOK (Ctx.make tabs f) frS) (hRu : ∀ a ∈ u.args, Reg frS a)
    (hfront : ∀ a ∈ ecFront f g x, ∀ y, frS.regs[a]? = some (some y) →
      ∃ y', T.regs[a]? = some (some y') ∧ Sem.Refines (ecCv tabs f g a y) y')
    {a : ID} (ha : a ∈ u.args) : EcArgRel tabs f g frS T a := by
  have hr := reg_rv (hRu a ha)
  exact ⟨_, hr, hRS a _ hr, hfront a (ecc_mem_front hu ha) _ hr⟩

/-- The Go-typed arguments have their parameters' shapes. -/
theorem ecc_pieces_hasTy {tabs : Tables} {f g : Func} {frS T : Frame} :
    ∀ (ps : List ABIParam) (as pcs : List ID), piecesOK tabs (typeShapes tabs) f g ps as pcs = true →
      (∀ a ∈ as, EcArgRel tabs f g frS T a) →
      List.Forall₂ (fun (p : ABIParam) (r : Val) => r.hasTy (tabs.ty p.type) = true) ps
        (as.map (rv frS))
  | [], [], _, _, _ => .nil
  | [], _ :: _, _, h, _ | _ :: _, [], _, h, _ => by simp [piecesOK] at h
  | p :: ps, a :: as, pcs, h, hrel => by
    unfold piecesOK at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨y, hyS, hry, -⟩ := hrel a List.mem_cons_self
    refine .cons ?_ (ecc_pieces_hasTy ps as _ h.2 fun b hb => hrel b (List.mem_cons_of_mem _ hb))
    rw [rv_of hyS]
    have := hry.1
    rw [← shapeOf_eq, eqE_hasTy h.1.1.1.1] at this
    exact this

/-- A memory refined after retyping at `mem`. -/
theorem ecc_retype_mem {a b : Val} (h : Sem.Refines a b) : Sem.Refines (a.retype .mem) b := by
  cases h with
  | mem h => exact .mem h
  | _ => exact .poison _

/-- The source's tuple of results and memory keeps its shape. -/
theorem ecc_retypePre {tabs : Tables} {mv : Val} :
    {ps : List ABIParam} → {G : List Val} →
      List.Forall₂ (fun (p : ABIParam) (r : Val) => r.hasTy (tabs.ty p.type) = true) ps G →
      {us : List Ty} → ((ps.map (tabs.ty ·.type)).zip us).all (fun (a, b) => eqE b a) = true →
      us.length = ps.length + 1 → us.getLast? = some .mem →
      Val.retypePre us (G ++ [mv]) = some (G ++ [mv.retype .mem])
  | _, _, .nil, [u], _, _, hl => by
    simp only [List.getLast?_singleton, Option.some.injEq] at hl
    subst hl; rfl
  | _, _, .nil, [], _, hu, _ | _, _, .nil, _ :: _ :: _, _, hu, _ => by simp at hu
  | _, _, .cons _ _, [], _, hu, _ => by simp at hu
  | p :: ps, g :: G, .cons hg hf, u :: us, he, hu, hl => by
    simp only [List.map_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at he
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hu
    have hne : us ≠ [] := by intro h0; subst h0; simp at hu
    rw [List.getLast?_cons_of_ne_nil hne] at hl
    simp only [List.cons_append, Val.retypePre, ecc_retypePre hf he.2 hu hl, Option.map_some]
    rw [eqE_retype he.1, Val.retype_of_hasTy hg]

theorem ecc_evalPure_result (ty : Ty) (ai : Int64) (ax : Option AuxRef) (args : List Val) :
    evalPure .MakeResult ty ai ax args = .tuple args := rfl

/-! ## `MakeResult` -/

theorem obl_result_imk {tabs : Tables} {f g : Func} {x : ID} {u w : Value}
    (hu : f.value? x = some u) (hw : g.value? x = some w) (hop : u.op = .MakeResult)
    (hok : resultOK tabs (typeShapes tabs) f g u w = true)
    (hreg : regParamsOK tabs (ownOuts tabs f) = true) (huid : u.id = x)
    (L : ID → Prop) (hLx : L x)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true → L a) :
    EcOblImk tabs f g (fun _ => False) x := by
  intro u' w' hu' hw' env _ frS T _ hRS E hNC hEw hRw hRu hfront himk _
  rw [hu] at hu'; cases hu'
  rw [hw] at hw'; cases hw'
  unfold resultOK at hok
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hwop, hn⟩, hws⟩, hlast⟩, hmsp⟩, hpc⟩, htup⟩, hrt⟩ := hok
  obtain ⟨hwid, hLw⟩ := hL x hLx w hw
  have hreg' := ecf_reg_of hreg
  have hsu := ecc_args_split1 u.args (by omega)
  have hsw := ecc_args_split1 w.args hws
  rw [hlast] at hsw
  have hrel : ∀ a ∈ (u.args.extract 0 (u.args.size - 1)).toList, EcArgRel tabs f g frS T a :=
    fun a ha => ecc_argRel hu hRS hRu hfront (Array.mem_toList_iff.1 (ecc_mem_of_split hsu ha))
  have hG := ecc_pieces_hasTy _ _ _ hpc hrel
  have hP := ec_pieces hNC hL hRS _ _ _ hpc (fun p hp => (hreg' p hp).2.1)
    (fun q hq => hRw q (Array.mem_toList_iff.1 (ecc_mem_of_split hsw hq)))
    (fun q hq hn' => have hq' := Array.mem_toList_iff.1 (ecc_mem_of_split hsw hq)
      ⟨hEw q hq' hn', hLw q hq' hn'⟩) hrel
    (fun a ha => himk a (Array.mem_toList_iff.1 (ecc_mem_of_split hsu ha)))
    (fun q hq yq hyq hn' => hfront q (eco_mem_front_tgt hw
      (Array.mem_toList_iff.1 (ecc_mem_of_split hsw hq)) hn') yq hyq)
  -- the memory argument
  have hm : u.args[u.args.size - 1]! ∈ u.args := by
    rw [← Array.mem_toList_iff, hsu]; simp
  obtain ⟨ym, hym, hymm⟩ := hfront _ (ecc_mem_front hu hm) _ (reg_rv (hRu _ hm))
  rw [ecCv_of_not_special hmsp] at hymm
  -- the evaluations
  have hRw' : ∀ a ∈ w.args, Reg T a := hRw
  rw [evalValue_of_regs hRu, evalValue_of_regs hRw', evalOp_term (by rw [hop]; decide),
    evalOp_term (by rw [hwop]; decide), hop, hwop, GoFV.Proof.Rules.opVal_pure (by decide),
    GoFV.Proof.Rules.opVal_pure (by decide), ecc_evalPure_result, ecc_evalPure_result,
    huid, hwid, tys_of_value hu, tys_of_value hw, Option.getD_some, Option.getD_some, hsu, hsw,
    List.map_append, List.map_append, List.map_cons, List.map_cons, List.map_nil, List.map_nil,
    rv_of hym]
  refine .ok ?_
  obtain ⟨us, hus, husl, hue, hul⟩ := ecf_tupleOf htup
  rw [ecf_valueTy] at hus
  rw [hus]
  show Sem.Refines (ecCv tabs f g x (match Val.retypePre us _ with
    | some vs' => Val.tuple vs'
    | none => Val.poison)) _
  rw [ecc_retypePre hG hue (by rw [husl, List.length_map]) hul]
  dsimp only
  rw [ecc_cv_result hu hop (ecf_not_invalidated hw (by rw [hwop]; decide)),
    ecf_convTuple (by rw [ecf_forall₂_length hG]), shapeOf, hw, ecf_valueTy]
  exact retype_mono _ (.tuple (RefinesList.append hP (.cons (ecc_retype_mem hymm) .nil)))

/-- **The `MakeResult` obligation.** -/
theorem obl_result {tabs : Tables} {f g : Func} {x : ID} {u w : Value} {HS HT : ID → Prop}
    (hu : f.value? x = some u) (hw : g.value? x = some w) (hop : u.op = .MakeResult)
    (hok : resultOK tabs (typeShapes tabs) f g u w = true)
    (hreg : regParamsOK tabs (ownOuts tabs f) = true) (huid : u.id = x)
    (L : ID → Prop) (hLx : L x)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true → L a)
    (hH : ∀ a ∈ u.args, EcoImkHeld tabs f g HS HT a) :
    Obl tabs f g (ecCv tabs f g) (isNewB f) (ecFront f g x) HS HT x :=
  obl_of_imk (obl_result_imk hu hw hop hok hreg huid L hLx hL) hu hH fun _ h => h.elim

/-! ## Calls: the semantic pieces -/

theorem ecc_evalOp_call {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val} {ty : Ty}
    (h : v.op = .StaticLECall ∨ v.op = .ClosureLECall ∨ v.op = .InterLECall ∨
      v.op = .StaticCall ∨ v.op = .ClosureCall ∨ v.op = .InterCall) :
    evalOp env ctx fr v argv ty = callOp env ctx v argv := by
  rcases h with h | h | h | h | h | h <;> (unfold evalOp; rw [h])

/-- The callee, closure context and rest of the source and target calls. -/
theorem ecc_callTarget {ctx ctx' : Ctx} (htabs : ctx'.tabs = ctx.tabs) {u w : Value} {op : Op}
    {k : Nat} (hmap : callOpMap u.op = some (op, k)) (hwop : w.op = op) (haux : w.aux = u.aux)
    {lead lead' rest rest' : List Val} (hl : lead.length = k) (hlr : Sem.RefinesList lead lead') :
    (callTarget ctx u (lead ++ rest)).2.2 = rest ∧ (callTarget ctx' w (lead' ++ rest')).2.2 = rest' ∧
      ((callTarget ctx u (lead ++ rest)).1 = none ∨
        (callTarget ctx' w (lead' ++ rest')).1 = (callTarget ctx u (lead ++ rest)).1) ∧
      OptRefines (callTarget ctx u (lead ++ rest)).2.1 (callTarget ctx' w (lead' ++ rest')).2.1 := by
  unfold callOpMap at hmap
  split at hmap
  · next hop =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hmap
    obtain ⟨rfl, rfl⟩ := hmap
    match lead, lead', hlr, hl with
    | [], [], .nil, _ =>
      have e1 : callTarget ctx u rest = (u.aux.bind ctx.tabs.callee?, none, rest) := by
        unfold callTarget; rw [hop]
      have e2 : callTarget ctx' w rest' = (w.aux.bind ctx'.tabs.callee?, none, rest') := by
        unfold callTarget; rw [hwop]
      rw [List.nil_append, List.nil_append, e1, e2]
      exact ⟨rfl, rfl, .inr (by dsimp only; rw [haux, htabs]), .none⟩
  · next hop =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hmap
    obtain ⟨rfl, rfl⟩ := hmap
    match lead, lead', hlr, hl with
    | [code, c], [code', c'], .cons h1 (.cons h2 .nil), _ =>
      have e1 : callTarget ctx u (code :: c :: rest) = (codeTarget? code, some c, rest) := by
        unfold callTarget; rw [hop]
      have e2 : callTarget ctx' w (code' :: c' :: rest') = (codeTarget? code', some c', rest') := by
        unfold callTarget; rw [hwop]
      rw [List.cons_append, List.cons_append, List.nil_append, List.cons_append, List.cons_append,
        List.nil_append, e1, e2]
      refine ⟨rfl, rfl, ?_, .some h2⟩
      cases hc : codeTarget? code with
      | none => exact .inl rfl
      | some s => exact .inr (codeTarget?_mono h1 hc)
  · next hop =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hmap
    obtain ⟨rfl, rfl⟩ := hmap
    match lead, lead', hlr, hl with
    | [code], [code'], .cons h1 .nil, _ =>
      have e1 : callTarget ctx u (code :: rest) = (codeTarget? code, none, rest) := by
        unfold callTarget; rw [hop]
      have e2 : callTarget ctx' w (code' :: rest') = (codeTarget? code', none, rest') := by
        unfold callTarget; rw [hwop]
      rw [List.cons_append, List.nil_append, List.cons_append, List.nil_append, e1, e2]
      refine ⟨rfl, rfl, ?_, .none⟩
      cases hc : codeTarget? code with
      | none => exact .inl rfl
      | some s => exact .inr (codeTarget?_mono h1 hc)
  · cases hmap

/-- `decodeArgs` of the pieces rebuilds refinements of the Go-typed arguments. -/
theorem ecc_decodeArgs {tabs : Tables} (act : Nat) (m : Mem) :
    {ps : List ABIParam} → {G : List Val} →
      List.Forall₂ (fun (p : ABIParam) (r : Val) => r.hasTy (tabs.ty p.type) = true) ps G →
      (∀ p ∈ ps, ecfReg tabs p) →
      ∃ D, decodeArgs tabs act m ps (ecfPieces tabs ps G) = some D ∧ Sem.RefinesList G D
  | _, _, .nil, _ => ⟨[], rfl, .nil⟩
  | p :: ps, g :: G, .cons hg hf, hreg => by
    obtain ⟨hne, hw, hlen⟩ := hreg p List.mem_cons_self
    obtain ⟨D, hD, hGD⟩ := ecc_decodeArgs act m hf fun q hq => hreg q (List.mem_cons_of_mem _ hq)
    have hlv : (leafVals (tabs.ty p.type) g).length = p.regs.size := by
      rw [leafVals_length hw, hlen]
    have hP : ecfPieces tabs (p :: ps) (g :: G) =
        leafVals (tabs.ty p.type) g ++ ecfPieces tabs ps G := by
      simp only [ecfPieces, List.zip_cons_cons, List.flatMap_cons]
    refine ⟨ofPieces (tabs.ty p.type) (leafVals (tabs.ty p.type) g) :: D, ?_,
      .cons (ofPieces_leafVals hw hg) hGD⟩
    rw [hP]
    unfold decodeArgs
    have hnl : ¬ (leafVals (tabs.ty p.type) g ++ ecfPieces tabs ps G).length < p.regs.size := by
      rw [List.length_append]; omega
    simp only [hne, Bool.false_eq_true, ↓reduceIte, hnl, List.take_left' hlv, List.drop_left' hlv,
      hD]
    rfl

theorem ecc_encodeResults_length {tabs : Tables} {act : Nat} :
    {ps : List ABIParam} → {rs : List Val} → {m : Mem} → {r : List Val × Mem} →
      encodeResults tabs act ps rs m = some r → rs.length = ps.length
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h | _ :: _, [], _, _, h => by simp [encodeResults] at h
  | p :: ps, r :: rs, m, res, h => by
    unfold encodeResults at h
    dsimp only at h
    split at h
    · cases hw : m.write ⟨.outargs act, BitVec.ofInt 64 p.offset⟩ (encode (tabs.ty p.type) r) with
      | none => rw [hw] at h; cases h
      | some m' =>
        rw [hw] at h
        simp only [List.length_cons, ecc_encodeResults_length h]
    · cases he : encodeResults tabs act ps rs m with
      | none => rw [he] at h; cases h
      | some r' => simp only [List.length_cons, ecc_encodeResults_length he]

/-- `encodeResults` of register-assigned results of their shapes: their pieces. -/
theorem ecc_encodeResults {tabs : Tables} {act : Nat} (m : Mem) :
    {ps : List ABIParam} → {rs : List Val} →
      List.Forall₂ (fun (p : ABIParam) (r : Val) => r.hasTy (tabs.ty p.type) = true) ps rs →
      (∀ p ∈ ps, ecfReg tabs p) →
      encodeResults tabs act ps rs m = some (ecfPieces tabs ps rs, m)
  | _, _, .nil, _ => rfl
  | p :: ps, r :: rs, .cons hr hf, hreg => by
    obtain ⟨hne, hw, -⟩ := hreg p List.mem_cons_self
    unfold encodeResults
    simp only [hne, Bool.false_eq_true, ↓reduceIte,
      ecc_encodeResults m hf fun q hq => hreg q (List.mem_cons_of_mem _ hq)]
    simp only [ecfPieces, List.zip_cons_cons, List.flatMap_cons, toPieces_eq_leafVals hw hr]
    rfl

theorem ecc_retypeResults {tabs : Tables} :
    {ps : List ABIParam} → {rs : List Val} → rs.length = ps.length →
      List.Forall₂ (fun (p : ABIParam) (r : Val) => r.hasTy (tabs.ty p.type) = true) ps
        (retypeResults tabs ps rs)
  | [], [], _ => .nil
  | [], _ :: _, h | _ :: _, [], h => by simp at h
  | p :: ps, r :: rs, h => .cons (Val.retype_hasTy _ r) (ecc_retypeResults (by simpa using h))

theorem ecc_retypeResults_length (tabs : Tables) :
    (ps : List ABIParam) → (rs : List Val) → (retypeResults tabs ps rs).length = rs.length
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: ps, _ :: rs => by simp [retypeResults, ecc_retypeResults_length tabs ps rs]

/-- A call's tuple of Go-typed results, memory and result addresses has its type's shape. -/
theorem ecc_hasTyPre_call {tabs : Tables} {tl : List Val} :
    {ps : List ABIParam} → {rs : List Val} →
      List.Forall₂ (fun (p : ABIParam) (r : Val) => r.hasTy (tabs.ty p.type) = true) ps rs →
      {us : List Ty} → ((ps.map (tabs.ty ·.type)).zip us).all (fun (a, b) => eqE b a) = true →
      us.length = ps.length + 1 → us.getLast? = some .mem → (m : Mem) →
      Val.hasTyPre (rs ++ .mem m :: tl) us = true
  | _, _, .nil, [u], _, _, hl, m => by
    simp only [List.getLast?_singleton, Option.some.injEq] at hl
    subst hl; simp [Val.hasTyPre, Val.hasTy]
  | _, _, .nil, [], _, hu, _, _ | _, _, .nil, _ :: _ :: _, _, hu, _, _ => by simp at hu
  | _, _, .cons _ _, [], _, hu, _, _ => by simp at hu
  | p :: ps, r :: rs, .cons hr hf, u :: us, he, hu, hl, m => by
    simp only [List.map_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at he
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hu
    have hne : us ≠ [] := by intro h0; subst h0; simp at hu
    rw [List.getLast?_cons_of_ne_nil hne] at hl
    simp only [List.cons_append, Val.hasTyPre, Bool.and_eq_true]
    exact ⟨by rw [eqE_hasTy he.1]; exact hr, ecc_hasTyPre_call hf he.2 hu hl m⟩

theorem ecc_convTuple {tabs : Tables} {ps : List ABIParam} {rs : List Val} (hl : rs.length = ps.length)
    (tl : List Val) : convTuple tabs ps (.tuple (rs ++ tl)) = .tuple (ecfPieces tabs ps rs ++ tl) := by
  unfold convTuple
  dsimp only
  have hz : ps.zip (rs ++ tl) = ps.zip rs := by
    conv => lhs; rw [← List.append_nil ps]
    rw [List.zip_append hl.symm, List.zip_nil_left, List.append_nil]
  rw [hz, List.drop_left' hl]

theorem ecc_cv_call {tabs : Tables} {f g : Func} {c : ID} {u : Value} (hu : f.value? c = some u)
    (hcall : (callOpMap u.op).isSome = true) (hinv : invalidated g c = false) (y : Val) :
    ecCv tabs f g c y =
      (convTuple tabs (callOuts tabs u.aux) y).retype (shapeOf (typeShapes tabs) g c) := by
  unfold ecCv
  simp only [hinv, hu, hcall, Bool.false_eq_true, ↓reduceIte]

/-- What the source's and the target's call results are: the source's Go-typed results (of their
shapes), memory and result addresses; the target's the pieces of the results. -/
def EcCallRes (tabs : Tables) (outs : List ABIParam) (y y' : Val) : Prop :=
  ∃ rs m a, y = .tuple (rs ++ [.mem m, a]) ∧
    List.Forall₂ (fun (p : ABIParam) (r : Val) => r.hasTy (tabs.ty p.type) = true) outs rs ∧
    Sem.Refines (.tuple (ecfPieces tabs outs rs ++ [.mem m, a])) y'

/-- **The call**: the source's call on the Go-typed arguments and the target's on their pieces
and its memory, which hold the Go-typed arguments (`decodeArgs`) and agree with the source's
outside the outgoing-arguments area. -/
theorem ecc_callOp {env : Env} (hE : env.Mono) {ctx ctx' : Ctx} (htabs : ctx'.tabs = ctx.tabs)
    (hact : ctx'.act = ctx.act) {u w : Value}
    (hpre : (u.op == .StaticCall || u.op == .ClosureCall || u.op == .InterCall) = false)
    (hpost : (w.op == .StaticCall || w.op == .ClosureCall || w.op == .InterCall) = true)
    (haux : w.aux = u.aux) {abi : CallABI} (habi : callABI? ctx.tabs u.aux = some abi)
    (houts : ∀ p ∈ outsOf abi, ecfReg ctx.tabs p) {argv argv' G P' : List Val} {mv mv' : Val}
    (hct : (callTarget ctx u argv).2.2 = G ++ [mv]) (hct' : (callTarget ctx' w argv').2.2 = P' ++ [mv'])
    (hcallee : (callTarget ctx u argv).1 = none ∨ (callTarget ctx' w argv').1 = (callTarget ctx u argv).1)
    (hclo : OptRefines (callTarget ctx u argv).2.1 (callTarget ctx' w argv').2.1)
    (hmem : ∀ m, mv = .mem m → G.any Val.hasPoison = false →
      outargsOK ctx.tabs ctx.act m (insOf abi) = true →
      ∃ mN D, mv' = .mem mN ∧
        Mem.Refines (m.poisonBlock (.outargs ctx.act)) (mN.poisonBlock (.outargs ctx.act)) ∧
        outargsOK ctx.tabs ctx.act mN (insOf abi) = true ∧
        decodeArgs ctx.tabs ctx.act mN (insOf abi) P' = some D ∧ Sem.RefinesList G D) :
    Res.Rel (EcCallRes ctx.tabs (outsOf abi)) (callOp env ctx u argv) (callOp env ctx' w argv') := by
  have habi' : callABI? ctx'.tabs w.aux = some abi := by rw [htabs, haux]; exact habi
  unfold callOp
  rw [habi, habi', htabs, hact]
  revert hct hct' hcallee hclo
  generalize callTarget ctx u argv = T1
  generalize callTarget ctx' w argv' = T2
  rcases T1 with ⟨callee?, clo, rest⟩
  rcases T2 with ⟨callee?', clo', rest'⟩
  intro hct hct' hcallee hclo
  dsimp only at hct hct' hcallee hclo ⊢
  subst hct hct'
  cases callee? with
  | none => exact .stuck _ _
  | some callee =>
    rcases hcallee with hc | hc
    · cases hc
    · subst hc
      dsimp only [bind, Res.bind, Res.ofOption]
      rw [List.getLast?_concat, List.getLast?_concat, List.dropLast_concat, List.dropLast_concat]
      cases mv with
      | mem m =>
        dsimp only
        simp only [hpre, hpost, Bool.false_eq_true, ↓reduceIte, Option.map_some, Option.getD_some]
        simp only [insOf, outsOf] at hmem houts ⊢
        dsimp only [pure, Res.bind]
        by_cases hp : (G.any Val.hasPoison || (clo.map Val.hasPoison).getD false) = true
        · rw [if_pos hp]; exact .stuck _ _
        rw [if_neg hp]
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hp
        by_cases hok : outargsOK ctx.tabs ctx.act m (abi.params.toList.filter (!·.out)) = true
        · rw [if_neg (by simp [hok])]
          obtain ⟨mN, D, rfl, hpm, hokN, hD, hargs⟩ := hmem m rfl hp.1 hok
          dsimp only
          rw [hD]
          dsimp only [pure, Res.bind]
          have hp1 := hargs.any_hasPoison hp.1
          have hp2 : (clo'.map Val.hasPoison).getD false = false := by
            cases hclo with
            | none => rfl
            | some hcc => exact (hcc.noPoison (by simpa using hp.2)).1
          simp only [hp1, hp2, hokN, Bool.or_false, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
          cases hx : env.extern callee with
          | none => exact .stuck _ _
          | some c =>
            dsimp only
            have := hE _ _ hx hp.1 hp.2 hargs hclo hpm
            revert this
            generalize c G clo (m.poisonBlock (.outargs ctx.act)) = o
            generalize c D clo' (mN.poisonBlock (.outargs ctx.act)) = o'
            intro ho
            cases ho with
            | returned hr0 hm' =>
              dsimp only
              cases he : encodeResults ctx.tabs ctx.act _ _ _ with
              | none => exact .stuck _ _
              | some r =>
                obtain ⟨r', he', hr1, hr2⟩ := encodeResults_mono ctx.tabs ctx.act _
                  (retypeResults_mono ctx.tabs _ hr0) hm' he
                rw [he']
                dsimp only
                have hlen := ecc_encodeResults_length he
                rw [ecc_retypeResults_length] at hlen
                have hF := ecc_retypeResults (tabs := ctx.tabs) hlen
                rw [ecc_encodeResults _ hF houts] at he
                cases he
                exact .ok ⟨_, _, _, rfl, hF,
                  .tuple (hr1.append (.cons (.mem hr2) (.cons (Sem.Refines.refl _) .nil)))⟩
            | panicked e hm' => exact .panic e hm'
            | stuck msg o => exact .stuck _ _
        · rw [if_pos (by simp [hok])]; exact .stuck _ _
      | _ => exact .stuck _ _

theorem ecc_callOpMap {o op : Op} {k : Nat} (h : callOpMap o = some (op, k)) :
    (o = .StaticLECall ∨ o = .ClosureLECall ∨ o = .InterLECall) ∧
      (o == .StaticCall || o == .ClosureCall || o == .InterCall) = false ∧
      (op == .StaticCall || op == .ClosureCall || op == .InterCall) = true ∧ op ≠ .Invalid := by
  unfold callOpMap at h
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;> simp_all <;> decide

theorem ecc_map_refines {F G : ID → Val} :
    {l : List ID} → (∀ a ∈ l, Sem.Refines (F a) (G a)) → Sem.RefinesList (l.map F) (l.map G)
  | [], _ => .nil
  | a :: _, h => .cons (h a List.mem_cons_self) (ecc_map_refines fun b hb => h b (List.mem_cons_of_mem _ hb))

/-! ## Calls: register and stack arguments -/

/-- The pairs of the parameters and arguments `piecesOK` accepts have the parameters' shapes. -/
theorem ecc_piecesOK_eqE {tabs : Tables} {sh : Array Ty} {f g : Func} :
    ∀ {ps : List ABIParam} {as pcs : List ID}, piecesOK tabs sh f g ps as pcs = true →
      ∀ x ∈ ps.zip as, eqE (shapeOf sh f x.2) (tabs.ty x.1.type) = true
  | [], _, _, _, x, hx => by simp at hx
  | _ :: _, [], _, h, _, _ => by simp [piecesOK] at h
  | p :: ps, a :: as, pcs, h, x, hx => by
    unfold piecesOK at h
    simp only [Bool.and_eq_true] at h
    rw [List.zip_cons_cons] at hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1.1.1.1
    · exact ecc_piecesOK_eqE h.2 x hx

theorem ecc_zip_map {α β γ : Type} (F : β → γ) : ∀ (l : List (α × β)),
    (l.map Prod.fst).zip ((l.map Prod.snd).map F) = l.map fun e => (e.1, F e.2)
  | [] => rfl
  | e :: l => by
    rw [List.map_cons, List.map_cons, List.map_cons, List.zip_cons_cons, ecc_zip_map F l, List.map_cons]

theorem ecc_zip_fst_snd {α β : Type} : ∀ (l : List (α × β)), (l.map Prod.fst).zip (l.map Prod.snd) = l
  | [] => rfl
  | e :: l => by simp [ecc_zip_fst_snd l]

theorem ecc_flatMap_pat (h : ABIParam → Val → List Val) (l : List (ABIParam × Val)) :
    (l.flatMap fun (p, r) => h p r) = l.flatMap fun x => h x.1 x.2 := by
  congr 1

theorem ecc_argPairs_map (reg : Bool) (F : ID → Val) (ps : List ABIParam) (as : List ID) :
    ((ps.zip as).map fun e => (e.1, F e.2)).filter (fun x => !x.1.regs.isEmpty == reg) =
      (argPairs reg ps as).map fun e => (e.1, F e.2) := by
  unfold argPairs; rw [List.filter_map]; rfl

/-- **`decodeArgs` of register and stack arguments**: the register pieces refine the leaf values
of the register-assigned arguments, and each stack slot decodes to a refinement of its argument. -/
theorem ecc_decodeArgs_mixed {tabs : Tables} {act : Nat} {M : Mem} :
    ∀ (L : List (ABIParam × Val)) (P' : List Val),
      (∀ x ∈ L, wf (tabs.ty x.1.type) = true ∧ x.2.hasTy (tabs.ty x.1.type) = true) →
      (∀ x ∈ L, x.1.regs.isEmpty = false → (leaves (tabs.ty x.1.type)).length = x.1.regs.size) →
      (∀ x ∈ L, x.1.regs.isEmpty = true → ∃ bs,
        M.read ⟨.outargs act, BitVec.ofInt 64 x.1.offset⟩ (tabs.ty x.1.type).size = some bs ∧
        Sem.Refines x.2 (decode bs 0 (tabs.ty x.1.type))) →
      Sem.RefinesList ((L.filter fun x => !x.1.regs.isEmpty == true).flatMap
        fun x => leafVals (tabs.ty x.1.type) x.2) P' →
      ∃ D, decodeArgs tabs act M (L.map Prod.fst) P' = some D ∧ Sem.RefinesList (L.map Prod.snd) D
  | [], P', _, _, _, h => by
    rw [RefinesList.nil_inv h]
    exact ⟨[], rfl, .nil⟩
  | (p, v) :: L, P', hw, hr, hs, hP => by
    obtain ⟨hwp, hvp⟩ := hw (p, v) List.mem_cons_self
    dsimp only at hwp hvp
    cases he : p.regs.isEmpty with
    | false =>
      rw [List.filter_cons, if_pos (by simp [he]), List.flatMap_cons] at hP
      obtain ⟨y1, y2, rfl, h1, h2⟩ := ecs_rl_split hP
      obtain ⟨D, hD, hGD⟩ := ecc_decodeArgs_mixed L y2 (fun x hx => hw x (List.mem_cons_of_mem _ hx))
        (fun x hx => hr x (List.mem_cons_of_mem _ hx)) (fun x hx => hs x (List.mem_cons_of_mem _ hx)) h2
      have hlv : y1.length = p.regs.size := by
        rw [← ecs_rl_length h1, leafVals_length hwp]; exact hr (p, v) List.mem_cons_self he
      refine ⟨ofPieces (tabs.ty p.type) y1 :: D, ?_,
        .cons ((ofPieces_leafVals hwp hvp).trans (ofPieces_mono _ h1)) hGD⟩
      rw [List.map_cons]
      unfold decodeArgs
      have hnl : ¬ (y1 ++ y2).length < p.regs.size := by rw [List.length_append]; omega
      simp only [he, Bool.false_eq_true, ↓reduceIte, hnl, List.take_left' hlv, List.drop_left' hlv,
        hD]
      rfl
    | true =>
      rw [List.filter_cons, if_neg (by simp [he])] at hP
      obtain ⟨D, hD, hGD⟩ := ecc_decodeArgs_mixed L P' (fun x hx => hw x (List.mem_cons_of_mem _ hx))
        (fun x hx => hr x (List.mem_cons_of_mem _ hx)) (fun x hx => hs x (List.mem_cons_of_mem _ hx)) hP
      obtain ⟨bs, hbs, hv⟩ := hs (p, v) List.mem_cons_self he
      refine ⟨decode bs 0 (tabs.ty p.type) :: D, ?_, .cons hv hGD⟩
      rw [List.map_cons]
      unfold decodeArgs
      simp only [he, ↓reduceIte]
      rw [hbs]
      simp only [hD]
      rfl

/-- The source call's target: its rest after the `k` leading arguments. -/
theorem ecc_callTarget_rest {ctx : Ctx} {u : Value} {op : Op} {k : Nat}
    (hmap : callOpMap u.op = some (op, k)) {lead rest : List Val} (hl : lead.length = k) :
    (callTarget ctx u (lead ++ rest)).2.2 = rest := by
  unfold callOpMap at hmap
  split at hmap
  · next hop =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hmap
    obtain ⟨rfl, rfl⟩ := hmap
    match lead, hl with
    | [], _ => rw [List.nil_append]; unfold callTarget; rw [hop]
  · next hop =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hmap
    obtain ⟨rfl, rfl⟩ := hmap
    match lead, hl with
    | [a, b], _ => rw [List.cons_append, List.cons_append, List.nil_append]; unfold callTarget; rw [hop]
  · next hop =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hmap
    obtain ⟨rfl, rfl⟩ := hmap
    match lead, hl with
    | [a], _ => rw [List.cons_append, List.nil_append]; unfold callTarget; rw [hop]
  · cases hmap

/-- A source call that completes or panics had a memory whose stack-argument slots are writable. -/
theorem ecc_callOp_outargs {env : Env} {ctx : Ctx} {u : Value} {abi : CallABI}
    (hpre : (u.op == .StaticCall || u.op == .ClosureCall || u.op == .InterCall) = false)
    (habi : callABI? ctx.tabs u.aux = some abi) {argv G : List Val} {mv : Val}
    (hct : (callTarget ctx u argv).2.2 = G ++ [mv])
    (h : (∃ y, callOp env ctx u argv = .ok y) ∨ ∃ e m, callOp env ctx u argv = .panic e m) :
    ∃ m, mv = .mem m ∧ outargsOK ctx.tabs ctx.act m (insOf abi) = true := by
  have hns : ∀ r : Res Val, (∃ msg, r = .stuck msg) → ¬ ((∃ y, r = .ok y) ∨ ∃ e m, r = .panic e m) :=
    fun r ⟨msg, hm⟩ hr => by subst hm; rcases hr with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h
  unfold callOp at h
  rw [habi] at h
  revert hct h
  generalize callTarget ctx u argv = T1
  rcases T1 with ⟨callee?, clo, rest⟩
  intro hct h
  dsimp only at hct h
  subst hct
  cases callee? with
  | none => exact absurd h (hns _ ⟨_, rfl⟩)
  | some callee =>
    dsimp only [bind, Res.bind, Res.ofOption] at h
    rw [List.getLast?_concat] at h
    cases mv with
    | mem m =>
      refine ⟨m, rfl, ?_⟩
      dsimp only at h
      simp only [hpre, Bool.false_eq_true, ↓reduceIte, Option.map_some, Option.getD_some] at h
      dsimp only [pure, Res.bind] at h
      cases hn : outargsOK ctx.tabs ctx.act m (insOf abi) with
      | true => rfl
      | false =>
        exfalso
        unfold insOf at hn
        split at h
        · exact hns _ ⟨_, rfl⟩ h
        · rw [if_pos (by simp [hn])] at h
          exact hns _ ⟨_, rfl⟩ h
    | _ => exact absurd h (hns _ ⟨_, rfl⟩)

/-- The `SP`s under the addresses of the stack-argument stores of call `u` (`w` in `g`) that the
source defines: what the call's obligation needs the target to hold. -/
def ecStackSP (f g : Func) (u w : Value) (a : ID) : Prop :=
  ∃ zs, callStores f g u w = some zs ∧ ∃ z ∈ zs, ∃ wz qw, g.value? z = some wz ∧
    g.value? wz.args[0]! = some qw ∧ isNewB f qw.args[0]! = false ∧ a = qw.args[0]!

theorem obl_call_imk {tabs : Tables} {f g : Func} {x : ID} {u w : Value}
    (hu : f.value? x = some u) (hw : g.value? x = some w) (hcall : (callOpMap u.op).isSome = true)
    (hok : callOK tabs (typeShapes tabs) f g u w = true) (huid : u.id = x)
    (L : ID → Prop) (hLx : L x)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true → L a) :
    EcOblImk tabs f g (ecStackSP f g u w) x := by
  intro u' w' hu' hw' env hE frS T _ hRS E hNC hEw hRw hRu hfront himk hHS
  rw [hu] at hu'; cases hu'
  rw [hw] at hw'; cases hw'
  unfold callOK at hok
  split at hok
  · next op k abi hmap habi =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true', ge_iff_le,
      List.all_eq_true] at hok
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hwop, hwaux⟩, -⟩, hkn⟩, houtsR⟩, hinsOK⟩, hlen⟩, hws⟩, hlead⟩, hstack⟩,
      hleadns⟩, hmns⟩, hpc⟩, htup⟩, -⟩ := hok
    obtain ⟨hopu, hpre, hpost, hinv⟩ := ecc_callOpMap hmap
    subst hwop
    obtain ⟨hwid, hLw⟩ := hL x hLx w hw
    have houts := ecf_reg_of houtsR
    have hsu := ecc_args_split u.args k hkn
    have hsw := ecc_args_split w.args k hws
    rw [hlead] at hsw
    have hmu : ∀ a, a ∈ (u.args.extract 0 k).toList ++ (u.args.extract k (u.args.size - 1)).toList ++
        [u.args[u.args.size - 1]!] → a ∈ u.args := fun a ha => by
      rw [← Array.mem_toList_iff, hsu]; exact ha
    have hmw : ∀ a, a ∈ (u.args.extract 0 k).toList ++ (w.args.extract k (w.args.size - 1)).toList ++
        [w.args[w.args.size - 1]!] → a ∈ w.args := fun a ha => by
      rw [← Array.mem_toList_iff, hsw]; exact ha
    have hmas : ∀ a ∈ (u.args.extract k (u.args.size - 1)).toList, a ∈ u.args := fun a ha =>
      hmu a (List.mem_append_left _ (List.mem_append_right _ ha))
    have hins : ∀ p ∈ insOf abi, wf (tabs.ty p.type) = true ∧
        (if p.regs.isEmpty then 0 ≤ p.offset else (leaves (tabs.ty p.type)).length = p.regs.size) := by
      intro p hp
      have := List.all_eq_true.1 hinsOK p hp
      rw [Bool.and_eq_true] at this
      refine ⟨this.1, ?_⟩
      have h2 := this.2
      split
      · next hr => rw [if_pos hr] at h2; exact of_decide_eq_true h2
      · next hr => rw [if_neg hr] at h2; exact beq_iff_eq.1 h2
    -- the Go-typed arguments
    have hrel : ∀ a ∈ (u.args.extract k (u.args.size - 1)).toList, EcArgRel tabs f g frS T a :=
      fun a ha => ecc_argRel hu hRS hRu hfront (hmas a ha)
    have hmemPair : ∀ {reg : Bool} {e : ABIParam × ID},
        e ∈ argPairs reg (insOf abi) (u.args.extract k (u.args.size - 1)).toList →
        e.1 ∈ insOf abi ∧ e.2 ∈ (u.args.extract k (u.args.size - 1)).toList := fun he =>
      List.of_mem_zip (List.mem_filter.1 he).1
    -- the register pieces
    have hP := ec_pieces hNC hL hRS _ _ _ hpc
      (fun p hp => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hp
        exact (hins _ (hmemPair he).1).1)
      (fun q hq => hRw q (hmw q (List.mem_append_left _ (List.mem_append_right _ hq))))
      (fun q hq hn' => have hq' := hmw q (List.mem_append_left _ (List.mem_append_right _ hq))
        ⟨hEw q hq' hn', hLw q hq' hn'⟩)
      (fun a ha => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
        exact hrel _ (hmemPair he).2)
      (fun a ha => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
        exact himk _ (hmas _ (hmemPair he).2))
      (fun q hq yq hyq hn' => hfront q (eco_mem_front_tgt hw
        (hmw q (List.mem_append_left _ (List.mem_append_right _ hq))) hn') yq hyq)
    rw [ecc_zip_map, ecc_flatMap_pat (fun p r => leafVals (tabs.ty p.type) r)] at hP
    -- the stack arguments
    unfold stackOK at hstack
    simp only [Bool.and_eq_true] at hstack
    obtain ⟨hsorted, hst⟩ := hstack
    cases hcs : callStores f g u w with
    | none => rw [hcs] at hst; cases hst
    | some zs =>
    rw [hcs] at hst
    simp only [Bool.and_eq_true, List.all_eq_true] at hst
    obtain ⟨⟨hsOK, hpcS⟩, hsrc⟩ := hst
    have hcs' := hcs
    unfold callStores at hcs'
    have htopEL : zs ≠ [] → E w.args[w.args.size - 1]! ∧ L w.args[w.args.size - 1]! := fun hne => by
      have hn := ecs_storeChain_new hcs' hne
      have hm : w.args[w.args.size - 1]! ∈ w.args := hmw _ (List.mem_append_right _ (by simp))
      exact ⟨hEw _ hm hn, hLw _ hm hn⟩
    have hzE := ecs_chain_E hNC hL _ hcs' htopEL
    have hzval : ∀ z ∈ zs, ∃ wz, g.value? z = some wz ∧ wz.args.size = 3 ∧ storeVal g z = wz.args[1]! ∧
        (∀ a ∈ wz.args, isNewB f a = true → E a ∧ L a) ∧ ∀ a ∈ wz.args, Reg T a := fun z hz => by
      obtain ⟨wz, -, -, hwz, -, -, hsz, -, -⟩ := ecs_chain_mem hcs' hz
      obtain ⟨-, wz', y, hwz', hcl, -, hev⟩ := hNC z (hzE z hz).1
      change g.value? z = some wz' at hwz'
      rw [hwz] at hwz'; cases hwz'
      refine ⟨wz, hwz, hsz, by unfold storeVal; rw [hwz]; rfl,
        fun a ha hn => ⟨hcl a ha hn, (hL z (hzE z hz).2 wz hwz).2 a ha hn⟩, regs_of_ok hev⟩
    have hpcv : ∀ q ∈ zs.map (storeVal g), ∃ z ∈ zs, ∃ wz, g.value? z = some wz ∧ q ∈ wz.args ∧
        (∀ a ∈ wz.args, isNewB f a = true → E a ∧ L a) ∧ ∀ a ∈ wz.args, Reg T a := fun q hq => by
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hq
      obtain ⟨wz, hwz, hsz, hsv, hcl, hreg⟩ := hzval z hz
      refine ⟨z, hz, wz, hwz, ?_, hcl, hreg⟩
      rw [hsv, ← Array.mem_toList_iff, ecs_args_three hsz]; simp
    have hS := ec_pieces hNC hL hRS _ _ _ hpcS
      (fun p hp => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hp
        exact (hins _ (hmemPair he).1).1)
      (fun q hq => by
        obtain ⟨z, -, wz, -, hqa, -, hreg⟩ := hpcv q hq
        exact hreg q hqa)
      (fun q hq hn' => by
        obtain ⟨z, -, wz, -, hqa, hcl, -⟩ := hpcv q hq
        exact hcl q hqa hn')
      (fun a ha => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
        exact hrel _ (hmemPair he).2)
      (fun a ha => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
        exact himk _ (hmas _ (hmemPair he).2))
      (fun q hq yq hyq hn' => by
        have := hsrc q hq
        rw [hn', Bool.false_or, Array.contains_iff_mem] at this
        exact hfront q (ecc_mem_front hu this) yq hyq)
    rw [ecc_zip_map, ecc_flatMap_pat (fun p r => leafVals (tabs.ty p.type) r), List.map_map] at hS
    -- the leading arguments and the memory
    have hsame : ∀ a ∈ u.args, special f g a = false →
        Sem.Refines (rv frS a) (rv T a) := fun a ha hs => by
      obtain ⟨y', hy', hr⟩ := hfront a (ecc_mem_front hu ha) _ (reg_rv (hRu a ha))
      rw [ecCv_of_not_special hs] at hr
      rw [rv_of hy']
      exact hr
    have hlr : Sem.RefinesList ((u.args.extract 0 k).toList.map (rv frS))
        ((u.args.extract 0 k).toList.map (rv T)) :=
      ecc_map_refines fun a ha => hsame a
        (hmu a (List.mem_append_left _ (List.mem_append_left _ ha))) (hleadns a ha)
    have hm0 : u.args[u.args.size - 1]! ∈ u.args := hmu _ (List.mem_append_right _ (by simp))
    have hmv := hsame _ hm0 hmns
    have hlk : ((u.args.extract 0 k).toList.map (rv frS)).length = k := by
      simp only [List.length_map, Array.length_toList, Array.size_extract]; omega
    obtain ⟨hct, hct', hcallee, hclo⟩ := ecc_callTarget (ctx := Ctx.make tabs f)
      (ctx' := Ctx.make tabs g) rfl hmap rfl hwaux (rest := (u.args.extract k (u.args.size - 1)).toList.map
        (rv frS) ++ [rv frS u.args[u.args.size - 1]!])
      (rest' := (w.args.extract k (w.args.size - 1)).toList.map (rv T) ++ [rv T w.args[w.args.size - 1]!])
      hlk hlr
    -- the call's memory and the decoded arguments
    have hmem : ∀ m, rv frS u.args[u.args.size - 1]! = .mem m →
        ((u.args.extract k (u.args.size - 1)).toList.map (rv frS)).any Val.hasPoison = false →
        outargsOK tabs 0 m (insOf abi) = true →
        ∃ mN D, rv T w.args[w.args.size - 1]! = .mem mN ∧
          Mem.Refines (m.poisonBlock (.outargs 0)) (mN.poisonBlock (.outargs 0)) ∧
          outargsOK tabs 0 mN (insOf abi) = true ∧
          decodeArgs tabs 0 mN (insOf abi) ((w.args.extract k (w.args.size - 1)).toList.map (rv T)) =
            some D ∧
          Sem.RefinesList ((u.args.extract k (u.args.size - 1)).toList.map (rv frS)) D := by
      intro m hm _ hokm
      rw [hm] at hmv
      obtain ⟨M, hMT, hMR⟩ : ∃ M, rv T u.args[u.args.size - 1]! = .mem M ∧ Mem.Refines m M := by
        revert hmv
        generalize rv T u.args[u.args.size - 1]! = yT
        intro hmv
        cases hmv with
        | mem h => exact ⟨_, rfl, h⟩
      have hat : ∀ s ∈ leafSlots tabs ((argPairs false (insOf abi)
          (u.args.extract k (u.args.size - 1)).toList).map Prod.fst), atom s.2 = true := fun s hs => by
        obtain ⟨p, hp, l, hl, rfl⟩ := ecs_mem_leafSlots hs
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hp
        exact (mem_leaves (hins _ (hmemPair he).1).1 hl).2
      obtain ⟨Mt, hMt, hW⟩ := ecs_chain hNC hL _ hcs' htopEL hsOK hat
        (fun z hz wz qw hwz hqw hn => hHS _ ⟨zs, hcs, z, hz, wz, qw, hwz, hqw, hn, rfl⟩) M hMT
      have hblk : ∀ e ∈ List.zipWith ecsW (leafSlots tabs ((argPairs false (insOf abi)
          (u.args.extract k (u.args.size - 1)).toList).map Prod.fst))
          (zs.map fun z => rv T (storeVal g z)), e.1.blk = .outargs 0 := fun e he => by
        obtain ⟨a, -, b, rfl⟩ := ecs_mem_zipWith he
        rfl
      have hokM : outargsOK tabs 0 Mt (insOf abi) = true := by
        rw [writeAll_outargsOK hW, hMR.outargsOK]; exact hokm
      have hpoi : Mem.Refines (m.poisonBlock (.outargs 0)) (Mt.poisonBlock (.outargs 0)) := by
        rw [writeAll_poison hblk hW]; exact hMR.poisonBlock _
      -- the arguments, register and stack
      have hpairs : ∀ e ∈ (insOf abi).zip (u.args.extract k (u.args.size - 1)).toList,
          (rv frS e.2).hasTy (tabs.ty e.1.type) = true := fun e he => by
        have hb : e ∈ argPairs (!e.1.regs.isEmpty) (insOf abi) (u.args.extract k (u.args.size - 1)).toList :=
          List.mem_filter.2 ⟨he, by simp⟩
        have heq : eqE (shapeOf (typeShapes tabs) f e.2) (tabs.ty e.1.type) = true := by
          cases hr : e.1.regs.isEmpty with
          | false =>
            rw [hr] at hb
            exact ecc_piecesOK_eqE hpc e (by rw [ecc_zip_fst_snd]; exact hb)
          | true =>
            rw [hr] at hb
            exact ecc_piecesOK_eqE hpcS e (by rw [ecc_zip_fst_snd]; exact hb)
        have hreg := reg_rv (hRu _ (hmas _ (List.of_mem_zip he).2))
        have := (hRS _ _ hreg).1
        rwa [← shapeOf_eq, eqE_hasTy heq] at this
      have hlenL : (insOf abi).length = (u.args.extract k (u.args.size - 1)).toList.length := hlen
      have hstk := ecs_stack_params (M := Mt)
        ((argPairs false (insOf abi) (u.args.extract k (u.args.size - 1)).toList).map
          fun e => (e.1, rv frS e.2)) _ hS
        (by
          rw [List.map_map]
          exact ecs_reads (ecs_leafSlots_pairwise (fun p hp => by
              obtain ⟨e, he, rfl⟩ := List.mem_map.1 hp
              exact (hins _ (hmemPair he).1).1)
            (ecs_slotsSorted_pairwise hsorted)) (ecs_storesOK_bounds hsOK) hW)
        (by
          rw [List.map_map]
          exact fun s hs => (ecs_storesOK_bounds hsOK s hs).2)
        (fun xe hxe => by
          obtain ⟨e, he, rfl⟩ := List.mem_map.1 hxe
          have hmz := (List.mem_filter.1 he)
          have hr : e.1.regs.isEmpty = true := by simpa using hmz.2
          obtain ⟨hwe, hoff⟩ := hins _ (hmemPair he).1
          rw [if_pos hr] at hoff
          refine ⟨hwe, hpairs e hmz.1, hoff, ?_⟩
          have := List.all_eq_true.1 hokM e.1 (hmemPair he).1
          rw [hr, Bool.not_true, Bool.false_or, ecs_ofInt hoff] at this
          exact this)
      obtain ⟨D, hD, hGD⟩ := ecc_decodeArgs_mixed (act := 0) (M := Mt)
        (((insOf abi).zip (u.args.extract k (u.args.size - 1)).toList).map fun e => (e.1, rv frS e.2))
        ((w.args.extract k (w.args.size - 1)).toList.map (rv T))
        (fun xe hxe => by
          obtain ⟨e, he, rfl⟩ := List.mem_map.1 hxe
          exact ⟨(hins _ (List.of_mem_zip he).1).1, hpairs e he⟩)
        (fun xe hxe hr => by
          obtain ⟨e, he, rfl⟩ := List.mem_map.1 hxe
          have := (hins _ (List.of_mem_zip he).1).2
          dsimp only at hr ⊢
          rw [if_neg (by rw [hr]; exact Bool.false_ne_true)] at this
          exact this)
        (fun xe hxe hr => by
          have hmf : xe ∈ (((insOf abi).zip (u.args.extract k (u.args.size - 1)).toList).map
              fun e => (e.1, rv frS e.2)).filter (fun x => !x.1.regs.isEmpty == false) :=
            List.mem_filter.2 ⟨hxe, by simp [hr]⟩
          rw [ecc_argPairs_map] at hmf
          obtain ⟨bs, hbs, hv⟩ := hstk xe hmf
          obtain ⟨e, he, rfl⟩ := List.mem_map.1 hxe
          obtain ⟨-, hoff⟩ := hins _ (List.of_mem_zip he).1
          rw [if_pos hr] at hoff
          exact ⟨bs, by rw [ecs_ofInt hoff]; exact hbs, hv⟩)
        (by rw [ecc_argPairs_map]; exact hP)
      have hfst : (((insOf abi).zip (u.args.extract k (u.args.size - 1)).toList).map
          fun e => (e.1, rv frS e.2)).map Prod.fst = insOf abi := by
        rw [List.map_map]
        exact List.map_fst_zip (by omega)
      have hsnd : (((insOf abi).zip (u.args.extract k (u.args.size - 1)).toList).map
          fun e => (e.1, rv frS e.2)).map Prod.snd =
          (u.args.extract k (u.args.size - 1)).toList.map (rv frS) := by
        rw [List.map_map, show (Prod.snd ∘ fun e : ABIParam × ID => (e.1, rv frS e.2)) =
          rv frS ∘ Prod.snd from rfl, ← List.map_map, List.map_snd_zip (by omega)]
      rw [hfst] at hD
      rw [hsnd] at hGD
      exact ⟨Mt, D, hMt, hpoi, hokM, hD, hGD⟩
    have hrel' := ecc_callOp hE (ctx := Ctx.make tabs f) (ctx' := Ctx.make tabs g) rfl rfl hpre hpost
      hwaux habi houts hct hct' hcallee hclo (fun m hm hp hokm => hmem m hm hp hokm)
    -- the evaluations
    have hRw' : ∀ a ∈ w.args, Reg T a := hRw
    have hopw : w.op = .StaticLECall ∨ w.op = .ClosureLECall ∨ w.op = .InterLECall ∨
        w.op = .StaticCall ∨ w.op = .ClosureCall ∨ w.op = .InterCall := by
      simp only [Bool.or_eq_true, beq_iff_eq] at hpost
      rcases hpost with (h | h) | h <;> simp [h]
    have hopu' : u.op = .StaticLECall ∨ u.op = .ClosureLECall ∨ u.op = .InterLECall ∨
        u.op = .StaticCall ∨ u.op = .ClosureCall ∨ u.op = .InterCall := by
      rcases hopu with h | h | h <;> simp [h]
    rw [evalValue_of_regs hRu, evalValue_of_regs hRw', ecc_evalOp_call hopu', ecc_evalOp_call hopw,
      hsu, hsw, List.map_append, List.map_append, List.append_assoc, List.map_append,
      List.map_append, List.append_assoc, List.map_cons, List.map_cons, List.map_nil, List.map_nil]
    rw [huid, hwid, tys_of_value hu, tys_of_value hw, Option.getD_some, Option.getD_some]
    revert hrel'
    generalize callOp env (Ctx.make tabs f) u _ = R1
    generalize callOp env (Ctx.make tabs g) w _ = R2
    intro hrel'
    cases hrel' with
    | ok hR =>
      obtain ⟨rs, m, a, rfl, hF, hR⟩ := hR
      refine .ok ?_
      obtain ⟨us, hus, husl, hue, hul⟩ := ecf_tupleOf htup
      rw [ecf_valueTy] at hus
      rw [hus, Val.retype_of_hasTy (by
        show Val.hasTyPre _ us = true
        exact ecc_hasTyPre_call (tl := [a]) hF hue (by rw [husl, List.length_map]) hul m),
        ecc_cv_call hu hcall (ecf_not_invalidated hw hinv)]
      have hco : callOuts tabs u.aux = outsOf abi := by
        unfold callOuts; rw [habi]; rfl
      rw [hco, ecc_convTuple (ecf_forall₂_length hF), shapeOf, hw, ecf_valueTy]
      exact retype_mono _ hR
    | panic e hm => exact .panic e hm
    | stuck msg r => exact .stuck msg _
  · cases hok

/-- **The call obligation**, given that the target holds the `SP`s of the stack-argument stores
the source defines (`ecStackSP`). -/
theorem obl_call {tabs : Tables} {f g : Func} {x : ID} {u w : Value} {HS HT : ID → Prop}
    (hu : f.value? x = some u) (hw : g.value? x = some w) (hcall : (callOpMap u.op).isSome = true)
    (hok : callOK tabs (typeShapes tabs) f g u w = true)
    (huid : u.id = x) (L : ID → Prop) (hLx : L x)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true → L a)
    (hH : ∀ a ∈ u.args, EcoImkHeld tabs f g HS HT a) (hSP : ∀ a, ecStackSP f g u w a → HT a) :
    Obl tabs f g (ecCv tabs f g) (isNewB f) (ecFront f g x) HS HT x :=
  obl_of_imk (obl_call_imk hu hw hcall hok huid L hLx hL) hu hH hSP

end GoFV.Proof.EC

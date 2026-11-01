import GoFV.Proof.Pass.ECChain
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
shortcut (`EcImkFacts`, which `Obl` does not provide); `obl_call`/`obl_result` are the `Obl`s
when no argument's node in `g` is an `IMake` (the shortcut cannot apply).
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
arguments. -/
def EcOblImk (tabs : Tables) (f g : Func) (x : ID) : Prop :=
  ∀ u w, f.value? x = some u → g.value? x = some w →
  ∀ env : Env, env.Mono → ∀ frS T : Frame, T = { frS with regs := T.regs } →
  RegsOK (Ctx.make tabs f) frS →
  ∀ E : ID → Prop, NewCons env (Ctx.make tabs g) (isNewB f) T E →
    (∀ a ∈ w.args, isNewB f a = true → E a) → (∀ a ∈ w.args, Reg T a) → (∀ a ∈ u.args, Reg frS a) →
    (∀ a ∈ ecFront f g x, ∀ y, frS.regs[a]? = some (some y) →
      ∃ y', T.regs[a]? = some (some y') ∧ Sem.Refines (ecCv tabs f g a y) y') →
    (∀ a ∈ u.args, EcImkFacts env tabs g T a) →
    ResCv (ecCv tabs f g x) (evalValue env (Ctx.make tabs f) frS u)
      (evalValue env (Ctx.make tabs g) T w)

/-- Without `IMake` arguments in `g`, `EcOblImk` is `Obl`. -/
theorem obl_of_imk {tabs : Tables} {f g : Func} {x : ID} {u : Value} (h : EcOblImk tabs f g x)
    (hu : f.value? x = some u)
    (hno : ∀ a ∈ u.args, ∀ aw, g.value? a = some aw → aw.op ≠ .IMake) :
    Obl tabs f g (ecCv tabs f g) (isNewB f) (ecFront f g x) x := by
  intro u' w hu' hw env hE frS T hT hRS E hNC hEw hRw hRu hfront
  rw [hu] at hu'
  cases hu'
  exact h u w hu hw env hE frS T hT hRS E hNC hEw hRw hRu hfront
    fun a ha aw haw hop => absurd hop (hno a ha aw haw)

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
    EcOblImk tabs f g x := by
  intro u' w' hu' hw' env _ frS T _ hRS E hNC hEw hRw hRu hfront himk
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
  have hP := ec_pieces hNC hL _ _ _ hpc (fun p hp => (hreg' p hp).2.1)
    (fun q hq => hRw q (Array.mem_toList_iff.1 (ecc_mem_of_split hsw hq)))
    (fun q hq hn' => have hq' := Array.mem_toList_iff.1 (ecc_mem_of_split hsw hq)
      ⟨hEw q hq' hn', hLw q hq' hn'⟩) hrel
    (fun a ha => himk a (Array.mem_toList_iff.1 (ecc_mem_of_split hsu ha)))
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

/-- **The `MakeResult` obligation** (no `IMake` argument pieces). -/
theorem obl_result {tabs : Tables} {f g : Func} {x : ID} {u w : Value}
    (hu : f.value? x = some u) (hw : g.value? x = some w) (hop : u.op = .MakeResult)
    (hok : resultOK tabs (typeShapes tabs) f g u w = true) (_hown : g.ownAux = f.ownAux)
    (hreg : regParamsOK tabs (ownOuts tabs f) = true) (huid : u.id = x)
    (L : ID → Prop) (hLx : L x)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true → L a)
    (hno : ∀ a ∈ u.args, ∀ aw, g.value? a = some aw → aw.op ≠ .IMake) :
    Obl tabs f g (ecCv tabs f g) (isNewB f) (ecFront f g x) x :=
  obl_of_imk (obl_result_imk hu hw hop hok hreg huid L hLx hL) hu hno

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

/-- **The call**: the source's call on the Go-typed arguments and the target's on their pieces. -/
theorem ecc_callOp {env : Env} (hE : env.Mono) {ctx ctx' : Ctx} (htabs : ctx'.tabs = ctx.tabs)
    (hact : ctx'.act = ctx.act) {u w : Value}
    (hpre : (u.op == .StaticCall || u.op == .ClosureCall || u.op == .InterCall) = false)
    (hpost : (w.op == .StaticCall || w.op == .ClosureCall || w.op == .InterCall) = true)
    (haux : w.aux = u.aux) {abi : CallABI} (habi : callABI? ctx.tabs u.aux = some abi)
    (hregs : ∀ p ∈ abi.params.toList, ecfReg ctx.tabs p) {argv argv' G P' : List Val} {mv mv' : Val}
    (hct : (callTarget ctx u argv).2.2 = G ++ [mv]) (hct' : (callTarget ctx' w argv').2.2 = P' ++ [mv'])
    (hcallee : (callTarget ctx u argv).1 = none ∨ (callTarget ctx' w argv').1 = (callTarget ctx u argv).1)
    (hclo : OptRefines (callTarget ctx u argv).2.1 (callTarget ctx' w argv').2.1)
    (hmv : Sem.Refines mv mv')
    (hG : List.Forall₂ (fun (p : ABIParam) (r : Val) => r.hasTy (ctx.tabs.ty p.type) = true)
      (insOf abi) G)
    (hP : Sem.RefinesList (ecfPieces ctx.tabs (insOf abi) G) P') :
    Res.Rel (EcCallRes ctx.tabs (outsOf abi)) (callOp env ctx u argv) (callOp env ctx' w argv') := by
  have habi' : callABI? ctx'.tabs w.aux = some abi := by rw [htabs, haux]; exact habi
  have hins : ∀ p ∈ insOf abi, ecfReg ctx.tabs p := fun p hp => hregs p ((List.mem_filter.1 hp).1)
  have houts : ∀ p ∈ outsOf abi, ecfReg ctx.tabs p := fun p hp => hregs p ((List.mem_filter.1 hp).1)
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
      cases hmv with
      | @mem m m' hm =>
        dsimp only
        simp only [hpre, hpost, Bool.false_eq_true, ↓reduceIte, Option.map_some, Option.getD_some]
        simp only [insOf, outsOf] at hG hP hins houts ⊢
        obtain ⟨D, hD, hGD⟩ := ecc_decodeArgs ctx.act m hG hins
        obtain ⟨args', hd', hDa⟩ := decodeArgs_mono ctx.tabs ctx.act hm _ hP hD
        have hargs := hGD.trans hDa
        rw [hd']
        dsimp only [pure, Res.bind]
        split
        · exact .stuck _ _
        · next hp =>
          simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hp
          have hp1 := hargs.any_hasPoison hp.1
          have hp2 : (clo'.map Val.hasPoison).getD false = false := by
            cases hclo with
            | none => rfl
            | some hcc => exact (hcc.noPoison (by simpa using hp.2)).1
          simp only [hp1, hp2, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
          cases hx : env.extern callee with
          | none => exact .stuck _ _
          | some c =>
            dsimp only
            have := hE _ _ hx hp.1 hp.2 hargs hclo (hm.poisonBlock (.outargs ctx.act))
            revert this
            generalize c G clo (m.poisonBlock (.outargs ctx.act)) = o
            generalize c args' clo' (m'.poisonBlock (.outargs ctx.act)) = o'
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

theorem obl_call_imk {tabs : Tables} {f g : Func} {x : ID} {u w : Value}
    (hu : f.value? x = some u) (hw : g.value? x = some w) (hcall : (callOpMap u.op).isSome = true)
    (hok : callOK tabs (typeShapes tabs) f g u w = true) (huid : u.id = x)
    (L : ID → Prop) (hLx : L x)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true → L a) :
    EcOblImk tabs f g x := by
  intro u' w' hu' hw' env hE frS T _ hRS E hNC hEw hRw hRu hfront himk
  rw [hu] at hu'; cases hu'
  rw [hw] at hw'; cases hw'
  unfold callOK at hok
  split at hok
  · next op k abi hmap habi =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true', ge_iff_le,
      List.all_eq_true] at hok
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hwop, hwaux⟩, -⟩, hkn⟩, hregs⟩, hws⟩, hlead⟩, hlast⟩, hleadns⟩, hmns⟩,
      hpc⟩, htup⟩, -⟩ := hok
    obtain ⟨hopu, hpre, hpost, hinv⟩ := ecc_callOpMap hmap
    subst hwop
    obtain ⟨hwid, hLw⟩ := hL x hLx w hw
    have hregs' := ecf_reg_of hregs
    have hsu := ecc_args_split u.args k hkn
    have hsw := ecc_args_split w.args k hws
    rw [hlead, hlast] at hsw
    have hmu : ∀ a, a ∈ (u.args.extract 0 k).toList ++ (u.args.extract k (u.args.size - 1)).toList ++
        [u.args[u.args.size - 1]!] → a ∈ u.args := fun a ha => by
      rw [← Array.mem_toList_iff, hsu]; exact ha
    have hmw : ∀ a, a ∈ (u.args.extract 0 k).toList ++ (w.args.extract k (w.args.size - 1)).toList ++
        [u.args[u.args.size - 1]!] → a ∈ w.args := fun a ha => by
      rw [← Array.mem_toList_iff, hsw]; exact ha
    -- the Go-typed arguments and their pieces
    have hrel : ∀ a ∈ (u.args.extract k (u.args.size - 1)).toList, EcArgRel tabs f g frS T a :=
      fun a ha => ecc_argRel hu hRS hRu hfront (hmu a (List.mem_append_left _ (List.mem_append_right _ ha)))
    have hG := ecc_pieces_hasTy _ _ _ hpc hrel
    have hP := ec_pieces hNC hL _ _ _ hpc
      (fun p hp => (hregs' p (List.mem_filter.1 hp).1).2.1)
      (fun q hq => hRw q (hmw q (List.mem_append_left _ (List.mem_append_right _ hq))))
      (fun q hq hn' => have hq' := hmw q (List.mem_append_left _ (List.mem_append_right _ hq)); ⟨hEw q hq' hn', hLw q hq' hn'⟩) hrel
      (fun a ha => himk a (hmu a (List.mem_append_left _ (List.mem_append_right _ ha))))
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
    have hmv := hsame _ (hmu _ (List.mem_append_right _ (List.mem_singleton_self _))) hmns
    have hlk : ((u.args.extract 0 k).toList.map (rv frS)).length = k := by
      simp only [List.length_map, Array.length_toList, Array.size_extract]; omega
    obtain ⟨hct, hct', hcallee, hclo⟩ := ecc_callTarget (ctx := Ctx.make tabs f)
      (ctx' := Ctx.make tabs g) rfl hmap rfl hwaux (rest := (u.args.extract k (u.args.size - 1)).toList.map
        (rv frS) ++ [rv frS u.args[u.args.size - 1]!])
      (rest' := (w.args.extract k (w.args.size - 1)).toList.map (rv T) ++ [rv T u.args[u.args.size - 1]!])
      hlk hlr
    have hrel' := ecc_callOp hE (ctx := Ctx.make tabs f) (ctx' := Ctx.make tabs g) rfl rfl hpre hpost
      hwaux habi hregs' hct hct' hcallee hclo hmv hG hP
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

/-- **The call obligation** (no `IMake` argument pieces). -/
theorem obl_call {tabs : Tables} {f g : Func} {x : ID} {u w : Value}
    (hu : f.value? x = some u) (hw : g.value? x = some w) (hcall : (callOpMap u.op).isSome = true)
    (hok : callOK tabs (typeShapes tabs) f g u w = true) (_hown : g.ownAux = f.ownAux)
    (huid : u.id = x) (L : ID → Prop) (hLx : L x)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true → L a)
    (hno : ∀ a ∈ u.args, ∀ aw, g.value? a = some aw → aw.op ≠ .IMake) :
    Obl tabs f g (ecCv tabs f g) (isNewB f) (ecFront f g x) x :=
  obl_of_imk (obl_call_imk hu hw hcall hok huid L hLx hL) hu hno

end GoFV.Proof.EC

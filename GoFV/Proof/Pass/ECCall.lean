import GoFV.Proof.Pass.ECStack
import GoFV.Proof.Pass.ECFinish
import GoFV.Proof.CallMono
import GoFV.Proof.MemRefine

/-!
# `expand calls`: the obligations of calls and `MakeResult`s (issue #28)

`obl_call`: a call on Go-typed arguments (`StaticLECall`, `ClosureLECall`, `InterLECall`)
becomes the post-`expand calls` call on the register pieces of its register-assigned arguments
(`ec_pieces`) and on a memory where a chain of new `Store`s wrote its stack-assigned ones
(`ECStack`); the target's `decodeArgs` rebuilds arguments refining the source's
(`ecc_decodeArgs_mixed`: `ofPieces_leafVals`, `ecs_stack_params`), the same callee's contract
sees refined arguments and memory (the stores vanish under the area's poisoning;
`Contract.Mono`), and the target's result pieces (`encodeResults`, `toPieces = leafVals`) refine
the conversion `convTuple` of the source's Go-typed results. `ecc_storeObl`: a stack-argument
store evaluates once the source reached its call (`NewObl`). `obl_result`: a `MakeResult` of
Go-typed results becomes one of their pieces.

Both are proved first in the form `EcOblImk`, `Obl` with the frame facts of the `IMake` data
shortcut (`EcImkFacts`) and the target's held values `H` (the `SP`s under the stack stores,
`ecStackSP`); `obl_call`/`obl_result` are the `Obl`s when every `IMake` argument is held
(`EcoImkHeld`) in target mode (it and its data operand among the target's held values,
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


theorem ecc_mem_of_split {l A B : List ID} {a : ID} (h : l = A ++ B) (ha : a ∈ A) : a ∈ l := by
  rw [h]; exact List.mem_append_left _ ha

/-! ## `Obl` with the frame facts of the `IMake` shortcut -/

/-- `Obl` of `x` for `expand calls` with the extra premise `EcImkFacts` for `x`'s source
arguments, given that the source registers of the values `HS0` and the target registers of the
values `H` hold their evaluations. -/
def EcOblImk (tabs : Tables) (f g : Func) (HS0 H : ID → Prop) (x : ID) : Prop :=
  ∀ u w, f.value? x = some u → g.value? x = some w →
  ∀ env : Env, env.Mono → ∀ frS T : Frame, T = { frS with regs := T.regs } →
  RegsOK (Ctx.make tabs f) frS →
  ∀ E : ID → Prop, NewCons env (Ctx.make tabs g) (isNewB f) T E →
    (∀ a ∈ w.args, isNewB f a = true → E a) → (∀ a ∈ w.args, Reg T a) → (∀ a ∈ u.args, Reg frS a) →
    (∀ a ∈ ecFront f g x, ∀ y, frS.regs[a]? = some (some y) →
      ∃ y', T.regs[a]? = some (some y') ∧ Sem.Refines (ecCv tabs f g a y) y') →
    (∀ a ∈ u.args, EcImkFacts env tabs f g frS T a) → (∀ a, H a → EcTgtHolds env tabs g T a) →
    (∀ a, HS0 a → EcSrcHolds env tabs f frS a) →
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
values `HS0` and `H` are among the source's and the target's held values. -/
theorem obl_of_imk {tabs : Tables} {f g : Func} {x : ID} {u : Value} {HS HT HS0 H : ID → Prop}
    (h : EcOblImk tabs f g HS0 H x) (hu : f.value? x = some u)
    (hH : ∀ a ∈ u.args, EcoImkHeld tabs f g HS HT a) (hHT : ∀ a, H a → HT a)
    (hHS : ∀ a, HS0 a → HS a) :
    Obl tabs f g (ecCv tabs f g) (isNewB f) (ecFront f g x) HS HT x := by
  intro u' w hu' hw env hE frS T hT hRS E hNC hEw hRw hRu hfront hheldS hheldT
  rw [hu] at hu'
  cases hu'
  refine h u w hu hw env hE frS T hT hRS E hNC hEw hRw hRu hfront (fun a ha aw haw hop => ?_)
    (fun a ha => hheldT a (hHT a ha)) fun a ha => hheldS a (hHS a ha)
  rcases hH a ha aw haw hop with ⟨h1, h2, h3⟩ | ⟨h1, hau, h3, hsp, hsh⟩
  · exact .inl ⟨hheldT a h1, hheldT _ h2, eco_ifaceShape h3⟩
  · exact .inr ⟨hheldS a h1, hau, eco_ifaceShape h3, hsp, hsh⟩

/-- An argument of the `Move` of `x`'s wide stack argument that the source defines is in
`ecFront`. -/
theorem eco_mem_front_move {f g : Func} {x z q : ID} {mw : Value} (hi : invalidated g x = false)
    (hz : stackMove f g x = some z)
    (hmw : g.value? z = some mw) (hq : q ∈ mw.args) (hn : isNewB f q = false) :
    q ∈ ecFront f g x := by
  unfold ecFront
  rw [hi, if_neg Bool.false_ne_true, hz]
  simp only [Option.bind_some, hmw, Option.map_some, Option.getD_some]
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_filter.2
    ⟨List.mem_append_right _ (Array.mem_toList_iff.2 hq), by rw [hn]; rfl⟩))

/-- `EcArgRel` of the source arguments of `x` in an obligation's frames. -/
theorem ecc_argRel {tabs : Tables} {f g : Func} {x : ID} {u : Value} {frS T : Frame}
    (hi : invalidated g x = false)
    (hu : f.value? x = some u) (hRS : RegsOK (Ctx.make tabs f) frS) (hRu : ∀ a ∈ u.args, Reg frS a)
    (hfront : ∀ a ∈ ecFront f g x, ∀ y, frS.regs[a]? = some (some y) →
      ∃ y', T.regs[a]? = some (some y') ∧ Sem.Refines (ecCv tabs f g a y) y')
    {a : ID} (ha : a ∈ u.args) : EcArgRel tabs f g frS T a := by
  have hr := reg_rv (hRu a ha)
  exact ⟨_, hr, hRS a _ hr, hfront a (ecFront_src hi hu ha) _ hr⟩

/-- The Go-typed arguments have their parameters' shapes. -/
theorem ecc_pieces_hasTy {tabs : Tables} {f g : Func} {frS T : Frame} :
    ∀ (ps : List ABIParam) (as pcs : List ID), piecesOK tabs (typeShapes tabs) f g false ps as pcs = true →
      (∀ a ∈ as, EcArgRel tabs f g frS T a) →
      List.Forall₂ (fun (p : ABIParam) (r : Val) => r.hasTy (tabs.ty p.type) = true) ps
        (as.map (rv frS))
  | [], [], _, _, _ => .nil
  | [], _ :: _, _, h, _ | _ :: _, [], _, h, _ => by simp [piecesOK] at h
  | p :: ps, a :: as, pcs, h, hrel => by
    unfold piecesOK at h
    simp only [Bool.and_eq_true, Bool.false_and, Bool.or_false] at h
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

/-- `encodeResults` of results of their shapes: their register pieces (the stack-assigned ones
go to memory). -/
theorem ecc_encodeResults {tabs : Tables} {act : Nat} :
    {ps : List ABIParam} → {rs : List Val} →
      List.Forall₂ (fun (p : ABIParam) (r : Val) => r.hasTy (tabs.ty p.type) = true) ps rs →
      (∀ p ∈ ps, wf (tabs.ty p.type) = true) → {m : Mem} → {res : List Val × Mem} →
      encodeResults tabs act ps rs m = some res → res.1 = ecfPieces tabs ps rs
  | _, _, .nil, _, _, _, h => by
    simp only [encodeResults, Option.some.injEq] at h
    subst h; rfl
  | p :: ps, r :: rs, .cons hr hf, hw, m, res, h => by
    have ih := @ecc_encodeResults tabs act ps rs hf (fun q hq => hw q (List.mem_cons_of_mem _ hq))
    unfold encodeResults at h
    dsimp only at h
    split at h
    · rename_i hst
      cases hwr : m.write ⟨.outargs act, BitVec.ofInt 64 p.offset⟩ (encode (tabs.ty p.type) r) with
      | none => rw [hwr] at h; cases h
      | some m' =>
        rw [hwr] at h
        rw [ih h]
        simp only [ecfPieces, List.zip_cons_cons, List.flatMap_cons, regLeafVals_stack hst,
          List.nil_append]
    · rename_i hst
      cases he : encodeResults tabs act ps rs m with
      | none => rw [he] at h; cases h
      | some r' =>
        rw [he] at h
        cases h
        simp only [ecfPieces, List.zip_cons_cons, List.flatMap_cons,
          regLeafVals_reg (Bool.eq_false_iff.2 hst), ← ih he,
          toPieces_eq_leafVals (hw p List.mem_cons_self) hr]

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

/-- **The call**: the source's call on the Go-typed arguments (retyped at the parameters' shapes)
and the target's on their pieces and its memory, which hold the Go-typed arguments (`decodeArgs`)
and agree with the source's outside the outgoing-arguments area. -/
theorem ecc_callOp {env : Env} (hE : env.Mono) {ctx ctx' : Ctx} (htabs : ctx'.tabs = ctx.tabs)
    (hact : ctx'.act = ctx.act) {u w : Value}
    (hpre : (u.op == .StaticCall || u.op == .ClosureCall || u.op == .InterCall) = false)
    (hpost : (w.op == .StaticCall || w.op == .ClosureCall || w.op == .InterCall) = true)
    (haux : w.aux = u.aux) {abi : CallABI} (habi : callABI? ctx.tabs u.aux = some abi)
    (houts : ∀ p ∈ outsOf abi, wf (ctx.tabs.ty p.type) = true) {argv argv' G P' : List Val} {mv mv' : Val}
    (hct : (callTarget ctx u argv).2.2 = G ++ [mv]) (hct' : (callTarget ctx' w argv').2.2 = P' ++ [mv'])
    (hcallee : (callTarget ctx u argv).1 = none ∨ (callTarget ctx' w argv').1 = (callTarget ctx u argv).1)
    (hclo : OptRefines (callTarget ctx u argv).2.1 (callTarget ctx' w argv').2.1)
    (hmem : ∀ m, mv = .mem m → (retypeResults ctx.tabs (insOf abi) G).any Val.hasPoison = false →
      outargsOK ctx.tabs ctx.act m (insOf abi) = true →
      ∃ mN D, mv' = .mem mN ∧
        Mem.Refines (m.poisonBlock (.outargs ctx.act)) (mN.poisonBlock (.outargs ctx.act)) ∧
        outargsOK ctx.tabs ctx.act mN (insOf abi) = true ∧
        decodeArgs ctx.tabs ctx.act mN (insOf abi) P' = some D ∧
        Sem.RefinesList (retypeResults ctx.tabs (insOf abi) G) D) :
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
        generalize retypeResults ctx.tabs (abi.params.toList.filter (!·.out)) G = G' at hmem ⊢
        by_cases hp : (G'.any Val.hasPoison || (clo.map Val.hasPoison).getD false) = true
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
            generalize c G' clo (m.poisonBlock (.outargs ctx.act)) = o
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
                have hP := ecc_encodeResults hF houts he
                obtain ⟨P1, M1⟩ := r
                dsimp only at hP hr1 hr2 ⊢
                subst hP
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

/-- The pairs of the parameters and arguments `piecesOK` accepts have the parameters' shapes (or,
with `cast`, are pointers of 64-bit integer parameters). -/
theorem ecc_piecesOK_eqE {tabs : Tables} {sh : Array Ty} {f g : Func} {cast : Bool} :
    ∀ {ps : List ABIParam} {as pcs : List ID}, piecesOK tabs sh f g cast ps as pcs = true →
      ∀ x ∈ ps.zip as, eqE (shapeOf sh f x.2) (tabs.ty x.1.type) = true ∨
        cast = true ∧ castOK (shapeOf sh f x.2) (tabs.ty x.1.type) = true
  | [], _, _, _, x, hx => by simp at hx
  | _ :: _, [], _, h, _, _ => by simp [piecesOK] at h
  | p :: ps, a :: as, pcs, h, x, hx => by
    unfold piecesOK at h
    simp only [Bool.and_eq_true, Bool.or_eq_true] at h
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

/-- A pointer as the register piece of a 64-bit integer: its address (`decodeInt`), as retyping. -/
theorem ecc_ofPieces_ptr (q : Ptr) : ofPieces (.int .w64) [.ptr q] = (Val.ptr q).retype (.int .w64) := by
  have hb : putBytes (Array.replicate 8 Byte.poison) 0 (ptrBytes q) = ptrBytes q := by
    have hs : (putBytes (Array.replicate 8 Byte.poison) 0 (ptrBytes q)).size = (ptrBytes q).size := by
      rw [putBytes_size]; simp [ptrBytes]
    have ha := putBytes_agree (dst := Array.replicate 8 Byte.poison) (off := 0) (src := ptrBytes q)
      (by simp [ptrBytes])
    apply Array.ext_getElem?
    intro k
    by_cases hk : k < (ptrBytes q).size
    · have := ha k hk
      simpa using this
    · rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]
  show decode (putBytes (Array.replicate 8 Byte.poison) 0 (ptrBytes q)) 0 (.int .w64) = _
  rw [hb]
  show decodeInt .w64 ((ptrBytes q).extract 0 (0 + 8)) = _
  rw [Array.extract_eq_self_of_le (by simp [ptrBytes])]
  unfold decodeInt
  rw [bytesNat?_ptrBytes, bytesPtr?_ptrBytes]
  simp only [Val.retype]
  cases q.addr? <;> rfl

theorem ecc_ecPieceVals_length {t : Ty} (hw : wf t = true) (cast : Bool) (r : Val) :
    (ecPieceVals cast t r).length = (leaves t).length := by
  unfold ecPieceVals
  split
  · rfl
  · exact leafVals_length hw

/-- **A register argument from its pieces**: an argument of its parameter's shape (or a pointer
of a 64-bit integer parameter) retyped at the parameter's shape is refined by assembling refined
pieces. -/
theorem ecc_ofPieces_arg {t : Ty} {v : Val} (hw : wf t = true)
    (hv : v.hasTy t = true ∨ t = .int .w64 ∧ ∃ e, v.hasTy (.ptr e) = true) {ys : List Val}
    (h : Sem.RefinesList (ecPieceVals true t v) ys) : Sem.Refines (v.retype t) (ofPieces t ys) := by
  rcases hv with hv | ⟨rfl, e, hv⟩
  · rw [ecPieceVals_of_hasTy true hv] at h
    rw [Val.retype_of_hasTy hv]
    exact (ofPieces_leafVals hw hv).trans (ofPieces_mono _ h)
  · cases v with
    | poison => exact .poison _
    | ptr q =>
      rw [← ecc_ofPieces_ptr]
      exact ofPieces_mono _ h
    | int w x =>
      have hv' : (Val.int w x).hasTy (.int .w64) = true := by
        cases w <;> simp_all [Val.hasTy]
      rw [ecPieceVals_of_hasTy true hv'] at h
      rw [Val.retype_of_hasTy hv']
      exact (ofPieces_leafVals hw hv').trans (ofPieces_mono _ h)
    | _ => simp [Val.hasTy] at hv

/-- **`decodeArgs` of register and stack arguments**: the register pieces refine the expected
pieces of the register-assigned arguments (`ecPieceVals`), and each stack slot decodes to a
refinement of its argument; the decoded arguments refine the arguments retyped at the
parameters' shapes. -/
theorem ecc_decodeArgs_mixed {tabs : Tables} {act : Nat} {M : Mem} :
    ∀ (L : List (ABIParam × Val)) (P' : List Val),
      (∀ x ∈ L, x.1.regs.isEmpty = false → wf (tabs.ty x.1.type) = true ∧
        (leaves (tabs.ty x.1.type)).length = x.1.regs.size ∧
        (x.2.hasTy (tabs.ty x.1.type) = true ∨
          tabs.ty x.1.type = .int .w64 ∧ ∃ e, x.2.hasTy (.ptr e) = true)) →
      (∀ x ∈ L, x.1.regs.isEmpty = true → ∃ bs,
        M.read ⟨.outargs act, BitVec.ofInt 64 x.1.offset⟩ (tabs.ty x.1.type).size = some bs ∧
        Sem.Refines (x.2.retype (tabs.ty x.1.type)) (decode bs 0 (tabs.ty x.1.type))) →
      Sem.RefinesList ((L.filter fun x => !x.1.regs.isEmpty == true).flatMap
        fun x => ecPieceVals true (tabs.ty x.1.type) x.2) P' →
      ∃ D, decodeArgs tabs act M (L.map Prod.fst) P' = some D ∧
        Sem.RefinesList (retypeResults tabs (L.map Prod.fst) (L.map Prod.snd)) D
  | [], P', _, _, h => by
    rw [RefinesList.nil_inv h]
    exact ⟨[], rfl, .nil⟩
  | (p, v) :: L, P', hr, hs, hP => by
    simp only [List.map_cons, retypeResults]
    cases he : p.regs.isEmpty with
    | false =>
      obtain ⟨hwp, hlp, hvp⟩ := hr (p, v) List.mem_cons_self he
      rw [List.filter_cons, if_pos (by simp [he]), List.flatMap_cons] at hP
      obtain ⟨y1, y2, rfl, h1, h2⟩ := ecs_rl_split hP
      obtain ⟨D, hD, hGD⟩ := ecc_decodeArgs_mixed L y2 (fun x hx => hr x (List.mem_cons_of_mem _ hx))
        (fun x hx => hs x (List.mem_cons_of_mem _ hx)) h2
      have hlv : y1.length = p.regs.size := by
        rw [← ecs_rl_length h1, ecc_ecPieceVals_length hwp]; exact hlp
      refine ⟨ofPieces (tabs.ty p.type) y1 :: D, ?_, .cons (ecc_ofPieces_arg hwp hvp h1) hGD⟩
      unfold decodeArgs
      have hnl : ¬ (y1 ++ y2).length < p.regs.size := by rw [List.length_append]; omega
      simp only [he, Bool.false_eq_true, ↓reduceIte, hnl, List.take_left' hlv, List.drop_left' hlv,
        hD]
      rfl
    | true =>
      rw [List.filter_cons, if_neg (by simp [he])] at hP
      obtain ⟨D, hD, hGD⟩ := ecc_decodeArgs_mixed L P' (fun x hx => hr x (List.mem_cons_of_mem _ hx))
        (fun x hx => hs x (List.mem_cons_of_mem _ hx)) hP
      obtain ⟨bs, hbs, hv⟩ := hs (p, v) List.mem_cons_self he
      refine ⟨decode bs 0 (tabs.ty p.type) :: D, ?_, .cons hv hGD⟩
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

/-- The `SP`s under the addresses of the stack-argument stores and the `Move` of call `u` (`w`
in `g`) that the source defines: what the call's obligation needs the target to hold. -/
def ecStackSP (f g : Func) (u w : Value) (a : ID) : Prop :=
  ∃ z, ((∃ zs, callStores f g u w = some zs ∧ z ∈ zs) ∨ callMove f g u w = some z) ∧
    ∃ wz qw, g.value? z = some wz ∧ g.value? wz.args[0]! = some qw ∧
      isNewB f qw.args[0]! = false ∧ a = qw.args[0]!

/-- The `Dereference` arguments of call `u` (`w` in `g`) when the target copies a wide stack
argument with a `Move`: what the call's obligation needs the source to hold. -/
def ecMoveArg (f g : Func) (u w : Value) (a : ID) : Prop :=
  (callMove f g u w).isSome = true ∧ a ∈ u.args ∧ ∃ au, f.value? a = some au ∧ au.op = .Dereference

/-- The parts of `stackOK`: the stack parameters split into the one the `Move` copies (if any)
and the ones the `Store`s write. -/
theorem ecc_stackOK_inv {tabs : Tables} {sh : Array Ty} {f g : Func} {u w : Value}
    {ins : List ABIParam} {as : List ID} (h : stackOK tabs sh f g u w ins as = true) :
    slotsSorted tabs ((argPairs false ins as).map (·.1)) = true ∧
    ∃ zs sp0 sp1, callStores f g u w = some zs ∧ argPairs false ins as = sp0 ++ sp1 ∧
      storeArgsOK tabs sh f g u sp1 zs = true ∧
      ((callMove f g u w = none ∧ sp0 = []) ∨
        ∃ z p a, callMove f g u w = some z ∧ sp0 = [(p, a)] ∧ moveOK tabs sh f g u p a z = true) := by
  unfold stackOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hs, h⟩ := h
  refine ⟨hs, ?_⟩
  split at h
  · rename_i zs hzs
    split at h
    · rename_i hm
      exact ⟨zs, [], _, hzs, rfl, h, .inl ⟨hm, rfl⟩⟩
    · rename_i z p a sp' hm hsp
      rw [Bool.and_eq_true] at h
      exact ⟨zs, [(p, a)], sp', hzs, by rw [hsp]; rfl, h.2, .inr ⟨z, p, a, hm, rfl, h.1⟩⟩
    · cases h
  · cases h

/-- The `Move` of a wide stack argument: a new `Move` on the source call's memory. -/
theorem ecc_callMove_spec {f g : Func} {u w : Value} {z : ID} (h : callMove f g u w = some z) :
    isNewB f z = true ∧ ∃ mw, g.value? z = some mw ∧ mw.op = .Move ∧ mw.args.size = 3 ∧
      mw.args[2]! = u.args[u.args.size - 1]! := by
  unfold callMove at h
  dsimp only at h
  split at h
  · rename_i mw hmw
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨hc.1.1.1, mw, hmw, hc.1.1.2, hc.1.2, hc.2⟩
    · cases h
  · cases h

/-- The facts of `moveOK`. -/
theorem ecc_moveOK_spec {tabs : Tables} {sh : Array Ty} {f g : Func} {u : Value} {p : ABIParam}
    {a z : ID} (h : moveOK tabs sh f g u p a z = true) :
    ∃ mw au, g.value? z = some mw ∧ f.value? a = some au ∧ mw.args.size = 3 ∧
      spOffOK sh g (isNewB f) mw.args[0]! p.offset = true ∧
      mw.auxInt.toInt = ((tabs.ty p.type).size : Int) ∧ shapeOf sh g z = .mem ∧
      au.op = .Dereference ∧ au.args.size = 2 ∧ au.args[0]! = mw.args[1]! ∧
      au.args[1]! = u.args[u.args.size - 1]! ∧ eqE (shapeOf sh f a) (tabs.ty p.type) = true ∧
      moveTy (tabs.ty p.type) = true ∧ isNewB f mw.args[1]! = false ∧
      special f g mw.args[1]! = false := by
  unfold moveOK at h
  dsimp only at h
  split at h
  · rename_i mw au hmw hau
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
    refine ⟨mw, au, hmw, hau, h1, h2, h3, ?_, h5, h6, h7, h8, h9, h10, h11, h12⟩
    split at h4
    · assumption
    · cases h4
  · cases h

theorem obl_call_imk {tabs : Tables} {f g : Func} {x : ID} {u w : Value}
    (hu : f.value? x = some u) (hw : g.value? x = some w) (hcall : (callOpMap u.op).isSome = true)
    (hok : callOK tabs (typeShapes tabs) f g u w = true) (huid : u.id = x)
    (L : ID → Prop) (hLx : L x)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true → L a) :
    EcOblImk tabs f g (ecMoveArg f g u w) (ecStackSP f g u w) x := by
  intro u' w' hu' hw' env hE frS T _ hRS E hNC hEw hRw hRu hfront himk hHS hMA
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
    have hi : invalidated g x = false := by
      unfold invalidated; rw [hw]; exact Bool.eq_false_iff.2 fun h => hinv (beq_iff_eq.1 h)
    have houts := ec_outsOK_wf houtsR
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
    have hinsR : ∀ p ∈ insOf abi, p.regs.isEmpty = false →
        wf (tabs.ty p.type) = true ∧ (leaves (tabs.ty p.type)).length = p.regs.size := by
      intro p hp hr
      have := List.all_eq_true.1 hinsOK p hp
      rw [hr, if_neg (by simp), Bool.and_eq_true] at this
      exact ⟨this.1, beq_iff_eq.1 this.2⟩
    have hinsS : ∀ p ∈ insOf abi, p.regs.isEmpty = true → movTy (tabs.ty p.type) = true ∧ 0 ≤ p.offset := by
      intro p hp hr
      have := List.all_eq_true.1 hinsOK p hp
      rw [hr, if_pos rfl, Bool.and_eq_true] at this
      exact ⟨this.1, of_decide_eq_true this.2⟩
    have hregOf : ∀ {reg : Bool} {e : ABIParam × ID},
        e ∈ argPairs reg (insOf abi) (u.args.extract k (u.args.size - 1)).toList →
        e.1.regs.isEmpty = !reg := fun {reg e} he => by
      have := (List.mem_filter.1 he).2
      revert this
      cases e.1.regs.isEmpty <;> cases reg <;> decide
    -- the Go-typed arguments
    have hrel : ∀ a ∈ (u.args.extract k (u.args.size - 1)).toList, EcArgRel tabs f g frS T a :=
      fun a ha => ecc_argRel hi hu hRS hRu hfront (hmas a ha)
    have hmemPair : ∀ {reg : Bool} {e : ABIParam × ID},
        e ∈ argPairs reg (insOf abi) (u.args.extract k (u.args.size - 1)).toList →
        e.1 ∈ insOf abi ∧ e.2 ∈ (u.args.extract k (u.args.size - 1)).toList := fun he =>
      List.of_mem_zip (List.mem_filter.1 he).1
    -- the register pieces
    have hP := ec_pieces hNC hL hRS true _ _ _ hpc
      (fun p hp => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hp
        exact (hinsR _ (hmemPair he).1 (hregOf he)).1)
      (fun q hq => hRw q (hmw q (List.mem_append_left _ (List.mem_append_right _ hq))))
      (fun q hq hn' => have hq' := hmw q (List.mem_append_left _ (List.mem_append_right _ hq))
        ⟨hEw q hq' hn', hLw q hq' hn'⟩)
      (fun a ha => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
        exact hrel _ (hmemPair he).2)
      (fun a ha => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
        exact himk _ (hmas _ (hmemPair he).2))
      (fun q hq yq hyq hn' => hfront q (ecFront_tgt hi hw
        (hmw q (List.mem_append_left _ (List.mem_append_right _ hq))) hn') yq hyq)
    rw [ecc_zip_map, ecc_flatMap_pat (fun p r => ecPieceVals true (tabs.ty p.type) r)] at hP
    -- the stack arguments: the one the `Move` copies (`sp0`) and the stored ones (`sp1`)
    obtain ⟨hsorted, zs, sp0, sp1, hcs, hsp01, hst, hmv0⟩ := ecc_stackOK_inv hstack
    unfold storeArgsOK at hst
    simp only [Bool.and_eq_true, List.all_eq_true] at hst
    obtain ⟨⟨⟨hsOK, hpcS⟩, hsrc⟩, hwfS⟩ := hst
    have hm1 : ∀ {e}, e ∈ sp1 → e ∈ argPairs false (insOf abi) (u.args.extract k (u.args.size - 1)).toList :=
      fun he => by rw [hsp01]; exact List.mem_append_right _ he
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
    have hS := ec_pieces hNC hL hRS false _ _ _ hpcS
      (fun p hp => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hp
        exact hwfS _ he)
      (fun q hq => by
        obtain ⟨z, -, wz, -, hqa, -, hreg⟩ := hpcv q hq
        exact hreg q hqa)
      (fun q hq hn' => by
        obtain ⟨z, -, wz, -, hqa, hcl, -⟩ := hpcv q hq
        exact hcl q hqa hn')
      (fun a ha => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
        exact hrel _ (hmemPair (hm1 he)).2)
      (fun a ha => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
        exact himk _ (hmas _ (hmemPair (hm1 he)).2))
      (fun q hq yq hyq hn' => by
        have := hsrc q hq
        rw [hn', Bool.false_or, Array.contains_iff_mem] at this
        exact hfront q (ecFront_src hi hu this) yq hyq)
    simp only [ecPieceVals_false] at hS
    rw [ecc_zip_map, ecc_flatMap_pat (fun p r => leafVals (tabs.ty p.type) r), List.map_map] at hS
    -- the leading arguments and the memory
    have hsame : ∀ a ∈ u.args, special f g a = false →
        Sem.Refines (rv frS a) (rv T a) := fun a ha hs => by
      obtain ⟨y', hy', hr⟩ := hfront a (ecFront_src hi hu ha) _ (reg_rv (hRu a ha))
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
        (retypeResults tabs (insOf abi)
          ((u.args.extract k (u.args.size - 1)).toList.map (rv frS))).any Val.hasPoison = false →
        outargsOK tabs 0 m (insOf abi) = true →
        ∃ mN D, rv T w.args[w.args.size - 1]! = .mem mN ∧
          Mem.Refines (m.poisonBlock (.outargs 0)) (mN.poisonBlock (.outargs 0)) ∧
          outargsOK tabs 0 mN (insOf abi) = true ∧
          decodeArgs tabs 0 mN (insOf abi) ((w.args.extract k (w.args.size - 1)).toList.map (rv T)) =
            some D ∧
          Sem.RefinesList (retypeResults tabs (insOf abi)
            ((u.args.extract k (u.args.size - 1)).toList.map (rv frS))) D := by
      intro m hm _ hokm
      rw [hm] at hmv
      obtain ⟨M, hMT, hMR⟩ : ∃ M, rv T u.args[u.args.size - 1]! = .mem M ∧ Mem.Refines m M := by
        revert hmv
        generalize rv T u.args[u.args.size - 1]! = yT
        intro hmv
        cases hmv with
        | mem h => exact ⟨_, rfl, h⟩
      -- the memory the stores start from: the call's, or the `Move`'s copy into it
      obtain ⟨M1, hM1, hA1, hP1, hmov⟩ : ∃ M1, rv T (callBase f g u w) = .mem M1 ∧
          (∀ blk, (M1.find? blk).map ecsAttr = (M.find? blk).map ecsAttr) ∧
          M1.poisonBlock (.outargs 0) = M.poisonBlock (.outargs 0) ∧
          ∀ e ∈ sp0, ∃ bs, M.write (ecsSlot e.1.offset.toNat) bs = some M1 ∧
            bs.size = (tabs.ty e.1.type).size ∧
            Sem.Refines (rv frS e.2) (decode bs 0 (tabs.ty e.1.type)) := by
        rcases hmv0 with ⟨hnone, rfl⟩ | ⟨z, p, a, hz, rfl, hmok⟩
        · exact ⟨M, by unfold callBase; rw [hnone]; exact hMT, fun _ => rfl, rfl,
            fun e he => absurd he List.not_mem_nil⟩
        obtain ⟨hzn, mw, hmvw, hmop, hmsz, hm2⟩ := ecc_callMove_spec hz
        obtain ⟨mw', au, hmw', hau, -, hoff, hai, hsh, hauop, hau2, hsrc0, hamem, heqa, hmt, hsn, hss⟩ :=
          ecc_moveOK_spec hmok
        rw [hmvw] at hmw'; cases hmw'
        have hbase : callBase f g u w = z := by unfold callBase; rw [hz]; rfl
        -- the `Move` is a new value of `E`
        have hzEL : E z ∧ L z := by
          have hcz := hcs'
          rw [hbase] at hcz
          by_cases hne : zs = []
          · subst hne
            have he := ecs_storeChain_nil hcz
            have hm : z ∈ w.args := by rw [← he]; exact hmw _ (List.mem_append_right _ (by simp))
            exact ⟨hEw _ hm hzn, hLw _ hm hzn⟩
          · exact ecs_chain_base_E hNC hL _ hcz (htopEL hne) hzn
        obtain ⟨-, mw', y, hmw', hcl, hy, hev⟩ := hNC z hzEL.1
        change g.value? z = some mw' at hmw'
        rw [hmvw] at hmw'; cases hmw'
        obtain ⟨hmid, hLcl⟩ := hL z hzEL.2 mw hmvw
        have hargs := ecs_args_three hmsz
        have hmem3 : ∀ i, i < 3 → mw.args[i]! ∈ mw.args := fun i hi => by
          rw [← Array.mem_toList_iff, hargs]
          match i, hi with
          | 0, _ | 1, _ | 2, _ => simp
        have hty : (Ctx.make tabs g).tys[mw.id]?.getD .other = .mem := by
          rw [hmid, ← shapeOf_eq]; exact hsh
        obtain ⟨d, s, M0, bs, M1, hd, hs, hM0, hrd, hW1, rfl⟩ := ecs_move_val hmop hargs hty hev
        rw [hm2, hMT] at hM0; cases hM0
        -- the destination: the parameter's slot
        have hEq : E mw.args[0]! ∧ L mw.args[0]! := by
          have hn : isNewB f mw.args[0]! = true := by
            unfold spOffOK at hoff; simp only [Bool.and_eq_true] at hoff; exact hoff.1.1.1
          exact ⟨hcl _ (hmem3 0 (by decide)) hn, hLcl _ (hmem3 0 (by decide)) hn⟩
        have ha := ecs_addr hNC hL hoff hEq.1 hEq.2 fun qw hqw hn =>
          hHS _ ⟨z, .inr hz, mw, qw, hmvw, hqw, hn, rfl⟩
        obtain ⟨a0, ha0, hasl⟩ := ha
        rw [rv_of ha0, hasl] at hd; cases hd
        have hrd' : M.read s (tabs.ty p.type).size = some bs := by
          rw [hai] at hrd; simpa using hrd
        -- the source's `Dereference`
        have hpa : (p, a) ∈ argPairs false (insOf abi) (u.args.extract k (u.args.size - 1)).toList := by
          rw [hsp01]; simp
        obtain ⟨haid, ya, hya, heva⟩ :=
          hMA a ⟨by rw [hz]; rfl, hmas _ (hmemPair hpa).2, au, hau, hauop⟩ au hau
        have hargsA := ec_args_two hau2
        have hsrcR : Reg frS au.args[0]! := regs_of_ok heva _ (by rw [← Array.mem_toList_iff, hargsA]; simp)
        have hva := evalValue_term (by rw [hauop]; decide) heva
        have hep : ∀ ty ai ax (args : List Val), evalPure .Dereference ty ai ax args = loadOp ty args :=
          fun _ _ _ _ => rfl
        rw [hauop, GoFV.Proof.Rules.opVal_pure (by decide), hep, hargsA, haid, ← shapeOf_eq,
          hsrc0, hamem] at hva
        simp only [List.map_cons, List.map_nil, hm] at hva
        -- the target's source pointer refines the source's
        have hsm : stackMove f g x = some z := by
          unfold stackMove; rw [hu, hw]; dsimp only; rw [if_pos hcall, hz]
        obtain ⟨ysT, hysT, hrys⟩ := hfront _ (eco_mem_front_move hi hsm hmvw (hmem3 1 (by decide)) hsn) _
          (by rw [← hsrc0]; exact reg_rv hsrcR)
        rw [ecCv_of_not_special hss] at hrys
        rw [rv_of hysT] at hs
        have hP := ecs_move_arg hMR (hinsS _ (hmemPair hpa).1 (hregOf hpa)).1 heqa hmt hrys hs hrd'
        refine ⟨_, by rw [hbase]; exact rv_of hy, fun blk => ecs_find_write hW1 blk,
          ecs_poisonBlock_write hW1, fun e he => ?_⟩
        rw [List.mem_singleton.1 he]
        refine ⟨bs, hW1, ecs_read_size hrd', ?_⟩
        rw [rv_of hya, hva]
        rw [hsrc0] at hP
        exact hP
      -- the stores
      have hat : ∀ s ∈ leafSlots tabs (sp1.map Prod.fst), atom s.2 = true := fun s hs => by
        obtain ⟨p, hp, l, hl, rfl⟩ := ecs_mem_leafSlots hs
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hp
        exact (mem_leaves (hwfS _ he) hl).2
      obtain ⟨Mt, hMt, hW⟩ := ecs_chain hNC hL _ hcs' htopEL hsOK hat
        (fun z hz wz qw hwz hqw hn => hHS _ ⟨z, .inl ⟨zs, hcs, hz⟩, wz, qw, hwz, hqw, hn, rfl⟩) M1 hM1
      have hblk : ∀ e ∈ List.zipWith ecsW (leafSlots tabs (sp1.map Prod.fst))
          (zs.map fun z => rv T (storeVal g z)), e.1.blk = .outargs 0 := fun e he => by
        obtain ⟨a, -, b, rfl⟩ := ecs_mem_zipWith he
        rfl
      have hokM : outargsOK tabs 0 Mt (insOf abi) = true := by
        rw [writeAll_outargsOK hW, show outargsOK tabs 0 M1 (insOf abi) = outargsOK tabs 0 M (insOf abi) by
          unfold outargsOK; simp only [ecs_canWrite_congr hA1], hMR.outargsOK]
        exact hokm
      have hpoi : Mem.Refines (m.poisonBlock (.outargs 0)) (Mt.poisonBlock (.outargs 0)) := by
        rw [writeAll_poison hblk hW, hP1]; exact hMR.poisonBlock _
      -- the slots in order
      have hpw := ecs_slotsSorted_pairwise hsorted
      rw [hsp01, List.map_append, List.pairwise_append] at hpw
      -- the arguments, register and stack
      have hshape : ∀ e ∈ (insOf abi).zip (u.args.extract k (u.args.size - 1)).toList,
          (rv frS e.2).hasTy (shapeOf (typeShapes tabs) f e.2) = true := fun e he => by
        have hreg := reg_rv (hRu _ (hmas _ (List.of_mem_zip he).2))
        have := (hRS _ _ hreg).1
        rwa [← shapeOf_eq] at this
      have hpairs : ∀ e ∈ (insOf abi).zip (u.args.extract k (u.args.size - 1)).toList,
          e.1.regs.isEmpty = true → (rv frS e.2).hasTy (tabs.ty e.1.type) = true := fun e he hr => by
        have hb : e ∈ argPairs false (insOf abi) (u.args.extract k (u.args.size - 1)).toList :=
          List.mem_filter.2 ⟨he, by simp [hr]⟩
        have heq : eqE (shapeOf (typeShapes tabs) f e.2) (tabs.ty e.1.type) = true := by
          rw [hsp01] at hb
          rcases List.mem_append.1 hb with h0 | h1
          · rcases hmv0 with ⟨-, rfl⟩ | ⟨z, p, a, -, rfl, hmok⟩
            · exact absurd h0 List.not_mem_nil
            · rw [List.mem_singleton.1 h0]
              obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, heqa, -⟩ := ecc_moveOK_spec hmok
              exact heqa
          · have := ecc_piecesOK_eqE hpcS e (by rw [ecc_zip_fst_snd]; exact h1)
            simpa using this
        rw [← eqE_hasTy heq]; exact hshape e he
      have hpairsR : ∀ e ∈ (insOf abi).zip (u.args.extract k (u.args.size - 1)).toList,
          e.1.regs.isEmpty = false → (rv frS e.2).hasTy (tabs.ty e.1.type) = true ∨
            tabs.ty e.1.type = .int .w64 ∧ ∃ e', (rv frS e.2).hasTy (.ptr e') = true := fun e he hr => by
        have hb : e ∈ argPairs true (insOf abi) (u.args.extract k (u.args.size - 1)).toList :=
          List.mem_filter.2 ⟨he, by simp [hr]⟩
        rcases ecc_piecesOK_eqE hpc e (by rw [ecc_zip_fst_snd]; exact hb) with heq | ⟨-, hc⟩
        · exact .inl (by rw [← eqE_hasTy heq]; exact hshape e he)
        · obtain ⟨⟨e', hs⟩, ht⟩ := ec_castOK hc
          exact .inr ⟨ht, e', by rw [← hs]; exact hshape e he⟩
      have hlenL : (insOf abi).length = (u.args.extract k (u.args.size - 1)).toList.length := hlen
      have hstk := ecs_stack_params (M := Mt) (sp1.map fun e => (e.1, rv frS e.2)) _ hS
        (by
          rw [List.map_map]
          exact ecs_reads (ecs_leafSlots_pairwise (fun p hp => by
              obtain ⟨e, he, rfl⟩ := List.mem_map.1 hp
              exact hwfS _ he)
            hpw.2.1) (ecs_storesOK_bounds hsOK) hW)
        (by
          rw [List.map_map]
          exact fun s hs => (ecs_storesOK_bounds hsOK s hs).2)
        (fun xe hxe => by
          obtain ⟨e, he, rfl⟩ := List.mem_map.1 hxe
          have hmz := (List.mem_filter.1 (hm1 he))
          have hr : e.1.regs.isEmpty = true := by simpa using hmz.2
          have hwe := hwfS _ he
          have hoff := (hinsS _ (hmemPair (hm1 he)).1 hr).2
          refine ⟨hwe, hpairs e hmz.1 hr, hoff, ?_⟩
          have := List.all_eq_true.1 hokM e.1 (hmemPair (hm1 he)).1
          rw [hr, Bool.not_true, Bool.false_or, ecs_ofInt hoff] at this
          exact this)
      obtain ⟨D, hD, hGD⟩ := ecc_decodeArgs_mixed (act := 0) (M := Mt)
        (((insOf abi).zip (u.args.extract k (u.args.size - 1)).toList).map fun e => (e.1, rv frS e.2))
        ((w.args.extract k (w.args.size - 1)).toList.map (rv T))
        (fun xe hxe hr => by
          obtain ⟨e, he, rfl⟩ := List.mem_map.1 hxe
          dsimp only at hr ⊢
          obtain ⟨h1, h2⟩ := hinsR _ (List.of_mem_zip he).1 hr
          exact ⟨h1, h2, hpairsR e he hr⟩)
        (fun xe hxe hr => by
          have hmf : xe ∈ (((insOf abi).zip (u.args.extract k (u.args.size - 1)).toList).map
              fun e => (e.1, rv frS e.2)).filter (fun x => !x.1.regs.isEmpty == false) :=
            List.mem_filter.2 ⟨hxe, by simp [hr]⟩
          rw [ecc_argPairs_map, hsp01, List.map_append, List.mem_append] at hmf
          obtain ⟨e, he, rfl⟩ := List.mem_map.1 hxe
          rw [Val.retype_of_hasTy (hpairs e he hr)]
          have hoff := (hinsS _ (List.of_mem_zip he).1 hr).2
          rw [ecs_ofInt hoff]
          rcases hmf with h0 | h1
          · obtain ⟨e0, he0, hee⟩ := List.mem_map.1 h0
            obtain ⟨bs, hW1, hsz, hv⟩ := hmov e0 he0
            simp only [Prod.mk.injEq] at hee
            obtain ⟨hp0, hv0⟩ := hee
            rw [hp0] at hW1 hsz hv
            rw [hv0] at hv
            refine ⟨bs, ?_, hv⟩
            rw [← hsz]
            refine ecs_move_read hW1 hW fun s hs => ⟨?_, (ecs_storesOK_bounds hsOK s hs).2⟩
            obtain ⟨q, hq, l, -, rfl⟩ := ecs_mem_leafSlots hs
            have h2 := hpw.2.2 e0.1 (List.mem_map.2 ⟨e0, he0, rfl⟩) q hq
            rw [hp0] at h2
            dsimp only
            rw [hsz]
            omega
          · exact hstk _ h1)
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
      rw [hfst, hsnd] at hGD
      rw [hfst] at hD
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
and the `Move` the source defines (`ecStackSP`), and the source the `Dereference` the `Move`
copies (`ecMoveArg`). -/
theorem obl_call {tabs : Tables} {f g : Func} {x : ID} {u w : Value} {HS HT : ID → Prop}
    (hu : f.value? x = some u) (hw : g.value? x = some w) (hcall : (callOpMap u.op).isSome = true)
    (hok : callOK tabs (typeShapes tabs) f g u w = true)
    (huid : u.id = x) (L : ID → Prop) (hLx : L x)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true → L a)
    (hH : ∀ a ∈ u.args, EcoImkHeld tabs f g HS HT a) (hSP : ∀ a, ecStackSP f g u w a → HT a)
    (hMA : ∀ a, ecMoveArg f g u w a → HS a) :
    Obl tabs f g (ecCv tabs f g) (isNewB f) (ecFront f g x) HS HT x :=
  obl_of_imk (obl_call_imk hu hw hcall hok huid L hLx hL) hu hH hSP hMA

theorem ecc_bind_def {R : Res Val} {F : Val → Val}
    (h : (∃ y, R.bind (fun r => .ok (F r)) = .ok y) ∨ ∃ e m, R.bind (fun r => .ok (F r)) = .panic e m) :
    (∃ y, R = .ok y) ∨ ∃ e m, R = .panic e m := by
  cases R with
  | ok y => exact .inl ⟨y, rfl⟩
  | panic e m => exact .inr ⟨e, m, rfl⟩
  | stuck msg => rcases h with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h

/-! ## `poison` survives retyping -/

theorem ecc_hasPoison_retypePtr {p : Val} (h : p.hasPoison = true) : p.retypePtr.hasPoison = true := by
  cases p <;> simp_all [Val.retypePtr, Val.hasPoison]

theorem ecc_hasPoison_retypeI64 {p : Val} (h : p.hasPoison = true) : p.retypeI64.hasPoison = true := by
  cases p <;> simp_all [Val.retypeI64, Val.hasPoison]

theorem ecc_hasPoison_retype_str (vs : List Val) (h : (Val.agg vs).hasPoison = true) :
    ((Val.agg vs).retype .str).hasPoison = true := by
  match vs, h with
  | [p, l], h =>
    simp only [Val.retype, Val.ofStr]
    split
    · simp only [Val.hasPoison, Val.anyPoison, Bool.or_false, Bool.or_eq_true] at h ⊢
      rcases h with h | h
      · exact .inl (ecc_hasPoison_retypePtr h)
      · exact .inr (ecc_hasPoison_retypeI64 h)
    · rfl
  | [], _ | [_], _ | _ :: _ :: _ :: _, _ => simp [Val.retype, Val.hasPoison]

theorem ecc_hasPoison_retype_slice (e : Option Nat) (vs : List Val) (h : (Val.agg vs).hasPoison = true) :
    ((Val.agg vs).retype (.slice e)).hasPoison = true := by
  match vs, h with
  | [p, l, c], h =>
    simp only [Val.retype, Val.ofSlice]
    split
    · simp only [Val.hasPoison, Val.anyPoison, Bool.or_false, Bool.or_eq_true] at h ⊢
      rcases h with h | h | h
      · exact .inl (ecc_hasPoison_retypePtr h)
      · exact .inr (.inl (ecc_hasPoison_retypeI64 h))
      · exact .inr (.inr (ecc_hasPoison_retypeI64 h))
    · rfl
  | [], _ | [_], _ | [_, _], _ | _ :: _ :: _ :: _ :: _, _ => simp [Val.retype, Val.hasPoison]

mutual
/-- Retyping keeps a `poison` inside a value. -/
theorem ecc_hasPoison_retype : (t : Ty) → (v : Val) → v.hasPoison = true → (v.retype t).hasPoison = true
  | t, .poison, _ => by cases t <;> rfl
  | _, .int _ _, h | _, .bool _, h | _, .mem _, h | _, .ptr _, h | _, .empty, h => by
    simp [Val.hasPoison] at h
  | t, .tuple vs, h => by
    cases t with
    | tuple ts =>
      simp only [Val.retype]
      split
      · rename_i vs' hr
        simp only [Val.hasPoison] at h ⊢
        exact ecc_anyPoison_retypePre ts vs h hr
      · rfl
    | _ => simp [Val.retype, Val.hasPoison]
  | t, .agg vs, h => by
    cases t with
    | agg fs n =>
      simp only [Val.retype]
      split
      · rename_i vs' hr
        simp only [Val.hasPoison] at h ⊢
        exact ecc_anyPoison_retypeFields fs vs h hr
      · rfl
    | str => exact ecc_hasPoison_retype_str vs h
    | slice e => exact ecc_hasPoison_retype_slice e vs h
    | _ => simp [Val.retype, Val.hasPoison]
  | t, .blob bs, h => by
    cases t with
    | blob n => simp only [Val.retype]; split <;> simp_all [Val.hasPoison]
    | _ => simp [Val.retype, Val.hasPoison]
theorem ecc_anyPoison_retypePre : (ts : List Ty) → (vs : List Val) → Val.anyPoison vs = true →
    ∀ {vs'}, Val.retypePre ts vs = some vs' → Val.anyPoison vs' = true
  | [], vs, h, _, hr => by simp only [Val.retypePre, Option.some.injEq] at hr; subst hr; exact h
  | t :: ts, v :: vs, h, _, hr => by
    simp only [Val.retypePre] at hr
    cases hr' : Val.retypePre ts vs with
    | none => rw [hr'] at hr; cases hr
    | some ws =>
      rw [hr'] at hr
      simp only [Option.map_some, Option.some.injEq] at hr
      subst hr
      simp only [Val.anyPoison, Bool.or_eq_true] at h ⊢
      rcases h with h | h
      · exact .inl (ecc_hasPoison_retype t v h)
      · exact .inr (ecc_anyPoison_retypePre ts vs h hr')
  | _ :: _, [], h, _, _ => by simp [Val.anyPoison] at h
theorem ecc_anyPoison_retypeFields : (fs : List (Nat × Ty)) → (vs : List Val) → Val.anyPoison vs = true →
    ∀ {vs'}, Val.retypeFields fs vs = some vs' → Val.anyPoison vs' = true
  | [], [], h, _, _ => by simp [Val.anyPoison] at h
  | (_, t) :: fs, v :: vs, h, _, hr => by
    simp only [Val.retypeFields] at hr
    cases hr' : Val.retypeFields fs vs with
    | none => rw [hr'] at hr; cases hr
    | some ws =>
      rw [hr'] at hr
      simp only [Option.map_some, Option.some.injEq] at hr
      subst hr
      simp only [Val.anyPoison, Bool.or_eq_true] at h ⊢
      rcases h with h | h
      · exact .inl (ecc_hasPoison_retype t v h)
      · exact .inr (ecc_anyPoison_retypeFields fs vs h hr')
  | [], _ :: _, _, _, hr => by simp [Val.retypeFields] at hr
  | _ :: _, [], _, _, hr => by simp [Val.retypeFields] at hr
end

/-- Retyping arguments keeps a `poison` among them. -/
theorem ecc_anyPoison_retypeResults (tabs : Tables) :
    ∀ (ps : List ABIParam) {G : List Val}, G.any Val.hasPoison = true →
      (retypeResults tabs ps G).any Val.hasPoison = true
  | [], _, h => h
  | _ :: _, [], h => h
  | p :: ps, v :: G, h => by
    simp only [retypeResults, List.any_cons, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact .inl (ecc_hasPoison_retype _ v h)
    · exact .inr (ecc_anyPoison_retypeResults tabs ps h)

/-- A source call that completes or panics had Go-typed arguments without `poison`. -/
theorem ecc_callOp_noPoison {env : Env} {ctx : Ctx} {u : Value} {abi : CallABI}
    (hpre : (u.op == .StaticCall || u.op == .ClosureCall || u.op == .InterCall) = false)
    (habi : callABI? ctx.tabs u.aux = some abi) {argv G : List Val} {mv : Val}
    (hct : (callTarget ctx u argv).2.2 = G ++ [mv])
    (h : (∃ y, callOp env ctx u argv = .ok y) ∨ ∃ e m, callOp env ctx u argv = .panic e m) :
    G.any Val.hasPoison = false := by
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
      dsimp only at h
      simp only [hpre, Bool.false_eq_true, ↓reduceIte, Option.map_some, Option.getD_some] at h
      dsimp only [pure, Res.bind] at h
      rw [List.dropLast_concat] at h
      cases hp : G.any Val.hasPoison with
      | false => rfl
      | true =>
        exfalso
        rw [if_pos (by simp [ecc_anyPoison_retypeResults _ _ hp])] at h
        exact hns _ ⟨_, rfl⟩ h
    | _ => exact absurd h (hns _ ⟨_, rfl⟩)

/-- The source operand of `Move` `z`. -/
def ecMoveSrc (g : Func) (z : ID) : ID := ((g.value? z).map (·.args[1]!)).getD z

theorem ecMoveSrc_of {g : Func} {z : ID} {mw : Value} (h : g.value? z = some mw) :
    ecMoveSrc g z = mw.args[1]! := by
  unfold ecMoveSrc; rw [h]; rfl

theorem ecs_moveTy_eqE {s t : Ty} (h : eqE s t = true) (ht : moveTy t = true) : moveTy s = true := by
  have he : erase s = erase t := Ty.eq_of_beq h
  cases t <;> cases s <;> simp_all [erase, moveTy]

/-- **The obligation of the `Move` of a wide stack argument** `z` of call `x` (`NewObl`, anchored
at `x`): once the source has reached the call, the `Dereference` the `Move` copies read its bytes
(the call's arguments have no `poison`), so does the target's refining memory at the same
pointer, and the parameter's slot is writable (`outargsOK`). -/
theorem ecc_moveObl {tabs : Tables} {f g : Func} {x z : ID} {u w : Value} {HS HT : ID → Prop}
    (hu : f.value? x = some u) (hw : g.value? x = some w) (hcall : (callOpMap u.op).isSome = true)
    (hok : callOK tabs (typeShapes tabs) f g u w = true) (hz : callMove f g u w = some z)
    (L : ID → Prop)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true → L a)
    (hLz : L z)
    (hsp : ∀ mw qw, g.value? z = some mw → g.value? mw.args[0]! = some qw →
      isNewB f qw.args[0]! = false → HT qw.args[0]!)
    (hMA : ∀ a, ecMoveArg f g u w a → HS a) :
    NewObl tabs f g (ecCv tabs f g) (isNewB f) [u.args[u.args.size - 1]!, ecMoveSrc g z] HS HT x z := by
  intro mw hmw env G T _ E hNC hEw hRw hfront hheldT hheldS hreach _
  unfold callOK at hok
  split at hok
  · next op k abi hmap habi =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true', ge_iff_le,
      List.all_eq_true] at hok
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hkn⟩, -⟩, hinsOK⟩, -⟩, -⟩, -⟩, hstack⟩,
      -⟩, hmns⟩, -⟩, -⟩, -⟩ := hok
    obtain ⟨hopu, hpre, -, -⟩ := ecc_callOpMap hmap
    have hopu' : u.op = .StaticLECall ∨ u.op = .ClosureLECall ∨ u.op = .InterLECall ∨
        u.op = .StaticCall ∨ u.op = .ClosureCall ∨ u.op = .InterCall := by
      rcases hopu with h | h | h <;> simp [h]
    have hsu := ecc_args_split u.args k hkn
    -- the `Move` and the parameter it copies
    obtain ⟨-, zs, sp0, sp1, -, hsp01, -, hmv0⟩ := ecc_stackOK_inv hstack
    obtain ⟨p, a, rfl, hmok⟩ : ∃ p a, sp0 = [(p, a)] ∧ moveOK tabs (typeShapes tabs) f g u p a z = true := by
      rcases hmv0 with ⟨hn, -⟩ | ⟨z', p, a, hz', h0, hm⟩
      · rw [hz] at hn; cases hn
      · rw [hz] at hz'; cases hz'; exact ⟨p, a, h0, hm⟩
    obtain ⟨hzn, mw', hmw', hmop, hmsz, hm2⟩ := ecc_callMove_spec hz
    rw [hmw] at hmw'; cases hmw'
    obtain ⟨mw', au, hmw', hau, -, hoff, hai, hsh, hauop, hau2, hsrc0, hamem, heqa, hmt, hsn, hss⟩ :=
      ecc_moveOK_spec hmok
    rw [hmw] at hmw'; cases hmw'
    have hpa : (p, a) ∈ argPairs false (insOf abi) (u.args.extract k (u.args.size - 1)).toList := by
      rw [hsp01]; simp
    have hpe := List.mem_filter.1 hpa
    have hpin : p ∈ insOf abi := (List.of_mem_zip hpe.1).1
    have hain : a ∈ (u.args.extract k (u.args.size - 1)).toList := (List.of_mem_zip hpe.1).2
    have hr : p.regs.isEmpty = true := by simpa using hpe.2
    have hins := List.all_eq_true.1 hinsOK p hpin
    rw [hr, if_pos rfl, Bool.and_eq_true] at hins
    have hoff0 : 0 ≤ p.offset := of_decide_eq_true hins.2
    -- the source reached the call: its memory's stack-argument slots are writable, its arguments
    -- have no `poison`
    have hrc := hreach u hu
    have hne : ∀ msg, evalValue env (Ctx.make tabs f) G u ≠ .stuck msg := fun msg h => by
      rw [h] at hrc; rcases hrc with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h
    have hregG : ∀ a ∈ u.args, Reg G a := evalValue_args_def hne
    rw [evalValue_of_regs hregG, ecc_evalOp_call hopu', hsu, List.map_append, List.map_append,
      List.append_assoc, List.map_cons, List.map_nil] at hrc
    have hlk : ((u.args.extract 0 k).toList.map (rv G)).length = k := by
      simp only [List.length_map, Array.length_toList, Array.size_extract]; omega
    obtain ⟨m, hm, hokm⟩ : ∃ m, rv G u.args[u.args.size - 1]! = .mem m ∧
        outargsOK tabs 0 m (insOf abi) = true :=
      ecc_callOp_outargs hpre habi (ecc_callTarget_rest hmap hlk) (ecc_bind_def hrc)
    have hnp := ecc_callOp_noPoison hpre habi (ecc_callTarget_rest hmap hlk) (ecc_bind_def hrc)
    have hnpa : (rv G a).hasPoison = false := by
      cases hh : (rv G a).hasPoison with
      | false => rfl
      | true =>
        have : ((u.args.extract k (u.args.size - 1)).toList.map (rv G)).any Val.hasPoison = true :=
          List.any_eq_true.2 ⟨_, List.mem_map.2 ⟨a, hain, rfl⟩, hh⟩
        rw [hnp] at this; cases this
    -- the `Dereference` read its bytes
    have hamu : a ∈ u.args := by
      rw [← Array.mem_toList_iff, hsu]; exact List.mem_append_left _ (List.mem_append_right _ hain)
    obtain ⟨haid, ya, hya, heva⟩ := hheldS a (hMA a ⟨by rw [hz]; rfl, hamu, au, hau, hauop⟩) au hau
    have hargsA := ec_args_two hau2
    have hsrcR : Reg G au.args[0]! := regs_of_ok heva _ (by rw [← Array.mem_toList_iff, hargsA]; simp)
    have hva := evalValue_term (by rw [hauop]; decide) heva
    have hep : ∀ ty ai ax (args : List Val), evalPure .Dereference ty ai ax args = loadOp ty args :=
      fun _ _ _ _ => rfl
    rw [hauop, GoFV.Proof.Rules.opVal_pure (by decide), hep, hargsA, haid, ← shapeOf_eq,
      hsrc0, hamem] at hva
    simp only [List.map_cons, List.map_nil, hm] at hva
    rw [rv_of hya, hva] at hnpa
    obtain ⟨p0, bs0, hP0, hrd0⟩ := ecs_deref_read (ecs_moveTy_eqE heqa hmt) hnpa
    rw [ecT_eqE_size heqa] at hrd0
    -- the target's operands
    have hm0 : u.args[u.args.size - 1]! ∈ u.args := by rw [← Array.mem_toList_iff, hsu]; simp
    obtain ⟨yM, hyM, hryM⟩ := hfront _ List.mem_cons_self (.mem m)
      (by rw [← hm]; exact reg_rv (hregG _ hm0))
    rw [ecCv_of_not_special hmns] at hryM
    obtain ⟨M, rfl, hMR⟩ : ∃ M, yM = .mem M ∧ Mem.Refines m M := by
      cases hryM with
      | mem h => exact ⟨_, rfl, h⟩
    have hsrcG : G.regs[ecMoveSrc g z]? = some (some (rv G mw.args[1]!)) := by
      have := reg_rv hsrcR
      rw [hsrc0] at this
      rw [ecMoveSrc_of hmw]
      exact this
    obtain ⟨yS, hyS, hryS⟩ := hfront _ (List.mem_cons_of_mem _ List.mem_cons_self) _ hsrcG
    have hssz : special f g (ecMoveSrc g z) = false := by rw [ecMoveSrc_of hmw]; exact hss
    rw [ecCv_of_not_special hssz] at hryS
    have hyS' : yS.asPtrWord = some p0 := hryS.asPtrWord hP0
    obtain ⟨bs, hrd, -⟩ := hMR.read hrd0
    -- the destination
    obtain ⟨hmid, hLcl⟩ := hL z hLz mw hmw
    have hargs := ecs_args_three hmsz
    have hmem3 : ∀ i, i < 3 → mw.args[i]! ∈ mw.args := fun i hi => by
      rw [← Array.mem_toList_iff, hargs]
      match i, hi with
      | 0, _ | 1, _ | 2, _ => simp
    have hEq : E mw.args[0]! ∧ L mw.args[0]! := by
      have hn : isNewB f mw.args[0]! = true := by
        unfold spOffOK at hoff; simp only [Bool.and_eq_true] at hoff; exact hoff.1.1.1
      exact ⟨hEw _ (hmem3 0 (by decide)) hn, hLcl _ (hmem3 0 (by decide)) hn⟩
    have ha := ecs_addr hNC hL hoff hEq.1 hEq.2 fun qw hqw hn => hheldT _ (hsp mw qw hmw hqw hn)
    have hokM : outargsOK tabs 0 M (insOf abi) = true := by rw [hMR.outargsOK]; exact hokm
    have hcw := List.all_eq_true.1 hokM p hpin
    rw [hr, Bool.not_true, Bool.false_or, ecs_ofInt hoff0] at hcw
    rw [← ecs_read_size hrd] at hcw
    obtain ⟨M1, hW⟩ := ecs_write_of_canWrite hcw
    have hty : (Ctx.make tabs g).tys[mw.id]?.getD .other = .mem := by
      rw [hmid, ← shapeOf_eq]; exact hsh
    have hsrcT : (rv T mw.args[1]!).asPtrWord = some p0 := by
      have := rv_of hyS
      rw [ecMoveSrc_of hmw] at this; rw [this]; exact hyS'
    have hrd' : M.read p0 mw.auxInt.toInt.toNat = some bs := by rw [hai]; simpa using hrd
    obtain ⟨a0, ha0, hasl⟩ := ha
    exact ⟨_, ecs_move_eval hmop hRw hargs hty (by rw [rv_of ha0]; exact hasl) hsrcT (by rw [hm2]; exact rv_of hyM) hrd' hW⟩
  · cases hok

/-- **The obligation of a stack-argument store** `z` of call `x` (`NewObl`, anchored at `x`): once
the source has reached the call, its memory's stack-argument slots are writable (`outargsOK`), so
are the target's (a refinement of it, then the stores below `z`), and `z`'s write succeeds. -/
theorem ecc_storeObl {tabs : Tables} {f g : Func} {x z : ID} {u w : Value} {HS HT : ID → Prop}
    (hu : f.value? x = some u) (hw : g.value? x = some w) (hcall : (callOpMap u.op).isSome = true)
    (hok : callOK tabs (typeShapes tabs) f g u w = true)
    {zs : List ID} (hzs : callStores f g u w = some zs) (hz : z ∈ zs) (L : ID → Prop)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true → L a)
    (hLz : L z)
    (hsp : ∀ wz qw, g.value? z = some wz → g.value? wz.args[0]! = some qw →
      isNewB f qw.args[0]! = false → HT qw.args[0]!) :
    NewObl tabs f g (ecCv tabs f g) (isNewB f) [u.args[u.args.size - 1]!] HS HT x z := by
  intro wz hwz env G T _ E hNC hEw hRw hfront hheldT _ hreach _
  unfold callOK at hok
  split at hok
  · next op k abi hmap habi =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true', ge_iff_le,
      List.all_eq_true] at hok
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hkn⟩, -⟩, hinsOK⟩, -⟩, -⟩, -⟩, hstack⟩,
      -⟩, hmns⟩, -⟩, -⟩, -⟩ := hok
    obtain ⟨hopu, hpre, -, -⟩ := ecc_callOpMap hmap
    have hopu' : u.op = .StaticLECall ∨ u.op = .ClosureLECall ∨ u.op = .InterLECall ∨
        u.op = .StaticCall ∨ u.op = .ClosureCall ∨ u.op = .InterCall := by
      rcases hopu with h | h | h <;> simp [h]
    have hsu := ecc_args_split u.args k hkn
    -- the source reached the call: its memory's stack-argument slots are writable
    have hr := hreach u hu
    have hne : ∀ msg, evalValue env (Ctx.make tabs f) G u ≠ .stuck msg := fun msg h => by
      rw [h] at hr; rcases hr with ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h
    have hregG : ∀ a ∈ u.args, Reg G a := evalValue_args_def hne
    rw [evalValue_of_regs hregG, ecc_evalOp_call hopu', hsu, List.map_append, List.map_append,
      List.append_assoc, List.map_cons, List.map_nil] at hr
    have hlk : ((u.args.extract 0 k).toList.map (rv G)).length = k := by
      simp only [List.length_map, Array.length_toList, Array.size_extract]; omega
    obtain ⟨m, hm, hokm⟩ : ∃ m, rv G u.args[u.args.size - 1]! = .mem m ∧
        outargsOK tabs 0 m (insOf abi) = true := by
      -- `have` first: elaborating against the expected type unfolded `outargsOK` in a failed
      -- unification (`ctx.act` vs `0`) for ~5 s before succeeding (#1)
      have h := ecc_callOp_outargs hpre habi (ecc_callTarget_rest hmap hlk) (ecc_bind_def hr)
      exact h
    have hm0 : u.args[u.args.size - 1]! ∈ u.args := by rw [← Array.mem_toList_iff, hsu]; simp
    obtain ⟨y', hy', hry⟩ := hfront _ List.mem_cons_self (.mem m)
      (by rw [← hm]; exact reg_rv (hregG _ hm0))
    rw [ecCv_of_not_special hmns] at hry
    obtain ⟨M, rfl, hMR⟩ : ∃ M, y' = .mem M ∧ Mem.Refines m M := by
      cases hry with
      | mem h => exact ⟨_, rfl, h⟩
    have hokM : outargsOK tabs 0 M (insOf abi) = true := by rw [hMR.outargsOK]; exact hokm
    -- the stores below `z`
    obtain ⟨-, zs0, sp0, sp1, hzs0, hsp01, hst, hmv0⟩ := ecc_stackOK_inv hstack
    rw [hzs] at hzs0; cases hzs0
    unfold storeArgsOK at hst
    simp only [Bool.and_eq_true, List.all_eq_true] at hst
    obtain ⟨⟨⟨hsOK, -⟩, -⟩, hwfS⟩ := hst
    have hcs' := hzs
    unfold callStores at hcs'
    obtain ⟨wz', n', zs', hwz', hnz, hop, hsz, hc, rest, hsplit⟩ := ecs_chain_mem hcs' hz
    rw [hwz] at hwz'; cases hwz'
    have hss := hsOK
    rw [hsplit] at hss
    obtain ⟨s12, s3, hs123, h12, -⟩ := ecs_storesOK_append hss
    obtain ⟨s1, s2, rfl, h1, h2⟩ := ecs_storesOK_append h12
    obtain ⟨s, rfl⟩ : ∃ s, s2 = [s] := by
      have := ecs_storesOK_length h2
      match s2, this with
      | [s], _ => exact ⟨s, rfl⟩
    obtain ⟨wz', hwz', haux, hoff, hsh⟩ := ecs_storesOK_one h2
    rw [hwz] at hwz'; cases hwz'
    obtain ⟨hwid, hLcl⟩ := hL z hLz wz hwz
    have hargs := ecs_args_three hsz
    have hmem : ∀ i, i < 3 → wz.args[i]! ∈ wz.args := fun i hi => by
      rw [← Array.mem_toList_iff, hargs]
      match i, hi with
      | 0, _ | 1, _ | 2, _ => simp
    have hEL : zs' ≠ [] → E wz.args[2]! ∧ L wz.args[2]! := fun hne => by
      have hn := ecs_storeChain_new hc hne
      exact ⟨hEw _ (hmem 2 (by decide)) hn, hLcl _ (hmem 2 (by decide)) hn⟩
    -- the memory the stores start from: the call's, or the `Move`'s copy into it
    obtain ⟨Mb0, hMb0, hA0⟩ : ∃ Mb0, rv T (callBase f g u w) = .mem Mb0 ∧
        ∀ blk, (Mb0.find? blk).map ecsAttr = (M.find? blk).map ecsAttr := by
      cases hmv : callMove f g u w with
      | none => exact ⟨M, by unfold callBase; rw [hmv]; exact rv_of hy', fun _ => rfl⟩
      | some z0 =>
        obtain ⟨hzn, mw, hmvw, hmop, hmsz, hm2⟩ := ecc_callMove_spec hmv
        have hmok : ∃ p a, moveOK tabs (typeShapes tabs) f g u p a z0 = true := by
          rcases hmv0 with ⟨hn, -⟩ | ⟨z', p, a, hz', -, hm⟩
          · rw [hmv] at hn; cases hn
          · rw [hmv] at hz'; cases hz'; exact ⟨p, a, hm⟩
        obtain ⟨p, a, hmok⟩ := hmok
        obtain ⟨mw', -, hmw', -, -, -, -, hsh, -⟩ := ecc_moveOK_spec hmok
        rw [hmvw] at hmw'; cases hmw'
        have hbase : callBase f g u w = z0 := by unfold callBase; rw [hmv]; rfl
        have hc0 := hc
        rw [hbase] at hc0
        have hz0EL : E z0 ∧ L z0 := by
          by_cases hne : zs' = []
          · subst hne
            have he := ecs_storeChain_nil hc0
            rw [← he]
            rw [← he] at hzn
            exact ⟨hEw _ (hmem 2 (by decide)) hzn, hLcl _ (hmem 2 (by decide)) hzn⟩
          · exact ecs_chain_base_E hNC hL _ hc0 (hEL hne) hzn
        obtain ⟨-, mw', y0, hmw', -, hy0, hev0⟩ := hNC z0 hz0EL.1
        change g.value? z0 = some mw' at hmw'
        rw [hmvw] at hmw'; cases hmw'
        have hmid := (hL z0 hz0EL.2 mw hmvw).1
        have hty0 : (Ctx.make tabs g).tys[mw.id]?.getD .other = .mem := by
          rw [hmid, ← shapeOf_eq]; exact hsh
        obtain ⟨d0, s0, M0, bs0, M1, -, -, hM0, -, hW1, rfl⟩ :=
          ecs_move_val hmop (ecs_args_three hmsz) hty0 hev0
        rw [hm2, rv_of hy'] at hM0; cases hM0
        exact ⟨M1, by rw [hbase]; exact rv_of hy0, fun blk => ecs_find_write hW1 blk⟩
    obtain ⟨Mb, hMb, hA⟩ := ecs_chain_attr hNC hL n' hc hEL h1 Mb0 hMb0
    -- `z`'s slot is writable
    have hsm : s ∈ leafSlots tabs (sp1.map Prod.fst) := by
      rw [hs123]; simp
    have hsb := ecs_storesOK_bounds hsOK s hsm
    obtain ⟨p, hp, l, hl, rfl⟩ := ecs_mem_leafSlots hsm
    obtain ⟨e, he1, rfl⟩ := List.mem_map.1 hp
    have he : e ∈ argPairs false (insOf abi) (u.args.extract k (u.args.size - 1)).toList := by
      rw [hsp01]; exact List.mem_append_right _ he1
    have hpe := List.mem_filter.1 he
    have hpin : e.1 ∈ insOf abi := (List.of_mem_zip hpe.1).1
    have hr : e.1.regs.isEmpty = true := by simpa using hpe.2
    have hins := List.all_eq_true.1 hinsOK e.1 hpin
    rw [hr, if_pos rfl, Bool.and_eq_true] at hins
    have hoff0 : 0 ≤ e.1.offset := of_decide_eq_true hins.2
    have hcw := List.all_eq_true.1 hokM e.1 hpin
    rw [hr, Bool.not_true, Bool.false_or, ecs_ofInt hoff0] at hcw
    have hl' := mem_leaves (hwfS e he1) hl
    have hcw' := ecs_canWrite_sub (k := l.1) (l := l.2.size) hl'.1 hcw (by dsimp only at hsb; omega)
    rw [show e.1.offset.toNat + l.1 = (e.1.offset + (l.1 : Int)).toNat by omega,
      ← ecs_canWrite_congr hA0, ← ecs_canWrite_congr hA] at hcw'
    -- `z`'s address and write
    have hq : E wz.args[0]! ∧ L wz.args[0]! := by
      have hn : isNewB f wz.args[0]! = true := by
        unfold spOffOK at hoff; simp only [Bool.and_eq_true] at hoff; exact hoff.1.1.1
      exact ⟨hEw _ (hmem 0 (by decide)) hn, hLcl _ (hmem 0 (by decide)) hn⟩
    have ha := ecs_addr hNC hL hoff hq.1 hq.2 fun qw hqw hn => hheldT _ (hsp wz qw hwz hqw hn)
    have hsz' : (encode (auxTy tabs wz.aux) (rv T wz.args[1]!)).size = l.2.size := by
      rw [ecs_encode_eqE hl'.2 haux, GoFV.SSA.Sem.encode_size]
    obtain ⟨M1, hW⟩ := ecs_write_of_canWrite (by rw [hsz']; exact hcw')
    have hty : (Ctx.make tabs g).tys[wz.id]?.getD .other = .mem := by
      rw [hwid, ← shapeOf_eq]; exact hsh
    obtain ⟨a0, ha0, hasl⟩ := ha
    exact ⟨_, ecs_store_eval hop hRw hargs hty (by rw [rv_of ha0]; exact hasl) hMb hW⟩
  · cases hok

end GoFV.Proof.EC

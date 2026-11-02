import GoFV.Proof.Pass.ECRel
import GoFV.Opt.ExpandCallsCheck

/-!
# The conversion of `expand calls` (issue #28)

The parameters of `CvRel` for `expand calls` (`GoFV.Opt.ECCheck.ecCheck`): the conversion `ecCv`
(identity, except for calls and `MakeResult`s, whose tuple of Go-typed results becomes the
register pieces of the register-assigned results, `convTuple`/`regLeafVals`, at the shape of
the target's register types (a call's stack-assigned result stays in the call's memory, in both
forms; a function's stack-assigned result is written into its frame slot, `convRes`/`resMem`),
and for the values the pass invalidated, which become `poison`), the new values (`isNewB`: IDs the
source does not define), the source values a value's obligation reads (`ecFront`: its arguments
in the source and its non-new arguments in the target) and the relation of `Ret` outcomes
(`ecRR`: the target returns the register pieces of the source's results, at register shapes, and
a memory refining the source's with the stack-assigned results in their frame slots).
-/

namespace GoFV.Proof.EC

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.ECCheck GoFV.Proof.ABI GoFV.Proof.Order GoFV.Proof.AtomSim

/-- The register pieces of result `v` of parameter `p`: none for a stack-assigned one. -/
def regLeafVals (tabs : Tables) (p : ABIParam) (v : Val) : List Val :=
  if p.regs.isEmpty then [] else leafVals (tabs.ty p.type) v

theorem regLeafVals_reg {tabs : Tables} {p : ABIParam} (h : p.regs.isEmpty = false) (v : Val) :
    regLeafVals tabs p v = leafVals (tabs.ty p.type) v := by
  simp only [regLeafVals, h, Bool.false_eq_true, ite_false]

theorem regLeafVals_stack {tabs : Tables} {p : ABIParam} (h : p.regs.isEmpty = true) (v : Val) :
    regLeafVals tabs p v = [] := by
  simp only [regLeafVals, h, ite_true]

theorem leafTys_nil (tabs : Tables) : leafTys tabs [] = [] := rfl

theorem leafTys_cons_reg (tabs : Tables) {p : ABIParam} (h : p.regs.isEmpty = false)
    (ps : List ABIParam) :
    leafTys tabs (p :: ps) = (leaves (tabs.ty p.type)).map (·.2) ++ leafTys tabs ps := by
  simp only [leafTys, List.flatMap_cons, h, Bool.false_eq_true, ite_false]

theorem leafTys_cons_stack (tabs : Tables) {p : ABIParam} (h : p.regs.isEmpty = true)
    (ps : List ABIParam) : leafTys tabs (p :: ps) = leafTys tabs ps := by
  simp only [leafTys, List.flatMap_cons, h, ite_true, List.nil_append]

theorem tailOp_eq {op : Op} (h : tailOp op = true) : op = .TailLECall ∨ op = .TailLECallInter := by
  unfold tailOp at h
  split at h
  · exact .inl rfl
  · exact .inr rfl
  · cases h

/-- The result shapes of an accepted call (`outsOK`): each well-formed. -/
theorem ec_outsOK_wf {tabs : Tables} {ps : List ABIParam} (h : outsOK tabs ps = true) :
    ∀ p ∈ ps, wf (tabs.ty p.type) = true := by
  intro p hp
  unfold outsOK at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  have := h.1 p hp
  rw [Bool.and_eq_true] at this
  exact this.1

/-- The register pieces of the results `outs` of a tuple `(results…, rest…)` (none for a
stack-assigned result, which the call writes into the outgoing-arguments area), followed by the
rest (memory, result addresses). -/
def convTuple (tabs : Tables) (outs : List ABIParam) : Val → Val
  | .tuple vs =>
    .tuple ((outs.zip vs).flatMap (fun (p, v) => regLeafVals tabs p v) ++ vs.drop outs.length)
  | _ => .poison

/-- The memory `m` with the encodings of the stack-assigned results `rs` of `qs` written into
their frame slots (`⟨.local 0 n, 0⟩` for result `n`), as the target's result stores leave it
before its `Ret`; a result marked as a self-move (`q.2`: already in its slot, `SkipOK`) is not
written. `none` if a write fails or a written result has no name. -/
def resMem (tabs : Tables) : List (ABIParam × Bool) → List Val → Mem → Option Mem
  | q :: qs, r :: rs, m =>
    if q.1.regs.isEmpty && !q.2 then
      match q.1.name with
      | some n => (m.write ⟨.local 0 n, 0⟩ (encode (tabs.ty q.1.type) r)).bind (resMem tabs qs rs)
      | none => none
    else resMem tabs qs rs m
  | _, _, m => some m

/-- A self-moved result `r` of shape `t` is already in its slot `n` of `m`: it contains `poison`
(the source's `Ret` is then stuck), or it refines the decoding of the slot's bytes. -/
def SelfHeld (t : Ty) (n : AuxRef) (r : Val) (m : Mem) : Prop :=
  r.hasPoison = true ∨ ∃ bs, m.read ⟨.local 0 n, 0⟩ t.size = some bs ∧ Sem.Refines r (decode bs 0 t)

/-- The results marked skipped in `qs` are stack-assigned, named and `SelfHeld` in `m`. -/
def SkipOK (tabs : Tables) (m : Mem) : List (ABIParam × Bool) → List Val → Prop
  | q :: qs, r :: rs => (q.2 = true → q.1.regs.isEmpty = true ∧
      ∃ n, q.1.name = some n ∧ SelfHeld (tabs.ty q.1.type) n r m) ∧ SkipOK tabs m qs rs
  | _, _ => True

/-- The results `ps` (values `rs`, memory `m`) marked skipped: the self-move candidates `cs` that
are stack-assigned, named and `SelfHeld` (decided classically: only proofs read it). -/
noncomputable def resSkip (tabs : Tables) (m : Mem) :
    List ABIParam → List Bool → List Val → List (ABIParam × Bool)
  | [], _, _ => []
  | p :: ps, cs, rs => (p, cs.headD false && p.regs.isEmpty &&
      @decide (∃ n, p.name = some n ∧ SelfHeld (tabs.ty p.type) n (rs.headD .poison) m)
        (Classical.propDecidable _)) ::
    resSkip tabs m ps cs.tail rs.tail

/-- The conversion of a `MakeResult`'s tuple `(results…, mem)` (`cs`: its self-move
candidates): the register pieces of the register-assigned results (`convTuple`) and the memory
with the stack-assigned results in their frame slots (`resMem`, skipping the self-moves already
there, `resSkip`; `poison` if a slot cannot be written). -/
noncomputable def convRes (tabs : Tables) (outs : List ABIParam) (cs : List Bool) : Val → Val
  | .tuple vs =>
    match vs.getLast? with
    | some (.mem m) =>
      match resMem tabs (resSkip tabs m outs cs vs) vs m with
      | some M => .tuple ((outs.zip vs).flatMap (fun (p, v) => regLeafVals tabs p v) ++ [.mem M])
      | none => .poison
    | _ => .poison
  | _ => .poison

/-- **The conversion of `expand calls`.** -/
noncomputable def ecCv (tabs : Tables) (f g : Func) : Cv := fun x y =>
  if invalidated g x then .poison else
  match f.value? x with
  | some u =>
    if (callOpMap u.op).isSome then
      (convTuple tabs (callOuts tabs u.aux) y).retype (shapeOf (typeShapes tabs) g x)
    else if u.op == .MakeResult then
      (convRes tabs (ownOuts tabs f) (selfMoves tabs (typeShapes tabs) f g u (ownOuts tabs f)
        (u.args.extract 0 (u.args.size - 1)).toList) y).retype (shapeOf (typeShapes tabs) g x)
    else if wideSel f g x then .poison
    else y
  | none => y

/-- The source values the obligation of `x` reads: its arguments in the source, its arguments
(and, for a call, its wide stack arguments' `Move`s' arguments) in the target that the source
defines, and the arguments of its wide call-result arguments (`wideSel`: the call whose register
pieces a wide store writes); none for a value the pass invalidated (its target node reads
nothing). -/
def ecFront (f g : Func) (x : ID) : List ID :=
  if invalidated g x then [] else
  ((f.value? x).map (·.args.toList)).getD [] ++
    ((((g.value? x).map (·.args.toList)).getD []) ++
      (stackMoves f g x).flatMap (fun z => ((g.value? z).map (·.args.toList)).getD [])).filter
        (fun a => !isNewB f a) ++
    ((((f.value? x).map (·.args.toList)).getD []).filter (wideSel f g)).flatMap
      (fun a => ((f.value? a).map (·.args.toList)).getD [])

theorem ecFront_src {f g : Func} {x a : ID} {u : Value} (hi : invalidated g x = false)
    (hu : f.value? x = some u) (ha : a ∈ u.args) : a ∈ ecFront f g x := by
  unfold ecFront
  rw [hi, if_neg Bool.false_ne_true, hu]
  exact List.mem_append_left _ (List.mem_append_left _ (Array.mem_toList_iff.2 ha))

theorem ecFront_tgt {f g : Func} {x a : ID} {w : Value} (hi : invalidated g x = false)
    (hw : g.value? x = some w) (ha : a ∈ w.args) (hn : isNewB f a = false) :
    a ∈ ecFront f g x := by
  unfold ecFront
  rw [hi, if_neg Bool.false_ne_true, hw]
  refine List.mem_append_left _ (List.mem_append_right _ (List.mem_filter.2 ⟨?_, ?_⟩))
  · exact List.mem_append_left _ (Array.mem_toList_iff.2 ha)
  · simp [hn]

/-- An argument of a wide call-result argument (`wideSel`) is in the front. -/
theorem ecFront_wide {f g : Func} {x a c : ID} {u au : Value} (hi : invalidated g x = false)
    (hu : f.value? x = some u) (ha : a ∈ u.args) (hwa : wideSel f g a = true)
    (hau : f.value? a = some au) (hc : c ∈ au.args) : c ∈ ecFront f g x := by
  unfold ecFront
  rw [hi, if_neg Bool.false_ne_true, hu]
  refine List.mem_append_right _ (List.mem_flatMap.2 ⟨a, List.mem_filter.2
    ⟨Array.mem_toList_iff.2 ha, hwa⟩, ?_⟩)
  rw [hau]
  exact Array.mem_toList_iff.2 hc

/-- The wide members of the front: the arguments of a wide call-result argument. -/
theorem ecFront_wide_cases {f g : Func} {x a : ID}
    (h : a ∈ ((((f.value? x).map (·.args.toList)).getD []).filter (wideSel f g)).flatMap
      (fun a => ((f.value? a).map (·.args.toList)).getD [])) :
    ∃ u b bu, f.value? x = some u ∧ b ∈ u.args ∧ wideSel f g b = true ∧ f.value? b = some bu ∧
      a ∈ bu.args := by
  cases hu : f.value? x with
  | none => rw [hu] at h; simp at h
  | some u =>
    rw [hu] at h
    obtain ⟨b, hb, hab⟩ := List.mem_flatMap.1 h
    obtain ⟨hb1, hb2⟩ : b ∈ u.args ∧ wideSel f g b = true := by simpa using hb
    cases hbu : f.value? b with
    | none => rw [hbu] at hab; simp at hab
    | some bu =>
      rw [hbu] at hab
      exact ⟨u, b, bu, rfl, hb1, hb2, hbu, Array.mem_toList_iff.1 hab⟩

/-- **The relation of `Ret` outcomes**: the source's results, one per result of the function,
each of its result's shape; the target's refine the register pieces of the source's, each
retyped at the shape of a register that holds its leaf without loss (`regShapeOK`: the leaf's
shape, or a pointer register for a pointer or 64-bit integer leaf); the target's memory refines
the source's with the stack-assigned results in their frame slots (`resMem`), but the self-moves
(`qs`, `SkipOK`), already there. -/
def ecRR (tabs : Tables) (f : Func) (rs : List Val) (m : Mem) (rs' : List Val) (m' : Mem) : Prop :=
  List.Forall₂ (fun (p : ABIParam) (r : Val) => r.hasTy (tabs.ty p.type) = true) (ownOuts tabs f) rs ∧
    ∃ rts : List Ty,
      List.Forall₂ (fun lt rt => regShapeOK rt lt = true) (leafTys tabs (ownOuts tabs f)) rts ∧
      RefinesList (List.zipWith Val.retype rts
        (((ownOuts tabs f).zip rs).flatMap fun (p, r) => regLeafVals tabs p r)) rs' ∧
      ∃ qs : List (ABIParam × Bool), qs.map (·.1) = ownOuts tabs f ∧ SkipOK tabs m qs rs ∧
        ∃ M, resMem tabs qs rs m = some M ∧ Mem.Refines M m'

/-- What `blockOK`'s `imkArgOK` gives for an argument `a` of a converted value `x` of block `fb`
whose node in `g` is an `IMake` (the `IMake` data shortcut, `ECCheck.imakeData`): the source
mode (`a` is the same interface-shaped `IMake` in `f` with an unconverted data operand of the
same constructor shape in both, and `x` depends on `a` in `gb` when `a` is a value of `fb`) or
the target mode (`a` is interface-shaped in `g`, and `a` and its data operand are each a node of
`gb` that `x` depends on or placed in a strict dominator of `gb` in `g`: `HeldT`). -/
def EcImkOK (tabs : Tables) (f g : Func) (fb gb : Block) (x a : ID) : Prop :=
  ∀ aw, g.value? a = some aw → aw.op = .IMake → aw.args.size = 2 ∧
    ((∃ au, f.value? a = some au ∧ au.op = .IMake ∧ au.args.size = 2 ∧
        au.args[1]! = aw.args[1]! ∧ ifaceShape (shapeOf (typeShapes tabs) f a) = true ∧
        special f g aw.args[1]! = false ∧
        ((∃ e e', shapeOf (typeShapes tabs) f aw.args[1]! = .ptr e ∧
            shapeOf (typeShapes tabs) g aw.args[1]! = .ptr e') ∨
          (∃ fs n fs' n', shapeOf (typeShapes tabs) f aw.args[1]! = .agg fs n ∧
            shapeOf (typeShapes tabs) g aw.args[1]! = .agg fs' n')) ∧
        (a ∈ fb.values →
          Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList) a x)) ∨
      (ifaceShape (shapeOf (typeShapes tabs) g a) = true ∧ HeldT g gb x a ∧ HeldT g gb x aw.args[1]!))

theorem ecCv_of_not_special {tabs : Tables} {f g : Func} {x : ID} (h : special f g x = false)
    (y : Val) : ecCv tabs f g x y = y := by
  unfold special at h
  simp only [Bool.or_eq_false_iff] at h
  obtain ⟨⟨hc, hi⟩, hw⟩ := h
  unfold ecCv
  rw [hi]
  unfold converted at hc
  cases hx : f.value? x with
  | none => rfl
  | some u =>
    rw [hx] at hc
    simp only [Bool.or_eq_false_iff] at hc
    simp only [Bool.false_eq_true, ite_false, hc.1, hc.2, hw]

/-- A wide call result (`wideSel`) converts to `poison`. -/
theorem ecCv_wideSel {tabs : Tables} {f g : Func} {x : ID} (h : wideSel f g x = true) (y : Val) :
    ecCv tabs f g x y = .poison := by
  have hu : ∃ u, f.value? x = some u ∧ u.op = .SelectN := by
    unfold wideSel at h
    split at h
    · next u w hu _ => simp only [Bool.and_eq_true, beq_iff_eq] at h; exact ⟨u, hu, h.1.1.1.1⟩
    · cases h
  obtain ⟨u, hu, hop⟩ := hu
  unfold ecCv
  split
  · rfl
  · rw [hu]
    simp only [hop, h, ite_true]
    rfl

end GoFV.Proof.EC

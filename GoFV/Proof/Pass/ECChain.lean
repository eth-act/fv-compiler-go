import GoFV.Proof.Pass.ECDefs
import GoFV.Proof.Pass.ECShape
import GoFV.Proof.ABI

/-!
# `expand calls`: the register pieces of a converted call's or `MakeResult`'s arguments (#28)

`piecesOK` (ExpandCallsCheck) says that the target's pieces of each Go-typed argument `a` are
selector chains of `a` (`chainOK`) along the leaf paths of the parameter's shape (`leafPaths`),
or the `IMake` data shortcut (`imakeData`). `ec_pieces`: in a target frame whose new chain
nodes hold their evaluations (`NewCons`) and whose register of `a` refines the source's, the
target's registers of the pieces refine `leafVals t` of the source's arguments.

`ecPathVal π v` is the value a chain computes along the path `π` (each step `Comp.select` then
`retype` at the field's shape); on a value of shape `t`, `leafVals t` is `ecPathVal` along each
leaf path (`ec_leafVals_paths`).

The `IMake` data shortcut needs facts of the frames the obligation does not provide
(`EcImkFacts`), in target mode (the target registers of the interface's `IMake` node and of its
data operand hold their evaluations, and the `IMake` is interface-typed in `g`) or source mode
(the source register of the same `IMake` in `f` holds its evaluation, interface-typed in `f`, its
data operand unconverted, a pointer in both functions, then the piece itself, or an aggregate in
both, then the source's data word is `poison`).
-/

namespace GoFV.Proof.EC

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.ECCheck GoFV.Proof.ABI GoFV.Proof.AtomSim

/-! ## Paths -/

/-- The value at path `π` of `v` (outermost field first). -/
def ecPathVal : List (Nat × Ty) → Val → Val
  | [], v => v
  | (k, s) :: π, v => ecPathVal π ((Comp.select k [v]).retype s)

theorem ecPathVal_poison : (π : List (Nat × Ty)) → ecPathVal π .poison = .poison
  | [] => rfl
  | (_, s) :: π => by
    show ecPathVal π (Val.retype s .poison) = _
    rw [show Val.retype s .poison = .poison by cases s <;> rfl]
    exact ecPathVal_poison π

theorem ecPathVal_append_one : (π : List (Nat × Ty)) → (k : Nat) → (s : Ty) → (v : Val) →
    ecPathVal (π ++ [(k, s)]) v = (Comp.select k [ecPathVal π v]).retype s
  | [], _, _, _ => rfl
  | (_, _) :: π, k, s, _ => ecPathVal_append_one π k s _

mutual
theorem ec_leafPaths_length : (t : Ty) → wf t = true → (leafPaths t).length = (leaves t).length
  | .int _, _ | .bool, _ | .ptr _, _ | .opaque _, _ | .empty, _ | .str, _ | .slice _, _ => rfl
  | .agg fs n, h => by
    unfold leafPaths
    rw [leaves_agg]
    exact ec_leafPathsFields_length fs n 0 0 h
  | .blob _, h | .mem, h | .tuple _, h | .other, h => nomatch h
theorem ec_leafPathsFields_length : (fs : List (Nat × Ty)) → (n s i : Nat) → wfFields fs n s = true →
    (leafPathsFields i fs).length = (leaves.leavesFields fs).length
  | [], _, _, _, _ => rfl
  | (o, t) :: fs, n, s, i, h => by
    simp only [wfFields, Bool.and_eq_true] at h
    unfold leafPathsFields
    rw [leavesFields_cons, List.length_append, List.length_append, List.length_map,
      List.length_map, ec_leafPaths_length t h.1.2, ec_leafPathsFields_length fs n _ (i + 1) h.2]
end

theorem ec_getD_of_drop {vs : List Val} {i : Nat} {v : Val} {rest : List Val}
    (h : vs.drop i = v :: rest) : vs.getD i .poison = v ∧ vs.drop (i + 1) = rest := by
  constructor
  · have : (vs.drop i)[0]? = some v := by rw [h]; rfl
    rw [List.getElem?_drop, Nat.add_zero] at this
    rw [List.getD_eq_getElem?_getD, this]; rfl
  · rw [← List.drop_drop, h]; rfl

mutual
/-- **`leafVals` along the leaf paths.** -/
theorem ec_leafVals_paths : (t : Ty) → wf t = true → {v : Val} → v.hasTy t = true →
    leafVals t v = (leafPaths t).map (ecPathVal · v)
  | .int _, _, v, hy | .bool, _, v, hy | .ptr _, _, v, hy | .opaque _, _, v, hy => by
    rw [leafVals_atom rfl, Val.retype_of_hasTy hy]; rfl
  | .empty, _, _, _ => rfl
  | .agg fs n, hw, v, hy => by
    cases v with
    | agg vs =>
      simp only [Val.hasTy] at hy
      show leafValsFields fs vs = (leafPathsFields 0 fs).map _
      have := ec_leafValsFields_paths fs n 0 hw 0 vs (by simpa using hy)
      simpa using this
    | poison =>
      rw [leafVals_agg_of_ne (v := .poison) fun _ e => nomatch e]
      simp only [ecPathVal_poison]
      rw [List.map_const', List.map_const', ec_leafPaths_length _ hw]
    | _ => simp [Val.hasTy] at hy
  | .str, _, v, hy | .slice _, _, v, hy => by
    cases v with
    | agg vs => rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> rfl
    | poison => rfl
    | _ => simp [Val.hasTy] at hy
  | .blob _, h, _, _ | .mem, h, _, _ | .tuple _, h, _, _ | .other, h, _, _ => nomatch h
theorem ec_leafValsFields_paths : (fs : List (Nat × Ty)) → (n s : Nat) → wfFields fs n s = true →
    (i : Nat) → (vs : List Val) → Val.hasTyList (vs.drop i) (fs.map (·.2)) = true →
    leafValsFields fs (vs.drop i) = (leafPathsFields i fs).map (ecPathVal · (.agg vs))
  | [], _, _, _, _, _, _ => rfl
  | (o, t) :: fs, n, s, hw, i, vs, hy => by
    simp only [wfFields, Bool.and_eq_true] at hw
    match hd : vs.drop i, hy with
    | v :: rest, hy =>
      simp only [List.map_cons, Val.hasTyList, Bool.and_eq_true] at hy
      obtain ⟨hv, hr⟩ := ec_getD_of_drop hd
      rw [leafValsFields_cons, Val.retype_of_hasTy hy.1, ec_leafVals_paths t hw.1.2 hy.1]
      unfold leafPathsFields
      rw [List.map_append, List.map_map, ← hr, ec_leafValsFields_paths fs n _ hw.2 (i + 1) vs
        (by rw [hr]; exact hy.2)]
      congr 1
      apply List.map_congr_left
      intro π _
      show ecPathVal π v = ecPathVal π ((Comp.select i [.agg vs]).retype t)
      rw [show Comp.select i [.agg vs] = vs.getD i .poison from rfl, hv,
        Val.retype_of_hasTy hy.1]
    | [], hy => simp [Val.hasTyList] at hy
end

/-! ## Selectors -/

theorem ec_getD_mono : {as bs : List Val} → Sem.RefinesList as bs → (k : Nat) →
    Sem.Refines (as.getD k .poison) (bs.getD k .poison)
  | _, _, .nil, _ => .poison _
  | _, _, .cons h _, 0 => h
  | _, _, .cons _ t, k + 1 => ec_getD_mono t k

theorem ec_select_mono (k : Nat) {v v' : Val} (h : Sem.Refines v v') :
    Sem.Refines (Comp.select k [v]) (Comp.select k [v']) := by
  cases h with
  | poison => exact .poison _
  | @agg as bs hl =>
    exact ec_getD_mono hl k
  | _ => exact .poison _

theorem ec_sel {w : Value} {k : Nat} (h : selIdx? w = some k) :
    GoFV.Opt.RewriteCheck.termOp w.op = true ∧ GoFV.Proof.Rules.frameOp w.op = false ∧
      ∀ ty args, evalPure w.op ty w.auxInt w.aux args = Comp.select k args := by
  unfold selIdx? at h
  split at h
  all_goals first
    | (next hop => cases h; rw [hop]; exact ⟨by decide, by decide, fun _ _ => rfl⟩)
    | (next hop =>
        by_cases hlt : w.auxInt.toInt < 0
        · simp [hlt] at h
        · simp only [hlt, ↓reduceIte, Option.some.injEq] at h
          subst h
          rw [hop]
          refine ⟨by decide, by decide, fun _ _ => ?_⟩
          show Comp.selectAux w.auxInt _ = _
          unfold Comp.selectAux
          simp only [hlt, ↓reduceIte])
    | cases h

theorem ec_args_one {arr : Array ID} (h : arr.size = 1) : arr.toList = [arr[0]!] := by
  rcases arr with ⟨l⟩
  match l, h with
  | [x], _ => rfl

/-! ## Selector chains -/

/-- The target register of a chain node refines the path value of the source's argument. -/
theorem ec_chain {tabs : Tables} {f g : Func} {env : Env} {T : Frame} {E L : ID → Prop}
    (hNC : NewCons env (Ctx.make tabs g) (isNewB f) T E)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ b ∈ w.args, isNewB f b = true → L b)
    {a : ID} {y y' : Val} (ha : T.regs[a]? = some (some y')) (hy : Sem.Refines y y') :
    ∀ (rp : List (Nat × Ty)) (p : ID), chainOK (typeShapes tabs) g (isNewB f) rp p a = true →
      (isNewB f p = true → E p ∧ L p) →
      ∃ yp, T.regs[p]? = some (some yp) ∧ Sem.Refines (ecPathVal rp.reverse y) yp
  | [], p, h, _ => by
    unfold chainOK at h
    rw [beq_iff_eq] at h
    subst h
    exact ⟨y', ha, hy⟩
  | (k, s) :: rp, p, h, hp => by
    unfold chainOK at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hn, h⟩ := h
    obtain ⟨hE, hLp⟩ := hp hn
    obtain ⟨-, w, yp, hw, hcl, hyp, hev⟩ := hNC p hE
    have hw : g.value? p = some w := hw
    rw [hw] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hk, hs⟩, h1⟩, hch⟩ := h
    obtain ⟨hid, hLa⟩ := hL p hLp w hw
    have hargs := ec_args_one h1
    have hmem : w.args[0]! ∈ w.args := by
      rw [← Array.mem_toList_iff, hargs]; exact List.mem_cons_self
    obtain ⟨yq, hyq, hr⟩ := ec_chain hNC hL ha hy rp w.args[0]! hch fun hq =>
      ⟨hcl _ hmem hq, hLa _ hmem hq⟩
    obtain ⟨hterm, hfr, hpure⟩ := ec_sel hk
    have hval := evalValue_term hterm hev
    rw [GoFV.Proof.Rules.opVal_pure hfr, hpure, hid, tys_of_value hw, Option.getD_some, hargs, List.map_cons, List.map_nil,
      rv_of hyq, ← typeShapes_getD, ← valueTy, eqE_retype hs] at hval
    refine ⟨yp, hyp, ?_⟩
    rw [hval, List.reverse_cons, ecPathVal_append_one]
    exact retype_mono s (ec_select_mono k hr)

/-! ## The `IMake` data shortcut -/

/-- What the `IMake` data shortcut needs of a source argument `a` whose node in `g` is an
`IMake` (facts of the frames the obligation does not provide), in one of two modes. Target
mode: the target registers of `a` and of the `IMake`'s data operand hold their evaluations and
`a`'s type in `g` is an interface. Source mode: `a` is the same `IMake` in `f`, its source
register holds its evaluation, its type in `f` is an interface, and the data operand is
unconverted, a pointer in both or an aggregate in both. -/
def EcImkFacts (env : Env) (tabs : Tables) (f g : Func) (frS T : Frame) (a : ID) : Prop :=
  ∀ aw, g.value? a = some aw → aw.op = .IMake →
    (EcTgtHolds env tabs g T a ∧ EcTgtHolds env tabs g T aw.args[1]! ∧
      ∃ f0 o e n, shapeOf (typeShapes tabs) g a = .agg [f0, (o, .ptr e)] n) ∨
    (EcSrcHolds env tabs f frS a ∧
      (∃ au, f.value? a = some au ∧ au.op = .IMake ∧ au.args.size = 2 ∧ au.args[1]! = aw.args[1]!) ∧
      (∃ f0 o e n, shapeOf (typeShapes tabs) f a = .agg [f0, (o, .ptr e)] n) ∧
      special f g aw.args[1]! = false ∧
      ((∃ e e', shapeOf (typeShapes tabs) f aw.args[1]! = .ptr e ∧
          shapeOf (typeShapes tabs) g aw.args[1]! = .ptr e') ∨
        (∃ fs n fs' n', shapeOf (typeShapes tabs) f aw.args[1]! = .agg fs n ∧
          shapeOf (typeShapes tabs) g aw.args[1]! = .agg fs' n')))

theorem ec_leafPathsFields_head_hasTy : (fs : List (Nat × Ty)) → (i : Nat) → (vs : List Val) →
    Val.hasTyList (vs.drop i) (fs.map (·.2)) = true → ∀ k s π, (k, s) :: π ∈ leafPathsFields i fs →
      (vs.getD k .poison).hasTy s = true
  | [], _, _, _, _, _, _, hm => by simp [leafPathsFields] at hm
  | (o, t) :: fs, i, vs, hy, k, s, π, hm => by
    match hd : vs.drop i, hy with
    | v :: rest, hy =>
      simp only [List.map_cons, Val.hasTyList, Bool.and_eq_true] at hy
      obtain ⟨hv, hr⟩ := ec_getD_of_drop hd
      unfold leafPathsFields at hm
      rcases List.mem_append.1 hm with hm | hm
      · obtain ⟨π', -, he⟩ := List.mem_map.1 hm
        simp only [List.cons.injEq, Prod.mk.injEq] at he
        obtain ⟨⟨rfl, rfl⟩, -⟩ := he
        rw [hv]; exact hy.1
      · exact ec_leafPathsFields_head_hasTy fs (i + 1) vs (by rw [hr]; exact hy.2) k s π hm
    | [], hy => simp [Val.hasTyList] at hy

/-- The first step of a leaf path selects a component of the step's shape. -/
theorem ec_leafPaths_head_hasTy {t : Ty} {y : Val} (hy : y.hasTy t = true) {k : Nat} {s : Ty}
    {π : List (Nat × Ty)} (hm : (k, s) :: π ∈ leafPaths t) : (Comp.select k [y]).hasTy s = true := by
  cases t with
  | agg fs n =>
    cases y with
    | agg vs =>
      simp only [Val.hasTy] at hy
      exact ec_leafPathsFields_head_hasTy fs 0 vs (by simpa using hy) k s π hm
    | poison => rfl
    | _ => simp [Val.hasTy] at hy
  | str =>
    cases y with
    | agg vs =>
      obtain ⟨p, l, rfl, hp, hl⟩ := Val.hasTy_agg_str.1 hy
      simp only [leafPaths, List.mem_cons, List.cons.injEq, Prod.mk.injEq, List.not_mem_nil,
        or_false] at hm
      rcases hm with ⟨⟨rfl, rfl⟩, -⟩ | ⟨⟨rfl, rfl⟩, -⟩
      · cases p <;> first
          | (simp_all [Comp.select, Val.hasTy, Val.isPtrWord]; done)
          | (rename_i w _; cases w <;> simp_all [Comp.select, Val.hasTy, Val.isPtrWord])
      · rfl
    | poison => rfl
    | _ => simp [Val.hasTy] at hy
  | slice e =>
    cases y with
    | agg vs =>
      obtain ⟨p, l, c, rfl, hp, -⟩ := Val.hasTy_agg_slice.1 hy
      simp only [leafPaths, List.mem_cons, List.cons.injEq, Prod.mk.injEq, List.not_mem_nil,
        or_false] at hm
      rcases hm with ⟨⟨rfl, rfl⟩, -⟩ | ⟨⟨rfl, rfl⟩, -⟩ | ⟨⟨rfl, rfl⟩, -⟩
      · cases p <;> first
          | (simp_all [Comp.select, Val.hasTy, Val.isPtrWord]; done)
          | (rename_i w _; cases w <;> simp_all [Comp.select, Val.hasTy, Val.isPtrWord])
      · rfl
      · rfl
    | poison => rfl
    | _ => simp [Val.hasTy] at hy
  | _ => simp [leafPaths] at hm

theorem ec_args_two {arr : Array ID} (h : arr.size = 2) : arr.toList = [arr[0]!, arr[1]!] := by
  rcases arr with ⟨l⟩
  match l, h with
  | [x, z], _ => rfl

theorem ec_agg_retype_ptr (vs : List Val) (t : Ty) (e : Option Nat) :
    ((Val.agg vs).retype t).retype (.ptr e) = .poison := by
  cases t with
  | agg fs n =>
    show (match Val.retypeFields fs vs with
      | some vs' => Val.agg vs'
      | none => Val.poison).retype (.ptr e) = .poison
    split <;> rfl
  | int w => cases w <;> rfl
  | str =>
    rw [retype_str_agg]
    split
    · unfold Val.ofStr; split <;> rfl
    · rfl
  | slice el =>
    rw [retype_slice_agg]
    split
    · unfold Val.ofSlice; split <;> rfl
    · rfl
  | _ => rfl

theorem ec_hasTy_ptr (v : Val) (e e' : Option Nat) : v.hasTy (.ptr e) = v.hasTy (.ptr e') := by
  cases v with
  | int w x => cases w <;> rfl
  | _ => rfl

/-- A value of an aggregate shape retyped at a pointer is `poison`. -/
theorem eco_retype_ptr_of_agg {v : Val} {fs : List (Nat × Ty)} {n : Nat} (e : Option Nat)
    (h : v.hasTy (.agg fs n) = true) : v.retype (.ptr e) = .poison := by
  cases v <;> first | rfl | exact absurd h (by simp [Val.hasTy])

/-- An ID with a pointer shape in `f` is defined by `f`. -/
theorem eco_not_new_of_ptr {sh : Array Ty} {f : Func} {d : ID} {e : Option Nat}
    (h : shapeOf sh f d = .ptr e) : isNewB f d = false := by
  unfold shapeOf at h
  unfold isNewB
  cases hd : f.value? d with
  | none => rw [hd] at h; cases h
  | some _ => rfl

/-- **The `IMake` data shortcut**: the piece is the data operand (a pointer) or the source's
data word is `poison` (the operand is an aggregate). -/
theorem ec_imake {tabs : Tables} {f g : Func} {env : Env} {frS T : Frame} {a q : ID}
    {π : List (Nat × Ty)} {t : Ty} {y ya : Val}
    (himk : imakeData (typeShapes tabs) g π q a = true) (hπ : π ∈ leafPaths t)
    (hyt : y.hasTy t = true) (hyS : frS.regs[a]? = some (some y))
    (hya : T.regs[a]? = some (some ya)) (hyy : Sem.Refines y ya)
    (hRS : RegsOK (Ctx.make tabs f) frS) (hF : EcImkFacts env tabs f g frS T a) (hq : Reg T q)
    (hfq : ∀ yq, frS.regs[q]? = some (some yq) → isNewB f q = false →
      ∃ yq', T.regs[q]? = some (some yq') ∧ Sem.Refines (ecCv tabs f g q yq) yq') :
    Sem.Refines (ecPathVal π y) (rv T q) := by
  unfold imakeData at himk
  split at himk
  · next s aw haw =>
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at himk
    obtain ⟨⟨⟨hop, h2⟩, -⟩, hd⟩ := himk
    rcases hF aw haw hop with ⟨hTa, hTd, f0, o, e, n, hsh⟩ |
      ⟨hSa, ⟨au, hau, hauop, hau2, haud⟩, ⟨f0, o, e, n, hsh⟩, hsp, hshape⟩
    · -- target mode: the target's `IMake` evaluates
      obtain ⟨hid, ya2, hya2, hev⟩ := hTa aw haw
      rw [hya] at hya2
      cases hya2
      have hargs := ec_args_two h2
      have hval := evalValue_term (by rw [hop]; decide) hev
      rw [hop, hid, ← shapeOf_eq, hsh, hargs] at hval
      rcases f0 with ⟨o0, t0⟩
      change ya = (Val.agg [rv T aw.args[0]!, rv T aw.args[1]!]).retype _ at hval
      have e1 : (Val.agg [rv T aw.args[0]!, rv T aw.args[1]!]).retype
          (.agg [(o0, t0), (o, .ptr e)] n) =
          .agg [(rv T aw.args[0]!).retype t0, (rv T aw.args[1]!).retype (.ptr e)] := rfl
      rw [e1] at hval
      subst hval
      cases hyy with
      | poison => rw [ecPathVal_poison]; exact .poison _
      | agg hl =>
        cases hl with
        | cons h0 hl1 =>
          cases hl1 with
          | cons h1 hnil =>
            cases hnil
            rename_i w0 w1
            show Sem.Refines ((Comp.select 1 [.agg [w0, w1]]).retype s) _
            change Sem.Refines (w1.retype s) _
            rcases hd with ⟨rfl, hptr⟩ | hsm
            · -- the data operand is the piece, a pointer
              split at hptr
              · next e' hsq =>
                unfold shapeOf at hsq
                cases hdw : g.value? aw.args[1]! with
                | none => rw [hdw] at hsq; cases hsq
                | some dw =>
                  rw [hdw] at hsq
                  obtain ⟨hdid, yd, hyd, hevd⟩ := hTd dw hdw
                  have hty := Proof.evalValue_hasTy hevd
                  rw [hdid, tys_of_value hdw, Option.getD_some, ← typeShapes_getD, ← valueTy, hsq]
                    at hty
                  rw [rv_of hyd] at h1 ⊢
                  rw [Val.retype_of_hasTy (by rw [ec_hasTy_ptr yd e e']; exact hty)] at h1
                  have hw1 : w1.hasTy s = true :=
                    ec_leafPaths_head_hasTy (y := .agg [w0, w1]) hyt hπ
                  rw [Val.retype_of_hasTy hw1]
                  exact h1
              · cases hptr
            · -- the data operand is an aggregate: the source's data word is `poison`
              split at hsm
              · next dw fs' n' hdw _ =>
                simp only [Bool.or_eq_true, beq_iff_eq] at hsm
                obtain ⟨hdid, yd, hyd, hevd⟩ := hTd dw hdw
                have hvd := evalValue_term (by rcases hsm with h | h <;> rw [h] <;> decide) hevd
                rw [GoFV.Proof.Rules.opVal_pure (by rcases hsm with h | h <;> rw [h] <;> decide)]
                  at hvd
                have hmk : ∀ ty args, evalPure dw.op ty dw.auxInt dw.aux args = Comp.make args := by
                  rcases hsm with h | h <;> rw [h] <;> intro _ _ <;> rfl
                rw [hmk] at hvd
                rw [rv_of hyd, hvd] at h1
                change Sem.Refines w1 ((Val.agg _).retype _ |>.retype _) at h1
                rw [ec_agg_retype_ptr] at h1
                cases h1
                rw [show Val.retype s .poison = .poison by cases s <;> rfl]
                exact .poison _
              · cases hsm
    · -- source mode: the source's `IMake` evaluates
      obtain ⟨hid, ys, hys, hev⟩ := hSa au hau
      rw [hyS] at hys
      cases hys
      have hargs := ec_args_two hau2
      have hm1 : au.args[1]! ∈ au.args := by
        rw [← Array.mem_toList_iff, hargs]; simp
      obtain ⟨yd, hyd⟩ := regs_of_ok hev _ hm1
      have hydt := (hRS _ _ hyd).1
      rw [← shapeOf_eq] at hydt
      have hval := evalValue_term (by rw [hauop]; decide) hev
      rw [hauop, hid, ← shapeOf_eq, hsh, hargs] at hval
      rcases f0 with ⟨o0, t0⟩
      change y = (Val.agg [rv frS au.args[0]!, rv frS au.args[1]!]).retype _ at hval
      have e1 : (Val.agg [rv frS au.args[0]!, rv frS au.args[1]!]).retype
          (.agg [(o0, t0), (o, .ptr e)] n) =
          .agg [(rv frS au.args[0]!).retype t0, (rv frS au.args[1]!).retype (.ptr e)] := rfl
      rw [e1] at hval
      subst hval
      have hw1 : ((rv frS au.args[1]!).retype (.ptr e)).hasTy s = true :=
        ec_leafPaths_head_hasTy hyt hπ
      show Sem.Refines (((rv frS au.args[1]!).retype (.ptr e)).retype s) _
      rw [Val.retype_of_hasTy hw1, rv_of hyd]
      rw [haud] at hyd hydt
      rcases hd with ⟨rfl, hptr⟩ | hsm
      · -- the data operand is the piece, a pointer in both
        split at hptr
        · next e' hsq =>
          rcases hshape with ⟨e1, _, hfp, -⟩ | ⟨_, _, _, _, -, hga⟩
          · rw [hfp] at hydt
            rw [Val.retype_of_hasTy (by rw [ec_hasTy_ptr yd e e1]; exact hydt)]
            obtain ⟨yq', hyq', hr⟩ := hfq yd hyd (eco_not_new_of_ptr hfp)
            rw [ecCv_of_not_special hsp] at hr
            rw [rv_of hyq']
            exact hr
          · rw [hsq] at hga; cases hga
        · cases hptr
      · -- the data operand is an aggregate in both: the source's data word is `poison`
        split at hsm
        · next dw fs' n' hdw hsg =>
          rcases hshape with ⟨_, _, -, hgp⟩ | ⟨_, _, _, _, hfa, -⟩
          · rw [hsg] at hgp; cases hgp
          · rw [hfa] at hydt
            rw [eco_retype_ptr_of_agg e hydt]
            exact .poison _
        · cases hsm
  · cases himk

/-! ## The pieces of the arguments -/

/-- The register pieces `piecesOK` expects of an argument `r` of a parameter of shape `t`:
`leafVals t r`, or (with `cast`) the pointer itself for a 64-bit integer parameter (`castOK`). -/
def ecPieceVals (cast : Bool) (t : Ty) (r : Val) : List Val :=
  match cast, t, r with
  | true, .int .w64, .ptr p => [.ptr p]
  | _, t, r => leafVals t r

theorem ecPieceVals_false (t : Ty) (r : Val) : ecPieceVals false t r = leafVals t r := rfl

/-- On an argument of the parameter's shape, the pieces are its leaf values (an address-less
pointer at a 64-bit integer shape retypes to itself). -/
theorem ecPieceVals_of_hasTy (cast : Bool) {t : Ty} {r : Val} (h : r.hasTy t = true) :
    ecPieceVals cast t r = leafVals t r := by
  cases cast with
  | false => rfl
  | true =>
    unfold ecPieceVals
    split
    · simp only [Val.hasTy] at h
      simp only [leafVals, Val.retype, List.cons.injEq, and_true]
      revert h
      split <;> simp_all
    · rfl

theorem ec_castOK {s t : Ty} (h : castOK s t = true) : (∃ e, s = .ptr e) ∧ t = .int .w64 := by
  unfold castOK at h
  split at h
  · exact ⟨⟨_, rfl⟩, rfl⟩
  · cases h

theorem ec_pairs {P : List (Nat × Ty) × ID → Bool} {F : List (Nat × Ty) → Val} {G : ID → Val} :
    (paths : List (List (Nat × Ty))) → (qs : List ID) → qs.length = paths.length →
      (paths.zip qs).all P = true →
      (∀ x ∈ paths.zip qs, P x = true → Sem.Refines (F x.1) (G x.2)) →
      Sem.RefinesList (paths.map F) (qs.map G)
  | [], [], _, _, _ => .nil
  | π :: paths, q :: qs, hl, ha, h => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at ha
    exact .cons (h (π, q) List.mem_cons_self ha.1)
      (ec_pairs paths qs (by simpa using hl) ha.2 fun x hx => h x (List.mem_cons_of_mem _ hx))
  | [], _ :: _, hl, _, _ | _ :: _, [], hl, _, _ => by simp at hl

/-- What the pieces lemma needs of a source argument `a`: a register of its shape whose
conversion the target's register refines. -/
def EcArgRel (tabs : Tables) (f g : Func) (frS T : Frame) (a : ID) : Prop :=
  ∃ y, frS.regs[a]? = some (some y) ∧ RegOK (Ctx.make tabs f) a y ∧
    ∃ y', T.regs[a]? = some (some y') ∧ Sem.Refines (ecCv tabs f g a y) y'

/-- **The register pieces of the arguments** (`piecesOK`): the target's registers of the pieces
refine the expected pieces (`ecPieceVals`: the leaf values) of the source's registers of the
arguments. -/
theorem ec_pieces {tabs : Tables} {f g : Func} {env : Env} {frS T : Frame} {E L : ID → Prop}
    (hNC : NewCons env (Ctx.make tabs g) (isNewB f) T E)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ b ∈ w.args, isNewB f b = true → L b)
    (hRS : RegsOK (Ctx.make tabs f) frS) (cast : Bool) :
    ∀ (ps : List ABIParam) (as pcs : List ID), piecesOK tabs (typeShapes tabs) f g cast ps as pcs = true →
      (∀ p ∈ ps, wf (tabs.ty p.type) = true) →
      (∀ q ∈ pcs, Reg T q) → (∀ q ∈ pcs, isNewB f q = true → E q ∧ L q) →
      (∀ a ∈ as, EcArgRel tabs f g frS T a) → (∀ a ∈ as, EcImkFacts env tabs f g frS T a) →
      (∀ q ∈ pcs, ∀ yq, frS.regs[q]? = some (some yq) → isNewB f q = false →
        ∃ yq', T.regs[q]? = some (some yq') ∧ Sem.Refines (ecCv tabs f g q yq) yq') →
      Sem.RefinesList ((ps.zip (as.map (rv frS))).flatMap fun (p, r) => ecPieceVals cast (tabs.ty p.type) r)
        (pcs.map (rv T))
  | [], [], [], _, _, _, _, _, _, _ => .nil
  | [], [], _ :: _, h, _, _, _, _, _, _ | [], _ :: _, _, h, _, _, _, _, _, _
  | _ :: _, [], _, h, _, _, _, _, _, _ => by simp [piecesOK] at h
  | p :: ps, a :: as, pcs, h, hwf, hreg, hEL, hrel, himk, hfq => by
    unfold piecesOK at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
    obtain ⟨⟨⟨⟨heq, hlen⟩, hsp⟩, hall⟩, hrest⟩ := h
    have hw := hwf p List.mem_cons_self
    obtain ⟨y, hyS, hry, y', hyT, hyy⟩ := hrel a List.mem_cons_self
    simp only [List.map_cons, List.zip_cons_cons, List.flatMap_cons, rv_of hyS]
    rw [← List.take_append_drop (leafPaths (tabs.ty p.type)).length pcs, List.map_append]
    refine RefinesList.append ?_ (ec_pieces hNC hL hRS cast ps as _ hrest (fun q hq => hwf q
      (List.mem_cons_of_mem _ hq)) (fun q hq => hreg q (List.mem_of_mem_drop hq))
      (fun q hq => hEL q (List.mem_of_mem_drop hq)) (fun b hb => hrel b (List.mem_cons_of_mem _ hb))
      (fun b hb => himk b (List.mem_cons_of_mem _ hb)) (fun q hq => hfq q (List.mem_of_mem_drop hq)))
    rcases heq with heq | ⟨rfl, hcast⟩
    · have hyt : y.hasTy (tabs.ty p.type) = true := by
        have := hry.1
        rw [← shapeOf_eq, eqE_hasTy heq] at this
        exact this
      rw [ecPieceVals_of_hasTy cast hyt, ec_leafVals_paths _ hw hyt]
      refine ec_pairs _ _ (by rw [List.length_take]; omega) hall fun x hx hP => ?_
      have hπ : x.1 ∈ leafPaths (tabs.ty p.type) := (List.of_mem_zip hx).1
      have hq : x.2 ∈ pcs := List.mem_of_mem_take (List.of_mem_zip hx).2
      have hns : special f g a = false := by
        rcases hsp with he | hs
        · rw [List.isEmpty_iff] at he; rw [he] at hπ; cases hπ
        · simpa using hs
      rw [ecCv_of_not_special hns] at hyy
      simp only [Bool.or_eq_true] at hP
      rcases hP with hc | hi
      · obtain ⟨yq, hyq, hr⟩ := ec_chain hNC hL hyT hyy _ _ hc (hEL _ hq)
        rw [List.reverse_reverse] at hr
        rw [rv_of hyq]
        exact hr
      · exact ec_imake hi hπ hyt hyS hyT hyy hRS (himk a List.mem_cons_self) (hreg _ hq) (hfq _ hq)
    · -- a pointer argument of a 64-bit integer parameter: its piece is the argument itself
      obtain ⟨⟨e, hs⟩, ht⟩ := ec_castOK hcast
      have hyp : y.hasTy (.ptr e) = true := by
        have := hry.1
        rw [← shapeOf_eq, hs] at this
        exact this
      rw [ht] at hall hsp hlen ⊢
      have hns : special f g a = false := by
        rcases hsp with he | hs
        · cases he
        · simpa using hs
      rw [ecCv_of_not_special hns] at hyy
      obtain ⟨q, pcs', rfl⟩ : ∃ q pcs', pcs = q :: pcs' := by
        cases pcs with
        | nil => simp [leafPaths] at hlen
        | cons q pcs' => exact ⟨q, pcs', rfl⟩
      have hqa : q = a := by
        simp [leafPaths, chainOK, imakeData] at hall
        exact hall
      subst hqa
      simp only [leafPaths, List.length_cons, List.length_nil, Nat.zero_add, List.take_succ_cons,
        List.take_zero, List.map_cons, List.map_nil, rv_of hyT]
      cases y with
      | ptr r => exact .cons hyy .nil
      | poison => exact .cons (.poison _) .nil
      | _ => simp [Val.hasTy] at hyp

end GoFV.Proof.EC

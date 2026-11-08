import GoFV.Proof.Pass.ECShape
import GoFV.Proof.ABI
import GoFV.Proof.ValRefine

variable [GoFV.SSA.Sem.Addrs]

/-!
# Evaluating the Make-trees of `expand calls` (issue #28)

`ECCheck.mkTree` accepts a value of `g` as a tree of `Make` ops (`StructMake`, `SliceMake`, …,
zero-sized parts `Empty`) over new values with atom leaves. Evaluated in a frame whose new
values hold their own evaluations (`NewCons`), the tree's root is `build t` of its leaves'
values, retyped at `t` (`ecT_node`), and it evaluates as soon as its leaves do
(`ecT_root_ok`). Also: shapes up to pointers' element sizes decode alike
(`ecT_eqE_decode`, `ecT_eqE_size`), and index forms of `Forall₂`/`RefinesList`.
-/

namespace GoFV.Proof.EC

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.ECCheck GoFV.Proof.ABI GoFV.Proof.AtomSim GoFV.Opt.RewriteCheck

/-! ## Shapes up to pointers' element sizes -/

mutual
theorem ecT_decode_erase (bs : Array Byte) : ∀ (o : Nat) (t : Ty), decode bs o (erase t) = decode bs o t
  | _, .ptr _ => rfl
  | o, .agg fs n => by
    simp only [erase, decode]
    rw [ecT_decodeFields_erase bs o fs]
  | _, .tuple _ => rfl
  | _, .int _ => rfl
  | _, .bool => rfl
  | _, .mem => rfl
  | _, .other => rfl
  | _, .blob _ => rfl
  | _, .empty => rfl
  | _, .opaque _ => rfl
  | _, .str => rfl
  | _, .slice _ => rfl
theorem ecT_decodeFields_erase (bs : Array Byte) :
    ∀ (o : Nat) (fs : List (Nat × Ty)), decodeFields bs o (eraseFields fs) = decodeFields bs o fs
  | _, [] => rfl
  | o, (p, t) :: fs => by
    simp only [eraseFields, decodeFields]
    rw [ecT_decode_erase bs (o + p) t, ecT_decodeFields_erase bs o fs]
end

theorem ecT_size_erase (t : Ty) : (erase t).size = t.size := by
  cases t <;> rfl

theorem ecT_eqE_decode {s t : Ty} (h : eqE s t = true) (bs : Array Byte) (o : Nat) :
    decode bs o s = decode bs o t := by
  rw [← ecT_decode_erase bs o s, Ty.eq_of_beq h, ecT_decode_erase]

theorem ecT_eqE_size {s t : Ty} (h : eqE s t = true) : s.size = t.size := by
  rw [← ecT_size_erase s, Ty.eq_of_beq h, ecT_size_erase]

/-! ## Index forms -/

theorem ecT_forall₂_get {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' →
      ∀ (k : Nat) (a : α), l[k]? = some a → ∃ b, l'[k]? = some b ∧ R a b
  | _, _, .nil, _, _, h => by cases h
  | _, _, .cons r _, 0, _, h => by cases h; exact ⟨_, rfl, r⟩
  | _, _, .cons _ hs, k + 1, a, h => ecT_forall₂_get hs k a h

theorem ecT_forall₂_get' {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' →
      ∀ (k : Nat) (b : β), l'[k]? = some b → ∃ a, l[k]? = some a ∧ R a b
  | _, _, .nil, _, _, h => by cases h
  | _, _, .cons r _, 0, _, h => by cases h; exact ⟨_, rfl, r⟩
  | _, _, .cons _ hs, k + 1, b, h => ecT_forall₂_get' hs k b h

theorem ecT_refinesList_of_get :
    ∀ {as bs : List Val}, as.length = bs.length →
      (∀ (k : Nat) a b, as[k]? = some a → bs[k]? = some b → Sem.Refines a b) → RefinesList as bs
  | [], [], _, _ => .nil
  | a :: as, b :: bs, hl, h =>
    .cons (h 0 a b rfl rfl)
      (ecT_refinesList_of_get (by simpa using hl) fun k x y hx hy => h (k + 1) x y hx hy)
  | [], _ :: _, hl, _ => nomatch hl
  | _ :: _, [], hl, _ => nomatch hl

theorem ecT_refinesList_get :
    ∀ {as bs : List Val}, RefinesList as bs →
      ∀ (k : Nat) (a : Val), as[k]? = some a → ∃ b, bs[k]? = some b ∧ Sem.Refines a b
  | _, _, .nil, _, _, h => by cases h
  | _, _, .cons r _, 0, _, h => by cases h; exact ⟨_, rfl, r⟩
  | _, _, .cons _ hs, k + 1, a, h => ecT_refinesList_get hs k a h

theorem ecT_refinesList_length : ∀ {as bs : List Val}, RefinesList as bs → as.length = bs.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => congrArg (· + 1) (ecT_refinesList_length h)

/-! ## Pure ops -/

theorem ecT_make_cases {op : Op} (h : isMake op = true) :
    op = .StructMake ∨ op = .ArrayMake1 ∨ op = .SliceMake ∨ op = .StringMake ∨ op = .IMake ∨
      op = .ComplexMake := by
  unfold isMake at h
  split at h <;> simp_all

theorem ecT_make_term {op : Op} (h : isMake op = true) :
    termOp op = true ∧ ∀ ty ai ax argv, evalPure op ty ai ax argv = .agg argv := by
  rcases ecT_make_cases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, fun _ _ _ _ => rfl⟩

/-- A pure, non-frame value whose arguments have registers evaluates by `evalPure`. -/
theorem ecT_eval_term {env : Env} {ctx : Ctx} {fr : Frame} {w : Value} (ht : termOp w.op = true)
    (hfr : GoFV.Proof.Rules.frameOp w.op = false) (hr : ∀ a ∈ w.args, Reg fr a) :
    evalValue env ctx fr w = .ok ((evalPure w.op (ctx.tys[w.id]?.getD .other) w.auxInt w.aux
      (w.args.toList.map (rv fr))).retype (ctx.tys[w.id]?.getD .other)) := by
  rw [evalValue_of_regs hr, evalOp_term ht, GoFV.Proof.Rules.opVal_pure hfr]; rfl

theorem ecT_eval_make {env : Env} {ctx : Ctx} {fr : Frame} {w : Value} (h : isMake w.op = true)
    (hr : ∀ a ∈ w.args, Reg fr a) :
    evalValue env ctx fr w =
      .ok ((Val.agg (w.args.toList.map (rv fr))).retype (ctx.tys[w.id]?.getD .other)) := by
  have hfr : GoFV.Proof.Rules.frameOp w.op = false := by
    rcases ecT_make_cases h with e | e | e | e | e | e <;> rw [e] <;> decide
  rw [ecT_eval_term (ecT_make_term h).1 hfr hr, (ecT_make_term h).2]

theorem ecT_eval_empty {env : Env} {ctx : Ctx} {fr : Frame} {w : Value} (h : w.op = .Empty)
    (hr : ∀ a ∈ w.args, Reg fr a) :
    evalValue env ctx fr w = .ok (Val.empty.retype (ctx.tys[w.id]?.getD .other)) := by
  rw [ecT_eval_term (by rw [h]; decide) (by rw [h]; decide) hr, h]; rfl

theorem ecT_eval_selectN {env : Env} {ctx : Ctx} {fr : Frame} {w : Value} (h : w.op = .SelectN)
    (hr : ∀ a ∈ w.args, Reg fr a) :
    evalValue env ctx fr w = .ok ((Tuple.selectN w.auxInt (w.args.toList.map (rv fr))).retype
      (ctx.tys[w.id]?.getD .other)) := by
  rw [ecT_eval_term (by rw [h]; decide) (by rw [h]; decide) hr, h]; rfl

/-! ## Make-trees -/

/-- A leaf of a Make-tree: the value of `g` at `l` (with ID `l`) evaluates to `y` in `T`. -/
def EcTLeaf (env : Env) (tabs : Tables) (g : Func) (T : Frame) (l : ID) (y : Val) : Prop :=
  ∃ wl, g.value? l = some wl ∧ wl.id = l ∧ evalValue env (Ctx.make tabs g) T wl = .ok y

/-- A leaf's type has (up to pointers' element sizes) its leaf shape. -/
def EcTShape (tabs : Tables) (g : Func) (l : ID) (e : Nat × Ty) : Prop :=
  eqE (shapeOf (typeShapes tabs) g l) e.2 = true

theorem ecT_retype_agg_congr {fs : List (Nat × Ty)} {m : Nat} {vs vs' : List Val}
    (h : Val.retypeFields fs vs = Val.retypeFields fs vs') :
    (Val.agg vs).retype (.agg fs m) = (Val.agg vs').retype (.agg fs m) := by
  simp only [Val.retype, h]

/-- The leaves of a shape whose aggregate layout (`Ty.asAgg`) has fields `fs`. -/
theorem ecT_leaves_of_asAgg {t : Ty} {fs : List (Nat × Ty)} {m : Nat}
    (ht : t.asAgg = .agg fs m) : leaves t = leaves.leavesFields fs := by
  cases t <;> simp only [Ty.asAgg, Ty.strAgg, Ty.sliceAgg, Ty.agg.injEq, reduceCtorEq] at ht
  case agg => rw [ht.1]; rfl
  case str => rw [← ht.1]; rfl
  case slice => rw [← ht.1]; rfl

theorem ecT_eq_of_asAgg_empty {t : Ty} (h : t.asAgg = .empty) : t = .empty := by
  cases t <;> simp_all [Ty.asAgg, Ty.strAgg, Ty.sliceAgg]

theorem ecT_asAgg_of_atom {t : Ty} (h : atom t.asAgg = true) : t.asAgg = t := by
  cases t <;> simp_all [Ty.asAgg, Ty.strAgg, Ty.sliceAgg, atom]

theorem ecT_headD_take {l : List Val} : (l.take 1).headD .poison = l.headD .poison := by
  cases l <;> rfl

/-- A `Make` node retyped at a shape whose aggregate layout has fields `fs` is `build` of its
children's values when the fields retype them alike. -/
theorem ecT_retype_make_congr {t : Ty} {fs : List (Nat × Ty)} {m : Nat}
    (ht : t.asAgg = .agg fs m) {vs ys : List Val}
    (h : Val.retypeFields fs vs = Val.retypeFields fs (buildFields fs ys)) :
    (Val.agg vs).retype t = (build t ys).retype t := by
  cases t <;> simp only [Ty.asAgg, Ty.strAgg, Ty.sliceAgg, Ty.agg.injEq, reduceCtorEq] at ht
  case agg fs' m' =>
    obtain ⟨rfl, rfl⟩ := ht
    exact ecT_retype_agg_congr h
  case str =>
    obtain ⟨rfl, rfl⟩ := ht
    rw [retype_asAgg .str (.agg vs)]
    simp only [Ty.asAgg, Ty.strAgg]
    rw [ecT_retype_agg_congr h]
    simp only [build, Val.retype_idem]
    rw [retype_asAgg .str]
    simp only [Ty.asAgg, Ty.strAgg, buildFields, leaves, List.length_cons, List.length_nil,
      Nat.zero_add, build, ecT_headD_take]
  case slice e =>
    obtain ⟨rfl, rfl⟩ := ht
    rw [retype_asAgg (.slice e) (.agg vs)]
    simp only [Ty.asAgg, Ty.sliceAgg]
    rw [ecT_retype_agg_congr h]
    simp only [build, Val.retype_idem]
    rw [retype_asAgg (.slice e)]
    simp only [Ty.asAgg, Ty.sliceAgg, buildFields, leaves, List.length_cons, List.length_nil,
      Nat.zero_add, build, ecT_headD_take, List.drop_drop, Nat.reduceAdd]

theorem ecT_shapeOf_value {tabs : Tables} {g : Func} {z : ID} {w : Value} (hw : g.value? z = some w) :
    shapeOf (typeShapes tabs) g z = valueTy (typeShapes tabs) (some w) := by
  unfold shapeOf; rw [hw]

theorem ecT_tys_value {tabs : Tables} {g : Func} {z : ID} {w : Value} (hw : g.value? z = some w)
    (hid : w.id = z) :
    (Ctx.make tabs g).tys[w.id]?.getD .other = valueTy (typeShapes tabs) (some w) := by
  rw [hid, ← shapeOf_eq, ecT_shapeOf_value hw]

section Tree
variable {env : Env} {tabs : Tables} {g : Func} {nw : ID → Bool} {T : Frame} {E P : ID → Prop}

/-- The children of a Make node. -/
theorem ecT_fields (hN : NewCons env (Ctx.make tabs g) nw T E)
    (hP : ∀ z, P z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, nw a = true → P a)
    {n : Nat}
    (ih : ∀ (z : ID) (t : Ty) (ls : List ID) (w : Value) (y : Val),
      mkTree (typeShapes tabs) g nw n z t = some ls → g.value? z = some w → P z →
      (∀ a ∈ w.args, nw a = true → E a) → evalValue env (Ctx.make tabs g) T w = .ok y →
      ∃ ys, List.Forall₂ (EcTLeaf env tabs g T) ls ys ∧
        List.Forall₂ (EcTShape tabs g) ls (leaves t) ∧ y = (build t ys).retype t) :
    ∀ (fs : List (Nat × Ty)) (as : List ID) (lss : List (List ID)), fs.length = as.length →
      (fs.zip as).mapM (fun (e : (Nat × Ty) × ID) =>
        if nw e.2 then mkTree (typeShapes tabs) g nw n e.2 e.1.2 else none) = some lss →
      (∀ a ∈ as, nw a = true → E a ∧ P a) →
      ∃ ys, List.Forall₂ (EcTLeaf env tabs g T) lss.flatten ys ∧
        List.Forall₂ (EcTShape tabs g) lss.flatten (leaves.leavesFields fs) ∧
        Val.retypeFields fs (as.map (rv T)) = Val.retypeFields fs (buildFields fs ys)
  | [], [], lss, _, h, _ => by
    cases h
    exact ⟨[], .nil, .nil, rfl⟩
  | (o, ft) :: fs, a :: as, lss, hl, h, hE => by
    simp only [List.zip_cons_cons, List.mapM_cons] at h
    cases hb : (if nw a = true then mkTree (typeShapes tabs) g nw n a ft else none) with
    | none => rw [hb] at h; cases h
    | some b =>
      rw [hb] at h
      cases hr : (fs.zip as).mapM (fun (e : (Nat × Ty) × ID) =>
          if nw e.2 then mkTree (typeShapes tabs) g nw n e.2 e.1.2 else none) with
      | none => rw [hr] at h; cases h
      | some bs =>
        rw [hr] at h
        cases h
        have hna : nw a = true := by
          cases hn : nw a
          · rw [hn] at hb; cases hb
          · rfl
        simp only [hna, ↓reduceIte] at hb
        obtain ⟨hEa, hPa⟩ := hE a List.mem_cons_self hna
        obtain ⟨-, wa, ya, hwa, hEargs, hreg, hev⟩ := hN a hEa
        obtain ⟨ys1, F1, S1, hy1⟩ := ih a ft b wa ya hb hwa hPa hEargs hev
        obtain ⟨ys', F', S', hrf⟩ := ecT_fields hN hP ih fs as bs (by simpa using hl) hr
          fun x hx => hE x (List.mem_cons_of_mem _ hx)
        have hlen : ys1.length = (leaves ft).length := F1.length_eq.symm.trans S1.length_eq
        refine ⟨ys1 ++ ys', ?_, ?_, ?_⟩
        · rw [List.flatten_cons]; exact F1.append F'
        · rw [List.flatten_cons, leavesFields_cons]
          exact (S1.map_right (fun x : Nat × Ty => (o + x.1, x.2)) fun _ _ r => r).append S'
        · show Val.retypeFields ((o, ft) :: fs) (rv T a :: as.map (rv T)) =
            Val.retypeFields ((o, ft) :: fs)
              (build ft ((ys1 ++ ys').take (leaves ft).length) ::
                buildFields fs ((ys1 ++ ys').drop (leaves ft).length))
          rw [← hlen, List.take_left' rfl, List.drop_left' rfl, rv_of hreg]
          simp only [Val.retypeFields, hrf, hy1, Val.retype_idem]
  | [], _ :: _, _, hl, _, _ => nomatch hl
  | _ :: _, [], _, hl, _, _ => nomatch hl

/-- **A Make-tree evaluates to `build` of its leaves.** -/
theorem ecT_node (hN : NewCons env (Ctx.make tabs g) nw T E)
    (hP : ∀ z, P z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, nw a = true → P a) :
    ∀ (n : Nat) (z : ID) (t : Ty) (ls : List ID) (w : Value) (y : Val),
      mkTree (typeShapes tabs) g nw n z t = some ls → g.value? z = some w → P z →
      (∀ a ∈ w.args, nw a = true → E a) → evalValue env (Ctx.make tabs g) T w = .ok y →
      ∃ ys, List.Forall₂ (EcTLeaf env tabs g T) ls ys ∧
        List.Forall₂ (EcTShape tabs g) ls (leaves t) ∧ y = (build t ys).retype t
  | 0, _, _, _, _, _, hm, _, _, _, _ => by cases hm
  | n + 1, z, t, ls, w, y, hm, hw, hPz, hE, hev => by
    obtain ⟨hid, hPa⟩ := hP z hPz w hw
    have hty := ecT_tys_value (tabs := tabs) hw hid
    rw [mkTree, hw] at hm
    dsimp only at hm
    split at hm
    · cases hm
    rename_i hq0
    have hq : eqE (valueTy (typeShapes tabs) (some w)) t = true := by
      simpa using hq0
    clear hq0
    have hregs := regs_of_ok hev
    split at hm
    · -- a Make node
      rename_i fs m hfs
      split at hm
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        cases hmap : (fs.zip w.args.toList).mapM (fun (e : (Nat × Ty) × ID) =>
            if nw e.2 then mkTree (typeShapes tabs) g nw n e.2 e.1.2 else none) with
        | none => rw [hmap] at hm; cases hm
        | some lss =>
          rw [hmap] at hm
          cases hm
          obtain ⟨ys, F, S, hrf⟩ := ecT_fields hN hP (ecT_node hN hP n) fs w.args.toList
            lss (hc.2.symm.trans Array.length_toList.symm) hmap
            fun a ha hna => ⟨hE a (Array.mem_toList_iff.1 ha) hna,
              hPa a (Array.mem_toList_iff.1 ha) hna⟩
          refine ⟨ys, F, by rw [ecT_leaves_of_asAgg hfs]; exact S, ?_⟩
          rw [ecT_eval_make hc.1 hregs, hty, eqE_retype hq] at hev
          cases hev
          exact ecT_retype_make_congr hfs hrf
      · cases hm
    · -- a zero-sized node
      rename_i h0
      obtain rfl := ecT_eq_of_asAgg_empty h0
      split at hm
      · rename_i he
        cases hm
        rw [ecT_eval_empty (beq_iff_eq.1 he) hregs, hty, eqE_retype hq] at hev
        cases hev
        exact ⟨[], .nil, .nil, rfl⟩
      · cases hm
    · -- a leaf
      split at hm
      · rename_i ha
        rw [ecT_asAgg_of_atom ha] at ha
        cases hm
        refine ⟨[y], .cons ⟨w, hw, hid, hev⟩ .nil, ?_, ?_⟩
        · rw [leaves_atom ha]
          exact .cons (by show eqE _ _ = true; rw [ecT_shapeOf_value hw]; exact hq) .nil
        · rw [build_atom ha, List.headD_cons, ← eqE_retype hq, ← hty, evalValue_typed hev]
      · cases hm

/-- **A Make-tree evaluates** when its arguments have registers and its root, if it is a leaf,
evaluates. -/
theorem ecT_root_ok {n : Nat} {z : ID} {t : Ty} {ls : List ID} {w : Value}
    (hm : mkTree (typeShapes tabs) g nw n z t = some ls) (hw : g.value? z = some w)
    (hr : ∀ a ∈ w.args, Reg T a)
    (hleaf : z ∈ ls → ∃ y, evalValue env (Ctx.make tabs g) T w = .ok y) :
    ∃ y, evalValue env (Ctx.make tabs g) T w = .ok y := by
  cases n with
  | zero => cases hm
  | succ n =>
    rw [mkTree, hw] at hm
    dsimp only at hm
    split at hm
    · cases hm
    split at hm
    · split at hm
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        exact ⟨_, ecT_eval_make hc.1 hr⟩
      · cases hm
    · split at hm
      · rename_i he
        exact ⟨_, ecT_eval_empty (beq_iff_eq.1 he) hr⟩
      · cases hm
    · split at hm
      · cases hm
        exact hleaf (List.mem_singleton.2 rfl)
      · cases hm

end Tree

end GoFV.Proof.EC

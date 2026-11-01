import GoFV.Opt.RewriteCheck

/-!
# Rule expressions do not read the values of pattern nodes (issue #113)

The validator evaluates a rule's checks and condition (`GoFV.Proof.Rules.evalE`) on the static
instance `RewriteCheck.env`, whose leaves are `poison`; `Rule.Sound` is applied to an instance
with the real leaf values. The two evaluations agree up to the values inside `DV.val`
(`DV.erase`): `evalE_erase`. On the semantic side every `DV.val` with a position is a
rule variable's value or the top's (`evalE_good`).
-/

namespace GoFV.Proof.Pass.Rewrite

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck
open GoFV.Proof.Rules (DV PEnv Oracle Path evalE evalEs fieldDV fieldE methodE convE unDV indexE
  binDV binE builtinE callE callH intBin litDV strctField magicDV udivDV sdivDV Helper)

/-- Forget the value inside `DV.val`. -/
def _root_.GoFV.Proof.Rules.DV.erase : DV → DV
  | .val _ p => .val .poison p
  | d => d

theorem _root_.GoFV.Proof.Rules.DV.erase_eq_cases : ∀ {d d' : DV}, d.erase = d'.erase →
    d = d' ∨ ∃ v v' p, d = .val v p ∧ d' = .val v' p := by
  intro d d' h
  cases d <;> cases d' <;> simp_all [DV.erase]

theorem _root_.GoFV.Proof.Rules.DV.erase_val (v : Val) (p : Option Path) : (DV.val v p).erase = .val .poison p := rfl

/-- Neither a value nor a struct. -/
def _root_.GoFV.Proof.Rules.DV.flat : DV → Bool
  | .val .. | .strct _ => false
  | _ => true

theorem _root_.GoFV.Proof.Rules.DV.erase_of_flat {d : DV} (h : d.flat = true) : d.erase = d := by
  cases d <;> simp_all [DV.flat, DV.erase]

/-! ## Helpers -/

section Helpers

variable {e e' : PEnv}

theorem fieldDV_rel (hty : e.ty = e'.ty) (hai : e.auxInt = e'.auxInt) {d d' : DV}
    (h : d.erase = d'.erase) (n : String) : fieldDV e d n = fieldDV e' d' n := by
  rcases DV.erase_eq_cases h with rfl | ⟨v, v', p, rfl, rfl⟩
  · cases d <;> simp only [fieldDV, hty, hai]
  · cases p with
    | none => simp only [fieldDV]
    | some q =>
      by_cases h1 : n = "Type"
      · subst h1; simp only [fieldDV, hty]
      · by_cases h2 : n = "AuxInt"
        · subst h2; simp only [fieldDV, hai]
        · simp [fieldDV, h1, h2]

theorem fieldE_rel (hty : e.ty = e'.ty) (hai : e.auxInt = e'.auxInt) (y : GoFV.Rules.Expr) {d d' : DV}
    (h : d.erase = d'.erase) (n : String) : fieldE e y d n = fieldE e' y d' n := by
  unfold fieldE; split
  · rfl
  · split
    · rfl
    · exact fieldDV_rel hty hai h n
  · exact fieldDV_rel hty hai h n

theorem methodE_rel {d d' : DV} (h : d.erase = d'.erase) (n : String) (args : List GoFV.Rules.Expr) :
    methodE d n args = methodE d' n args := by
  rcases DV.erase_eq_cases h with rfl | ⟨v, v', p, rfl, rfl⟩
  · rfl
  · unfold methodE; split <;> rfl

theorem convE_rel {d d' : DV} (h : d.erase = d'.erase) (ty : GoFV.Rules.GoTy) :
    convE ty d = convE ty d' := by
  rcases DV.erase_eq_cases h with rfl | ⟨v, v', p, rfl, rfl⟩
  · rfl
  · simp only [convE]

theorem unDV_rel {d d' : DV} (h : d.erase = d'.erase) (o : GoFV.Rules.UnOp) (ty : GoFV.Rules.GoTy) :
    unDV o ty d = unDV o ty d' := by
  rcases DV.erase_eq_cases h with rfl | ⟨v, v', p, rfl, rfl⟩
  · rfl
  · simp only [unDV]

theorem indexE_rel {d d' : DV} (h : d.erase = d'.erase) (y : GoFV.Rules.Expr) : indexE y d = indexE y d' := by
  rcases DV.erase_eq_cases h with rfl | ⟨v, v', p, rfl, rfl⟩
  · rfl
  · unfold indexE; split <;> simp_all

theorem binDV_rel {a a' b b' : DV} (ha : a.erase = a'.erase) (hb : b.erase = b'.erase)
    (o : GoFV.Rules.BinOp) (ty : GoFV.Rules.GoTy) : binDV o ty a b = binDV o ty a' b' := by
  rcases DV.erase_eq_cases ha with rfl | ⟨v, v', p, rfl, rfl⟩
  · rcases DV.erase_eq_cases hb with rfl | ⟨w, w', q, rfl, rfl⟩
    · rfl
    · cases a <;> simp only [binDV]
  · simp only [binDV]

theorem binE_rel {a a' b b' : DV} (ha : a.erase = a'.erase) (hb : b.erase = b'.erase)
    (vtys : List GoFV.Rules.GoTy) (o : GoFV.Rules.BinOp) (ty : GoFV.Rules.GoTy) (y : GoFV.Rules.Expr) :
    (binE vtys o ty y a b).map DV.erase = (binE vtys o ty y a' b').map DV.erase := by
  unfold binE
  split
  · rcases DV.erase_eq_cases ha with rfl | ⟨v, v', p, rfl, rfl⟩
    · split <;> simp_all
    · rfl
  · rcases DV.erase_eq_cases ha with rfl | ⟨v, v', p, rfl, rfl⟩
    · split <;> simp_all
    · rfl
  all_goals rw [binDV_rel ha hb]

theorem eq_of_map_erase {α : Type} {f : α → DV} {g : DV → α → α} :
    ∀ {l l' : List α}, (∀ a ∈ l, (f a).flat = true) → (∀ a, g (f a) a = a) →
      l.map (fun a => g (f a).erase a) = l'.map (fun a => g (f a).erase a) →
      (∀ a b, g (f a).erase a = g (f b).erase b → (f a).flat = true → a = b) → l' = l
  | [], [], _, _, _, _ => rfl
  | a :: l, b :: l', hf, hg, h, hi => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [hi a b h.1 (hf a List.mem_cons_self) |>.symm,
      eq_of_map_erase (fun x hx => hf x (List.mem_cons_of_mem _ hx)) hg h.2 hi]
  | [], _ :: _, _, _, h, _ | _ :: _, [], _, _, h, _ => by simp at h

theorem dv_eq_of_erase {a b : DV} (h : a.erase = b.erase) (ha : a.flat = true) : a = b := by
  rcases DV.erase_eq_cases h with h | ⟨v, v', p, rfl, rfl⟩
  · exact h
  · simp [DV.flat] at ha

theorem list_eq_of_erase {l l' : List DV} (hf : ∀ a ∈ l, a.flat = true)
    (h : l.map DV.erase = l'.map DV.erase) : l' = l :=
  eq_of_map_erase (f := id) (g := fun d _ => d) hf (fun _ => rfl) h
    (fun _ _ hab ha => dv_eq_of_erase hab ha)

theorem pairs_eq_of_erase {l l' : List (DV × GoFV.Rules.GoTy)} (hf : ∀ a ∈ l, a.1.flat = true)
    (h : l.map (fun a => (a.1.erase, a.2)) = l'.map (fun a => (a.1.erase, a.2))) : l' = l :=
  eq_of_map_erase (f := Prod.fst) (g := fun d a => (d, a.2)) hf (fun _ => rfl) h
    (fun a b hab ha => by
      simp only [Prod.mk.injEq] at hab
      exact Prod.ext (dv_eq_of_erase hab.1 ha) hab.2)

theorem builtinE_rel {l l' : List DV} (h : l.map DV.erase = l'.map DV.erase) (fn : String) :
    builtinE fn l = builtinE fn l' := by
  have key : ∀ {l l' : List DV}, l.map DV.erase = l'.map DV.erase → ∀ {d},
      builtinE fn l = some d → builtinE fn l' = some d := by
    intro l l' h d hd
    unfold builtinE at hd
    split at hd
    · obtain rfl := list_eq_of_erase (by simp [DV.flat]) h
      exact hd
    · cases hd
  cases hb : builtinE fn l with
  | none =>
    cases hb' : builtinE fn l' with
    | none => rfl
    | some d => rw [key h.symm hb'] at hb; cases hb
  | some d => rw [key h hb]

/-- `callH` reads only the positions of `DV.val` arguments. -/
theorem callH_rel_some (hai : e.auxInt = e'.auxInt) {h : Helper} {l l' : List (DV × GoFV.Rules.GoTy)}
    (hl : l.map (fun a => (a.1.erase, a.2)) = l'.map (fun a => (a.1.erase, a.2))) {d : DV}
    (hd : callH e h l = some d) : callH e' h l' = some d := by
  unfold callH at hd
  split at hd
  · cases hd
    rcases l' with _ | ⟨⟨y, t'⟩, _ | ⟨_, _⟩⟩ <;> simp at hl
    obtain ⟨h1, rfl⟩ := hl
    cases y <;> simp only [DV.erase, reduceCtorEq, DV.val.injEq] at h1
    obtain ⟨-, rfl⟩ := h1
    simp only [callH, hai]
  all_goals first
    | (cases hd; done)
    | (obtain rfl := pairs_eq_of_erase (by simp [DV.flat]) hl; exact hd)

theorem callH_rel (hai : e.auxInt = e'.auxInt) (h : Helper) {l l' : List (DV × GoFV.Rules.GoTy)}
    (hl : l.map (fun a => (a.1.erase, a.2)) = l'.map (fun a => (a.1.erase, a.2))) :
    callH e h l = callH e' h l' := by
  cases hd : callH e h l with
  | none =>
    cases hd' : callH e' h l' with
    | none => rfl
    | some d => rw [callH_rel_some hai.symm hl.symm hd'] at hd; cases hd
  | some d => rw [callH_rel_some hai hl hd]

end Helpers

theorem getD_erase {o o' : Option DV} (h : o.map DV.erase = o'.map DV.erase) (d : DV) :
    (o.getD d).erase = (o'.getD d).erase := by
  cases o <;> cases o' <;> simp_all

theorem zip_erase {l l' : List DV} (h : l.map DV.erase = l'.map DV.erase) :
    ∀ ts : List GoFV.Rules.GoTy, (l.zip ts).map (fun a => (a.1.erase, a.2)) =
      (l'.zip ts).map (fun a => (a.1.erase, a.2)) := by
  induction l generalizing l' with
  | nil => cases l' with
    | nil => intro; rfl
    | cons _ _ => simp at h
  | cons a l ih =>
    cases l' with
    | nil => simp at h
    | cons b l' =>
      simp only [List.map_cons, List.cons.injEq] at h
      intro ts
      cases ts with
      | nil => rfl
      | cons t ts => simp only [List.zip_cons_cons, List.map_cons, h.1, ih h.2 ts]

mutual
/-- **Leaf independence**: two evaluations whose instances have the same node fields and whose
variables agree up to the values of `DV.val` agree up to those values. -/
theorem evalE_erase (vtys : List GoFV.Rules.GoTy) (or : Oracle) {e e' : PEnv} (hty : e.ty = e'.ty)
    (hai : e.auxInt = e'.auxInt) {σ σ' : Nat → DV} (hσ : ∀ x, (σ x).erase = (σ' x).erase)
    (top top' : Val) :
    ∀ x : GoFV.Rules.Expr, (evalE vtys σ or e top x).erase = (evalE vtys σ' or e' top' x).erase
  | .lit _ _ => rfl
  | .cnst _ _ _ => rfl
  | .op _ => rfl
  | .var i => hσ i
  | .rsv r => by cases r <;> rfl
  | .glob _ _ => rfl
  | .field y n _ => by
    simp only [evalE]
    rw [fieldE_rel hty hai y (evalE_erase vtys or hty hai hσ top top' y) n]
  | .call fn args _ => by
    simp only [evalE, callE]
    split
    · rw [callH_rel hai _ (zip_erase (evalEs_erase vtys or hty hai hσ top top' args) _)]
    · rfl
  | .method y n args _ => by
    simp only [evalE]
    rw [methodE_rel (evalE_erase vtys or hty hai hσ top top' y) n args]
  | .builtin fn args _ => by
    simp only [evalE]
    rw [builtinE_rel (evalEs_erase vtys or hty hai hσ top top' args) fn]
  | .conv ty y => by
    simp only [evalE]
    rw [convE_rel (evalE_erase vtys or hty hai hσ top top' y) ty]
  | .assert _ _ => rfl
  | .unop o y ty => by
    simp only [evalE]
    rw [unDV_rel (evalE_erase vtys or hty hai hσ top top' y) o ty]
  | .binop o y z ty => by
    simp only [evalE]
    exact getD_erase (binE_rel (evalE_erase vtys or hty hai hσ top top' y)
      (evalE_erase vtys or hty hai hσ top top' z) vtys o ty y) _
  | .index y k _ => by
    simp only [evalE]
    rw [indexE_rel (evalE_erase vtys or hty hai hσ top top' k) y]
  | .deref _ _ => rfl
theorem evalEs_erase (vtys : List GoFV.Rules.GoTy) (or : Oracle) {e e' : PEnv} (hty : e.ty = e'.ty)
    (hai : e.auxInt = e'.auxInt) {σ σ' : Nat → DV} (hσ : ∀ x, (σ x).erase = (σ' x).erase)
    (top top' : Val) :
    ∀ xs : List GoFV.Rules.Expr,
      (evalEs vtys σ or e top xs).map DV.erase = (evalEs vtys σ' or e' top' xs).map DV.erase
  | [] => rfl
  | x :: xs => by
    simp only [evalEs, List.map_cons]
    rw [evalE_erase vtys or hty hai hσ top top' x, evalEs_erase vtys or hty hai hσ top top' xs]
end

/-! ## Values on the semantic side -/

/-- Every positioned value satisfies `P`, and a struct's fields are flat. -/
def Good (P : Val → Path → Prop) (d : DV) : Prop :=
  (∀ w p, d = .val w (some p) → P w p) ∧ (∀ fs, d = .strct fs → ∀ x ∈ fs, x.2.flat = true)

theorem good_of_flat {P : Val → Path → Prop} {d : DV} (h : d.flat = true) : Good P d :=
  ⟨fun w p hd => by subst hd; simp [DV.flat] at h, fun fs hd => by subst hd; simp [DV.flat] at h⟩

theorem good_strct {P : Val → Path → Prop} {fs : List (String × DV)}
    (h : ∀ x ∈ fs, x.2.flat = true) : Good P (.strct fs) :=
  ⟨fun _ _ hd => (by cases hd), fun _ hd => (by cases hd; exact h)⟩

theorem good_getD {P : Val → Path → Prop} {o : Option DV} {d : DV} (ho : ∀ x, o = some x → Good P x)
    (hd : Good P d) : Good P (o.getD d) := by
  cases o with
  | none => exact hd
  | some x => exact ho x rfl

theorem strctField_mem {fs : List (String × DV)} {n : String} {d : DV} (h : strctField fs n = some d) :
    ∃ x ∈ fs, x.2 = d := by
  unfold strctField at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨x, hx, rfl⟩ := h
  exact ⟨x, List.mem_of_find?_eq_some hx, rfl⟩

theorem fieldE_good {P : Val → Path → Prop} {e : PEnv} {y : GoFV.Rules.Expr} {dy : DV} {n : String}
    (hy : Good P dy) : ∀ d, fieldE e y dy n = some d → Good P d := by
  intro d h
  have hdv : fieldDV e dy n = some d → Good P d := by
    intro h
    unfold fieldDV at h
    split at h
    · cases h; exact good_of_flat rfl
    · cases h; exact good_of_flat rfl
    · obtain ⟨x, hx, rfl⟩ := strctField_mem h
      exact good_of_flat (hy.2 _ rfl x hx)
    · cases h
  unfold fieldE at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨t, -, rfl⟩ := h
    exact good_of_flat rfl
  · split at h
    · cases h; exact good_of_flat rfl
    · exact hdv h
  · exact hdv h

theorem callH_good {P : Val → Path → Prop} {e : PEnv} {h : Helper} {l : List (DV × GoFV.Rules.GoTy)} :
    ∀ d, callH e h l = some d → Good P d := by
  intro d hd
  unfold callH at hd
  split at hd
  all_goals first
    | (cases hd; done)
    | (cases hd; exact good_of_flat rfl)
    | (cases hd; exact good_strct (by simp [DV.flat]))
    | (simp only [Option.map_eq_some_iff] at hd; obtain ⟨⟨_, _⟩, _, rfl⟩ := hd;
       exact good_of_flat rfl)
    | (simp only [magicDV, udivDV, sdivDV] at hd
       split at hd <;> (try (cases hd; done)) <;> cases hd <;>
         first | exact good_of_flat rfl | exact good_strct (by simp [DV.flat]))
    | (split at hd <;> (try (cases hd; done)) <;> cases hd <;> exact good_of_flat rfl)

theorem flat_good_opt {P : Val → Path → Prop} {o : Option DV} (h : ∀ d, o = some d → d.flat = true) :
    ∀ d, o = some d → Good P d := fun d hd => good_of_flat (h d hd)

mutual
/-- **Values on the semantic side**: every positioned value of an evaluation is a variable's or
the top's. -/
theorem evalE_good {P : Val → Path → Prop} (vtys : List GoFV.Rules.GoTy) (or : Oracle) (e : PEnv)
    {σ : Nat → DV} (hσ : ∀ x, Good P (σ x)) {top : Val} (htop : P top [])
    (hor : ∀ x, Good P (or.dv x)) : ∀ x : GoFV.Rules.Expr, Good P (evalE vtys σ or e top x)
  | .lit _ c => by
    simp only [evalE]; refine good_getD (flat_good_opt fun d hd => ?_) (hor _)
    unfold litDV at hd; split at hd <;> cases hd <;> rfl
  | .cnst _ _ c => by
    simp only [evalE]; refine good_getD (flat_good_opt fun d hd => ?_) (hor _)
    unfold litDV at hd; split at hd <;> cases hd <;> rfl
  | .op _ => good_of_flat rfl
  | .var i => hσ i
  | .rsv r => by
    cases r
    · exact ⟨fun w p hd => by cases hd; exact htop, fun _ hd => by cases hd⟩
    all_goals exact hor _
  | .glob _ _ => hor _
  | .field y n _ => by
    simp only [evalE]
    exact good_getD (fieldE_good (evalE_good vtys or e hσ htop hor y)) (hor _)
  | .call fn args _ => by
    simp only [evalE, callE]
    refine good_getD (fun d hd => ?_) (hor _)
    split at hd
    · exact callH_good d hd
    · cases hd
  | .method y n args _ => by
    simp only [evalE]
    refine good_getD (fun d hd => ?_) (hor _)
    unfold methodE at hd
    split at hd
    · split at hd
      · simp only [Option.map_eq_some_iff] at hd; obtain ⟨_, _, rfl⟩ := hd; exact good_of_flat rfl
      · rename_i fs heq
        obtain ⟨x, hx, rfl⟩ := strctField_mem hd
        exact good_of_flat ((evalE_good vtys or e hσ htop hor y).2 fs heq x hx)
      · cases hd
    · split at hd
      · cases hd; exact good_strct (by simp [DV.flat])
      · cases hd; exact good_strct (by simp [DV.flat])
      · cases hd; exact good_strct (by simp [DV.flat])
      · cases hd; exact good_of_flat rfl
      · cases hd
    · split at hd
      · rename_i fs heq
        obtain ⟨x, hx, rfl⟩ := strctField_mem hd
        exact good_of_flat ((evalE_good vtys or e hσ htop hor y).2 fs heq x hx)
      · cases hd
    all_goals first
      | cases hd
      | (unfold GoFV.Proof.Rules.kindDV at hd
         split at hd
         · simp only [Option.map_eq_some_iff] at hd; obtain ⟨_, _, rfl⟩ := hd; exact good_of_flat rfl
         · cases hd)
  | .builtin fn args _ => by
    simp only [evalE]
    refine good_getD (flat_good_opt fun d hd => ?_) (hor _)
    unfold builtinE at hd; split at hd <;> cases hd; rfl
  | .conv ty y => by
    simp only [evalE]
    refine good_getD (flat_good_opt fun d hd => ?_) (hor _)
    unfold convE at hd; split at hd
    · split at hd <;> cases hd; rfl
    · cases hd
  | .assert _ _ => hor _
  | .unop o y ty => by
    simp only [evalE]
    refine good_getD (flat_good_opt fun d hd => ?_) (hor _)
    unfold unDV at hd; repeat' split at hd
    all_goals first | (cases hd; done) | (cases hd; rfl)
  | .binop o y z ty => by
    simp only [evalE]
    refine good_getD (fun d hd => ?_) (hor _)
    have hz := evalE_good vtys or e hσ htop hor z
    have bin : ∀ o ty a b d, binDV o ty a b = some d → d.flat = true := by
      intro o ty a b d h
      unfold binDV at h
      split at h
      · unfold intBin at h
        split at h <;> (repeat' split at h) <;> first | (cases h; done) | (cases h; rfl)
      all_goals first
        | (cases h; done)
        | (unfold GoFV.Proof.Rules.floatCmp at h
           split at h <;> first | (cases h; done) | (cases h; rfl))
        | (split at h <;> first | (cases h; done) | (cases h; rfl))
        | (split at h
           · cases h; rfl
           · unfold GoFV.Proof.Rules.floatCmp at h
             split at h <;> first | (cases h; done) | (cases h; rfl))
    unfold binE at hd
    split at hd
    · split at hd
      · cases hd; exact hz
      · cases hd; exact good_of_flat rfl
      · cases hd
    · split at hd
      · cases hd; exact good_of_flat rfl
      · cases hd; exact hz
      · cases hd
    all_goals exact good_of_flat (bin _ _ _ _ _ hd)
  | .index y k _ => by
    simp only [evalE]
    refine good_getD (flat_good_opt fun d hd => ?_) (hor _)
    unfold indexE at hd; split at hd
    · simp only [Option.map_eq_some_iff] at hd; obtain ⟨_, _, rfl⟩ := hd; rfl
    · cases hd
  | .deref _ _ => hor _
end

end GoFV.Proof.Pass.Rewrite

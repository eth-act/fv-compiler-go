import GoFV.Proof.Pass.CSERel
import GoFV.Proof.Pass.CSEComm
import GoFV.Proof.Eval
import GoFV.Proof.Frame

/-!
# cse: evaluating related values

`argVals fr as`: the registers of the arguments `as` (all defined). `evalValue_of_argVals`:
a value evaluates as its op on those. `evalValue_rel`: a value of `g` whose argument registers
are those of its source in `f` (the first two possibly swapped, for a commutative op) evaluates
alike (`evalOp_swap`). `evalOp_ok_same`: two values with the same op, aux and auxint that both
evaluate on the same arguments give the same result (the IDs only appear in error messages);
`LocalAddr` ignores its arguments, `NilCheck` returns its first.
-/

namespace GoFV.Proof.CSE

open GoFV.SSA GoFV.SSA.Sem

/-- The registers of the arguments `as`, if all are defined. -/
def argVals (fr : Frame) (as : Array ID) : Option (List Val) :=
  as.toList.mapM fun a => (fr.regs[a]?).join

theorem mapM_res_ofOption {m : ID → String} {r : ID → Option Val} :
    ∀ {l : List ID} {vs : List Val}, l.mapM r = some vs →
      l.mapM (fun a => Res.ofOption (m a) (r a)) = .ok vs
  | [], vs, h => by simp at h; subst h; rfl
  | a :: l, vs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨y, hy, ys, hys, rfl⟩ := h
    rw [List.mapM_cons, hy, mapM_res_ofOption hys]
    rfl

theorem mapM_some_of_forall {r : ID → Option Val} :
    ∀ {l : List ID}, (∀ a ∈ l, ∃ y, r a = some y) → ∃ vs, l.mapM r = some vs
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨y, hy⟩ := h a List.mem_cons_self
    obtain ⟨vs, hvs⟩ := mapM_some_of_forall (l := l) fun b hb => h b (List.mem_cons_of_mem _ hb)
    exact ⟨y :: vs, by simp [List.mapM_cons, hy, hvs]⟩

theorem argVals_some {fr : Frame} {as : Array ID}
    (h : ∀ a ∈ as, ∃ y, fr.regs[a]? = some (some y)) : ∃ vs, argVals fr as = some vs :=
  mapM_some_of_forall fun a ha => by
    obtain ⟨y, hy⟩ := h a (Array.mem_toList_iff.1 ha)
    exact ⟨y, by simp [hy]⟩

/-- A value evaluates as its op on its argument registers. -/
theorem evalValue_of_argVals {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {vs : List Val}
    (h : argVals fr v.args = some vs) :
    evalValue env ctx fr v =
      (evalOp env ctx fr v vs (ctx.tys[v.id]?.getD .other)).bind
        fun r => .ok (r.retype (ctx.tys[v.id]?.getD .other)) := by
  unfold evalValue
  rw [mapM_res_ofOption h]
  rfl

/-- A value that does not get stuck has all its argument registers. -/
theorem argVals_of_eval {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    (h : ∀ msg, evalValue env ctx fr v ≠ .stuck msg) : ∃ vs, argVals fr v.args = some vs :=
  argVals_some (evalValue_args_def h)

theorem argVals_eq {fr fr' : Frame} {as as' : Array ID} (hsz : as'.size = as.size)
    (h : ∀ (k : Nat) a, as[k]? = some a → ∃ a' y, as'[k]? = some a' ∧
      fr.regs[a]? = some (some y) ∧ fr'.regs[a']? = some (some y)) :
    argVals fr' as' = argVals fr as := by
  unfold argVals
  have key : ∀ (l l' : List ID), l.length = l'.length →
      (∀ (k : Nat) a, l[k]? = some a → ∃ a' y, l'[k]? = some a' ∧
        fr.regs[a]? = some (some y) ∧ fr'.regs[a']? = some (some y)) →
      l'.mapM (fun a => (fr'.regs[a]?).join) = l.mapM (fun a => (fr.regs[a]?).join) := by
    intro l
    induction l with
    | nil => intro l' hl _; cases l' with
      | nil => rfl
      | cons _ _ => simp at hl
    | cons a l ih =>
      intro l' hl hk
      cases l' with
      | nil => simp at hl
      | cons a' l' =>
        obtain ⟨b, y, hb, hy, hy'⟩ := hk 0 a rfl
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
        subst hb
        rw [List.mapM_cons, List.mapM_cons, ih l' (by simpa using hl)
          (fun k x hx => hk (k + 1) x (by simpa using hx))]
        simp [hy, hy']
  exact key as.toList as'.toList (by simp [hsz]) (fun k a ha => by
    obtain ⟨a', y, h1, h2, h3⟩ := h k a (by simpa using ha)
    exact ⟨a', y, by simpa using h1, h2, h3⟩)

theorem argVals_swap {fr : Frame} {as : Array ID} {a b : Val} {rest : List Val}
    (h : argVals fr as = some (a :: b :: rest)) :
    argVals fr (as.swapIfInBounds 0 1) = some (b :: a :: rest) := by
  unfold argVals at h ⊢
  rcases as with ⟨l⟩
  match l, h with
  | x :: y :: l, h =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨a', ha, l1, ⟨b', hb, l2, hl2, rfl⟩, he⟩ := h
    simp only [List.cons.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    have : (List.toArray (x :: y :: l)).swapIfInBounds 0 1 = List.toArray (y :: x :: l) := by
      simp [Array.swapIfInBounds, Array.swap]
    rw [this]
    simp [List.mapM_cons, ha, hb, hl2]
  | [], h => simp at h
  | [x], h =>
    simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨_, _, _, rfl, he⟩ := h
    simp at he

/-- A value of `g` whose argument registers (in `T`) are its source's in `f` (in `S`), the first
two possibly swapped for a commutative op, evaluates alike. -/
theorem evalValue_rel {env : Env} {ctxF ctxG : Ctx} {S T : Frame} {fv gv : Value}
    (hop : gv.op = fv.op) (hax : gv.aux = fv.aux) (hai : gv.auxInt = fv.auxInt)
    (hid : gv.id = fv.id) (hty : ctxG.tys[gv.id]? = ctxF.tys[fv.id]?)
    (htabs : ctxG.tabs = ctxF.tabs) (hpar : ctxG.params = ctxF.params) (hact : ctxG.act = ctxF.act)
    (hfr : T = { S with regs := T.regs }) {vs : List Val} (hS : argVals S fv.args = some vs)
    (hT : argVals T gv.args = some vs ∨ (fv.op.commutative = true ∧
      ∃ a b rest, vs = a :: b :: rest ∧ argVals T gv.args = some (b :: a :: rest))) :
    evalValue env ctxG T gv = evalValue env ctxF S fv := by
  have hc : ∀ argv ty, evalOp env ctxG T gv argv ty = evalOp env ctxF S fv argv ty :=
    fun argv ty => by rw [hfr, evalOp_frame, evalOp_congr hop hax hai hid htabs hpar hact]
  rcases hT with hT | ⟨hcomm, a, b, rest, rfl, hT⟩
  · rw [evalValue_of_argVals hT, evalValue_of_argVals hS, hty, hc]
  · rw [evalValue_of_argVals hT, evalValue_of_argVals hS, hty, hc, evalOp_swap hcomm]

/-- The argument registers of `g`'s version of a value, when each source argument's
representative holds the source argument's register. -/
theorem argVals_rel {S T : Frame} {rw : Array (Option ID)} {op : Op} {fa ga : Array ID}
    (hrel : ArgsRel rw op fa ga)
    (h : ∀ a ∈ fa, ∃ y, S.regs[a]? = some (some y) ∧ T.regs[GoFV.Opt.CSE.rep rw a]? = some (some y)) :
    ∃ vs, argVals S fa = some vs ∧ (argVals T ga = some vs ∨ (op.commutative = true ∧
      ∃ a b rest, vs = a :: b :: rest ∧ argVals T ga = some (b :: a :: rest))) := by
  obtain ⟨vs, hvs⟩ := argVals_some (fr := S) (as := fa) fun a ha => by
    obtain ⟨y, hy, -⟩ := h a ha; exact ⟨y, hy⟩
  have hmap : ∀ (as : Array ID), (∀ a ∈ as, a ∈ fa) →
      argVals T (as.map (GoFV.Opt.CSE.rep rw)) = argVals S as := fun as hsub =>
    argVals_eq (by simp) fun k a ha => by
      obtain ⟨y, hy, hy'⟩ := h a (hsub a (Array.mem_of_getElem? ha))
      exact ⟨GoFV.Opt.CSE.rep rw a, y, by simp [ha], hy, hy'⟩
  refine ⟨vs, hvs, ?_⟩
  rcases hrel with rfl | ⟨hc, hsz, rfl⟩
  · left; rw [hmap fa fun a ha => ha, hvs]
  · right
    refine ⟨hc, ?_⟩
    rcases fa with ⟨l⟩
    match l, hsz, hvs, hmap with
    | x :: y :: l, _, hvs, hmap =>
      have hsw : (List.toArray (x :: y :: l)).swapIfInBounds 0 1 = List.toArray (y :: x :: l) := by
        simp [Array.swapIfInBounds, Array.swap]
      rw [hsw, hmap _ fun a ha => by
        simp only [List.mem_toArray, List.mem_cons] at ha ⊢
        rcases ha with h | h | h <;> simp [h]]
      unfold argVals at hvs
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at hvs
      obtain ⟨a, ha, l1, ⟨b, hb, l2, hl2, rfl⟩, rfl⟩ := hvs
      exact ⟨a, b, l2, rfl, by unfold argVals; simp [List.mapM_cons, ha, hb, hl2]⟩
    | [], h0, _, _ | [_], h0, _, _ => simp at h0

end GoFV.Proof.CSE

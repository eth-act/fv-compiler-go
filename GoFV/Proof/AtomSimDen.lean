import GoFV.Proof.Term
import GoFV.Proof.Sim
import GoFV.Proof.Eval

/-!
# Registers as terms over the atoms (issue #113)

`DenOK D tabs fr V`: every value of `V` has a register in `fr`, and for every valuation `ρ`
that agrees with the registers on the atoms of `V` (`¬ IsTerm D`), `den D tabs ρ n x` is the
register of `x` for all large `n`. It holds of the empty set and is kept by evaluating a value
whose arguments (if it is a term node) are in `V` (`denOK_step`, `denOK_evalAll`), by adding
atoms (`DenOK.extend`) and by restriction to a set closed under the arguments of term nodes
(`DenOK.restrict`). `den_fuel_mono`: `den` is a refinement chain in the fuel.
-/

namespace GoFV.Proof.AtomSim

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck GoFV.Proof.Term

/-- The register of `a` (`poison` if none). -/
def rv (fr : Frame) (a : ID) : Val := (fr.regs[a]?).join.getD .poison

theorem rv_of {fr : Frame} {a : ID} {y : Val} (h : fr.regs[a]? = some (some y)) : rv fr a = y := by
  simp [rv, h]

/-- `a` has a register. -/
def Reg (fr : Frame) (a : ID) : Prop := ∃ y, fr.regs[a]? = some (some y)

theorem reg_rv {fr : Frame} {a : ID} (h : Reg fr a) : fr.regs[a]? = some (some (rv fr a)) := by
  obtain ⟨y, hy⟩ := h; rw [rv_of hy]; exact hy

/-- `V` contains the arguments of its term nodes. -/
def Closed (D : ID → Option Value) (V : ID → Prop) : Prop :=
  ∀ x, V x → ∀ v, D x = some v → termOp v.op = true → ∀ a ∈ v.args, V a

/-- The registers of `V` are the terms' values over the atoms' registers. -/
def DenOK (D : ID → Option Value) (tabs : Tables) (fr : Frame) (V : ID → Prop) : Prop :=
  ∀ x, V x → Reg fr x ∧
    ∀ ρ : ID → Val, (∀ a, V a → ¬ IsTerm D a → ρ a = rv fr a) →
      ∃ N, ∀ n, N ≤ n → den D tabs ρ n x = rv fr x

/-! ## `den` -/

theorem den_succ_term {D : ID → Option Value} {tabs : Tables} {ρ : ID → Val} {n : Nat} {x : ID}
    {v : Value} (hx : D x = some v) (ht : termOp v.op = true) :
    den D tabs ρ (n + 1) x = (GoFV.Proof.Rules.opVal tabs v.op (tabs.ty v.type) v.auxInt v.aux
      (v.args.toList.map (den D tabs ρ n))).retype (tabs.ty v.type) := by
  simp only [den, hx, ht, ite_true]

theorem den_succ_atom {D : ID → Option Value} {tabs : Tables} {ρ : ID → Val} {n : Nat} {x : ID}
    (hx : ¬ IsTerm D x) : den D tabs ρ (n + 1) x = ρ x := by
  cases h : D x with
  | none => simp only [den, h]
  | some v =>
    have ht : termOp v.op = false := by
      cases hv : termOp v.op
      · rfl
      · exact absurd ⟨v, h, hv⟩ hx
    simp only [den, h, ht, Bool.false_eq_true, ite_false]

theorem refinesList_map {α : Type} {f g : α → Val} :
    ∀ {l : List α}, (∀ a ∈ l, Sem.Refines (f a) (g a)) → RefinesList (l.map f) (l.map g)
  | [], _ => .nil
  | a :: _, h => .cons (h a List.mem_cons_self)
      (refinesList_map fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- `den` is a refinement chain in the fuel. -/
theorem den_fuel_mono (D : ID → Option Value) (tabs : Tables) (ρ : ID → Val) :
    ∀ (n m : Nat) (x : ID), n ≤ m → Sem.Refines (den D tabs ρ n x) (den D tabs ρ m x)
  | 0, _, _, _ => .poison _
  | n + 1, 0, _, h => absurd h (by omega)
  | n + 1, m + 1, x, h => by
    by_cases ht : IsTerm D x
    · obtain ⟨v, hx, hv⟩ := ht
      rw [den_succ_term hx hv, den_succ_term hx hv]
      exact retype_mono _ (GoFV.Proof.Rules.opVal_mono _ _ _ _ _
        (refinesList_map fun a _ => den_fuel_mono D tabs ρ n m a (by omega)))
    · rw [den_succ_atom ht, den_succ_atom ht]; exact Sem.Refines.refl _

/-- `den` reads the valuation only at the atoms reached through term nodes. -/
theorem den_congr {D : ID → Option Value} {tabs : Tables} {C : ID → Prop} (hC : Closed D C)
    {ρ1 ρ2 : ID → Val} (h : ∀ a, C a → ¬ IsTerm D a → ρ1 a = ρ2 a) :
    ∀ (n : Nat) (x : ID), C x → den D tabs ρ1 n x = den D tabs ρ2 n x
  | 0, _, _ => rfl
  | n + 1, x, hx => by
    by_cases ht : IsTerm D x
    · obtain ⟨v, hv, hop⟩ := ht
      rw [den_succ_term hv hop, den_succ_term hv hop]
      rw [List.map_congr_left (fun a ha =>
        den_congr hC h n a (hC x hx v hv hop a (Array.mem_toList_iff.1 ha)))]
    · rw [den_succ_atom ht, den_succ_atom ht]; exact h x hx ht

/-! ## `DenOK` -/

theorem denOK_empty (D : ID → Option Value) (tabs : Tables) (fr : Frame) :
    DenOK D tabs fr (fun _ => False) := fun _ h => h.elim

theorem DenOK.iff {D : ID → Option Value} {tabs : Tables} {fr : Frame} {V W : ID → Prop}
    (h : DenOK D tabs fr V) (hVW : ∀ x, V x ↔ W x) : DenOK D tabs fr W := by
  intro x hx
  refine ⟨(h x ((hVW x).2 hx)).1, fun ρ hρ => ?_⟩
  exact (h x ((hVW x).2 hx)).2 ρ fun a ha hat => hρ a ((hVW a).1 ha) hat

theorem DenOK.restrict {D : ID → Option Value} {tabs : Tables} {fr : Frame} {V W : ID → Prop}
    (h : DenOK D tabs fr V) (hWV : ∀ x, W x → V x) (hW : Closed D W) : DenOK D tabs fr W := by
  classical
  intro x hx
  refine ⟨(h x (hWV x hx)).1, fun ρ hρ => ?_⟩
  let ρ2 : ID → Val := fun a => if V a ∧ ¬ IsTerm D a then rv fr a else ρ a
  obtain ⟨N, hN⟩ := (h x (hWV x hx)).2 ρ2 (fun a ha hat => by simp [ρ2, ha, hat])
  refine ⟨N, fun n hn => ?_⟩
  rw [← hN n hn]
  exact den_congr hW (fun a ha hat => by simp [ρ2, hWV a ha, hat, hρ a ha hat]) n x hx

/-- Adding atoms with registers, the registers of `V` unchanged. -/
theorem DenOK.extend {D : ID → Option Value} {tabs : Tables} {fr fr' : Frame} {V W : ID → Prop}
    (h : DenOK D tabs fr V) (hk : ∀ a, V a → fr'.regs[a]? = fr.regs[a]?)
    (hW : ∀ x, W x → ¬ V x → ¬ IsTerm D x ∧ Reg fr' x) :
    DenOK D tabs fr' (fun a => V a ∨ W a) := by
  intro x hx
  by_cases hv : V x
  · obtain ⟨⟨y, hy⟩, hd⟩ := h x hv
    refine ⟨⟨y, by rw [hk x hv]; exact hy⟩, fun ρ hρ => ?_⟩
    obtain ⟨N, hN⟩ := hd ρ (fun a ha hat => by rw [hρ a (.inl ha) hat]; unfold rv; rw [hk a ha])
    exact ⟨N, fun n hn => by rw [hN n hn]; unfold rv; rw [hk x hv]⟩
  · have hw : W x := hx.resolve_left hv
    obtain ⟨hat, hr⟩ := hW x hw hv
    refine ⟨hr, fun ρ hρ => ⟨1, fun n hn => ?_⟩⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [den_succ_atom hat]; exact hρ x hx hat

theorem DenOK.list {D : ID → Option Value} {tabs : Tables} {fr : Frame} {V : ID → Prop}
    (h : DenOK D tabs fr V) {ρ : ID → Val} (hρ : ∀ a, V a → ¬ IsTerm D a → ρ a = rv fr a) :
    ∀ {l : List ID}, (∀ a ∈ l, V a) →
      ∃ N, ∀ n, N ≤ n → l.map (den D tabs ρ n) = l.map (rv fr)
  | [], _ => ⟨0, fun _ _ => rfl⟩
  | a :: l, hl => by
    obtain ⟨N1, h1⟩ := (h a (hl a List.mem_cons_self)).2 ρ hρ
    obtain ⟨N2, h2⟩ := DenOK.list h hρ (l := l) fun b hb => hl b (List.mem_cons_of_mem _ hb)
    refine ⟨max N1 N2, fun n hn => ?_⟩
    rw [List.map_cons, List.map_cons, h1 n (by omega), h2 n (by omega)]

/-- Adding a term node whose arguments are in `V`, with its value over their registers. -/
theorem DenOK.term {D : ID → Option Value} {tabs : Tables} {fr fr' : Frame} {V : ID → Prop}
    {x : ID} {v : Value} (h : DenOK D tabs fr V) (hk : ∀ a, V a → fr'.regs[a]? = fr.regs[a]?)
    (hxV : ¬ V x) (hx : D x = some v) (ht : termOp v.op = true) (hargs : ∀ a ∈ v.args, V a)
    (hreg : fr'.regs[x]? = some (some ((GoFV.Proof.Rules.opVal tabs v.op (tabs.ty v.type) v.auxInt v.aux
      (v.args.toList.map (rv fr))).retype (tabs.ty v.type)))) :
    DenOK D tabs fr' (fun a => V a ∨ a = x) := by
  intro z hz
  by_cases hv : V z
  · obtain ⟨⟨y, hy⟩, hd⟩ := h z hv
    refine ⟨⟨y, by rw [hk z hv]; exact hy⟩, fun ρ hρ => ?_⟩
    obtain ⟨N, hN⟩ := hd ρ (fun a ha hat => by rw [hρ a (.inl ha) hat]; unfold rv; rw [hk a ha])
    exact ⟨N, fun n hn => by rw [hN n hn]; unfold rv; rw [hk z hv]⟩
  · have hzx : z = x := hz.resolve_left hv
    subst hzx
    refine ⟨⟨_, hreg⟩, fun ρ hρ => ?_⟩
    have hρ' : ∀ a, V a → ¬ IsTerm D a → ρ a = rv fr a := fun a ha hat => by
      rw [hρ a (.inl ha) hat]; unfold rv; rw [hk a ha]
    obtain ⟨N, hN⟩ := DenOK.list h hρ' (l := v.args.toList)
      fun a ha => hargs a (Array.mem_toList_iff.1 ha)
    refine ⟨N + 1, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [den_succ_term hx ht, hN k (by omega), rv_of hreg]

/-! ## Evaluating values -/

theorem mapM_regs {m : ID → String} {fr : Frame} :
    ∀ {l : List ID}, (∀ a ∈ l, Reg fr a) →
      l.mapM (fun a => Res.ofOption (m a) (fr.regs[a]?).join) = .ok (l.map (rv fr))
  | [], _ => rfl
  | a :: l, h => by
    rw [List.mapM_cons, reg_rv (h a List.mem_cons_self)]
    simp only [Option.join, Option.bind_some, id, Res.ofOption]
    change Res.bind (List.mapM (fun a => Res.ofOption (m a) (fr.regs[a]?).join) l) _ = _
    rw [mapM_regs fun b hb => h b (List.mem_cons_of_mem _ hb)]
    rfl

/-- A value whose arguments have registers: its op on their registers, retyped. -/
theorem evalValue_of_regs {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    (h : ∀ a ∈ v.args, Reg fr a) :
    evalValue env ctx fr v = (evalOp env ctx fr v (v.args.toList.map (rv fr))
      (ctx.tys[v.id]?.getD .other)).bind (fun r => .ok (r.retype (ctx.tys[v.id]?.getD .other))) := by
  unfold evalValue
  rw [mapM_regs fun a ha => h a (Array.mem_toList_iff.1 ha)]
  rfl

theorem regs_of_ok {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {y : Val}
    (h : evalValue env ctx fr v = .ok y) : ∀ a ∈ v.args, Reg fr a :=
  evalValue_args_def fun msg hm => by rw [h] at hm; cases hm

theorem regs_of_panic {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {e : Panic} {m : Mem}
    (h : evalValue env ctx fr v = .panic e m) : ∀ a ∈ v.args, Reg fr a :=
  evalValue_args_def fun msg hm => by rw [h] at hm; cases hm

/-- `Addr`/`ConstString` are frame values the tables determine. -/
theorem frameVal_tab {ctx : Ctx} {v : Value} (ty : Ty) (argv : List Val)
    (h : v.op = .Addr ∨ v.op = .ConstString) :
    frameVal ctx v = some (GoFV.Proof.Rules.opVal ctx.tabs v.op ty v.auxInt v.aux argv) := by
  rcases h with h | h
  · unfold frameVal; rw [h, GoFV.Proof.Rules.opVal_addr]; unfold GoFV.Proof.Rules.addrVal
    dsimp only
    generalize v.aux.bind ctx.tabs.aux? = o
    rcases o with _ | ⟨fmt, kind⟩
    · rfl
    · cases kind <;> rfl
  · unfold frameVal; rw [h, GoFV.Proof.Rules.opVal_constString]; unfold GoFV.Proof.Rules.strVal
    dsimp only
    generalize v.aux.bind ctx.tabs.aux? = o
    rcases o with _ | ⟨fmt, kind⟩
    · rfl
    · cases kind <;> rfl

/-- A term node evaluates by `opVal`: `evalPure`, or the tables for `Addr`/`ConstString`. -/
theorem evalOp_term {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val} {ty : Ty}
    (ht : termOp v.op = true) :
    evalOp env ctx fr v argv ty = .ok (GoFV.Proof.Rules.opVal ctx.tabs v.op ty v.auxInt v.aux argv) := by
  have hr : isRoot v.op = false := by
    unfold termOp at ht
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at ht
    exact ht.1
  by_cases hfr : v.op = .Addr ∨ v.op = .ConstString
  · have hf := frameVal_tab (ctx := ctx) ty argv hfr
    unfold evalOp
    split <;> first
      | (rename_i h; rw [h] at ht; exact absurd ht (by decide))
      | (rw [hf]; rfl)
  · have hf : frameVal ctx v = none := by
      unfold frameVal
      split <;> first
        | rfl
        | (rename_i h; rw [h] at ht; exact absurd ht (by decide))
        | (rename_i h; exact (hfr (.inl h)).elim)
        | (rename_i h; exact (hfr (.inr h)).elim)
    have hp : GoFV.Proof.Rules.frameOp v.op = false := by
      unfold GoFV.Proof.Rules.frameOp
      cases h1 : v.op == .Addr <;> cases h2 : v.op == .ConstString <;> simp_all
    rw [GoFV.Proof.Rules.opVal_pure hp]
    unfold evalOp
    split <;> first
      | (rename_i h; rw [h] at ht; exact absurd ht (by decide))
      | (rw [hf]; simp only [hr, Bool.false_eq_true, ite_false]; rfl)

theorem evalValue_term {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {y : Val}
    (ht : termOp v.op = true) (h : evalValue env ctx fr v = .ok y) :
    y = (GoFV.Proof.Rules.opVal ctx.tabs v.op (ctx.tys[v.id]?.getD .other) v.auxInt v.aux
      (v.args.toList.map (rv fr))).retype (ctx.tys[v.id]?.getD .other) := by
  rw [evalValue_of_regs (regs_of_ok h), evalOp_term ht] at h
  cases h; rfl

/-! ## Evaluating a list of values -/

theorem refOK_of_topo {D : ID → List ID} :
    ∀ {L : List ID} {V : ID → Prop}, TopoRem D L → (∀ x ∈ L, ∀ a ∈ D x, V a ∨ a ∈ L) →
      RefOK D V L
  | [], _, _, _ => trivial
  | x :: s, V, ⟨hx, hs⟩, h => by
    refine ⟨fun a ha => (h x List.mem_cons_self a ha).resolve_right (hx a ha),
      refOK_of_topo hs fun y hy a ha => ?_⟩
    rcases h y (List.mem_cons_of_mem _ hy) a ha with h1 | h1
    · exact .inl (.inl h1)
    · rcases List.mem_cons.1 h1 with rfl | h1
      · exact .inl (.inr rfl)
      · exact .inr h1

end GoFV.Proof.AtomSim

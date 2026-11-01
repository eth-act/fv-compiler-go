import GoFV.Proof.Merge
import GoFV.Proof.Enter

/-!
# Evaluating a list of values against expected results

`evalAll_map`: the target evaluates its list `o` (a dependency order) from a frame `PT`; each
listed value `x` may have an expected result `exp x` (`none`: any result). If each value, in a
frame of `PT`'s activation whose registers outside `O` (the list's values) are `PT`'s and whose
listed arguments hold their expected results, evaluates (to its expected result), the whole
evaluation succeeds, every listed value holding its expected result. `evalAll_map_panic`: the
same up to a value that panics. Unlike `evalAll_ref`/`evalAll_mix`, the expected results are
not the target's own registers of a reference frame: the target's values may stand for other
values of the source (short circuit's renamed registers).
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

private theorem topoRem_suffix' {D : ID → List ID} :
    ∀ {L1 L2 : List ID}, TopoRem D (L1 ++ L2) → TopoRem D L2
  | [], _, h => h
  | _ :: L1, _, ⟨_, h2⟩ => topoRem_suffix' (L1 := L1) h2

/-- The registers of `g`: outside `O` those of `PT`; in `D` defined with their expected results. -/
def MapInv (PT : Frame) (O D : ID → Prop) (exp : ID → Option Val) (g : Frame) : Prop :=
  g = { PT with regs := g.regs } ∧ g.regs.size = PT.regs.size ∧
    (∀ a, D a → ∃ z, g.regs[a]? = some (some z) ∧ ∀ y, exp a = some y → z = y) ∧
    (∀ a, ¬ D a → g.regs[a]? = PT.regs[a]?)

/-- Value `x` evaluates, to its expected result, in every frame of `PT`'s activation that holds
`PT`'s registers outside `O` and the expected results of its arguments in `O`. -/
def MapLoc (env : Env) (ctx : Ctx) (PT : Frame) (O : ID → Prop) (exp : ID → Option Val)
    (x : ID) : Prop :=
  ∀ g : Frame, g = { PT with regs := g.regs } →
    (∀ a ∈ argsF ctx.f x, ¬ O a → g.regs[a]? = PT.regs[a]?) →
    (∀ a ∈ argsF ctx.f x, O a → ∃ z, g.regs[a]? = some (some z) ∧ ∀ y, exp a = some y → z = y) →
    ∃ y, stepV env ctx g x = .ok y ∧ ∀ y', exp x = some y' → y = y'

theorem evalAll_map {env : Env} {ctx : Ctx} {PT : Frame} {O : ID → Prop} {exp : ID → Option Val}
    (hPs : PT.regs.size = ctx.f.valueTab.size) :
    ∀ {rest : List ID} {D : ID → Prop} {g : Frame}, rest.Nodup → TopoRem (argsF ctx.f) rest →
      (∀ x ∈ rest, ¬ D x ∧ O x ∧ MapLoc env ctx PT O exp x) →
      (∀ x ∈ rest, ∀ a ∈ argsF ctx.f x, O a → D a ∨ a ∈ rest) → (∀ a, D a → O a) →
      MapInv PT O D exp g →
      ∃ g', evalAll env ctx g rest = .ok g' ∧ MapInv PT O (fun a => D a ∨ a ∈ rest) exp g'
  | [], D, g, _, _, _, _, _, hI => by
    refine ⟨g, rfl, ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := hI
    exact ⟨h1, h2, fun a ha => h3 a (ha.elim id (fun h => absurd h List.not_mem_nil)),
      fun a ha => h4 a fun h => ha (.inl h)⟩
  | x :: s, D, g, hnd, ⟨htx, hts⟩, hloc, hO, hDO, ⟨hg, hgs, hD, hnD⟩ => by
    obtain ⟨hxD, hxO, hxl⟩ := hloc x List.mem_cons_self
    obtain ⟨y, hxs, hxe⟩ := hxl g hg
      (fun a _ hOa => hnD a fun hDa => hOa (hDO a hDa))
      (fun a ha hOa => by
        rcases hO x List.mem_cons_self a ha hOa with hDa | hm
        · exact hD a hDa
        · exact absurd hm (htx a ha))
    have hxlt : x < g.regs.size := by rw [hgs, hPs]; exact stepV_lt hxs
    rw [evalAll_cons, hxs]
    have hxs' : x ∉ s := (List.nodup_cons.1 hnd).1
    have hI' : MapInv PT O (fun a => D a ∨ a = x) exp (g.set x y) := by
      refine ⟨by rw [hg]; rfl, by simp [Frame.set, hgs], fun a ha => ?_, fun a ha => ?_⟩
      · rcases ha with ha | rfl
        · by_cases hxa : x = a
          · subst hxa; exact absurd ha hxD
          · rw [Frame.set_regs_ne hxa]; exact hD a ha
        · exact ⟨y, Frame.set_regs_self hxlt, hxe⟩
      · have hxa : x ≠ a := fun he => ha (.inr he.symm)
        rw [Frame.set_regs_ne hxa]; exact hnD a fun h => ha (.inl h)
    obtain ⟨g', h1, h2⟩ := evalAll_map hPs (D := fun a => D a ∨ a = x) (g := g.set x y)
      (List.nodup_cons.1 hnd).2 hts
      (fun z hz => ⟨fun h => h.elim (hloc z (List.mem_cons_of_mem _ hz)).1
          (fun he => hxs' (he ▸ hz)), (hloc z (List.mem_cons_of_mem _ hz)).2⟩)
      (fun z hz a ha hOa => by
        rcases hO z (List.mem_cons_of_mem _ hz) a ha hOa with hDa | hm
        · exact .inl (.inl hDa)
        · rcases List.mem_cons.1 hm with rfl | hm
          · exact .inl (.inr rfl)
          · exact .inr hm)
      (fun a ha => ha.elim (hDO a) (fun he => he ▸ hxO)) hI'
    refine ⟨g', h1, ?_⟩
    obtain ⟨k1, k2, k3, k4⟩ := h2
    refine ⟨k1, k2, fun a ha => k3 a ?_, fun a ha => k4 a ?_⟩
    · rcases ha with ha | ha
      · exact .inl (.inl ha)
      · rcases List.mem_cons.1 ha with rfl | ha
        · exact .inl (.inr rfl)
        · exact .inr ha
    · rintro ((h | h) | h)
      · exact ha (.inl h)
      · exact ha (.inr (h ▸ List.mem_cons_self))
      · exact ha (.inr (List.mem_cons_of_mem _ h))

/-- **Evaluation up to a panicking value**: `evalAll_map` on the values before it, then the
value panics. -/
theorem evalAll_map_panic {env : Env} {ctx : Ctx} {PT : Frame} {O : ID → Prop}
    {exp : ID → Option Val} (hPs : PT.regs.size = ctx.f.valueTab.size) {pre post : List ID}
    {r : ID} {e : Panic} {m : Mem} (hnd : (pre ++ r :: post).Nodup)
    (ht : TopoRem (argsF ctx.f) (pre ++ r :: post))
    (hloc : ∀ x ∈ pre, O x ∧ MapLoc env ctx PT O exp x)
    (hO : ∀ a, O a → a ∈ pre ++ r :: post)
    (hr : ∀ g : Frame, g = { PT with regs := g.regs } →
      (∀ a ∈ argsF ctx.f r, ¬ O a → g.regs[a]? = PT.regs[a]?) →
      (∀ a ∈ argsF ctx.f r, O a → ∃ z, g.regs[a]? = some (some z) ∧
        ∀ y, exp a = some y → z = y) →
      stepV env ctx g r = .panic e m) :
    evalAll env ctx PT (pre ++ r :: post) = .panic e m := by
  have hnd1 : pre.Nodup := (List.nodup_append.1 hnd).1
  have ht1 : TopoRem (argsF ctx.f) pre := topoRem_prefix ht
  obtain ⟨g', h1, k1, k2, k3, k4⟩ := evalAll_map (D := fun _ => False) (g := PT) hPs hnd1 ht1
    (fun x hx => ⟨id, hloc x hx⟩)
    (fun x hx a ha hOa => .inr (topoRem_arg_prefix ht x hx a ha (hO a hOa)))
    (fun _ h => h.elim) ⟨rfl, rfl, fun _ h => h.elim, fun _ _ => rfl⟩
  rw [evalAll_append, h1]
  show evalAll env ctx g' (r :: post) = _
  have htr : TopoRem (argsF ctx.f) (r :: post) := topoRem_suffix' ht
  rw [evalAll_cons, hr g' k1 (fun a _ hOa => k4 a fun h => h.elim (fun h => h) fun hm =>
      hOa (hloc a hm).1) (fun a ha hOa => ?_)]
  have hpre : a ∈ pre := by
    rcases List.mem_append.1 (hO a hOa) with h | h
    · exact h
    · exact absurd h (htr.1 a ha)
  exact k3 a (.inr hpre)

end GoFV.Proof

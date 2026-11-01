import GoFV.Proof.Sim

/-!
# Evaluation against a reference frame, with free values

`evalAll_mix` generalises `evalAll_ref` to target blocks that evaluate values the source run
did not (speculated values: branchelim's arms, a fused comparison's operand). The values of a
set `F` are *free*: the reference frame `G` (the source's) does not fix their results; each
must merely evaluate wherever its arguments have values. Every other listed value yields its
`G` register in a frame that agrees with `G` on its non-free arguments and has all its
arguments (`MixOK`). The target's `evalAll` then succeeds, agreeing with `G` outside `F` and
defining every listed value. `evalAll_mix_panic`: a value panicking as the reference says
makes the target panic alike, after an evaluated prefix.
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

/-- See the module doc. -/
def MixOK (env : Env) (ctx : Ctx) (G : Frame) (F : ID → Prop) (o : List ID) : Prop :=
  ∀ x ∈ o,
    (¬ F x → ∃ y, G.regs[x]? = some (some y) ∧ ∀ g : Frame, g = { G with regs := g.regs } →
      (∀ a ∈ argsF ctx.f x, ¬ F a → g.regs[a]? = G.regs[a]?) →
      (∀ a ∈ argsF ctx.f x, ∃ z, g.regs[a]? = some (some z)) → stepV env ctx g x = .ok y) ∧
    (F x → ∀ g : Frame, g = { G with regs := g.regs } →
      (∀ a ∈ argsF ctx.f x, ∃ z, g.regs[a]? = some (some z)) → ∃ y, stepV env ctx g x = .ok y)

theorem MixOK.tail {env : Env} {ctx : Ctx} {G : Frame} {F : ID → Prop} {x : ID} {o : List ID}
    (h : MixOK env ctx G F (x :: o)) : MixOK env ctx G F o :=
  fun z hz => h z (List.mem_cons_of_mem _ hz)

theorem stepV_lt {env : Env} {ctx : Ctx} {g : Frame} {x : ID} {y : Val}
    (h : stepV env ctx g x = .ok y) : x < ctx.f.valueTab.size := by
  unfold stepV at h
  cases hv : ctx.f.value? x with
  | none => rw [hv] at h; cases h
  | some v => exact lt_of_value? hv

theorem evalAll_mix {env : Env} {ctx : Ctx} {G : Frame} {F : ID → Prop}
    (hGs : G.regs.size = ctx.f.valueTab.size) :
    ∀ {o : List ID} {S : ID → Prop} {g : Frame}, MixOK env ctx G F o →
      RefOK (argsF ctx.f) S o →
      (∀ a, S a → ¬ F a → g.regs[a]? = G.regs[a]?) →
      (∀ a, S a → ∃ z, g.regs[a]? = some (some z)) →
      g = { G with regs := g.regs } → g.regs.size = G.regs.size →
      ∃ g', evalAll env ctx g o = .ok g' ∧ g' = { G with regs := g'.regs } ∧
        g'.regs.size = G.regs.size ∧
        (∀ a, (S a ∨ a ∈ o) → ¬ F a → g'.regs[a]? = G.regs[a]?) ∧
        (∀ a, (S a ∨ a ∈ o) → ∃ z, g'.regs[a]? = some (some z)) ∧
        (∀ a, a ∉ o → g'.regs[a]? = g.regs[a]?)
  | [], _, g, _, _, hS, hSd, hg, hs =>
    ⟨g, rfl, hg, hs, fun a ha => ha.elim (hS a) (fun h => absurd h List.not_mem_nil),
      fun a ha => ha.elim (hSd a) (fun h => absurd h List.not_mem_nil), fun _ _ => rfl⟩
  | x :: s, S, g, hl, ⟨hx, hr⟩, hS, hSd, hg, hs => by
    have hdef : ∀ a ∈ argsF ctx.f x, ∃ z, g.regs[a]? = some (some z) := fun a ha => hSd a (hx a ha)
    -- the value of `x`
    obtain ⟨y, hxs, hfix⟩ : ∃ y, stepV env ctx g x = .ok y ∧ (¬ F x → G.regs[x]? = some (some y)) := by
      by_cases hF : F x
      · obtain ⟨y, hy⟩ := (hl x List.mem_cons_self).2 hF g hg hdef
        exact ⟨y, hy, fun h => absurd hF h⟩
      · obtain ⟨y, hGx, hstep⟩ := (hl x List.mem_cons_self).1 hF
        exact ⟨y, hstep g hg (fun a ha hFa => hS a (hx a ha) hFa) hdef, fun _ => hGx⟩
    have hxlt : x < g.regs.size := by rw [hs, hGs]; exact stepV_lt hxs
    rw [evalAll_cons, hxs]
    obtain ⟨g', h1, h2, h3, h4, h5, h6⟩ := evalAll_mix hGs (S := fun a => S a ∨ a = x)
      (g := g.set x y) hl.tail hr
      (fun a ha hFa => by
        rcases ha with ha | rfl
        · by_cases hax : x = a
          · subst hax; rw [Frame.set_regs_self hxlt, hfix hFa]
          · rw [Frame.set_regs_ne hax]; exact hS a ha hFa
        · rw [Frame.set_regs_self hxlt, hfix hFa])
      (fun a ha => by
        rcases ha with ha | rfl
        · by_cases hax : x = a
          · subst hax; exact ⟨y, Frame.set_regs_self hxlt⟩
          · rw [Frame.set_regs_ne hax]; exact hSd a ha
        · exact ⟨y, Frame.set_regs_self hxlt⟩)
      (by rw [hg]; rfl) (by simp [Frame.set, hs])
    have hlift : ∀ a, (S a ∨ a ∈ x :: s) → ((S a ∨ a = x) ∨ a ∈ s) := fun a ha => by
      rcases ha with ha | ha
      · exact .inl (.inl ha)
      · rcases List.mem_cons.1 ha with rfl | ha
        · exact .inl (.inr rfl)
        · exact .inr ha
    refine ⟨g', h1, h2, h3, fun a ha hFa => h4 a (hlift a ha) hFa,
      fun a ha => h5 a (hlift a ha), fun a ha => ?_⟩
    have has : a ∉ s := fun h => ha (List.mem_cons_of_mem _ h)
    have hxa : x ≠ a := fun h => ha (h ▸ List.mem_cons_self)
    rw [h6 a has, Frame.set_regs_ne hxa]

theorem evalAll_mix_panic {env : Env} {ctx : Ctx} {G : Frame} {F : ID → Prop}
    (hGs : G.regs.size = ctx.f.valueTab.size) {pre post : List ID} {r : ID}
    {S : ID → Prop} {g : Frame} {e : Panic} {m : Mem}
    (hl : MixOK env ctx G F pre) (href : RefOK (argsF ctx.f) S pre)
    (hS : ∀ a, S a → ¬ F a → g.regs[a]? = G.regs[a]?)
    (hSd : ∀ a, S a → ∃ z, g.regs[a]? = some (some z))
    (hg : g = { G with regs := g.regs }) (hs : g.regs.size = G.regs.size)
    (hrargs : ∀ a ∈ argsF ctx.f r, S a ∨ a ∈ pre)
    (hr : ∀ g' : Frame, g' = { G with regs := g'.regs } →
      (∀ a ∈ argsF ctx.f r, ¬ F a → g'.regs[a]? = G.regs[a]?) →
      (∀ a ∈ argsF ctx.f r, ∃ z, g'.regs[a]? = some (some z)) → stepV env ctx g' r = .panic e m) :
    evalAll env ctx g (pre ++ r :: post) = .panic e m := by
  obtain ⟨g', h1, h2, -, h4, h5, -⟩ := evalAll_mix hGs hl href hS hSd hg hs
  rw [evalAll_append, h1]
  show evalAll env ctx g' (r :: post) = _
  rw [evalAll_cons, hr g' h2 (fun a ha hFa => h4 a (hrargs a ha) hFa)
    (fun a ha => h5 a (hrargs a ha))]

end GoFV.Proof

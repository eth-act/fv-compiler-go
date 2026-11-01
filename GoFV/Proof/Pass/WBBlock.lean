import GoFV.Proof.Pass.WBRole

/-!
# writebarrier: the checker's block conditions as propositions (issue #36)

`blockOK_spec`, `runOK_spec`, `npOK_spec`, `keptNP_spec`: `Ctx.blockOK`, `Ctx.runOK`,
`Ctx.npOK` and `Ctx.keptNP` read as propositions; `availIn_spec`: an available argument.
-/

namespace GoFV.Proof.WB

open GoFV.SSA GoFV.Opt GoFV.Opt.WBCheck

/-- The dropped nil check of a run, as `npOK` lists it. -/
def ncsOf (c : WBCheck.Ctx) (r : Run) : List ID :=
  match r.nc with
  | some n => if c.K.getD n false then [] else [n]
  | none => []

section
variable {c : WBCheck.Ctx}

theorem availIn_spec {B : Block} {segs : List ID} {j : Nat} {a : ID}
    (h : c.availIn B segs j a = true) :
    c.held a = true ∧ (a ∈ B.values → ∃ s ∈ segs.take (j + 1), a ∈ vals c.g s) ∧
      (a ∉ B.values → ∃ y ∈ B.values, ∃ u, c.f.value? y = some u ∧ u.op ≠ .Phi ∧ a ∈ u.args) := by
  unfold Ctx.availIn at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hh, h2⟩ := h
  refine ⟨hh, fun ha => ?_, fun ha => ?_⟩
  · simp only [Array.contains_iff_mem.2 ha, ↓reduceIte] at h2
    obtain ⟨s, hs, hc⟩ := List.any_eq_true.1 h2
    exact ⟨s, hs, Array.contains_iff_mem.1 hc⟩
  · have hc : B.values.contains a = false := by
      cases hc : B.values.contains a
      · rfl
      · exact absurd (Array.contains_iff_mem.1 hc) ha
    simp only [hc, Bool.false_eq_true, ↓reduceIte] at h2
    unfold Ctx.srcArg at h2
    obtain ⟨y, hy, hu⟩ := Array.any_eq_true'.1 h2
    cases hv : c.f.value? y with
    | none => rw [hv] at hu; cases hu
    | some u =>
      rw [hv] at hu
      simp only [Option.any_some, Bool.and_eq_true, bne_iff_ne, ne_eq] at hu
      exact ⟨y, hy, u, hv, hu.1, Array.contains_iff_mem.1 hu.2⟩

theorem keptNP_spec {s : ID} {l : List ID} (h : c.keptNP s = some l) :
    ∃ C o, c.g.block? s = some C ∧ Sem.schedule c.g C = some o ∧
      l = (o.toList.filter (npOf c.g C)).filter (c.K.getD · false) := by
  simp only [Ctx.keptNP, Ctx.npSeq, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.map_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨C, hC, l', ⟨o, ho, rfl⟩, rfl⟩ := h
  exact ⟨C, o, hC, ho, rfl⟩

theorem npOK_spec {B : Block} {rs : List Run} {segs : List ID} (h : c.npOK B rs segs = true) :
    ∃ src k0 ks, Ctx.npSeq c.f B = some src ∧ segs.mapM c.keptNP = some (k0 :: ks) ∧
      src = k0 ++ (rs.zip ks).flatMap (fun p => ncsOf c p.1 ++ p.1.src ++ p.2) := by
  unfold Ctx.npOK at h
  split at h
  next src k0 ks hs hm =>
    refine ⟨src, k0, ks, hs, hm, ?_⟩
    rw [beq_iff_eq.1 h]
    congr 1
  next => cases h

theorem runOK_spec {b : ID} {B : Block} {segs : List ID} {rs : List Run} {j : Nat} {r : Run}
    (h : c.runOK b B segs rs j r = true) :
    segs[j]? = some r.sp.c ∧ segs[j + 1]? = some r.sp.e ∧
    (∃ T, c.g.block? r.sp.t = some T ∧ T.id = r.sp.t ∧ T.kind = .Plain ∧
      T.succs = #[⟨r.sp.e, 1⟩] ∧ (Ctx.npSeq c.g T).isSome ∧
      (∀ n, r.nc = some n → ∃ y ys, Ctx.npSeq c.g T = some (y :: ys) ∧ c.roleOf rs y = .ncThen j) ∧
      ∀ x ∈ T.values, c.roleOK b B segs rs true j x = true) ∧
    (∃ E, c.g.block? r.sp.e = some E ∧ E.id = r.sp.e ∧
      (∀ y, r.ncEnd = some y → ∃ ys, Ctx.npSeq c.g E = some (y :: ys)) ∧
      (r.ncEnd = none → r.nc = none)) ∧
    (∃ C, c.g.block? r.sp.c = some C ∧ C.id = r.sp.c) ∧
    r.src.length = r.tgt.length ∧ 0 < r.src.length ∧ r.last ∈ vals c.g r.sp.e ∧
    (∀ y ∈ r.tgt, y ∈ vals c.g r.sp.e) ∧ (∀ y, r.ncEnd = some y → y ∈ vals c.g r.sp.e) ∧
    r.sp.load ∈ vals c.g r.sp.c ∧ r.sp.flag ∈ vals c.g r.sp.c ∧ c.roleOf rs r.sp.flag = .flag j ∧
    c.held r.sp.mem = true ∧ (∀ y, r.ncEnd = some y → c.roleOf rs y = .ncEnd j) ∧
    (∀ x ∈ r.src, x ∈ B.values ∧ c.K.getD x false = false) ∧
    (∀ n, r.nc = some n → n ∈ B.values ∧ ∃ u, c.f.value? n = some u ∧ u.op = .NilCheck) := by
  unfold Ctx.runOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, hT⟩, hE⟩, hC⟩, hlen⟩, hpos⟩, hlast⟩, htgt⟩, hncE⟩, hload⟩, hflag⟩,
    hrole⟩, hmem⟩, hncR⟩, hsrc⟩, hnc⟩ := h
  refine ⟨h1, h2, ?_, ?_, ?_, hlen, hpos, Array.contains_iff_mem.1 hlast,
    fun y hy => Array.contains_iff_mem.1 (List.all_eq_true.1 htgt y hy),
    fun y hy => by rw [hy] at hncE; exact Array.contains_iff_mem.1 hncE,
    Array.contains_iff_mem.1 hload, Array.contains_iff_mem.1 hflag, hrole, hmem,
    fun y hy => by rw [hy] at hncR; simpa using hncR, ?_, ?_⟩
  · split at hT
    next T hT' =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hT
      obtain ⟨⟨⟨⟨hid, hk⟩, hs⟩, hM⟩, hall⟩ := hT
      refine ⟨T, hT', hid, hk, hs, ?_, ?_, fun x hx => Array.all_eq_true_iff_forall_mem.1 hall x hx⟩
      · rcases hn : r.nc with _ | n <;> rcases hq : Ctx.npSeq c.g T with _ | _ | ⟨y, ys⟩ <;>
          simp only [hn, hq, Bool.false_eq_true] at hM <;> simp
      · intro n hn
        rcases hq : Ctx.npSeq c.g T with _ | _ | ⟨y, ys⟩ <;> simp only [hn, hq] at hM
        · cases hM
        · cases hM
        · exact ⟨y, ys, rfl, beq_iff_eq.1 hM⟩
    next => cases hT
  · rcases hEb : c.g.block? r.sp.e with _ | E <;> rcases hy : r.ncEnd with _ | y <;>
      simp only [hEb, hy] at hE
    · cases hE
    · cases hE
    · simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hE
      refine ⟨E, rfl, hE.1, ?_, fun _ => hE.2⟩
      intro _ h
      cases h
    · simp only [Bool.and_eq_true, beq_iff_eq] at hE
      obtain ⟨hid, hz⟩ := hE
      refine ⟨E, rfl, hid, ?_, ?_⟩
      rotate_left
      · intro h; cases h
      intro y' hy'
      cases hy'
      rcases hq : Ctx.npSeq c.g E with _ | _ | ⟨z, zs⟩ <;> simp only [hq] at hz
      · cases hz
      · cases hz
      · rw [beq_iff_eq.1 hz]; exact ⟨zs, rfl⟩
  · split at hC
    next C hC' => exact ⟨C, hC', beq_iff_eq.1 hC⟩
    next => cases hC
  · intro x hx
    have := List.all_eq_true.1 hsrc x hx
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    exact ⟨Array.contains_iff_mem.1 this.1, this.2⟩
  · intro n hn
    rw [hn] at hnc
    simp only [Bool.and_eq_true] at hnc
    obtain ⟨hm, ha⟩ := hnc
    refine ⟨Array.contains_iff_mem.1 hm, ?_⟩
    cases hv : c.f.value? n with
    | none => rw [hv] at ha; cases ha
    | some u => rw [hv] at ha; exact ⟨u, rfl, beq_iff_eq.1 ha⟩

theorem blockOK_spec {b : ID} (h : c.blockOK b = true) {B : Block} (hB : c.f.block? b = some B)
    {rs : List Run} {l : ID} (hch : chainRuns? c.f c.g b = some (rs, l)) :
    (∃ L C0, c.g.block? l = some L ∧ c.g.block? b = some C0 ∧ L.id = l ∧ C0.id = b ∧
      L.kind = B.kind ∧ L.controls = B.controls ∧ L.succs = B.succs ∧
      ∀ x ∈ B.controls, c.held x = true) ∧
    (segsOf b rs).getLast? = some l ∧
    ((segsOf b rs) ++ rs.map (·.sp.t)).Nodup ∧ (∀ s ∈ (segsOf b rs) ++ rs.map (·.sp.t), s ∈ c.g.blocks) ∧
    (∀ j r, rs[j]? = some r → c.runOK b B (segsOf b rs) rs j r = true) ∧
    (∀ x ∈ B.values, (c.K.getD x false = true → ∃ s ∈ segsOf b rs, x ∈ vals c.g s) ∧
      (c.K.getD x false = false → (∃ r ∈ rs, x ∈ r.src) ∨ ∃ r ∈ rs, r.nc = some x)) ∧
    (∀ j s, (segsOf b rs)[j]? = some s → ∀ x ∈ vals c.g s,
      c.roleOK b B (segsOf b rs) rs false j x = true) ∧
    c.npOK B rs (segsOf b rs) = true := by
  unfold Ctx.blockOK at h
  rw [hB, hch] at h
  dsimp only at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hLC, hlast⟩, hnd⟩, hbl⟩, hruns⟩, hvals⟩, hsegs⟩, hnp⟩ := h
  refine ⟨?_, beq_iff_eq.1 hlast, hnd,
    fun s hs => Array.contains_iff_mem.1 (List.all_eq_true.1 hbl s hs), ?_, ?_, ?_, hnp⟩
  · split at hLC
    next L C0 hL hC0 =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hLC
      obtain ⟨⟨⟨⟨⟨hl, hb⟩, hk⟩, hc⟩, hs⟩, hh⟩ := hLC
      exact ⟨L, C0, hL, hC0, hl, hb, hk, hc, hs,
        fun x hx => Array.all_eq_true_iff_forall_mem.1 hh x hx⟩
    next => cases hLC
  · intro j r hj
    exact List.all_eq_true.1 hruns (r, j) (List.mem_zipIdx_iff_getElem?.2 hj)
  · intro x hx
    have hv := Array.all_eq_true_iff_forall_mem.1 hvals x hx
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · simp only [hk, ↓reduceIte] at hv
      obtain ⟨s, hs, hc⟩ := List.any_eq_true.1 hv
      exact ⟨s, hs, Array.contains_iff_mem.1 hc⟩
    · simp only [hk, Bool.false_eq_true, ↓reduceIte] at hv
      simp only [Bool.or_eq_true] at hv
      rcases hv with hv | hv
      · obtain ⟨r, hr, hc⟩ := List.any_eq_true.1 hv
        exact Or.inl ⟨r, hr, List.contains_iff_mem.1 hc⟩
      · obtain ⟨r, hr, hc⟩ := List.any_eq_true.1 hv
        exact Or.inr ⟨r, hr, beq_iff_eq.1 hc⟩
  · intro j s hj x hx
    exact Array.all_eq_true_iff_forall_mem.1
      (List.all_eq_true.1 hsegs (s, j) (List.mem_zipIdx_iff_getElem?.2 hj)) x hx

end

end GoFV.Proof.WB

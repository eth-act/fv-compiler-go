import GoFV.Opt.WriteBarrierCheck
import GoFV.Proof.Pass.RewriteTerm

/-!
# writebarrier: what the checker's structure establishes (issue #36)

The checker `WBCheck.wbOK` read as propositions: the context (`ctxOf_spec`, `wbOK_spec`), the
kept and last-store marks (`keptMarks_spec`, `lastMarks_spec`), the flag address and constant
(`lazyOK_spec`), and the chain of a block (`splitOf_spec`, `chainRuns_spec`, `runOf_spec`).
-/

namespace GoFV.Proof.WB

open GoFV.SSA GoFV.Opt GoFV.Opt.WBCheck

private theorem guard_some {p : Prop} [Decidable p] {u : Unit}
    (h : (guard p : Option Unit) = some u) : p := by
  by_cases hp : p
  · exact hp
  · simp [guard, hp] at h

private theorem mapM_some {α β : Type} {F : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM F = some l' →
      l'.length = l.length ∧ ∀ j : Nat, l'[j]? = l[j]?.bind F
  | [], l', h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; exact ⟨rfl, fun _ => rfl⟩
  | a :: l, l', h => by
    rw [List.mapM_cons] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨b, hb, l'', hl, rfl⟩ := h
    obtain ⟨h1, h2⟩ := mapM_some hl
    refine ⟨by simp [h1], fun j => ?_⟩
    cases j with
    | zero => simp [hb]
    | succ j => simp [h2 j]

private theorem mapM_some_mem {α β : Type} {F : α → Option β} {l : List α} {l' : List β}
    (h : l.mapM F = some l') {a : α} (ha : a ∈ l) : ∃ b ∈ l', F a = some b := by
  obtain ⟨h1, h2⟩ := mapM_some h
  obtain ⟨j, hj⟩ := List.getElem?_of_mem ha
  have hjl : j < l'.length := by
    rw [h1]; exact (List.getElem?_eq_some_iff.1 hj).1
  obtain ⟨b, hb⟩ : ∃ b, l'[j]? = some b := ⟨_, List.getElem?_eq_getElem hjl⟩
  refine ⟨b, List.mem_of_getElem? hb, ?_⟩
  rw [h2 j, hj] at hb; exact hb

theorem ctxOf_spec {tabs : Tables} {f g : Func} {c : WBCheck.Ctx} (h : ctxOf tabs f g = some c) :
    c.tabs = tabs ∧ c.f = f ∧ c.g = g ∧ c.K = keptMarks f g ∧ c.Lst = lastMarks f g ∧
      lazyOK tabs f g c.K c.Lst = some c.lazy := by
  simp only [ctxOf, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨lz, hl, rfl⟩ := h
  exact ⟨rfl, rfl, rfl, rfl, rfl, hl⟩

theorem wbOK_spec {tabs : Tables} {f g : Func} (h : wbOK tabs f g = true) :
    g.entry = f.entry ∧ g.ownAux = f.ownAux ∧ memTyOK tabs f = true ∧
      ∃ c, ctxOf tabs f g = some c ∧ ∀ b ∈ f.blocks, c.blockOK b = true := by
  unfold wbOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨he, ho⟩, hm⟩, hc⟩ := h
  refine ⟨he, ho, hm, ?_⟩
  cases hcx : ctxOf tabs f g with
  | none => rw [hcx] at hc; cases hc
  | some c =>
    rw [hcx] at hc
    exact ⟨c, rfl, fun b hb => Array.all_eq_true_iff_forall_mem.1 hc b hb⟩

private theorem getD_some {a : Array Bool} {x : Nat} (h : a.getD x false = true) :
    a[x]? = some true := by
  rw [Array.getD_eq_getD_getElem?] at h
  cases hx : a[x]? with
  | none => rw [hx] at h; cases h
  | some v => rw [hx] at h; cases h; rfl

/-- A kept value: listed in both functions with the same fields. -/
theorem keptMarks_spec {f g : Func} {x : ID} (h : (keptMarks f g).getD x false = true) :
    ∃ u w, f.value? x = some u ∧ g.value? x = some w ∧ sameV u w = true ∧
      (∃ b ∈ f.blocks, ∃ B, f.block? b = some B ∧ x ∈ B.values) ∧
      (∃ b ∈ g.blocks, ∃ B, g.block? b = some B ∧ x ∈ B.values) := by
  have h' := getD_some h
  simp only [keptMarks, Array.getElem?_map, List.getElem?_toArray] at h'
  cases hr : (List.range (max f.valueTab.size g.valueTab.size))[x]? with
  | none => rw [hr] at h'; cases h'
  | some y =>
    rw [hr] at h'
    have hy : y = x := by
      obtain ⟨hlt, hyx⟩ := List.getElem?_eq_some_iff.1 hr
      rw [← hyx, List.getElem_range]
    subst hy
    simp only [Option.map_some, Option.some.injEq, Bool.and_eq_true] at h'
    obtain ⟨⟨hf, hg⟩, hm⟩ := h'
    obtain ⟨bf, hbf, Bf, hBf, hxf, -⟩ := Pass.Rewrite.listedMarks_sound f y (getD_some hf)
    obtain ⟨bg, hbg, Bg, hBg, hxg, -⟩ := Pass.Rewrite.listedMarks_sound g y (getD_some hg)
    cases hu : f.value? y with
    | none => rw [hu] at hm; cases hm
    | some u =>
      cases hw : g.value? y with
      | none => rw [hu, hw] at hm; cases hm
      | some w =>
        rw [hu, hw] at hm
        exact ⟨u, w, rfl, rfl, hm, ⟨bf, hbf, Bf, hBf, hxf⟩, ⟨bg, hbg, Bg, hBg, hxg⟩⟩

/-- A marked last store is the last store of a run of some block's chain. -/
theorem lastMarks_spec {f g : Func} {x : ID} (h : (lastMarks f g).getD x false = true) :
    ∃ b ∈ f.blocks, ∃ rs l, chainRuns? f g b = some (rs, l) ∧ ∃ r ∈ rs, r.last = x := by
  let P : Array Bool → Prop := fun L => ∀ y, L.getD y false = true →
    ∃ b ∈ f.blocks, ∃ rs l, chainRuns? f g b = some (rs, l) ∧ ∃ r ∈ rs, r.last = y
  have hP : P (lastMarks f g) := by
    unfold lastMarks
    rw [← Array.foldl_toList]
    refine Pass.Rewrite.foldl_inv P _ _ _ ?_ ?_
    · intro y hy
      have := getD_some hy
      rw [Array.getElem?_replicate] at this
      split at this <;> cases this
    · intro L b hb hL
      cases hc : chainRuns? f g b with
      | none => exact hL
      | some p =>
        obtain ⟨rs, l⟩ := p
        refine Pass.Rewrite.foldl_inv P _ _ _ hL ?_
        intro L r hr hL' y hy
        have hy' := getD_some hy
        simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at hy'
        split at hy'
        · rename_i hry
          exact ⟨b, Array.mem_toList_iff.1 hb, rs, l, hc, r, hr, hry⟩
        · exact hL' y (by rw [Array.getD_eq_getD_getElem?, hy']; rfl)
  exact hP x h

theorem lazyOK_some {tabs : Tables} {f g : Func} {K Lst : Array Bool} {wa c0 : ID}
    (h : lazyOK tabs f g K Lst = some (some (wa, c0))) :
    (∃ w, g.value? wa = some w ∧ w.op = .Addr ∧ symName? tabs w.aux = some "runtime.writeBarrier" ∧
      isPtrTy (tabs.ty w.type) = true ∧ w.args.size = 1 ∧ w.args[0]! ∈ vals g g.entry ∧
      ∃ v, g.value? w.args[0]! = some v ∧ v.op = .SB ∧ v.args = #[]) ∧
    (∃ w, g.value? c0 = some w ∧ w.op = .Const32 ∧ w.auxInt = (0 : Int64) ∧ w.args = #[] ∧
      tabs.ty w.type = .int .w32) ∧
    wa ∈ vals g g.entry ∧ c0 ∈ vals g g.entry ∧
    (∀ b ∈ f.blocks, ∀ rs l, chainRuns? f g b = some (rs, l) → ∀ r ∈ rs,
      r.sp.wbaddr = wa ∧ r.sp.const0 = c0) := by
  simp only [lazyOK, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨runs, hruns, h⟩ := h
  have hmem : ∀ b ∈ f.blocks, ∀ rs l, chainRuns? f g b = some (rs, l) → ∀ r ∈ rs,
      r.sp ∈ runs.flatMap (fun x => x.fst.map fun x => x.sp) := by
    intro b hb rs l hc r hr
    obtain ⟨p, hp, hcp⟩ := mapM_some_mem hruns (Array.mem_toList_iff.2 hb)
    rw [hc] at hcp; cases hcp
    exact List.mem_flatMap.2 ⟨(rs, l), hp, List.mem_map.2 ⟨r, hr, rfl⟩⟩
  generalize runs.flatMap (fun x => x.fst.map fun x => x.sp) = sps at h hmem
  cases sps with
  | nil => simp [pure] at h
  | cons s ss =>
    simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨u1, hall, w, hw, cv, hcv, u2, hwa, u3, hc0, u4, hge, u5, hsb, u6, -, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have hall := guard_some hall
    have hwa := guard_some hwa
    have hc0 := guard_some hc0
    have hge := guard_some hge
    have hsb := guard_some hsb
    obtain ⟨v, hv, hsb⟩ := (Option.any_eq_true _ _).1 hsb
    simp only [Bool.and_eq_true, beq_iff_eq, Array.isEmpty_iff] at hsb
    simp only [Bool.and_eq_true, beq_iff_eq] at hwa
    simp only [Bool.and_eq_true, beq_iff_eq, Array.isEmpty_iff] at hc0
    simp only [Bool.and_eq_true, Array.contains_iff_mem] at hge
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hwa
    obtain ⟨⟨⟨h5, h6⟩, h7⟩, h8⟩ := hc0
    refine ⟨⟨w, hw, h1, h2, h3, h4, hge.2, v, hv, hsb⟩, ⟨cv, hcv, h5, h6, h7, ?_⟩, hge.1.1, hge.1.2,
      ?_⟩
    · split at h8
      · assumption
      · cases h8
    · intro b hb rs l hc r hr
      rcases List.mem_cons.1 (hmem b hb rs l hc r hr) with he | he
      · rw [he]; exact ⟨rfl, rfl⟩
      · have := List.all_eq_true.1 hall _ he
        simp only [Bool.and_eq_true, beq_iff_eq] at this
        exact this

theorem lazyOK_ne {tabs : Tables} {f g : Func} {K Lst : Array Bool} {wa c0 : ID}
    (h : lazyOK tabs f g K Lst = some (some (wa, c0))) : wa ≠ c0 := by
  obtain ⟨⟨w, hw, hop, -⟩, ⟨w', hw', hop', -⟩, -⟩ := lazyOK_some h
  intro he
  subst he
  rw [hw] at hw'
  cases hw'
  rw [hop] at hop'
  cases hop'

/-- The flag address is not held. -/
theorem lazyOK_not_held {tabs : Tables} {f g : Func} {K Lst : Array Bool} {wa c0 : ID}
    (h : lazyOK tabs f g K Lst = some (some (wa, c0))) :
    K.getD wa false = false ∧ Lst.getD wa false = false := by
  simp only [lazyOK, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨runs, -, h⟩ := h
  generalize runs.flatMap (fun x => x.fst.map fun x => x.sp) = sps at h
  cases sps with
  | nil => simp [pure] at h
  | cons s ss =>
    simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, u5, hnh, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have hnh := guard_some hnh
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hnh
    exact hnh

theorem lazyOK_none {tabs : Tables} {f g : Func} {K Lst : Array Bool}
    (h : lazyOK tabs f g K Lst = some none) :
    ∀ b ∈ f.blocks, ∀ rs l, chainRuns? f g b = some (rs, l) → rs = [] := by
  simp only [lazyOK, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨runs, hruns, h⟩ := h
  have hmem : ∀ b ∈ f.blocks, ∀ rs l, chainRuns? f g b = some (rs, l) → ∀ r ∈ rs,
      r.sp ∈ runs.flatMap (fun x => x.fst.map fun x => x.sp) := by
    intro b hb rs l hc r hr
    obtain ⟨p, hp, hcp⟩ := mapM_some_mem hruns (Array.mem_toList_iff.2 hb)
    rw [hc] at hcp; cases hcp
    exact List.mem_flatMap.2 ⟨(rs, l), hp, List.mem_map.2 ⟨r, hr, rfl⟩⟩
  generalize runs.flatMap (fun x => x.fst.map fun x => x.sp) = sps at h hmem
  cases sps with
  | nil =>
    intro b hb rs l hc
    exact List.eq_nil_iff_forall_not_mem.2 fun r hr => List.not_mem_nil (hmem b hb rs l hc r hr)
  | cons s ss =>
    simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, heq⟩ := h
    cases heq

private theorem arr_one {α : Type} [Inhabited α] {a : Array α} (h : a.size = 1) : a = #[a[0]!] := by
  cases a with
  | mk l =>
    simp only [List.size_toArray] at h
    match l, h with
    | [x], _ => rfl

private theorem arr_two {α : Type} [Inhabited α] {a : Array α} (h : a.size = 2) :
    a = #[a[0]!, a[1]!] := by
  cases a with
  | mk l =>
    simp only [List.size_toArray] at h
    match l, h with
    | [x, y], _ => rfl

/-- A split block. -/
theorem splitOf_spec {f g : Func} {c : ID} {s : Split} (h : splitOf? f g c = some s) :
    s.c = c ∧ ∃ C, g.block? c = some C ∧ C.kind = .If ∧ C.controls = #[s.flag] ∧
      C.succs = #[⟨s.t, 0⟩, ⟨s.e, 0⟩] ∧ s.t ≠ s.e ∧ s.t ∉ f.blocks ∧ s.e ∉ f.blocks ∧
      (∃ fv, g.value? s.flag = some fv ∧ fv.op = .Neq32 ∧ fv.args = #[s.load, s.const0]) ∧
      (∃ lv, g.value? s.load = some lv ∧ lv.op = .Load ∧ lv.args = #[s.wbaddr, s.mem]) := by
  simp only [splitOf?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨C, hC, u1, hg1, fv, hfv, u2, hg2, lv, hlv, u3, hg3, u4, hg4, hs⟩ := h
  simp only [pure, Option.some.injEq] at hs
  subst hs
  have hg1 := guard_some hg1
  have hg2 := guard_some hg2
  have hg3 := guard_some hg3
  have hg4 := guard_some hg4
  simp only [Bool.and_eq_true, beq_iff_eq] at hg1 hg2 hg3
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hg4
  obtain ⟨⟨hk, hc1⟩, hs2⟩ := hg1
  obtain ⟨⟨⟨⟨ht0, he0⟩, hte⟩, htf⟩, hef⟩ := hg4
  have hedge : ∀ e : Edge, e.i = 0 → e = ⟨e.b, 0⟩ := fun ⟨b, i⟩ h => by
    simp only at h; subst h; rfl
  have hnm : ∀ b, f.blocks.contains b = false → b ∉ f.blocks := fun b hb hm => by
    rw [Array.contains_iff_mem.2 hm] at hb; cases hb
  refine ⟨rfl, C, hC, hk, arr_one hc1, ?_, hte, hnm _ htf, hnm _ hef,
    ⟨fv, hfv, hg2.1, arr_two hg2.2⟩, ⟨lv, hlv, hg3.1, arr_two hg3.2⟩⟩
  show C.succs = #[⟨C.succs[0]!.b, 0⟩, ⟨C.succs[1]!.b, 0⟩]
  rw [← hedge _ ht0, ← hedge _ he0]
  exact arr_two hs2

private theorem chainOf_spec {f g : Func} : ∀ {fuel : Nat} {c l : ID} {ss : List Split},
    chainOf f g fuel c = some (ss, l) →
    (∀ j s, ss[j]? = some s → (c :: ss.map (·.e))[j]? = some s.c ∧
      (c :: ss.map (·.e))[j + 1]? = some s.e ∧ splitOf? f g s.c = some s) ∧
    (c :: ss.map (·.e)).getLast? = some l
  | 0, _, _, _, h => by cases h
  | fuel + 1, c, l, ss, h => by
    unfold chainOf at h
    cases hs : splitOf? f g c with
    | none =>
      rw [hs] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨fun j s hj => by simp at hj, rfl⟩
    | some s =>
      rw [hs] at h
      dsimp only at h
      cases hr : chainOf f g fuel s.e with
      | none => rw [hr] at h; cases h
      | some p =>
        obtain ⟨ss', l'⟩ := p
        rw [hr] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ih1, ih2⟩ := chainOf_spec hr
        have hsc := (splitOf_spec hs).1
        refine ⟨fun j s' hj => ?_, ?_⟩
        · cases j with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
            subst hj
            exact ⟨by simp [hsc], by simp, by rw [hsc]; exact hs⟩
          | succ j =>
            simp only [List.getElem?_cons_succ] at hj
            obtain ⟨h1, h2, h3⟩ := ih1 j s' hj
            exact ⟨by simpa using h1, by simpa using h2, h3⟩
        · simpa using ih2

private theorem runOf_sp {f g : Func} {s : Split} {r : Run} (h : runOf? f g s = some r) :
    r.sp = s := by
  simp only [runOf?, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := h
  rfl

/-- The chain of a block: consecutive splits, each with its run, ending at the last block. -/
theorem chainRuns_spec {f g : Func} {b l : ID} {rs : List Run} (h : chainRuns? f g b = some (rs, l)) :
    (∀ j r, rs[j]? = some r → (segsOf b rs)[j]? = some r.sp.c ∧
      (segsOf b rs)[j + 1]? = some r.sp.e ∧ splitOf? f g r.sp.c = some r.sp ∧
      runOf? f g r.sp = some r) ∧
    (segsOf b rs).getLast? = some l := by
  simp only [chainRuns?, Option.bind_eq_bind, Option.bind_eq_some_iff, pure,
    Option.some.injEq] at h
  obtain ⟨⟨ss, l'⟩, hc, rs', hrs, heq⟩ := h
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  dsimp only at hrs
  obtain ⟨hlen, hidx⟩ := mapM_some hrs
  have hsp : rs'.map (·.sp) = ss := by
    refine List.ext_getElem? fun j => ?_
    rw [List.getElem?_map, hidx j]
    cases hj : ss[j]? with
    | none => rfl
    | some s =>
      cases hr : runOf? f g s with
      | some r => simp [hr, runOf_sp hr]
      | none =>
        have : rs'[j]? = none := by rw [hidx j, hj]; exact hr
        have hjs : j < ss.length := (List.getElem?_eq_some_iff.1 hj).1
        rw [List.getElem?_eq_none_iff, hlen] at this
        omega
  have hseg : segsOf b rs' = b :: ss.map (·.e) := by
    rw [segsOf, ← hsp, List.map_map]; rfl
  obtain ⟨h1, h2⟩ := chainOf_spec hc
  rw [hseg]
  refine ⟨fun j r hj => ?_, h2⟩
  have hss : ss[j]? = some r.sp := by rw [← hsp, List.getElem?_map, hj]; rfl
  obtain ⟨k1, k2, k3⟩ := h1 j r.sp hss
  refine ⟨k1, k2, k3, ?_⟩
  rw [hidx j, hss] at hj
  exact hj

private theorem srcChain_spec {f : Func} {mem : ID} : ∀ {n : Nat} {x : ID} {l : List ID},
    srcChain f mem n x = some l →
    l.length = n ∧ (n = 0 → x = mem) ∧ (0 < n → l.getLast? = some x) ∧
    ∀ (k : Nat) (y : ID), l[k]? = some y → ∃ u, f.value? y = some u ∧
      (u.op = .Store ∨ u.op = .VarDef ∨ u.op = .VarLive ∨ u.op = .Move ∨ u.op = .Zero) ∧
      u.args.toList.getLast? = some (match k with
        | 0 => mem
        | k + 1 => l[k]!)
  | 0, x, l, h => by
    simp only [srcChain] at h
    split at h
    · rename_i hx
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨rfl, fun _ => by simpa using hx, fun h => absurd h (Nat.lt_irrefl 0),
        fun k y hy => by simp at hy⟩
    · cases h
  | n + 1, x, l, h => by
    simp only [srcChain, Option.bind_eq_bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at h
    obtain ⟨v, hv, u1, hg, m, hm, l0, hl0, rfl⟩ := h
    have hg := guard_some hg
    simp only [Bool.or_eq_true, beq_iff_eq] at hg
    obtain ⟨ih1, ih2, ih3, ih4⟩ := srcChain_spec hl0
    refine ⟨by simp [ih1], fun h => absurd h (Nat.succ_ne_zero n), fun _ => by simp, ?_⟩
    intro k y hy
    rcases Nat.lt_or_ge k n with hk | hk
    · rw [List.getElem?_append_left (by omega)] at hy
      obtain ⟨u, hu, hop, hlast⟩ := ih4 k y hy
      refine ⟨u, hu, hop, ?_⟩
      rw [hlast]
      cases k with
      | zero => rfl
      | succ k =>
        simp only [Option.some.injEq]
        rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
          List.getElem?_append_left (by omega)]
    · rw [List.getElem?_append_right (by omega)] at hy
      have hkn : k = n := by
        rcases Nat.lt_or_ge (k - l0.length) 1 with h' | h'
        · omega
        · rw [List.getElem?_eq_none (by simp; omega)] at hy; cases hy
      subst hkn
      rw [ih1, Nat.sub_self] at hy
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
      subst hy
      refine ⟨v, hv, by rcases hg with (((h | h) | h) | h) | h <;> simp [h], ?_⟩
      rw [Array.getLast?_toList, hm]
      cases k with
      | zero => rw [ih2 rfl]
      | succ k =>
        have hl := ih3 (Nat.succ_pos k)
        rw [List.getLast?_eq_getElem?, ih1] at hl
        simp only [Nat.add_sub_cancel] at hl
        simp only [Option.some.injEq]
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_left (by omega), hl]
        rfl

/-- A run: its source stores form a memory chain from the split's memory, ending at `last`; the
dropped nil check is the first store's address. -/
theorem runOf_spec {f g : Func} {s : Split} {r : Run} (h : runOf? f g s = some r) :
    r.sp = s ∧ r.src.length = r.tgt.length ∧ r.src.getLast? = some r.last ∧
    (∀ (k : Nat) (x : ID), r.src[k]? = some x → ∃ u, f.value? x = some u ∧
      (u.op = .Store ∨ u.op = .VarDef ∨ u.op = .VarLive ∨ u.op = .Move ∨ u.op = .Zero) ∧
      u.args.toList.getLast? = some (match k with
        | 0 => s.mem
        | k + 1 => r.src[k]!)) ∧
    (∀ n, r.nc = some n → ∃ x0 v0 a nv, r.src[0]? = some x0 ∧ f.value? x0 = some v0 ∧
      (v0.op = .Store ∨ v0.op = .Move ∨ v0.op = .Zero) ∧ v0.args[0]? = some a ∧
      f.value? a = some nv ∧ nv.op = .NilCheck ∧
      nv.args[1]? = some s.mem ∧ nv.id = n) ∧
    (∃ pv, g.value? r.phi = some pv ∧ pv.op = .Phi ∧ pv.args = #[s.mem, r.memThen]) ∧
    (vals g s.e)[0]? = some r.phi := by
  simp only [runOf?, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨phi, hphi, pv, hpv, u1, hg1, last, hlast, src, hsc, s0, hs0, v0, hv0, rfl⟩ := h
  have hg1 := guard_some hg1
  simp only [Bool.and_eq_true, beq_iff_eq] at hg1
  obtain ⟨⟨hph, hsz⟩, hm0⟩ := hg1
  obtain ⟨c1, -, c3, c4⟩ := srcChain_spec hsc
  have hpos : 0 < src.length := by
    cases src with
    | nil => cases hs0
    | cons _ _ => simp
  refine ⟨rfl, c1, c3 (c1 ▸ hpos), c4, ?_, ⟨pv, hpv, hph, ?_⟩, hphi⟩
  · intro n hn
    dsimp only at hn
    split at hn
    · rename_i hst
      simp only [Bool.or_eq_true, beq_iff_eq] at hst
      cases ha : v0.args[0]? with
      | none => rw [ha] at hn; cases hn
      | some a =>
        rw [ha] at hn
        cases hnv : f.value? a with
        | none => simp [hnv] at hn
        | some nv =>
          simp only [Option.bind_some, hnv] at hn
          split at hn
          · rename_i hc
            simp only [Bool.and_eq_true, beq_iff_eq] at hc
            simp only [Option.some.injEq] at hn
            exact ⟨s0, v0, a, nv, by rw [← List.head?_eq_getElem?]; exact hs0, hv0,
              by rcases hst with (h | h) | h <;> simp [h], ha, hnv, hc.1, hc.2, hn⟩
          · cases hn
    · cases hn
  · have := arr_two hsz
    rw [hm0] at this
    exact this

end GoFV.Proof.WB

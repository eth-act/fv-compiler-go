import GoFV.Proof.Pass.SchedLRel

variable [GoFV.SSA.Sem.Addrs]

/-!
# `schedule` on `runSched`: one block's values

The source evaluates the block's non-`Phi` values in `runL`'s order `oS` (`kahn`), the target
`g`'s values in `runSched`'s order `oT` (`b.Values` of the scheduled block). `walk_ok`: if the
source evaluates them all, so does the target, to the same registers except at nil checks and
`SPanchored`s (`Agree`). `walk_panic`: if the source panics, the target panics alike: before the
source's panicking value `r` the target evaluates only values the source evaluated before `r`
(alike), values that always evaluate (`Cls.safe`), and values that `swapOK` lets it run first,
which evaluate or panic as `r` does (`nilDeref` of the same memory).

The walk follows the target order (`Inv`: the target frame after a prefix `D` of `oT` agrees
with the source's frame `H` after its prefix `P` on the values of `D` in `P`); the arguments of a
value the source evaluated hold, in the target, the source's registers (`argFact`): nil-check
results are their pointers (`ncEq`, the shape condition of `useOK`), and a bypassed `SPanchored`
is only the base of a symbolic address (`evalValueL_vc`).
-/

namespace GoFV.Proof.SchedL

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.ScheduleCheck GoFV.Proof

/-! ## Contexts -/

theorem makeSched_f (tabs : Tables) (g : Func) : (Ctx.makeSched tabs g).f = g := makeL_f tabs g

theorem makeSched_tabs (tabs : Tables) (g : Func) : (Ctx.makeSched tabs g).tabs = tabs :=
  tabs_makeL tabs g

theorem makeSched_tys (tabs : Tables) (g : Func) :
    (Ctx.makeSched tabs g).tys = (Ctx.makeL tabs g).tys := rfl

theorem makeSched_params (tabs : Tables) (g : Func) :
    (Ctx.makeSched tabs g).params = (Ctx.makeL tabs g).params := rfl

theorem makeSched_act (tabs : Tables) (g : Func) :
    (Ctx.makeSched tabs g).act = (Ctx.makeL tabs g).act := rfl

/-! ## Shapes -/

theorem hasTy_word {v : Val} {t t' : Ty} (ht : wordShape t = true) (ht' : wordShape t' = true)
    (h : v.hasTy t = true) : v.hasTy t' = true := by
  cases t with
  | int w => cases w <;> simp [wordShape] at ht
             cases t' with
             | int w' => cases w' <;> simp [wordShape] at ht'; exact h
             | ptr e =>
               cases v with
               | int w x => cases w <;> simp_all [Val.hasTy]
               | _ => simp_all [Val.hasTy]
             | _ => simp [wordShape] at ht'
  | ptr e =>
    cases t' with
    | int w' =>
      cases w' <;> simp [wordShape] at ht'
      cases v with
      | int w x => cases w <;> simp_all [Val.hasTy]
      | _ => simp_all [Val.hasTy]
    | ptr e' =>
      cases v with
      | int w x => cases w <;> simp_all [Val.hasTy]
      | _ => simp_all [Val.hasTy]
    | _ => simp [wordShape] at ht'
  | _ => simp [wordShape] at ht

theorem LMode.retype_of_hasTy' {md : LMode} {t : Ty} {v : Val} (h : v.hasTy t = true) :
    md.retype t v = v := by
  unfold LMode.retype
  split
  · exact Val.retypeL_of_hasTy h
  · exact Val.retype_of_hasTy h

theorem hasTy_of_typedL {md : LMode} {t : Ty} {v : Val} (h : md.retype t v = v) : v.hasTy t = true := by
  rw [← h]; exact LMode.retype_hasTy md t v

/-- A register of shape `tP` read at shape `tA`, the same or both word shapes, is unchanged. -/
theorem retype_shape {md : LMode} {tA tP : Ty} {v : Val} (hv : md.retype tP v = v)
    (h : tA = tP ∨ (wordShape tA = true ∧ wordShape tP = true)) : md.retype tA v = v := by
  rcases h with rfl | ⟨h1, h2⟩
  · exact hv
  · exact LMode.retype_of_hasTy' (hasTy_word h2 h1 (hasTy_of_typedL hv))

/-- The shapes of two values of the same type in `runL`'s context. -/
theorem tys_eq_of_type {tabs : Tables} {f : Func} {a p : ID} {va vp : Value}
    (ha : f.value? a = some va) (hp : f.value? p = some vp) (h : va.type = vp.type) :
    (Ctx.makeL tabs f).tys[a]? = (Ctx.makeL tabs f).tys[p]? := by
  rw [tysL_of_value ha, tysL_of_value hp, h]

/-- `a` and `p` have the same `runL` shape, or both word shapes. -/
def Shp (tabs : Tables) (f : Func) (a p : ID) : Prop :=
  ((Ctx.makeL tabs f).tys[a]?.getD .other) = ((Ctx.makeL tabs f).tys[p]?.getD .other) ∨
    (wordShape ((Ctx.makeL tabs f).tys[a]?.getD .other) = true ∧
      wordShape ((Ctx.makeL tabs f).tys[p]?.getD .other) = true)

theorem Shp.trans {tabs : Tables} {f : Func} {a b c : ID} (h1 : Shp tabs f a b)
    (h2 : Shp tabs f b c) : Shp tabs f a c := by
  unfold Shp at *
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · exact .inl (h1.trans h2)
  · exact .inr ⟨by rw [h1]; exact h2, h2'⟩
  · exact .inr ⟨h1, by rw [← h2]; exact h1'⟩
  · exact .inr ⟨h1, h2'⟩

/-! ## Bypasses -/

/-- A nil check is no `SPanchored`. -/
theorem nc_not_spa {f : Func} {a : ID} (hnc : isNC f a = true) : isSPA f a = false := by
  unfold isNC at hnc; unfold isSPA
  cases hv : f.value? a with
  | none => rw [hv] at hnc; cases hnc
  | some v =>
    rw [hv] at hnc; simp only [Option.map_some, Option.getD_some] at hnc
    simp only [Option.map_some, Option.getD_some, beq_eq_false_iff_ne, ne_eq]
    intro he; rw [he] at hnc; cases hnc

/-- A value `rep1` changes is a bypassed one, and its bypass is its first argument. -/
theorem rep1_arg0 {f : Func} {a : ID} {v : Value} (hv : f.value? a = some v) (hne : rep1 f a ≠ a) :
    v.args[0]? = some (rep1 f a) := by
  unfold rep1 at hne ⊢
  rw [hv] at hne ⊢
  simp only at hne ⊢
  split at hne
  · rename_i hb
    simp only [hb, ite_true]
    cases h : v.args[0]? with
    | none => rw [h] at hne; exact absurd rfl hne
    | some p => rfl
  · exact absurd rfl hne

theorem rep1_self {f : Func} {a : ID} (h1 : isNC f a = false) (h2 : isSPA f a = false) :
    rep1 f a = a := by
  unfold rep1
  unfold isNC at h1; unfold isSPA at h2
  cases hv : f.value? a with
  | none => rfl
  | some v =>
    rw [hv] at h1 h2
    simp only [Option.map_some, Option.getD_some] at h1 h2
    simp [h1, h2]

theorem repK_fix {f : Func} {a : ID} (h : rep1 f a = a) : ∀ k, repK f k a = a
  | 0 => rfl
  | k + 1 => by simp only [repK, h, beq_self_eq_true, ite_true]

theorem repK_succ {f : Func} {a : ID} (hne : rep1 f a ≠ a) (k : Nat) :
    repK f (k + 1) a = repK f k (rep1 f a) := by
  have h : (rep1 f a == a) = false := by simpa using hne
  simp only [repK, h, Bool.false_eq_true, ite_false]

theorem rep_self {f : Func} {a : ID} (h1 : isNC f a = false) (h2 : isSPA f a = false) :
    rep f a = a :=
  repK_fix (rep1_self h1 h2) _

/-- What a step of a nil-check chain gives, at any shapes. -/
theorem ncStep_basic {tys : Array Ty} {f : Func} {a : ID} (h : ncStep tys f a = true) :
    rep1 f a ≠ a ∧ isSPA f (rep1 f a) = false ∧ ∃ vp, f.value? (rep1 f a) = some vp := by
  unfold ncStep at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', Option.isSome_iff_exists] at h
  obtain ⟨⟨⟨h1, h2⟩, ⟨tp, htp⟩⟩, -⟩ := h
  refine ⟨h1, h2, ?_⟩
  cases hvp : f.value? (rep1 f a) with
  | none => rw [hvp] at htp; cases htp
  | some vp => exact ⟨vp, rfl⟩

/-- What a step of a nil-check chain gives: the shape condition. -/
theorem ncStep_shp {tabs : Tables} {f : Func} {a : ID}
    (h : ncStep (Ctx.makeL tabs f).tys f a = true) : Shp tabs f a (rep1 f a) := by
  unfold ncStep at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', Bool.or_eq_true, beq_iff_eq,
    Option.isSome_iff_exists] at h
  obtain ⟨⟨-, ⟨tp, htp⟩⟩, h5⟩ := h
  rcases h5 with h5 | h5
  · left
    cases hvp : f.value? (rep1 f a) with
    | none => rw [hvp] at htp; cases htp
    | some vp =>
      cases hva : f.value? a with
      | none => rw [hvp, hva] at h5; cases h5
      | some va =>
        rw [hvp, hva] at h5; simp at h5
        rw [tys_eq_of_type hva hvp h5.symm]
  · exact .inr h5

/-- More steps do not change the end of a chain. -/
theorem ncChain_rep {tys : Array Ty} {f : Func} :
    ∀ (k : Nat) (a : ID), ncChain tys f k a = true → ∀ j, k ≤ j → repK f j a = repK f k a
  | 0, a, h, _, _ => by simp [ncChain] at h
  | k + 1, a, h, j, hj => by
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    simp only [ncChain, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hs, hc⟩ := h
    obtain ⟨hne, hsp, -⟩ := ncStep_basic hs
    rw [repK_succ hne, repK_succ hne]
    rcases hc with hn | hc
    · rw [repK_fix (rep1_self hn hsp), repK_fix (rep1_self hn hsp)]
    · exact ncChain_rep k _ hc j (by omega)

/-- **One step of a nil-check chain** (fuel `k + 1` within the value table's size): the step's
facts, the bypass is the next value's, and the chain goes on from it or ends there. -/
theorem chain_cases {tys : Array Ty} {f : Func} {k : Nat} {a : ID}
    (hc : ncChain tys f (k + 1) a = true) (hk : k + 1 ≤ f.valueTab.size) :
    ncStep tys f a = true ∧ rep f a = rep f (rep1 f a) ∧
      (isNC f (rep1 f a) = true → ncChain tys f k (rep1 f a) = true) ∧
      (isNC f (rep1 f a) = false → rep f (rep1 f a) = rep1 f a) := by
  simp only [ncChain, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨hs, hc⟩ := hc
  obtain ⟨hne, hsp, -⟩ := ncStep_basic hs
  obtain ⟨n, hn⟩ : ∃ n, f.valueTab.size = n + 1 := ⟨f.valueTab.size - 1, by omega⟩
  have hfix : isNC f (rep1 f a) = false → rep f (rep1 f a) = rep1 f a :=
    fun h => repK_fix (rep1_self h hsp) _
  refine ⟨hs, ?_, fun h => ?_, hfix⟩
  · unfold rep
    rw [hn, repK_succ hne]
    rcases hc with h' | h'
    · rw [repK_fix (rep1_self h' hsp), repK_fix (rep1_self h' hsp)]
    · rw [ncChain_rep k _ h' n (by omega), ncChain_rep k _ h' (n + 1) (by omega)]
  · rcases hc with h' | h'
    · rw [h] at h'; cases h'
    · exact h'

/-- The end of a nil-check chain is a value, no nil check or `SPanchored`. -/
theorem chain_end {tys : Array Ty} {f : Func} :
    ∀ (k : Nat) (a : ID), ncChain tys f k a = true → k ≤ f.valueTab.size →
      isNC f (rep f a) = false ∧ isSPA f (rep f a) = false ∧ ∃ vp, f.value? (rep f a) = some vp
  | 0, a, h, _ => by simp [ncChain] at h
  | k + 1, a, h, hk => by
    obtain ⟨hs, hrep, hnext, hfix⟩ := chain_cases h hk
    obtain ⟨-, hsp, hv⟩ := ncStep_basic hs
    cases hn : isNC f (rep1 f a)
    · rw [hrep, hfix hn]; exact ⟨hn, hsp, hv⟩
    · rw [hrep]; exact chain_end k _ (hnext hn) (by omega)

/-- The shape condition along a nil-check chain. -/
theorem chain_shp {tabs : Tables} {f : Func} :
    ∀ (k : Nat) (a : ID), ncChain (Ctx.makeL tabs f).tys f k a = true → k ≤ f.valueTab.size →
      Shp tabs f a (rep f a)
  | 0, a, h, _ => by simp [ncChain] at h
  | k + 1, a, h, hk => by
    obtain ⟨hs, hrep, hnext, hfix⟩ := chain_cases h hk
    have h1 := ncStep_shp hs
    cases hn : isNC f (rep1 f a)
    · rw [hrep, hfix hn]; exact h1
    · rw [hrep]; exact h1.trans (chain_shp k _ (hnext hn) (by omega))

/-- A property closed under one bypass step of a nil check holds of the chain's end. -/
theorem chain_closed {tys : Array Ty} {f : Func} (P : ID → Prop)
    (hcl : ∀ z, P z → isNC f z = true → P (rep1 f z)) :
    ∀ (k : Nat) (a : ID), ncChain tys f k a = true → k ≤ f.valueTab.size → P a →
      isNC f a = true → P (rep f a)
  | 0, a, h, _, _, _ => by simp [ncChain] at h
  | k + 1, a, h, hk, ha, hn => by
    obtain ⟨-, hrep, hnext, hfix⟩ := chain_cases h hk
    have hp := hcl a ha hn
    cases hn' : isNC f (rep1 f a)
    · rw [hrep, hfix hn']; exact hp
    · rw [hrep]; exact chain_closed P hcl k _ (hnext hn') (by omega) hp hn'

/-- A use that is a nil check starts a nil-check chain. -/
theorem use_chain {tabs : Tables} {tys : Array Ty} {f : Func} {user : Option Value} {k : Nat}
    {a : ID} (hu : useOK tabs tys f user k a = true) (hnc : isNC f a = true) :
    ncChain tys f f.valueTab.size a = true := by
  unfold useOK at hu
  rw [nc_not_spa hnc, hnc] at hu
  simpa using hu

/-- A bypassed `SPanchored` use: one step, to a value that is no nil check or `SPanchored`. -/
theorem use_spa {tabs : Tables} {tys : Array Ty} {f : Func} {user : Option Value} {k : Nat}
    {a : ID} (hu : useOK tabs tys f user k a = true) (hs : isSPA f a = true) :
    k = 0 ∧ (user.map fun u => symAddrOp u.op && symbolic tabs u).getD false = true ∧
      rep1 f a ≠ a ∧ (∃ vp, f.value? (rep1 f a) = some vp) ∧ isNC f (rep1 f a) = false ∧
      isSPA f (rep1 f a) = false ∧ rep f a = rep1 f a := by
  unfold useOK at hu
  simp only [hs, ite_true] at hu
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.not_eq_true',
    Option.isSome_iff_exists] at hu
  obtain ⟨⟨hk, hsym⟩, ⟨⟨hne, vp, hvp⟩, hnc⟩, hspa⟩ := hu
  refine ⟨hk, hsym, hne, ⟨vp, hvp⟩, hnc, hspa, ?_⟩
  have hsz : 0 < f.valueTab.size := by
    unfold isSPA at hs
    cases hv : f.value? a with
    | none => rw [hv] at hs; cases hs
    | some v => exact Nat.lt_of_le_of_lt (Nat.zero_le _) (lt_of_value? hv)
  obtain ⟨n, hn⟩ : ∃ n, f.valueTab.size = n + 1 := ⟨f.valueTab.size - 1, by omega⟩
  unfold rep
  rw [hn, repK_succ hne, repK_fix (rep1_self hnc hspa)]

/-- The shape condition of `useOK` for a nil check `a`, through its chain to `rep f a`. -/
theorem nc_shape {tabs : Tables} {f : Func} {user : Option Value} {k : Nat} {a : ID}
    (hu : useOK tabs (Ctx.makeL tabs f).tys f user k a = true) (hnc : isNC f a = true) :
    isSPA f a = false ∧ rep f a ≠ a ∧ isNC f (rep f a) = false ∧ isSPA f (rep f a) = false ∧
      (∃ vp, f.value? (rep f a) = some vp) ∧ Shp tabs f a (rep f a) := by
  have hc := use_chain hu hnc
  obtain ⟨h1, h2, h3⟩ := chain_end _ _ hc (Nat.le_refl _)
  refine ⟨nc_not_spa hnc, fun h => ?_, h1, h2, h3, chain_shp _ _ hc (Nat.le_refl _)⟩
  rw [h, hnc] at h1; cases h1

/-- One step of a nil check use: its pointer, of a compatible shape. -/
theorem nc_step1 {tabs : Tables} {f : Func} {user : Option Value} {k : Nat} {a : ID}
    (hu : useOK tabs (Ctx.makeL tabs f).tys f user k a = true) (hnc : isNC f a = true) :
    rep1 f a ≠ a ∧ Shp tabs f a (rep1 f a) := by
  have hc := use_chain hu hnc
  obtain ⟨n, hn⟩ : ∃ n, f.valueTab.size = n + 1 := by
    cases h : f.valueTab.size with
    | zero => rw [h] at hc; simp [ncChain] at hc
    | succ n => exact ⟨n, rfl⟩
  rw [hn] at hc
  obtain ⟨hs, -⟩ := chain_cases hc (by omega)
  exact ⟨(ncStep_basic hs).1, ncStep_shp hs⟩

/-! ## Lists -/

theorem topo_mid {D : ID → List ID} {x : ID} {s : List ID} :
    ∀ {d : List ID}, TopoRem D (d ++ x :: s) → ∀ a ∈ D x, a ∉ x :: s
  | [], h => h.1
  | _ :: d, h => topo_mid (d := d) h.2

theorem topo_prefix {D : ID → List ID} {s : List ID} :
    ∀ {d : List ID}, TopoRem D (d ++ s) → TopoRem D d
  | [], _ => trivial
  | x :: d, ⟨h1, h2⟩ => ⟨fun a ha hm => h1 a ha (by
      rcases List.mem_cons.1 hm with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ hm)), topo_prefix h2⟩

theorem split_at {o : List ID} {j : Nat} {x : ID} (h : o[j]? = some x) :
    o = o.take j ++ x :: o.drop (j + 1) := by
  have hj : j < o.length := (List.getElem?_eq_some_iff.1 h).1
  conv => lhs; rw [← List.take_append_drop j o]
  congr 1
  rw [List.drop_eq_getElem_cons hj]
  simp [(List.getElem?_eq_some_iff.1 h).2]

/-- An argument of the value at position `j` of a dependency order that is listed is listed
before `j`. -/
theorem topo_before {D : ID → List ID} {o : List ID} (ht : TopoRem D o) {j : Nat} {x : ID}
    (hx : o[j]? = some x) {a : ID} (ha : a ∈ D x) (hm : a ∈ o) : a ∈ o.take j := by
  have hs := split_at hx
  rw [hs] at ht hm
  rcases List.mem_append.1 hm with hm | hm
  · exact hm
  · exact absurd hm (topo_mid ht a ha)

/-! ## The block step -/

/-- Values not bypassed (`isNC`, `isSPA`) hold the same registers. -/
def Agree (f : Func) (F T : Frame) : Prop :=
  ∀ a, isNC f a = false → isSPA f a = false → T.regs[a]? = F.regs[a]?

/-- The arguments of the block's values outside the block (lemma (D) at the block's entry): they
have registers, and so do their bypasses, which a nil check's result equals; a nil check's
result, an `SP`, a `GetG` or the closure pointer (`isNN`; `tys`: `f`'s shapes) has no nil
base. -/
def Out (tys : Array Ty) (f : Func) (S : List ID) (F : Frame) : Prop :=
  ∀ x ∈ S, ∀ a ∈ argsF f x, a ∉ S → (∃ z, F.regs[a]? = some (some z)) ∧ rep f a ∉ S ∧
    (∃ z, F.regs[rep f a]? = some (some z)) ∧ (isNC f a = true → F.regs[rep f a]? = F.regs[a]?) ∧
    (isNN tys f a = true → ∀ z, F.regs[a]? = some (some z) → ¬ NilBase z)

/-- A block entry of the simulation: source order `oS`, target order `oT`, frames after the
`Phi`s. -/
structure BStep (tabs : Tables) (f g : Func) (md : LMode) (oS oT : List ID)
    (frPS frPT : Frame) : Prop where
  sNodup : oS.Nodup
  sTopo : TopoRem (argsF f) oS
  sOwn : ∀ x ∈ oS, ∀ v, f.value? x = some v → v.id = x
  sVal : ∀ x ∈ oS, ∃ v, f.value? x = some v
  tNodup : oT.Nodup
  tTopo : TopoRem (argsF g) oT
  tMem : ∀ x, x ∈ oT ↔ x ∈ oS ∧ isSPA f x = false
  frT : frPT = { frPS with regs := frPT.regs }
  size : frPT.regs.size = frPS.regs.size
  sizeS : frPS.regs.size = f.valueTab.size
  agree : Agree f frPS frPT
  typed : TypedL md (Ctx.makeL tabs f) frPS
  out : Out (Ctx.makeL tabs f).tys f oS frPS
  swap : ∀ (i j : Nat) (x y : ID), i < j → oT[i]? = some y → oT[j]? = some x →
    mayFail tabs f y = true → mayFail tabs f x = true → ∀ (k l : Nat), k < l → oS[k]? = some x →
    oS[l]? = some y → swapOK tabs (Ctx.makeL tabs f).params (Ctx.makeL tabs f).tys f
      (srcPos f.valueTab.size oS) x y = true
  /-- The values of `oS` are values of `f` (`srcPos`). -/
  sLt : ∀ x ∈ oS, x < f.valueTab.size
  /-- An image per parameter (`argOK` pieces evaluate). -/
  img : frPS.images.size = (Ctx.makeL tabs f).params.size
  /-- The closure context has no nil base (`poison` without one; `ArgPtrsOK` at the entry). -/
  clo : ∀ c, frPS.closure = some c → ¬ NilBase c
  /-- The pointer-shaped parameter pieces that the block's values take from outside it read nil
  or pointers that are not wild. -/
  argOut : ∀ x ∈ oS, ∀ a ∈ argsF f x, a ∉ oS →
    argPtr tabs (Ctx.makeL tabs f).params (Ctx.makeL tabs f).tys f a = true →
    ∀ z, frPS.regs[a]? = some (some z) → PtrOK z

/-- The source after the prefix `P` of its order. -/
structure Src (tabs : Tables) (f : Func) (md : LMode) (env : Env) (frPS H : Frame) (P : List ID) :
    Prop where
  frH : H = { frPS with regs := H.regs }
  size : H.regs.size = frPS.regs.size
  out : ∀ z, z ∉ P → H.regs[z]? = frPS.regs[z]?
  eval : ∀ x ∈ P, ∃ v y, f.value? x = some v ∧ H.regs[x]? = some (some y) ∧
    evalValueL md env (Ctx.makeL tabs f) H v = .ok y
  typed : TypedL md (Ctx.makeL tabs f) H

/-- The target after the prefix `D` of its order. -/
structure Inv (f : Func) (frPT H T : Frame) (P D : List ID) : Prop where
  frT : T = { frPT with regs := T.regs }
  size : T.regs.size = frPT.regs.size
  out : ∀ a, a ∉ D → T.regs[a]? = frPT.regs[a]?
  inP : ∀ a ∈ D, a ∈ P → isNC f a = false → T.regs[a]? = H.regs[a]?
  some : ∀ a ∈ D, ∃ z, T.regs[a]? = some (some z)

variable {tabs : Tables} {f g : Func} {md : LMode} {env : Env}

theorem isSPA_of {f : Func} {a : ID} {v : Value} (hv : f.value? a = some v) :
    isSPA f a = (v.op == .SPanchored) := by
  unfold isSPA; rw [hv]; rfl

theorem isNC_of {f : Func} {a : ID} {v : Value} (hv : f.value? a = some v) :
    isNC f a = v.op.nilCheck := by
  unfold isNC; rw [hv]; rfl

/-- The end of a nil-check chain is the pointer of the chain's last check. -/
theorem chain_last {tys : Array Ty} {f : Func} :
    ∀ (k : Nat) (a : ID), ncChain tys f k a = true → k ≤ f.valueTab.size → isNC f a = true →
      ∃ c vc, f.value? c = some vc ∧ vc.op.nilCheck = true ∧ vc.args[0]? = some (rep f a)
  | 0, a, h, _, _ => by simp [ncChain] at h
  | k + 1, a, h, hk, hn => by
    obtain ⟨hs, hrep, hnext, hfix⟩ := chain_cases h hk
    obtain ⟨hne, -, -⟩ := ncStep_basic hs
    cases hn' : isNC f (rep1 f a)
    · cases hva : f.value? a with
      | none => unfold isNC at hn; rw [hva] at hn; cases hn
      | some va =>
        refine ⟨a, va, hva, by rw [← isNC_of hva]; exact hn, ?_⟩
        rw [hrep, hfix hn']; exact rep1_arg0 hva hne
    · rw [hrep]; exact chain_last k _ (hnext hn') (by omega) hn'

/-- What a use says of its bypass. -/
theorem use_rep {tys : Array Ty} {user : Option Value} {k : Nat} {a : ID}
    (hu : useOK tabs tys f user k a = true) :
    isNC f (rep f a) = false ∧ isSPA f (rep f a) = false ∧
      (isSPA f a = true → k = 0 ∧ (user.map fun u => symAddrOp u.op && symbolic tabs u).getD false = true ∧
        rep f a ≠ a) ∧
      (isNC f a = true → rep f a ≠ a) := by
  by_cases hs : isSPA f a = true
  · obtain ⟨hk, hsym, hne, -, hnc, hspa, hr⟩ := use_spa hu hs
    rw [hr]
    exact ⟨hnc, hspa, fun _ => ⟨hk, hsym, hne⟩, fun hn => by rw [nc_not_spa hn] at hs; cases hs⟩
  · have hs' : isSPA f a = false := by simpa using hs
    by_cases hn : isNC f a = true
    · obtain ⟨h1, h2, -⟩ := chain_end _ _ (use_chain hu hn) (Nat.le_refl _)
      refine ⟨h1, h2, fun h => absurd h hs, fun _ h => ?_⟩
      rw [h, hn] at h1; cases h1
    · have hn' : isNC f a = false := by simpa using hn
      rw [rep_self hn' hs']
      exact ⟨hn', hs', fun h => absurd h hs, fun h => absurd h hn⟩

/-- **A nil check's result is its pointer** (one step) in a frame where it evaluated. -/
theorem ncEq1 {fr : Frame} {a : ID} {va : Value} (hva : f.value? a = some va) (hid : va.id = a)
    (hnc : isNC f a = true) (hev : ∃ y, fr.regs[a]? = some (some y) ∧
      evalValueL md env (Ctx.makeL tabs f) fr va = .ok y)
    (ht : TypedL md (Ctx.makeL tabs f) fr) (hsh : Shp tabs f a (rep1 f a))
    (hne : rep1 f a ≠ a) : fr.regs[rep1 f a]? = fr.regs[a]? := by
  obtain ⟨y, hy, hev⟩ := hev
  rw [isNC_of hva] at hnc
  obtain ⟨p, yp, hp, hyp, hyy, -⟩ := evalValueL_nc_ok hnc hev
  have hrp : rep1 f a = p := by rw [rep1_arg0 hva hne] at hp; cases hp; rfl
  unfold Shp at hsh
  rw [hrp] at hsh ⊢
  rw [hy, hyp, hyy, hid]
  congr 2
  exact (retype_shape (ht p yp hyp) hsh).symm

/-- **A chain of nil checks' result is its end** in a frame where the chain's nil checks
evaluated (`P`: values with that fact, closed under a nil check's pointer). -/
theorem ncEq {fr : Frame} (P : ID → Prop)
    (hP : ∀ z, P z → isNC f z = true → (∃ vz y, f.value? z = some vz ∧ vz.id = z ∧
      fr.regs[z]? = some (some y) ∧ evalValueL md env (Ctx.makeL tabs f) fr vz = .ok y) ∧
      P (rep1 f z))
    (ht : TypedL md (Ctx.makeL tabs f) fr) :
    ∀ (k : Nat) (a : ID), ncChain (Ctx.makeL tabs f).tys f k a = true → k ≤ f.valueTab.size →
      P a → isNC f a = true → fr.regs[rep f a]? = fr.regs[a]?
  | 0, a, h, _, _, _ => by simp [ncChain] at h
  | k + 1, a, h, hk, ha, hn => by
    obtain ⟨hs, hrep, hnext, hfix⟩ := chain_cases h hk
    obtain ⟨⟨va, y, hva, hid, hy, hev⟩, hp⟩ := hP a ha hn
    have h1 := ncEq1 hva hid hn ⟨y, hy, hev⟩ ht (ncStep_shp hs) (ncStep_basic hs).1
    cases hn' : isNC f (rep1 f a)
    · rw [hrep, hfix hn', h1]
    · rw [hrep, ncEq P hP ht k _ (hnext hn') (by omega) hp hn', h1]

/-- **A nil check's result is a pointer outside the nil block** in a frame where it evaluated. -/
theorem ncNonNil {fr : Frame} {a : ID} {va : Value} (hva : f.value? a = some va) (hid : va.id = a)
    (hnc : isNC f a = true) (hev : ∃ y, fr.regs[a]? = some (some y) ∧
      evalValueL md env (Ctx.makeL tabs f) fr va = .ok y)
    (ht : TypedL md (Ctx.makeL tabs f) fr) (hsh : Shp tabs f a (rep1 f a))
    (hne : rep1 f a ≠ a) : ∀ z, fr.regs[a]? = some (some z) → NonNil z := by
  intro z hz
  have heq := ncEq1 hva hid hnc hev ht hsh hne
  obtain ⟨y, -, hev'⟩ := hev
  rw [isNC_of hva] at hnc
  obtain ⟨p, yp, hp, hyp, -, hnn⟩ := evalValueL_nc_ok hnc hev'
  have hrp : rep1 f a = p := by rw [rep1_arg0 hva hne] at hp; cases hp; rfl
  rw [hrp, hyp, hz] at heq
  cases heq
  exact hnn

/-- The target frame is the source's with other registers. -/
theorem frame_eq {frPS frPT H T : Frame} (hPT : frPT = { frPS with regs := frPT.regs })
    (hH : H = { frPS with regs := H.regs }) (hT : T = { frPT with regs := T.regs }) :
    T = { H with regs := T.regs } := by
  rw [hT, hPT, hH]

/-- **A chain of nil checks from a value the source evaluated**: in the target, the chain's end
holds the first check's register (`n`: the chain's fuel). -/
theorem argFactNC {oS oT : List ID} {frPS frPT H T : Frame} {P D : List ID}
    (B : BStep tabs f g md oS oT frPS frPT) (Sr : Src tabs f md env frPS H P)
    (hPS : ∀ x ∈ P, x ∈ oS) (hPc : ∀ x ∈ P, ∀ a ∈ argsF f x, a ∈ oS → a ∈ P)
    (I : Inv f frPT H T P D) (hDo : ∀ a ∈ D, a ∈ oT) :
    ∀ (n : Nat) (a : ID), ncChain (Ctx.makeL tabs f).tys f n a = true → n ≤ f.valueTab.size →
      a ∈ P → isNC f a = true → (rep f a ∈ oT → rep f a ∈ D) → T.regs[rep f a]? = H.regs[a]?
  | 0, a, h, _, _, _, _ => by simp [ncChain] at h
  | n + 1, a, h, hk, haP, hn, hrep => by
    obtain ⟨hs, hra, hnext, hfix⟩ := chain_cases h hk
    obtain ⟨hne, hsp, -⟩ := ncStep_basic hs
    have haS := hPS a haP
    obtain ⟨va, z, hva, hz, hev⟩ := Sr.eval a haP
    have hid := B.sOwn a haS va hva
    have h1 := ncEq1 hva hid hn ⟨z, hz, hev⟩ Sr.typed (ncStep_shp hs) hne
    have hpa : rep1 f a ∈ argsF f a := by
      rw [argsF_of hva]; exact Array.mem_toList_iff.2 (Array.mem_of_getElem? (rep1_arg0 hva hne))
    rw [hra] at hrep ⊢
    rw [← h1]
    cases hpn : isNC f (rep1 f a)
    · -- the chain ends at `rep1 f a`
      rw [hfix hpn] at hrep ⊢
      by_cases hpS : rep1 f a ∈ oS
      · exact I.inP _ (hrep ((B.tMem _).2 ⟨hpS, hsp⟩)) (hPc a haP _ hpa hpS) hpn
      · rw [I.out _ (fun hD => hpS ((B.tMem _).1 (hDo _ hD)).1), B.agree _ hpn hsp,
          Sr.out _ (fun hP => hpS (hPS _ hP))]
    · by_cases hpS : rep1 f a ∈ oS
      · exact argFactNC B Sr hPS hPc I hDo n _ (hnext hpn) (by omega) (hPc a haP _ hpa hpS) hpn
          hrep
      · obtain ⟨-, hrS, -, hnc, -⟩ := B.out a haS _ hpa hpS
        obtain ⟨hrn, hrs, -⟩ := chain_end _ _ (hnext hpn) (by omega)
        rw [I.out _ (fun hD => hrS ((B.tMem _).1 (hDo _ hD)).1), B.agree _ hrn hrs, hnc hpn,
          Sr.out _ (fun hP => hpS (hPS _ hP))]

/-- **The arguments of a value the source evaluated (or reached) hold, in the target, the
source's registers** (a bypassed `SPanchored`: some register, as the base of a symbolic
address). -/
theorem argFact (S : SchedRel tabs f g) {oS oT : List ID} {frPS frPT H T : Frame} {P D : List ID}
    (B : BStep tabs f g md oS oT frPS frPT) (Sr : Src tabs f md env frPS H P)
    (hPS : ∀ x ∈ P, x ∈ oS) (hPc : ∀ x ∈ P, ∀ a ∈ argsF f x, a ∈ oS → a ∈ P)
    (I : Inv f frPT H T P D) (hDo : ∀ a ∈ D, a ∈ oT)
    {y : ID} {vy : Value} (hy : f.value? y = some vy) (hyS : y ∈ oS)
    (hdone : ∀ a ∈ argsF f y, a ∈ oS → a ∈ P) {k : Nat} {a : ID} (ha : vy.args[k]? = some a)
    (hrep : rep f a ∈ oT → rep f a ∈ D) :
    (∃ z, H.regs[a]? = some (some z)) ∧ (∃ z, T.regs[rep f a]? = some (some z)) ∧
      (isSPA f a = false → T.regs[rep f a]? = H.regs[a]?) ∧
      (isSPA f a = true → k = 0 ∧ vy.op ∈ symAddrOps ∧ symbolic tabs vy = true) := by
  have hu := S.argUse hy ha
  obtain ⟨hrn, hrs, hspa, -⟩ := use_rep hu
  have haf : a ∈ argsF f y := by
    rw [argsF_of hy]; exact Array.mem_toList_iff.2 (Array.mem_of_getElem? ha)
  have hspa' : isSPA f a = true → k = 0 ∧ vy.op ∈ symAddrOps ∧ symbolic tabs vy = true := by
    intro h
    obtain ⟨hk, hsym, -⟩ := hspa h
    simp only [Option.map_some, Option.getD_some, Bool.and_eq_true] at hsym
    exact ⟨hk, of_decide_eq_true hsym.1, hsym.2⟩
  -- the bypass outside the block
  have hTout : rep f a ∉ oS → T.regs[rep f a]? = H.regs[rep f a]? := fun h => by
    rw [I.out _ (fun hD => h ((B.tMem _).1 (hDo _ hD)).1), B.agree _ hrn hrs,
      Sr.out _ (fun hP => h (hPS _ hP))]
  -- the bypass inside the block, evaluated by the source
  have hTin : rep f a ∈ oS → rep f a ∈ P → T.regs[rep f a]? = H.regs[rep f a]? := fun h hP =>
    I.inP _ (hrep ((B.tMem _).2 ⟨h, hrs⟩)) hP hrn
  by_cases haS : a ∈ oS
  · have haP : a ∈ P := hdone a haf haS
    obtain ⟨va, z, hva, hz, hev⟩ := Sr.eval a haP
    by_cases hs : isSPA f a = true
    · -- a bypassed `SPanchored`: its first argument, which `a`'s evaluation read
      obtain ⟨-, -, hne, -, -, -, hr1⟩ := use_spa hu hs
      have h0 := rep1_arg0 hva hne
      have hm : rep1 f a ∈ va.args := Array.mem_of_getElem? h0
      have hz' := evalValueL_args_def (fun msg h => by rw [hev] at h; cases h) _ hm
      have hin : rep1 f a ∈ oS → rep1 f a ∈ P := fun hS =>
        hPc a haP _ (by rw [argsF_of hva]; exact Array.mem_toList_iff.2 hm) hS
      refine ⟨⟨z, hz⟩, ?_, fun h => (by rw [hs] at h; cases h), hspa'⟩
      rw [hr1] at hTin hTout ⊢
      by_cases hr : rep1 f a ∈ oS
      · rw [hTin hr (hin hr)]; exact hz'
      · rw [hTout hr]; exact hz'
    · have hs' : isSPA f a = false := by simpa using hs
      by_cases hn : isNC f a = true
      · have hT : T.regs[rep f a]? = H.regs[a]? :=
          argFactNC B Sr hPS hPc I hDo _ a (use_chain hu hn) (Nat.le_refl _) haP hn hrep
        exact ⟨⟨z, hz⟩, ⟨z, by rw [hT, hz]⟩, fun _ => hT, fun h => (by rw [hs'] at h; cases h)⟩
      · have hn' : isNC f a = false := by simpa using hn
        have hr := rep_self hn' hs'
        have hT : T.regs[rep f a]? = H.regs[a]? := by
          have := hTin (by rw [hr]; exact haS) (by rw [hr]; exact haP)
          rw [this, hr]
        exact ⟨⟨z, hz⟩, ⟨z, by rw [hT, hz]⟩, fun _ => hT, fun h => (by rw [hs'] at h; cases h)⟩
  · obtain ⟨⟨z, hz⟩, hrS, ⟨z', hz'⟩, hnc, -⟩ := B.out y hyS a haf haS
    have hHa : H.regs[a]? = frPS.regs[a]? := Sr.out _ (fun hP => haS (hPS _ hP))
    have hHr : H.regs[rep f a]? = frPS.regs[rep f a]? := Sr.out _ (fun hP => hrS (hPS _ hP))
    refine ⟨⟨z, by rw [hHa, hz]⟩, ⟨z', by rw [hTout hrS, hHr, hz']⟩, fun hs => ?_, hspa'⟩
    by_cases hn : isNC f a = true
    · rw [hTout hrS, hHr, hnc hn, hHa]
    · have hr := rep_self (by simpa using hn) hs
      rw [hTout hrS, hr]

/-! ## Target values -/

theorem params_eq (S : SchedRel tabs f g) :
    (Ctx.makeSched tabs g).params = (Ctx.makeL tabs f).params := by
  rw [makeSched_params, params_makeL, params_makeL]
  simp only [Ctx.make, abiParams, S.ownAux]

theorem act_eq : (Ctx.makeSched tabs g).act = (Ctx.makeL tabs f).act := by
  rw [makeSched_act, act_makeL, act_makeL]; rfl

theorem tys_eq (S : SchedRel tabs f g) {x : ID} {fv gv : Value} (hf : f.value? x = some fv)
    (hg : g.value? x = some gv) (ht : gv.type = fv.type) :
    (Ctx.makeSched tabs g).tys[x]? = (Ctx.makeL tabs f).tys[x]? := by
  rw [makeSched_tys, tysL_of_value hg, tysL_of_value hf, S.lowered, ht]

theorem cls_congr {fv gv : Value} (hr : VRel f g fv gv) :
    cls tabs gv = cls tabs fv := by
  have hsz : gv.args.size = fv.args.size := by rw [hr.args, Array.size_map]
  unfold cls symbolic
  rw [hr.op, hr.aux, hsz]

theorem argOK_congr {fv gv : Value} (hr : VRel f g fv gv) (params : Array (Option AuxRef)) :
    argOK tabs params gv = argOK tabs params fv := by
  have hsz : gv.args.isEmpty = fv.args.isEmpty := by
    rw [hr.args]; cases fv.args; simp
  unfold argOK
  rw [hr.op, hr.aux, hsz]

theorem isNN_cases {tys : Array Ty} {a : ID} (h : isNN tys f a = true) :
    ∃ v, f.value? a = some v ∧ (isNC f a = true ∨
      (v.op = .ARM64LoweredGetClosurePtr ∧ wordShape (tys[a]?.getD .other) = true) ∨
      ((v.op = .SP ∨ v.op = .GetG) ∧ wordShape (tys[a]?.getD .other) = true)) := by
  unfold isNN at h
  split at h
  · rename_i v hv
    refine ⟨v, hv, ?_⟩
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with h | ⟨(h | h) | h, hw⟩
    · exact .inl (by rw [isNC_of hv]; exact h)
    · exact .inr (.inl ⟨h, hw⟩)
    · exact .inr (.inr ⟨.inl h, hw⟩)
    · exact .inr (.inr ⟨.inr h, hw⟩)
  · cases h

theorem tval (S : SchedRel tabs f g) {oS oT : List ID} {frPS frPT : Frame}
    (B : BStep tabs f g md oS oT frPS frPT) {x : ID} (hx : x ∈ oT) :
    ∃ fv gv, f.value? x = some fv ∧ g.value? x = some gv ∧ VRel f g fv gv := by
  obtain ⟨hxS, hs⟩ := (B.tMem x).1 hx
  obtain ⟨fv, hfv⟩ := B.sVal x hxS
  obtain ⟨gv, hgv, hr⟩ := S.fval hfv (fun h => by rw [isSPA_of hfv, h] at hs; cases hs)
  exact ⟨fv, gv, hfv, hgv, hr⟩

theorem argsF_g {x : ID} {fv gv : Value} (hg : g.value? x = some gv) (hr : VRel f g fv gv)
    {k : Nat} {a : ID} (ha : fv.args[k]? = some a) :
    gv.args[k]? = some (rep f a) ∧ rep f a ∈ argsF g x := by
  have h : gv.args[k]? = some (rep f a) := by rw [hr.args, Array.getElem?_map, ha]; rfl
  exact ⟨h, by rw [argsF_of hg]; exact Array.mem_toList_iff.2 (Array.mem_of_getElem? h)⟩

/-- **A value the source evaluated (or reached) evaluates in the target alike.** -/
theorem stepT (S : SchedRel tabs f g) (hf : md.faulting = true) {oS oT : List ID}
    {frPS frPT H T : Frame} {P : List ID} (B : BStep tabs f g md oS oT frPS frPT)
    (Sr : Src tabs f md env frPS H P) (hPS : ∀ x ∈ P, x ∈ oS)
    (hPc : ∀ x ∈ P, ∀ a ∈ argsF f x, a ∈ oS → a ∈ P) {j : Nat}
    (I : Inv f frPT H T P (oT.take j)) {y : ID} (hyj : oT[j]? = some y)
    (hdone : ∀ a ∈ argsF f y, a ∈ oS → a ∈ P) {fv gv : Value} (hfv : f.value? y = some fv)
    (hgv : g.value? y = some gv) (hr : VRel f g fv gv) :
    (∀ z, evalValueL md env (Ctx.makeL tabs f) H fv = .ok z →
      ∃ z', evalValueL md env (Ctx.makeSched tabs g) T gv = .ok z' ∧ (isNC f y = false → z' = z)) ∧
    (∀ e m, evalValueL md env (Ctx.makeL tabs f) H fv = .panic e m →
      evalValueL md env (Ctx.makeSched tabs g) T gv = .panic e m) := by
  have hyT : y ∈ oT := List.mem_of_getElem? hyj
  have hyS : y ∈ oS := ((B.tMem y).1 hyT).1
  have hid := B.sOwn y hyS fv hfv
  have hDo : ∀ a ∈ oT.take j, a ∈ oT := fun a ha => List.mem_of_mem_take ha
  have hfr : T = { H with regs := T.regs } := frame_eq B.frT Sr.frH I.frT
  have hsx : sxOf (Ctx.makeSched tabs g).f gv = sxOf (Ctx.makeL tabs f).f fv := by
    unfold sxOf; rw [makeSched_f, makeL_f]; exact hr.sx
  have hty : (Ctx.makeSched tabs g).tys[fv.id]? = (Ctx.makeL tabs f).tys[fv.id]? ∨
      fv.op.nilCheck = true := by
    rcases hr.type with h | h
    · exact .inr h
    · exact .inl (by rw [hid]; exact tys_eq S hfv hgv h)
  have hvc := evalValueL_vc (md := md) (env := env) (ctx := Ctx.makeL tabs f)
    (ctx' := Ctx.makeSched tabs g) (fr := H) (fr' := T) hf hr.op hr.aux hr.auxInt hr.id
    (by rw [hr.args, Array.size_map]) (by rw [makeSched_tabs, tabs_makeL]) (params_eq S) act_eq
    hsx hfr hty (fun k a ha => by
      obtain ⟨hg, hgm⟩ := argsF_g hgv hr ha
      obtain ⟨⟨z, hz⟩, ⟨z', hz'⟩, hns, hsp⟩ := argFact S B Sr hPS hPc I hDo hfv hyS hdone ha
        (fun hm => topo_before B.tTopo hyj hgm hm)
      refine ⟨rep f a, z, hg, hz, z', hz', ?_⟩
      cases hs : isSPA f a
      · left; have := hns hs; rw [hz', hz] at this; cases this; rfl
      · right; rw [tabs_makeL]; exact hsp hs)
  refine ⟨fun z hz => ?_, hvc.2⟩
  obtain ⟨z', h1, h2⟩ := hvc.1 z hz
  refine ⟨z', h1, fun hn => h2 ?_⟩
  rcases hty with h | h
  · exact h
  · rw [isNC_of hfv, h] at hn; cases hn

/-- A chain of nil checks of the block whose end is outside it: the end has a register at the
block's entry. -/
theorem chainOutReg {oS oT : List ID} {frPS frPT : Frame} (B : BStep tabs f g md oS oT frPS frPT) :
    ∀ (n : Nat) (a : ID), ncChain (Ctx.makeL tabs f).tys f n a = true → n ≤ f.valueTab.size →
      a ∈ oS → rep f a ∉ oS → ∃ z, frPS.regs[rep f a]? = some (some z)
  | 0, a, h, _, _, _ => by simp [ncChain] at h
  | n + 1, a, h, hk, haS, hrS => by
    obtain ⟨hs, hra, hnext, hfix⟩ := chain_cases h hk
    obtain ⟨hne, -, -⟩ := ncStep_basic hs
    obtain ⟨va, hva⟩ := B.sVal a haS
    have hpa : rep1 f a ∈ argsF f a := by
      rw [argsF_of hva]; exact Array.mem_toList_iff.2 (Array.mem_of_getElem? (rep1_arg0 hva hne))
    rw [hra] at hrS ⊢
    by_cases hpS : rep1 f a ∈ oS
    · cases hpn : isNC f (rep1 f a)
      · rw [hfix hpn] at hrS; exact absurd hpS hrS
      · exact chainOutReg B n _ (hnext hpn) (by omega) hpS hrS
    · exact (B.out a haS _ hpa hpS).2.2.1

/-- **Every argument of a target value has a register** once the values before it ran. -/
theorem targs (S : SchedRel tabs f g) {oS oT : List ID} {frPS frPT H T : Frame} {P : List ID}
    (B : BStep tabs f g md oS oT frPS frPT) {j : Nat} (I : Inv f frPT H T P (oT.take j))
    {y : ID} (hyj : oT[j]? = some y) {fv gv : Value} (hfv : f.value? y = some fv)
    (hgv : g.value? y = some gv) (hr : VRel f g fv gv) :
    ∀ a' ∈ gv.args, ∃ z, T.regs[a']? = some (some z) := by
  intro a' ha'
  obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 ha'
  have : ∃ a, fv.args[k]? = some a ∧ a' = rep f a := by
    rw [hr.args, Array.getElem?_map] at hk
    cases h : fv.args[k]? with
    | none => rw [h] at hk; cases hk
    | some a => rw [h] at hk; cases hk; exact ⟨a, rfl, rfl⟩
  obtain ⟨a, ha, rfl⟩ := this
  obtain ⟨-, hgm⟩ := argsF_g hgv hr ha
  have hyS : y ∈ oS := ((B.tMem y).1 (List.mem_of_getElem? hyj)).1
  obtain ⟨hrn, hrs, -, -⟩ := use_rep (S.argUse hfv ha)
  by_cases hr' : rep f a ∈ oT
  · exact I.some _ (topo_before B.tTopo hyj hgm hr')
  · have hrS : rep f a ∉ oS := fun h => hr' ((B.tMem _).2 ⟨h, hrs⟩)
    rw [I.out _ (fun h => hr' (List.mem_of_mem_take h)), B.agree _ hrn hrs]
    have haf : a ∈ argsF f y := by
      rw [argsF_of hfv]; exact Array.mem_toList_iff.2 (Array.mem_of_getElem? ha)
    by_cases haS : a ∈ oS
    · -- `a` is a bypassed value of the block: an `SPanchored` (one step) or a nil-check chain
      have hne : rep f a ≠ a := fun h => hrS (by rw [h]; exact haS)
      have hu := S.argUse hfv ha
      by_cases hs : isSPA f a = true
      · obtain ⟨-, -, hne1, -, -, -, hr1⟩ := use_spa hu hs
        obtain ⟨va, hva⟩ := B.sVal a haS
        have h0 := rep1_arg0 hva hne1
        have hm : rep1 f a ∈ argsF f a := by
          rw [argsF_of hva]; exact Array.mem_toList_iff.2 (Array.mem_of_getElem? h0)
        rw [hr1] at hrS ⊢
        exact (B.out a haS _ hm hrS).1
      · have hn : isNC f a = true := by
          cases h : isNC f a
          · exact absurd (rep_self h (by simpa using hs)) hne
          · rfl
        exact chainOutReg B _ a (use_chain hu hn) (Nat.le_refl _) haS hrS
    · exact (B.out y hyS a haf haS).2.2.1

/-! ## The walk -/

theorem take_succ_of {o : List ID} {j : Nat} {y : ID} (h : o[j]? = some y) :
    o.take (j + 1) = o.take j ++ [y] := by
  rw [List.take_add_one, h]; rfl

theorem not_mem_take_of {o : List ID} (hnd : o.Nodup) {j : Nat} {y : ID} (h : o[j]? = some y) :
    y ∉ o.take j := by
  intro hm
  have hs := split_at h
  rw [hs] at hnd
  exact (List.nodup_append.1 hnd).2.2 y hm y List.mem_cons_self rfl

/-- The invariant after one more target value. -/
theorem inv_step {frPT H T : Frame} {P : List ID} {oT : List ID} (hnd : oT.Nodup) {j : Nat}
    (I : Inv f frPT H T P (oT.take j)) {y : ID} (hyj : oT[j]? = some y) {z : Val}
    (hlt : y < T.regs.size) (hin : y ∈ P → isNC f y = false → H.regs[y]? = some (some z)) :
    Inv f frPT H (T.set y z) P (oT.take (j + 1)) := by
  rw [take_succ_of hyj]
  have hy := not_mem_take_of hnd hyj
  refine ⟨?_, ?_, fun a ha => ?_, fun a ha haP han => ?_, fun a ha => ?_⟩
  · rw [I.frT]; rfl
  · simp [Frame.set, I.size]
  · have hya : y ≠ a := fun h => ha (by rw [← h]; simp)
    rw [Frame.set_regs_ne hya, I.out a (fun h => ha (List.mem_append_left _ h))]
  · rcases List.mem_append.1 ha with ha | ha
    · have hya : y ≠ a := fun h => hy (h ▸ ha)
      rw [Frame.set_regs_ne hya, I.inP a ha haP han]
    · simp at ha; subst ha; rw [Frame.set_regs_self hlt, hin haP han]
  · rcases List.mem_append.1 ha with ha | ha
    · have hya : y ≠ a := fun h => hy (h ▸ ha)
      rw [Frame.set_regs_ne hya]; exact I.some a ha
    · simp at ha; subst ha; exact ⟨z, Frame.set_regs_self hlt⟩

/-- **The walk along the target order**, given what each value does. -/
theorem walk_gen (S : SchedRel tabs f g) {oS oT : List ID} {frPS frPT H : Frame} {P : List ID}
    (B : BStep tabs f g md oS oT frPS frPT) {e : Panic} {m : Mem} :
    ∀ (n : Nat), n ≤ oT.length →
      (∀ j T y gv, j < n → Inv f frPT H T P (oT.take j) → oT[j]? = some y →
        g.value? y = some gv →
        evalValueL md env (Ctx.makeSched tabs g) T gv = .panic e m ∨
          ∃ z, evalValueL md env (Ctx.makeSched tabs g) T gv = .ok z ∧
            (y ∈ P → isNC f y = false → H.regs[y]? = some (some z))) →
      evalAllL md env (Ctx.makeSched tabs g) frPT (oT.take n) = .panic e m ∨
        ∃ T, evalAllL md env (Ctx.makeSched tabs g) frPT (oT.take n) = .ok T ∧
          Inv f frPT H T P (oT.take n)
  | 0, _, _ => .inr ⟨frPT, by simp; rfl, ⟨by rfl, rfl, fun _ _ => rfl, fun _ h => by simp at h,
      fun _ h => by simp at h⟩⟩
  | n + 1, hn, hstep => by
    obtain ⟨y, hy⟩ : ∃ y, oT[n]? = some y := ⟨oT[n], List.getElem?_eq_getElem (by omega)⟩
    rcases walk_gen S B n (by omega) (fun j T y gv hj => hstep j T y gv (by omega)) with h | ⟨T, hT, I⟩
    · left
      rw [take_succ_of hy, evalAllL_append, h]
    · obtain ⟨fv, gv, hfv, hgv, -⟩ := tval S B (List.mem_of_getElem? hy)
      have hev : evalAllL md env (Ctx.makeSched tabs g) frPT (oT.take (n + 1)) =
          evalAllL md env (Ctx.makeSched tabs g) T [y] := by
        rw [take_succ_of hy, evalAllL_append, hT]
      rw [hev, evalAllL_cons, stepVL_of (by rw [makeSched_f]; exact hgv)]
      rcases hstep n T y gv (by omega) I hy hgv with hp | ⟨z, hz, hin⟩
      · rw [hp]; exact .inl rfl
      · rw [hz]
        have hlt : y < T.regs.size := by
          rw [I.size, B.size, B.sizeS]; exact lt_of_value? hfv
        exact .inr ⟨T.set y z, rfl, inv_step B.tNodup I hy hlt hin⟩

end GoFV.Proof.SchedL

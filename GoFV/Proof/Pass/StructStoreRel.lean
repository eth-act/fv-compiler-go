import GoFV.Opt.RewriteCheck
import GoFV.SSA.Sem.TyEq

/-!
# Struct-store splits: the relation (issue #151)

What the checker `GoFV.Opt.RewriteCheck.ssRel` says, declaratively: a split `Store` (`SplitD`,
from `ssSplit?`) with its fields' links (`Link`, from `ssLink`), and the relation's global and
per-block facts (`ssRel_spec`, `BlockSpec`).
-/

namespace GoFV.Proof.StructStore

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.RewriteCheck

variable {tabs : Tables} {f g : Func}

/-- Field `k` of a split: what `ssLink` checks. -/
structure Link (tabs : Tables) (f g : Func) (b dst : ID) (ps : List (ID × ID)) (m0 : ID)
    (k o : Nat) (t : Ty) (a p s : ID) (av sv ov : Value) : Prop where
  ha : f.value? a = some av
  haty : tabs.ty av.type = t
  hs : g.value? s = some sv
  hsf : f.value? s = none
  hsid : sv.id = s
  hsop : sv.op = .Store
  hsbl : sv.block = b
  hsargs : sv.args = #[p, sv.args[1]!, if k = 0 then m0 else (ps[k - 1]?.map (·.2)).getD 0]
  hw : copyReach tabs f.valueTab f.valueTab.size a sv.args[1]! = true
  hsty : auxTy tabs sv.aux = t
  hp : g.value? p = some ov
  hpf : f.value? p = none
  hpid : ov.id = p
  hpop : ov.op = .OffPtr
  hpbl : ov.block = b
  hpargs : ov.args = #[ov.args[0]!]
  hdst : copyReach tabs f.valueTab f.valueTab.size dst ov.args[0]! = true
  hpai : ov.auxInt = Int64.ofNat o
  hpty : isPtrTy (tabs.ty ov.type) = true

theorem args3 {xs : Array ID} (h : xs.size = 3) : xs = #[xs[0]!, xs[1]!, xs[2]!] := by
  apply Array.ext (by simp [h])
  intro i h1 h2
  rcases i with _ | _ | _ | i
  · simp [getElem!_pos xs 0 (by omega)]
  · simp [getElem!_pos xs 1 (by omega)]
  · simp [getElem!_pos xs 2 (by omega)]
  · simp at h2; omega

theorem args1 {xs : Array ID} (h : xs.size = 1) : xs = #[xs[0]!] := by
  apply Array.ext (by simp [h])
  intro i h1 h2
  have : i = 0 := by simp at h2; omega
  subst this; simp [getElem!_pos xs 0 (by omega)]

theorem ssLink_spec {b dst : ID} {fs : List (Nat × Ty)} {as : Array ID} {ps : List (ID × ID)}
    {m0 : ID} {k : Nat} (h : ssLink tabs f g b dst fs as ps m0 k = true) :
    ∃ o t a p s av sv ov, fs[k]? = some (o, t) ∧ as[k]? = some a ∧ ps[k]? = some (p, s) ∧
      Link tabs f g b dst ps m0 k o t a p s av sv ov := by
  unfold ssLink at h
  split at h
  next o t a p s hf ha hp =>
    dsimp only at h
    split at h
    next av sv ov h1 h2 h3 =>
      simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none, and_assoc] at h
      obtain ⟨hat, hsf, hsid, hsop, hsbl, hs3, hs0, hs2, hw, hst, hpf, hpid, hpop, hpbl, hp1, hd,
        hai, hpt⟩ := h
      refine ⟨o, t, a, p, s, av, sv, ov, hf, ha, hp, ⟨h1, Ty.eq_of_beq hat, h2, hsf, hsid, hsop,
        hsbl, ?_, hw, Ty.eq_of_beq hst, h3, hpf, hpid, hpop, hpbl, args1 hp1, hd, hai, hpt⟩⟩
      rw [args3 hs3, hs0, hs2]
      simp
    next => simp at h
  next => simp at h

/-- What `ssSplit? tabs f g x = some ps` says. -/
structure SplitD (tabs : Tables) (f g : Func) (x : ID) (ps : List (ID × ID)) where
  fv : Value
  gv : Value
  smv : Value
  dst : ID
  sm : ID
  mem : ID
  m0 : ID
  fs : List (Nat × Ty)
  n : Nat
  hfv : f.value? x = some fv
  hgv : g.value? x = some gv
  hfargs : fv.args = #[dst, sm, mem]
  hop : fv.op = .Store
  haux : auxTy tabs fv.aux = .agg fs n
  hsmv : f.value? (copyEnd tabs f.valueTab f.valueTab.size sm) = some smv
  hsmop : smv.op = .StructMake
  hsmty : tabs.ty smv.type = .agg fs n
  hlay : layoutsOK n fs = true
  hlt : ∀ q ∈ fs, q.1 < n
  hsmsz : smv.args.size = fs.length
  hgop : gv.op = .Copy
  hgid : gv.id = x
  hgty : gv.type = fv.type
  hgbl : gv.block = fv.block
  hgargs : gv.args = #[(ps.getLast?.map (·.2)).getD m0]
  hlen : ps.length = fs.length
  hm0 : copyReach tabs f.valueTab f.valueTab.size mem m0 = true
  hlink : ∀ k < fs.length, ssLink tabs f g fv.block dst fs smv.args ps m0 k = true

theorem toList_eq3 {xs : Array ID} {a b c : ID} (h : xs.toList = [a, b, c]) : xs = #[a, b, c] := by
  rcases xs with ⟨l⟩; simp only [List.toList_toArray] at h; rw [h]

theorem toList_eq1 {xs : Array ID} {a : ID} (h : xs.toList = [a]) : xs = #[a] := by
  rcases xs with ⟨l⟩; simp only [List.toList_toArray] at h; rw [h]

theorem ssSplit_spec {x : ID} {ps : List (ID × ID)} (h : ssSplit? tabs f g x = some ps) :
    Nonempty (SplitD tabs f g x ps) := by
  unfold ssSplit? at h
  split at h
  next fv gv hfv hgv =>
    split at h
    next dst sm mem fs n last hfa hax hga =>
      split at h
      next smv hsmv =>
        dsimp only at h
        split at h
        next hc =>
          cases h
          simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
            List.mem_range, and_assoc] at hc
          obtain ⟨hop, hsmop, hsmty, hlay, hlt, hsz, hgop, hgid, hgty, hgbl, hgax, hgai, hlen, hlast,
            hm0, hlink⟩ := hc
          exact ⟨⟨fv, gv, smv, dst, sm, mem, (ssWalk g fs.length last).2, fs, n, hfv, hgv,
            toList_eq3 hfa, hop, hax, hsmv, hsmop, Ty.eq_of_beq hsmty, hlay,
            fun q hq => by simpa using hlt q hq, hsz, hgop, hgid, hgty, hgbl,
            by rw [toList_eq1 hga]; exact congrArg (fun y => #[y]) hlast, hlen, hm0, fun k hk => hlink k hk⟩⟩
        next => simp at h
      next => simp at h
    next => simp at h
  next => simp at h

/-- A well laid-out aggregate's fields lie inside it. -/
theorem layoutsOK_in {n : Nat} : {fs : List (Nat × Ty)} → layoutsOK n fs = true →
    ∀ q ∈ fs, q.1 + q.2.size ≤ n
  | [], _, _, h => absurd h List.not_mem_nil
  | (o, t) :: fs, h, q, hq => by
    unfold layoutsOK at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.1 hq with rfl | hq
    · exact h.1.1
    · exact layoutsOK_in h.2 q hq

/-- The splits of `f` by ID (`ssRel`'s array). -/
theorem splits_get (x : ID) :
    ((Array.range f.valueTab.size).map (ssSplit? tabs f g))[x]?.join = ssSplit? tabs f g x := by
  rw [Array.getElem?_map, Array.getElem?_range]
  split
  · rfl
  · rename_i hx
    unfold ssSplit?
    have : f.value? x = none := by
      unfold Func.value?; rw [Array.getElem?_eq_none (by omega)]; rfl
    simp [this]

/-- The fresh values of a split: its chain's pointers and stores. -/
def Fresh (tabs : Tables) (f g : Func) (z : ID) : Prop :=
  ∃ x ps, ssSplit? tabs f g x = some ps ∧ ∃ q ∈ ps, z = q.1 ∨ z = q.2

theorem news_mem {z : ID}
    (h : z ∈ ((Array.range f.valueTab.size).map (ssSplit? tabs f g)).toList.flatMap
      fun s => (s.getD []).flatMap fun (p, m) => [p, m]) : Fresh tabs f g z := by
  simp only [List.mem_flatMap, Array.toList_map, List.mem_map, Array.toList_range,
    List.mem_range] at h
  obtain ⟨s, ⟨x, -, rfl⟩, q, hq, hz⟩ := h
  cases hs : ssSplit? tabs f g x with
  | none => rw [hs] at hq; simp at hq
  | some ps =>
    rw [hs] at hq
    refine ⟨x, ps, hs, q, by simpa using hq, ?_⟩
    simp at hz
    rcases hz with h | h <;> simp [h]

/-- One block of `ssRel`. -/
structure BlockSpec (tabs : Tables) (f g : Func) (bid : ID) (fb gb : Block) : Prop where
  kind : gb.kind = fb.kind
  controls : gb.controls = fb.controls
  values : ∃ E : Array ID, gb.values = fb.values ++ E ∧
    ∀ z ∈ E, f.value? z = none ∧ Fresh tabs f g z ∧ ∃ v, g.value? z = some v ∧ v.block = bid
  sched : ∀ oS, Sem.schedule f fb = some oS → ∃ oT, Sem.schedule g gb = some oT ∧
    oT.toList.filter (CSE.rootNode g) =
      ssRoots ((Array.range f.valueTab.size).map (ssSplit? tabs f g))
        (oS.toList.filter (CSE.rootNode f))

/-- **What `ssRel` says.** -/
structure SRel (tabs : Tables) (f g : Func) : Prop where
  cfg : DomCert.cfgView g = DomCert.cfgView f
  ownAux : g.ownAux = f.ownAux
  size : f.valueTab.size ≤ g.valueTab.size
  value : ∀ x fv, f.value? x = some fv → ∃ gv, g.value? x = some gv ∧
    (ssSame fv gv = true ∨ ∃ ps, ssSplit? tabs f g x = some ps)
  listed : ∀ x ps fv, ssSplit? tabs f g x = some ps → f.value? x = some fv →
    ∃ gb, g.block? fv.block = some gb ∧ ∀ q ∈ ps, q.1 ∈ gb.values ∧ q.2 ∈ gb.values
  block : ∀ bid ∈ f.blocks, ∀ fb, f.block? bid = some fb → ∃ gb, g.block? bid = some gb ∧
    BlockSpec tabs f g bid fb gb

theorem extract_append {a : Array ID} {k : Nat} (hk : k ≤ a.size) :
    a = a.extract 0 k ++ a.extract k a.size := by
  apply Array.ext (by simp; omega)
  intro i h1 h2
  simp only [Array.getElem_append, Array.size_extract, Array.getElem_extract]
  split <;> (congr 1; omega)

theorem ssRel_spec (h : ssRel tabs f g = true) : SRel tabs f g := by
  unfold ssRel at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Array.all_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨hcfg, hown⟩, hsz⟩, hval⟩, -⟩, hlist⟩, hblk⟩ := h
  refine ⟨hcfg, hown, hsz, fun x fv hfv => ?_, fun x ps fv hs hfv => ?_, fun bid hb fb hfb => ?_⟩
  · have hx : x < f.valueTab.size := by
      unfold Func.value? at hfv
      rcases Nat.lt_or_ge x f.valueTab.size with h | h
      · exact h
      · rw [Array.getElem?_eq_none h] at hfv; cases hfv
    have := hval x hx
    rw [hfv] at this
    cases hgv : g.value? x with
    | none => rw [hgv] at this; cases this
    | some gv =>
      rw [hgv] at this
      simp only [Bool.or_eq_true, splits_get, Option.isSome_iff_exists] at this
      exact ⟨gv, rfl, this.imp id fun ⟨ps, h⟩ => ⟨ps, h⟩⟩
  · have hx : x < f.valueTab.size := by
      unfold Func.value? at hfv
      rcases Nat.lt_or_ge x f.valueTab.size with h | h
      · exact h
      · rw [Array.getElem?_eq_none h] at hfv; cases hfv
    have := hlist x hx
    rw [splits_get, hs, hfv] at this
    simp only [Option.any_eq_true, List.all_eq_true, Bool.and_eq_true,
      Array.contains_iff_mem] at this
    obtain ⟨gb, hgb, hall⟩ := this
    exact ⟨gb, hgb, fun q hq => hall q hq⟩
  · have := hblk bid hb
    unfold ssBlockOK at this
    rw [hfb] at this
    cases hgb : g.block? bid with
    | none => rw [hgb] at this; cases this
    | some gb =>
      rw [hgb] at this
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Array.all_eq_true] at this
      obtain ⟨⟨⟨⟨⟨hk, hc⟩, hle⟩, hpre⟩, hext⟩, hsch⟩ := this
      refine ⟨gb, rfl, hk, hc, ⟨gb.values.extract fb.values.size gb.values.size, ?_, ?_⟩, ?_⟩
      · conv => lhs; rw [extract_append hle]
        rw [hpre]
      · intro z hz
        obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hz
        have := hext i hi
        simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, List.contains_iff_mem,
          Option.any_eq_true, beq_iff_eq] at this
        obtain ⟨⟨h1, h2⟩, v, h3, h4⟩ := this
        exact ⟨h1, news_mem h2, v, h3, h4⟩
      · intro oS hoS
        rw [hoS] at hsch
        simp only at hsch
        cases hoT : Sem.schedule g gb with
        | none => rw [hoT] at hsch; cases hsch
        | some oT =>
          rw [hoT] at hsch
          exact ⟨oT, rfl, by simpa using hsch⟩

end GoFV.Proof.StructStore

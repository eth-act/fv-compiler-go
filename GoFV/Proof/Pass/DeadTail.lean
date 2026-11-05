import GoFV.Proof.Pass.DeadRel
import GoFV.Opt.Deadcode
import GoFV.Proof.Pass.DeadLive

/-!
# deadcode after copyelim: the static relation

`deadTail` is the part of `deadcode` after `copyelim` (`deadcode_eq`): liveness, `pruneNames`,
`unlink`, `moveStmts`, `freeDead`. `deadTail_rel`: its output is related to its input by
`DeadRel` with the kept blocks `(· ∈ g.blocks)`.

`Sk r live f g`: `g` is `f` up to names, positions, use counts, caches, the controls of
unreachable blocks and the arguments of dead values (what `pruneNames`, `unlink` and
`moveStmts` change). `freeDead` (`freeDead_spec`) then drops the dead values from the tables
and the block lists and the unreachable blocks from `f.Blocks`.
-/

open Std.Do

set_option mvcgen.warning false

namespace GoFV.Proof.Dead

open GoFV.SSA GoFV.Opt GoFV.Proof

/-- `deadcode` after `copyelim`. -/
def deadTail (tabs : Tables) (reachable : Array Bool) (f : Func) : Except String Func := do
  let (live, order) := f.liveValuesOrder tabs reachable
  let f := Deadcode.pruneNames live f
  let some pending := XPosMap.ofCache f.cache.lineStarts
    | throw "deadcode: f.cachedLineStarts is nil"
  let (f, pending) ← Deadcode.unlink reachable live f pending.clear
  let (f, pending) := Deadcode.moveStmts order f pending
  let f := { f with cache := { f.cache with lineStarts := some pending.toCache } }
  Deadcode.freeDead reachable live f

theorem deadcode_eq (tabs : Tables) (f : Func) :
    deadcode tabs f = (copyelim tabs (Deadcode.removeFirstEdges f.reachableBlocks
      (Deadcode.removeDeadEdges f.reachableBlocks f))).bind (deadTail tabs f.reachableBlocks) :=
  rfl

/-! ## Loops -/

theorem forIn'_list_mono {ε α σ : Type} (I : σ → Prop) : ∀ (xs : List α) {init r : σ}
    {body : (a : α) → a ∈ xs → σ → Except ε (ForInStep σ)},
    (∀ a ha s s', I s → body a ha s = .ok s' → I s'.value) → I init →
    forIn' xs init body = .ok r → I r
  | [], init, r, body, _, h0, h => by
    rw [List.forIn'_nil] at h; cases h; exact h0
  | a :: as, init, r, body, hb, h0, h => by
    rw [List.forIn'_cons] at h
    obtain ⟨s', h1, h2⟩ := CheckFacts.bind_ok h
    have hs := hb a _ init s' h0 h1
    cases s' with
    | done t => cases h2; exact hs
    | yield t => exact forIn'_list_mono I as (fun a ha s s' => hb a _ s s') hs h2

theorem forIn'_range_mono {ε σ : Type} (I : σ → Prop) {n : Nat} {init r : σ}
    {body : (i : Nat) → i ∈ [:n] → σ → Except ε (ForInStep σ)}
    (hb : ∀ i hi s s', I s → body i hi s = .ok s' → I s'.value) (h0 : I init)
    (h : forIn' [:n] init body = .ok r) : I r := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range'] at h
  exact forIn'_list_mono I _ (fun a ha s s' => hb a _ s s') h0 h

theorem bnot_ne {b : Bool} (h : (!b) = true) : b ≠ true := by
  cases b <;> simp_all

/-! ## `Sk`: what `pruneNames`, `unlink` and `moveStmts` keep -/

/-- A value up to position, use count and (if dead) arguments. -/
def VSk (live : Array Bool) (x : ID) (fv gv : Value) : Prop :=
  gv.op = fv.op ∧ gv.type = fv.type ∧ gv.aux = fv.aux ∧ gv.auxInt = fv.auxInt ∧
    gv.block = fv.block ∧ (live.getD x false = true → gv.args = fv.args)

/-- A block up to position, likeliness, predecessors and (if unreachable) controls. -/
def BSk (r : Array Bool) (bid : ID) (fb gb : Block) : Prop :=
  gb.kind = fb.kind ∧ gb.succs = fb.succs ∧ gb.values = fb.values ∧
    (r.getD bid false = true → gb.controls = fb.controls)

theorem VSk.refl {live : Array Bool} {x : ID} {v : Value} : VSk live x v v :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

theorem VSk.trans {live : Array Bool} {x : ID} {a b c : Value} (h1 : VSk live x a b)
    (h2 : VSk live x b c) : VSk live x a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
    h2.2.2.2.2.1.trans h1.2.2.2.2.1,
    fun hl => (h2.2.2.2.2.2 hl).trans (h1.2.2.2.2.2 hl)⟩

theorem BSk.refl {r : Array Bool} {bid : ID} {b : Block} : BSk r bid b b :=
  ⟨rfl, rfl, rfl, fun _ => rfl⟩

theorem BSk.trans {r : Array Bool} {bid : ID} {a b c : Block} (h1 : BSk r bid a b)
    (h2 : BSk r bid b c) : BSk r bid a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
    fun hr => (h2.2.2.2 hr).trans (h1.2.2.2 hr)⟩

structure Sk (r live : Array Bool) (f g : Func) : Prop where
  blocks : g.blocks = f.blocks
  entry : g.entry = f.entry
  ownAux : g.ownAux = f.ownAux
  vsize : g.valueTab.size = f.valueTab.size
  block : ∀ bid gb, g.block? bid = some gb → ∃ fb, f.block? bid = some fb ∧ BSk r bid fb gb
  value : ∀ x gv, g.value? x = some gv → ∃ fv, f.value? x = some fv ∧ VSk live x fv gv

theorem Sk.refl {r live : Array Bool} {f : Func} : Sk r live f f :=
  ⟨rfl, rfl, rfl, rfl, fun _ gb h => ⟨gb, h, BSk.refl⟩, fun _ gv h => ⟨gv, h, VSk.refl⟩⟩

theorem Sk.trans {r live : Array Bool} {f g h : Func} (h1 : Sk r live f g) (h2 : Sk r live g h) :
    Sk r live f h where
  blocks := h2.blocks.trans h1.blocks
  entry := h2.entry.trans h1.entry
  ownAux := h2.ownAux.trans h1.ownAux
  vsize := h2.vsize.trans h1.vsize
  block bid hb hh := by
    obtain ⟨gb, hg, s2⟩ := h2.block bid hb hh
    obtain ⟨fb, hf, s1⟩ := h1.block bid gb hg
    exact ⟨fb, hf, s1.trans s2⟩
  value x hv hh := by
    obtain ⟨gv, hg, s2⟩ := h2.value x hv hh
    obtain ⟨fv, hf, s1⟩ := h1.value x gv hg
    exact ⟨fv, hf, s1.trans s2⟩

theorem value?_modV (F : Func) (v : ID) (g : Value → Value) (x : ID) :
    (F.modV v g).value? x = if v = x then (F.value? x).map g else F.value? x := by
  unfold Func.modV Func.value?
  simp only [Array.getElem?_modify]
  split
  · cases F.valueTab[x]? with
    | none => rfl
    | some o => cases o <;> rfl
  · rfl

private theorem block?_modB (F : Func) (b : ID) (k : Block → Block) (x : ID) :
    (F.modB b k).block? x = if b = x then (F.block? x).map k else F.block? x := by
  unfold Func.modB Func.block?
  simp only [Array.getElem?_modify]
  split
  · cases F.blockTab[x]? with
    | none => rfl
    | some o => cases o <;> rfl
  · rfl

theorem Sk.modV {r live : Array Bool} {f g : Func} (h : Sk r live f g) (v : ID)
    (k : Value → Value) (hk : ∀ u, VSk live v u (k u)) : Sk r live f (g.modV v k) where
  blocks := h.blocks
  entry := h.entry
  ownAux := h.ownAux
  vsize := by
    show (g.valueTab.modify v (Option.map k)).size = _
    rw [Array.size_modify]; exact h.vsize
  block := h.block
  value x gv hx := by
    rw [value?_modV] at hx
    split at hx
    · subst_vars
      obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.1 hx
      obtain ⟨fv, hfv, hs⟩ := h.value _ u hu
      exact ⟨fv, hfv, hs.trans (hk u)⟩
    · exact h.value x gv hx

theorem Sk.modB {r live : Array Bool} {f g : Func} (h : Sk r live f g) (b : ID)
    (k : Block → Block) (hk : ∀ u, BSk r b u (k u)) : Sk r live f (g.modB b k) where
  blocks := h.blocks
  entry := h.entry
  ownAux := h.ownAux
  vsize := h.vsize
  block x gb hx := by
    rw [block?_modB] at hx
    split at hx
    · subst_vars
      obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.1 hx
      obtain ⟨fb, hfb, hs⟩ := h.block _ u hu
      exact ⟨fb, hfb, hs.trans (hk u)⟩
    · exact h.block x gb hx
  value := h.value

theorem Sk.decUses {r live : Array Bool} {f g : Func} (h : Sk r live f g) (a : ID) :
    Sk r live f (g.decUses a) :=
  h.modV a _ fun _ => ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

theorem Sk.foldl_decUses {r live : Array Bool} {f : Func} (xs : Array ID) {g : Func}
    (h : Sk r live f g) : Sk r live f (xs.foldl Func.decUses g) := by
  rw [← Array.foldl_toList]
  induction xs.toList generalizing g with
  | nil => exact h
  | cons a as ih => exact ih (h.decUses a)

theorem Sk.resetArgs {r live : Array Bool} {f g : Func} (h : Sk r live f g) {v : ID}
    (hd : live.getD v false ≠ true) : Sk r live f (g.resetArgs v) := by
  unfold Func.resetArgs
  exact (h.foldl_decUses _).modV v _ fun _ => ⟨rfl, rfl, rfl, rfl, rfl, fun hl => absurd hl hd⟩

theorem Sk.resetControls {r live : Array Bool} {f g : Func} (h : Sk r live f g) {b : ID}
    (hr : r.getD b false ≠ true) : Sk r live f (g.resetControls b) := by
  unfold Func.resetControls
  exact (h.foldl_decUses _).modB b _ fun _ => ⟨rfl, rfl, rfl, fun h' => absurd h' hr⟩

theorem unlink_sk {r live : Array Bool} {f g : Func} {p p' : XPosMap}
    (h : Deadcode.unlink r live f p = .ok (g, p')) : Sk r live f g := by
  unfold Deadcode.unlink at h
  dsimp only at h
  obtain ⟨s, hs, h⟩ := CheckFacts.bind_ok h
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h)
  refine forIn'_range_mono (fun s : Func × XPosMap => Sk r live f s.1) ?_ Sk.refl hs
  intro i hi s s' hI hb
  split at hb <;>
  · obtain ⟨t, ht, hb⟩ := CheckFacts.bind_ok hb
    cases Except.ok.inj hb
    refine CheckFacts.forIn_array_inv (fun _ t => Sk r live f t.1) ?_ ?_ ht
    · first | exact hI | exact hI.resetControls (bnot_ne (by with_reducible assumption))
    · intro pre x t t' hI hb
      split at hb
      · rename_i hc
        have hI2 := hI.resetArgs (bnot_ne hc)
        split at hb
        · obtain ⟨q, -, hb⟩ := CheckFacts.bind_ok hb
          exact ⟨_, (Except.ok.inj hb).symm, hI2⟩
        · exact ⟨_, (Except.ok.inj hb).symm, hI2⟩
      · exact ⟨_, (Except.ok.inj hb).symm, hI⟩

theorem move_sk {r live : Array Bool} {o : Array ID} {f g : Func} {p p' : XPosMap}
    (h : Deadcode.moveStmts o f p = (g, p')) : Sk r live f g := by
  apply Id.of_wp_run_eq h (fun res => Sk r live f res.1)
  mvcgen
  case inv1 => exact ⇓⟨_, g, _⟩ => ⌜Sk r live f g⌝
  case inv2 => exact ⇓⟨_, g⟩ => ⌜Sk r live f g⌝
  all_goals mleave
  all_goals first
    | exact Sk.refl
    | (rename_i hI
       first
        | exact hI
        | exact hI.modV _ _ fun _ => ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
        | exact hI.modB _ _ fun _ => ⟨rfl, rfl, rfl, fun _ => rfl⟩)

/-! ## `freeDead` -/

theorem unCacheLine_consts {F F' : Func} {v : ID} {k : Int64} (h : F.unCacheLine v k = some F') :
    ∃ c, F' = { F with consts := c } := by
  unfold Func.unCacheLine at h
  cases h1 : F.constLine? k with
  | none => rw [h1] at h; cases h
  | some li =>
    rw [h1] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    cases h2 : (F.consts[li]!.2).idxOf? v with
    | none => rw [h2] at h; cases h
    | some i =>
      rw [h2] at h
      simp only [Option.bind_some, pure] at h
      split at h
      · cases h; exact ⟨_, rfl⟩
      · cases h; exact ⟨_, rfl⟩

theorem unCache_consts (F : Func) (v : ID) : ∃ c, F.unCache v = { F with consts := c } := by
  unfold Func.unCache
  dsimp only
  cases h : F.unCacheLine v (F.getV v).auxInt with
  | some F' => exact unCacheLine_consts h
  | none =>
    dsimp only
    split
    · exact ⟨_, rfl⟩
    · split <;>
      · split
        · exact ⟨_, rfl⟩
        · cases h' : F.unCacheLine v _ with
          | none => exact ⟨_, rfl⟩
          | some F' => exact unCacheLine_consts h'

theorem join_set_none {α : Type} {a : Array (Option α)} {v x : Nat} {u : α}
    (h : ((a.set! v none)[x]?).join = some u) : (a[x]?).join = some u := by
  rw [Array.set!_eq_setIfInBounds] at h
  by_cases hvx : v = x
  · subst hvx
    by_cases hlt : v < a.size
    · rw [Array.getElem?_setIfInBounds_self_of_lt hlt] at h; cases h
    · rw [Array.getElem?_eq_none (by rw [Array.size_setIfInBounds]; omega)] at h; cases h
  · rwa [Array.getElem?_setIfInBounds_ne hvx] at h

/-- Freeing values keeps the block list and shrinks the value table. -/
structure Fr (F G : Func) : Prop where
  blocks : G.blocks = F.blocks
  entry : G.entry = F.entry
  ownAux : G.ownAux = F.ownAux
  vsize : G.valueTab.size = F.valueTab.size
  value : ∀ x v, G.value? x = some v → F.value? x = some v

theorem Fr.refl {F : Func} : Fr F F := ⟨rfl, rfl, rfl, rfl, fun _ _ h => h⟩

theorem Fr.trans {F G H : Func} (h1 : Fr F G) (h2 : Fr G H) : Fr F H :=
  ⟨h2.blocks.trans h1.blocks, h2.entry.trans h1.entry, h2.ownAux.trans h1.ownAux,
    h2.vsize.trans h1.vsize, fun x v h => h1.value x v (h2.value x v h)⟩

theorem freeValue_fr (G : Func) (v : ID) :
    Fr G (G.freeValue v) ∧ (G.freeValue v).blockTab = G.blockTab := by
  obtain ⟨c, hc⟩ := unCache_consts G v
  unfold Func.freeValue
  rw [hc]
  refine ⟨⟨rfl, rfl, rfl, ?_, fun x u h => join_set_none h⟩, rfl⟩
  show (G.valueTab.set! v none).size = _
  rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

/-- The blocks of `G` after `freeDead`'s first loop has done the blocks `pre` of `F`. -/
def BI (live : Array Bool) (F : Func) (pre : List ID) (G : Func) : Prop :=
  ∀ bid gb, G.block? bid = some gb → ∃ fb, F.block? bid = some fb ∧ gb.kind = fb.kind ∧
    gb.succs = fb.succs ∧ gb.controls = fb.controls ∧
    (gb.values = fb.values.filter (live.getD · false) ∨ (bid ∉ pre ∧ gb.values = fb.values))

theorem freeDead_spec {r live : Array Bool} {F g : Func}
    (h : Deadcode.freeDead r live F = .ok g) :
    g.entry = F.entry ∧ g.ownAux = F.ownAux ∧ g.valueTab.size = F.valueTab.size ∧
    (∀ x v, g.value? x = some v → F.value? x = some v) ∧
    (∀ bid ∈ g.blocks, bid ∈ F.blocks ∧ r.getD bid false = true) ∧
    (∀ bid gb, bid ∈ F.blocks → g.block? bid = some gb → ∃ fb, F.block? bid = some fb ∧
      gb.kind = fb.kind ∧ gb.succs = fb.succs ∧ gb.controls = fb.controls ∧
      gb.values = fb.values.filter (live.getD · false)) := by
  unfold Deadcode.freeDead at h
  dsimp only at h
  obtain ⟨G1, h1, h⟩ := CheckFacts.bind_ok h
  -- the first loop: dead values freed, block value lists filtered
  have hI1 := CheckFacts.forIn_array_inv (fun pre G => Fr F G ∧ BI live F pre G)
    ⟨Fr.refl, fun bid gb hb => ⟨gb, hb, rfl, rfl, rfl, .inr ⟨List.not_mem_nil, rfl⟩⟩⟩ ?_ h1
  rotate_left
  · intro pre b G G' ⟨hF, hB⟩ hb
    obtain ⟨s, hs, hb⟩ := CheckFacts.bind_ok hb
    cases Except.ok.inj hb
    have hJ := CheckFacts.forIn_array_inv
      (fun pre (t : Func × Array ID) => Fr G t.1 ∧ t.1.blockTab = G.blockTab ∧
        t.2.toList = pre.filter (live.getD · false))
      ⟨Fr.refl, rfl, rfl⟩ ?_ hs
    rotate_left
    · intro pre x t t' ⟨htF, htB, htK⟩ hb
      split at hb
      · rename_i hl
        refine ⟨_, (Except.ok.inj hb).symm, htF, htB, ?_⟩
        rw [Array.toList_push, htK, List.filter_append]
        simp only [List.filter_cons, List.filter_nil, hl, ↓reduceIte]
      · rename_i hl
        refine ⟨_, (Except.ok.inj hb).symm, htF.trans (freeValue_fr _ _).1,
          (freeValue_fr _ _).2.trans htB, ?_⟩
        rw [htK, List.filter_append]
        simp only [List.filter_cons, List.filter_nil, Bool.eq_false_iff.2 hl, Bool.false_eq_true,
          ↓reduceIte, List.append_nil]
    obtain ⟨hsF, hsB, hsK⟩ := hJ
    have hkept : s.2 = (G.getB b).values.filter (live.getD · false) := by
      apply Array.toList_inj.1
      rw [hsK, Array.toList_filter]
    refine ⟨_, rfl, ⟨(hF.trans hsF).blocks, (hF.trans hsF).entry, (hF.trans hsF).ownAux,
      (hF.trans hsF).vsize, (hF.trans hsF).value⟩, ?_⟩
    intro bid gb hgb
    rw [block?_modB] at hgb
    have hsb : s.1.block? = G.block? := by funext y; unfold Func.block?; rw [hsB]
    rw [hsb] at hgb
    split at hgb
    · subst_vars
      obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.1 hgb
      obtain ⟨fb, hfb, hk, hsc, hc, hv⟩ := hB _ u hu
      refine ⟨fb, hfb, hk, hsc, hc, .inl ?_⟩
      show s.2 = _
      rw [hkept]
      unfold Func.getB
      rw [hu, Option.getD_some]
      rcases hv with hv | ⟨-, hv⟩
      · rw [hv, Array.filter_filter]; simp
      · rw [hv]
    · rename_i hne
      obtain ⟨fb, hfb, hk, hsc, hc, hv⟩ := hB bid gb hgb
      refine ⟨fb, hfb, hk, hsc, hc, ?_⟩
      rcases hv with hv | ⟨hn, hv⟩
      · exact .inl hv
      · refine .inr ⟨fun hm => ?_, hv⟩
        rcases List.mem_append.1 hm with hm | hm
        · exact hn hm
        · exact hne (List.mem_singleton.1 hm).symm
  obtain ⟨hF1, hB1⟩ := hI1
  -- the second loop: unreachable blocks freed and dropped from the list
  obtain ⟨s2, h2, h⟩ := CheckFacts.bind_ok h
  cases Except.ok.inj h
  have hK := CheckFacts.forIn_array_inv
    (fun pre (t : Func × Array ID) => t.1.entry = G1.entry ∧ t.1.ownAux = G1.ownAux ∧
      t.1.valueTab = G1.valueTab ∧ (∀ x gb, t.1.block? x = some gb → G1.block? x = some gb) ∧
      t.2.toList = pre.filter (r.getD · false))
    ⟨rfl, rfl, rfl, fun _ _ h => h, rfl⟩ ?_ h2
  rotate_left
  · intro pre b t t' ⟨he, ho, hv, hb', hl⟩ hb
    split at hb
    · rename_i hr
      refine ⟨_, (Except.ok.inj hb).symm, he, ho, hv, hb', ?_⟩
      rw [Array.toList_push, hl, List.filter_append]
      simp only [List.filter_cons, List.filter_nil, hr, ↓reduceIte]
    · rename_i hr
      split at hb
      · obtain ⟨_, hth, -⟩ := CheckFacts.bind_ok hb
        cases hth
      · refine ⟨_, (Except.ok.inj hb).symm, he, ho, hv, fun x gb h => hb' x gb (join_set_none h), ?_⟩
        rw [hl, List.filter_append]
        simp only [List.filter_cons, List.filter_nil, Bool.eq_false_iff.2 hr, Bool.false_eq_true,
          ↓reduceIte, List.append_nil]
  obtain ⟨he, ho, hv, hb2, hl⟩ := hK
  refine ⟨he.trans hF1.entry, ho.trans hF1.ownAux, by rw [← hF1.vsize]; exact congrArg _ hv,
    fun x u hx => hF1.value x u (by unfold Func.value? at hx ⊢; rw [← hv]; exact hx), ?_, ?_⟩
  · intro bid hm
    have hm' : bid ∈ s2.2.toList := Array.mem_toList_iff.2 hm
    rw [hl, List.mem_filter, hF1.blocks] at hm'
    exact ⟨Array.mem_toList_iff.1 hm'.1, hm'.2⟩
  · intro bid gb hm hgb
    obtain ⟨fb, hfb, hk, hsc, hc, hvl⟩ := hB1 bid gb (hb2 bid gb hgb)
    refine ⟨fb, hfb, hk, hsc, hc, ?_⟩
    rcases hvl with hvl | ⟨hn, -⟩
    · exact hvl
    · exact absurd (Array.mem_toList_iff.2 hm) hn

/-! ## The relation -/

/-- **deadcode after copyelim keeps `DeadRel`.** -/
theorem deadTail_rel {ce' : CheckEnv} {tabs : Tables} {r : Array Bool} {f g : Func}
    (hwg : WF ce' g) (hsize : f.valueTab.size ≤ f.vidLast + 1)
    (h : deadTail tabs r f = .ok g) : DeadRel f g (· ∈ g.blocks) := by
  unfold deadTail at h
  generalize hlo : f.liveValuesOrder tabs r = lo at h
  obtain ⟨live, order⟩ := lo
  dsimp only at h
  split at h
  · rename_i pending _
    obtain ⟨⟨f2, p2⟩, hu, h⟩ := CheckFacts.bind_ok h
    dsimp only at h
    generalize hm : Deadcode.moveStmts order f2 p2 = mm at h
    obtain ⟨f3, p3⟩ := mm
    dsimp only at h
    have S1 : Sk r live f (Deadcode.pruneNames live f) :=
      ⟨rfl, rfl, rfl, rfl, fun _ gb h => ⟨gb, h, BSk.refl⟩, fun _ gv h => ⟨gv, h, VSk.refl⟩⟩
    have S3 := (S1.trans (unlink_sk hu)).trans (move_sk hm)
    have S : Sk r live f { f3 with cache := { f3.cache with lineStarts := some p3.toCache } } :=
      S3.trans ⟨rfl, rfl, rfl, rfl, fun _ gb h => ⟨gb, h, BSk.refl⟩, fun _ gv h => ⟨gv, h, VSk.refl⟩⟩
    generalize { f3 with cache := { f3.cache with lineStarts := some p3.toCache } } = F at S h
    obtain ⟨hE, hO, hV, hVal, hBm, hBlk⟩ := freeDead_spec h
    -- a kept block of `g`
    have kept : ∀ bid gb, bid ∈ g.blocks → g.block? bid = some gb → ∃ fb, f.block? bid = some fb ∧
        bid ∈ f.blocks ∧ r.getD bid false = true ∧ gb.kind = fb.kind ∧ gb.succs = fb.succs ∧
        gb.controls = fb.controls ∧ gb.values = fb.values.filter (live.getD · false) := by
      intro bid gb hm hgb
      obtain ⟨hmF, hr⟩ := hBm bid hm
      obtain ⟨b3, hb3, hk, hsc, hc, hv⟩ := hBlk bid gb hmF hgb
      obtain ⟨fb, hfb, hk', hsc', hv', hc'⟩ := S.block bid b3 hb3
      refine ⟨fb, hfb, S.blocks ▸ hmF, hr, hk.trans hk', hsc.trans hsc', hc.trans (hc' hr), ?_⟩
      rw [hv, hv']
    -- a live value of `g`
    have keptV : ∀ x gv, live.getD x false = true → g.value? x = some gv → ∃ fv,
        f.value? x = some fv ∧ gv.op = fv.op ∧ gv.type = fv.type ∧ gv.aux = fv.aux ∧
        gv.auxInt = fv.auxInt ∧ gv.args = fv.args := by
      intro x gv hl hgv
      obtain ⟨fv, hfv, ho, ht, ha, hai, -, hargs⟩ := S.value x gv (hVal x gv hgv)
      exact ⟨fv, hfv, ho, ht, ha, hai, hargs hl⟩
    have hlive : live = (f.liveValuesOrder tabs r).1 := by rw [hlo]
    refine ⟨hE.trans S.entry, hO.trans S.ownAux, hV.trans S.vsize, ?_, fun _ h => h, ?_, ?_, ?_,
      ?_, ?_⟩
    · have := hwg.entry
      rwa [hE.trans S.entry] at this
    · intro x gv fv hgv hfv
      obtain ⟨fv', hfv', -, -, -, -, hb, -⟩ := S.value x gv (hVal x gv hgv)
      rw [hfv] at hfv'; cases hfv'
      exact hb
    · intro bid hm gb hgb
      obtain ⟨fb, hfb, hmf, -, hk, -, hc, hv⟩ := kept bid gb hm hgb
      refine ⟨fb, hfb, hmf, .inl hk, hc, fun x hx => ?_⟩
      rw [hv] at hx
      exact (Array.mem_filter.1 hx).1
    · intro bid hm gb fb hgb hfb k e hk _
      obtain ⟨fb', hfb', -, -, -, hsc, -, -⟩ := kept bid gb hm hgb
      rw [hfb] at hfb'; cases hfb'
      have hk' : gb.succs[k]? = some e := by rw [hsc]; exact hk
      have heb : e.b ∈ g.blocks := (hwg.succLink bid gb ⟨hm, hgb⟩ k e hk').1
      refine ⟨e, hk', rfl, heb, ?_⟩
      intro gc hgc x hx gv hgv _
      obtain ⟨_, -, -, -, -, -, -, hv⟩ := kept e.b gc heb hgc
      rw [hv] at hx
      obtain ⟨fv, hfv, -, -, -, -, hargs⟩ := keptV x gv (Array.mem_filter.1 hx).2 hgv
      exact ⟨fv, hfv, by rw [hargs]⟩
    · intro bid hm gb hgb x hx gv hgv
      obtain ⟨_, -, -, -, -, -, -, hv⟩ := kept bid gb hm hgb
      rw [hv] at hx
      obtain ⟨fv, hfv, ho, ht, ha, hai, hargs⟩ := keptV x gv (Array.mem_filter.1 hx).2 hgv
      exact ⟨fv, hfv, ht, by rw [ho], fun _ => ⟨ho, ha, hai, hargs⟩⟩
    · intro bid hm gb fb hgb hfb x hx hnx fv hfv hpan
      obtain ⟨fb', hfb', hmf, hr, -, -, -, hv⟩ := kept bid gb hm hgb
      rw [hfb] at hfb'; cases hfb'
      have hl := live_root (t := tabs) hsize hmf hr hfb hx hfv (panicking_root hpan)
      rw [← hlive] at hl
      exact hnx (hv ▸ Array.mem_filter.2 ⟨hx, hl⟩)
  · cases h

end GoFV.Proof.Dead

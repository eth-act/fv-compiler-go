import GoFV.Proof.Pass.DeadEdgeWalk
import GoFV.Proof.Pass.DeadReach
import GoFV.Proof.Pass.DeadRel

/-!
# deadcode's edge removal: well-formedness and `DeadRel`

From the invariant `EI f r F` of the edge-removal walk (`ei_edgesG`): `F` is well formed
(`wf_of_ei`: same blocks and values, crosslinked edges, `Phi` arity, arguments among the
original ones) and, for `r = f.reachableBlocks`, keeps the reachable blocks of `f` with their
values and the edges a run takes (`deadRel_of_ei`, using `reachable_spec`).
-/

namespace GoFV.Proof.Dead

open GoFV.SSA GoFV.Opt GoFV.Proof GoFV.Proof.CopyElim

theorem getB_of_block? {F : Func} {y : ID} {b : Block} (h : F.block? y = some b) : F.getB y = b := by
  unfold Func.getB; rw [h]; rfl

theorem noArgs_some {f F : Func} {x : ID} (h : (vw F x).map noArgs = (vw f x).map noArgs)
    {u : Value} (hu : vw F x = some u) : ∃ u0, vw f x = some u0 ∧ noArgs u = noArgs u0 := by
  rw [hu] at h
  cases h0 : vw f x with
  | none => rw [h0] at h; cases h
  | some u0 => rw [h0] at h; exact ⟨u0, rfl, Option.some.inj h⟩

theorem noArgs_some' {f F : Func} {x : ID} (h : (vw F x).map noArgs = (vw f x).map noArgs)
    {u0 : Value} (hu : vw f x = some u0) : ∃ u, vw F x = some u ∧ noArgs u = noArgs u0 := by
  rw [hu] at h
  cases h0 : vw F x with
  | none => rw [h0] at h; cases h
  | some u => rw [h0] at h; exact ⟨u, rfl, Option.some.inj h⟩

/-- Values equal up to arguments and use count. -/
theorem noArgs_parts {u v : Value} (h : noArgs (strip u) = noArgs (strip v)) :
    u.op = v.op ∧ u.type = v.type ∧ u.aux = v.aux ∧ u.auxInt = v.auxInt ∧ u.block = v.block ∧
      u.id = v.id := by
  cases u; cases v
  simp_all [noArgs, strip]

theorem strip_args {u v : Value} (h : strip u = strip v) : u.args = v.args := by
  have := congrArg Value.args h; exact this

section
variable {ce : CheckEnv} {f F : Func} {r : Array Bool}

theorem block_getB (hwf : WF ce f) {y : ID} (hy : y ∈ f.blocks) : f.block? y = some (f.getB y) := by
  obtain ⟨b, hb, -⟩ := hwf.blockId y hy
  rw [getB_of_block? hb, hb]

theorem ei_block (hwf : WF ce f) (hE : EI f r F) {y : ID} (hy : y ∈ f.blocks) :
    F.block? y = some (F.getB y) := by
  obtain ⟨b, hb, -⟩ := hwf.blockId y hy
  have : (F.block? y).isSome := by rw [hE.pres y, hb]; rfl
  obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 this
  rw [getB_of_block? hb', hb']

theorem ei_values (hE : EI f r F) (y : ID) : (F.getB y).values = (f.getB y).values :=
  values_of_kview (hE.kv y)

theorem ei_controls (hE : EI f r F) (y : ID) : (F.getB y).controls = (f.getB y).controls := by
  have := congrArg Block.controls (hE.kv y); exact this

theorem ei_listed (hwf : WF ce f) (hE : EI f r F) {a : ID} (h : Listed f a) : Listed F a := by
  obtain ⟨bid, b, ⟨hm, hb⟩, ha⟩ := h
  refine ⟨bid, F.getB bid, ⟨hE.blocks ▸ hm, ei_block hwf hE hm⟩, ?_⟩
  rw [ei_values hE, getB_of_block? hb]; exact ha

/-- A value of `F`: its `f` counterpart, the same up to arguments. -/
theorem ei_value (hE : EI f r F) {x : ID} {v : Value} (hv : F.value? x = some v) :
    ∃ v0, f.value? x = some v0 ∧ noArgs (strip v) = noArgs (strip v0) := by
  obtain ⟨u0, hu0, hn⟩ := noArgs_some (hE.vals x) (vw_of_value? hv)
  obtain ⟨v0, hv0, rfl⟩ := vw_eq_some hu0
  exact ⟨v0, hv0, hn⟩

/-- A non-`Phi` value of `F` is its `f` counterpart. -/
theorem ei_nonphi (hE : EI f r F) {x : ID} {v v0 : Value} (hv : F.value? x = some v)
    (hv0 : f.value? x = some v0) (hop : v0.op ≠ .Phi) : strip v = strip v0 := by
  have := hE.nonphi x (strip v0) (vw_of_value? hv0) hop
  rw [vw_of_value? hv] at this
  exact Option.some.inj this

/-- **The edge-removed function is well formed.** -/
theorem wf_of_ei (hwf : WF ce f) (hE : EI f r F) : WF ce F := by
  have hB : ∀ bid b, BlockIn F bid b → bid ∈ f.blocks ∧ b = F.getB bid := by
    rintro bid b ⟨hm, hb⟩
    exact ⟨hE.blocks ▸ hm, (getB_of_block? hb).symm⟩
  have hBf : ∀ bid b, BlockIn F bid b → BlockIn f bid (f.getB bid) ∧
      b.values = (f.getB bid).values := by
    intro bid b h
    obtain ⟨hm, rfl⟩ := hB bid b h
    exact ⟨⟨hm, block_getB hwf hm⟩, ei_values hE bid⟩
  have hV : ∀ bid b vid v, ValueIn F bid b vid v → ∃ v0, ValueIn f bid (f.getB bid) vid v0 ∧
      noArgs (strip v) = noArgs (strip v0) := by
    rintro bid b vid v ⟨hb, hx, hv⟩
    obtain ⟨hbf, hvals⟩ := hBf bid b hb
    obtain ⟨v0, hv0, hn⟩ := ei_value hE hv
    exact ⟨v0, ⟨hbf, hvals ▸ hx, hv0⟩, hn⟩
  refine ⟨fun bid hm => ?_, by rw [hE.blocks]; exact hwf.blocksNodup, fun bid b hb vid hx => ?_,
    fun bid b hb => ?_, fun b1 c1 b2 c2 h1 h2 vid hx1 hx2 => ?_, fun bid b hb i e he => ?_,
    fun bid b hb j e he => ?_, fun bid b vid v hv hl => ?_, fun bid b vid v hv hop => ?_,
    fun bid b vid v hv ht => ?_, fun bid b vid v hv a ha => ?_, fun bid b hb c hc => ?_,
    hE.blocks ▸ hE.entry ▸ hwf.entry, fun b hb => ?_⟩
  · rw [hE.blocks] at hm
    obtain ⟨b0, hb0, hid⟩ := hwf.blockId bid hm
    refine ⟨F.getB bid, ei_block hwf hE hm, ?_⟩
    have := congrArg Block.id (hE.kv bid)
    simp only [kview] at this
    rw [show (F.getB bid).id = (f.getB bid).id from this, getB_of_block? hb0, hid]
  · obtain ⟨hbf, hvals⟩ := hBf bid b hb
    rw [hvals] at hx
    obtain ⟨v0, hv0, hid, hblk⟩ := hwf.valueId bid _ hbf vid hx
    obtain ⟨u, hu, hn⟩ := noArgs_some' (hE.vals vid) (vw_of_value? hv0)
    obtain ⟨v, hv, rfl⟩ := vw_eq_some hu
    refine ⟨v, hv, ?_, ?_⟩
    · have := congrArg Value.id hn; simp only [noArgs, strip] at this; rw [this, hid]
    · have := congrArg Value.block hn; simp only [noArgs, strip] at this; rw [this, hblk]
  · obtain ⟨hbf, hvals⟩ := hBf bid b hb
    rw [hvals]; exact hwf.valuesNodup bid _ hbf
  · obtain ⟨hf1, hv1⟩ := hBf b1 c1 h1
    obtain ⟨hf2, hv2⟩ := hBf b2 c2 h2
    rw [hv1] at hx1; rw [hv2] at hx2
    exact hwf.valueOnce b1 _ b2 _ hf1 hf2 vid hx1 hx2
  · obtain ⟨hm, rfl⟩ := hB bid b hb
    obtain ⟨h1, h2⟩ := hE.xl.pred bid hm i e he
    exact ⟨hE.blocks ▸ h1, F.getB e.b, ei_block hwf hE h1, h2⟩
  · obtain ⟨hm, rfl⟩ := hB bid b hb
    obtain ⟨h1, h2⟩ := hE.xl.succ bid hm j e he
    exact ⟨hE.blocks ▸ h1, F.getB e.b, ei_block hwf hE h1, h2⟩
  · obtain ⟨v0, hv0, hn⟩ := hV bid b vid v hv
    have hop : v.op = v0.op := (noArgs_parts hn).1
    by_cases hph : v0.op = .Phi
    · rw [hop, hph] at hl ⊢; exact absurd rfl hl
    · have hs := ei_nonphi hE hv.2.2 hv0.2.2 hph
      have ha : v.args = v0.args := strip_args hs
      rw [hop, ha]; exact hwf.arity bid _ vid v0 hv0 (hop ▸ hl)
  · obtain ⟨hm, rfl⟩ := hB bid b hv.1
    exact hE.arity bid hm vid hv.2.1 (strip v) (vw_of_value? hv.2.2) hop
  · obtain ⟨v0, hv0, hn⟩ := hV bid b vid v hv
    have hop : v.op = v0.op := (noArgs_parts hn).1
    have hai : v.auxInt = v0.auxInt := (noArgs_parts hn).2.2.2.1
    rw [hai]; exact hwf.boolAux bid _ vid v0 hv0 (hop ▸ ht)
  · obtain ⟨v0, hv0, -⟩ := hV bid b vid v hv
    have ha0 := hE.sub vid (strip v0) (strip v) (vw_of_value? hv0.2.2) (vw_of_value? hv.2.2) a ha
    exact ei_listed hwf hE (hwf.argListed bid _ vid v0 hv0 a ha0)
  · obtain ⟨hm, rfl⟩ := hB bid b hb
    rw [ei_controls hE] at hc
    exact ei_listed hwf hE (hwf.ctrlListed bid _ ⟨hm, block_getB hwf hm⟩ c hc)
  · rw [hE.entry] at hb
    rw [← getB_of_block? hb]
    have := hE.psize f.entry
    rw [hwf.entryPreds _ (block_getB hwf hwf.entry)] at this
    omega

/-- **The edge-removed function keeps the reachable blocks** (`K`: marked by
`reachableBlocks`), with their values and the edges a run takes. -/
theorem deadRel_of_ei (hwf : WF ce f) (hbid : ∀ b ∈ f.blocks, b ≤ f.bidLast)
    (hE : EI f f.reachableBlocks F) :
    DeadRel f F (fun b => f.reachableBlocks.getD b false = true) := by
  obtain ⟨hre, hrl, hrc⟩ := reachable_spec hwf hbid
  have hgb : ∀ bid gb, F.block? bid = some gb → (F.block? bid).isSome := fun _ _ h => by rw [h]; rfl
  refine ⟨hE.entry, hE.ownAux, hE.vsize, hre, fun bid hb => hE.blocks ▸ hrl bid hb,
    fun x gv fv hgv hfv => ?_, fun bid hb gb hgb' => ?_, fun bid hb gb fb hgb' hfb k e he hk => ?_,
    fun bid hb gb hgb' x hx gv hgv => ?_, fun bid hb gb fb hgb' hfb x hx hxn => ?_⟩
  · obtain ⟨v0, hv0, hn⟩ := ei_value hE hgv
    rw [hfv] at hv0; cases hv0
    exact (noArgs_parts hn).2.2.2.2.1
  · have hm := hrl bid hb
    have hg := getB_of_block? hgb'
    subst hg
    refine ⟨f.getB bid, block_getB hwf hm, hm, ?_, ei_controls hE bid,
      fun x hx => by rw [ei_values hE] at hx; exact hx⟩
    rcases hE.kind bid with h | ⟨-, h1, h2⟩
    · exact .inl h
    · exact .inr ⟨h1, h2⟩
  · have hm := hrl bid hb
    have he' : sOf f bid k = some e := by unfold sOf; rw [getB_of_block? hfb]; exact he
    obtain ⟨e', h1, h2, h3⟩ := hE.edge bid hm hb k e he' (by rw [getB_of_block? hfb]; exact hk)
    refine ⟨e', by unfold sOf at h1; rw [getB_of_block? hgb'] at h1; exact h1, h2,
      hrc bid fb hb hfb k e he hk, fun gc hgc x hx gv hgv hph => ?_⟩
    rw [← getB_of_block? hgc] at hx
    obtain ⟨u0, hu0, ha⟩ := h3 x hx (strip gv) (vw_of_value? hgv) hph
    obtain ⟨fv, hfv, rfl⟩ := vw_eq_some hu0
    exact ⟨fv, hfv, ha⟩
  · obtain ⟨v0, hv0, hn⟩ := ei_value hE hgv
    obtain ⟨hop, hty, hax, hai, -, -⟩ := noArgs_parts hn
    refine ⟨v0, hv0, hty, by rw [hop], fun hph => ?_⟩
    have hs := ei_nonphi hE hgv hv0 (hop ▸ hph)
    exact ⟨hop, hax, hai, strip_args hs⟩
  · rw [← getB_of_block? hgb', ei_values hE, getB_of_block? hfb] at hxn
    exact absurd hx hxn

end

end GoFV.Proof.Dead

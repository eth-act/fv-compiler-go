import GoFV.Proof.Pass.DeadEdgeInv

/-!
# deadcode's edge removal keeps `EI`

`ei_edgesG`: `edgesG false f` (the edge removal of deadcode with `Phi`s only losing arguments)
satisfies `EI f r` for `r = f.reachableBlocks`, when reachable `First` blocks have two successors
(`FirstTwo`, a `check` fact).
-/

namespace GoFV.Proof.Dead

open GoFV.SSA GoFV.Opt GoFV.Proof.CopyElim

/-- Listed `First` blocks have two successors. -/
def FirstTwo (f : Func) : Prop :=
  ∀ b ∈ f.blocks, (f.getB b).kind = .First → (f.getB b).succs.size = 2

/-- Reachable `First` blocks not yet turned `Plain` still have their successors. -/
def FS (f : Func) (r : Array Bool) (F : Func) : Prop :=
  ∀ b ∈ f.blocks, r.getD b false = true → (F.getB b).kind = .First →
    (F.getB b).succs.size = (f.getB b).succs.size

theorem ei_init {ce : CheckEnv} {f : Func} (hwf : WF ce f) (r : Array Bool) : EI f r f := by
  have hpres : ∀ x ∈ f.blocks, (f.block? x).isSome := fun x hx => by
    obtain ⟨b, hb, -⟩ := hwf.blockId x hx; rw [hb]; rfl
  have hgetB : ∀ x ∈ f.blocks, ∃ b, f.block? x = some b ∧ f.getB x = b := fun x hx => by
    obtain ⟨b, hb, -⟩ := hwf.blockId x hx; exact ⟨b, hb, by unfold Func.getB; rw [hb]; rfl⟩
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ⟨hpres, fun x hx k e he => ?_, fun y hy l e he => ?_⟩,
    fun _ => rfl, fun _ => rfl, fun _ => .inl rfl, fun _ => rfl, fun _ _ h _ => h,
    fun x u u' h h' a ha => by rw [h] at h'; cases h'; exact ha, fun y hy x hx u hu hop => ?_,
    fun b hb _ k e he _ => ⟨e, he, rfl, fun x _ u hu _ => ⟨u, hu, rfl⟩⟩⟩
  · obtain ⟨b, hb, hg⟩ := hgetB x hx
    unfold sOf at he; rw [hg] at he
    obtain ⟨hm, p, hp, hps⟩ := hwf.succLink x b ⟨hx, hb⟩ k e he
    refine ⟨hm, ?_⟩
    unfold pOf Func.getB; rw [hp]; exact hps
  · obtain ⟨b, hb, hg⟩ := hgetB y hy
    unfold pOf at he; rw [hg] at he
    obtain ⟨hm, p, hp, hps⟩ := hwf.predLink y b ⟨hy, hb⟩ l e he
    refine ⟨hm, ?_⟩
    unfold sOf Func.getB; rw [hp]; exact hps
  · obtain ⟨b, hb, hg⟩ := hgetB y hy
    rw [hg] at hx ⊢
    obtain ⟨v, hv, rfl⟩ := vw_eq_some hu
    exact hwf.phiArity y b x v ⟨⟨hy, hb⟩, hx, hv⟩ hop

/-- Other blocks keep their successor count and kind when an edge out of `b0` is removed. -/
theorem removeEdge_other {F : Func} {B : Array ID} (el : Bool) (hX : XL F B) {b0 : ID} {i0 : Nat}
    (hb0 : b0 ∈ B) (hi0 : i0 < (F.getB b0).succs.size) (x : ID) :
    (x ≠ b0 → ((removeEdgeG el F b0 i0).getB x).succs.size = (F.getB x).succs.size) ∧
    ((removeEdgeG el F b0 i0).getB x).kind = (F.getB x).kind := by
  obtain ⟨ec, hec⟩ : ∃ ec, sOf F b0 i0 = some ec := ⟨_, Array.getElem?_eq_getElem hi0⟩
  obtain ⟨c, j⟩ := ec
  obtain ⟨-, hcj⟩ := hX.succ b0 hb0 i0 _ hec
  dsimp only at hcj
  have hcs : 0 < (F.getB c).preds.size := by
    have := (Array.getElem?_eq_some_iff.1 hcj).1; omega
  have he : (F.getB b0).succs[i0]! = ⟨c, j⟩ := by
    rw [getElem!_pos ((F.getB b0).succs) _ hi0]
    exact Option.some.inj ((Array.getElem?_eq_getElem hi0).symm.trans hec)
  have hG := getB_of_skel (skel_removeEdgeG el F b0 i0)
  rw [he] at hG
  obtain ⟨-, -, -, -, -, c6, -, c8, -⟩ :=
    edge_core (n := (F.getB b0).succs.size - 1) (m := (F.getB c).preds.size - 1) hX hb0
      (by omega) (by omega) hec (by omega)
  rw [hG]
  exact ⟨fun hx => by rw [c6 x, if_neg (Ne.symm hx)], kind_of_bview (c8 x)⟩

/-- The successor loop of an unreachable block keeps `EI` and `FS`. -/
theorem ei_deadInner {ce : CheckEnv} {f : Func} {r : Array Bool} (hwf : WF ce f) {b : ID}
    (hb : b ∈ f.blocks) (hr : r.getD b false = false) :
    ∀ (fuel i : Nat) (F : Func), EI f r F → FS f r F →
      EI f r (deadInner false r b fuel i F) ∧ FS f r (deadInner false r b fuel i F)
  | 0, _, _, hE, hF => ⟨hE, hF⟩
  | fuel + 1, i, F, hE, hF => by
    unfold deadInner
    split
    · rename_i hi
      split
      · refine ei_deadInner hwf hb hr fuel i _ (ei_step hwf hE hb hi (fun h => by simp_all)) ?_
        intro x hx hrx hk
        have hxb : x ≠ b := fun h => by subst h; simp_all
        obtain ⟨h1, h2⟩ := removeEdge_other false hE.xl hb hi x
        rw [h1 hxb]; rw [h2] at hk; exact hF x hx hrx hk
      · exact ei_deadInner hwf hb hr fuel (i + 1) F hE hF
    · exact ⟨hE, hF⟩

/-- The block loop of `removeDeadEdges` keeps `EI` and `FS`. -/
theorem ei_deadOuter {ce : CheckEnv} {f : Func} {r : Array Bool} (hwf : WF ce f) :
    ∀ (L : List ID) (F : Func), (∀ b ∈ L, b ∈ f.blocks) → EI f r F → FS f r F →
      EI f r (deadOuter false r L F) ∧ FS f r (deadOuter false r L F)
  | [], _, _, hE, hF => ⟨hE, hF⟩
  | b :: L, F, hL, hE, hF => by
    unfold deadOuter
    refine ei_deadOuter hwf L _ (fun x hx => hL x (List.mem_cons_of_mem _ hx)) ?_ ?_
    all_goals split
    all_goals first
      | exact hE
      | exact hF
      | exact (ei_deadInner hwf (hL b List.mem_cons_self)
          (Bool.eq_false_iff.2 ‹¬r.getD b false = true›) _ 0 F hE hF).1
      | exact (ei_deadInner hwf (hL b List.mem_cons_self)
          (Bool.eq_false_iff.2 ‹¬r.getD b false = true›) _ 0 F hE hF).2

/-- A reachable `First` block, its edge 1 removed, becomes `Plain`. -/
theorem ei_plain {f F : Func} {r : Array Bool} (hE : EI f r F) {b : ID} (hb : b ∈ f.blocks)
    (hr : r.getD b false = true) (hk : (f.getB b).kind = .First) :
    EI f r (F.modB b fun x => { x with kind := .Plain, likely := .unknown }) := by
  have hp := hE.xl.pres b hb
  have hG : ∀ y, (F.modB b fun x => { x with kind := .Plain, likely := .unknown }).getB y =
      if b = y then { F.getB y with kind := .Plain, likely := .unknown } else F.getB y :=
    fun y => getB_modB hp _ y
  have hS : ∀ y, ((F.modB b fun x => { x with kind := .Plain, likely := .unknown }).getB y).succs =
      (F.getB y).succs := fun y => by rw [hG]; split <;> rfl
  have hP : ∀ y, ((F.modB b fun x => { x with kind := .Plain, likely := .unknown }).getB y).preds =
      (F.getB y).preds := fun y => by rw [hG]; split <;> rfl
  have hK : ∀ y, kview ((F.modB b fun x => { x with kind := .Plain, likely := .unknown }).getB y) =
      kview (F.getB y) := fun y => by rw [hG]; split <;> rfl
  have hV : ∀ y, ((F.modB b fun x => { x with kind := .Plain, likely := .unknown }).getB y).values =
      (F.getB y).values := fun y => by rw [hG]; split <;> rfl
  have hvw : vw (F.modB b fun x => { x with kind := .Plain, likely := .unknown }) = vw F := rfl
  refine ⟨hE.entry, hE.blocks, hE.ownAux, hE.vsize, hE.vidLast, hE.bidLast,
    ⟨fun x hx => by rw [isSome_modB]; exact hE.xl.pres x hx,
      fun x hx k e he => by
        unfold sOf pOf at *; rw [hS] at he; rw [hP]; exact hE.xl.succ x hx k e he,
      fun y hy l e he => by
        unfold sOf pOf at *; rw [hP] at he; rw [hS]; exact hE.xl.pred y hy l e he⟩,
    fun y => by rw [isSome_modB]; exact hE.pres y, fun y => by rw [hK]; exact hE.kv y,
    fun y => ?_, hE.vals, hE.nonphi, hE.sub,
    fun y hy x hx u hu hop => by rw [hV] at hx; rw [hP]; exact hE.arity y hy x hx u hu hop,
    fun b' hb' hr' k e he hk' => ?_⟩
  · rw [hG]; split
    · rename_i h; subst h; exact .inr ⟨hr, hk, rfl⟩
    · exact hE.kind y
  · obtain ⟨e', he', heb, hPA⟩ := hE.edge b' hb' hr' k e he hk'
    refine ⟨e', by unfold sOf; rw [hS]; exact he', heb, fun x hx u hu hop => ?_⟩
    rw [hV] at hx
    exact hPA x hx u hu hop

/-- One block of `removeFirstEdges` keeps `EI` and `FS`. -/
theorem ei_firstStep {ce : CheckEnv} {f : Func} {r : Array Bool} (hwf : WF ce f)
    (h2 : FirstTwo f) {b : ID} (hb : b ∈ f.blocks) {F : Func} (hE : EI f r F) (hF : FS f r F) :
    EI f r (firstStep false r F b) ∧ FS f r (firstStep false r F b) := by
  unfold firstStep
  split
  · exact ⟨hE, hF⟩
  · rename_i hc
    simp only [Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, not_or,
      Bool.not_eq_false, Decidable.not_not] at hc
    obtain ⟨hr, hkF⟩ := hc
    have hkf : (f.getB b).kind = .First := by
      rcases hE.kind b with h | ⟨-, -, h⟩
      · rw [← h]; exact hkF
      · rw [hkF] at h; cases h
    have hsz : (F.getB b).succs.size = 2 := by rw [hF b hb hr hkF]; exact h2 b hb hkf
    have hE' := ei_step hwf hE hb (i0 := 1) (by omega) (fun _ => ⟨hkf, rfl, hsz⟩)
    refine ⟨ei_plain hE' hb hr hkf, fun x hx hrx hk => ?_⟩
    have hp := hE'.xl.pres b hb
    rw [getB_modB hp] at hk ⊢
    split at hk
    · cases hk
    · rename_i hxb
      obtain ⟨h1, h2'⟩ := removeEdge_other false hE.xl hb (i0 := 1) (by omega) x
      rw [if_neg hxb, h1 (Ne.symm hxb)]; rw [h2'] at hk; exact hF x hx hrx hk

theorem ei_firstFold {ce : CheckEnv} {f : Func} {r : Array Bool} (hwf : WF ce f)
    (h2 : FirstTwo f) :
    ∀ (L : List ID) (F : Func), (∀ b ∈ L, b ∈ f.blocks) → EI f r F → FS f r F →
      EI f r (L.foldl (firstStep false r) F)
  | [], _, _, hE, _ => hE
  | b :: L, F, hL, hE, hF => by
    rw [List.foldl_cons]
    obtain ⟨hE', hF'⟩ := ei_firstStep hwf h2 (hL b List.mem_cons_self) hE hF
    exact ei_firstFold hwf h2 L _ (fun x hx => hL x (List.mem_cons_of_mem _ hx)) hE' hF'

/-- **deadcode's edge removal, `Phi`s only losing arguments, keeps `EI`.** -/
theorem ei_edgesG {ce : CheckEnv} {f : Func} (hwf : WF ce f) (h2 : FirstTwo f) :
    EI f f.reachableBlocks (edgesG false f) := by
  unfold edgesG
  have hL : ∀ b ∈ f.blocks.toList, b ∈ f.blocks := fun b hb => Array.mem_toList_iff.1 hb
  obtain ⟨hE, hF⟩ := ei_deadOuter hwf f.blocks.toList f hL (ei_init hwf _) (fun _ _ _ _ => rfl)
  exact ei_firstFold hwf h2 _ _ hL hE hF

end GoFV.Proof.Dead

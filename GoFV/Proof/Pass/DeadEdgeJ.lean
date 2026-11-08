import GoFV.Proof.Pass.DeadEdgeWF

variable [GoFV.SSA.Sem.Addrs]

/-!
# deadcode's real edge removal against the one keeping `Phi`s

`edgesG true f` (deadcode's edge removal, where `removePhiArg` may turn a `Phi` into a copy)
and `edgesG false f` (the same walk, `Phi`s only losing arguments) take the same steps, as the
walk reads only blocks: `J f F' F` (`j_edgesG`) — the same skeleton, and every value of `F` is
`F'`'s or a `Phi` of `F'` turned into `Copy w`, every argument of the `Phi` being itself or `w`
(and `w` an argument of the value in `f`). So `F` is a state of copyelim's sweeps started from
`F'` (`inv_of_j`: `CopyElim.Inv tabs F' F`, given copyelim's fragment of `F`), and copyelim's
proof relates `F'` to deadcode's copyelim output.
-/

namespace GoFV.Proof.Dead

open GoFV.SSA GoFV.Opt GoFV.Proof GoFV.Proof.CopyElim

/-- A value of `F` against `F'` (see the module doc). -/
def JV (f : Func) (V' V : ID → Option Value) (x : ID) : Prop :=
  V x = V' x ∨ ∃ u w u0, V' x = some u ∧ u.op = .Phi ∧
    V x = some { u with op := .Copy, args := #[w] } ∧ w ≠ x ∧ (∀ a ∈ u.args, a = x ∨ a = w) ∧
    vw f x = some u0 ∧ w ∈ u0.args

theorem jv_of_eq {f : Func} {V' V W' W : ID → Option Value} {x : ID} (h' : V' x = W' x)
    (h : V x = W x) (hj : JV f W' W x) : JV f V' V x := by
  unfold JV at *; rw [h', h]; exact hj

/-- `F` (deadcode's edge removal) against `F'` (the one keeping `Phi`s). -/
structure J (f F' F : Func) : Prop where
  skel : skel F = skel F'
  val : ∀ x, JV f (vw F') (vw F) x

/-! ## Congruence: the CFG edits read only the block table -/

theorem blockTab_removeSucc {F F' : Func} (h : F.blockTab = F'.blockTab) (b : ID) (i : Nat) :
    (F.removeSucc b i).blockTab = (F'.removeSucc b i).blockTab := by
  unfold Func.removeSucc Func.modB Func.getB Func.block? Func.invalidateCFG
  simp only [h]
  split <;> simp only [h]

theorem blockTab_removePred {F F' : Func} (h : F.blockTab = F'.blockTab) (c : ID) (j : Nat) :
    (F.removePred c j).blockTab = (F'.removePred c j).blockTab := by
  unfold Func.removePred Func.modB Func.getB Func.block? Func.invalidateCFG
  simp only [h]
  split <;> simp only [h]

theorem skel_parts' {F F' : Func} (h : skel F = skel F') :
    F.entry = F'.entry ∧ F.bidLast = F'.bidLast ∧ F.blocks = F'.blocks ∧
      F.blockTab = F'.blockTab ∧ F.vidLast = F'.vidLast ∧ F.ownAux = F'.ownAux ∧
      F.valueTab.size = F'.valueTab.size := by
  simpa only [skel, Prod.mk.injEq] using h

theorem skel_of_parts {F F' : Func} (h1 : F.entry = F'.entry) (h2 : F.bidLast = F'.bidLast)
    (h3 : F.blocks = F'.blocks) (h4 : F.blockTab = F'.blockTab) (h5 : F.vidLast = F'.vidLast)
    (h6 : F.ownAux = F'.ownAux) (h7 : F.valueTab.size = F'.valueTab.size) : skel F = skel F' := by
  simp only [skel, h1, h2, h3, h4, h5, h6, h7]

theorem skel_removeSucc_congr {F F' : Func} (h : skel F = skel F') (b : ID) (i : Nat) :
    skel (F.removeSucc b i) = skel (F'.removeSucc b i) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := skel_parts' h
  rw [removeSucc_eta F, removeSucc_eta F']
  exact skel_of_parts h1 h2 h3 (blockTab_removeSucc h4 b i) h5 h6 h7

theorem skel_removePred_congr {F F' : Func} (h : skel F = skel F') (c : ID) (j : Nat) :
    skel (F.removePred c j) = skel (F'.removePred c j) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := skel_parts' h
  rw [removePred_eta F, removePred_eta F']
  exact skel_of_parts h1 h2 h3 (blockTab_removePred h4 c j) h5 h6 h7

theorem vw_removeSucc (F : Func) (b : ID) (i : Nat) : vw (F.removeSucc b i) = vw F := by
  rw [removeSucc_eta]; rfl

theorem vw_removePred (F : Func) (c : ID) (j : Nat) : vw (F.removePred c j) = vw F := by
  rw [removePred_eta]; rfl

theorem skel_modB_congr {F F' : Func} (h : skel F = skel F') (b : ID) (g : Block → Block) :
    skel (F.modB b g) = skel (F'.modB b g) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := skel_parts' h
  exact skel_of_parts h1 h2 h3 (by unfold Func.modB; simp only [h4]) h5 h6 h7

/-! ## One removed edge -/

theorem removePhiArgG_true (F : Func) (c v : ID) (j : Nat) :
    removePhiArgG true F c v j = ((removePhiArgG false F c v j).phielimValue v).1 := rfl

theorem dropArg'_copy (j n : Nat) (args : Array ID) (u : Value) (w : ID) :
    { dropArg' j n args u with op := .Copy, args := #[w] } = { u with op := .Copy, args := #[w] } :=
  rfl

/-- The `Phi` loop of one removed edge, on both sides. -/
theorem j_phiFold {f : Func} {c : ID} {j n : Nat} (hj : j ≤ n) :
    ∀ (l : List ID) (G' G : Func), l.Nodup → skel G = skel G' → (G'.getB c).preds.size = n →
      (∀ x, JV f (vw G') (vw G) x) →
      (∀ v ∈ l, ∀ u, vw G' v = some u → u.op = .Phi →
        u.args.size = n + 1 ∧ ∀ a ∈ u.args, ∃ u0, vw f v = some u0 ∧ a ∈ u0.args) →
      skel (l.foldl (fun f v => if (f.getV v).op == .Phi then removePhiArgG true f c v j else f) G)
        = skel (l.foldl (fun f v => if (f.getV v).op == .Phi then removePhiArgG false f c v j else f)
          G') ∧
      ∀ x, JV f (vw (l.foldl (fun f v => if (f.getV v).op == .Phi then removePhiArgG false f c v j
          else f) G'))
        (vw (l.foldl (fun f v => if (f.getV v).op == .Phi then removePhiArgG true f c v j else f) G))
        x
  | [], G', G, _, hs, _, hJ, _ => ⟨hs, hJ⟩
  | v :: l, G', G, hnd, hs, hn, hJ, hA => by
    obtain ⟨hvl, hnd'⟩ := List.nodup_cons.1 hnd
    have hgB : G.getB = G'.getB := getB_of_skel hs
    have hA' : ∀ (H' : Func), (∀ y ∈ l, vw H' y = vw G' y) → (H'.getB c).preds.size = n →
        ∀ y ∈ l, ∀ u, vw H' y = some u → u.op = .Phi →
          u.args.size = n + 1 ∧ ∀ a ∈ u.args, ∃ u0, vw f y = some u0 ∧ a ∈ u0.args :=
      fun H' hH _ y hy u hu hop => hA y (List.mem_cons_of_mem _ hy) u (by rw [← hH y hy]; exact hu) hop
    have hne : ∀ y ∈ l, y ≠ v := fun y hy h => hvl (h ▸ hy)
    rw [List.foldl_cons, List.foldl_cons]
    -- the false side's step
    have hD : ∀ (H : Func), vw (removePhiArgG false H c v j) =
        upd (vw H) v (dropArg' j (H.getB c).preds.size (H.getV v).args) :=
      fun H => vw_removePhiArg H c v j
    rcases hJ v with hsame | ⟨u, w, u0, hu', hop, hu, hwv, hall, hu0, hw0⟩
    · -- the same value on both sides
      cases hu' : vw G' v with
      | none =>
        have hG' : (G'.getV v).op ≠ .Phi := by rw [getV_of_vw_none hu']; exact default_op_ne_phi
        have hG : (G.getV v).op ≠ .Phi := by
          rw [getV_of_vw_none (hsame.trans hu')]; exact default_op_ne_phi
        rw [if_neg (by simpa using hG), if_neg (by simpa using hG')]
        exact j_phiFold hj l G' G hnd' hs hn hJ (hA' G' (fun _ _ => rfl) hn)
      | some u =>
        have hu : vw G v = some u := hsame.trans hu'
        obtain ⟨hgo', hga', -⟩ := getV_of_vw hu'
        obtain ⟨hgo, hga, -⟩ := getV_of_vw hu
        by_cases hop : u.op = .Phi
        · have hG' : ((G'.getV v).op == .Phi) = true := by rw [hgo', hop]; rfl
          have hG : ((G.getV v).op == .Phi) = true := by rw [hgo, hop]; rfl
          rw [if_pos hG, if_pos hG']
          obtain ⟨hsz, hsub⟩ := hA v List.mem_cons_self u hu' hop
          -- both drop argument `j`
          generalize hDf : dropArg' j n u.args = D
          have hV1' : vw (removePhiArgG false G' c v j) = upd (vw G') v D := by
            rw [hD, hn, hga', hDf]
          have hV1 : vw (removePhiArgG false G c v j) = upd (vw G) v D := by
            rw [hD, hgB, hn, hga, hDf]
          have hs1 : skel (removePhiArgG false G c v j) = skel (removePhiArgG false G' c v j) := by
            rw [skel_removePhiArg, skel_removePhiArg]; exact hs
          have hn1 : ((removePhiArgG false G' c v j).getB c).preds.size = n := by
            rw [getB_removePhiArg]; exact hn
          have hrest := hA' (removePhiArgG false G' c v j)
            (fun y hy => by rw [hV1', upd_ne _ _ _ (hne y hy)]) hn1
          have hDu : D u = dropArg' j n u.args u := by rw [← hDf]
          have hDmem : ∀ a ∈ (D u).args, a ∈ u.args := by
            intro a ha
            rw [hDu] at ha
            exact mem_dropArg hsz hj ha
          have hDop : (D u).op = .Phi := by rw [hDu]; exact hop
          rw [removePhiArgG_true]
          rcases phielimValue_cases (removePhiArgG false G c v j) v with
            hpe | ⟨w, hpop, hw, hwv, hall, hpe⟩
          · rw [hpe]
            refine j_phiFold hj l _ _ hnd' hs1 hn1 (fun x => ?_) hrest
            rw [hV1, hV1']
            by_cases hxv : x = v
            · subst hxv; exact .inl (by rw [upd_self, upd_self, hu, hu'])
            · exact jv_of_eq (upd_ne _ _ _ hxv) (upd_ne _ _ _ hxv) (hJ x)
          · rw [hpe]
            have hs2 : skel ((((removePhiArgG false G c v j).modV v fun y => { y with op := .Copy }).setArgs1 v w))
                = skel (removePhiArgG false G' c v j) := by rw [skel_toCopy]; exact hs1
            refine j_phiFold hj l _ _ hnd' hs2 hn1 (fun x => ?_) hrest
            rw [vw_toCopy, hV1, hV1']
            have hDv : vw (removePhiArgG false G c v j) v = some (D u) := by
              rw [hV1, upd_self, hu]; rfl
            obtain ⟨-, hDa, -⟩ := getV_of_vw hDv
            rw [hDa] at hw hall
            by_cases hxv : x = v
            · subst hxv
              obtain ⟨u1, hu1, hm⟩ := hsub w (hDmem w hw)
              refine .inr ⟨D u, w, u1, by rw [upd_self, hu']; rfl, hDop, ?_, hwv, hall, hu1, hm⟩
              rw [upd_self, upd_self, hu]; rfl
            · exact jv_of_eq (upd_ne _ _ _ hxv)
                ((upd_ne _ _ _ hxv).trans (upd_ne _ _ _ hxv)) (hJ x)
        · have hG' : ((G'.getV v).op == .Phi) = false := by rw [hgo']; simpa using hop
          have hG : ((G.getV v).op == .Phi) = false := by rw [hgo]; simpa using hop
          rw [if_neg (by rw [hG]; exact Bool.false_ne_true),
            if_neg (by rw [hG']; exact Bool.false_ne_true)]
          exact j_phiFold hj l G' G hnd' hs hn hJ (hA' G' (fun _ _ => rfl) hn)
    · -- a `Phi` of `G'` already a copy in `G`: only `G'` drops the argument
      obtain ⟨hgo', hga', -⟩ := getV_of_vw hu'
      obtain ⟨hgo, -, -⟩ := getV_of_vw hu
      have hG' : ((G'.getV v).op == .Phi) = true := by rw [hgo', hop]; rfl
      have hG : ((G.getV v).op == .Phi) = false := by rw [hgo]; rfl
      rw [if_neg (by rw [hG]; exact Bool.false_ne_true), if_pos hG']
      obtain ⟨hsz, -⟩ := hA v List.mem_cons_self u hu' hop
      generalize hDf : dropArg' j n u.args = D
      have hV1' : vw (removePhiArgG false G' c v j) = upd (vw G') v D := by
        rw [hD, hn, hga', hDf]
      have hs1 : skel G = skel (removePhiArgG false G' c v j) := by
        rw [skel_removePhiArg]; exact hs
      have hn1 : ((removePhiArgG false G' c v j).getB c).preds.size = n := by
        rw [getB_removePhiArg]; exact hn
      have hrest := hA' (removePhiArgG false G' c v j)
        (fun y hy => by rw [hV1', upd_ne _ _ _ (hne y hy)]) hn1
      have hDu : D u = dropArg' j n u.args u := by rw [← hDf]
      refine j_phiFold hj l _ _ hnd' hs1 hn1 (fun x => ?_) hrest
      rw [hV1']
      by_cases hxv : x = v
      · subst hxv
        refine .inr ⟨D u, w, u0, by rw [upd_self, hu']; rfl, by rw [hDu]; exact hop, ?_, hwv,
          fun a ha => hall a (mem_dropArg hsz hj (by rw [hDu] at ha; exact ha)), hu0, hw0⟩
        rw [hu, hDu]; rfl
      · exact jv_of_eq (upd_ne _ _ _ hxv) rfl (hJ x)

theorem vw_modB (F : Func) (b : ID) (g : Block → Block) : vw (F.modB b g) = vw F := rfl

/-- **One removed edge keeps `J`.** -/
theorem j_step {ce : CheckEnv} {f F' F : Func} {r : Array Bool} (hwf : WF ce f) (hE : EI f r F')
    (hJ : J f F' F) {b0 : ID} {i0 : Nat} (hb0 : b0 ∈ f.blocks) (hi0 : i0 < (F'.getB b0).succs.size) :
    J f (removeEdgeG false F' b0 i0) (removeEdgeG true F b0 i0) := by
  obtain ⟨ec, hec⟩ : ∃ ec, sOf F' b0 i0 = some ec := ⟨_, Array.getElem?_eq_getElem hi0⟩
  obtain ⟨c, j⟩ := ec
  have hX := hE.xl
  obtain ⟨hcB, hcj⟩ := hX.succ b0 hb0 i0 _ hec
  dsimp only at hcB hcj
  have hcs : 0 < (F'.getB c).preds.size := by
    have := (Array.getElem?_eq_some_iff.1 hcj).1; omega
  obtain ⟨-, hjm, -, -, -, -, h7, h8, -, -, -⟩ :=
    edge_core (n := (F'.getB b0).succs.size - 1) (m := (F'.getB c).preds.size - 1) hX hb0
      (by omega) (by omega) hec (by omega)
  have he : (F'.getB b0).succs[i0]! = ⟨c, j⟩ := by
    rw [getElem!_pos ((F'.getB b0).succs) _ hi0]
    exact Option.some.inj ((Array.getElem?_eq_getElem hi0).symm.trans hec)
  have hgB : F.getB = F'.getB := getB_of_skel hJ.skel
  have he2 : (F.getB b0).succs[i0]! = ⟨c, j⟩ := by rw [hgB]; exact he
  have hsG : skel ((F.removeSucc b0 i0).removePred c j) =
      skel ((F'.removeSucc b0 i0).removePred c j) :=
    skel_removePred_congr (skel_removeSucc_congr hJ.skel b0 i0) c j
  have hvG' : vw ((F'.removeSucc b0 i0).removePred c j) = vw F' := by
    rw [vw_removePred, vw_removeSucc]
  have hvG : vw ((F.removeSucc b0 i0).removePred c j) = vw F := by
    rw [vw_removePred, vw_removeSucc]
  have hgG : ((F.removeSucc b0 i0).removePred c j).getB =
      ((F'.removeSucc b0 i0).removePred c j).getB := getB_of_skel hsG
  have hvals : (((F'.removeSucc b0 i0).removePred c j).getB c).values = (F'.getB c).values := by
    have := congrArg Block.values (h8 c); simpa [bview] using this
  have hn : (((F'.removeSucc b0 i0).removePred c j).getB c).preds.size =
      (F'.getB c).preds.size - 1 := by rw [h7]; simp
  have hnd : (((F'.removeSucc b0 i0).removePred c j).getB c).values.toList.Nodup := by
    obtain ⟨bc, hbc, -⟩ := hwf.blockId c hcB
    have := hwf.valuesNodup c bc ⟨hcB, hbc⟩
    rw [hvals, values_of_kview (hE.kv c)]; unfold Func.getB; rw [hbc]; exact this
  unfold removeEdgeG
  simp only [he, he2]
  rw [← Array.foldl_toList, ← Array.foldl_toList, hgG]
  obtain ⟨h1, h2⟩ := j_phiFold (f := f) (c := c) hjm _ _ _ hnd hsG hn
    (fun x => by rw [hvG, hvG']; exact hJ.val x) (fun v hv u hu hop => by
      rw [hvG'] at hu
      have hv' : v ∈ (F'.getB c).values := by rw [← hvals]; simpa using hv
      have har := hE.arity c hcB v hv' u hu hop
      refine ⟨by omega, fun a ha => ?_⟩
      obtain ⟨u0, hu0, -⟩ := noArgs_some (hE.vals v) hu
      exact ⟨u0, hu0, hE.sub v u0 u hu0 hu a ha⟩)
  exact ⟨h1, h2⟩

/-! ## The walk -/

theorem fs_step {f F' : Func} {r : Array Bool} (hE : EI f r F') (hF : FS f r F') {b : ID}
    (hb : b ∈ f.blocks) (hr : r.getD b false = false) {i : Nat}
    (hi : i < (F'.getB b).succs.size) : FS f r (removeEdgeG false F' b i) := by
  intro x hx hrx hk
  have hxb : x ≠ b := fun h => by subst h; simp_all
  obtain ⟨h1, h2⟩ := removeEdge_other false hE.xl hb hi x
  rw [h1 hxb]; rw [h2] at hk; exact hF x hx hrx hk

theorem j_deadInner {ce : CheckEnv} {f : Func} {r : Array Bool} (hwf : WF ce f) {b : ID}
    (hb : b ∈ f.blocks) (hr : r.getD b false = false) :
    ∀ (fuel i : Nat) (F' F : Func), EI f r F' → FS f r F' → J f F' F →
      J f (deadInner false r b fuel i F') (deadInner true r b fuel i F)
  | 0, _, _, _, _, _, hJ => hJ
  | fuel + 1, i, F', F, hE, hF, hJ => by
    have hg : F.getB b = F'.getB b := by rw [getB_of_skel hJ.skel]
    unfold deadInner
    rw [hg]
    by_cases hi : i < (F'.getB b).succs.size
    · rw [dif_pos hi, dif_pos hi]
      by_cases hc : r.getD (F'.getB b).succs[i].b false = true
      · rw [if_pos hc, if_pos hc]
        exact j_deadInner hwf hb hr fuel i _ _ (ei_step hwf hE hb hi (fun h => by simp_all))
          (fs_step hE hF hb hr hi) (j_step hwf hE hJ hb hi)
      · rw [if_neg hc, if_neg hc]
        exact j_deadInner hwf hb hr fuel (i + 1) F' F hE hF hJ
    · rw [dif_neg hi, dif_neg hi]
      exact hJ

theorem j_deadOuter {ce : CheckEnv} {f : Func} {r : Array Bool} (hwf : WF ce f) :
    ∀ (L : List ID) (F' F : Func), (∀ b ∈ L, b ∈ f.blocks) → EI f r F' → FS f r F' → J f F' F →
      J f (deadOuter false r L F') (deadOuter true r L F)
  | [], _, _, _, _, _, hJ => hJ
  | b :: L, F', F, hL, hE, hF, hJ => by
    have hg : F.getB b = F'.getB b := by rw [getB_of_skel hJ.skel]
    have hL' : ∀ x ∈ L, x ∈ f.blocks := fun x hx => hL x (List.mem_cons_of_mem _ hx)
    unfold deadOuter
    rw [hg]
    by_cases hr : r.getD b false = true
    · rw [if_pos hr, if_pos hr]
      exact j_deadOuter hwf L F' F hL' hE hF hJ
    · rw [if_neg hr, if_neg hr]
      have hr' := Bool.eq_false_iff.2 hr
      obtain ⟨hE', hF'⟩ := ei_deadInner hwf (hL b List.mem_cons_self) hr' _ 0 F' hE hF
      exact j_deadOuter hwf L _ _ hL' hE' hF'
        (j_deadInner hwf (hL b List.mem_cons_self) hr' _ 0 F' F hE hF hJ)

theorem j_firstStep {ce : CheckEnv} {f : Func} {r : Array Bool} (hwf : WF ce f)
    (h2 : FirstTwo f) {b : ID} (hb : b ∈ f.blocks) {F' F : Func} (hE : EI f r F')
    (hF : FS f r F') (hJ : J f F' F) : J f (firstStep false r F' b) (firstStep true r F b) := by
  have hg : F.getB b = F'.getB b := by rw [getB_of_skel hJ.skel]
  unfold firstStep
  rw [hg]
  by_cases hc : (!r.getD b false || (F'.getB b).kind != .First) = true
  · rw [if_pos hc, if_pos hc]; exact hJ
  · rw [if_neg hc, if_neg hc]
    simp only [Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq, not_or,
      Bool.not_eq_false, Decidable.not_not] at hc
    obtain ⟨hr, hkF⟩ := hc
    have hkf : (f.getB b).kind = .First := by
      rcases hE.kind b with h | ⟨-, -, h⟩
      · rw [← h]; exact hkF
      · rw [hkF] at h; cases h
    have hsz : (F'.getB b).succs.size = 2 := by rw [hF b hb hr hkF]; exact h2 b hb hkf
    have hJ1 := j_step hwf hE hJ hb (i0 := 1) (by omega)
    exact ⟨skel_modB_congr hJ1.skel b _, fun x => by rw [vw_modB, vw_modB]; exact hJ1.val x⟩

theorem j_firstFold {ce : CheckEnv} {f : Func} {r : Array Bool} (hwf : WF ce f)
    (h2 : FirstTwo f) :
    ∀ (L : List ID) (F' F : Func), (∀ b ∈ L, b ∈ f.blocks) → EI f r F' → FS f r F' → J f F' F →
      J f (L.foldl (firstStep false r) F') (L.foldl (firstStep true r) F)
  | [], _, _, _, _, _, hJ => hJ
  | b :: L, F', F, hL, hE, hF, hJ => by
    rw [List.foldl_cons, List.foldl_cons]
    obtain ⟨hE', hF'⟩ := ei_firstStep hwf h2 (hL b List.mem_cons_self) hE hF
    exact j_firstFold hwf h2 L _ _ (fun x hx => hL x (List.mem_cons_of_mem _ hx)) hE' hF'
      (j_firstStep hwf h2 (hL b List.mem_cons_self) hE hF hJ)

/-- **deadcode's edge removal against the one keeping `Phi`s.** -/
theorem j_edgesG {ce : CheckEnv} {f : Func} (hwf : WF ce f) (h2 : FirstTwo f) :
    J f (edgesG false f) (edgesG true f) := by
  unfold edgesG
  have hL : ∀ b ∈ f.blocks.toList, b ∈ f.blocks := fun b hb => Array.mem_toList_iff.1 hb
  obtain ⟨hE, hF⟩ := ei_deadOuter hwf f.blocks.toList f hL (ei_init hwf _) (fun _ _ _ _ => rfl)
  exact j_firstFold hwf h2 _ _ _ hL hE hF
    (j_deadOuter hwf _ f f hL (ei_init hwf _) (fun _ _ _ _ => rfl) ⟨rfl, fun _ => .inl rfl⟩)

/-! ## copyelim's invariant -/

theorem listed_of_skel {F F' : Func} (h : skel F = skel F') {a : ID} (ha : Listed F' a) :
    Listed F a := by
  obtain ⟨bid, b, ⟨hm, hb⟩, hx⟩ := ha
  obtain ⟨-, -, h3, -⟩ := skel_parts' h
  exact ⟨bid, b, ⟨h3 ▸ hm, by rw [block?_of_skel h]; exact hb⟩, hx⟩

theorem ei_listed' {ce : CheckEnv} {f F : Func} {r : Array Bool} (hwf : WF ce f) (hE : EI f r F)
    {a : ID} (h : Listed F a) : Listed f a := by
  obtain ⟨bid, b, ⟨hm, hb⟩, ha⟩ := h
  rw [hE.blocks] at hm
  refine ⟨bid, f.getB bid, ⟨hm, block_getB hwf hm⟩, ?_⟩
  rw [← ei_values hE, getB_of_block? hb]; exact ha

/-- A value of `F` has its block, type and ID in `F'`. -/
theorem jv_keep {f : Func} {V' V : ID → Option Value} {x : ID} (h : JV f V' V x) :
    (V x).map (fun u => (u.block, u.type, u.id)) = (V' x).map (fun u => (u.block, u.type, u.id)) := by
  rcases h with h | ⟨u, w, u0, hu', -, hu, -⟩
  · rw [h]
  · rw [hu, hu']; rfl

/-- **`F` is a state of copyelim's sweeps from `F'`** (given copyelim's fragment of `F`). -/
theorem inv_of_j {ce : CheckEnv} {tabs : Tables} {f F' F : Func} {r : Array Bool} (hwf : WF ce f)
    (hE : EI f r F') (hJ : J f F' F) (hfrag : CopyFrag tabs F) : Inv tabs F' F := by
  have hwf' := wf_of_ei hwf hE
  have hLs : ∀ a, Listed F' a → Listed F a := fun a h => listed_of_skel hJ.skel h
  have hsrc : ∀ a, Listed F' a → ∃ r n, Src (vw F) a r n := by
    intro a ha
    obtain ⟨r, n, h⟩ := hfrag.acyclic a (hLs a ha)
    exact ⟨r, n, src_congr (by intro y; rw [cstep_vw]) h⟩
  have hty : ∀ y v, vw F y = some v → ∃ v', F'.value? y = some v' ∧ v'.type = v.type := by
    intro y v hv
    have := jv_keep (hJ.val y)
    rw [hv] at this
    cases h' : vw F' y with
    | none => rw [h'] at this; cases this
    | some v' =>
      rw [h'] at this
      obtain ⟨v'', hv'', rfl⟩ := vw_eq_some h'
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at this
      exact ⟨v'', hv'', this.2.1.symm⟩
  -- chains of `F'` ending at a non-phi avoid the `Phi`s that became copies
  have hends : ∀ {x r n}, Src (vw F') x r n → NotPhi F' r → Src (vw F) x r n := by
    intro x r n hs hr
    induction hs with
    | sink h0 =>
      rcases hJ.val _ with h | ⟨u, w, u0, hu', hop, -⟩
      · exact .sink (by unfold cstep at h0 ⊢; rw [h]; exact h0)
      · obtain ⟨u1, hu1, rfl⟩ := vw_eq_some hu'
        exact absurd hop (hr u1 hu1)
    | step h1 _ ih =>
      rcases hJ.val _ with h | ⟨u, w, u0, hu', hop, -⟩
      · exact .step (by unfold cstep at h1 ⊢; rw [h]; exact h1) (ih hr)
      · rw [cstep_of_ne hu' (by rw [hop]; decide)] at h1; cases h1
  refine ⟨hJ.skel, fun x => jv_keep (hJ.val x), fun x hx fv hfv => ?_, fun x hx v hv c hc => ?_,
    hsrc, fun x hx w hw => ?_, fun x r n hs hr => ⟨n, hends hs hr⟩⟩
  · have hfv' := vw_of_value? hfv
    rcases hJ.val x with h | ⟨u, w, u0, hu', hop, hu, -, hall, -, -⟩
    · refine ⟨strip fv, h.trans hfv', .same rfl rfl rfl rfl fun k a c ha hc => ?_⟩
      have hc' : fv.args[k]? = some c := hc
      rw [ha] at hc'; cases hc'
      obtain ⟨bid, b, hb, hxb⟩ := hx
      obtain ⟨r, n, hs⟩ := hsrc a (hwf'.argListed bid b x fv ⟨hb, hxb, hfv⟩ a
        (Array.mem_of_getElem? ha))
      exact ⟨r, n, n, hs, hs⟩
    · rw [hfv'] at hu'; cases hu'
      obtain ⟨v', hv', hvv⟩ := vw_eq_some hu
      have hop' : v'.op = .Copy := by have := congrArg Value.op hvv; exact this.symm
      have hty' : v'.type = fv.type := by have := congrArg Value.type hvv; exact this.symm
      have hcx : cstep (vw F) x = some (some w) := cstep_of_copy hu rfl rfl
      obtain ⟨r, n, hs⟩ := hsrc x hx
      refine ⟨_, hu, .phi w hop rfl rfl
        (hty' ▸ hfrag.copyNZ x (hLs x hx) v' hv' hop') fun a ha => ?_⟩
      cases hs with
      | sink h0 => rw [hcx] at h0; cases h0
      | step h1 hs' =>
        rw [hcx] at h1; cases h1
        rcases hall a ha with rfl | rfl
        · exact ⟨r, _, _, .step hcx hs', hs'⟩
        · exact ⟨r, _, _, hs', hs'⟩
  · rcases hJ.val x with h | ⟨u, w, u0, -, -, hu, -, -, hu0, hw0⟩
    · rw [h] at hv
      obtain ⟨v', hv', rfl⟩ := vw_eq_some hv
      obtain ⟨bid, b, hb, hxb⟩ := hx
      exact hwf'.argListed bid b x v' ⟨hb, hxb, hv'⟩ c hc
    · rw [hu] at hv; cases hv
      have hcw : c = w := by simpa using hc
      subst hcw
      obtain ⟨u1, hu1, rfl⟩ := vw_eq_some hu0
      obtain ⟨bid, b, hb, hxb⟩ := ei_listed' hwf hE hx
      exact ei_listed hwf hE (hwf.argListed bid b x u1 ⟨hb, hxb, hu1⟩ c hw0)
  · rw [cstep_vw] at hw
    obtain ⟨v, hv, hop, ha⟩ := cstep_some_some hw
    obtain ⟨wv0, hwv0, hR⟩ := hfrag.shape x (hLs x hx) v hv (.inl hop) w (by rw [ha]; simp)
    obtain ⟨xv, hxv, htx⟩ := hty x (strip v) (vw_of_value? hv)
    obtain ⟨wv, hwv, htw⟩ := hty w (strip wv0) (vw_of_value? hwv0)
    refine ⟨xv, wv, hxv, hwv, ?_⟩
    have h1 : xv.type = v.type := htx
    have h2 : wv.type = wv0.type := htw
    rw [h1, h2]; exact hR

end GoFV.Proof.Dead

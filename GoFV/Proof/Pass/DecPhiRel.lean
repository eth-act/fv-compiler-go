import GoFV.Opt.DecPhiCheck
import GoFV.Proof.Pass.ECTree
import GoFV.Proof.Pass.ECChain
import GoFV.Proof.Pass.ECIdent
import GoFV.Proof.Merge

variable [GoFV.SSA.Sem.Addrs]

/-!
# Decompose's phi splitting: components and the checker's facts (issue #17)

`ext π y`: component `π` of the value `y` (per step `(k, t)`: `Comp.select k`, retyped at `t`),
what a value of meaning `(s, π)` (`DecPhiCheck.meanOf`) holds of the source's register of `s`.
It is monotone (`ext_mono`), has the last step's shape (`ext_hasTy`), and a value of an
aggregate shape is refined by the `Make` of anything refining its components (`refines_make`;
a zero-sized one by `Empty`, `refines_empty`).

The rest decodes `decPhiCheck`: the CFG and own aux (`check_spec`), per block (`blockOK_spec`)
and per value (`srcOK_spec`, `newOK_spec` and the classes `selOK_spec`, `phiOK_spec`,
`makeOK_spec`, `emptyOK_spec`).
-/

namespace GoFV.Proof.DecPhi

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.ECCheck GoFV.Opt.DecPhiCheck

/-! ## Components -/

/-- Component `π` of `y`. -/
def ext : Path → Val → Val
  | [], y => y
  | (k, t) :: π, y => ext π ((Comp.select k [y]).retype t)

theorem ext_snoc : ∀ (π : Path) (k : Nat) (t : Ty) (y : Val),
    ext (π ++ [(k, t)]) y = (Comp.select k [ext π y]).retype t
  | [], _, _, _ => rfl
  | (_, _) :: π, k, t, _ => ext_snoc π k t _

theorem ext_mono : ∀ (π : Path) {y y' : Val}, Sem.Refines y y' → Sem.Refines (ext π y) (ext π y')
  | [], _, _, h => h
  | (k, t) :: π, _, _, h => ext_mono π (retype_mono t (EC.ec_select_mono k h))

theorem dropLast_append_of_getLast? {α : Type} :
    ∀ {l : List α} {a : α}, l.getLast? = some a → l.dropLast ++ [a] = l
  | [], _, h => by cases h
  | [b], a, h => by simp at h; subst h; rfl
  | b :: c :: l, a, h => by
    have h' : (c :: l).getLast? = some a := by simpa using h
    have := dropLast_append_of_getLast? h'
    simp only [List.dropLast_cons_cons, List.cons_append]
    rw [this]

theorem ext_hasTy {π : Path} {k : Nat} {t : Ty} (h : π.getLast? = some (k, t)) (y : Val) :
    (ext π y).hasTy t = true := by
  rw [← dropLast_append_of_getLast? h, ext_snoc]
  exact Val.retype_hasTy _ _

/-- Pointwise refinement of the fields of a value with field shapes `ts`. -/
theorem refinesList_of : ∀ {vs ws : List Val} {ts : List Ty}, Val.hasTyList vs ts = true →
    ws.length = ts.length →
    (∀ k (hk : k < ts.length) (hw : k < ws.length),
      Sem.Refines ((vs.getD k .poison).retype ts[k]) ws[k]) → Sem.RefinesList vs ws
  | [], [], [], _, _, _ => .nil
  | v :: vs, w :: ws, t :: ts, hv, hl, h => by
    simp only [Val.hasTyList, Bool.and_eq_true] at hv
    have h0 := h 0 (by simp) (by simp)
    simp only [List.getD_cons_zero, List.getElem_cons_zero] at h0
    rw [Val.retype_of_hasTy hv.1] at h0
    exact .cons h0 (refinesList_of hv.2 (by simpa using hl) fun k hk hw => by
      have := h (k + 1) (by simp; omega) (by simp; omega)
      simpa using this)
  | [], [], _ :: _, hv, _, _ => by simp [Val.hasTyList] at hv
  | [], _ :: _, _, hv, hl, _ => by
    cases ‹List Ty› with
    | nil => simp at hl
    | cons _ _ => simp [Val.hasTyList] at hv
  | _ :: _, [], ts, hv, hl, _ => by
    cases ts with
    | nil => simp [Val.hasTyList] at hv
    | cons _ _ => simp at hl
  | _ :: _, _ :: _, [], hv, _, _ => by simp [Val.hasTyList] at hv

/-- **A `Make` of refined components** refines a value of its aggregate shape. -/
theorem refines_make {fs : List (Nat × Ty)} {n : Nat} {y : Val}
    (hy : y.hasTy (.agg fs n) = true) {ws : List Val} (hl : ws.length = fs.length)
    (hw : ∀ k (hk : k < fs.length) (hk' : k < ws.length),
      Sem.Refines ((Comp.select k [y]).retype fs[k].2) ws[k]) :
    Sem.Refines y ((Val.agg ws).retype (.agg fs n)) := by
  cases y with
  | poison => exact .poison _
  | agg vs =>
    have hv : Val.hasTyList vs (fs.map (·.2)) = true := by simpa [Val.hasTy] using hy
    have hr : Sem.RefinesList vs ws := refinesList_of hv (by simpa using hl) fun k hk hk' => by
      have := hw k (by simpa using hk) hk'
      simpa [Comp.select] using this
    have := retype_mono (.agg fs n) (Sem.Refines.agg hr)
    rwa [Val.retype_of_hasTy hy] at this
  | _ => simp [Val.hasTy] at hy

/-- A zero-sized value is refined by `Empty`'s. -/
theorem refines_empty {y : Val} (hy : y.hasTy .empty = true) : Sem.Refines y .empty := by
  cases y with
  | poison => exact .poison _
  | empty => exact .empty
  | _ => simp [Val.hasTy] at hy

/-! ## The checker's facts -/

theorem pathBeq_eq : ∀ {π π' : Path}, pathBeq π π' = true → π = π'
  | [], [], _ => rfl
  | (k, t) :: π, (k', t') :: π', h => by
    simp only [pathBeq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1.1, Ty.eq_of_beq h.1.2, pathBeq_eq h.2]
  | [], _ :: _, h => by simp [pathBeq] at h
  | _ :: _, [], h => by simp [pathBeq] at h

theorem meanIs_spec {m : Array (Option Mean)} {z s : ID} {π : Path} (h : meanIs m z s π = true) :
    meanAt m z = some (s, π) := by
  unfold meanIs at h
  split at h
  · next s' π' heq =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rw [heq, h.1, pathBeq_eq h.2]
  · cases h

theorem sameOK_spec {u w : Value} (h : sameOK u w = true) :
    w.op = u.op ∧ w.type = u.type ∧ w.auxInt = u.auxInt ∧ w.aux = u.aux ∧ w.args = u.args := by
  unfold sameOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem argsMeanOK_spec {m : Array (Option Mean)} {s : ID} {π : Path} :
    ∀ {j : Nat} {fs : List (Nat × Ty)} {as : List ID}, argsMeanOK m s π j fs as = true →
      as.length = fs.length ∧ ∀ k (hk : k < fs.length) (hk' : k < as.length),
        meanAt m as[k] = some (s, π ++ [(j + k, fs[k].2)])
  | _, [], [], _ => ⟨rfl, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩
  | j, (o, t) :: fs, a :: as, h => by
    unfold argsMeanOK at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hl, hk⟩ := argsMeanOK_spec h.2
    refine ⟨by simp [hl], fun k hk1 hk2 => ?_⟩
    cases k with
    | zero => simpa using meanIs_spec h.1
    | succ k =>
      have := hk k (by simp at hk1; omega) (by simp at hk2; omega)
      simp only [List.getElem_cons_succ]
      rw [this, show j + 1 + k = j + (k + 1) by omega]
  | _, [], _ :: _, h => by simp [argsMeanOK] at h
  | _, _ :: _, [], h => by simp [argsMeanOK] at h

theorem makeOK_spec {sh : Array Ty} {g : Func} {m : Array (Option Mean)} {w : Value} {s : ID}
    {π : Path} (h : makeOK sh g m w s π = true) :
    isMake w.op = true ∧ ∃ fs n, (shapeOf sh g w.id).asAgg = .agg fs n ∧ w.args.size = fs.length ∧
      ∀ k (hk : k < fs.length) (hk' : k < w.args.size),
        meanAt m w.args[k] = some (s, π ++ [(k, fs[k].2)]) := by
  unfold makeOK at h
  simp only [Bool.and_eq_true] at h
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  split at h2
  · next fs n hsh =>
    obtain ⟨hl, hk⟩ := argsMeanOK_spec h2
    refine ⟨fs, n, hsh, by simpa using hl, fun k hk1 hk2 => ?_⟩
    have := hk k hk1 (by simpa using hk2)
    simpa using this
  · cases h2

theorem emptyOK_spec {sh : Array Ty} {g : Func} {w : Value} (h : emptyOK sh g w = true) :
    w.op = .Empty ∧ w.args = #[] ∧ shapeOf sh g w.id = .empty := by
  unfold emptyOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.isEmpty_iff] at h
  exact ⟨h.1.1, h.1.2, Ty.eq_of_beq h.2⟩

theorem selOK_spec {m : Array (Option Mean)} {w : Value} {s : ID} {π : Path}
    (h : selOK m w s π = true) :
    ∃ k a t, selIdx? w = some k ∧ w.args.toList = [a] ∧ π.getLast? = some (k, t) ∧
      meanAt m a = some (s, π.dropLast) := by
  unfold selOK at h
  split at h
  · next k a k' t hk ha hl =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h2⟩ := h
    exact ⟨k, a, t, hk, ha, hl, meanIs_spec h2⟩
  · cases h

theorem phiOK_spec {sh : Array Ty} {f : Func} {m : Array (Option Mean)} {w : Value} {s : ID}
    {π : Path} (h : phiOK sh f m w s π = true) :
    w.op = .Phi ∧ ∃ u, f.value? s = some u ∧ u.op = .Phi ∧ w.args.size = u.args.size ∧
      ∀ (j : Nat) (c a : ID), w.args[j]? = some c → u.args[j]? = some a →
        meanAt m c = some (a, π) ∧ shapeOf sh f a = shapeOf sh f s := by
  unfold phiOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hop, h2⟩ := h
  refine ⟨hop, ?_⟩
  split at h2
  · next u hu =>
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h2
    obtain ⟨⟨hu1, hsz⟩, hall⟩ := h2
    refine ⟨u, hu, hu1, hsz, fun j c a hc ha => ?_⟩
    have hj : j < (w.args.toList.zip u.args.toList).length := by
      have := (Array.getElem?_eq_some_iff.1 hc).1
      simp [hsz] at this ⊢; omega
    have hmem : (c, a) ∈ w.args.toList.zip u.args.toList := by
      have : (w.args.toList.zip u.args.toList)[j]? = some (c, a) := by
        rw [List.getElem?_zip_eq_some]
        exact ⟨by simpa using hc, by simpa using ha⟩
      exact List.mem_of_getElem? this
    have := hall _ hmem
    simp only [Bool.and_eq_true] at this
    exact ⟨meanIs_spec this.1, Ty.eq_of_beq this.2⟩
  · cases h2

theorem newOK_spec {sh : Array Ty} {f g : Func} {m : Array (Option Mean)} {fb : Block}
    {w : Value} (h : newOK sh f g m fb w = true) :
    ∃ s π, meanAt m w.id = some (s, π) ∧ π ≠ [] ∧ shapeOf sh g w.id = meanTy sh f s π ∧
      s ∈ fb.values ∧
      (selOK m w s π = true ∨ phiOK sh f m w s π = true ∨ makeOK sh g m w s π = true ∨
        emptyOK sh g w = true) := by
  unfold newOK at h
  split at h
  · next s π hm =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      Array.contains_iff_mem] at h
    obtain ⟨⟨⟨hne, hsh⟩, hs⟩, hcls⟩ := h
    exact ⟨s, π, hm, hne, Ty.eq_of_beq hsh, hs, by
      rcases hcls with ((h | h) | h) | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr h))⟩
  · cases h

theorem srcOK_spec {sh : Array Ty} {g : Func} {m : Array (Option Mean)} {u w : Value}
    (h : srcOK sh g m u w = true) :
    w.block = u.block ∧ meanAt m u.id = some (u.id, []) ∧
      (sameOK u w = true ∨
        (u.op = .Phi ∧ w.type = u.type ∧ (makeOK sh g m w u.id [] = true ∨ emptyOK sh g w = true))) := by
  unfold srcOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hb, hm⟩, hc⟩ := h
  refine ⟨hb, meanIs_spec hm, ?_⟩
  rcases hc with hc | ⟨⟨hp, ht⟩, hc⟩
  · exact .inl hc
  · exact .inr ⟨hp, ht, hc⟩

/-- What `blockOK` says of block `bid`. -/
theorem blockOK_spec {sh : Array Ty} {f g : Func} {m : Array (Option Mean)} {bid : ID}
    {fb : Block} (h : DecPhiCheck.blockOK sh f g m bid = true) (hfb : f.block? bid = some fb) :
    ∃ gb, g.block? bid = some gb ∧ gb.kind = fb.kind ∧ gb.controls = fb.controls ∧
      (∀ x ∈ fb.values, x ∈ gb.values) ∧
      (∀ z ∈ gb.values, ∃ w, g.value? z = some w ∧ w.id = z ∧
        (∀ u, f.value? z = some u → z ∈ fb.values ∧ srcOK sh g m u w = true) ∧
        (f.value? z = none → newOK sh f g m fb w = true)) ∧
      ∃ of og, schedule f fb = some of ∧ schedule g gb = some og ∧
        of.toList.filter (npOf f fb) = og.toList.filter (npOf f fb) := by
  unfold DecPhiCheck.blockOK at h
  rw [hfb] at h
  cases hgb : g.block? bid with
  | none => rw [hgb] at h; cases h
  | some gb =>
    rw [hgb] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨hk, hc⟩, hsub⟩, hval⟩, hsch⟩ := h
    refine ⟨gb, rfl, hk, hc, fun x hx => Array.contains_iff_mem.1 (Array.all_eq_true'.1 hsub x hx),
      fun z hz => ?_, ?_⟩
    · have hz' := Array.all_eq_true'.1 hval z hz
      split at hz'
      · next w hw =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hz'
        obtain ⟨hid, hz'⟩ := hz'
        refine ⟨w, hw, hid, fun u hu => ?_, fun hn => ?_⟩
        · rw [hu] at hz'
          simp only [Bool.and_eq_true, Array.contains_iff_mem] at hz'
          exact hz'
        · rw [hn] at hz'; exact hz'
      · cases hz'
    · split at hsch
      · next of og h1 h2 =>
        exact ⟨of, og, h1, h2, by simpa using hsch⟩
      · cases hsch

theorem check_spec {tabs : Tables} {f g : Func} (h : decPhiCheck tabs f g = true) :
    DomCert.cfgView g = DomCert.cfgView f ∧ g.ownAux = f.ownAux ∧
      ∀ bid ∈ f.blocks, DecPhiCheck.blockOK (typeShapes tabs) f g (meanOf (typeShapes tabs) f g) bid = true := by
  unfold decPhiCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true'] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, h3⟩

end GoFV.Proof.DecPhi

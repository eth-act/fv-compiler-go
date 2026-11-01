import GoFV.Proof.Pass.SegBlock
import GoFV.Proof.Pass.StructStoreEval

/-!
# Segments: one block's evaluation (issue #151)

`Blk.step`: one value of the target's schedule keeps `TFacts`, if every target root it reaches
is covered (`Cov`: a kept root the source evaluated, or a fresh value or anchor of a segment whose
roots in `f` the source evaluated) and an argument lookup it reaches was evaluated by the source.
`okCase`: if the source evaluates the block, the target does, its registers refining the source's
on the values the target keeps. `panicCase`: if the source panics, the target panics alike on a
refined memory: the panicking root is no segment's (`SegSound`: those never panic), and the
target's roots before it are covered (`segRoots_prefix`: a segment's roots are put in at the last
of its roots in `f`).
-/

namespace GoFV.Proof.Seg

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Proof.CopyElim GoFV.Opt GoFV.Opt.RewriteCheck
open GoFV.Proof.CSE (Base Node SFacts)
open GoFV.Proof.AtomSim (Reg rv evalValue_of_regs regs_of_ok)
open GoFV.Proof.StructStore (Src ssSame_spec pureEval)

variable {Q : Mem → Prop} {env : Env} {tabs : Tables} {f g : Func} {bid : ID} {fb gb : Block}
  {F0 F0T : Frame} {oS oT : Array ID}

/-! ## The segments' list -/

theorem anchor_iff (x : ID) : (segList (segArr tabs f g)).any (·.1 == x) = true ↔
    ∃ D N, segOK tabs f g x = some (D, N) := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨⟨x', D, N⟩, hm, he⟩
    simp only [beq_iff_eq] at he; subst he
    exact ⟨D, N, mem_segList.1 hm⟩
  · rintro ⟨D, N, h⟩
    exact ⟨(x, D, N), mem_segList.2 h, by simp⟩

theorem segOf_some (R : SRel tabs f g) {z x : ID} (h : segOf (segList (segArr tabs f g)) z = some x) :
    (z = x ∧ ∃ D N, segOK tabs f g x = some (D, N)) ∨ Drop tabs f g x z := by
  unfold segOf at h
  split at h
  · next ha => cases h; exact .inl ⟨rfl, (anchor_iff z).1 ha⟩
  · exact .inr ((R.own z x).1 h)

theorem segOf_anchor {x : ID} {D N : List ID} (h : segOK tabs f g x = some (D, N)) :
    segOf (segList (segArr tabs f g)) x = some x := by
  unfold segOf; rw [ite_eq_left ((anchor_iff x).2 ⟨D, N, h⟩)]

theorem segOf_drop (R : SRel tabs f g) {x z : ID} (h : Drop tabs f g x z) :
    segOf (segList (segArr tabs f g)) z = some x := by
  unfold segOf
  have hna : ¬ (segList (segArr tabs f g)).any (·.1 == z) = true := fun ha => by
    obtain ⟨D, N, hs⟩ := (anchor_iff z).1 ha
    exact R.anchorNot z D N hs x h
  rw [ite_eq_right hna]; exact (R.own z x).2 h

theorem mem_segNew {x y : ID} (hy : y ∈ segNew g (segList (segArr tabs f g)) x) :
    ∃ D N, segOK tabs f g x = some (D, N) ∧ y ∈ segL x N := by
  unfold segNew at hy
  cases hfd : (segList (segArr tabs f g)).find? (·.1 == x) with
  | none => rw [hfd] at hy; simp at hy
  | some s =>
    rw [hfd] at hy
    obtain ⟨x', D, N⟩ := s
    have h1 := List.mem_of_find?_eq_some hfd
    have h2 := List.find?_some hfd
    simp only [beq_iff_eq] at h2; subst h2
    simp only [Option.map_some, Option.getD_some, List.mem_filter] at hy
    exact ⟨D, N, mem_segList.1 h1, hy.1⟩

/-- `segRoots` before a root of no segment: the roots before it are those of no segment before it,
and segments' roots put in at the last of their roots in `f`, which are all before it. -/
theorem segRoots_prefix (h : Func) (S : List (ID × List ID × List ID)) (r : ID)
    (hr : segOf S r = none) (L2 : List ID) :
    ∀ L1 : List ID, ∃ P Q, segRoots h S (L1 ++ r :: L2) = P ++ r :: Q ∧
      ∀ y ∈ P, (y ∈ L1 ∧ segOf S y = none) ∨
        ∃ x, y ∈ segNew h S x ∧ ∀ z ∈ L1 ++ r :: L2, segOf S z = some x → z ∈ L1
  | [] => ⟨[], segRoots h S L2, by simp [segRoots, hr], by simp⟩
  | a :: L1 => by
    obtain ⟨P, Q, hPQ, hP⟩ := segRoots_prefix h S r hr L2 L1
    cases ha : segOf S a with
    | none =>
      refine ⟨a :: P, Q, by simp [segRoots, ha, hPQ], fun y hy => ?_⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · exact .inl ⟨List.mem_cons_self, ha⟩
      · rcases hP y hy with ⟨h1, h2⟩ | ⟨x, h1, h2⟩
        · exact .inl ⟨List.mem_cons_of_mem _ h1, h2⟩
        · refine .inr ⟨x, h1, fun z hz hzx => ?_⟩
          rcases List.mem_cons.1 hz with rfl | hz
          · rw [ha] at hzx; cases hzx
          · exact List.mem_cons_of_mem _ (h2 z hz hzx)
    | some x =>
      refine ⟨(if (L1 ++ r :: L2).any (fun z => segOf S z == some x) then [] else segNew h S x) ++ P,
        Q, ?_, fun y hy => ?_⟩
      · simp only [List.cons_append, segRoots, ha, hPQ, List.append_assoc]
      · rcases List.mem_append.1 hy with hy | hy
        · by_cases hany : (L1 ++ r :: L2).any (fun z => segOf S z == some x) = true
          · rw [ite_eq_left hany] at hy; simp at hy
          · rw [ite_eq_right hany] at hy
            refine .inr ⟨x, hy, fun z hz hzx => ?_⟩
            rcases List.mem_cons.1 hz with rfl | hz
            · exact List.mem_cons_self
            · exact absurd (List.any_eq_true.2 ⟨z, hz, by simp [hzx]⟩) hany
        · rcases hP y hy with ⟨h1, h2⟩ | ⟨x2, h1, h2⟩
          · exact .inl ⟨List.mem_cons_of_mem _ h1, h2⟩
          · refine .inr ⟨x2, h1, fun z hz hzx => ?_⟩
            rcases List.mem_cons.1 hz with rfl | hz
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (h2 z hz hzx)

/-- A target root is covered: a kept root of `f` the source evaluated, or a fresh value or the
anchor of a segment whose roots in `f` the source evaluated. -/
def Cov (tabs : Tables) (f g : Func) (pre : List ID) (n : ID) : Prop :=
  (n ∈ pre ∧ ∀ D N, segOK tabs f g n ≠ some (D, N)) ∨
    ∃ x D N, segOK tabs f g x = some (D, N) ∧ n ∈ segL x N ∧ Covered f pre x D

namespace Blk

variable (K : Blk Q env tabs f g bid fb gb F0 F0T oS oT)
include K

/-- **One target step.** -/
theorem step (hE : env.Mono) {S T : Frame} {k j : Nat} {n : ID}
    (hS : SFacts env tabs f F0 S (oS.toList.take k))
    (hT : TFacts env tabs f g F0T S T (oS.toList.take k) (oT.toList.take j))
    (hjT : oT.toList[j]? = some n)
    (hcov : CSE.rootNode g n = true → Cov tabs f g (oS.toList.take k) n)
    (hpure : ∀ fv, f.value? n = some fv → n ∉ oS.toList.take k →
      fv.op ≠ .Arg ∧ fv.op ≠ .ArgIntReg)
    (hinv : ∀ (z : ID) (y : Val), S.regs[z]? = some (some y) → MemInv.MemsOK Q y) :
    ∃ y, stepV env (Ctx.make tabs g) T n = .ok y ∧
      TFacts env tabs f g F0T S (T.set n y) (oS.toList.take k) (oT.toList.take (j + 1)) := by
  obtain ⟨hnb, gv, hgv, hgph⟩ := K.memT.1 (List.mem_of_getElem? hjT)
  have hkept : ∀ fv, f.value? n = some fv → ssSame fv gv = true →
      ∀ x D N, segOK tabs f g x = some (D, N) → n ∉ segL x N := by
    intro fv hfv hss x D N hs hn
    obtain ⟨d⟩ := segOK_spec hs
    simp only [segL, List.mem_append, List.mem_singleton] at hn
    rcases hn with hn | rfl
    · rw [(d.hN n hn).1] at hfv; cases hfv
    · rw [d.hfv] at hfv; cases hfv; rw [d.hgv] at hgv; cases hgv; rw [d.hns] at hss; cases hss
  have keptStep : ∀ fv, f.value? n = some fv → ssSame fv gv = true → ∀ y,
      evalValue env (Ctx.make tabs g) T gv = .ok y →
      (n ∈ oS.toList.take k → ∃ yS, S.regs[n]? = some (some yS) ∧ Sem.Refines yS y) →
      ∃ y, stepV env (Ctx.make tabs g) T n = .ok y ∧
        TFacts env tabs f g F0T S (T.set n y) (oS.toList.take k) (oT.toList.take (j + 1)) :=
    fun fv hfv hss y hy hrel => ⟨y, by rw [stepV_of (ctx := Ctx.make tabs g) hgv, hy],
      K.tstep hjT hT hrel fun x D N hs _ _ _ hn => absurd hn (hkept fv hfv hss x D N hs)⟩
  by_cases hroot : CSE.rootNode g n = true
  · rcases hcov hroot with ⟨hnp, hna⟩ | ⟨x, D, N, hs, hn, hc⟩
    · obtain ⟨_, fv, hfv, _⟩ := K.hLk k n hnp
      obtain ⟨-, hnd⟩ := K.nodeF ⟨hnb, gv, hgv, hgph⟩ hfv
      obtain ⟨gv', hgv', hsv⟩ := K.gval hfv hnd
      rw [hgv] at hgv'; cases hgv'
      have hss : ssSame fv gv = true := hsv.resolve_right fun ⟨D, N, h⟩ => hna D N h
      obtain ⟨y, hy, yS, hyS, hr⟩ := K.keptOk hE hS hT hjT hnp hgv hfv hss
      exact keptStep fv hfv hss y hy fun _ => ⟨yS, hyS, hr⟩
    · exact K.segStep hE hS hT hjT hs hc hn hinv
  · have hroot' : CSE.rootNode g n = false := by simpa using hroot
    cases hfv : f.value? n with
    | none =>
      obtain ⟨x, D, N, hs, hnN⟩ := K.rel.fresh n gv hfv hgv
      obtain ⟨d⟩ := segOK_spec hs
      rw [d.hroot n (by simp [segL, hnN])] at hroot'; cases hroot'
    | some fv =>
      obtain ⟨hnF, hnd⟩ := K.nodeF ⟨hnb, gv, hgv, hgph⟩ hfv
      obtain ⟨gv', hgv', hsv⟩ := K.gval hfv hnd
      rw [hgv] at hgv'; cases hgv'
      have hss : ssSame fv gv = true := hsv.resolve_right fun ⟨D, N, h⟩ => by
        obtain ⟨d⟩ := segOK_spec h
        rw [d.hroot n (by simp [segL])] at hroot'; cases hroot'
      by_cases hnp : n ∈ oS.toList.take k
      · obtain ⟨y, hy, yS, hyS, hr⟩ := K.keptOk hE hS hT hjT hnp hgv hfv hss
        exact keptStep fv hfv hss y hy fun _ => ⟨yS, hyS, hr⟩
      · obtain ⟨-, hop, -, -, -, -, hga⟩ := ssSame_spec hss
        have hp0 : Sem.prio gv.op = 0 := by simpa [CSE.rootNode, hgv] using hroot'
        obtain ⟨ha, hb⟩ := hpure fv hfv hnp
        obtain ⟨hxb, fv', hfv', hph⟩ := hnF
        rw [hfv] at hfv'; cases hfv'
        obtain ⟨y, hy⟩ := pureEval (env := env) (tabs := tabs) (fun a ha' => by
            rcases K.arg_base_or_node hxb hfv hph (hga ▸ ha') with hB | hn
            · exact K.argDefd hS hT hjT hgv ha' (.inl hB)
            · have hag := K.argG hnb hgv ha'
              obtain ⟨av, hav⟩ := Option.isSome_iff_exists.1 hag
              exact K.argDefd hS hT hjT hgv ha' (.inr (K.nodeG hn fun x' hd => by
                rw [K.rel.dropNone x' _ hd] at hav; cases hav)))
          (CSE.Blk.isRoot_of_prio hp0) (by rw [hop]; exact ha) (by rw [hop]; exact hb)
        exact keptStep fv hfv hss y hy fun h => absurd h hnp

omit K in
/-- **The target's loop** over the first `K'` values of its schedule. -/
theorem loop {S : Frame} {pre : List ID} {K' : Nat}
    (hev : ∀ j x, j < K' → oT.toList[j]? = some x → ∀ T,
      TFacts env tabs f g F0T S T pre (oT.toList.take j) →
      ∃ y, stepV env (Ctx.make tabs g) T x = .ok y ∧
        TFacts env tabs f g F0T S (T.set x y) pre (oT.toList.take (j + 1))) :
    ∃ T', evalAll env (Ctx.make tabs g) F0T (oT.toList.take K') = .ok T' ∧
      TFacts env tabs f g F0T S T' pre (oT.toList.take K') := by
  have hstep : ∀ d x rest T, oT.toList.take K' = d ++ x :: rest →
      (d = oT.toList.take d.length ∧ TFacts env tabs f g F0T S T pre d) →
      ∃ y, stepV env (Ctx.make tabs g) T x = .ok y ∧
        (d ++ [x] = oT.toList.take (d ++ [x]).length ∧
          TFacts env tabs f g F0T S (T.set x y) pre (d ++ [x])) := by
    intro d x rest T hL ⟨hd, hT⟩
    have hjx : (oT.toList.take K')[d.length]? = some x := by rw [hL]; simp
    have hjK : d.length < K' := by
      have := (List.getElem?_eq_some_iff.1 hjx).1; simp at this; omega
    have hj : oT.toList[d.length]? = some x := by
      rwa [List.getElem?_take_of_lt hjK] at hjx
    rw [hd] at hT
    obtain ⟨y, hy, hT'⟩ := hev d.length x hjK hj T hT
    refine ⟨y, hy, ?_, ?_⟩
    · rw [List.length_append, List.length_singleton, take_succ_eqT hj, ← hd]
    · rw [hd, ← take_succ_eqT hj]; exact hT'
  have h0 : TFacts env tabs f g F0T S F0T pre (oT.toList.take 0) := by
    refine ⟨rfl, rfl, fun _ _ => rfl, fun _ h => by simp at h, fun _ h => by simp at h, ?_⟩
    intro _ _ _ _ _ _ _ _ _ hn; simp at hn
  obtain ⟨T', h1, -, h2⟩ := CSE.evalAll_loop hstep (oT.toList.take K') [] F0T rfl ⟨rfl, h0⟩
  exact ⟨T', h1, h2⟩

/-- The roots of a segment of the block are source nodes. -/
theorem segRoots_node {x : ID} {D N : List ID} (hs : segOK tabs f g x = some (D, N))
    {d : SegD tabs f g x D N} (hb : d.fv.block = bid) {s : ID} (hsm : s ∈ D ++ [x])
    (hr : CSE.rootNode f s = true) : Node f fb s := by
  have hl : s ∈ fb.values := by
    simp only [List.mem_append, List.mem_singleton] at hsm
    rcases hsm with hsm | rfl
    · obtain ⟨b, hfb, hsb⟩ := (d.hD s hsm).1
      rw [hb, K.hfb] at hfb; cases hfb; exact hsb
    · obtain ⟨b, hfb, hsb⟩ := d.hlisted
      rw [hb, K.hfb] at hfb; cases hfb; exact hsb
  obtain ⟨v, hv, -, -⟩ := K.valueIn hl
  exact ⟨hl, v, hv, root_ne_phi hr hv⟩

/-- **The ok case.** -/
theorem okCase (hE : env.Mono) {G : Frame}
    (h : evalAll env (Ctx.make tabs f) F0 oS.toList = .ok G) :
    ∃ GT, evalAll env (Ctx.make tabs g) F0T oT.toList = .ok GT ∧
      GT = { G with regs := GT.regs } ∧ GT.regs.size = g.valueTab.size ∧ RR f g G.regs GT.regs := by
  have hS : SFacts env tabs f F0 G (oS.toList.take oS.toList.length) := by
    rw [List.take_length]; exact K.sfacts ⟨[], by simp⟩ h
  have hcovAll : ∀ n, n ∈ oT.toList → ∀ x D N, segOK tabs f g x = some (D, N) → n ∈ segL x N →
      Covered f (oS.toList.take oS.toList.length) x D := by
    intro n hn x D N hs hnL s hsm hr
    obtain ⟨d⟩ := segOK_spec hs
    obtain ⟨hnb, gv, hgv, -⟩ := K.memT.1 hn
    rw [List.take_length]
    exact K.memS.2 (K.segRoots_node hs (d := d) (K.segBlock hs d hnL hnb hgv) hsm hr)
  obtain ⟨T', h1, hT'⟩ := loop (env := env) (S := G) (pre := oS.toList.take oS.toList.length)
    (K' := oT.toList.length) fun j x hj hjx T hT => by
      have hxT := K.memT.1 (List.mem_of_getElem? hjx)
      refine K.step hE hS hT hjx (fun hr => ?_) (fun fv hfv hn => ?_) (K.inv _ G (List.prefix_refl _) h)
      · cases hfx : f.value? x with
        | some fv =>
          cases hsx : segOK tabs f g x with
          | none =>
            exact .inl ⟨by rw [List.take_length]; exact K.memS.2 (K.nodeF hxT hfx).1,
              fun D N h => by rw [hsx] at h; cases h⟩
          | some p =>
            exact .inr ⟨x, p.1, p.2, hsx, by simp [segL],
              hcovAll x (List.mem_of_getElem? hjx) x p.1 p.2 hsx (by simp [segL])⟩
        | none =>
          obtain ⟨_, gv, hgv, _⟩ := hxT
          obtain ⟨x', D, N, hs, hxN⟩ := K.rel.fresh x gv hfx hgv
          exact .inr ⟨x', D, N, hs, by simp [segL, hxN],
            hcovAll x (List.mem_of_getElem? hjx) x' D N hs (by simp [segL, hxN])⟩
      · exact absurd (by rw [List.take_length]; exact K.memS.2 (K.nodeF hxT hfv).1) hn
  have hfr := K.tframe hS hT'
  simp only [List.take_length] at h1 hT' hS
  refine ⟨T', h1, hfr, by rw [hT'.size, K.sizeT], fun a v yS hv hg hyS => ?_⟩
  have hnd : ∀ x', ¬ Drop tabs f g x' a := fun x' hd => by
    rw [K.rel.dropNone x' a hd] at hg; cases hg
  by_cases haS : a ∈ oS.toList
  · have haT : a ∈ oT.toList := K.memT.2 (K.nodeG (K.memS.1 haS) hnd)
    obtain ⟨yS', yT, h1', h2', h3'⟩ := hT'.rel a haT haS
    rw [hyS] at h1'; cases h1'
    exact ⟨yT, h2', h3'⟩
  · have haT : a ∉ oT.toList := fun hm => haS (K.memS.2 (K.nodeF (K.memT.1 hm) hv).1)
    rw [hS.out a haS] at hyS
    obtain ⟨yT, hyT, hr⟩ := K.rr a v yS hv hg hyS
    exact ⟨yT, by rw [hT'.out a haT]; exact hyT, hr⟩

/-- The target's roots before a kept root `r` are covered by the source's before it. -/
theorem rootsBefore {k k' : Nat} {r : ID} (hk : oS.toList[k]? = some r)
    (hk' : oT.toList[k']? = some r) (hfr : CSE.rootNode f r = true)
    (hgr : CSE.rootNode g r = true) (hrs : segOf (segList (segArr tabs f g)) r = none) :
    ∀ y ∈ oT.toList.take k', CSE.rootNode g y = true → Cov tabs f g (oS.toList.take k) y := by
  intro y hy hry
  have hR := K.roots
  rw [CSE.split_at hk, List.filter_append, List.filter_cons_of_pos hfr] at hR
  obtain ⟨P, Q, hPQ, hP⟩ := segRoots_prefix g (segList (segArr tabs f g)) r hrs
    ((oS.toList.drop (k + 1)).filter (CSE.rootNode f)) ((oS.toList.take k).filter (CSE.rootNode f))
  rw [hPQ, CSE.split_at hk', List.filter_append, List.filter_cons_of_pos hgr] at hR
  have hrP : r ∉ P := fun hm => by
    rcases hP r hm with ⟨h1, -⟩ | ⟨x, h1, -⟩
    · exact CSE.not_mem_take_of K.ndS hk (List.mem_filter.1 h1).1
    · obtain ⟨D, N, hs, hrL⟩ := mem_segNew h1
      obtain ⟨d⟩ := segOK_spec hs
      simp only [segL, List.mem_append, List.mem_singleton] at hrL
      rcases hrL with hrL | rfl
      · obtain ⟨-, rv0, hrv, -⟩ := K.memS.1 (List.mem_of_getElem? hk)
        rw [(d.hN r hrL).1] at hrv; cases hrv
      · rw [segOf_anchor hs] at hrs; cases hrs
  have heq := CSE.prefix_eq hR (fun hm => CSE.not_mem_take_of K.ndT hk' (List.mem_filter.1 hm).1) hrP
  have hm : y ∈ (oT.toList.take k').filter (CSE.rootNode g) := List.mem_filter.2 ⟨hy, hry⟩
  rw [heq] at hm
  rcases hP y hm with ⟨h1, h2⟩ | ⟨x, h1, h2⟩
  · refine .inl ⟨(List.mem_filter.1 h1).1, fun D N hs => ?_⟩
    rw [segOf_anchor hs] at h2; cases h2
  · obtain ⟨D, N, hs, hyL⟩ := mem_segNew h1
    obtain ⟨d⟩ := segOK_spec hs
    have hyT : y ∈ oT.toList := List.mem_of_mem_take hy
    obtain ⟨hyb, gv, hgv, -⟩ := K.memT.1 hyT
    have hb := K.segBlock hs d hyL hyb hgv
    refine .inr ⟨x, D, N, hs, hyL, fun s hsm hsr => ?_⟩
    have hsn := K.segRoots_node hs (d := d) hb hsm hsr
    have hsL : s ∈ (oS.toList.take k).filter (CSE.rootNode f) ++
        r :: (oS.toList.drop (k + 1)).filter (CSE.rootNode f) := by
      rw [← List.filter_cons_of_pos hfr, ← List.filter_append, ← CSE.split_at hk]
      exact List.mem_filter.2 ⟨K.memS.2 hsn, hsr⟩
    have hso : segOf (segList (segArr tabs f g)) s = some x := by
      simp only [List.mem_append, List.mem_singleton] at hsm
      rcases hsm with hsm | rfl
      · exact segOf_drop K.rel ⟨D, N, hs, hsm⟩
      · exact segOf_anchor hs
    exact (List.mem_filter.1 (h2 s hsL hso)).1

theorem nodeOf_x {x : ID} {v : Value} (hx : x ∈ fb.values) (hv : f.value? x = some v)
    (hph : v.op ≠ .Phi) : nodeOf (schedNodes f fb).toList x = some ⟨x, v.args, prio v.op⟩ := by
  obtain ⟨v', hv', hid, -⟩ := K.valueIn hx
  rw [hv] at hv'; cases hv'
  have hm : (⟨v.id, v.args, prio v.op⟩ : SNode) ∈ (schedNodes f fb).toList :=
    mem_schedNodes.2 ⟨x, hx, v, hv, hph, rfl⟩
  have := nodeOf_of_mem (schedNodes_ids K.ownF K.ndF) hm
  rw [hid] at this; exact this

/-- **The panic case.** -/
theorem panicCase (hE : env.Mono) {e : Panic} {m : Mem}
    (h : evalAll env (Ctx.make tabs f) F0 oS.toList = .panic e m) :
    ∃ m', evalAll env (Ctx.make tabs g) F0T oT.toList = .panic e m' ∧ Mem.Refines m m' := by
  obtain ⟨ce, hwf⟩ := K.wf
  obtain ⟨pre, r, post, Gp, hsplit, hpre, hrp⟩ := evalAll_panic_split h
  have hk : oS.toList[pre.length]? = some r := by rw [hsplit]; simp
  have htk : oS.toList.take pre.length = pre := by rw [hsplit]; simp
  have hS : SFacts env tabs f F0 Gp (oS.toList.take pre.length) := by
    rw [htk]; exact K.sfacts ⟨r :: post, hsplit⟩ hpre
  have hrS : r ∈ oS.toList := List.mem_of_getElem? hk
  obtain ⟨hrb, rv0, hrv, hrph⟩ := K.memS.1 hrS
  rw [stepV_of (ctx := Ctx.make tabs f) hrv] at hrp
  have hrop : Panicking rv0.op := evalValue_panic_op hrp
  have hp2 : Sem.prio rv0.op ≠ 0 := prio_panicking hrop
  have hfroot : CSE.rootNode f r = true := by simp [CSE.rootNode, hrv, hp2]
  -- the panicking root is no segment's
  have hnoseg : ∀ x D N, segOK tabs f g x = some (D, N) → r ∉ D ++ [x] := fun x D N hs hm =>
    (K.sound x D N hs).1 r hm hfroot rv0 _ e m hrv hrp
  have hrs : segOf (segList (segArr tabs f g)) r = none := by
    cases ho : segOf (segList (segArr tabs f g)) r with
    | none => rfl
    | some x =>
      rcases segOf_some K.rel ho with ⟨rfl, D, N, hs⟩ | ⟨D, N, hs, hrD⟩
      · exact (hnoseg r D N hs (by simp)).elim
      · exact (hnoseg x D N hs (List.mem_append_left _ hrD)).elim
  have hnd : ∀ x', ¬ Drop tabs f g x' r := fun x' hd => by
    rw [segOf_drop K.rel hd] at hrs; cases hrs
  obtain ⟨gr, hgr, hsr⟩ := K.gval hrv hnd
  have hs : ssSame rv0 gr = true := hsr.resolve_right fun ⟨D, N, h⟩ => by
    rw [segOf_anchor h] at hrs; cases hrs
  have hgroot : CSE.rootNode g r = true := by
    simp [CSE.rootNode, hgr, (ssSame_spec hs).2.1, hp2]
  obtain ⟨k', hk'⟩ := List.getElem?_of_mem (K.memT.2 (K.nodeG (K.memS.1 hrS) hnd))
  have hroots := K.rootsBefore hk hk' hfroot hgroot hrs
  obtain ⟨T', h1, hT'⟩ := loop (env := env) (S := Gp) (pre := oS.toList.take pre.length) (K' := k')
    (fun j x hj hjx T hT => by
      have hxmem : x ∈ oT.toList.take k' :=
        List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hj]; exact hjx)
      refine K.step hE hS hT hjx (fun hr => hroots x hxmem hr) (fun fv hfv hn => ?_)
        (K.inv pre Gp ⟨r :: post, hsplit.symm⟩ hpre)
      obtain ⟨hxn, -⟩ := K.nodeF (K.memT.1 (List.mem_of_getElem? hjx)) hfv
      obtain ⟨hxb, fv', hfv', hph⟩ := hxn
      rw [hfv] at hfv'; cases hfv'
      obtain ⟨i, hi⟩ := List.getElem?_of_mem (K.memS.2 ⟨hxb, fv, hfv, hph⟩)
      have hxr : x ≠ r := fun he => by
        subst he; exact absurd (Order.idx_unique K.ndT hjx hk') (by omega)
      have hki : pre.length < i := by
        rcases Nat.lt_or_ge pre.length i with h' | h'
        · exact h'
        · rcases Nat.lt_or_ge i pre.length with h'' | h''
          · exact absurd (List.mem_of_getElem? (by rw [List.getElem?_take_of_lt h'']; exact hi)) hn
          · have : i = pre.length := by omega
            subst this; rw [hk] at hi; cases hi; exact absurd rfl hxr
      have hnA : ∀ op, fv.op = op → (op = .Arg ∨ op = .ArgIntReg) → False := by
        intro op hop hor
        by_cases hfr0 : prio fv.op = 0
        · have hspec := schedule_spec K.hoS
          obtain ⟨a, haD, -⟩ := hspec.pureFirst pre.length i r x hki hk hi
            (fun hpu => by
              have := hpu _ (K.nodeOf_x hrb hrv hrph)
              exact hp2 this)
            (fun n hn => by rw [K.nodeOf_x hxb hfv hph] at hn; cases hn; exact hfr0)
          rw [argsOf_schedNodes K.ownF K.ndF hxb hfv hph] at haD
          have hne : fv.args.size ≠ 0 := fun h0 => by
            rw [Array.eq_empty_of_size_eq_zero h0] at haD; simp at haD
          have har := hwf.arity bid fb x fv ⟨⟨K.tree.1, K.hfb⟩, hxb, hfv⟩
            (by rw [hop, CSE.argLen_zero_of_arg hor]; decide)
          rw [hop, CSE.argLen_zero_of_arg hor] at har
          exact hne (by exact_mod_cast har)
        · rw [hop] at hfr0
          rcases hor with rfl | rfl <;> exact hfr0 (by decide)
      exact ⟨fun h' => hnA _ h' (.inl rfl), fun h' => hnA _ h' (.inr rfl)⟩)
  have hrid : rv0.id = r := by
    obtain ⟨v', hv', hid, -⟩ := K.valueIn hrb
    rw [hrv] at hv'; cases hv'; exact hid
  have hres := K.keptRes hE hS hT' hk' hrv hrid hgr hs (fun a ha => by
      rcases K.arg_base_or_node hrb hrv hrph ha with hB | hn
      · exact .inl hB
      · obtain ⟨i, hi, hia⟩ := K.topoS hk hrv ha hn
        exact .inr (List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hi]; exact hia)))
    (AtomSim.regs_of_panic hrp)
  rw [hrp] at hres
  generalize hT'r : evalValue env (Ctx.make tabs g) T' gr = rT at hres
  cases hres with
  | panic e hm =>
    refine ⟨_, ?_, hm⟩
    rw [CSE.split_at hk', evalAll_append, h1]
    show evalAll env (Ctx.make tabs g) T' (r :: oT.toList.drop (k' + 1)) = _
    rw [evalAll_cons, stepV_of (ctx := Ctx.make tabs g) hgr, hT'r]

end Blk

end GoFV.Proof.Seg

import GoFV.Proof.Pass.ECRel
import GoFV.Proof.AtomSimLoop

/-!
# The target's schedule against a source reference frame (issue #28)

`tgt_loop`: the target evaluates a prefix `L` of its schedule `og` of block `gb` from the frame
`T0` (after its `Phi`s). Against a source frame `G` (of the same activation) that holds the
source's evaluation of every source value of `L`, each value of `L` evaluates: a new one by
`NewEval`, a source value by its obligation `Obl`, to a refinement of its conversion. The
invariant `LInv`: registers outside `L` unchanged, source values of `L` refining their
conversions, new values of `L` (and the initial set `E0`: new values placed in strict
dominators) holding their own evaluations, and every value of `L` holding its evaluation
(`EcTgtHolds`; with lemma (D) on the target, `TgtHyp.hdinvT`, the `HeldT` premise of `Obl`).
-/

namespace GoFV.Proof.EC

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Proof.AtomSim GoFV.Proof.Order

/-- The invariant along the target's schedule prefix `d`. -/
def LInv (env : Env) (tabs : Tables) (g : Func) (cv : Cv) (isNew : ID → Bool) (G T0 : Frame)
    (E0 : ID → Prop) (d : List ID) (T : Frame) : Prop :=
  T = { T0 with regs := T.regs } ∧ T.regs.size = T0.regs.size ∧
    (∀ a, a ∉ d → T.regs[a]? = T0.regs[a]?) ∧
    (∀ x ∈ d, isNew x = false → ∀ y, G.regs[x]? = some (some y) →
      ∃ y', T.regs[x]? = some (some y') ∧ Sem.Refines (cv x y) y') ∧
    NewCons env (Ctx.make tabs g) isNew T (fun z => (z ∈ d ∧ isNew z = true) ∨ E0 z) ∧
    (∀ x ∈ d, Reg T x) ∧ (∀ z ∈ d, EcTgtHolds env tabs g T z)

theorem ecl_dep_left {N : ID → Prop} {D : ID → List ID} {x y : ID} : Dep N D x y → N x
  | .arg hx _ _ => hx
  | .trans h _ => ecl_dep_left h

/-- A value keeps holding its evaluation when a register other than its own and its
arguments' is set. -/
theorem ecl_holds_set {env : Env} {tabs : Tables} {g : Func} {T : Frame} {z x : ID} {y : Val}
    (h : EcTgtHolds env tabs g T z) (hzx : x ≠ z) (hargs : ∀ w, g.value? z = some w → x ∉ w.args) :
    EcTgtHolds env tabs g (T.set x y) z := by
  intro w hw
  obtain ⟨hid, yz, hreg, hev⟩ := h w hw
  refine ⟨hid, yz, by rw [Frame.set_regs_ne hzx]; exact hreg, ?_⟩
  rw [← hev]
  exact evalValue_congr (fr := T.set x y) (g := T) rfl fun a ha =>
    Frame.set_regs_ne (fun he => hargs w hw (by rw [he]; exact ha))

/-- The value just set to its evaluation holds it. -/
theorem ecl_holds_self {env : Env} {tabs : Tables} {g : Func} {T : Frame} {x : ID} {w : Value}
    {y : Val} (hw : g.value? x = some w) (hid : w.id = x) (hxw : x ∉ w.args)
    (hlt : x < T.regs.size) (hev : evalValue env (Ctx.make tabs g) T w = .ok y) :
    EcTgtHolds env tabs g (T.set x y) x := by
  intro w' hw'
  rw [hw] at hw'; cases hw'
  refine ⟨hid, y, Frame.set_regs_self hlt, ?_⟩
  rw [← hev]
  exact evalValue_congr (fr := T.set x y) (g := T) rfl fun a ha =>
    Frame.set_regs_ne (fun he => hxw (by rw [he]; exact ha))

theorem reg_set {T : Frame} {x a : ID} {y : Val} (h : Reg T a) : Reg (T.set x y) a := by
  by_cases hxa : x = a
  · subst hxa
    obtain ⟨y0, hy0⟩ := h
    have hlt : x < T.regs.size := (Array.getElem?_eq_some_iff.1 hy0).1
    exact ⟨y, Frame.set_regs_self hlt⟩
  · rw [Reg, Frame.set_regs_ne hxa]; exact h

/-- A new-value set keeps holding its evaluations when a value outside it and outside its
members' arguments is set. -/
theorem NewCons.set {env : Env} {ctx : Ctx} {isNew : ID → Bool} {T : Frame} {E : ID → Prop}
    (h : NewCons env ctx isNew T E) {x : ID} {y : Val} (hx : ¬ E x)
    (hargs : ∀ z, E z → ∀ w, ctx.f.value? z = some w → x ∉ w.args) :
    NewCons env ctx isNew (T.set x y) E := by
  intro z hz
  obtain ⟨hn, w, yz, hw, hcl, hreg, hev⟩ := h z hz
  have hzx : x ≠ z := fun he => hx (he ▸ hz)
  refine ⟨hn, w, yz, hw, hcl, by rw [Frame.set_regs_ne hzx]; exact hreg, ?_⟩
  rw [← hev]
  refine evalValue_congr (fr := T.set x y) (g := T) rfl fun a ha => ?_
  have hxa : x ≠ a := fun he => hargs z hz w hw (by rw [he]; exact ha)
  exact Frame.set_regs_ne hxa

theorem NewCons.mono {env : Env} {ctx : Ctx} {isNew : ID → Bool} {T : Frame} {E E' : ID → Prop}
    (h : NewCons env ctx isNew T E) (hE : ∀ z, E' z → E z)
    (hcl : ∀ z, E' z → ∀ w, ctx.f.value? z = some w → ∀ a ∈ w.args, isNew a = true → E' a) :
    NewCons env ctx isNew T E' := by
  intro z hz
  obtain ⟨hn, w, yz, hw, -, hreg, hev⟩ := h z (hE z hz)
  exact ⟨hn, w, yz, hw, hcl z hz w hw, hreg, hev⟩

/-- The value at position `|d|` of `d ++ x :: s`. -/
theorem getElem?_mid {d s : List ID} {x : ID} : (d ++ x :: s)[d.length]? = some x := by simp

/-- A schedule element at a position before `|d|` is in `d`. -/
theorem mem_of_idx_lt {d s : List ID} {x a : ID} {i : Nat} (h : (d ++ x :: s)[i]? = some a)
    (hi : i < d.length) : a ∈ d := by
  rw [List.getElem?_append_left hi] at h
  exact List.mem_of_getElem? h

/-- A value that precedes `x` in the schedule `d ++ x :: s` (without repetitions) is in `d`. -/
theorem ecl_before {g : Func} {gb : Block} {og : Array ID} (hsg : schedule g gb = some og)
    (hnd : og.toList.Nodup) {d s : List ID} {x z : ID} (hog' : og.toList = d ++ x :: s)
    (h : SchedBefore g gb z x) : z ∈ d := by
  obtain ⟨A, B, hAB, hxB⟩ := h og hsg
  obtain ⟨B1, B2, rfl⟩ := List.append_of_mem hxB
  have h1 : og.toList[A.length + 1 + B1.length]? = some x := by
    rw [hAB, show A.length + 1 + B1.length = A.length + (B1.length + 1) by omega,
      List.getElem?_append_right (by omega)]
    simp
  have h2 : og.toList[d.length]? = some x := by rw [hog']; exact getElem?_mid
  have heq := idx_unique hnd h1 h2
  have h3 : (d ++ x :: s)[A.length]? = some z := by rw [← hog', hAB]; simp
  exact mem_of_idx_lt h3 (by omega)

/-- In a list without duplicates, what follows an element is determined. -/
theorem ecl_suffix_eq {z : ID} : ∀ {A A' X Y : List ID}, (A ++ z :: X).Nodup →
    A ++ z :: X = A' ++ z :: Y → X = Y
  | [], [], _, _, _, h => by simpa using h
  | [], a :: A', X, Y, hn, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact absurd (List.mem_append_right _ List.mem_cons_self) (List.nodup_cons.1 hn).1
  | a :: A, [], X, Y, hn, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact absurd (List.mem_append_right _ List.mem_cons_self) (List.nodup_cons.1 hn).1
  | a :: A, a' :: A', X, Y, hn, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    exact ecl_suffix_eq (List.nodup_cons.1 hn).2 h.2

/-- If no node with `np` precedes `c` in `P ++ c :: Q = B ++ r :: R` and `r` has `np`, then `c`
is in `B` or is `r`. -/
theorem ecl_gap {np : ID → Bool} {c r : ID} {Q R : List ID} (hr : np r = true) :
    ∀ {P B : List ID}, P ++ c :: Q = B ++ r :: R → (∀ y ∈ P, np y = false) → c ∈ B ∨ c = r
  | [], [], h, _ => by simp only [List.nil_append, List.cons.injEq] at h; exact .inr h.1
  | [], b :: B, h, _ => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact .inl (h.1 ▸ List.mem_cons_self)
  | p :: P, [], h, hP => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    have hp := hP p List.mem_cons_self
    rw [h.1, hr] at hp; cases hp
  | p :: P, b :: B, h, hP => by
    simp only [List.cons_append, List.cons.injEq] at h
    rcases ecl_gap hr h.2 (fun y hy => hP y (List.mem_cons_of_mem _ hy)) with h' | h'
    · exact .inl (List.mem_cons_of_mem _ h')
    · exact .inr h'

section
variable {tabs : Tables} {f g : Func} {cv : Cv} {isNew : ID → Bool} {front : ID → List ID}
  {RR : List Val → Mem → List Val → Mem → Prop} {fb gb : Block}

/-- The facts about block `gb` of the target, its schedule `og`, the frame `T0` after its
`Phi`s and the source reference frame `G`, that `tgt_loop` and `tgt_next` use. -/
structure TgtHyp (env : Env) (tabs : Tables) (f g : Func) (cv : Cv) (isNew : ID → Bool)
    (front : ID → List ID) (RR : List Val → Mem → List Val → Mem → Prop) (fb gb : Block)
    (og : Array ID) (G T0 : Frame) (E0 : ID → Prop) : Prop where
  B : CvBlock tabs f g cv isNew front RR fb gb
  hsg : schedule g gb = some og
  hnd : og.toList.Nodup
  htopo : TopoRem (argsF g) og.toList
  hmem : ∀ x, x ∈ og.toList ↔ x ∈ gb.values ∧ ∃ w, g.value? x = some w ∧ w.op ≠ .Phi
  hid : ∀ x ∈ gb.values, ∀ w, g.value? x = some w → w.id = x
  hT0 : T0 = { G with regs := T0.regs }
  hsz : T0.regs.size = g.valueTab.size
  himg : T0.images.size = (Ctx.make tabs g).params.size
  hE0 : NewCons env (Ctx.make tabs g) isNew T0 E0
  hE0og : ∀ z, E0 z → z ∉ og.toList
  hE0args : ∀ z, E0 z → ∀ w, g.value? z = some w → ∀ a ∈ w.args, a ∉ og.toList
  hnewArgs : ∀ x ∈ og.toList, ∀ w, g.value? x = some w → ∀ a ∈ w.args, isNew a = true →
    a ∉ og.toList → E0 a
  hout : ∀ x ∈ og.toList, ∀ w, g.value? x = some w → ∀ a ∈ w.args, a ∉ og.toList → Reg T0 a
  hrel0 : ∀ a, a ∉ og.toList → isNew a = false → ∀ y, G.regs[a]? = some (some y) →
    ∃ y', T0.regs[a]? = some (some y') ∧ Sem.Refines (cv a y) y'
  hGok : RegsOK (Ctx.make tabs f) G
  htree : ((make f).depthOf fb.id).isSome
  hdinv : DInv env (Ctx.make tabs f) (fun a => Anc (make f) a fb.id ∧ a ≠ fb.id) G
  hidF : ∀ z u, Placed f z u → u.id = z
  hfbP : ∀ z ∈ fb.values, ∀ u, f.value? z = some u → Placed f z u
  hdinvT : ∀ T : Frame, T = { T0 with regs := T.regs } →
    (∀ z, z ∉ gb.values → T.regs[z]? = T0.regs[z]?) →
    DInv env (Ctx.make tabs g) (fun a => Anc (make g) a gb.id ∧ a ≠ gb.id) T
  hidG : ∀ z w, Placed g z w → w.id = z
  hslots : ∀ (a : ID) (m : Mem), G.regs[a]? = some (some (Val.mem m)) → EcQ tabs f m

/-- A source value that reaches the schedule element `x` (or is a `Phi`, or is outside the
block) has a target register refining the source's when `x` is evaluated. -/
theorem ecl_front {env : Env} {og : Array ID} {G T0 : Frame} {E0 : ID → Prop}
    (TH : TgtHyp env tabs f g cv isNew front RR fb gb og G T0 E0) {d s : List ID} {x : ID}
    (hog' : og.toList = d ++ x :: s) {T : Frame}
    (hI : LInv env tabs g cv isNew G T0 E0 d T) {a : ID} (han : isNew a = false)
    (hdep : a ∈ gb.values → (∃ w, g.value? a = some w ∧ w.op = .Phi) ∨
      Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList) a x ∨
      SchedBefore g gb a x) :
    ∀ ya, G.regs[a]? = some (some ya) →
      ∃ y', T.regs[a]? = some (some y') ∧ Sem.Refines (cv a ya) y' := by
  obtain ⟨-, -, hTk, hTr, -, -, -⟩ := hI
  have hspec := (schedule_spec TH.hsg).topo
  have hdog : ∀ a ∈ d, a ∈ og.toList := fun a ha => by rw [hog']; exact List.mem_append_left _ ha
  intro ya hya
  by_cases hm : a ∈ og.toList
  · obtain ⟨hagb, -, -⟩ := (TH.hmem a).1 hm
    rcases hdep hagb with ⟨wa, hwa, hph⟩ | hd | hb
    · obtain ⟨-, wa', hwa', hph'⟩ := (TH.hmem a).1 hm
      rw [hwa] at hwa'; cases hwa'; exact absurd hph hph'
    · obtain ⟨i, hi⟩ := List.getElem?_of_mem hm
      have hj : og.toList[d.length]? = some x := by rw [hog']; exact getElem?_mid
      have hlt := hspec.dep_lt hd hi hj
      rw [hog'] at hi
      exact hTr a (mem_of_idx_lt hi hlt) han ya hya
    · exact hTr a (ecl_before TH.hsg TH.hnd hog' hb) han ya hya
  · rw [hTk a fun hd => hm (hdog a hd)]; exact TH.hrel0 a hm han ya hya

/-- The values `HeldT` at schedule element `x` hold their evaluations in the target. -/
theorem ecl_heldT {env : Env} {og : Array ID} {G T0 : Frame} {E0 : ID → Prop}
    (TH : TgtHyp env tabs f g cv isNew front RR fb gb og G T0 E0) {d s : List ID} {x : ID}
    (hog' : og.toList = d ++ x :: s) {T : Frame}
    (hI : LInv env tabs g cv isNew G T0 E0 d T) :
    ∀ z, HeldT g gb x z → EcTgtHolds env tabs g T z := by
  obtain ⟨hTf, -, hTk, -, -, -, hTH⟩ := hI
  have hspec := (schedule_spec TH.hsg).topo
  have hdog : ∀ a ∈ d, a ∈ og.toList := fun a ha => by rw [hog']; exact List.mem_append_left _ ha
  intro z hz w' hw'
  rcases hz with hd | ⟨v, hP, hph, hanc, hne⟩
  · obtain ⟨i, hi⟩ := List.getElem?_of_mem ((hspec.mem z).2 (ecl_dep_left hd))
    have hj : og.toList[d.length]? = some x := by rw [hog']; exact getElem?_mid
    have hlt := hspec.dep_lt hd hi hj
    rw [hog'] at hi
    exact hTH z (mem_of_idx_lt hi hlt) w' hw'
  · rw [hP.1] at hw'; cases hw'
    have hD := TH.hdinvT T hTf fun a ha =>
      hTk a fun hd => ha ((TH.hmem a).1 (hdog a hd)).1
    obtain ⟨y, hy, hev⟩ := hD z w' hP ⟨hanc, hne⟩
    exact ⟨TH.hidG z w' hP, y, hy, hev hph⟩

/-- **A source value of the schedule** evaluated by the target after the prefix `d`: a
refinement of its conversion (or the same panic), by its obligation. -/
theorem tgt_next {env : Env} (hE : env.Mono) {og : Array ID} {G T0 : Frame} {E0 : ID → Prop}
    (TH : TgtHyp env tabs f g cv isNew front RR fb gb og G T0 E0) {d s : List ID} {x : ID}
    (hog' : og.toList = d ++ x :: s) {T : Frame}
    (hI : LInv env tabs g cv isNew G T0 E0 d T) (hn : isNew x = false) {u : Value}
    (hu : f.value? x = some u) (hGa : ∀ a ∈ u.args, Reg G a)
    (hsrcd : ∀ z ∈ d, isNew z = false → ¬ TgtInvalid g z → ∃ u y, f.value? z = some u ∧
      G.regs[z]? = some (some y) ∧ evalValue env (Ctx.make tabs f) G u = .ok y)
    (hsrcA : ∀ z, SrcArg f fb x z → ∃ u y, f.value? z = some u ∧
      G.regs[z]? = some (some y) ∧ evalValue env (Ctx.make tabs f) G u = .ok y) :
    ResCv (cv x) (evalValue env (Ctx.make tabs f) G u) (stepV env (Ctx.make tabs g) T x) := by
  obtain ⟨hTf, hTs, hTk, hTr, hTN, hTreg, hTH⟩ := hI
  have hspec := (schedule_spec TH.hsg).topo
  have hxog : x ∈ og.toList := by rw [hog']; simp
  have hdog : ∀ a ∈ d, a ∈ og.toList := fun a ha => by rw [hog']; exact List.mem_append_left _ ha
  have hxd : x ∉ d := fun hm => by
    have := TH.hnd; rw [hog'] at this
    exact (List.nodup_append.1 this).2.2 x hm x List.mem_cons_self rfl
  obtain ⟨hxgb, w, hw, hwphi⟩ := (TH.hmem x).1 hxog
  have htopo' := TH.htopo; rw [hog'] at htopo'
  have hargIn : ∀ a ∈ w.args, a ∈ og.toList → a ∈ d := fun a ha hm => by
    rw [hog'] at hm
    exact topoRem_before htopo' (by rw [argsF_of hw]; exact Array.mem_toList_iff.2 ha) hm
  have hreg : ∀ a ∈ w.args, Reg T a := fun a ha => by
    by_cases hm : a ∈ og.toList
    · exact hTreg a (hargIn a ha hm)
    · rw [Reg, hTk a fun hd => hm (hdog a hd)]; exact TH.hout x hxog w hw a ha hm
  have hstepV : stepV env (Ctx.make tabs g) T x = evalValue env (Ctx.make tabs g) T w := by
    unfold stepV; rw [show (Ctx.make tabs g).f = g from rfl, hw]
  have hxfb : x ∈ fb.values := Classical.byContradiction fun h => by
    rw [TH.B.fresh x hxgb h] at hn; cases hn
  have huphi : u.op ≠ .Phi := fun hph => by
    obtain ⟨⟨w', hgu, hsame⟩, -⟩ := TH.B.phiS x hxfb u hu hph
    rw [hw] at hgu; cases hgu; exact hwphi (hsame.1.trans hph)
  have hfront : ∀ a ∈ front x, ∀ ya, G.regs[a]? = some (some ya) →
      ∃ y', T.regs[a]? = some (some y') ∧ Sem.Refines (cv a ya) y' := by
    intro a ha
    obtain ⟨han, hdep⟩ := TH.B.front x hxfb u hu huphi a ha
    exact ecl_front TH hog' ⟨hTf, hTs, hTk, hTr, hTN, hTreg, hTH⟩ han hdep
  have hT_G : T = { G with regs := T.regs } := by rw [hTf]; rw [TH.hT0]
  have hdepd : ∀ z, Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList) z x →
      z ∈ d := fun z hd => by
    obtain ⟨i, hi⟩ := List.getElem?_of_mem ((hspec.mem z).2 (ecl_dep_left hd))
    have hj : og.toList[d.length]? = some x := by rw [hog']; exact getElem?_mid
    have hlt := hspec.dep_lt hd hi hj
    rw [hog'] at hi
    exact mem_of_idx_lt hi hlt
  have hheldS : ∀ z, Held f g fb gb x z → EcSrcHolds env tabs f G z := by
    intro z hz u' hu'
    unfold Held at hz
    rcases hz with ⟨hzf, hd⟩ | ⟨v, hP, hph, hanc, hne⟩ | ⟨hzf, hzi, hb⟩ | hza
    · have hzid := TH.hidF z u' (TH.hfbP z hzf u' hu')
      obtain ⟨b, hNb, hzb⟩ := hd.left_arg
      obtain ⟨u2, y, hu2, hy, hev⟩ := hsrcd z (hdepd z hd) (TH.B.common z hzf).2
        (TH.B.invArgs z b hNb hzb)
      rw [hu'] at hu2; cases hu2
      exact ⟨hzid, y, hy, hev⟩
    · rw [hP.1] at hu'; cases hu'
      obtain ⟨y, hy, hev⟩ := TH.hdinv z u' hP ⟨hanc, hne⟩
      exact ⟨TH.hidF z u' hP, y, hy, hev hph⟩
    · have hzid := TH.hidF z u' (TH.hfbP z hzf u' hu')
      obtain ⟨u2, y, hu2, hy, hev⟩ := hsrcd z (ecl_before TH.hsg TH.hnd hog' hb) (TH.B.common z hzf).2 hzi
      rw [hu'] at hu2; cases hu2
      exact ⟨hzid, y, hy, hev⟩
    · have hzid := TH.hidF z u' (TH.hfbP z hza.1 u' hu')
      obtain ⟨u2, y, hu2, hy, hev⟩ := hsrcA z hza
      rw [hu'] at hu2; cases hu2
      exact ⟨hzid, y, hy, hev⟩
  have hheldT : ∀ z, HeldT g gb x z → EcTgtHolds env tabs g T z := by
    intro z hz w' hw'
    rcases hz with hd | ⟨v, hP, hph, hanc, hne⟩
    · exact hTH z (hdepd z hd) w' hw'
    · rw [hP.1] at hw'; cases hw'
      have hD := TH.hdinvT T hTf fun a ha =>
        hTk a fun hd => ha ((TH.hmem a).1 (hdog a hd)).1
      obtain ⟨y, hy, hev⟩ := hD z w' hP ⟨hanc, hne⟩
      exact ⟨TH.hidG z w' hP, y, hy, hev hph⟩
  rw [hstepV]
  exact TH.B.obl TH.htree x hxfb u hu huphi u w hu hw env hE G T hT_G TH.hGok _ hTN
    (fun a ha han => by
      by_cases hm : a ∈ og.toList
      · exact .inl ⟨hargIn a ha hm, han⟩
      · exact .inr (TH.hnewArgs x hxog w hw a ha han hm))
    hreg hGa hfront hheldS hheldT

/-- **The target's schedule prefix `L`.** -/
theorem tgt_loop {env : Env} (hE : env.Mono) {og : Array ID} {G T0 : Frame} {E0 : ID → Prop}
    (TH : TgtHyp env tabs f g cv isNew front RR fb gb og G T0 E0)
    {L M : List ID} (hog : og.toList = L ++ M)
    (hsrc : ∀ x ∈ L, isNew x = false → ¬ TgtInvalid g x → ∃ u y, f.value? x = some u ∧
      G.regs[x]? = some (some y) ∧ evalValue env (Ctx.make tabs f) G u = .ok y)
    (hsrcA : ∀ x ∈ L, isNew x = false → ¬ TgtInvalid g x → ∀ z, SrcArg f fb x z → ∃ u y,
      f.value? z = some u ∧ G.regs[z]? = some (some y) ∧ evalValue env (Ctx.make tabs f) G u = .ok y)
    (hreach : ∀ c z, c ∈ fb.values → ¬ TgtInvalid g c → z ∈ L → ∀ A P Q,
      og.toList = A ++ z :: (P ++ c :: Q) → (∀ y ∈ P, npIn (schedNodes f fb).toList y = false) →
      Reached env tabs f G c ∧ ∀ z, SrcArg f fb c z → ∃ u y, f.value? z = some u ∧
        G.regs[z]? = some (some y) ∧ evalValue env (Ctx.make tabs f) G u = .ok y)
    (hret : ∀ z ∈ L, RetAnchored tabs f g cv isNew fb gb z → ∀ c, fb.controls[0]? = some c →
      EcSrcHolds env tabs f G c ∧ ∀ y, G.regs[c]? = some (some y) → ∃ rs m, retOf y = some (rs, m)) :
    ∃ T, evalAll env (Ctx.make tabs g) T0 L = .ok T ∧ LInv env tabs g cv isNew G T0 E0 L T := by
  have TH0 := TH
  obtain ⟨B, hsg, hnd, htopo, hmem, hid, hT0, hsz, himg, hE0, hE0og, hE0args, hnewArgs, hout,
    hrel0, hGok, htree, hdinv, hidF, hfbP, hdinvT, hidG, hslots⟩ := TH
  refine evalAll_induct L (LInv env tabs g cv isNew G T0 E0) ?_ L [] T0 rfl
    ⟨by cases T0; rfl, rfl, fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil,
      hE0.mono (fun z hz => hz.resolve_left fun h => absurd h.1 List.not_mem_nil)
        fun z hz w hw a ha han => by
          obtain ⟨-, w', -, hw', hcl, -⟩ := hE0 z (hz.resolve_left fun h => absurd h.1 List.not_mem_nil)
          rw [hw] at hw'; cases hw'; exact .inr (hcl a ha han),
      fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
  intro d x s T hL hI
  obtain ⟨hTf, hTs, hTk, hTr, hTN, hTreg, hTH⟩ := hI
  have hog' : og.toList = d ++ x :: (s ++ M) := by rw [hog, hL]; simp
  have hxog : x ∈ og.toList := by rw [hog']; simp
  have hxL : x ∈ L := by rw [hL]; simp
  have hdog : ∀ a ∈ d, a ∈ og.toList := fun a ha => by rw [hog']; exact List.mem_append_left _ ha
  have hxd : x ∉ d := fun hm => by
    have := hnd; rw [hog'] at this
    exact (List.nodup_append.1 this).2.2 x hm x List.mem_cons_self rfl
  obtain ⟨hxgb, w, hw, hwphi⟩ := (hmem x).1 hxog
  have hwid : w.id = x := hid x hxgb w hw
  have hxlt : x < T.regs.size := by rw [hTs, hsz]; exact lt_of_value? hw
  have htopo' := htopo; rw [hog'] at htopo'
  have hargIn : ∀ a ∈ w.args, a ∈ og.toList → a ∈ d := fun a ha hm => by
    rw [hog'] at hm
    exact topoRem_before htopo' (by rw [argsF_of hw]; exact Array.mem_toList_iff.2 ha) hm
  have hreg : ∀ a ∈ w.args, Reg T a := fun a ha => by
    by_cases hm : a ∈ og.toList
    · exact hTreg a (hargIn a ha hm)
    · rw [Reg, hTk a fun hd => hm (hdog a hd)]; exact hout x hxog w hw a ha hm
  have hxw : x ∉ w.args := fun ha => hxd (hargIn x ha hxog)
  have hstepV : stepV env (Ctx.make tabs g) T x = evalValue env (Ctx.make tabs g) T w := by
    unfold stepV; rw [show (Ctx.make tabs g).f = g from rfl, hw]
  have hEx : ∀ a ∈ w.args, isNew a = true → (a ∈ d ++ [x] ∧ isNew a = true) ∨ E0 a :=
    fun a ha hn => by
      by_cases hm : a ∈ og.toList
      · exact .inl ⟨List.mem_append_left _ (hargIn a ha hm), hn⟩
      · exact .inr (hnewArgs x hxog w hw a ha hn hm)
  have hnotargD : ∀ z ∈ d, ∀ wz, g.value? z = some wz → x ∉ wz.args := by
    intro z hzd wz hwz hx
    obtain ⟨d1, d2, rfl⟩ := List.append_of_mem hzd
    have ht : TopoRem (argsF g) (d1 ++ z :: (d2 ++ x :: (s ++ M))) := by
      rw [hog'] at htopo; simpa using htopo
    exact topoRem_mid ht x (by rw [argsF_of hwz]; exact Array.mem_toList_iff.2 hx)
      (List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self))
  have hnotarg : ∀ z, ((z ∈ d ∧ isNew z = true) ∨ E0 z) → ∀ wz,
      (Ctx.make tabs g).f.value? z = some wz → x ∉ wz.args := by
    intro z hz wz hwz hx
    change g.value? z = some wz at hwz
    rcases hz with ⟨hzd, -⟩ | hz0
    · exact hnotargD z hzd wz hwz hx
    · exact hE0args z hz0 wz hwz x hx hxog
  have holdsSet : ∀ y, evalValue env (Ctx.make tabs g) T w = .ok y →
      ∀ z ∈ d ++ [x], EcTgtHolds env tabs g (T.set x y) z := by
    intro y hev z hz
    rcases List.mem_append.1 hz with hz | hz
    · exact ecl_holds_set (hTH z hz) (fun he => hxd (he ▸ hz)) (hnotargD z hz)
    · rw [List.mem_singleton.1 hz]; exact ecl_holds_self hw hwid hxw hxlt hev
  have hnotE : ¬ ((x ∈ d ∧ isNew x = true) ∨ E0 x) := fun h =>
    h.elim (fun h => hxd h.1) fun h => hE0og x h hxog
  have common : ∀ y, (T.set x y = { T0 with regs := (T.set x y).regs }) ∧
      (T.set x y).regs.size = T0.regs.size ∧
      (∀ a, a ∉ d ++ [x] → (T.set x y).regs[a]? = T0.regs[a]?) ∧
      (∀ a ∈ d ++ [x], Reg (T.set x y) a) ∧
      (∀ a ∈ d, isNew a = false → ∀ ya, G.regs[a]? = some (some ya) →
        ∃ y', (T.set x y).regs[a]? = some (some y') ∧ Sem.Refines (cv a ya) y') := by
    intro y
    refine ⟨by rw [hTf]; rfl, by simp [Frame.set, hTs], fun a ha => ?_, fun a ha => ?_,
      fun a ha hn ya hya => ?_⟩
    · have hxa : x ≠ a := fun he => ha (by simp [he])
      rw [Frame.set_regs_ne hxa]; exact hTk a fun hm => ha (List.mem_append_left _ hm)
    · rcases List.mem_append.1 ha with ha | ha
      · exact reg_set (hTreg a ha)
      · rw [List.mem_singleton.1 ha]; exact ⟨y, Frame.set_regs_self hxlt⟩
    · have hxa : x ≠ a := fun he => hxd (he ▸ ha)
      rw [Frame.set_regs_ne hxa]; exact hTr a ha hn ya hya
  have himgT : T.images.size = (Ctx.make tabs g).params.size := by rw [hTf]; exact himg
  -- the new-value set after setting `x` (a source value)
  have newSet : ∀ y, isNew x = false → NewCons env (Ctx.make tabs g) isNew (T.set x y)
      (fun z => (z ∈ d ++ [x] ∧ isNew z = true) ∨ E0 z) := by
    intro y hn
    refine (hTN.set (y := y) hnotE hnotarg).mono (fun z hz => ?_) fun z hz wz hwz a ha han => ?_
    · rcases hz with ⟨hzd, hzn⟩ | hz0
      · rcases List.mem_append.1 hzd with h | h
        · exact .inl ⟨h, hzn⟩
        · rw [List.mem_singleton.1 h, hn] at hzn; cases hzn
      · exact .inr hz0
    · have hz' : (z ∈ d ∧ isNew z = true) ∨ E0 z := by
        rcases hz with ⟨hzd, hzn⟩ | hz0
        · rcases List.mem_append.1 hzd with h | h
          · exact .inl ⟨h, hzn⟩
          · rw [List.mem_singleton.1 h, hn] at hzn; cases hzn
        · exact .inr hz0
      obtain ⟨-, wz', -, hwz', hcl, -⟩ := hTN z hz'
      rw [hwz] at hwz'; cases hwz'
      rcases hcl a ha han with ⟨had, hn'⟩ | h0
      · exact .inl ⟨List.mem_append_left _ had, hn'⟩
      · exact .inr h0
  cases hn : isNew x with
  | true =>
    obtain ⟨y0, hev⟩ : ∃ y0, evalValue env (Ctx.make tabs g) T w = .ok y0 := by
      rcases (B.newOK x hxgb hn w hw).2 with hne | ⟨c, hc, hci, fr, hob, hfr, hgap⟩ |
          hra
      · obtain ⟨r, hr⟩ := hne env T (w.args.toList.map (rv T)) himgT
        have hty : (Ctx.make tabs g).tys[w.id]?.getD .other = tabs.ty w.type := by
          rw [hwid, tys_of_value hw]; rfl
        exact ⟨_, by rw [evalValue_of_regs hreg, hty, hr]; rfl⟩
      · have hI : LInv env tabs g cv isNew G T0 E0 d T := ⟨hTf, hTs, hTk, hTr, hTN, hTreg, hTH⟩
        obtain ⟨P, Q, hB, hP⟩ := hgap og hsg d (s ++ M) hog'
        obtain ⟨hRc, hRa⟩ := hreach c x hc hci hxL d P Q (by rw [hog', hB]) hP
        refine hob w hw env G T (by rw [hTf, hT0]) _ hTN (fun a ha han => ?_) hreg
          (fun a ha => ecl_front TH0 hog' hI (hfr a ha).1 fun hag => ((hfr a ha).2 hag).imp_right Or.inl)
          (ecl_heldT TH0 hog' hI) (fun a ha u' hu' => ?_) hRc hslots
        · rcases hEx a ha han with ⟨hm, hn'⟩ | h0
          · rcases List.mem_append.1 hm with h | h
            · exact .inl ⟨h, hn'⟩
            · exact absurd (by rw [← List.mem_singleton.1 h]; exact ha) hxw
          · exact .inr h0
        · rcases ha with ⟨haf, hai, hb⟩ | hsa
          · have had := ecl_before hsg hnd hog' hb
            obtain ⟨u2, y, hu2, hy, hev⟩ := hsrc a (by rw [hL]; exact List.mem_append_left _ had)
              (B.common a haf).2 hai
            rw [hu'] at hu2; cases hu2
            exact ⟨hidF a u' (hfbP a haf u' hu'), y, hy, hev⟩
          · obtain ⟨u2, y, hu2, hy, hev⟩ := hRa a hsa
            rw [hu'] at hu2; cases hu2
            exact ⟨hidF a u' (hfbP a hsa.1 u' hu'), y, hy, hev⟩
      · have hI : LInv env tabs g cv isNew G T0 E0 d T := ⟨hTf, hTs, hTk, hTr, hTN, hTreg, hTH⟩
        obtain ⟨hk, c, hc0, -, -, fr, hob, hfr, -⟩ := id hra
        obtain ⟨hSc, hRc⟩ := hret x hxL hra c hc0
        refine hob w hw env G T (by rw [hTf, hT0]) _ hTN (fun a ha han => ?_) hreg
          (fun a ha => ecl_front TH0 hog' hI (hfr a ha).1 fun hag => ((hfr a ha).2 hag).imp_right Or.inl)
          (ecl_heldT TH0 hog' hI) hSc hRc hslots
        rcases hEx a ha han with ⟨hm, hn'⟩ | h0
        · rcases List.mem_append.1 hm with h | h
          · exact .inl ⟨h, hn'⟩
          · exact absurd (by rw [← List.mem_singleton.1 h]; exact ha) hxw
        · exact .inr h0
    refine ⟨_, by rw [hstepV, hev], ?_⟩
    obtain ⟨c1, c2, c3, c4, c5⟩ := common y0
    refine ⟨c1, c2, c3, fun a ha hna ya hya => ?_, ?_, c4, holdsSet _ hev⟩
    · rcases List.mem_append.1 ha with ha | ha
      · exact c5 a ha hna ya hya
      · rw [List.mem_singleton.1 ha, hn] at hna; cases hna
    · intro z hz
      by_cases hzx : z = x
      · subst hzx
        refine ⟨hn, w, _, hw, hEx, Frame.set_regs_self hxlt, ?_⟩
        rw [← hev]
        exact evalValue_congr (fr := T.set z _) (g := T) rfl fun a ha =>
          Frame.set_regs_ne (fun he => hxw (by rw [he]; exact ha))
      · have hz' : (z ∈ d ∧ isNew z = true) ∨ E0 z := by
          rcases hz with ⟨hzd, hzn⟩ | hz0
          · rcases List.mem_append.1 hzd with h | h
            · exact .inl ⟨h, hzn⟩
            · exact absurd (List.mem_singleton.1 h) hzx
          · exact .inr hz0
        obtain ⟨hzn, wz, yz, hwz, -, hrz, hevz⟩ := hTN.set (y := y0) hnotE
          hnotarg z hz'
        refine ⟨hzn, wz, yz, hwz, fun a ha han => ?_, hrz, hevz⟩
        obtain ⟨-, wz', -, hwz', hcl, -⟩ := hTN z hz'
        rw [hwz] at hwz'; cases hwz'
        rcases hcl a ha han with ⟨had, hn'⟩ | h0
        · exact .inl ⟨List.mem_append_left _ had, hn'⟩
        · exact .inr h0
  | false =>
    have hxfb : x ∈ fb.values := Classical.byContradiction fun h => by
      rw [B.fresh x hxgb h] at hn; cases hn
    by_cases hxi : TgtInvalid g x
    · -- an invalidated value: the target evaluates it, its conversion is `poison`
      obtain ⟨hcv, hne⟩ := B.invalid x hxfb hxi
      obtain ⟨r, hr⟩ := hne w hw env T (w.args.toList.map (rv T)) himgT
      have hty : (Ctx.make tabs g).tys[w.id]?.getD .other = tabs.ty w.type := by
        rw [hwid, tys_of_value hw]; rfl
      have hev : evalValue env (Ctx.make tabs g) T w = .ok (r.retype (tabs.ty w.type)) := by
        rw [evalValue_of_regs hreg, hty, hr]; rfl
      refine ⟨_, by rw [hstepV, hev], ?_⟩
      obtain ⟨c1, c2, c3, c4, c5⟩ := common (r.retype (tabs.ty w.type))
      refine ⟨c1, c2, c3, fun a ha hna ya hya => ?_, newSet _ hn, c4, holdsSet _ hev⟩
      rcases List.mem_append.1 ha with ha | ha
      · exact c5 a ha hna ya hya
      · rw [List.mem_singleton.1 ha, hcv]
        exact ⟨_, Frame.set_regs_self hxlt, .poison _⟩
    obtain ⟨u, y, hu, hGy, hevS⟩ := hsrc x hxL hn hxi
    have hob := tgt_next hE ⟨B, hsg, hnd, htopo, hmem, hid, hT0, hsz, himg, hE0, hE0og, hE0args,
      hnewArgs, hout, hrel0, hGok, htree, hdinv, hidF, hfbP, hdinvT, hidG, hslots⟩ hog'
      ⟨hTf, hTs, hTk, hTr, hTN, hTreg, hTH⟩ hn hu (regs_of_ok hevS)
      (fun z hz hn' hzi => hsrc z (by rw [hL]; exact List.mem_append_left _ hz) hn' hzi)
      (hsrcA x hxL hn hxi)
    rw [hevS] at hob
    generalize hT' : stepV env (Ctx.make tabs g) T x = rT at hob
    cases hob with
    | ok hyy =>
      rename_i y'
      refine ⟨y', rfl, ?_⟩
      obtain ⟨c1, c2, c3, c4, c5⟩ := common y'
      refine ⟨c1, c2, c3, fun a ha hna ya hya => ?_, newSet y' hn, c4,
        holdsSet y' (by rw [← hstepV]; exact hT')⟩
      rcases List.mem_append.1 ha with ha | ha
      · exact c5 a ha hna ya hya
      · rw [List.mem_singleton.1 ha] at hya ⊢
        rw [hGy] at hya; cases hya
        exact ⟨y', Frame.set_regs_self hxlt, hyy⟩

end

end GoFV.Proof.EC

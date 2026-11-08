import GoFV.Opt.ShortCircuitBlockCheck
import GoFV.Proof.WFCheck
import GoFV.Proof.DomRel
import GoFV.Proof.Checked
import GoFV.Proof.Avail

variable [GoFV.SSA.Sem.Addrs]

/-!
# Checked `shortcircuitBlock`: the setting and the checker's facts

`Setup ce tabs f g s`: `f` is well formed with uses dominated on paths, and `scOK tabs f g s`
accepted the rewrite `g` of `f` at site `s` (`GoFV/Opt/ShortCircuitBlockCheck.lean`). The lemmas
here turn the checker's Boolean parts into propositions for the simulation
(`ShortCircSim*.lean`) and the preservation of use dominance (`ShortCircUseDom.lean`).

`Delta`: the registers that may differ between a source run and the target run (`b`'s values
and the values not listed in `f`). `FactsRel I f E frS frT`: two frames equal outside `Delta`, and
each fact of `E` (target register `w` holds the source's other phi `v`). `Defd`: the source
registers of the facts hold values.
-/

namespace GoFV.Proof.ShortCirc

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.ShortCircuit GoFV.Proof Dom

/-- The registers that may differ: `b`'s values and the values not listed in `f`. -/
def Delta (I : Info) (f : Func) (x : ID) : Prop := x ∈ I.bvals ∨ ¬ Listed f x

/-- Frames equal outside `Delta`, with the facts `E`. -/
def FactsRel (I : Info) (f : Func) (E : Facts) (frS frT : Frame) : Prop :=
  (∀ x, ¬ Delta I f x → frT.regs[x]? = frS.regs[x]?) ∧
    ∀ v w, I.look E v = some w → frT.regs[w]? = frS.regs[v]?

/-- The source registers of the facts `E` hold values. -/
def Defd (I : Info) (E : Facts) (fr : Frame) : Prop :=
  ∀ v w, I.look E v = some w → ∃ y, fr.regs[v]? = some (some y)

/-- `b`'s other phis hold values in the source frame (it went through `b`). -/
def SrcB (I : Info) (fr : Frame) : Prop := ∀ v ∈ I.vs, ∃ y, fr.regs[v]? = some (some y)

/-- The shape the semantics gives value `x` of `h`. -/
def tyOf (tabs : Tables) (h : Func) (x : ID) : Ty := (Ctx.make tabs h).tys[x]?.getD .other

/-- A checked `shortcircuitBlock` rewrite. -/
structure Setup (ce : CheckEnv) (tabs : Tables) (f g : Func) (s : Site) : Prop where
  wf : WF ce f
  dom : UseDom f
  ok : scOK tabs f g s = true

/-! ## Basic lemmas about the checker's helpers -/

theorem contains_iff {a : Array ID} {x : ID} : a.contains x = true ↔ x ∈ a :=
  Array.contains_iff_mem

theorem contains_false {a : Array ID} {x : ID} : a.contains x = false ↔ x ∉ a := by
  rw [← contains_iff]; simp

theorem mem_nodesOf {h : Func} {B : Block} {x : ID} :
    x ∈ Info.nodesOf h B ↔ x ∈ B.values ∧ isPhiIn h x = false := by
  unfold Info.nodesOf
  rw [Array.mem_filter]; simp

theorem isPhiIn_iff {h : Func} {x : ID} : isPhiIn h x = true ↔ ∃ v, h.value? x = some v ∧ v.op = .Phi := by
  unfold isPhiIn
  cases h.value? x <;> simp

theorem isPhiIn_false {h : Func} {x : ID} {v : Value} (hv : h.value? x = some v) :
    isPhiIn h x = false ↔ v.op ≠ .Phi := by
  unfold isPhiIn; rw [hv]; simp

theorem isPhiIn_true {h : Func} {x : ID} {v : Value} (hv : h.value? x = some v) :
    isPhiIn h x = true ↔ v.op = .Phi := by
  unfold isPhiIn; rw [hv]; simp

theorem getV_of {h : Func} {x : ID} {v : Value} (hv : h.value? x = some v) : h.getV x = v := by
  unfold Func.getV; rw [hv]; rfl

theorem getB_of {h : Func} {x : ID} {B : Block} (hB : h.block? x = some B) : h.getB x = B := by
  unfold Func.getB; rw [hB]; rfl

namespace SCI

variable (I : Info)

theorem look_mem {F : Facts} {v w : ID} (h : I.look F v = some w) : v ∈ I.vs := by
  unfold Info.look at h
  cases hi : I.vs.findIdx? (· == v) with
  | none => rw [hi] at h; cases h
  | some i =>
    obtain ⟨hlt, hx⟩ := Array.findIdx?_eq_some_iff_getElem.1 hi
    have : I.vs[i] = v := by simpa using hx.1
    exact this ▸ Array.getElem_mem hlt

/-- `trans`: the register holding the source's `a` under facts `F`. -/
theorem trans_eq_some {F : Facts} {a w : ID} :
    I.trans F a = some w ↔ (a ∈ I.vs ∧ I.look F a = some w) ∨ (a ∉ I.vs ∧ a ∉ I.bvals ∧ w = a) := by
  unfold Info.trans
  by_cases hv : I.vs.contains a = true
  · simp only [hv, ↓reduceIte]
    have := contains_iff.1 hv
    constructor
    · intro h; exact .inl ⟨this, h⟩
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact h
      · exact absurd this h
  · simp only [hv, ↓reduceIte, Bool.false_eq_true]
    have hv' : a ∉ I.vs := fun h => hv (contains_iff.2 h)
    by_cases hb : I.bvals.contains a = true
    · simp only [hb, ↓reduceIte]
      have := contains_iff.1 hb
      constructor
      · intro h; cases h
      · rintro (⟨h, -⟩ | ⟨-, h, -⟩)
        · exact absurd h hv'
        · exact absurd this h
    · simp only [hb, ↓reduceIte, Bool.false_eq_true]
      have hb' : a ∉ I.bvals := fun h => hb (contains_iff.2 h)
      constructor
      · intro h; cases h; exact .inr ⟨hv', hb', rfl⟩
      · rintro (⟨h, -⟩ | ⟨-, -, rfl⟩)
        · exact absurd h hv'
        · rfl

theorem idPost_iff {f g : Func} {fB gB : Block} {a : ID} :
    I.idPost f g fB gB a = true ↔ a ∉ I.bvals ∨
      (isPhiIn f a = true ∧ isPhiIn g a = true ∧ a ∈ fB.values ∧ a ∈ gB.values) := by
  unfold Info.idPost
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, contains_false, contains_iff,
    and_assoc]

theorem pinRel_iff {f g : Func} {fB gB : Block} {pin : Facts} {w a : ID} :
    I.pinRel f g fB gB pin w a = true ↔ (w = a ∧ I.idPost f g fB gB a = true) ∨
      (a ∈ I.vs ∧ I.look pin a = some w) := by
  unfold Info.pinRel
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, contains_iff]

theorem home_eq_some {f g : Func} {fB : Block} {out : Facts} {x a : ID}
    (h : I.home f g fB out x = some a) :
      (x ∈ fB.values ∧ isPhiIn f x = false ∧ a = x) ∨
      (¬ (x ∈ fB.values ∧ isPhiIn f x = false) ∧ (g.getV x).op ≠ .Invalid ∧
        ((x ∈ fB.values ∧ a = x) ∨ (x ∉ fB.values ∧ a ∈ I.vs ∧ I.look out a = some x))) := by
  unfold Info.home at h
  by_cases h1 : (fB.values.contains x && !isPhiIn f x) = true
  · simp only [h1, ↓reduceIte] at h
    simp only [Bool.and_eq_true, Bool.not_eq_true', contains_iff] at h1
    cases h; exact .inl ⟨h1.1, h1.2, rfl⟩
  · simp only [h1, ↓reduceIte, Bool.false_eq_true] at h
    have h1' : ¬ (x ∈ fB.values ∧ isPhiIn f x = false) := by
      simpa [Bool.and_eq_true, contains_iff] using h1
    by_cases h2 : ((g.getV x).op == .Invalid) = true
    · simp only [h2, ↓reduceIte] at h; cases h
    · simp only [h2, ↓reduceIte, Bool.false_eq_true] at h
      have h2' : (g.getV x).op ≠ .Invalid := by simpa using h2
      by_cases h3 : fB.values.contains x = true
      · simp only [h3, ↓reduceIte] at h
        cases h; exact .inr ⟨h1', h2', .inl ⟨contains_iff.1 h3, rfl⟩⟩
      · simp only [h3, ↓reduceIte, Bool.false_eq_true] at h
        have h3' : x ∉ fB.values := fun h => h3 (contains_iff.2 h)
        have hm := Array.mem_of_find?_eq_some h
        have hp := Array.find?_some h
        simp only [beq_iff_eq] at hp
        exact .inr ⟨h1', h2', .inr ⟨h3', hm, hp⟩⟩

end SCI


/-! ## Shapes -/

theorem tyOf_eq {tabs : Tables} {h : Func} {x : ID} {v : Value} (hv : h.value? x = some v) :
    tyOf tabs h x = (if v.type < tabs.types.size then tabs.ty v.type else .other) := by
  unfold tyOf
  have hlt := lt_of_value? hv
  unfold Func.value? at hv
  simp only [Ctx.make, Array.getElem?_map, Array.getElem?_eq_getElem hlt, Option.map_some,
    Option.getD_some]
  rw [Array.getElem?_eq_getElem hlt] at hv
  simp only [Option.join_some] at hv
  rw [hv]
  simp only [valueTy, typeShapes, Array.getElem?_map, List.getElem?_toArray]
  split
  · rename_i hlt'; rw [List.getElem?_range hlt']; rfl
  · rename_i hge; rw [List.getElem?_eq_none (by simpa using hge)]; rfl

theorem tyOf_shape {I : Info} {tabs : Tables} (ht : I.tabs = tabs) {h : Func} {x : ID} {v : Value}
    (hv : h.value? x = some v) : tyOf tabs h x = I.shapeOf v.type := by
  rw [tyOf_eq hv]; unfold Info.shapeOf; rw [ht]

theorem tyEq_shape {I : Info} {t1 t2 : TypeRef} (h : I.tyEq t1 t2 = true) :
    I.shapeOf t1 = I.shapeOf t2 := by
  unfold Info.tyEq at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · rw [beq_iff_eq] at h; rw [h]
  · exact Ty.eq_of_beq h

theorem tys_of_tyOf {tabs : Tables} {h : Func} {x : ID} {v : Value} (hv : h.value? x = some v) :
    (Ctx.make tabs h).tys[x]? = some (tyOf tabs h x) := by
  unfold tyOf
  have hlt := lt_of_value? hv
  simp [Ctx.make, Array.getElem?_map, Array.getElem?_eq_getElem hlt]

/-- A register of a typed frame is fixed by `retype` at its value's shape. -/
theorem typed_fix {tabs : Tables} {h : Func} {fr : Frame} (ht : Typed (Ctx.make tabs h) fr)
    {x : ID} {y : Val} (hx : fr.regs[x]? = some (some y)) : y.retype (tyOf tabs h x) = y :=
  ht x y hx

/-! ## `tabEqBy` -/

theorem tabEqBy_spec {α : Type} {eq : Option α → Option α → Bool} {heq : ∀ o, eq o o = true}
    {a b : Array (Option α)} {skip : Nat → Bool} (h : tabEqBy eq heq a b skip = true) :
    ∀ i, skip i = false → eq (a[i]?).join (b[i]?).join = true := by
  intro i hi
  unfold tabEqBy at h
  rw [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hsz, h⟩ := h
  rcases Nat.lt_or_ge i a.size with hlt | hge
  · have := nat_all_spec h i hlt
    simp only [withPtrEq, hi, Bool.false_or] at this
    have hb : i < b.size := hsz ▸ hlt
    rw [getElem!_pos a i hlt, getElem!_pos b i hb] at this
    rw [Array.getElem?_eq_getElem hlt, Array.getElem?_eq_getElem hb, Option.join_some,
      Option.join_some]
    exact this
  · rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]
    exact heq _

theorem sameEntry_spec {o o' : Option Value} (h : sameEntry o o' = true) :
    (o = none ∧ o' = none) ∨ ∃ v v', o = some v ∧ o' = some v' ∧ v'.id = v.id ∧ v'.op = v.op ∧
      v'.type = v.type ∧ v'.aux = v.aux ∧ v'.auxInt = v.auxInt ∧ v'.args = v.args ∧
      v'.block = v.block := by
  cases o with
  | none => cases o' with
    | none => exact .inl ⟨rfl, rfl⟩
    | some _ => simp [sameEntry] at h
  | some v => cases o' with
    | none => simp [sameEntry] at h
    | some v' =>
      simp only [sameEntry, beq_iff_eq] at h
      have := congrArg (·.id) h; have := congrArg (·.op) h; have := congrArg (·.type) h
      have := congrArg (·.aux) h; have := congrArg (·.auxInt) h; have := congrArg (·.args) h
      have := congrArg (·.block) h
      simp_all

/-! ## The checker's parts -/

namespace Setup

variable {ce : CheckEnv} {tabs : Tables} {f g : Func} {s : Site} (S : Setup ce tabs f g s)
include S

set_option hygiene false in
local notation "𝓘" => infoOf tabs f g s
set_option hygiene false in
local notation "𝓣" => Info.factTab (infoOf tabs f g s) f g

theorem parts : (𝓘).preOK f = true ∧ g.blocks = f.blocks ∧ g.entry = f.entry ∧
    g.ownAux = f.ownAux ∧ g.valueTab.size = f.valueTab.size ∧
    g.blockTab.size = f.blockTab.size ∧
    (s.b ∈ (𝓘).K ∧ s.te.b ∈ (𝓘).K ∧ s.p ∈ (𝓘).K) ∧
    (𝓘).redirOK f g = true ∧ (𝓘).regionOK g = true ∧
    (𝓘).frameOK f g = true ∧ (∀ B ∈ (𝓘).K, (𝓘).blockOK f g 𝓣 B = true) ∧
    (𝓘).exitOK g 𝓣 = true ∧ (𝓘).scanOK g = true ∧ (∀ B ∈ (𝓘).K, (𝓘).wfKOK f g B = true) ∧
    (𝓘).dsOK g = true ∧ (𝓘).closeOK g = true ∧ (∀ B ∈ (𝓘).K, (𝓘).domKOK f g B = true) := by
  have h := S.ok
  unfold scOK at h
  simp only [withPtrEq, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, hk1⟩, hk2⟩, hk3⟩, h8⟩, h9⟩, h10⟩,
    h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩, h17⟩ := h
  exact ⟨h1, h3, h4, h5, h6, h7, ⟨contains_iff.1 hk1, contains_iff.1 hk2, contains_iff.1 hk3⟩,
    h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

omit S in
@[simp] theorem infoOf_s : (infoOf tabs f g s).s = s := rfl
omit S in
@[simp] theorem infoOf_t : (infoOf tabs f g s).t = s.te.b := rfl

theorem gblocks : g.blocks = f.blocks := S.parts.2.1
theorem gentry : g.entry = f.entry := S.parts.2.2.1
theorem gownAux : g.ownAux = f.ownAux := S.parts.2.2.2.1
theorem gvsize : g.valueTab.size = f.valueTab.size := S.parts.2.2.2.2.1
theorem gbsize : g.blockTab.size = f.blockTab.size := S.parts.2.2.2.2.2.1
theorem bK : s.b ∈ (𝓘).K := S.parts.2.2.2.2.2.2.1.1
theorem tK : s.te.b ∈ (𝓘).K := S.parts.2.2.2.2.2.2.1.2.1
theorem pK : s.p ∈ (𝓘).K := S.parts.2.2.2.2.2.2.1.2.2
theorem redirOK : (𝓘).redirOK f g = true := S.parts.2.2.2.2.2.2.2.1
theorem regionOK : (𝓘).regionOK g = true := S.parts.2.2.2.2.2.2.2.2.1
theorem frameOK : (𝓘).frameOK f g = true := S.parts.2.2.2.2.2.2.2.2.2.1
theorem blockOK {B : ID} (hB : B ∈ (𝓘).K) : (𝓘).blockOK f g 𝓣 B = true :=
  S.parts.2.2.2.2.2.2.2.2.2.2.1 B hB
theorem exitOK : (𝓘).exitOK g 𝓣 = true := S.parts.2.2.2.2.2.2.2.2.2.2.2.1
theorem scanOK : (𝓘).scanOK g = true := S.parts.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem wfKOK {B : ID} (hB : B ∈ (𝓘).K) : (𝓘).wfKOK f g B = true :=
  S.parts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 B hB
theorem dsOK : (𝓘).dsOK g = true := S.parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem closeOK : (𝓘).closeOK g = true := S.parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem domKOK {B : ID} (hB : B ∈ (𝓘).K) : (𝓘).domKOK f g B = true :=
  S.parts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 B hB

/-! ### The site in `f` -/

/-- **The site before the rewrite** (`preOK`). -/
theorem pre : ∃ B, f.block? s.b = some B ∧ s.b ∈ f.blocks ∧ B.id = s.b ∧ B.values = (𝓘).bvals ∧ B.kind = .If ∧
    s.p ≠ s.b ∧ s.te.b ≠ s.b ∧ B.preds[s.cidx]? = some ⟨s.p, s.pi⟩ ∧
    (𝓘).last + 1 = B.preds.size ∧
    (𝓘).vs = (𝓘).bvals.filter (fun x => x != s.ctl && isPhiIn f x) ∧
    ((𝓘).vs = #[] ∨ B.preds.size = 2) ∧
    ∃ top cv chain par c cc, B.controls[0]? = some top ∧ B.controls.size = 1 ∧
      f.value? s.ctl = some cv ∧ cv.op = .Phi ∧
      s.ctl ∈ B.values ∧ chainOf f B s.ctl (B.values.size + 1) top = some (chain, par) ∧
      cv.args[s.cidx]? = some c ∧ f.value? c = some cc ∧ cc.op = .ConstBool ∧ cc.args = #[] ∧
      B.succs[if (cc.auxInt != 0) ^^ par then 0 else 1]? = some s.te ∧
      ∀ x ∈ B.values, x = s.ctl ∨ x ∈ chain ∨ isPhiIn f x = true := by
  have h := S.parts.1
  unfold Info.preOK at h
  split at h
  · cases h
  · rename_i B hB
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.or_eq_true,
      Array.isEmpty_iff] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h11⟩ := h
    refine ⟨B, hB, contains_iff.1 h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, ?_⟩
    split at h11
    · rename_i top cv hc hcv
      simp only [Bool.and_eq_true, beq_iff_eq] at h11
      obtain ⟨⟨⟨hsz, hph⟩, hmem⟩, h11⟩ := h11
      split at h11
      · rename_i chain par c hch hcc
        simp only [Bool.and_eq_true, Array.all_eq_true'] at h11
        obtain ⟨h12, h13⟩ := h11
        split at h12
        · rename_i cc hcc'
          simp only [Bool.and_eq_true, beq_iff_eq, Array.isEmpty_iff] at h12
          refine ⟨top, cv, chain, par, c, cc, hc, hsz, hcv, hph, contains_iff.1 hmem, hch, hcc, hcc',
            h12.1.1, h12.1.2, by simpa using h12.2, fun x hx => ?_⟩
          have := h13 x hx
          simpa [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem, or_assoc] using this
        · cases h12
      · cases h11
    · cases h11

theorem vs_mem {v : ID} (hv : v ∈ (𝓘).vs) :
    v ∈ (𝓘).bvals ∧ v ≠ s.ctl ∧ isPhiIn f v = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hvs, -⟩ := S.pre
  rw [hvs, Array.mem_filter] at hv
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hv
  exact ⟨hv.1, hv.2.1, hv.2.2⟩

end Setup

end GoFV.Proof.ShortCirc

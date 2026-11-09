import GoFV.Proof.Pass.DeadSim
import GoFV.Proof.FrameL

variable [GoFV.SSA.Sem.Addrs]

/-!
# Removing unreachable blocks and dead values in lowered code: what `runL` adds to `DeadRel`

`refinesL_of_deadRel` (`GoFV.Proof.Pass.DeadSimL`) is Phase 1's `refines_of_deadRel` over `runL`.
Beyond `DeadRel`, `runL` reads three things of the functions (`DeadRelL`):

* an arm64 terminator reads its block's `auxInt` (`Arm64.taken`, `TBZ`/`TBNZ`): kept blocks keep
  it (`auxInt`);
* `MOVDreg`/`MOVDnop` read whether their argument sign-extends (`sxOf`, `Arm64.signExtendsIn`):
  every value of `g` has its op in `f` (`op`), and a listed `Select0`/`Select1` of `g` keeps its
  arguments (`sel`: it may select from `LDPSW`), so `signExtendsIn` agrees (`signExtendsIn_eq`);
* the ops that panic under `runL` are `PanickingL false` (calls, `NilCheck` and
  `LoweredNilCheck`, not only Phase 1's `Panicking`): a dropped value of a kept block is none
  (`dropped`).

This module: `DeadRelL`, the lowered terminator lemma (`stepTermL_rel`: a generic kind is Phase 1's
`stepTerm_rel`; an arm64 kind branches on the same control value and `auxInt` alike, along the
same successor index, `stepTermL_arm`; `stepTermL_not_panic`, `stepTermL_goto_mem`), and the shapes of `runL`'s context (`tys_of_valueL`).
-/

namespace GoFV.Proof.Dead

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof

/-- What `runL` needs of `f`, `g` and the kept blocks `K` beyond `DeadRel` (see the module doc). -/
structure DeadRelL (f g : Func) (K : ID → Prop) : Prop where
  /-- Every value of `g` has its op in `f`. -/
  op : ∀ x gv, g.value? x = some gv → ∃ fv, f.value? x = some fv ∧ gv.op = fv.op
  /-- A kept block keeps its `auxInt`. -/
  auxInt : ∀ bid, K bid → ∀ gb fb, g.block? bid = some gb → f.block? bid = some fb →
    gb.auxInt = fb.auxInt
  /-- A dropped value of a kept block cannot panic under `runL`. -/
  dropped : ∀ bid, K bid → ∀ gb fb, g.block? bid = some gb → f.block? bid = some fb →
    ∀ x ∈ fb.values, x ∉ gb.values → ∀ fv, f.value? x = some fv → ¬ PanickingL false fv.op
  /-- A listed `Select0`/`Select1` of `g` has the arguments of `f`'s. -/
  sel : ∀ x gv, Listed g x → g.value? x = some gv → (gv.op = .Select0 ∨ gv.op = .Select1) →
    ∃ fv, f.value? x = some fv ∧ gv.args = fv.args

/-- A listed value of `g` and its `f` counterpart hold the same sign extension. -/
theorem DeadRelL.signExtendsIn_eq {f g : Func} {K : ID → Prop} (L : DeadRelL f g K)
    {ce : CheckEnv} (hwg : WF ce g) {a : ID} {ga fa : Value} (hl : Listed g a)
    (hga : g.value? a = some ga) (hfa : f.value? a = some fa) :
    Arm64.signExtendsIn g.value? ga = Arm64.signExtendsIn f.value? fa := by
  obtain ⟨fa', hfa', hop⟩ := L.op a ga hga
  rw [hfa] at hfa'; cases hfa'
  unfold Arm64.signExtendsIn
  rw [hop]
  congr 1
  by_cases hs : fa.op = .Select0 ∨ fa.op = .Select1
  · obtain ⟨fa'', hfa'', hargs⟩ := L.sel a ga hl hga (hop ▸ hs)
    rw [hfa] at hfa''; cases hfa''
    have hsel : ∀ c ∈ ga.args, ((g.value? c).map (·.op == .ARM64LDPSW)) =
        ((f.value? c).map (·.op == .ARM64LDPSW)) := by
      intro c hc
      obtain ⟨bid, b, hbi, hmem⟩ := hl
      obtain ⟨c', b', hbi', hc'⟩ := hwg.argListed bid b a ga ⟨hbi, hmem, hga⟩ c hc
      obtain ⟨gc, hgc, -, -⟩ := hwg.valueId c' b' hbi' c hc'
      obtain ⟨fc, hfc, hopc⟩ := L.op c gc hgc
      simp only [hgc, hfc, Option.map_some, hopc]
    have h0 : ((ga.args[0]?.bind g.value?).map (·.op == .ARM64LDPSW)) =
        ((fa.args[0]?.bind f.value?).map (·.op == .ARM64LDPSW)) := by
      rw [← hargs]
      cases hc : ga.args[0]? with
      | none => rfl
      | some c => exact hsel c (Array.mem_of_getElem? hc)
    split <;> simp only [h0]
  · split
    · exact absurd (Or.inl ‹_›) hs
    · exact absurd (Or.inr ‹_›) hs
    · rfl

/-- A value that may panic under `runL` is not pure. -/
theorem prio_panickingL {op : Op} (h : PanickingL false op) : prio op ≠ 0 := by
  rcases h with h | h | ⟨h, -⟩
  · rw [prio_call h]; decide
  · unfold prio; simp [h]
  · cases h

/-! ## Terminators -/

theorem control_not_panic {fr : Frame} {b : Block} {k : Nat} {e : Panic} {m : Mem} :
    Sem.control fr b k ≠ .panic e m := by
  unfold Sem.control
  split
  · cases (fr.regs[‹ID›]?).join <;> nofun
  · nofun

/-- An arm64 terminator continues along the successor its control value and `auxInt` select;
a block of the same kind and `auxInt` with the same control value continues along its own. -/
theorem stepTermL_arm {fr : Frame} {b : Block} {n : Next} (ha : b.kind.isArm64 = true)
    (h : stepTermL fr b = .ok n) :
    ∃ v k, Sem.control fr b 0 = .ok v ∧ succ b k = .ok n ∧ ∀ (fr' : Frame) (b' : Block),
      b'.kind = b.kind → b'.auxInt = b.auxInt → Sem.control fr' b' 0 = .ok v →
        stepTermL fr' b' = succ b' k := by
  unfold stepTermL at h
  simp only [ha, ↓reduceIte] at h
  cases hc : Sem.control fr b 0 with
  | panic e m => exact absurd hc control_not_panic
  | stuck msg =>
    split at h <;> (simp only [bind, Res.bind, hc] at h; cases h)
  | ok v =>
  refine ⟨v, ?_⟩
  have key : ∀ (fr' : Frame) (b' : Block), b'.kind = b.kind → b'.auxInt = b.auxInt →
      Sem.control fr' b' 0 = .ok v → stepTermL fr' b' =
        match b.kind with
        | .ARM64JUMPTABLE =>
          match Arm64.reg v with
          | some x => succ b' x.toNat
          | none => .stuck s!"b{b'.id}: JUMPTABLE on poison or non-int"
        | k =>
          match Arm64.taken k b.auxInt v with
          | some true => succ b' 0
          | some false => succ b' 1
          | none => .stuck s!"b{b'.id}: {k.name} on poison or an ill-typed control" := by
    intro fr' b' hk hai hc'
    unfold stepTermL
    rw [hk, hai]
    simp only [ha, ↓reduceIte, bind, Res.bind, hc']
    rfl
  have h0 := key fr b rfl rfl hc
  unfold stepTermL at h0
  simp only [ha, ↓reduceIte] at h0
  rw [h0] at h
  split at h
  · split at h
    · exact ⟨_, rfl, h, fun fr' b' hk hai hc' => by
        rw [key fr' b' hk hai hc']; simp only [*]⟩
    · cases h
  · split at h
    · exact ⟨_, rfl, h, fun fr' b' hk hai hc' => by
        rw [key fr' b' hk hai hc']; split <;> simp_all⟩
    · exact ⟨_, rfl, h, fun fr' b' hk hai hc' => by
        rw [key fr' b' hk hai hc']; split <;> simp_all⟩
    · cases h

theorem stepTermL_not_panic {fr : Frame} {b : Block} {e : Panic} {m : Mem} :
    stepTermL fr b ≠ .panic e m := by
  intro h
  by_cases ha : b.kind.isArm64 = true
  · have hsp : ∀ k, succ b k ≠ .panic e m := fun k h => by
      unfold succ at h; cases hk : b.succs[k]? <;> rw [hk] at h <;> cases h
    unfold stepTermL at h
    simp only [ha, ↓reduceIte] at h
    cases hc : Sem.control fr b 0 with
    | panic e' m' => exact control_not_panic hc
    | stuck msg => split at h <;> (simp only [bind, Res.bind, hc] at h; cases h)
    | ok v =>
      split at h <;> simp only [bind, Res.bind, hc] at h <;> split at h <;>
        first | exact hsp _ h | cases h
  · rw [stepTermL_generic fr (Bool.eq_false_iff.2 ha)] at h
    exact CopyElim.stepTerm_not_panic h

/-- **The terminator of a kept block** under `runL`: `stepTerm_rel` with arm64 kinds, which also
read the block's `auxInt`. -/
theorem stepTermL_rel {fr fr' : Frame} {b b' : Block} (hk : KindRel b.kind b'.kind)
    (hai : b'.auxInt = b.auxInt) (hc : b'.controls = b.controls)
    (hag : ∀ c ∈ b.controls, fr'.regs[c]? = fr.regs[c]?) {n : Next} (h : stepTermL fr b = .ok n) :
    (∃ k e, n = .goto e ∧ b.succs[k]? = some e ∧ (b.kind = .First → k = 0) ∧
      stepTermL fr' b' = succ b' k) ∨
    (∃ rs m, n = .ret rs m ∧ stepTermL fr' b' = .ok (.ret rs m)) := by
  by_cases ha : b.kind.isArm64 = true
  · have hkk : b'.kind = b.kind := by
      rcases hk with hk | ⟨hf, -⟩
      · exact hk
      · rw [hf] at ha; cases ha
    obtain ⟨v, k, hcv, hs, hT⟩ := stepTermL_arm ha h
    obtain ⟨e, he, rfl⟩ := succ_ok hs
    refine .inl ⟨k, e, rfl, he, fun hf => (by rw [hf] at ha; cases ha), ?_⟩
    exact hT fr' b' hkk hai (control_agree hc hag hcv)
  · have ha' : b'.kind.isArm64 = false := by
      rcases hk with hk | ⟨-, hp⟩
      · rw [hk]; exact Bool.eq_false_iff.2 ha
      · rw [hp]; rfl
    rw [stepTermL_generic fr (Bool.eq_false_iff.2 ha)] at h
    rw [stepTermL_generic fr' ha']
    exact stepTerm_rel hk hc hag h

/-- A terminator under `runL` continues along one of the block's successors. -/
theorem stepTermL_goto_mem {fr : Frame} {b : Block} {e : Edge}
    (h : stepTermL fr b = .ok (.goto e)) : e ∈ b.succs := by
  by_cases ha : b.kind.isArm64 = true
  · obtain ⟨-, k, -, hs, -⟩ := stepTermL_arm ha h
    obtain ⟨e', he', hee⟩ := succ_ok hs
    cases hee
    exact Array.mem_of_getElem? he'
  · rw [stepTermL_generic fr (Bool.eq_false_iff.2 ha)] at h
    exact CopyElim.stepTerm_goto_mem h

/-! ## Shapes -/

theorem tys_of_valueL {tabs : Tables} {f : Func} {x : ID} {v : Value} (h : f.value? x = some v) :
    (Ctx.makeL tabs f).tys[x]? =
      some ((if f.lowered then typeShapesL tabs else typeShapes tabs)[v.type]?.getD .other) := by
  unfold Func.value? at h
  rw [tys_makeL, Array.getElem?_map]
  cases hx : f.valueTab[x]? with
  | none => rw [hx] at h; cases h
  | some o =>
    rw [hx] at h; simp at h; subst h
    rfl

end GoFV.Proof.Dead

import GoFV.Proof.Pass.DeadEdgeJ
import GoFV.Proof.Pass.CopyElimSim

/-!
# deadcode's input fragment

`DeadFrag tabs f`: what `deadcode_refines` assumes of its input beyond `check`, all of it decided
on the input (`deadFragB`, `deadFrag_of`): block IDs up to `bid.last` (`reachable_spec`), listed
`First` blocks with two successors (`FirstTwo`), copyelim's fragment (`CopyFrag`, `EmptyFrag`)
of the edge-removed functions `edgesG false f` and `edgesG true f` (the latter is deadcode's own
edge removal, `edgesG_true`), and the dominator certificates (`CertOK`) of `edgesG false f` and
of copyelim's output on `edgesG true f` (`check` is not available on them: an unreachable block
that lost an edge breaks its kind's successor count). `lake exe deadcode-probe` counts the
corpus inputs in the fragment.
-/

namespace GoFV.Proof.Dead

open GoFV.SSA GoFV.Opt GoFV.Proof GoFV.Proof.CopyElim GoFV.Proof.Dom

/-- deadcode's input fragment (see the module doc). -/
structure DeadFrag (tabs : Tables) (f : Func) : Prop where
  bid : ∀ b ∈ f.blocks, b ≤ f.bidLast
  firstTwo : FirstTwo f
  copy1 : CopyFrag tabs (edgesG false f)
  copy2 : CopyFrag tabs (edgesG true f)
  empty : EmptyFrag tabs (edgesG false f)
  cert1 : CertOK (edgesG false f)
  cert2 : ∀ g, copyelim tabs (edgesG true f) = .ok g → CertOK g

/-- Decides `FirstTwo`. -/
def firstTwoB (f : Func) : Bool :=
  f.blocks.all fun b => (f.getB b).kind != .First || (f.getB b).succs.size == 2

/-- Decides `DeadFrag` (`deadFrag_of`). -/
def deadFragB (tabs : Tables) (f : Func) : Bool :=
  f.blocks.all (· ≤ f.bidLast) && firstTwoB f &&
  copyFrag tabs (edgesG false f) && copyFrag tabs (edgesG true f) &&
  emptyFragB tabs (edgesG false f) && (DomCert.check (edgesG false f)).toBool &&
  match copyelim tabs (edgesG true f) with
  | .ok g => (DomCert.check g).toBool
  | .error _ => true

theorem certOK_of_toBool {f : Func} (h : (DomCert.check f).toBool = true) : CertOK f := by
  apply certOK_of_check
  cases hc : DomCert.check f with
  | ok u => rfl
  | error e => rw [hc] at h; cases h

theorem deadFrag_of {tabs : Tables} {f : Func} (h : deadFragB tabs f = true) : DeadFrag tabs f := by
  unfold deadFragB firstTwoB at h
  simp only [Bool.and_eq_true, Array.all_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨h1, fun b hb hk => ?_, copyFrag_sound h3, copyFrag_sound h4, emptyFrag_of h5,
    certOK_of_toBool h6, fun g hg => ?_⟩
  · have := h2 b hb
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, hk, not_true_eq_false,
      false_or] at this
    exact this
  · rw [hg] at h7; exact certOK_of_toBool h7

end GoFV.Proof.Dead

import GoFV.Proof.Low.TermL
import GoFV.Proof.Pass.LoadFwdFixed

/-!
# Loads of read-only symbols (issue #385, `ARM64.rules:1811-1817`)

The lowering validator replays a rule event at an integer load of a read-only symbol as the
`MOVDconst` it builds (`GoFV.Opt.LowerCheck.roLoadDef`) when the load from the symbol's allocation
alone gives the constant's word or `poison` (`roLoadWord`). `roLoadWord_loadN`: a load at the
symbol (`Arm64.loadN`) from any memory that holds the allocation reads exactly that, under every
address assignment: `loadN` reads only the allocation of the pointer's block (`loadN_congr_find`),
an allocation without frame pointers is read alike under every assignment (`loadN_agree`,
`Mem.load_agree`), and the word a load reads at the shape `other` is the register it puts at any
shape (`loadN_other`).
-/

namespace GoFV.Proof.Low

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.LowerCheck

/-- `Arm64.loadN` reads the same from two memories with the same allocation at the pointer's
block. -/
theorem loadN_congr_find [Addrs] {m m' : Mem} {p : Ptr} (h : m.find? p.blk = m'.find? p.blk)
    (ty : Ty) (n : Nat) (s : Bool) : Arm64.loadN ty n s m p = Arm64.loadN ty n s m' p := by
  have hl : ∀ t, m.load t p = m'.load t p := fun t => by
    unfold Mem.load
    simp only [GoFV.Proof.Pass.LoadFwd.read_congr_find h]
  unfold Arm64.loadN
  simp only [hl]

/-- `Arm64.loadN` of a memory without frame pointers is the same under every address
assignment. -/
theorem loadN_agree {A B : Addrs} {m : Mem} (hm : m.lowB = true) (ty : Ty) (n : Nat) (s : Bool)
    (p : Ptr) : @Arm64.loadN A ty n s m p = @Arm64.loadN B ty n s m p := by
  unfold Arm64.loadN
  simp only [Mem.load_agree (A := A) (B := B) hm]

/-- The register a load puts at shape `ty` is the word it reads at shape `other`. -/
theorem loadN_other [Addrs] (ty : Ty) (n : Nat) (s : Bool) (m : Mem) (p : Ptr) :
    Arm64.loadN ty n s m p = match Arm64.loadN .other n s m p with
      | .int .w64 x => Arm64.res ty x
      | v => v := by
  unfold Arm64.loadN
  split
  · split <;> simp_all [Arm64.res]
  · split
    · split <;> simp [Arm64.res]
    · rfl

/-- **The load `roLoadWord` checks**: if `roLoadWord` accepts the allocation `a` of `name`, an
`n`-byte load at offset `o` of `name` from a memory holding `a` there gives the word it found at
the shape `ty`, or `poison`. -/
theorem roLoadWord_loadN [Addrs] {name : String} {a : Alloc} {n : Nat} {s : Bool} {o : BitVec 64}
    {r : Option (BitVec 64)} (h : roLoadWord name a n s o = some r) {m : Mem}
    (hm : m.find? (.global name) = some a) (ty : Ty) :
    Arm64.loadN ty n s m ⟨.global name, o⟩ = r.elim .poison (Arm64.res ty) := by
  have hf : m.find? (Ptr.blk ⟨.global name, o⟩) =
      (({} : Mem).set (.global name) a).find? (Ptr.blk ⟨.global name, o⟩) := by
    rw [hm, GoFV.Proof.CSE.Mem.find?_set]; simp
  rw [loadN_congr_find hf, loadN_other]
  unfold roLoadWord at h
  simp only at h
  split at h
  · rename_i hlow
    rw [loadN_agree (B := Addrs.fixed) hlow]
    split at h
    · rename_i x hx
      cases h
      rw [hx]
      rfl
    · rename_i hx
      cases h
      rw [hx]
      rfl
    · cases h
  · cases h

end GoFV.Proof.Low

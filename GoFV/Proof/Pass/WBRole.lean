import GoFV.Proof.Pass.WBLocal
import GoFV.Proof.Pass.WBSpec

/-!
# writebarrier: roles as propositions (issue #36)

`roleOK` (the checker's per-value condition) read for each role (`roleOK_*`), the ops of the
buffer-block roles (`roleOf_then`), and `local_all`: a listed value of a chain whose role's
source facts hold (`Cov`) evaluates as `QR` says.
-/

namespace GoFV.Proof.WB

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.WBCheck GoFV.Proof

/-- The source evaluated `x` in `Gr`. -/
def Ev (env : Env) (c : WBCheck.Ctx) (Gr : Frame) (x : ID) : Prop :=
  ∃ u y, c.f.value? x = some u ∧ Gr.regs[x]? = some (some y) ∧
    evalValue env (Ctx.make c.tabs c.f) Gr u = .ok y

/-- The source facts a value of the chain needs, by role. -/
def Cov (env : Env) (c : WBCheck.Ctx) (rs : List Run) (Gr : Frame) (x : ID) : Prop :=
  match c.roleOf rs x with
  | .held => c.K.getD x false = true → Ev env c Gr x
  | .tgt j k => ∃ r s, rs[j]? = some r ∧ r.src[k]? = some s ∧ Ev env c Gr s
  | .ncEnd j => ∃ r n, rs[j]? = some r ∧ r.nc = some n ∧ Ev env c Gr n
  | .ncThen j => ∃ r n, rs[j]? = some r ∧ r.nc = some n ∧ Ev env c Gr n
  | .wb j => ∃ M, RunMem Gr rs j M
  | _ => True

/-- `ncCopyOK` as a proposition. -/
def NcCopy (c : WBCheck.Ctx) (B : Block) (segs : List ID) (j : Nat) (n y m : ID) : Prop :=
  ∃ u w p mS, c.f.value? n = some u ∧ c.g.value? y = some w ∧ u.op = .NilCheck ∧
    w.op = .NilCheck ∧ w.type = u.type ∧ u.args = #[p, mS] ∧ w.args = #[p, m] ∧
    c.availIn B segs j p = true

theorem array_two {α : Type} [Inhabited α] {a : Array α} (h : a.size = 2) : a = #[a[0]!, a[1]!] := by
  rcases a with ⟨_ | ⟨x, _ | ⟨y, _ | ⟨z, l⟩⟩⟩⟩ <;> simp at h ⊢

theorem ncCopy_spec {c : WBCheck.Ctx} {B : Block} {segs : List ID} {j : Nat} {n y m : ID}
    (h : c.ncCopyOK B segs j n y m = true) : NcCopy c B segs j n y m := by
  unfold Ctx.ncCopyOK at h
  split at h
  · rename_i u w hu hw
    simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h
    obtain ⟨hu1, hw1, hty, hws, hus, h0, h1, hav⟩ := h
    refine ⟨u, w, u.args[0]!, u.args[1]!, hu, hw, hu1, hw1, hty, array_two hus, ?_, hav⟩
    rw [array_two hws, h0, h1]
  · cases h

/-! ## `roleOK` by role -/

section
variable {c : WBCheck.Ctx} {b : ID} {B : Block} {segs : List ID} {rs : List Run} {inT : Bool}
  {j : Nat} {x : ID} {w : Value}

theorem roleOK_held (h : c.roleOK b B segs rs inT j x = true) (hw : c.g.value? x = some w)
    (hρ : c.roleOf rs x = .held) :
    inT = false ∧ x ∈ B.values ∧
    ((c.K.getD x false = true ∧ ∃ u, c.f.value? x = some u ∧
        (u.op = .Phi → j = 0 ∧ ∀ a ∈ u.args, c.held a = true) ∧
        (u.op ≠ .Phi → ∀ a ∈ u.args, c.availIn B segs j a = true)) ∨
      (c.K.getD x false = false ∧ ∃ j' r, j = j' + 1 ∧ rs[j']? = some r ∧ r.last = x ∧
        w.op = .WBend ∧ w.args = #[w.args[0]!] ∧ r.tgt.getLast? = some w.args[0]! ∧
        c.tabs.ty w.type = .mem ∧ (∃ u, c.f.value? x = some u ∧ u.type = w.type) ∧
        c.roleOf rs w.args[0]! = .tgt j' (r.tgt.length - 1))) := by
  unfold Ctx.roleOK at h
  rw [hw] at h
  simp only [hρ, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hT, hx⟩, h⟩ := h
  refine ⟨hT, by simpa using hx, ?_⟩
  split at h
  · rename_i hK
    left
    refine ⟨hK, ?_⟩
    split at h
    · rename_i u hu
      refine ⟨u, hu, fun hp => ?_, fun hp => ?_⟩
      · rw [if_pos (by simpa using hp)] at h
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        exact ⟨h.1, Array.all_eq_true_iff_forall_mem.1 h.2⟩
      · rw [if_neg (by simpa using hp)] at h
        exact Array.all_eq_true_iff_forall_mem.1 h
    · cases h
  · rename_i hK
    right
    refine ⟨by simpa using hK, ?_⟩
    split at h
    · rename_i j' r hr
      simp only [Bool.and_eq_true, beq_iff_eq, and_assoc, Option.isNone_iff_eq_none] at h
      obtain ⟨hl, hop, hsz, h0, -, hty, hu, hrole⟩ := h
      refine ⟨j', r, rfl, hr, hl, hop, ?_, ?_, ?_, ?_, hrole⟩
      · rcases hw' : w.args with ⟨_ | ⟨a, _ | ⟨_, _⟩⟩⟩ <;> simp_all
      · rcases hw' : w.args with ⟨_ | ⟨a, _ | ⟨_, _⟩⟩⟩ <;> simp_all
      · unfold tyIs isMemTy at hty; split at hty <;> simp_all
      · cases hf : c.f.value? x with
        | none => rw [hf] at hu; cases hu
        | some u => rw [hf] at hu; exact ⟨u, rfl, by simpa using hu⟩
    · cases h

theorem roleOK_lazy (h : c.roleOK b B segs rs inT j x = true) (hw : c.g.value? x = some w)
    (hρ : c.roleOf rs x = .wbaddr ∨ c.roleOf rs x = .const0 ∨ c.roleOf rs x = .lazy) :
    inT = false ∧ b = c.f.entry ∧ j = 0 ∧ (c.held x = true → x ∈ B.values) ∧
      ∀ a ∈ w.args, a ∈ vals c.g b := by
  unfold Ctx.roleOK at h
  rw [hw] at h
  rcases hρ with hρ | hρ | hρ <;>
  · simp only [hρ, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, and_assoc,
      Array.all_eq_true_iff_forall_mem, Bool.or_eq_true] at h
    obtain ⟨hT, hb, hj, hh, ha⟩ := h
    refine ⟨hT, hb, hj, fun hx => ?_, fun a h' => by simpa using ha a h'⟩
    rcases hh with hh | hh
    · rw [hx] at hh; cases hh
    · simpa using hh

theorem roleOK_invalid (h : c.roleOK b B segs rs inT j x = true) (hw : c.g.value? x = some w)
    (hρ : c.roleOf rs x = .invalid) : inT = false ∧ w.op = .Invalid ∧ w.args = #[] := by
  unfold Ctx.roleOK at h
  rw [hw] at h
  simp only [hρ, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, Array.isEmpty_iff] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem roleOK_load {i : Nat} (h : c.roleOK b B segs rs inT j x = true) (hw : c.g.value? x = some w)
    (hρ : c.roleOf rs x = .load i) :
    inT = false ∧ i = j ∧ ∃ r, rs[i]? = some r ∧ w.op = .Load ∧
      w.args = #[r.sp.wbaddr, r.sp.mem] ∧ c.tabs.ty w.type = .int .w32 ∧
      c.isWbaddr r.sp.wbaddr = true ∧ c.availIn B segs j r.sp.mem = true := by
  unfold Ctx.roleOK at h
  rw [hw] at h
  simp only [hρ, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨hT, hi⟩, h⟩ := h
  refine ⟨hT, hi, ?_⟩
  split at h
  · rename_i r hr
    simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h
    obtain ⟨hop, ha, hty, hwa, hm⟩ := h
    refine ⟨r, hr, hop, ha, ?_, hwa, hm⟩
    split at hty
    · assumption
    · cases hty
  · cases h

theorem roleOK_flag {i : Nat} (h : c.roleOK b B segs rs inT j x = true) (hw : c.g.value? x = some w)
    (hρ : c.roleOf rs x = .flag i) :
    inT = false ∧ i = j ∧ ∃ r, rs[i]? = some r ∧ w.op = .Neq32 ∧
      w.args = #[r.sp.load, r.sp.const0] ∧ c.tabs.ty w.type = .bool ∧
      c.isConst0 r.sp.const0 = true ∧ c.roleOf rs r.sp.load = .load i := by
  unfold Ctx.roleOK at h
  rw [hw] at h
  simp only [hρ, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨hT, hi⟩, h⟩ := h
  refine ⟨hT, hi, ?_⟩
  split at h
  · rename_i r hr
    simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h
    obtain ⟨hop, ha, hty, hc, hl⟩ := h
    refine ⟨r, hr, hop, ha, ?_, hc, hl⟩
    split at hty
    · assumption
    · cases hty
  · cases h

theorem roleOK_phi {i : Nat} (h : c.roleOK b B segs rs inT j x = true) (hw : c.g.value? x = some w)
    (hρ : c.roleOf rs x = .phi i) :
    inT = false ∧ j = i + 1 ∧ ∃ r, rs[i]? = some r ∧ w.op = .Phi ∧
      w.args = #[r.sp.mem, r.memThen] ∧ c.tabs.ty w.type = .mem ∧
      (r.memThen = r.sp.mem ∨ c.roleOf rs r.memThen = .sel1 i ∨
        c.roleOf rs r.memThen = .bstore i) := by
  unfold Ctx.roleOK at h
  rw [hw] at h
  simp only [hρ, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨hT, hi⟩, h⟩ := h
  refine ⟨hT, hi, ?_⟩
  split at h
  · rename_i r hr
    simp only [Bool.and_eq_true, beq_iff_eq, and_assoc, Bool.or_eq_true] at h
    obtain ⟨hop, ha, hty, hm⟩ := h
    refine ⟨r, hr, hop, ha, ?_, ?_⟩
    · unfold tyIs isMemTy at hty; split at hty <;> simp_all
    · rcases hm with hm | hm
      · exact .inl hm
      · split at hm
        · rename_i k hk; right; left; rw [hk]; simp at hm; rw [hm]
        · rename_i k hk; right; right; rw [hk]; simp at hm; rw [hm]
        · cases hm
  · cases h

theorem roleOK_ncEnd {i : Nat} (h : c.roleOK b B segs rs inT j x = true) (hw : c.g.value? x = some w)
    (hρ : c.roleOf rs x = .ncEnd i) :
    inT = false ∧ j = i + 1 ∧ ∃ r n, rs[i]? = some r ∧ r.nc = some n ∧
      NcCopy c B segs j n x r.phi ∧ c.roleOf rs r.phi = .phi i := by
  unfold Ctx.roleOK at h
  rw [hw] at h
  simp only [hρ, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨hT, hi⟩, h⟩ := h
  refine ⟨hT, hi, ?_⟩
  split at h
  · rename_i r hr
    split at h
    · rename_i n hn
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨r, n, hr, hn, ncCopy_spec h.1, h.2⟩
    · cases h
  · cases h

theorem roleOK_ncThen {i : Nat} (h : c.roleOK b B segs rs inT j x = true) (hw : c.g.value? x = some w)
    (hρ : c.roleOf rs x = .ncThen i) :
    inT = true ∧ i = j ∧ ∃ r n, rs[i]? = some r ∧ r.nc = some n ∧
      NcCopy c B segs j n x r.sp.mem := by
  unfold Ctx.roleOK at h
  rw [hw] at h
  simp only [hρ, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hT, hi⟩, h⟩ := h
  refine ⟨hT, hi, ?_⟩
  split at h
  · rename_i r hr
    split at h
    · rename_i n hn
      exact ⟨r, n, hr, hn, ncCopy_spec h⟩
    · cases h
  · cases h

end

end GoFV.Proof.WB

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

/-- `copyOK` as a proposition. -/
def CopyP (c : WBCheck.Ctx) (B : Block) (segs : List ID) (j : Nat) (nc ncEnd : Option ID)
    (s y m : ID) : Prop :=
  ∃ u w, c.f.value? s = some u ∧ c.g.value? y = some w ∧ w.op = u.op ∧ w.type = u.type ∧
    w.aux = u.aux ∧ w.auxInt = u.auxInt ∧ w.args.size = u.args.size ∧
    w.args.back? = some m ∧ c.tabs.ty w.type = .mem ∧
    ∀ i, i < u.args.size - 1 →
      (nc = some u.args[i]! ∧ i = 0 → w.args[i]! = ncEnd.getD u.args[i]!) ∧
      (¬ (nc = some u.args[i]! ∧ i = 0) → w.args[i]! = u.args[i]! ∧
        c.availIn B segs j u.args[i]! = true)

theorem copy_spec {B : Block} {segs : List ID} {j : Nat} {nc ncEnd : Option ID} {s y m : ID}
    (h : c.copyOK B segs j nc ncEnd s y m = true) : CopyP c B segs j nc ncEnd s y m := by
  unfold Ctx.copyOK at h
  split at h
  · rename_i u w hu hw
    simp only [Bool.and_eq_true, beq_iff_eq, and_assoc, List.all_eq_true, List.mem_range] at h
    obtain ⟨hop, hty, haux, hai, hsz, hback, hmt, hall⟩ := h
    refine ⟨u, w, hu, hw, hop, hty, haux, hai, hsz, hback, ?_, fun i hi => ?_⟩
    · unfold tyIs isMemTy at hmt; split at hmt <;> simp_all
    · have := hall i hi
      by_cases hc : nc = some u.args[i]! ∧ i = 0
      · rw [if_pos (by simp [hc.1, hc.2])] at this
        exact ⟨fun _ => by simpa using this, fun h' => absurd hc h'⟩
      · rw [if_neg (by simpa [and_comm] using hc)] at this
        simp only [Bool.and_eq_true, beq_iff_eq] at this
        exact ⟨fun h' => absurd h' hc, fun _ => this⟩
  · cases h

theorem roleOK_tgt {i k : Nat} (h : c.roleOK b B segs rs inT j x = true) (hw : c.g.value? x = some w)
    (hρ : c.roleOf rs x = .tgt i k) :
    inT = false ∧ j = i + 1 ∧ ∃ r s, rs[i]? = some r ∧ r.src[k]? = some s ∧ r.tgt[k]? = some x ∧
      CopyP c B segs j r.nc r.ncEnd s x (match k with | 0 => r.phi | k' + 1 => r.tgt[k']!) ∧
      c.roleOf rs (match k with | 0 => r.phi | k' + 1 => r.tgt[k']!) =
        (match k with | 0 => .phi i | k' + 1 => .tgt i k') := by
  unfold Ctx.roleOK at h
  rw [hw] at h
  simp only [hρ, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨hT, hi⟩, h⟩ := h
  refine ⟨hT, hi, ?_⟩
  split at h
  · rename_i r hr
    split at h
    · rename_i s y hs hy
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨rfl, hc⟩, hrole⟩ := h
      refine ⟨r, s, hr, hs, hy, ?_, ?_⟩
      · rcases k with _ | k <;> simpa using copy_spec hc
      · rcases k with _ | k <;> simpa using hrole
    · cases h
  · cases h

theorem roleOK_wb {i : Nat} (h : c.roleOK b B segs rs inT j x = true) (hw : c.g.value? x = some w)
    (hρ : c.roleOf rs x = .wb i) :
    inT = true ∧ i = j ∧ ∃ r, rs[i]? = some r ∧ w.args = #[r.sp.mem] ∧
      w.auxInt.toInt.toNat = r.wbN ∧ 0 < r.wbN ∧ r.wbN ≤ 8 ∧
      ∃ e, c.tabs.ty w.type = .tuple [.ptr e, .mem] := by
  unfold Ctx.roleOK at h
  rw [hw] at h
  simp only [hρ, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hT, hi⟩, h⟩ := h
  refine ⟨hT, hi, ?_⟩
  split at h
  · rename_i r hr
    simp only [Bool.and_eq_true, beq_iff_eq, and_assoc, decide_eq_true_eq] at h
    obtain ⟨ha, hn, h0, h8, -, hty⟩ := h
    refine ⟨r, hr, ha, hn, h0, h8, ?_⟩
    split at hty
    · exact ⟨_, ‹_›⟩
    · cases hty
  · cases h

theorem roleOK_sel {i : Nat} (h : c.roleOK b B segs rs inT j x = true) (hw : c.g.value? x = some w)
    (hρ : c.roleOf rs x = .sel0 i ∨ c.roleOf rs x = .sel1 i) :
    inT = true ∧ i = j ∧ w.args = #[w.args[0]!] ∧ c.roleOf rs w.args[0]! = .wb i ∧
      (c.roleOf rs x = .sel0 i → isPtrTy (c.tabs.ty w.type) = true) ∧
      (c.roleOf rs x = .sel1 i → c.tabs.ty w.type = .mem) := by
  unfold Ctx.roleOK at h
  rw [hw] at h
  rcases hρ with hρ | hρ
  · simp only [hρ, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
    obtain ⟨hT, hi, hsz, hty, hr⟩ := h
    refine ⟨hT, hi, ?_, hr, fun _ => hty, fun h' => (by rw [hρ] at h'; cases h')⟩
    rcases hw' : w.args with ⟨_ | ⟨a, _ | ⟨_, _⟩⟩⟩ <;> simp_all
  · simp only [hρ, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
    obtain ⟨hT, hi, hsz, hty, hr⟩ := h
    refine ⟨hT, hi, ?_, hr, fun h' => (by rw [hρ] at h'; cases h'), fun _ => ?_⟩
    · rcases hw' : w.args with ⟨_ | ⟨a, _ | ⟨_, _⟩⟩⟩ <;> simp_all
    · unfold tyIs isMemTy at hty; split at hty <;> simp_all

theorem roleOK_off {i : Nat} (h : c.roleOK b B segs rs inT j x = true) (hw : c.g.value? x = some w)
    (hρ : c.roleOf rs x = .off i) :
    inT = true ∧ i = j ∧ w.args = #[w.args[0]!] ∧ isPtrTy (c.tabs.ty w.type) = true ∧
      c.roleOf rs w.args[0]! = .sel0 i ∧ ∃ r, rs[i]? = some r ∧ 0 ≤ w.auxInt.toInt ∧
        w.auxInt.toInt % 8 = 0 ∧ w.auxInt.toInt / 8 < r.wbN := by
  unfold Ctx.roleOK at h
  rw [hw] at h
  simp only [hρ, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨hT, hi, hsz, hty, hr, h⟩ := h
  refine ⟨hT, hi, ?_, hty, hr, ?_⟩
  · rcases hw' : w.args with ⟨_ | ⟨a, _ | ⟨_, _⟩⟩⟩ <;> simp_all
  · split at h
    · rename_i r hr'
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      exact ⟨r, hr', h.1.1, h.1.2, h.2⟩
    · cases h

theorem roleOK_bstore {i : Nat} (h : c.roleOK b B segs rs inT j x = true)
    (hw : c.g.value? x = some w) (hρ : c.roleOf rs x = .bstore i) :
    inT = true ∧ i = j ∧ w.args = #[w.args[0]!, w.args[1]!, w.args[2]!] ∧
      c.tabs.ty w.type = .mem ∧ Sem.auxTy c.tabs w.aux = .int .w64 ∧
      c.roleOf rs w.args[0]! = .off i ∧
      (∃ r, rs[i]? = some r ∧ (c.runArg B segs j r w.args[1]! = true ∨
        c.roleOf rs w.args[1]! = .tload i)) ∧
      (c.roleOf rs w.args[2]! = .sel1 i ∨ c.roleOf rs w.args[2]! = .bstore i) := by
  unfold Ctx.roleOK at h
  rw [hw] at h
  simp only [hρ, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨hT, hi, hsz, hty, haux, ho, hv, hm⟩ := h
  refine ⟨hT, hi, ?_, ?_, ?_, ho, ?_, ?_⟩
  · rcases hw' : w.args with ⟨_ | ⟨a, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp_all
  · unfold tyIs isMemTy at hty; split at hty <;> simp_all
  · split at haux
    · assumption
    · cases haux
  · split at hv
    · rename_i r hr
      simp only [Bool.or_eq_true, beq_iff_eq] at hv
      exact ⟨r, hr, hv⟩
    · cases hv
  · split at hm
    · rename_i k hk; simp at hm; subst hm; exact .inl hk
    · rename_i k hk; simp at hm; subst hm; exact .inr hk
    · cases hm

theorem roleOK_tload {i : Nat} (h : c.roleOK b B segs rs inT j x = true)
    (hw : c.g.value? x = some w) (hρ : c.roleOf rs x = .tload i) :
    inT = true ∧ i = j ∧ w.args = #[w.args[0]!, w.args[1]!] ∧
      ∃ r, rs[i]? = some r ∧ (c.runArg B segs j r w.args[0]! = true ∨
        c.roleOf rs w.args[0]! = .ncThen i) ∧
      (w.args[1]! = r.sp.mem ∨ c.roleOf rs w.args[1]! = .sel1 i ∨
        c.roleOf rs w.args[1]! = .bstore i) := by
  unfold Ctx.roleOK at h
  rw [hw] at h
  simp only [hρ, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨hT, hi, hsz, h⟩ := h
  refine ⟨hT, hi, ?_, ?_⟩
  · rcases hw' : w.args with ⟨_ | ⟨a, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;> simp_all
  · split at h
    · rename_i r hr
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
      refine ⟨r, hr, h.1, ?_⟩
      rcases h.2 with h2 | h2
      · exact .inl h2
      · split at h2
        · rename_i k hk; simp at h2; subst h2; exact .inr (.inl hk)
        · rename_i k hk; simp at h2; subst h2; exact .inr (.inr hk)
        · cases h2
    · cases h

end

/-! ## Roles and ops -/

/-- The run index and op of a buffer-block role. -/
def thenOp : Role → Option (Nat × Op)
  | .ncThen j => some (j, .NilCheck)
  | .wb j => some (j, .WB)
  | .sel0 j => some (j, .Select0)
  | .sel1 j => some (j, .Select1)
  | .off j => some (j, .OffPtr)
  | .bstore j => some (j, .Store)
  | .tload j => some (j, .Load)
  | _ => none

theorem roleRun_then {g : Func} {x : ID} :
    ∀ {rs : List Run} {k j : Nat} {o : Op} {ρ : Role}, roleRun g x rs k = ρ →
      thenOp ρ = some (j, o) → k ≤ j ∧ ∃ r, rs[j - k]? = some r ∧ x ∈ vals g r.sp.t ∧
        ∃ w, g.value? x = some w ∧ w.op = o
  | [], k, j, o, ρ, h, ht => by subst h; simp [roleRun, thenOp] at ht
  | r :: rs, k, j, o, ρ, h, ht => by
    unfold roleRun at h
    split at h
    · subst h; simp [thenOp] at ht
    split at h
    · subst h; simp [thenOp] at ht
    split at h
    · subst h; simp [thenOp] at ht
    split at h
    · subst h; simp [thenOp] at ht
    split at h
    · subst h; simp [thenOp] at ht
    split at h
    · rename_i hx
      split at h
      · rename_i v hv
        have hx' : x ∈ vals g r.sp.t := by simpa using hx
        split at h
        · rename_i hop
          subst h; simp only [thenOp, Option.some.injEq, Prod.mk.injEq] at ht
          obtain ⟨rfl, rfl⟩ := ht
          exact ⟨le_refl _, r, by simp, hx', v, hv, by simpa using hop⟩
        split at h
        · rename_i hop
          subst h; simp only [thenOp, Option.some.injEq, Prod.mk.injEq] at ht
          obtain ⟨rfl, rfl⟩ := ht
          exact ⟨le_refl _, r, by simp, hx', v, hv, by simpa using hop⟩
        split at h
        · rename_i hop
          subst h; simp only [thenOp, Option.some.injEq, Prod.mk.injEq] at ht
          obtain ⟨rfl, rfl⟩ := ht
          exact ⟨le_refl _, r, by simp, hx', v, hv, by simpa using hop⟩
        split at h
        · rename_i hop
          subst h; simp only [thenOp, Option.some.injEq, Prod.mk.injEq] at ht
          obtain ⟨rfl, rfl⟩ := ht
          exact ⟨le_refl _, r, by simp, hx', v, hv, by simpa using hop⟩
        split at h
        · rename_i hop
          subst h; simp only [thenOp, Option.some.injEq, Prod.mk.injEq] at ht
          obtain ⟨rfl, rfl⟩ := ht
          exact ⟨le_refl _, r, by simp, hx', v, hv, by simpa using hop⟩
        split at h
        · rename_i hop
          subst h; simp only [thenOp, Option.some.injEq, Prod.mk.injEq] at ht
          obtain ⟨rfl, rfl⟩ := ht
          exact ⟨le_refl _, r, by simp, hx', v, hv, by simpa using hop⟩
        split at h
        · rename_i hop
          subst h; simp only [thenOp, Option.some.injEq, Prod.mk.injEq] at ht
          obtain ⟨rfl, rfl⟩ := ht
          exact ⟨le_refl _, r, by simp, hx', v, hv, by simpa using hop⟩
        · subst h; simp [thenOp] at ht
      · subst h; simp [thenOp] at ht
    · obtain ⟨hk, r', hr', hx, w, hw, ho⟩ := roleRun_then h ht
      refine ⟨by omega, r', ?_, hx, w, hw, ho⟩
      rw [show j - k = (j - (k + 1)) + 1 by omega]
      simpa using hr'

/-- A buffer-block role is found among the runs. -/
theorem roleOf_then {c : WBCheck.Ctx} {rs : List Run} {x : ID} {j : Nat} {o : Op} {ρ : Role}
    (h : c.roleOf rs x = ρ) (ht : thenOp ρ = some (j, o)) :
    ∃ r, rs[j]? = some r ∧ x ∈ vals c.g r.sp.t ∧ ∃ w, c.g.value? x = some w ∧ w.op = o := by
  unfold Ctx.roleOf at h
  split at h
  · subst h; simp [thenOp] at ht
  split at h
  · subst h; simp [thenOp] at ht
  split at h
  · subst h; simp [thenOp] at ht
  generalize hR : roleRun c.g x rs 0 = R at h
  cases R
  case none =>
    split at h
    · split at h
      · subst h; simp [thenOp] at ht
      split at h
      · subst h; simp [thenOp] at ht
      · subst h; simp [thenOp] at ht
    · subst h; simp [thenOp] at ht
  all_goals
    subst h
    obtain ⟨-, r, hr, hx, w, hw, ho⟩ := roleRun_then hR ht
    exact ⟨r, by simpa using hr, hx, w, hw, ho⟩

/-- A held value's role is `held`, or the flag address or constant. -/
theorem role_of_held {c : WBCheck.Ctx} {rs : List Run} {a : ID} (h : c.held a = true) :
    c.roleOf rs a = .held ∨ c.roleOf rs a = .wbaddr ∨ c.roleOf rs a = .const0 := by
  unfold Ctx.roleOf
  split
  · exact .inr (.inl rfl)
  split
  · exact .inr (.inr rfl)
  split
  · exact .inl rfl
  · contradiction

theorem roleOf_wbaddr {c : WBCheck.Ctx} {rs : List Run} {a : ID} (h : c.isWbaddr a = true) :
    c.roleOf rs a = .wbaddr := by
  unfold Ctx.roleOf; rw [if_pos h]

theorem roleOf_const0 {c : WBCheck.Ctx} {rs : List Run} {a : ID} (h : c.isConst0 a = true)
    (hne : c.isWbaddr a = false) : c.roleOf rs a = .const0 := by
  unfold Ctx.roleOf
  rw [if_neg (by simp [hne]), if_pos h]

end GoFV.Proof.WB

import GoFV.Proof.Pass.WBAll
import GoFV.Proof.Pass.WBEnter

/-!
# writebarrier: the blocks of a chain and the arguments of their values (issue #36)

The blocks of the chain of block `b` (segments `segsOf b rs`, buffer blocks `r.sp.t`): listed,
distinct, with schedules, the split blocks' `If` on the run's flag, the last block with `b`'s
terminator (`seg_block`, `t_block`, `split_block`, `last_block`). Which values are listed where
(`held_seg`, `held_t`, `lazy_entry`, `avail_not_seg`, `avail_not_t`), the `Phi`s of the
segments (`phi_seg0`, `phi_seg`, `t_nophi`), and the arguments of a segment's or buffer
block's values that are not listed there: available at its entry (`Avail`, `args_seg`,
`args_t`).
-/

namespace GoFV.Proof.WB

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.WBCheck GoFV.Proof

/-- Held values outside `B` that are arguments of `B`'s non-`Phi` values have registers in
`Gr`. -/
def OutDef (c : WBCheck.Ctx) (B : Block) (Gr : Frame) : Prop :=
  ∀ a, c.held a = true → a ∉ B.values →
    (∃ y ∈ B.values, ∃ u, c.f.value? y = some u ∧ u.op ≠ .Phi ∧ a ∈ u.args) →
      ∃ z, Gr.regs[a]? = some (some z)

/-- The registers available at the entry of segment `k` of the chain of `b`: held values outside
`B` that `Gr` holds, the values of the earlier segments, and (when `b` is not the entry) the flag
address, the constant and the `SB` the flag address reads. -/
def Avail (c : WBCheck.Ctx) (b : ID) (B : Block) (rs : List Run) (Gr : Frame) (k : Nat)
    (a : ID) : Prop :=
  (c.held a = true ∧ a ∉ B.values ∧ ∃ y, Gr.regs[a]? = some (some y)) ∨
  (∃ j, j < k ∧ InSeg c b rs j a) ∨
  (b ≠ c.f.entry ∧ (c.isWbaddr a = true ∨ c.isConst0 a = true ∨ c.isSb a = true))

theorem vals_of {h : Func} {s : ID} {C : Block} (hC : h.block? s = some C) :
    vals h s = C.values := by
  unfold vals; rw [hC]; rfl

/-! ## Generic helpers -/

private theorem mapM_some_of_mem {α β : Type} {F : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM F = some l' → ∀ a ∈ l, ∃ b, F a = some b
  | [], _, _, _, ha => absurd ha List.not_mem_nil
  | x :: l, l', h, a, ha => by
    rw [List.mapM_cons] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨b, hb, l'', hl, rfl⟩ := h
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨b, hb⟩
    · exact mapM_some_of_mem hl a ha

private theorem sameV_op {u w : Value} (h : sameV u w = true) : u.op = w.op ∧ u.args = w.args := by
  unfold sameV at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨-, hop⟩, -⟩, -⟩, -⟩, hargs⟩ := h
  exact ⟨hop, hargs⟩

/-- The roles `roleRun` may return. -/
private def isRunRole : Role → Bool
  | .held | .wbaddr | .const0 | .lazy | .invalid => false
  | _ => true

private theorem thenRole_isRun {v : Value} {j : Nat} : isRunRole (thenRole v j) = true := by
  unfold thenRole
  repeat' split
  all_goals rfl

private theorem roleRun_isRun {g : Func} {x : ID} :
    ∀ {rs : List Run} {k : Nat}, isRunRole (roleRun g x rs k) = true
  | [], _ => rfl
  | r :: rs, k => by
    rw [roleRun]
    split
    · rfl
    split
    · rfl
    split
    · rfl
    split
    · rfl
    split
    · rfl
    · split
      · cases g.value? x with
        | none => rfl
        | some v => exact thenRole_isRun
      · split
        · rfl
        · exact roleRun_isRun

private theorem otherRole_cases {g : Func} {x : ID} :
    otherRole g x = .invalid ∨ otherRole g x = .lazy ∨ otherRole g x = .none := by
  unfold otherRole
  repeat' split
  all_goals simp

private theorem roleOf_nonrun {c : WBCheck.Ctx} {rs : List Run} {x : ID}
    (h : isRunRole (c.roleOf rs x) = false) :
    c.isWbaddr x = true ∨ c.isConst0 x = true ∨ c.roleOf rs x = .held ∨
      c.roleOf rs x = otherRole c.g x := by
  by_cases h1 : c.isWbaddr x = true
  · exact .inl h1
  by_cases h2 : c.isConst0 x = true
  · exact .inr (.inl h2)
  by_cases h3 : c.held x = true
  · right; right; left
    unfold Ctx.roleOf; rw [if_neg h1, if_neg h2, if_pos h3]
  right; right; right
  unfold Ctx.roleOf at h ⊢
  rw [if_neg h1, if_neg h2, if_neg h3] at h ⊢
  have hRun := roleRun_isRun (g := c.g) (x := x) (rs := rs) (k := 0)
  generalize roleRun c.g x rs 0 = R at h hRun ⊢
  cases R
  case none => rfl
  all_goals first | (cases h; done) | (cases hRun; done)

private theorem roleOf_wbaddr' {c : WBCheck.Ctx} {rs : List Run} {x : ID}
    (h : c.roleOf rs x = .wbaddr) : c.isWbaddr x = true := by
  rcases roleOf_nonrun (c := c) (rs := rs) (x := x) (by rw [h]; rfl) with h1 | h2 | h3 | h4
  · exact h1
  · by_cases h1 : c.isWbaddr x = true
    · exact h1
    · unfold Ctx.roleOf at h; rw [if_neg h1, if_pos h2] at h; cases h
  · rw [h] at h3; cases h3
  · rw [h] at h4
    rcases otherRole_cases (g := c.g) (x := x) with h5 | h5 | h5 <;> rw [h5] at h4 <;> cases h4

private theorem roleOf_const0' {c : WBCheck.Ctx} {rs : List Run} {x : ID}
    (h : c.roleOf rs x = .const0) : c.isConst0 x = true := by
  rcases roleOf_nonrun (c := c) (rs := rs) (x := x) (by rw [h]; rfl) with h1 | h2 | h3 | h4
  · unfold Ctx.roleOf at h; rw [if_pos h1] at h; cases h
  · exact h2
  · rw [h] at h3; cases h3
  · rw [h] at h4
    rcases otherRole_cases (g := c.g) (x := x) with h5 | h5 | h5 <;> rw [h5] at h4 <;> cases h4

private theorem roleOf_lazy' {c : WBCheck.Ctx} {rs : List Run} {x : ID}
    (h : c.roleOf rs x = .lazy) : otherRole c.g x = .lazy := by
  rcases roleOf_nonrun (c := c) (rs := rs) (x := x) (by rw [h]; rfl) with h1 | h2 | h3 | h4
  · unfold Ctx.roleOf at h; rw [if_pos h1] at h; cases h
  · by_cases h1 : c.isWbaddr x = true
    · unfold Ctx.roleOf at h; rw [if_pos h1] at h; cases h
    · unfold Ctx.roleOf at h; rw [if_neg h1, if_pos h2] at h; cases h
  · rw [h] at h3; cases h3
  · rw [← h4, h]

private theorem otherRole_lazy_op {g : Func} {x : ID} {v : Value} (h : otherRole g x = .lazy)
    (hv : g.value? x = some v) : v.op ≠ .Phi := by
  intro hp
  unfold otherRole at h
  rw [hv] at h
  dsimp only at h
  split at h
  · cases h
  split at h
  · rename_i hc
    simp only [hp, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, reduceCtorEq, false_or,
      or_false, false_and, and_false] at hc
  · cases h

private theorem thenRole_ne_phi {v : Value} {j i : Nat} : thenRole v j ≠ .phi i := by
  intro h
  unfold thenRole at h
  repeat' split at h
  all_goals cases h

private theorem roleRun_phi {g : Func} {x : ID} :
    ∀ {rs : List Run} {k i : Nat}, roleRun g x rs k = .phi i →
      k ≤ i ∧ ∃ r, rs[i - k]? = some r ∧ x = r.phi
  | [], _, _, h => by rw [roleRun] at h; cases h
  | r :: rs, k, i, h => by
    rw [roleRun] at h
    by_cases h1 : (x == r.sp.load) = true
    · rw [if_pos h1] at h; cases h
    rw [if_neg h1] at h
    by_cases h2 : (x == r.sp.flag) = true
    · rw [if_pos h2] at h; cases h
    rw [if_neg h2] at h
    by_cases h3 : (x == r.phi) = true
    · rw [if_pos h3] at h; cases h
      exact ⟨Nat.le_refl _, r, by simp, by simpa using h3⟩
    rw [if_neg h3] at h
    by_cases h4 : (r.ncEnd == some x) = true
    · rw [if_pos h4] at h; cases h
    rw [if_neg h4] at h
    cases hk : r.tgt.idxOf? x with
    | some k' => rw [hk] at h; cases h
    | none =>
      rw [hk] at h
      dsimp only at h
      by_cases h5 : (vals g r.sp.t).contains x = true
      · rw [if_pos h5] at h
        cases hv : g.value? x with
        | none => rw [hv] at h; cases h
        | some v =>
          rw [hv] at h
          exact absurd h thenRole_ne_phi
      · rw [if_neg h5] at h
        by_cases h6 : ((vals g r.sp.c).contains x && (g.value? x).any (·.op == .Addr)) = true
        · rw [if_pos h6] at h; cases h
        rw [if_neg h6] at h
        obtain ⟨hk', r', hr', hx⟩ := roleRun_phi h
        refine ⟨by omega, r', ?_, hx⟩
        rw [show i - k = (i - (k + 1)) + 1 by omega]
        simpa using hr'

private theorem roleOf_phi {c : WBCheck.Ctx} {rs : List Run} {x : ID} {i : Nat}
    (h : c.roleOf rs x = .phi i) : ∃ r, rs[i]? = some r ∧ x = r.phi := by
  unfold Ctx.roleOf at h
  by_cases h1 : c.isWbaddr x = true
  · rw [if_pos h1] at h; cases h
  rw [if_neg h1] at h
  by_cases h2 : c.isConst0 x = true
  · rw [if_pos h2] at h; cases h
  rw [if_neg h2] at h
  by_cases h3 : c.held x = true
  · rw [if_pos h3] at h; cases h
  rw [if_neg h3] at h
  have hR : roleRun c.g x rs 0 = .phi i := by
    generalize roleRun c.g x rs 0 = R at h
    cases R
    case none =>
      rcases otherRole_cases (g := c.g) (x := x) with h5 | h5 | h5 <;>
        (dsimp only at h; rw [h5] at h; cases h)
    case phi i' => exact h
    all_goals cases h
  obtain ⟨-, r, hr, hx⟩ := roleRun_phi hR
  exact ⟨r, by simpa using hr, hx⟩

private theorem thenRole_ne_taddr {v : Value} {j i : Nat} : thenRole v j ≠ .taddr i := by
  intro h
  unfold thenRole at h
  repeat' split at h
  all_goals cases h

private theorem roleRun_taddr {g : Func} {x : ID} :
    ∀ {rs : List Run} {k i : Nat}, roleRun g x rs k = .taddr i →
      k ≤ i ∧ ∃ r, rs[i - k]? = some r ∧ x ∈ vals g r.sp.c
  | [], _, _, h => by rw [roleRun] at h; cases h
  | r :: rs, k, i, h => by
    rw [roleRun] at h
    by_cases h1 : (x == r.sp.load) = true
    · rw [if_pos h1] at h; cases h
    rw [if_neg h1] at h
    by_cases h2 : (x == r.sp.flag) = true
    · rw [if_pos h2] at h; cases h
    rw [if_neg h2] at h
    by_cases h3 : (x == r.phi) = true
    · rw [if_pos h3] at h; cases h
    rw [if_neg h3] at h
    by_cases h4 : (r.ncEnd == some x) = true
    · rw [if_pos h4] at h; cases h
    rw [if_neg h4] at h
    cases hk : r.tgt.idxOf? x with
    | some k' => rw [hk] at h; cases h
    | none =>
      rw [hk] at h
      dsimp only at h
      by_cases h5 : (vals g r.sp.t).contains x = true
      · rw [if_pos h5] at h
        cases hv : g.value? x with
        | none => rw [hv] at h; cases h
        | some v =>
          rw [hv] at h
          exact absurd h thenRole_ne_taddr
      · rw [if_neg h5] at h
        by_cases h6 : ((vals g r.sp.c).contains x && (g.value? x).any (·.op == .Addr)) = true
        · rw [if_pos h6] at h; cases h
          simp only [Bool.and_eq_true, Array.contains_iff_mem] at h6
          exact ⟨Nat.le_refl _, r, by simp, h6.1⟩
        rw [if_neg h6] at h
        obtain ⟨hk', r', hr', hx⟩ := roleRun_taddr h
        refine ⟨by omega, r', ?_, hx⟩
        rw [show i - k = (i - (k + 1)) + 1 by omega]
        simpa using hr'

/-- A type address is listed in its run's split block. -/
theorem roleOf_taddr {c : WBCheck.Ctx} {rs : List Run} {x : ID} {i : Nat}
    (h : c.roleOf rs x = .taddr i) : ∃ r, rs[i]? = some r ∧ x ∈ vals c.g r.sp.c := by
  unfold Ctx.roleOf at h
  by_cases h1 : c.isWbaddr x = true
  · rw [if_pos h1] at h; cases h
  rw [if_neg h1] at h
  by_cases h2 : c.isConst0 x = true
  · rw [if_pos h2] at h; cases h
  rw [if_neg h2] at h
  by_cases h3 : c.held x = true
  · rw [if_pos h3] at h; cases h
  rw [if_neg h3] at h
  have hR : roleRun c.g x rs 0 = .taddr i := by
    generalize roleRun c.g x rs 0 = R at h
    cases R
    case none =>
      rcases otherRole_cases (g := c.g) (x := x) with h5 | h5 | h5 <;>
        (dsimp only at h; rw [h5] at h; cases h)
    case taddr i' => exact h
    all_goals cases h
  obtain ⟨-, r, hr, hx⟩ := roleRun_taddr hR
  exact ⟨r, by simpa using hr, hx⟩

section
variable {c : WBCheck.Ctx} {b : ID} {B : Block} {segs : List ID} {rs : List Run} {inT : Bool}
  {j : Nat} {x : ID} {w : Value}

private theorem roleOK_value (h : c.roleOK b B segs rs inT j x = true) :
    ∃ w, c.g.value? x = some w := by
  unfold Ctx.roleOK at h
  split at h
  · cases h
  · exact ⟨_, ‹_›⟩

private theorem roleOK_none (h : c.roleOK b B segs rs inT j x = true)
    (hρ : c.roleOf rs x = .none) : False := by
  obtain ⟨w, hw⟩ := roleOK_value h
  unfold Ctx.roleOK at h
  rw [hw] at h
  simp only [hρ, Bool.false_eq_true] at h

/-- The roles of a value listed in a segment. -/
private theorem seg_roles (h : c.roleOK b B segs rs false j x = true)
    (hw : c.g.value? x = some w) :
    c.roleOf rs x = .held ∨
      (c.roleOf rs x = .wbaddr ∨ c.roleOf rs x = .const0 ∨ c.roleOf rs x = .lazy) ∨
      c.roleOf rs x = .invalid ∨ (∃ i, c.roleOf rs x = .load i) ∨
      (∃ i, c.roleOf rs x = .flag i) ∨ (∃ i, c.roleOf rs x = .phi i) ∨
      (∃ i, c.roleOf rs x = .ncEnd i) ∨ (∃ i k, c.roleOf rs x = .tgt i k) ∨
      ∃ i, c.roleOf rs x = .taddr i := by
  cases hρ : c.roleOf rs x with
  | ncThen i => cases (roleOK_ncThen h hw hρ).1
  | wb i => cases (roleOK_wb h hw hρ).1
  | sel0 i => cases (roleOK_sel h hw (.inl hρ)).1
  | sel1 i => cases (roleOK_sel h hw (.inr hρ)).1
  | off i => cases (roleOK_off h hw hρ).1
  | bstore i => cases (roleOK_bstore h hw hρ).1
  | tload i => cases (roleOK_tload h hw hρ).1
  | call i => cases (roleOK_call h hw hρ).1
  | seln i => cases (roleOK_seln h hw hρ).1
  | none => exact (roleOK_none h hρ).elim
  | _ => simp

/-- The roles of a value listed in a buffer block. -/
private theorem t_roles (h : c.roleOK b B segs rs true j x = true)
    (hw : c.g.value? x = some w) :
    (∃ i, c.roleOf rs x = .ncThen i) ∨ (∃ i, c.roleOf rs x = .wb i) ∨
      (∃ i, c.roleOf rs x = .sel0 i) ∨ (∃ i, c.roleOf rs x = .sel1 i) ∨
      (∃ i, c.roleOf rs x = .off i) ∨ (∃ i, c.roleOf rs x = .bstore i) ∨
      (∃ i, c.roleOf rs x = .tload i) ∨ (∃ i, c.roleOf rs x = .call i) ∨
      ∃ i, c.roleOf rs x = .seln i := by
  cases hρ : c.roleOf rs x with
  | held => cases (roleOK_held h hw hρ).1
  | wbaddr => cases (roleOK_lazy h hw (.inl hρ)).1
  | const0 => cases (roleOK_lazy h hw (.inr (.inl hρ))).1
  | lazy => cases (roleOK_lazy h hw (.inr (.inr hρ))).1
  | invalid => cases (roleOK_invalid h hw hρ).1
  | load i => cases (roleOK_load h hw hρ).1
  | flag i => cases (roleOK_flag h hw hρ).1
  | phi i => cases (roleOK_phi h hw hρ).1
  | ncEnd i => cases (roleOK_ncEnd h hw hρ).1
  | tgt i k => cases (roleOK_tgt h hw hρ).1
  | taddr i => cases (roleOK_taddr h hw hρ).1
  | none => exact (roleOK_none h hρ).elim
  | _ => simp

end

private theorem then_nophi {c : WBCheck.Ctx} {rs : List Run} {x : ID} {i : Nat} {o : Op}
    {v : Value} (ht : thenOp (c.roleOf rs x) = some (i, o)) (ho : o ≠ .Phi)
    (hv : c.g.value? x = some v) : v.op ≠ .Phi := by
  obtain ⟨-, -, -, w', hw', hop⟩ := roleOf_then ht
  rw [hv] at hw'; cases hw'
  rw [hop]; exact ho

private theorem runArg_availIn {c : WBCheck.Ctx} {B : Block} {segs : List ID} {j : Nat} {r : Run}
    {a : ID} (h : c.runArg B segs j r a = true) : c.availIn B segs j a = true := by
  unfold Ctx.runArg at h
  simp only [Bool.and_eq_true] at h
  exact h.2

private theorem seg0 {b s : ID} {rs : List Run} (hs : (segsOf b rs)[0]? = some s) : s = b := by
  simp [segsOf] at hs; exact hs.symm

namespace Setup

variable {c : WBCheck.Ctx} {b : ID} {B : Block} {rs : List Run} {l : ID}

private theorem run_ok (S : Setup c b B rs l) {j : Nat} {r : Run} (hr : rs[j]? = some r) :
    c.runOK b B (segsOf b rs) rs j r = true :=
  (blockOK_spec S.ok S.hB S.ch).2.2.2.2.1 j r hr

private theorem seg_roleOK (S : Setup c b B rs l) {j : Nat} {s x : ID}
    (hs : (segsOf b rs)[j]? = some s) (hx : x ∈ vals c.g s) :
    c.roleOK b B (segsOf b rs) rs false j x = true :=
  (blockOK_spec S.ok S.hB S.ch).2.2.2.2.2.2.1 j s hs x hx

private theorem t_roleOK (S : Setup c b B rs l) {j : Nat} {r : Run} {x : ID}
    (hr : rs[j]? = some r) (hx : x ∈ vals c.g r.sp.t) :
    c.roleOK b B (segsOf b rs) rs true j x = true := by
  obtain ⟨-, -, ⟨T, hT, -, -, -, -, -, hall⟩, -⟩ := runOK_spec (run_ok S hr)
  rw [vals_of hT] at hx
  exact hall x hx

private theorem K_eq (S : Setup c b B rs l) : c.K = keptMarks c.f c.g :=
  (ctxOf_spec S.ctx).2.2.2.1

private theorem kept_u (S : Setup c b B rs l) {x : ID} {u w : Value}
    (hK : c.K.getD x false = true) (hu : c.f.value? x = some u) (hw : c.g.value? x = some w) :
    sameV u w = true ∧ u.op = w.op ∧ u.args = w.args := by
  obtain ⟨u', w', hu', hw', hsame, -⟩ := keptMarks_spec (by rw [← K_eq S]; exact hK)
  rw [hu] at hu'; cases hu'; rw [hw] at hw'; cases hw'
  exact ⟨hsame, sameV_op hsame⟩

private theorem run_of (S : Setup c b B rs l) {j : Nat} {r : Run} (hr : rs[j]? = some r) :
    runOf? c.f c.g r.sp = some r :=
  ((chainRuns_spec S.ch).1 j r hr).2.2.2

private theorem phi_mem (S : Setup c b B rs l) {j : Nat} {r : Run} (hr : rs[j]? = some r) :
    r.phi ∈ vals c.g r.sp.e := by
  obtain ⟨-, -, -, -, -, -, h, -⟩ := runOf_spec (run_of S hr)
  exact List.mem_of_getElem? (l := (vals c.g r.sp.e).toList) (by simpa using h) |>
    Array.mem_toList_iff.1

private theorem src_op (S : Setup c b B rs l) {j k : Nat} {r : Run} {s : ID} {u : Value}
    (hr : rs[j]? = some r) (hs : r.src[k]? = some s) (hu : c.f.value? s = some u) :
    u.op ≠ .Phi := by
  obtain ⟨-, -, -, h, -⟩ := runOf_spec (run_of S hr)
  obtain ⟨u', hu', hop, -⟩ := h k s hs
  rw [hu] at hu'; cases hu'
  rcases hop with hop | hop | hop | hop | hop <;> rw [hop] <;> exact fun h => by cases h

private theorem split_new (S : Setup c b B rs l) {r : Run} (hr : r ∈ rs) :
    r.sp.t ∉ c.f.blocks ∧ r.sp.e ∉ c.f.blocks := by
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hr
  obtain ⟨-, -, hsp, -⟩ := (chainRuns_spec S.ch).1 j r hj
  obtain ⟨-, C, -, -, -, -, -, ht, he, -⟩ := splitOf_spec hsp
  exact ⟨ht, he⟩

theorem listed_once (S : Setup c b B rs l) {s s' a : ID} (hs : s ∈ c.g.blocks)
    (hs' : s' ∈ c.g.blocks) (ha : a ∈ vals c.g s) (ha' : a ∈ vals c.g s') : s = s' := by
  obtain ⟨ce, hg⟩ := S.wg
  obtain ⟨C, hC, -⟩ := hg.blockId s hs
  obtain ⟨C', hC', -⟩ := hg.blockId s' hs'
  rw [vals_of hC] at ha
  rw [vals_of hC'] at ha'
  exact hg.valueOnce s C s' C' ⟨hs, hC⟩ ⟨hs', hC'⟩ a ha ha'

theorem segs_length (b : ID) (rs : List Run) : (segsOf b rs).length = rs.length + 1 := by
  simp [segsOf]

theorem seg_block (S : Setup c b B rs l) {k : Nat} {s : ID} (hs : (segsOf b rs)[k]? = some s) :
    ∃ C, c.g.block? s = some C ∧ C.id = s ∧ s ∈ c.g.blocks ∧ ∃ o, schedule c.g C = some o := by
  have bo := blockOK_spec S.ok S.hB S.ch
  have hmem : s ∈ segsOf b rs := List.mem_of_getElem? hs
  have hsb : s ∈ c.g.blocks := bo.2.2.2.1 s (List.mem_append_left _ hmem)
  obtain ⟨ce, hg⟩ := S.wg
  obtain ⟨C, hC, hid⟩ := hg.blockId s hsb
  obtain ⟨src, k0, ks, -, hm, -⟩ := npOK_spec bo.2.2.2.2.2.2.2
  obtain ⟨l', hl'⟩ := mapM_some_of_mem hm s hmem
  obtain ⟨C', o, hC', ho, -⟩ := keptNP_spec hl'
  rw [hC] at hC'; cases hC'
  exact ⟨C, hC, hid, hsb, o, ho⟩

theorem run_seg (S : Setup c b B rs l) {j : Nat} {r : Run} (hr : rs[j]? = some r) :
    (segsOf b rs)[j]? = some r.sp.c ∧ (segsOf b rs)[j + 1]? = some r.sp.e := by
  obtain ⟨h1, h2, -⟩ := runOK_spec (run_ok S hr)
  exact ⟨h1, h2⟩

theorem t_block (S : Setup c b B rs l) {j : Nat} {r : Run} (hr : rs[j]? = some r) :
    ∃ T, c.g.block? r.sp.t = some T ∧ T.id = r.sp.t ∧ r.sp.t ∈ c.g.blocks ∧ T.kind = .Plain ∧
      T.succs = #[⟨r.sp.e, 1⟩] ∧ ∃ o, schedule c.g T = some o := by
  obtain ⟨-, -, ⟨T, hT, hid, hk, hsu, hnp, -, -⟩, -⟩ := runOK_spec (run_ok S hr)
  have hmem : r.sp.t ∈ c.g.blocks := (blockOK_spec S.ok S.hB S.ch).2.2.2.1 _
    (List.mem_append_right _ (List.mem_map.2 ⟨r, List.mem_of_getElem? hr, rfl⟩))
  obtain ⟨o, ho⟩ : ∃ o, schedule c.g T = some o := by
    unfold Ctx.npSeq at hnp
    cases ho : schedule c.g T with
    | none => rw [ho] at hnp; cases hnp
    | some o => exact ⟨o, rfl⟩
  exact ⟨T, hT, hid, hmem, hk, hsu, o, ho⟩

theorem split_block (S : Setup c b B rs l) {j : Nat} {r : Run} (hr : rs[j]? = some r) :
    ∃ C, c.g.block? r.sp.c = some C ∧ C.kind = .If ∧ C.controls = #[r.sp.flag] ∧
      C.succs = #[⟨r.sp.t, 0⟩, ⟨r.sp.e, 0⟩] ∧ c.roleOf rs r.sp.flag = .flag j ∧
      r.sp.flag ∈ vals c.g r.sp.c := by
  obtain ⟨-, -, hsp, -⟩ := (chainRuns_spec S.ch).1 j r hr
  obtain ⟨-, C, hC, hk, hctl, hsu, -⟩ := splitOf_spec hsp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hflag, hfr, -⟩ := runOK_spec (run_ok S hr)
  exact ⟨C, hC, hk, hctl, hsu, hfr, hflag⟩

theorem last_block (S : Setup c b B rs l) :
    ∃ L, c.g.block? l = some L ∧ (segsOf b rs)[rs.length]? = some l ∧ L.kind = B.kind ∧
      L.controls = B.controls ∧ L.succs = B.succs ∧ ∀ x ∈ B.controls, c.held x = true := by
  obtain ⟨⟨L, C0, hL, -, -, -, hk, hctl, hsu, hh⟩, hlast, -⟩ := blockOK_spec S.ok S.hB S.ch
  refine ⟨L, hL, ?_, hk, hctl, hsu, hh⟩
  rw [List.getLast?_eq_getElem?, segs_length] at hlast
  simpa using hlast

/-- Distinct positions of the chain are distinct blocks. -/
theorem seg_inj (S : Setup c b B rs l) {j j' : Nat} {s : ID} (hj : (segsOf b rs)[j]? = some s)
    (hj' : (segsOf b rs)[j']? = some s) : j = j' :=
  Order.idx_unique (List.nodup_append.1 (blockOK_spec S.ok S.hB S.ch).2.2.1).1 hj hj'

theorem seg_ne_t (S : Setup c b B rs l) {j j' : Nat} {s : ID} {r : Run}
    (hj : (segsOf b rs)[j]? = some s) (hr : rs[j']? = some r) : s ≠ r.sp.t :=
  (List.nodup_append.1 (blockOK_spec S.ok S.hB S.ch).2.2.1).2.2 s (List.mem_of_getElem? hj)
    r.sp.t (List.mem_map.2 ⟨r, List.mem_of_getElem? hr, rfl⟩)

theorem t_inj (S : Setup c b B rs l) {j j' : Nat} {r r' : Run} (hr : rs[j]? = some r)
    (hr' : rs[j']? = some r') (he : r.sp.t = r'.sp.t) : j = j' := by
  have hnd := (List.nodup_append.1 (blockOK_spec S.ok S.hB S.ch).2.2.1).2.1
  have h1 : (rs.map (·.sp.t))[j]? = some r.sp.t := by rw [List.getElem?_map, hr]; rfl
  have h2 : (rs.map (·.sp.t))[j']? = some r.sp.t := by rw [List.getElem?_map, hr', he]; rfl
  exact Order.idx_unique hnd h1 h2

/-- Held values listed in a segment are values of `B`. -/
theorem held_seg (S : Setup c b B rs l) {j : Nat} {a : ID} (h : InSeg c b rs j a)
    (hh : c.held a = true) : a ∈ B.values := by
  obtain ⟨s, hs, hx⟩ := h
  have hok := seg_roleOK S hs hx
  obtain ⟨w, hw⟩ := roleOK_value hok
  rcases role_of_held (rs := rs) hh with hρ | hρ | hρ
  · exact (roleOK_held hok hw hρ).2.1
  · exact (roleOK_lazy hok hw (.inl hρ)).2.2.2.1 hh
  · exact (roleOK_lazy hok hw (.inr (.inl hρ))).2.2.2.1 hh

/-- No held value is listed in a buffer block. -/
theorem held_t (S : Setup c b B rs l) {j : Nat} {a : ID} (h : InT c rs j a)
    (hh : c.held a = true) : False := by
  obtain ⟨r, hr, hx⟩ := h
  have hok := t_roleOK S hr hx
  obtain ⟨w, hw⟩ := roleOK_value hok
  rcases role_of_held (rs := rs) hh with hρ | hρ | hρ
  · cases (roleOK_held hok hw hρ).1
  · cases (roleOK_lazy hok hw (.inl hρ)).1
  · cases (roleOK_lazy hok hw (.inr (.inl hρ))).1

/-- The flag address and constant are listed in `g`'s entry, which is `f`'s. -/
theorem lazy_entry (S : Setup c b B rs l) {wa c0 : ID} (hz : c.lazy = some (wa, c0)) :
    wa ∈ vals c.g c.f.entry ∧ c0 ∈ vals c.g c.f.entry ∧ c.f.entry ∈ c.g.blocks := by
  obtain ⟨-, -, -, -, -, hl⟩ := ctxOf_spec S.ctx
  rw [hz] at hl
  obtain ⟨-, -, hwa, hc0, -⟩ := lazyOK_some hl
  obtain ⟨ce, hg⟩ := S.wg
  rw [S.entry] at hwa hc0
  exact ⟨hwa, hc0, by rw [← S.entry]; exact hg.entry⟩

/-- The flag address or constant: listed in the entry, an `Addr` or a `Const32`. -/
private theorem lazy_info (S : Setup c b B rs l) {a : ID}
    (hl : c.isWbaddr a = true ∨ c.isConst0 a = true) :
    a ∈ vals c.g c.f.entry ∧ c.f.entry ∈ c.g.blocks ∧
      ∃ w, c.g.value? a = some w ∧ (w.op = .Addr ∨ w.op = .Const32) := by
  unfold Ctx.isWbaddr Ctx.isConst0 at hl
  cases hz : c.lazy with
  | none => rw [hz] at hl; simp at hl
  | some p =>
    obtain ⟨wa, c0⟩ := p
    rw [hz] at hl
    obtain ⟨h1, h2, h3⟩ := lazy_entry S hz
    obtain ⟨-, -, -, -, -, hlz⟩ := ctxOf_spec S.ctx
    rw [hz] at hlz
    obtain ⟨⟨w1, hw1, hop1, -⟩, ⟨w2, hw2, hop2, -⟩, -⟩ := lazyOK_some hlz
    simp only [Option.any_some, beq_iff_eq] at hl
    rcases hl with rfl | rfl
    · exact ⟨h1, h3, w1, hw1, .inl hop1⟩
    · exact ⟨h2, h3, w2, hw2, .inr hop2⟩

/-- The `SB` the flag address reads: an argument-free `SB` listed in the entry. -/
theorem sb_entry (S : Setup c b B rs l) {a : ID} (hl : c.isSb a = true) :
    a ∈ vals c.g c.f.entry ∧ ∃ v, c.g.value? a = some v ∧ v.op = .SB ∧ v.args = #[] := by
  unfold Ctx.isSb Ctx.sbOf at hl
  cases hz : c.lazy with
  | none => rw [hz] at hl; simp at hl
  | some p =>
    obtain ⟨wa, c0⟩ := p
    rw [hz] at hl
    obtain ⟨-, -, -, -, -, hlz⟩ := ctxOf_spec S.ctx
    rw [hz] at hlz
    obtain ⟨⟨w1, hw1, -, -, -, -, hmem, hsb⟩, -⟩ := lazyOK_some hlz
    simp only [Option.bind_some, hw1, beq_iff_eq] at hl
    rw [getElem!_def, hl] at hmem hsb
    rw [← S.entry]; exact ⟨hmem, hsb⟩

/-- The flag address, constant or `SB`: listed in the entry. -/
theorem entry_mem (S : Setup c b B rs l) {a : ID}
    (hl : c.isWbaddr a = true ∨ c.isConst0 a = true ∨ c.isSb a = true) :
    a ∈ vals c.g c.f.entry ∧ c.f.entry ∈ c.g.blocks := by
  rcases hl with hl | hl | hl
  · obtain ⟨hm, he, -⟩ := lazy_info S (.inl hl); exact ⟨hm, he⟩
  · obtain ⟨hm, he, -⟩ := lazy_info S (.inr hl); exact ⟨hm, he⟩
  · obtain ⟨ce, hg⟩ := S.wg
    exact ⟨(sb_entry S hl).1, by rw [← S.entry]; exact hg.entry⟩

/-- When `b` is not the entry, no block of its chain is `g`'s entry. -/
theorem entry_not_chain (S : Setup c b B rs l) (hb : b ≠ c.f.entry) :
    ∀ s ∈ segsOf b rs ++ rs.map (·.sp.t), s ≠ c.f.entry := by
  intro s hs he
  obtain ⟨ce, hf⟩ := S.wf
  have hent := hf.entry
  rcases List.mem_append.1 hs with hs | hs
  · unfold segsOf at hs
    rcases List.mem_cons.1 hs with h | h
    · exact hb (h ▸ he)
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h
      exact (split_new S hr).2 (he ▸ hent)
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hs
    exact (split_new S hr).1 (he ▸ hent)

/-- An available register is not listed in segment `k`. -/
theorem avail_not_seg (S : Setup c b B rs l) {Gr : Frame} {k : Nat} {s a : ID}
    (hs : (segsOf b rs)[k]? = some s) (ha : Avail c b B rs Gr k a) : a ∉ vals c.g s := by
  intro hx
  obtain ⟨-, -, -, hsb, -⟩ := seg_block S hs
  rcases ha with ⟨hh, hnB, -⟩ | ⟨j, hj, s', hs', hx'⟩ | ⟨hb, hl⟩
  · exact hnB (held_seg S ⟨s, hs, hx⟩ hh)
  · obtain ⟨-, -, -, hsb', -⟩ := seg_block S hs'
    have he := listed_once S hsb hsb' hx hx'
    subst he
    have := seg_inj S hs hs'
    omega
  · obtain ⟨hm, he⟩ := entry_mem S hl
    exact entry_not_chain S hb s (List.mem_append_left _ (List.mem_of_getElem? hs))
      (listed_once S hsb he hx hm)

/-- A register available after segment `k` is not listed in run `k`'s buffer block. -/
theorem avail_not_t (S : Setup c b B rs l) {Gr : Frame} {k : Nat} {r : Run} {a : ID}
    (hr : rs[k]? = some r) (ha : Avail c b B rs Gr (k + 1) a) : a ∉ vals c.g r.sp.t := by
  intro hx
  obtain ⟨T, hT, -, htb, -⟩ := t_block S hr
  rcases ha with ⟨hh, -, -⟩ | ⟨j, hj, s', hs', hx'⟩ | ⟨hb, hl⟩
  · exact held_t S ⟨r, hr, hx⟩ hh
  · obtain ⟨-, -, -, hsb', -⟩ := seg_block S hs'
    exact seg_ne_t S hs' hr (listed_once S hsb' htb hx' hx)
  · obtain ⟨hm, he⟩ := entry_mem S hl
    exact entry_not_chain S hb r.sp.t
      (List.mem_append_right _ (List.mem_map.2 ⟨r, List.mem_of_getElem? hr, rfl⟩))
      (listed_once S htb he hx hm)

/-- A value listed in no block of the chain has no role of a run. -/
private theorem roleRun_unlisted (S : Setup c b B rs l) {x : ID}
    (hx : ∀ s ∈ segsOf b rs ++ rs.map (·.sp.t), x ∉ vals c.g s) :
    ∀ (rs' : List Run) (k : Nat), (∀ r ∈ rs', r ∈ rs) → roleRun c.g x rs' k = .none
  | [], _, _ => rfl
  | r :: rs', k, hsub => by
    have hr : r ∈ rs := hsub r List.mem_cons_self
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hr
    obtain ⟨h1, h2, -, -, -, -, -, -, htgt, hncE, hload, hflag, -⟩ := runOK_spec (run_ok S hj)
    have hc : x ∉ vals c.g r.sp.c := hx _ (List.mem_append_left _ (List.mem_of_getElem? h1))
    have he : x ∉ vals c.g r.sp.e := hx _ (List.mem_append_left _ (List.mem_of_getElem? h2))
    have ht : x ∉ vals c.g r.sp.t :=
      hx _ (List.mem_append_right _ (List.mem_map.2 ⟨r, hr, rfl⟩))
    rw [roleRun, if_neg (by simp only [beq_iff_eq]; rintro rfl; exact hc hload),
      if_neg (by simp only [beq_iff_eq]; rintro rfl; exact hc hflag),
      if_neg (by simp only [beq_iff_eq]; rintro rfl; exact he (phi_mem S hj)),
      if_neg (by simp only [beq_iff_eq]; intro h; exact he (hncE x h))]
    cases hk : r.tgt.idxOf? x with
    | some k' =>
      obtain ⟨hlt, heq, -⟩ := List.idxOf?_eq_some_iff.1 hk
      exact absurd (htgt x (heq ▸ List.getElem_mem hlt)) he
    | none =>
      dsimp only
      rw [if_neg (by rw [Array.contains_iff_mem]; exact ht),
        if_neg (by simp only [Bool.and_eq_true, Array.contains_iff_mem]; exact fun h => hc h.1)]
      exact roleRun_unlisted S hx rs' (k + 1) fun r' hr' => hsub r' (List.mem_cons_of_mem _ hr')

/-- The `SB` the flag address reads, outside the entry's chain: the flag address, the constant,
held, or lazy. -/
theorem sb_role (S : Setup c b B rs l) (hb : b ≠ c.f.entry) {a : ID} (hl : c.isSb a = true) :
    c.isWbaddr a = true ∨ c.isConst0 a = true ∨ (c.held a = true ∧ c.roleOf rs a = .held) ∨
      c.roleOf rs a = .lazy := by
  obtain ⟨haE, v, hv, hop, hargs⟩ := sb_entry S hl
  by_cases h1 : c.isWbaddr a = true
  · exact .inl h1
  by_cases h2 : c.isConst0 a = true
  · exact .inr (.inl h2)
  right; right
  unfold Ctx.roleOf
  rw [if_neg h1, if_neg h2]
  by_cases h3 : c.held a = true
  · left; exact ⟨h3, by rw [if_pos h3]⟩
  right
  have hEg : c.f.entry ∈ c.g.blocks := (entry_mem S (.inr (.inr hl))).2
  have hun : ∀ s ∈ segsOf b rs ++ rs.map (·.sp.t), a ∉ vals c.g s := fun s hs has =>
    entry_not_chain S hb s hs (listed_once S
      ((blockOK_spec S.ok S.hB S.ch).2.2.2.1 s hs) hEg has haE)
  rw [if_neg h3, roleRun_unlisted S hun rs 0 fun _ h => h]
  dsimp only
  unfold otherRole
  rw [hv]
  simp [hop, hargs]

/-- The `Phi`s of the first segment are kept `Phi`s of `B` with held arguments. -/
theorem phi_seg0 (S : Setup c b B rs l) {s x : ID} {v : Value} (hs : (segsOf b rs)[0]? = some s)
    (hx : x ∈ vals c.g s) (hv : c.g.value? x = some v) (hp : v.op = .Phi) :
    c.roleOf rs x = .held ∧ c.K.getD x false = true ∧ x ∈ B.values ∧
      ∃ u, c.f.value? x = some u ∧ sameV u v = true ∧ ∀ a ∈ u.args, c.held a = true := by
  have hok := seg_roleOK S hs hx
  rcases seg_roles hok hv with hρ | hρ | hρ | ⟨i, hρ⟩ | ⟨i, hρ⟩ | ⟨i, hρ⟩ | ⟨i, hρ⟩ | ⟨i, k, hρ⟩ |
    ⟨i, hρ⟩
  · obtain ⟨-, hxB, hK | hK⟩ := roleOK_held hok hv hρ
    · obtain ⟨hK, u, hu, hphi, -⟩ := hK
      obtain ⟨hsame, hop, -⟩ := kept_u S hK hu hv
      exact ⟨hρ, hK, hxB, u, hu, hsame, (hphi (hop.trans hp)).2⟩
    · obtain ⟨-, j', r, hj, -⟩ := hK
      exact absurd hj (by omega)
  · exfalso
    obtain ⟨w', hw', hop⟩ : ∃ w', c.g.value? x = some w' ∧ w'.op ≠ .Phi := by
      rcases hρ with hρ | hρ | hρ
      · obtain ⟨-, -, w', hw', hop⟩ := lazy_info S (.inl (roleOf_wbaddr' hρ))
        exact ⟨w', hw', by rcases hop with hop | hop <;> rw [hop] <;> exact fun h => by cases h⟩
      · obtain ⟨-, -, w', hw', hop⟩ := lazy_info S (.inr (roleOf_const0' hρ))
        exact ⟨w', hw', by rcases hop with hop | hop <;> rw [hop] <;> exact fun h => by cases h⟩
      · exact ⟨v, hv, otherRole_lazy_op (roleOf_lazy' hρ) hv⟩
    rw [hv] at hw'; cases hw'
    exact hop hp
  · rw [(roleOK_invalid hok hv hρ).2.1] at hp; cases hp
  · obtain ⟨-, -, r, -, hop, -⟩ := roleOK_load hok hv hρ
    rw [hop] at hp; cases hp
  · obtain ⟨-, -, r, -, hop, -⟩ := roleOK_flag hok hv hρ
    rw [hop] at hp; cases hp
  · exact absurd (roleOK_phi hok hv hρ).2.1 (by omega)
  · exact absurd (roleOK_ncEnd hok hv hρ).2.1 (by omega)
  · exact absurd (roleOK_tgt hok hv hρ).2.1 (by omega)
  · obtain ⟨-, -, hop, -⟩ := roleOK_taddr hok hv hρ
    rw [hop] at hp; cases hp

/-- The only `Phi` of segment `k + 1` is run `k`'s memory `Phi`. -/
theorem phi_seg (S : Setup c b B rs l) {k : Nat} {s x : ID} {v : Value}
    (hs : (segsOf b rs)[k + 1]? = some s) (hx : x ∈ vals c.g s) (hv : c.g.value? x = some v)
    (hp : v.op = .Phi) :
    ∃ r, rs[k]? = some r ∧ x = r.phi ∧ c.roleOf rs x = .phi k ∧
      v.args = #[r.sp.mem, r.memThen] ∧ c.tabs.ty v.type = .mem ∧
      (r.memThen = r.sp.mem ∨ c.roleOf rs r.memThen = .sel1 k ∨
        c.roleOf rs r.memThen = .bstore k ∨ c.roleOf rs r.memThen = .seln k) := by
  have hok := seg_roleOK S hs hx
  rcases seg_roles hok hv with hρ | hρ | hρ | ⟨i, hρ⟩ | ⟨i, hρ⟩ | ⟨i, hρ⟩ | ⟨i, hρ⟩ | ⟨i, k', hρ⟩ |
    ⟨i, hρ⟩
  · obtain ⟨-, -, hK | hK⟩ := roleOK_held hok hv hρ
    · obtain ⟨hK, u, hu, hphi, -⟩ := hK
      obtain ⟨-, hop, -⟩ := kept_u S hK hu hv
      exact absurd (hphi (hop.trans hp)).1 (by omega)
    · obtain ⟨-, -, -, -, -, -, hop, -⟩ := hK
      rw [hop] at hp; cases hp
  · exact absurd (roleOK_lazy hok hv hρ).2.2.1 (by omega)
  · rw [(roleOK_invalid hok hv hρ).2.1] at hp; cases hp
  · obtain ⟨-, -, r, -, hop, -⟩ := roleOK_load hok hv hρ
    rw [hop] at hp; cases hp
  · obtain ⟨-, -, r, -, hop, -⟩ := roleOK_flag hok hv hρ
    rw [hop] at hp; cases hp
  · obtain ⟨-, hj, r, hr, -, hargs, hty, hmt⟩ := roleOK_phi hok hv hρ
    have hik : i = k := by omega
    subst hik
    obtain ⟨r', hr', hxr⟩ := roleOf_phi hρ
    rw [hr] at hr'; cases hr'
    exact ⟨r, hr, hxr, hρ, hargs, hty, hmt⟩
  · obtain ⟨-, -, r, n, -, -, ⟨u, w', p, mS, -, hw', -, hwop, -⟩, -⟩ := roleOK_ncEnd hok hv hρ
    rw [hv] at hw'; cases hw'
    rw [hwop] at hp; cases hp
  · obtain ⟨-, -, r, s', hr, hs', -, ⟨u, w', hu, hw', hop, -⟩, -⟩ := roleOK_tgt hok hv hρ
    rw [hv] at hw'; cases hw'
    exact (src_op S hr hs' hu (hop ▸ hp)).elim
  · obtain ⟨-, -, hop, -⟩ := roleOK_taddr hok hv hρ
    rw [hop] at hp; cases hp

/-- Run `k`'s memory is held. -/
theorem mem_held (S : Setup c b B rs l) {k : Nat} {r : Run} (hr : rs[k]? = some r) :
    c.held r.sp.mem = true ∧ c.availIn B (segsOf b rs) k r.sp.mem = true := by
  obtain ⟨h1, -, -, -, -, -, -, -, -, -, hload, hflag, hfr, hmem, -⟩ := runOK_spec (run_ok S hr)
  have hokf := seg_roleOK S h1 hflag
  obtain ⟨wf, hwf⟩ := roleOK_value hokf
  obtain ⟨-, -, r', hr', -, -, -, -, hlr⟩ := roleOK_flag hokf hwf hfr
  rw [hr] at hr'; cases hr'
  have hokl := seg_roleOK S h1 hload
  obtain ⟨wl, hwl⟩ := roleOK_value hokl
  obtain ⟨-, -, r'', hr'', -, -, -, -, hav⟩ := roleOK_load hokl hwl hlr
  rw [hr] at hr''; cases hr''
  exact ⟨hmem, hav⟩

/-- A buffer block has no `Phi`. -/
theorem t_nophi (S : Setup c b B rs l) {k : Nat} {r : Run} {x : ID} {v : Value}
    (hr : rs[k]? = some r) (hx : x ∈ vals c.g r.sp.t) (hv : c.g.value? x = some v) :
    v.op ≠ .Phi := by
  have hok := t_roleOK S hr hx
  rcases t_roles hok hv with ⟨i, hρ⟩ | ⟨i, hρ⟩ | ⟨i, hρ⟩ | ⟨i, hρ⟩ | ⟨i, hρ⟩ | ⟨i, hρ⟩ | ⟨i, hρ⟩ |
    ⟨i, hρ⟩ | ⟨i, hρ⟩ <;>
    exact then_nophi (by rw [hρ]; rfl) (fun h => by cases h) hv

/-- An available argument is available at the segment's entry or listed in the segment. -/
private theorem avail_or {Gr : Frame} (hO : OutDef c B Gr) {k : Nat} {s a : ID}
    (hs : (segsOf b rs)[k]? = some s) (h : c.availIn B (segsOf b rs) k a = true) :
    Avail c b B rs Gr k a ∨ a ∈ vals c.g s := by
  obtain ⟨hh, h1, h2⟩ := availIn_spec h
  by_cases haB : a ∈ B.values
  · obtain ⟨s', hs', has'⟩ := h1 haB
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hs'
    rw [List.getElem?_take] at hj
    split at hj
    · rename_i hjk
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hjk) with hlt | rfl
      · exact .inl (.inr (.inl ⟨j, hlt, s', hj, has'⟩))
      · rw [hs] at hj; cases hj; exact .inr has'
    · cases hj
  · obtain ⟨z, hz⟩ := hO a hh haB (h2 haB)
    exact .inl (.inl ⟨hh, haB, z, hz⟩)

private theorem avail_of {Gr : Frame} (hO : OutDef c B Gr) {k : Nat} {s a : ID}
    (hs : (segsOf b rs)[k]? = some s) (h : c.availIn B (segsOf b rs) k a = true)
    (hna : a ∉ vals c.g s) : Avail c b B rs Gr k a :=
  (avail_or hO hs h).resolve_right hna

private theorem avail_succ (S : Setup c b B rs l) {Gr : Frame} (hO : OutDef c B Gr) {k : Nat}
    {r : Run} {a : ID} (hr : rs[k]? = some r) (h : c.availIn B (segsOf b rs) k a = true) :
    Avail c b B rs Gr (k + 1) a := by
  have hs := (run_seg S hr).1
  rcases avail_or hO hs h with hA | hin
  · rcases hA with h1 | ⟨j, hj, hj'⟩ | h3
    · exact .inl h1
    · exact .inr (.inl ⟨j, by omega, hj'⟩)
    · exact .inr (.inr h3)
  · exact .inr (.inl ⟨k, Nat.lt_succ_self _, r.sp.c, hs, hin⟩)

/-- The flag address, constant or `SB`, not listed in segment `k`, is available there. -/
private theorem lazy_avail (S : Setup c b B rs l) {Gr : Frame} {k : Nat} {s a : ID}
    (hs : (segsOf b rs)[k]? = some s) (hna : a ∉ vals c.g s)
    (hl : c.isWbaddr a = true ∨ c.isConst0 a = true ∨ c.isSb a = true) :
    Avail c b B rs Gr k a := by
  by_cases hb : b = c.f.entry
  · obtain ⟨hm, -⟩ := entry_mem S hl
    rw [← hb] at hm
    cases k with
    | zero => rw [seg0 hs] at hna; exact absurd hm hna
    | succ k => exact .inr (.inl ⟨0, Nat.succ_pos _, b, by simp [segsOf], hm⟩)
  · exact .inr (.inr ⟨hb, hl⟩)

/-- A value of the buffer block of run `k` (found by its role). -/
private theorem in_t {k : Nat} {r : Run} {a : ID} {o : Op} (hr : rs[k]? = some r)
    (ht : thenOp (c.roleOf rs a) = some (k, o)) : a ∈ vals c.g r.sp.t := by
  obtain ⟨r', hr', ha, -⟩ := roleOf_then ht
  rw [hr] at hr'; cases hr'
  exact ha

/-- **Arguments in a segment.** An argument of a non-`Phi` value of segment `k` that is not
listed there is available at the segment's entry. -/
theorem args_seg (S : Setup c b B rs l) {Gr : Frame} (hO : OutDef c B Gr) {k : Nat} {s x a : ID}
    {w : Value} (hs : (segsOf b rs)[k]? = some s) (hx : x ∈ vals c.g s)
    (hw : c.g.value? x = some w) (hnp : w.op ≠ .Phi) (ha : a ∈ w.args)
    (hna : a ∉ vals c.g s) : Avail c b B rs Gr k a := by
  have hok := seg_roleOK S hs hx
  rcases seg_roles hok hw with hρ | hρ | hρ | ⟨i, hρ⟩ | ⟨i, hρ⟩ | ⟨i, hρ⟩ | ⟨i, hρ⟩ | ⟨i, k', hρ⟩ |
    ⟨i, hρ⟩
  · obtain ⟨-, -, hK | hK⟩ := roleOK_held hok hw hρ
    · obtain ⟨hK, u, hu, -, hnp'⟩ := hK
      obtain ⟨-, hop, hargs⟩ := kept_u S hK hu hw
      exact avail_of hO hs (hnp' (by rw [hop]; exact hnp) a (by rw [hargs]; exact ha)) hna
    · obtain ⟨-, j', r, hj, hr, -, -, hargs1, hlast, -⟩ := hK
      subst hj
      obtain ⟨-, h2, -, -, -, -, -, -, htgt, -⟩ := runOK_spec (run_ok S hr)
      rw [hs] at h2; cases h2
      rw [hargs1] at ha
      simp only [List.mem_toArray, List.mem_singleton] at ha
      subst ha
      exact absurd (htgt _ (List.mem_of_getLast? hlast)) hna
  · obtain ⟨-, -, hk0, -, hargs⟩ := roleOK_lazy hok hw hρ
    subst hk0
    rw [seg0 hs] at hna
    exact absurd (hargs a ha) hna
  · rw [(roleOK_invalid hok hw hρ).2.2] at ha; simp at ha
  · obtain ⟨-, -, r, -, -, hargs, -, hwa, hav⟩ := roleOK_load hok hw hρ
    rw [hargs] at ha
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact lazy_avail S hs hna (.inl hwa)
    · exact avail_of hO hs hav hna
  · obtain ⟨-, hik, r, hr, -, hargs, -, hc0, -⟩ := roleOK_flag hok hw hρ
    subst hik
    rw [hargs] at ha
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · obtain ⟨h1, -, -, -, -, -, -, -, -, -, hload, -⟩ := runOK_spec (run_ok S hr)
      rw [hs] at h1; cases h1
      exact absurd hload hna
    · exact lazy_avail S hs hna (.inr (.inl hc0))
  · obtain ⟨-, -, r, -, hop, -⟩ := roleOK_phi hok hw hρ
    exact absurd hop hnp
  · obtain ⟨-, hk, r, n, hr, -, ⟨u, w', p, mS, -, hw', -, -, -, -, hwargs, hav⟩, -⟩ :=
      roleOK_ncEnd hok hw hρ
    rw [hw] at hw'; cases hw'
    rw [hwargs] at ha
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact avail_of hO hs hav hna
    · subst hk
      rw [(run_seg S hr).2] at hs; cases hs
      exact absurd (phi_mem S hr) hna
  · obtain ⟨-, hk, r, s', hr, -, ht', ⟨u, w', -, hw', -, -, -, -, hsz, hback, -, hall⟩, -⟩ :=
      roleOK_tgt hok hw hρ
    rw [hw] at hw'; cases hw'
    subst hk
    rw [(run_seg S hr).2] at hs; cases hs
    obtain ⟨-, -, -, ⟨E, -, -, -, hEnc⟩, -, -, -, -, htgt, hncE, -⟩ := runOK_spec (run_ok S hr)
    obtain ⟨idx, hidx, rfl⟩ := Array.getElem_of_mem ha
    by_cases hl : idx = w.args.size - 1
    · subst hl
      rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem hidx, Option.some.injEq] at hback
      exfalso; apply hna
      rw [hback]
      cases k' with
      | zero => exact phi_mem S hr
      | succ k'' =>
        have hlt : k'' < r.tgt.length := by
          have := (List.getElem?_eq_some_iff.1 ht').1; omega
        exact htgt _ (by
          show r.tgt[k'']! ∈ r.tgt
          rw [getElem!_pos r.tgt k'' hlt]; exact List.getElem_mem hlt)
    · have hlt : idx < u.args.size - 1 := by omega
      obtain ⟨hc1, hc2⟩ := hall idx hlt
      have hbang : w.args[idx]! = w.args[idx] := getElem!_pos w.args idx hidx
      by_cases hc : r.nc = some u.args[idx]! ∧ idx = 0
      · have he := hc1 hc
        rw [hbang] at he
        cases hne : r.ncEnd with
        | none => rw [hEnc hne] at hc; exact absurd hc.1 (by simp)
        | some y =>
          rw [hne] at he
          simp only [Option.getD_some] at he
          rw [he] at hna
          exact absurd (hncE y hne) hna
      · obtain ⟨he, hav⟩ := hc2 hc
        rw [hbang] at he
        rw [he] at hna ⊢
        exact avail_of hO (run_seg S hr).2 hav hna
  · obtain ⟨-, -, -, hargs, hsb, -⟩ := roleOK_taddr hok hw hρ
    rw [hargs] at ha
    simp only [List.mem_toArray, List.mem_singleton] at ha
    subst ha
    exact lazy_avail S hs hna (.inr (.inr hsb))

/-- **Arguments in a buffer block.** An argument of a value of run `k`'s buffer block that is not
listed there is available after segment `k`. -/
theorem args_t (S : Setup c b B rs l) {Gr : Frame} (hO : OutDef c B Gr) {k : Nat} {r : Run}
    {x a : ID} {w : Value} (hr : rs[k]? = some r) (hx : x ∈ vals c.g r.sp.t)
    (hw : c.g.value? x = some w) (ha : a ∈ w.args) (hna : a ∉ vals c.g r.sp.t) :
    Avail c b B rs Gr (k + 1) a := by
  have hok := t_roleOK S hr hx
  have hmem := (mem_held S hr).2
  rcases t_roles hok hw with ⟨i, hρ⟩ | ⟨i, hρ⟩ | ⟨i, hρ⟩ | ⟨i, hρ⟩ | ⟨i, hρ⟩ | ⟨i, hρ⟩ | ⟨i, hρ⟩ |
    ⟨i, hρ⟩ | ⟨i, hρ⟩
  · obtain ⟨-, hik, r', n, hr', -, ⟨u, w', p, mS, -, hw', -, -, -, -, hwargs, hav⟩⟩ :=
      roleOK_ncThen hok hw hρ
    subst hik
    rw [hr] at hr'; cases hr'
    rw [hw] at hw'; cases hw'
    rw [hwargs] at ha
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact avail_succ S hO hr hav
    · exact avail_succ S hO hr hmem
  · obtain ⟨-, hik, r', hr', hargs, -⟩ := roleOK_wb hok hw hρ
    subst hik
    rw [hr] at hr'; cases hr'
    rw [hargs] at ha
    simp only [List.mem_toArray, List.mem_singleton] at ha
    subst ha
    exact avail_succ S hO hr hmem
  · obtain ⟨-, hik, hargs, hrole, -⟩ := roleOK_sel hok hw (.inl hρ)
    subst hik
    rw [hargs] at ha
    simp only [List.mem_toArray, List.mem_singleton] at ha
    subst ha
    exact absurd (in_t hr (by rw [hrole]; rfl)) hna
  · obtain ⟨-, hik, hargs, hrole, -⟩ := roleOK_sel hok hw (.inr hρ)
    subst hik
    rw [hargs] at ha
    simp only [List.mem_toArray, List.mem_singleton] at ha
    subst ha
    exact absurd (in_t hr (by rw [hrole]; rfl)) hna
  · obtain ⟨-, hik, hargs, -, hrole, -⟩ := roleOK_off hok hw hρ
    subst hik
    rw [hargs] at ha
    simp only [List.mem_toArray, List.mem_singleton] at ha
    subst ha
    exact absurd (in_t hr (by rw [hrole]; rfl)) hna
  · obtain ⟨-, hik, hargs, -, -, h0, ⟨r', hr', h1⟩, h2⟩ := roleOK_bstore hok hw hρ
    subst hik
    rw [hr] at hr'; cases hr'
    rw [hargs] at ha
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact absurd (in_t hr (by rw [h0]; rfl)) hna
    · rcases h1 with h1 | h1
      · exact avail_succ S hO hr (runArg_availIn h1)
      · exact absurd (in_t hr (by rw [h1]; rfl)) hna
    · rcases h2 with h2 | h2
      · exact absurd (in_t hr (by rw [h2]; rfl)) hna
      · exact absurd (in_t hr (by rw [h2]; rfl)) hna
  · obtain ⟨-, hik, hargs, r', hr', h0, h1⟩ := roleOK_tload hok hw hρ
    subst hik
    rw [hr] at hr'; cases hr'
    rw [hargs] at ha
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · rcases h0 with h0 | h0
      · exact avail_succ S hO hr (runArg_availIn h0)
      · exact absurd (in_t hr (by rw [h0]; rfl)) hna
    · rcases h1 with h1 | h1 | h1
      · rw [h1]; exact avail_succ S hO hr hmem
      · exact absurd (in_t hr (by rw [h1]; rfl)) hna
      · exact absurd (in_t hr (by rw [h1]; rfl)) hna
  · obtain ⟨-, hik, -, -, r', hr', P⟩ := roleOK_call hok hw hρ
    subst hik
    rw [hr] at hr'; cases hr'
    obtain ⟨idx, hidx, rfl⟩ := Array.getElem_of_mem ha
    have hbang : w.args[idx]! = w.args[idx] := getElem!_pos w.args idx hidx
    obtain ⟨s, u, -, -, husz, hopu, hdst⟩ := P.src
    by_cases hl : idx = w.args.size - 1
    · subst hl
      obtain ⟨m, hm, hmr⟩ := P.mem
      rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem hidx, Option.some.injEq] at hm
      rw [hm] at hna ⊢
      rcases hmr with h | h | h | h
      · rw [h]; exact avail_succ S hO hr hmem
      · exact absurd (in_t hr (by rw [h]; rfl)) hna
      · exact absurd (in_t hr (by rw [h]; rfl)) hna
      · exact absurd (in_t hr (by rw [h]; rfl)) hna
    · rcases idx with _ | _ | _ | idx
      · have ht := P.typ
        rw [hbang] at ht
        obtain ⟨r', hr', hx'⟩ := roleOf_taddr ht
        rw [hr] at hr'; cases hr'
        exact .inr (.inl ⟨_, Nat.lt_succ_self _, r.sp.c, (run_seg S hr).1, hx'⟩)
      · rcases hdst with ⟨he, hav⟩ | ⟨-, hn⟩
        · rw [hbang] at he; rw [he]; exact avail_succ S hO hr hav
        · rw [hbang] at hn; exact absurd (in_t hr (by rw [hn]; rfl)) hna
      · rcases hopu with ⟨-, h3⟩ | ⟨-, -, h2, hav⟩
        · omega
        · rw [hbang] at h2; rw [h2]; exact avail_succ S hO hr hav
      · rcases hopu with ⟨-, h3⟩ | ⟨-, h4, -⟩ <;> omega
  · obtain ⟨-, hik, -, hargs, -, -, hrole⟩ := roleOK_seln hok hw hρ
    subst hik
    rw [hargs] at ha
    simp only [List.mem_toArray, List.mem_singleton] at ha
    subst ha
    exact absurd (in_t hr (by rw [hrole]; rfl)) hna

end Setup

end GoFV.Proof.WB

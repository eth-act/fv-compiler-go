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
address and constant. -/
def Avail (c : WBCheck.Ctx) (b : ID) (B : Block) (rs : List Run) (Gr : Frame) (k : Nat)
    (a : ID) : Prop :=
  (c.held a = true ∧ a ∉ B.values ∧ ∃ y, Gr.regs[a]? = some (some y)) ∨
  (∃ j, j < k ∧ InSeg c b rs j a) ∨
  (b ≠ c.f.entry ∧ (c.isWbaddr a = true ∨ c.isConst0 a = true))

theorem vals_of {h : Func} {s : ID} {C : Block} (hC : h.block? s = some C) :
    vals h s = C.values := by
  unfold vals; rw [hC]; rfl

namespace Setup

variable {c : WBCheck.Ctx} {b : ID} {B : Block} {rs : List Run} {l : ID}

theorem listed_once (S : Setup c b B rs l) {s s' a : ID} (hs : s ∈ c.g.blocks)
    (hs' : s' ∈ c.g.blocks) (ha : a ∈ vals c.g s) (ha' : a ∈ vals c.g s') : s = s' := by
  sorry

theorem segs_length (b : ID) (rs : List Run) : (segsOf b rs).length = rs.length + 1 := by
  simp [segsOf]

theorem seg_block (S : Setup c b B rs l) {k : Nat} {s : ID} (hs : (segsOf b rs)[k]? = some s) :
    ∃ C, c.g.block? s = some C ∧ C.id = s ∧ s ∈ c.g.blocks ∧ ∃ o, schedule c.g C = some o := by
  sorry

theorem run_seg (S : Setup c b B rs l) {j : Nat} {r : Run} (hr : rs[j]? = some r) :
    (segsOf b rs)[j]? = some r.sp.c ∧ (segsOf b rs)[j + 1]? = some r.sp.e := by
  sorry

theorem t_block (S : Setup c b B rs l) {j : Nat} {r : Run} (hr : rs[j]? = some r) :
    ∃ T, c.g.block? r.sp.t = some T ∧ T.id = r.sp.t ∧ r.sp.t ∈ c.g.blocks ∧ T.kind = .Plain ∧
      T.succs = #[⟨r.sp.e, 1⟩] ∧ ∃ o, schedule c.g T = some o := by
  sorry

theorem split_block (S : Setup c b B rs l) {j : Nat} {r : Run} (hr : rs[j]? = some r) :
    ∃ C, c.g.block? r.sp.c = some C ∧ C.kind = .If ∧ C.controls = #[r.sp.flag] ∧
      C.succs = #[⟨r.sp.t, 0⟩, ⟨r.sp.e, 0⟩] ∧ c.roleOf rs r.sp.flag = .flag j ∧
      r.sp.flag ∈ vals c.g r.sp.c := by
  sorry

theorem last_block (S : Setup c b B rs l) :
    ∃ L, c.g.block? l = some L ∧ (segsOf b rs)[rs.length]? = some l ∧ L.kind = B.kind ∧
      L.controls = B.controls ∧ L.succs = B.succs ∧ ∀ x ∈ B.controls, c.held x = true := by
  sorry

/-- Distinct positions of the chain are distinct blocks. -/
theorem seg_inj (S : Setup c b B rs l) {j j' : Nat} {s : ID} (hj : (segsOf b rs)[j]? = some s)
    (hj' : (segsOf b rs)[j']? = some s) : j = j' := by
  sorry

theorem seg_ne_t (S : Setup c b B rs l) {j j' : Nat} {s : ID} {r : Run}
    (hj : (segsOf b rs)[j]? = some s) (hr : rs[j']? = some r) : s ≠ r.sp.t := by
  sorry

theorem t_inj (S : Setup c b B rs l) {j j' : Nat} {r r' : Run} (hr : rs[j]? = some r)
    (hr' : rs[j']? = some r') (he : r.sp.t = r'.sp.t) : j = j' := by
  sorry

/-- Held values listed in a segment are values of `B`. -/
theorem held_seg (S : Setup c b B rs l) {j : Nat} {a : ID} (h : InSeg c b rs j a)
    (hh : c.held a = true) : a ∈ B.values := by
  sorry

/-- No held value is listed in a buffer block. -/
theorem held_t (S : Setup c b B rs l) {j : Nat} {a : ID} (h : InT c rs j a)
    (hh : c.held a = true) : False := by
  sorry

/-- The flag address and constant are listed in `g`'s entry, which is `f`'s. -/
theorem lazy_entry (S : Setup c b B rs l) {wa c0 : ID} (hz : c.lazy = some (wa, c0)) :
    wa ∈ vals c.g c.f.entry ∧ c0 ∈ vals c.g c.f.entry ∧ c.f.entry ∈ c.g.blocks := by
  sorry

/-- When `b` is not the entry, no block of its chain is `g`'s entry. -/
theorem entry_not_chain (S : Setup c b B rs l) (hb : b ≠ c.f.entry) :
    ∀ s ∈ segsOf b rs ++ rs.map (·.sp.t), s ≠ c.f.entry := by
  sorry

/-- An available register is not listed in segment `k`. -/
theorem avail_not_seg (S : Setup c b B rs l) {Gr : Frame} {k : Nat} {s a : ID}
    (hs : (segsOf b rs)[k]? = some s) (ha : Avail c b B rs Gr k a) : a ∉ vals c.g s := by
  sorry

/-- A register available after segment `k` is not listed in run `k`'s buffer block. -/
theorem avail_not_t (S : Setup c b B rs l) {Gr : Frame} {k : Nat} {r : Run} {a : ID}
    (hr : rs[k]? = some r) (ha : Avail c b B rs Gr (k + 1) a) : a ∉ vals c.g r.sp.t := by
  sorry

/-- The `Phi`s of the first segment are kept `Phi`s of `B` with held arguments. -/
theorem phi_seg0 (S : Setup c b B rs l) {s x : ID} {v : Value} (hs : (segsOf b rs)[0]? = some s)
    (hx : x ∈ vals c.g s) (hv : c.g.value? x = some v) (hp : v.op = .Phi) :
    c.roleOf rs x = .held ∧ c.K.getD x false = true ∧ x ∈ B.values ∧
      ∃ u, c.f.value? x = some u ∧ sameV u v = true ∧ ∀ a ∈ u.args, c.held a = true := by
  sorry

/-- The only `Phi` of segment `k + 1` is run `k`'s memory `Phi`. -/
theorem phi_seg (S : Setup c b B rs l) {k : Nat} {s x : ID} {v : Value}
    (hs : (segsOf b rs)[k + 1]? = some s) (hx : x ∈ vals c.g s) (hv : c.g.value? x = some v)
    (hp : v.op = .Phi) :
    ∃ r, rs[k]? = some r ∧ x = r.phi ∧ c.roleOf rs x = .phi k ∧
      v.args = #[r.sp.mem, r.memThen] ∧ c.tabs.ty v.type = .mem ∧
      (r.memThen = r.sp.mem ∨ c.roleOf rs r.memThen = .sel1 k ∨
        c.roleOf rs r.memThen = .bstore k) := by
  sorry

/-- Run `k`'s memory is held. -/
theorem mem_held (S : Setup c b B rs l) {k : Nat} {r : Run} (hr : rs[k]? = some r) :
    c.held r.sp.mem = true ∧ c.availIn B (segsOf b rs) k r.sp.mem = true := by
  sorry

/-- A buffer block has no `Phi`. -/
theorem t_nophi (S : Setup c b B rs l) {k : Nat} {r : Run} {x : ID} {v : Value}
    (hr : rs[k]? = some r) (hx : x ∈ vals c.g r.sp.t) (hv : c.g.value? x = some v) :
    v.op ≠ .Phi := by
  sorry

/-- **Arguments in a segment.** An argument of a non-`Phi` value of segment `k` that is not
listed there is available at the segment's entry. -/
theorem args_seg (S : Setup c b B rs l) {Gr : Frame} (hO : OutDef c B Gr) {k : Nat} {s x a : ID}
    {w : Value} (hs : (segsOf b rs)[k]? = some s) (hx : x ∈ vals c.g s)
    (hw : c.g.value? x = some w) (hnp : w.op ≠ .Phi) (ha : a ∈ w.args)
    (hna : a ∉ vals c.g s) : Avail c b B rs Gr k a := by
  sorry

/-- **Arguments in a buffer block.** An argument of a value of run `k`'s buffer block that is not
listed there is available after segment `k`. -/
theorem args_t (S : Setup c b B rs l) {Gr : Frame} (hO : OutDef c B Gr) {k : Nat} {r : Run}
    {x a : ID} {w : Value} (hr : rs[k]? = some r) (hx : x ∈ vals c.g r.sp.t)
    (hw : c.g.value? x = some w) (ha : a ∈ w.args) (hna : a ∉ vals c.g r.sp.t) :
    Avail c b B rs Gr (k + 1) a := by
  sorry

end Setup

end GoFV.Proof.WB

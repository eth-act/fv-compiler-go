import GoFV.Proof.Pass.WBCov

/-!
# writebarrier: facts for a panicking block entry (issue #36)

`src_np`/`ncs_np`: a run's stores and dropped nil check are non-pure nodes of `B`.
`held_pure_args`: the in-block arguments of a held pure value listed in segment `j` are held and
listed in segment `j` (before it in the schedule) or earlier. `cov_of_runs`: the source facts of
the values of the segments up to `J` and the buffer blocks before `J`, when the runs before `J`
were evaluated. `localQ_mono`: `LocalQ` under a stronger property that only constrains values
outside the evaluated list. `panic_kept_step`, `panic_nc_step`: the target's copy of the
source's panicking node panics alike. `runMem_of_panic`: a dropped nil check that panics read
its run's memory. `filter_first`: the values before the first non-pure node are pure.
-/

namespace GoFV.Proof.WB

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.WBCheck GoFV.Proof

theorem filter_first {p : ID → Bool} : ∀ {o : List ID} {y : ID} {ys : List ID},
    o.filter p = y :: ys → ∃ pre post, o = pre ++ y :: post ∧ ∀ x ∈ pre, p x = false := by
  sorry

theorem localQ_mono {env : Env} {ctx : Sem.Ctx} {fr0 : Frame} {Q Q' : ID → Val → Prop} {x : ID}
    (h : LocalQ env ctx fr0 Q x) (hQ' : ∀ a z, Q' a z → Q a z) (hx : ∀ z, Q x z → Q' x z) :
    LocalQ env ctx fr0 Q' x := by
  sorry

namespace Setup

variable {c : WBCheck.Ctx} {b : ID} {B : Block} {rs : List Run} {l : ID}

theorem src_np (S : Setup c b B rs l) {j : Nat} {r : Run} (hr : rs[j]? = some r) {s : ID}
    (hs : s ∈ r.src) : npOf c.f B s = true := by
  sorry

theorem ncs_np (S : Setup c b B rs l) {j : Nat} {r : Run} (hr : rs[j]? = some r) {n : ID}
    (hn : n ∈ ncsOf c r) : npOf c.f B n = true := by
  sorry

/-- The in-block arguments of a held pure value of segment `j`. -/
theorem held_pure_args (S : Setup c b B rs l) {j : Nat} {s x : ID}
    (hs : (segsOf b rs)[j]? = some s) (hx : x ∈ vals c.g s) (hh : c.held x = true)
    (hp : npOf c.f B x = false) {u : Value} (hu : c.f.value? x = some u) {a : ID}
    (ha : a ∈ u.args) (haB : a ∈ B.values) (hap : ∀ va, c.f.value? a = some va → va.op ≠ .Phi) :
    c.held a = true ∧ ∃ j', j' ≤ j ∧ InSeg c b rs j' a ∧
      (j' = j → ∀ C oC, c.g.block? s = some C → schedule c.g C = some oC →
        Order.Before oC.toList a x) := by
  sorry

/-- **Source facts up to `J`**: the values of segments `j ≤ J` and of the buffer blocks `j < J`,
when the runs before `J` are in a closed set `P` of evaluated values and the held values in
question are too. -/
theorem cov_of_runs (S : Setup c b B rs l) {env : Env} {Gr : Frame} {P : ID → Prop}
    (hEv : ∀ x, P x → Ev env c Gr x)
    (hPcl : ∀ x a v, P x → c.f.value? x = some v → a ∈ v.args → a ∈ B.values →
      (∀ va, c.f.value? a = some va → va.op ≠ .Phi) → P a)
    {J : Nat} (hruns : ∀ j r, j < J → rs[j]? = some r →
      (∀ s ∈ r.src, P s) ∧ (∀ n ∈ ncsOf c r, P n))
    {x : ID} (hpos : (∃ j, j ≤ J ∧ InSeg c b rs j x) ∨ (∃ j, j < J ∧ InT c rs j x))
    (hheld : c.roleOf rs x = .held → c.K.getD x false = true →
      (∀ u, c.f.value? x = some u → u.op ≠ .Phi) → P x) :
    Cov env c rs Gr x := by
  sorry

/-- **The kept panicking node**: on any frame whose argument registers satisfy `QR`, it panics as
the source's. -/
theorem panic_kept_step (S : Setup c b B rs l) {env : Env} {Gr fr0 : Frame}
    (hG : GrOK c B rs Gr fr0) {k : Nat} {r : ID} (hr : InSeg c b rs k r)
    (hK : c.K.getD r false = true) {rv : Value} (hrv : c.f.value? r = some rv)
    (hrop : Panicking rv.op) {e : Panic} {m : Mem}
    (hpan : stepV env (Ctx.make c.tabs c.f) Gr r = .panic e m) :
    ∀ g' : Frame, g' = { fr0 with regs := g'.regs } →
      (∀ a ∈ argsF c.g r, ∃ z, g'.regs[a]? = some (some z) ∧ QR c rs Gr a z) →
      stepV env (Ctx.make c.tabs c.g) g' r = .panic e m := by
  sorry

/-- **A dropped nil check that panics** reads its run's memory, the panic's memory. -/
theorem runMem_of_panic (S : Setup c b B rs l) {env : Env} {Gr : Frame} {j : Nat} {r : Run}
    (hr : rs[j]? = some r) {n : ID} (hn : r.nc = some n) {e : Panic} {m : Mem}
    (hpan : stepV env (Ctx.make c.tabs c.f) Gr n = .panic e m) : RunMem Gr rs j m := by
  sorry

/-- **A copy of the dropped nil check** panics as the source's, on any frame whose argument
registers hold the nil check's pointer (held) and the run's memory. -/
theorem panic_nc_step (S : Setup c b B rs l) {env : Env} {Gr fr0 : Frame}
    (hG : GrOK c B rs Gr fr0) {j : Nat} {r : Run} (hr : rs[j]? = some r) {n : ID}
    (hn : r.nc = some n) {e : Panic} {m : Mem}
    (hpan : stepV env (Ctx.make c.tabs c.f) Gr n = .panic e m) {y mT : ID}
    (hy : NcCopy c B (segsOf b rs) j n y mT ∨ NcCopy c B (segsOf b rs) (j + 1) n y mT) :
    ∀ g' : Frame, g' = { fr0 with regs := g'.regs } →
      (∀ a ∈ argsF c.g y, ∃ z, g'.regs[a]? = some (some z) ∧ QR c rs Gr a z) →
      g'.regs[mT]? = some (some (.mem m)) →
      stepV env (Ctx.make c.tabs c.g) g' y = .panic e m := by
  sorry

end Setup

end GoFV.Proof.WB

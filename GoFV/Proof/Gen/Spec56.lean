import GoFV.Gen.Check56
import GoFV.Proof.Gen.Spec55

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `checkG56` accepted (`GoFV/Gen/Check56.lean`)

`VK56`: a float constant (`FMOVSconst`/`FMOVDconst`, no temporary, homed in an `F` register of its
class) with `fconstPat56`, or G55's kinds (`VK55`) of every other value. `constSymA_spec`: the
symbol operand of a constant load names a float constant symbol of `G2In.syms` whose allocation
(`constSymAlloc?`) holds the bits. On `InitMem`, `vkind56` is `vkind55` (`vkind56_initMem`), and
so on any op but the float constants (`vkind56_eq55`); on an op of none of G52–G56's groups it is
`vkind49` (`vkind56_eq49`). `checkG56L_spec` is `checkG55L_spec` with `vkind56`, and
`checkG56_spec` splits off `refsLive`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind56` accepted of a value that is not an entry value. -/
inductive VK56 (lc : LocCtx) (g : G2In) (v : Value) : VKind2 → Prop
  /-- A value of slice G55 that is no float constant. -/
  | g55 {kd : VKind2} : v.op ≠ .ARM64FMOVSconst → v.op ≠ .ARM64FMOVDconst → VK55 lc g v kd →
      VK56 lc g v kd
  /-- A float constant: `FMOVS`/`FMOVD $c, Fd`, or the load of its constant symbol. -/
  | fconst {c : Nat} {rd : Int} : (v.op = .ARM64FMOVSconst ∨ v.op = .ARM64FMOVDconst) →
      (lc.temps[v.id]?).join = none → v.args.size = 0 → fresObj lc v = .ok (c, rd) →
      c = 8 * fBytes v.op → VK56 lc g v (.prog (fconstPat56 g v c rd))

/-- `vkind56a` of every op but the float constants is `none`. -/
theorem vkind56a_none {lc : LocCtx} {g : G2In} {v : Value} (h1 : v.op ≠ .ARM64FMOVSconst)
    (h2 : v.op ≠ .ARM64FMOVDconst) : vkind56a lc g v = none := by
  unfold vkind56a
  simp [h1, h2]

/-- What `vkind56` accepted of a value that is not an entry value. -/
theorem vkind56_spec {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}
    (h : vkind56 lc g v = .ok kd) (hen : entryOp24 v.op = false) : VK56 lc g v kd := by
  unfold vkind56 at h
  by_cases hop : v.op = .ARM64FMOVSconst ∨ v.op = .ARM64FMOVDconst
  · have hb : (v.op == .ARM64FMOVSconst || v.op == .ARM64FMOVDconst) = true := by
      rcases hop with h' | h' <;> simp [h']
    unfold vkind56a at h
    simp only [hb, ↓reduceIte] at h
    obtain ⟨ht, h⟩ := ex_guard h
    obtain ⟨hsz, h⟩ := ex_guard h
    obtain ⟨⟨c, rd⟩, hro, h⟩ := ex_bind_eq_ok h
    obtain ⟨hc, h⟩ := ex_guard h
    cases h
    simp only [beq_iff_eq] at ht hsz hc
    exact .fconst hop ht hsz hro hc
  · have h1 : v.op ≠ .ARM64FMOVSconst := fun h' => hop (.inl h')
    have h2 : v.op ≠ .ARM64FMOVDconst := fun h' => hop (.inr h')
    rw [vkind56a_none h1 h2] at h
    exact .g55 h1 h2 (vkind55_spec h hen)

/-- On `InitMem`, `vkind56` is `vkind55`. -/
theorem vkind56_initMem {lc : LocCtx} {g : G2In} {v : Value} (hop : v.op = .InitMem) :
    vkind56 lc g v = vkind55 lc g v := by
  unfold vkind56
  rw [vkind56a_none (by rw [hop]; nofun) (by rw [hop]; nofun)]

/-- The operand `constSymA` accepted: `sym(SB)` of a symbol `y` of `G2In.syms` whose name is a
float constant symbol holding the `n` little-endian bytes of `x`. -/
theorem constSymA_spec {g : G2In} {n x : Nat} {a : Addr} (h : constSymA g n x a = true) :
    a.type = .MEM ∧ a.name = .EXTERN ∧ a.offset = 0 ∧ ∃ y name abi, a.sym = some y ∧
      g.syms[y]? = some (name, abi) ∧
      constSymAlloc? name.toStringLossy = some (roAlloc (leBytesU8 x n)) := by
  unfold constSymA at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, h5⟩, h⟩ := h
  refine ⟨h1, h2, h5, ?_⟩
  cases hy : a.sym with
  | none => rw [hy] at h; cases h
  | some y =>
    rw [hy] at h
    simp only at h
    cases hs : g.syms[y]? with
    | none => rw [hs] at h; cases h
    | some e =>
      obtain ⟨name, abi⟩ := e
      rw [hs] at h
      simp only [beq_iff_eq] at h
      exact ⟨y, name, abi, rfl, hs, h⟩

/-- G56's ops: the float constants. -/
def op56 (op : Op) : Bool := op == .ARM64FMOVSconst || op == .ARM64FMOVDconst

/-- On an op off G56's, `vkind56` is `vkind55`. -/
theorem vkind56_eq55 {lc : LocCtx} {g : G2In} {v : Value} (h : op56 v.op = false) :
    vkind56 lc g v = vkind55 lc g v := by
  have h1 : v.op ≠ .ARM64FMOVSconst := fun h' => by simp [op56, h'] at h
  have h2 : v.op ≠ .ARM64FMOVDconst := fun h' => by simp [op56, h'] at h
  unfold vkind56
  rw [vkind56a_none h1 h2]

/-- On an op of none of G52's, G53's, G54's, G55's and G56's groups, `vkind56` is `vkind49`. -/
theorem vkind56_eq49 {lc : LocCtx} {g : G2In} {v : Value} (h6 : op56 v.op = false)
    (h5a : op55a v.op = false) (h5b : op55b v.op = false)
    (h2 : op52b v.op = false) (h3 : op53a v.op = false) (h4 : op54a v.op = false) :
    vkind56 lc g v = vkind49 lc g v := by
  rw [vkind56_eq55 h6, vkind55_eq54 h5a h5b, vkind54_eq49 h2 h3 h4]

/-- On a function with no arm64 op, G56's check is G33. -/
theorem checkG33_of_56L {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG56L lc ps bstart g = r) : checkG33 lc ps bstart g = r := by
  simpa [checkG33, checkG56L, hl] using h

/-- What `checkG56L` accepted of a function with an arm64 op: G55's facts with G56's value
check. -/
theorem checkG56L_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hl : lc.ctx.f.lowered = true)
    (h : checkG56L lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.cx.bstart = bstart ∧ c.g = g ∧
      c.vk = vkind56 lc g ∧ c.tm = c.cx.termG3 ∧
      lc.ctx.f.lowered = true ∧ (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      checkK lc kt = .ok () ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab ∧ pbOK lc ps.toList tab = true ∧
      movdOK35 lc = true ∧ uEdgesOK35 lc = true ∧ loopOK lc ps tab = true := by
  simp only [checkG56L, hl, ↓reduceIte] at h
  obtain ⟨tab', hb, h⟩ := ex_bind_eq_ok h
  obtain ⟨hpb, h⟩ := ex_guard h
  obtain ⟨hlp, h⟩ := ex_guard h
  obtain ⟨hmovd, h⟩ := ex_guard h
  simp only [Bool.and_eq_true] at hmovd
  cases hf : List.find? (fun x => !homeOK10 lc x) (List.range lc.homes.size) with
  | some i =>
    rw [hf] at h
    exact (ex_throw_bind h).elim
  | none =>
    rw [hf] at h
    obtain ⟨-, h⟩ := ex_guard h
    obtain ⟨⟨⟩, hfr, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨⟩, -, h⟩ := ex_bind_eq_ok h
    obtain ⟨⟨⟩, hk, h⟩ := ex_bind_eq_ok h
    obtain ⟨hids, h⟩ := ex_guard h
    simp only [ex_pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hids
    refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, hl, fun i => ?_, hfr, hk,
      fun p hp => hids.1 _ (List.mem_map_of_mem hp), hids.2, hb, hpb, hmovd.1, hmovd.2, hlp⟩
    by_cases hi : i < lc.homes.size
    · have := List.find?_eq_none.mp hf i (List.mem_range.mpr hi)
      simpa using this
    · have hh : lc.home i = none := by
        simp only [LocCtx.home]
        rw [getElem?_neg lc.homes i hi]
        rfl
      unfold homeOK10 homeOK4 homeOK3 homeOK2 homeOK
      rw [hh]
      rfl

/-- What `checkG56` accepted: `refsLive`, and `checkG56L` on `liveCtx`. -/
theorem checkG56_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : PcTab × KTab} (h : checkG56 lc ps bstart g = .ok r) :
    refsLive lc = true ∧ checkG56L (liveCtx lc) ps bstart g = .ok r := by
  unfold checkG56 at h
  cases hr : refsLive lc with
  | false => simp [hr] at h; cases h
  | true => simp only [hr] at h; exact ⟨rfl, by simpa using h⟩

end GoFV.Gen.Check

import GoFV.Proof.Pass.WBWalk
import GoFV.Proof.DomCert
import GoFV.Proof.Pass.WBInv

/-!
# writebarrier: the simulation relation and the start of a chain (issue #36)

`SimAt env c frS frT b i`: the source enters block `b` along edge `i` with frame `frS` (lemma (D)
for the strict dominators, `SInv`), the target enters `b` (the first segment of its chain) with
`frT`: the source's frame but for the registers, equal on held values, with the flag address and
constant once the entry block has run.

From a reference frame `Gr` of the source after (a prefix of) block `b`: `grOK` (the facts the
chain's values read), `regs0`/`phis0` (the target at the chain's entry), `final_held` (held
registers after the chain).
-/

namespace GoFV.Proof.WB

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Opt GoFV.Opt.WBCheck GoFV.Proof

/-- The target holds the flag address and constant. -/
def LazyRegs (c : WBCheck.Ctx) (fr : Frame) : Prop :=
  ∀ wa c0, c.lazy = some (wa, c0) →
    fr.regs[wa]? = some (some (.ptr flagPtr)) ∧ fr.regs[c0]? = some (some (.int .w32 0))

/-- How the source enters block `b` along edge `i`: the entry, or a successor of a tree block `p`
after which lemma (D) holds for `p`'s ancestors. -/
def Pre (env : Env) (c : WBCheck.Ctx) (fr : Frame) (b : ID) (i : Nat) : Prop :=
  b = c.f.entry ∨ ∃ p P, p ∈ c.f.blocks ∧ c.f.block? p = some P ∧
    ((make c.f).depthOf p).isSome ∧ (⟨b, i⟩ : Edge) ∈ P.succs ∧
    DInv env (Ctx.make c.tabs c.f) (fun a => Anc (make c.f) a p) fr

/-- The simulation relation at block entries (see the module doc). -/
structure SimAt (env : Env) (c : WBCheck.Ctx) (frS frT : Frame) (b : ID) (i : Nat) : Prop where
  pre : Pre env c frS b i
  sizeS : frS.regs.size = c.f.valueTab.size
  sizeT : frT.regs.size = c.g.valueTab.size
  fr : frT = { frS with regs := frT.regs }
  held : ∀ a, c.held a = true → frT.regs[a]? = frS.regs[a]?
  sinv : SInv frS
  lazy : b ≠ c.f.entry → LazyRegs c frT
  entry : b = c.f.entry → ∀ (a : ID) (y : Val), frS.regs[a]? ≠ some (some y)

theorem pre_tree {ce : CheckEnv} {c : WBCheck.Ctx} (hwf : WF ce c.f) (hc : CertOK c.f)
    {env : Env} {fr : Frame} {b : ID} {i : Nat} (h : Pre env c fr b i) :
    b ∈ c.f.blocks ∧ ((make c.f).depthOf b).isSome := by
  rcases h with rfl | ⟨p, P, hp, hpb, hpt, he, -⟩
  · exact ⟨hwf.entry, by simp [entry_depth hc.parents]⟩
  · obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 he
    exact ⟨(hwf.succLink p P ⟨hp, hpb⟩ j _ hj).1, (edge hc hp hpb hpt he).2.1⟩

theorem pre_strict {c : WBCheck.Ctx} (hc : CertOK c.f) {env : Env} {fr : Frame} {b : ID}
    {i : Nat} (h : Pre env c fr b i) :
    DInv env (Ctx.make c.tabs c.f) (fun a => Anc (make c.f) a b ∧ a ≠ b) fr := by
  rcases h with rfl | ⟨p, P, hp, hpb, hpt, he, hd⟩
  · exact dinv_entry hc fr
  · exact hd.mono fun _ ⟨ha, hne⟩ =>
      Anc.trans hc.parents (ha.up hc.parents hne) (edge hc hp hpb hpt he).2.2

/-- The source's evaluation of a kept flag address. -/
theorem eval_wbaddr {env : Env} {tabs : Tables} {f : Func} {fr : Frame} {u : Value} {y : Val}
    (h : evalValue env (Ctx.make tabs f) fr u = .ok y) (hop : u.op = .Addr)
    (hsym : symName? tabs u.aux = some "runtime.writeBarrier")
    (hty : isPtrTy (tabs.ty u.type) = true) (hid : f.value? u.id = some u) :
    y = .ptr flagPtr := by
  sorry

/-- The source's evaluation of a kept `Const32 [0]`. -/
theorem eval_const0 {env : Env} {tabs : Tables} {f : Func} {fr : Frame} {u : Value} {y : Val}
    (h : evalValue env (Ctx.make tabs f) fr u = .ok y) (hop : u.op = .Const32)
    (hai : u.auxInt = (0 : Int64)) (hty : tabs.ty u.type = .int .w32)
    (hid : f.value? u.id = some u) : y = .int .w32 0 := by
  sorry

namespace Setup

variable {c : WBCheck.Ctx} {b : ID} {B : Block} {rs : List Run} {l : ID}

/-- A held value of `B` is listed in a segment. -/
theorem held_listed (S : Setup c b B rs l) {a : ID} (hh : c.held a = true) (ha : a ∈ B.values) :
    ∃ j, InSeg c b rs j a := by
  sorry

/-- A held flag address or constant is a kept value of the entry block. -/
theorem lazy_held (S : Setup c b B rs l) (hall : ∀ b' ∈ c.f.blocks, c.blockOK b' = true)
    {a : ID} (hh : c.held a = true) (hl : c.isWbaddr a = true ∨ c.isConst0 a = true) :
    c.K.getD a false = true ∧ ∃ E, c.f.block? c.f.entry = some E ∧ a ∈ E.values := by
  sorry

/-- **The reference frame's facts.** -/
theorem grOK (S : Setup c b B rs l) (hall : ∀ b' ∈ c.f.blocks, c.blockOK b' = true) {env : Env}
    {frS frT : Frame} {i : Nat} (hA : SimAt env c frS frT b i) {Gr : Frame}
    (hfr : Gr = { frS with regs := Gr.regs }) (hsinv : SInv Gr)
    (hout : ∀ a, a ∉ B.values → Gr.regs[a]? = frS.regs[a]?)
    (hev : b = c.f.entry → ∀ a ∈ B.values, ∀ y, Gr.regs[a]? = some (some y) →
      (c.isWbaddr a = true ∨ c.isConst0 a = true) → Ev env c Gr a)
    (hO : OutDef c B Gr) : GrOK c B rs Gr frS := by
  sorry

/-- **The target at the chain's entry.** -/
theorem regs0 (S : Setup c b B rs l) {env : Env} {frS frT : Frame} {i : Nat}
    (hA : SimAt env c frS frT b i) {Gr : Frame} (hG : GrOK c B rs Gr frS)
    (hout : ∀ a, a ∉ B.values → Gr.regs[a]? = frS.regs[a]?) :
    Regs c b B rs Gr frS frT 0 frT := by
  sorry

/-- **The `Phi`s of the chain's entry** take the source's arguments. -/
theorem phis0 (S : Setup c b B rs l) {env : Env} {frS frT : Frame} {i : Nat}
    (hA : SimAt env c frS frT b i) {Gr : Frame}
    (hphi : ∀ x ∈ B.values, ∀ u, c.f.value? x = some u → u.op = .Phi →
      ∃ a y, u.args[i]? = some a ∧ frS.regs[a]? = some (some y) ∧
        Gr.regs[x]? = some (some (y.retype ((Ctx.make c.tabs c.f).tys[x]?.getD .other)))) :
    Phis c b rs Gr 0 frT i := by
  sorry

end Setup

end GoFV.Proof.WB

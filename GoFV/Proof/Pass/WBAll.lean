import GoFV.Proof.Pass.WBBlock

/-!
# writebarrier: every value of a chain (issue #36)

`Setup`: the static facts about block `b` of `f` and its chain in `g` (`chainRuns?`, `blockOK`).
`Cov`: the source facts a value of the chain needs, by role (a kept non-`Phi` value, a run's
store and a nil check copied: the source evaluated them in the reference frame `Gr`; the `WB`:
the run's memory is a memory). `local_seg`/`local_t`: a non-`Phi` value listed in a segment or
a buffer block of the chain whose `Cov` holds evaluates as `QR` says (`LocalQ`), dispatching on
`roleOf` to the local steps of `WBLocal`.
-/

namespace GoFV.Proof.WB

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.WBCheck GoFV.Proof

/-- The static facts about block `b` of `f` (table entry `B`) and its chain (runs `rs`, last
block `l`) in `g`. -/
structure Setup (c : WBCheck.Ctx) (b : ID) (B : Block) (rs : List Run) (l : ID) : Prop where
  ctx : ctxOf c.tabs c.f c.g = some c
  wf : ∃ ce, WF ce c.f
  wg : ∃ ce, WF ce c.g
  entry : c.g.entry = c.f.entry
  own : c.g.ownAux = c.f.ownAux
  memTy : memTyOK c.tabs c.f = true
  hb : b ∈ c.f.blocks
  hB : c.f.block? b = some B
  ch : chainRuns? c.f c.g b = some (rs, l)
  ok : c.blockOK b = true

/-- `x` is listed in segment `j` of the chain. -/
def InSeg (c : WBCheck.Ctx) (b : ID) (rs : List Run) (j : Nat) (x : ID) : Prop :=
  ∃ s, (segsOf b rs)[j]? = some s ∧ x ∈ vals c.g s

/-- `x` is listed in the buffer block of run `j`. -/
def InT (c : WBCheck.Ctx) (rs : List Run) (j : Nat) (x : ID) : Prop :=
  ∃ r, rs[j]? = some r ∧ x ∈ vals c.g r.sp.t

/-- The source evaluated `x` in `Gr`. -/
def Ev (env : Env) (c : WBCheck.Ctx) (Gr : Frame) (x : ID) : Prop :=
  ∃ u y, c.f.value? x = some u ∧ Gr.regs[x]? = some (some y) ∧
    evalValue env (Ctx.make c.tabs c.f) Gr u = .ok y

/-- The source facts a value of the chain needs, by role. -/
def Cov (env : Env) (c : WBCheck.Ctx) (rs : List Run) (Gr : Frame) (x : ID) : Prop :=
  match c.roleOf rs x with
  | .held => c.K.getD x false = true → ∀ u, c.f.value? x = some u → u.op ≠ .Phi → Ev env c Gr x
  | .tgt j k => ∃ r s, rs[j]? = some r ∧ r.src[k]? = some s ∧ Ev env c Gr s
  | .ncEnd j => ∃ r n, rs[j]? = some r ∧ r.nc = some n ∧ Ev env c Gr n
  | .ncThen j => ∃ r n, rs[j]? = some r ∧ r.nc = some n ∧ Ev env c Gr n
  | .wb j => ∃ M, RunMem Gr rs j M
  | _ => True

namespace Setup

variable {c : WBCheck.Ctx} {b : ID} {B : Block} {rs : List Run} {l : ID}

/-- **A value of a segment.** -/
theorem local_seg (S : Setup c b B rs l) {env : Env} {Gr fr0 : Frame}
    (hGr : Gr = { fr0 with regs := Gr.regs }) (hH : HeldGr c rs Gr) (hM : MemsGr Gr)
    {j : Nat} {x : ID} {w : Value} (hx : InSeg c b rs j x) (hw : c.g.value? x = some w)
    (hnp : w.op ≠ .Phi) (hcov : Cov env c rs Gr x) :
    LocalQ env (Ctx.make c.tabs c.g) fr0 (QR c rs Gr) x := by
  sorry

/-- **A value of a buffer block.** -/
theorem local_t (S : Setup c b B rs l) {env : Env} {Gr fr0 : Frame}
    (hH : HeldGr c rs Gr) (hM : MemsGr Gr)
    {j : Nat} {x : ID} {w : Value} (hx : InT c rs j x) (hw : c.g.value? x = some w)
    (hcov : Cov env c rs Gr x) :
    LocalQ env (Ctx.make c.tabs c.g) fr0 (QR c rs Gr) x := by
  sorry

end Setup

end GoFV.Proof.WB

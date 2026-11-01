import GoFV.SSA.Sem.Run

/-!
# Contracts that cannot see unreachable frame temporaries (#31)

A `Blk.temp` is a frame variable whose address the program never takes as a user variable
(`Tables.forgeable`); no integer converts back to it (`Ptr.ofAddr_ne_temp`). `Contract.FrameSafe`:
a callee given arguments, closure context and memory that hold no pointer into a set `U` of
`temp` blocks behaves the same whatever those blocks hold, and returns no pointer into them.
`dead auto elim`'s theorem holds for environments whose contracts are frame-safe
(`Env.FrameSafe`), as Go's runtime is (it only follows the pointers it is given).
-/

namespace GoFV.SSA.Sem

/-- `x` is not a fragment of a pointer into `U`. -/
def Byte.Avoids (U : Blk → Prop) : Byte → Prop
  | .frag p _ => ¬ U p.blk
  | _ => True

/-- No byte of an allocation outside `U` is a fragment of a pointer into `U`. -/
def Mem.Avoids (U : Blk → Prop) (m : Mem) : Prop :=
  ∀ b a, (b, a) ∈ m.blocks.toList → ¬ U b → ∀ x ∈ a.data.toList, Byte.Avoids U x

mutual
/-- `v` holds no pointer into `U` (nor a fragment of one), componentwise. -/
def Val.Avoids (U : Blk → Prop) : Val → Prop
  | .ptr p => ¬ U p.blk
  | .tuple vs => Val.AvoidsList U vs
  | .agg vs => Val.AvoidsList U vs
  | .blob bs => ∀ x ∈ bs, Byte.Avoids U x
  | .mem m => m.Avoids U
  | _ => True
def Val.AvoidsList (U : Blk → Prop) : List Val → Prop
  | [] => True
  | v :: vs => Val.Avoids U v ∧ Val.AvoidsList U vs
end

/-- `m` and `m'` have the same allocations (order, sizes, writability) and counters, and the
same bytes outside `U`. -/
def Mem.EqOff (U : Blk → Prop) (m m' : Mem) : Prop :=
  m.nextHeap = m'.nextHeap ∧ m.nextAct = m'.nextAct ∧ m.blocks.size = m'.blocks.size ∧
  ∀ (i : Nat) b b' a a', m.blocks[i]? = some (b, a) → m'.blocks[i]? = some (b', a') →
    b = b' ∧ a.data.size = a'.data.size ∧ a.writable = a'.writable ∧ (¬ U b → a.data = a'.data)

/-- A contract cannot observe or leak `temp` blocks it is given no pointer to. -/
def Contract.FrameSafe (c : Contract) : Prop :=
  ∀ (U : Blk → Prop), (∀ b, U b → ∃ a n, b = .temp a n) →
  ∀ args clo m m', (∀ v ∈ args, v.Avoids U) → (∀ v ∈ clo, v.Avoids U) → m.Avoids U →
    Mem.EqOff U m m' →
    match c args clo m, c args clo m' with
    | .stuck _, _ => True
    | .returned rs r, .returned rs' r' =>
      rs' = rs ∧ (∀ v ∈ rs, v.Avoids U) ∧ r.Avoids U ∧ Mem.EqOff U r r'
    | .panicked e r, .panicked e' r' => e' = e ∧ r.Avoids U ∧ Mem.EqOff U r r'
    | _, _ => False

/-- Every contract of the environment is frame-safe. -/
def Env.FrameSafe (env : Env) : Prop := ∀ name c, env.extern name = some c → c.FrameSafe

/-- The inputs of a run hold no pointer into a `temp` block and the memory has none yet: the
arguments, the memory's other allocations and the global image avoid every `temp` block (a
pointer into the run's frame temporaries cannot exist before the frame does). -/
def InitAvoids (env : Env) (args : List Val) (mem : Mem) : Prop :=
  ∀ a n, (∀ v ∈ args, v.Avoids (· = .temp a n)) ∧ mem.Avoids (· = .temp a n) ∧
    mem.find? (.temp a n) = none ∧
    ∀ g ∈ env.globals, ∀ x ∈ g.2.data.toList, Byte.Avoids (· = .temp a n) x

/-- **No integer converts to a `temp` block.** -/
theorem Ptr.ofAddr_ne_temp (x : BitVec 64) (a n : Nat) : (Ptr.ofAddr x).blk ≠ .temp a n := by
  unfold Ptr.ofAddr
  simp only
  split
  · nofun
  · split
    · nofun
    · split <;> nofun

theorem frameBlk_temp {tabs : Tables} {n : AuxRef} (h : tabs.forgeable n = false) (act : Nat) :
    frameBlk tabs act n = .temp act n := by
  unfold frameBlk; rw [h]; rfl

theorem frameBlk_local {tabs : Tables} {n : AuxRef} (h : tabs.forgeable n = true) (act : Nat) :
    frameBlk tabs act n = .local act n := by
  unfold frameBlk; rw [h]; rfl

/-- A `LocalAddr` points to its variable's frame block. -/
theorem frameVal_localAddr {ctx : Ctx} {v : Value} {n : AuxRef} (hop : v.op = .LocalAddr)
    (hax : v.aux = some n) : frameVal ctx v = some (.ptr ⟨frameBlk ctx.tabs ctx.act n, 0⟩) := by
  unfold frameVal; rw [hop, hax]; rfl

end GoFV.SSA.Sem

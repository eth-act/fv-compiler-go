import GoFV.Proof.RoImage

variable [GoFV.SSA.Sem.Addrs]

/-!
# Contracts keep the caller's frame (`Env.FrameKeep`, issue #28)

After `expand calls`, a function stores its stack-assigned results into their frame slots
(`PPARAMOUT` variables, `Blk.local`) just before it returns; before, the results are values of
its `MakeResult`. The stores must not get stuck where the source returns, so the result slots
must still be allocated and writable after the calls the function made. Nothing in the semantics
ties a contract's returned memory to the caller's frame. The environment precondition
`Env.FrameKeep`: every contract keeps the frame allocations (`Blk.local`, `Blk.temp`,
`Blk.outargs`) of the memory it is given, with their sizes and writability (`Mem.KeepsFrame`),
and returns no memory. The runtime's contracts only write and allocate heap blocks
(`Env.runtime_frameKeep`).
-/

namespace GoFV.SSA.Sem

open GoFV.Proof

/-- A frame block: a frame variable or the outgoing-arguments area of an activation. -/
def Blk.isFrame : Blk → Bool
  | .local _ _ | .temp _ _ | .outargs _ => true
  | _ => false

/-- What a write needs of an allocation: its writability and size. -/
def Alloc.attr (a : Alloc) : Bool × Nat := (a.writable, a.data.size)

/-- `m'` keeps the frame allocations of `m`: every frame block allocated in `m` is allocated in
`m'` with the same writability and size. -/
def Mem.KeepsFrame (m m' : Mem) : Prop :=
  ∀ b a, b.isFrame = true → m.find? b = some a → (m'.find? b).map Alloc.attr = some a.attr

/-- **A contract keeps the caller's frame**: its returned memory keeps the frame allocations of
the memory it is given, and it returns no memory. -/
def Contract.FrameKeep (c : Contract) : Prop := c.Keeps Mem.KeepsFrame

/-- **Every contract of the environment keeps the caller's frame.** -/
def Env.FrameKeep (env : Env) : Prop := ∀ name c, env.extern name = some c → c.FrameKeep

theorem Mem.KeepsFrame.refl (m : Mem) : m.KeepsFrame m := fun _ a _ h => by rw [h]; rfl

theorem Mem.KeepsFrame.trans {m1 m2 m3 : Mem} (h1 : m1.KeepsFrame m2) (h2 : m2.KeepsFrame m3) :
    m1.KeepsFrame m3 := fun b a hb ha => by
  have h := h1 b a hb ha
  cases h2' : m2.find? b with
  | none => rw [h2'] at h; cases h
  | some a2 =>
    rw [h2'] at h
    rw [h2 b a2 hb h2']
    exact h

/-- A write keeps every allocation's writability and size. -/
theorem Mem.find_write_attr {m m' : Mem} {p : Ptr} {bs : Array Byte} (hw : m.write p bs = some m')
    (b : Blk) : (m'.find? b).map Alloc.attr = (m.find? b).map Alloc.attr := by
  unfold Mem.write at hw
  by_cases he : bs.isEmpty = true
  · simp only [he, ite_true] at hw; cases hw; rfl
  simp only [he, Bool.false_eq_true, ite_false] at hw
  cases ha : m.find? p.blk with
  | none => rw [ha] at hw; cases hw
  | some a =>
    rw [ha] at hw
    simp only [Option.bind_eq_bind, Option.bind_some] at hw
    split at hw
    · cases hw
      rw [CSE.Mem.find?_set]
      split
      · next hb =>
        subst hb; rw [ha]
        simp only [Option.map_some, Alloc.attr, CSE.Mem.foldl_set_size]
      · rfl
    · cases hw

/-- A fresh heap allocation keeps the frame allocations. -/
theorem Mem.keepsFrame_allocHeap (m : Mem) (data : Array Byte) :
    m.KeepsFrame (m.allocHeap data).2 := fun b a hb ha => by
  simp only [Mem.allocHeap]
  change ((m.set (.heap m.nextHeap) { data }).find? b).map Alloc.attr = _
  rw [CSE.Mem.find?_set]
  split
  · next h => subst h; cases hb
  · rw [ha]; rfl

/-- Writes and fresh heap allocations keep the frame allocations. -/
theorem Mem.keepsFrame_steps : MemSteps Mem.KeepsFrame :=
  ⟨Mem.KeepsFrame.refl, fun h1 h2 => h1.trans h2,
    fun hw b a _ ha => by rw [Mem.find_write_attr hw, ha]; rfl, Mem.keepsFrame_allocHeap⟩

/-- **The runtime's contracts keep the caller's frame**: they only write and allocate heap
blocks. -/
theorem Env.runtime_frameKeep : Env.runtime.FrameKeep := Env.runtime_keeps Mem.keepsFrame_steps

/-- `Env.p1`'s contracts only panic. -/
theorem Env.p1_frameKeep : Env.p1.FrameKeep := Env.p1_keeps _

end GoFV.SSA.Sem

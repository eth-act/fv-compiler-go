import GoFV.SSA.Sem.RunMach
import GoFV.SSA.Sem.Mem
import Std.Data.HashMap

variable [GoFV.SSA.Sem.Addrs]

/-!
# The injection `ι` executed: Phase 1 memory in the flat machine memory (`docs/plans/semantics3.md` §4.3)

`LocMatch.lean` states the relation of a Phase 1 memory (`Mem`, blocks with provenance) and the
machine's flat memory through an injection `ι : Blk → Option (BitVec 64)`. This module is the
executable side of the same injection, used by the runtime hooks (`Hooks.lean`), which lift
Phase 1's runtime contracts to the machine, and by the native difftest (`GoFVTest/MachDiff.lean`):

* **Addresses.** Heap blocks sit at Phase 1's own concrete addresses, `heap n ↦ (n + 1)·2^40`
  (`Blk.base?`), so a pointer converted to an integer has the same value in both semantics and
  heap pointers need no translation. Every other block the machine knows (globals with their
  linked addresses, code symbols, runtime entry points, the stack) is a `Window` of the static
  `Layout`, below `2^40`.
* **Allocator state in machine memory.** The runtime's private table at `Layout.rt` holds the
  number of heap blocks and each block's size (`rt`: `nextHeap`; `rt + 8 + 8n`: the size of
  `heap n`), so `ι` is a function of the machine state and the hooks are functions of the state
  (`Hooks.call : MState → …`), as the real runtime's allocator keeps its spans in memory.
* **Pulling back** (`Layout.pull`): the blocks reachable from a set of roots, read from the
  machine; an aligned word of a window block that holds an address inside a window is the
  pointer's eight `Byte.frag`s (heap addresses stay concrete bytes: `decodePtr` reads them as the
  heap pointer they encode).
* **Pushing forward** (`Layout.pushWrites`): the bytes of a Phase 1 memory as machine bytes,
  fragments as the bytes of the injected address, `poison` bytes leaving the machine's byte.
-/

namespace GoFV.Arm64

open GoFV.SSA.Sem

/-- A block of the static layout: its machine address and size. `data`: its bytes are Phase 1
memory (globals, the stack); otherwise only its address is (code, runtime entry points). -/
structure Window where
  blk : Blk
  base : BitVec 64
  size : Nat
  data : Bool
  writable : Bool := true
  deriving Inhabited, Repr

/-- The static part of `ι` and the runtime's private table (build with `Layout.make`). -/
structure Layout where
  /-- The windows, sorted by base address, pairwise disjoint (ends included). -/
  windows : Array Window
  /-- The runtime's allocator table: `nextHeap` at `rt`, the size of `heap n` at `rt + 8 + 8n`. -/
  rt : BitVec 64
  /-- The index in `windows` of each window's block. -/
  index : Std.HashMap Blk Nat := {}
  deriving Inhabited

/-- The layout of windows `ws` (sorted and indexed). -/
def Layout.make (ws : Array Window) (rt : BitVec 64) : Layout :=
  let ws := ws.qsort (·.base.toNat < ·.base.toNat)
  { windows := ws, rt, index := (List.range ws.size).foldl (fun m i => m.insert ws[i]!.blk i) {} }

/-- Where Phase 1 puts `heap n` (`Blk.base?`). -/
def heapBase (n : Nat) : BitVec 64 := BitVec.ofNat 64 ((n + 1) * 2 ^ 40)

namespace Layout

/-- The number of heap blocks the runtime has allocated. -/
def nextHeap (L : Layout) (s : MState) : Nat := (s.word L.rt).toNat

/-- The size of `heap n`. -/
def heapSize (L : Layout) (s : MState) (n : Nat) : Nat :=
  (s.word (L.rt + 8 + BitVec.ofNat 64 (8 * n))).toNat

/-- The window of block `b`. -/
def window? (L : Layout) (b : Blk) : Option Window := (L.index.get? b).bind (L.windows[·]?)

/-- `ι` in state `s`. -/
def ι (L : Layout) (s : MState) : Blk → Option (BitVec 64)
  | .nil => some 0
  | .heap n => if n < L.nextHeap s then some (heapBase n) else none
  | b => (L.window? b).map (·.base)

/-- The machine address of a pointer. -/
def addr? (L : Layout) (s : MState) (p : Ptr) : Option (BitVec 64) :=
  (L.ι s p.blk).map (· + p.off)

/-- The pointer into a window an address denotes (its end included: a pointer one past the
end of a block, as `Ptr` allows): the last window whose base is at most the address (binary
search). -/
def windowPtr? (L : Layout) (a : BitVec 64) : Option Ptr :=
  let base (i : Nat) : Nat := (L.windows[i]?.map (·.base.toNat)).getD 0
  let rec go : Nat → Nat → Nat → Nat
    | 0, lo, _ => lo
    | n + 1, lo, hi =>
      if lo + 1 < hi then
        let mid := (lo + hi) / 2
        if base mid ≤ a.toNat then go n mid hi else go n lo mid
      else lo
  match L.windows[go 64 0 L.windows.size]? with
  | some w =>
    if w.base.toNat ≤ a.toNat && a.toNat ≤ w.base.toNat + w.size then some ⟨w.blk, a - w.base⟩
    else none
  | none => none

/-- The pointer an address denotes, if it is in a block of `s` (a window or an allocated heap
block). -/
def ptrOf? (L : Layout) (s : MState) (a : BitVec 64) : Option Ptr :=
  match L.windowPtr? a with
  | some p => some p
  | none =>
    let p := Ptr.ofAddr a
    match p.blk with
    | .heap n => if n < L.nextHeap s && p.off.toNat ≤ L.heapSize s n then some p else none
    | _ => none

/-- The machine byte of a Phase 1 byte (`none`: `poison`, or a fragment of an unmapped
pointer). -/
def pushByte (L : Layout) (s : MState) : Byte → Option (BitVec 8)
  | .b x => some x
  | .frag p i => (L.addr? s p).map fun a => a.extractLsb' (8 * (i % 8)) 8
  | .poison => none

/-- `n` machine bytes at `a` as Phase 1 bytes: concrete, except that an 8-aligned word holding an
address inside a window is that pointer's fragments. -/
def pullBytes (L : Layout) (s : MState) (a : BitVec 64) (n : Nat) : Array Byte := Id.run do
  let mut out : Array Byte := Array.mkEmpty n
  let mut i := 0
  while i < n do
    let x := a + BitVec.ofNat 64 i
    if x.toNat % 8 == 0 && i + 8 ≤ n then
      match L.windowPtr? (s.word x) with
      | some p =>
        out := out ++ ptrBytes p
        i := i + 8
        continue
      | none => pure ()
    out := out.push (.b (s.mem x))
    i := i + 1
  return out

/-- The allocation of block `b` read from the machine, if it is mapped with data. -/
def pullBlock (L : Layout) (s : MState) : Blk → Option Alloc
  | .heap n =>
    if n < L.nextHeap s then some { data := L.pullBytes s (heapBase n) (L.heapSize s n) } else none
  | b => match L.window? b with
    | some w => if w.data then some { data := L.pullBytes s w.base w.size, writable := w.writable }
      else none
    | none => none

/-- The blocks a byte array points to (fragments and concrete heap addresses). -/
def pointees (L : Layout) (s : MState) (bs : Array Byte) : List Blk := Id.run do
  let mut out : List Blk := []
  let mut i := 0
  while i < bs.size do
    match bs[i]! with
    | .frag p _ => out := p.blk :: out; i := i + 1
    | .b _ =>
      if i + 8 ≤ bs.size then
        match bytesNat? (bs.extract i (i + 8)) with
        | some w =>
          match L.ptrOf? s (BitVec.ofNat 64 w) with
          | some p => out := p.blk :: out
          | none => pure ()
        | none => pure ()
      i := i + 1
    | .poison => i := i + 1
  return out

/-- The Phase 1 memory of the blocks reachable from `roots` (at most `fuel` blocks), with
`nextHeap` the runtime's: what a runtime entry point sees (§6: the runtime functions the hooks
model follow pointers from their arguments; blocks they cannot reach keep their bytes). Pointers
are followed out of writable blocks only: a read-only block (type descriptors, string data,
constants) is read where an argument points, and the runtime functions the hooks model do not
dereference the pointers stored in it (a type descriptor's element type, …). -/
def pull (L : Layout) (s : MState) (roots : List Blk) (fuel : Nat := 4096) : Mem := Id.run do
  let mut m : Mem := { nextHeap := L.nextHeap s }
  let mut todo := roots
  for _ in [0:fuel] do
    match todo with
    | [] => break
    | b :: rest =>
      todo := rest
      if (m.find? b).isSome then continue
      match L.pullBlock s b with
      | some a =>
        m := m.set b a
        if a.writable then todo := L.pointees s a.data ++ todo
      | none => pure ()
  return m

/-- The machine writes that make the blocks of `m` the machine's (after `m'`, the memory the
blocks were pulled into, every block of `m` that differs from `m'`): the allocator table for
new heap blocks, then each changed block's bytes (pushed with the table already updated, so
fragments of new blocks have their addresses). `none` if a block of `m` has no address. -/
def pushWrites (L : Layout) (s : MState) (m0 m : Mem) : Option (Array (BitVec 64 × BitVec 8)) := do
  let mut ws : Array (BitVec 64 × BitVec 8) := #[]
  let word (a : BitVec 64) (x : Nat) : Array (BitVec 64 × BitVec 8) :=
    (List.range 8).toArray.map fun i => (a + BitVec.ofNat 64 i, BitVec.ofNat 8 (x / 2 ^ (8 * i)))
  -- the allocator table
  let old := L.nextHeap s
  if m.nextHeap > old then
    ws := ws ++ word L.rt m.nextHeap
    for n in [old:m.nextHeap] do
      let size := ((m.find? (.heap n)).map (·.data.size)).getD 0
      ws := ws ++ word (L.rt + 8 + BitVec.ofNat 64 (8 * n)) size
  let tbl : Std.HashMap (BitVec 64) (BitVec 8) := Std.HashMap.ofList ws.toList
  let s' : MState := { s with mem := fun a => tbl.getD a (s.mem a) }
  for (b, a) in m.blocks do
    if m0.find? b == some a then continue
    let base ← L.ι s' b
    for i in [0:a.data.size] do
      match L.pushByte s' a.data[i]! with
      | some x => ws := ws.push (base + BitVec.ofNat 64 i, x)
      | none => pure ()
  return ws

end Layout

/-- `s` with the bytes `ws` written (later writes win). -/
def MState.withWrites (s : MState) (ws : Array (BitVec 64 × BitVec 8)) : MState :=
  if ws.isEmpty then s else
  let tbl : Std.HashMap (BitVec 64) (BitVec 8) := Std.HashMap.ofList ws.toList
  { s with mem := fun a => tbl.getD a (s.mem a) }

end GoFV.Arm64

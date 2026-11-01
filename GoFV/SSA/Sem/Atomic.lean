import GoFV.SSA.Value
import GoFV.SSA.Sem.Cmp
import GoFV.SSA.Sem.Mem
import GoFV.SSA.Sem.Env

/-!
# Atomics, barriers, prefetch (`docs/plans/semantics.md` §9.5, phase P5)

The roots among `sync/atomic`'s and `internal/runtime/atomic`'s intrinsics (`AtomicLoad*` only
read and are pure, `Sem/Ptr.lean`). `run` executes one goroutine, so an atomic op is its
sequentially consistent single-threaded meaning: a read-modify-write of a naturally aligned
location in one step, ordered by the memory chain like every root. The acquire/release forms
(`AtomicStoreRel*`, `AtomicCompareAndSwapRel32`) and the `*Variant` forms (arm64's LSE
instructions, chosen by `HasCPUFeature`) mean the same. An access that is not naturally
aligned, invalid or read-only is `stuck` (arm64 faults); a `poison` operand is stored as poison
bytes like a plain `Store`, and a compare-and-swap on a `poison` value is `stuck` (it decides
whether memory changes).

`PubBarrier` (a data barrier) and `PrefetchCache*` (a hint; the address is not accessed) have
no effect on memory.
-/

namespace GoFV.SSA.Sem

namespace Atomic

/-- The read-modify-write an atomic op performs. -/
inductive Kind where
  /-- `AtomicStore*`: store the operand; result: memory. -/
  | store
  /-- `AtomicExchange*`: store the operand; result: (old value, memory). -/
  | exchange
  /-- `AtomicAdd*`: store old + operand; result: (new value, memory). -/
  | add
  /-- `AtomicAnd8/32`, `AtomicOr8/32`: store old &/| operand; result: memory. -/
  | and | or
  /-- `AtomicAnd*value`, `AtomicOr*value`: store old &/| operand; result: (old value, memory). -/
  | andOld | orOld
  deriving DecidableEq, Repr

/-- The read-modify-write of an atomic root and the shape of the location (`none`: not one). -/
def info? : Op → Option (Kind × Ty)
  | .AtomicStore8 | .AtomicStore8Variant => some (.store, .int .w8)
  | .AtomicStore32 | .AtomicStore32Variant | .AtomicStoreRel32 => some (.store, .int .w32)
  | .AtomicStore64 | .AtomicStore64Variant | .AtomicStoreRel64 => some (.store, .int .w64)
  | .AtomicStorePtrNoWB => some (.store, .ptr none)
  | .AtomicExchange8 | .AtomicExchange8Variant => some (.exchange, .int .w8)
  | .AtomicExchange32 | .AtomicExchange32Variant => some (.exchange, .int .w32)
  | .AtomicExchange64 | .AtomicExchange64Variant => some (.exchange, .int .w64)
  | .AtomicAdd32 | .AtomicAdd32Variant => some (.add, .int .w32)
  | .AtomicAdd64 | .AtomicAdd64Variant => some (.add, .int .w64)
  | .AtomicAnd8 => some (.and, .int .w8)
  | .AtomicAnd32 => some (.and, .int .w32)
  | .AtomicOr8 => some (.or, .int .w8)
  | .AtomicOr32 => some (.or, .int .w32)
  | .AtomicAnd8value | .AtomicAnd8valueVariant => some (.andOld, .int .w8)
  | .AtomicAnd32value | .AtomicAnd32valueVariant => some (.andOld, .int .w32)
  | .AtomicAnd64value | .AtomicAnd64valueVariant => some (.andOld, .int .w64)
  | .AtomicOr8value | .AtomicOr8valueVariant => some (.orOld, .int .w8)
  | .AtomicOr32value | .AtomicOr32valueVariant => some (.orOld, .int .w32)
  | .AtomicOr64value | .AtomicOr64valueVariant => some (.orOld, .int .w64)
  | _ => none

/-- The width of a compare-and-swap (`none`: not one). -/
def casWidth? : Op → Option Width
  | .AtomicCompareAndSwap32 | .AtomicCompareAndSwap32Variant | .AtomicCompareAndSwapRel32 =>
    some .w32
  | .AtomicCompareAndSwap64 | .AtomicCompareAndSwap64Variant => some .w64
  | _ => none

/-- The ops `atomicRoot` gives a meaning (every other root is `stuck`). -/
def modelled (op : Op) : Bool :=
  (info? op).isSome || (casWidth? op).isSome || op == .PubBarrier || op == .PrefetchCache ||
    op == .PrefetchCacheStreamed

/-- The value stored and the value returned (`none`: the op returns only memory), from the old
value `old` and the operand `x` (`w`: the width of the integer forms). -/
def step (k : Kind) (w : Width) (old x : Val) : Val × Option Val :=
  match k with
  | .store => (x, none)
  | .exchange => (x, some old)
  | .add => (Int.add w [old, x], some (Int.add w [old, x]))
  | .and => (Int.and w [old, x], none)
  | .or => (Int.or w [old, x], none)
  | .andOld => (Int.and w [old, x], some old)
  | .orOld => (Int.or w [old, x], some old)

/-- An `n`-byte access at `p` is naturally aligned (offsets within an allocation; every
allocation is at least 8-aligned, `Blk.base?`). -/
def aligned (p : Ptr) (n : Nat) : Bool := n != 0 && p.off.toNat % n == 0

/-- The result of an atomic op: the value it returns (if any) and the new memory. -/
def result (r : Option Val) (m : Mem) : Val :=
  match r with
  | some y => .tuple [y, .mem m]
  | none => .mem m

/-- An unmodelled root, or a root with ill-shaped (e.g. `poison`) arguments. -/
def unmodelled (v : Value) : Res Val := .stuck s!"v{v.id}: {v.op.name} is not in phases P1–P5"

/-- The integer width `step` computes in for a location of shape `t`. -/
def width : Ty → Width
  | .int w => w
  | _ => .w64

/-- The read-modify-write `k` of root `v` on the `t`-shaped location at `p` with operand `x`. -/
def rmw (v : Value) (k : Kind) (t : Ty) (p : Ptr) (x : Val) (m : Mem) : Res Val :=
  if aligned p t.size then
    match m.write p (encode t (step k (width t) (m.load t p) x).1) with
    | some m' => .ok (result (step k (width t) (m.load t p) x).2 m')
    | none => .stuck s!"v{v.id}: {v.op.name}: invalid or read-only access"
  else .stuck s!"v{v.id}: {v.op.name}: misaligned"

/-- The `w`-bit compare-and-swap of root `v` at `p`: `n` replaces `o`. -/
def cas (v : Value) (w : Width) (p : Ptr) (o n : Val) (m : Mem) : Res Val :=
  if aligned p w.bytes then
    match (m.load (.int w) p).asInt w, o.asInt w with
    | some cur, some old =>
      if cur = old then
        match m.write p (encode (.int w) n) with
        | some m' => .ok (.tuple [.bool true, .mem m'])
        | none => .stuck s!"v{v.id}: {v.op.name}: invalid or read-only access"
      else .ok (.tuple [.bool false, .mem m])
    | _, _ => .stuck s!"v{v.id}: {v.op.name}: poison or invalid comparison"
  else .stuck s!"v{v.id}: {v.op.name}: misaligned"

/-- `PubBarrier mem`. -/
def barrier (v : Value) : Val → Res Val
  | .mem m => if v.op = .PubBarrier then .ok (.mem m) else unmodelled v
  | _ => unmodelled v

/-- `PrefetchCache* addr mem` (the address is not accessed). -/
def prefetch (v : Value) : Val → Res Val
  | .mem m =>
    if v.op = .PrefetchCache ∨ v.op = .PrefetchCacheStreamed then .ok (.mem m) else unmodelled v
  | _ => unmodelled v

/-- A read-modify-write root `p x mem`. -/
def rmwRoot (v : Value) : Val → Val → Val → Res Val
  | .ptr p, x, .mem m =>
    match info? v.op with
    | some (k, t) => rmw v k t p x m
    | none => unmodelled v
  | _, _, _ => unmodelled v

/-- A compare-and-swap root `p old new mem`. -/
def casRoot (v : Value) : Val → Val → Val → Val → Res Val
  | .ptr p, o, n, .mem m =>
    match casWidth? v.op with
    | some w => cas v w p o n m
    | none => unmodelled v
  | _, _, _, _ => unmodelled v

end Atomic

open Atomic in
/-- The P5 roots other than calls and memory roots (`memRoot`): atomic read-modify-writes
(`Atomic.info?`), compare-and-swap (`Atomic.casWidth?`), `PubBarrier`, `PrefetchCache*`. Any
other root is `stuck` (its semantics is not modelled: `GetG`, `TailLECall*`, …). Dispatched on
the number of arguments only, so that refined arguments take the same arm. -/
def atomicRoot (v : Value) (argv : List Val) : Res Val :=
  match argv with
  | [a] => barrier v a
  | [_, a] => prefetch v a
  | [a, b, c] => rmwRoot v a b c
  | [a, b, c, d] => casRoot v a b c d
  | _ => unmodelled v

end GoFV.SSA.Sem

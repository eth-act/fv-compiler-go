import GoFV.Proof.RunMono
import GoFV.Proof.Eval

/-!
# Witnesses for the atomic roots (`Sem/Atomic.lean`, §9.5)

A 4-byte heap word holding 1. `AtomicAdd32 p 2 mem` returns the new value 3 and stores it;
`AtomicCompareAndSwap32 p 1 7 mem` succeeds (stores 7), `… p 5 7 mem` fails (memory unchanged);
a misaligned access is `stuck`. `atomicRoot_mono` is applied to an argument list where `poison`
is refined by a defined operand, and `atomicRoot_ne_panic` to the add.
-/

namespace GoFV.Proof.Witness.AtomicW

open GoFV.SSA GoFV.SSA.Sem

/-- A 4-byte heap word holding 1. -/
def m0 : Mem := { blocks := #[(.heap 0, { data := #[.b 1, .b 0, .b 0, .b 0] })], nextHeap := 1 }

def p : Ptr := ⟨.heap 0, 0⟩

/-- A root `v1` with op `op`. -/
def root (op : Op) : Value :=
  { id := 1, op, type := 0, auxInt := 0, aux := none, pos := default, uses := 0, args := #[],
    block := 1 }

/-- `.ok (.tuple [x, .mem m])` with `x == r` and the word at `p` in `m` equal to `w`. -/
def okWith (r w : Val) : Res Val → Bool
  | .ok (.tuple [x, .mem m]) => x == r && m.load (.int .w32) p == w
  | _ => false

example : okWith (.i32 3) (.i32 3) (atomicRoot (root .AtomicAdd32) [.ptr p, .i32 2, .mem m0]) =
    true := by decide +kernel

example : okWith (.bool true) (.i32 7)
    (atomicRoot (root .AtomicCompareAndSwap32) [.ptr p, .i32 1, .i32 7, .mem m0]) = true := by
  decide +kernel

example : okWith (.bool false) (.i32 1)
    (atomicRoot (root .AtomicCompareAndSwap32) [.ptr p, .i32 5, .i32 7, .mem m0]) = true := by
  decide +kernel

example : (match atomicRoot (root .AtomicAdd32) [.ptr ⟨.heap 0, 2⟩, .i32 2, .mem m0] with
    | .stuck _ => true | _ => false) = true := by decide +kernel

example : Res.Refines (atomicRoot (root .AtomicAdd32) [.ptr p, .poison, .mem m0])
    (atomicRoot (root .AtomicAdd32) [.ptr p, .i32 2, .mem m0]) :=
  atomicRoot_mono _ (.cons (.ptr p) (.cons (.poison _) (.cons (.mem (Mem.Refines.refl m0)) .nil)))

example (e : Panic) (m : Mem) :
    atomicRoot (root .AtomicAdd32) [.ptr p, .i32 2, .mem m0] ≠ .panic e m :=
  atomicRoot_ne_panic

end GoFV.Proof.Witness.AtomicW

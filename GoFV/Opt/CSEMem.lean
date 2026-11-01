import GoFV.SSA.Func
import GoFV.SSA.Sem.Run

/-!
# cse's checker: loads through disjoint stores

cse merges two `Load`s of the same address whose memory arguments differ when both memory
chains reach the same def after skipping stores that cannot alias the load
(`getEffectiveMemoryArg`). The checker accepts such a merge only when it can re-derive the common
def with skips whose disjointness holds in the byte-level memory of the semantics: `memEnd`
walks the chain from a load's memory argument over `Store`/`Zero` defs that write a different
global symbol or local variable than the load reads, or the same base at a non-overlapping
offset (`disjointP`). Go's type-based (`disjointTypes`) and `VarDef` skips are not re-derived.

Widths are the semantic ones (`Sem.Ty.size` of the shapes `Load` reads and `Store` writes), and
offsets are compared modulo 2^64 (pointer offsets wrap). A pointer typed `uintptr`
(`Val.retype` turns it into its concrete address, which an `OffPtr` can move into another
variable) ends an `OffPtr` chain and names no allocation (`keepsPtr`).
-/

namespace GoFV.Opt.CSE

open GoFV.SSA

/-- The shape `run` gives value `v` (`Ctx.tys` at `v.id`). -/
def valShape (tabs : Tables) (f : Func) (v : Value) : Sem.Ty :=
  ((f.value? v.id).map fun w => tabs.ty w.type).getD .other

/-- `Val.retype` at shape `t` keeps every pointer a pointer (`t` is neither `uintptr`- nor
`bool`-shaped). -/
def keepsPtr : Sem.Ty → Bool
  | .int .w64 => false
  | .bool => false
  | _ => true

/-- `t` is not `bool`-shaped: `Val.retype` at `t` keeps a global pointer a pointer and a memory
a memory (at `bool` shape, non-booleans are `poison`). -/
def notBool : Sem.Ty → Bool
  | .bool => false
  | _ => true

/-- `baseAndOffset`: the base of an `OffPtr` chain and the summed offset. -/
def baseOff (tabs : Tables) (f : Func) : Nat → ID → Int → ID × Int
  | 0, p, off => (p, off)
  | n + 1, p, off =>
    match f.value? p with
    | some x =>
      if x.op == .OffPtr && x.args.size == 1 && keepsPtr (valShape tabs f x) then
        baseOff tabs f n x.args[0]! (off + x.auxInt.toInt)
      else (p, off)
    | none => (p, off)

/-- The allocation an `Addr`/`LocalAddr` base names: a global symbol's name or a local's aux. -/
inductive Alloc where
  | global (name : String)
  | local (n : AuxRef)
  deriving DecidableEq

/-- The allocation of base `b`, if it is an `Addr` of a symbol (not `bool`-shaped) or a
pointer-typed `LocalAddr` with a name. -/
def allocOf (tabs : Tables) (f : Func) (b : ID) : Option Alloc :=
  match f.value? b with
  | some x =>
    if x.op == .Addr && notBool (valShape tabs f x) then
      match x.aux.bind tabs.aux? with
      | some { kind := .sym name .., .. } => some (.global name.toStringLossy)
      | _ => none
    else if x.op == .LocalAddr && keepsPtr (valShape tabs f x) then x.aux.map .local
    else none
  | none => none

/-- `[op, op+w)` and `[oq, oq+wq)` are disjoint modulo 2^64. -/
def apart (op w oq wq : Int) : Bool :=
  let d := (oq - op) % 2 ^ 64
  w ≤ d && d + wq ≤ 2 ^ 64

/-- `[p, p+w)` and `[q, q+wq)` are disjoint: an empty access, different allocations, or the
same base (or bases naming the same allocation) at non-overlapping offsets. -/
def disjointP (tabs : Tables) (f : Func) (p : ID) (w : Int) (q : ID) (wq : Int) : Bool :=
  w == 0 || wq == 0 ||
  let (bp, op) := baseOff tabs f 64 p 0
  let (bq, oq) := baseOff tabs f 64 q 0
  if bp == bq then apart op w oq wq
  else
    match allocOf tabs f bp, allocOf tabs f bq with
    | some a, some b => a != b || apart op w oq wq
    | _, _ => false

/-- The def before `m` on a load's memory chain, if `m` is a `Store`/`Zero` whose write is
disjoint from the load of `w` bytes at `p`. -/
def memSkip (tabs : Tables) (f : Func) (p : ID) (w : Nat) (m : ID) : Option ID :=
  match f.value? m with
  | some d =>
    if d.op == .Store && d.args.size == 3 && notBool (valShape tabs f d) &&
        disjointP tabs f p w d.args[0]! (Sem.auxTy tabs d.aux).size then some d.args[2]!
    else if d.op == .Zero && d.args.size == 2 && notBool (valShape tabs f d) &&
        disjointP tabs f p w d.args[0]! d.auxInt.toInt then some d.args[1]!
    else none
  | none => none

/-- `memSkip` repeated at most `n` times. -/
def memWalk (tabs : Tables) (f : Func) (p : ID) (w : Nat) : Nat → ID → ID
  | 0, m => m
  | n + 1, m =>
    match memSkip tabs f p w m with
    | some m' => memWalk tabs f p w n m'
    | none => m

/-- The def a load of `t` at `p` with memory argument `m` reads through: the first def along the
chain that is not a `Store`/`Zero` disjoint from the load (at most 256 steps). -/
def memEnd (tabs : Tables) (f : Func) (p : ID) (t : TypeRef) (m : ID) : ID :=
  memWalk tabs f p (tabs.ty t).size 256 m

end GoFV.Opt.CSE

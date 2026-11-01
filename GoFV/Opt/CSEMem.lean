import GoFV.SSA.Func
import GoFV.Rules.Helpers.Types

/-!
# cse's checker: loads through disjoint stores

cse merges two `Load`s of the same address whose memory arguments differ when both memory
chains reach the same def after skipping stores that cannot alias the load
(`getEffectiveMemoryArg`). The checker accepts such a merge only when it can re-derive the common
def with skips whose disjointness holds in the byte-level memory of the semantics: `memEnd`
walks the chain from a load's memory argument over `Store`/`Zero` defs that write a different
global symbol or local variable than the load reads, or the same base at a non-overlapping
offset (`disjointP`). Go's type-based (`disjointTypes`) and `VarDef` skips are not re-derived.
-/

namespace GoFV.Opt.CSE

open GoFV.SSA

/-- `baseAndOffset`: the base of an `OffPtr` chain and the summed offset. -/
def baseOff (f : Func) : Nat → ID → Int → ID × Int
  | 0, p, off => (p, off)
  | n + 1, p, off =>
    match f.value? p with
    | some x => if x.op == .OffPtr && x.args.size == 1 then
        baseOff f n x.args[0]! (off + x.auxInt.toInt) else (p, off)
    | none => (p, off)

/-- The allocation an `Addr`/`LocalAddr` base names: a global symbol's name or a local's aux. -/
inductive Alloc where
  | global (name : String)
  | local (n : AuxRef)
  deriving BEq

/-- The allocation of base `b`, if it is an `Addr` of a symbol or a `LocalAddr` with a name. -/
def allocOf (tabs : Tables) (f : Func) (b : ID) : Option Alloc :=
  match f.value? b with
  | some x =>
    match x.op with
    | .Addr =>
      match x.aux.bind tabs.aux? with
      | some { kind := .sym name .., .. } => some (.global name.toStringLossy)
      | _ => none
    | .LocalAddr => x.aux.map .local
    | _ => none
  | none => none

/-- `[p, p+w)` and `[q, q+wq)` are disjoint: an empty access, different allocations, or the
same base at non-overlapping offsets. -/
def disjointP (tabs : Tables) (f : Func) (p : ID) (w : Int) (q : ID) (wq : Int) : Bool :=
  w == 0 || wq == 0 ||
  let (bp, op) := baseOff f 64 p 0
  let (bq, oq) := baseOff f 64 q 0
  if bp == bq then op + w ≤ oq || oq + wq ≤ op
  else
    match allocOf tabs f bp, allocOf tabs f bq with
    | some a, some b => a != b
    | _, _ => false

/-- The def a load of `t` at `p` with memory argument `m` reads through: the first def along the
chain that is not a `Store`/`Zero` disjoint from the load (at most 256 steps). -/
def memEnd (tabs : Tables) (f : Func) (p : ID) (t : TypeRef) (m : ID) : ID := Id.run do
  let w := (Rules.Ty.size tabs t).toOption.getD (-1)
  let mut m := m
  for _ in [0:256] do
    let some d := f.value? m | break
    match d.op with
    | .Store =>
      let some wq := (do Rules.Ty.size tabs (← Rules.Ty.ofAux tabs d.aux)).toOption | break
      if d.args.size == 3 && w ≥ 0 && disjointP tabs f p w d.args[0]! wq then m := d.args[2]!
      else break
    | .Zero =>
      if d.args.size == 2 && w ≥ 0 && disjointP tabs f p w d.args[0]! d.auxInt.toInt then
        m := d.args[1]!
      else break
    | _ => break
  return m

end GoFV.Opt.CSE

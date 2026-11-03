import GoFV.Opt.ElimDeadAutos
import Std.Data.TreeSet

/-!
# elim unread autos (`deadstore.go:433-501`, `elimUnreadAutos`)

Two scans (docs/PASSES2.md, elim unread autos; issue #394):

1. Over `f.Blocks` × `b.Values`, the values whose aux is an `*ir.Name` of class `PAUTO` or an
   ABIInternal `PPARAM`: an op whose `SymEffect` is exactly `SymNone` or `SymWrite` is queued if
   its name is not yet seen; any other effect marks the name seen, but only if the value has
   uses (dead loads are still around).
2. Each queued value whose name was never seen becomes `Copy(MemoryArg)` (aux and `AuxInt`
   cleared; type, position, ID and list position kept), in queue order.
-/

namespace GoFV.Opt

open GoFV.SSA

/-- `elimUnreadAutos(f)`; `abiInternal` is `f.ABISelf.Which() == obj.ABIInternal`. The seen
names are a `Std.TreeSet` (not a `HashSet`, which the kernel does not evaluate: the witness
`GoFV.Proof.Witness.elimUnreadAutosL_witness` runs the pass by `decide +kernel`). -/
def elimUnreadAutos (tabs : Tables) (isMem : TypeRef → Bool) (abiInternal : Bool) (f : Func) :
    Except String Func := do
  let mut seen : Std.TreeSet AuxRef := {}
  let mut stores : Array (ID × AuxRef) := #[]
  for b in f.blocks do
    for v in (f.getB b).values do
      let x := f.getV v
      let some n := ElimDeadAutos.autoName? tabs abiInternal x.aux | continue
      let e := x.op.symEffect
      if !e.read && !e.addr then
        if !seen.contains n then stores := stores.push (v, n)
      else if x.uses > 0 then
        seen := seen.insert n
  let mut f := f
  for (v, n) in stores do
    if seen.contains n then continue
    let x := f.getV v
    -- `v.MemoryArg()` (nil, which Go's `SetArgs1` would dereference, is a fatal error here)
    if x.op == .Phi then throw s!"v{v}: MemoryArg on Phi"
    let some m := x.args.back? | throw s!"v{v}: no memory argument"
    if !isMem (f.getV m).type then throw s!"v{v}: no memory argument"
    f := (f.setArgs1 v m).modV v fun y => { y with aux := none, auxInt := 0, op := .Copy }
  return f

/-- The `elim unread autos` pass. -/
def elimUnreadAutosPass : Pass := Pass.ofFunc fun env f => do
  let some mem := env.typ? "Mem" | throw "typs: no Mem"
  elimUnreadAutos env.tables (env.tables.isMemory mem) (env.abi == 1) f

end GoFV.Opt

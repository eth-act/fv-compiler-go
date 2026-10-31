import GoFV.Opt.Pass
import GoFV.SSA.Alloc
import GoFV.SSA.TypePred
import Std.Data.HashMap.Basic
import Std.Data.HashSet.Basic

/-!
# dead auto elim (`deadstore.go:240-429`, `elimDeadAutosGeneric`)

Tracks which values the address of each auto (or ABIInternal parameter) reaches. Stores,
`Move`s, `Zero`s and `VarDef`s of an auto that is never otherwise used become
`Copy(MemoryArg)`. The fixpoint runs at most 4 rounds over `f.Blocks` × `b.Values` and the
controls; if the 4th round still changes something, nothing is eliminated
(`docs/PASSES.md`, dead auto elim). Names are aux numbers (Go `*ir.Name` identity).

Go's map iterations here are order-independent: `usedAdd` computes a closure (ported as a
worklist), and the final rewrite touches only each eliminated value itself; the port rewrites
in first-recorded order.
-/

namespace GoFV.Opt

open GoFV.SSA

namespace ElimDeadAutos

structure St where
  /-- `addr`: values the address of an auto reaches. -/
  addr : Std.HashMap ID AuxRef := {}
  /-- `elim`: values to eliminate if their auto is unused, in first-recorded order. -/
  elim : Std.HashMap ID AuxRef := {}
  elimOrder : Array ID := #[]
  /-- `move[y]`: sources `x` of `Move &y &x` while `y` is unused. -/
  move : Std.HashMap AuxRef (Array AuxRef) := {}
  used : Std.HashSet AuxRef := {}

/-- `usedAdd(n)`: add `n` (and transitively its pending `move` sources) to `used`; whether `n`
was new. -/
def usedAdd (s : St) (n : AuxRef) : St × Bool := Id.run do
  if s.used.contains n then return (s, false)
  let mut s := s
  let mut work := #[n]
  -- each round adds a fresh name to `used`; the names are aux numbers below the move-map
  -- total, so the fuel bound is the number of pending sources plus one
  let fuel := s.move.fold (fun acc _ xs => acc + xs.size) 1
  for _ in [0:fuel + 1] do
    match work.back? with
    | none => break
    | some m =>
      work := work.pop
      if s.used.contains m then continue
      s := { s with used := s.used.insert m }
      if let some xs := s.move.get? m then
        s := { s with move := s.move.erase m }
        work := work ++ xs.reverse
  return (s, true)

/-- `n` is an `*ir.Name` of class `PAUTO`, or `PPARAM` of an ABIInternal function. -/
def autoName? (tabs : Tables) (abiInternal : Bool) (a : Option AuxRef) : Option AuxRef := do
  let a ← a
  let d ← tabs.aux? a
  match d.kind with
  | .name _ cls .. => if cls == .PAUTO || (cls == .PPARAM && abiInternal) then some a else none
  | _ => none

/-- `visit(v)`: update the maps; whether any changed. -/
def visit (f : Func) (tabs : Tables) (isMem : TypeRef → Bool) (flags : TypeRef)
    (abiInternal : Bool) (s : St) (v : ID) : Except String (St × Bool) := do
  let x := f.getV v
  let mut s := s
  let mut changed := false
  let mut args := x.args
  match x.op with
  | .Addr | .LocalAddr =>
    let some n := autoName? tabs abiInternal x.aux | return (s, false)
    if s.addr.contains v then return (s, false)
    return ({ s with addr := s.addr.insert v n }, true)
  | .VarDef =>
    let some n := autoName? tabs abiInternal x.aux | return (s, false)
    if s.elim.contains v then return (s, false)
    return ({ s with elim := s.elim.insert v n, elimOrder := s.elimOrder.push v }, true)
  | .VarLive =>
    let some n := autoName? tabs abiInternal x.aux | return (s, false)
    return usedAdd s n
  | .Store | .Move | .Zero =>
    if let some n := s.addr.get? x.args[0]! then
      if !s.elim.contains v then
        s := { s with elim := s.elim.insert v n, elimOrder := s.elimOrder.push v }
        changed := true
    args := args.extract 1
  | _ => pure ()
  if x.op.symEffect != ⟨false, false, false⟩ && x.op != .Arg then
    throw "unhandled op with sym effect"
  if (x.uses == 0 && !x.op.nilCheck && !x.op.call && !x.op.hasSideEffects) || args.isEmpty then
    return (s, changed)
  let memArg := match x.args.back? with
    | some m => isMem (f.getV m).type
    | none => false
  if isMem x.type || x.type == flags || x.op == .Phi || memArg then
    for a in args do
      if let some n := s.addr.get? a then
        if let some nam := s.elim.get? v then
          if x.op == .Move && !s.used.contains nam then
            if s.used.contains n then continue
            s := { s with move := s.move.insert nam ((s.move.getD nam #[]).push n) }
            continue
        let (s', c) := usedAdd s n
        s := s'
        changed := c || changed
    return (s, changed)
  -- propagate any auto addresses through v
  let mut node : Option AuxRef := none
  for a in args do
    if let some n := s.addr.get? a then
      match node with
      | none => if !s.used.contains n then node := some n
      | some nd =>
        if nd == n then continue
        let (s', c) := usedAdd s n
        s := s'
        changed := c || changed
  let some nd := node | return (s, changed)
  match s.addr.get? v with
  | none => return ({ s with addr := s.addr.insert v nd }, true)
  | some n =>
    if n != nd then
      let (s', c) := usedAdd s nd
      return (s', c || changed)
    return (s, changed)

/-- One round over `f.Blocks`: values, then the block's controls. -/
def round (f : Func) (tabs : Tables) (isMem : TypeRef → Bool) (flags : TypeRef)
    (abiInternal : Bool) (s : St) : Except String (St × Bool) := do
  let mut s := s
  let mut changed := false
  for b in f.blocks do
    let blk := f.getB b
    for v in blk.values do
      let (s', c) ← visit f tabs isMem flags abiInternal s v
      s := s'
      changed := c || changed
    for c in blk.controls do
      if let some n := s.addr.get? c then
        let (s', c) := usedAdd s n
        s := s'
        changed := c || changed
  return (s, changed)

/-- The fixpoint: at most 4 rounds; `none` if it did not converge (Go gives up). -/
def fixpoint (f : Func) (tabs : Tables) (isMem : TypeRef → Bool) (flags : TypeRef)
    (abiInternal : Bool) : Nat → St → Except String (Option St)
  | 0, _ => pure none
  | k + 1, s => do
    let (s, changed) ← round f tabs isMem flags abiInternal s
    if changed then fixpoint f tabs isMem flags abiInternal k s else pure (some s)

end ElimDeadAutos

/-- `elimDeadAutosGeneric(f)`; `abiInternal` is `f.ABISelf.Which() == obj.ABIInternal`. -/
def elimDeadAutosGeneric (tabs : Tables) (mem flags : TypeRef) (abiInternal : Bool) (f : Func) :
    Except String Func := do
  let isMem := tabs.isMemory mem
  let some s ← ElimDeadAutos.fixpoint f tabs isMem flags abiInternal 4 {} | return f
  let mut f := f
  for v in s.elimOrder do
    let n := s.elim.getD v 0
    if s.used.contains n then continue
    let x := f.getV v
    let some m := x.args.back? | throw s!"v{v}: no memory argument"
    if !isMem (f.getV m).type then throw s!"v{v}: no memory argument"
    f := (f.setArgs1 v m).modV v fun y => { y with aux := none, auxInt := 0, op := .Copy }
  return f

/-- The `dead auto elim` pass. -/
def elimDeadAutosPass : Pass := Pass.ofFunc fun env f => do
  let some mem := env.typ? "Mem" | throw "typs: no Mem"
  let some flags := env.typ? "Flags" | throw "typs: no Flags"
  elimDeadAutosGeneric env.tables mem flags (env.abi == 1) f

end GoFV.Opt

import GoFV.Opt.LowTy
import GoFV.SSA.Alloc
import GoFV.SSA.XPosMap
import GoFV.Util.SparseMap

/-!
# late nilcheck (`nilcheck.go:189-354`)

Port of `nilcheckelim2` (go1.27.3; docs/PASSES2.md, late nilcheck, #408). Each scheduled block
is walked backwards; `unnecessary` maps a pointer (value ID) to the index of the nearest later
value that faults when it is nil (`faultOnNilArg0/1`, loads only when `faultOnLoad`, i.e.
`GOOS != "aix"`; the offset must be below `minZeroPage`). A nil check of a recorded pointer is
reset to `Unknown` (not freed), and its position moves to the faulting value (the displaced
statement mark, or the check's own if on the same line, goes to `f.cachedLineStarts`). A value
that changes memory clears the map, except `VarLive` and `VarDef` of a pointer-free variable.
The block is then compacted from the first removed index; surviving values of a pending line
(not `notStmtBoundary`) take the mark, else the block. `Debug_checknil` only logs.
-/

namespace GoFV.Opt

open GoFV.SSA GoFV.Util

namespace NilCheckLate

/-- `minZeroPage`. -/
abbrev minZeroPage : Int := 4096

/-- `!v.Aux.(*ir.Name).Type().HasPointers()` for a `VarDef`. -/
def varDefNoPointers (tabs : Tables) (x : Value) : Except String Bool := do
  let some a := x.aux | throw s!"VarDef v{x.id} has no aux"
  let some d := tabs.aux? a | throw s!"VarDef v{x.id}: undefined aux a{a}"
  let .name _ _ t .. := d.kind | throw s!"VarDef v{x.id}: aux a{a} is not an *ir.Name"
  let some td := tabs.type? t | throw s!"VarDef v{x.id}: undefined type t{t}"
  return !td.flags.hasptr

/-- Whether the offset of `x`'s address is small enough for a fault (`nilcheck.go:285-317`). -/
def smallOffset (x : Value) : Except String Bool :=
  match x.op.auxType with
  | .Sym => pure x.aux.isNone
  | .SymOff => pure (x.aux.isNone && 0 ≤ x.auxInt.toInt && x.auxInt.toInt < minZeroPage)
  | .SymValAndOff =>
    let off := x.auxInt.toInt32.toInt
    pure (x.aux.isNone && 0 ≤ off && off < minZeroPage)
  | .Int32 | .Int64 | .None | .SizeAndAlign => pure true
  | t => throw s!"can't handle aux of v{x.id} (type {repr t}) yet"

end NilCheckLate

open NilCheckLate in
/-- `nilcheckelim2(f)`. -/
def nilcheckelim2 (env : PassEnv) (f : Func) : Except String Func := do
  let ty ← LowTy.ofEnv env
  let faultOnLoad := env.config? "goos" != some #[.word "aix"]
  let some pending := XPosMap.ofCache f.cache.lineStarts | throw "nil f.cachedLineStarts"
  let mut pending := pending
  let mut unnecessary : SparseMap Nat := SparseMap.new (max f.valueTab.size (f.vidLast + 1))
  let mut f := f
  let mut removed : Array ID := #[]
  for b in f.blocks do
    unnecessary := unnecessary.clear
    pending := pending.clear
    let vals := (f.getB b).values
    let mut firstToRemove := vals.size
    for k in [0:vals.size] do
      let i := vals.size - 1 - k
      let v := vals[i]!
      let x := f.getV v
      if x.op.nilCheck then
        let some ptr := x.args[0]? | throw s!"nil check v{v} has no argument"
        if let some uid := unnecessary.get ptr then
          let u := vals[uid]!
          let up := (f.getV u).pos
          if !up.sameFileAndLine x.pos then
            if up.isStmt == Pos.isStmtMark then pending ← pending.add up
            f := f.modV u fun y => { y with pos := x.pos }
          else if x.pos.isStmt == Pos.isStmtMark then
            pending ← pending.add x.pos
          f := f.resetValue v .Unknown
          removed := removed.push v
          firstToRemove := i
          continue
      if ty.isMemory x.type || (ty.tuple? x.type).any (fun (_, s) => ty.isMemory s) then
        if x.op == .VarLive then continue
        if x.op == .VarDef then
          if ← varDefNoPointers env.tables x then continue
        unnecessary := unnecessary.clear
      let mut ptrs : Array ID := #[]
      if x.op.faultOnNilArg0 && (faultOnLoad || ty.isMemory x.type) then
        ptrs := ptrs.push x.args[0]!
      if x.op.faultOnNilArg1 && (faultOnLoad || ty.isMemory x.type) then
        ptrs := ptrs.push x.args[1]!
      for ptr in ptrs do
        if ← smallOffset x then unnecessary := unnecessary.set ptr i
    -- remove the values clobbered with Unknown
    let mut out : Array ID := vals.extract 0 firstToRemove
    for j in [firstToRemove:vals.size] do
      let v := vals[j]!
      let x := f.getV v
      if x.op != .Unknown then
        if !x.op.notStmtBoundary && pending.contains x.pos then
          let p := x.pos.withIsStmt
          f := f.modV v fun y => { y with pos := p }
          pending := pending.remove p
        out := out.push v
    let bpos := (f.getB b).pos
    if pending.contains bpos then f := f.modB b fun y => { y with pos := bpos.withIsStmt }
    f := f.modB b fun y => { y with values := out }
  -- the removed checks are detached, not freed
  for v in removed do
    f := { f with valueTab := f.valueTab.set! v none }
  return { f with cache := { f.cache with lineStarts := some pending.toCache } }

/-- The `late nilcheck` pass. -/
def nilcheckelim2Pass : Pass := Pass.ofFunc nilcheckelim2

end GoFV.Opt

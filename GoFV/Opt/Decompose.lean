import GoFV.Opt.Decompose.Order
import GoFV.Opt.Decompose.Phi
import GoFV.Rules.Run
import GoFV.Rules.Generated.Dec

/-!
# decompose user, decompose builtin (`decompose.go`, `expand_calls.go:16`)

`decomposeUser` splits phis of structs and arrays into `StructMake`/`ArrayMake1` of per-field
phis and the names of structs and arrays into their leaf fields' slots. "decompose builtin" is
`postExpandCallsDecompose`: `decomposeUser` again, then `decomposeBuiltin`, which splits phis
of strings, slices, interfaces, complex numbers (and integers wider than `RegSize`), runs the
dec rules with `applyRewrite(…, leaveDeadValues)` and splits the names of those types
(docs/PASSES.md, issue #17).

Names follow Go exactly, including its quirks: struct names that keep some values stay in
`f.NamedValues` though they leave `f.Names`; `maybeAppend` tests key presence (nil entries
included); `deleteNamedVals` swap-deletes from the back and keeps a name whose values were all
`OpInvalid` (it tests the original length); freed values read as `OpInvalid`.

linux/arm64 only: `RegSize` 8 (`dec64` does not run), no SIMD types.
-/

namespace GoFV.Opt.Decompose

open GoFV.SSA

/-! ## decomposeUser (`decompose.go:236`) -/

mutual

/-- `decomposeUserArrayInto` (`:267`). -/
def userArrayInto : Nat → SlotRef → Array SlotRef → M (Array SlotRef)
  | 0, _, _ => throw "decomposeUserArrayInto: type nesting too deep"
  | fuel + 1, name, slots => do
    let t := (← slotDef name).type
    if (← ty (Rules.Ty.size · t)) == 0 then return slots
    if (← ty (Rules.Ty.numElem · t)) != 1 then throw "array not of size 1"
    let elemName ← splitArray name
    let mut keep := #[]
    for v in ← named name do
      let x ← val v
      if x.op != .ArrayMake1 then
        keep := keep.push v
        continue
      appendNamed elemName x.args[0]!
    if keep.isEmpty then deleteNamed name else setNamed name keep
    let et ← ty (Rules.Ty.elem · t)
    if ← isArray et then return ← userArrayInto fuel elemName slots
    if ← isStructNotSIMD et then return ← userStructInto fuel elemName slots
    return slots.push elemName

/-- `decomposeUserStructInto` (`:306`). -/
def userStructInto : Nat → SlotRef → Array SlotRef → M (Array SlotRef)
  | 0, _, _ => throw "decomposeUserStructInto: type nesting too deep"
  | fuel + 1, name, slots => do
    let t := (← slotDef name).type
    let n ← ty (Rules.Ty.numFields · t)
    let mut slots := slots
    let mut fnames := #[]
    for i in [0:n] do
      let fs ← splitStruct name i
      fnames := fnames.push fs
      let ft := (← slotDef fs).type
      if !(← isArray ft) && !(← isStructNotSIMD ft) then
        slots ← maybeAppend slots fs
    let mut keep := #[]
    for v in ← named name do
      let x ← val v
      if x.op != .StructMake || x.args.size != n then
        keep := keep.push v
        continue
      for h : i in [0:fnames.size] do
        appendNamed fnames[i] x.args[i]!
    if keep.isEmpty then deleteNamed name else setNamed name keep
    for h : i in [0:fnames.size] do
      let ft ← ty (Rules.Ty.fieldType · t i)
      if ← isStructNotSIMD ft then
        slots ← userStructInto fuel fnames[i] slots
        deleteNamed fnames[i]
      else if ← isArray ft then
        slots ← userArrayInto fuel fnames[i] slots
        deleteNamed fnames[i]
    return slots

end

/-- `decomposeUser` (`:236`). -/
def decomposeUser : M Unit := do
  forEachPhi (decomposeUserPhi typeFuel)
  let mut kept := #[]
  let mut newNames := #[]
  for name in (← get).names do
    let t := (← slotDef name).type
    if ← isStructNotSIMD t then newNames ← userStructInto typeFuel name newNames
    else if ← isArray t then newNames ← userArrayInto typeFuel name newNames
    else kept := kept.push name
  modify fun s => { s with names := kept ++ newNames }

/-! ## decomposeBuiltin (`decompose.go:16`) -/

/-- The component slots of a builtin-typed name and the `Make` op whose arguments they get
(`decomposeBuiltin`'s `switch`, `:43-105`), adding them to `newNames` by `maybeAppend`. -/
def builtinSplit (name : SlotRef) (newNames : Array SlotRef) :
    M (Option (Array SlotRef × Op) × Array SlotRef) := do
  let c ← read
  let t := (← slotDef name).type
  let tabs := (← get).tabs
  let kind ← ty (Rules.Ty.kind · t)
  if Rules.Ty.isIntegerKind kind && (← ty (Rules.Ty.size · t)) > c.regSize then
    let (hi, lo) ← splitInt64 name
    return (some (#[hi, lo], .Int64Make), ← maybeAppend2 newNames hi lo)
  if ← liftE (Rules.Ty.isComplex tabs t) then
    let (r, i) ← splitComplex name
    return (some (#[r, i], .ComplexMake), ← maybeAppend2 newNames r i)
  if kind == .STRING then
    let (p, l) ← splitString name
    return (some (#[p, l], .StringMake), ← maybeAppend2 newNames p l)
  if kind == .SLICE then
    let (p, l, k) ← splitSlice name
    let nn ← maybeAppend2 newNames p l
    return (some (#[p, l, k], .SliceMake), ← maybeAppend nn k)
  if kind == .INTER then
    let (i, d) ← splitInterface name
    return (some (#[i, d], .IMake), ← maybeAppend2 newNames i d)
  if ← liftE (Rules.Ty.isFloat tabs t) then return (none, newNames)
  if (← ty (Rules.Ty.size · t)) > c.regSize then
    throw s!"undecomposed named type s{name} t{t}"
  return (none, newNames)

/-- `deleteNamedVals` (`:420`). -/
def deleteNamedVals (toDelete : Array (Nat × Nat)) : M Unit := do
  let sorted := toDelete.qsort fun a b => a.1 > b.1 || (a.1 == b.1 && a.2 > b.2)
  for (li, vi) in sorted do
    let some loc := (← get).names[li]? | throw "deleteNamedVals: name index out of range"
    let vals ← named loc
    if vals.isEmpty then throw "deleteNamedVals: value index out of range"
    let l := vals.size - 1
    let vals ← if l > 0 then
        if vi < vals.size then pure (vals.set! vi vals[l]!)
        else throw "deleteNamedVals: value index out of range"
      else pure vals
    setNamed loc vals.pop
  let mut names := (← get).names
  let mut stop := names.size
  for k in [0:names.size] do
    let i := names.size - 1 - k
    let loc := names[i]!
    let mut vals ← named loc
    let n := vals.size
    let mut last := n
    for k' in [0:n] do
      let j := n - 1 - k'
      if (← val vals[j]!).op == .Invalid then
        last := last - 1
        vals := vals.set! j vals[last]!
    if last < n then setNamed loc (vals.extract 0 last)
    if n == 0 then
      deleteNamed loc
      stop := stop - 1
      names := names.set! i names[stop]!
  modify fun s => { s with names := names.extract 0 stop }

/-- The names part of `decomposeBuiltin` (`:35-109`). -/
def builtinNames : M Unit := do
  let names := (← get).names
  let mut toDelete := #[]
  let mut newNames := #[]
  for h : i in [0:names.size] do
    let (comps?, nn) ← builtinSplit names[i] newNames
    newNames := nn
    let some (comps, mk) := comps? | continue
    let vs ← named names[i]
    for h : j in [0:vs.size] do
      let x ← val vs[j]
      if x.op != mk then continue
      for h : k in [0:comps.size] do
        appendNamed comps[k] x.args[k]!
      toDelete := toDelete.push (i, j)
  deleteNamedVals toDelete
  modify fun s => { s with names := s.names ++ newNames }

/-! ## Passes -/

/-- The dec rules (`_gen/dec.rules`), indexed by op. -/
def decTable : Rules.Interp.Table := Rules.Interp.Table.ofRuleSet Rules.Generated.Dec.ruleSet

def ctxOf (env : PassEnv) : Except String Ctx := do
  let int (k : String) : Except String Int := match env.config? k with
    | some #[.word w] => match w.toInt? with
      | some n => pure n
      | none => throw s!"config {k}: not an integer"
    | _ => throw s!"config {k}: missing"
  let typ (n : String) : Except String TypeRef := match env.typ? n with
    | some t => pure t
    | none => throw s!"typs: no {n}"
  if ← env.flag "exp.simd" then throw "decompose: GOEXPERIMENT=simd is not ported"
  return {
    ptrSize := ← int "ptrsize", regSize := ← int "regsize", bigEndian := ← env.flag "bigendian"
    bytePtr := ← typ "BytePtr", int := ← typ "Int", uintptr := ← typ "Uintptr"
    int32 := ← typ "Int32", uint32 := ← typ "UInt32", float32 := ← typ "Float32"
    float64 := ← typ "Float64"
    typeFloor := max env.tables.types.size env.typeOrder.rank.size }

/-- Run `m` on `f`'s decompose state. -/
def runM (c : Ctx) (m : M Unit) (s : St) : Except String St :=
  match (m.run c).run s with
  | .ok _ s => .ok s
  | .error e _ => .error e

/-- Write the state back as a pass result, the new slots at the export's numbers. -/
def finish (env : PassEnv) (s : St) : Except String PassOut := do
  let slotFloor := env.tables.slots.size
  let (f, nums) ← toFunc s slotFloor env.tables.auxes.size
  let (tables, func) := renumberSlots slotFloor nums s.tabs f
  return { func, tables }

/-- "decompose user": `decomposeUser`. -/
def decomposeUserPass : Pass := fun env f => do
  let c ← ctxOf env
  let s ← runM c decomposeUser (← ofFunc env.tables f)
  finish env s

/-- "decompose builtin": `postExpandCallsDecompose` = `decomposeUser`, then `decomposeBuiltin`
(phis, the dec rules with `leaveDeadValues`, names). -/
def postExpandCallsDecomposePass : Pass := fun env f => do
  let c ← ctxOf env
  if c.regSize != 8 then throw "decomposeBuiltin: only RegSize 8 is ported (no dec64 rules)"
  let s ← runM c (do decomposeUser; forEachPhi decomposeBuiltinPhi) (← ofFunc env.tables f)
  let out ← Rules.rewritePass decTable false { env with tables := s.tabs } s.f
  let s ← runM c builtinNames { s with f := out.func, tabs := out.tables }
  finish env s

end GoFV.Opt.Decompose

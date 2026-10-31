import GoFV.Opt.Decompose.State

/-!
# decompose: phis (`decompose.go:124-234`, `:352-408`)

A phi of an aggregate or builtin compound type becomes `<T>Make` of new component phis. The
component phis are allocated first, in `v.Block` (`NewValue0(v.Pos, OpPhi, …)`); then, for each
argument `a` in order and each component in order, the extractor is allocated **in `a.Block`**
with the phi's position and appended to the component phi's arguments; then `v.reset(<T>Make)`
and `AddArg` of the component phis. `decomposeUserPhi` then recurses into the new phis.
-/

namespace GoFV.Opt.Decompose

open GoFV.SSA

/-- Split phi `v` into one phi per `(type, extractor op, auxint)` component and make it
`mk` of them. Returns the new phis. -/
def splitPhi (v : ID) (parts : Array (TypeRef × Op × Int64)) (mk : Op) : M (Array ID) := do
  let x ← val v
  let mut phis := #[]
  for (t, _, _) in parts do
    phis := phis.push (← modFGet (·.newValue0 x.block x.pos .Phi t))
  for a in x.args do
    let ab := (← val a).block
    for h : i in [0:parts.size] do
      let (t, op, ai) := parts[i]
      let e ← modFGet (·.newValueArgs ab x.pos op t ai none #[a])
      modF (·.addArg phis[i]! e)
  modF (·.resetValue v mk)
  modF (·.addArgs v phis)
  return phis

/-- `decomposeUserPhi` (`:352`) with `decomposeStructPhi` (`:363`) and `decomposeArrayPhi`
(`:390`). -/
def decomposeUserPhi : Nat → ID → M Unit
  | 0, _ => throw "decomposeUserPhi: type nesting too deep"
  | fuel + 1, v => do
    let t := (← val v).type
    if ← isStructNotSIMD t then
      if (← ty (Rules.Ty.size · t)) == 0 then
        modF (·.resetValue v .Empty)
        return
      let n ← ty (Rules.Ty.numFields · t)
      let mut parts := #[]
      for i in [0:n] do
        parts := parts.push (← ty (Rules.Ty.fieldType · t i), Op.StructSelect, Int64.ofNat i)
      let fields ← splitPhi v parts .StructMake
      for w in fields do decomposeUserPhi fuel w
    else if ← isArray t then
      if (← ty (Rules.Ty.size · t)) == 0 then
        modF (·.resetValue v .Empty)
        return
      if (← ty (Rules.Ty.numElem · t)) != 1 then
        throw s!"v{v}: SSAable array must have no more than 1 element"
      let fields ← splitPhi v #[(← ty (Rules.Ty.elem · t), .ArraySelect, 0)] .ArrayMake1
      for w in fields do decomposeUserPhi fuel w

/-- `decomposeBuiltinPhi` (`:124`) with `decompose{Int64,Complex,String,Slice,Interface}Phi`. -/
def decomposeBuiltinPhi (v : ID) : M Unit := do
  let c ← read
  let t := (← val v).type
  let tabs := (← get).tabs
  let kind ← ty (Rules.Ty.kind · t)
  if Rules.Ty.isIntegerKind kind && (← ty (Rules.Ty.size · t)) > c.regSize then
    let part := if Rules.Ty.isSignedKind kind then c.int32 else c.uint32
    discard <| splitPhi v #[(part, .Int64Hi, 0), (c.uint32, .Int64Lo, 0)] .Int64Make
  else if ← liftE (Rules.Ty.isComplex tabs t) then
    let part ← match ← ty (Rules.Ty.size · t) with
      | 8 => pure c.float32
      | 16 => pure c.float64
      | z => throw s!"decomposeComplexPhi: bad complex size {z}"
    discard <| splitPhi v #[(part, .ComplexReal, 0), (part, .ComplexImag, 0)] .ComplexMake
  else if kind == .STRING then
    discard <| splitPhi v #[(c.bytePtr, .StringPtr, 0), (c.int, .StringLen, 0)] .StringMake
  else if kind == .SLICE then
    let pt ← ptrTo (← ty (Rules.Ty.elem · t))
    discard <| splitPhi v
      #[(pt, .SlicePtr, 0), (c.int, .SliceLen, 0), (c.int, .SliceCap, 0)] .SliceMake
  else if kind == .INTER then
    discard <| splitPhi v #[(c.uintptr, .ITab, 0), (c.bytePtr, .IData, 0)] .IMake
  else if ← liftE (Rules.Ty.isFloat tabs t) then
    pure ()
  else if (← ty (Rules.Ty.size · t)) > c.regSize then
    throw s!"v{v} undecomposed type t{t}"

/-- Apply `g` to every phi of `f.Blocks` × `b.Values` (each block's value list as it was when
its loop started: Go's `range` snapshot). -/
def forEachPhi (g : ID → M Unit) : M Unit := do
  for b in (← getF).blocks do
    for v in ((← getF).getB b).values do
      if (← val v).op == .Phi then g v

end GoFV.Opt.Decompose

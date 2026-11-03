import GoFVTest.Parity.Renumber
import GoFV.Opt.Pass
import GoFV.SSA.Print

/-!
# Comparing a Lean result with a stock section

Shared by `pass-parity` (per pass) and `gofv-ssa-opt --check` (whole pipeline): pair the
objects the Lean side created with the stock section's (`renumber`), then compare the
functions structurally, else by their printed text.
-/

open GoFV.SSA GoFV.Opt

namespace GoFVTest.Parity

/-- A section's `zvar` as a lookup (`PassEnv.zvar`). -/
def zvarFn (zv : Array (ID × Nat)) : ID → Nat :=
  let m : Std.HashMap ID Nat := zv.foldl (fun m (v, c) => m.insert v c) {}
  fun i => m.getD i 0

/-- The file's `ptrcache` as a predicate (`PassEnv.ptrCache`). -/
def ptrCacheFn (ts : Array TypeRef) : TypeRef → Bool :=
  let m : Std.HashMap TypeRef Unit := ts.foldl (fun m t => m.insert t ()) {}
  fun t => m.contains t

/-- The file's `typelink` groups as a key (`PassEnv.typeLink`): each member maps to its group's
first number. -/
def typeLinkFn (groups : Array (Array TypeRef)) : TypeRef → TypeRef :=
  let m : Std.HashMap TypeRef TypeRef :=
    groups.foldl (fun m g => match g[0]? with
      | some r => g.foldl (fun m t => m.insert t r) m
      | none => m) {}
  fun t => m.getD t t

/-- First differing line of two texts. -/
def firstDiff (want got : String) : String := Id.run do
  let la := want.splitOn "\n"
  let lb := got.splitOn "\n"
  for k in [0:max la.length lb.length] do
    let x := la.getD k "<eof>"
    let y := lb.getD k "<eof>"
    if x != y then return s!"func line {k+1}:\n    stock: {x}\n    lean:  {y}"
  return "no difference"

def printFunc (f : Func) : String := (Print.func f none |>.run "").2

private unsafe def sameObjImpl {α : Type} (a b : α) : Bool := ptrAddrUnsafe a == ptrAddrUnsafe b

/-- Pointer equality (a fast path only: `false` is always safe). -/
@[implemented_by sameObjImpl] def sameObj {α : Type} (_ _ : α) : Bool := false

/-- Position bases the pass defined or changed must be section `k`'s (no pass creates them). -/
def checkPosBases (input out want : Tables) : Option String := Id.run do
  for i in [0:max input.posBases.size out.posBases.size] do
    let o := out.posBase? i
    if input.posBase? i != o && o != want.posBase? i then
      return some s!"position base p{i} differs from the stock output section"
  return none

/-- The printed function with the entries of `namedx`, `splits` and `canon` (Go maps, which the
exporter sorts by object numbers) in sorted order: the importer's `gofvMapOrder`. -/
def mapOrder (text : String) : String := Id.run do
  let lines := (text.splitOn "\n").toArray
  let sortStr (xs : Array String) : Array String := xs.qsort (· < ·)
  let mut out := #[]
  let mut namedx := #[]
  let mut first : Option Nat := none
  for l in lines do
    if l.startsWith "splits " || l.startsWith "canon " then
      let (tag, list) := match l.splitOn " " with
        | tag :: rest => (tag, " ".intercalate rest)
        | [] => ("", "")
      out := out.push (tag ++ " " ++ ",".intercalate (sortStr (list.splitOn ",").toArray).toList)
    else if l.startsWith "namedx " then
      if first.isNone then first := some out.size
      namedx := namedx.push l
      out := out.push l
    else out := out.push l
  if let some i := first then
    let sorted := sortStr namedx
    let mut j := 0
    for k in [i:out.size] do
      if (out[k]!).startsWith "namedx " then
        out := out.set! k sorted[j]!
        j := j + 1
  return "\n".intercalate out.toList

/-- Compare the pass result with section `k` (`stock`, with tables `want`). With `loose`, as the
driver's importer compares (`docs/DRIVER.md`): a new symbol by name and ABI only, the map lines
(`namedx`, `splits`, `canon`) as sets. -/
def compare (input : Tables) (out : PassOut) (want : Tables) (stock : Section)
    (loose : Bool := false) : Option String :=
  -- fast path: the pass made no definitions and the stock section has none
  let renamed : Except String Func :=
    if sameObj out.tables input && stock.defs.isEmpty then pure out.func
    else match checkPosBases input out.tables want with
      | some d => throw d
      | none => renumber input out.tables want out.func stock.func (symNameOnly := loose)
  match renamed with
  | .error d => some d
  | .ok f =>
    if f == stock.func then none else
    let w := printFunc stock.func
    let g := printFunc f
    if w == g then none else
    if loose && mapOrder w == mapOrder g then none else some (firstDiff w g)

end GoFVTest.Parity

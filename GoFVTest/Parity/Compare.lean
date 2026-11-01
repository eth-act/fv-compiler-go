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

/-- Compare the pass result with section `k` (`stock`, with tables `want`). -/
def compare (input : Tables) (out : PassOut) (want : Tables) (stock : Section) : Option String :=
  -- fast path: the pass made no definitions and the stock section has none
  let renamed : Except String Func :=
    if sameObj out.tables input && stock.defs.isEmpty then pure out.func
    else match checkPosBases input out.tables want with
      | some d => throw d
      | none => renumber input out.tables want out.func stock.func
  match renamed with
  | .error d => some d
  | .ok f =>
    if f == stock.func then none else
    let w := printFunc stock.func
    let g := printFunc f
    if w == g then none else some (firstDiff w g)

end GoFVTest.Parity

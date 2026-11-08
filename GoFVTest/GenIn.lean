import GoFV.Gen.Progs

/-!
# G2's frame input and rejection classes, shared by `gen-check` and `gofv-ssa-opt --e2e`

`slotOpOf` gives the genssa validator's `G2In.slotOp` from a frame layout; `classOf` groups
rejection messages by replacing numbers with `#`.
-/

open GoFV.Asm GoFV.Gen

namespace GoFVTest.GenCheck

/-- The reason with `v<n>`, `b<n>` and other numbers replaced. -/
def classOf (msg : String) : String := Id.run do
  let mut out := ""
  let mut prevDigit := false
  for c in msg.toList do
    if c.isDigit then
      unless prevDigit do out := out.push '#'
      prevDigit := true
    else
      out := out.push c
      prevDigit := false
  return out

/-- Go's frame layout of slot `k`: the name class and operand offset (`AddrAuto`). -/
def slotOpOf (env : Env) (offs : Array (Option Int)) (k : GoFV.SSA.SlotKey) :
    Option (AddrName × Int) := do
  let n ← env.nameOfAux? k.name
  let off ← (offs[n]?).join
  let x ← (env.name n).toOption
  let outregs := (env.inFlags[n]?).any (·.outregs)
  let cls := if x.cls == "PPARAM" || (x.cls == "PPARAMOUT" && !outregs) then AddrName.PARAM
    else .AUTO
  return (cls, off + k.off)

end GoFVTest.GenCheck

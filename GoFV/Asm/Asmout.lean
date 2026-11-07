import GoFV.Asm.AsmoutA
import GoFV.Asm.AsmoutB

/-!
# `asmout` (`asm7.go:3616-6217`; `docs/PASSES3.md` D5)

`ctxt7.asmout(p, out)`: `oplook`, then the case `o.type_` of the selected optab entry, which
computes up to five words `o1 … o5` (and appends relocations to the text symbol at `ctxt7.pc`);
the result is the first `o.size(ctxt, p) / 4` of them. The cases are ported in
`GoFV.Asm.AsmoutA` (cases 0–45) and `GoFV.Asm.AsmoutB` (46 and above), each a function from the
case number to `none` (not its case) or the words `o1, o2, …` it sets (missing trailing words
are 0). A case neither ports is a port error naming the case.
-/

namespace GoFV.Asm

open AsmM

/-- `ctxt7.asmout`: the machine words of Prog `p`. -/
def asmout (p : Nat) : AsmM (Array UInt32) := do
  let o ← oplook p
  let ws ← if o.type_ == 0 then pure #[] else
    match ← asmoutA o.type_ p o with
    | some ws => pure ws
    | none =>
      match ← asmoutB o.type_ p o with
      | some ws => pure ws
      | none => fail s!"asmout: case {o.type_} not ported ({(← getP p).as.name})"
  if ws.size > 5 then fail s!"asmout: case {o.type_} set {ws.size} words"
  let ws := ws ++ Array.replicate (5 - ws.size) (0 : UInt32)
  let n := (← optabSize o p) / 4
  if n > 5 then fail s!"asmout: size {n * 4} of case {o.type_}"
  return ws.extract 0 n.toNat

end GoFV.Asm

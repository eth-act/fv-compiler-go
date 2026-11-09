import GoFV.Opt.KnownBitsCheck
import GoFV.SSA.Sem.Pure

variable [GoFV.SSA.Sem.Addrs]

/-!
# The op families of known bits' checker (issue #26)

`sem k`: the semantics (`evalPure`) of the ops of family `k` (`GoFV.Opt.KnownBits.kind`), and
`kind_spec`: an op of family `k` evaluates as `sem k`, with widths `k` relates validly
(`KOp.Valid`: extensions widen, truncations narrow). Proved once by cases on the op.
-/

namespace GoFV.Proof.KnownBits

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.KnownBits

/-- The semantics of a family. -/
def sem : KOp → Int64 → List Val → Val
  | .const w, ai, _ => Conv.const w ai
  | .constBool, ai, _ => Conv.constBool ai
  | .and w, _, l => Sem.Int.and w l
  | .andB, _, l => Cmp.andB l
  | .or w, _, l => Sem.Int.or w l
  | .orB, _, l => Cmp.orB l
  | .xor w, _, l => Sem.Int.xor w l
  | .com w, _, l => Sem.Int.com w l
  | .not, _, l => Cmp.not l
  | .copy, _, l => match l with | [x] => x | _ => .poison
  | .cvt, _, l => Conv.boolToUint8 l
  | .signExt w w', _, l => Conv.signExt w w' l
  | .trunc w w', _, l => Conv.trunc w w' l
  | .zeroExt w w', _, l => Conv.zeroExt w w' l
  | .eq w, _, l => Cmp.eq w l
  | .eqB, _, l => Cmp.eqB l
  | .neq w, _, l => Cmp.neq w l
  | .neqB, _, l => Cmp.neqB l
  | .shift .lsh w a, ai, l => Shift.lsh w a (ai == 1) l
  | .shift .rsh w a, ai, l => Shift.rsh w a (ai == 1) l
  | .shift .rshu w a, ai, l => Shift.rshu w a (ai == 1) l

/-- The widths of a family are related as its ops' are. -/
def validB : KOp → Bool
  | .signExt w w' => w.bits < w'.bits
  | .zeroExt w w' => w.bits < w'.bits
  | .trunc w w' => w'.bits < w.bits
  | _ => true

theorem kind_spec {op : Op} {k : KOp} (h : kind op = some k) (ty : Ty) (ai : Int64)
    (aux : Option AuxRef) (l : List Val) :
    evalPure op ty ai aux l = sem k ai l ∧ validB k = true := by
  cases op <;> first | (cases h; done) | (cases h; exact ⟨rfl, rfl⟩)

end GoFV.Proof.KnownBits

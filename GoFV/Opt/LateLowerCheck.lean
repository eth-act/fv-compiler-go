import GoFV.Opt.Lower
import GoFV.Opt.LowerCheck
import GoFV.Proof.CongL

/-!
# The checked `late lower`: renames (`renameB`, issue #385)

`late lower` (`GoFV.Opt.lateLower`, `ARM64latelower.rules`) rewrites lowered values in place. Two
of its rules only rename an op to one `runL` evaluates alike: `(MOVDreg x) && x.Uses == 1 =>
(MOVDnop x)` (line 91; `arm64Op` has one arm for both) and `(MOVDconst [0]) => (ZERO)` (line 98;
both are the word 0). `normV` maps `MOVDnop` back to `MOVDreg` and `ZERO [0]` back to
`MOVDconst [0]`. `renameB tabs tabs' f g` accepts `g` (with tables `tabs'`) for `f` (with tables
`tabs`) when, after `normV`, `g` is `f` up to what `runL` does not read (`eraseFL`: positions, use
counts, predictions, block order, caches) and the tables agree for `f` (`tabsAgreeL`). Then `g`
runs as `f` (`GoFV.Proof.LateLowerL.lateLower_refinesL`). Sections where any other rule fires are
rejected.
-/

namespace GoFV.Opt.LateLowerCheck

open GoFV.SSA GoFV.Proof

/-- `late lower`'s renames undone: `MOVDnop` is `MOVDreg`, `ZERO [0]` is `MOVDconst [0]`. -/
def normV (v : Value) : Value :=
  if v.op = .ARM64MOVDnop then { v with op := .ARM64MOVDreg }
  else if v.op = .ARM64ZERO ∧ v.auxInt = 0 then { v with op := .ARM64MOVDconst }
  else v

/-- `f` with its values `normV`ed. -/
def normF (f : Func) : Func := { f with valueTab := f.valueTab.map (Option.map normV) }

/-- **The `late lower` rename validator** (module doc). -/
def renameB (tabs tabs' : Tables) (f g : Func) : Bool :=
  LowerCheck.tabsAgreeL tabs tabs' f && decide (eraseFL (normF g) = eraseFL (normF f))

end GoFV.Opt.LateLowerCheck

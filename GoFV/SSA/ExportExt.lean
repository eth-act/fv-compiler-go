/-!
# Format 5.1 additions

`gofv-ssa 5.1` (`docs/contracts/export.md`, "Format 5.1") adds one line to each section,
`dcllen <n>`: `len(curfn.Dcl)` when the section was written. The parser returns it next to the
`ExportFile` (`parseExportExt`), not inside it: `Section` and `ExportFile` are imported by every
pass and proof module, and a field there rebuilds all of them.
-/

namespace GoFV.SSA

/-- What a format 5.1 file has beyond `ExportFile`. -/
structure ExportExt where
  /-- The minor format version (`gofv-ssa 5.1`: 1; 0 when the first line has none). -/
  minor : Nat := 0
  /-- Per section, by section index: its `dcllen` (`len(curfn.Dcl)`; `f.NewLocal` names its
  autos `.autotmp_<len(Dcl)>`, and every new auto, `fe.SplitSlot` or `f.NewLocal`, appends to
  `Dcl`). `none` before format 5.1. The next pass's `PassEnv.dclLen`. -/
  dclLen : Array (Option Nat) := #[]
  deriving Inhabited

/-- The `dcllen` of section `k`. -/
def ExportExt.dclLen? (x : ExportExt) (k : Nat) : Option Nat := (x.dclLen[k]?).join

end GoFV.SSA

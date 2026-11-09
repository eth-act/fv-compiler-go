import GoFV.Gen.Check31

/-!
# The genssa validator, slice G33: more single-instruction ops (`docs/plans/proofs3.md` §4)

`checkG33 lc ps bstart g` is slice G31 (`GoFV/Gen/Check31.lean`) with more single-instruction ops
in a function with an arm64 op:

* `UBFIZ [k] x` (`k = lsb · 256 + width`, `0 ≤ k < 2 ^ 16`): `UBFIZ $lsb, Rn, $width, Rd`, the
  low `width` bits of `x` moved up to bit `lsb`. Bit `i < c` of the result is bit `i - lsb < width`
  of `x`, so an argument of class `ca` with `width ≤ ca` or `c ≤ ca` holds every bit it reads;
* `CLZ x`, `REV x` (`un33?`): `CLZ`/`REV Rm, Rd`, of a 64-bit argument (their low bits depend on
  every bit of `x`);
* `SRAconst [k] x` (`0 ≤ k < 64`): `ASR $k, Rn, Rd`, of a 64-bit argument (as G3's `SRLconst`);
* `CMNWconst [k] x`: `CMNW $k, Rn`, the flags of the 32-bit `ADDS` of `x`'s low word and `k`'s,
  with an argument of class at least 32 (as G3's `CMPWconst`); its result is the flags, with no
  home.

An ALU op has no temporary and a result of class `c ≥ 8`. The G33 ops empty the upper-bit table
(`uStep31` is `uStepL` on them), as every value outside `keep31` does.

On a function with no arm64 op, `checkG33` is `checkG31`'s `checkNL30`.
`GoFV/Proof/Gen/G33.lean` proves what an accepted function satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The unary ops of G33 on a 64-bit argument and their opcode: `op Rm, Rd`. -/
def un33? : Op → Option As
  | .ARM64CLZ => some .CLZ | .ARM64REV => some .REV
  | _ => none

/-- A `UBFIZ` operand pair: `$lsb` in `from_`, `$width` the one `RestArgs` source. -/
def ubfizOK (lsb width : Int) (rn rd : Int) (p : Prog) : Bool :=
  p.as == .UBFIZ && p.from_ == constA lsb && p.reg == rn && p.to == regA rd && p.scond == 0 &&
    p.regTo2 == 0 && match p.rest with
    | #[(_, a)] => a == constA width
    | _ => false

/-- `UBFIZ [k] x` (module doc): what it emits. -/
def ubfizKind (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 1 && 0 ≤ v.auxInt.toInt && v.auxInt.toInt < 2 ^ 16 do
    throw s!"v{v.id}: bitfield shape"
  let (ca, rn) ← argObj lc v 0
  let (c, rd) ← resObj lc v
  let lsb := v.auxInt.toInt / 256
  let width := v.auxInt.toInt % 256
  unless 8 ≤ c && (width ≤ ca || c ≤ ca) do throw s!"v{v.id}: bitfield widths"
  return .prog ⟨ubfizOK lsb width rn rd, "UBFIZ"⟩

/-- `CLZ x`, `REV x` (module doc): what they emit. -/
def un33Kind (lc : LocCtx) (v : Value) (as : As) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 1 do throw s!"v{v.id}: shape"
  let (ca, rm) ← argObj lc v 0
  let (c, rd) ← resObj lc v
  unless 8 ≤ c && ca == 64 do throw s!"v{v.id}: {v.op.name} widths"
  return .prog (.ofShape { as, from_ := regA rm, to := regA rd })

/-- `SRAconst [k] x` (module doc): what it emits. -/
def sraKind (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 1 do throw s!"v{v.id}: shape"
  let (ca, rn) ← argObj lc v 0
  let (c, rd) ← resObj lc v
  unless 8 ≤ c && ca == 64 && 0 ≤ v.auxInt.toInt && v.auxInt.toInt < 64 do
    throw s!"v{v.id}: shift or mask widths"
  return .prog (.ofShape { as := .ASR, from_ := constA v.auxInt.toInt, reg := rn, to := regA rd })

/-- `CMNWconst [k] x` (module doc): what it emits. -/
def cmnwKind (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 1 && (lc.ty v.id).isFlags && lc.home v.id == none do
    throw s!"v{v.id}: compare shape"
  let (ca, rn) ← argObj lc v 0
  unless 32 ≤ ca do throw s!"v{v.id}: compare widths"
  return .prog (.ofShape { as := .CMNW, from_ := constA v.auxInt.toInt, reg := rn })

/-- What `v` emits in G33, or why it is outside the slice. -/
def vkind33 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  match un33? v.op with
  | some as => un33Kind lc v as
  | none =>
    if v.op == .ARM64UBFIZ then ubfizKind lc v
    else if v.op == .ARM64SRAconst then sraKind lc v
    else if v.op == .ARM64CMNWconst then cmnwKind lc v
    else vkind32 lc g v

/-- Slice G33 of the genssa validator (module doc): G31's check with G33's value check. -/
def checkG33 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind33 lc g, tm := cx.termG3 }
    let tab ← c.blocks lc.ctx.f.blocks.toList
    unless pbOK lc ps.toList tab do throw "bounds panic PCDATA"
    unless movdOK31 lc && uEdgesOK lc do throw "MOVDnop/MOVDreg: upper bits unknown"
    if let some i := (List.range lc.homes.size).find? (!homeOK10 lc ·) then throw (homeErr lc i)
    unless cloFirst lc do throw "LoweredGetClosurePtr after code"
    checkFrame lc g
    checkVars lc g
    let kin := kFlow lc (65 * lc.ctx.f.blocks.size + 2)
    let kt : KTab := lc.ctx.f.blocks.toList.map fun b => (b, (kin[b]?).getD KMap.bot)
    checkK lc kt
    let ids := ps.toList.map (·.id)
    unless ids.all (· < 2 ^ 32) && ids.Nodup do throw "Prog IDs"
    return (tab, kt)
  else checkNL30 lc ps bstart g

end GoFV.Gen.Check

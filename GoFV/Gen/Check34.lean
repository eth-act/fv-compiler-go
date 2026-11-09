import GoFV.Gen.Check33

/-!
# The genssa validator, slice G34: the upper-bit table across more values
(`docs/plans/proofs3.md` §4)

`checkG34 lc ps bstart g` is slice G33 (`GoFV/Gen/Check33.lean`) with a larger upper-bit table:
G31's table `uL31` keeps its entries only across G1's kinds and G3's 32-bit compares (`keep31`);
G34's `uL34` also keeps the entries of the registers a value does not write across the
single-register ops of G3 (the extensions, `ANDconst`, `SLLconst`, `SRLconst`, `UBFX`), G16
(`ADDshiftLL`), G23 (the condition values `Equal` …), G25 (`CSEL`, `CSEL0`, `TSTconst`,
`TSTWconst`), G32 and G33, the spills and reloads (`StoreReg`, `LoadReg`) and `MOVDaddr`
(`keep34`). Each writes at most its register home's X register. The dataflow (`uPass34`,
`uFlow34`, `uIn34`), its check (`uEdgesOK34`) and the `MOVDnop`/`MOVDreg` check (`movdOK34`) are
G31's over `uStep34`.

On a function with no arm64 op, `checkG34` is `checkG33`'s `checkNL30`.
`GoFV/Proof/Gen/G34.lean` proves what an accepted function satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The ops beyond `keepOp31` across which G34's table keeps the entries of the registers the value
does not write. -/
def keepOp34 : Op → Bool
  | .ARM64MOVBreg | .ARM64MOVBUreg | .ARM64MOVHreg | .ARM64MOVHUreg | .ARM64MOVWreg | .ARM64MOVWUreg
  | .ARM64ANDconst | .ARM64SLLconst | .ARM64SRLconst | .ARM64UBFX | .ARM64ADDshiftLL
  | .ARM64Equal | .ARM64NotEqual | .ARM64LessThan | .ARM64LessEqual | .ARM64GreaterThan
  | .ARM64GreaterEqual | .ARM64LessThanU | .ARM64LessEqualU | .ARM64GreaterThanU
  | .ARM64GreaterEqualU | .ARM64CSEL | .ARM64CSEL0 | .ARM64TSTconst | .ARM64TSTWconst
  | .ARM64MUL | .ARM64MNEG | .ARM64AND | .ARM64OR | .ARM64XOR | .ARM64BIC | .ARM64EON | .ARM64ORN
  | .ARM64ORconst | .ARM64XORconst | .ARM64NEG | .ARM64MVN | .ARM64CSINC | .ARM64CLZ | .ARM64REV
  | .ARM64UBFIZ | .ARM64SRAconst | .ARM64CMNWconst | .LoadReg | .StoreReg | .ARM64MOVDaddr => true
  | _ => false

/-- The values across which G34's table keeps the entries of the registers they do not write:
`keep31`'s and `keepOp34`'s. -/
def keep34 (v : Value) : Bool := keep31 v || keepOp34 v.op

/-- The upper-bit table after value `v` (module doc). -/
def uStep34 (lc : LocCtx) (L : List (Nat × Nat × Bool)) (v : Value) : List (Nat × Nat × Bool) :=
  if keep34 v then L.filter fun e => regHome? lc v.id != some e.1 else uStepL lc L v

/-- The upper-bit table before value `i` of block `blk`, which starts with `L0` (nothing past the
start on a function with no arm64 op). -/
def uL34 (lc : LocCtx) (L0 : List (Nat × Nat × Bool)) (blk : Block) :
    Nat → List (Nat × Nat × Bool)
  | 0 => L0
  | i + 1 =>
    if lc.ctx.f.lowered then
      match (blk.values[i]?).bind lc.ctx.f.value? with
      | some v => uStep34 lc (uL34 lc L0 blk i) v
      | none => []
    else []

/-- One pass of the forward dataflow over the blocks `bids` (`uPass` over `uL34`). -/
def uPass34 (lc : LocCtx) (tin : Std.HashMap ID (List (Nat × Nat × Bool))) (bids : List ID) :
    Std.HashMap ID (List (Nat × Nat × Bool)) :=
  bids.foldl (fun tin bid =>
    match tin[bid]?, lc.ctx.f.block? bid with
    | some L, some b =>
      let out := uL34 lc L b b.values.size
      b.succs.foldl (fun tin e =>
        match tin[e.b]? with
        | some L' => tin.insert e.b (L'.filter (out.contains ·))
        | none => tin.insert e.b out) tin
    | _, _ => tin) tin

/-- The block starts: the dataflow from the entry block (nothing known) to a fixed point (at most
`fuel` passes). -/
def uFlow34 (lc : LocCtx) (fuel : Nat) : Std.HashMap ID (List (Nat × Nat × Bool)) :=
  let bids := lc.ctx.f.blocks.toList
  let rec go : Nat → Std.HashMap ID (List (Nat × Nat × Bool)) →
      Std.HashMap ID (List (Nat × Nat × Bool))
    | 0, tin => tin
    | n + 1, tin =>
      let tin' := uPass34 lc tin bids
      if bids.all (fun b => tin'[b]? == tin[b]?) then tin' else go n tin'
  go fuel (({} : Std.HashMap ID (List (Nat × Nat × Bool))).insert lc.ctx.f.entry [])

/-- The upper-bit table at the start of block `b` (nothing on a function with no arm64 op). -/
def uIn34 (lc : LocCtx) (b : ID) : List (Nat × Nat × Bool) :=
  if lc.ctx.f.lowered then ((uFlow34 lc (65 * lc.ctx.f.blocks.size + 2))[b]?).getD [] else []

/-- The entry block starts with nothing in the table, and every successor's start is in its
predecessor's end. -/
def uEdgesOK34 (lc : LocCtx) : Bool :=
  uIn34 lc lc.ctx.f.entry == [] && lc.ctx.f.blocks.toList.all fun bid =>
    match lc.ctx.f.block? bid with
    | none => true
    | some b =>
      let out := uL34 lc (uIn34 lc bid) b b.values.size
      b.succs.toList.all fun e => (uIn34 lc e.b).all (out.contains ·)

/-- Every `MOVDnop x` and `MOVDreg x` finds `x`'s register, class and `signOf` in the upper-bit
table `uL34` before it. -/
def movdOK34 (lc : LocCtx) : Bool :=
  lc.ctx.f.blocks.toList.all fun bid =>
    match lc.ctx.f.block? bid with
    | none => true
    | some b => (List.range b.values.size).all fun i =>
      match (b.values[i]?).bind lc.ctx.f.value? with
      | some v => (v.op != .ARM64MOVDnop && v.op != .ARM64MOVDreg) || match v.args[0]? with
        | some x => match regHome? lc x, cls (lc.ty x) with
          | some r, some c =>
            (uL34 lc (uIn34 lc bid) b i).contains (r, c, lc.signOf lc.ctx.f.valueTab.size x)
          | _, _ => false
        | none => false
      | none => true

/-- Slice G34 of the genssa validator (module doc): G33 with the upper-bit table `uL34`. -/
def checkG34 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind33 lc g, tm := cx.termG3 }
    let tab ← c.blocks lc.ctx.f.blocks.toList
    unless pbOK lc ps.toList tab do throw "bounds panic PCDATA"
    unless movdOK34 lc && uEdgesOK34 lc do throw "MOVDnop/MOVDreg: upper bits unknown"
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

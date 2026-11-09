import GoFV.Gen.Check32

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G31: the upper-bit table across values and blocks
(`docs/plans/proofs3.md` §4)

`checkG31 lc ps bstart g` is slice G32 (`GoFV/Gen/Check32.lean`) with a larger upper-bit table on a
function with an arm64 op. G29's table `uL` is emptied by every value other than a narrow load,
`MOVDnop` or `MOVDreg`, and starts empty in every block. G31's table `uL31`:

* keeps, across a value of G1's kinds or G3's `CMPW`/`CMPWconst` (`keep31`: `Phi`, `ZERO`,
  `InlMark`, `Copy`, `MakeResult`, `MOVDconst`, `ADD`, `SUB`, `ADDconst`, `SUBconst`, `CMP`,
  `CMPconst`, `CMPW`, `CMPWconst`, and `MOVDload`/`MOVDstore` without symbol), the entries of the
  registers other than the value's register home (`uStep31`); every other value steps as in G29
  (`uStepL`);
* starts each block with `uIn`: nothing at the entry block, elsewhere the entries every reached
  predecessor ends with (`uFlow`, a forward dataflow to a fixed point; `uEdgesOK` checks whatever
  it returns: the entry starts empty and every successor's start is in its predecessor's end).

`movdOK31` requires each `MOVDnop x` and `MOVDreg x` to find `(x`'s register, `x`'s class,
`signOf x)` in the table before it. On a function with no arm64 op, `checkG31` is `checkNL30` and
the tables are empty. `GoFV/Proof/Gen/G31.lean` proves what an accepted function satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The ops across which the table keeps the entries of the registers the value does not write
(G1's kinds and G3's 32-bit compares). -/
def keepOp31 : Op → Bool
  | .Phi | .ARM64ZERO | .InlMark | .Copy | .MakeResult | .ARM64MOVDconst | .ARM64ADD | .ARM64SUB
  | .ARM64ADDconst | .ARM64SUBconst | .ARM64CMP | .ARM64CMPconst | .ARM64CMPW
  | .ARM64CMPWconst => true
  | _ => false

/-- The values across which the table keeps the entries of the registers they do not write:
`keepOp31`, or a `MOVDload`/`MOVDstore` without symbol (G1's `load`/`store`). -/
def keep31 (v : Value) : Bool :=
  keepOp31 v.op || ((v.op == .ARM64MOVDload || v.op == .ARM64MOVDstore) && v.aux.isNone)

/-- The upper-bit table after value `v` (module doc). -/
def uStep31 (lc : LocCtx) (L : List (Nat × Nat × Bool)) (v : Value) : List (Nat × Nat × Bool) :=
  if keep31 v then L.filter fun e => regHome? lc v.id != some e.1 else uStepL lc L v

/-- The upper-bit table before value `i` of block `blk`, which starts with `L0` (nothing past the
start on a function with no arm64 op). -/
def uL31 (lc : LocCtx) (L0 : List (Nat × Nat × Bool)) (blk : Block) :
    Nat → List (Nat × Nat × Bool)
  | 0 => L0
  | i + 1 =>
    if lc.ctx.f.lowered then
      match (blk.values[i]?).bind lc.ctx.f.value? with
      | some v => uStep31 lc (uL31 lc L0 blk i) v
      | none => []
    else []

/-- One pass of the forward dataflow over the blocks `bids`: the table at the start of each
reached block, met with the end of each reached predecessor. -/
def uPass (lc : LocCtx) (tin : Std.HashMap ID (List (Nat × Nat × Bool))) (bids : List ID) :
    Std.HashMap ID (List (Nat × Nat × Bool)) :=
  bids.foldl (fun tin bid =>
    match tin[bid]?, lc.ctx.f.block? bid with
    | some L, some b =>
      let out := uL31 lc L b b.values.size
      b.succs.foldl (fun tin e =>
        match tin[e.b]? with
        | some L' => tin.insert e.b (L'.filter (out.contains ·))
        | none => tin.insert e.b out) tin
    | _, _ => tin) tin

/-- The block starts: the dataflow from the entry block (nothing known) to a fixed point (at most
`fuel` passes). -/
def uFlow (lc : LocCtx) (fuel : Nat) : Std.HashMap ID (List (Nat × Nat × Bool)) :=
  let bids := lc.ctx.f.blocks.toList
  let rec go : Nat → Std.HashMap ID (List (Nat × Nat × Bool)) →
      Std.HashMap ID (List (Nat × Nat × Bool))
    | 0, tin => tin
    | n + 1, tin =>
      let tin' := uPass lc tin bids
      if bids.all (fun b => tin'[b]? == tin[b]?) then tin' else go n tin'
  go fuel (({} : Std.HashMap ID (List (Nat × Nat × Bool))).insert lc.ctx.f.entry [])

/-- The upper-bit table at the start of block `b` (nothing on a function with no arm64 op). -/
def uIn (lc : LocCtx) (b : ID) : List (Nat × Nat × Bool) :=
  if lc.ctx.f.lowered then ((uFlow lc (65 * lc.ctx.f.blocks.size + 2))[b]?).getD [] else []

/-- The entry block starts with nothing in the table, and every successor's start is in its
predecessor's end. -/
def uEdgesOK (lc : LocCtx) : Bool :=
  uIn lc lc.ctx.f.entry == [] && lc.ctx.f.blocks.toList.all fun bid =>
    match lc.ctx.f.block? bid with
    | none => true
    | some b =>
      let out := uL31 lc (uIn lc bid) b b.values.size
      b.succs.toList.all fun e => (uIn lc e.b).all (out.contains ·)

/-- Every `MOVDnop x` and `MOVDreg x` finds `x`'s register, class and `signOf` in the upper-bit
table `uL31` before it. -/
def movdOK31 (lc : LocCtx) : Bool :=
  lc.ctx.f.blocks.toList.all fun bid =>
    match lc.ctx.f.block? bid with
    | none => true
    | some b => (List.range b.values.size).all fun i =>
      match (b.values[i]?).bind lc.ctx.f.value? with
      | some v => (v.op != .ARM64MOVDnop && v.op != .ARM64MOVDreg) || match v.args[0]? with
        | some x => match regHome? lc x, cls (lc.ty x) with
          | some r, some c =>
            (uL31 lc (uIn lc bid) b i).contains (r, c, lc.signOf lc.ctx.f.valueTab.size x)
          | _, _ => false
        | none => false
      | none => true

/-- Slice G31 of the genssa validator (module doc): G32 with the upper-bit table `uL31`. -/
def checkG31 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind32 lc g, tm := cx.termG3 }
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

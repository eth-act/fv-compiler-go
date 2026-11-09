import GoFV.Gen.Check28

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G29: the upper-bit table within a block (`docs/plans/proofs3.md` §4)

`checkG29 lc ps bstart g` is slice G28 (`GoFV/Gen/Check28.lean`) with a larger upper-bit table.
G20's table `uAt` holds one entry, directly after a narrow load. G29's `uL` carries a list of
entries `(r, c, sg)` (register `r` holds the `sg` extension of its low `c` bits) across the values
of one block that write at most one register (`uStepL`):

* a narrow load homed in `r` (`uEntry`) adds its entry in place of `r`'s;
* `MOVDnop` emits no code and keeps the table;
* `MOVDreg x` homed in `r` (genssa's `MOVD Rx, Rr`, or nothing when the registers agree) gives
  `r` the entry of `x`'s register, if it has one;
* every other value empties the table.

`movdOK29` requires each `MOVDnop x` and `MOVDreg x` to find `(x`'s register, `x`'s class,
`signOf x)` in the table before it. `GoFV/Proof/Gen/G29.lean` proves what an accepted function
satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The upper-bit table after `MOVDreg x`, `x` in `rx` and the value in `rv`: `rv` gets the entry
of `rx`, if it has one. -/
def movdRegStep (L : List (Nat × Nat × Bool)) (rx rv : Nat) : List (Nat × Nat × Bool) :=
  match L.find? (·.1 == rx) with
  | some (_, c, sg) => (rv, c, sg) :: L.filter (·.1 != rv)
  | none => L.filter (·.1 != rv)

/-- The upper-bit table after value `v` (module doc). -/
def uStepL (lc : LocCtx) (L : List (Nat × Nat × Bool)) (v : Value) : List (Nat × Nat × Bool) :=
  match uEntry lc v with
  | some e => e :: L.filter (·.1 != e.1)
  | none =>
    if v.op == .ARM64MOVDnop then L
    else if v.op == .ARM64MOVDreg then
      match (v.args[0]?).bind (regHome? lc), regHome? lc v.id with
      | some rx, some rv => movdRegStep L rx rv
      | _, _ => []
    else []

/-- The upper-bit table before value `i` of block `blk`. -/
def uL (lc : LocCtx) (blk : Block) : Nat → List (Nat × Nat × Bool)
  | 0 => []
  | i + 1 =>
    match (blk.values[i]?).bind lc.ctx.f.value? with
    | some v => uStepL lc (uL lc blk i) v
    | none => []

/-- Every `MOVDnop x` and `MOVDreg x` finds `x`'s register, class and `signOf` in the upper-bit
table `uL` before it. -/
def movdOK29 (lc : LocCtx) : Bool :=
  lc.ctx.f.blocks.toList.all fun bid =>
    match lc.ctx.f.block? bid with
    | none => true
    | some b => (List.range b.values.size).all fun i =>
      match (b.values[i]?).bind lc.ctx.f.value? with
      | some v => (v.op != .ARM64MOVDnop && v.op != .ARM64MOVDreg) || match v.args[0]? with
        | some x => match regHome? lc x, cls (lc.ty x) with
          | some r, some c => (uL lc b i).contains (r, c, lc.signOf lc.ctx.f.valueTab.size x)
          | _, _ => false
        | none => false
      | none => true

/-- Slice G29 of the genssa validator (module doc): G28 with the upper-bit table `uL`. -/
def checkG29 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind28 lc g, tm := cx.termG3 }
    let tab ← c.blocks lc.ctx.f.blocks.toList
    unless pbOK lc ps.toList tab do throw "bounds panic PCDATA"
    unless movdOK29 lc do throw "MOVDnop/MOVDreg: upper bits unknown"
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
  else checkNL lc ps bstart g

end GoFV.Gen.Check

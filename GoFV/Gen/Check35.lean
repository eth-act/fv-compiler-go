import GoFV.Gen.Check34

/-!
# The genssa validator, slice G35: the upper-bit table across pair loads
(`docs/plans/proofs3.md` §4)

`checkG35 lc ps bstart g` is slice G34 (`GoFV/Gen/Check34.lean`) with a larger upper-bit table:
besides `keep34`'s values, G35's `uL35` keeps the entries of the registers a value does not write
across the pair load `LDP` (G4's, G6's at a frame variable and G22's at a global), which writes the
two registers of its pair home, and across `Select0`/`Select1` of an `LDP`, which emit no code
(`pairOp35`); across these it drops the entries of the registers of the value's home (`homeRegs`:
its register, or the two of its pair). A narrow load at any operand, also of a frame variable
(G6), puts its entry in place of its register's (`ldEntry35`; G20's `uEntry` names only loads
through a register or of a global). `uStep35` is G34's `uStep34` otherwise. The dataflow
(`uPass35`, `uFlow35`, `uIn35`), its check (`uEdgesOK35`) and the `MOVDnop`/`MOVDreg` check
(`movdOK35`) are G34's over `uStep35`.

On a function with no arm64 op, `checkG35` is `checkG33`'s `checkNL30`.
`GoFV/Proof/Gen/G35.lean` proves what an accepted function satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The pair load `LDP`, and `Select0`/`Select1` of a value whose op is `LDP`. -/
def pairOp35 (lc : LocCtx) (v : Value) : Bool :=
  v.op == .ARM64LDP || ((v.op == .Select0 || v.op == .Select1) &&
    ((v.args[0]?).bind lc.ctx.f.value?).any (·.op == .ARM64LDP))

/-- The registers of `id`'s home: its register, or the two registers of its pair. -/
def homeRegs (lc : LocCtx) (id : ID) : List Nat :=
  match lc.home id with
  | some (.reg r) => [r]
  | some (.pair (some a) (some b)) => [a, b]
  | _ => []

/-- The entry of a narrow load of `n` bytes (`loadOp?`, at any operand: G3's through a register or
of a global, G6's of a frame variable) homed in register `r` at class `c ∈ {8, 16, 32}`, `8n ≤ c`:
`r` holds the sign (`sg`) or zero extension of its low `c` bits. -/
def ldEntry35 (lc : LocCtx) (v : Value) : Option (Nat × Nat × Bool) :=
  match loadOp? v.op, regHome? lc v.id, cls (lc.ty v.id) with
  | some (as, n, sg), some r, some c =>
    if as != .MOVD && (c == 8 || c == 16 || c == 32) && 8 * n ≤ c then some (r, c, sg) else none
  | _, _, _ => none

/-- The upper-bit table after value `v` (module doc). -/
def uStep35 (lc : LocCtx) (L : List (Nat × Nat × Bool)) (v : Value) : List (Nat × Nat × Bool) :=
  match ldEntry35 lc v with
  | some e => e :: L.filter (·.1 != e.1)
  | none => if pairOp35 lc v then L.filter (!(homeRegs lc v.id).contains ·.1) else uStep34 lc L v

/-- The upper-bit table before value `i` of block `blk`, which starts with `L0` (nothing past the
start on a function with no arm64 op). -/
def uL35 (lc : LocCtx) (L0 : List (Nat × Nat × Bool)) (blk : Block) :
    Nat → List (Nat × Nat × Bool)
  | 0 => L0
  | i + 1 =>
    if lc.ctx.f.lowered then
      match (blk.values[i]?).bind lc.ctx.f.value? with
      | some v => uStep35 lc (uL35 lc L0 blk i) v
      | none => []
    else []

/-- One pass of the forward dataflow over the blocks `bids` (`uPass` over `uL35`). -/
def uPass35 (lc : LocCtx) (tin : Std.HashMap ID (List (Nat × Nat × Bool))) (bids : List ID) :
    Std.HashMap ID (List (Nat × Nat × Bool)) :=
  bids.foldl (fun tin bid =>
    match tin[bid]?, lc.ctx.f.block? bid with
    | some L, some b =>
      let out := uL35 lc L b b.values.size
      b.succs.foldl (fun tin e =>
        match tin[e.b]? with
        | some L' => tin.insert e.b (L'.filter (out.contains ·))
        | none => tin.insert e.b out) tin
    | _, _ => tin) tin

/-- The block starts: the dataflow from the entry block (nothing known) to a fixed point (at most
`fuel` passes). -/
def uFlow35 (lc : LocCtx) (fuel : Nat) : Std.HashMap ID (List (Nat × Nat × Bool)) :=
  let bids := lc.ctx.f.blocks.toList
  let rec go : Nat → Std.HashMap ID (List (Nat × Nat × Bool)) →
      Std.HashMap ID (List (Nat × Nat × Bool))
    | 0, tin => tin
    | n + 1, tin =>
      let tin' := uPass35 lc tin bids
      if bids.all (fun b => tin'[b]? == tin[b]?) then tin' else go n tin'
  go fuel (({} : Std.HashMap ID (List (Nat × Nat × Bool))).insert lc.ctx.f.entry [])

/-- The upper-bit table at the start of block `b` (nothing on a function with no arm64 op). -/
def uIn35 (lc : LocCtx) (b : ID) : List (Nat × Nat × Bool) :=
  if lc.ctx.f.lowered then ((uFlow35 lc (65 * lc.ctx.f.blocks.size + 2))[b]?).getD [] else []

/-- The entry block starts with nothing in the table, and every successor's start is in its
predecessor's end. -/
def uEdgesOK35 (lc : LocCtx) : Bool :=
  uIn35 lc lc.ctx.f.entry == [] && lc.ctx.f.blocks.toList.all fun bid =>
    match lc.ctx.f.block? bid with
    | none => true
    | some b =>
      let out := uL35 lc (uIn35 lc bid) b b.values.size
      b.succs.toList.all fun e => (uIn35 lc e.b).all (out.contains ·)

/-- Every `MOVDnop x` and `MOVDreg x` finds `x`'s register, class and `signOf` in the upper-bit
table `uL35` before it. -/
def movdOK35 (lc : LocCtx) : Bool :=
  lc.ctx.f.blocks.toList.all fun bid =>
    match lc.ctx.f.block? bid with
    | none => true
    | some b => (List.range b.values.size).all fun i =>
      match (b.values[i]?).bind lc.ctx.f.value? with
      | some v => (v.op != .ARM64MOVDnop && v.op != .ARM64MOVDreg) || match v.args[0]? with
        | some x => match regHome? lc x, cls (lc.ty x) with
          | some r, some c =>
            (uL35 lc (uIn35 lc bid) b i).contains (r, c, lc.signOf lc.ctx.f.valueTab.size x)
          | _, _ => false
        | none => false
      | none => true

/-- Slice G35 of the genssa validator (module doc): G34 with the upper-bit table `uL35`. -/
def checkG35 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind33 lc g, tm := cx.termG3 }
    let tab ← c.blocks lc.ctx.f.blocks.toList
    unless pbOK lc ps.toList tab do throw "bounds panic PCDATA"
    unless movdOK35 lc && uEdgesOK35 lc do throw "MOVDnop/MOVDreg: upper bits unknown"
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

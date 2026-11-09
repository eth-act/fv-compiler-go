import GoFV.Gen.Check19

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G20: `MOVDnop` after its narrow load (`docs/plans/proofs3.md` §4, §8)

`checkG20 lc ps bstart g` extends slice G19 (`GoFV/Gen/Check19.lean`) by `MOVDnop x`, which genssa
emits as nothing (`ssa.go`, `OpARM64MOVDnop`: regalloc puts it in `x`'s register) and which
`runLoc` runs as `movdLoc`: the 64-bit zero or sign extension of `x`'s low bits, as
`LocCtx.signOf` names from `x`'s producer. The machine register holds that word only when the
instruction that wrote it extended its low bits so; `LocMatch` relates only the low bits of a
narrow integer.

**The upper-bit table.** `uAt lc blk i` names what the machine register written by the value
before value `i` holds above its low bits (`uEntry`): after a narrow load of `n` bytes
(`MOV{B,H,W}{,U}load` of an address in a register or a global, as G3; `MOV{B,H,W}{,U}loadidx*`, as
G14) homed in register `r` with a result of class `c ∈ {8, 16, 32}`, `c ≥ 8n`, `r` holds the zero
or sign extension of its low `c` bits, as the load's signedness says. Every other value, and a
block's start, leaves nothing known. (A table that carries entries across values that keep the
register, `docs/plans/proofs3.md` §8, needs every slice's value lemma to say which registers it
keeps; on quick-v10, 1,300 of the 1,520 `MOVDnop`s follow their load directly.)

G20 accepts `MOVDnop x` with no temporary, `x` its only argument, homed in `x`'s register (one
G1 may write) at an integer class, `x` of class 8, 16 or 32, no code (`nopKind`), when the table
before it names `x`'s register at `x`'s class with the signedness `signOf` gives `x` (`movdOK`,
which slice G21 also applies to `MOVDreg x`).

`GoFV/Proof/Gen/G20.lean` proves what an accepted function satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The narrow loads G3 and G14 run, with their bytes and signedness: an address in a register or
a global (`loadOp?`, not `MOVD`; no frame variable), or a register-index load (`loadIdxOp?`, not
`MOVD`). -/
def narrowLd? (lc : LocCtx) (v : Value) : Option (Nat × Bool) :=
  match loadOp? v.op, loadIdxOp? v.op with
  | some (as, n, sg), _ =>
    if as == .MOVD then none
    else match v.aux with
      | none => some (n, sg)
      | some _ =>
        if (v.args[0]?.bind lc.ctx.f.value?).map (·.op) == some .SB then some (n, sg) else none
  | none, some (as, n, _, sg) => if as == .MOVD then none else some (n, sg)
  | none, none => none

/-- What the register written by `v` holds above its low bits: `(r, c, sg)` when `v` is a narrow
load of `n` bytes homed in register `r` at class `c ∈ {8, 16, 32}`, `8n ≤ c`, and `r` holds the
sign (`sg`) or zero extension of its low `c` bits. -/
def uEntry (lc : LocCtx) (v : Value) : Option (Nat × Nat × Bool) :=
  match narrowLd? lc v, regHome? lc v.id, cls (lc.ty v.id) with
  | some (n, sg), some r, some c =>
    if (c == 8 || c == 16 || c == 32) && 8 * n ≤ c then some (r, c, sg) else none
  | _, _, _ => none

/-- The upper-bit table before value `i` of block `blk`: the entry of value `i - 1`. -/
def uAt (lc : LocCtx) (blk : Block) (i : Nat) : Option (Nat × Nat × Bool) :=
  match i with
  | 0 => none
  | i + 1 => ((blk.values[i]?).bind lc.ctx.f.value?).bind (uEntry lc)

/-- `MOVDnop x`: no temporary, one argument, homed in `x`'s register (one G1 may write) at an
integer class, `x` of class 8, 16 or 32; no code. -/
def nopKind (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  let some x := v.args[0]? | throw s!"v{v.id}: MOVDnop shape"
  unless v.args.size == 1 do throw s!"v{v.id}: MOVDnop shape"
  let some r := regHome? lc v.id | throw s!"v{v.id}: MOVDnop shape"
  unless destOK r && r != zeroReg && regHome? lc x == some r do
    throw s!"v{v.id}: MOVDnop shape"
  let cv := cls (lc.ty v.id)
  unless cv == some 8 || cv == some 16 || cv == some 32 || cv == some 64 do
    throw s!"v{v.id}: MOVDnop shape"
  let c := cls (lc.ty x)
  unless c == some 8 || c == some 16 || c == some 32 do throw s!"v{v.id}: MOVDnop widths"
  return .none

/-- What `v` emits in G20, or why it is outside the slice. -/
def vkind20 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  if v.op == .ARM64MOVDnop then nopKind lc v else vkind19 lc g v

/-- Every `MOVDnop x` and `MOVDreg x` (`runLoc`'s `movdLoc`) finds `x`'s register, class and
`signOf` in the upper-bit table before it. -/
def movdOK (lc : LocCtx) : Bool :=
  lc.ctx.f.blocks.toList.all fun bid =>
    match lc.ctx.f.block? bid with
    | none => true
    | some b => (List.range b.values.size).all fun i =>
      match (b.values[i]?).bind lc.ctx.f.value? with
      | some v => (v.op != .ARM64MOVDnop && v.op != .ARM64MOVDreg) || match v.args[0]? with
        | some x => match regHome? lc x, cls (lc.ty x) with
          | some r, some c =>
            uAt lc b i == some (r, c, lc.signOf lc.ctx.f.valueTab.size x)
          | _, _ => false
        | none => false
      | none => true

/-- Slice G20 of the genssa validator (module doc): G4's tables of the accepted function. -/
def checkG20 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless lc.ctx.f.lowered do throw "not lowered"
  let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
  let cx : Cx := { lc, ps, idx, bstart }
  let c : Cx2 := { cx, g, vk := vkind20 lc g, tm := cx.termG3 }
  let tab ← c.blocks lc.ctx.f.blocks.toList
  unless pbOK lc ps.toList tab do throw "bounds panic PCDATA"
  unless movdOK lc do throw "MOVDnop: upper bits unknown"
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

end GoFV.Gen.Check

import GoFV.Gen.Check18
import GoFV.Asm.Abi

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G19: bounds panics (`docs/plans/proofs3.md` §4)

`checkG19 lc ps bstart g` extends slice G18 (`GoFV/Gen/Check18.lean`) by the lowered bounds
panics `LoweredPanicBounds{RR,RC,CR,CC} [kind] … mem` (`pbOp`): Phase 1's `panicBounds` of the
index `x` and the length `y`, each in a register (`R`) or an aux constant (`C`). Genssa
(`ssa.go:1752-1835`, `Arm64ValueRt.panicBounds`) moves a constant outside `0..31`
(`BoundsMaxConst`) into a register (`MOVD $c, R0` or `R1`), then emits
`PCDATA $PCDATA_PanicBounds, $c` with `c` the `abi.BoundsEncode` of the kind's error code, its
signedness and the operands (`pbEnc`), then `CALL runtime.panicBounds(SB)`, whose runtime hook
decodes `c` from the PC-value table at the call (`boundsPanic`) and panics.

G19 accepts such a value with no temporary, the memory shape and no home, its register operands
of class 64 in `R0`–`R15` (`BoundsMaxReg`), the memory last (`pbInfo`): the `MOVD`s of its moved
constants and the `CALL` (`pbPats`); the `PCDATA_PanicBounds` in force at that `CALL` in the
Prog list (`pbData`, a no-op Prog between them) is the encoding (`pbOK`). It rejects a `CR` whose
constant index is outside `0..31`: genssa, as Go, moves it to a register without marking it so in
the encoding, and the runtime reports the index 0 or 1 (#541).

`GoFV/Proof/Gen/G19.lean` proves what an accepted function satisfies (`g19_value`, `g19_term`,
`g19_nilPanic`, `g19_boundsPanic`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The lowered bounds panics. -/
def pbOp : Op → Bool
  | .ARM64LoweredPanicBoundsRR | .ARM64LoweredPanicBoundsRC | .ARM64LoweredPanicBoundsCR
  | .ARM64LoweredPanicBoundsCC => true
  | _ => false

/-- `abi.BoundsEncode` of the error code, the signedness of `x` (recorded only when `x` is in a
register), whether `x` and `y` are registers, and their register numbers or constants. -/
def pbEnc (code : Nat) (signed xReg yReg : Bool) (xv yv : Nat) : Nat :=
  ((if xReg then 1 + (if signed then 4 else 0) + 8 * xv else 4 * xv) + (if yReg then 2 else 0) +
    128 * yv) * 9 + code

/-- The runtime symbol bounds panics call (`runtime.panicBounds`, ABIInternal). -/
def pbSym : GoStr × Nat := (GoStr.ofString "runtime.panicBounds", 1)

/-- The `CALL` target of a bounds panic: `runtime.panicBounds(SB)`. -/
def pbTarget (g : G2In) (a : Addr) : Bool :=
  a.type == .MEM && a.name == .EXTERN && a.reg == 0 && a.index == 0 && a.offset == 0 &&
    match a.sym with
    | some y => g.syms[y]? == some pbSym
    | none => false

/-- `MOVD $c, R<k>`: a constant operand moved to a register. -/
def pbMov (k : Nat) (c : Int) : Pat :=
  ⟨plain .MOVD (· == constA c) (· == regA (GoFV.Asm.ARM64.REG_R0 + k)), "MOVD"⟩

/-- `CALL runtime.panicBounds(SB)`. -/
def pbCall (g : G2In) : Pat := ⟨plain .CALL (fun a : Addr => a == {}) (pbTarget g), "CALL"⟩

/-- The Progs of a bounds panic with the moves `mvs`: the `MOVD`s, then the `CALL`. -/
def pbPats (g : G2In) (mvs : List (Nat × Int)) : List Pat :=
  mvs.map (fun km => pbMov km.1 km.2) ++ [pbCall g]

/-- The register number `k` of a register operand `REG_R0 + k`, `k ≤ 15` (`BoundsMaxReg`). -/
def pbReg (v : Value) (r : Int) : Except String Nat := do
  let k := r - GoFV.Asm.ARM64.REG_R0
  unless 0 ≤ k && k ≤ 15 do throw s!"v{v.id}: bounds panic register"
  return k.toNat

/-- A constant the encoding holds (`0..31`, `BoundsMaxConst`). -/
def pbConst (c : Int) : Bool := 0 ≤ c && c ≤ 31

/-- The constant of a `PanicBoundsC` aux (`RC`, `CR`). -/
def pbcOf (lc : LocCtx) (v : Value) : Option Int :=
  match v.aux.bind lc.ctx.tabs.aux? with
  | some { kind := .pbc c, .. } => some c
  | _ => none

/-- The constants of a `PanicBoundsCC` aux (`CC`). -/
def pbccOf (lc : LocCtx) (v : Value) : Option (Int × Int) :=
  match v.aux.bind lc.ctx.tabs.aux? with
  | some { kind := .pbcc cx cy, .. } => some (cx, cy)
  | _ => none

/-- The `ssa.BoundsKind` of a bounds panic, below 17 (`BoundsConvert` = 16). -/
def pbKindOf (v : Value) : Except String Nat := do
  let k := v.auxInt.toInt
  unless 0 ≤ k && k ≤ 16 do throw s!"v{v.id}: bounds panic kind"
  return k.toNat

/-- Whether kind `k` reads `x` signed (`ssa.BoundsKind.Code`). -/
def pbSigned (k : Nat) : Bool := k % 2 == 0 && k < 16

/-- The encoding of a bounds panic and the constants genssa moves to registers (register,
constant), as `ssa.go`: a register operand at its register; a constant in `0..31` in the
encoding; another moved to `R0` for `x` and to `R1` (`R0` if `x` is in a register other than `R0`)
for `y`. -/
def pbInfo (lc : LocCtx) (v : Value) : Except String (Nat × List (Nat × Int)) := do
  let k ← pbKindOf v
  let code := k / 2
  let sg := pbSigned k
  match v.op with
  | .ARM64LoweredPanicBoundsRR =>
    unless v.args.size == 3 do throw s!"v{v.id}: bounds panic shape"
    let (cx, rx) ← argObj lc v 0
    let (cy, ry) ← argObj lc v 1
    memArg lc v 2
    unless cx == 64 && cy == 64 do throw s!"v{v.id}: bounds panic widths"
    let xv ← pbReg v rx
    let yv ← pbReg v ry
    return (pbEnc code sg true true xv yv, [])
  | .ARM64LoweredPanicBoundsRC =>
    unless v.args.size == 2 do throw s!"v{v.id}: bounds panic shape"
    let (cx, rx) ← argObj lc v 0
    memArg lc v 1
    unless cx == 64 do throw s!"v{v.id}: bounds panic widths"
    let xv ← pbReg v rx
    let some c := pbcOf lc v | throw s!"v{v.id}: bounds panic aux"
    if pbConst c then return (pbEnc code sg true false xv c.toNat, [])
    let yv := if xv == 0 then 1 else 0
    return (pbEnc code sg true true xv yv, [(yv, c)])
  | .ARM64LoweredPanicBoundsCR =>
    unless v.args.size == 2 do throw s!"v{v.id}: bounds panic shape"
    let (cy, ry) ← argObj lc v 0
    memArg lc v 1
    unless cy == 64 do throw s!"v{v.id}: bounds panic widths"
    let yv ← pbReg v ry
    let some c := pbcOf lc v | throw s!"v{v.id}: bounds panic aux"
    unless pbConst c do throw s!"v{v.id}: bounds panic: constant index outside 0..31 (#541)"
    return (pbEnc code sg false true c.toNat yv, [])
  | .ARM64LoweredPanicBoundsCC =>
    unless v.args.size == 1 do throw s!"v{v.id}: bounds panic shape"
    memArg lc v 0
    let some (cx, cy) := pbccOf lc v | throw s!"v{v.id}: bounds panic aux"
    let xr := !pbConst cx
    let yr := !pbConst cy
    return (pbEnc code sg xr yr (if xr then 0 else cx.toNat) (if yr then 1 else cy.toNat),
      (if xr then [(0, cx)] else []) ++ (if yr then [(1, cy)] else []))
  | _ => throw s!"v{v.id}: not a bounds panic"

/-- A bounds panic: no temporary, the memory shape and no home, `pbInfo`; its `MOVD`s and `CALL`. -/
def pbKind (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless memTy (lc.ty v.id) && lc.home v.id == none do throw s!"v{v.id}: bounds panic shape"
  let (_, mvs) ← pbInfo lc v
  return .progs (pbPats g mvs)

/-- What `v` emits in G19, or why it is outside the slice. -/
def vkind19 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  if pbOp v.op then pbKind lc g v else vkind18 lc g v

/-- The operand of the `PCDATA_PanicBounds` in force at the Prog at index `k` of `ps`: the last
`PCDATA $PCDATA_PanicBounds` before it. -/
def pbData (ps : List Prog) (k : Nat) : Option Addr :=
  ((ps.take k).reverse.find? fun p =>
    p.as == .PCDATA && p.from_ == constA GoFV.Asm.Abi.PCDATA_PanicBounds).map (·.to)

/-- The `PCDATA_PanicBounds` at each bounds panic's `CALL` (the Prog before the next value's
start in the PC table) is its encoding. -/
def pbOK (lc : LocCtx) (ps : List Prog) (tab : PcTab) : Bool :=
  tab.all fun (bid, row) =>
    match lc.ctx.f.block? bid with
    | none => true
    | some b => (List.range b.values.size).all fun i =>
      match (b.values[i]?).bind lc.ctx.f.value? with
      | some v => !pbOp v.op || match pbInfo lc v with
        | .ok (c, _) => pbData ps (row.getD (i + 1) 0 - 1) == some (constA c)
        | .error _ => false
      | none => true

/-- Slice G19 of the genssa validator (module doc): G4's tables of the accepted function. -/
def checkG19 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless lc.ctx.f.lowered do throw "not lowered"
  let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
  let cx : Cx := { lc, ps, idx, bstart }
  let c : Cx2 := { cx, g, vk := vkind19 lc g, tm := cx.termG3 }
  let tab ← c.blocks lc.ctx.f.blocks.toList
  unless pbOK lc ps.toList tab do throw "bounds panic PCDATA"
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

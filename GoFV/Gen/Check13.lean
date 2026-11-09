import GoFV.Gen.Check12

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G13: zeroing (`docs/plans/proofs3.md` §4)

`checkG13 lc ps bstart g` extends slice G12 (`GoFV/Gen/Check12.lean`) by `LoweredZero [n] p mem`,
`n` zero bytes at `p` (`n ≥ 16`; larger blocks are `LoweredZeroLoop`'s). Genssa emits the
straight-line stores of `zeroTail` (`ssa.go:1503-1523`, `GoFV/Gen/Arm64ValueRt.lean`): an
`STP (ZR, ZR), off(Rp)` for each 16 bytes, then, of the `r = n mod 16` bytes left, an
`MOVD ZR, off(Rp)` for 8 of them when `r > 8`, and an `MOVD ZR` of the last 8 bytes (overlapping
the previous store) when bytes remain (`zeroOffs`).

G13 accepts it with no temporary, `p` in a register of class 64, the memory last, the value a
memory with no home, and those Progs (`zeroPat`, `VKind2.progs`) when their stores lie inside the
`n` bytes and cover each of them (`zeroCovers`, decided per value).

`GoFV/Proof/Gen/G13.lean` proves what an accepted function satisfies (`g13_value`, `g13_term`,
`g13_nilPanic`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The width in bytes of a zeroing store: 16 for an `STP (ZR, ZR)`, 8 for an `MOVD ZR`. -/
def zeroW (pair : Bool) : Nat := if pair then 16 else 8

/-- The stores of `zeroTail` for `n` bytes, in order: whether it is an `STP` and its offset. -/
def zeroOffs (n : Nat) : List (Bool × Nat) :=
  let k := n / 16
  let r := n % 16
  let off := 16 * k
  (List.range k).map (fun i => (true, 16 * i)) ++
    if 8 < r then [(false, off), (false, off + r - 8)]
    else if r != 0 then [(false, off + r - 8)] else []

/-- The stores lie inside the `n` bytes and cover each of them. -/
def zeroCovers (n : Nat) (offs : List (Bool × Nat)) : Bool :=
  offs.all (fun (pr, o) => o + zeroW pr ≤ n) &&
    (List.range n).all fun j => offs.any fun (pr, o) => o ≤ j && j < o + zeroW pr

/-- The obj number of `ZR` (`REGZERO`). -/
def zrA : Int := ARM64.REG_R0 + 31

/-- The Prog of a zeroing store off `Rp`: `STP (ZR, ZR), off(Rp)` or `MOVD ZR, off(Rp)`. -/
def zeroPat (rp : Int) (st : Bool × Nat) : Pat :=
  if st.1 then .ofShape { as := .STP, from_ := pairA zrA zrA, to := memA rp st.2 }
  else .ofShape { as := .MOVD, from_ := regA zrA, to := memA rp st.2 }

/-- `LoweredZero [n] p mem`: no temporary, `p` in a register of class 64, the memory last, a
memory with no home, `16 ≤ n`, and `zeroTail`'s stores covering the `n` bytes. -/
def zeroKind (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 2 && memTy (lc.ty v.id) && lc.home v.id == none do
    throw s!"v{v.id}: zero shape"
  let (c, rp) ← argObj lc v 0
  memArg lc v 1
  let n := v.auxInt.toInt
  unless c == 64 && 16 ≤ n do throw s!"v{v.id}: zero shape"
  let offs := zeroOffs n.toNat
  unless zeroCovers n.toNat offs do throw s!"v{v.id}: zero stores"
  return .progs (offs.map (zeroPat rp))

/-- What `v` emits in G13, or why it is outside the slice. -/
def vkind13 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  if v.op == .ARM64LoweredZero then zeroKind lc v else vkind12 lc g v

/-- Slice G13 of the genssa validator (module doc): G4's tables of the accepted function. -/
def checkG13 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless lc.ctx.f.lowered do throw "not lowered"
  let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
  let cx : Cx := { lc, ps, idx, bstart }
  let c : Cx2 := { cx, g, vk := vkind13 lc g, tm := cx.termG3 }
  let tab ← c.blocks lc.ctx.f.blocks.toList
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

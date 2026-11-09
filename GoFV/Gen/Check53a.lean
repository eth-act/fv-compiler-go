import GoFV.Gen.Check50

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G53, group A: `LoweredMove` (`docs/plans/proofs3.md` §4)

`LoweredMove [n] dst src mem` copies `n` bytes from `src` to `dst` (`n ≥ 16`; larger copies are
`LoweredMoveLoop`'s). Genssa emits nothing when `dst` and `src` are in the same register, else the
straight-line chunks of `moveTail` (`ssa.go:1622-1648`, `GoFV/Gen/Arm64ValueRt.lean`), each a load
into the op's fixed temporaries then a store at the same offset off `dst`: a `FLDPQ off(Rsrc),
(F16, F17)`; `FSTPQ (F16, F17), off(Rdst)` for each 32 bytes, a `FMOVQ off(Rsrc), F16`;
`FMOVQ F16, off(Rdst)` for 16 of the bytes left, then of the `r < 16` bytes left a `MOVD off(Rsrc),
R25`; `MOVD R25, off(Rdst)` for 8 of them when `r > 8`, and one of the last 8 bytes (overlapping
the previous chunk) when bytes remain (`moveOffs`).

G53's group A accepts it with no temporary, `dst` and `src` in registers of class 64 other than
`R25` (the 8-byte chunks' temporary, written before the next chunk reads them), the memory last,
the value a memory with no home, `16 ≤ n`, and those Progs (`movePats`, `VKind2.progs`) when the
chunks lie inside the `n` bytes and cover each of them (`moveCovers`, decided per value).
`vkind53a lc v` is `none` exactly off `LoweredMove` (`op53a`). `GoFV/Proof/Gen/G53a.lean` proves
what an accepted value satisfies under the run premise `Pre53a`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The op of G53's group A. -/
def op53a (op : Op) : Bool := op == .ARM64LoweredMove

/-- The obj numbers of `LoweredMove`'s temporaries `R25`, `F16`, `F17` (its `clobbers`). -/
def r25A : Int := ARM64.REG_R0 + 25
def f16A : Int := ARM64.REG_F0 + 16
def f17A : Int := ARM64.REG_F0 + 17

/-- The bytes a chunk of kind `w` copies: 32 (`FLDPQ`/`FSTPQ`), 16 (`FMOVQ`) or 8 (`MOVD`). -/
def moveW (w : Nat) : Nat := if w = 32 then 32 else if w = 16 then 16 else 8

/-- The chunks of `moveTail` for `n` bytes, in order: kind and offset. -/
def moveOffs (n : Nat) : List (Nat × Nat) :=
  let k := n / 32
  let r := n % 32
  let off := 32 * k
  let c16 : List (Nat × Nat) := if 16 ≤ r then [(16, off)] else []
  let off := if 16 ≤ r then off + 16 else off
  let r := r % 16
  (List.range k).map (fun i => (32, 32 * i)) ++ c16 ++
    if 8 < r then [(8, off), (8, off + r - 8)]
    else if r != 0 then [(8, off + r - 8)] else []

/-- The chunks lie inside the `n` bytes and cover each of them. -/
def moveCovers (n : Nat) (cs : List (Nat × Nat)) : Bool :=
  cs.all (fun (w, o) => o + moveW w ≤ n) &&
    (List.range n).all fun j => cs.any fun (w, o) => o ≤ j && j < o + moveW w

/-- The load of chunk `c` off `Rsrc` (obj number `rs`) into the temporaries. -/
def moveLd (rs : Int) (c : Nat × Nat) : Pat :=
  if c.1 = 32 then .ofShape { as := .FLDPQ, from_ := memA rs c.2, to := pairA f16A f17A }
  else if c.1 = 16 then .ofShape { as := .FMOVQ, from_ := memA rs c.2, to := regA f16A }
  else .ofShape { as := .MOVD, from_ := memA rs c.2, to := regA r25A }

/-- The store of chunk `c` from the temporaries off `Rdst` (obj number `rd`). -/
def moveSt (rd : Int) (c : Nat × Nat) : Pat :=
  if c.1 = 32 then .ofShape { as := .FSTPQ, from_ := pairA f16A f17A, to := memA rd c.2 }
  else if c.1 = 16 then .ofShape { as := .FMOVQ, from_ := regA f16A, to := memA rd c.2 }
  else .ofShape { as := .MOVD, from_ := regA r25A, to := memA rd c.2 }

/-- The two Progs of chunk `c`. -/
def movePats (rs rd : Int) (c : Nat × Nat) : List Pat := [moveLd rs c, moveSt rd c]

/-- `LoweredMove [n] dst src mem` (module doc): what it emits. -/
def moveKind (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 3 && memTy (lc.ty v.id) && lc.home v.id == none do
    throw s!"v{v.id}: move shape"
  let (cd, rd) ← argObj lc v 0
  let (cs, rs) ← argObj lc v 1
  memArg lc v 2
  let n := v.auxInt.toInt
  unless cd == 64 && cs == 64 && 16 ≤ n && rd != r25A && rs != r25A do
    throw s!"v{v.id}: move shape"
  let offs := moveOffs n.toNat
  unless moveCovers n.toNat offs do throw s!"v{v.id}: move chunks"
  return .progs (if rd == rs then [] else offs.flatMap (movePats rs rd))

/-- What `v` emits if its op is G53's group A (`op53a`), else `none`. -/
def vkind53a (lc : LocCtx) (v : Value) : Option (Except String VKind2) :=
  if v.op == .ARM64LoweredMove then some (moveKind lc v) else none

end GoFV.Gen.Check

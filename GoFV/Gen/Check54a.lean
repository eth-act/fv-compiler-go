import GoFV.Gen.Check53a

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G54, group A: `LoweredZeroLoop`, `LoweredMoveLoop` (`docs/plans/proofs3.md` §4)

`LoweredZeroLoop [n] p mem` zeroes `n` bytes at `p` and `LoweredMoveLoop [n] dst src mem` copies
`n` bytes from `src` to `dst` (`n ≥ 192`, `ARM64.rules:377`, `439`). Genssa (`ssa.go:1525-1600`,
`1650-1735`, `GoFV/Gen/Arm64ValueRt.lean`) emits a loop of `n / 64` iterations of 64 bytes, then
the straight-line tail of `LoweredZero`/`LoweredMove` for the `n mod 64` bytes left, off the
advanced pointers:

* `MOVD $n/64, Rc`, the counter (`ZeroLoop`: the value's temporary; `MoveLoop`: `R24`);
* the body: four `STP.P (ZR, ZR), 16(Rp)` (`ZeroLoop`), or two `FLDPQ.P 32(Rsrc), (F16, F17)`;
  `FSTPQ.P (F16, F17), 32(Rdst)` pairs (`MoveLoop`), each post-incrementing its base register;
* `SUB $1, Rc`; `CBNZ Rc, <head>`, the head the Prog after the counter's `MOVD`;
* `zeroTail`'s stores (`zeroOffs`, `zeroPat`) or `moveTail`'s chunks (`moveOffs`, `movePats`) of
  the `n mod 64` bytes left.

`MoveLoop` emits nothing when `dst` and `src` are in the same register.

G54's group A accepts them with the memory last, the value a memory with no home, `64 ≤ n`, the
pointers in registers of class 64 that a value may write (Go 0–25, `R0`–`R17`, `R19`–`R26`), the
counter another such register (`ZeroLoop`: the temporary, distinct from `p`; `MoveLoop`: no
temporary, `dst` and `src` other than `R24` and `R25`), and the tail when its stores or chunks lie
inside the `n mod 64` bytes and cover them (`zeroCovers`, `moveCovers`, decided per value). The
`CBNZ` pattern takes any operand; `loopOK` checks on the whole function that each loop's `CBNZ`
(the seventh Prog of the value, after no-ops) branches to the Prog after its `MOVD` (`loopTgt`).
`vkind54a lc v` is `none` exactly off the two ops (`op54a`). `GoFV/Proof/Gen/G54a.lean` and
`G54b.lean` prove what an accepted value satisfies under the run premise `Pre54`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The ops of G54's group A. -/
def op54a (op : Op) : Bool := op == .ARM64LoweredZeroLoop || op == .ARM64LoweredMoveLoop

/-- The obj number of `LoweredMoveLoop`'s counter `R24`. -/
def r24A : Int := ARM64.REG_R0 + 24

/-- `p` has shape `sh`, post-indexed (`.P`, `C_XPOST`), no rest or second destination. -/
def Shape.okP (sh : Shape) (p : Prog) : Bool :=
  p.as == sh.as && p.from_ == sh.from_ && p.reg == sh.reg && p.to == sh.to &&
    p.scond == ARM64.C_XPOST.toNat && p.rest.isEmpty && p.regTo2 == 0

/-- `STP.P (ZR, ZR), 16(Rp)`. -/
def stpPPat (rp : Int) : Pat :=
  ⟨Shape.okP { as := .STP, from_ := pairA zrA zrA, to := memA rp 16 }, "STP.P"⟩

/-- `FLDPQ.P 32(Rsrc), (F16, F17)`. -/
def fldpqPPat (rs : Int) : Pat :=
  ⟨Shape.okP { as := .FLDPQ, from_ := memA rs 32, to := pairA f16A f17A }, "FLDPQ.P"⟩

/-- `FSTPQ.P (F16, F17), 32(Rdst)`. -/
def fstpqPPat (rd : Int) : Pat :=
  ⟨Shape.okP { as := .FSTPQ, from_ := pairA f16A f17A, to := memA rd 32 }, "FSTPQ.P"⟩

/-- `CBNZ Rc, <any target>` (`loopOK` fixes the target). -/
def cbnzPat (rc : Int) : Pat :=
  ⟨fun p => p.as == .CBNZ && p.from_ == regA rc && p.reg == 0 && p.scond == 0 &&
    p.rest.isEmpty && p.regTo2 == 0, "CBNZ"⟩

/-- The loop's Progs (module doc): `MOVD $n/64, Rc`, the four body Progs, `SUB $1, Rc`,
`CBNZ Rc`. -/
def loopPats (rc : Int) (n : Int) (body : List Pat) : List Pat :=
  .ofShape { as := .MOVD, from_ := constA (n / 64), to := regA rc } :: body ++
    [.ofShape { as := .SUB, from_ := constA 1, to := regA rc }, cbnzPat rc]

/-- The body of `ZeroLoop`: four `STP.P (ZR, ZR), 16(Rp)`. -/
def zeroBody (rp : Int) : List Pat := [stpPPat rp, stpPPat rp, stpPPat rp, stpPPat rp]

/-- The body of `MoveLoop`: two `FLDPQ.P`/`FSTPQ.P` pairs. -/
def moveBody (rs rd : Int) : List Pat :=
  [fldpqPPat rs, fstpqPPat rd, fldpqPPat rs, fstpqPPat rd]

/-- Argument `i` of `v` is in a register a value may write, not `ZERO` (Go 0–25). -/
def argDest (lc : LocCtx) (v : Value) (i : Nat) : Bool :=
  match v.args[i]?.bind (regHome? lc) with
  | some r => decide (r < 26)
  | none => false

/-- `LoweredZeroLoop [n] p mem` (module doc): what it emits. -/
def zeroLoopKind (lc : LocCtx) (v : Value) : Except String VKind2 := do
  let some t := (lc.temps[v.id]?).join | throw s!"v{v.id}: zero loop without temporary"
  unless v.args.size == 2 && memTy (lc.ty v.id) && lc.home v.id == none do
    throw s!"v{v.id}: zero loop shape"
  let (c, rp) ← argObj lc v 0
  memArg lc v 1
  let some rc := objOf? t | throw s!"v{v.id}: temporary in register {t}"
  let n := v.auxInt.toInt
  unless c == 64 && 64 ≤ n && argDest lc v 0 && t < 26 && rc != rp do
    throw s!"v{v.id}: zero loop shape"
  let r := n.toNat % 64
  unless zeroCovers r (zeroOffs r) do throw s!"v{v.id}: zero loop stores"
  return .progs (loopPats rc n (zeroBody rp) ++ (zeroOffs r).map (zeroPat rp))

/-- `LoweredMoveLoop [n] dst src mem` (module doc): what it emits. -/
def moveLoopKind (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 3 && memTy (lc.ty v.id) && lc.home v.id == none do
    throw s!"v{v.id}: move loop shape"
  let (cd, rd) ← argObj lc v 0
  let (cs, rs) ← argObj lc v 1
  memArg lc v 2
  let n := v.auxInt.toInt
  unless cd == 64 && cs == 64 && 64 ≤ n && argDest lc v 0 && argDest lc v 1 && rd != r24A &&
      rs != r24A && rd != r25A && rs != r25A do
    throw s!"v{v.id}: move loop shape"
  let r := n.toNat % 64
  unless moveCovers r (moveOffs r) do throw s!"v{v.id}: move loop chunks"
  return .progs (if rd == rs then [] else
    loopPats r24A n (moveBody rs rd) ++ (moveOffs r).flatMap (movePats rs rd))

/-- What `v` emits if its op is G54's group A (`op54a`), else `none`. -/
def vkind54a (lc : LocCtx) (v : Value) : Option (Except String VKind2) :=
  if v.op == .ARM64LoweredZeroLoop then some (zeroLoopKind lc v)
  else if v.op == .ARM64LoweredMoveLoop then some (moveLoopKind lc v)
  else none

/-! ## The loops' branch targets -/

/-- The index after the first Prog at or after `j` that is not a no-op. -/
def nextIdx (ps : Array Prog) (j : Nat) : Nat := skipFrom ps j ps.size + 1

/-- The loop of a value whose Progs start at index `j`: its `CBNZ`, the seventh Prog after
no-ops, branches to the Prog after the first (the counter's `MOVD`). -/
def loopTgt (ps : Array Prog) (j : Nat) : Bool :=
  let k1 := nextIdx ps j
  let kc := nextIdx ps (nextIdx ps (nextIdx ps (nextIdx ps (nextIdx ps (nextIdx ps k1))))) - 1
  match ps[k1]?, ps[kc]? with
  | some h, some c => c.to == brA h.id
  | _, _ => false

/-- `v` emits a loop: a `ZeroLoop`, or a `MoveLoop` whose arguments are in two registers. -/
def loopOp (lc : LocCtx) (v : Value) : Bool :=
  v.op == .ARM64LoweredZeroLoop ||
    (v.op == .ARM64LoweredMoveLoop &&
      v.args[0]?.bind (regHome? lc) != v.args[1]?.bind (regHome? lc))

/-- Every loop branches to its head (`loopTgt`), at its value's start in the PC table. -/
def loopOK (lc : LocCtx) (ps : Array Prog) (tab : PcTab) : Bool :=
  tab.all fun (bid, row) =>
    match lc.ctx.f.block? bid with
    | none => true
    | some b => (List.range b.values.size).all fun i =>
      match (b.values[i]?).bind lc.ctx.f.value? with
      | some v => !loopOp lc v || loopTgt ps (row.getD i 0)
      | none => true

end GoFV.Gen.Check

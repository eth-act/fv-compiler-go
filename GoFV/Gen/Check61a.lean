import GoFV.Gen.Check54a

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G61, group A: the atomic read-modify-writes (`docs/plans/proofs3.md` §4)

`runLoc` runs a lowered atomic as the generic atomic it lowers (`Arm64.atomicOf`, `atomicRoot`):
one read-modify-write of a naturally aligned location (`Atomic.rmw`, `Atomic.cas`). Genssa
(`ssa.go:1038-1352`, `GoFV/Gen/Arm64ValueRt.lean`'s `atomic`) emits for each a load-exclusive /
store-exclusive loop or one LSE instruction (the `*Variant` ops); on one core an exclusive store
always succeeds (`GoFV.Arm64`'s single-core row), so each loop runs once:

* `LoweredAtomicExchange{64,32,8}` (`xchg`): `LDAXR (Rp), Rd`; `STLXR Rv, (Rp), R27`; `CBNZ R27`;
* `LoweredAtomicExchange{64,32,8}Variant` (`xchgV`): `SWPAL Rv, (Rp), Rd`;
* `LoweredAtomicAdd{64,32}` (`add`): `LDAXR (Rp), Rd`; `ADD Rv, Rd`; `STLXR Rd, (Rp), R27`;
  `CBNZ R27`;
* `LoweredAtomicAdd{64,32}Variant` (`addV`): `LDADDAL Rv, (Rp), Rd`; `ADD Rv, Rd`;
* `LoweredAtomicCas{64,32}` (`cas`): `LDAXR (Rp), R27`; `CMP Ro, R27`; `BNE L`;
  `STLXR Rn, (Rp), R27`; `CBNZ R27`; `L: CSET EQ, Rd`;
* `LoweredAtomicCas{64,32}Variant` (`casV`): `MOVD Ro, R27`; `CASAL R27, (Rp), Rn`;
  `CMP Ro, R27`; `CSET EQ, Rd`;
* `LoweredAtomic{And,Or}{64,32,8}` (`andL`, `orL`): `LDAXR (Rp), Rd`; `AND`/`ORR Rv, Rd, Rt`;
  `STLXR Rt, (Rp), R27`; `CBNZ R27` (`Rt` the value's temporary);
* `LoweredAtomicAnd{64,32,8}Variant` (`andV`): `MVN Rv, R27`; `LDCLRAL R27, (Rp), Rd`;
* `LoweredAtomicOr{64,32,8}Variant` (`orV`): `LDORAL Rv, (Rp), Rd`.

The `W`/`B` forms for 4 and 1 bytes (`CMPW`, `MOVW` for a 4-byte compare-and-swap). Group A
accepts them with no aux, the pointer in a 64-bit register other than `ZERO`, every other operand
in a register of class `8n` (`ZERO` allowed), the memory last; the value a tuple of a component and
the memory homed in `(Rd, -)`, `Rd` a register G1 may write: the component of class `8n` (`1`, a
boolean, for a compare-and-swap); `Rd` none of the operand registers (none of them is `R27`, which
holds no Go register); the temporary of `andL`/`orL` (only those have one) a register G1 may
write, distinct from `Rp` and `Rd`. The `CBNZ R27` and `BNE` patterns take any target;
`atomOK` checks on the whole function that each loop's `CBNZ R27` branches to its `LDAXR` (a
target in the Prog list, never taken: the store left `R27 = 0`) and each `cas`'s `BNE` (its third
Prog after no-ops) to its `CSET` (the sixth, `atomTgt`). Their `Select0` is homed in `Rd` and
`Select1` is the memory without a home (no code, `selAtom61`). `vkind61a lc v` is `none`
exactly off these ops and their components (`op61a`). `GoFV/Proof/Gen/G61a.lean` proves what an
accepted value satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The families of G61's group A (module doc). -/
inductive AtomF61 where
  | xchg | xchgV | add | addV | cas | casV | andL | orL | andV | orV
  deriving DecidableEq, Repr

/-- The atomics of G61's group A: their family and bytes. -/
def atom61? : Op → Option (AtomF61 × Nat)
  | .ARM64LoweredAtomicExchange64 => some (.xchg, 8)
  | .ARM64LoweredAtomicExchange32 => some (.xchg, 4)
  | .ARM64LoweredAtomicExchange8 => some (.xchg, 1)
  | .ARM64LoweredAtomicExchange64Variant => some (.xchgV, 8)
  | .ARM64LoweredAtomicExchange32Variant => some (.xchgV, 4)
  | .ARM64LoweredAtomicExchange8Variant => some (.xchgV, 1)
  | .ARM64LoweredAtomicAdd64 => some (.add, 8)
  | .ARM64LoweredAtomicAdd32 => some (.add, 4)
  | .ARM64LoweredAtomicAdd64Variant => some (.addV, 8)
  | .ARM64LoweredAtomicAdd32Variant => some (.addV, 4)
  | .ARM64LoweredAtomicCas64 => some (.cas, 8)
  | .ARM64LoweredAtomicCas32 => some (.cas, 4)
  | .ARM64LoweredAtomicCas64Variant => some (.casV, 8)
  | .ARM64LoweredAtomicCas32Variant => some (.casV, 4)
  | .ARM64LoweredAtomicAnd64 => some (.andL, 8)
  | .ARM64LoweredAtomicAnd32 => some (.andL, 4)
  | .ARM64LoweredAtomicAnd8 => some (.andL, 1)
  | .ARM64LoweredAtomicOr64 => some (.orL, 8)
  | .ARM64LoweredAtomicOr32 => some (.orL, 4)
  | .ARM64LoweredAtomicOr8 => some (.orL, 1)
  | .ARM64LoweredAtomicAnd64Variant => some (.andV, 8)
  | .ARM64LoweredAtomicAnd32Variant => some (.andV, 4)
  | .ARM64LoweredAtomicAnd8Variant => some (.andV, 1)
  | .ARM64LoweredAtomicOr64Variant => some (.orV, 8)
  | .ARM64LoweredAtomicOr32Variant => some (.orV, 4)
  | .ARM64LoweredAtomicOr8Variant => some (.orV, 1)
  | _ => none

/-- The load-exclusive and store-exclusive of `n` bytes. -/
def llsc61 (n : Nat) : As × As :=
  if n == 8 then (.LDAXR, .STLXR) else if n == 4 then (.LDAXRW, .STLXRW) else (.LDAXRB, .STLXRB)

/-- The LSE opcode of a `*Variant` family at `n` bytes (`casV`: `CASAL`). -/
def lse61 (f : AtomF61) (n : Nat) : As :=
  match f with
  | .xchgV => if n == 8 then .SWPALD else if n == 4 then .SWPALW else .SWPALB
  | .addV => if n == 8 then .LDADDALD else .LDADDALW
  | .casV => if n == 8 then .CASALD else .CASALW
  | .andV => if n == 8 then .LDCLRALD else if n == 4 then .LDCLRALW else .LDCLRALB
  | _ => if n == 8 then .LDORALD else if n == 4 then .LDORALW else .LDORALB

/-- `REGTMP`, the obj register `R27`. -/
def r27A : Int := ARM64.REGTMP

/-- `p` has shape `sh` with second destination `t` (no condition suffix or rest). -/
def Shape.okT (sh : Shape) (t : Int) (p : Prog) : Bool :=
  p.as == sh.as && p.from_ == sh.from_ && p.reg == sh.reg && p.to == sh.to && p.scond == 0 &&
    p.rest.isEmpty && p.regTo2 == t

/-- `LDAXR* (Rp), Rd`. -/
def ldaxPat (n : Nat) (rp rd : Int) : Pat :=
  .ofShape { as := (llsc61 n).1, from_ := memA rp 0, to := regA rd }

/-- `STLXR* Rs, (Rp), R27`. -/
def stlxPat (n : Nat) (rs rp : Int) : Pat :=
  ⟨Shape.okT { as := (llsc61 n).2, from_ := regA rs, to := memA rp 0 } r27A, (llsc61 n).2.name⟩

/-- An LSE instruction `op Rs, (Rp), Rt`. -/
def lsePat (as : As) (rs rp rt : Int) : Pat :=
  ⟨Shape.okT { as, from_ := regA rs, to := memA rp 0 } rt, as.name⟩

/-- `BNE <any target>` (`atomOK` fixes the target). -/
def bnePat : Pat :=
  ⟨fun p => p.as == .BNE && p.from_ == {} && p.reg == 0 &&
    (match p.to.val with | .target t => p.to == brA t | _ => false) && p.scond == 0 &&
    p.rest.isEmpty && p.regTo2 == 0, "BNE"⟩

/-- `CMP`/`CMPW Ro, R27`. -/
def cmp61Pat (n : Nat) (ro : Int) : Pat :=
  .ofShape { as := if n == 8 then .CMP else .CMPW, from_ := regA ro, reg := r27A }

/-- `CSET EQ, Rd`. -/
def csetEqPat (rd : Int) : Pat :=
  .ofShape { as := .CSET, from_ := specA ARM64.SPOP_EQ, to := regA rd }

/-- The Progs of a value of group A of family `f` and `n` bytes, from its pointer `rp`, operands
`rv` (the compared value of a compare-and-swap) and `rn` (its new value), result `rd` and
temporary `rt` (module doc). -/
def atomPats61 (f : AtomF61) (n : Nat) (rp rv rn rd rt : Int) : List Pat :=
  match f with
  | .xchg => [ldaxPat n rp rd, stlxPat n rv rp, cbnzPat r27A]
  | .add => [ldaxPat n rp rd, .ofShape { as := .ADD, from_ := regA rv, to := regA rd },
      stlxPat n rd rp, cbnzPat r27A]
  | .cas => [ldaxPat n rp r27A, cmp61Pat n rv, bnePat, stlxPat n rn rp, cbnzPat r27A,
      csetEqPat rd]
  | .casV => [.ofShape { as := if n == 8 then .MOVD else .MOVW, from_ := regA rv, to := regA r27A },
      lsePat (lse61 .casV n) r27A rp rn, cmp61Pat n rv, csetEqPat rd]
  | .andL => [ldaxPat n rp rd, .ofShape { as := .AND, from_ := regA rv, reg := rd, to := regA rt },
      stlxPat n rt rp, cbnzPat r27A]
  | .orL => [ldaxPat n rp rd, .ofShape { as := .ORR, from_ := regA rv, reg := rd, to := regA rt },
      stlxPat n rt rp, cbnzPat r27A]
  | .addV => [lsePat (lse61 .addV n) rv rp rd, .ofShape { as := .ADD, from_ := regA rv, to := regA rd }]
  | .andV => [.ofShape { as := .MVN, from_ := regA rv, to := regA r27A },
      lsePat (lse61 .andV n) r27A rp rd]
  | f => [lsePat (lse61 f n) rv rp rd]

/-- The shape of a value of group A of `n` bytes: a component of class `8n` (`1` for a
compare-and-swap), then the memory. -/
def atomTy61 (cas : Bool) (n : Nat) (t : Ty) : Bool :=
  match t with
  | .tuple [t0, .mem] => cls t0 == some (if cas then 1 else 8 * n)
  | _ => false

/-- An operand of a value of group A: in a register of class `c`, not `R27`. -/
def atomArg61 (lc : LocCtx) (v : Value) (i c : Nat) : Except String Int := do
  let (ca, r) ← argObj lc v i
  unless ca == c && r != r27A do throw s!"v{v.id}: atomic operand {i}"
  return r

/-- The register of the `(Rd, -)` home of a value of group A: one G1 may write, not `ZERO`. -/
def atomHome61 (lc : LocCtx) (v : Value) : Except String Int := do
  let some r := ldarHome? lc v.id | throw s!"v{v.id}: atomic home"
  unless r != zeroReg && destOK r do throw s!"v{v.id}: atomic register"
  let some rd := objOf? r | throw s!"v{v.id}: register {r}"
  return rd

/-- A read-modify-write of group A (every family but `cas`, `casV`) of `n` bytes, `p x mem`
(module doc): what it emits. -/
def rmwKind61 (lc : LocCtx) (v : Value) (f : AtomF61) (n : Nat) : Except String VKind2 := do
  unless v.args.size == 3 && v.aux == none && atomTy61 false n (lc.ty v.id) do
    throw s!"v{v.id}: atomic shape"
  let rp ← atomArg61 lc v 0 64
  unless rp != ARM64.REGZERO do throw s!"v{v.id}: atomic pointer"
  let rv ← atomArg61 lc v 1 (8 * n)
  memArg lc v 2
  let rd ← atomHome61 lc v
  unless rd != rp && rd != rv do throw s!"v{v.id}: atomic result register"
  match (lc.temps[v.id]?).join with
  | none =>
    if f == .andL || f == .orL then throw s!"v{v.id}: atomic without temporary"
    return .progs (atomPats61 f n rp rv rv rd 0)
  | some t =>
    unless f == .andL || f == .orL do throw s!"v{v.id}: temporary register"
    let some rt := objOf? t | throw s!"v{v.id}: temporary in register {t}"
    unless t != zeroReg && destOK t && rt != rp && rt != rd do throw s!"v{v.id}: atomic temporary"
    return .progs (atomPats61 f n rp rv rv rd rt)

/-- A compare-and-swap of group A (`cas`, `casV`) of `n` bytes, `p old new mem` (module doc):
what it emits. -/
def casKind61 (lc : LocCtx) (v : Value) (f : AtomF61) (n : Nat) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 4 && v.aux == none && atomTy61 true n (lc.ty v.id) do
    throw s!"v{v.id}: atomic shape"
  let rp ← atomArg61 lc v 0 64
  unless rp != ARM64.REGZERO do throw s!"v{v.id}: atomic pointer"
  let ro ← atomArg61 lc v 1 (8 * n)
  let rn ← atomArg61 lc v 2 (8 * n)
  memArg lc v 3
  let rd ← atomHome61 lc v
  return .progs (atomPats61 f n rp ro rn rd 0)

/-- A value of group A of family `f` and `n` bytes (module doc): what it emits. -/
def atomKind61 (lc : LocCtx) (v : Value) (f : AtomF61) (n : Nat) : Except String VKind2 :=
  if f == .cas || f == .casV then casKind61 lc v f n else rmwKind61 lc v f n

/-- `Select0`/`Select1` of a value of group A. -/
def selAtom61 (lc : LocCtx) (v : Value) : Bool :=
  (v.op == .Select0 || v.op == .Select1) &&
    ((v.args[0]?).bind lc.ctx.f.value?).any fun u => (atom61? u.op).isSome

/-- The ops of G61's group A, and their components. -/
def op61a (op : Op) : Bool := (atom61? op).isSome || op == .Select0 || op == .Select1

/-- What `v` emits if it is one of G61's group A or one of their components, else `none`. -/
def vkind61a (lc : LocCtx) (v : Value) : Option (Except String VKind2) :=
  match atom61? v.op with
  | some (f, n) => some (atomKind61 lc v f n)
  | none => if selAtom61 lc v then some (selLdarKind lc v) else none

/-! ## The loops' and the compare-and-swap's branches -/

/-- The index after the `k`-th Prog at or after `j` that is not a no-op (`nextIdx` `k` times). -/
def nexts (ps : Array Prog) (j : Nat) : Nat → Nat
  | 0 => j
  | k + 1 => nextIdx ps (nexts ps j k)

/-- From index `j`, the `a`-th Prog after no-ops branches to the `b`-th. -/
def brTo (ps : Array Prog) (j a b : Nat) : Bool :=
  match ps[nexts ps j a - 1]?, ps[nexts ps j b - 1]? with
  | some x, some y => x.to == brA y.id
  | _, _ => false

/-- The branches of a value of family `f` whose Progs start at index `j`: each loop's `CBNZ R27`
branches to its `LDAXR` (the first Prog), and a `cas`'s `BNE` (the third) to its `CSET` (the
sixth). -/
def atomTgt (f : AtomF61) (ps : Array Prog) (j : Nat) : Bool :=
  match f with
  | .xchg => brTo ps j 3 1
  | .add | .andL | .orL => brTo ps j 4 1
  | .cas => brTo ps j 3 6 && brTo ps j 5 1
  | _ => true

/-- Every value of group A has its branches (`atomTgt`), at its value's start in the PC table. -/
def atomOK (lc : LocCtx) (ps : Array Prog) (tab : PcTab) : Bool :=
  tab.all fun (bid, row) =>
    match lc.ctx.f.block? bid with
    | none => true
    | some b => (List.range b.values.size).all fun i =>
      match (b.values[i]?).bind lc.ctx.f.value? with
      | some v => match atom61? v.op with
        | some (f, _) => atomTgt f ps (row.getD i 0)
        | none => true
      | none => true

end GoFV.Gen.Check

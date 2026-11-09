import GoFV.Gen.Check45

/-!
# The genssa validator, slice G46: float arithmetic, conversions and compares
(`docs/plans/proofs3.md` §4, float stage (b))

G46 adds to G45 the float values that compute, each one Prog of `ssaGenValue`
(`GoFV/Gen/Arm64Value.lean`) with the opcode `opAsm op`, on registers of the classes the op says
(`S` 32 bits, `D` 64):

* `FADD`/`FSUB`/`FMUL`/`FDIV` (`fp2Of`): `op Fm, Fn, Fd` with `Fn` the first argument, `Fm` the
  second (the `binary` case);
* `FNEG`/`FABS`/`FSQRT`, `FCVTSD`, `FCVTDS` (`fp1Of`): `op Fa, Fd` (`unary`);
* `SCVTF`/`UCVTF` (`cvtfOf`): `op Rn, Fd` of an integer register of at least the input's width;
* `FCVTZS`/`FCVTZU` (`fcvtzOf`): `op Fn, Rd` into an integer register of the output's width;
* `FCMPS`/`FCMPD` (`FCMP Fm, Fn`, `Fn` the first argument) and `FCMPS0`/`FCMPD0`
  (`FCMP $(0.0), Fn`) (`fcmpOf`), of a flags value with no home;
* `FMADD`/`FNMSUB` (`fp3Of` with no multiplicand negated): `op Fm, Fa, Fn, Fd` with `Fa` the
  addend (argument 0), `Fm` argument 1 and `Fn` (the rest operand) argument 2 (`ternary`).
  `FMSUB`/`FNMADD` are not in G46: Phase 1 negates the other multiplicand than the machine, and the
  results differ in a NaN's sign (`GoFV/Proof/Gen/FArith.lean`).

The fused ops appear in the lowered function only where `lower` contracted a multiply and an add
(Phase 2's `Contract`, the 12 `useFMA` shapes, semantics2 §2.1); G46 relates the machine's fused
instruction to Phase 1's fused op, and the contraction itself is `lower`'s.

The flags of a float compare are read as an integer compare's: by G23's `CSET` and, since this
slice, by the `FLT`/`FLE`/`FGT`/`FGE` blocks of `condBr` (`GoFV/Gen/Check.lean`).

`checkG46 lc ps bstart g` is slice G45 (`GoFV/Gen/Check45.lean`) with these values (`fkind46`,
tried when G45 rejects a value). `GoFV/Proof/Gen/G46.lean` proves what an accepted function
satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-! ## Opcode tables

`if` chains, not `match`es on `Op` (a `match` with a wildcard over `Op`'s constructors makes
`split` generate a splitter with an equation per constructor). Each gives the operands of
`GoFV.Arm64`'s `fp2Op`/`fp1Op`/`fp3Op`/`fcmpOp` (`Exec.lean`). -/

/-- The binary float ops: bytes `n`, `ftype` and `opc` of `fp2Op`. -/
def fp2Of (op : Op) : Option (Nat × BitVec 2 × BitVec 4) :=
  if op = .ARM64FADDD then some (8, 1, 2) else if op = .ARM64FADDS then some (4, 0, 2)
  else if op = .ARM64FSUBD then some (8, 1, 3) else if op = .ARM64FSUBS then some (4, 0, 3)
  else if op = .ARM64FMULD then some (8, 1, 0) else if op = .ARM64FMULS then some (4, 0, 0)
  else if op = .ARM64FDIVD then some (8, 1, 1) else if op = .ARM64FDIVS then some (4, 0, 1)
  else none

/-- The unary float ops (`FNEG`, `FABS`, `FSQRT`, `FCVT`): source bytes `ns`, destination bytes
`nd`, `ftype` and `opc` of `fp1Op`. -/
def fp1Of (op : Op) : Option (Nat × Nat × BitVec 2 × BitVec 6) :=
  if op = .ARM64FNEGD then some (8, 8, 1, 2) else if op = .ARM64FNEGS then some (4, 4, 0, 2)
  else if op = .ARM64FABSD then some (8, 8, 1, 1) else if op = .ARM64FABSS then some (4, 4, 0, 1)
  else if op = .ARM64FSQRTD then some (8, 8, 1, 3)
  else if op = .ARM64FSQRTS then some (4, 4, 0, 3)
  else if op = .ARM64FCVTSD then some (4, 8, 0, 5)
  else if op = .ARM64FCVTDS then some (8, 4, 1, 4)
  else none

/-- `SCVTF`/`UCVTF`: unsigned, integer source bytes `ns`, float destination bytes `nd`. -/
def cvtfOf (op : Op) : Option (Bool × Nat × Nat) :=
  if op = .ARM64SCVTFWS then some (false, 4, 4)
  else if op = .ARM64SCVTFWD then some (false, 4, 8)
  else if op = .ARM64UCVTFWS then some (true, 4, 4)
  else if op = .ARM64UCVTFWD then some (true, 4, 8)
  else if op = .ARM64SCVTFS then some (false, 8, 4)
  else if op = .ARM64SCVTFD then some (false, 8, 8)
  else if op = .ARM64UCVTFS then some (true, 8, 4)
  else if op = .ARM64UCVTFD then some (true, 8, 8)
  else none

/-- `FCVTZS`/`FCVTZU`: unsigned, float source bytes `ns`, integer destination bytes `nd`. -/
def fcvtzOf (op : Op) : Option (Bool × Nat × Nat) :=
  if op = .ARM64FCVTZSSW then some (false, 4, 4)
  else if op = .ARM64FCVTZSDW then some (false, 8, 4)
  else if op = .ARM64FCVTZUSW then some (true, 4, 4)
  else if op = .ARM64FCVTZUDW then some (true, 8, 4)
  else if op = .ARM64FCVTZSS then some (false, 4, 8)
  else if op = .ARM64FCVTZSD then some (false, 8, 8)
  else if op = .ARM64FCVTZUS then some (true, 4, 8)
  else if op = .ARM64FCVTZUD then some (true, 8, 8)
  else none

/-- `FCMP`: bytes `n`, `ftype`, and whether it compares with `#0.0` (`FCMPS0`/`FCMPD0`). -/
def fcmpOf (op : Op) : Option (Nat × BitVec 2 × Bool) :=
  if op = .ARM64FCMPS then some (4, 0, false) else if op = .ARM64FCMPD then some (8, 1, false)
  else if op = .ARM64FCMPS0 then some (4, 0, true) else if op = .ARM64FCMPD0 then some (8, 1, true)
  else none

/-- The fused multiply-adds: bytes `n`, `ftype` and `(o1, o0)` of `fp3Op`. -/
def fp3Of (op : Op) : Option (Nat × BitVec 2 × Bool × Bool) :=
  if op = .ARM64FMADDD then some (8, 1, false, false)
  else if op = .ARM64FMADDS then some (4, 0, false, false)
  else if op = .ARM64FMSUBD then some (8, 1, false, true)
  else if op = .ARM64FMSUBS then some (4, 0, false, true)
  else if op = .ARM64FNMADDD then some (8, 1, true, false)
  else if op = .ARM64FNMADDS then some (4, 0, true, false)
  else if op = .ARM64FNMSUBD then some (8, 1, true, true)
  else if op = .ARM64FNMSUBS then some (4, 0, true, true)
  else none

/-- The `FCONST` operand `$(0.0)` of a compare with zero. -/
def fzeroA : Addr := { type := .FCONST, val := .float 0 }

/-! ## The values -/

/-- A two-operand float op of `n` bytes: `op Fm, Fn, Fd`. -/
def fbin46 (lc : LocCtx) (v : Value) (n : Nat) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 2 do throw s!"v{v.id}: float op shape"
  let (ca, rn) ← fargObj lc v 0
  let (cb, rm) ← fargObj lc v 1
  let (cd, rd) ← fresObj lc v
  unless ca == 8 * n && cb == 8 * n && cd == 8 * n do throw s!"v{v.id}: float op widths"
  return .prog (.ofShape { as := opAsm v.op, from_ := regA rm, reg := rn, to := regA rd })

/-- A one-operand float op from `ns` to `nd` bytes: `op Fa, Fd`. -/
def fun46 (lc : LocCtx) (v : Value) (ns nd : Nat) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 1 do throw s!"v{v.id}: float op shape"
  let (ca, ra) ← fargObj lc v 0
  let (cd, rd) ← fresObj lc v
  unless ca == 8 * ns && cd == 8 * nd do throw s!"v{v.id}: float op widths"
  return .prog (.ofShape { as := opAsm v.op, from_ := regA ra, to := regA rd })

/-- An integer-to-float conversion from `ns` to `nd` bytes: `op Rn, Fd`. -/
def cvtf46 (lc : LocCtx) (v : Value) (ns nd : Nat) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 1 do throw s!"v{v.id}: conversion shape"
  let (ca, rn) ← argObj lc v 0
  let (cd, rd) ← fresObj lc v
  unless 8 * ns ≤ ca && cd == 8 * nd do throw s!"v{v.id}: conversion widths"
  return .prog (.ofShape { as := opAsm v.op, from_ := regA rn, to := regA rd })

/-- A float-to-integer conversion from `ns` to `nd` bytes: `op Fn, Rd`. -/
def fcvtz46 (lc : LocCtx) (v : Value) (ns nd : Nat) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 1 do throw s!"v{v.id}: conversion shape"
  let (ca, rn) ← fargObj lc v 0
  let (cd, rd) ← resObj lc v
  unless ca == 8 * ns && cd == 8 * nd do throw s!"v{v.id}: conversion widths"
  return .prog (.ofShape { as := opAsm v.op, from_ := regA rn, to := regA rd })

/-- A float compare of `n` bytes: `FCMP Fm, Fn` or `FCMP $(0.0), Fn`. -/
def fcmp46 (lc : LocCtx) (v : Value) (n : Nat) (zero : Bool) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless (lc.ty v.id).isFlags && lc.home v.id == none do throw s!"v{v.id}: compare shape"
  if zero then
    unless v.args.size == 1 do throw s!"v{v.id}: compare shape"
    let (ca, rn) ← fargObj lc v 0
    unless ca == 8 * n do throw s!"v{v.id}: compare widths"
    return .prog (.ofShape { as := opAsm v.op, from_ := fzeroA, reg := rn })
  else
    unless v.args.size == 2 do throw s!"v{v.id}: compare shape"
    let (ca, rn) ← fargObj lc v 0
    let (cb, rm) ← fargObj lc v 1
    unless ca == 8 * n && cb == 8 * n do throw s!"v{v.id}: compare widths"
    return .prog (.ofShape { as := opAsm v.op, from_ := regA rm, reg := rn })

/-- The pattern of a fused multiply-add `op Fm, Fa, Fn, Fd` (`Fn` the rest operand). -/
def fmaPat (op : Op) (ra rm rn rd : Int) : Pat :=
  ⟨fun p => p.as == opAsm op && p.from_ == regA rm && p.reg == ra && p.to == regA rd &&
    p.scond == 0 && p.rest == #[(0, regA rn)] && p.regTo2 == 0, (opAsm op).name⟩

/-- A fused multiply-add of `n` bytes with no multiplicand negated: `fmaPat`. -/
def fma46 (lc : LocCtx) (v : Value) (n : Nat) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 3 do throw s!"v{v.id}: fused op shape"
  let (ca, ra) ← fargObj lc v 0
  let (cm, rm) ← fargObj lc v 1
  let (cn, rn) ← fargObj lc v 2
  let (cd, rd) ← fresObj lc v
  unless ca == 8 * n && cm == 8 * n && cn == 8 * n && cd == 8 * n do
    throw s!"v{v.id}: fused op widths"
  return .prog (fmaPat v.op ra rm rn rd)

/-- What a G46 value emits (module doc), or why it is outside the slice; `e` is G45's reason, kept
for the other ops. -/
def fkind46 (lc : LocCtx) (v : Value) (e : String) : Except String VKind2 :=
  match fp2Of v.op with
  | some (n, _, _) => fbin46 lc v n
  | none => match fp1Of v.op with
    | some (ns, nd, _, _) => fun46 lc v ns nd
    | none => match cvtfOf v.op with
      | some (_, ns, nd) => cvtf46 lc v ns nd
      | none => match fcvtzOf v.op with
        | some (_, ns, nd) => fcvtz46 lc v ns nd
        | none => match fcmpOf v.op with
          | some (n, _, zero) => fcmp46 lc v n zero
          | none => match fp3Of v.op with
            | some (n, _, o1, o0) =>
              if o1 = o0 then fma46 lc v n
              else .error s!"v{v.id}: op {v.op.name}: negated multiplicand"
            | none => .error e

/-- What `v` emits in G46, or why it is outside the slice: G45's kinds, then G46's float
arithmetic, conversions and compares. -/
def vkind46 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  match vkind45 lc g v with
  | .ok kd => .ok kd
  | .error e => fkind46 lc v e

/-- G45's check with G46's value check. -/
def checkG46L (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind46 lc g, tm := cx.termG3 }
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

/-- Slice G46 of the genssa validator (module doc): `refsLive`, then G46's check on `liveCtx lc`. -/
def checkG46 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless refsLive lc do throw "a value refers to an ID that is no value of the function"
  checkG46L (liveCtx lc) ps bstart g

end GoFV.Gen.Check

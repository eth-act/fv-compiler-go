import GoFV.SSA.Sem.LocMatch
import GoFV.SSA.Sem.RunProg

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G1 (`docs/plans/proofs3.md` §3)

`checkG1 lc ps bstart` checks the P0 Prog list `ps` (genssa's output in list order, `bstart` the
Prog ID at which each block starts) against the allocated function of `lc` (`runLoc`'s context:
the function after `trim`, its homes and shapes) for the ops of slice G1, and returns the PC
table of `LocMatch`: for each block, the index in `ps` of the first Prog of each value and of
its terminator. It accepts a function when

* the function is lowered (`runLoc` reads values as registers); no value lives in a stack slot
  or a register pair, only `MakeResult` has a `results` home, and no op needs a temporary
  register;
* every register other than `ZERO` holds values of one **width class** (`cls`: an integer's
  width, 64 for a pointer, 1 for a boolean), so whatever a register holds is read at a shape of
  its own class;
* the entry block starts with the values that emit nothing and set up the activation
  (`entryOp`: `InitMem`, `SP`, `SB`, `ArgIntReg`, `ArgFloatReg`), and no other value is one;
* every other value is a `Phi` whose arguments share its home, `ZERO` in `ZERO` at a register
  shape, `InlMark` (one `HINT` or `NOP`, or nothing; no home and a shape `LocState.write` drops,
  `inertTy`), `MakeResult` with its results in their result registers and a shape whose write
  changes nothing (`resultsTy`), a
  `Copy` (of memory, a register copy that emits nothing, or `MOVD Rs, Rd`), or `MOVDconst`
  (`MOVD $k, Rd`), `ADD`, `SUB` (`OP Rm, Rn, Rd`), `ADDconst`, `SUBconst` (`OP $k, Rn, Rd`),
  `CMP` (`CMP Rm, Rn`), `CMPconst` (`CMP $k, Rn`), `MOVDload` (`MOVD off(Rn), Rd`) or
  `MOVDstore` (`MOVD Rs, off(Rn)`) without a symbol (`vkind`), each emitting that Prog after
  any pseudo-ops (`Prog.isSkip`); the arguments of the arithmetic are at least as wide as the
  result, compares and addresses read 64-bit registers, a stored value is 64-bit or boolean;
* every block is `Plain` (only no-ops when it falls through to its successor, else `JMP`), `Ret`
  (`RET`), a two-way flags branch (`EQ`, `NE`, `LT`, `LE`, `GT`, `GE`, `ULT`, `ULE`, `UGT`,
  `UGE`) or a register test (`Z`, `NZ`: `CBZ`, `CBNZ` on a 64-bit or boolean register) emitted as
  `ssaGenBlock` does: a conditional branch (the condition or its inverse) and the fall-through
  to the next block's start (over no-ops only, `Cx.falls`), or a conditional branch and a `JMP`;
  every successor is laid out;
* destination registers are neither `g` (`R28`), `R29` nor `R30`; Prog IDs are distinct and
  below `2^32`.

`GoFV/Proof/Gen/G1.lean` proves what an accepted function satisfies (`g1_value`, `g1_term`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-! ## Operands -/

/-- The integer obj register of Go register `r`: `ZERO` is `REGZERO`, a register with an X
register `k` (`objX?`) is `REG_R0 + k`. -/
def objOf? (r : Nat) : Option Int :=
  if r = zeroReg then some ARM64.REGZERO else (objX? r).map fun k => ARM64.REG_R0 + k.toNat

/-- A register G1 may write: `ZERO` or one of `R0`–`R17`, `R19`–`R26` (Go 0–25); not `g`, `R29`
or `R30`, which `LocMatch`'s frame clause pins down. -/
def destOK (r : Nat) : Bool := r == zeroReg || r < 26

def regA (r : Int) : Addr := { type := .REG, reg := r }
def constA (k : Int) : Addr := { type := .CONST, offset := k }
def memA (r : Int) (off : Int) : Addr := { type := .MEM, reg := r, offset := off }
def brA (t : Nat) : Addr := { type := .BRANCH, val := .target t }

/-- The operands of a Prog that G1 fixes. -/
structure Shape where
  as : As
  from_ : Addr := {}
  reg : Int := 0
  to : Addr := {}
  deriving DecidableEq, Inhabited

/-- `p` has shape `sh`: its opcode and operands, no condition suffix, rest or second destination. -/
def Shape.ok (sh : Shape) (p : Prog) : Bool :=
  p.as == sh.as && p.from_ == sh.from_ && p.reg == sh.reg && p.to == sh.to && p.scond == 0 &&
    p.rest.isEmpty && p.regTo2 == 0

/-! ## Shapes -/

/-- The width class of a register shape: an integer's width, 64 for a pointer, 1 for a boolean. -/
def cls : Ty → Option Nat
  | .int w => some w.bits
  | .ptr _ => some 64
  | .bool => some 1
  | _ => none

/-- The memory shape. -/
def memTy : Ty → Bool
  | .mem => true
  | _ => false

/-- A shape whose result `LocState.write` drops when the value has no home: not memory, not a
tuple, not the flags. -/
def inertTy : Ty → Bool
  | .mem | .tuple _ => false
  | t => !t.isFlags

/-- The shape of a `MakeResult` with arguments `args` whose write changes nothing: a tuple of
one component per argument, no flags component, and a memory component only where the argument
is the memory. -/
def resultsTy (lc : LocCtx) (args : Array ID) : Ty → Bool
  | .tuple ts => ts.length == args.size &&
    (ts.zip args.toList).all fun (t, a) => !t.isFlags && (!memTy t || memTy (lc.ty a))
  | _ => false

/-- The register home of `id`. -/
def regHome? (lc : LocCtx) (id : ID) : Option Nat :=
  match lc.home id with
  | some (.reg r) => some r
  | _ => none

/-- The width class of register `r`: that of the first value homed there. -/
def regCls (lc : LocCtx) (r : Nat) : Option Nat :=
  (List.range lc.homes.size).findSome? fun i =>
    if lc.home i == some (.reg r) then cls (lc.ty i) else none

/-- The home of value `i` is one G1 handles: `ZERO`, a register whose values all have one
class (`regCls`), no home, or an empty `results` home of a `MakeResult`. -/
def homeOK (lc : LocCtx) (i : Nat) : Bool :=
  match lc.home i with
  | some (.reg r) => r == zeroReg || ((cls (lc.ty i)).isSome && cls (lc.ty i) == regCls lc r)
  | some (.results rs) => rs.isEmpty && (lc.ctx.f.value? i).map (·.op) == some .MakeResult
  | some (.slot _) | some (.pair _ _) => false
  | none => true

/-- Why the home of value `i` is not one G1 handles. -/
def homeErr (lc : LocCtx) (i : Nat) : String :=
  match lc.home i with
  | some (.reg r) => match cls (lc.ty i) with
    | some c => s!"v{i}: register {r} holds classes {(regCls lc r).getD 0} and {c}"
    | none => s!"v{i}: register value of shape {repr (lc.ty i)}"
  | some (.results _) => s!"v{i}: results home"
  | some (.slot _) => s!"v{i}: stack slot"
  | some (.pair _ _) => s!"v{i}: register pair"
  | none => s!"v{i}"

/-! ## Values -/

/-- What a value emits in G1. -/
inductive VKind where
  /-- An activation value at the head of the entry block (no code). -/
  | entry
  /-- No code (no-op Progs may precede the next value's). -/
  | none
  /-- One Prog of this shape (after any no-op Progs). -/
  | prog (sh : Shape)
  deriving DecidableEq, Inhabited

/-- The ops that set up the activation. -/
def entryOp : Op → Bool
  | .InitMem | .SP | .SB | .ArgIntReg | .ArgFloatReg => true
  | _ => false

/-- The class of argument `i` of `v` and the obj register holding it (an X register or `ZERO`). -/
def argObj (lc : LocCtx) (v : Value) (i : Nat) : Except String (Nat × Int) := do
  let some a := v.args[i]? | throw s!"v{v.id}: no argument {i}"
  let some r := regHome? lc a | throw s!"v{v.id}: argument v{a} has no register"
  let some o := objOf? r | throw s!"v{v.id}: argument v{a} in register {r}"
  let some c := cls (lc.ty a) | throw s!"v{v.id}: argument v{a} shape"
  return (c, o)

/-- The obj register `v` writes (a register home G1 may write) and the class of `v`. -/
def resObj (lc : LocCtx) (v : Value) : Except String (Nat × Int) := do
  let some r := regHome? lc v.id | throw s!"v{v.id}: no register"
  unless destOK r do throw s!"v{v.id}: writes register {r}"
  let some o := objOf? r | throw s!"v{v.id}: register {r}"
  let some c := cls (lc.ty v.id) | throw s!"v{v.id}: result shape"
  return (c, o)

/-- The memory argument `i` of `v`: its shape is `mem` (so it has no home and reads the current
memory). -/
def memArg (lc : LocCtx) (v : Value) (i : Nat) : Except String Unit := do
  let some a := v.args[i]? | throw s!"v{v.id}: no argument {i}"
  unless memTy (lc.ty a) && lc.home a == none do throw s!"v{v.id}: argument {i} is not memory"

/-- What `v` emits in G1, or why it is outside the slice. -/
def vkind (lc : LocCtx) (v : Value) : Except String VKind := do
  let ty := lc.ty v.id
  if (lc.temps[v.id]?).join != none then throw s!"v{v.id}: temporary register"
  if entryOp v.op then return .entry
  match v.op with
  | .Phi =>
    unless v.args.all (lc.home · == lc.home v.id) do throw s!"v{v.id}: phi argument elsewhere"
    return .none
  | .ARM64ZERO =>
    unless v.args.size == 0 && regHome? lc v.id == some zeroReg && (cls ty).isSome do
      throw s!"v{v.id}: ZERO home"
    return .none
  | .InlMark =>
    unless lc.home v.id == none && inertTy ty do throw s!"v{v.id}: inline mark home"
    return .none
  | .Copy =>
    if memTy ty then
      memArg lc v 0
      unless v.args.size == 1 && lc.home v.id == none do throw s!"v{v.id}: memory copy"
      return .none
    unless v.args.size == 1 do throw s!"v{v.id}: copy shape"
    let (ca, ra) ← argObj lc v 0
    let (cd, rd) ← resObj lc v
    unless ca == cd do throw s!"v{v.id}: copy across classes"
    if ra == rd then return .none
    return .prog { as := .MOVD, from_ := regA ra, to := regA rd }
  | .MakeResult =>
    -- regalloc gives `MakeResult` an empty `results` home: the value writes only the memory,
    -- and its non-memory arguments already sit in their (result) registers
    unless lc.home v.id == none || lc.home v.id == some (.results #[]) do
      throw s!"v{v.id}: result home"
    unless resultsTy lc v.args ty do throw s!"v{v.id}: result shape"
    for a in v.args do
      if memTy (lc.ty a) then
        unless lc.home a == none do throw s!"v{v.id}: memory result"
      else
        unless (regHome? lc a).isSome && (cls (lc.ty a)).isSome do
          throw s!"v{v.id}: result v{a} has no register"
    return .none
  | .ARM64MOVDconst =>
    unless v.args.size == 0 do throw s!"v{v.id}: const shape"
    let (c, rd) ← resObj lc v
    if c == 1 && !(v.auxInt == 0 || v.auxInt == 1) then throw s!"v{v.id}: boolean constant"
    return .prog { as := .MOVD, from_ := constA v.auxInt.toInt, to := regA rd }
  | .ARM64ADD | .ARM64SUB =>
    unless v.args.size == 2 do throw s!"v{v.id}: shape"
    let (ca, rn) ← argObj lc v 0
    let (cb, rm) ← argObj lc v 1
    let (c, rd) ← resObj lc v
    unless 8 ≤ c && c ≤ ca && c ≤ cb do throw s!"v{v.id}: arithmetic widths"
    let as := if v.op == .ARM64ADD then As.ADD else As.SUB
    return .prog { as, from_ := regA rm, reg := rn, to := regA rd }
  | .ARM64ADDconst | .ARM64SUBconst =>
    unless v.args.size == 1 do throw s!"v{v.id}: shape"
    let (ca, rn) ← argObj lc v 0
    let (c, rd) ← resObj lc v
    unless 8 ≤ c && c ≤ ca do throw s!"v{v.id}: arithmetic widths"
    let as := if v.op == .ARM64ADDconst then As.ADD else As.SUB
    return .prog { as, from_ := constA v.auxInt.toInt, reg := rn, to := regA rd }
  | .ARM64CMP =>
    unless v.args.size == 2 && ty.isFlags && lc.home v.id == none do
      throw s!"v{v.id}: compare shape"
    let (ca, rn) ← argObj lc v 0
    let (cb, rm) ← argObj lc v 1
    unless ca == 64 && cb == 64 do throw s!"v{v.id}: compare widths"
    return .prog { as := .CMP, from_ := regA rm, reg := rn }
  | .ARM64CMPconst =>
    unless v.args.size == 1 && ty.isFlags && lc.home v.id == none do
      throw s!"v{v.id}: compare shape"
    let (ca, rn) ← argObj lc v 0
    unless ca == 64 do throw s!"v{v.id}: compare widths"
    return .prog { as := .CMP, from_ := constA v.auxInt.toInt, reg := rn }
  | .ARM64MOVDload =>
    unless v.args.size == 2 && v.aux == none do throw s!"v{v.id}: load shape"
    let (ca, rn) ← argObj lc v 0
    memArg lc v 1
    let (c, rd) ← resObj lc v
    unless ca == 64 && 8 ≤ c do throw s!"v{v.id}: load widths"
    return .prog { as := .MOVD, from_ := memA rn v.auxInt.toInt, to := regA rd }
  | .ARM64MOVDstore =>
    unless v.args.size == 3 && v.aux == none && memTy ty && lc.home v.id == none do
      throw s!"v{v.id}: store shape"
    let (ca, rn) ← argObj lc v 0
    let (cs, rs) ← argObj lc v 1
    memArg lc v 2
    unless ca == 64 && (cs == 64 || cs == 1) do throw s!"v{v.id}: store widths"
    return .prog { as := .MOVD, from_ := regA rs, to := memA rn v.auxInt.toInt }
  | op => throw s!"v{v.id}: op {op.name}"

/-! ## Blocks -/

/-- The conditional branch of a flags block kind and of its inverse (`blockJump`, `ssa.go`): the
integer kinds, the float kinds `FLT`/`FLE`/`FGT`/`FGE` (`MI`, `LS`, `GT`, `GE` after `FCMP`) and
`LTnoov`/`GEnoov`. -/
def condBr : BlockKind → Option (As × As)
  | .ARM64EQ => some (.BEQ, .BNE)
  | .ARM64NE => some (.BNE, .BEQ)
  | .ARM64LT => some (.BLT, .BGE)
  | .ARM64GE => some (.BGE, .BLT)
  | .ARM64LE => some (.BLE, .BGT)
  | .ARM64GT => some (.BGT, .BLE)
  | .ARM64ULT => some (.BLO, .BHS)
  | .ARM64UGE => some (.BHS, .BLO)
  | .ARM64ULE => some (.BLS, .BHI)
  | .ARM64UGT => some (.BHI, .BLS)
  | .ARM64FLT => some (.BMI, .BPL)
  | .ARM64FGE => some (.BGE, .BLT)
  | .ARM64FLE => some (.BLS, .BHI)
  | .ARM64FGT => some (.BGT, .BLE)
  | .ARM64LTnoov => some (.BMI, .BPL)
  | .ARM64GEnoov => some (.BPL, .BMI)
  | _ => none

/-- The compare-and-branch of a register test block kind and of its inverse. -/
def zeroBr : BlockKind → Option (As × As)
  | .ARM64Z => some (.CBZ, .CBNZ)
  | .ARM64NZ => some (.CBNZ, .CBZ)
  | _ => none

/-- A Prog that only advances the PC: a pseudo-op (`Prog.isSkip`) or `HINT $0` (`ginsnop`: inline
marks, the instruction before an inlined first instruction of a frameless leaf, empty loops). -/
def noop (p : Prog) : Bool := p.isSkip || ({ as := .HINT, from_ := constA 0 } : Shape).ok p

/-- The index in `ps` of the first Prog at or after `j` that is not a no-op. -/
def skipFrom (ps : Array Prog) (j : Nat) (fuel : Nat) : Nat :=
  match fuel with
  | 0 => j
  | fuel + 1 =>
    match ps[j]? with
    | some p => if noop p then skipFrom ps (j + 1) fuel else j
    | none => j

/-- The context of the check. -/
structure Cx where
  lc : LocCtx
  ps : Array Prog
  /-- The index in `ps` of the Prog with each ID. -/
  idx : Std.HashMap Nat Nat
  /-- The Prog ID each block starts at. -/
  bstart : ID → Option Nat

/-- The index of the Prog where block `b` starts. -/
def Cx.startIdx (cx : Cx) (b : ID) : Except String Nat := do
  let some id := cx.bstart b | throw s!"b{b}: no start"
  let some j := cx.idx[id]? | throw s!"b{b}: start {id} not in the list"
  unless (cx.ps[j]?).map (·.id) == some id do throw s!"b{b}: start {id} misplaced"
  return j

/-- One Prog of shape `sh` after no-ops from `j`: the index after it. -/
def Cx.one (cx : Cx) (j : Nat) (sh : Shape) : Except String Nat := do
  let k := skipFrom cx.ps j cx.ps.size
  let some p := cx.ps[k]? | throw s!"no Prog at {k} for {sh.as.name}"
  unless sh.ok p do throw s!"Prog {p.id}: {p.as.name}, expected {sh.as.name}"
  return k + 1

/-- Whether the Progs from index `k` fall through to block `s`: `s` is laid out next (`next`,
starting at index `n`) and only no-ops lie between, `k ≤ n` and `ps[k:n]` all `noop` (argument
liveness PCDATA, inline-mark NOP/`HINT $0` that no value consumed). Bounded by `n`, so no-ops
leading `s` itself are not skipped past. -/
def Cx.falls (cx : Cx) (next : Option (ID × Nat)) (k : Nat) (s : ID) : Bool :=
  match next with
  | some (s', n) => s == s' && decide (k ≤ n) && skipFrom cx.ps k (n - k) == n
  | none => false

/-- A branch of shape `br` to `t` from index `j`, then the fall-through to `f` (laid out next,
`next`, `Cx.falls`) or a `JMP` to `f` (`Cx.term`'s two-way case). -/
def Cx.two (cx : Cx) (j : Nat) (next : Option (ID × Nat)) (br : Shape) (t f : ID) :
    Except String Unit := do
  let tgt (s : ID) : Except String Addr := do
    let some id := cx.bstart s | throw s!"b{s}: no start"
    return brA id
  let k ← cx.one j { br with to := ← tgt t }
  unless cx.falls next k f do
    let _ ← cx.one k { as := .JMP, to := ← tgt f }

/-- The values of a block from index `j`: the start index of each and the index after them.
`head`: no other value came before in the entry block. -/
def Cx.values (cx : Cx) (entry : Bool) : List ID → Nat → Bool → Except String (List Nat × Nat)
  | [], j, _ => return ([], j)
  | id :: ids, j, head => do
    let some v := cx.lc.ctx.f.value? id | throw s!"v{id} is not in the function"
    let k ← match ← vkind cx.lc v with
      | .entry =>
        unless entry && head do throw s!"v{id}: {v.op.name} after the entry values"
        pure j
      | .none => pure j
      | .prog sh => cx.one j sh
    let head := head && entryOp v.op
    let (js, e) ← cx.values entry ids k head
    return (j :: js, e)

/-- The terminator of `b` from index `j`; `stop`: where the next block starts, if one is laid out
after `b`. A `Defer` block (`ssaGenBlock`'s `BlockPlain, BlockDefer` case) is `Plain`'s jump to
`Succs[0]`: its `deferproc` call returned (Phase 1's `stepTerm`); `Succs[1]` is the recovery edge
the runtime takes, not code. -/
def Cx.term (cx : Cx) (b : Block) (j : Nat) (next : Option (ID × Nat)) : Except String Unit := do
  let tgt (s : ID) : Except String Addr := do
    let some id := cx.bstart s | throw s!"b{s}: no start"
    return brA id
  -- a branch to `t` and either the fall-through or a jump to `f`
  let two (br : Shape) (t f : ID) : Except String Unit := do
    let k ← cx.one j { br with to := ← tgt t }
    unless cx.falls next k f do
      let _ ← cx.one k { as := .JMP, to := ← tgt f }
  unless b.succs.all (cx.lc.ctx.f.blocks.contains ·.b) do throw s!"b{b.id}: successor not laid out"
  match b.kind with
  | .Plain =>
    let some e := b.succs[0]? | throw s!"b{b.id}: no successor"
    unless b.succs.size == 1 && b.controls.isEmpty do throw s!"b{b.id}: plain shape"
    unless cx.falls next j e.b do
      let _ ← cx.one j { as := .JMP, to := ← tgt e.b }
  | .Defer =>
    let some e := b.succs[0]? | throw s!"b{b.id}: no successor"
    unless b.succs.size == 2 && b.controls.size == 1 do throw s!"b{b.id}: defer shape"
    unless cx.falls next j e.b do
      let _ ← cx.one j { as := .JMP, to := ← tgt e.b }
  | .Ret =>
    unless b.controls.size == 1 && b.succs.isEmpty do throw s!"b{b.id}: ret shape"
    let _ ← cx.one j { as := .RET }
  | k =>
    let some e0 := b.succs[0]? | throw s!"b{b.id}: no successor 0"
    let some e1 := b.succs[1]? | throw s!"b{b.id}: no successor 1"
    unless b.succs.size == 2 && b.controls.size == 1 do throw s!"b{b.id}: branch shape"
    let some c := b.controls[0]? | throw s!"b{b.id}: no control"
    let (asm, inv, sh) ← match condBr k, zeroBr k with
      | some (asm, inv), _ =>
        unless (cx.lc.ty c).isFlags && cx.lc.home c == none do throw s!"b{b.id}: control shape"
        pure (asm, inv, ({ as := .XXX } : Shape))
      | none, some (asm, inv) =>
        let some r := regHome? cx.lc c | throw s!"b{b.id}: control has no register"
        let some o := objOf? r | throw s!"b{b.id}: control register {r}"
        unless cls (cx.lc.ty c) == some 64 || cls (cx.lc.ty c) == some 1 do
          throw s!"b{b.id}: control width"
        pure (asm, inv, ({ as := .XXX, from_ := regA o } : Shape))
      | none, none => throw s!"b{b.id}: block kind {k.name}"
    match two { sh with as := asm } e0.b e1.b with
    | .ok () => return
    | .error _ => two { sh with as := inv } e1.b e0.b

/-- The PC table: for each block, the index in `ps` of the first Prog of each value and of the
terminator. -/
abbrev PcTab := List (ID × List Nat)

/-- Checks every block (in layout order). -/
def Cx.blocks (cx : Cx) : List ID → Except String PcTab
  | [] => return []
  | bid :: rest => do
    let some b := cx.lc.ctx.f.block? bid | throw s!"b{bid} is not in the function"
    let j ← cx.startIdx bid
    let (js, e) ← cx.values (bid == cx.lc.ctx.f.entry) b.values.toList j true
    let next ← match rest.head? with
      | some n => pure (some (n, ← cx.startIdx n))
      | none => pure none
    cx.term b e next
    let tab ← cx.blocks rest
    return (bid, js ++ [e]) :: tab

/-- Slice G1 of the genssa validator (module doc): the PC table of the accepted function. -/
def checkG1 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) : Except String PcTab := do
  unless lc.ctx.f.lowered do throw "not lowered"
  let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
  let cx : Cx := { lc, ps, idx, bstart }
  let tab ← cx.blocks lc.ctx.f.blocks.toList
  -- after the blocks, which reject most functions quickly (this check is quadratic)
  if let some i := (List.range lc.homes.size).find? (!homeOK lc ·) then throw (homeErr lc i)
  let ids := ps.toList.map (·.id)
  unless ids.all (· < 2 ^ 32) && ids.Nodup do throw "Prog IDs"
  return tab

end GoFV.Gen.Check

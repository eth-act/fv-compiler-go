import GoFV.Gen.Check

/-!
# The genssa validator, slice G2 (`docs/plans/proofs3.md` §4)

`checkG2 lc ps bstart g` extends slice G1 (`GoFV/Gen/Check.lean`) by the most frequent blockers
on the corpus: static calls and their results, addresses of globals, spill slots, and `Exit`
blocks. Besides G1's inputs it takes `g : G2In`: the symbols of the Prog list (genssa's interned
`(name, ABI)` by index) and Go's frame layout of the spill slots (`slotOp`: the operand name class
and offset of each slot, from the exported frame, `FrameOffset + off`; `stksize`). It accepts what
G1 accepts and

* `CALLstatic` of a function symbol with an ABI: one `CALL` whose target (`TYPE_MEM`,
  `NAME_EXTERN`) is the callee's symbol; every input parameter in registers, each register
  argument homed in its `abi.RegIndex` register (`abiReg`), the memory last; the call's `results`
  home lists the result registers of the ABI;
* `SelectN [i]` of such a call: the memory (no home), or result `i` homed in the call's result
  register `i`; no code;
* `MOVDaddr` of a global (`SB` argument, a symbol aux): `MOVD $sym+off(SB), Rd` with the global's
  symbol;
* `StoreReg`/`LoadReg` of a 64-bit register to/from an 8-byte spill slot: `MOVD Rs, off(RSP)` /
  `MOVD off(RSP), Rd` with the slot's operand from the frame layout (`NAME_AUTO`: the locals,
  `NAME_PARAM`: the spill area of a register argument);
* `Exit` blocks (a call that does not return; `runLoc` is `stuck` past it): no-ops up to the next
  block's start;
* the entry values may follow spills (`StoreReg`, which change neither a register nor the
  memory) at the head of the entry block.

**checkFrame** (proofs3 §2, the spill-slot part): every slot used as a home has an operand in the
frame layout, 8 bytes, 8-aligned, `NAME_AUTO` slots inside the locals (`[-stksize, 0)`),
`NAME_PARAM` slots at non-negative offsets, and distinct slots at distinct operands (so they are
disjoint).

The soundness proof of G2 (calls through the runtime hooks of semantics3 §6 and `MatchEnv.Extends`,
`framed = true` with the prologue and epilogue validators, `LocMatch.slots` preservation) is the
next step of proofs3 §4.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The inputs of slice G2 beyond G1's. -/
structure G2In where
  /-- The Prog list's symbols by index: name and ABI. -/
  syms : Array (GoStr × Nat)
  /-- Go's frame layout: the operand name class and offset of a spill slot. -/
  slotOp : SlotKey → Option (AddrName × Int)
  /-- The size of the locals (`NAME_AUTO` operands lie in `[-stksize, 0)`). -/
  stksize : Int

/-- The Go register of an `abi.RegIndex`: `R0`–`R15` (0–15), `F0`–`F15` (16–31 ↦ 31–46). -/
def abiReg (k : Nat) : Nat := if k < 16 then k else 31 + (k - 16)

/-- `REGSP`. -/
def regSP : Int := 8383

/-- The symbol and ABI of a function or global aux. -/
def symOf? (tabs : Tables) (a : AuxRef) : Option (GoStr × Nat) :=
  match tabs.aux? a with
  | some { kind := .sym name abi .., .. } => some (name, abi)
  | _ => none

/-- The callee symbol and the ABI analysis of a call aux. -/
def callOf? (tabs : Tables) (aux : Option AuxRef) : Option (GoStr × Nat × CallABI) :=
  match aux.bind tabs.aux? with
  | some { kind := .call (some fn) (some abi), .. } => (symOf? tabs fn).map fun (n, a) => (n, a, abi)
  | _ => none

/-- A Prog G2 expects: a predicate and what it is. -/
structure Pat where
  ok : Prog → Bool
  what : String

def Pat.ofShape (sh : Shape) : Pat := ⟨sh.ok, sh.as.name⟩

/-- What a value emits in G2. -/
inductive VKind2 where
  | entry
  | none
  | prog (p : Pat)

/-- A memory operand off `RSP` with the given name class and offset (the symbol, which
`NAME_AUTO`/`NAME_PARAM` addressing ignores, unconstrained). -/
def slotA (a : Addr) (cls : AddrName) (off : Int) : Bool :=
  a.type == .MEM && a.reg == regSP && a.index == 0 && a.name == cls && a.offset == off

/-- A plain Prog with operands `from_`, `to` checked by predicates. -/
def plain (as : As) (f t : Addr → Bool) (p : Prog) : Bool :=
  p.as == as && f p.from_ && p.reg == 0 && t p.to && p.scond == 0 && p.rest.isEmpty &&
    p.regTo2 == 0

/-- The slot home of `id`. -/
def slotHome? (lc : LocCtx) (id : ID) : Option SlotKey :=
  match lc.home id with
  | some (.slot k) => some k
  | _ => none

/-- The register arguments of a call (all but the memory) and the result registers, from its
ABI: every input parameter in registers. -/
def callRegs (abi : CallABI) : Except String (List Nat × List Nat) := do
  let ins := abi.params.toList.filter (!·.out)
  let outs := abi.params.toList.filter (·.out)
  for p in ins do
    if p.regs.isEmpty then throw "stack argument"
  for p in outs do
    if p.regs.isEmpty then throw "stack result"
  return (ins.flatMap (·.regs.toList.map abiReg), outs.flatMap (·.regs.toList.map abiReg))

/-- What `v` emits in G2, or why it is outside the slice. -/
def vkind2 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 := do
  let ty := lc.ty v.id
  if (lc.temps[v.id]?).join != none then throw s!"v{v.id}: temporary register"
  match v.op with
  | .ARM64CALLstatic =>
    let some (name, abi, cabi) := callOf? lc.ctx.tabs v.aux | throw s!"v{v.id}: call without ABI"
    let (ins, outs) ← callRegs cabi
    let some m := v.args.back? | throw s!"v{v.id}: call without memory"
    unless memTy (lc.ty m) && lc.home m == none do throw s!"v{v.id}: call memory"
    let rargs := v.args.toList.dropLast
    unless rargs.length == ins.length do throw s!"v{v.id}: call arguments"
    for (a, r) in rargs.zip ins do
      unless regHome? lc a == some r do throw s!"v{v.id}: argument v{a} not in register {r}"
    match lc.home v.id with
    | some (.results rs) =>
      unless rs.toList == outs.map some do throw s!"v{v.id}: result registers"
    | none => unless outs.isEmpty do throw s!"v{v.id}: result registers"
    | _ => throw s!"v{v.id}: call home"
    let target (a : Addr) : Bool :=
      a.type == .MEM && a.name == .EXTERN && a.reg == 0 && a.index == 0 && a.offset == 0 &&
        match a.sym with
        | some y => g.syms[y]? == some (name, abi)
        | none => false
    return .prog ⟨plain .CALL (fun a : Addr => a == {}) target, "CALL"⟩
  | .SelectN =>
    let some c := v.args[0]? | throw s!"v{v.id}: select shape"
    let some u := lc.ctx.f.value? c | throw s!"v{v.id}: select of v{c}"
    unless v.args.size == 1 && u.op == .ARM64CALLstatic do throw s!"v{v.id}: select of {u.op.name}"
    if memTy ty then
      unless lc.home v.id == none do throw s!"v{v.id}: memory select home"
      return .none
    let some r := regHome? lc v.id | throw s!"v{v.id}: select home"
    match lc.home c with
    | some (.results rs) =>
      unless rs[v.auxInt.toInt.toNat]? == some (some r) do throw s!"v{v.id}: select register"
    | _ => throw s!"v{v.id}: select home"
    return .none
  | .ARM64MOVDaddr =>
    let some a := v.args[0]? | throw s!"v{v.id}: address shape"
    unless v.args.size == 1 && (lc.ctx.f.value? a).map (·.op) == some .SB do
      throw s!"v{v.id}: address of a frame variable"
    let some x := v.aux | throw s!"v{v.id}: address without symbol"
    let some (name, abi) := symOf? lc.ctx.tabs x | throw s!"v{v.id}: address of a non-global"
    let (_, rd) ← resObj lc v
    let src (a : Addr) : Bool :=
      a.type == .ADDR && a.name == .EXTERN && a.reg == 0 && a.index == 0 &&
        a.offset == v.auxInt.toInt &&
        match a.sym with
        | some y => g.syms[y]? == some (name, abi)
        | none => false
    return .prog ⟨plain .MOVD src (· == regA rd), "MOVD $sym"⟩
  | .StoreReg =>
    let some k := slotHome? lc v.id | throw s!"v{v.id}: store home"
    let some (cls, off) := g.slotOp k | throw s!"v{v.id}: slot without frame offset"
    unless v.args.size == 1 do throw s!"v{v.id}: store shape"
    let (c, rs) ← argObj lc v 0
    unless c == 64 do throw s!"v{v.id}: narrow spill"
    return .prog ⟨plain .MOVD (· == regA rs) (slotA · cls off), "MOVD spill"⟩
  | .LoadReg =>
    let some a := v.args[0]? | throw s!"v{v.id}: load shape"
    let some k := slotHome? lc a | throw s!"v{v.id}: reload of v{a} without slot"
    let some (cls, off) := g.slotOp k | throw s!"v{v.id}: slot without frame offset"
    unless v.args.size == 1 do throw s!"v{v.id}: load shape"
    let (c, rd) ← resObj lc v
    unless c == 64 do throw s!"v{v.id}: narrow reload"
    return .prog ⟨plain .MOVD (slotA · cls off) (· == regA rd), "MOVD reload"⟩
  | _ =>
    match ← vkind lc v with
    | .entry => return .entry
    | .none => return .none
    | .prog sh => return .prog (.ofShape sh)

/-- The home of value `i` is one G2 handles: G1's, a spill slot of a `StoreReg`, or the
`results` home of a static call. -/
def homeOK2 (lc : LocCtx) (i : Nat) : Bool :=
  match lc.home i with
  | some (.slot _) => (lc.ctx.f.value? i).map (·.op) == some .StoreReg
  | some (.results rs) =>
    (rs.isEmpty && (lc.ctx.f.value? i).map (·.op) == some .MakeResult) ||
      (lc.ctx.f.value? i).map (·.op) == some .ARM64CALLstatic
  | _ => homeOK lc i

/-- checkFrame for the spill slots used as homes (module doc). -/
def checkFrame (lc : LocCtx) (g : G2In) : Except String Unit := do
  let ks := (List.range lc.homes.size).filterMap (slotHome? lc)
  let mut seen : List (SlotKey × AddrName × Int) := []
  for k in ks do
    let some (cls, off) := g.slotOp k | throw s!"slot n{k.name}+{k.off}: no frame offset"
    unless typeSize? lc.ctx.tabs k.type == some 8 do throw s!"slot n{k.name}+{k.off}: size"
    unless off % 8 == 0 do throw s!"slot n{k.name}+{k.off}: alignment"
    match cls with
    | .AUTO => unless -g.stksize ≤ off && off + 8 ≤ 0 do throw s!"slot n{k.name}+{k.off}: outside the locals"
    | .PARAM => unless 0 ≤ off do throw s!"slot n{k.name}+{k.off}: parameter offset"
    | _ => throw s!"slot n{k.name}+{k.off}: name class"
    for (k', cls', off') in seen do
      if k' != k && cls' == cls && off' == off then throw s!"slot n{k.name}+{k.off}: overlaps"
    seen := (k, cls, off) :: seen

/-- The context of the check. -/
structure Cx2 where
  cx : Cx
  g : G2In

/-- One Prog matching `pat` after no-ops from `j`: the index after it. -/
def Cx2.one (c : Cx2) (j : Nat) (pat : Pat) : Except String Nat := do
  let k := skipFrom c.cx.ps j c.cx.ps.size
  let some p := c.cx.ps[k]? | throw s!"no Prog at {k} for {pat.what}"
  unless pat.ok p do throw s!"Prog {p.id}: {p.as.name}, expected {pat.what}"
  return k + 1

def Cx2.values (c : Cx2) (entry : Bool) : List ID → Nat → Bool → Except String (List Nat × Nat)
  | [], j, _ => return ([], j)
  | id :: ids, j, head => do
    let some v := c.cx.lc.ctx.f.value? id | throw s!"v{id} is not in the function"
    let k ← match ← vkind2 c.cx.lc c.g v with
      | .entry =>
        unless entry && head do throw s!"v{id}: {v.op.name} after the entry values"
        pure j
      | .none => pure j
      | .prog pat => c.one j pat
    -- a spill changes neither a register nor the memory: entry values may follow it
    let head := head && (entryOp v.op || v.op == .StoreReg)
    let (js, e) ← c.values entry ids k head
    return (j :: js, e)

/-- The terminator: G1's kinds, and `Exit` (no-ops up to the next block's start). -/
def Cx2.term (c : Cx2) (b : Block) (j : Nat) (next : Option (ID × Nat)) : Except String Unit := do
  if b.kind == .Exit then
    unless b.succs.isEmpty do throw s!"b{b.id}: exit shape"
    if let some (_, k) := next then
      unless j ≤ k && ((List.range (k - j)).all fun i => (c.cx.ps[j + i]?.map noop) == some true) do
        throw s!"b{b.id}: code after exit"
  else c.cx.term b j next

def Cx2.blocks (c : Cx2) : List ID → Except String PcTab
  | [] => return []
  | bid :: rest => do
    let some b := c.cx.lc.ctx.f.block? bid | throw s!"b{bid} is not in the function"
    let j ← c.cx.startIdx bid
    let (js, e) ← c.values (bid == c.cx.lc.ctx.f.entry) b.values.toList j true
    let next ← match rest.head? with
      | some n => pure (some (n, ← c.cx.startIdx n))
      | none => pure none
    c.term b e next
    let tab ← c.blocks rest
    return (bid, js ++ [e]) :: tab

/-- Slice G2 of the genssa validator (module doc): the PC table of the accepted function. -/
def checkG2 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String PcTab := do
  unless lc.ctx.f.lowered do throw "not lowered"
  let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
  let c : Cx2 := { cx := { lc, ps, idx, bstart }, g }
  let tab ← c.blocks lc.ctx.f.blocks.toList
  if let some i := (List.range lc.homes.size).find? (!homeOK2 lc ·) then throw (homeErr lc i)
  checkFrame lc g
  let ids := ps.toList.map (·.id)
  unless ids.all (· < 2 ^ 32) && ids.Nodup do throw "Prog IDs"
  return tab

end GoFV.Gen.Check

import GoFV.Gen.Check65

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G66: spill slots of 1, 2 and 4 bytes (`docs/plans/slot-size.md`)

`stackalloc` homes a value in a spill slot of its own type, so a value of a narrow type (`bool`,
`int8`/`uint8`, `int16`/`uint16`, `int32`/`uint32`, `float32`) has a slot of 1, 2 or 4 bytes.
`checkFrame` (G2, widened by this slice) accepts such slots (`slotOK`: 1, 2, 4 or 8 bytes, aligned,
windows apart, every homed value of its slot's class and size, `homeFits`), and `StkAt` gives each
slot its own size. Every earlier slice's spill and reload is of a 64-bit value; genssa
(`cmd/compile/internal/arm64/ssa.go`, `ssa.OpStoreReg`/`ssa.OpLoadReg`, `storeByType`/`loadByType`;
`GoFV/Gen/Arm64Value.lean`) emits for the narrow ones:

* a narrow spill (`nspill66`): a `StoreReg` of an integer or boolean of `n ∈ {1, 2, 4}` bytes
  (`narrowBytes`) whose argument is homed in an `X` register at the value's class:
  `MOVB`/`MOVH`/`MOVW Rs, off(RSP)` at the slot's operand;
* a narrow reload (`nreload66`): a `LoadReg` of such a value into an `X` register:
  `MOVB`/`MOVH`/`MOVW` for a signed type, `MOVBU`/`MOVHU`/`MOVWU` otherwise (`typeSigned`; a
  `bool` is unsigned);
* a `float32` spill or reload (`fspill66`, `freload66`) through an `F` register: `FMOVS Fs,
  off(RSP)` / `FMOVS off(RSP), Fd`;
* an incoming stack argument (`Arg`) of a narrow class (`argKind66`): G62's `argKind62` at any
  class; no code.

A value of another kind keeps G65's reason. `GoFV/Proof/Gen/G66.lean` proves what an accepted
function satisfies, with G65's premises.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The bytes of a narrow (1, 2 or 4 bytes) type that is no float: `none` otherwise. -/
def narrowBytes (lc : LocCtx) (t : TypeRef) : Option Nat :=
  match lc.ctx.tabs.type? t with
  | some d =>
    if d.kind == .FLOAT32 || d.kind == .FLOAT64 then none
    else match typeSize? lc.ctx.tabs t with
      | some n => if n == 1 || n == 2 || n == 4 then some n else none
      | none => none
  | none => none

/-- `storeByType` of an integer of `n` bytes. -/
def nstoreAs : Nat → As
  | 1 => .MOVB
  | 2 => .MOVH
  | _ => .MOVW

/-- `loadByType` of an integer of `n` bytes, signed (`sg`) or not. -/
def nloadAs (n : Nat) (sg : Bool) : As :=
  match n with
  | 1 => if sg then .MOVB else .MOVBU
  | 2 => if sg then .MOVH else .MOVHU
  | _ => if sg then .MOVW else .MOVWU

/-- A narrow spill (module doc); `e` is G65's reason, kept for a `StoreReg` that is no narrow
integer spill from an `X` register. -/
def nspill66 (lc : LocCtx) (g : G2In) (v : Value) (e : String) : Except String VKind2 := do
  unless ((v.args[0]?).bind (regHome? lc) |>.bind objOf?).isSome do throw e
  let some n := narrowBytes lc v.type | throw e
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  let some k := slotHome? lc v.id | throw s!"v{v.id}: store home"
  let some (nc, off) := g.slotOp k | throw s!"v{v.id}: slot without frame offset"
  unless v.args.size == 1 && (lc.ty v.id).size == n do throw s!"v{v.id}: narrow spill shape"
  let (c, rs) ← argObj lc v 0
  unless cls (lc.ty v.id) == some c do throw s!"v{v.id}: narrow spill widths"
  return .prog ⟨plain (nstoreAs n) (· == regA rs) (slotA · nc off), "narrow spill"⟩

/-- A narrow reload (module doc); `e` is G65's reason, kept for a `LoadReg` that is no narrow
integer reload into an `X` register. -/
def nreload66 (lc : LocCtx) (g : G2In) (v : Value) (e : String) : Except String VKind2 := do
  unless ((regHome? lc v.id).bind objOf?).isSome do throw e
  let some n := narrowBytes lc v.type | throw e
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  let some a := v.args[0]? | throw s!"v{v.id}: load shape"
  let some k := slotHome? lc a | throw s!"v{v.id}: reload of v{a} without slot"
  let some (nc, off) := g.slotOp k | throw s!"v{v.id}: slot without frame offset"
  unless v.args.size == 1 && (lc.ty a).size == n && cls (lc.ty a) == cls (lc.ty v.id) do
    throw s!"v{v.id}: narrow reload shape"
  let (_, rd) ← resObj lc v
  let as := nloadAs n (typeSigned lc.ctx.tabs v.type)
  return .prog ⟨plain as (slotA · nc off) (· == regA rd), "narrow reload"⟩

/-- A `float32` spill: `FMOVS Fs, off(RSP)`; `e` is G65's reason. -/
def fspill66 (lc : LocCtx) (g : G2In) (v : Value) (e : String) : Except String VKind2 := do
  unless ((v.args[0]?).bind (regHome? lc) |>.bind fobjOf?).isSome do throw e
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  let some k := slotHome? lc v.id | throw s!"v{v.id}: store home"
  let some (nc, off) := g.slotOp k | throw s!"v{v.id}: slot without frame offset"
  unless v.args.size == 1 && fTy (lc.ty v.id) && cls (lc.ty v.id) == some 32 do throw e
  let (c, rs) ← fargObj lc v 0
  unless c == 32 do throw s!"v{v.id}: float32 spill widths"
  return .prog ⟨plain .FMOVS (· == regA rs) (slotA · nc off), "FMOVS spill"⟩

/-- A `float32` reload: `FMOVS off(RSP), Fd`; `e` is G65's reason. -/
def freload66 (lc : LocCtx) (g : G2In) (v : Value) (e : String) : Except String VKind2 := do
  unless ((regHome? lc v.id).bind fobjOf?).isSome do throw e
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  let some a := v.args[0]? | throw s!"v{v.id}: load shape"
  let some k := slotHome? lc a | throw s!"v{v.id}: reload of v{a} without slot"
  let some (nc, off) := g.slotOp k | throw s!"v{v.id}: slot without frame offset"
  unless v.args.size == 1 && cls (lc.ty a) == some 32 do throw e
  let (c, rd) ← fresObj lc v
  unless c == 32 do throw s!"v{v.id}: float32 reload widths"
  return .prog ⟨plain .FMOVS (slotA · nc off) (· == regA rd), "FMOVS reload"⟩

/-- An `Arg` of an incoming stack argument of any class (G62's `argKind62` but its width): no
code. -/
def argKind66 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 0 do throw s!"v{v.id}: Arg shape"
  let some x := v.aux | throw s!"v{v.id}: Arg without name"
  unless stackParam lc x do throw s!"v{v.id}: Arg of a register parameter"
  unless (cls (lc.ty v.id)).isSome do throw s!"v{v.id}: Arg width"
  unless lc.home v.id == some (.slot (argKey x v.type v.auxInt.toInt)) do
    throw s!"v{v.id}: Arg home"
  let some (.PARAM, _) := g.slotOp (argKey x v.type v.auxInt.toInt)
    | throw s!"v{v.id}: Arg slot operand"
  return .none

/-- G66's values (module doc), `e` G65's reason: `none` off `StoreReg`/`LoadReg`/`Arg`. A spill or
reload is a `float32` one through an `F` register, else a narrow integer one. -/
def vkind66a (lc : LocCtx) (g : G2In) (v : Value) (e : String) : Option (Except String VKind2) :=
  if v.op == .StoreReg then
    if ((v.args[0]?).bind (regHome? lc) |>.bind fobjOf?).isSome then some (fspill66 lc g v e)
    else some (nspill66 lc g v e)
  else if v.op == .LoadReg then
    if ((regHome? lc v.id).bind fobjOf?).isSome then some (freload66 lc g v e)
    else some (nreload66 lc g v e)
  else if v.op == .Arg then some (argKind66 lc g v)
  else none

/-- What `v` emits in G66, or why it is outside the slice: G65's kinds, then G66's (`e` is G65's
reason, kept for the other values). -/
def vkind66 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  match vkind65 lc g v with
  | .ok kd => .ok kd
  | .error e =>
    match vkind66a lc g v e with
    | some r => r
    | none => .error e

/-- G65's check with G66's value check. -/
def checkG66L (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind66 lc g, tm := cx.termG3 }
    let tab ← c.blocks lc.ctx.f.blocks.toList
    unless pbOK lc ps.toList tab do throw "bounds panic PCDATA"
    unless loopOK lc ps tab do throw "loop branch target"
    unless atomOK lc ps tab do throw "atomic branch target"
    unless movdOK35 lc && uEdgesOK35 lc do throw "MOVDnop/MOVDreg: upper bits unknown"
    if let some i := (List.range lc.homes.size).find? (!homeOK10 lc ·) then throw (homeErr lc i)
    unless cloFirst lc do throw "LoweredGetClosurePtr after code"
    unless spHomes48 lc do throw "a value other than SP homed in SP"
    checkFrame lc g
    checkVars49 lc g
    let kin := kFlow lc (65 * lc.ctx.f.blocks.size + 2)
    let kt : KTab := lc.ctx.f.blocks.toList.map fun b => (b, (kin[b]?).getD KMap.bot)
    checkK lc kt
    let ids := ps.toList.map (·.id)
    unless ids.all (· < 2 ^ 32) && ids.Nodup do throw "Prog IDs"
    return (tab, kt)
  else checkNL30 lc ps bstart g

/-- Slice G66 of the genssa validator (module doc): `refsLive`, then G66's check on `liveCtx lc`. -/
def checkG66 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless refsLive lc do throw "a value refers to an ID that is no value of the function"
  checkG66L (liveCtx lc) ps bstart g

end GoFV.Gen.Check

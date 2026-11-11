import GoFV.Gen.Check62

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G63: float spills (`docs/plans/proofs3.md` §4)

Register allocation spills a value homed in an `F` register to a spill slot (`StoreReg`) and
reloads it into an `F` register (`LoadReg`) as it does a 64-bit integer. Genssa emits them with
`storeByType`/`loadByType` of the value's type (`cmd/compile/internal/arm64/ssa.go`,
`ssa.OpStoreReg`/`ssa.OpLoadReg`; `GoFV/Gen/Arm64Value.lean`): for a `float64`, `FMOVD Fs,
off(RSP)` and `FMOVD off(RSP), Fd`, with the slot's operand from the frame layout (`AddrAuto`).
G2's spill and reload (`vkind2`) take X registers only (`argObj`, `resObj`), so every slice before
G63 rejects them (`argument v# in register #`, `writes register #`).

`checkG63 lc ps bstart g` is slice G62 (`GoFV/Gen/Check62.lean`, on P0') with, tried when G62
rejects a `StoreReg` or `LoadReg` (`vkind63a`):

* a float spill (`fspill63`): a `StoreReg` of a float of class 64 (`fTy`, the `float64` bit
  pattern) whose argument is homed in an `F` register (`fargObj`), the value homed in a spill slot
  with a frame operand: `FMOVD Fs, off(RSP)`;
* a float reload (`freload63`): a `LoadReg` of a value of class 64 homed in a spill slot with a
  frame operand, into an `F` register at a float shape of class 64 (`fresObj`):
  `FMOVD off(RSP), Fd`.

A `StoreReg` whose argument, or a `LoadReg` whose home, is no `F` register keeps G62's reason. The
slots are `checkFrame`'s 8-byte slots, as G2's (a `float32` slot of 4 bytes fails `slotOK`).
`GoFV/Proof/Gen/G63.lean` proves what an accepted function satisfies, given that a float reload
reads no pointer without an integer form (`FReloadPre`, as G44's `FLoadPre`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- A float spill (module doc): `FMOVD Fs, off(RSP)`; `e` is G62's reason, kept for a `StoreReg`
whose argument is not in an `F` register. -/
def fspill63 (lc : LocCtx) (g : G2In) (v : Value) (e : String) : Except String VKind2 := do
  unless ((v.args[0]?).bind (regHome? lc) |>.bind fobjOf?).isSome do throw e
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  let some k := slotHome? lc v.id | throw s!"v{v.id}: store home"
  let some (nc, off) := g.slotOp k | throw s!"v{v.id}: slot without frame offset"
  unless v.args.size == 1 && fTy (lc.ty v.id) && (cls (lc.ty v.id) == some 64 ||
      (cls (lc.ty v.id) == some 32 && slotN lc k == some 4)) do
    throw s!"v{v.id}: float spill shape"
  let (c, rs) ← fargObj lc v 0
  unless some c == cls (lc.ty v.id) do throw s!"v{v.id}: narrow float spill"
  return .prog ⟨plain (fmovAs c) (· == regA rs) (slotA · nc off), "FMOV spill"⟩

/-- A float reload (module doc): `FMOVD off(RSP), Fd`; `e` is G62's reason, kept for a `LoadReg`
not homed in an `F` register. -/
def freload63 (lc : LocCtx) (g : G2In) (v : Value) (e : String) : Except String VKind2 := do
  unless ((regHome? lc v.id).bind fobjOf?).isSome do throw e
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  let some a := v.args[0]? | throw s!"v{v.id}: load shape"
  let some k := slotHome? lc a | throw s!"v{v.id}: reload of v{a} without slot"
  let some (nc, off) := g.slotOp k | throw s!"v{v.id}: slot without frame offset"
  unless v.args.size == 1 && (cls (lc.ty a) == some 64 ||
      (cls (lc.ty a) == some 32 && slotN lc k == some 4)) do
    throw s!"v{v.id}: float reload shape"
  let (c, rd) ← fresObj lc v
  unless some c == cls (lc.ty a) do throw s!"v{v.id}: narrow float reload"
  return .prog ⟨plain (fmovAs c) (slotA · nc off) (· == regA rd), "FMOV reload"⟩

/-- G63's values: a float spill or reload (module doc); `none` off `StoreReg`/`LoadReg`. -/
def vkind63a (lc : LocCtx) (g : G2In) (v : Value) (e : String) : Option (Except String VKind2) :=
  if v.op == .StoreReg then some (fspill63 lc g v e)
  else if v.op == .LoadReg then some (freload63 lc g v e)
  else none

/-- What `v` emits in G63, or why it is outside the slice: G62's kinds, then G63's float spills
and reloads (`e` is G62's reason, kept for the other values). -/
def vkind63 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  match vkind62 lc g v with
  | .ok kd => .ok kd
  | .error e =>
    match vkind63a lc g v e with
    | some r => r
    | none => .error e

/-- G62's check with G63's value check. -/
def checkG63L (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind63 lc g, tm := cx.termG3 }
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

/-- Slice G63 of the genssa validator (module doc): `refsLive`, then G63's check on `liveCtx lc`. -/
def checkG63 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless refsLive lc do throw "a value refers to an ID that is no value of the function"
  checkG63L (liveCtx lc) ps bstart g

end GoFV.Gen.Check

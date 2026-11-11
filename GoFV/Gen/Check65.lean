import GoFV.Gen.Check64

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G65: float loads of frame variables, float pair stores through a
register or to a global (`docs/plans/proofs3.md` §4)

Two float accesses that each earlier slice handles at one operand form only:

* G44 loads a float (`FMOVSload`/`FMOVDload`) through a 64-bit register or of a global
  (`accessA`), and rejects a frame variable (`access of a frame variable`, or G49's `frame
  variable aux on FMOVDload`); G57 stores a float to one (`fvarStore57`);
* G57 stores a float pair (`FSTPS`/`FSTPD`) to a frame variable (`fvarStp57`), and every slice
  rejects one through a register or to a global (`op FSTPD`); G4 and G22 store an integer pair
  there (`STP`).

`checkG65 lc ps bstart g` is slice G64 (`GoFV/Gen/Check64.lean`, on P0') with, tried when G64
rejects a value (`vkind65a`):

* a float load of a frame variable (`fvload65`): `FMOVSload`/`FMOVDload [off] {x} SP mem` of a
  variable `x` that G57's float stores accept (`fvar57?`: G49's `Blk.local` variables at
  `NAME_AUTO` or `NAME_PARAM`, G6's `Blk.temp` ones at `NAME_AUTO`), into an `F` register at the
  float shape of the op's width (`fresObj`): `FMOVS`/`FMOVD off(<nc>), Fd`, as `ssaGenValue`'s
  load case (`cmd/compile/internal/arm64/ssa.go`, `GoFV/Gen/Arm64Value.lean`) emits it with the
  variable's frame operand (`AddrAuto`);
* a float pair store through a register or to a global (`fstp65`): `FSTPS`/`FSTPD [off] {sym}
  base a b mem` at G3's operand forms (`accessA`: `off(Rn)` through a 64-bit register without a
  symbol, `sym+off(SB)` of a global), `a` and `b` floats of the op's element width in `F`
  registers: `FSTPS`/`FSTPD (Fa, Fb), dst`.

A float load of any other operand keeps G64's reason. `GoFV/Proof/Gen/G65.lean` proves what an
accepted function satisfies, with G64's premises: the loads are G44's (`FLoadPre`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- A float load of a frame variable at the operand `nc`, `off`: `FMOVS`/`FMOVD off(<nc>), Fd`. -/
def fvload65 (lc : LocCtx) (v : Value) (nc : AddrName) (off : Int) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 2 do throw s!"v{v.id}: load shape"
  memArg lc v 1
  let (c, rd) ← fresObj lc v
  unless c == 8 * fBytes v.op do throw s!"v{v.id}: load widths"
  return .prog ⟨plain (fmovAs c) (slotA · nc off) (· == regA rd), (fmovAs c).name⟩

/-- A float pair store of `n`-byte elements through a register or to a global (`accessA`):
`FSTPS`/`FSTPD (Fa, Fb), dst`. -/
def fstp65 (lc : LocCtx) (g : G2In) (v : Value) (n : Nat) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  unless v.args.size == 4 && memTy (lc.ty v.id) && lc.home v.id == none do
    throw s!"v{v.id}: pair store shape"
  let (cx, rx) ← fargObj lc v 1
  let (cy, ry) ← fargObj lc v 2
  memArg lc v 3
  unless cx == 8 * n && cy == 8 * n do throw s!"v{v.id}: pair store widths"
  let dst ← accessA lc g v
  return .prog ⟨plain (fstpAs n) (· == pairA rx ry) dst, (fstpAs n).name⟩

/-- G65's values (module doc); `none` off them, and on a float load of no frame variable. -/
def vkind65a (lc : LocCtx) (g : G2In) (v : Value) : Option (Except String VKind2) :=
  if v.op = .ARM64FMOVSload ∨ v.op = .ARM64FMOVDload then
    (fvar57? lc g v).map fun (nc, off) => fvload65 lc v nc off
  else
    (fstpOf v.op).map (fstp65 lc g v)

/-- What `v` emits in G65, or why it is outside the slice: G64's kinds, then G65's float accesses
(`e` is G64's reason, kept for the other values). -/
def vkind65 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  match vkind64 lc g v with
  | .ok kd => .ok kd
  | .error e =>
    match vkind65a lc g v with
    | some r => r
    | none => .error e

/-- G64's check with G65's value check. -/
def checkG65L (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind65 lc g, tm := cx.termG3 }
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

/-- Slice G65 of the genssa validator (module doc): `refsLive`, then G65's check on `liveCtx lc`. -/
def checkG65 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless refsLive lc do throw "a value refers to an ID that is no value of the function"
  checkG65L (liveCtx lc) ps bstart g

end GoFV.Gen.Check

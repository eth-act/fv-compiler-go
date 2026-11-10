import GoFV.Gen.Check55
import GoFV.SSA.Sem.ConstSym

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G56: float constants in read-only symbols (`docs/plans/proofs3.md` §10)

`progedit` rewrites `FMOVS`/`FMOVD $c, Fd`, when `c` is no `FMOV` immediate and not 0, into a
load of the read-only constant symbol `$f32.<bits>`/`$f64.<bits>` (`GoFV.Asm.fconstSym?`); the
driver gives the validator P0' (`GoFV.Asm.p0Prime`), P0 with that rewrite, and the symbol in
`G2In.syms`. `checkG56 lc ps bstart g` is slice G55 (`GoFV/Gen/Check55.lean`) with, in a function
with an arm64 op, `FMOVSconst`/`FMOVDconst` (`vkind56a`, tried before G55's kinds) homed by
`FMOVS`/`FMOVD $c, Fd` (G44's `FCONST` Prog) or by the load `FMOVS`/`FMOVD sym(SB), Fd` of a
symbol whose name is a float constant symbol (`constSymAlloc?`) holding the bits the `FCONST`
Prog writes (`fconstNat`: `float32(c)`'s for `FMOVS`, `c`'s for `FMOVD`). `GoFV/Proof/Gen/G56.lean`
proves what an accepted function satisfies, given the symbols' bytes in memory.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The names of the Prog list's symbols. -/
def symNames (g : G2In) : List String := g.syms.toList.map (·.1.toStringLossy)

/-- The bits `FMOVS`/`FMOVD $c` (`n` = 4 or 8 bytes) writes for the constant `k` (`FCONST`
operand: the `float64` bits of `auxInt`): `float32(c)`'s bits for `FMOVS`, `c`'s for `FMOVD`. -/
def fconstNat (n : Nat) (k : Int64) : Nat :=
  if n = 4 then
    (GoFV.IEEE.convert GoFV.IEEE.Fmt.b64 GoFV.IEEE.Fmt.b32 .rne
      (BitVec.ofNat 64 k.toUInt64.toNat)).toNat
  else k.toUInt64.toNat

/-- A memory operand `sym(SB)` (offset 0) whose symbol is a float constant symbol holding the `n`
little-endian bytes of `x` (`constSymAlloc?` of its name). -/
def constSymA (g : G2In) (n x : Nat) (a : Addr) : Bool :=
  a.type == .MEM && a.name == .EXTERN && a.reg == 0 && a.index == 0 && a.offset == 0 &&
    match a.sym with
    | some y =>
      match g.syms[y]? with
      | some (name, _) => constSymAlloc? name.toStringLossy == some (roAlloc (leBytesU8 x n))
      | none => false
    | none => false

/-- The Prog of a float constant `v` of class `c` into `rd`: G44's `FMOVS`/`FMOVD $c, Fd`, or
P0''s load `FMOVS`/`FMOVD sym(SB), Fd` of its constant symbol. -/
def fconstPat56 (g : G2In) (v : Value) (c : Nat) (rd : Int) : Pat :=
  ⟨fun p => Shape.ok { as := fmovAs c, from_ := fconstA v, to := regA rd } p ||
      plain (fmovAs c) (constSymA g (fBytes v.op) (fconstNat (fBytes v.op) v.auxInt)) (· == regA rd)
        p,
    (fmovAs c).name⟩

/-- The float constants of G56: `FMOVSconst`/`FMOVDconst` (`none` for every other op). -/
def vkind56a (lc : LocCtx) (g : G2In) (v : Value) : Option (Except String VKind2) :=
  if v.op == .ARM64FMOVSconst || v.op == .ARM64FMOVDconst then
    some do
      unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
      unless v.args.size == 0 do throw s!"v{v.id}: const shape"
      let (c, rd) ← fresObj lc v
      unless c == 8 * fBytes v.op do throw s!"v{v.id}: const widths"
      return .prog (fconstPat56 g v c rd)
  else none

/-- What `v` emits in G56, or why it is outside the slice: a float constant by `vkind56a`, every
other value by G55's kinds. -/
def vkind56 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  match vkind56a lc g v with
  | some r => r
  | none => vkind55 lc g v

/-- G55's check with G56's value check. -/
def checkG56L (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind56 lc g, tm := cx.termG3 }
    let tab ← c.blocks lc.ctx.f.blocks.toList
    unless pbOK lc ps.toList tab do throw "bounds panic PCDATA"
    unless loopOK lc ps tab do throw "loop branch target"
    unless movdOK35 lc && uEdgesOK35 lc do throw "MOVDnop/MOVDreg: upper bits unknown"
    if let some i := (List.range lc.homes.size).find? (!homeOK10 lc ·) then throw (homeErr lc i)
    unless cloFirst lc do throw "LoweredGetClosurePtr after code"
    checkFrame lc g
    checkVars49 lc g
    let kin := kFlow lc (65 * lc.ctx.f.blocks.size + 2)
    let kt : KTab := lc.ctx.f.blocks.toList.map fun b => (b, (kin[b]?).getD KMap.bot)
    checkK lc kt
    let ids := ps.toList.map (·.id)
    unless ids.all (· < 2 ^ 32) && ids.Nodup do throw "Prog IDs"
    return (tab, kt)
  else checkNL30 lc ps bstart g

/-- Slice G56 of the genssa validator (module doc): `refsLive`, then G56's check on `liveCtx lc`. -/
def checkG56 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless refsLive lc do throw "a value refers to an ID that is no value of the function"
  checkG56L (liveCtx lc) ps bstart g

end GoFV.Gen.Check

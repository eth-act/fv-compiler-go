import GoFV.Gen.Check63

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G64: 128-bit moves of blobs (`docs/plans/proofs3.md` §4)

`lower` copies a `Move` of 16 to 64 bytes through V registers (`ARM64.rules` 420–428):
`FMOVQstore dst (FMOVQload src mem) mem` for 16 bytes, `FSTPQ dst (Select0 (FLDPQ src mem))
(Select1 (FLDPQ src mem)) mem` for 32, and their offset and symbol folds. The loaded values have
the shape `Ty.blob 16` (`Vec128`): `runLoc` loads them as their 16 raw bytes (`Arm64.load16`) and
stores those bytes back (`Arm64.storeBytes`), and the machine moves the 128 bits (`LDR`/`STR Q`,
`LDP`/`STP Q`; genssa emits `FMOVQ` and `FLDPQ`/`FSTPQ`, `cmd/compile/internal/arm64/ssa.go`).
Every slice before G64 rejects them (`op FMOVQload`, `register value of shape blob 16`, …).

`checkG64 lc ps bstart g` is slice G63 (`GoFV/Gen/Check63.lean`, on P0') with, tried when G63
rejects a value (`vkind64a`):

* `FMOVQload [off] {sym} base mem` into an `F` register at the blob shape (`qresObj`):
  `FMOVQ off(Rn), Fd`;
* `FMOVQstore [off] {sym} base x mem` of a blob in an `F` register (`qargObj`):
  `FMOVQ Fs, off(Rn)`;
* `FLDPQ [off] {sym} base mem` into a pair of distinct `F` registers, both components blobs:
  `FLDPQ off(Rn), (Fa, Fb)`;
* `FSTPQ [off] {sym} base x y mem` of two blobs in `F` registers: `FSTPQ (Fx, Fy), off(Rn)`;
* `Select0`/`Select1` of such an `FLDPQ`, homed in the register of its component: no code.

The memory operand (`qaccessA`) is G3's (`accessA`: `off(Rn)` through a 64-bit register without
a symbol, or `sym+off(SB)` of a global), or a frame variable's operand: G6's (`frameVar?`: a
`NAME_AUTO` variable in a `Blk.temp` block) or G49's (`frameVar49?`: a variable in a `Blk.local`
block, at its `NAME_AUTO` or `NAME_PARAM` operand). Accesses off `SP` without a symbol (G48's
outgoing area) stay rejected. A blob's V register home is `homeOK10`'s `blobHome`.
`GoFV/Proof/Gen/G64.lean` proves what an accepted function satisfies, given that a 128-bit load
reads valid bytes (`QLoadPre`, as G3's loads).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The obj register of the V register a 16-byte blob `v` writes (its register home, an `F`
register, at the blob shape). -/
def qresObj (lc : LocCtx) (v : Value) : Except String Int := do
  let some r := regHome? lc v.id | throw s!"v{v.id}: no register"
  let some o := fobjOf? r | throw s!"v{v.id}: writes register {r}"
  unless blob16 (lc.ty v.id) do throw s!"v{v.id}: 128-bit result shape"
  return o

/-- The obj register of the V register holding the 16-byte blob argument `i` of `v`. -/
def qargObj (lc : LocCtx) (v : Value) (i : Nat) : Except String Int := do
  let some a := v.args[i]? | throw s!"v{v.id}: no argument {i}"
  let some r := regHome? lc a | throw s!"v{v.id}: argument v{a} has no register"
  let some o := fobjOf? r | throw s!"v{v.id}: argument v{a} in register {r}"
  unless blob16 (lc.ty a) do throw s!"v{v.id}: 128-bit argument v{a} shape"
  return o

/-- The pair shape of `FLDPQ`: two 16-byte blobs. -/
def qpairTy : Ty → Bool
  | .tuple [t0, t1] => blob16 t0 && blob16 t1
  | _ => false

/-- The memory operand of a 128-bit access `v` (address argument 0): a frame variable's operand
(`fvar57?`: G49's `Blk.local` variables at `NAME_AUTO` or `NAME_PARAM`, G6's `Blk.temp` ones at
`NAME_AUTO`), or G3's (`accessA`: `off(Rn)`, `sym+off(SB)`). -/
def qaccessA (lc : LocCtx) (g : G2In) (v : Value) : Except String (Addr → Bool) :=
  match fvar57? lc g v with
  | some (nc, off) => .ok (slotA · nc off)
  | none => accessA lc g v

/-- G64's values (module doc), or why `v` is outside the slice. -/
def qkind64 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  match v.op with
  | .ARM64FMOVQload =>
    unless v.args.size == 2 do throw s!"v{v.id}: load shape"
    let rd ← qresObj lc v
    memArg lc v 1
    let src ← qaccessA lc g v
    return .prog ⟨plain .FMOVQ src (· == regA rd), "FMOVQ load"⟩
  | .ARM64FMOVQstore =>
    unless v.args.size == 3 && memTy (lc.ty v.id) && lc.home v.id == none do
      throw s!"v{v.id}: store shape"
    let rs ← qargObj lc v 1
    memArg lc v 2
    let dst ← qaccessA lc g v
    return .prog ⟨plain .FMOVQ (· == regA rs) dst, "FMOVQ store"⟩
  | .ARM64FLDPQ =>
    unless v.args.size == 2 && qpairTy (lc.ty v.id) do throw s!"v{v.id}: pair load shape"
    memArg lc v 1
    let some (ra, rb) := pairHome? lc v.id | throw s!"v{v.id}: pair load home"
    unless ra != rb do throw s!"v{v.id}: pair load registers"
    let some oa := fobjOf? ra | throw s!"v{v.id}: register {ra}"
    let some ob := fobjOf? rb | throw s!"v{v.id}: register {rb}"
    let src ← qaccessA lc g v
    return .prog ⟨plain .FLDPQ src (· == pairA oa ob), "FLDPQ"⟩
  | .ARM64FSTPQ =>
    unless v.args.size == 4 && memTy (lc.ty v.id) && lc.home v.id == none do
      throw s!"v{v.id}: pair store shape"
    let rx ← qargObj lc v 1
    let ry ← qargObj lc v 2
    memArg lc v 3
    let dst ← qaccessA lc g v
    return .prog ⟨plain .FSTPQ (· == pairA rx ry) dst, "FSTPQ"⟩
  | .Select0 | .Select1 =>
    let some c := v.args[0]? | throw s!"v{v.id}: select shape"
    let some u := lc.ctx.f.value? c | throw s!"v{v.id}: select of v{c}"
    unless v.args.size == 1 && u.op == .ARM64FLDPQ && qpairTy (lc.ty c) do
      throw s!"v{v.id}: select of {u.op.name}"
    let some (ra, rb) := pairHome? lc c | throw s!"v{v.id}: select of a pair without registers"
    let r := if v.op == .Select0 then ra else rb
    unless lc.home v.id == some (.reg r) && (fobjOf? r).isSome && blob16 (lc.ty v.id) do
      throw s!"v{v.id}: select home"
    return .none
  | op => throw s!"v{v.id}: op {op.name}"

/-- The ops of G64's values. -/
def qop64 (op : Op) : Bool :=
  op == .ARM64FMOVQload || op == .ARM64FMOVQstore || op == .ARM64FLDPQ || op == .ARM64FSTPQ ||
    op == .Select0 || op == .Select1

/-- G64's values: a 128-bit move (module doc); `none` off its ops. -/
def vkind64a (lc : LocCtx) (g : G2In) (v : Value) : Option (Except String VKind2) :=
  if qop64 v.op then some (qkind64 lc g v) else none

/-- What `v` emits in G64, or why it is outside the slice: G63's kinds, then G64's 128-bit moves
(`e` is G63's reason, kept for the other values and for a select G64 rejects too). -/
def vkind64 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  match vkind63 lc g v with
  | .ok kd => .ok kd
  | .error e =>
    match vkind64a lc g v with
    | some (.ok kd) => .ok kd
    | some (.error e') => .error (if v.op == .Select0 || v.op == .Select1 then e else e')
    | none => .error e

/-- G63's check with G64's value check. -/
def checkG64L (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind64 lc g, tm := cx.termG3 }
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

/-- Slice G64 of the genssa validator (module doc): `refsLive`, then G64's check on `liveCtx lc`. -/
def checkG64 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless refsLive lc do throw "a value refers to an ID that is no value of the function"
  checkG64L (liveCtx lc) ps bstart g

end GoFV.Gen.Check

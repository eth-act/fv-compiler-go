import GoFV.SSA.Sem.Run
import GoFV.SSA.Sem.Arm64

/-!
# `GoFV.SSA.runL`: lowered arm64 SSA (L0, `docs/plans/semantics2.md` §1, §3–§5)

`runL` is Phase 1's runner (`runCtx`: frame, block loop, terminators, calls, defers) with four
additions. Phase 1's definitions (`run`, `evalOp`, `evalPure`, `stepTerm`, `Val.retype`,
`encode`, `tyOf`) are unchanged; lowered code reaches the arm64 definitions only through `runL`.

* **Ops** (`evalOpL`). A value whose op is not generic is an arm64 op: `arm64Op` for the ops that
  need the activation, `Arm64.evalPure` for the others. A generic op is Phase 1's `evalOp`.
* **Block kinds** (`stepTermL`). The 25 arm64 kinds branch on flags or a register; a generic kind
  is Phase 1's `stepTerm`.
* **Narrow values** (`Val.retypeL`). In a lowered function (`Func.lowered`), a value is read at a
  shape as the register holding it: a narrower integer or a boolean at a wider integer or a
  pointer shape is zero-extended (`Val.widen`), then shaped by Phase 1's `Val.retype`. Lowering
  hands such values to generic consumers: Go's rewrite removes copies inline (`rewrite.go`,
  `applyRewrite`), so after `(MOVWUreg x) && ZeroUpper32Bits(x, 3) => x`,
  `(MOVBUreg x:(Equal …)) => x` (`ARM64latelower.rules`) or `(CvtBoolToUint8 x) => (Copy x)`
  a narrower or boolean `x` is an argument of a `Phi`, `MakeResult` or `Copy` of a wider type.
  The rules drop the extension exactly where the register's upper bits are zero. Calls and
  atomics read their register operands at their parameters' shapes (`fitPieces`, `atomicArgs`).
* **Shapes** (`tyOfL`). Go's `flags` type is `Ty.flags`, a `vec128` a 16-byte blob.

On a function with no arm64 op and no arm64 block kind the additions are inert: `runL_generic`
proves `runL = run`. So the `lower` theorem relates `run` of its input to `runL` of its output
(§2), and Phase 1's semantics is the generic fragment of `runL`.
-/

namespace GoFV.SSA.Sem

open GoFV.SSA

/-! ## Lowered shapes and narrow values -/

/-- The shape of type `t` in lowered code: Phase 1's `tyOf`, with Go's `flags` type as
`Ty.flags` and a `Vec128` register as its 16 bytes, also as tuple components (`ADDSflags`). -/
def tyOfL (tabs : Tables) : Nat → TypeRef → Ty
  | 0, _ => .other
  | fuel + 1, t =>
    match tabs.type? t with
    | none => .other
    | some d =>
      match d.kind with
      | .SSA =>
        if d.str == GoStr.ofString "flags" then Ty.flags
        else if d.str == GoStr.ofString "vec128" then .blob 16
        else tyOf tabs (fuel + 1) t
      | .TUPLE =>
        match d.tail with
        | .tuple a b => .tuple [tyOfL tabs fuel a, tyOfL tabs fuel b]
        | _ => .other
      | .RESULTS =>
        match d.tail with
        | .results ts => .tuple (ts.toList.map (tyOfL tabs fuel))
        | _ => .other
      | _ => tyOf tabs (fuel + 1) t

/-- The lowered shape of every type of `tabs` (`typeShapes`). -/
def typeShapesL (tabs : Tables) : Array Ty := (List.range tabs.types.size).toArray.map (tyOfL tabs 32)

mutual
/-- `v` read at shape `t` as the register holding it: a narrower integer or a boolean at a wider
integer or a pointer shape is zero-extended, a tuple componentwise; every other value is
unchanged. -/
def Val.widen : Ty → Val → Val
  | .int w', .int w x => if w.bits < w'.bits then .int w' (x.setWidth w'.bits) else .int w x
  | .int w', .bool b => .int w' (if b then 1 else 0)
  | .ptr _, .int w x => if w.bits < 64 then .int .w64 (x.setWidth 64) else .int w x
  | .ptr _, .bool b => .int .w64 (if b then 1 else 0)
  | .tuple ts, .tuple vs => .tuple (Val.widenList ts vs)
  | _, v => v
/-- `Val.widen` componentwise; components beyond the shapes are unchanged. -/
def Val.widenList : List Ty → List Val → List Val
  | t :: ts, v :: vs => Val.widen t v :: Val.widenList ts vs
  | _, vs => vs
end

/-- A value at shape `t` in lowered code: widened as its register (`Val.widen`), then shaped as
in Phase 1 (`Val.retype`). -/
def Val.retypeL (t : Ty) (v : Val) : Val := (v.widen t).retype t

/-! ## Lowered functions -/

/-- The 25 arm64 block kinds. -/
def _root_.GoFV.SSA.BlockKind.isArm64 : BlockKind → Bool
  | .ARM64EQ | .ARM64NE | .ARM64LT | .ARM64LE | .ARM64GT | .ARM64GE | .ARM64ULT | .ARM64ULE
  | .ARM64UGT | .ARM64UGE | .ARM64Z | .ARM64NZ | .ARM64ZW | .ARM64NZW | .ARM64TBZ | .ARM64TBNZ
  | .ARM64FLT | .ARM64FLE | .ARM64FGT | .ARM64FGE | .ARM64LTnoov | .ARM64LEnoov | .ARM64GTnoov
  | .ARM64GEnoov | .ARM64JUMPTABLE => true
  | _ => false

/-- `f` holds an arm64 op or an arm64 block kind. -/
def _root_.GoFV.SSA.Func.lowered (f : Func) : Bool :=
  f.valueTab.any (fun | some v => !v.op.generic | none => false) ||
    f.blockTab.any (fun | some b => b.kind.isArm64 | none => false)

/-- The context of `runL` for `f`: `Ctx.make`'s, with the lowered shapes (`tyOfL`) if `f` is
lowered. -/
def Ctx.makeL (tabs : Tables) (f : Func) : Ctx :=
  let c := Ctx.make tabs f
  if f.lowered then { c with tys := f.valueTab.map (valueTy (typeShapesL tabs)) } else c

/-- How `runL` evaluates: `low`, values are read as registers (`Val.retypeL`; a lowered
function); `faulting`, memory ops fault on the nil page (`runSched`, L1, §6). -/
structure LMode where
  low : Bool
  faulting : Bool

/-- A value at shape `t` under mode `md`. -/
def LMode.retype (md : LMode) (t : Ty) (v : Val) : Val := if md.low then v.retypeL t else v.retype t

/-! ## Lowered arm64 ops that need the activation (§3, §4 (c.4)) -/

/-- Value `u` (of a function whose values are `val?`) holds a sign-extended register: its op
sign-extends (`Arm64.signExtends`), or it is a component (`Select0`/`Select1`) of `LDPSW`, the
pair load `pair` makes of two `MOVWload`s, which `late lower` may already have made `MOVDreg`'s
arguments (`(MOVWreg x:(MOVWload …)) => (MOVDreg x)`, then `pair`). -/
def Arm64.signExtendsIn (val? : ID → Option Value) (u : Value) : Bool :=
  Arm64.signExtends u.op ||
    match u.op with
    | .Select0 | .Select1 => ((u.args[0]?.bind val?).map (·.op == .ARM64LDPSW)).getD false
    | _ => false

/-- `signExtendsIn` reads of `u` its op and, for a `Select0`/`Select1`, the op of its first
argument. -/
theorem Arm64.signExtendsIn_congr {val? val?' : ID → Option Value} {u u' : Value}
    (hop : u.op = u'.op)
    (hsel : (u.op = .Select0 ∨ u.op = .Select1) →
      ((u.args[0]?.bind val?).map (·.op == .ARM64LDPSW)) =
        ((u'.args[0]?.bind val?').map (·.op == .ARM64LDPSW))) :
    Arm64.signExtendsIn val? u = Arm64.signExtendsIn val?' u' := by
  unfold Arm64.signExtendsIn
  rw [hop]
  congr 1
  split
  next h => rw [hsel (Or.inl (hop.trans h))]
  next h => rw [hsel (Or.inr (hop.trans h))]
  next => rfl

/-- The address `base + auxInt + aux` of a `SymOff` op (`MOV*load`, `MOV*store`, `LDP`, `STP`,
`MOVDaddr`, …): the aux's global symbol or frame variable at the offset (the base is then `SB` or
`SP`, `addressing modes`' `mergeSym`), else the base moved by the offset. -/
def symAddr (ctx : Ctx) (v : Value) (base : Val) : Option Ptr :=
  let off := BitVec.ofInt 64 v.auxInt.toInt
  match v.aux with
  | some n =>
    match ctx.tabs.aux? n with
    | some { kind := .sym name .., .. } => some ⟨.global name.toStringLossy, off⟩
    | some { kind := .name .., .. } => some ⟨frameBlk ctx.tabs ctx.act n, off⟩
    | _ => none
  | none => Arm64.addr base off

/-- The element addresses of a pair access (`LDP*`, `STP*`) of `n`-byte elements: `symAddr`
at offsets `auxInt` and `auxInt + n` (the machine's `base + off` and `base + off + n` on an integer
base; the first pointer moved by `n` on a pointer or symbol base). -/
def pairAddr (ctx : Ctx) (v : Value) (n : Nat) (base : Val) : Option (Ptr × Ptr) :=
  (symAddr ctx v base).bind fun p =>
    (symAddr ctx { v with auxInt := v.auxInt + Int64.ofNat n } base).map (p, ·)

theorem pairAddr_eq_some {ctx : Ctx} {v : Value} {n : Nat} {base : Val} {p q : Ptr}
    (h : pairAddr ctx v n base = some (p, q)) :
    symAddr ctx v base = some p ∧
      symAddr ctx { v with auxInt := v.auxInt + Int64.ofNat n } base = some q := by
  unfold pairAddr at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨p', h1, q', h2, rfl, rfl⟩ := h
  exact ⟨h1, h2⟩

/-- `minZeroPage` (`nilcheck.go:192`): the lowest mapped address (`VPre₂`: no allocation below
it), so an access below it is a nil dereference. -/
def minZeroPage : Nat := 4096

/-- An access at `p` faults: `p` points into the unmapped page at address 0. -/
def Ptr.nilFault (p : Ptr) : Bool := p.blk == .nil && decide (p.off.toNat < minZeroPage)

/-- A wild pointer: into the nil block (`Blk.nil`, no allocation) but not nil itself, i.e. an
integer address below the heap or nil moved by an offset. -/
def Ptr.wild (p : Ptr) : Bool := p.blk == .nil && !p.isNil

/-- The accesses of an op that faults on a nil argument (`faultOnNilArg0`/`faultOnNilArg1`, the
facts `late nilcheck` relies on; `LoweredNilCheck` is one, its access at the pointer): for each
such argument, its base (`Arm64.addr a 0`) and its address (for a `SymOff` op with its offset and
symbol, `symAddr`). `LoweredMemEq p q n` (`runtime.memequal`, `internal/bytealg/equal_arm64.s`)
reads only if `n ≠ 0` and `p ≠ q`: none then. -/
def nilAccesses (ctx : Ctx) (v : Value) (argv : List Val) : List (Ptr × Ptr) :=
  let at0 : Option (Ptr × Ptr) := if !v.op.faultOnNilArg0 then none else
    argv.head?.bind fun a => (Arm64.addr a 0).bind fun b =>
      (if v.op.auxType == .SymOff then symAddr ctx v a else some b).map (b, ·)
  let at1 : Option (Ptr × Ptr) := if !v.op.faultOnNilArg1 then none else
    argv[1]?.bind fun a => (Arm64.addr a 0).map fun b => (b, b)
  let reads : Bool := match v.op, argv with
    | .ARM64LoweredMemEq, [_, _, n, _] => Arm64.reg n != some 0 && at0.map (·.2) != at1.map (·.2)
    | _, _ => true
  if reads then at0.toList ++ at1.toList else []

/-- When memory ops fault (`faulting`, `runSched`), the memory of an op that faults on a nil
argument: an access whose base is nil and whose address is in the nil page (a nil
dereference, `nilDeref`). An access through a wild base (`Ptr.wild`) does not fault: the
machine faults with a nil dereference only in the nil page, which a wild base plus an offset
may or may not reach. -/
def nilFaults (faulting : Bool) (ctx : Ctx) (v : Value) (argv : List Val) : Option Mem :=
  if !faulting then none else
  match argv.getLast? with
  | some (.mem m) =>
    if (nilAccesses ctx v argv).any (fun (b, p) => b.isNil && p.nilFault) then some m else none
  | _ => none

/-- The pointer of a nil check (its base, `Arm64.addr p 0`) is wild (`Ptr.wild`). When memory
ops fault such a check is undefined (`stuck`; Go: an invalid `unsafe.Pointer`): `late nilcheck`
replaces a check of `p` by an access at `p + k` (`k < minZeroPage`) and `schedule` moves a check
of `p` before an access at `p + k`, both sound only if the check panics exactly when the access
faults, i.e. when `p` is nil (`nilFaults`). -/
def wildNil (argv : List Val) : Bool :=
  ((argv.head?.bind fun a => Arm64.addr a 0).map Ptr.wild).getD false

/-- A register piece `x` of a lowered call at the shape `t` of the leaf it passes: lowering drops
truncations and zero extensions, so an integer piece may be wider or narrower than its leaf, or a
boolean; the callee reads the register's low bits (`Val.retypeL`), which Phase 1's `encode`
(`decodeArgs`) would make `poison`. Every other piece is unchanged. -/
def fitPiece (t : Ty) (x : Val) : Val :=
  match x, t with
  | .int w _, .int w' => if w == w' then x else x.retypeL t
  | .int w _, .ptr _ => if w == .w64 then x else x.retypeL t
  | .bool _, .int _ | .bool _, .ptr _ => x.retypeL t
  | _, _ => x

/-- The operands of the generic atomic `g` a lowered atomic runs as, fitted to the shape of its
location (`fitPiece`): the instruction uses the register's low bits, and lowering drops
truncations (`(Trunc64to32 x) => (Copy x)`) and zero extensions, so an integer operand may be
wider or narrower than the location; every other operand is unchanged (Phase 1's `encode` reads
it as the generic atomic does). -/
def atomicArgs (g : Op) (argv : List Val) : List Val :=
  match argv, Atomic.info? g, Atomic.casWidth? g with
  | [a, x, m], some (_, t), _ => [a, fitPiece t x, m]
  | [a, o, n, m], _, some w => [a, fitPiece (.int w) o, fitPiece (.int w) n, m]
  | _, _, _ => argv

/-- The register pieces `pieces` of a lowered call's input parameters (`decodeArgs`' order) at
their leaves' shapes (`fitPiece`); the memory and any piece beyond the register parameters'
leaves are unchanged. -/
def fitPieces (tabs : Tables) : List ABIParam → List Val → List Val
  | [], pieces => pieces
  | p :: ps, pieces =>
    if p.regs.isEmpty then fitPieces tabs ps pieces
    else
      let k := p.regs.size
      let ls := leaves (tabs.ty p.type)
      (pieces.take k).mapIdx (fun i x => match ls[i]? with
        | some (_, t) => fitPiece t x
        | none => x) ++ fitPieces tabs ps (pieces.drop k)

/-- The arm64 ops evaluated with the activation: `SymOff` loads and stores, indexed stores,
`MOVDaddr`, `MOVDreg`/`MOVDnop`, the closure pointer and caller SP, calls, nil checks, bounds
panics, `LoweredMemEq`, atomics, `DMB`, `PRFM`. Each is Phase 1's meaning of the generic op it
lowers (calls, nil checks, atomics run as that op; `memRoot`/`callOp`/`atomicRoot`), or an access
on the Phase 1 memory (`Sem/Arm64/Mem.lean`). A load is pure (`poison` on an invalid access), a
store `stuck` on an invalid one, as Phase 1's `Load`/`Store`. A pair access (`LDP*`, `STP*`)
addresses its elements by `pairAddr` (semantics2.md, #156).

`MOVDreg x`/`MOVDnop x` copy `x`'s register; when `x` has a narrow type its upper bits are those
of its producer (`Arm64.signExtendsIn`: a sign-extending load or extension, or a component of the
sign-extending pair load `LDPSW`; otherwise zero, the
invariant of every rule that drops an extension, `ZeroUpper32Bits` and the boolean producers).

The other memory ops (`LDAR*`, `LoweredZero`/`LoweredMove` and their loops) are
`Arm64.evalPure`'s; they are here for `nilFaults`, which makes every op that faults on a nil
argument a `nilDeref` panic on a nil base in the nil page when memory ops fault (`runSched`)
and changes nothing otherwise. A nil check of a wild pointer is then `stuck` (`wildNil`). -/
def arm64Op (faulting : Bool) (env : Env) (ctx : Ctx) (fr : Frame) (v : Value) (argv : List Val)
    (ty : Ty) : Res Val :=
  let what := s!"v{v.id}: {v.op.name}"
  let ld (n : Nat) (signed : Bool) : Res Val := match argv with
    | [a, .mem m] => .ok ((symAddr ctx v a).elim .poison (Arm64.loadN ty n signed m))
    | _ => .ok .poison
  let ldPair (n : Nat) (signed : Bool) : Res Val := match argv with
    | [a, .mem m] => .ok ((pairAddr ctx v n a).elim .poison fun pq =>
      Arm64.loadPair ty n signed m pq.1 pq.2)
    | _ => .ok .poison
  let ld16 : Res Val := match argv with
    | [a, .mem m] => .ok ((symAddr ctx v a).elim .poison (Arm64.load16 m))
    | _ => .ok .poison
  let bad : Res Val :=
    if argv.any (fun | .poison => true | _ => false) then .stuck s!"{what}: poison argument"
    else .stuck s!"{what}: undefined or ill-typed arguments"
  let st (n : Nat) : Res Val := match argv with
    | [a, x, .mem m] => match symAddr ctx v a with
      | some p => writeRes what (Arm64.storeN n p x m)
      | none => bad
    | _ => bad
  let stPair (n : Nat) : Res Val := match argv with
    | [a, x, y, .mem m] => match pairAddr ctx v n a with
      | some (p, q) => writeRes what (Arm64.storePair n p q x y m)
      | none => bad
    | _ => bad
  let stIdx (n scale : Nat) : Res Val := match argv with
    | [a, i, x, .mem m] =>
      let s := if scale = 1 then Arm64.add .other [a, i] else
        match Arm64.reg i with
        | some k => Arm64.add .other [a, .int .w64 (k * BitVec.ofNat 64 scale)]
        | none => .poison
      match Arm64.addr s 0 with
      | some p => writeRes what (Arm64.storeN n p x m)
      | none => bad
    | _ => bad
  let pbc (n : Option AuxRef) : Option Int := match n.bind ctx.tabs.aux? with
    | some { kind := .pbc c, .. } => some c
    | _ => none
  let pbcc (n : Option AuxRef) : Option (Int × Int) := match n.bind ctx.tabs.aux? with
    | some { kind := .pbcc cx cy, .. } => some (cx, cy)
    | _ => none
  let gen (op : Op) : Value := { v with op }
  -- a call whose first `k` arguments are not register pieces (closure code and context, code)
  let call (op : Op) (k : Nat) : Res Val :=
    let ins := ((callABI? ctx.tabs v.aux).map (·.params.toList.filter (!·.out))).getD []
    callOp env ctx (gen op) (argv.take k ++ fitPieces ctx.tabs ins (argv.drop k))
  match nilFaults faulting ctx v argv with
  | some m => .panic .nilDeref m
  | none =>
  match v.op with
  | .ARM64MOVBload => ld 1 true
  | .ARM64MOVBUload => ld 1 false
  | .ARM64MOVHload => ld 2 true
  | .ARM64MOVHUload => ld 2 false
  | .ARM64MOVWload => ld 4 true
  | .ARM64MOVWUload => ld 4 false
  | .ARM64MOVDload => ld 8 false
  | .ARM64FMOVSload => ld 4 false
  | .ARM64FMOVDload => ld 8 false
  | .ARM64FMOVQload => ld16
  | .ARM64LDP => ldPair 8 false
  | .ARM64LDPW => ldPair 4 false
  | .ARM64LDPSW => ldPair 4 true
  | .ARM64FLDPD => ldPair 8 false
  | .ARM64FLDPS => ldPair 4 false
  | .ARM64FLDPQ => ldPair 16 false
  | .ARM64MOVBstore => st 1
  | .ARM64MOVHstore => st 2
  | .ARM64MOVWstore => st 4
  | .ARM64MOVDstore => st 8
  | .ARM64FMOVSstore => st 4
  | .ARM64FMOVDstore => st 8
  | .ARM64FMOVQstore => st 16
  | .ARM64STP => stPair 8
  | .ARM64STPW => stPair 4
  | .ARM64FSTPD => stPair 8
  | .ARM64FSTPS => stPair 4
  | .ARM64FSTPQ => stPair 16
  | .ARM64MOVBstoreidx => stIdx 1 1
  | .ARM64MOVHstoreidx => stIdx 2 1
  | .ARM64MOVWstoreidx => stIdx 4 1
  | .ARM64MOVDstoreidx => stIdx 8 1
  | .ARM64FMOVSstoreidx => stIdx 4 1
  | .ARM64FMOVDstoreidx => stIdx 8 1
  | .ARM64MOVHstoreidx2 => stIdx 2 2
  | .ARM64MOVWstoreidx4 => stIdx 4 4
  | .ARM64MOVDstoreidx8 => stIdx 8 8
  | .ARM64FMOVSstoreidx4 => stIdx 4 4
  | .ARM64FMOVDstoreidx8 => stIdx 8 8
  | .ARM64MOVDaddr => match argv with
    | [a] => .ok ((symAddr ctx v a).elim .poison PtrOps.ptrRes)
    | _ => .ok .poison
  | .ARM64MOVDreg | .ARM64MOVDnop => match argv with
    | [a] =>
      let sx := ((v.args[0]?.bind ctx.f.value?).map (Arm64.signExtendsIn ctx.f.value?)).getD false
      match a with
      | .int w x => .ok (Arm64.res ty (if sx then x.signExtend 64 else x.setWidth 64))
      | a => .ok (Arm64.regVal ty a)
    | _ => .ok .poison
  | .ARM64LoweredGetClosurePtr => .ok (fr.closure.getD .poison)
  | .ARM64LoweredGetCallerSP => .ok ((frameVal ctx (gen .GetCallerSP)).getD .poison)
  | .ARM64CALLstatic => call .StaticCall 0
  | .ARM64CALLclosure => call .ClosureCall 2
  | .ARM64CALLinter => call .InterCall 1
  | .ARM64LoweredNilCheck =>
    if faulting && wildNil argv then .stuck s!"{what}: nil check of a wild pointer"
    else memRoot ctx (gen .NilCheck) argv
  | .ARM64LoweredPanicBoundsRR => panicBounds v.auxInt argv
  | .ARM64LoweredPanicBoundsRC => match argv, pbc v.aux with
    | [x, m], some c => panicBounds v.auxInt [x, .i64 (BitVec.ofInt 64 c), m]
    | _, _ => bad
  | .ARM64LoweredPanicBoundsCR => match argv, pbc v.aux with
    | [y, m], some c => panicBounds v.auxInt [.i64 (BitVec.ofInt 64 c), y, m]
    | _, _ => bad
  | .ARM64LoweredPanicBoundsCC => match argv, pbcc v.aux with
    | [m], some (cx, cy) =>
      panicBounds v.auxInt [.i64 (BitVec.ofInt 64 cx), .i64 (BitVec.ofInt 64 cy), m]
    | _, _ => bad
  | .ARM64LoweredMemEq => .ok (memEq argv)
  | .ARM64DMB => match argv with
    | [.mem m] => .ok (.mem m)
    | _ => bad
  | .ARM64PRFM => match argv with
    | [_, .mem m] => .ok (.mem m)
    | _ => bad
  | op => match Arm64.atomicOf op with
    | some g => atomicRoot (gen g) (atomicArgs g argv)
    | none => .ok (Arm64.evalPure op ty v.auxInt v.aux argv)

/-! ## The runner -/

/-- The result of value `v` before it takes its shape: Phase 1's `evalOp` for a generic op; for
an arm64 op `arm64Op` (the ops that need the activation, and the memory ops that fault), else
`atomicRoot` for a root (`unmodelled`), else `Arm64.evalPure`. -/
def evalOpL (faulting : Bool) (env : Env) (ctx : Ctx) (fr : Frame) (v : Value) (argv : List Val)
    (ty : Ty) : Res Val :=
  if v.op.generic then evalOp env ctx fr v argv ty else
  match v.op with
  | .ARM64MOVBload | .ARM64MOVBUload | .ARM64MOVHload | .ARM64MOVHUload | .ARM64MOVWload
  | .ARM64MOVWUload | .ARM64MOVDload | .ARM64FMOVSload | .ARM64FMOVDload | .ARM64FMOVQload
  | .ARM64LDP | .ARM64LDPW | .ARM64LDPSW | .ARM64FLDPD | .ARM64FLDPS | .ARM64FLDPQ
  | .ARM64MOVBstore | .ARM64MOVHstore | .ARM64MOVWstore | .ARM64MOVDstore | .ARM64FMOVSstore
  | .ARM64FMOVDstore | .ARM64FMOVQstore | .ARM64STP | .ARM64STPW | .ARM64FSTPD | .ARM64FSTPS
  | .ARM64FSTPQ | .ARM64MOVBstoreidx | .ARM64MOVHstoreidx | .ARM64MOVWstoreidx
  | .ARM64MOVDstoreidx | .ARM64FMOVSstoreidx | .ARM64FMOVDstoreidx | .ARM64MOVHstoreidx2
  | .ARM64MOVWstoreidx4 | .ARM64MOVDstoreidx8 | .ARM64FMOVSstoreidx4 | .ARM64FMOVDstoreidx8
  | .ARM64MOVDaddr | .ARM64MOVDreg | .ARM64MOVDnop | .ARM64LoweredGetClosurePtr
  | .ARM64LoweredGetCallerSP | .ARM64CALLstatic | .ARM64CALLclosure | .ARM64CALLinter
  | .ARM64LoweredNilCheck | .ARM64LoweredPanicBoundsRR | .ARM64LoweredPanicBoundsRC
  | .ARM64LoweredPanicBoundsCR | .ARM64LoweredPanicBoundsCC | .ARM64LoweredMemEq | .ARM64DMB
  | .ARM64PRFM | .ARM64STLRB | .ARM64STLRW | .ARM64STLR | .ARM64LoweredAtomicExchange8
  | .ARM64LoweredAtomicExchange32 | .ARM64LoweredAtomicExchange64
  | .ARM64LoweredAtomicExchange8Variant | .ARM64LoweredAtomicExchange32Variant
  | .ARM64LoweredAtomicExchange64Variant | .ARM64LoweredAtomicAdd32 | .ARM64LoweredAtomicAdd64
  | .ARM64LoweredAtomicAdd32Variant | .ARM64LoweredAtomicAdd64Variant
  | .ARM64LoweredAtomicCas32 | .ARM64LoweredAtomicCas64 | .ARM64LoweredAtomicCas32Variant
  | .ARM64LoweredAtomicCas64Variant | .ARM64LoweredAtomicAnd8 | .ARM64LoweredAtomicAnd32
  | .ARM64LoweredAtomicAnd64 | .ARM64LoweredAtomicOr8 | .ARM64LoweredAtomicOr32
  | .ARM64LoweredAtomicOr64 | .ARM64LoweredAtomicAnd8Variant | .ARM64LoweredAtomicAnd32Variant
  | .ARM64LoweredAtomicAnd64Variant | .ARM64LoweredAtomicOr8Variant
  | .ARM64LoweredAtomicOr32Variant | .ARM64LoweredAtomicOr64Variant | .ARM64LDAR | .ARM64LDARB
  | .ARM64LDARW | .ARM64LoweredZero | .ARM64LoweredZeroLoop | .ARM64LoweredMove
  | .ARM64LoweredMoveLoop =>
    arm64Op faulting env ctx fr v argv ty
  | op =>
    if isRoot op then atomicRoot v argv
    else pure (Arm64.evalPure op ty v.auxInt v.aux argv)

/-- `evalValue` under mode `md`: the result of `evalOpL` at the value's shape (`LMode.retype`). -/
def evalValueL (md : LMode) (env : Env) (ctx : Ctx) (fr : Frame) (v : Value) : Res Val := do
  let argv ← v.args.toList.mapM fun a =>
    Res.ofOption s!"v{v.id}: argument v{a} has no value" (fr.regs[a]?).join
  let ty := ctx.tys[v.id]?.getD .other
  let r ← evalOpL md.faulting env ctx fr v argv ty
  pure (md.retype ty r)

/-- `evalAll` under mode `md`. -/
def evalAllL (md : LMode) (env : Env) (ctx : Ctx) (fr : Frame) : List ID → Res Frame
  | [] => .ok fr
  | id :: ids =>
    match ctx.f.value? id with
    | none => .stuck s!"v{id} is not in the function"
    | some v =>
      match evalValueL md env ctx fr v with
      | .ok x => evalAllL md env ctx { fr with regs := fr.regs.set! id (some x) } ids
      | .panic e m => .panic e m
      | .stuck msg => .stuck msg

/-- `enterBlock` under mode `md` (the `Phi`s take their arguments at their shapes,
`LMode.retype`). -/
def enterBlockL (md : LMode) (env : Env) (ctx : Ctx) (fr : Frame) (b : Block) (i : Nat) :
    Res Frame := do
  let phis ← b.values.toList.filterMapM fun id =>
    match ctx.f.value? id with
    | some v =>
      if v.op == .Phi then
        match v.args[i]? with
        | some a =>
          match (fr.regs[a]?).join with
          | some x => .ok (some (id, md.retype (ctx.tys[id]?.getD .other) x))
          | none => .stuck s!"phi v{id}: argument v{a} has no value"
        | none => .stuck s!"phi v{id}: no argument {i}"
      else .ok none
    | none => .stuck s!"v{id} is not in the function"
  let fr := { fr with regs := phis.foldl (fun r (id, x) => r.set! id (some x)) fr.regs }
  let order ← Res.ofOption s!"b{b.id}: cyclic values" (ctx.sched[b.id]?).join
  evalAllL md env ctx fr order.toList

/-- The terminator of `b`: an arm64 kind (§5) branches on its flags or register control (a
`poison` control is `stuck`, as `If`'s), a generic kind is Phase 1's `stepTerm`. -/
def stepTermL (fr : Frame) (b : Block) : Res Next :=
  if b.kind.isArm64 then
    match b.kind with
    | .ARM64JUMPTABLE => do
      match Arm64.reg (← control fr b 0) with
      | some x => succ b x.toNat
      | none => .stuck s!"b{b.id}: JUMPTABLE on poison or non-int"
    | k => do
      match Arm64.taken k b.auxInt (← control fr b 0) with
      | some true => succ b 0
      | some false => succ b 1
      | none => .stuck s!"b{b.id}: {k.name} on poison or an ill-typed control"
  else stepTerm fr b

/-- `runLoop` under mode `md`. -/
def runLoopL (md : LMode) (env : Env) (ctx : Ctx) : Nat → Frame → ID → Nat → Outcome
  | 0, _, _, _ => .outOfFuel
  | fuel + 1, fr, bid, i =>
    match ctx.f.block? bid with
    | none => .stuck s!"b{bid} is not in the function"
    | some b =>
      match enterBlockL md env ctx fr b i with
      | .panic e m => .panicked e m
      | .stuck msg => .stuck msg
      | .ok fr =>
        match stepTermL fr b with
        | .ok (.goto e) => runLoopL md env ctx fuel fr e.b e.i
        | .ok (.ret rs m) => .returned rs m
        | .panic e m => .panicked e m
        | .stuck msg => .stuck msg

/-- `runCtx` under mode `md`. -/
def runCtxL (md : LMode) (env : Env) (ctx : Ctx) (args : List Val) (mem : Mem) (fuel : Nat) :
    Outcome :=
  if args.length != ctx.params.size then
    .stuck s!"{args.length} arguments for {ctx.params.size} parameters"
  else
    finish env ctx.outs ctx.defers ctx.act
      (runLoopL md env ctx fuel (entryFrame env ctx args mem) ctx.f.entry 0)

/-! ## On generic code `runL` is `run` -/

theorem _root_.GoFV.SSA.Func.generic_of_lowered {f : Func} (h : f.lowered = false) {id : ID}
    {v : Value} (hv : f.value? id = some v) : v.op.generic = true := by
  simp only [Func.lowered, Bool.or_eq_false_iff] at h
  simp only [Func.value?, Option.join_eq_some_iff, Array.getElem?_eq_some_iff] at hv
  obtain ⟨hlt, hv⟩ := hv
  have := Array.any_eq_false.1 h.1 id hlt
  rw [hv] at this
  simpa using this

theorem _root_.GoFV.SSA.Func.notArm64_of_lowered {f : Func} (h : f.lowered = false) {id : ID}
    {b : Block} (hb : f.block? id = some b) : b.kind.isArm64 = false := by
  simp only [Func.lowered, Bool.or_eq_false_iff] at h
  simp only [Func.block?, Option.join_eq_some_iff, Array.getElem?_eq_some_iff] at hb
  obtain ⟨hlt, hb⟩ := hb
  have := Array.any_eq_false.1 h.2 id hlt
  rw [hb] at this
  simpa using this

theorem evalOpL_generic (faulting : Bool) (env : Env) (ctx : Ctx) (fr : Frame) {v : Value}
    (argv : List Val) (ty : Ty) (hg : v.op.generic = true) :
    evalOpL faulting env ctx fr v argv ty = evalOp env ctx fr v argv ty := by
  simp only [evalOpL, hg, ite_true]

theorem evalValueL_generic {md : LMode} (hlow : md.low = false) (env : Env) (ctx : Ctx)
    (fr : Frame) {v : Value} (hg : v.op.generic = true) :
    evalValueL md env ctx fr v = evalValue env ctx fr v := by
  simp only [evalValueL, evalValue, evalOpL_generic _ _ _ _ _ _ hg, LMode.retype, hlow,
    Bool.false_eq_true, ite_false]

theorem evalAllL_generic {md : LMode} (hlow : md.low = false) (env : Env) (ctx : Ctx)
    (hv : ∀ id v, ctx.f.value? id = some v → v.op.generic = true) :
    ∀ (ids : List ID) (fr : Frame), evalAllL md env ctx fr ids = evalAll env ctx fr ids
  | [], _ => rfl
  | id :: ids, fr => by
    simp only [evalAllL, evalAll]
    cases hval : ctx.f.value? id with
    | none => rfl
    | some v =>
      dsimp only
      rw [evalValueL_generic hlow env ctx fr (hv id v hval)]
      cases evalValue env ctx fr v with
      | ok x => exact evalAllL_generic hlow env ctx hv ids _
      | panic e m => rfl
      | stuck msg => rfl

theorem enterBlockL_generic {md : LMode} (hlow : md.low = false) (env : Env) (ctx : Ctx)
    (hv : ∀ id v, ctx.f.value? id = some v → v.op.generic = true) (fr : Frame) (b : Block)
    (i : Nat) : enterBlockL md env ctx fr b i = enterBlock env ctx fr b i := by
  simp only [enterBlockL, enterBlock, LMode.retype, hlow, Bool.false_eq_true, ite_false,
    evalAllL_generic hlow env ctx hv]
  rfl

theorem stepTermL_generic (fr : Frame) {b : Block} (hb : b.kind.isArm64 = false) :
    stepTermL fr b = stepTerm fr b := by
  simp only [stepTermL, hb, Bool.false_eq_true, ite_false]

theorem runLoopL_generic {md : LMode} (hlow : md.low = false) (env : Env) (ctx : Ctx)
    (hv : ∀ id v, ctx.f.value? id = some v → v.op.generic = true)
    (hb : ∀ id b, ctx.f.block? id = some b → b.kind.isArm64 = false) :
    ∀ (fuel : Nat) (fr : Frame) (bid : ID) (i : Nat),
      runLoopL md env ctx fuel fr bid i = runLoop env ctx fuel fr bid i
  | 0, _, _, _ => rfl
  | fuel + 1, fr, bid, i => by
    rw [runLoop_succ]
    simp only [runLoopL]
    cases hblk : ctx.f.block? bid with
    | none => rfl
    | some b =>
      dsimp only
      rw [enterBlockL_generic hlow env ctx hv]
      cases enterBlock env ctx fr b i with
      | panic e m => rfl
      | stuck msg => rfl
      | ok fr' =>
        dsimp only
        rw [stepTermL_generic fr' (hb bid b hblk)]
        cases stepTerm fr' b with
        | ok n =>
          cases n with
          | goto e => exact runLoopL_generic hlow env ctx hv hb fuel _ _ _
          | ret rs m => rfl
        | panic e m => rfl
        | stuck msg => rfl

theorem Ctx.makeL_of_generic {tabs : Tables} {f : Func} (h : f.lowered = false) :
    Ctx.makeL tabs f = Ctx.make tabs f := by
  simp only [Ctx.makeL, h, Bool.false_eq_true, ite_false]

end GoFV.SSA.Sem

namespace GoFV.SSA

/-- `GoFV.SSA.runL`: the outcome of running lowered `f` (L0: `lower` … `layout`) on `args` from
memory `mem` with at most `fuel` block entries. -/
def runL (env : Sem.Env) (tabs : Tables) (f : Func) (args : List Sem.Val) (mem : Sem.Mem)
    (fuel : Nat) : Sem.Outcome :=
  Sem.runCtxL ⟨f.lowered, false⟩ env (Sem.Ctx.makeL tabs f) args mem fuel

/-- **`runL` extends `run`**: on a function with no arm64 op and no arm64 block kind, `runL` is
Phase 1's `run` (`docs/plans/semantics2.md` §1). -/
theorem runL_generic (env : Sem.Env) (tabs : Tables) {f : Func} (h : f.lowered = false)
    (args : List Sem.Val) (mem : Sem.Mem) (fuel : Nat) :
    runL env tabs f args mem fuel = run env tabs f args mem fuel := by
  simp only [runL, run, Sem.runCtxL, Sem.runCtx, Sem.Ctx.makeL_of_generic h, h]
  rw [Sem.runLoopL_generic rfl env _ (fun _ _ hv => Func.generic_of_lowered h hv)
    (fun _ _ hb => Func.notArm64_of_lowered h hb)]

end GoFV.SSA

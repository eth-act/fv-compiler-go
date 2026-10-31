import GoFV.Opt.Pass
import GoFV.SSA.ConstCache
import GoFV.SSA.Analysis.CfgCache
import GoFV.Rules.Helpers.Types

/-!
# known bits (`known_bits.go`)

Abstract interpretation over a `(value, known)` bit lattice per value (`docs/PASSES.md`, known
bits): blocks in reverse `f.postorder()` (the cached one), values in `b.Values` order (a
snapshot: constants appended to `f.Entry` are not visited), skipping unused values, non-integer
non-boolean ones and constants; `fold` is memoised by value ID and marks a value seen *before*
recursing, so a value reached again inside a cycle reads its zero entry ("nothing known"). A
value whose bits are all known becomes a `Copy` of the cached constant `f.ConstX(v.Type, val)`.

Arithmetic is Go's `int64`: shifts by ≥ 64 give 0 (left, unsigned right) or the sign fill
(signed right), unlike Lean's shifts modulo 64 (`shl`, `sar`, `shrU`). Panics (unknown block
kind or type size) are errors.
-/

namespace GoFV.Opt

open GoFV.SSA

namespace KnownBits

/-- Go's `x << s` for `int64` with `0 ≤ s`. -/
@[inline] def shl (x : Int64) (s : Int64) : Int64 := if s ≥ 64 then 0 else x <<< s
/-- Go's `x >> s` for `int64` (arithmetic) with `0 ≤ s`. -/
@[inline] def sar (x : Int64) (s : Int64) : Int64 :=
  if s ≥ 64 then (if x < 0 then -1 else 0) else x >>> s
/-- Go's `x >> s` for `uint64` with `0 ≤ s`. -/
@[inline] def shrU (x : UInt64) (s : Int64) : UInt64 := if s ≥ 64 then 0 else x >>> s.toUInt64
/-- Go's `x << s` for `uint64` with `0 ≤ s`. -/
@[inline] def shlU (x : UInt64) (s : Int64) : UInt64 := if s ≥ 64 then 0 else x <<< s.toUInt64

/-- A `doShiftByAConst` function: `(x, xk, xSize, shift) ↦ (value, known)`. -/
abbrev ShiftFn := Int64 → Int64 → Int64 → Int64 → Int64 × Int64

def lshFn : ShiftFn := fun x xk _ s => (shl x s, shl xk s ||| (shl 1 s - 1))

def rshuFn : ShiftFn := fun x xk xSize s =>
  let x := x &&& (shl 1 xSize - 1)
  let xk := xk ||| shl (-1) xSize
  ((shrU x.toUInt64 s).toInt64,
   (shrU xk.toUInt64 s ||| shlU (~~~(0 : UInt64)) (64 - s)).toInt64)

def rshFn : ShiftFn := fun x xk _ s => (sar x s, sar xk s)

/-- The phi-style meet of `(value, known)` with `(a, k)`. -/
@[inline] def meet (value known a k : Int64) : Int64 :=
  (known &&& ~~~(value ^^^ a)) &&& k

/-- `allPossibleValues(value, known)` folded with `step` until it returns `false` (Go's
`yield`). At most `2^popcount(^known)` iterations; callers pass `known` with at most 6 unknown
bits, so 65 steps suffice. -/
def allPossibleValues {σ} (value known : Int64) (st : σ) (step : σ → Int64 → σ × Bool) : σ :=
  let unknown := ~~~known
  go unknown 65 0 st
where
  go (unknown : Int64) : Nat → Int64 → σ → σ
    | 0, _, st => st
    | fuel + 1, s, st =>
      let (st, cont) := step st (value ||| s)
      if !cont || s == unknown then st
      else go unknown fuel ((s - unknown) &&& unknown) st

/-- The shift transfer function after both operands are folded
(`computeKnownBitsForShift`, from the comparison of `y` on). -/
def shiftResult (doShift : ShiftFn) (auxInt x xk xSize y yk : Int64) : Int64 × Int64 :=
  if y.toUInt64 ≥ xSize.toUInt64 then doShift x xk xSize 64 else
  let init : Option (Int64 × Int64) :=
    if auxInt == 0 && (~~~yk).toUInt64 ≥ xSize.toUInt64 then some (doShift x xk xSize 64)
    else none
  let yk := yk ||| ~~~(xSize - 1)
  let r := allPossibleValues y yk init fun st i =>
    let (a, k) := doShift x xk xSize i
    let (value, known) := match st with
      | none => (a, k)
      | some (value, known) => (value, meet value known a k)
    (some (value, known), known != 0)
  let (value, known) := r.getD (0, 0)
  (value &&& known, known)

/-- The analysis state: `entries` (value, known) and `seenValues`, by value ID. -/
structure St where
  entries : Array (Int64 × Int64)
  seen : Array Bool

abbrev M := StateT St (Except String)

/-- What `fold` reads: the function, its tables and `reachableBlocks`. -/
structure Ctx where
  f : Func
  tabs : Tables
  reachable : Array Bool

/-- `isLiveOutEdge(b, index)`. -/
def isLiveOutEdge (c : Ctx) (b : ID) (index : Nat) : Except String Bool :=
  if !c.reachable.getD b false then pure false else
  match (c.f.getB b).kind with
  | .First => pure (index == 0)
  | .Plain | .If | .Defer | .Ret | .RetJmp | .Exit | .JumpTable => pure true
  | k => throw s!"known bits: unknown block kind {k.name}"

/-- `isLiveInEdge(b, index)`. -/
def isLiveInEdge (c : Ctx) (b : ID) (index : Nat) : Except String Bool :=
  match (c.f.getB b).preds[index]? with
  | some e => isLiveOutEdge c e.b e.i
  | none => throw s!"known bits: b{b} has no pred {index}"

/-- The deferred normalisation of `fold`: booleans keep bit 0, sign-extension from the type's
size, unknown bits cleared; then the entry is stored. -/
def finish (c : Ctx) (v : ID) (r : Int64 × Int64) : M (Int64 × Int64) := do
  let t := (c.f.getV v).type
  let (value, known) := r
  let (value, known) :=
    if (← Rules.Ty.kind c.tabs t) == .BOOL then (value &&& 1, known ||| ~~~1) else (value, known)
  let (value, known) ← match ← Rules.Ty.size c.tabs t with
    | 1 => pure (value.toInt8.toInt64, known.toInt8.toInt64)
    | 2 => pure (value.toInt16.toInt64, known.toInt16.toInt64)
    | 4 => pure (value.toInt32.toInt64, known.toInt32.toInt64)
    | 8 => pure (value, known)
    | n => throw s!"known bits: v{v}: unknown integer size {n}"
  let value := value &&& known
  modify fun s => { s with entries := s.entries.set! v (value, known) }
  return (value, known)

/-- `kb.fold(v)`. Each call that recurses marks a new value seen first, so the recursion depth
is at most the number of values (`fuel`). -/
def fold (c : Ctx) : Nat → ID → M (Int64 × Int64)
  | 0, v => throw s!"known bits: fold fuel exhausted at v{v}"
  | fuel + 1, v => do
    let s ← get
    if s.seen.getD v false then return s.entries.getD v (0, 0)
    set { s with seen := s.seen.set! v true }
    let x := c.f.getV v
    let arg (i : Nat) : M (Int64 × Int64) := fold c fuel x.args[i]!
    -- `computeKnownBitsForShift(v, doShift)`
    let shift (doShift : ShiftFn) : M (Int64 × Int64) := do
      let xSize := Int64.ofInt ((← Rules.Ty.size c.tabs (c.f.getV x.args[0]!).type) * 8)
      let (a, ak) ← arg 0
      let (y, yk) ← arg 1
      return shiftResult doShift x.auxInt a ak xSize y yk
    let r : Int64 × Int64 ← match x.op with
      | .Const64 | .Const32 | .Const16 | .Const8 | .ConstBool => pure (x.auxInt, -1)
      | .And64 | .And32 | .And16 | .And8 | .AndB => do
        let (a, ak) ← arg 0
        let (b, bk) ← arg 1
        pure (a &&& b, (a &&& b) ||| (~~~a &&& ak) ||| (~~~b &&& bk))
      | .Or64 | .Or32 | .Or16 | .Or8 | .OrB => do
        let (a, ak) ← arg 0
        let (b, bk) ← arg 1
        pure (a ||| b, a ||| b ||| (~~~a &&& ~~~b &&& (ak &&& bk)))
      | .Xor64 | .Xor32 | .Xor16 | .Xor8 => do
        let (a, ak) ← arg 0
        let (b, bk) ← arg 1
        pure (a ^^^ b, ak &&& bk)
      | .Com64 | .Com32 | .Com16 | .Com8 | .Not => do
        let (a, ak) ← arg 0
        pure (~~~a, ak)
      | .Phi => do
        let mut acc : Option (Int64 × Int64) := none
        for h : i in [0:x.args.size] do
          if !(← isLiveInEdge c x.block i) then continue
          let (a, k) ← fold c fuel x.args[i]
          let (value, known) := match acc with
            | none => (a, k)
            | some (value, known) => (value, meet value known a k)
          acc := some (value, known)
          if known == 0 then break
        pure (acc.getD (0, 0))
      | .Copy | .CvtBoolToUint8
      | .SignExt8to16 | .SignExt8to32 | .SignExt8to64 | .SignExt16to32 | .SignExt16to64
      | .SignExt32to64
      | .Trunc64to32 | .Trunc64to16 | .Trunc64to8 | .Trunc32to16 | .Trunc32to8
      | .Trunc16to8 => arg 0
      | .Eq64 | .Eq32 | .Eq16 | .Eq8 | .EqB => do
        let (a, ak) ← arg 0
        let (b, bk) ← arg 1
        if (a ^^^ b) &&& ak &&& bk != 0 then pure (0, -1)
        else if ak == -1 && bk == -1 then pure (if a == b then 1 else 0, -1)
        else pure (0, -2)
      | .Neq64 | .Neq32 | .Neq16 | .Neq8 | .NeqB => do
        let (a, ak) ← arg 0
        let (b, bk) ← arg 1
        if (a ^^^ b) &&& ak &&& bk != 0 then pure (1, -1)
        else if ak == -1 && bk == -1 then pure (if a != b then 1 else 0, -1)
        else pure (0, -2)
      | .ZeroExt8to16 | .ZeroExt8to32 | .ZeroExt8to64 | .ZeroExt16to32 | .ZeroExt16to64
      | .ZeroExt32to64 => do
        let (a, k) ← arg 0
        let srcSize := (← Rules.Ty.size c.tabs (c.f.getV x.args[0]!).type) * 8
        let mask := shl 1 (Int64.ofInt srcSize) - 1
        pure (a &&& mask, k ||| ~~~mask)
      | .Lsh8x8 | .Lsh16x8 | .Lsh32x8 | .Lsh64x8
      | .Lsh8x16 | .Lsh16x16 | .Lsh32x16 | .Lsh64x16
      | .Lsh8x32 | .Lsh16x32 | .Lsh32x32 | .Lsh64x32
      | .Lsh8x64 | .Lsh16x64 | .Lsh32x64 | .Lsh64x64 => shift lshFn
      | .Rsh8Ux8 | .Rsh16Ux8 | .Rsh32Ux8 | .Rsh64Ux8
      | .Rsh8Ux16 | .Rsh16Ux16 | .Rsh32Ux16 | .Rsh64Ux16
      | .Rsh8Ux32 | .Rsh16Ux32 | .Rsh32Ux32 | .Rsh64Ux32
      | .Rsh8Ux64 | .Rsh16Ux64 | .Rsh32Ux64 | .Rsh64Ux64 => shift rshuFn
      | .Rsh8x8 | .Rsh16x8 | .Rsh32x8 | .Rsh64x8
      | .Rsh8x16 | .Rsh16x16 | .Rsh32x16 | .Rsh64x16
      | .Rsh8x32 | .Rsh16x32 | .Rsh32x32 | .Rsh64x32
      | .Rsh8x64 | .Rsh16x64 | .Rsh32x64 | .Rsh64x64 => shift rshFn
      | _ => pure (0, 0)
    finish c v r

/-- `f.ConstX(t, val)` for an integer or boolean type of size `size`. -/
def mkConst (f : Func) (eq : TypeRef → TypeRef → Bool) (t : TypeRef) (isBool : Bool)
    (size : Int) (val : Int64) : Except String (Func × ID) :=
  match size with
  | 1 => if isBool then pure (f.constBool eq t (val != 0)) else pure (f.constInt8 eq t val.toInt8)
  | 2 => pure (f.constInt16 eq t val.toInt16)
  | 4 => pure (f.constInt32 eq t val.toInt32)
  | 8 => pure (f.constInt64 eq t val)
  | n => throw s!"known bits: unknown integer size {n}"

end KnownBits

open KnownBits in
/-- `knownBits(f)`. -/
def knownBits (tabs : Tables) (order : TypeOrder) (f : Func) : Except String Func := do
  let (po, f) := f.postorder
  let reachable := po.foldl (fun r b => r.set! b true) (Array.replicate (f.bidLast + 1) false)
  let n := f.vidLast + 1
  let mut st : St := { entries := Array.replicate n (0, 0), seen := Array.replicate n false }
  let mut f := f
  for k in [0:po.size] do
    let b := po[po.size - 1 - k]!
    for v in (f.getB b).values do
      let x := f.getV v
      if x.uses == 0 then continue
      let kind ← Rules.Ty.kind tabs x.type
      let isBool := kind == .BOOL
      if !(Rules.Ty.isIntegerKind kind || isBool) then continue
      match x.op with
      | .Const64 | .Const32 | .Const16 | .Const8 | .ConstBool => continue
      | _ => pure ()
      let c : Ctx := { f, tabs, reachable }
      let ((val, known), st') ← (fold c (f.vidLast + 1) v).run st
      st := st'
      if known != -1 then continue
      let (f', cv) ← mkConst f order.eq x.type isBool (← Rules.Ty.size tabs x.type) val
      f := f'.copyOf v cv
  return f

/-- The `known bits` pass. -/
def knownBitsPass : Pass := Pass.ofFunc fun env f => knownBits env.tables env.typeOrder f

end GoFV.Opt

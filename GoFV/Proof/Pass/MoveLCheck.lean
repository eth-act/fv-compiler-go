import GoFV.Proof.EvalL
import GoFV.SSA.Sem.TyEq

/-!
# The fixed-CFG value-motion validator `moveB` (issue #385)

`tighten`, `phi tighten`, `tighten tuple selectors` and (after `unhoist`) `loop invariant`
keep the CFG and move or clone values between blocks. `moveB f g` checks that `g` is such a
rearrangement of `f`; `GoFV.Proof.MoveL.refinesL_of_move` proves that it then refines `f` under
`runL`.

* **Related values** (`relB`): a value `x` of `g` stands for a value `y` of `f` (`x ≈ y`) if
  `x = y` and the certificate `ok` holds at `x` (identity; `okLocal`: same op, type, aux,
  auxint, sign extension of the first argument, arguments pairwise related, a `Phi` in the same
  block), or `x` is a clone of `y` (a total op, `totalOp`, with the same op, type, aux, auxint
  and arguments, each in the certificate), or `x` is a `Copy` of a value related to `y` of the
  same type. The certificate `ok` is computed by `okCert` (greatest fixed point) and validated
  locally (`certValid`), so the checker is linear apart from the fixed point.
* **Total ops** (`totalOp`): non-root ops whose lowered evaluation (non-faulting) is `.ok` for
  every argument list and does not read the value's ID: generic non-root ops but `Arg` /
  `ArgIntReg`, the arm64 ops `Arm64.evalPure` evaluates, and the arm64 loads, `MOVDaddr`,
  `MOVDreg`, `MOVDnop`, `LoweredGetClosurePtr`, `LoweredGetCallerSP`, `LoweredMemEq`.
* **Blocks** (`blockOK`): `g` lists the blocks of `f`, each with the same kind, `auxInt`,
  edges and controls (each control related to itself, `relB`: a selector turned into a `Copy`
  stays a control); every value of `g`'s block is a `Phi`
  of `f`'s block in the certificate, a non-`Phi` of `f`'s block in the certificate, or total.
* **Panics in order** (`orderOK`): every value of `f`'s schedule that may panic (`mayPanic`: a
  call or a nil check) is in `g`'s schedule of the block and in the certificate, and every
  non-total value `g` evaluates before it, `f` evaluates before it. So a panic of `f` at `r` is
  one of `g` at `r` (the total values never panic or get stuck), and a run of `f` through the
  block is one of `g`.
-/

namespace GoFV.Proof.MoveL

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof

/-- The arm64 ops `evalOpL` evaluates with `arm64Op` (its explicit list). -/
def actOp : Op → Bool
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
  | .ARM64LoweredMoveLoop => true
  | _ => false

/-- The ops of `arm64Op` that are `.ok` when memory ops do not fault: loads (`poison` on an
invalid access), addresses, register moves, the closure pointer and caller SP, `LoweredMemEq`. -/
def actTotal : Op → Bool
  | .ARM64MOVBload | .ARM64MOVBUload | .ARM64MOVHload | .ARM64MOVHUload | .ARM64MOVWload
  | .ARM64MOVWUload | .ARM64MOVDload | .ARM64FMOVSload | .ARM64FMOVDload | .ARM64FMOVQload
  | .ARM64LDP | .ARM64LDPW | .ARM64LDPSW | .ARM64FLDPD | .ARM64FLDPS | .ARM64FLDPQ
  | .ARM64MOVDaddr | .ARM64MOVDreg | .ARM64MOVDnop | .ARM64LoweredGetClosurePtr
  | .ARM64LoweredGetCallerSP | .ARM64LoweredMemEq => true
  | _ => false

/-- **Total ops**: never a root nor a `Phi`, and their lowered (non-faulting) evaluation is `.ok`
for every argument list, independently of the value's ID. -/
def totalOp (op : Op) : Bool :=
  op != .Phi && !isRoot op &&
    if op.generic then op != .Arg && op != .ArgIntReg else actTotal op || !actOp op

/-- The certificate at `x`, `false` beyond its size. -/
@[inline] def okAt (ok : Array Bool) (x : ID) : Bool := ok.getD x false

/-- The depth of `Copy` chains `relB` follows. -/
def relFuel : Nat := 4

/-- The depth `relB` follows: with `pr`, chains of adjacent pair stores relate through each
pair's memory (one level per pair). -/
def fuelOf (pr : Bool) : Nat := if pr then 32 else relFuel

/-- `pair`'s pairable loads (`pairableLoads`): element width and pair load. Each pair load
evaluates its element `i` as the load does at offset `auxInt + i * width` (`arm64Op`'s `ld` and
`ldPair` with the same width and sign extension). -/
def ldPairOf : Op → Option (Nat × Op)
  | .ARM64MOVDload => some (8, .ARM64LDP)
  | .ARM64MOVWUload => some (4, .ARM64LDPW)
  | .ARM64MOVWload => some (4, .ARM64LDPSW)
  | .ARM64FMOVDload => some (8, .ARM64FLDPD)
  | .ARM64FMOVSload => some (4, .ARM64FLDPS)
  | _ => none

/-- `pair`'s pairable stores (`pairableStores`): element width and pair store, which writes
as the two stores at offsets `auxInt` and `auxInt + width` in that order (`st`, `stPair`). -/
def stPairOf : Op → Option (Nat × Op)
  | .ARM64MOVDstore => some (8, .ARM64STP)
  | .ARM64MOVWstore => some (4, .ARM64STPW)
  | .ARM64FMOVDstore => some (8, .ARM64FSTPD)
  | .ARM64FMOVSstore => some (4, .ARM64FSTPS)
  | _ => none

/-- The component a tuple selector reads. -/
def selIdx : Op → Option Nat
  | .Select0 => some 0
  | .Select1 => some 1
  | _ => none

/-- `x` of `g` is a clone of `y` of `f`: a total op with the same op, type, aux, auxint, first
argument sign extension and arguments, each in the certificate. -/
def cloneB (ok : Array Bool) (f g : Func) (gv fv : Value) : Bool :=
  totalOp gv.op && gv.op == fv.op && gv.type == fv.type && gv.aux == fv.aux &&
    gv.auxInt == fv.auxInt && gv.args == fv.args && gv.args.all (okAt ok) &&
    sxOf g gv == sxOf f fv

/-- **Related values** `x ≈ y` (`x` of `g`, `y` of `f`), following at most `n` copies. With
`pr` (`pair`), also a selector `Select_i l` of a pair load `l` for the load `y` of element `i`
(the same aux, `y`'s offset `i` widths above `l`'s, related pointer and memory), and a pair
store for the second store `y` of two adjacent stores with `y`'s pointer, in order (`y`'s memory
the first store, at one width below `y`'s offset) or reversed (`y`'s memory the store one width
above `y`'s offset; the two writes are disjoint and commute); related pointer, values and
memory. -/
def relB (pr : Bool) (ok : Array Bool) (f g : Func) : Nat → ID → ID → Bool
  | n, x, y =>
    (x == y && okAt ok x) ||
    match g.value? x, f.value? y with
    | some gv, some fv =>
      cloneB ok f g gv fv ||
        (gv.op == .Copy && fv.op != .Phi && gv.type == fv.type &&
          match n, gv.args.toList with
          | n + 1, [z] => relB pr ok f g n z y
          | _, _ => false) ||
        (pr && gv.type == fv.type &&
          match n with
          | 0 => false
          | n + 1 =>
            (match selIdx gv.op, gv.args.toList, ldPairOf fv.op with
              | some i, [l], some (w, pop) =>
                match g.value? l with
                | some lv =>
                  lv.op == pop && lv.aux == fv.aux &&
                    fv.auxInt == lv.auxInt + Int64.ofNat (i * w) &&
                    match lv.args.toList, fv.args.toList with
                    | [p', m'], [p, m] => relB pr ok f g n p' p && relB pr ok f g n m' m
                    | _, _ => false
                | none => false
              | _, _, _ => false) ||
            (match stPairOf fv.op, gv.args.toList, fv.args.toList with
              | some (w, pop), [p', a', b', m'], [p2, b, ym] =>
                match f.value? ym with
                | some mv =>
                  gv.op == pop && mv.op == fv.op && mv.aux == fv.aux && gv.aux == fv.aux &&
                    gv.auxInt == mv.auxInt && fv.auxInt == mv.auxInt + Int64.ofNat w &&
                    match mv.args.toList with
                    | [p1, a, m] =>
                      p1 == p2 && relB pr ok f g n p' p1 && relB pr ok f g n a' a &&
                        relB pr ok f g n b' b && relB pr ok f g n m' m
                    | _ => false
                | none => false
              | _, _, _ => false) ||
            (match stPairOf fv.op, gv.args.toList, fv.args.toList with
              | some (w, pop), [p', a', b', m'], [p2, a, ym] =>
                match f.value? ym with
                | some mv =>
                  gv.op == pop && mv.op == fv.op && mv.aux == fv.aux && gv.aux == fv.aux &&
                    gv.auxInt == fv.auxInt && mv.auxInt == fv.auxInt + Int64.ofNat w &&
                    match mv.args.toList with
                    | [p1, b, m] =>
                      p1 == p2 && relB pr ok f g n p' p1 && relB pr ok f g n a' a &&
                        relB pr ok f g n b' b && relB pr ok f g n m' m
                    | _ => false
                | none => false
              | _, _, _ => false))
    | _, _ => false

/-- The certificate's local condition at `x`: the values `x` of `g` and `f` have the same op and
type, pairwise related arguments, and are `Phi`s in the same block or agree on aux, auxint and
first argument sign extension. -/
def okLocal (pr : Bool) (ok : Array Bool) (f g : Func) (x : ID) : Bool :=
  match g.value? x, f.value? x with
  | some gv, some fv =>
    gv.op == fv.op && gv.type == fv.type && gv.args.size == fv.args.size &&
      (List.range gv.args.size).all (fun k => relB pr ok f g (fuelOf pr) gv.args[k]! fv.args[k]!) &&
      if gv.op == .Phi then gv.block == fv.block
      else gv.aux == fv.aux && gv.auxInt == fv.auxInt && sxOf g gv == sxOf f fv
  | _, _ => false

/-- The certificate is locally valid. -/
def certValid (pr : Bool) (ok : Array Bool) (f g : Func) : Bool :=
  (List.range ok.size).all fun x => !okAt ok x || okLocal pr ok f g x

/-- The values of `g` through which `relB` reads the certificate beyond its arguments: it follows
the arguments of a `Copy`, a tuple selector, a pair load (behind a selector) and a pair store. -/
def conduitOp (op : Op) : Bool :=
  op == .Copy || (selIdx op).isSome || op == .ARM64LDP || op == .ARM64LDPW ||
    op == .ARM64LDPSW || op == .ARM64FLDPD || op == .ARM64FLDPS || op == .ARM64STP ||
    op == .ARM64STPW || op == .ARM64FSTPD || op == .ARM64FSTPS

/-- The certificate: the greatest fixed point of `okLocal` (untrusted, `certValid` checks it),
by a worklist. `okLocal pr ok f g z` reads `okAt ok x` only for `x` reached from `z` by at most
`2 * fuelOf pr + 2` argument edges whose intermediate values are conduits (`conduitOp`), except
the one next to `x`, which may be any value (`cloneB` reads its arguments). So when `x` leaves
the certificate, only the users reached from `x` that way are checked again; each value is
checked once at the start. (Rechecking every value until nothing changes took one round per
value of a dropped memory chain: 23 s on a 33,194-value function.) -/
def okCert (pr : Bool) (f g : Func) : Array Bool := Id.run do
  let n := g.valueTab.size
  let mut users : Array (Array ID) := Array.replicate n #[]
  for o in g.valueTab do
    if let some v := o then
      for a in v.args do
        if a < n then users := users.modify a (·.push v.id)
  let conduit : Array Bool := g.valueTab.map fun o => match o with
    | some v => conduitOp v.op
    | none => false
  let depth := 2 * fuelOf pr + 2
  let mut ok : Array Bool := Array.replicate n true
  let mut queued : Array Bool := Array.replicate n true
  let mut work : Array ID := (Array.range n).reverse
  -- the drop that last reached each value (`0`: none yet)
  let mut seen : Array Nat := Array.replicate n 0
  let mut drops := 0
  for _ in [0:n * (n + 1) + 1] do
    let some x := work.back? | break
    work := work.pop
    queued := queued.set! x false
    if okAt ok x && !okLocal pr ok f g x then
      ok := ok.set! x false
      drops := drops + 1
      let mut front : Array ID := #[x]
      for d in [0:depth] do
        let mut next : Array ID := #[]
        for u in front do
          if d ≤ 1 || conduit.getD u false then
            for z in users.getD u #[] do
              if seen.getD z 0 != drops then
                seen := seen.set! z drops
                next := next.push z
                if !queued.getD z true then
                  queued := queued.set! z true
                  work := work.push z
        if next.isEmpty then break
        front := next
  return ok

/-- Not total in `f`. -/
def nonTotal (f : Func) (x : ID) : Bool := match f.value? x with
  | some v => !totalOp v.op
  | none => true

/-- `x` is, in `f`, a pairable store on a store of the same op one width above it: the second
of two reversed adjacent stores `pair` merged into `x` (`relB`'s reversed store case). -/
def revStore (f : Func) (x : ID) : Bool :=
  match f.value? x with
  | some fv =>
    match stPairOf fv.op, fv.args.back? with
    | some (w, _), some ym =>
      match f.value? ym with
      | some mv => mv.op == fv.op && mv.auxInt == fv.auxInt + Int64.ofNat w
      | none => false
    | _, _ => false
  | none => false

/-- The store of `f`'s block `fb` a pair store `x` of `g` stands for (`relB`'s store cases): `x`
itself if it is the second of two reversed stores (`revStore`), else a pairable store whose
memory is `x`, the first of the two stores `pair` merged into `x`. -/
def pairSrc (f : Func) (fb : Block) (x : ID) : Option ID :=
  if revStore f x && fb.values.contains x then some x
  else fb.values.find? fun y => match f.value? y with
    | some fv => (stPairOf fv.op).isSome && fv.args.back? == some x
    | none => false

/-- The value of `f` that `g`'s evaluation of `x` waits for: `x` itself, or with `pr` and `x`
outside the certificate, the store `pairSrc` (a pair store evaluates once both stores have). -/
def srcOf (pr : Bool) (ok : Array Bool) (f : Func) (fb : Block) (x : ID) : ID :=
  if pr && !okAt ok x then (pairSrc f fb x).getD x else x

/-- A value of `g`'s block `b`: a `Phi` or non-total value in place in `f`'s block `fb` with the
certificate, a total one, or with `pr` a pair store outside the certificate related to its
`pairSrc`. -/
def valueOK (pr : Bool) (ok : Array Bool) (f g : Func) (fb : Block) (x : ID) : Bool :=
  match g.value? x with
  | some gv =>
    if gv.op == .Phi then okAt ok x && fb.values.contains x
    else totalOp gv.op || (okAt ok x && fb.values.contains x) ||
      (pr && !okAt ok x && match pairSrc f fb x with
        | some y => relB pr ok f g (fuelOf pr) x y
        | none => false)
  | none => false

/-- A value of `f` that may panic (`PanickingL false`: a call or a nil check). -/
def mayPanic (f : Func) (x : ID) : Bool := match f.value? x with
  | some v => v.op.call || v.op.nilCheck
  | none => false

/-- The values of `l` before `r`. -/
def before (l : List ID) (r : ID) : List ID := l.takeWhile (· != r)

/-- **Panics in the same order**: every value `r` of `f`'s schedule `oS` that may panic is in
the certificate and in `g`'s schedule `oT`, and for every non-total value `g` evaluates before
it, `f` evaluates its `srcOf` before it. -/
def orderOK (pr : Bool) (ok : Array Bool) (f g : Func) (fb : Block) (oT oS : List ID) : Bool :=
  oS.all fun r => !mayPanic f r ||
    (okAt ok r && oT.contains r &&
      (before oT r).all fun x => !nonTotal g x || (before oS r).contains (srcOf pr ok f fb x))

/-- Block `b` of `f`: the same block in `g` up to its values (see the module doc). -/
def blockOK (pr : Bool) (ok : Array Bool) (f g : Func) (b : ID) : Bool :=
  match f.block? b, g.block? b with
  | some fb, some gb =>
    gb.kind == fb.kind && gb.auxInt == fb.auxInt && gb.succs == fb.succs &&
      gb.preds == fb.preds && gb.controls == fb.controls &&
      gb.controls.all (fun c => relB pr ok f g (fuelOf pr) c c) &&
      gb.values.all (valueOK pr ok f g fb) &&
      match schedule g gb, schedule f fb with
      | some oT, some oS => orderOK pr ok f g fb oT.toList oS.toList
      | _, _ => false
  | _, _ => false

/-- **The value-motion validator** with certificate `ok`. -/
def moveWith (pr : Bool) (ok : Array Bool) (f g : Func) : Bool :=
  g.entry == f.entry && g.blocks == f.blocks && g.ownAux == f.ownAux && g.lowered == f.lowered &&
    certValid pr ok f g &&
    f.blocks.all (blockOK pr ok f g)

/-- **The value-motion validator.** -/
def moveB (f g : Func) : Bool := moveWith false (okCert false f g) f g

/-- A lowered shape (`typeShapesL`, the shapes `runL` gives a lowered function's values). -/
def shapeL (tabs : Tables) (t : TypeRef) : Ty := (typeShapesL tabs)[t]?.getD .other

/-- The pair loads (`ldPairOf`'s). -/
def pairLoadOp (op : Op) : Bool :=
  op == .ARM64LDP || op == .ARM64LDPW || op == .ARM64LDPSW || op == .ARM64FLDPD ||
    op == .ARM64FLDPS

/-- `g` is lowered, and every selector `Select_i l` of a pair load `l` has the shape of
component `i` of `l`'s two-component tuple shape. -/
def selShapesB (tabs : Tables) (g : Func) : Bool :=
  g.lowered && g.valueTab.all fun o => match o with
    | some gv => match selIdx gv.op, gv.args.toList with
      | some i, [l] => match g.value? l with
        | some lv => !pairLoadOp lv.op || match shapeL tabs lv.type with
          | .tuple [c0, c1] => Ty.beq ([c0, c1].getD i .other) (shapeL tabs gv.type)
          | _ => false
        | none => true
      | _, _ => true
    | none => true

/-- **The `pair` validator** in tables `tabs` (`pair`'s output tables): the moves of
`moveWith` plus the selectors of pair loads and pair stores (`relB` with `pr`), the selectors'
shapes (`selShapesB`). -/
def pairMoveB (tabs : Tables) (f g : Func) : Bool :=
  selShapesB tabs g && moveWith true (okCert true f g) f g

end GoFV.Proof.MoveL

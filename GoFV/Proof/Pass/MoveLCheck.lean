import GoFV.Proof.EvalL

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
  edges and controls (each control in the certificate); every value of `g`'s block is a `Phi`
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

/-- `x` of `g` is a clone of `y` of `f`: a total op with the same op, type, aux, auxint, first
argument sign extension and arguments, each in the certificate. -/
def cloneB (ok : Array Bool) (f g : Func) (gv fv : Value) : Bool :=
  totalOp gv.op && gv.op == fv.op && gv.type == fv.type && gv.aux == fv.aux &&
    gv.auxInt == fv.auxInt && gv.args == fv.args && gv.args.all (okAt ok) &&
    sxOf g gv == sxOf f fv

/-- **Related values** `x ≈ y` (`x` of `g`, `y` of `f`), following at most `n` copies. -/
def relB (ok : Array Bool) (f g : Func) : Nat → ID → ID → Bool
  | n, x, y =>
    (x == y && okAt ok x) ||
    match g.value? x, f.value? y with
    | some gv, some fv =>
      cloneB ok f g gv fv ||
        (gv.op == .Copy && fv.op != .Phi && gv.type == fv.type &&
          match n, gv.args.toList with
          | n + 1, [z] => relB ok f g n z y
          | _, _ => false)
    | _, _ => false

/-- The certificate's local condition at `x`: the values `x` of `g` and `f` have the same op and
type, pairwise related arguments, and are `Phi`s in the same block or agree on aux, auxint and
first argument sign extension. -/
def okLocal (ok : Array Bool) (f g : Func) (x : ID) : Bool :=
  match g.value? x, f.value? x with
  | some gv, some fv =>
    gv.op == fv.op && gv.type == fv.type && gv.args.size == fv.args.size &&
      (List.range gv.args.size).all (fun k => relB ok f g relFuel gv.args[k]! fv.args[k]!) &&
      if gv.op == .Phi then gv.block == fv.block
      else gv.aux == fv.aux && gv.auxInt == fv.auxInt && sxOf g gv == sxOf f fv
  | _, _ => false

/-- The certificate is locally valid. -/
def certValid (ok : Array Bool) (f g : Func) : Bool :=
  (List.range ok.size).all fun x => !okAt ok x || okLocal ok f g x

/-- The certificate: the greatest fixed point of `okLocal` (untrusted, `certValid` checks it). -/
def okCert (f g : Func) : Array Bool := Id.run do
  let n := g.valueTab.size
  let mut ok : Array Bool := Array.replicate n true
  for _ in [0:n + 1] do
    let ok' := (Array.range n).map fun x => okAt ok x && okLocal ok f g x
    if ok' == ok then break
    ok := ok'
  return ok

/-- Not total in `f`. -/
def nonTotal (f : Func) (x : ID) : Bool := match f.value? x with
  | some v => !totalOp v.op
  | none => true

/-- A value of `g`'s block `b`: a `Phi` or non-total value in place in `f`'s block `fb` with the
certificate, or a total one. -/
def valueOK (ok : Array Bool) (g : Func) (fb : Block) (x : ID) : Bool :=
  match g.value? x with
  | some gv =>
    if gv.op == .Phi then okAt ok x && fb.values.contains x
    else totalOp gv.op || (okAt ok x && fb.values.contains x)
  | none => false

/-- A value of `f` that may panic (`PanickingL false`: a call or a nil check). -/
def mayPanic (f : Func) (x : ID) : Bool := match f.value? x with
  | some v => v.op.call || v.op.nilCheck
  | none => false

/-- The values of `l` before `r`. -/
def before (l : List ID) (r : ID) : List ID := l.takeWhile (· != r)

/-- **Panics in the same order**: every value `r` of `f`'s schedule `oS` that may panic is in
the certificate and in `g`'s schedule `oT`, and every non-total value `g` evaluates before it,
`f` evaluates before it. -/
def orderOK (ok : Array Bool) (f g : Func) (oT oS : List ID) : Bool :=
  oS.all fun r => !mayPanic f r ||
    (okAt ok r && oT.contains r &&
      (before oT r).all fun x => !nonTotal g x || (before oS r).contains x)

/-- Block `b` of `f`: the same block in `g` up to its values (see the module doc). -/
def blockOK (ok : Array Bool) (f g : Func) (b : ID) : Bool :=
  match f.block? b, g.block? b with
  | some fb, some gb =>
    gb.kind == fb.kind && gb.auxInt == fb.auxInt && gb.succs == fb.succs &&
      gb.preds == fb.preds && gb.controls == fb.controls && gb.controls.all (okAt ok) &&
      gb.values.all (valueOK ok g fb) &&
      match schedule g gb, schedule f fb with
      | some oT, some oS => orderOK ok f g oT.toList oS.toList
      | _, _ => false
  | _, _ => false

/-- **The value-motion validator** with certificate `ok`. -/
def moveWith (ok : Array Bool) (f g : Func) : Bool :=
  g.entry == f.entry && g.blocks == f.blocks && g.ownAux == f.ownAux && g.lowered == f.lowered &&
    certValid ok f g &&
    f.blocks.all (blockOK ok f g)

/-- **The value-motion validator.** -/
def moveB (f g : Func) : Bool := moveWith (okCert f g) f g

end GoFV.Proof.MoveL

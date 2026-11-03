import GoFV.SSA.Op
import GoFV.SSA.AuxData
import GoFV.SSA.Sem.Shift
import GoFV.SSA.Sem.Conv
import GoFV.SSA.Sem.Ptr
import GoFV.SSA.Sem.Float
import GoFV.SSA.Sem.Arm64

/-!
# `evalPure`: the pure ops (`docs/plans/semantics.md` §4)

`evalPure op ty auxInt aux args` is the value of a pure op applied to already-evaluated
arguments. It is total: partial ops and ops whose semantics belongs to a later phase give
`poison` (§3.5, §9), so evaluation order among pure values never matters.

`ty` is the shape of the value's type (the result width of `Ctz`/`BitLen`/`PopCount`, which is
`int` on arm64, and of `Slicemask`), the element size of `PtrIndex`'s pointer type, the
layout a `Load` decodes. `aux` is unused: the ops that read symbols or names (`Addr`,
`LocalAddr`, `ConstString`, `Arg`) depend on the activation and are evaluated by `evalValue`.

One arm per op, each calling its family's definition (`Sem/Int`, `Sem/Shift`, `Sem/Cmp`,
`Sem/Conv`, `Sem/Float`), so a rule lemma unfolds `evalPure` at a concrete op and then only its
family. Every other op is the lowered arm64 op of `Arm64.evalPure` (`Sem/Arm64.lean`,
`docs/plans/semantics2.md`), `poison` if it is not one.
Never `simp [evalPure]` on an op variable (446-arm match, `docs/contracts/ir.md`).
-/

namespace GoFV.SSA.Sem

/-- The integer width of a type shape. -/
def Ty.width? : Ty → Option Width
  | .int w => some w
  | _ => none

/-- The value of pure op `op` (P1, P2 and P4 subsets, and the pure lowered arm64 ops; every other
op is `poison`). -/
def evalPure (op : Op) (ty : Ty) (auxInt : Int64) (aux : Option AuxRef) (args : List Val) :
    Val :=
  let flag := auxInt == 1
  let rw := ty.width?
  match op with
  | .Add8 => Int.add .w8 args
  | .Sub8 => Int.sub .w8 args
  | .Mul8 => Int.mul .w8 args
  | .And8 => Int.and .w8 args
  | .Or8 => Int.or .w8 args
  | .Xor8 => Int.xor .w8 args
  | .Neg8 => Int.neg .w8 args
  | .Com8 => Int.com .w8 args
  | .Add16 => Int.add .w16 args
  | .Sub16 => Int.sub .w16 args
  | .Mul16 => Int.mul .w16 args
  | .And16 => Int.and .w16 args
  | .Or16 => Int.or .w16 args
  | .Xor16 => Int.xor .w16 args
  | .Neg16 => Int.neg .w16 args
  | .Com16 => Int.com .w16 args
  | .Add32 => Int.add .w32 args
  | .Sub32 => Int.sub .w32 args
  | .Mul32 => Int.mul .w32 args
  | .And32 => Int.and .w32 args
  | .Or32 => Int.or .w32 args
  | .Xor32 => Int.xor .w32 args
  | .Neg32 => Int.neg .w32 args
  | .Com32 => Int.com .w32 args
  | .Add64 => Int.add .w64 args
  | .Sub64 => Int.sub .w64 args
  | .Mul64 => Int.mul .w64 args
  | .And64 => Int.and .w64 args
  | .Or64 => Int.or .w64 args
  | .Xor64 => Int.xor .w64 args
  | .Neg64 => Int.neg .w64 args
  | .Com64 => Int.com .w64 args
  | .Hmul32 => Int.hmul .w32 true args
  | .Hmul32u => Int.hmul .w32 false args
  | .Mul32uhilo => Int.mulhilo .w32 args
  | .Mul32uover => Int.mulover .w32 args
  | .Hmul64 => Int.hmul .w64 true args
  | .Hmul64u => Int.hmul .w64 false args
  | .Mul64uhilo => Int.mulhilo .w64 args
  | .Mul64uover => Int.mulover .w64 args
  | .Avg64u => Int.avgu .w64 args
  | .Div8 => Int.divs .w8 false args
  | .Div8u => Int.divu .w8 args
  | .Mod8 => Int.mods .w8 false args
  | .Mod8u => Int.modu .w8 args
  | .Div16 => Int.divs .w16 flag args
  | .Div16u => Int.divu .w16 args
  | .Mod16 => Int.mods .w16 flag args
  | .Mod16u => Int.modu .w16 args
  | .Div32 => Int.divs .w32 flag args
  | .Div32u => Int.divu .w32 args
  | .Mod32 => Int.mods .w32 flag args
  | .Mod32u => Int.modu .w32 args
  | .Div64 => Int.divs .w64 flag args
  | .Div64u => Int.divu .w64 args
  | .Mod64 => Int.mods .w64 flag args
  | .Mod64u => Int.modu .w64 args
  | .Div128u => Int.div128u args
  | .Lsh8x8 => Shift.lsh .w8 .w8 flag args
  | .Rsh8x8 => Shift.rsh .w8 .w8 flag args
  | .Rsh8Ux8 => Shift.rshu .w8 .w8 flag args
  | .Lsh8x16 => Shift.lsh .w8 .w16 flag args
  | .Rsh8x16 => Shift.rsh .w8 .w16 flag args
  | .Rsh8Ux16 => Shift.rshu .w8 .w16 flag args
  | .Lsh8x32 => Shift.lsh .w8 .w32 flag args
  | .Rsh8x32 => Shift.rsh .w8 .w32 flag args
  | .Rsh8Ux32 => Shift.rshu .w8 .w32 flag args
  | .Lsh8x64 => Shift.lsh .w8 .w64 flag args
  | .Rsh8x64 => Shift.rsh .w8 .w64 flag args
  | .Rsh8Ux64 => Shift.rshu .w8 .w64 flag args
  | .Lsh16x8 => Shift.lsh .w16 .w8 flag args
  | .Rsh16x8 => Shift.rsh .w16 .w8 flag args
  | .Rsh16Ux8 => Shift.rshu .w16 .w8 flag args
  | .Lsh16x16 => Shift.lsh .w16 .w16 flag args
  | .Rsh16x16 => Shift.rsh .w16 .w16 flag args
  | .Rsh16Ux16 => Shift.rshu .w16 .w16 flag args
  | .Lsh16x32 => Shift.lsh .w16 .w32 flag args
  | .Rsh16x32 => Shift.rsh .w16 .w32 flag args
  | .Rsh16Ux32 => Shift.rshu .w16 .w32 flag args
  | .Lsh16x64 => Shift.lsh .w16 .w64 flag args
  | .Rsh16x64 => Shift.rsh .w16 .w64 flag args
  | .Rsh16Ux64 => Shift.rshu .w16 .w64 flag args
  | .Lsh32x8 => Shift.lsh .w32 .w8 flag args
  | .Rsh32x8 => Shift.rsh .w32 .w8 flag args
  | .Rsh32Ux8 => Shift.rshu .w32 .w8 flag args
  | .Lsh32x16 => Shift.lsh .w32 .w16 flag args
  | .Rsh32x16 => Shift.rsh .w32 .w16 flag args
  | .Rsh32Ux16 => Shift.rshu .w32 .w16 flag args
  | .Lsh32x32 => Shift.lsh .w32 .w32 flag args
  | .Rsh32x32 => Shift.rsh .w32 .w32 flag args
  | .Rsh32Ux32 => Shift.rshu .w32 .w32 flag args
  | .Lsh32x64 => Shift.lsh .w32 .w64 flag args
  | .Rsh32x64 => Shift.rsh .w32 .w64 flag args
  | .Rsh32Ux64 => Shift.rshu .w32 .w64 flag args
  | .Lsh64x8 => Shift.lsh .w64 .w8 flag args
  | .Rsh64x8 => Shift.rsh .w64 .w8 flag args
  | .Rsh64Ux8 => Shift.rshu .w64 .w8 flag args
  | .Lsh64x16 => Shift.lsh .w64 .w16 flag args
  | .Rsh64x16 => Shift.rsh .w64 .w16 flag args
  | .Rsh64Ux16 => Shift.rshu .w64 .w16 flag args
  | .Lsh64x32 => Shift.lsh .w64 .w32 flag args
  | .Rsh64x32 => Shift.rsh .w64 .w32 flag args
  | .Rsh64Ux32 => Shift.rshu .w64 .w32 flag args
  | .Lsh64x64 => Shift.lsh .w64 .w64 flag args
  | .Rsh64x64 => Shift.rsh .w64 .w64 flag args
  | .Rsh64Ux64 => Shift.rshu .w64 .w64 flag args
  | .Eq8 => Cmp.eq .w8 args
  | .Neq8 => Cmp.neq .w8 args
  | .Less8 => Cmp.less .w8 args
  | .Less8U => Cmp.lessU .w8 args
  | .Leq8 => Cmp.leq .w8 args
  | .Leq8U => Cmp.leqU .w8 args
  | .Eq16 => Cmp.eq .w16 args
  | .Neq16 => Cmp.neq .w16 args
  | .Less16 => Cmp.less .w16 args
  | .Less16U => Cmp.lessU .w16 args
  | .Leq16 => Cmp.leq .w16 args
  | .Leq16U => Cmp.leqU .w16 args
  | .Eq32 => Cmp.eq .w32 args
  | .Neq32 => Cmp.neq .w32 args
  | .Less32 => Cmp.less .w32 args
  | .Less32U => Cmp.lessU .w32 args
  | .Leq32 => Cmp.leq .w32 args
  | .Leq32U => Cmp.leqU .w32 args
  | .Eq64 => Cmp.eq .w64 args
  | .Neq64 => Cmp.neq .w64 args
  | .Less64 => Cmp.less .w64 args
  | .Less64U => Cmp.lessU .w64 args
  | .Leq64 => Cmp.leq .w64 args
  | .Leq64U => Cmp.leqU .w64 args
  | .AndB => Cmp.andB args
  | .OrB => Cmp.orB args
  | .EqB => Cmp.eqB args
  | .NeqB => Cmp.neqB args
  | .Not => Cmp.not args
  | .CondSelect => Cmp.condSelect args
  | .IsInBounds => Cmp.inBounds false args
  | .IsSliceInBounds => Cmp.inBounds true args
  | .SpectreIndex => Cmp.spectreIndex false args
  | .SpectreSliceIndex => Cmp.spectreIndex true args
  | .Ctz8 => Int.ctz .w8 false rw args
  | .Ctz8NonZero => Int.ctz .w8 true rw args
  | .BitLen8 => Int.bitLen .w8 rw args
  | .PopCount8 => Int.popCount .w8 rw args
  | .BitRev8 => Int.bitRev .w8 args
  | .RotateLeft8 => Int.rotateLeft .w8 args
  | .Ctz16 => Int.ctz .w16 false rw args
  | .Ctz16NonZero => Int.ctz .w16 true rw args
  | .BitLen16 => Int.bitLen .w16 rw args
  | .PopCount16 => Int.popCount .w16 rw args
  | .BitRev16 => Int.bitRev .w16 args
  | .RotateLeft16 => Int.rotateLeft .w16 args
  | .Bswap16 => Int.bswap .w16 args
  | .Ctz32 => Int.ctz .w32 false rw args
  | .Ctz32NonZero => Int.ctz .w32 true rw args
  | .BitLen32 => Int.bitLen .w32 rw args
  | .PopCount32 => Int.popCount .w32 rw args
  | .BitRev32 => Int.bitRev .w32 args
  | .RotateLeft32 => Int.rotateLeft .w32 args
  | .Bswap32 => Int.bswap .w32 args
  | .Ctz64 => Int.ctz .w64 false rw args
  | .Ctz64NonZero => Int.ctz .w64 true rw args
  | .BitLen64 => Int.bitLen .w64 rw args
  | .PopCount64 => Int.popCount .w64 rw args
  | .BitRev64 => Int.bitRev .w64 args
  | .RotateLeft64 => Int.rotateLeft .w64 args
  | .Bswap64 => Int.bswap .w64 args
  | .Min64 => Int.min .w64 true args
  | .Min64u => Int.min .w64 false args
  | .Max64 => Int.max .w64 true args
  | .Max64u => Int.max .w64 false args
  | .Add64carry => Int.addcarry args
  | .Sub64borrow => Int.subborrow args
  | .Slicemask => match rw with | some w => Int.slicemask w args | none => .poison
  | .SignExt8to16 => Conv.signExt .w8 .w16 args
  | .ZeroExt8to16 => Conv.zeroExt .w8 .w16 args
  | .SignExt8to32 => Conv.signExt .w8 .w32 args
  | .ZeroExt8to32 => Conv.zeroExt .w8 .w32 args
  | .SignExt8to64 => Conv.signExt .w8 .w64 args
  | .ZeroExt8to64 => Conv.zeroExt .w8 .w64 args
  | .SignExt16to32 => Conv.signExt .w16 .w32 args
  | .ZeroExt16to32 => Conv.zeroExt .w16 .w32 args
  | .SignExt16to64 => Conv.signExt .w16 .w64 args
  | .ZeroExt16to64 => Conv.zeroExt .w16 .w64 args
  | .SignExt32to64 => Conv.signExt .w32 .w64 args
  | .ZeroExt32to64 => Conv.zeroExt .w32 .w64 args
  | .Trunc16to8 => Conv.trunc .w16 .w8 args
  | .Trunc32to8 => Conv.trunc .w32 .w8 args
  | .Trunc32to16 => Conv.trunc .w32 .w16 args
  | .Trunc64to8 => Conv.trunc .w64 .w8 args
  | .Trunc64to16 => Conv.trunc .w64 .w16 args
  | .Trunc64to32 => Conv.trunc .w64 .w32 args
  | .CvtBoolToUint8 => Conv.boolToUint8 args
  | .Const8 => Conv.const .w8 auxInt
  | .Const16 => Conv.const .w16 auxInt
  | .Const32 => Conv.const .w32 auxInt
  | .Const64 => Conv.const .w64 auxInt
  | .ConstBool => Conv.constBool auxInt
  | .SelectN => Tuple.selectN auxInt args
  | .SelectNAddr => Tuple.selectNAddr auxInt args
  | .Select0 => Tuple.select 0 args
  | .Select1 => Tuple.select 1 args
  | .MakeTuple => Tuple.make args
  | .Copy => match args with | [x] => x | _ => .poison
  | .MakeResult => .tuple args
  | .OffPtr => PtrOps.offPtr auxInt args
  | .AddPtr => PtrOps.addPtr args
  | .PtrIndex => PtrOps.ptrIndex (match ty with | .ptr e => e | _ => none) args
  | .SubPtr => PtrOps.subPtr args
  | .EqPtr => PtrOps.eqPtr false args
  | .NeqPtr => PtrOps.eqPtr true args
  | .IsNonNil => PtrOps.isNonNil args
  | .Convert => PtrOps.convert ty args
  | .EqInter => PtrOps.eqFirst false args
  | .NeqInter => PtrOps.eqFirst true args
  | .EqSlice => PtrOps.eqFirst false args
  | .NeqSlice => PtrOps.eqFirst true args
  | .StringMake => Comp.make args
  | .SliceMake => Comp.make args
  | .IMake => Comp.make args
  | .ComplexMake => Comp.make args
  | .StructMake => Comp.make args
  | .ArrayMake1 => Comp.make args
  | .StringPtr => Comp.select 0 args
  | .SlicePtr => Comp.select 0 args
  | .SlicePtrUnchecked => Comp.select 0 args
  | .ITab => Comp.select 0 args
  | .ComplexReal => Comp.select 0 args
  | .StringLen => Comp.select 1 args
  | .SliceLen => Comp.select 1 args
  | .IData => Comp.select 1 args
  | .ComplexImag => Comp.select 1 args
  | .SliceCap => Comp.select 2 args
  | .StructSelect => Comp.selectAux auxInt args
  | .ArraySelect => Comp.selectAux auxInt args
  -- the nil pointer as its word (`Ptr.word`, §3.2): address 0
  | .ConstNil => .i64 0
  | .ConstSlice => .agg [.i64 0, .i64 0, .i64 0]
  | .ConstInterface => .agg [.i64 0, .i64 0]
  | .Empty => .empty
  -- a feature the guarded code does not need: arm64's only use guards the LSE `*Variant`
  -- atomics, which mean the same as their base forms (`Sem/Atomic.lean`)
  | .HasCPUFeature => .bool false
  -- the current goroutine: an opaque allocation of the environment (§5), never nil
  | .GetG => .ptr ⟨.global "runtime.g", 0⟩
  | .Load => loadOp ty args
  | .Dereference => loadOp ty args
  | .MemEq => memEq args
  | .AtomicLoad8 | .AtomicLoad32 | .AtomicLoad64 | .AtomicLoadPtr | .AtomicLoadAcq32
  | .AtomicLoadAcq64 => atomicLoad ty args
  | .WB => wbOp auxInt args
  | .Add32F => FOps.add .w32 args
  | .Add64F => FOps.add .w64 args
  | .Sub32F => FOps.sub .w32 args
  | .Sub64F => FOps.sub .w64 args
  | .Mul32F => FOps.mul .w32 args
  | .Mul64F => FOps.mul .w64 args
  | .Div32F => FOps.div .w32 args
  | .Div64F => FOps.div .w64 args
  | .Neg32F => FOps.neg .w32 args
  | .Neg64F => FOps.neg .w64 args
  | .Eq32F => FOps.eq .w32 args
  | .Eq64F => FOps.eq .w64 args
  | .Neq32F => FOps.neq .w32 args
  | .Neq64F => FOps.neq .w64 args
  | .Less32F => FOps.less .w32 args
  | .Less64F => FOps.less .w64 args
  | .Leq32F => FOps.leq .w32 args
  | .Leq64F => FOps.leq .w64 args
  | .Min32F => FOps.min .w32 args
  | .Min64F => FOps.min .w64 args
  | .Max32F => FOps.max .w32 args
  | .Max64F => FOps.max .w64 args
  | .Sqrt => FOps.sqrt .w64 args
  | .Sqrt32 => FOps.sqrt .w32 args
  | .Floor => FOps.roundInt .rmi .w64 args
  | .Ceil => FOps.roundInt .rpi .w64 args
  | .Trunc => FOps.roundInt .rz .w64 args
  | .Round => FOps.roundInt .rna .w64 args
  | .RoundToEven => FOps.roundInt .rne .w64 args
  | .Abs => FOps.abs .w64 args
  | .Copysign => FOps.copysign .w64 args
  | .FMA => FOps.fma .w64 args
  | .Round32F => FOps.round .w32 args
  | .Round64F => FOps.round .w64 args
  | .Cvt32to32F => FOps.ofInt false .w32 .w32 args
  | .Cvt32to64F => FOps.ofInt false .w32 .w64 args
  | .Cvt64to32F => FOps.ofInt false .w64 .w32 args
  | .Cvt64to64F => FOps.ofInt false .w64 .w64 args
  | .Cvt32Uto32F => FOps.ofInt true .w32 .w32 args
  | .Cvt32Uto64F => FOps.ofInt true .w32 .w64 args
  | .Cvt64Uto32F => FOps.ofInt true .w64 .w32 args
  | .Cvt64Uto64F => FOps.ofInt true .w64 .w64 args
  | .Cvt32Fto32 => FOps.toInt false .w32 .w32 args
  | .Cvt32Fto64 => FOps.toInt false .w64 .w32 args
  | .Cvt64Fto32 => FOps.toInt false .w32 .w64 args
  | .Cvt64Fto64 => FOps.toInt false .w64 .w64 args
  | .Cvt32Fto32U => FOps.toInt true .w32 .w32 args
  | .Cvt32Fto64U => FOps.toInt true .w64 .w32 args
  | .Cvt64Fto32U => FOps.toInt true .w32 .w64 args
  | .Cvt64Fto64U => FOps.toInt true .w64 .w64 args
  | .Cvt32Fto64F => FOps.f32to64 args
  | .Cvt64Fto32F => FOps.f64to32 args
  | .Const32F => FOps.const32 auxInt
  | .Const64F => FOps.const64 auxInt
  | op => Arm64.evalPure op ty auxInt aux args

end GoFV.SSA.Sem

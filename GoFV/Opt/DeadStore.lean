import GoFV.Opt.Pass
import GoFV.SSA.Alloc
import GoFV.SSA.TypePred
import GoFV.Util.SparseSet
import GoFV.Util.SparseMap
import GoFV.Rules.Helpers.Sym
import Std.Data.TreeMap

/-!
# dse (`deadstore.go:13-238`)

Block-local backward dead-store elimination (`docs/PASSES.md`, dse). Per block in `f.Blocks`
order: classify the in-block memory uses (`loadUse`, `storeUse`), find the unique last store,
walk the memory chain backwards keeping, per base pointer, the byte ranges known to be
overwritten (`shadowRanges`, 16-bit offsets, at most 64 ranges); a `Store`/`Zero`/`Move` fully
inside one recorded range becomes `Copy mem`. Nothing is allocated or freed.

The `shadowed` sparse map holds each base's ranges directly (Go stores a 1-based index into a
slice of `*shadowRanges` that it mutates through the pointer; the observable state is the
same). `localAddrs` is a `TreeMap` (lookup only), which the kernel can evaluate.

`GoFV.Proof.DSE.dse_refines` proves that `dse`'s result refines its input when the checker
`DSE.drel` (`GoFV/Opt/DeadStoreCheck.lean`) accepts it (`dseFrag`).
-/

namespace GoFV.Opt

open GoFV.SSA GoFV.Util

namespace DSE

/-- `maxShadowRanges`. -/
def maxShadowRanges : Nat := 64

/-- `shadowRanges`: disjoint byte ranges `[lo, hi]` (each fits in 16 bits). -/
abbrev ShadowRanges := Array (Int64 × Int64)

/-- `sr.contains(lo, hi)`: `[lo, hi]` lies within a single range. -/
def ShadowRanges.contains (sr : ShadowRanges) (lo hi : Int64) : Bool :=
  sr.any fun (rlo, rhi) => lo ≥ rlo && hi ≤ rhi

/-- `sr.add(lo, hi)`: merge `[lo, hi]` with every range it overlaps or touches, appended last;
ignored outside 16 bits or when 64 ranges are already tracked. -/
def ShadowRanges.add (sr : ShadowRanges) (lo hi : Int64) : ShadowRanges := Id.run do
  if lo < 0 || hi > 0xffff || sr.size ≥ maxShadowRanges then return sr
  let mut nlo := lo
  let mut nhi := hi
  let mut out := #[]
  for (rlo, rhi) in sr do
    if nhi < rlo || nlo > rhi then
      out := out.push (rlo, rhi)
      continue
    if rlo < nlo then nlo := rlo
    if rhi > nhi then nhi := rhi
  return out.push (nlo, nhi)

/-- The in-block memory arguments of `x`. -/
@[inline] def memArgsIn (f : Func) (isMem : TypeRef → Bool) (b : ID) (x : Value) : Array ID :=
  x.args.filter fun a => let y := f.getV a; y.block == b && isMem y.type

/-- The first `LocalAddr` of each aux. A `TreeMap` (only searched, so any key order gives the
same result), which the kernel can evaluate, unlike a `HashMap`. -/
abbrev LocalAddrs := Std.TreeMap (Option AuxRef) ID

/-- Scan of `b.Values`: the stores, `loadUse`, `storeUse` and the first `LocalAddr` per aux. -/
def classify (f : Func) (tabs : Tables) (isMem : TypeRef → Bool) (b : ID)
    (loadUse storeUse : SparseSet) :
    Except String (Array ID × SparseSet × SparseSet × LocalAddrs) := do
  let mut stores := #[]
  let mut loadUse := loadUse
  let mut storeUse := storeUse
  let mut localAddrs : LocalAddrs := {}
  for v in (f.getB b).values do
    let x := f.getV v
    if x.op == .Phi then continue
    if isMem x.type then
      stores := stores.push v
      for a in memArgsIn f isMem b x do
        storeUse := storeUse.add a
        -- `Store`/`Zero`/`VarDef` never read their memory; a `Move` from read-only data
        -- is treated as not reading it.
        let reads ← match x.op with
          | .Store | .Zero | .VarDef => pure false
          | .Move =>
            let src := f.getV x.args[1]!
            if src.op == .Addr then (! ·) <$> GoFV.Rules.Sym.symIsRO tabs src.aux
            else pure true
          | _ => pure true
        if reads then loadUse := loadUse.add a
    else
      if x.op == .LocalAddr then
        if !localAddrs.contains x.aux then localAddrs := localAddrs.insert x.aux v
        continue
      if x.op == .InlMark || x.op == .Convert then continue
      for a in memArgsIn f isMem b x do
        loadUse := loadUse.add a
  return (stores, loadUse, storeUse, localAddrs)

/-- Strip an `OffPtr` chain: the base pointer and the summed offset. -/
def offPtrBase (f : Func) : Nat → ID → Int64 → ID × Int64
  | 0, p, off => (p, off)
  | fuel + 1, p, off =>
    let x := f.getV p
    if x.op == .OffPtr then offPtrBase f fuel x.args[0]! (off + x.auxInt) else (p, off)

/-- One block of `dse`. -/
def block (tabs : Tables) (isMem : TypeRef → Bool) (b : ID)
    (st : Func × SparseSet × SparseSet × SparseMap ShadowRanges) :
    Except String (Func × SparseSet × SparseSet × SparseMap ShadowRanges) := do
  let (f, loadUse, storeUse, shadowed) := st
  let (stores, loadUse, storeUse, localAddrs) ←
    classify f tabs isMem b loadUse.clear storeUse.clear
  if stores.isEmpty then return (f, loadUse, storeUse, shadowed)
  -- find last store in the block
  let mut last : Option ID := none
  for v in stores do
    if storeUse.contains v then continue
    if last.isSome then throw s!"b{b}: two final stores - simultaneous live stores"
    last := some v
  let some lastV := last | throw s!"b{b}: no last store found - cycle?"
  let mut f := f
  let mut shadowed := shadowed.clear
  let mut v := lastV
  for _ in [0:(f.getB b).values.size + 1] do
    if loadUse.contains v then shadowed := shadowed.clear
    let x := f.getV v
    if x.op == .Store || x.op == .Zero || x.op == .Move then
      let (ptr, off) := offPtrBase f f.vidLast x.args[0]! 0
      let sz : Int64 ← match x.op with
        | .Store => pure (Int64.ofInt (← GoFV.Rules.Ty.size tabs (← GoFV.Rules.Ty.ofAux tabs x.aux)))
        | _ => pure x.auxInt
      let p := f.getV ptr
      let ptr := if p.op == .LocalAddr then (localAddrs.get? p.aux).getD ptr else ptr
      let si := shadowed.get ptr
      if si.any (·.contains off (off + sz)) then
        let m := if x.op == .Zero then x.args[1]! else x.args[2]!
        f := (f.setArgs1 v m).modV v fun y => { y with aux := none, auxInt := 0, op := .Copy }
      else
        shadowed := shadowed.set ptr ((si.getD #[]).add off (off + sz))
    -- walk to previous store
    let x := f.getV v
    if x.op == .Phi then break
    match (memArgsIn f isMem b x)[0]? with
    | some a => v := a
    | none => break
  return (f, loadUse, storeUse, shadowed)

end DSE

/-- `dse(f)`. -/
def dse (tabs : Tables) (mem : TypeRef) (f : Func) : Except String Func := do
  let n := f.vidLast + 1
  let isMem := tabs.isMemory mem
  let st ← f.blocks.foldlM (fun st b => DSE.block tabs isMem b st)
    (f, SparseSet.new n, SparseSet.new n, SparseMap.new n)
  return st.1

/-- The `dse` pass. -/
def dsePass : Pass := Pass.ofFunc fun env f => do
  let some mem := env.typ? "Mem" | throw "typs: no Mem"
  dse env.tables mem f

end GoFV.Opt

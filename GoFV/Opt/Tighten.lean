import GoFV.Opt.Pass
import GoFV.SSA.Alloc
import GoFV.SSA.Analysis.CfgCache
import GoFV.SSA.TypePred
import GoFV.Util.SparseSet

/-!
# tighten (`tighten.go:14-277`, `lca.go`)

`tighten` (docs/PASSES2.md, tighten, issue #400): skipped when `base.Flag.N != 0` and the
function has fewer than 10,000 blocks.

1. `memState`: each block's start and end memory (block-ID arrays), seeded from memory phis,
   `InitMem` and incoming memory arguments, then flooded backwards FIFO through predecessors.
2. Movable values (once): not `LoweredGetClosurePtr`, `Phi`, `Arg*`, `Select0/1/N` or a nil
   check, and fewer than two distinct register-needing arguments other than `SP`/`SB` unless
   the value is flags.
3. Until nothing moves: each movable value's target is the dominator-tree LCA (`lcaRange`,
   built from `f.Idom()`) of its uses (a phi argument is used at the end of the corresponding
   predecessor, a control in its block); unless the cached `f.loopnest()` saw an irreducible
   loop, a target in a loop deeper than the value's own is lifted to the loop header's idom;
   then, in `f.Blocks` × `b.Values` order, a value whose memory argument (if any) is its target's
   start memory is appended to the target and swap-removed from its block (the slot is
   re-examined).
-/

namespace GoFV.Opt

open GoFV.SSA

namespace Tighten

/-- `lcaRangeBlock`: dominator-tree links (0 = none), Euler-tour position and depth. -/
structure LcaBlock where
  parent : ID := 0
  firstChild : ID := 0
  sibling : ID := 0
  pos : Nat := 0
  depth : Nat := 0
  deriving Inhabited

/-- `lcaRange`. -/
structure LcaRange where
  blocks : Array LcaBlock
  rangeMin : Array (Array ID)

/-- `makeLCArange(f)` with `dom = f.Idom()`. -/
def makeLcaRange (f : Func) (dom : Array (Option ID)) : LcaRange := Id.run do
  let nb := f.bidLast + 1
  let mut blocks : Array LcaBlock := Array.replicate nb {}
  for b in f.blocks do
    let some parent := dom[b]?.join | continue
    let sib := blocks[parent]!.firstChild
    blocks := blocks.modify b fun x => { x with parent, sibling := sib }
    blocks := blocks.modify parent fun x => { x with firstChild := b }
  let mut tour : Array ID := #[]
  let mut q : Array (ID × ID) := #[(f.entry, 0)]
  for _ in [0:4 * nb + 4] do
    let some (bid, cid) := q.back? | break
    q := q.pop
    blocks := blocks.modify bid fun x => { x with pos := tour.size }
    tour := tour.push bid
    let mut cid := cid
    if cid == 0 then
      let d := blocks[blocks[bid]!.parent]!.depth + 1
      blocks := blocks.modify bid fun x => { x with depth := d }
      cid := blocks[bid]!.firstChild
    else
      cid := blocks[cid]!.sibling
    if cid != 0 then
      q := (q.push (bid, cid)).push (cid, 0)
  let mut rangeMin : Array (Array ID) := #[tour]
  let mut logS := 1
  let mut s := 2
  for _ in [0:64] do
    if s ≥ tour.size then break
    let prev := rangeMin[logS - 1]!
    let mut r : Array ID := Array.mkEmpty (tour.size - s + 1)
    for i in [0:tour.size - s + 1] do
      let mut bid := prev[i]!
      let bid2 := prev[i + s / 2]!
      if blocks[bid2]!.depth < blocks[bid]!.depth then bid := bid2
      r := r.push bid
    rangeMin := rangeMin.push r
    logS := logS + 1
    s := s * 2
  return { blocks, rangeMin }

/-- `lca.find(a, b)`. -/
def LcaRange.find (lca : LcaRange) (a b : ID) : Except String ID := do
  if a == b then return a
  let mut p1 := lca.blocks[a]!.pos
  let mut p2 := lca.blocks[b]!.pos
  if p1 > p2 then (p1, p2) := (p2, p1)
  if p1 == p2 then throw s!"tighten: lca of b{a} and b{b}: equal tour positions"
  let logS := Nat.log2 (p2 - p1)
  let bid1 := lca.rangeMin[logS]![p1]!
  let bid2 := lca.rangeMin[logS]![p2 + 1 - (1 <<< logS)]!
  if lca.blocks[bid1]!.depth < lca.blocks[bid2]!.depth then return bid1
  return bid2

/-- `v.MemoryArg()` (not for phis): the last argument if it is memory-typed. -/
def memoryArg (isMem : TypeRef → Bool) (f : Func) (x : Value) : Option ID :=
  match x.args.back? with
  | some a => if isMem (f.getV a).type then some a else none
  | none => none

/-- `memState(f, startMem, endMem)`: start and end memory by block ID. -/
def memState (isMem : TypeRef → Bool) (f : Func) :
    Except String (Array (Option ID) × Array (Option ID)) := do
  let nb := f.bidLast + 1
  let mut startMem : Array (Option ID) := Array.replicate nb none
  let mut endMem : Array (Option ID) := Array.replicate nb none
  let mut changed : Array ID := #[]
  for b in f.blocks do
    for v in (f.getB b).values do
      let x := f.getV v
      let mem : Option ID :=
        if x.op == .Phi then (if isMem x.type then some v else none)
        else if x.op == .InitMem then some v
        else match memoryArg isMem f x with
          | some a => if (f.getV a).block != b then some a else none
          | none => none
      let some mem := mem | continue
      if let some old := startMem[b]! then
        if old == mem then continue
        throw s!"tighten: startMem[b{b}] has different values, old v{old}, new v{mem}"
      startMem := startMem.set! b (some mem)
      changed := changed.push b
  let mut head := 0
  for _ in [0:2 * nb + 1] do
    if h : head < changed.size then
      let top := changed[head]
      head := head + 1
      let mem := startMem[top]!.get!
      let mx := f.getV mem
      let preds := (f.getB top).preds
      for hi : i in [0:preds.size] do
        let pb := preds[i].b
        if endMem[pb]!.isSome then continue
        let e := if mx.op == .Phi && mx.block == top then mx.args[i]! else mem
        endMem := endMem.set! pb (some e)
        if startMem[pb]!.isNone then
          startMem := startMem.set! pb (some e)
          changed := changed.push pb
    else break
  return (startMem, endMem)

end Tighten

open Tighten in
/-- `tighten(f)`. -/
def tighten (env : PassEnv) (f : Func) : Except String Func := do
  let flagN := match env.config? "flagN" with
    | some #[.word w] => w != "0"
    | _ => false
  if flagN && f.blocks.size < 10000 then return f
  let some mem := env.typ? "Mem" | throw "tighten: no typ.Mem"
  let some void := env.typ? "Void" | throw "tighten: no typ.Void"
  let some flags := env.typ? "Flags" | throw "tighten: no typ.Flags"
  let tabs := env.tables
  let isMem := tabs.isMemory mem
  let isTuple (t : TypeRef) : Bool := (tabs.type? t).map (·.kind) == some .TUPLE
  let needRegister (t : TypeRef) : Bool := !isMem t && t != void && t != flags && !isTuple t
  let nv := f.vidLast + 1
  let (startMem, _) ← memState isMem f
  let mut canMove : Array Bool := Array.replicate nv false
  let mut distinct := Util.SparseSet.new nv
  for b in f.blocks do
    for v in (f.getB b).values do
      let x := f.getV v
      match x.op with
      | .ARM64LoweredGetClosurePtr | .Phi | .Arg | .ArgIntReg | .ArgFloatReg | .Select0
      | .Select1 | .SelectN => continue
      | _ => pure ()
      if x.op.nilCheck then continue
      distinct := distinct.clear
      for a in x.args do
        let y := f.getV a
        if needRegister y.type && y.op != .SB && y.op != .SP then distinct := distinct.add a
      if distinct.size ≥ 2 && x.type != flags then continue
      canMove := canMove.set! v true
  let (dom, f) := f.idom
  let lca := makeLcaRange f dom
  let (idom, f) := f.idom
  let (loops, f) ← f.loopnest
  let mut f := f
  let mut changed := true
  for _ in [0:nv * (f.bidLast + 1) + 2] do
    if !changed then break
    changed := false
    let mut target : Array (Option ID) := Array.replicate nv none
    for b in f.blocks do
      let blk := f.getB b
      for v in blk.values do
        let x := f.getV v
        for hi : i in [0:x.args.size] do
          let a := x.args[i]
          if !canMove[a]! then continue
          let use := if x.op == .Phi then blk.preds[i]!.b else b
          match target[a]! with
          | none => target := target.set! a (some use)
          | some t => target := target.set! a (some (← lca.find t use))
      for c in blk.controls do
        if !canMove[c]! then continue
        match target[c]! with
        | none => target := target.set! c (some b)
        | some t => target := target.set! c (some (← lca.find t b))
    if !loops.hasIrreducible then
      for b in f.blocks do
        let origloop := loops.loopOf b
        for v in (f.getB b).values do
          let some t := target[v]! | continue
          let mut t := t
          let mut targetloop := loops.loopOf t
          for _ in [0:loops.loops.size + 1] do
            let some tl := targetloop | break
            let deeper := match origloop with
              | none => true
              | some ol => loops.loops[tl]!.depth > loops.loops[ol]!.depth
            if !deeper then break
            let some t' := idom[loops.loops[tl]!.header]?.join
              | throw s!"tighten: loop header b{loops.loops[tl]!.header} has no idom"
            t := t'
            target := target.set! v (some t)
            targetloop := loops.loopOf t
    for b in f.blocks do
      let mut i := 0
      for _ in [0:2 * (f.getB b).values.size + 2] do
        let vals := (f.getB b).values
        if h : i < vals.size then
          let v := vals[i]
          let t := target[v]!
          let movable : Bool := match t with
            | none => false
            | some t =>
              t != b &&
                match memoryArg isMem f (f.getV v) with
                | some m => startMem[t]! == some m
                | none => true
          match t, movable with
          | some t, true =>
            f := f.modB t fun x => { x with values := x.values.push v }
            f := f.modV v fun x => { x with block := t }
            f := f.modB b fun x =>
              let last := x.values.size - 1
              { x with values := (x.values.set! i x.values[last]!).pop }
            changed := true
          | _, _ => i := i + 1
        else break
  return f

/-- `phiTighten(f)` (`tighten.go:181-200`): every phi argument that is rematerializeable
(`regalloc.go:2923`: the op's bit and every argument's op `fixedReg`) and not in the
corresponding predecessor is replaced by a fresh `copyInto` that predecessor, per occurrence. -/
def phiTighten (env : PassEnv) (f : Func) : Except String Func := do
  let some mem := env.typ? "Mem" | throw "phi tighten: no typ.Mem"
  let isMem := env.tables.isMemory mem
  let mut f := f
  for b in f.blocks do
    for v in (f.getB b).values do
      if (f.getV v).op != .Phi then continue
      let n := (f.getV v).args.size
      for i in [0:n] do
        let a := (f.getV v).args[i]!
        let x := f.getV a
        if !x.op.rematerializeable then continue
        if !x.args.all fun w => (f.getV w).op.fixedReg then continue
        let p := (f.getB b).preds[i]!.b
        if x.block == p then continue
        let (f', c) ← f.copyInto isMem a p
        f := f'.setArg v i c
  return f

/-- The `tighten` pass. -/
def tightenPass : Pass := Pass.ofFunc tighten

/-- The `phi tighten` pass. -/
def phiTightenPass : Pass := Pass.ofFunc phiTighten

end GoFV.Opt

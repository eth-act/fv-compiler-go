import GoFV.Opt.Pass
import GoFV.SSA.Alloc
import GoFV.SSA.TypePred
import GoFV.SSA.Analysis.CfgCache
import GoFV.Util.PdqSort
import GoFV.Rules.Helpers.Ptr
import GoFV.SSA.DomCert
import GoFV.SSA.Sem.Run
import GoFV.Opt.CSEMem
import Std.Data.TreeMap

/-!
# generic cse (`cse.go`)

Partition refinement (`docs/PASSES.md`, generic cse):

1. The non-memory values, in `f.Blocks` × `b.Values` order, numbering new auxes in `f.auxmap`
   (persistent, first appearance); `partitionValues` sorts them by `cmpVal` then ID
   (`slices.SortFunc`, Go's pdqsort: `GoFV.Util.PdqSort`) and keeps the runs of `cmpVal`-equal
   values with more than one member, numbered from 1 (`valueEqClass`; other values `-ID`).
2. Refinement to a fixpoint: classes are visited by index while the list grows; commutative
   values get `Args[0]`/`Args[1]` swapped in place when the classes are out of order; the class is
   sorted by argument classes (a `Load`/`NilCheck` memory argument replaced by its effective
   memory argument, skipping provably disjoint stores) and split where adjacent members differ
   (`LocalAddr`'s memory argument ignored); a split class is swap-removed and its non-singleton
   pieces appended.
3. With `f.Sdom()`: each class sorted by dominator-tree entry number, then memory-def skips,
   `LocalAddr` store order, statement marks first; each first remaining member replaces the
   following members its block dominates.
4. Arguments (moving a statement mark from a replaced argument to its same-block same-line
   user) and non-`NilCheck` controls are redirected.

Both unstable sorts can see ties, so the comparators and the sort are exact ports. Go memoises
`getEffectiveMemoryArg` (a pure function of the graph during the pass) and `storeOrdering`. The
`storeOrdering` cache makes a store's score depend on which stores were scored before, but the
cached scores along a block's memory chain are always strictly increasing (a score is written
from a store down to the first cached one, so the cached stores form a prefix of the chain), so
every comparison has the result of the uncached score, which is used here.
-/

namespace GoFV.Opt

open GoFV.SSA GoFV.SSA.Analysis

namespace CSE

/-- What the pass reads besides the function. -/
structure Ctx where
  tabs : Tables
  order : TypeOrder
  isMem : TypeRef → Bool
  ptrSize : Int

/-- `lt2Cmp(isLt)`. -/
@[inline] def lt2 (b : Bool) : Ordering := if b then .lt else .gt

/-- A total order on auxes (`none` first), the key order of `AuxIDs`. -/
def auxCmp (a b : Option AuxRef) : Ordering :=
  compare ((a.map (· + 1)).getD 0) ((b.map (· + 1)).getD 0)

/-- `auxIDs`: the number of each aux. A `TreeMap` (only searched, so any key order gives the same
result), which the kernel can evaluate, unlike a `HashMap`. -/
abbrev AuxIDs := Std.TreeMap (Option AuxRef) Int auxCmp

/-- `cmpVal(v, w, auxIDs)`. -/
def cmpVal (c : Ctx) (f : Func) (auxIDs : AuxIDs) (v w : ID) :
    Ordering :=
  let x := f.getV v
  let y := f.getV w
  if x.op != y.op then lt2 (x.op.ctorIdx < y.op.ctorIdx)
  else if x.auxInt != y.auxInt then lt2 (x.auxInt < y.auxInt)
  else if x.args.size != y.args.size then lt2 (x.args.size < y.args.size)
  else if x.op == .Phi && x.block != y.block then lt2 (x.block < y.block)
  else if c.isMem x.type then lt2 (v < w)
  else
    let tc := if x.op == .Select0 || x.op == .Select1 || x.op == .SelectN then Ordering.eq
      else c.order.compare x.type y.type
    if tc != .eq then tc
    else if x.aux != y.aux then
      match x.aux, y.aux with
      | none, _ => .lt
      | _, none => .gt
      | a, b => lt2 (auxIDs.getD a 0 < auxIDs.getD b 0)
    else .eq

/-- `partitionValues(a, auxIDs)`. -/
def partitionValues (c : Ctx) (f : Func) (auxIDs : AuxIDs)
    (a : Array ID) : Array (Array ID) := Id.run do
  let a := GoFV.Util.PdqSort.sortFunc (fun v w =>
    match cmpVal c f auxIDs v w with
    | .lt => -1
    | .gt => 1
    | .eq => if v < w then -1 else if v > w then 1 else 0) a
  let mut part : Array (Array ID) := #[]
  let mut i := 0
  for _ in [0:a.size] do
    if i ≥ a.size then break
    let v := a[i]!
    let mut j := i + 1
    for _ in [0:a.size] do
      if j ≥ a.size then break
      if cmpVal c f auxIDs v a[j]! != .eq then break
      j := j + 1
    if j > i + 1 then part := part.push (a.extract i j)
    i := j
  return part

/-- `isMemUser(v)`: `Load` and `NilCheck` (pointer argument 0, memory argument 1). -/
@[inline] def isMemUser (op : Op) : Bool := op == .Load || op == .NilCheck

/-- `maxId`: IDs above it are not remapped. -/
def maxId : Nat := 2 ^ 23 - 1

/-- `skipDisjointMemDefs(user, 0, 1, useWidth)`: the first memory def along the chain from the
user's memory argument that may alias it, and the number of defs skipped (at most 255). -/
def skipDisjointMemDefs (c : Ctx) (f : Func) (usePtr mem0 : ID) (useWidth : Int) :
    Except String (ID × Nat) := do
  let mut mem := mem0
  let mut skips := 0
  for _ in [0:255] do
    let m := f.getV mem
    -- `isMemDef(mem)`: pointer index, memory index, access width
    let d? : Option (Nat × Nat × Int) ← match m.op with
      | .Store => pure (some (0, 2, ← Rules.Ty.size c.tabs (← Rules.Ty.ofAux c.tabs m.aux)))
      | .VarDef => pure (some (0, 0, 0))
      | .Zero => pure (some (0, 1, m.auxInt.toInt))
      | _ => pure none
    let some (ip, im, width) := d? | break
    if (f.getV m.args[im]!).uses > 50 then break
    if width == 0 then
      mem := m.args[im]!; skips := skips + 1; continue
    if ← Rules.Ptr.disjoint f c.tabs c.ptrSize m.args[ip]! width usePtr useWidth then
      mem := m.args[im]!; skips := skips + 1; continue
    break
  return (mem, skips)

/-- `getEffectiveMemoryArg(memTable, v)` for a memory user `v`. -/
def effectiveMemoryArg (c : Ctx) (f : Func) (v : ID) : Except String (ID × Nat) := do
  let x := f.getV v
  let width ← if x.op == .Load then Rules.Ty.size c.tabs x.type else pure 0
  let memId := x.args[1]!
  if memId > maxId then return (memId, 0)
  let (mem, skips) ← skipDisjointMemDefs c f x.args[0]! memId width
  if mem ≤ maxId then return (mem, skips) else return (memId, 0)

/-- `storeOrdering(v, cache)` without the cache (see the module comment): one more than the
number of memory-chain steps from `v` that stay in `v`'s block before reaching a `Phi`, an
`InitMem` or a memory argument in another block. -/
def storeOrdering (c : Ctx) (f : Func) (v : ID) : Except String Nat := do
  let mut w := v
  let mut score := 1
  for _ in [0:f.vidLast + 1] do
    let x := f.getV w
    if x.op == .Phi || x.op == .InitMem then return score
    let some a := x.args.back? | throw s!"cse: storeOrdering: v{w} has no memory argument"
    if !c.isMem (f.getV a).type then throw s!"cse: storeOrdering: v{w} has no memory argument"
    if (f.getV a).block != x.block then return score
    w := a
    score := score + 1
  throw s!"cse: storeOrdering: memory cycle at v{v}"

/-- The refinement state. -/
structure St where
  f : Func
  /-- `valueEqClass`, by value ID. -/
  cls : Array Int
  partition : Array (Array ID)
  pNum : Int
  /-- `memTable`: effective memory argument and skips of the memory users seen so far. -/
  mem : Array (Option (ID × Nat))

@[inline] def St.cl (s : St) (v : ID) : Int := s.cls.getD v 0
@[inline] def St.eff (s : St) (v : ID) : ID × Nat := (s.mem.getD v none).getD (0, 0)

/-- The argument IDs compared at index `i`: the effective memory arguments for a memory user's
memory argument. -/
@[inline] def argPair (s : St) (memUser : Bool) (v w : ID) (x y : Value) (i : Nat) : ID × ID :=
  if memUser && i == 1 then ((s.eff v).1, (s.eff w).1) else (x.args[i]!, y.args[i]!)

/-- The refinement sort comparator (`cse.go:107-128`). -/
def cmpArgs (s : St) (v w : ID) : Int := Id.run do
  let x := s.f.getV v
  let y := s.f.getV w
  let mu := isMemUser x.op
  for i in [0:x.args.size] do
    let (a, b) := argPair s mu v w x y i
    if s.cl a < s.cl b then return -1
    if s.cl a > s.cl b then return 1
  return 0

/-- Adjacent members `v`, `w` have equivalent arguments (`cse.go:136-158`). -/
def eqArgs (s : St) (v w : ID) : Bool := Id.run do
  let x := s.f.getV v
  let y := s.f.getV w
  let mu := isMemUser x.op
  for i in [0:x.args.size] do
    if x.op == .LocalAddr && i == 1 then continue
    let (a, b) := argPair s mu v w x y i
    if s.cl a != s.cl b then return false
  return true

/-- Visit class `i`: returns the new state and whether it was split. -/
def refineClass (c : Ctx) (s : St) (i : Nat) : Except String (St × Bool) := do
  let e := s.partition[i]!
  let mut s := s
  if (s.f.getV e[0]!).op.commutative then
    for v in e do
      let x := s.f.getV v
      if s.cl x.args[0]! > s.cl x.args[1]! then
        s := { s with f := s.f.modV v fun y => { y with args := y.args.swapIfInBounds 0 1 } }
  if isMemUser (s.f.getV e[0]!).op then
    for v in e do
      if (s.mem.getD v none).isNone then
        let r ← effectiveMemoryArg c s.f v
        s := { s with mem := s.mem.set! v (some r) }
  let st := s
  let e := GoFV.Util.PdqSort.sortFunc (cmpArgs st) e
  let mut splitPoints : Array Nat := #[0]
  for j in [1:e.size] do
    if !eqArgs s e[j - 1]! e[j]! then splitPoints := splitPoints.push j
  if splitPoints.size == 1 then
    return ({ s with partition := s.partition.set! i e }, false)
  let last := s.partition.size - 1
  let mut part := (s.partition.set! i s.partition[last]!).pop
  let mut cls := s.cls
  let mut pNum := s.pNum
  splitPoints := splitPoints.push e.size
  for j in [0:splitPoints.size - 1] do
    let piece := e.extract splitPoints[j]! splitPoints[j + 1]!
    if piece.size == 1 then
      cls := cls.set! piece[0]! (-(piece[0]! : Int))
      continue
    for v in piece do cls := cls.set! v pNum
    pNum := pNum + 1
    part := part.push piece
  return ({ s with partition := part, cls, pNum }, true)

/-- One round over the (growing) partition list; `true` if some class was split. Each step
advances `i` or splits a class into more pieces, so `fuel` steps suffice. -/
def refineRound (c : Ctx) (fuel : Nat) (s : St) : Except String (St × Bool) := do
  let mut s := s
  let mut i := 0
  let mut changed := false
  for _ in [0:fuel] do
    if i ≥ s.partition.size then return (s, changed)
    let (s', split) ← refineClass c s i
    s := s'
    if split then changed := true else i := i + 1
  throw "cse: refinement did not terminate"

/-- The dominator-order comparator (`cse.go:209-267`). -/
def cmpDom (c : Ctx) (f : Func) (sdom : SparseTree) (mem : Array (Option (ID × Nat)))
    (v w : ID) : Int :=
  let x := f.getV v
  let y := f.getV w
  let dv := sdom.domorder x.block
  let dw := sdom.domorder y.block
  if dv < dw then -1 else if dv > dw then 1 else
  let skips (u : ID) : Nat := ((mem.getD u none).getD (0, 0)).2
  let sk := if isMemUser x.op then compare (skips v) (skips w) else .eq
  if sk == .lt then -1 else if sk == .gt then 1 else
  if x.op == .LocalAddr then
    let vm := x.args[1]!
    let wm := y.args[1]!
    if vm == wm then 0
    else if (f.getV vm).block != x.block then -1
    else if (f.getV wm).block != y.block then 1
    else
      -- `storeOrdering` never fails on a function the compiler accepted
      let vs := (storeOrdering c f vm).toOption.getD 0
      let ws := (storeOrdering c f wm).toOption.getD 0
      if vs < ws then -1 else if vs > ws then 1 else 0
  else
    let vStmt := x.pos.isStmt == Pos.isStmtMark
    let wStmt := y.pos.isStmt == Pos.isStmtMark
    if vStmt != wStmt then (if vStmt then -1 else 1) else 0

/-- The substitutions of one class, sorted by `cmpDom`, added to `rewrite`. -/
def classRewrites (f : Func) (sdom : SparseTree) (e : Array ID) (rewrite : Array (Option ID)) :
    Array (Option ID) := Id.run do
  let mut e : Array (Option ID) := e.map some
  let mut rewrite := rewrite
  for i in [0:e.size - 1] do
    let some v := e[i]! | continue
    e := e.set! i none
    let vb := (f.getV v).block
    for j in [i + 1:e.size] do
      let some w := e[j]! | continue
      if sdom.isAncestorEq vb (f.getV w).block then
        rewrite := rewrite.set! w (some v)
        e := e.set! j none
      else break
  return rewrite

/-- Apply the substitutions (`cse.go:288-317`). -/
def applyRewrites (f : Func) (rewrite : Array (Option ID)) : Func := Id.run do
  let mut f := f
  for b in f.blocks do
    for v in (f.getB b).values do
      let n := (f.getV v).args.size
      for i in [0:n] do
        let w := (f.getV v).args[i]!
        let some x := rewrite.getD w none | continue
        let wv := f.getV w
        if wv.pos.isStmt == Pos.isStmtMark && wv.op != .NilCheck then
          let vv := f.getV v
          if wv.block == vv.block && wv.pos.line == vv.pos.line then
            f := f.modV v fun y => { y with pos := y.pos.withIsStmt }
            f := f.modV w fun y => { y with pos := y.pos.withNotStmt }
        f := f.setArg v i x
    let cs := (f.getB b).controls
    for h : i in [0:cs.size] do
      let c := cs[i]
      let some x := rewrite.getD c none | continue
      if (f.getV c).op == .NilCheck then continue
      f := f.replaceControl b i x
  return f

end CSE

open CSE in
/-- `cse(f)` with its substitution (`rewrite[w] = v`: uses of `w` now read `v`). -/
def cseRw (c : Ctx) (f : Func) : Except String (Func × Array (Option ID)) := do
  -- the non-memory values, numbering new auxes in `f.auxmap`
  let am := f.cache.auxmap.getD #[]
  let mut auxIDs : AuxIDs :=
    am.foldl (fun m (a, k) => m.insert a k) {}
  let mut am := am
  let mut a : Array ID := #[]
  for b in f.blocks do
    for v in (f.getB b).values do
      let x := f.getV v
      if c.isMem x.type then continue
      if auxIDs.getD x.aux 0 == 0 then
        let k : Int := auxIDs.size + 1
        auxIDs := auxIDs.insert x.aux k
        am := am.push (x.aux, k)
      a := a.push v
  let f := { f with cache := { f.cache with auxmap := some am } }
  let partition := partitionValues c f auxIDs a
  let n := f.vidLast + 1
  let mut cls : Array Int := Array.replicate n 0
  for b in f.blocks do
    for v in (f.getB b).values do
      cls := cls.set! v (-(v : Int))
  let mut pNum : Int := 1
  for e in partition do
    for v in e do cls := cls.set! v pNum
    pNum := pNum + 1
  let mut s : St := { f, cls, partition, pNum, mem := Array.replicate n none }
  -- each round that does not stop splits a class
  let fuel := 4 * (n + partition.size) + 8
  for _ in [0:n + 2] do
    let (s', changed) ← refineRound c fuel s
    s := s'
    if !changed then break
  let (sdom, f) := s.f.sdom
  let mut rewrite : Array (Option ID) := Array.replicate n none
  for e in s.partition do
    let e := GoFV.Util.PdqSort.sortFunc (cmpDom c f sdom s.mem) e
    rewrite := classRewrites f sdom e rewrite
  return (applyRewrites f rewrite, rewrite)

/-- `cse(f)`. -/
def cse (c : CSE.Ctx) (f : Func) : Except String Func := (·.1) <$> cseRw c f

namespace CSE

/-! ## The checker -/

/-- The representative of `x` under the substitution `rw` (`x` itself if not replaced). -/
def rep (rw : Array (Option ID)) (x : ID) : ID := (rw.getD x none).getD x

/-- Ops whose first two arguments cse may have swapped. -/
def swappable (op : Op) : Bool := op.commutative

/-- `g`'s arguments `ga` are `f`'s `fa` through `rep`, the first two possibly swapped. -/
def argsOK (rw : Array (Option ID)) (op : Op) (fa ga : Array ID) : Bool :=
  ga == fa.map (rep rw) ||
    (swappable op && 2 ≤ fa.size && ga == (fa.swapIfInBounds 0 1).map (rep rw))

/-- Value `x` of `f` and `g`: the same but for its arguments (`argsOK`). -/
def valueOK (rw : Array (Option ID)) (f g : Func) (x : ID) : Bool :=
  match f.value? x with
  | none => true
  | some fv =>
    match g.value? x with
    | none => false
    | some gv =>
      gv.id == fv.id && gv.op == fv.op && gv.aux == fv.aux && gv.auxInt == fv.auxInt &&
      gv.type == fv.type && gv.block == fv.block && argsOK rw fv.op fv.args gv.args

/-- Block `bid` of `f` and `g`: same kind and values; each control kept or its representative. -/
def blockOK (rw : Array (Option ID)) (f g : Func) (bid : ID) : Bool :=
  match f.block? bid, g.block? bid with
  | some fb, some gb =>
    gb.kind == fb.kind && gb.values == fb.values && gb.controls.size == fb.controls.size &&
      (List.range fb.controls.size).all fun k =>
        gb.controls[k]! == fb.controls[k]! || gb.controls[k]! == rep rw fb.controls[k]!
  | _, _ => false

mutual
/-- Equality of type shapes (`Sem.Ty` derives no `BEq`). -/
def tyEq : Sem.Ty → Sem.Ty → Bool
  | .int w, .int w' => w == w'
  | .bool, .bool | .mem, .mem | .other, .other | .empty, .empty => true
  | .tuple ts, .tuple ts' => tysEq ts ts'
  | .ptr e, .ptr e' => e == e'
  | .agg fs n, .agg fs' n' => fieldsEq fs fs' && n == n'
  | .blob n, .blob n' => n == n'
  | .opaque n, .opaque n' => n == n'
  | _, _ => false

def tysEq : List Sem.Ty → List Sem.Ty → Bool
  | [], [] => true
  | t :: ts, t' :: ts' => tyEq t t' && tysEq ts ts'
  | _, _ => false

def fieldsEq : List (Nat × Sem.Ty) → List (Nat × Sem.Ty) → Bool
  | [], [] => true
  | (o, t) :: fs, (o', t') :: fs' => o == o' && tyEq t t' && fieldsEq fs fs'
  | _, _ => false
end

/-- The loads `x` (of `f`) and its representative `r` read the same address (up to `rep`) and
their memory chains reach the same def through stores disjoint from `x`'s access (`memEnd`, both
walked for `x`'s address and type); their memory arguments are not replaced, and `r`'s is in
another block, a `Phi` or a root (so a run evaluates it before `r` whenever it evaluates `r`). -/
def loadOK (tabs : Tables) (rw : Array (Option ID)) (f : Func) (fx fr : Value) : Bool :=
  match fx.args[0]?, fr.args[0]?, fx.args[1]?, fr.args[1]? with
  | some p, some p', some m, some m' =>
    rep rw p == rep rw p' && memEnd tabs f p fx.type m == memEnd tabs f p fx.type m' &&
      (rw.getD m none).isNone && (rw.getD m' none).isNone &&
      match f.value? m' with
      | some mv => mv.block != fr.block || mv.op == .Phi || Sem.prio mv.op != 0
      | none => false
  | _, _, _, _ => false

/-- The replaced value `x` and its representative `r` are congruent: same op, aux, auxint and
type shape, and the same (already substituted) arguments in `g`, except: `LocalAddr` (a named
local's address, independent of its memory argument) and `NilCheck` (its pointer, if it does
not panic) compare their first argument only; a `Load` may read through different memory
arguments, which with `strict` must pass `loadOK`. -/
def congr (tabs : Tables) (strict : Bool) (rw : Array (Option ID)) (f : Func)
    (fx fr gx gr : Value) : Bool :=
  fr.op == fx.op && fr.aux == fx.aux && fr.auxInt == fx.auxInt &&
    (fr.type == fx.type || tyEq (tabs.ty fr.type) (tabs.ty fx.type)) &&
    (gx.args == gr.args ||
      gx.args.size == gr.args.size && gx.args[0]? == gr.args[0]? &&
        ((fx.op == .LocalAddr && fx.aux.isSome) || fx.op == .NilCheck ||
          (fx.op == .Load && (!strict || loadOK tabs rw f fx fr))))

/-- The substitution of `x`, if any, is sound: its representative is not replaced, is listed
in its block, is congruent to it (`congr`), its block is an ancestor of `x`'s in `f`'s
dominator certificate, a `Phi` representative sits in `x`'s block, and the op is not a root
other than `NilCheck`. -/
def substOK (tabs : Tables) (strict : Bool) (c : DomCert.Cert) (rw : Array (Option ID))
    (f g : Func) (x : ID) : Bool :=
  match rw.getD x none with
  | none => true
  | some r =>
    (rw.getD r none).isNone &&
    match f.value? x, f.value? r, g.value? x, g.value? r with
    | some fx, some fr, some gx, some gr =>
      congr tabs strict rw f fx fr gx gr && (!Sem.isRoot fx.op || fx.op == .NilCheck) &&
        (fx.op != .Phi || fr.block == fx.block) && c.anc fr.block fx.block &&
        f.blocks.contains fr.block && ((f.block? fr.block).map (·.values.contains r)).getD false
    | _, _, _, _ => false

/-- A root for the scheduler (priority 1 or 2: `NilCheck`s, calls, stores, …). -/
def rootNode (f : Func) (x : ID) : Bool := ((f.value? x).map (Sem.prio ·.op)).getD 0 != 0

/-- A root list split at the priority-2 roots: each such root with the run of `NilCheck`s
that follows it (the first entry: the run before any, under `none`). -/
def runs (f : Func) (o : List ID) : List (Option ID × List ID) :=
  let step (acc : List (Option ID × List ID)) (x : ID) : List (Option ID × List ID) :=
    if ((f.value? x).map (Sem.prio ·.op)).getD 0 == 1 then
      match acc with
      | (r, run) :: acc => (r, x :: run) :: acc
      | [] => [(none, [x])]
    else (some x, []) :: acc
  ((o.foldl step [(none, [])]).map fun (r, run) => (r, run.reverse)).reverse

/-- The memory argument of `NilCheck` `x` in `g`. -/
def nilMem (g : Func) (x : ID) : Option ID := (g.value? x).bind (·.args[1]?)

/-- Root orders that agree up to permutations of a run of `NilCheck`s on one memory (each
panics, if at all, with that memory): accepted by the checker, outside `cse_refines`'
fragment unless the orders agree exactly. -/
def runsAgree (f g : Func) (oS oT : List ID) : Bool :=
  let rS := runs f oS
  let rT := runs f oT
  rS.length == rT.length && (rS.zip rT).all fun ((r, a), (r', b)) =>
    r == r' && (a == b || (a.mergeSort (· ≤ ·) == b.mergeSort (· ≤ ·) &&
      b.all fun x => nilMem g x == (b.head?.bind (nilMem g))))

/-- Block `bid`: if `f`'s block has a schedule, `g`'s has one listing the roots in the same
order (with `strict`; else up to `runsAgree`). -/
def schedOK (strict : Bool) (f g : Func) (bid : ID) : Bool :=
  match f.block? bid, g.block? bid with
  | some fb, some gb =>
    match Sem.schedule f fb with
    | none => true
    | some oS =>
      match Sem.schedule g gb with
      | some oT =>
        let rS := oS.toList.filter (rootNode f)
        let rT := oT.toList.filter (rootNode f)
        rT == rS || (!strict && runsAgree f g rS rT)
      | none => false
  | _, _ => false

/-- **cse's output relation**, checked against the substitution `rw`: `g` has `f`'s
control-flow graph, blocks and values, each argument and control redirected through `rw`
(arguments of commutative ops possibly swapped); every substitution is sound (`substOK`), and
every block of `g` has a schedule with the roots in `f`'s order (`schedOK`). -/
def crel (tabs : Tables) (strict : Bool) (f g : Func) (rw : Array (Option ID)) : Bool :=
  DomCert.cfgView g == DomCert.cfgView f && g.ownAux == f.ownAux &&
  g.valueTab.size == f.valueTab.size &&
  f.blocks.all (blockOK rw f g) &&
  (List.range f.valueTab.size).all (valueOK rw f g) &&
  (List.range rw.size).all (substOK tabs strict (DomCert.make f) rw f g) &&
  f.blocks.all (schedOK strict f g)

end CSE

/-- `cse`, validated by `CSE.crel` (the input if the checker rejects the result). A `Load`
merge through different memory arguments, and a reordering of `NilCheck`s on one memory, are
accepted as Go found them; the proof covers them when the strict check re-derives the merge
through disjoint stores and finds the roots in the same order (`CSE.inFrag`). -/
def cseChecked (c : CSE.Ctx) (f : Func) : Except String Func := do
  let (g, rw) ← cseRw c f
  return if CSE.crel c.tabs false f g rw then g else f

/-- The fragment `cse_refines` covers: cse fails, its result is rejected, or the strict
checker accepts it too (`Load` merges through different memory arguments pass `CSE.loadOK`,
roots keep their order). -/
def CSE.inFrag (c : CSE.Ctx) (f : Func) : Bool :=
  match cseRw c f with
  | .ok (g, rw) => !CSE.crel c.tabs false f g rw || CSE.crel c.tabs true f g rw
  | .error _ => true

/-- What `generic cse` reads from the pass environment (`typ.Mem`, the pointer size). -/
def cseCtx (env : PassEnv) : Except String CSE.Ctx := do
  let some mem := env.typ? "Mem" | throw "cse: no typ.Mem"
  let some #[.word ps] := env.config? "ptrsize" | throw "cse: config ptrsize"
  let some ptrSize := ps.toInt? | throw "cse: config ptrsize"
  return { tabs := env.tables, order := env.typeOrder, isMem := env.tables.isMemory mem, ptrSize }

/-- The `generic cse` pass. -/
def csePass : Pass := Pass.ofFunc fun env f => do cseChecked (← cseCtx env) f

/-- `cse_refines`' fragment for an input of the pass (`CSE.inFrag`). -/
def cseFrag (env : PassEnv) (f : Func) : Bool :=
  match cseCtx env with
  | .ok c => CSE.inFrag c f
  | .error _ => true

end GoFV.Opt

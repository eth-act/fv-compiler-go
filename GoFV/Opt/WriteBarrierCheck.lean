import GoFV.Opt.WriteBarrier
import GoFV.Opt.Checked
import GoFV.Opt.SchedFast
import GoFV.Opt.TabsAgree
import GoFV.Opt.RewriteCheck

/-!
# writebarrier, validated (issue #36)

`wbOK tabs f g` accepts `g` as a result of `writebarrier` on `f` whose write-barrier runs hold
only `Store`s, `VarDef`s and `VarLive`s (no `ZeroWB`/`MoveWB`, so no `wbZero`/`wbMove` calls:
those clobber the caller's outgoing-arguments area in the semantics, #36). Every block `b` of
`f` becomes a chain of blocks of `g` (`chainOf`): `c₀ = b`, and per expanded run `i` a split
`cᵢ₋₁ → tᵢ, cᵢ` (`Split`) on `Neq32 (Load <uint32> wbaddr memᵢ) const0`, with `tᵢ → cᵢ`;
the last block `c_K` has `b`'s kind, controls and successors, `c₀` `b`'s predecessors.

- Values: a value of `f` listed in `b` is *kept* (listed in `g` in one block of the chain, the
  fields the semantics reads unchanged, `sameV`), or a store of a run (`Run.src`: the memory
  chain from `memᵢ` to the run's last store `last`, which becomes `WBend` in `cᵢ`), or the run's
  nil check `nc` (dropped: `Invalid` or unlisted). A kept value's arguments are kept or `last`s
  and are not listed in a later block of the chain.
- New values of `g`: in `cᵢ₋₁` the flag `Load`/`Neq32`; in `tᵢ` (`thenOK`) the nil-check copy,
  at most one `WB [n] memᵢ` with its `Select0`/`Select1`, buffer pointers `OffPtr [8j]`
  (`j < n`), buffer `Store`s of `uintptr` (a memory chain from the `Select1`) and old-value
  `Load`s; in `cᵢ` (`endOK`) the memory `Phi [memᵢ, memThen]`, the nil-check copy, the run's
  stores re-emitted in order on that chain (`Run.tgt`, same fields, the nil check replaced by
  its copy) and `WBend`; `Invalid`s without arguments; in `g`'s entry block the lazily created
  `SB`, `SP`, `Addr`, `Const32` (`wbaddr`: `Addr {runtime.writeBarrier}`, `const0`:
  `Const32 [0]`, both listed there).
- Order: the non-pure nodes of `b`'s schedule are the kept ones of `c₀`, the dropped nil check,
  the run, the kept ones of `c₁`, … (`npOK`); the nil-check copies come first in `tᵢ` and `cᵢ`.
- Shapes: values of `f` whose shape holds a memory are memory ops (`memTyOK`), so every memory a
  run of `f` holds is one of theirs (`GoFV.Proof.WB` keeps the flag defined and `Blk.wbuf`
  absent along a run).

Schedules are computed by `SchedFast.schedFast`. `writebarrierChecked` runs the pass and returns
its result if `wbOK` accepts it and `f` runs the same in the result's tables (`tabsAgree`), else
an error.
-/

namespace GoFV.Opt.WBCheck

open GoFV.SSA

/-- The fields of `u` and `w` the semantics reads are equal (block and position may differ). -/
def sameV (u w : Value) : Bool :=
  u.id == w.id && u.op == w.op && u.type == w.type && u.auxInt == w.auxInt && u.aux == w.aux &&
    u.args == w.args

/-- The values of block `b` of `h`. -/
@[inline] def vals (h : Func) (b : ID) : Array ID := ((h.block? b).map (·.values)).getD #[]

/-- The symbol name an `Addr`'s aux names. -/
def symName? (tabs : Tables) (aux : Option AuxRef) : Option String :=
  match aux.bind tabs.aux? with
  | some { kind := .sym name .., .. } => some name.toStringLossy
  | _ => none

/-- The shape of value `x`'s type in `h`. -/
def shapeOf (tabs : Tables) (h : Func) (x : ID) : Sem.Ty :=
  match h.value? x with
  | some v => tabs.ty v.type
  | none => .other

/-- A shape that holds no memory (and no tuple, which may carry one). -/
def memFree : Sem.Ty → Bool
  | .mem | .tuple _ => false
  | .agg fs _ => memFreeFields fs
  | _ => true
where
  memFreeFields : List (Nat × Sem.Ty) → Bool
    | [] => true
    | (_, t) :: fs => memFree t && memFreeFields fs

/-- The ops of `f` whose values may hold memories: memory roots, calls, atomics, tuple ops. -/
def memOps : List Op :=
  [.InitMem, .Phi, .Copy, .Select0, .Select1, .SelectN, .MakeResult,
   .Store, .Move, .Zero, .VarDef, .VarLive, .KeepAlive, .PanicBounds,
   .StaticCall, .ClosureCall, .InterCall, .StaticLECall, .ClosureLECall, .InterLECall,
   .AtomicLoad32, .AtomicLoad64, .AtomicLoadPtr,
   .AtomicStore32, .AtomicStore64, .AtomicAdd32, .AtomicAdd32Variant, .AtomicAdd64,
   .AtomicCompareAndSwap32, .AtomicCompareAndSwap32Variant, .AtomicCompareAndSwap64,
   .AtomicCompareAndSwap64Variant]

@[inline] def memOpOK (op : Op) : Bool := memOps.contains op

/-- Every listed value of `f` whose shape may hold a memory is a memory op, and `f` has none of
the write-barrier ops. -/
def memTyOK (tabs : Tables) (f : Func) : Bool :=
  f.blocks.all fun b => (vals f b).all fun x =>
    match f.value? x with
    | some v =>
      v.op != .WB && v.op != .WBend && v.op != .StoreWB && v.op != .MoveWB &&
        v.op != .ZeroWB && (memFree (tabs.ty v.type) || memOpOK v.op)
    | none => false

/-- A split of block `c` of `g`: `If (Neq32 (Load wbaddr mem) const0)` to `t`, else `e`, both
blocks new (not blocks of `f`). -/
structure Split where
  c : ID
  t : ID
  e : ID
  flag : ID
  load : ID
  wbaddr : ID
  const0 : ID
  mem : ID
  deriving Inhabited, Repr

def splitOf? (f g : Func) (c : ID) : Option Split := do
  let C ← g.block? c
  guard (C.kind == .If && C.controls.size == 1 && C.succs.size == 2)
  let flag := C.controls[0]!
  let fv ← g.value? flag
  guard (fv.op == .Neq32 && fv.args.size == 2)
  let load := fv.args[0]!
  let lv ← g.value? load
  guard (lv.op == .Load && lv.args.size == 2)
  let t := C.succs[0]!
  let e := C.succs[1]!
  guard (t.i == 0 && e.i == 0 && t.b != e.b && !f.blocks.contains t.b && !f.blocks.contains e.b)
  return { c, t := t.b, e := e.b, flag, load, wbaddr := lv.args[0]!, const0 := fv.args[1]!,
           mem := lv.args[1]! }

/-- The chain of `g`'s blocks that block `b` of `f` became: the splits and the last block. -/
def chainOf (f g : Func) : Nat → ID → Option (List Split × ID)
  | 0, _ => none
  | fuel + 1, c =>
    match splitOf? f g c with
    | none => some ([], c)
    | some s => (chainOf f g fuel s.e).map fun (ss, l) => (s :: ss, l)

/-- A run: the source stores `src` (in memory order, from `mem`) and their copies `tgt` in the
end block, the last store `last` (`WBend` in `g`), the memory `Phi` and the nil checks. -/
structure Run where
  sp : Split
  src : List ID
  tgt : List ID
  last : ID
  phi : ID
  memThen : ID
  nc : Option ID
  ncEnd : Option ID
  deriving Inhabited, Repr

/-- The source chain of memory ops ending at `x`, `k` of them, back to memory `mem`. -/
def srcChain (f : Func) (mem : ID) : Nat → ID → Option (List ID)
  | 0, x => if x == mem then some [] else none
  | k + 1, x => do
    let v ← f.value? x
    guard (v.op == .Store || v.op == .VarDef || v.op == .VarLive)
    let m ← v.args.back?
    let l ← srcChain f mem k m
    return l ++ [x]

/-- The run of split `s` from the end block's values `[phi, ncEnd?, tgt…, last, …]`. -/
def runOf? (f g : Func) (s : Split) : Option Run := do
  let es := vals g s.e
  let phi ← es[0]?
  let pv ← g.value? phi
  guard (pv.op == .Phi && pv.args.size == 2 && pv.args[0]! == s.mem)
  let rest := es.toList.drop 1
  let (ncEnd, rest) := match rest with
    | x :: r => if (g.value? x).any (fun (v : Value) => v.op == Op.NilCheck) then (some x, r)
      else (none, rest)
    | [] => (none, rest)
  let k := rest.findIdx fun x => (g.value? x).any (fun (v : Value) => v.op == Op.WBend)
  let tgt := rest.take k
  let last ← rest[k]?
  let src ← srcChain f s.mem tgt.length last
  let s0 ← src.head?
  let v0 ← f.value? s0
  let nc : Option ID :=
    if v0.op == Op.Store then
      match v0.args[0]?.bind f.value? with
      | some n => if n.op == Op.NilCheck && n.args[1]? == some s.mem then some n.id else none
      | none => none
    else none
  return { sp := s, src, tgt, last, phi, memThen := pv.args[1]!, nc, ncEnd }

section Check

variable (tabs : Tables) (f g : Func)

/-- `x` is a value of `f` kept in `g`: listed in both, the same fields. -/
def keptMarks : Array Bool :=
  let Lf := RewriteCheck.listedMarks f
  let Lg := RewriteCheck.listedMarks g
  (List.range (max f.valueTab.size g.valueTab.size)).toArray.map fun x =>
    Lf.getD x false && Lg.getD x false &&
      match f.value? x, g.value? x with
      | some u, some w => sameV u w
      | _, _ => false

/-- The re-emitted store `y` of `g` copies the source store `x` (the nil check `nc` replaced by
its copy `ncEnd`) on memory `m`. -/
def copyOK (nc ncEnd : Option ID) (x y m : ID) : Bool :=
  match f.value? x, g.value? y with
  | some u, some w =>
    w.op == u.op && w.type == u.type && w.aux == u.aux && w.auxInt == u.auxInt &&
    w.args.size == u.args.size && w.args.back? == some m &&
    (List.range (u.args.size - 1)).all fun j =>
      let a := u.args[j]!
      w.args[j]! == (if nc == some a && j == 0 then ncEnd.getD a else a)
  | _, _ => false

/-- The copies `tgt` of the source stores `src` form a memory chain from `m`. -/
def copiesOK (nc ncEnd : Option ID) : ID → List ID → List ID → Bool
  | _, [], [] => true
  | m, x :: xs, y :: ys => copyOK f g nc ncEnd x y m && copiesOK nc ncEnd y xs ys
  | _, _, _ => false

/-- The nil-check copy `y` of `nc` on memory `m`. -/
def ncCopyOK (nc : ID) (y m : ID) : Bool :=
  match f.value? nc, g.value? y with
  | some u, some w =>
    w.op == .NilCheck && w.type == u.type && w.args.size == 2 && u.args.size == 2 &&
      w.args[0]! == u.args[0]! && w.args[1]! == m
  | _, _ => false

/-- The non-pure nodes of block `c` of `h` in their schedule's order. -/
def npSeq (h : Func) (c : ID) : Option (List ID) := do
  let C ← h.block? c
  let o ← SchedFast.schedFast h C
  return o.toList.filter (npOf h C)

end Check

/-- What the check needs about a block chain: kept marks `K`, the `last`s `Lst`, the segment
index of every value listed in the chain. -/
structure Ctx where
  tabs : Tables
  f : Func
  g : Func
  K : Array Bool
  /-- `WBend`s of `g` that were the last store of a run. -/
  Lst : Array Bool
  wbaddr : ID
  const0 : ID

namespace Ctx

variable (c : Ctx)

/-- Kept or the `WBend` of a run: holds the source's value. -/
@[inline] def held (x : ID) : Bool := c.K.getD x false || c.Lst.getD x false

/-- An argument `a` available in segment `j` of the chain `segs` (and not a value of `b` listed
in a later segment). -/
def availIn (b : ID) (segs : List ID) (j : Nat) (a : ID) : Bool :=
  c.held a &&
    (!((vals c.f b).contains a || segs.any fun s => (vals c.g s).contains a) ||
      (segs.take (j + 1)).any fun s => (vals c.g s).contains a)

/-- The buffer block `t` of run `r`: see the module doc. -/
def thenOK (b : ID) (segs : List ID) (j : Nat) (r : Run) : Bool := Id.run do
  let s := r.sp
  let some T := c.g.block? s.t | return false
  if !(T.id == s.t && T.kind == .Plain && T.controls.isEmpty && T.succs == #[⟨s.e, 1⟩]) then
    return false
  let xs := T.values.toList
  let ncThen := xs.filter fun x => (c.g.value? x).any (·.op == .NilCheck)
  let wbs := xs.filter fun x => (c.g.value? x).any (·.op == .WB)
  if wbs.length > 1 then return false
  match r.nc, ncThen with
  | some n, [y] => if !ncCopyOK c.f c.g n y s.mem then return false
  | none, [] => pure ()
  | _, _ => return false
  -- the WB and its selects
  let wb? := wbs.head?
  let n : Nat := match wb?.bind c.g.value? with
    | some w => w.auxInt.toInt.toNat
    | none => 0
  let sel (i : Nat) : List ID := xs.filter fun x => (c.g.value? x).any fun v =>
    v.op == (if i == 0 then .Select0 else .Select1) && some (v.args[0]!) == wb? && v.args.size == 1
  let sel0 := (sel 0).head?
  let sel1 := (sel 1).head?
  -- the buffer's memory chain: the `Select1` and buffer stores
  let isChain (m : ID) : Bool := some m == sel1 ||
    (xs.contains m && (c.g.value? m).any (·.op == .Store))
  let avail := c.availIn b segs j
  let ok := xs.all fun x => match c.g.value? x with
    | none => false
    | some v =>
      match v.op with
      | .NilCheck => true
      | .WB => v.args == #[s.mem] && 0 < n &&
          (match c.tabs.ty v.type with | .tuple [.ptr _, .mem] => true | _ => false)
      | .Select0 => some x == sel0 && (match c.tabs.ty v.type with | .ptr _ => true | _ => false)
      | .Select1 => some x == sel1 && (match c.tabs.ty v.type with | .mem => true | _ => false)
      | .OffPtr => v.args.size == 1 && some v.args[0]! == sel0 && 0 ≤ v.auxInt.toInt &&
          v.auxInt.toInt % 8 == 0 && v.auxInt.toInt / 8 < n &&
          (match c.tabs.ty v.type with | .ptr _ => true | _ => false)
      | .Store => v.args.size == 3 &&
          (c.g.value? v.args[0]!).any (fun p => p.op == .OffPtr && xs.contains p.id) &&
          (avail v.args[1]! || xs.contains v.args[1]!) && isChain v.args[2]! &&
          (match Sem.auxTy c.tabs v.aux with | .int .w64 => true | _ => false) &&
          (match c.tabs.ty v.type with | .mem => true | _ => false)
      | .Load => v.args.size == 2 && (avail v.args[0]! || ncThen.contains v.args[0]!) &&
          (v.args[1]! == s.mem || isChain v.args[1]!)
      | _ => false
  -- one select per kind, the buffer stores and selects only with a WB
  let memThenOK := r.memThen == s.mem || (wb?.isSome && isChain r.memThen)
  let headOK := match ncThen, npSeq c.g s.t with
    | [y], some (z :: _) => y == z
    | [], some _ => true
    | _, _ => false
  return ok && memThenOK && headOK && (sel 0).length ≤ 1 && (sel 1).length ≤ 1

/-- The end block `e` of run `r`: `[phi, ncEnd?, tgt…, last] ++ kept`. -/
def endOK (r : Run) : Bool :=
  let s := r.sp
  match c.g.block? s.e with
  | none => false
  | some E =>
    E.id == s.e && E.preds == #[⟨s.c, 1⟩, ⟨s.t, 0⟩] &&
    (c.g.value? r.phi).any (fun p => p.args == #[s.mem, r.memThen] &&
      (match c.tabs.ty p.type with | .mem => true | _ => false)) &&
    (match r.nc, r.ncEnd with
      | some n, some y => ncCopyOK c.f c.g n y r.phi &&
          (match npSeq c.g s.e with | some (z :: _) => z == y | _ => false)
      | none, none => true
      | _, _ => false) &&
    copiesOK c.f c.g r.nc r.ncEnd r.phi r.src r.tgt &&
    r.tgt.all (fun y => (c.g.value? y).any fun w =>
      match c.tabs.ty w.type with | .mem => true | _ => false) &&
    (c.g.value? r.last).any (fun w => w.op == .WBend && some w.args == r.tgt.getLast?.map (#[·]) &&
      w.aux.isNone && (c.f.value? r.last).any (·.type == w.type)) &&
    (c.f.value? r.last).any (fun u => u.op == .Store || u.op == .VarDef || u.op == .VarLive) &&
    !c.K.getD r.last false

/-- The new values allowed in segment `j` of the chain of `b`: the flag of the next split, the
end block's run values, `Invalid`s, and in `g`'s entry the lazily created values. -/
def newOK (b : ID) (runs : List Run) (j : Nat) (x : ID) : Bool :=
  match c.g.value? x with
  | none => false
  | some v =>
    (v.op == .Invalid && v.args.isEmpty) ||
    (match runs[j]? with
      | some r => x == r.sp.flag || x == r.sp.load
      | none => false) ||
    (match j, runs[j - 1]? with
      | j + 1, some r => x == r.phi || some x == r.ncEnd || r.tgt.contains x || x == r.last
      | _, _ => false) ||
    (b == c.f.entry && j == 0 &&
      ((v.op == .SB || v.op == .SP || v.op == .Const32) && v.args.isEmpty ||
       (v.op == .Addr && v.args.size == 1)))

/-- The flag of split `s`: `Neq32 (Load <uint32> wbaddr mem) const0`. -/
def flagOK (s : Split) : Bool :=
  s.wbaddr == c.wbaddr && s.const0 == c.const0 &&
  (c.g.value? s.load).any (fun v =>
    (match c.tabs.ty v.type with | .int .w32 => true | _ => false)) &&
  (c.g.value? s.flag).any (fun v => match c.tabs.ty v.type with | .bool => true | _ => false)

/-- The kept non-pure nodes of segment `c` in schedule order. -/
def keptNP (seg : ID) : Option (List ID) :=
  (npSeq c.g seg).map (·.filter (c.K.getD · false))

/-- The source schedule's non-pure nodes: the kept ones of `c₀`, then per run the dropped nil
check and the run's stores, then the kept ones of `cᵢ`. -/
def npOK (b : ID) (runs : List Run) (segs : List ID) : Bool :=
  match npSeq c.f b, segs.mapM c.keptNP with
  | some src, some ks =>
    let pieces := ks.zipIdx.flatMap fun (k, j) =>
      match j, runs[j - 1]? with
      | j + 1, some r =>
        (match r.nc with
          | some n => if c.K.getD n false then [] else [n]
          | none => []) ++ r.src ++ k
      | _, _ => k
    src == pieces
  | _, _ => false

/-- Block `b` of `f` and its chain in `g`. -/
def blockOK (b : ID) : Bool := Id.run do
  let some B := c.f.block? b | return false
  let some (splits, last) := chainOf c.f c.g (c.g.blocks.size + 1) b | return false
  let some runs := splits.mapM (runOf? c.f c.g) | return false
  let segs := b :: splits.map (·.e)
  if !(segs.getLast? == some last) then return false
  let some L := c.g.block? last | return false
  let some C0 := c.g.block? b | return false
  -- the chain's ends
  if !(C0.id == b && L.id == last && L.kind == B.kind &&
      L.controls == B.controls && L.succs == B.succs && B.controls.all c.held) then return false
  -- distinct blocks
  let blocksT := segs ++ splits.map (·.t)
  if blocksT.eraseDups.length != blocksT.length then return false
  -- the runs
  if !(runs.zipIdx.all fun (r, i) =>
      c.flagOK r.sp && c.endOK r && c.thenOK b segs i r &&
      (match r.nc with
        | some n => c.K.getD n false || (B.values.contains n &&
            (c.g.value? n).all (fun v => v.op == .Invalid && v.args.isEmpty))
        | none => true) &&
      r.src.all (fun x => B.values.contains x && !c.K.getD x false)) then return false
  -- the values of b
  if !(B.values.all fun x =>
      (c.K.getD x false && (segs.filter fun s => (vals c.g s).contains x).length == 1) ||
        runs.any (fun r => r.src.contains x) || runs.any (fun r => r.nc == some x)) then
    return false
  -- the values of the segments
  let segOK := segs.zipIdx.all fun (s, j) => (vals c.g s).all fun x =>
    if c.K.getD x false then
      B.values.contains x &&
      (match c.f.value? x with
        | some u => (u.op == .Phi → j == 0) &&
            (u.op == .Phi || u.args.all (c.availIn b segs j))
        | none => false)
    else c.newOK b runs j x
  if !segOK then return false
  return c.npOK b runs segs

end Ctx

/-- **The check of a `writebarrier` result.** -/
def wbOK (tabs : Tables) (f g : Func) : Bool := Id.run do
  if !(g.entry == f.entry && g.ownAux == f.ownAux && memTyOK tabs f) then return false
  let K := keptMarks f g
  -- the `WBend`s that were last stores
  let mut Lst := Array.replicate g.valueTab.size false
  let mut lazy : Option (ID × ID) := none
  for b in f.blocks do
    let some (splits, _) := chainOf f g (g.blocks.size + 1) b | return false
    for s in splits do
      lazy := some (s.wbaddr, s.const0)
      match runOf? f g s with
      | some r => Lst := Lst.set! r.last true
      | none => return false
  let (wbaddr, const0) := lazy.getD (0, 0)
  if lazy.isSome then
    let ge := vals g g.entry
    let okA := (g.value? wbaddr).any fun v => v.op == .Addr &&
      symName? tabs v.aux == some "runtime.writeBarrier" &&
      (match tabs.ty v.type with | .ptr _ => true | _ => false)
    let okC := (g.value? const0).any fun (v : Value) =>
      v.op == Op.Const32 && v.auxInt == (0 : Int64) && v.args.isEmpty &&
        (match tabs.ty v.type with | .int .w32 => true | _ => false)
    if !(okA && okC && ge.contains wbaddr && ge.contains const0) then return false
  let c : Ctx := { tabs, f, g, K, Lst, wbaddr, const0 }
  return f.blocks.all c.blockOK

end GoFV.Opt.WBCheck

namespace GoFV.Opt

open GoFV.SSA

/-- **writebarrier, validated**: the pass's result if `WBCheck.wbOK` accepts it and `f` runs the
same in the result's tables, else an error. -/
def writebarrierChecked : Pass := fun env f => do
  let out ← writebarrier env f
  if tabsAgree env.tables out.tables f && WBCheck.wbOK out.tables f out.func then return out
  else throw "writebarrier: result rejected by the checker"

end GoFV.Opt

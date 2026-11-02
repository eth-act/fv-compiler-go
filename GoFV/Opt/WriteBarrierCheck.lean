import GoFV.Opt.WriteBarrier
import GoFV.Opt.Checked
import GoFV.Opt.TabsAgree
import GoFV.Opt.RewriteCheck

/-!
# writebarrier, validated (issue #36)

`wbOK tabs f g` accepts `g` as a result of `writebarrier` on `f` whose write-barrier runs hold
`Store`s, `Move`s, `Zero`s, `VarDef`s and `VarLive`s. Every block `b` of `f` becomes a chain of
blocks of `g` (`chainOf`): `c₀ = b`, and per expanded run `j` a split
`cⱼ → tⱼ₊₁, cⱼ₊₁` (`Split`) on `Neq32 (Load <uint32> wbaddr memⱼ) const0`, with `tⱼ₊₁ → cⱼ₊₁`;
the last block `c_K` has `b`'s kind, controls and successors.

Every value listed in a block of the chain has a *role* (`roleOf`, first match): *held* (kept:
a value of `f` listed in `g` with the fields the semantics reads unchanged, `sameV`; or the
last store `last` of a run, which becomes `WBend` in its end block: either way it holds the
source's register), the write-barrier flag's address `wbaddr` (a new value, never held) and the
constant `const0` (values of `g`'s entry block), a value of run `j` (`roleRun`: in `cⱼ` the flag
`Load`/`Neq32` and the type addresses `Addr {type:T} SB` of the helper calls, `SB` the flag
address's; in `cⱼ₊₁` the memory `Phi [memⱼ, memThen]`, the nil-check copy and the run's
stores re-emitted in order, `Run.tgt`; in `tⱼ₊₁` by op (`thenRole`): the nil-check copy,
`WB [n]`s (`n ≤ 8`, one per 8 buffer entries: on `memⱼ` or on the last buffer `Store` of the
previous one) with their `Select0`/`Select1`, buffer pointers `OffPtr [8k]` (`k < n` of their
`WB`, `offSize`), buffer `Store`s of `uintptr` through them on a memory chain from the
`Select1` of the same `WB` (`memWb`) and old-value `Load`s, and the
`runtime.wbZero(typ, dst)`/`runtime.wbMove(typ, dst, src)` calls (`StaticCall`, register
arguments only, the arguments of one of the run's `Zero`s/`Move`s) with their memory
`SelectN [0]`), the lazily created `SB`/`SP`/`Const32`/`Addr` of `g`'s entry, or an argument-free
`Invalid` (`otherRole`).
`roleOK` checks each role's fields, arguments and block; arguments of new values that are held
are arguments of a source value of `b`, or of a source value outside `b` that one reads (`srcArg`;
so they are available where the source evaluates that value). `runOK` also checks that each run's
values are listed where their roles say (flag in `cⱼ`, copies and `WBend` in `cⱼ₊₁`), that the
run's memory is held, that its nil check is a value of `b` or kept (one of a dominating block) and
the nil-check copies have their roles; `blockOK` that the chain's blocks are listed in `g` and
every kept value of `b` is listed in a segment.

Order: the non-pure nodes of `b`'s schedule are the kept ones of `c₀`, then per run the dropped
nil check and the run's stores, then the kept ones of `cⱼ₊₁` (`npOK`); the nil-check copies
come first in `tⱼ₊₁` and `cⱼ₊₁`. Shapes: values of `f` whose shape holds a memory are memory ops
(`memTyOK`), so every memory a run of `f` holds is one of theirs (`GoFV.Proof.WB` keeps the
flag defined and `Blk.wbuf` absent along a run).

`writebarrierChecked` runs the pass and returns its result if `wbOK` accepts it and `f` runs the
same in the result's tables (`tabsAgree`), else an error.
-/

namespace GoFV.Opt.WBCheck

open GoFV.SSA

/-- The fields of `u` and `w` the semantics reads are equal (block and position may differ). -/
def sameV (u w : Value) : Bool :=
  u.id == w.id && u.op == w.op && u.type == w.type && u.auxInt == w.auxInt && u.aux == w.aux &&
    u.args == w.args

/-- `v`'s type has shape `t`. -/
@[inline] def tyIs (tabs : Tables) (v : Value) (p : Sem.Ty → Bool) : Bool := p (tabs.ty v.type)

def isMemTy : Sem.Ty → Bool
  | .mem => true
  | _ => false

def isPtrTy : Sem.Ty → Bool
  | .ptr _ => true
  | _ => false

/-! ## The chain of a block -/

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
    guard (v.op == .Store || v.op == .VarDef || v.op == .VarLive || v.op == .Move ||
      v.op == .Zero)
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
    if v0.op == Op.Store || v0.op == Op.Move || v0.op == Op.Zero then
      match v0.args[0]?.bind f.value? with
      | some n => if n.op == Op.NilCheck && n.args[1]? == some s.mem then some n.id else none
      | none => none
    else none
  return { sp := s, src, tgt, last, phi, memThen := pv.args[1]!, nc, ncEnd }

/-- The runs and the last block of `b`'s chain. -/
def chainRuns? (f g : Func) (b : ID) : Option (List Run × ID) := do
  let (ss, l) ← chainOf f g (g.blocks.size + 1) b
  let rs ← ss.mapM (runOf? f g)
  return (rs, l)

/-- The segments `c₀ = b, c₁, …` of a chain. -/
def segsOf (b : ID) (rs : List Run) : List ID := b :: rs.map (·.sp.e)

/-! ## Marks -/

/-- `x` is a value of `f` kept in `g`: listed in both, the same fields. -/
def keptMarks (f g : Func) : Array Bool :=
  let Lf := RewriteCheck.listedMarks f
  let Lg := RewriteCheck.listedMarks g
  (List.range (max f.valueTab.size g.valueTab.size)).toArray.map fun x =>
    Lf.getD x false && Lg.getD x false &&
      match f.value? x, g.value? x with
      | some u, some w => sameV u w
      | _, _ => false

/-- The last stores of the runs of all chains. -/
def lastMarks (f g : Func) : Array Bool :=
  f.blocks.foldl (init := Array.replicate g.valueTab.size false) fun L b =>
    match chainRuns? f g b with
    | some (rs, _) => rs.foldl (fun L r => L.set! r.last true) L
    | none => L

/-! ## Roles -/

/-- The role of a value listed in a block of a chain (see the module doc). -/
inductive Role where
  | held
  | wbaddr
  | const0
  | lazy
  | invalid
  | load (j : Nat)
  | flag (j : Nat)
  | phi (j : Nat)
  | ncEnd (j : Nat)
  | tgt (j k : Nat)
  | ncThen (j : Nat)
  | wb (j : Nat)
  | sel0 (j : Nat)
  | sel1 (j : Nat)
  | off (j : Nat)
  | bstore (j : Nat)
  | tload (j : Nat)
  | taddr (j : Nat)
  | call (j : Nat)
  | seln (j : Nat)
  | none
  deriving DecidableEq, Repr, Inhabited

/-- The role of value `v` of run `j`'s buffer block, by op. -/
def thenRole (v : Value) (j : Nat) : Role :=
  if v.op == .NilCheck then .ncThen j
  else if v.op == .WB then .wb j
  else if v.op == .Select0 then .sel0 j
  else if v.op == .Select1 then .sel1 j
  else if v.op == .OffPtr then .off j
  else if v.op == .Store then .bstore j
  else if v.op == .Load then .tload j
  else if v.op == .StaticCall then .call j
  else if v.op == .SelectN then .seln j
  else .none

/-- The role of `x` among the values of run `j` and the later runs. -/
def roleRun (g : Func) (x : ID) : List Run → Nat → Role
  | [], _ => .none
  | r :: rs, j =>
    if x == r.sp.load then .load j
    else if x == r.sp.flag then .flag j
    else if x == r.phi then .phi j
    else if r.ncEnd == some x then .ncEnd j
    else match r.tgt.idxOf? x with
      | some k => .tgt j k
      | none =>
        if (vals g r.sp.t).contains x then ((g.value? x).map (thenRole · j)).getD .none
        else if (vals g r.sp.c).contains x && (g.value? x).any (·.op == .Addr) then .taddr j
        else roleRun g x rs (j + 1)

/-- The role of a value of no run: an argument-free `Invalid`, or a lazily created value of
`g`'s entry. -/
def otherRole (g : Func) (x : ID) : Role :=
  match g.value? x with
  | some v =>
    if v.op == .Invalid && v.args.isEmpty then .invalid
    else if ((v.op == .SB || v.op == .SP || v.op == .Const32) && v.args.isEmpty) ||
        (v.op == .Addr && v.args.size == 1) then .lazy
    else .none
  | none => .none

/-- What the check reads besides the two functions. -/
structure Ctx where
  tabs : Tables
  f : Func
  g : Func
  K : Array Bool
  /-- `WBend`s of `g` that were the last store of a run. -/
  Lst : Array Bool
  /-- The flag address `Addr {runtime.writeBarrier}` and `Const32 [0]` of `g`'s entry, if
  there are runs. -/
  lazy : Option (ID × ID)

/-- A parameter of a write-barrier helper: an input in one register, of shape `uintptr`. -/
def wbParam (tabs : Tables) (p : ABIParam) : Bool :=
  !p.out && p.regs.size == 1 && (match tabs.ty p.type with | .int .w64 => true | _ => false)

namespace Ctx

variable (c : Ctx)

/-- Kept or the `WBend` of a run: holds the source's value. -/
@[inline] def held (x : ID) : Bool := c.K.getD x false || c.Lst.getD x false

@[inline] def isWbaddr (x : ID) : Bool := c.lazy.any (·.1 == x)
@[inline] def isConst0 (x : ID) : Bool := c.lazy.any (·.2 == x)

/-- The `SB` the flag address reads. -/
def sbOf : Option ID := c.lazy.bind fun (wa, _) => (c.g.value? wa).bind (·.args[0]?)

@[inline] def isSb (x : ID) : Bool := c.sbOf == some x

/-- The role of a value of a block of the chain of runs `rs`. -/
def roleOf (rs : List Run) (x : ID) : Role :=
  if c.isWbaddr x then .wbaddr
  else if c.isConst0 x then .const0
  else if c.held x then .held
  else match roleRun c.g x rs 0 with
    | .none => otherRole c.g x
    | r => r

/-- `a` is an argument of a non-`Phi` value of block `b` of `f`, or of a non-`Phi` value outside
`b` that is one (a kept nil check of a dominating block whose pointer a nil-check copy reads). -/
def srcArg (B : Block) (a : ID) : Bool :=
  B.values.any fun y => (c.f.value? y).any fun u => u.op != .Phi &&
    (u.args.contains a || u.args.any fun y' => !B.values.contains y' &&
      (c.f.value? y').any fun u' => u'.op != .Phi && u'.args.contains a)

/-- An argument `a` available in segment `j` of the chain `segs` of block `B`: held, and either
not a value of `B` (then an argument of a non-`Phi` value of `B` or of one of its non-`Phi`
arguments, `srcArg`) or listed in a segment up to `j`. -/
def availIn (B : Block) (segs : List ID) (j : Nat) (a : ID) : Bool :=
  c.held a &&
    (if B.values.contains a then (segs.take (j + 1)).any fun s => (vals c.g s).contains a
     else c.srcArg B a)

/-- The store `y` of `g` re-emits the source store `x` (the nil check `nc` replaced by its copy
`ncEnd`) on memory `m`, its other arguments available in segment `j`. -/
def copyOK (B : Block) (segs : List ID) (j : Nat) (nc ncEnd : Option ID) (x y m : ID) : Bool :=
  match c.f.value? x, c.g.value? y with
  | some u, some w =>
    w.op == u.op && w.type == u.type && w.aux == u.aux && w.auxInt == u.auxInt &&
    w.args.size == u.args.size && w.args.back? == some m && tyIs c.tabs w isMemTy &&
    (List.range (u.args.size - 1)).all fun i =>
      let a := u.args[i]!
      if nc == some a && i == 0 then w.args[i]! == ncEnd.getD a
      else w.args[i]! == a && c.availIn B segs j a
  | _, _ => false

/-- The nil-check copy `y` of `nc` on memory `m`. -/
def ncCopyOK (B : Block) (segs : List ID) (j : Nat) (nc : ID) (y m : ID) : Bool :=
  match c.f.value? nc, c.g.value? y with
  | some u, some w =>
    u.op == .NilCheck && w.op == .NilCheck && w.type == u.type && w.args.size == 2 &&
      u.args.size == 2 && w.args[0]! == u.args[0]! && w.args[1]! == m &&
      c.availIn B segs j u.args[0]!
  | _, _ => false

/-- The non-pure nodes of block `C` of `h` in their schedule's order. -/
def npSeq (h : Func) (C : Block) : Option (List ID) :=
  (Sem.schedule h C).map fun o => o.toList.filter (npOf h C)

/-- The kept non-pure nodes of segment `s` in schedule order. -/
def keptNP (s : ID) : Option (List ID) := do
  let C ← c.g.block? s
  let l ← npSeq c.g C
  return l.filter (c.K.getD · false)

/-- An argument of a buffer-block value of run `r` in segment `j`: an argument of one of the
run's source stores, available there. -/
def runArg (B : Block) (segs : List ID) (j : Nat) (r : Run) (a : ID) : Bool :=
  r.src.any (fun s => (c.f.value? s).any (·.args.contains a)) && c.availIn B segs j a

/-- The memory of run `i`'s buffer block at `m`: the run's memory, or the memory after a buffer
store or a helper call of the run. -/
def tMem (rs : List Run) (r : Run) (i : Nat) (m : ID) : Bool :=
  m == r.sp.mem || (match c.roleOf rs m with
    | .sel1 k | .bstore k | .seln k => k == i
    | _ => false)

/-- The size `n` of the `WB [n]` `x`. -/
def wbSize (x : ID) : Nat := ((c.g.value? x).map (·.auxInt.toInt.toNat)).getD 0

/-- The first argument of `x`. -/
def arg0 (x : ID) : Option ID := (c.g.value? x).bind (·.args[0]?)

/-- The `WB` whose buffer the pointer `o = OffPtr (Select0 wb)` points into. -/
def offWb (o : ID) : Option ID := (c.arg0 o).bind c.arg0

/-- The `WB` whose buffer the memory `m` holds: a `Select1` of it, or a buffer `Store` through
one of its pointers. -/
def memWb (rs : List Run) (m : ID) : Option ID :=
  match c.roleOf rs m with
  | .sel1 _ => c.arg0 m
  | .bstore _ => (c.arg0 m).bind c.offWb
  | _ => none

/-- The number of entries of the buffer the pointer `o` points into. -/
def offSize (o : ID) : Nat := ((c.offWb o).map c.wbSize).getD 0

/-- The number of entries of the buffer the memory `m` holds. -/
def memSize (rs : List Run) (m : ID) : Nat := ((c.memWb rs m).map c.wbSize).getD 0

/-- The helper call `w` of run `r` (number `i`, its buffer block checked as segment `j`'s):
`wbZero(typ, dst)` or `wbMove(typ, dst, src)` with register arguments of shape `uintptr`, `typ` a
type address of the run, `dst`/`src` the arguments of one of the run's `Zero`s/`Move`s (`dst`
possibly its nil-check copy), on a memory of the buffer block. -/
def wbCallOK (B : Block) (segs : List ID) (j : Nat) (rs : List Run) (r : Run) (i : Nat)
    (w : Value) : Bool :=
  match w.aux.bind c.tabs.callee?, Sem.callABI? c.tabs w.aux with
  | some name, some abi =>
    let n := w.args.size - 1
    (if name == "runtime.wbZero" then n == 2 else name == "runtime.wbMove" && n == 3) &&
    abi.params.size == n && abi.params.all (wbParam c.tabs) &&
    c.roleOf rs w.args[0]! == .taddr i &&
    (match w.args.back? with
      | some m => c.tMem rs r i m
      | none => false) &&
    r.src.any fun s => match c.f.value? s with
      | some u =>
        u.args.size == n &&
        (if n == 2 then u.op == .Zero
         else u.op == .Move && w.args[2]! == u.args[1]! && c.availIn B segs j u.args[1]!) &&
        ((w.args[1]! == u.args[0]! && c.availIn B segs j u.args[0]!) ||
          (r.nc == some u.args[0]! && c.roleOf rs w.args[1]! == .ncThen i))
      | none => false
  | _, _ => false

/-- The role-specific conditions of value `x` listed in segment `j` (`inT = false`) or in the
buffer block of run `j` (`inT = true`) of the chain of block `b`. -/
def roleOK (b : ID) (B : Block) (segs : List ID) (rs : List Run) (inT : Bool) (j : Nat)
    (x : ID) : Bool :=
  match c.g.value? x with
  | none => false
  | some w =>
    match c.roleOf rs x with
    | .held =>
      !inT && B.values.contains x &&
      (if c.K.getD x false then
        match c.f.value? x with
        | some u =>
          if u.op == .Phi then j == 0 && u.args.all c.held
          else u.args.all (c.availIn B segs j)
        | none => false
      else (match j, rs[j - 1]? with
        | j' + 1, some r => r.last == x && w.op == .WBend && w.args.size == 1 &&
            w.args[0]? == r.tgt.getLast? && w.aux.isNone && tyIs c.tabs w isMemTy &&
            (c.f.value? x).any (·.type == w.type) &&
            c.roleOf rs w.args[0]! == .tgt j' (r.tgt.length - 1)
        | _, _ => false))
    | .wbaddr | .const0 | .lazy =>
      !inT && b == c.f.entry && j == 0 && (!c.held x || B.values.contains x) &&
        w.args.all fun a => (vals c.g b).contains a
    | .invalid => !inT && w.op == .Invalid && w.args.isEmpty
    | .load i =>
      !inT && i == j &&
      (match rs[i]? with
        | some r => w.op == .Load && w.args == #[r.sp.wbaddr, r.sp.mem] &&
            (match c.tabs.ty w.type with | .int .w32 => true | _ => false) &&
            c.isWbaddr r.sp.wbaddr && c.availIn B segs j r.sp.mem
        | none => false)
    | .flag i =>
      !inT && i == j &&
      (match rs[i]? with
        | some r => w.op == .Neq32 && w.args == #[r.sp.load, r.sp.const0] &&
            (match c.tabs.ty w.type with | .bool => true | _ => false) && c.isConst0 r.sp.const0 &&
            c.roleOf rs r.sp.load == .load i
        | none => false)
    | .phi i =>
      !inT && j == i + 1 &&
      (match rs[i]? with
        | some r => w.op == .Phi && w.args == #[r.sp.mem, r.memThen] && tyIs c.tabs w isMemTy &&
            (r.memThen == r.sp.mem ||
              (match c.roleOf rs r.memThen with
                | .sel1 k | .bstore k | .seln k => k == i
                | _ => false))
        | none => false)
    | .ncEnd i =>
      !inT && j == i + 1 &&
      (match rs[i]? with
        | some r => (match r.nc with
            | some n => c.ncCopyOK B segs j n x r.phi && c.roleOf rs r.phi == .phi i
            | none => false)
        | none => false)
    | .tgt i k =>
      !inT && j == i + 1 &&
      (match rs[i]? with
        | some r =>
          match r.src[k]?, r.tgt[k]? with
          | some s, some y => y == x &&
              c.copyOK B segs j r.nc r.ncEnd s x (if k == 0 then r.phi else r.tgt[k - 1]!) &&
              c.roleOf rs (if k == 0 then r.phi else r.tgt[k - 1]!) ==
                (if k == 0 then .phi i else .tgt i (k - 1))
          | _, _ => false
        | none => false)
    | .ncThen i =>
      inT && i == j &&
      (match rs[i]? with
        | some r => (match r.nc with
            | some n => c.ncCopyOK B segs j n x r.sp.mem
            | none => false)
        | none => false)
    | .wb i =>
      inT && i == j && w.args.size == 1 && 0 < w.auxInt.toInt && w.auxInt.toInt ≤ 8 &&
      (match c.tabs.ty w.type with | .tuple [.ptr _, .mem] => true | _ => false) &&
      (match rs[i]? with
        | some r => w.args[0]! == r.sp.mem || (match c.roleOf rs w.args[0]! with
            | .sel1 k | .bstore k => k == i
            | _ => false)
        | none => false)
    | .sel0 i =>
      inT && i == j && w.args.size == 1 && tyIs c.tabs w isPtrTy &&
        c.roleOf rs w.args[0]! == .wb i
    | .sel1 i =>
      inT && i == j && w.args.size == 1 && tyIs c.tabs w isMemTy &&
        c.roleOf rs w.args[0]! == .wb i
    | .off i =>
      inT && i == j && w.args.size == 1 && tyIs c.tabs w isPtrTy &&
        c.roleOf rs w.args[0]! == .sel0 i && 0 ≤ w.auxInt.toInt && w.auxInt.toInt % 8 == 0 &&
        w.auxInt.toInt / 8 < c.offSize x
    | .bstore i =>
      inT && i == j && w.args.size == 3 && tyIs c.tabs w isMemTy &&
        (match Sem.auxTy c.tabs w.aux with | .int .w64 => true | _ => false) &&
        c.roleOf rs w.args[0]! == .off i &&
        (match rs[i]? with
          | some r => c.runArg B segs j r w.args[1]! || c.roleOf rs w.args[1]! == .tload i
          | none => false) &&
        (match c.roleOf rs w.args[2]! with
          | .sel1 k | .bstore k => k == i
          | _ => false) &&
        c.memWb rs w.args[2]! == c.offWb w.args[0]!
    | .taddr i =>
      !inT && i == j && w.op == .Addr && w.args.size == 1 && c.isSb w.args[0]! &&
        (symName? c.tabs w.aux).isSome &&
        (match c.tabs.ty w.type with | .int .w64 => true | _ => false)
    | .call i =>
      inT && i == j && w.op == .StaticCall &&
        (match c.tabs.ty w.type with | .tuple [.mem] => true | _ => false) &&
        (match rs[i]? with
          | some r => c.wbCallOK B segs j rs r i w
          | none => false)
    | .seln i =>
      inT && i == j && w.op == .SelectN && w.args.size == 1 && w.auxInt == 0 &&
        tyIs c.tabs w isMemTy && c.roleOf rs w.args[0]! == .call i
    | .tload i =>
      inT && i == j && w.args.size == 2 &&
        (match rs[i]? with
          | some r =>
            (c.runArg B segs j r w.args[0]! || c.roleOf rs w.args[0]! == .ncThen i) &&
            (w.args[1]! == r.sp.mem ||
              (match c.roleOf rs w.args[1]! with
                | .sel1 k | .bstore k => k == i
                | _ => false))
          | none => false)
    | .none => false

/-- The source schedule's non-pure nodes: the kept ones of `c₀`, then per run the dropped nil
check and the run's stores, then the kept ones of `cⱼ₊₁`. -/
def npOK (B : Block) (rs : List Run) (segs : List ID) : Bool :=
  match npSeq c.f B, segs.mapM c.keptNP with
  | some src, some (k0 :: ks) =>
    src == k0 ++ (rs.zip ks).flatMap fun (r, k) =>
      (match r.nc with
        | some n => if c.K.getD n false then [] else [n]
        | none => []) ++ r.src ++ k
  | _, _ => false

/-- The block structure of run `j` of the chain: the split block, the buffer block, the end
block, the run's sources and nil checks. -/
def runOK (b : ID) (B : Block) (segs : List ID) (rs : List Run) (j : Nat) (r : Run) : Bool :=
  let s := r.sp
  segs[j]? == some s.c && segs[j + 1]? == some s.e &&
  -- the buffer block: `t → e`, its first non-pure node the nil-check copy
  (match c.g.block? s.t with
    | some T =>
      T.id == s.t && T.kind == .Plain && T.succs == #[⟨s.e, 1⟩] &&
      (match r.nc, npSeq c.g T with
        | some _, some (y :: _) => c.roleOf rs y == .ncThen j
        | some _, _ => false
        | none, some _ => true
        | none, none => false) &&
      T.values.all fun x => c.roleOK b B segs rs true j x
    | none => false) &&
  -- the end block: its first non-pure node the nil-check copy
  (match c.g.block? s.e, r.ncEnd with
    | some E, some y => E.id == s.e && (match npSeq c.g E with
        | some (z :: _) => z == y
        | _ => false)
    | some E, none => E.id == s.e && r.nc.isNone
    | none, _ => false) &&
  (match c.g.block? s.c with
    | some C => C.id == s.c
    | none => false) &&
  r.src.length == r.tgt.length && 0 < r.src.length && (vals c.g s.e).contains r.last &&
  -- the run's values are listed where their roles say
  r.tgt.all (vals c.g s.e).contains && r.ncEnd.all (vals c.g s.e).contains &&
  (vals c.g s.c).contains s.load && (vals c.g s.c).contains s.flag &&
  c.roleOf rs s.flag == .flag j && c.held s.mem &&
  r.ncEnd.all (fun y => c.roleOf rs y == .ncEnd j) &&
  r.src.all (fun x => B.values.contains x && !c.K.getD x false) &&
  (match r.nc with
    | some n => (B.values.contains n || c.K.getD n false) &&
        (c.f.value? n).any (·.op == .NilCheck)
    | none => true)

/-- Block `b` of `f` and its chain in `g`. -/
def blockOK (b : ID) : Bool :=
  match c.f.block? b, chainRuns? c.f c.g b with
  | some B, some (rs, l) =>
    let segs := segsOf b rs
    (match c.g.block? l, c.g.block? b with
      | some L, some C0 => L.id == l && C0.id == b && L.kind == B.kind &&
          L.controls == B.controls && L.succs == B.succs && B.controls.all c.held
      | _, _ => false) &&
    segs.getLast? == some l &&
    (segs ++ rs.map (·.sp.t)).Nodup && (segs ++ rs.map (·.sp.t)).all c.g.blocks.contains &&
    rs.zipIdx.all (fun (r, j) => c.runOK b B segs rs j r) &&
    -- every value of `b` is kept and listed in a segment, a run's store or a dropped nil check
    B.values.all (fun x =>
      if c.K.getD x false then segs.any fun s => (vals c.g s).contains x
      else rs.any (fun r => r.src.contains x) || rs.any (fun r => r.nc == some x)) &&
    -- the values of the segments
    segs.zipIdx.all (fun (s, j) => (vals c.g s).all (c.roleOK b B segs rs false j)) &&
    c.npOK B rs segs
  | _, _ => false

end Ctx

/-- The flag address and `Const32 [0]` the runs use, checked once: new values of `g`'s entry
with the expected fields (the flag address reads an `SB` of the entry), the same for every
split. -/
def lazyOK (tabs : Tables) (f g : Func) (K Lst : Array Bool) : Option (Option (ID × ID)) := do
  let runs ← f.blocks.toList.mapM (chainRuns? f g ·)
  let splits := runs.flatMap fun (rs, _) => rs.map (·.sp)
  match splits with
  | [] => return none
  | s :: ss =>
    guard (ss.all fun t => t.wbaddr == s.wbaddr && t.const0 == s.const0)
    let ge := vals g g.entry
    let wa ← g.value? s.wbaddr
    let c0 ← g.value? s.const0
    guard (wa.op == .Addr && symName? tabs wa.aux == some "runtime.writeBarrier" &&
      isPtrTy (tabs.ty wa.type) && wa.args.size == 1)
    guard (c0.op == .Const32 && c0.auxInt == (0 : Int64) && c0.args.isEmpty &&
      (match tabs.ty c0.type with | .int .w32 => true | _ => false))
    guard (ge.contains s.wbaddr && ge.contains s.const0 && ge.contains wa.args[0]!)
    guard ((g.value? wa.args[0]!).any fun v => v.op == .SB && v.args.isEmpty)
    -- the flag address is new (`writebarrier` creates it), so it holds no source value
    guard (!K.getD s.wbaddr false && !Lst.getD s.wbaddr false)
    return some (s.wbaddr, s.const0)

/-- The context of the check. -/
def ctxOf (tabs : Tables) (f g : Func) : Option Ctx := do
  let K := keptMarks f g
  let Lst := lastMarks f g
  let lazy ← lazyOK tabs f g K Lst
  return { tabs, f, g, K, Lst, lazy }

/-- **The check of a `writebarrier` result.** -/
def wbOK (tabs : Tables) (f g : Func) : Bool :=
  g.entry == f.entry && g.ownAux == f.ownAux && memTyOK tabs f &&
    match ctxOf tabs f g with
    | some c => f.blocks.all c.blockOK
    | none => false

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

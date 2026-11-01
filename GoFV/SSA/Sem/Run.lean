import GoFV.SSA.Sem.Pure
import GoFV.SSA.Sem.Env
import GoFV.SSA.Sem.Layout
import GoFV.SSA.Sem.Mem

/-!
# `GoFV.SSA.run`: executable, fuel-bounded semantics (`docs/plans/semantics.md` §3.6, §7, §8)

Structure (bottom-up, each layer separately unfoldable, as clifv's `Clif.run`):

* `evalPure` (`Sem/Pure`) — the pure ops, total.
* `schedule` — the evaluation order of a block's non-`Phi` values: a dependency order that
  runs every ready pure value first, then a ready `NilCheck`, then the next other root (§3.6;
  roots are `isRoot`). Generic SSA is unscheduled, so `b.Values` order only breaks ties between
  roots that are not ordered by their arguments (in P1 only stuck roots can be).
* `evalValue` — one value from the registers: `evalPure`, the function's own arguments,
  frame and global addresses, and the roots P1/P2 know (`PanicBounds`, calls of `Env`
  contracts, `Store`/`Move`/`Zero` and their write-barrier forms, `VarDef`, `VarLive`,
  `KeepAlive`, `NilCheck`). Any other root is `stuck` (its semantics belongs to a later phase),
  any other pure op `poison` (§9).
* `enterBlock` — `Phi`s in parallel from the incoming edge, then the schedule.
* `stepTerm` — the terminator (§7): `Plain`, `First`, `If`, `JumpTable`, `Ret`, `Exit`.
* `runLoop` — block entries bounded by `fuel`; `runCtx` — the activation: frame allocations,
  argument images, the loop, Go-typed results; `run` — the entry point.

`stuck` means a precondition failed: ill-formed SSA (undefined argument, cyclic block, missing
block), an observation of `poison` (§3.5: a branch on it, a result, an argument of a contract),
an invalid store, or an op/block kind outside phases P1/P2.
-/

namespace GoFV.SSA.Sem

open GoFV.SSA

/-- Values that can fail or act on the environment (§3.6 step 3): calls, nil checks, ops with
side effects, and the ops that write memory. Their order matters; pure values' does not. -/
def isRoot (op : Op) : Bool :=
  op.call || op.nilCheck || op.hasSideEffects || op.typ == "Mem" || op == .VarLive

/-- Scheduling priority of a non-`Phi` value: 0 pure, 1 `NilCheck`, 2 other roots. -/
def prio (op : Op) : Nat := if op.nilCheck then 1 else if isRoot op then 2 else 0

/-- A non-`Phi` value of a block as `schedule` sees it: its ID, arguments and priority. -/
structure SNode where
  id : ID
  args : Array ID
  prio : Nat
  deriving Inhabited

/-- The non-`Phi` values of `b`, in `b.Values` order. -/
def schedNodes (f : Func) (b : Block) : Array SNode :=
  b.values.filterMap fun id =>
    match f.value? id with
    | some v => if v.op == .Phi then none else some ⟨v.id, v.args, prio v.op⟩
    | none => none

/-- The largest node ID (0 if none). -/
def maxNodeId (vs : Array SNode) : ID := vs.foldl (fun m v => max m v.id) 0

/-- Kahn's algorithm over `vs` (`none` if their arguments within the block form a cycle): a
ready pure value first (any order would do: pure evaluation is total), else the earliest ready
`NilCheck`, else the earliest ready other root, "earliest" in the order the value became ready
(initially `vs` order). -/
def kahn (vs : Array SNode) : Option (Array ID) := Id.run do
  let n := vs.size
  -- position of each node by ID (arrays, not hash maps: the kernel can evaluate `run`)
  let mut idx : Array (Option Nat) := Array.replicate (maxNodeId vs + 1) none
  for h : i in [0:n] do
    idx := idx.set! vs[i].id (some i)
  let mut indeg : Array Nat := Array.replicate n 0
  let mut users : Array (Array Nat) := Array.replicate n #[]
  for h : i in [0:n] do
    for a in vs[i].args do
      match idx[a]?.join with
      | some j =>
        indeg := indeg.modify i (· + 1)
        users := users.modify j (·.push i)
      | none => pure ()
  -- ready queues: pure values (a stack), nil checks and roots (FIFO)
  let mut pureQ : Array Nat := #[]
  let mut nilQ : Array Nat := #[]
  let mut rootQ : Array Nat := #[]
  for h : i in [0:n] do
    if indeg[i]! == 0 then
      match vs[i].prio with
      | 0 => pureQ := pureQ.push i
      | 1 => nilQ := nilQ.push i
      | _ => rootQ := rootQ.push i
  let mut nilHead := 0
  let mut rootHead := 0
  let mut out : Array ID := Array.mkEmpty n
  for _ in [0:n] do
    let i ←
      if h : 0 < pureQ.size then
        let i := pureQ[pureQ.size - 1]
        pureQ := pureQ.pop
        pure (some i)
      else if h : nilHead < nilQ.size then
        let i := nilQ[nilHead]
        nilHead := nilHead + 1
        pure (some i)
      else if h : rootHead < rootQ.size then
        let i := rootQ[rootHead]
        rootHead := rootHead + 1
        pure (some i)
      else pure none
    match i with
    | none => break
    | some i =>
      out := out.push vs[i]!.id
      for u in users[i]! do
        let d := indeg[u]! - 1
        indeg := indeg.set! u d
        if d == 0 then
          match vs[u]!.prio with
          | 0 => pureQ := pureQ.push u
          | 1 => nilQ := nilQ.push u
          | _ => rootQ := rootQ.push u
  return if out.size == n then some out else none

/-- Walk of `schedValid`. `nodes`: each node's arguments and whether it is early (a flag: pure,
or priority ≤ 1), by ID; `pos`: 1 + the position of each listed ID (0: not listed yet); `j`: the
next position; `np`: 1 + the position of the last listed node that is not early (0: none yet).
Each listed ID is a node not listed before, its arguments that are nodes are listed before it,
and an early node listed after a non-early one has an argument listed at or after that one (it
was not ready when the non-early node was chosen: early nodes go first). -/
def schedValidAux (nodes : Array (Option (Array ID × Bool))) :
    Array Nat → Nat → Nat → List ID → Bool
  | _, _, _, [] => true
  | pos, j, np, x :: xs =>
    match nodes[x]?.join with
    | some (args, pure) =>
      pos.getD x 0 == 0 &&
      args.all (fun a => (nodes[a]?.join).isNone || pos.getD a 0 != 0) &&
      (!pure || np == 0 || args.any (fun a => (nodes[a]?.join).isSome && np ≤ pos.getD a 0)) &&
        schedValidAux nodes (pos.set! x (j + 1)) (j + 1) (if pure then np else j + 1) xs
    | none => false

/-- The nodes' IDs are distinct (`seen`: the IDs met so far). -/
def idsDistinct : Array Bool → List SNode → Bool
  | _, [] => true
  | seen, n :: ns => !seen.getD n.id false && idsDistinct (seen.set! n.id true) ns

/-- `o` lists every node of `vs` exactly once (`vs` has distinct IDs), each after its
arguments within the block (a dependency order), pure nodes as early as their arguments allow
relative to the other nodes, and nodes of priority ≤ 1 (pure or `NilCheck`) as early as their
arguments allow relative to the other roots (`schedValidAux`, once per flag). Validates
`kahn`'s output, so proofs use this specification rather than the algorithm. -/
def schedValid (vs : Array SNode) (o : Array ID) : Bool :=
  let m := maxNodeId vs + 1
  let nodes (early : SNode → Bool) : Array (Option (Array ID × Bool)) :=
    vs.foldl (fun t n => t.set! n.id (some (n.args, early n))) (Array.replicate m none)
  idsDistinct (Array.replicate m false) vs.toList && o.size == vs.size &&
    schedValidAux (nodes (·.prio == 0)) (Array.replicate m 0) 0 0 o.toList &&
    schedValidAux (nodes (·.prio ≤ 1)) (Array.replicate m 0) 0 0 o.toList

/-- A simple scheduler, used only if `kahn`'s output fails validation (never on the corpus):
repeatedly the first ready pure node, else the first ready `NilCheck`, else the first ready
node (`fuel`: one step per node). It makes `schedule` provably defined on every acyclic block
without a proof of `kahn`. -/
def greedy (vs : List SNode) : Nat → List SNode → List ID → Option (List ID)
  | _, [], acc => some acc.reverse
  | 0, _ :: _, _ => none
  | fuel + 1, rem@(_ :: _), acc =>
    let ready (n : SNode) : Bool :=
      n.args.all fun a => !(vs.any (·.id == a)) || acc.contains a
    match rem.findIdx? (fun n => n.prio == 0 && ready n) with
    | some i => greedy vs fuel (rem.eraseIdx i) ((rem[i]?.map (·.id)).getD 0 :: acc)
    | none =>
      match rem.findIdx? (fun n => n.prio == 1 && ready n) with
      | some i => greedy vs fuel (rem.eraseIdx i) ((rem[i]?.map (·.id)).getD 0 :: acc)
      | none =>
        match rem.findIdx? ready with
        | some i => greedy vs fuel (rem.eraseIdx i) ((rem[i]?.map (·.id)).getD 0 :: acc)
        | none => none

/-- The evaluation order of the non-`Phi` values of `b` (`none` if their IDs are not distinct
or their arguments within the block form a cycle): `kahn`, validated by `schedValid`, else
`greedy`. -/
def schedule (f : Func) (b : Block) : Option (Array ID) :=
  let vs := schedNodes f b
  if idsDistinct (Array.replicate (maxNodeId vs + 1) false) vs.toList then
    match (kahn vs).filter (schedValid vs) with
    | some o => some o
    | none => (greedy vs.toList vs.size vs.toList []).map List.toArray
  else none

/-- The static context of a function's runs, computed once. -/
structure Ctx where
  f : Func
  tabs : Tables
  /-- Shape of each value's type, by value ID. -/
  tys : Array Ty
  /-- `schedule` of each block, by block ID. -/
  sched : Array (Option (Array ID))
  /-- The `*ir.Name` of each input parameter (receiver, then parameters), from `f.OwnAux`'s
  ABI assignments. -/
  params : Array (Option AuxRef)
  /-- Shape of each input parameter's type. -/
  paramTys : Array Ty := #[]
  /-- Each result: its `*ir.Name`, shape, and number of registers (0: on the stack). -/
  outs : Array (Option AuxRef × Ty × Nat) := #[]
  /-- The frame variables (`PAUTO`/`PPARAM`/`PPARAMOUT` names the function refers to) with
  their sizes, and the input parameter each `PPARAM` holds. -/
  locals : Array (AuxRef × Nat × Option Nat) := #[]
  /-- The activation number (frame blocks are `Blk.local act name`). -/
  act : Nat := 0
  deriving Inhabited

/-- The callee symbol of an `*AuxCall`. -/
def _root_.GoFV.SSA.Tables.callee? (tabs : Tables) (a : AuxRef) : Option String :=
  match tabs.aux? a with
  | some { kind := .call (some fn) _, .. } =>
    match tabs.aux? fn with
    | some { kind := .sym name .., .. } => some name.toStringLossy
    | _ => none
  | _ => none

/-- The ABI assignments of `f.OwnAux`. -/
def abiParams (tabs : Tables) (f : Func) : Array ABIParam :=
  match f.ownAux.bind tabs.aux? with
  | some { kind := .call _ (some abi), .. } => abi.params
  | _ => #[]

/-- The frame variables: every `PAUTO`/`PPARAM`/`PPARAMOUT` `*ir.Name` the tables define
(the export's tables are per function: these are the function's own variables, including those
earlier passes stopped referring to), with its size and, for a `PPARAM`, the index of the input
parameter it holds. Taken from the tables rather than from the values so that deleting a
value (deadcode, dse) never changes the frame. -/
def frameLocals (tabs : Tables) (params : Array (Option AuxRef)) :
    Array (AuxRef × Nat × Option Nat) :=
  (List.range tabs.auxes.size).toArray.filterMap fun n =>
    match tabs.aux? n with
    | some { kind := .name _ cls t .., .. } =>
      if cls == .PAUTO || cls == .PPARAM || cls == .PPARAMOUT then
        (typeSize? tabs t).map fun sz =>
          (n, sz, if cls == .PPARAM then params.findIdx? (· == some n) else none)
      else none
    | _ => none

def Ctx.make (tabs : Tables) (f : Func) : Ctx :=
  let ps := abiParams tabs f
  let ins := ps.filter (!·.out)
  let params := ins.map (·.name)
  { f := f
    tabs := tabs
    tys :=
      -- one shape per type number, shared by the values of that type
      let byType := (List.range tabs.types.size).toArray.map tabs.ty
      f.valueTab.map fun o => match o with
        | some v => byType[v.type]?.getD .other
        | none => .other
    sched := f.blockTab.map fun o => o.bind (schedule f)
    params := params
    paramTys := ins.map (tabs.ty ·.type)
    outs := (ps.filter (·.out)).map fun p => (p.name, tabs.ty p.type, p.regs.size)
    locals := frameLocals tabs params }

/-- The state of an activation: the latest value of each value ID (by ID), the function's
arguments and initial memory. -/
structure Frame where
  regs : Array (Option Val)
  args : List Val
  mem0 : Mem
  /-- The in-memory image of each argument (its encoding by the parameter's shape), which
  `Arg`/`ArgIntReg` pieces are read from. -/
  images : Array (Array Byte) := #[]

/-- The value of input parameter `name` at byte offset `off`, as a value of shape `ty` (`Arg`,
`ArgIntReg`): decoded from the argument's image, so whole parameters (before `expand calls`)
and their register or stack pieces (after) read the same bytes. -/
def argVal (ctx : Ctx) (fr : Frame) (name : AuxRef) (off : Int) (ty : Ty) : Res Val :=
  match ctx.params.findIdx? (· == some name) with
  | none => .stuck s!"argument a{name} is not a parameter"
  | some i =>
    match fr.images[i]? with
    | none => .stuck s!"missing argument {i}"
    | some img =>
      if off < 0 || img.size < off.toNat + ty.size then .ok .poison
      else .ok (decode img off.toNat ty)

/-- `PanicBounds [kind] x y mem` (§6): `x` read signed for the signed kinds (even, below
`BoundsConvert` = 16), `y` signed. -/
def panicBounds (kind : Int64) : List Val → Res Val
  | [.int _ x, .int _ y, .mem m] =>
    let k := kind.toInt.toNat
    let xi := if k % 2 == 0 && k < 16 then x.toInt else x.toNat
    .panic (.bounds k xi y.toInt) m
  | _ => .stuck "PanicBounds: undefined or ill-typed arguments"

/-- A call of a callee without SSA (`StaticLECall`/`StaticCall {AuxCall} args… mem`): the
contract's results, followed by the memory (the `RESULTS` tuple read by `SelectN`). -/
def callExtern (env : Env) (callee : String) (args : List Val) : Res Val := do
  let mem ← match args.getLast? with
    | some (.mem m) => .ok m
    | _ => .stuck s!"call {callee}: no memory argument"
  let goArgs := args.dropLast
  if goArgs.any (fun | .poison => true | _ => false) then
    .stuck s!"call {callee}: poison argument"
  else
    match env.extern callee with
    | none => .stuck s!"call {callee}: no contract (phase P3)"
    | some c =>
      match c goArgs mem with
      | .returned rs m => .ok (.tuple (rs ++ [.mem m]))
      | .panicked e m => .panic e m
      | .stuck msg => .stuck msg

/-- The shape of the type an aux names (`Store {T}`, `Move {T}`, `Zero {T}`). -/
def auxTy (tabs : Tables) (aux : Option AuxRef) : Ty :=
  match aux.bind tabs.aux? with
  | some { kind := .type t, .. } => tabs.ty t
  | _ => .other

/-- A memory write of a root: `stuck` on an invalid access (§3.4). -/
@[inline] def writeRes (what : String) : Option Mem → Res Val
  | some m => .ok (.mem m)
  | none => .stuck s!"{what}: invalid or read-only access"

/-- The memory roots of P2 (§3.4): `Store {T} p x mem`, `Move {T} [n] dst src mem`,
`Zero {T} [n] p mem` (and their write-barrier forms, which have the same semantics),
`VarDef {n} mem`, `VarLive {n} mem`, `KeepAlive x mem`, `WBend mem` (the end of a
write-barrier sequence: no memory effect), `NilCheck p mem` (§6). The address of
a write and the pointer of a nil check are observation points. -/
def memRoot (ctx : Ctx) (v : Value) (argv : List Val) : Res Val :=
  let what := s!"v{v.id}: {v.op.name}"
  match v.op, argv with
  | .Store, [.ptr p, x, .mem m] | .StoreWB, [.ptr p, x, .mem m] =>
    writeRes what (m.write p (encode (auxTy ctx.tabs v.aux) x))
  | .Move, [.ptr d, .ptr s, .mem m] | .MoveWB, [.ptr d, .ptr s, .mem m] =>
    match m.read s v.auxInt.toInt.toNat with
    | some bs => writeRes what (m.write d bs)
    | none => .stuck s!"{what}: invalid source"
  | .Zero, [.ptr p, .mem m] | .ZeroWB, [.ptr p, .mem m] =>
    writeRes what (m.write p (Array.replicate v.auxInt.toInt.toNat (.b 0)))
  | .VarDef, [.mem m] =>
    match v.aux with
    | some n => .ok (.mem (m.poisonBlock (.local ctx.act n)))
    | none => .stuck s!"{what}: no name"
  | .VarLive, [.mem m] | .WBend, [.mem m] => .ok (.mem m)
  | .KeepAlive, [_, .mem m] => .ok (.mem m)
  | .NilCheck, [.ptr p, .mem m] => if p.isNil then .panic .nilDeref m else .ok (.ptr p)
  | .NilCheck, [.int .w64 x, .mem m] => if x == 0 then .panic .nilDeref m else .ok (.int .w64 x)
  | _, args =>
    if args.any (fun | .poison => true | _ => false) then .stuck s!"{what}: poison argument"
    else .stuck s!"{what}: ill-typed arguments"

/-- Ops whose value depends on the activation or on symbols (not on `evalPure`'s inputs). -/
def frameVal (ctx : Ctx) (v : Value) : Option Val :=
  match v.op with
  | .SP => some (.ptr ⟨.outargs ctx.act, 0⟩)
  | .LocalAddr => v.aux.map fun n => .ptr ⟨.local ctx.act n, 0⟩
  | .Addr =>
    match v.aux.bind ctx.tabs.aux? with
    | some { kind := .sym name .., .. } => some (.ptr ⟨.global name.toStringLossy, 0⟩)
    | _ => some .poison
  | .ConstString =>
    match v.aux.bind ctx.tabs.aux? with
    | some { kind := .str s dataSym, .. } =>
      some (.agg [if s.size == 0 then .ptr Ptr.null else .ptr ⟨.global dataSym.toStringLossy, 0⟩,
        .i64 (BitVec.ofNat 64 s.size)])
    | _ => some .poison
  | _ => none

/-- Evaluate value `v` from the registers (its arguments are already evaluated). -/
def evalValue (env : Env) (ctx : Ctx) (fr : Frame) (v : Value) : Res Val := do
  let argv ← v.args.toList.mapM fun a =>
    Res.ofOption s!"v{v.id}: argument v{a} has no value" (fr.regs[a]?).join
  let ty := ctx.tys[v.id]?.getD .other
  match v.op with
  | .InitMem => pure (.mem fr.mem0)
  | .Arg =>
    match v.aux with
    | some n => argVal ctx fr n v.auxInt.toInt ty
    | none => .stuck s!"v{v.id}: Arg without name"
  | .ArgIntReg =>
    match v.aux.bind ctx.tabs.aux? with
    | some { kind := .nameOff n off, .. } => argVal ctx fr n off ty
    | _ => .stuck s!"v{v.id}: ArgIntReg without name"
  | .PanicBounds => panicBounds v.auxInt argv
  | .StaticLECall | .StaticCall =>
    match v.aux.bind ctx.tabs.callee? with
    | some callee => callExtern env callee argv
    | none => .stuck s!"v{v.id}: call without callee"
  | .Store | .StoreWB | .Move | .MoveWB | .Zero | .ZeroWB | .VarDef | .VarLive | .KeepAlive
  | .WBend | .NilCheck => memRoot ctx v argv
  | op =>
    match frameVal ctx v with
    | some x => pure x
    | none =>
      if isRoot op then .stuck s!"v{v.id}: {op.name} is not in phases P1/P2"
      else pure ((evalPure op ty v.auxInt v.aux argv).retype ty)

/-- Evaluate the values listed in `ids`, in order, storing each in the registers. -/
def evalAll (env : Env) (ctx : Ctx) (fr : Frame) : List ID → Res Frame
  | [] => .ok fr
  | id :: ids =>
    match ctx.f.value? id with
    | none => .stuck s!"v{id} is not in the function"
    | some v =>
      match evalValue env ctx fr v with
      | .ok x => evalAll env ctx { fr with regs := fr.regs.set! id (some x) } ids
      | .panic e m => .panic e m
      | .stuck msg => .stuck msg

/-- Enter block `b` along its incoming edge `i`: the `Phi`s of `b` take their `i`-th argument
in parallel (values of the previous activations), then the other values are evaluated in
`schedule` order. -/
def enterBlock (env : Env) (ctx : Ctx) (fr : Frame) (b : Block) (i : Nat) : Res Frame := do
  let phis ← b.values.toList.filterMapM fun id =>
    match ctx.f.value? id with
    | some v =>
      if v.op == .Phi then
        match v.args[i]? with
        | some a =>
          match (fr.regs[a]?).join with
          | some x => .ok (some (id, x.retype (ctx.tys[id]?.getD .other)))
          | none => .stuck s!"phi v{id}: argument v{a} has no value"
        | none => .stuck s!"phi v{id}: no argument {i}"
      else .ok none
    | none => .stuck s!"v{id} is not in the function"
  let fr := { fr with regs := phis.foldl (fun r (id, x) => r.set! id (some x)) fr.regs }
  let order ← Res.ofOption s!"b{b.id}: cyclic values" (ctx.sched[b.id]?).join
  evalAll env ctx fr order.toList

/-- What a terminator does. -/
inductive Next where
  /-- Continue at the block of edge `e` (`e.i` is the index of the edge among its preds). -/
  | goto (e : Edge)
  | ret (results : List Val) (m : Mem)

/-- The value of control `k` of `b`. -/
def control (fr : Frame) (b : Block) (k : Nat) : Res Val :=
  match b.controls[k]? with
  | some c => Res.ofOption s!"b{b.id}: control v{c} has no value" (fr.regs[c]?).join
  | none => .stuck s!"b{b.id}: missing control {k}"

/-- Successor `k` of `b`. -/
def succ (b : Block) (k : Nat) : Res Next :=
  Res.ofOption s!"b{b.id}: no successor {k}" (b.succs[k]?.map .goto)

/-- The terminator of `b` (§7). -/
def stepTerm (fr : Frame) (b : Block) : Res Next :=
  match b.kind with
  | .Plain | .First => succ b 0
  | .If => do
    match ← control fr b 0 with
    | .bool true => succ b 0
    | .bool false => succ b 1
    | _ => .stuck s!"b{b.id}: If on poison or non-bool"
  | .JumpTable => do
    match ← control fr b 0 with
    | .int _ x => succ b x.toNat
    | _ => .stuck s!"b{b.id}: JumpTable on poison or non-int"
  | .Ret => do
    match ← control fr b 0 with
    | .tuple vs =>
      match vs.getLast?, vs.dropLast with
      | some (.mem m), rs =>
        if rs.any (fun | .poison => true | _ => false) then .stuck s!"b{b.id}: poison result"
        else .ok (.ret rs m)
      | _, _ => .stuck s!"b{b.id}: Ret without memory"
    | _ => .stuck s!"b{b.id}: Ret control is not a MakeResult"
  | .Exit => .stuck s!"b{b.id}: Exit reached (a non-returning call returned)"
  | k => .stuck s!"b{b.id}: block kind {k.name} is not in phase P1"

/-- Run from the entry of block `b` (entered along edge index `i`) with at most `fuel` block
entries. -/
def runLoop (env : Env) (ctx : Ctx) : Nat → Frame → ID → Nat → Outcome
  | 0, _, _, _ => .outOfFuel
  | fuel + 1, fr, bid, i =>
    match ctx.f.block? bid with
    | none => .stuck s!"b{bid} is not in the function"
    | some b =>
      match enterBlock env ctx fr b i with
      | .panic e m => .panicked e m
      | .stuck msg => .stuck msg
      | .ok fr =>
        match stepTerm fr b with
        | .ok (.goto e) => runLoop env ctx fuel fr e.b e.i
        | .ok (.ret rs m) => .returned rs m
        | .panic e m => .panicked e m
        | .stuck msg => .stuck msg

@[simp] theorem runLoop_zero (env : Env) (ctx : Ctx) (fr : Frame) (b : ID) (i : Nat) :
    runLoop env ctx 0 fr b i = .outOfFuel := (rfl)

/-- One block entry: the unfolding a simulation proof steps with (never `simp [runLoop]`). -/
theorem runLoop_succ (env : Env) (ctx : Ctx) (fuel : Nat) (fr : Frame) (bid : ID) (i : Nat) :
    runLoop env ctx (fuel + 1) fr bid i =
      match ctx.f.block? bid with
      | none => .stuck s!"b{bid} is not in the function"
      | some b =>
        match enterBlock env ctx fr b i with
        | .panic e m => .panicked e m
        | .stuck msg => .stuck msg
        | .ok fr =>
          match stepTerm fr b with
          | .ok (.goto e) => runLoop env ctx fuel fr e.b e.i
          | .ok (.ret rs m) => .returned rs m
          | .panic e m => .panicked e m
          | .stuck msg => .stuck msg := (rfl)

/-- The register-assigned leaves of a shape, at their offsets, in the order of the ABI's
register assignment (fields in order; string: pointer, length; slice: pointer, length,
capacity; interface: type word, data word). -/
def leaves : Ty → List (Nat × Ty)
  | .agg fs _ => leavesFields fs
  | .empty => []
  | .blob _ => []
  | t => [(0, t)]
where
  leavesFields : List (Nat × Ty) → List (Nat × Ty)
    | [] => []
    | (o, t) :: fs => (leaves t).map (fun (o', t') => (o + o', t')) ++ leavesFields fs

/-- `v` contains `poison` (anywhere inside a composite). -/
def Val.hasPoison : Val → Bool
  | .poison => true
  | .agg vs => vs.attach.any fun ⟨v, _⟩ => v.hasPoison
  | .tuple vs => vs.attach.any fun ⟨v, _⟩ => v.hasPoison
  | _ => false

/-- The Go-typed results of a `Ret` (§7), from the `MakeResult` components `rs` (memory
removed) and the memory `m` at the return. Before `expand calls` the components are the
Go-typed results; after it they are the register pieces of the register-assigned results
(in ABI order), and stack-assigned results are in their `PPARAMOUT` variables. Both forms are
reduced to the results' bytes and decoded by the result types, so every section yields the
same values. A result containing `poison` is observed: `stuck`. -/
def goResults (ctx : Ctx) (rs : List Val) (m : Mem) : Res (List Val) := do
  let outs := ctx.outs.toList
  let pre := rs.length == outs.length &&
    (rs.zip outs).all fun (v, (_, t, _)) => v.hasTy t
  let bytes ← if pre then
      pure ((rs.zip outs).map fun (v, (_, t, _)) => encode t v)
    else
      let rec post (pieces : List Val) : List (Option AuxRef × Ty × Nat) → Res (List (Array Byte))
        | [] => if pieces.isEmpty then .ok [] else .stuck "Ret: extra result pieces"
        | (name, t, k) :: os =>
          if k == 0 then do
            let n ← Res.ofOption "Ret: stack result without name" name
            let bs := (m.read ⟨.local ctx.act n, 0⟩ t.size).getD (Array.replicate t.size .poison)
            return bs :: (← post pieces os)
          else
            let ls := leaves t
            if ls.length != k || pieces.length < k then .stuck "Ret: result pieces do not match the ABI"
            else do
              let buf := (ls.zip (pieces.take k)).foldl
                (fun buf ((o, lt), v) => putBytes buf o (encode lt v))
                (Array.replicate t.size Byte.poison)
              return buf :: (← post (pieces.drop k) os)
      post rs outs
  let vals := (bytes.zip outs).map fun (bs, (_, t, _)) => decode bs 0 t
  if vals.any Val.hasPoison then .stuck "poison result" else .ok vals

/-- `m` without the frame of activation `act` (`Blk.local act _`, `Blk.outargs act`). -/
def _root_.GoFV.SSA.Sem.Mem.freeFrame (m : Mem) (act : Nat) : Mem :=
  { m with blocks := m.blocks.filter fun (b, _) => match b with
    | .local a _ | .outargs a => a != act
    | _ => true }

/-- The memory an activation starts with: `mem`, the global image of `env` (allocations not
already in `mem`), and the frame: one allocation per frame variable, a `PPARAM` holding its
argument's image, every other variable poison (§3.4). -/
def frameMem (env : Env) (ctx : Ctx) (images : Array (Array Byte)) (mem : Mem) : Mem :=
  let mem := env.globals.foldl (fun m (name, a) =>
    if (m.find? (.global name)).isSome then m else m.set (.global name) a) mem
  ctx.locals.foldl (fun m (n, sz, pi) =>
    let data := match pi.bind (images[·]?) with
      | some img => if img.size == sz then img else Array.replicate sz .poison
      | none => Array.replicate sz .poison
    m.set (.local ctx.act n) { data }) mem

/-- Run `f` (with the definition tables `tabs` of its export section) on the Go-typed
arguments `args` (receiver first) and memory `mem`, for at most `fuel` block entries: set up
the frame, run, decode the Go-typed results and remove the frame from the memory. -/
def runCtx (env : Env) (ctx : Ctx) (args : List Val) (mem : Mem) (fuel : Nat) : Outcome :=
  if args.length != ctx.params.size then
    .stuck s!"{args.length} arguments for {ctx.params.size} parameters"
  else
    let images := (args.toArray.zip ctx.paramTys).map fun (a, t) => encode t a
    let mem0 := frameMem env ctx images mem
    match runLoop env ctx fuel
        { regs := Array.replicate ctx.f.valueTab.size none, args, mem0, images }
        ctx.f.entry 0 with
    | .returned rs m =>
      match goResults ctx rs m with
      | .ok vals =>
        .returned vals (m.freeFrame ctx.act)
      | .panic e m => .panicked e m
      | .stuck msg => .stuck msg
    | o => o

end GoFV.SSA.Sem

namespace GoFV.SSA

/-- `GoFV.SSA.run`: the outcome of running `f` (with the tables `tabs` of its export section)
on `args` from memory `mem` with at most `fuel` block entries (`docs/plans/semantics.md` §8). -/
def run (env : Sem.Env) (tabs : Tables) (f : Func) (args : List Sem.Val) (mem : Sem.Mem)
    (fuel : Nat) : Sem.Outcome :=
  Sem.runCtx env (Sem.Ctx.make tabs f) args mem fuel

end GoFV.SSA

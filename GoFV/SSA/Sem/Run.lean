import GoFV.SSA.Sem.Pure
import GoFV.SSA.Sem.Env
import GoFV.SSA.Sem.Layout

/-!
# `GoFV.SSA.run`: executable, fuel-bounded semantics (`docs/plans/semantics.md` §3.6, §7, §8)

Structure (bottom-up, each layer separately unfoldable, as clifv's `Clif.run`):

* `evalPure` (`Sem/Pure`) — the pure ops, total.
* `schedule` — the evaluation order of a block's non-`Phi` values: a dependency order that
  runs every ready pure value first, then a ready `NilCheck`, then the next other root (§3.6;
  roots are `isRoot`). Generic SSA is unscheduled, so `b.Values` order only breaks ties between
  roots that are not ordered by their arguments (in P1 only stuck roots can be).
* `evalValue` — one value from the registers: `evalPure`, the function's own arguments and
  memory, and the roots P1 knows (`PanicBounds`, calls of `Env` contracts). Any other root is
  `stuck` (its semantics belongs to a later phase), any other pure op `poison` (§9).
* `enterBlock` — `Phi`s in parallel from the incoming edge, then the schedule.
* `stepTerm` — the terminator (§7): `Plain`, `First`, `If`, `JumpTable`, `Ret`, `Exit`.
* `runLoop` — block entries bounded by `fuel`; `run` — the entry point.

`stuck` means a precondition failed: ill-formed SSA (undefined argument, cyclic block, missing
block), an observation of `poison` (§3.5: a branch on it, a result, an argument of a contract),
or an op/block kind outside phase P1.
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

/-- Walk of `schedValid` (`nodes`: each node's arguments, by ID; `done`: the IDs listed so
far): each listed ID is a node not listed before, and its arguments that are nodes are listed
before it. -/
def schedValidAux (nodes : Array (Option (Array ID))) : Array Bool → List ID → Bool
  | _, [] => true
  | done, x :: xs =>
    match nodes[x]?.join with
    | some args =>
      !done.getD x false && args.all (fun a => (nodes[a]?.join).isNone || done.getD a false) &&
        schedValidAux nodes (done.set! x true) xs
    | none => false

/-- `o` lists every node of `vs` exactly once (`vs` has distinct IDs), each after its
arguments within the block: a dependency order. Validates `kahn`'s output, so proofs use this
specification rather than the algorithm. -/
def schedValid (vs : Array SNode) (o : Array ID) : Bool :=
  let m := maxNodeId vs + 1
  let nodes : Array (Option (Array ID)) :=
    vs.foldl (fun t n => t.set! n.id (some n.args)) (Array.replicate m none)
  (nodes.filter Option.isSome).size == vs.size && o.size == vs.size &&
    schedValidAux nodes (Array.replicate m false) o.toList

/-- The evaluation order of the non-`Phi` values of `b` (`none` if their arguments within
the block form a cycle): `kahn`, validated by `schedValid`. -/
def schedule (f : Func) (b : Block) : Option (Array ID) :=
  let vs := schedNodes f b
  (kahn vs).filter (schedValid vs)

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

/-- The callee symbol of an `*AuxCall`. -/
def _root_.GoFV.SSA.Tables.callee? (tabs : Tables) (a : AuxRef) : Option String :=
  match tabs.aux? a with
  | some { kind := .call (some fn) _, .. } =>
    match tabs.aux? fn with
    | some { kind := .sym name .., .. } => some name.toStringLossy
    | _ => none
  | _ => none

def Ctx.make (tabs : Tables) (f : Func) : Ctx where
  f := f
  tabs := tabs
  tys := f.valueTab.map fun o => match o with
    | some v => tabs.ty v.type
    | none => .other
  sched := f.blockTab.map fun o => o.bind (schedule f)
  params :=
    match f.ownAux.bind tabs.aux? with
    | some { kind := .call _ (some abi), .. } =>
      (abi.params.filter (!·.out)).map (·.name)
    | _ => #[]

/-- The state of an activation: the latest value of each value ID (by ID), the function's
arguments and initial memory. -/
structure Frame where
  regs : Array (Option Val)
  args : List Val
  mem0 : Mem

/-- The value of input parameter `name` at byte offset `off`, as a value of shape `ty` (`Arg`,
`ArgIntReg`). P1 has scalar parameters only: a piece of a composite is `poison`. -/
def argVal (ctx : Ctx) (fr : Frame) (name : AuxRef) (off : Int) (ty : Ty) : Res Val :=
  match ctx.params.findIdx? (· == some name) with
  | none => .stuck s!"argument a{name} is not a parameter"
  | some i =>
    match fr.args[i]? with
    | none => .stuck s!"missing argument {i}"
    | some a => .ok (if off == 0 && a.hasTy ty then a else .poison)

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
  | op =>
    if isRoot op then .stuck s!"v{v.id}: {op.name} is not in phase P1"
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

/-- Run `f` (with the definition tables `tabs` of its export section) on the Go-typed
arguments `args` (receiver first) and memory `mem`, for at most `fuel` block entries. -/
def runCtx (env : Env) (ctx : Ctx) (args : List Val) (mem : Mem) (fuel : Nat) : Outcome :=
  if args.length != ctx.params.size then
    .stuck s!"{args.length} arguments for {ctx.params.size} parameters"
  else
    runLoop env ctx fuel { regs := Array.replicate ctx.f.valueTab.size none, args, mem0 := mem }
      ctx.f.entry 0

end GoFV.SSA.Sem

namespace GoFV.SSA

/-- `GoFV.SSA.run`: the outcome of running `f` (with the tables `tabs` of its export section)
on `args` from memory `mem` with at most `fuel` block entries (`docs/plans/semantics.md` §8). -/
def run (env : Sem.Env) (tabs : Tables) (f : Func) (args : List Sem.Val) (mem : Sem.Mem)
    (fuel : Nat) : Sem.Outcome :=
  Sem.runCtx env (Sem.Ctx.make tabs f) args mem fuel

end GoFV.SSA

import GoFV.SSA.Sem.Pure
import GoFV.SSA.Sem.Env
import GoFV.SSA.Sem.Layout
import GoFV.SSA.Sem.Mem
import GoFV.SSA.Sem.Atomic

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

/-- The rank order of non-pure nodes: priority first, then value ID. Every schedule lists the
ready non-pure node of least rank next, so the sequence of non-pure nodes is determined by
their dependencies alone, and passes that keep a value's ID and op keep its rank (#96). -/
@[inline] def SNode.rankLt (m n : SNode) : Bool :=
  m.prio < n.prio || (m.prio == n.prio && m.id < n.id)

/-- Kahn's algorithm over `vs` (`none` if their arguments within the block form a cycle): a
ready pure value first (any order would do: pure evaluation is total), else the ready
non-pure node of least rank (`SNode.rankLt`: a `NilCheck` before other roots, then by ID). -/
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
  -- ready sets: pure values (a stack) and non-pure nodes (picked by least rank)
  let mut pureQ : Array Nat := #[]
  let mut npQ : Array Nat := #[]
  for h : i in [0:n] do
    if indeg[i]! == 0 then
      if vs[i].prio == 0 then pureQ := pureQ.push i else npQ := npQ.push i
  let mut out : Array ID := Array.mkEmpty n
  for _ in [0:n] do
    let i ←
      if h : 0 < pureQ.size then
        let i := pureQ[pureQ.size - 1]
        pureQ := pureQ.pop
        pure (some i)
      else if 0 < npQ.size then
        -- the ready non-pure node of least rank; removed by swapping with the last
        let mut best := 0
        for k in [1:npQ.size] do
          if vs[npQ[k]!]!.rankLt vs[npQ[best]!]! then best := k
        let i := npQ[best]!
        npQ := (npQ.set! best npQ[npQ.size - 1]!).pop
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
          if vs[u]!.prio == 0 then pureQ := pureQ.push u else npQ := npQ.push u
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

/-- The non-pure nodes of `vs` with their arguments, by ID (`none`: pure or not a node). -/
def npTable (vs : Array SNode) : Array (Option SNode) :=
  vs.foldl (fun t n => if n.prio == 0 then t else t.set! n.id (some n))
    (Array.replicate (maxNodeId vs + 1) none)

/-- `RankFirst` for `o`: a non-pure node `x` listed after a non-pure node `y` of greater rank
has an argument that is a node (`isNode`) listed at or after `y`. -/
def rankOK (vs : Array SNode) (isNode : ID → Bool) (o : Array ID) : Bool :=
  let T := npTable vs
  let npPos := (List.range o.size).filter fun j => (o[j]?.bind fun x => T[x]?.join).isSome
  npPos.all fun j => npPos.all fun k =>
    !(k < j) ||
    match (o[k]?.bind fun y => T[y]?.join), (o[j]?.bind fun x => T[x]?.join) with
    | some y, some x =>
      !(x.rankLt y) || (List.range (j - k)).any fun d =>
        match o[k + d]? with
        | some a => x.args.contains a && isNode a
        | none => false
    | _, _ => true

/-! ### `rankOK`, compiled as a linear scan

`rankOK` compares every pair of non-pure positions, scanning the gap between them: cubic in the
block size, the dominant cost of the checked CFG passes (issue #147). `rankOKFast` checks each
non-pure node `x` once, scanning backwards from its position up to the latest argument of `x`
(`rankScan`): an earlier non-pure node of greater rank must lie before that argument.
`rankOK_eq_rankOKFast` (`@[csimp]`) makes the compiled code use it; proofs keep `rankOK`. -/

/-- The positions before `i` back to the latest argument (a node) of `x` hold no non-pure node
of greater rank than `x`. -/
def rankScan (T : Array (Option SNode)) (isNode : ID → Bool) (o : Array ID) (x : SNode) :
    Nat → Bool
  | 0 => true
  | i + 1 =>
    match o[i]? with
    | some a =>
      if x.args.contains a && isNode a then true
      else (match T[a]?.join with
        | some y => !(x.rankLt y)
        | none => true) && rankScan T isNode o x i
    | none => rankScan T isNode o x i

/-- `rankOK`, one backward scan per non-pure node. -/
def rankOKFast (vs : Array SNode) (isNode : ID → Bool) (o : Array ID) : Bool :=
  let T := npTable vs
  Nat.all o.size fun j _ =>
    match o[j]?.bind fun x => T[x]?.join with
    | some x => rankScan T isNode o x j
    | none => true

/-- What `rankOK` and `rankOKFast` check. -/
def RankProp (T : Array (Option SNode)) (isNode : ID → Bool) (o : Array ID) : Prop :=
  ∀ (j k : Nat) (xa : ID) (x : SNode) (ya : ID) (y : SNode), k < j → o[j]? = some xa → T[xa]?.join = some x → o[k]? = some ya →
    T[ya]?.join = some y → x.rankLt y = true →
    ∃ i a, k ≤ i ∧ i < j ∧ o[i]? = some a ∧ x.args.contains a = true ∧ isNode a = true

theorem rankScan_iff (T : Array (Option SNode)) (isNode : ID → Bool) (o : Array ID) (x : SNode) :
    ∀ n, rankScan T isNode o x n = true ↔ ∀ k ya y, k < n → o[k]? = some ya →
      T[ya]?.join = some y → x.rankLt y = true →
      ∃ i a, k ≤ i ∧ i < n ∧ o[i]? = some a ∧ x.args.contains a = true ∧ isNode a = true
  | 0 => by simp [rankScan]
  | n + 1 => by
    have ih := rankScan_iff T isNode o x n
    unfold rankScan
    cases hn : o[n]? with
    | none =>
      simp only
      rw [ih]
      constructor
      · intro h k ya y hk hya hy hr
        have hkn : k ≠ n := fun e => by rw [e, hn] at hya; cases hya
        obtain ⟨i, a, h1, h2, h3⟩ := h k ya y (by omega) hya hy hr
        exact ⟨i, a, h1, by omega, h3⟩
      · intro h k ya y hk hya hy hr
        obtain ⟨i, a, h1, h2, h3, h4⟩ := h k ya y (by omega) hya hy hr
        have hin : i ≠ n := fun e => by rw [e, hn] at h3; cases h3
        exact ⟨i, a, h1, by omega, h3, h4⟩
    | some a =>
      simp only
      by_cases han : (x.args.contains a && isNode a) = true
      · rw [if_pos han]
        simp only [true_iff]
        intro k ya y hk _ _ _
        rw [Bool.and_eq_true] at han
        exact ⟨n, a, by omega, by omega, hn, han.1, han.2⟩
      · rw [if_neg han, Bool.and_eq_true, ih]
        constructor
        · rintro ⟨hc, h⟩ k ya y hk hya hy hr
          by_cases hkn : k = n
          · subst hkn
            rw [hn] at hya; cases hya
            rw [hy] at hc
            simp [hr] at hc
          · obtain ⟨i, b, h1, h2, h3⟩ := h k ya y (by omega) hya hy hr
            exact ⟨i, b, h1, by omega, h3⟩
        · intro h
          have hne : ∀ i b, i < n + 1 → o[i]? = some b → x.args.contains b = true →
              isNode b = true → i < n := fun i b hi hb h1 h2 => by
            refine Nat.lt_of_le_of_ne (by omega) fun e => han ?_
            rw [e, hn] at hb; cases hb
            rw [h1, h2]; rfl
          refine ⟨?_, fun k ya y hk hya hy hr => ?_⟩
          · cases hy : T[a]?.join with
            | none => rfl
            | some y =>
              simp only [Bool.not_eq_true']
              cases hr : x.rankLt y
              · rfl
              · obtain ⟨i, b, h1, h2, h3, h4, h5⟩ := h n a y (by omega) hn hy hr
                exact absurd (hne i b h2 h3 h4 h5) (by omega)
          · obtain ⟨i, b, h1, h2, h3, h4, h5⟩ := h k ya y (by omega) hya hy hr
            exact ⟨i, b, h1, hne i b h2 h3 h4 h5, h3, h4, h5⟩

theorem nat_all_iff {n : Nat} {f : (i : Nat) → i < n → Bool} :
    Nat.all n f = true ↔ ∀ i (h : i < n), f i h = true := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.all_succ, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_or_ge i n with hl | hl
      · exact h1 i hl
      · obtain rfl : i = n := by omega
        exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

theorem rankOKFast_iff (vs : Array SNode) (isNode : ID → Bool) (o : Array ID) :
    rankOKFast vs isNode o = true ↔ RankProp (npTable vs) isNode o := by
  unfold rankOKFast RankProp
  rw [nat_all_iff]
  constructor
  · intro h j k xa x ya y hkj hxa hx hya hy hr
    have hj : j < o.size := (Array.getElem?_eq_some_iff.1 hxa).1
    have := h j hj
    rw [hxa] at this
    simp only [Option.bind_some, hx] at this
    exact (rankScan_iff _ _ _ _ j).1 this k ya y hkj hya hy hr
  · intro h j hj
    cases hxa : o[j]? with
    | none => rfl
    | some xa =>
      simp only [Option.bind_some]
      cases hx : (npTable vs)[xa]?.join with
      | none => rfl
      | some x =>
        exact (rankScan_iff _ _ _ _ j).2 fun k ya y hkj hya hy hr =>
          h j k xa x ya y hkj hxa hx hya hy hr

theorem rankOK_iff (vs : Array SNode) (isNode : ID → Bool) (o : Array ID) :
    rankOK vs isNode o = true ↔ RankProp (npTable vs) isNode o := by
  unfold rankOK RankProp
  simp only [List.all_eq_true, List.mem_filter, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt]
  constructor
  · intro h j k xa x ya y hkj hxa hx hya hy hr
    have hj : j < o.size := (Array.getElem?_eq_some_iff.1 hxa).1
    have hk : k < o.size := by omega
    have := h j ⟨hj, by simp [hxa, hx]⟩ k ⟨hk, by simp [hya, hy]⟩
    rw [hya, hxa] at this
    simp only [Option.bind_some, hy, hx, hr, Bool.not_true, Bool.false_or] at this
    rcases this with h1 | h1
    · omega
    · obtain ⟨d, hd, hda⟩ := List.any_eq_true.1 h1
      rw [List.mem_range] at hd
      cases ha : o[k + d]? with
      | none => rw [ha] at hda; cases hda
      | some a =>
        rw [ha, Bool.and_eq_true] at hda
        exact ⟨k + d, a, by omega, by omega, ha, hda.1, hda.2⟩
  · intro h j ⟨hj, hjn⟩ k ⟨hk, hkn⟩
    by_cases hkj : k < j
    · refine .inr ?_
      cases hxa : o[j]? with
      | none => rw [hxa] at hjn; simp at hjn
      | some xa =>
        cases hya : o[k]? with
        | none => rw [hya] at hkn; simp at hkn
        | some ya =>
          rw [hxa] at hjn; rw [hya] at hkn
          simp only [Option.bind_some] at hjn hkn ⊢
          obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hjn
          obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hkn
          rw [hx, hy]
          simp only
          cases hr : x.rankLt y
          · rfl
          · obtain ⟨i, a, h1, h2, h3, h4, h5⟩ := h j k xa x ya y hkj hxa hx hya hy hr
            simp only [Bool.not_true, Bool.false_or]
            refine List.any_eq_true.2 ⟨i - k, List.mem_range.2 (by omega), ?_⟩
            rw [show k + (i - k) = i by omega, h3]
            simp only [h4, h5, Bool.and_self]
    · exact .inl (by omega)

@[csimp] theorem rankOK_eq_rankOKFast : @rankOK = @rankOKFast := by
  funext vs isNode o
  exact Bool.eq_iff_iff.2 ((rankOK_iff vs isNode o).trans (rankOKFast_iff vs isNode o).symm)

variable [Addrs]

/-- `o` lists every node of `vs` exactly once (`vs` has distinct IDs), each after its
arguments within the block (a dependency order), pure nodes as early as their arguments allow
relative to the other nodes, and nodes of priority ≤ 1 (pure or `NilCheck`) as early as their
arguments allow relative to the other roots (`schedValidAux`, once per flag), and the non-pure nodes in rank
order as far as their arguments allow (`rankOK`). Validates
`kahn`'s output, so proofs use this specification rather than the algorithm. -/
def schedValid (vs : Array SNode) (o : Array ID) : Bool :=
  let m := maxNodeId vs + 1
  let nodes (early : SNode → Bool) : Array (Option (Array ID × Bool)) :=
    vs.foldl (fun t n => t.set! n.id (some (n.args, early n))) (Array.replicate m none)
  let pureNodes := nodes (·.prio == 0)
  idsDistinct (Array.replicate m false) vs.toList && o.size == vs.size &&
    schedValidAux pureNodes (Array.replicate m 0) 0 0 o.toList &&
    schedValidAux (nodes (·.prio ≤ 1)) (Array.replicate m 0) 0 0 o.toList &&
    rankOK vs (fun a => (pureNodes[a]?.join).isSome) o

/-- The index in `l` of the node of least rank (`SNode.rankLt`) among those with `p`. -/
def minIdx (p : SNode → Bool) : List SNode → Option Nat
  | [] => none
  | n :: ns =>
    match minIdx p ns with
    | none => if p n then some 0 else none
    | some i =>
      if p n && (ns[i]?.all fun m => n.rankLt m) then some 0 else some (i + 1)

/-- A simple scheduler, used only if `kahn`'s output fails validation (never on the corpus):
repeatedly the first ready pure node, else the ready node of least rank (`fuel`: one step per
node). It makes `schedule` provably defined on every acyclic block without a proof of
`kahn`. -/
def greedy (vs : List SNode) : Nat → List SNode → List ID → Option (List ID)
  | _, [], acc => some acc.reverse
  | 0, _ :: _, _ => none
  | fuel + 1, rem@(_ :: _), acc =>
    let ready (n : SNode) : Bool :=
      n.args.all fun a => !(vs.any (·.id == a)) || acc.contains a
    match rem.findIdx? (fun n => n.prio == 0 && ready n) with
    | some i => greedy vs fuel (rem.eraseIdx i) ((rem[i]?.map (·.id)).getD 0 :: acc)
    | none =>
      match minIdx ready rem with
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

/-- What the panic machinery needs of a function's open-coded defers (§9.7): its `deferBits`
variable (the `deferbits` name flag, export format 4) and its `opendeferslot` variables by
index (their frame offset at SSA time), each with whether its frame block is `Blk.local`
(`Tables.forgeable`). -/
structure DeferInfo where
  bits : Option (AuxRef × Bool) := none
  slots : Array (Option (AuxRef × Bool)) := #[]
  deriving Inhabited, DecidableEq

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
  /-- The activation number (frame blocks are `Blk.local act name`/`Blk.temp act name`). -/
  act : Nat := 0
  /-- The open-coded defers (`deferInfo`). -/
  defers : DeferInfo := {}
  deriving Inhabited

/-- A variable whose address the function converts to an integer (`addrconv`, export format
3: the address reaches a `Convert` to `uintptr` in the `start` section, e.g. `uintptr(unsafe.
Pointer(&x))` or the copy a `range` over an array iterates with `uintptr` arithmetic), or a
parameter or result: its frame block is `Blk.local`, which an integer may convert back to; every
other `PAUTO`, address-taken or not, is `Blk.temp` (§3.3). -/
def _root_.GoFV.SSA.Tables.forgeable (tabs : Tables) (n : AuxRef) : Bool :=
  match tabs.aux? n with
  | some { kind := .name _ cls _ _ _ fl _, .. } => cls != .PAUTO || fl.addrconv
  | _ => true

/-- The open-coded defer variables of the tables' function (`DeferInfo`). -/
def deferInfo (tabs : Tables) : DeferInfo :=
  (List.range tabs.auxes.size).foldl (fun di n =>
    match tabs.aux? n with
    | some { kind := .name _ cls _ off _ fl _, .. } =>
      if cls != .PAUTO then di
      else if fl.deferbits then
        { di with bits := di.bits <|> some (n, tabs.forgeable n) }
      else if fl.opendeferslot && 0 ≤ off then
        let i := off.toNat
        let slots := if i < di.slots.size then di.slots
          else di.slots ++ Array.replicate (i + 1 - di.slots.size) none
        { di with slots := slots.set! i (some (n, tabs.forgeable n)) }
      else di
    | _ => di) {}

/-- The frame block of variable `n` of activation `act`. -/
def frameBlk (tabs : Tables) (act : Nat) (n : AuxRef) : Blk :=
  if tabs.forgeable n then .local act n else .temp act n

/-- `VarDef {n}` poisons `n`'s block only when `n` is a `PAUTO`. `VarDef` is a zero-width
liveness annotation (`genericOps.go:562`): it writes nothing. A variable's bytes can change at
the start of its live range only through MergeLocals, which shares the slots of `PAUTO`s with
disjoint live ranges, starting at `VarDef` (`mergelocals.go`, `ssa/func.go:869-880`); it never
merges a `PPARAM`/`PPARAMOUT`. On those (and on any other aux) `VarDef` is the identity, as
`VarLive` is. -/
def _root_.GoFV.SSA.Tables.varDefPoisons (tabs : Tables) (n : AuxRef) : Bool :=
  match tabs.aux? n with
  | some { kind := .name _ cls .., .. } => cls == .PAUTO
  | _ => false

/-- The memory after `VarDef {n}` of activation `act` (`Tables.varDefPoisons`). -/
def varDefMem (tabs : Tables) (act : Nat) (n : AuxRef) (m : Mem) : Mem :=
  if tabs.varDefPoisons n then m.poisonBlock (frameBlk tabs act n) else m

/-- A property of memories that holds before a `VarDef` and after poisoning its block holds
after the `VarDef`. -/
theorem varDefMem_of {P : Mem → Prop} {tabs : Tables} {act : Nat} {n : AuxRef} {m : Mem}
    (h : P m) (hp : P (m.poisonBlock (frameBlk tabs act n))) : P (varDefMem tabs act n m) := by
  unfold varDefMem; split <;> assumption

/-- A relation between memories that holds before a `VarDef` and after poisoning its block on
both sides holds after the `VarDef` on both sides. -/
theorem varDefMem_rel {R : Mem → Mem → Prop} {tabs : Tables} {act : Nat} {n : AuxRef}
    {m m' : Mem} (h : R m m')
    (hp : R (m.poisonBlock (frameBlk tabs act n)) (m'.poisonBlock (frameBlk tabs act n))) :
    R (varDefMem tabs act n m) (varDefMem tabs act n m') := by
  unfold varDefMem; split <;> assumption

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

/-- The shape of every type of the tables, by type number (computed once per function). -/
def typeShapes (tabs : Tables) : Array Ty := (List.range tabs.types.size).toArray.map tabs.ty

/-- The shape of a value's type (`other` for an absent value). -/
def valueTy (shapes : Array Ty) : Option Value → Ty
  | some v => shapes[v.type]?.getD .other
  | none => .other

def Ctx.make (tabs : Tables) (f : Func) : Ctx :=
  let ps := abiParams tabs f
  let ins := ps.filter (!·.out)
  let params := ins.map (·.name)
  { f := f
    tabs := tabs
    tys := f.valueTab.map (valueTy (typeShapes tabs))
    sched := f.blockTab.map fun o => o.bind (schedule f)
    params := params
    paramTys := ins.map (tabs.ty ·.type)
    outs := (ps.filter (·.out)).map fun p => (p.name, tabs.ty p.type, p.regs.size)
    locals := frameLocals tabs params
    defers := deferInfo tabs }

/-- The state of an activation: the latest value of each value ID (by ID), the function's
arguments and initial memory. -/
structure Frame where
  regs : Array (Option Val)
  args : List Val
  mem0 : Mem
  /-- The in-memory image of each argument (its encoding by the parameter's shape), which
  `Arg`/`ArgIntReg` pieces are read from. -/
  images : Array (Array Byte) := #[]
  /-- The closure context of the activation (`GetClosurePtr`): `Env.closure` at the top-level
  activation (`entryFrame`), the call's context in a called one (`runActivation`); `none`
  outside a closure. -/
  closure : Option Val := none

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

/-- `ArgFloatReg {name+off} [reg]` (P4): a float register piece of a parameter, read like
`ArgIntReg`; an ill-formed one (no name, or a name that is not a parameter) is `poison`
rather than `stuck`, so the op evaluates like a pure value. -/
def argFloat (ctx : Ctx) (fr : Frame) (v : Value) (ty : Ty) : Val :=
  match v.aux.bind ctx.tabs.aux? with
  | some { kind := .nameOff n off, .. } =>
    match argVal ctx fr n off ty with
    | .ok x => x
    | _ => .poison
  | _ => .poison

/-- `PanicBounds [kind] x y mem` (§6): `x` read signed for the signed kinds (even, below
`BoundsConvert` = 16), `y` signed. -/
def panicBounds (kind : Int64) : List Val → Res Val
  | [.int _ x, .int _ y, .mem m] =>
    let k := kind.toInt.toNat
    let xi := if k % 2 == 0 && k < 16 then x.toInt else x.toNat
    .panic (.bounds k xi y.toInt) m
  | _ => .stuck "PanicBounds: undefined or ill-typed arguments"

/-! ## Calls (§5, phase P3) -/

/-- The `*AuxCall` ABI assignments of a call value's aux. -/
def callABI? (tabs : Tables) (aux : Option AuxRef) : Option CallABI :=
  match aux.bind tabs.aux? with
  | some { kind := .call _ abi, .. } => abi
  | _ => none

/-- The function a code pointer points to: the start of a code symbol (a closure's first word,
an itab's method entry, `Addr {fn}`). -/
def codeTarget? : Val → Option String
  | .ptr ⟨.global s, off⟩ => if off == 0 then some s else none
  | _ => none

mutual
/-- `v` contains `poison` (anywhere inside a composite or blob). -/
def Val.hasPoison : Val → Bool
  | .poison => true
  | .agg vs => Val.anyPoison vs
  | .tuple vs => Val.anyPoison vs
  | .blob bs => bs.contains .poison
  | _ => false
/-- Some value of `vs` contains `poison`. -/
def Val.anyPoison : List Val → Bool
  | [] => false
  | v :: vs => v.hasPoison || Val.anyPoison vs
end

/-- The register-assigned leaves of a shape, at their offsets, in the order of the ABI's
register assignment (fields in order; string: pointer, length; slice: pointer, length,
capacity; interface: type word, data word). -/
def leaves : Ty → List (Nat × Ty)
  | .agg fs _ => leavesFields fs
  | .str => [(0, .ptr (some 1)), (8, .int .w64)]
  | .slice e => [(0, .ptr e), (8, .int .w64), (16, .int .w64)]
  | .empty => []
  | .blob _ => []
  | t => [(0, t)]
where
  leavesFields : List (Nat × Ty) → List (Nat × Ty)
    | [] => []
    | (o, t) :: fs => (leaves t).map (fun (o', t') => (o + o', t')) ++ leavesFields fs

/-- A value of shape `t` from its register pieces (in `leaves t` order). -/
def ofPieces (t : Ty) (pieces : List Val) : Val :=
  let buf := ((leaves t).zip pieces).foldl (fun buf ((o, lt), v) => putBytes buf o (encode lt v))
    (Array.replicate t.size Byte.poison)
  decode buf 0 t

/-- The register pieces of a value of shape `t`. -/
def toPieces (t : Ty) (v : Val) : List Val :=
  let buf := encode t v
  (leaves t).map fun (o, lt) => decode buf o lt

/-- The Go-typed arguments of a post-`expand calls` call (§5): each input parameter of the
call's ABI assignments from its register pieces, or from the outgoing-arguments area of
activation `act` at its stack offset. -/
def decodeArgs (tabs : Tables) (act : Nat) (m : Mem) :
    List ABIParam → List Val → Option (List Val)
  | [], [] => some []
  | [], _ :: _ => none
  | p :: ps, pieces =>
    let t := tabs.ty p.type
    if p.regs.isEmpty then do
      let bs ← m.read ⟨.outargs act, BitVec.ofInt 64 p.offset⟩ t.size
      return decode bs 0 t :: (← decodeArgs tabs act m ps pieces)
    else
      let k := p.regs.size
      if pieces.length < k then none
      else do return ofPieces t (pieces.take k) :: (← decodeArgs tabs act m ps (pieces.drop k))

/-- The register pieces of the Go-typed results `rs` of a post-`expand calls` call; results
assigned to the stack are written to the outgoing-arguments area of activation `act`. -/
def encodeResults (tabs : Tables) (act : Nat) :
    List ABIParam → List Val → Mem → Option (List Val × Mem)
  | [], [], m => some ([], m)
  | p :: ps, r :: rs, m =>
    let t := tabs.ty p.type
    if p.regs.isEmpty then do
      let m ← m.write ⟨.outargs act, BitVec.ofInt 64 p.offset⟩ (encode t r)
      encodeResults tabs act ps rs m
    else do
      let (pieces, m) ← encodeResults tabs act ps rs m
      return (toPieces t r ++ pieces, m)
  | _, _, _ => none

/-- Values `rs` at the shapes of the ABI parameters `ps`: a callee's results at the call's result
types (the results a contract returns are Go-typed by the call), and a pre-`expand calls` call's
arguments at its parameter types (as the post form decodes them from their pieces); extra or
missing values are left for `encodeResults`/the contract to reject. -/
def retypeResults (tabs : Tables) : List ABIParam → List Val → List Val
  | p :: ps, r :: rs => r.retype (tabs.ty p.type) :: retypeResults tabs ps rs
  | _, rs => rs

/-- The callee, closure context and remaining arguments of call value `v` on arguments
`argv`: a closure call's code pointer and context, an interface call's code pointer, or the
static call's `AuxCall` function. -/
def callTarget (ctx : Ctx) (v : Value) (argv : List Val) : Option String × Option Val × List Val :=
  match v.op, argv with
  | .ClosureLECall, code :: c :: rest | .ClosureCall, code :: c :: rest =>
    (codeTarget? code, some c, rest)
  | .InterLECall, code :: rest | .InterCall, code :: rest => (codeTarget? code, none, rest)
  | _, _ => (v.aux.bind ctx.tabs.callee?, none, argv)

/-- The slots of the stack-assigned input parameters `ins` in the outgoing-arguments area of
activation `act` are writable in `m` (`Mem.canWrite`): where post-`expand calls` code stores
the stack arguments before the call. -/
def outargsOK (tabs : Tables) (act : Nat) (m : Mem) (ins : List ABIParam) : Bool :=
  ins.all fun p => !p.regs.isEmpty ||
    m.canWrite ⟨.outargs act, BitVec.ofInt 64 p.offset⟩ (tabs.ty p.type).size

/-- The end of a call's frame in its caller's outgoing-arguments area (§5): the callee owns the
area below it while it runs. abi-internal.md: the caller reserves the callee's stack-assigned
arguments and results, then "spill space for each register-assigned argument", which the callee
may use as their home; the frame ends at `spillOff + spillSize` of the call's ABI assignments
(the area below it also holds the fixed-frame word below the arguments, `ArgWidth` above it),
or at the end of a slot of a stack-assigned input parameter `ins` beyond it (Go's assignments
have none); 0 without assignments. A callee that never uses the spill slots (`spills = false`,
`Env.noSpill`) owns only its stack arguments' slots. -/
def callFrame (tabs : Tables) (aux : Option AuxRef) (ins : List ABIParam) (spills : Bool) : Nat :=
  ins.foldl (fun n p =>
      if p.regs.isEmpty then max n ((BitVec.ofInt 64 p.offset).toNat + (tabs.ty p.type).size)
      else n)
    (if spills then ((callABI? tabs aux).map fun a => (a.spillOff + a.spillSize).toNat).getD 0
     else 0)

/-! ## Deferred calls and recover (§9.7, phase P5) -/

/-- The `deferproc` entries of every activation, oldest first: 16 bytes each (`entryTy`: the
activation number, the closure). A global without an address and without a Go name. -/
def deferBlk : Blk := .global "gofv:defers"

/-- The panic record `recover` reads (`recTy`). -/
def panicBlk : Blk := .global "gofv:panic"

/-- A `deferproc` entry: the activation that registered it, the closure. -/
def entryTy : Ty := .agg [(0, .int .w64), (8, .ptr none)] 16

/-- The panic record: whether `recover` was called, whether the deferred function is a
wrapper, the activation of the deferred call (0: none; activation 0 is a run's own, never a
deferred call's), the value `recover` returns. -/
def recTy : Ty := .agg [(0, .int .w8), (1, .int .w8), (8, .int .w64), (16, .iface)] 32

/-- The `deferproc` entries (activation, closure), oldest first. -/
def deferEntries (m : Mem) : List (Val × Val) :=
  match m.find? deferBlk with
  | some a => (List.range (a.data.size / 16)).map fun i =>
      (decode a.data (16 * i) (.int .w64), decode a.data (16 * i + 8) (.ptr none))
  | none => []

def setDeferEntries (m : Mem) (es : List (Val × Val)) : Mem :=
  m.set deferBlk { data := (es.map fun (a, c) => encode entryTy (.agg [a, c])).foldl (· ++ ·) #[] }

/-- `deferproc` of activation `act`: a new entry. -/
def pushDefer (act : Nat) (clo : Val) (m : Mem) : Mem :=
  setDeferEntries m (deferEntries m ++ [(.i64 (BitVec.ofNat 64 act), clo)])

/-- The newest entry, removed, if activation `act` registered it (an undefined entry is
observed: an error). -/
def popDefer (act : Nat) (m : Mem) : Except String (Option (Val × Mem)) :=
  let es := deferEntries m
  match es.getLast? with
  | some (a, c) =>
    match a.asInt .w64 with
    | some k => .ok (if k.toNat == act then some (c, setDeferEntries m es.dropLast) else none)
    | none => .error "undefined defer entry"
  | none => .ok none

def setPanicRec (m : Mem) (recovered wrapper : Bool) (act : Nat) (v : Val) : Mem :=
  m.set panicBlk { data := encode recTy (.agg [.i8 (if recovered then 1 else 0),
    .i8 (if wrapper then 1 else 0), .i64 (BitVec.ofNat 64 act), v]) }

/-- The panic record (recovered, wrapper, activation, value), `none` without one; an
undefined record is observed (an error). -/
def panicRec? (m : Mem) : Except String (Option (Bool × Bool × Nat × Val)) :=
  match m.find? panicBlk with
  | none => .ok none
  | some a =>
    match decode a.data 0 recTy with
    | .agg [r, w, k, v] =>
      match r.asInt .w8, w.asInt .w8, k.asInt .w64 with
      | some r, some w, some k => .ok (some (r != 0, w != 0, k.toNat, v))
      | _, _, _ => .error "undefined panic record"
    | _ => .error "undefined panic record"

/-- The nil `any` (its data word the nil pointer's word, address 0). -/
def nilIface : Val := .agg [.i64 0, .i64 0]

/-- The value `recover` returns for a panic: `gopanic`'s argument, or for a runtime error a
non-nil `any` whose type word is an opaque global (its data word is not modelled). -/
def _root_.GoFV.SSA.Sem.Panic.toAny : Panic → Val
  | .value bs => decode bs.toArray 0 .iface
  | _ => .agg [.ptr ⟨.global "gofv:runtime.Error", 0⟩, .poison]

/-- A wrapper function by its link name (`deferwrap` closures, method value wrappers), which
`recover`'s stack walk skips. -/
def isWrapperName (name : String) : Bool :=
  (name.splitOn ".deferwrap").length > 1 || name.endsWith "-fm"

/-- The code symbol of the deferred closure `clo` (a pointer word, `Val.asPtrWord`; its code is
its first word): `none` for a nil closure (calling it faults); an undefined closure or code word
is an error. `runDefers` reads it before it sets the panic record, so the record's wrapper flag
(`deferredWrapper`) and the call (`callDeferred`) name the same callee. -/
def deferredCode? (m : Mem) (clo : Val) : Except String (Option String) :=
  match clo.asPtrWord with
  | some p =>
    if p.isNil then .ok none
    else
      match codeTarget? (m.load (.ptr none) p) with
      | some name => .ok (some name)
      | none => .error "deferred call without a known callee"
  | none => .error "deferred call of an undefined closure"

/-- The deferred function with code symbol `code` (`deferredCode?`, read before the panic record
is set) is a wrapper. -/
def deferredWrapper : Option String → Bool
  | some n => isWrapperName n
  | none => false

/-- Run the deferred closure `clo` of activation `act` with code symbol `code` (`deferredCode?`,
read before the panic record is set; `none`: a nil closure, which faults): a closure call without
arguments. The caller's outgoing area is the callee's (`callOp`). -/
def callDeferred (env : Env) (act : Nat) (clo : Val) : Option String → Mem → COutcome
  | none, m => .panicked .nilDeref m
  | some name, m =>
    match env.extern name with
    | some c => c [] (some clo) (m.poisonBlock (.outargs act))
    | none => .stuck s!"deferred call {name}: no contract"

/-- The runtime's block `b` (`deferBlk`, `panicBlk`) may be replaced: it is absent or writable.
The runtime entry points never overwrite a read-only allocation there (only an initial memory
or a global image could hold one): they are `stuck` instead, so contracts keep the read-only
allocations (`Mem.KeepsRo`). -/
def rtWritable (m : Mem) (b : Blk) : Bool :=
  match m.find? b with
  | some a => a.writable
  | none => true

/-- `runtime.deferproc(fn)` from activation `act`. -/
def deferproc (act : Nat) : Contract := fun args _ m =>
  match args with
  | [fn] =>
    if rtWritable m deferBlk then .returned [] (pushDefer act fn m)
    else .stuck "deferproc: read-only defer list"
  | _ => .stuck "deferproc: bad arguments"

/-- `runtime.deferprocStack(d *_defer)` from activation `act`: `d.fn` is at offset 24 (`d` is
passed as a `uintptr`: after `expand calls` an integer, whose variable is `addrconv`). -/
def deferprocStack (act : Nat) : Contract := fun args _ m =>
  let reg (d : Ptr) : COutcome :=
    match m.load (.ptr none) ⟨d.blk, d.off + 24⟩ with
    | .poison => .stuck "deferprocStack: undefined fn"
    | fn =>
      if rtWritable m deferBlk then .returned [] (pushDefer act fn m)
      else .stuck "deferprocStack: read-only defer list"
  match args with
  | [.ptr d] => reg d
  | [.int .w64 x] => reg (Ptr.ofAddr x)
  | _ => .stuck "deferprocStack: bad arguments"

/-- `runtime.deferreturn()` from activation `act`: runs the activation's `deferproc` entries,
newest first. -/
def deferreturn (env : Env) (act : Nat) : Contract := fun _ _ m =>
  go (deferEntries m).length m
where
  go : Nat → Mem → COutcome
    | 0, m => .returned [] m
    | n + 1, m =>
      if !rtWritable m deferBlk then .stuck "deferreturn: read-only defer list" else
      match popDefer act m with
      | .error msg => .stuck msg
      | .ok none => .returned [] m
      | .ok (some (clo, m)) =>
        match deferredCode? m clo with
        | .error msg => .stuck msg
        | .ok code =>
          match callDeferred env act clo code m with
          | .returned _ m => go n m
          | o => o

/-- `runtime.gorecover()` from activation `act` (`runtime/panic.go`): the panic's value if a
panic is being handled, not yet recovered, and the caller is the deferred function the panic
machinery called, or that function's direct callee when it is a wrapper; `nil` otherwise. -/
def gorecover (act : Nat) : Contract := fun _ _ m =>
  match panicRec? m with
  | .error msg => .stuck msg
  | .ok (some (false, w, k, v)) =>
    if k != 0 && (act == k || (w && act == k + 1)) then
      if rtWritable m panicBlk then .returned [v] (setPanicRec m true w k v)
      else .stuck "gorecover: read-only panic record"
    else .returned [nilIface] m
  | .ok _ => .returned [nilIface] m

/-- The environment of a call from activation `act`: `env` with the runtime entry points that
work on the caller's activation (`deferproc`, `deferprocStack`, `deferreturn`, `gorecover`). -/
def _root_.GoFV.SSA.Sem.Env.atAct (env : Env) (act : Nat) : Env :=
  { env with extern := fun name =>
      if name == "runtime.deferproc" then some (deferproc act)
      else if name == "runtime.deferprocStack" then some (deferprocStack act)
      else if name == "runtime.deferreturn" then some (deferreturn env act)
      else if name == "runtime.gorecover" then some (gorecover act)
      else env.extern name }

/-- The runtime entry points `Env.atAct` overrides. -/
def isDeferName (name : String) : Bool :=
  name == "runtime.deferproc" || name == "runtime.deferprocStack" ||
    name == "runtime.deferreturn" || name == "runtime.gorecover"

/-- Other callees are `env`'s. -/
theorem _root_.GoFV.SSA.Sem.Env.atAct_extern_of {env : Env} {act : Nat} {name : String}
    (h : isDeferName name = false) : (env.atAct act).extern name = env.extern name := by
  simp only [isDeferName, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  simp [Env.atAct, h1, h2, h3, h4]

/-- The closure of a closure call is the nil pointer word (`Val.asPtrWord`). Go loads the code
word from the closure without a nil check (arm64 faults), so the call panics with `nilDeref`
(`deferNilFunc`: an open-coded `defer f()` of a nil `f` at a normal exit). -/
def nilClosure (clo : Option Val) : Bool :=
  match clo.bind Val.asPtrWord with
  | some p => p.isNil
  | none => false

@[simp] theorem nilClosure_none : nilClosure none = false := rfl

/-- A call (§5): `StaticLECall {AuxCall} args… mem`, `ClosureLECall code ctx args… mem`,
`InterLECall code args… mem` pass Go-typed arguments and yield `(results…, mem)`; their
post-`expand calls` forms `StaticCall`, `ClosureCall`, `InterCall` pass register pieces and
stack arguments in the outgoing-arguments area, and yield the results' register pieces (stack
results are stored back into the outgoing area). The callee is the `AuxCall`'s function or the
code symbol the code pointer points to; its contract sees the Go-typed arguments (the pre form's
retyped at the parameters' shapes, `retypeResults`: an `unsafe.Pointer` passed to a `uintptr`
parameter is its address, as the post form decodes it). Arguments
and memory are observation points (`poison` ⇒ `stuck`). The callee owns its frame in the
caller's outgoing-arguments area while it runs (`callFrame`: its stack arguments and results
and the spill area of its register arguments, which it may use): its contract sees the area
below the frame's end poisoned, in both forms, so post-`expand calls` argument stores into it
are invisible to the callee except through the decoded arguments; the caller's bytes above it
are the caller's across the call. In both forms the call is
`stuck` unless the slots of its stack-assigned arguments are writable in its memory
(`outargsOK`; always so in a run, whose frame allocates the area): the post form's argument
stores into them then cannot fail where the pre form's call succeeds. A closure call through a
nil closure (`nilClosure`) faults loading the closure's code word once its arguments are passed:
a `nilDeref` panic on the memory the callee would see, decided by the closure (the code word
loaded from it is `poison`, so the callee is unknown). -/
def callOp (env : Env) (ctx : Ctx) (v : Value) (argv : List Val) : Res Val := do
  let (callee?, clo, rest) := callTarget ctx v argv
  let m ← match rest.getLast? with
    | some (.mem m) => .ok m
    | _ => .stuck s!"v{v.id}: call without a memory argument"
  let pieces := rest.dropLast
  let post := v.op == .StaticCall || v.op == .ClosureCall || v.op == .InterCall
  let params := ((callABI? ctx.tabs v.aux).map (·.params.toList)).getD []
  let ins := params.filter (!·.out)
  let outs := params.filter (·.out)
  let args ← if post then
      Res.ofOption s!"v{v.id}: call arguments do not match the ABI" (decodeArgs ctx.tabs ctx.act m ins pieces)
    else pure (retypeResults ctx.tabs ins pieces)
  if args.any Val.hasPoison || (clo.map Val.hasPoison).getD false then
    .stuck s!"v{v.id}: call with a poison argument"
  else if !outargsOK ctx.tabs ctx.act m ins then
    .stuck s!"v{v.id}: call with an outgoing-arguments area not writable"
  else if nilClosure clo then
    .panic .nilDeref (m.poisonBelow (.outargs ctx.act) (callFrame ctx.tabs v.aux ins true))
  else
    let callee ← Res.ofOption s!"v{v.id}: call without a known callee" callee?
    let c ← Res.ofOption s!"call {callee}: no contract" ((env.atAct ctx.act).extern callee)
    match c args clo (m.poisonBelow (.outargs ctx.act)
        (callFrame ctx.tabs v.aux ins (!env.noSpill callee))) with
    | .returned rs m' =>
      let rs := retypeResults ctx.tabs outs rs
      -- stack-assigned results are in the outgoing area in both forms; their addresses follow
      -- the memory (`SelectNAddr`)
      let (ps, m'') ← Res.ofOption s!"call {callee}: results do not match the ABI"
        (encodeResults ctx.tabs ctx.act outs rs m')
      let addrs := Val.agg (outs.map fun p =>
        if p.regs.isEmpty then .ptr ⟨.outargs ctx.act, BitVec.ofInt 64 p.offset⟩ else .poison)
      if post then pure (.tuple (ps ++ [.mem m'', addrs]))
      else pure (.tuple (rs ++ [.mem m'', addrs]))
    | .panicked e m' => .panic e m'
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
`VarDef {n} mem` (poisons a `PAUTO` `n`, else the identity: `varDefMem`), `VarLive {n} mem`,
`KeepAlive x mem`, `WBend mem` (the end of a
write-barrier sequence: the GC has taken the buffer, `Blk.wbuf` is freed), `NilCheck p mem`
(§6). The address of a write and the pointer of a nil check are observation points; an
integer word is the pointer at its address (`Val.asPtrWord`, §3.3). -/
def memRoot (ctx : Ctx) (v : Value) (argv : List Val) : Res Val :=
  let what := s!"v{v.id}: {v.op.name}"
  match v.op, argv with
  | .Store, [a, x, .mem m] | .StoreWB, [a, x, .mem m] =>
    match a.asPtrWord with
    | some p => writeRes what (m.write p (encode (auxTy ctx.tabs v.aux) x))
    | none => .stuck s!"{what}: undefined or ill-typed address"
  | .Move, [a, b, .mem m] | .MoveWB, [a, b, .mem m] =>
    match a.asPtrWord, b.asPtrWord with
    | some d, some s =>
      match m.read s v.auxInt.toInt.toNat with
      | some bs => writeRes what (m.write d bs)
      | none => .stuck s!"{what}: invalid source"
    | _, _ => .stuck s!"{what}: undefined or ill-typed address"
  | .Zero, [a, .mem m] | .ZeroWB, [a, .mem m] =>
    match a.asPtrWord with
    | some p => writeRes what (m.write p (Array.replicate v.auxInt.toInt.toNat (.b 0)))
    | none => .stuck s!"{what}: undefined or ill-typed address"
  | .VarDef, [.mem m] =>
    match v.aux with
    | some n => .ok (.mem (varDefMem ctx.tabs ctx.act n m))
    | none => .stuck s!"{what}: no name"
  | .VarLive, [.mem m] => .ok (.mem m)
  | .WBend, [.mem m] => .ok (.mem (m.free .wbuf))
  | .KeepAlive, [_, .mem m] => .ok (.mem m)
  | .NilCheck, [a, .mem m] =>
    match a.asPtrWord with
    | some p => if p.blk == .nil then .panic .nilDeref m else .ok a
    | none => .stuck s!"{what}: undefined or ill-typed pointer"
  | _, args =>
    if args.any (fun | .poison => true | _ => false) then .stuck s!"{what}: poison argument"
    else .stuck s!"{what}: ill-typed arguments"

/-- Ops whose value depends on the activation or on symbols (not on `evalPure`'s inputs). -/
def frameVal (ctx : Ctx) (v : Value) : Option Val :=
  match v.op with
  | .SP => some (.ptr ⟨.outargs ctx.act, 0⟩)
  -- the caller's SP (`Addrs.callerSP`; under `Addrs.fixed` just above this activation's frame
  -- region, so "is this pointer in my frame" checks, `append` of a stack slice, see the frame)
  | .GetCallerSP => some (.int .w64 (Addrs.callerSP ctx.act))
  | .LocalAddr => v.aux.map fun n => .ptr ⟨frameBlk ctx.tabs ctx.act n, 0⟩
  | .Addr =>
    match v.aux.bind ctx.tabs.aux? with
    | some { kind := .sym name .., .. } => some (.ptr ⟨.global name.toStringLossy, 0⟩)
    | _ => some .poison
  | .ConstString =>
    match v.aux.bind ctx.tabs.aux? with
    | some { kind := .str s dataSym, .. } =>
      some (Val.ofStr [if s.size == 0 then .i64 0 else .ptr ⟨.global dataSym.toStringLossy, 0⟩,
        .i64 (BitVec.ofNat 64 s.size)])
    | _ => some .poison
  | _ => none

/-- The result of value `v` from its evaluated arguments `argv`, before it takes the shape
`ty` of its type (`evalValue`). -/
def evalOp (env : Env) (ctx : Ctx) (fr : Frame) (v : Value) (argv : List Val) (ty : Ty) :
    Res Val :=
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
  | .ArgFloatReg => pure (argFloat ctx fr v ty)
  | .PanicBounds => panicBounds v.auxInt argv
  | .StaticLECall | .StaticCall | .ClosureLECall | .ClosureCall | .InterLECall | .InterCall =>
    callOp env ctx v argv
  | .GetClosurePtr => pure (fr.closure.getD .poison)
  | .Store | .StoreWB | .Move | .MoveWB | .Zero | .ZeroWB | .VarDef | .VarLive | .KeepAlive
  | .WBend | .NilCheck => memRoot ctx v argv
  | op =>
    match frameVal ctx v with
    | some x => pure x
    | none =>
      if isRoot op then atomicRoot v argv
      else pure (evalPure op ty v.auxInt v.aux argv)

/-- Evaluate value `v` from the registers (its arguments are already evaluated); the result
takes the shape of the value's type (`Val.retype`, §3.2). -/
def evalValue (env : Env) (ctx : Ctx) (fr : Frame) (v : Value) : Res Val := do
  let argv ← v.args.toList.mapM fun a =>
    Res.ofOption s!"v{v.id}: argument v{a} has no value" (fr.regs[a]?).join
  let ty := ctx.tys[v.id]?.getD .other
  let r ← evalOp env ctx fr v argv ty
  pure (r.retype ty)

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
  -- `deferproc` returned: the normal path (a recovery returns through `finish`, §9.7)
  | .Defer => succ b 0
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

/-- The Go-typed results of a `Ret` (§7), from the `MakeResult` components `rs` (memory
removed) and the memory `m` at the return. Before `expand calls` the components are the
Go-typed results; after it they are the register pieces of the register-assigned results
(in ABI order), and stack-assigned results are in their `PPARAMOUT` variables. Both forms are
reduced to the results' bytes and decoded by the result types, so every section yields the
same values. A result containing `poison` is observed: `stuck`. -/
def goResults (outs : Array (Option AuxRef × Ty × Nat)) (act : Nat) (rs : List Val) (m : Mem) :
    Res (List Val) := do
  let outs := outs.toList
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
            let bs := (m.read ⟨.local act n, 0⟩ t.size).getD (Array.replicate t.size .poison)
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
    | .local a _ | .temp a _ | .outargs a => a != act
    | _ => true }

/-- The size of the outgoing-arguments area: the end of the furthest stack-assigned argument or
result of any call the tables describe. -/
def outargsSize (tabs : Tables) : Nat :=
  tabs.auxes.foldl (fun n o => match o with
    | some { kind := .call _ (some abi), .. } =>
      abi.params.foldl (fun n p =>
        if p.regs.isEmpty then max n ((p.offset.toNat) + (typeSize? tabs p.type).getD 0) else n) n
    | _ => n) 0

/-- `mem` with the global image of `env` (allocations not already in `mem`). -/
def addGlobals (env : Env) (mem : Mem) : Mem :=
  env.globals.foldl (fun m (name, a) =>
    if (m.find? (.global name)).isSome then m else m.set (.global name) a) mem

/-- `mem` with the outgoing-arguments area and the frame allocations of an activation. -/
def frameAllocs (ctx : Ctx) (images : Array (Array Byte)) (mem : Mem) : Mem :=
  let mem := mem.set (.outargs ctx.act)
    { data := Array.replicate (outargsSize ctx.tabs) .poison }
  ctx.locals.foldl (fun m (n, sz, pi) =>
    let data := match pi.bind (images[·]?) with
      | some img => if img.size == sz then img else Array.replicate sz .poison
      | none => Array.replicate sz .poison
    m.set (frameBlk ctx.tabs ctx.act n) { data }) mem

/-- The memory an activation starts with: `mem`, the global image of `env` (allocations not
already in `mem`), the outgoing-arguments area (poison) and the frame: one allocation per frame
variable, a `PPARAM` holding its argument's image, every other variable poison (§3.4). -/
def frameMem (env : Env) (ctx : Ctx) (images : Array (Array Byte)) (mem : Mem) : Mem :=
  frameAllocs ctx images (addGlobals env mem)

/-- The frame of a new activation on `args` from memory `mem`: no registers, the arguments'
images, the frame allocations (`frameMem`), the top-level closure context (`Env.closure`). -/
def entryFrame (env : Env) (ctx : Ctx) (args : List Val) (mem : Mem) : Frame :=
  let images := (args.toArray.zip ctx.paramTys).map fun (a, t) => encode t a
  { regs := Array.replicate ctx.f.valueTab.size none, args,
    mem0 := frameMem env ctx images mem, images, closure := env.closure }

/-- The top-level activation's closure context is the environment's. -/
theorem entryFrame_closure (env : Env) (ctx : Ctx) (args : List Val) (mem : Mem) :
    (entryFrame env ctx args mem).closure = env.closure := rfl

/-- Outside a closure (`env.closure = none`), `entryFrame` is the frame without a context. -/
theorem entryFrame_of_none {env : Env} (h : env.closure = none) (ctx : Ctx) (args : List Val)
    (mem : Mem) :
    entryFrame env ctx args mem =
      let images := (args.toArray.zip ctx.paramTys).map fun (a, t) => encode t a
      { regs := Array.replicate ctx.f.valueTab.size none, args,
        mem0 := frameMem env ctx images mem, images } := by
  unfold entryFrame; rw [h]

/-- The next deferred call of activation `act` (§9.7): the closure of the highest set bit of
the open-coded `deferBits` (the bit cleared), else the newest `deferproc` entry of `act`
(removed); `none` if there is none. An undefined `deferBits` is observed (an error). -/
def nextDefer (di : DeferInfo) (act : Nat) (m : Mem) : Except String (Option (Val × Mem)) :=
  let blk (n : AuxRef × Bool) : Blk := if n.2 then .local act n.1 else .temp act n.1
  match di.bits with
  | none => popDefer act m
  | some nb =>
    let p : Ptr := ⟨blk nb, 0⟩
    match (m.load (.int .w8) p).asInt .w8 with
    | none => .error "panic: undefined deferBits"
    | some bits =>
      match (List.range 8).reverse.find? (fun i => bits.getLsbD i) with
      | none => popDefer act m
      | some i =>
        match di.slots[i]? with
        | some (some sn) =>
          match m.write p (encode (.int .w8) (.i8 (bits &&& ~~~((1 : BitVec 8) <<< i)))) with
          | some m' => .ok (some (m.load (.ptr none) ⟨blk sn, 0⟩, m'))
          | none => .error "panic: deferBits not writable"
        | _ => .error s!"panic: no open-coded defer slot {i}"

/-- The results of a recovered activation: its result variables (`PPARAMOUT`, in memory in a
function with defers) at their result types. -/
def stackOuts (outs : Array (Option AuxRef × Ty × Nat)) : Array (Option AuxRef × Ty × Nat) :=
  outs.map fun (n, t, _) => (n, t, 0)

/-- The memory `r` after a deferred call of `runDefers` with the panic record `saved` from
before the call restored while panicking (`pe = some _`; `saved = none`: removed). -/
def restorePanicRec (pe : Option Panic) (saved : Option Alloc) (r : Mem) : Mem :=
  match pe, saved with
  | some _, some a => r.set panicBlk a
  | some _, none => r.free panicBlk
  | none, _ => r

/-- Run the deferred calls of activation `act` (at most `n`; §9.7). While panicking
(`pe = some e`) each runs with a panic record that lets it `recover` (`gorecover`), restored
afterwards (an outer panic's record, `none`: removed); a recovery ends the panic, the remaining
deferred calls run as at a normal exit, and the activation returns the values of its result
variables with its frame freed. A deferred call that panics replaces the panic; the frames of
its activations are gone (`dropFrames`). When no deferred call is left, a panic propagates with
the memory as it is. The deferred closure's code is read (`deferredCode?`) before the panic
record is set. -/
def runDefers (env : Env) (outs : Array (Option AuxRef × Ty × Nat)) (di : DeferInfo)
    (act : Nat) : Nat → Option Panic → Mem → Outcome
  | 0, _, _ => .stuck "too many deferred calls"
  | n + 1, pe, m =>
    match nextDefer di act m with
    | .error msg => .stuck msg
    | .ok none =>
      match pe with
      | some e => .panicked e m
      | none =>
        match goResults (stackOuts outs) act [] m with
        | .ok vals => .returned vals (m.freeFrame act)
        | .panic e m => .panicked e m
        | .stuck msg => .stuck msg
    | .ok (some (clo, m1)) =>
      match deferredCode? m1 clo with
      | .error msg => .stuck msg
      | .ok code =>
      let restore := restorePanicRec pe (m1.find? panicBlk)
      let m2 := match pe with
        | some e => setPanicRec m1 false (deferredWrapper code) m1.nextAct e.toAny
        | none => m1
      match callDeferred env act clo code m2 with
      | .returned _ m3 =>
        match pe with
        | some e =>
          match panicRec? m3 with
          | .ok (some (true, _)) => runDefers env outs di act n none (restore m3)
          | .ok (some (false, _)) => runDefers env outs di act n (some e) (restore m3)
          | .ok none => .stuck "panic record lost"
          | .error msg => .stuck msg
        | none => runDefers env outs di act n none m3
      | .panicked e2 m3 => runDefers env outs di act n (some e2) ((restore m3).dropFrames (act + 1))
      | .stuck msg => .stuck msg

/-- The outcome of an activation from its loop's outcome: Go-typed results (`goResults`) and
the memory without the frame; at a panic, the frames of the activation's callees are gone and
its deferred calls run (`runDefers`, §9.7); other outcomes unchanged. A `MakeResult` component
containing poison is observed (`stuck`) before decoding, so `finish` preserves refinement
(`docs/plans/semantics.md` §3.5). -/
def finish (env : Env) (outs : Array (Option AuxRef × Ty × Nat)) (di : DeferInfo) (act : Nat) :
    Outcome → Outcome
  | .returned rs m =>
    if Val.anyPoison rs then .stuck "poison result" else
    match goResults outs act rs m with
    | .ok vals => .returned vals (m.freeFrame act)
    | .panic e m => .panicked e m
    | .stuck msg => .stuck msg
  | .panicked e m =>
    let m := m.dropFrames (act + 1)
    runDefers env outs di act (9 + (deferEntries m).length) (some e) m
  | o => o

/-- `finish` only defines defined outcomes. -/
theorem finish_defined {env : Env} {outs : Array (Option AuxRef × Ty × Nat)} {di : DeferInfo}
    {act : Nat} {o : Outcome} (h : (finish env outs di act o).Defined) : o.Defined := by
  cases o with
  | returned => trivial
  | panicked => trivial
  | stuck => exact h
  | outOfFuel => exact h

/-- Run `f` (with the definition tables `tabs` of its export section) on the Go-typed
arguments `args` (receiver first) and memory `mem`, for at most `fuel` block entries: set up
the frame, run, decode the Go-typed results and remove the frame from the memory. -/
def runCtx (env : Env) (ctx : Ctx) (args : List Val) (mem : Mem) (fuel : Nat) : Outcome :=
  if args.length != ctx.params.size then
    .stuck s!"{args.length} arguments for {ctx.params.size} parameters"
  else
    finish env ctx.outs ctx.defers ctx.act
      (runLoop env ctx fuel (entryFrame env ctx args mem) ctx.f.entry 0)

/-! ## Program functions as callees -/

/-- A run's outcome as a callee's (`outOfFuel` is `stuck`: a callee always gets bounded fuel). -/
def Outcome.toC : Outcome → COutcome
  | .returned rs m => .returned rs m
  | .panicked e m => .panicked e m
  | .stuck msg => .stuck msg
  | .outOfFuel => .stuck "callee out of fuel"

/-- A called activation of the function of `ctx`: a fresh activation number from the memory,
its frame (the caller's memory already holds the globals), the closure context, the run,
Go-typed results and the frame removed. -/
def runActivation (env : Env) (ctx : Ctx) (clo : Option Val) (args : List Val) (mem : Mem)
    (fuel : Nat) : Outcome :=
  let act := mem.nextAct
  let ctx := { ctx with act }
  let mem := { mem with nextAct := act + 1 }
  if args.length != ctx.params.size then
    .stuck s!"{args.length} arguments for {ctx.params.size} parameters"
  else
    let images := (args.toArray.zip ctx.paramTys).map fun (a, t) => encode t a
    finish env ctx.outs ctx.defers act
      (runLoop env ctx fuel
        { regs := Array.replicate ctx.f.valueTab.size none, args, images, closure := clo,
          mem0 := frameAllocs ctx images mem } ctx.f.entry 0)

/-- The environment `base` extended with program functions (`funcs`: a function's context by
link symbol name), each run with `fuel` block entries per activation in the environment of
depth `d - 1`: calls between program functions nest at most `d` deep (deeper calls use
`base`, where a program function has no contract unless `base` gives one). -/
def Env.withFuncs (base : Env) (funcs : String → Option Ctx) (fuel : Nat) : Nat → Env
  | 0 => base
  | d + 1 =>
    { base with
      extern := fun name =>
        match funcs name with
        | some ctx => some fun args clo m =>
            (runActivation (base.withFuncs funcs fuel d) ctx clo args m fuel).toC
        | none => base.extern name }

end GoFV.SSA.Sem

namespace GoFV.SSA

/-- `GoFV.SSA.run`: the outcome of running `f` (with the tables `tabs` of its export section)
on `args` from memory `mem` with at most `fuel` block entries (`docs/plans/semantics.md` §8). -/
def run [Sem.Addrs] (env : Sem.Env) (tabs : Tables) (f : Func) (args : List Sem.Val) (mem : Sem.Mem)
    (fuel : Nat) : Sem.Outcome :=
  Sem.runCtx env (Sem.Ctx.make tabs f) args mem fuel

end GoFV.SSA

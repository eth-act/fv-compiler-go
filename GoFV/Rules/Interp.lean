import GoFV.Rules.Eval
import GoFV.SSA.Edges

/-!
# The rule interpreter

`rewriteValue rules v` / `rewriteBlock rules b` replay rulegen's generated
`rewriteValue<file>`/`rewriteBlock<file>` (docs/contracts/rules.md, "Semantics the interpreter
must replicate"): the rules of the op (block kind) in order, the first that fires wins; the
commutative choices of a rule are enumerated in pattern preorder, lexicographically with 0
(arguments in order) before 1 (swapped); `cond` is evaluated once per complete assignment;
results are built in rulegen's statement order, so values get the same IDs.

Checks are pure, so their order is free except that an `eq` field or a `same` argument whose
variable is not bound yet (rulegen binds a trailing plain argument first) is checked once the
whole pattern has matched.
-/

namespace GoFV.Rules

open GoFV.SSA

namespace Interp

open RwM Eval

/-- `auxIntTo<T>(i)` for an op's aux type. -/
def auxIntVal (aty : AuxType) (i : Int64) : Except String GVal :=
  let x := i.toInt
  match aty with
  | .Bool => .ok (.bool (i != 0))
  | .Int8 => .ok (.int (wrapInt 8 true x))
  | .Int16 => .ok (.int (wrapInt 16 true x))
  | .Int32 | .SymOff | .CallOff => .ok (.int (wrapInt 32 true x))
  | .Int64 | .TypSize => .ok (.int x)
  | .UInt8 => .ok (.int (wrapInt 8 false x))
  | .Float32 => .ok (.f32 (f64OfBits x).toFloat32)
  | .Float64 => .ok (.f64 (f64OfBits x))
  | a => .error s!"auxInt of aux type {repr a}"

/-- `<T>ToAuxInt(x)`. -/
def toAuxInt (aty : AuxType) (x : GVal) : Except String Int64 :=
  match aty, x with
  | .Bool, .bool b => .ok (if b then 1 else 0)
  | .UInt8, .int i => .ok (Int64.ofInt (wrapInt 8 true i))
  | .Float32, .f32 f => .ok (Int64.ofInt (f64Bits f.toFloat))
  | .Float64, .f64 f => .ok (Int64.ofInt (f64Bits f))
  | _, .int i => .ok (Int64.ofInt i)
  | a, _ => .error s!"bad auxInt value for aux type {repr a}"

/-- `auxTo<T>(a)` for an op's aux type. -/
def auxVal (tabs : Tables) (aty : AuxType) (a : Option AuxRef) : Except String GVal := do
  match aty with
  | .String =>
    let some a := a | throw "auxToString of nil"
    match (← Sym.auxDef tabs a).kind with
    | .str s _ => return .str s.bytes
    | _ => throw s!"aux a{a} is not a string"
  | .Typ | .TypSize => return .typ (← Ty.ofAux tabs a)
  | _ => return .aux a

/-- `<T>ToAux(x)`. -/
def toAux (x : GVal) : RwM (Option AuxRef) := do
  match x with
  | .aux a => return a
  | .nil => return none
  | .typ t => return some (← typeAux t)
  | _ => throw "unsupported aux value"

mutual
/-- Whether every rule variable `e` reads is bound. -/
def bound (binds : Array GVal) : Expr → Bool
  | .var i => match binds[i]? with
    | some .nil => false
    | some _ => true
    | none => false
  | .field x _ _ | .conv _ x | .assert _ x | .unop _ x _ | .deref x _ => bound binds x
  | .call _ as _ | .builtin _ as _ => boundAll binds as
  | .method x _ as _ => bound binds x && boundAll binds as
  | .binop _ x y _ | .index x y _ => bound binds x && bound binds y
  | _ => true
/-- `bound` of each expression. -/
def boundAll (binds : Array GVal) : List Expr → Bool
  | [] => true
  | e :: es => bound binds e && boundAll binds es
end

/-- A check postponed until the pattern has matched. -/
inductive Pending where
  | same (x : Nat) (w : ID)
  | eq (e : Expr) (actual : GVal)

/-- The match state: bindings (`nil` = unbound), postponed checks, and the values whose type
the type variables were bound from (`Scope.tySrc`). -/
structure MState where
  binds : Array GVal
  pending : List Pending
  tySrc : List (Nat × ID) := []

@[inline] def isUnbound (binds : Array GVal) (x : Nat) : Bool :=
  match binds[x]? with
  | some .nil => true
  | _ => false

/-- Check or bind a `<type>`/`[auxint]`/`{aux}` field; the field's value is computed only when
the pattern looks at it (an op without AuxInt has no `auxIntTo<T>`). -/
def field (sc : Scope) (st : MState) (fld : Field) (actual : Unit → RwM GVal) :
    RwM (Option MState) := do
  match fld with
  | .any => return some st
  | .bind x => return some { st with binds := st.binds.set! x (← actual ()) }
  | .eq e =>
    let actual ← actual ()
    if bound st.binds e then
      let want ← eval { sc with binds := st.binds } e
      return if actual.beq want then some st else none
    else return some { st with pending := .eq e actual :: st.pending }

/-- Bound on the work items `matchWork` takes on one search path (each pattern node is taken
once). -/
def matchFuel : Nat := 4096

/-- Match the work list of `(pattern, value)` pairs in preorder, trying the commutative choices
depth-first (0 before 1); `k` is called on each complete match and decides (by evaluating the
condition) whether the search stops. `fuel` bounds the items taken on one path. -/
def matchWorkF : Nat → Scope → List (Pat × ID) → MState → (MState → RwM Bool) → RwM Bool
  | 0, _, _, _, _ => throw "pattern too large"
  | fuel + 1, sc, work, st, k => do
  let matchWork := matchWorkF fuel
  match work with
  | [] => k st
  | (p, w) :: rest =>
    match p with
    | .wild => matchWork sc rest st k
    | .bind x => matchWork sc rest { st with binds := st.binds.set! x (.val w) } k
    | .same x =>
      if isUnbound st.binds x then
        matchWork sc rest { st with pending := .same x w :: st.pending } k
      else if st.binds[x]!.beq (.val w) then matchWork sc rest st k
      else return false
    | .op o name ty ai ax arity args commute =>
      let x ← val w
      if x.op != o then return false
      match arity with
      | .exact n => if x.args.size != n then return false
      | .atLeast n => if n ≥ 1 && o.argLen == -1 && x.args.size < n then return false
      | _ => pure ()
      let some st ← field sc st ty (fun _ => pure (.typ x.type)) | return false
      let st := match ty with
        | .bind tx => { st with tySrc := (tx, w) :: st.tySrc }
        | _ => st
      let some st ← field sc st ai (fun _ => liftE (auxIntVal o.auxType x.auxInt)) | return false
      let some st ← field sc st ax (fun _ => do liftE (auxVal (← tables) o.auxType x.aux))
        | return false
      let st := match name with
        | some n => { st with binds := st.binds.set! n (.val w) }
        | none => st
      let pairs := args.zip x.args.toList
      if commute then
        match pairs with
        | (p0, a0) :: (p1, a1) :: more =>
          if ← matchWork sc ((p0, a0) :: (p1, a1) :: more ++ rest) st k then return true
          matchWork sc ((p0, a1) :: (p1, a0) :: more ++ rest) st k
        | _ => throw "commutative pattern with fewer than two arguments"
      else matchWork sc (pairs ++ rest) st k

/-- `matchWorkF` with `matchFuel`. -/
def matchWork (sc : Scope) (work : List (Pat × ID)) (st : MState) (k : MState → RwM Bool) :
    RwM Bool :=
  matchWorkF matchFuel sc work st k

/-- The postponed checks hold. -/
def pendingOk (sc : Scope) (st : MState) : RwM Bool := do
  for p in st.pending.reverse do
    match p with
    | .same x w => if !(st.binds[x]!.beq (.val w)) then return false
    | .eq e actual =>
      if !actual.beq (← eval { sc with binds := st.binds } e) then return false
  return true

/-- The `*types.Type` object of a result node's type expression (#101): `t.PtrTo()` is a fresh
object unless `t`'s pointer type is cached; `x.Type` and a type variable bound from a matched
value are that value's object; anything else (`typ.<name>`, `t.Elem()`, …) is canonical. -/
def typeObjOf (sc : Scope) (e : Expr) : RwM GoFV.Opt.TypeObj := do
  match e with
  | .method x "PtrTo" [] _ =>
    match ← eval sc x with
    | .typ t => return if (← read).ptrCache t then .canonical else .fresh
    | _ => return .canonical
  | .field x "Type" _ =>
    match ← eval sc x with
    | .val w => return .of w
    | _ => return .canonical
  | .var i => return match sc.tySrc.lookup i with
    | some w => .of w
    | none => .canonical
  | _ => return .canonical

/-- Record the type object of value `id` (`PassOut.typeObjs`). -/
def recordTypeObj (id : ID) (o : GoFV.Opt.TypeObj) : RwM Unit :=
  modify fun s => { s with typeObjs := s.typeObjs.push (id, o) }

/-- Build the nodes of a value rule's result (`Result.build`), starting from node `j`, which is
the value `id`; `built` maps node indices to the values made so far. Returns `built`. `fuel`
bounds the depth (`nodes.size` suffices: a result is a tree with shared subtrees). -/
def buildNodeF : Nat → Scope → Array RNode → ID → Pos → Nat → ID → Array (Option ID) →
    RwM (Array (Option ID))
  | 0, _, _, _, _, _, _, _ => throw "result too deep"
  | fuel + 1, sc, nodes, blk, pos, j, id, built => do
  let buildNode := buildNodeF fuel
  let n := nodes[j]!
  if let some e := n.auxInt then
    let ai ← liftE (toAuxInt n.op.auxType (← eval sc e))
    modF fun f => f.modV id fun x => { x with auxInt := ai }
  if let some e := n.aux then
    let a ← toAux (← eval sc e)
    modF fun f => f.modV id fun x => { x with aux := a }
  let mut built := built
  let mut args : Array ID := #[]
  for a in n.args do
    match a with
    | .var x => args := args.push (← liftE (sc.binds[x]!.asVal))
    | .node k =>
      match built[k]! with
      | some c => args := args.push c
      | none =>
        let nk := nodes[k]!
        let e ← match nk.ty with
          | some e => pure e
          | none => throw "result node without a type"
        let t ← liftE (← eval sc e).asTyp
        let c ← newValue blk pos nk.op t
        recordTypeObj c (← typeObjOf sc e)
        built := built.set! k (some c)
        built ← buildNode sc nodes blk pos k c built
        args := args.push c
  modF fun f => f.addArgs id args
  return built

/-- `buildNodeF` with enough fuel. -/
def buildNode (sc : Scope) (nodes : Array RNode) (blk : ID) (pos : Pos) (j : Nat) (id : ID)
    (built : Array (Option ID)) : RwM (Array (Option ID)) :=
  buildNodeF (nodes.size + 1) sc nodes blk pos j id built

/-- Apply the result of a fired value rule to `v`; returns the values of the result's nodes in
node order (`Result.build`; empty otherwise). -/
def applyResult (sc : Scope) (r : Rule) (v : ID) : RwM (Array (Option ID)) := do
  match r.result with
  | .copy e =>
    let w ← liftE (← eval sc e).asVal
    copyOf v w
    return #[]
  | .setOp o =>
    modF fun f => f.modV v fun x => { x with op := o }
    return #[]
  | .build nodes =>
    let nodes := nodes.toArray
    let x ← val v
    let pos := x.pos
    let n0 := nodes[0]!
    let built0 : Array (Option ID) := Array.replicate nodes.size none
    match r.block with
    | none =>
      reset v n0.op
      if let some e := n0.ty then
        let t ← liftE (← eval sc e).asTyp
        modF fun f => f.modV v fun y => { y with type := t }
        recordTypeObj v (← typeObjOf sc e)
      buildNode sc nodes x.block pos 0 v (built0.set! 0 (some v))
    | some be =>
      let .blk blk ← eval sc be | throw "@ placement is not a block"
      let (t, o) ← match n0.ty with
        | some e => pure ((← liftE (← eval sc e).asTyp), (← typeObjOf sc e))
        | none => pure (x.type, GoFV.Opt.TypeObj.of v)
      let top ← newValue blk pos n0.op t
      recordTypeObj top o
      copyOf v top
      buildNode sc nodes blk pos 0 top (built0.set! 0 (some top))

/-- A value rule with its variable types and an all-unbound binding array, computed once. -/
structure CRule where
  rule : Rule
  vtys : Array GoTy
  unbound : Array GVal

def CRule.ofRule (r : Rule) : CRule :=
  { rule := r, vtys := (r.vars.map (·.ty)).toArray, unbound := Array.replicate r.vars.length .nil }

/-- The values `rewriteStructLoad` built at `v` (`StructMake` of field `Load`s at `OffPtr`s),
in the order `RewriteCheck.structLoadOK` reads them: per argument of `v` its `OffPtr` and
itself. -/
def structLoadDefs (f : Func) (v : ID) : Array Value :=
  match f.value? v with
  | some x => x.args.foldl (init := #[]) fun acc a =>
      match f.value? a with
      | some l => match l.args[0]?.bind f.value? with
        | some o => (acc.push o).push l
        | none => acc.push l
      | none => acc
  | none => #[]

/-- The values `rewriteStructStore` built for the `Store` `v` (now `Copy` of the last field
`Store`; `f0`: the function before the rule), in the order `RewriteCheck.ssEvent?` reads them:
per field, first to last, its `OffPtr` and its `Store`. The chain is walked back from `v`'s
argument through the `Store`s `f0` does not have (at most `f.valueTab.size` steps). -/
def structStoreDefs (f0 f : Func) (v : ID) : Array Value :=
  match (f.value? v).bind (·.args[0]?) with
  | some m0 => Id.run do
    let mut m := m0
    let mut acc : List Value := []
    for _ in [0:f.valueTab.size] do
      match f.value? m with
      | some s =>
        if s.op == .Store && (f0.value? m).isNone then
          match s.args[0]?.bind f.value? with
          | some o => acc := o :: s :: acc; m := s.args[2]!
          | none => break
        else break
      | none => break
    return acc.toArray
  | none => #[]

/-- Try rule `cr` (index `idx` in its table row) on `v`; true if it fired. `slDefs`: log the
values a struct-load expansion built (`structLoadDefs`) after `v`; `ssDefs`: those of a
struct-store split (`structStoreDefs`). -/
def tryRule (v : ID) (cr : CRule) (idx : Nat) (slDefs : Bool := false) (ssDefs : Bool := false) :
    RwM Bool := do
  let r := cr.rule
  let x ← val v
  let sc : Scope := { v := some v, b := x.block, binds := cr.unbound, vtys := cr.vtys }
  let st : MState := { binds := sc.binds, pending := [] }
  matchWork sc [(r.pat, v)] st fun st => do
    let sc := { sc with binds := st.binds, tySrc := st.tySrc }
    if !(← pendingOk sc st) then return false
    if let some c := r.cond then
      if !(← liftE (← eval sc c).asBool) then return false
    -- the function before a struct-store split (its fresh values are those it lacks); kept
    -- only then, as holding it makes the rule's edits copy the tables
    let f0? ← if ssDefs && (← get).log.isSome then some <$> getF else pure none
    let built ← applyResult sc r v
    modify fun s => { s with fired := s.fired + 1 }
    if (← get).log.isSome then
      let f ← getF
      let defs := (#[some v] ++ built).filterMap fun id => id.bind f.value?
      let defs := if slDefs then defs ++ structLoadDefs f v else defs
      let defs := match f0? with
        | some f0 => defs ++ structStoreDefs f0 f v
        | none => defs
      logEv fun _ => .rule v idx st.binds defs
    return true

/-- Per-op rule table of a rule set, indexed by `Op.ctorIdx`; `nilChecks`/`loads`: the rule
set's `nilChecks`/`loads`, tried on a `NilCheck`/`Load` after its row (their index continues
the row's); `structLoads`: the rule set's `structLoads`, tried on a `Load` after `loads`;
`structStores`: the rule set's `structStores`, tried on a `Store` after its row, then `loads`
(dropped identity writes, also tried on a `Zero` after its row). -/
structure Table where
  values : Array (Array CRule)
  blocks : Array (Array BlockRule)
  nilChecks : Array CRule := #[]
  loads : Array CRule := #[]
  structLoads : Array CRule := #[]
  structStores : Array CRule := #[]

def Table.ofRuleSet (s : RuleSet) : Table := Id.run do
  let mut values : Array (Array CRule) := Array.replicate (Op.all.size + 1) #[]
  for (o, rs) in s.values do
    values := values.set! o.ctorIdx (rs.toArray.map CRule.ofRule)
  let mut blocks : Array (Array BlockRule) := Array.replicate (BlockKind.all.size + 1) #[]
  for (k, rs) in s.blocks do
    blocks := blocks.set! k.ctorIdx rs.toArray
  return { values, blocks, nilChecks := (s.nilChecks.map CRule.ofRule).toArray,
           loads := (s.loads.map CRule.ofRule).toArray,
           structLoads := (s.structLoads.map CRule.ofRule).toArray,
           structStores := (s.structStores.map CRule.ofRule).toArray }

/-- `rewriteValue<file>(v)`. -/
def rewriteValue (t : Table) (v : ID) : RwM Bool := do
  let o := (← val v).op
  let rs := t.values[o.ctorIdx]!
  for h : i in [0:rs.size] do
    if ← tryRule v rs[i] i then return true
  if o == .NilCheck then
    let ns := t.nilChecks
    for h : i in [0:ns.size] do
      if ← tryRule v ns[i] (rs.size + i) then return true
  if o == .Load then
    let ls := t.loads
    for h : i in [0:ls.size] do
      if ← tryRule v ls[i] (rs.size + i) then return true
    let ss := t.structLoads
    for h : i in [0:ss.size] do
      if ← tryRule v ss[i] (rs.size + ls.size + i) (slDefs := true) then return true
  if o == .Store then
    let ss := t.structStores
    for h : i in [0:ss.size] do
      if ← tryRule v ss[i] (rs.size + i) (ssDefs := true) then return true
    let ls := t.loads
    for h : i in [0:ls.size] do
      if ← tryRule v ls[i] (rs.size + ss.size + i) then return true
  if o == .Zero then
    let ls := t.loads
    for h : i in [0:ls.size] do
      if ← tryRule v ls[i] (rs.size + i) then return true
  return false

/-! ## Block rules -/

/-- The value at `path` below `root` (argument indices). -/
def valueAt (root : ID) : List Nat → RwM ID
  | [] => pure root
  | i :: is => do
    match (← val root).args[i]? with
    | some a => valueAt a is
    | none => throw "bad control position path"

/-- Build a new block control (`NewControl.build`): nodes created in `b`, node 0 is the
control, no sharing; `fuel` bounds the depth. -/
def buildCtrlNodeF : Nat → Scope → Array RNode → ID → Pos → Nat → RwM ID
  | 0, _, _, _, _, _ => throw "control result too deep"
  | fuel + 1, sc, nodes, b, pos, j => do
  let buildCtrlNode := buildCtrlNodeF fuel
  let n := nodes[j]!
  let e ← match n.ty with
    | some e => pure e
    | none => throw "control node without a type"
  let t ← liftE (← eval sc e).asTyp
  let id ← newValue b pos n.op t
  recordTypeObj id (← typeObjOf sc e)
  if let some e := n.auxInt then
    let ai ← liftE (toAuxInt n.op.auxType (← eval sc e))
    modF fun f => f.modV id fun x => { x with auxInt := ai }
  if let some e := n.aux then
    let a ← toAux (← eval sc e)
    modF fun f => f.modV id fun x => { x with aux := a }
  let mut args : Array ID := #[]
  for a in n.args do
    match a with
    | .var x => args := args.push (← liftE (sc.binds[x]!.asVal))
    | .node k => args := args.push (← buildCtrlNode sc nodes b pos k)
  modF fun f => f.addArgs id args
  return id

/-- `buildCtrlNodeF` with enough fuel. -/
def buildCtrlNode (sc : Scope) (nodes : Array RNode) (b : ID) (pos : Pos) (j : Nat) : RwM ID :=
  buildCtrlNodeF (nodes.size + 1) sc nodes b pos j

/-- Apply a fired block rule to `b`. -/
def applyBlockResult (sc : Scope) (r : BlockRule) (b : ID) : RwM Unit := do
  let blk0 ← blk b
  let mut ctrls : Array ID := #[]
  for (nc, cp) in r.newControls do
    match nc with
    | .var x => ctrls := ctrls.push (← liftE (sc.binds[x]!.asVal))
    | .build nodes =>
      let pos ← match cp with
        | .block => pure blk0.pos
        | .control i path => do pure (← val (← valueAt blk0.controls[i]! path)).pos
      ctrls := ctrls.push (← buildCtrlNode sc nodes.toArray b pos 0)
  match ctrls.size with
  | 0 => modF fun f => f.resetBlock b r.newKind
  | 1 => modF fun f => f.resetWithControl b r.newKind ctrls[0]!
  | 2 => modF fun f => f.resetWithControl2 b r.newKind ctrls[0]! ctrls[1]!
  | _ => throw "more than two controls"
  if let some e := r.newAuxInt then
    -- no block rule of the four files sets an AuxInt; generic block aux ints are plain int64
    let ai ← liftE (toAuxInt .Int64 (← eval sc e))
    modF fun f => f.modB b fun x => { x with auxInt := ai }
  if let some e := r.newAux then
    let a ← toAux (← eval sc e)
    modF fun f => f.modB b fun x => { x with aux := a }
  if r.swapSuccs then modF fun f => f.swapSuccessors b

/-- Try block rule `r` (index `idx` in its table row) on `b`. -/
def tryBlockRule (b : ID) (r : BlockRule) (idx : Nat) : RwM Bool := do
  let blk0 ← blk b
  if blk0.controls.size < r.controls.length then return false
  let sc : Scope := { v := none, b, binds := Array.replicate r.vars.length .nil,
                      vtys := (r.vars.map (·.ty)).toArray }
  let st : MState := { binds := sc.binds, pending := [] }
  let work := r.controls.zip blk0.controls.toList
  matchWork sc work st fun st => do
    let sc := { sc with binds := st.binds }
    let some st ← field sc st r.auxInt (fun _ => pure (.int blk0.auxInt.toInt)) | return false
    let some st ← field sc st r.aux (fun _ => pure (.aux blk0.aux)) | return false
    let sc := { sc with binds := st.binds }
    if !(← pendingOk sc st) then return false
    if let some c := r.cond then
      if !(← liftE (← eval sc c).asBool) then return false
    applyBlockResult sc r b
    modify fun s => { s with fired := s.fired + 1 }
    if (← get).log.isSome then
      let ctrls := (← blk b).controls
      logEv fun _ => .blockRule b idx ctrls
    return true

/-- `rewriteBlock<file>(b)`. -/
def rewriteBlock (t : Table) (b : ID) : RwM Bool := do
  let k := (← blk b).kind
  let rs := t.blocks[k.ctorIdx]!
  for h : i in [0:rs.size] do
    if ← tryBlockRule b rs[i] i then return true
  return false

end Interp

end GoFV.Rules

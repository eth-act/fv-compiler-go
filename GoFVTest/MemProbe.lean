import GoFV.SSA.Parse
import GoFV.SSA.Check
import GoFV.SSA.DomCert
import GoFV.Opt.NilCheck
import GoFV.Opt.DeadStore
import GoFV.Opt.ElimDeadAutos
import GoFV.Opt.CSE

/-!
# `mem-probe`: what the nilcheckelim / dse / dead auto elim proofs have to cover

Runs each pass on the input of every instance of it in the given export files and classifies
its changes by the argument a refinement proof needs:

* nilcheckelim: a `NilCheck` becoming `Copy nc` — `nc` a nil check of the same pointer in a
  strictly dominating block (`dom`), in the same block before it in the source schedule
  (`same-before`) or after it (`same-after`); `nc` the pointer itself, which points into an
  allocation by its op (`seed-alloc`: `Addr`/`LocalAddr`, through `OffPtr`/`AddPtr`) or only by
  Go's assumptions (`seed-<op>`), a phi (`phi`), or an `If (IsNonNil p)` edge (`edge`). An
  `IsNonNil` becoming `ConstBool` likewise. `roots`: the target's schedule runs the source's
  roots minus the removed checks in the same order.
* dse: each eliminated store, by `cover`: the bytes it writes are overwritten by later kept
  stores to the same base before any read (forward walk over the unique memory users), and by
  the base's op.
* dead auto elim: changed functions, those with calls or integer→pointer conversions.
-/

open GoFV.SSA GoFV.Opt

namespace GoFVTest.MemProbe

def bump (m : Std.HashMap String Nat) (k : String) (n : Nat := 1) : Std.HashMap String Nat :=
  m.insert k (m.getD k 0 + n)

def show' (m : Std.HashMap String Nat) : String :=
  toString ((m.toList.mergeSort fun a b => a.2 ≥ b.2).map fun (k, n) => s!"{k}:{n}")

/-! ## nilcheckelim -/

/-- `x` points into an allocation by its op. -/
def allocPtr (f : Func) : Nat → ID → Bool
  | 0, _ => false
  | n + 1, x =>
    match f.value? x with
    | some v =>
      match v.op with
      | .Addr | .LocalAddr => true
      | .OffPtr | .AddPtr => match v.args[0]? with
        | some a => allocPtr f n a
        | none => false
      | _ => false
    | none => false

def pos (o : Array ID) (x : ID) : Option Nat := o.findIdx? (· == x)

/-- Source schedule of every block. -/
def scheds (f : Func) : Std.HashMap ID (Array ID) := Id.run do
  let mut m := {}
  for b in f.blocks do
    if let some fb := f.block? b then
      if let some o := Sem.schedule f fb then m := m.insert b o
  return m

/-- Classify the justification of `ptr` being non-nil for value `x` (in block `bx`) by the
nil check `nc` or the pointer itself. -/
def why (c : DomCert.Cert) (f : Func) (os : Std.HashMap ID (Array ID)) (x ptr nc : ID) : String :=
  let bx := (f.getV x).block
  if nc == ptr then
    let p := f.getV ptr
    if allocPtr f 8 ptr then "seed-alloc"
    else if NilCheck.nonNilOp p.op then s!"seed-{p.op.name}"
    else if p.op == .Phi then "phi"
    else "edge"
  else
    let n := f.getV nc
    if n.op != .NilCheck || n.args[0]? != some ptr then s!"other-{n.op.name}"
    else if n.block != bx then
      if c.anc n.block bx then "dom" else "notdom"
    else
      match os.get? bx with
      | none => "nosched"
      | some o =>
        match pos o nc, pos o x with
        | some i, some j => if i < j then "same-before" else "same-after"
        | _, _ => "nopos"

/-- For an `IsNonNil ptr` turned constant: the best justification among the surviving checks. -/
def whyIsNonNil (c : DomCert.Cert) (f g : Func) (os : Std.HashMap ID (Array ID)) (x ptr : ID) :
    String := Id.run do
  if allocPtr f 8 ptr then return "seed-alloc"
  let mut best := "none"
  for y in List.range g.valueTab.size do
    if let (some gy, some fy) := (g.value? y, f.value? y) then
      if gy.op == .NilCheck && fy.op == .NilCheck && fy.args[0]? == some ptr then
        let w := why c f os x ptr y
        if w == "dom" || w == "same-before" then return w
        if best == "none" then best := w
  if best == "none" then
    let p := f.getV ptr
    if NilCheck.nonNilOp p.op then return s!"seed-{p.op.name}"
    if p.op == .Phi then return "phi"
    return "edge"
  return best

def rootG (g : Func) (x : ID) : Bool := CSE.rootNode g x

/-- The target's roots, in order, are the source's minus the removed ones, per block. -/
def rootsOK (f g : Func) : Bool := Id.run do
  for b in f.blocks do
    match f.block? b, g.block? b with
    | some fb, some gb =>
      match Sem.schedule f fb, Sem.schedule g gb with
      | some oS, some oT =>
        if oT.filter (rootG g) != oS.filter (rootG g) then return false
      | _, _ => return false
    | _, _ => return false
  return true

/-! ## dse -/

/-- Strip `OffPtr`s: base and offset. -/
def offBase (f : Func) : Nat → ID → Int → ID × Int
  | 0, p, o => (p, o)
  | n + 1, p, o =>
    let x := f.getV p
    if x.op == .OffPtr then offBase f n x.args[0]! (o + x.auxInt.toInt) else (p, o)

/-- The key of a base: `LocalAddr`s by name, others by ID. -/
def baseKey (f : Func) (p : ID) : String :=
  let x := f.getV p
  if x.op == .LocalAddr then s!"L{x.aux}" else if x.op == .Addr then s!"A{x.aux}" else s!"v{p}"

/-- Byte range written by store `x` (`Store` by its aux type's shape size). -/
def range? (tabs : Tables) (f : Func) (x : Value) : Option (String × String × Int × Int) :=
  let ptr := x.args[0]!
  let (b, o) := offBase f 64 ptr 0
  let sz : Int := match x.op with
    | .Store => (Sem.auxTy tabs x.aux).size
    | _ => x.auxInt.toInt
  some (baseKey f b, (f.getV b).op.name, o, o + sz)

/-- Users of every value (args of listed values; controls as `none`). -/
def users (f : Func) : Array (List (Option ID)) := Id.run do
  let mut u := Array.replicate f.valueTab.size []
  for b in f.blocks do
    let blk := f.getB b
    for v in blk.values do
      for a in (f.getV v).args do
        if a < u.size then u := u.modify a (some v :: ·)
    for c in blk.controls do
      if c < u.size then u := u.modify c (none :: ·)
  return u

/-- `[lo, hi)` is covered by the union of `rs`. -/
def covered (rs : List (Int × Int)) (lo hi : Int) : Bool := Id.run do
  let mut cur := lo
  for _ in [0:rs.length + 1] do
    if cur ≥ hi then return true
    match rs.find? (fun (a, b) => a ≤ cur && cur < b) with
    | some (_, b) => cur := b
    | none => return false
  return cur ≥ hi

/-- Forward cover check of an eliminated store `v` of `f` (`g`: the output). -/
def cover (tabs : Tables) (f g : Func) (us : Array (List (Option ID))) (v : ID) : String := Id.run do
  let x := f.getV v
  let some (key, bop, lo, hi) := range? tabs f x | return "norange"
  if bop != "LocalAddr" && bop != "Addr" then return s!"base-{bop}"
  let mut w := v
  let mut rs : List (Int × Int) := []
  for _ in [0:f.valueTab.size] do
    let uw := us.getD w []
    match uw with
    | [some u] =>
      let y := f.getV u
      if y.block != x.block then return "user-other-block"
      if y.args.back? != some w then return s!"user-arg-{y.op.name}"
      if (y.args.pop).contains w then return "user-twice"
      match y.op with
      | .Store | .Zero | .Move | .VarDef =>
        if y.op == .Move then
          let s := f.getV y.args[1]!
          let ro := if s.op == .Addr then (GoFV.Rules.Sym.symIsRO tabs s.aux).toOption.getD false
            else false
          if !ro then return "move-reads"
          if bop == "Addr" && s.aux == x.aux then return "move-same-sym"
        let kept := (g.getV u).op == y.op
        if kept && y.op != .VarDef then
          if let some (k2, _, lo2, hi2) := range? tabs f y then
            if k2 == key then rs := (lo2, hi2) :: rs
        if covered rs lo hi then return "ok"
        w := u
      | op => return s!"user-{op.name}"
    | [] => return "no-users"
    | [none] => return "control"
    | _ => return s!"users-{uw.length}"
  return "fuel"

/-! ## driver -/

def main (args : List String) : IO UInt32 := do
  let mut files := #[]
  for a in args do
    let p : System.FilePath := a
    if ← p.isDir then
      files := files ++ ((← p.walkDir).filter (·.extension == some "ssa"))
    else files := files.push p
  let mut nInst := 0
  let mut nChanged := 0
  let mut nFrag := 0
  let mut nRootsBad := 0
  let mut nErr := 0
  let mut nck : Std.HashMap String Nat := {}
  let mut isnn : Std.HashMap String Nat := {}
  let mut fnWorst : Std.HashMap String Nat := {}
  let mut dInst := 0
  let mut dChanged := 0
  let mut dFrag := 0
  let mut dWhy : Std.HashMap String Nat := {}
  let mut dFn : Std.HashMap String Nat := {}
  let mut aInst := 0
  let mut aChanged := 0
  let mut aCalls := 0
  let mut aConv := 0
  let mut aKinds : Std.HashMap String Nat := {}
  for path in files do
    let data ← IO.FS.readBinFile path
    let .ok e := parseExport data | continue
    let typs := (e.sections[0]?.bind (·.typs)).getD #[]
    let mut tables : Tables := {}
    for h : k in [0:e.sections.size] do
      let s := e.sections[k]
      let prev := tables
      tables := tables.addAll s.defs
      if k == 0 then continue
      let pass := s.pass.toStringLossy
      let penv : PassEnv :=
        { passName := pass, pkg := e.pkg, funcName := e.name, abi := e.abi
          nosplit := e.nosplit, pgohot := e.pgohot, config := e.config, typs
          typeOrder := TypeOrder.ofGroups e.typeOrder e.typeCmp, tables := prev
          frontend := e.frontendTables }
      let f := e.sections[k-1]!.func
      if pass == "nilcheckelim" then
        nInst := nInst + 1
        match nilcheckelim penv f with
        | .error _ => nErr := nErr + 1
        | .ok g =>
          let c := DomCert.make f
          let os := scheds f
          let mut kinds : List String := []
          for x in List.range f.valueTab.size do
            if let (some fx, some gx) := (f.value? x, g.value? x) then
              if fx.op == .NilCheck && gx.op == .Copy then
                let w := why c f os x fx.args[0]! gx.args[0]!
                nck := bump nck w
                if !kinds.contains w then kinds := w :: kinds
              else if fx.op == .IsNonNil && gx.op == .ConstBool then
                let w := "isnn-" ++ whyIsNonNil c f g os x fx.args[0]!
                isnn := bump isnn w
                if !kinds.contains w then kinds := w :: kinds
          if !kinds.isEmpty then
            nChanged := nChanged + 1
            let rok := rootsOK f g
            if !rok then nRootsBad := nRootsBad + 1
            let bad := kinds.filter fun w =>
              !(w == "dom" || w == "same-before" || w == "seed-alloc" || w == "isnn-dom" ||
                w == "isnn-seed-alloc")
            let bad := if rok then bad else "roots" :: bad
            if bad.isEmpty then nFrag := nFrag + 1
            else fnWorst := bump fnWorst (toString (bad.mergeSort (· ≤ ·)))
      else if pass == "dse" then
        dInst := dInst + 1
        let some mem := penv.typ? "Mem" | continue
        match dse prev mem f with
        | .error _ => nErr := nErr + 1
        | .ok g =>
          let us := users f
          let mut ws : List String := []
          for x in List.range f.valueTab.size do
            if let (some fx, some gx) := (f.value? x, g.value? x) then
              if fx.op != gx.op && gx.op == .Copy then
                let w := cover prev f g us x
                dWhy := bump dWhy w
                if !ws.contains w then ws := w :: ws
          if !ws.isEmpty then
            dChanged := dChanged + 1
            let bad := ws.filter (· != "ok")
            let rok := rootsOK f g
            let bad := if rok then bad else "roots" :: bad
            if bad.isEmpty then dFrag := dFrag + 1
            else dFn := bump dFn (toString (bad.mergeSort (· ≤ ·)))
      else if pass == "dead auto elim" then
        aInst := aInst + 1
        let some mem := penv.typ? "Mem" | continue
        let some flags := penv.typ? "Flags" | continue
        match elimDeadAutosGeneric prev mem flags (penv.abi == 1) f with
        | .error _ => nErr := nErr + 1
        | .ok g =>
          let mut any := false
          for x in List.range f.valueTab.size do
            if let (some fx, some gx) := (f.value? x, g.value? x) then
              if fx.op != gx.op then
                any := true
                aKinds := bump aKinds fx.op.name
          if any then
            aChanged := aChanged + 1
            let ops := (List.range f.valueTab.size).filterMap fun x => (f.value? x).map (·.op)
            if ops.any (fun o => o == .StaticLECall || o == .StaticCall || o == .ClosureLECall ||
                o == .InterLECall || o == .TailLECall) then aCalls := aCalls + 1
            if ops.any (· == .Convert) then aConv := aConv + 1
  IO.println s!"nilcheckelim: inputs {nInst}, errors {nErr}, changed {nChanged}, in fragment {nFrag}, roots reordered {nRootsBad}"
  IO.println s!"  NilCheck→Copy by justification: {show' nck}"
  IO.println s!"  IsNonNil→ConstBool by justification: {show' isnn}"
  IO.println s!"  changed functions outside the fragment, by the kinds they need: {show' fnWorst}"
  IO.println s!"dse: inputs {dInst}, changed {dChanged}, in fragment {dFrag}"
  IO.println s!"  eliminated stores by cover check: {show' dWhy}"
  IO.println s!"  changed functions outside the fragment: {show' dFn}"
  IO.println s!"dead auto elim: inputs {aInst}, changed {aChanged}, with calls {aCalls}, with Convert {aConv}"
  IO.println s!"  eliminated values by op: {show' aKinds}"
  return 0

end GoFVTest.MemProbe

def main (args : List String) : IO UInt32 := GoFVTest.MemProbe.main args

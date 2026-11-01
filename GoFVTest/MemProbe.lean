import GoFV.SSA.Parse
import GoFV.SSA.Check
import GoFV.SSA.DomCert
import GoFV.Opt.NilCheckRel
import GoFV.Opt.DeadStoreCheck
import GoFV.Opt.DeadAutosCheck
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
* dse: changed functions, those the checker `DSE.drel` accepts (`dseFrag`), and for the others
  the conditions it rejects (`dseWhy`).
* dead auto elim: changed functions, those with calls or integer→pointer conversions. With
  `--dae-candidates`, every accepted change of a function without calls (non-vacuity witness
  candidates: file, section, values, blocks).
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

/-- The op at the root of an `OffPtr`/`AddPtr` chain. -/
def chainRoot (f : Func) : Nat → ID → String
  | 0, _ => "deep"
  | n + 1, x =>
    match f.value? x with
    | some v =>
      match v.op with
      | .OffPtr | .AddPtr => match v.args[0]? with
        | some a => chainRoot f n a
        | none => "?"
      | op => op.name
    | none => "?"

def rootG (g : Func) (x : ID) : Bool := CSE.rootNode g x

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
    else if NilCheck.nonNilOp p.op then s!"seed-{p.op.name}-{chainRoot f 8 ptr}"
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
        | some i, some j =>
          if i < j then "same-before"
          else
            let rs := o.filter (rootG f)
            let adj := match pos rs x, pos rs nc with
              | some a, some b => b == a + 1
              | _, _ => false
            let sameMem := (f.getV x).args[1]? == (f.getV nc).args[1]?
            s!"same-after-{if adj then "adj" else "far"}-{if sameMem then "mem" else "nomem"}"
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

/-- Why `DSE.drel` rejects `g` (the first failing condition per value/block; `[]` if it
accepts). -/
def dseWhy (tabs : Tables) (f g : Func) : List String := Id.run do
  let A := DSE.pendArr tabs f g
  let P := fun x => A.getD x []
  let mut ws : List String := []
  let add (ws : List String) (w : String) := if ws.contains w then ws else w :: ws
  if DomCert.cfgView g != DomCert.cfgView f || g.ownAux != f.ownAux ||
      g.valueTab.size != f.valueTab.size then
    ws := add ws "shape"
  for b in f.blocks do
    if !DSE.blockOK f g P b then
      ws := add ws (if (f.block? b).any (·.controls.any (fun c => !(P c).isEmpty)) then "control" else "block")
    if !DSE.schedOK f g b then ws := add ws "roots"
  for x in List.range f.valueTab.size do
    if !DSE.valueOK f g x then ws := add ws "value"
    let some fv := f.value? x | continue
    if DSE.pendStep tabs f g P x != some (P x) then
      match DSE.pendStep tabs f g P x with
      | none =>
        if (g.value? x).any (DSE.elimV fv ·) then
          let b := (CSE.baseOff tabs f 64 (fv.args[0]?.getD 0) 0)
          ws := add ws (match DSE.ptrAlloc tabs f (fv.args[0]?.getD 0) with
            | none => s!"base-{(f.getV b.1).op.name}"
            | some _ => "offset")
        else ws := add ws s!"move-src-{(f.getV (fv.args[1]?.getD 0)).op.name}"
      | some _ => ws := add ws "pend"
    if !DSE.usesOK f P x then
      let bad := fv.args.filter fun a => !(P a).isEmpty
      let other := bad.any fun a => (f.value? a).map (·.block) != some fv.block
      ws := add ws (if other then "user-other-block" else s!"user-{fv.op.name}")
  return ws

/-! ## dead auto elim -/

mutual
/-- A shape that may hold a memory. -/
partial def tyMem : Sem.Ty → Bool
  | .mem => true
  | .tuple ts => tysMem ts
  | .agg fs _ => tysMem (fs.map (·.2))
  | _ => false
partial def tysMem : List Sem.Ty → Bool
  | [] => false
  | t :: ts => tyMem t || tysMem ts
end

mutual
/-- A shape that may hold a pointer into a frame block. -/
partial def tyPtr : Sem.Ty → Bool
  | .ptr _ | .blob _ => true
  | .tuple ts => tysPtr ts
  | .agg fs _ => tysPtr (fs.map (·.2))
  | _ => false
partial def tysPtr : List Sem.Ty → Bool
  | [] => false
  | t :: ts => tyPtr t || tysPtr ts
end

/-- Why `DAE.arel` rejects `g` (each failing condition; `[]` if it accepts). -/
def daeWhy (tabs : Tables) (f g : Func) : List String := Id.run do
  let A := DAE.tagArr tabs f
  let T := fun x => A.getD x none
  let E := DAE.names f g T
  let mut ws : List String := []
  let add (ws : List String) (w : String) := if ws.contains w then ws else w :: ws
  if DomCert.cfgView g != DomCert.cfgView f || g.ownAux != f.ownAux ||
      g.valueTab.size != f.valueTab.size then ws := add ws "shape"
  for n in E do
    if !DAE.unforgeable tabs n then
      ws := add ws (match tabs.aux? n with
        | some { kind := .name _ _ _ _ _ fl _, .. } =>
          if fl.opendeferslot then "opendeferslot" else "forgeable"
        | _ => "not-a-name")
  for b in f.blocks do
    if !DAE.blockOK f g T E b then ws := add ws "control"
    if !DSE.schedOK f g b then ws := add ws "roots"
  for x in List.range f.valueTab.size do
    let some fv := f.value? x | continue
    if !DAE.valueOK f g T E x then ws := add ws "value"
    if DAE.tagStep tabs T fv != T x then ws := add ws "tag"
    if !DAE.usesOK f g T E x then
      let el := (g.value? x).any (DAE.elimV fv ·)
      ws := add ws s!"use-{fv.op.name}{if el then "-elim" else ""}"
    if !DAE.keptOK tabs f g x then ws := add ws s!"op-{fv.op.name}"
  return ws

/-- The name an eliminated value of dead auto elim writes: `VarDef`'s aux, or the `LocalAddr`
under the destination's `OffPtr`s. -/
def elimName (f : Func) (v : Value) : Option AuxRef := Id.run do
  if v.op == .VarDef then return v.aux
  let mut p := v.args[0]?.getD 0
  for _ in [0:64] do
    let x := f.getV p
    if x.op == .OffPtr then p := x.args[0]?.getD 0
    else if x.op == .LocalAddr then return x.aux
    else return none
  return none

/-! ## driver -/

def main (args : List String) : IO UInt32 := do
  let mut files := #[]
  let cands := args.contains "--dae-candidates"
  for a in args.filter (· != "--dae-candidates") do
    let p : System.FilePath := a
    if ← p.isDir then
      files := files ++ ((← p.walkDir).filter (·.extension == some "ssa"))
    else files := files.push p
  let mut nInst := 0
  let mut nChanged := 0
  let mut nFrag := 0
  let mut nAcc := 0
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
  let mut aNames : Std.HashMap String Nat := {}
  let mut aFnNoAddr := 0
  let mut aAcc := 0
  let mut aMemOps : Std.HashMap String Nat := {}
  let mut aPtrOps : Std.HashMap String Nat := {}
  let mut aMemRes : Std.HashMap String Nat := {}
  let mut aWhy : Std.HashMap String Nat := {}
  let mut aFnNoAddrNoCall := 0
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
            if NilCheck.nrel false prev f g then
              nAcc := nAcc + 1
              pure ()
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
          let mut n := 0
          for x in List.range f.valueTab.size do
            if let (some fx, some gx) := (f.value? x, g.value? x) then
              if fx.op != gx.op && gx.op == .Copy then n := n + 1
          if n > 0 then
            dChanged := dChanged + 1
            dWhy := bump dWhy "eliminated" n
            if DSE.drel prev f g then dFrag := dFrag + 1
            else
              let ws := dseWhy prev f g
              for w in ws do dWhy := bump dWhy w
              dFn := bump dFn (toString (ws.mergeSort (· ≤ ·)))
      else if pass == "dead auto elim" then
        aInst := aInst + 1
        let some mem := penv.typ? "Mem" | continue
        let some flags := penv.typ? "Flags" | continue
        match elimDeadAutosGeneric prev mem flags (penv.abi == 1) f with
        | .error _ => nErr := nErr + 1
        | .ok g =>
          let mut any := false
          let mut names : List AuxRef := []
          for x in List.range f.valueTab.size do
            if let (some fx, some gx) := (f.value? x, g.value? x) then
              if fx.op != gx.op then
                any := true
                aKinds := bump aKinds fx.op.name
                if let some n := elimName f fx then
                  if !names.contains n then names := n :: names
          if any then
            aChanged := aChanged + 1
            if DAE.arel prev f g then
              aAcc := aAcc + 1
              let ty := fun (x : ID) => prev.ty ((f.value? x).map (·.type) |>.getD 0)
              for x in List.range f.valueTab.size do
                if let some fx := f.value? x then
                  if fx.args.any (fun a => tyMem (ty a)) then aMemOps := bump aMemOps fx.op.name
                  if tyPtr (ty x) then aPtrOps := bump aPtrOps fx.op.name
                  if tyMem (ty x) then aMemRes := bump aMemRes fx.op.name
            else
              let ws := daeWhy prev f g
              aWhy := bump aWhy (toString (ws.mergeSort (· ≤ ·)))
            let ops := (List.range f.valueTab.size).filterMap fun x => (f.value? x).map (·.op)
            let calls := ops.any (fun o => o == .StaticLECall || o == .StaticCall ||
              o == .ClosureLECall || o == .InterLECall || o == .TailLECall)
            if calls then aCalls := aCalls + 1
            if cands && !calls && DAE.arel prev f g then
              IO.println s!"dae candidate: {path} section {k} values {f.valueTab.size} blocks {f.blocks.size}"

            if ops.any (· == .Convert) then aConv := aConv + 1
            let mut addr := false
            for n in names do
              match prev.aux? n with
              | some { kind := .name _ cls _ _ esc fl _, .. } =>
                addr := addr || (fl.addrtaken && !fl.autotmp)
                let atk := if fl.addrtaken then "-addrtaken" else ""
                let tmp := if fl.autotmp then "-autotmp" else ""
                aNames := bump aNames s!"{cls.name}{atk}{tmp}-esc{esc}"
              | _ => aNames := bump aNames "unknown"
            if !addr then
              aFnNoAddr := aFnNoAddr + 1
              if !calls then aFnNoAddrNoCall := aFnNoAddrNoCall + 1
  IO.println s!"nilcheckelim: inputs {nInst}, errors {nErr}, changed {nChanged}, prototype fragment {nFrag}, checker accepts {nAcc}, roots reordered {nRootsBad}"
  IO.println s!"  NilCheck→Copy by justification: {show' nck}"
  IO.println s!"  IsNonNil→ConstBool by justification: {show' isnn}"
  IO.println s!"  changed functions outside the fragment, by the kinds they need: {show' fnWorst}"
  IO.println s!"dse: inputs {dInst}, changed {dChanged}, in fragment {dFrag}"
  IO.println s!"  eliminated stores, and rejected functions by reason: {show' dWhy}"
  IO.println s!"  changed functions outside the fragment, by their reasons: {show' dFn}"
  IO.println s!"dead auto elim: inputs {aInst}, changed {aChanged}, checker accepts {aAcc}, with calls {aCalls}, with Convert {aConv}"
  IO.println s!"  changed functions outside the fragment, by their reasons: {show' aWhy}"
  IO.println s!"  accepted: ops with a memory-shaped argument: {show' aMemOps}"
  IO.println s!"  accepted: ops with a pointer-capable result: {show' aPtrOps}"
  IO.println s!"  accepted: ops with a memory-shaped result: {show' aMemRes}"
  IO.println s!"  eliminated values by op: {show' aKinds}"
  IO.println s!"  eliminated names by class/flags: {show' aNames}"
  IO.println s!"  changed functions eliminating no user addrtaken name (addrtaken, not autotmp): {aFnNoAddr}, of which without calls: {aFnNoAddrNoCall}"
  return 0

end GoFVTest.MemProbe

def main (args : List String) : IO UInt32 := GoFVTest.MemProbe.main args

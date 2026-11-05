import Lean

/-!
# `axioms-audit`: the axioms gate (`scripts/axioms-audit.sh`, docs/GATE.md)

A compiled program, not a `#eval` in a generated file: it imports the audited modules with
`importModules` and never calls `enableInitializersExecution`, so no `initialize` code of an
audited module runs while it decides (a `#eval` file runs every imported initializer, which could
print a fake result or exit early). Every decision is made here, on `Name`s; the exit code is the
verdict and the shell script only lists the modules.

usage: `lake env .lake/build/bin/axioms-audit ALLOWLIST LIB ROOTS`, where `LIB` is a
comma-separated list of the modules imported together (the GoFV library and the `GoFVTest`
modules that do not define `main`) and `ROOTS` the `GoFVTest` modules that define `main`
(executable roots, which cannot be imported together, nor imported again next to `LIB`: an
`.olean` mapped twice is copied onto the heap). A root's `.olean` is read on its own
(`readModuleData`), and its constants are audited against the `LIB` environment.

Audited: every constant declared in those modules, of every kind (theorems, definitions including
`partial`/`unsafe` ones, opaques, axioms, instances), by the traversal of `Lean.collectAxioms`
(what `#print axioms` prints), `axiomsOf`. Allowed axioms: `propext`, `Classical.choice`,
`Quot.sound`, and the names in `ALLOWLIST`, each of which must be a
`…._native.(native_decide|bv_decide).ax_…` axiom declared in a `LIB` module whose type is
`b = true` (for `native_decide`: `decide p = true`); `sorryAx` and `Lean.trustCompiler` are never
allowed. A dependency that cannot be found is an error. Exit 0 iff there is no violation and no
error.

The shape check does not prove an entry was generated: Lean 4.34 records nothing that tells a
`native_decide` axiom from a hand-written `axiom ….native_decide.ax_1 : decide p = true`, and the
computation cannot be replayed (it is native because the kernel cannot evaluate it). The allowlist
is therefore the trust boundary: `scripts/axioms-audit.sh` prints every allowlist line that
differs from `origin/main`.

Each allowlisted axiom is pinned to its statement and to every definition of the audited modules
the statement reaches (`NAME PIN`, `closurePin`), so a PR that changes what an entry admits, also
by changing a definition it names, must change the entry. Also a violation: an `@[implemented_by]`, `@[extern]` or
`@[export]` declaration (it replaces or exports compiled code that no proof is about, as a
`@[csimp]` lemma does with a proof), unless `ALLOWLIST` lists it with its argument
(`implemented_by NAME TARGET PIN`, the target pinned like an axiom; `extern NAME`,
`export NAME SYMBOL`); in an executable root, any. Every imported module must be audited or part
of Lean (`Init`, `Std`, `Lean`) read from the toolchain's `lib/lean`, and every allowlist entry
must match a declaration.

A theorem that several modules declare (an equation lemma realized on demand) has one copy in the
imported environment; the audit takes the axioms of every copy (`St.copies`), so a module that
saw another copy than the one `importModules` keeps is audited too.
-/

open Lean

namespace GoFVTest.AxiomsAudit

def std : NameSet := NameSet.empty |>.insert ``propext |>.insert ``Classical.choice
  |>.insert ``Quot.sound

/-- Traversal state: the non-standard axioms of every constant seen (shared by the whole audit,
for the `LIB` environment's constants), those of the current root's own constants, and the
dependencies that were not found. -/
structure St where
  /-- Every copy of a constant that `LIB` modules declare more than once (or that a toolchain
  module declares too): `importModules` keeps one, and other modules may have used another. -/
  copies : Std.HashMap Name (Array ConstantInfo) := {}
  memo : Std.HashMap Name NameSet := {}
  rootMemo : Std.HashMap Name NameSet := {}
  missing : NameSet := {}

/-- The axioms other than `std` that constant `c` depends on, through its type, value and
constructors: the traversal of `Lean.CollectAxioms.collect`, with one cache for the whole audit.
(`collectAxioms` reads per-module tables that `importModules (loadExts := false)` does not load;
it then walks every body afresh, for minutes.) `rootConsts` holds the current root's own constants,
cached separately (two roots may declare the same name, such as `main`). A constant met again on
a cycle (an inductive and its constructors) contributes nothing on the back edge; the cycle's
axioms are collected at its first constant, so the union over all audited constants, which
decides the verdict, is complete. -/
partial def axiomsOf (env : Environment) (rootConsts : Std.HashMap Name ConstantInfo) (c : Name) :
    StateM St NameSet := do
  let isLocal := rootConsts.contains c
  if isLocal then
    if let some s := (← get).rootMemo[c]? then return s
  else
    if let some s := (← get).memo[c]? then return s
  let mark (s : NameSet) : StateM St Unit :=
    if isLocal then modify fun st => { st with rootMemo := st.rootMemo.insert c s }
    else modify fun st => { st with memo := st.memo.insert c s }
  mark {}
  let mut acc : NameSet := {}
  let mut deps : Array Name := #[]
  let cis : Array ConstantInfo ← match rootConsts[c]? with
    | some ci => pure #[ci]
    | none => do
      let cs := (← get).copies[c]?.getD #[]
      pure <| match env.find? c with
        | some ci => cs.push ci
        | none => cs
  if cis.isEmpty then modify fun st => { st with missing := st.missing.insert c }
  for ci in cis do
    match ci with
    | .axiomInfo v =>
      -- the standard axioms are always allowed: not tracked, so almost every set is the empty one
      unless std.contains c do acc := acc.insert c
      deps := deps ++ v.type.getUsedConstants
    | .defnInfo v => deps := deps ++ v.type.getUsedConstants ++ v.value.getUsedConstants
    | .thmInfo v => deps := deps ++ v.type.getUsedConstants ++ v.value.getUsedConstants
    | .opaqueInfo v => deps := deps ++ v.type.getUsedConstants ++ v.value.getUsedConstants
    | .ctorInfo v => deps := deps ++ v.type.getUsedConstants
    | .recInfo v => deps := deps ++ v.type.getUsedConstants
    | .inductInfo v => deps := deps ++ v.type.getUsedConstants ++ v.ctors.toArray
    | .quotInfo _ => pure ()
  for d in deps do
    let ds ← axiomsOf env rootConsts d
    unless ds.isEmpty do
      for a in ds.toList do acc := acc.insert a
  mark acc
  return acc

/-- `…._native.native_decide.ax_…` / `…._native.bv_decide.ax_…`: the tactic, if `n` has that shape. -/
def nativeTactic? (n : Name) : Option String :=
  match n with
  | .str (.str (.str _ "_native") tac) ax =>
    if ax.startsWith "ax_" && (tac == "native_decide" || tac == "bv_decide") then some tac else none
  | _ => none

/-- The SHA-256 (hex, by `sha256sum`) of `s`. -/
def sha256 (s : String) : IO String := do
  let child ← IO.Process.spawn { cmd := "sha256sum", stdin := .piped, stdout := .piped }
  let (stdin, child) ← child.takeStdin
  stdin.putStr s
  stdin.flush
  let out ← child.stdout.readToEnd
  unless (← child.wait) == 0 do throw <| IO.userError "axioms-audit: sha256sum failed"
  let some h := out.splitOn " " |>.head? | throw <| IO.userError "axioms-audit: sha256sum output"
  unless h.length == 64 do throw <| IO.userError s!"axioms-audit: sha256sum output {out}"
  return h

/-- A `Name`, component by component (`toString` and `repr` do not escape every component:
`«a.b»` and `a.b` can print alike, so a look-alike constant could stand in for a pinned one). -/
def serName : Name → String
  | .anonymous => "."
  | .str p s => serName p ++ "/s" ++ s.quote
  | .num p n => serName p ++ "/n" ++ toString n

def serLevel : Level → String
  | .zero => "0"
  | .succ u => s!"(S {serLevel u})"
  | .max a b => s!"(M {serLevel a} {serLevel b})"
  | .imax a b => s!"(I {serLevel a} {serLevel b})"
  | .param n => s!"(P {serName n})"
  | .mvar _ => "(?)"

/-- The serialization of a set of expressions: one line per distinct subterm, children by line
number (hash-consed on the line, so linear in the size of the shared term, which `repr` is not).
Binder names, binder info and metadata are left out: the kernel ignores them. -/
structure Ser where
  lines : Array String := #[]
  ids : Std.HashMap String Nat := {}
  /-- Subterms already serialized, by address: only a cache (the lines depend on the terms'
  structure alone). -/
  ptrs : Std.HashMap USize Nat := {}

unsafe def serExpr (e : Expr) : StateM Ser Nat := do
  if let .mdata _ b := e then return ← serExpr b
  if let some i := (← get).ptrs[ptrAddrUnsafe e]? then return i
  let line ← match e with
    | .bvar i => pure s!"B {i}"
    | .sort u => pure s!"T {serLevel u}"
    | .const n us => pure s!"C {serName n} {us.map serLevel}"
    | .app f a => do let i ← serExpr f; let j ← serExpr a; pure s!"A {i} {j}"
    | .lam _ t b _ => do let i ← serExpr t; let j ← serExpr b; pure s!"L {i} {j}"
    | .forallE _ t b _ => do let i ← serExpr t; let j ← serExpr b; pure s!"F {i} {j}"
    | .letE _ t v b nd => do
      let i ← serExpr t; let j ← serExpr v; let k ← serExpr b; pure s!"E {i} {j} {k} {nd}"
    | .lit (.natVal n) => pure s!"N {n}"
    | .lit (.strVal x) => pure s!"S {x.quote}"
    | .proj t i b => do let j ← serExpr b; pure s!"J {serName t} {i} {j}"
    | _ => pure "?"
  -- (the index is read before the push: reading `st.lines` after pushing to it copies the array)
  let i ← modifyGet fun st => match st.ids[line]? with
    | some i => (i, st)
    | none => let i := st.lines.size
      (i, { st with ids := st.ids.insert line i, lines := st.lines.push line })
  modify fun st => { st with ptrs := st.ptrs.insert (ptrAddrUnsafe e) i }
  return i

/-- The serialization of the constants `names` (`closurePin`). -/
unsafe def serConsts (env : Environment) (names : Array Name) : StateM Ser (Array String) := do
  let mut out : Array String := #[]
  for c in names do
    let some ci := env.find? c | continue
    let kind := match ci with
      | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
      | .ctorInfo _ => "ctor" | .recInfo _ => "rec"
    let t ← serExpr ci.type
    let mut entry := s!"{kind} {serName c} {ci.levelParams.map serName} type {t}"
    match ci with
    | .defnInfo { value, .. } | .opaqueInfo { value, .. } =>
      entry := entry ++ s!" value {← serExpr value}"
    | _ => pure ()
    out := out.push entry
  return out

/-- The structures of the projections in `e` (`getUsedConstants` does not list them). -/
unsafe def projStructs (e : Expr) : Array Name :=
  let rec go (e : Expr) : StateM (Std.HashSet USize × Array Name) Unit := do
    if (← get).1.contains (ptrAddrUnsafe e) then return
    modify fun (v, a) => (v.insert (ptrAddrUnsafe e), a)
    match e with
    | .proj t _ b => modify (fun (v, a) => (v, a.push t)); go b
    | .app f x => go f; go x
    | .lam _ t b _ | .forallE _ t b _ => go t; go b
    | .letE _ t v b _ => go t; go v; go b
    | .mdata _ b => go b
    | _ => pure ()
  ((go e).run ({}, #[])).2.2

/-- The pin of an allowlist entry: the SHA-256 of `start` and of every constant declared in an
audited module (`inLib`) that it reaches through types, definition and opaque values, and
inductive types' constructors; theorems contribute their statement only (their proofs are checked
anyway). A PR that changes a definition an allowlisted statement names changes the pin, which
the audit prints, so the allowlist line changes too. Toolchain constants are not followed. -/
unsafe def closurePin (env : Environment) (inLib : Name → Bool) (start : Name) : IO String := do
  let mut todo : Array Name := #[start]
  let mut seen : NameSet := {}
  while h : todo.size > 0 do
    let c := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains c || !(c == start || inLib c) then continue
    seen := seen.insert c
    let some ci := env.find? c | continue
    -- the compiled code of a `partial def` (its kernel value is opaque)
    if env.contains (c ++ `_unsafe_rec) then todo := todo.push (c ++ `_unsafe_rec)
    -- a projection's structure (`getUsedConstants` skips it)
    let projs (e : Expr) : Array Name := e.getUsedConstants ++ projStructs e
    todo := todo ++ projs ci.type
    match ci with
    | .defnInfo v => todo := todo ++ projs v.value
    | .opaqueInfo v => todo := todo ++ projs v.value
    | .inductInfo v => todo := todo ++ v.ctors.toArray
    | .ctorInfo v => todo := todo.push v.induct
    | _ => pure ()
  let names := seen.toArray.qsort (fun a b => serName a < serName b)
  -- one state for the whole serialization (a state also held by a variable is copied on write)
  let (out, ser) := (serConsts env names).run {}
  sha256 ("\n".intercalate (ser.lines.toList ++ ["--"] ++ out.toList))

/-- An allowlist entry is admissible when it is an axiom of the generated shape whose statement
is a boolean computation evaluating to `true` (`decide p = true` for `native_decide`). -/
unsafe def entryOk (env : Environment) (inLib : Name → Bool) (n : Name) (want : String) :
    ExceptT String IO Unit := do
  let some tac := nativeTactic? n | throw "not a `_native.(native_decide|bv_decide).ax_*` name"
  let some (.axiomInfo ai) := env.find? n | throw "not an axiom of the audited modules"
  let ty := ai.type.consumeMData
  unless ty.isAppOfArity ``Eq 3 && (ty.getArg! 0).isConstOf ``Bool &&
      (ty.getArg! 2).isConstOf ``Bool.true do
    throw "its type is not `_ = true`"
  if tac == "native_decide" && !(ty.getArg! 1).isAppOfArity ``Decidable.decide 2 then
    throw "a native_decide axiom whose type is not `decide _ = true`"
  -- the entry pins the statement, so changing what it admits needs a visible allowlist edit
  let h ← closurePin env inLib n
  unless h == want do
    throw s!"its pin is {h}, the allowlist pins {want} (type: {ai.type})"

structure Totals where
  theorems : Nat := 0
  constants : Nat := 0
  natives : Nat := 0
  violations : Nat := 0
  errors : Nat := 0

/-- Audit one constant: count it, report each axiom it depends on that the policy does not admit. -/
def auditConst (env : Environment) (rootConsts : Std.HashMap Name ConstantInfo) (allow : NameSet)
    (c : Name) (ci : ConstantInfo) (st : St) (t : Totals) : IO (St × Totals) := do
  let (axs, st) := (axiomsOf env rootConsts c).run st
  let isThm := ci matches .thmInfo _
  let mut t := { t with constants := t.constants + 1, theorems := t.theorems + (if isThm then 1 else 0) }
  if isThm && axs.toList.any (nativeTactic? · |>.isSome) then t := { t with natives := t.natives + 1 }
  for a in axs.toList do
    unless allow.contains a && a != ``sorryAx && a != ``Lean.trustCompiler do
      IO.println s!"VIOLATION {(toString c).quote} {(toString a).quote}"
      t := { t with violations := t.violations + 1 }
  return (st, t)

/-- The allowlist: `NAME PIN` lines for `_native` axioms (`PIN`: `closurePin` of the axiom, which
an allowlist error prints), and `implemented_by NAME TARGET PIN` (`PIN`: `closurePin` of the
target), `extern NAME`, `export NAME SYMBOL` lines for declarations that replace or export compiled
code. -/
structure Allow where
  axioms : NameMap String := {}
  /-- `(attribute, declaration) ↦ argument` (`""` for `extern`). -/
  code : Std.HashMap (String × Name) String := {}

def readAllowlist (path : System.FilePath) : IO Allow := do
  let mut a : Allow := {}
  for line in (← IO.FS.lines path) do
    let l := ((line.splitOn "#").headD "").trimAscii.toString
    if l.isEmpty then continue
    match l.splitOn " " |>.filter (!·.isEmpty) with
    | ["implemented_by", n, tgt, h] =>
      a := { a with code := a.code.insert ("implemented_by", n.toName) s!"{tgt} {h}" }
    | ["export", n, sym] => a := { a with code := a.code.insert ("export", n.toName) sym }
    | ["extern", n] => a := { a with code := a.code.insert ("extern", n.toName) "" }
    | [n, h] =>
      unless h.length == 64 && h.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) do
        throw <| IO.userError s!"axioms-audit: allowlist line not understood: {l}"
      a := { a with axioms := a.axioms.insert n.toName h }
    | _ => throw <| IO.userError s!"axioms-audit: allowlist line not understood: {l}"
  return a

def modules (s : String) : Array Name :=
  (s.splitOn ",").filter (!·.isEmpty) |>.map String.toName |>.toArray

end GoFVTest.AxiomsAudit

/-- Send `cis` to the kernel, into `kenv`. A theorem whose name is already taken (a copy that
another module declares too, which `Kernel.Environment.replay` would skip when the statements
agree) is checked under a fresh name, so every copy's proof is checked. -/
def replayAll (kenv : Kernel.Environment) (cis : Array ConstantInfo) :
    IO (Kernel.Environment × Nat) := do
  let mut consts : Std.HashMap Name ConstantInfo := {}
  let mut copies : Array TheoremVal := #[]
  for ci in cis do
    if consts.contains ci.name || (kenv.find? ci.name).isSome then
      match ci with
      | .thmInfo v => copies := copies.push v
      | _ => throw <| IO.userError s!"{ci.name} declared twice"
    else
      consts := consts.insert ci.name ci
  let kenv ← kenv.replay consts
  let mut fresh : Std.HashMap Name ConstantInfo := {}
  for v in copies, k in 0...copies.size do
    let n := Name.mkNum (v.name ++ `_gofvAuditCopy) k
    fresh := fresh.insert n (.thmInfo { v with name := n, all := [n] })
  return (← kenv.replay fresh, copies.size)

open GoFVTest.AxiomsAudit in
/-- `--replay LIB ROOTS`: send every constant declared in the `LIB` modules to the kernel again,
then each root's, in an environment holding only the modules they import that are not in `LIB`
(`Init`, `Std`, `Lean`, and, for `--replay-changed`, the unchanged `LIB` modules),
trusted as `leanchecker` trusts imports; exit 0 iff the kernel accepts all. A `.olean` holds
whatever the elaborator added, and `set_option debug.skipKernelTC true` lets declarations bypass
the kernel; the axioms audit reads declarations and would not notice. `LIB` must be closed under
importers (a module importing a `LIB` module is in `LIB` or a root): the base is imported once,
and an `.olean` mapped twice is copied onto the heap. Unsafe and partial constants are not
replayed, as in `leanchecker` (a checked constant that uses one fails); every copy of a theorem
that several modules declare is (`replayAll`). -/
def replayMain (lib roots : Array Name) (trustedOk : NameSet := {}) : IO UInt32 := do
  let libSet : NameSet := lib.foldl (·.insert ·) {}
  let mut base : Array Import := #[]
  let mut seen : NameSet := {}
  let mut trusted := 0
  let mut mds : Array (Name × ModuleData) := #[]
  for m in lib ++ roots do
    let (md, _) ← readModuleData (← findOLean m)
    if md.isModule then throw <| IO.userError s!"module {m} uses the module system (not supported)"
    for i in md.imports do
      if libSet.contains i.module || seen.contains i.module then continue
      unless [`Init, `Std, `Lean].contains i.module.getRoot do
        -- only an audited module that `--replay-changed` leaves out (unchanged) may be trusted
        unless trustedOk.contains i.module do
          throw <| IO.userError s!"module {m} imports {i.module}, which is neither replayed nor part of Lean"
        trusted := trusted + 1
      seen := seen.insert i.module
      base := base.push { module := i.module }
    mds := mds.push (m, md)
  let env ← importModules base {} (loadExts := false)
  if trusted > 0 then
    IO.println s!"trusted, not replayed: {trusted} GoFV/GoFVTest modules imported directly"
  let t0 ← IO.monoMsNow
  let libConsts := mds.filter (libSet.contains ·.1) |>.flatMap (·.2.constants)
  let (kenv, n) ← replayAll env.toKernelEnv libConsts
  IO.println s!"replayed {libConsts.size} constants ({n} copies) of {lib.size} modules in {(← IO.monoMsNow) - t0} ms"
  for (m, md) in mds do
    if libSet.contains m then continue
    discard <| replayAll kenv md.constants
  IO.println s!"replayed {roots.size} executable roots"
  IO.println "RESULT PASS"
  return 0

open GoFVTest.AxiomsAudit in
unsafe def main (args : List String) : IO UInt32 := do
  if let ["--replay", libArg, rootsArg] := args then
    initSearchPath (← findSysroot)
    return ← replayMain (modules libArg) (modules rootsArg)
  if let ["--replay-changed", changedArg, libArg, rootsArg] := args then
    -- the changed modules and every module that imports one, directly or not (their elaboration
    -- ran code of the changed modules); the others are imported, trusted, as checked before
    initSearchPath (← findSysroot)
    let lib := modules libArg
    let roots := modules rootsArg
    let mut importers : Std.HashMap Name (Array Name) := {}
    for m in lib ++ roots do
      let path := System.mkFilePath (m.components.map toString) |>.addExtension "lean"
      let (imps, _, log) ← Elab.parseImports (← IO.FS.readFile path) path.toString
      if log.hasErrors then throw <| IO.userError s!"cannot parse the imports of {path}"
      for i in imps do importers := importers.insert i.module ((importers.getD i.module #[]).push m)
    for m in modules changedArg do
      unless lib.contains m || roots.contains m do
        throw <| IO.userError s!"changed module {m} is neither in LIB nor a root"
    let mut sel : NameSet := {}
    let mut todo := modules changedArg
    while h : todo.size > 0 do
      let m := todo[todo.size - 1]
      todo := todo.pop
      if sel.contains m then continue
      sel := sel.insert m
      todo := todo ++ importers.getD m #[]
    IO.println s!"replaying {sel.size} changed or dependent modules"
    let unchanged : NameSet := lib.foldl (fun s m => if sel.contains m then s else s.insert m) {}
    return ← replayMain (lib.filter sel.contains) (roots.filter sel.contains) unchanged
  let [allowPath, libArg, rootsArg] := args
    | IO.eprintln "usage: axioms-audit ALLOWLIST LIB ROOTS | axioms-audit --replay LIB ROOTS | axioms-audit --replay-changed CHANGED LIB ROOTS"
      return 2
  let sysroot ← findSysroot
  initSearchPath sysroot
  let al ← readAllowlist allowPath
  let allow : NameSet := al.axioms.foldl (fun s n _ => s.insert n) {}
  let lib := modules libArg
  let roots := modules rootsArg
  if lib.isEmpty then IO.eprintln "axioms-audit: no LIB modules"; return 2
  -- `Lean` too: the roots' dependencies outside LIB (a root may import only `Lean`)
  let env ← importModules ((lib.push `Lean).map ({ module := · })) {} (loadExts := false)
  let mut idx : Std.HashSet Nat := {}
  for m in lib do
    let some i := env.getModuleIdx? m | throw <| IO.userError s!"module {m} not imported"
    idx := idx.insert i.toNat
  let mut t : Totals := {}
  let inLib (c : Name) : Bool := (env.getModuleIdxFor? c).any (idx.contains ·.toNat)
  -- every imported module is audited or part of Lean itself, read from the toolchain
  let leanLib := (← IO.FS.realPath (sysroot / "lib" / "lean")).toString ++ "/"
  let fromToolchain (m : Name) : IO Bool := do
    if [`Init, `Std, `Lean].contains m.getRoot then
      pure ((← IO.FS.realPath (← findOLean m)).toString.startsWith leanLib)
    else pure false
  for m in env.header.moduleNames, i in 0...env.header.moduleNames.size do
    if idx.contains i then continue
    unless ← fromToolchain m do
      IO.println s!"ERROR imported module {(toString m).quote} is neither audited nor part of the Lean toolchain"
      t := { t with errors := t.errors + 1 }
  for (n, h) in al.axioms.toList do
    let r : Except String Unit ← if inLib n then (entryOk env inLib n h).run
      else pure (.error "not declared in an audited module")
    if let .error e := r then
      IO.println s!"ALLOWLIST-ERROR {(toString n).quote}: {e}"
      t := { t with errors := t.errors + 1 }
  -- `@[implemented_by]` / `@[extern]` / `@[export]` in LIB modules: allowed only as listed
  let mut used : Std.HashSet (String × Name) := {}
  for i in idx.toList do
    -- an `implemented_by` target is pinned with what it reaches: changing the code that replaces
    -- the definition's needs a visible allowlist edit
    let impl ← (Compiler.implementedByAttr.ext.getModuleEntries env i).mapM fun (n, tgt) => do
      return ("implemented_by", n, s!"{toString tgt} {← closurePin env inLib tgt}")
    let found : Array (String × Name × String) := impl ++
      (externAttr.ext.getModuleEntries env i).map (fun (n, _) => ("extern", n, "")) ++
      (exportAttr.ext.getModuleEntries env i).map (fun (n, sym) => ("export", n, toString sym))
    for (attr, n, arg) in found do
      used := used.insert (attr, n)
      unless al.code[(attr, n)]? == some arg do
        IO.println s!"VIOLATION {(toString n).quote} {s!"@[{attr}] {arg}".trimAscii.toString.quote}"
        t := { t with violations := t.violations + 1 }
  for ((attr, n), arg) in al.code.toList do
    unless used.contains (attr, n) do
      IO.println s!"ALLOWLIST-ERROR {(toString n).quote}: no @[{attr}] {arg} declaration in an audited module"
      t := { t with errors := t.errors + 1 }
  -- every copy of a constant declared by several modules (`importModules` keeps one)
  let mut count : Std.HashMap Name Nat := {}
  for i in idx.toList do
    for c in env.header.moduleData[i]!.constNames do count := count.insert c (count.getD c 0 + 1)
  let mut copies : Std.HashMap Name (Array ConstantInfo) := {}
  for i in idx.toList do
    for ci in env.header.moduleData[i]!.constants do
      if count.getD ci.name 0 > 1 || !inLib ci.name then
        copies := copies.insert ci.name ((copies.getD ci.name #[]).push ci)
  let mut st : St := { copies }
  for (c, ci) in env.constants.map₁.toList do
    -- a constant some audited module declares, also when a toolchain module declares it first
    unless inLib c || copies.contains c do continue
    (st, t) ← auditConst env {} allow c ci st t
  for r in roots do
    if (env.getModuleIdx? r).isSome then
      IO.println s!"ERROR root {(toString r).quote} is also imported by LIB"
      t := { t with errors := t.errors + 1 }
      continue
    let (md, _) ← readModuleData (← findOLean r)
    if md.isModule then
      -- only the exported part would be read: private declarations would go unaudited
      IO.println s!"ERROR root {(toString r).quote} uses the module system (not supported)"
      t := { t with errors := t.errors + 1 }
      continue
    -- a root's imports follow the same rule as `LIB`'s: audited, or read from the toolchain
    for i in md.imports do
      let audited := (env.getModuleIdx? i.module).any (idx.contains ·.toNat)
      unless audited || (← fromToolchain i.module) do
        IO.println s!"ERROR root {(toString r).quote} imports {(toString i.module).quote}, which is neither audited nor part of the Lean toolchain"
        t := { t with errors := t.errors + 1 }
    for (ext, es) in md.entries do
      if (ext == Compiler.implementedByAttr.ext.name || ext == externAttr.ext.name ||
          ext == exportAttr.ext.name) && !es.isEmpty then
        IO.println s!"VIOLATION {(toString r).quote} \"@[implemented_by]/@[extern]/@[export] in an executable root\""
        t := { t with violations := t.violations + 1 }
    let rootConsts : Std.HashMap Name ConstantInfo :=
      md.constants.foldl (fun m ci => m.insert ci.name ci) {}
    for ci in md.constants do
      if env.contains ci.name then
        -- it would shadow a library constant in the shared memo
        IO.println s!"ERROR root constant {(toString ci.name).quote} also declared in LIB"
        t := { t with errors := t.errors + 1 }
    st := { st with rootMemo := {} }
    for ci in md.constants do
      (st, t) ← auditConst env rootConsts allow ci.name ci st t
  for n in st.missing.toList do
    IO.println s!"ERROR dependency {(toString n).quote} not found"
    t := { t with errors := t.errors + 1 }
  let ok := t.violations == 0 && t.errors == 0 && t.theorems > 0
  IO.println s!"theorems audited: {t.theorems} (constants: {t.constants}, modules: {lib.size} + {roots.size} executable roots)"
  IO.println s!"theorems using a _native axiom (bv_decide/native_decide): {t.natives}"
  IO.println s!"violations: {t.violations}, errors: {t.errors}"
  IO.println s!"RESULT {if ok then "PASS" else "FAIL"}"
  return if ok then 0 else 1

import GoFV.Rules.Generated
import GoFV.Proof.Rules.Den

/-!
# Satisfying instances of the rule obligations (`docs/proofs/rules.md`, "Non-vacuity")

`lake exe rule-sat` searches, for every exported value rule, an instance of its pattern
(`GoFV.Proof.Rules.PEnv`) and an oracle on which every hypothesis of `Rule.Sound` holds and the
matched value is not `poison`, so that `Rule.Sound r` says something about it. It prints one
line per rule:

* `<file> <op>#<index> SAT <instance>`: found; the rule's result refines the matched value there;
* `<file> <op>#<index> CEX <instance>`: found, and the result does not refine the matched value
  (a counterexample to `Rule.Sound`);
* `<file> <op>#<index> NONE`: no instance found.

`scripts/rule-proofs.py sat` runs it and lists the proven rules without an instance (or with a
counterexample). The search is random (fixed seed): leaves get values of a width suggested by
their consumer op, auxints come from a pool of boundary values, `[c]`/`<t>` checks and `same x`
leaves are then solved for, node types are the shapes of the computed values, and unmodelled
atoms (`Oracle`) are all `true` or all `false`, helper calls and unmodelled literals (`"opt"`)
independently of the rest. The checks below mirror `Pat.wf`, `Pat.cons`,
`condHolds` and `Refines` as `Bool` functions.
-/

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules

namespace GoFVTest.RuleSat

/-! ## `Bool` mirrors of the obligation's hypotheses -/

partial def tyBeq : Ty → Ty → Bool
  | .int a, .int b => a == b
  | .bool, .bool | .mem, .mem | .other, .other | .empty, .empty => true
  | .tuple as, .tuple bs => as.length == bs.length && (as.zip bs).all fun (a, b) => tyBeq a b
  | .ptr a, .ptr b => a == b
  | .agg fs n, .agg gs m =>
    n == m && fs.length == gs.length &&
      (fs.zip gs).all fun ((i, a), (j, b)) => i == j && tyBeq a b
  | .blob a, .blob b | .opaque a, .opaque b => a == b
  | _, _ => false

partial def dvBeq : DV → DV → Bool
  | .int a, .int b => a == b
  | .bool a, .bool b => a == b
  | .ty a, .ty b => tyBeq a b
  | .op a, .op b => a == b
  | .val v p, .val w q => v == w && p == q
  | .strct fs, .strct gs =>
    fs.length == gs.length && (fs.zip gs).all fun ((n, a), (m, b)) => n == m && dvBeq a b
  | .other, .other => true
  | _, _ => false

mutual
def consB (ev : GoFV.Rules.Expr → DV) (σ : Nat → DV) (e : PEnv) (p : Path) : Pat → Bool
  | .wild | .bind _ => true
  | .same x => match σ x with
    | .val w _ => e.leaf p == w
    | _ => true
  | .op o _ ty ai _ _ args _ =>
    (match ty with | .eq te => dvBeq (.ty (e.ty p)) (ev te) | _ => true) &&
    (match ai with | .eq ae => dvBeq (auxIntDV o.auxType (e.auxInt p)) (ev ae) | _ => true) &&
    conssB ev σ e p 0 args
def conssB (ev : GoFV.Rules.Expr → DV) (σ : Nat → DV) (e : PEnv) (p : Path) (i : Nat) :
    List Pat → Bool
  | [] => true
  | q :: qs => consB ev σ e (i :: p) q && conssB ev σ e p (i + 1) qs
end

def auxIntOkB (aty : AuxType) (a : Int64) : Bool :=
  match aty with
  | .Bool => a == 0 || a == 1
  | _ => true

mutual
def wfB (e : PEnv) (p : Path) : Pat → Bool
  | .op o _ _ _ _ _ args _ => auxIntOkB o.auxType (e.auxInt p) && wfsB e p 0 args
  | _ => true
def wfsB (e : PEnv) (p : Path) (i : Nat) : List Pat → Bool
  | [] => true
  | q :: qs => wfB e (i :: p) q && wfsB e p (i + 1) qs
end

mutual
def typedB (e : PEnv) (p : Path) : Pat → Bool
  | .op _ _ _ _ _ _ args _ => typedsB e p 0 args
  | _ => (e.leaf p).hasTy (e.ty p)
def typedsB (e : PEnv) (p : Path) (i : Nat) : List Pat → Bool
  | [] => true
  | q :: qs => typedB e (i :: p) q && typedsB e p (i + 1) qs
end

def condB (ev : GoFV.Rules.Expr → DV) : Option GoFV.Rules.Expr → Bool
  | some c => match ev c with
    | .bool true => true
    | _ => false
  | none => true

partial def refinesB : Val → Val → Bool
  | .poison, _ => true
  | .tuple as, .tuple bs | .agg as, .agg bs =>
    as.length == bs.length && (as.zip bs).all fun (a, b) => refinesB a b
  | a, b => a == b

/-! ## Instances -/

-- Every position of a pattern with its sub-pattern.
mutual
def patPos (p : Path) : Pat → List (Path × Pat)
  | pat@(.op _ _ _ _ _ _ args _) => (p, pat) :: patsPos p 0 args
  | pat => [(p, pat)]
def patsPos (p : Path) (i : Nat) : List Pat → List (Path × Pat)
  | [] => []
  | q :: qs => patPos (i :: p) q ++ patsPos p (i + 1) qs
end

/-- A finite instance; missing entries are `poison`, `other`, `0`. -/
structure Inst where
  leaf : List (Path × Val) := []
  ty : List (Path × Ty) := []
  auxInt : List (Path × Int64) := []

def Inst.env (i : Inst) : PEnv where
  leaf p := (i.leaf.lookup p).getD .poison
  ty p := (i.ty.lookup p).getD .other
  auxInt p := (i.auxInt.lookup p).getD 0
  aux _ := none

def set {α} (l : List (Path × α)) (p : Path) (a : α) : List (Path × α) :=
  (p, a) :: l.filter (·.1 != p)

/-- Every oracle atom is `b`, except helper calls (`hasSmallRotate(config)`, `canRotate()`, …),
which are `calls`, and unmodelled literals, which are `lits`: a condition may need a call atom
false next to a field atom true, or a field different from a literal
(`v.Block.Func.pass.name != "opt"`). -/
def oracle (b calls lits : Bool) : Oracle where
  dv x := match x with
    | .call .. => .bool calls
    | .lit .. => .bool lits
    | _ => .bool b
  ty _ := .other
  auxInt _ := 0
  aux _ := none
  val _ := .poison

/-- The shape of a computed value. -/
partial def shapeOf : Val → Ty
  | .int w _ => .int w
  | .bool _ => .bool
  | .mem _ => .mem
  | .tuple vs => .tuple (vs.map shapeOf)
  | .ptr _ => .ptr none
  | .agg _ | .blob _ | .poison => .other
  | .empty => .empty

/-- The shape of an op's Go result type (`Op.typ`). -/
def tyOfTyp : String → Ty
  | "Int8" | "UInt8" => .int .w8
  | "Int16" | "UInt16" => .int .w16
  | "Int32" | "UInt32" => .int .w32
  | "Int64" | "UInt64" | "Int" | "UInt" | "Uintptr" => .int .w64
  | "Bool" => .bool
  | _ => .other

/-- The widths named in an op (`Lsh32x64` → `[32, 64]`, `ZeroExt8to64` → `[8, 64]`). -/
def opWidths (o : Op) : List Width :=
  let groups := (o.name.splitOn "x").flatMap (·.splitOn "to")
  groups.filterMap fun g =>
    match String.ofList (g.toList.filter Char.isDigit) with
    | "8" => some .w8 | "16" => some .w16 | "32" => some .w32 | "64" => some .w64
    | _ => none

/-- The width an op probably reads its argument `i` at: shifts read the amount (argument 1)
at their second width, conversions read their first width, others their only width. -/
def argHint (o : Op) (i : Nat) : Option Width :=
  match opWidths o with
  | [w] => some w
  | [a, b] => if (o.name.splitOn "x").length > 1 then some (if i == 1 then b else a) else some a
  | _ => none

def isBoolOp (o : Op) : Bool :=
  ["AndB", "OrB", "EqB", "NeqB", "Not"].contains o.name

/-- The binding occurrences of the rule's value variables with the op and argument index
consuming them. -/
def leafHints (pos : List (Path × Pat)) : List (Path × Option Op × Nat) :=
  pos.filterMap fun (p, q) =>
    match q with
    | .bind _ | .wild =>
      match p with
      | i :: parent => match pos.lookup parent with
        | some (.op o _ _ _ _ _ _ _) => some (p, some o, i)
        | _ => some (p, none, i)
      | [] => some (p, none, 0)
    | _ => none

def intPool : Array Int :=
  #[0, 1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 255, 256, 1000,
    32767, 32768, 65535, 2147483647, 2147483648, 4294967295, 9223372036854775807, -1, -2, -3,
    -8, -16, -128, -32768, -2147483648, -9223372036854775808]

def pick {α} [Inhabited α] (xs : Array α) : IO α := do
  return xs[← IO.rand 0 (xs.size - 1)]!

def randInt : IO Int := do
  if (← IO.rand 0 3) == 0 then return Int.ofNat (← IO.rand 0 1000000) - 500000
  pick intPool

def randWidth : IO Width := pick #[.w8, .w16, .w32, .w64]

/-- The leaf read by `o` at argument `i` is a pointer (`argShapeOk`). -/
def ptrArg (o : Option Op) (i : Nat) : Bool :=
  match o with
  | some o => (["OffPtr", "AddPtr", "PtrIndex", "IsNonNil"].contains o.name && i == 0) ||
      ["EqPtr", "NeqPtr"].contains o.name
  | none => false

/-- A random pointer: nil, a heap or a global allocation, small offsets. -/
def randPtr : IO Val := do
  let blk ← pick #[Blk.nil, .heap 0, .heap 3, .global "g"]
  let off ← pick #[(0 : Int), 8, 16, 1000]
  return .ptr ⟨blk, BitVec.ofInt 64 off⟩

/-- A random leaf value for a leaf read by `o` at argument `i`. -/
def randLeaf (o : Option Op) (i : Nat) : IO Val := do
  if ptrArg o i then return ← randPtr
  let boolish := match o with
    | some o => isBoolOp o || (o.name == "CondSelect" && i == 2)
    | none => false
  if boolish || (← IO.rand 0 9) == 0 then
    if (← IO.rand 0 9) != 0 || boolish then return .bool ((← IO.rand 0 1) == 1)
  let w ← match o.bind (argHint · i) with
    | some w => if (← IO.rand 0 4) == 0 then randWidth else pure w
    | none => randWidth
  return .int w (BitVec.ofInt w.bits (← randInt))

/-- Op nodes, deepest first. -/
def nodesOf (pos : List (Path × Pat)) : List (Path × Pat) :=
  let ns := pos.filter fun (_, q) => match q with | .op .. => true | _ => false
  (ns.toArray.qsort (fun a b => a.1.length > b.1.length)).toList

/-- Every leaf typed by its value's shape (`Pat.typed`). -/
def typeLeaves (pos : List (Path × Pat)) (i : Inst) : Inst := Id.run do
  let mut i := i
  for (p, q) in pos do
    match q with
    | .op .. => pure ()
    | _ => i := { i with ty := set i.ty p (shapeOf (i.env.leaf p)) }
  return i

/-- One round of solving: leaf types from their values, node types from the computed values,
then `<t>` and `[c]` checks and `same x` leaves from the current bindings. -/
def solve (r : Rule) (pos : List (Path × Pat)) (or : Oracle) (i : Inst) : Inst := Id.run do
  let mut i := typeLeaves pos i
  for (p, q) in nodesOf pos do
    match q with
    | .op o .. =>
      let e := i.env
      let raw := evalPure o (e.ty p) (e.auxInt p) none (Pat.dens e p 0 (match q with
        | .op _ _ _ _ _ _ args _ => args | _ => []))
      let t := match raw, e.ty p with
        | .poison, .other => tyOfTyp o.typ
        | .poison, t => t
        | .ptr _, .ptr el => .ptr el
        | v, _ => shapeOf v
      i := { i with ty := set i.ty p t }
    | _ => pure ()
  let e := i.env
  let σ := sigma e r.pat
  let ev := evalE (r.vars.map (·.ty)) σ or e (Pat.den e [] r.pat)
  for (p, q) in pos do
    match q with
    | .op _ _ ty ai _ _ _ _ =>
      if let .eq te := ty then
        if let .ty t := ev te then i := { i with ty := set i.ty p t }
      if let .eq ae := ai then
        match ev ae with
        | .int k => i := { i with auxInt := set i.auxInt p (Int64.ofInt k) }
        | .bool b => i := { i with auxInt := set i.auxInt p (if b then 1 else 0) }
        | _ => pure ()
    | .same x =>
      if let .val w _ := σ x then i := { i with leaf := set i.leaf p w }
    | _ => pure ()
  return typeLeaves pos i

/-- The instance satisfies every hypothesis and the matched value is not `poison`; `some ok`
with `ok` whether the result refines the matched value. -/
def check (r : Rule) (or : Oracle) (i : Inst) : Option Bool :=
  let e := i.env
  let σ := sigma e r.pat
  let ev := evalE (r.vars.map (·.ty)) σ or e (Pat.den e [] r.pat)
  let raw := Pat.raw e r.pat
  let ok := Pat.arityOk r.pat && wfB e [] r.pat && consB ev σ e [] r.pat && condB ev r.cond &&
    raw.hasTy (e.ty []) && typedB e [] r.pat && Pat.argsOK e.ty [] r.pat &&
    !(match raw with | .poison => true | _ => false)
  if ok then some (refinesB raw (resDen ev or σ (e.ty []) r.result)) else none

def render (i : Inst) : String :=
  let ls := i.leaf.map fun (p, v) => s!"{p.reverse}={v.render}"
  let as := i.auxInt.filter (·.2 != 0) |>.map fun (p, a) => s!"{p.reverse}:[{a.toInt}]"
  " ".intercalate (ls ++ as)

/-- Random search; `some (inst, refines)`. -/
def search (r : Rule) (trials : Nat) : IO (Option (Inst × Bool)) := do
  let pos := patPos [] r.pat
  let hints := leafHints pos
  let mut cex : Option (Inst × Bool) := none
  for t in [0:trials] do
    let b := t % 2 == 0
    let or := oracle b (if t % 4 == 2 then false else b) (if t % 8 ≥ 4 then !b else b)
    let mut i : Inst := {}
    for (p, o, k) in hints do
      i := { i with leaf := set i.leaf p (← randLeaf o k) }
    for (p, q) in pos do
      if let .op o .. := q then
        let a ← if o.auxType == .Bool then pure (Int64.ofInt (← IO.rand 0 1)) else
          pure (Int64.ofInt (← randInt))
        let t ← if o == .PtrIndex then pure (Ty.ptr (some (← pick #[1, 4, 8, 24])))
          else pure (tyOfTyp o.typ)
        i := { i with auxInt := set i.auxInt p a, ty := set i.ty p t }
    for _ in [0:3] do
      i := solve r pos or i
    match check r or i with
    | some true => return some (i, true)
    | some false => cex := cex <|> some (i, false)
    | none => pure ()
  return cex

def files : List RuleSet :=
  [Generated.Generic.ruleSet, Generated.Dec.ruleSet, Generated.Divisible.ruleSet,
   Generated.Divmod.ruleSet]

def main (args : List String) : IO UInt32 := do
  let trials := (args.find? (·.startsWith "--trials=")).bind (·.drop 9 |>.toNat?) |>.getD 6000
  let only := args.filter (!·.startsWith "--")
  IO.setRandSeed 69
  let mut stats := (0, 0, 0)
  for rs in files do
    for (o, rules) in rs.values do
      for (r, k) in rules.zipIdx do
        let key := s!"{o.name}#{k}"
        if !only.isEmpty && !only.contains s!"{rs.name}:{key}" then continue
        match ← search r trials with
        | some (i, true) =>
          IO.println s!"{rs.name} {key} SAT {render i}"
          stats := (stats.1 + 1, stats.2.1, stats.2.2)
        | some (i, false) =>
          IO.println s!"{rs.name} {key} CEX {render i}"
          stats := (stats.1, stats.2.1 + 1, stats.2.2)
        | none =>
          IO.println s!"{rs.name} {key} NONE"
          stats := (stats.1, stats.2.1, stats.2.2 + 1)
  IO.eprintln s!"SAT {stats.1}, CEX {stats.2.1}, NONE {stats.2.2}"
  return 0

end GoFVTest.RuleSat

def main (args : List String) : IO UInt32 := GoFVTest.RuleSat.main args

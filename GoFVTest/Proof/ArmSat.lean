import GoFV.Rules.Generated.ARM64
import GoFV.Rules.Generated.ARM64latelower
import GoFV.Proof.Low.RuleL
import GoFV.Rules.Derive
import GoFV.SSA.OpARM64

/-!
# Random counterexample search for `ARM64.rules` / `ARM64latelower.rules` value rules

`RuleSat` for `ArmRule.Sound1` (`GoFV/Proof/Low/RuleL.lean`): random instances of a rule's
pattern with integer, boolean and flags leaves only (no pointers, so the provenance model limits
of `docs/proofs/rules.md` do not show up), every hypothesis of `ArmRule.Sound1` checked as a
`Bool`, and the result compared with `Refines`. Lines:

* `<file>:<line> #k SAT`, `CEX <instance>`, `NONE`, `ORACLE <instance>` (the verdict depends on
  an unmodelled atom).
-/

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low

namespace GoFVTest.ArmSat

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


/-- `auxIntDVL` with the arm64 bit fields as integers (`bfc.lsb()`, `bfc.width()`). -/
def auxDVA (aty : AuxType) (i : Int64) : DV :=
  match aty with
  | .ARM64BitField | .FlagConstant => .int i.toInt
  | _ => auxIntDVL aty i

mutual
def bindsA (tabs : Tables) (e : PEnv) (p : Path) : Pat → List (Nat × DV)
  | .wild | .same _ => []
  | .bind x => [(x, .val (e.leaf p) (some p))]
  | pat@(.op o name ty ai _ _ args _) =>
    (match name with | some x => [(x, .val (Pat.denL tabs e p pat) (some p))] | none => []) ++
    (match ty with | .bind x => [(x, .ty (e.ty p))] | _ => []) ++
    (match ai with | .bind x => [(x, auxDVA o.auxType (e.auxInt p))] | _ => []) ++
    bindssA tabs e p 0 args
def bindssA (tabs : Tables) (e : PEnv) (p : Path) (i : Nat) : List Pat → List (Nat × DV)
  | [] => []
  | q :: qs => bindsA tabs e (i :: p) q ++ bindssA tabs e p (i + 1) qs
end

def sigmaA (tabs : Tables) (e : PEnv) (pat : Pat) (x : Nat) : DV :=
  ((bindsA tabs e [] pat).lookup x).getD .other

mutual
def consB (ev : GoFV.Rules.Expr → DV) (σ : Nat → DV) (e : PEnv) (p : Path) : Pat → Bool
  | .wild | .bind _ => true
  | .same x => match σ x with
    | .val w _ => e.leaf p == w
    | _ => true
  | .op o _ ty ai _ _ args _ =>
    (match ty with | .eq te => dvBeq (.ty (e.ty p)) (ev te) | _ => true) &&
    (match ai with | .eq ae => dvBeq (auxDVA o.auxType (e.auxInt p)) (ev ae) | _ => true) &&
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

def copyShapeB (ev : GoFV.Rules.Expr → DV) (e : PEnv) : Result → Bool
  | .copy ce => match ev ce with
    | .val _ (some p) => GoFV.Opt.RewriteCheck.copyCompat (e.ty p) (e.ty [])
    | _ => true
  | _ => true

mutual
def patPos (p : Path) : Pat → List (Path × Pat)
  | pat@(.op _ _ _ _ _ _ args _) => (p, pat) :: patsPos p 0 args
  | pat => [(p, pat)]
def patsPos (p : Path) (i : Nat) : List Pat → List (Path × Pat)
  | [] => []
  | q :: qs => patPos (i :: p) q ++ patsPos p (i + 1) qs
end

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

def oracle (b calls lits : Bool) (k : Int64) (vv : Val) : Oracle where
  dv x := match x with
    | .call .. => .bool calls
    | .lit .. => .bool lits
    | _ => .bool b
  ty _ := .other
  auxInt _ := k
  aux _ := none
  val _ := vv

instance : Inhabited DV := ⟨.other⟩

/-- The panic marker: a helper Go would panic in (`armBFAuxInt` out of range, …). -/
def panicDV : DV := .strct [("__panic", .bool true)]

def exOk (r : Except String Int) : DV :=
  match r with
  | .ok k => .int k
  | .error _ => panicDV

/-- The arm64 helpers `evalE` leaves to the oracle, evaluated as `GoFV.Rules.Eval` does. -/
partial def armDV (vtys : List GoTy) (σ : Nat → DV) (base : Oracle) (e : PEnv) (top : Val)
    (x : GoFV.Rules.Expr) : DV :=
  let or : Oracle := { base with dv := armDV vtys σ base e top }
  let ev := evalE vtys σ or e top
  match x with
  | .call fn args _ =>
    match fn, args.map ev with
    | "armBFAuxInt", [.int l, .int w] => exOk (GoFV.Rules.Arm64.armBFAuxInt l w)
    | "isARM64BFMask", [.int l, .int m, .int r] => .bool (GoFV.Rules.Arm64.isARM64BFMask l m r)
    | "arm64BFWidth", [.int m, .int r] => exOk (GoFV.Rules.Arm64.arm64BFWidth m r)
    | "rotateRight64", [.int v, .int r] => .int (GoFV.Rules.Arm64.rotateRight64 v r)
    | "isARM64bitcon", [.int v] => .bool (GoFV.Rules.Arm64.isARM64bitcon v)
    | "isARM64addcon", [.int v] => .bool (GoFV.Rules.Arm64.isARM64addcon v)
    | "addFlags64", [.int a, .int b] => .int (GoFV.Rules.Arm64.addFlags64 a b)
    | "subFlags64", [.int a, .int b] => .int (GoFV.Rules.Arm64.subFlags64 a b)
    | "addFlags32", [.int a, .int b] => .int (GoFV.Rules.Arm64.addFlags32 a b)
    | "subFlags32", [.int a, .int b] => .int (GoFV.Rules.Arm64.subFlags32 a b)
    | "logicFlags64", [.int a] => .int (GoFV.Rules.Arm64.logicFlags64 a)
    | "logicFlags32", [.int a] => .int (GoFV.Rules.Arm64.logicFlags32 a)
    | "b2i", [.bool b] => .int (if b then 1 else 0)
    | "arm64Negate", [.op o] => match GoFV.Rules.Arm64.arm64Negate o with
      | .ok o => .op o
      | .error _ => panicDV
    | "arm64Invert", [.op o] => match GoFV.Rules.Arm64.arm64Invert o with
      | .ok o => .op o
      | .error _ => panicDV
    | _, _ => base.dv x
  | .method y n [] _ =>
    match ev y, n with
    | .int i, "lsb" => .int (GoFV.Rules.Arm64.bfLsb i)
    | .int i, "width" => .int (GoFV.Rules.Arm64.bfWidth i)
    | .int i, n => match GoFV.Rules.Arm64.fcMethod? n i with
      | some b => .bool b
      | none => base.dv x
    | _, _ => base.dv x
  | _ => base.dv x

def armOracle (vtys : List GoTy) (σ : Nat → DV) (base : Oracle) (e : PEnv) (top : Val) : Oracle :=
  { base with dv := armDV vtys σ base e top }

/-- Some auxint expression of the result evaluates to the panic marker. -/
def resPanics (ev : GoFV.Rules.Expr → DV) : Result → Bool
  | .build nodes => nodes.any fun n =>
      (match n.auxInt with | some ae => dvBeq (ev ae) panicDV | none => false)
  | _ => false

def isFlags (v : Val) : Bool :=
  match v with
  | .agg [.bool _, .bool _, .bool _, .bool _, _] => true
  | _ => false

partial def shapeOf : Val → Ty
  | .int w _ => .int w
  | .bool _ => .bool
  | .mem _ => .mem
  | .tuple vs => .tuple (vs.map shapeOf)
  | .ptr _ => .ptr none
  | v@(.agg vs) => if isFlags v then Ty.flags else
      .agg (((List.range vs.length).zip vs).map fun (i, v) => (8 * i, shapeOf v)) (8 * vs.length)
  | .blob _ | .poison => .other
  | .empty => .empty

def tyOfTyp : String → Ty
  | "Int8" | "UInt8" => .int .w8
  | "Int16" | "UInt16" => .int .w16
  | "Int32" | "UInt32" => .int .w32
  | "Int64" | "UInt64" | "Int" | "UInt" | "Uintptr" => .int .w64
  | "Bool" => .bool
  | "Flags" => Ty.flags
  | _ => .other

def opWidths (o : Op) : List Width :=
  let groups := (o.name.splitOn "x").flatMap (·.splitOn "to")
  groups.filterMap fun g =>
    match String.ofList (g.toList.filter Char.isDigit) with
    | "8" => some .w8 | "16" => some .w16 | "32" => some .w32 | "64" => some .w64
    | _ => none

def argHint (o : Op) (i : Nat) : Option Width :=
  match opWidths o with
  | [w] => some w
  | [a, b] => if (o.name.splitOn "x").length > 1 then some (if i == 1 then b else a) else some a
  | _ => none

def isBoolOp (o : Op) : Bool :=
  ["AndB", "OrB", "EqB", "NeqB", "Not"].contains o.name

def intPool : Array Int :=
  #[0, 1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 255, 256, 1000,
    32767, 32768, 65535, 65536, 2147483647, 2147483648, 4294967295, 4294967296,
    9223372036854775807, -1, -2, -3, -8, -16, -128, -129, -32768, -2147483648,
    -9223372036854775808, 0xff, 0xffff, 0xffffffff, 0x80, 0x8000, 0x80000000, 0xff00, 0xf0f0,
    0x7fffffff, 0x100000000, -0x80000001]

def pick {α} [Inhabited α] (xs : Array α) : IO α := do
  return xs[← IO.rand 0 (xs.size - 1)]!

def randInt : IO Int := do
  match ← IO.rand 0 5 with
  | 0 => return Int.ofNat (← IO.rand 0 1000000) - 500000
  | 1 => return Int.ofNat (← IO.rand 0 70)
  | 2 =>
    let hi := Int.ofNat (← IO.rand 0 0xffffffff)
    let lo := Int.ofNat (← IO.rand 0 0xffffffff)
    return (hi * 0x100000000 + lo) - (if (← IO.rand 0 1) == 0 then 0 else 2 ^ 63)
  | 3 =>
    -- a mask 2^k - 1 shifted
    let k ← IO.rand 1 64
    let s ← IO.rand 0 63
    return ((2 ^ k - 1) * 2 ^ s) % (2 ^ 64) - (if (← IO.rand 0 1) == 0 then 0 else 2 ^ 64)
  | _ => pick intPool

def randWidth : IO Width := pick #[.w8, .w16, .w32, .w64, .w64, .w64]

def randFlags : IO Val := do
  let b := fun _ => do return Val.bool ((← IO.rand 0 1) == 1)
  return .agg [← b (), ← b (), ← b (), ← b (), ← b ()]

/-- Is argument `i` of arm64 op `o` a register input (else flags or memory)? Float register? -/
def armArg (o : Op) (i : Nat) : Option Bool :=
  match o.regInfo.inputs.find? (·.idx == i) with
  | some r => some (r.regs.v1 &&& 0xffffffff == 0)
  | none => none

def randLeaf (o : Option Op) (i : Nat) : IO Val := do
  match o with
  | some o =>
    if !o.generic then
      match armArg o i with
      | none => return ← randFlags
      | some _ =>
        let w ← randWidth
        return .int w (BitVec.ofInt w.bits (← randInt))
    let boolish := isBoolOp o || (o.name == "CondSelect" && i == 2)
    if boolish then return .bool ((← IO.rand 0 1) == 1)
    let w ← match argHint o i with
      | some w => if (← IO.rand 0 4) == 0 then randWidth else pure w
      | none => randWidth
    return .int w (BitVec.ofInt w.bits (← randInt))
  | none =>
    let w ← randWidth
    return .int w (BitVec.ofInt w.bits (← randInt))

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

def nodesOf (pos : List (Path × Pat)) : List (Path × Pat) :=
  let ns := pos.filter fun (_, q) => match q with | .op .. => true | _ => false
  (ns.toArray.qsort (fun a b => a.1.length > b.1.length)).toList

def typeLeaves (pos : List (Path × Pat)) (i : Inst) : Inst := Id.run do
  let mut i := i
  for (p, q) in pos do
    match q with
    | .op .. => pure ()
    | _ => i := { i with ty := set i.ty p (shapeOf (i.env.leaf p)) }
  return i

def tabs : Tables := default

def solve (r : Rule) (pos : List (Path × Pat)) (or : Oracle) (i : Inst) : Inst := Id.run do
  let mut i := typeLeaves pos i
  for (p, q) in nodesOf pos do
    match q with
    | .op o _ _ _ _ _ args _ =>
      let e := i.env
      let raw := opValL tabs o (e.ty p) (e.auxInt p) none (Pat.densL tabs e p 0 args)
      let t := match raw, e.ty p with
        | .poison, .other => tyOfTyp o.typ
        | .poison, t => t
        | .int _ _, .int w => .int w
        | v, _ => shapeOf v
      i := { i with ty := set i.ty p t }
    | _ => pure ()
  let e := i.env
  let σ := sigmaA tabs e r.pat
  let top := Pat.denL tabs e [] r.pat
  let or := armOracle (r.vars.map (·.ty)) σ or e top
  let ev := evalE (r.vars.map (·.ty)) σ or e top
  for (p, q) in pos do
    match q with
    | .op o _ ty ai _ _ _ _ =>
      if let .eq te := ty then
        if let .ty t := ev te then i := { i with ty := set i.ty p t }
      if let .eq ae := ai then
        match ev ae with
        | .int k => i := { i with auxInt := set i.auxInt p (Int64.ofInt k) }
        | .bool b => i := { i with auxInt := set i.auxInt p (if b then 1 else 0) }
        | .op c => if o.auxType == .CCop then
            i := { i with auxInt := set i.auxInt p (Int64.ofNat c.goNum) }
        | _ => pure ()
    | .same x =>
      if let .val w _ := σ x then i := { i with leaf := set i.leaf p w }
    | _ => pure ()
  return typeLeaves pos i

/-- `some (ok, res)` when every hypothesis holds and the matched value is defined. -/
def check (r : Rule) (or : Oracle) (i : Inst) : Option (Bool × Val × Val) :=
  let e := i.env
  let σ := sigmaA tabs e r.pat
  let top := Pat.denL tabs e [] r.pat
  let or := armOracle (r.vars.map (·.ty)) σ or e top
  let ev := evalE (r.vars.map (·.ty)) σ or e top
  let raw := (Pat.rawL tabs e r.pat).retypeL (e.ty [])
  let ok := Pat.arityOk r.pat && wfB e [] r.pat && consB ev σ e [] r.pat && condB ev r.cond &&
    typedB e [] r.pat && Pat.argsOK e.ty [] r.pat && Pat.topOKL (e.ty []) r.pat &&
    argsOKLr r.loc e.ty r.pat && copyShapeB ev e r.result && resFitsL (e.ty []) r.result &&
    Pat.addrOKL e.ty e.aux e.auxInt [] r.pat &&
    !(match raw with | .poison => true | _ => false)
  if ok then
    let res := resDenL tabs e r.pat ev or σ (e.ty []) r.result
    if resPanics ev r.result then some (false, raw, .blob []) else
    some (refinesB raw res, raw, res)
  else none

def render (i : Inst) : String :=
  let ls := i.leaf.map fun (p, v) => s!"{p.reverse}={v.render}"
  let ts := i.ty.filter (fun (p, _) => p.isEmpty) |>.map fun (_, t) => s!"top:{repr t}"
  let as := i.auxInt.filter (·.2 != 0) |>.map fun (p, a) => s!"{p.reverse}:[{a.toInt}]"
  " ".intercalate (ls ++ as ++ ts)

def randAux (o : Op) : IO Int64 := do
  match o.auxType with
  | .Bool => return Int64.ofInt (← IO.rand 0 1)
  | .ARM64BitField =>
    let lsb ← IO.rand 0 63
    let w ← IO.rand 1 (64 - lsb)
    return Int64.ofNat (w + lsb * 256)
  | .CCop => return Int64.ofNat (← pick GoFV.Rules.Derive.condOps.toArray).goNum
  | .FlagConstant => return Int64.ofNat (← IO.rand 0 15)
  | _ =>
    -- shift amounts: Go only builds them in range (`[c&63]`, `[c&31]`)
    let n := o.name
    if (n.splitOn "shift").length > 1 || n == "SLLconst" || n == "SRLconst" ||
        n == "SRAconst" || n == "RORconst" || n == "EXTRconst" then
      return Int64.ofNat (← IO.rand 0 63)
    if n == "RORWconst" || n == "EXTRWconst" then return Int64.ofNat (← IO.rand 0 31)
    return Int64.ofInt (← randInt)

def randTy (o : Op) : IO Ty := do
  if o.generic then return tyOfTyp o.typ
  match ← IO.rand 0 5 with
  | 0 => return .int .w32
  | 1 => return .int (← randWidth)
  | _ => return .int .w64

def search (r0 : Rule) (trials : Nat) : IO (Option (String × Inst)) := do
  let sws := GoFV.Opt.RewriteCheck.choices (GoFV.Opt.RewriteCheck.Pat.commutes r0.pat)
  let mut sat : Option Inst := none
  for t in [0:trials] do
    let sw ← pick sws.toArray
    let r := Rule.swapC r0 sw
    let pos := patPos [] r.pat
    let hints := leafHints pos
    let b := t % 2 == 0
    let or := oracle b (if t % 4 == 2 then false else b) (if t % 8 ≥ 4 then !b else b) 0 .poison
    let or2 := oracle b (if t % 4 == 2 then false else b) (if t % 8 ≥ 4 then !b else b) 77777
      (.int .w64 0x5a5a5a5a)
    let mut i : Inst := {}
    for (p, o, k) in hints do
      i := { i with leaf := set i.leaf p (← randLeaf o k) }
    for (p, q) in pos do
      if let .op o .. := q then
        i := { i with auxInt := set i.auxInt p (← randAux o), ty := set i.ty p (← randTy o) }
    for _ in [0:3] do
      i := solve r pos or i
    match check r or i, check r or2 i with
    | some (true, _, _), some (true, _, _) => sat := sat <|> some i
    | some (false, raw, res), some (false, _, res2) =>
      if res == res2 then
        return some (s!"CEX {render i} src={raw.render} tgt={res.render}", i)
      else return some (s!"ORACLE {render i} src={raw.render} tgt={res.render}", i)
    | some (a, raw, res), some (b, _, _) =>
      if a != b then return some (s!"ORACLE {render i} src={raw.render} tgt={res.render}", i)
    | _, _ => pure ()
  return sat.map fun i => ("SAT", i)

def files : List RuleSet :=
  [Generated.ARM64.ruleSet, Generated.ARM64latelower.ruleSet]

def main (args : List String) : IO UInt32 := do
  let trials := (args.find? (·.startsWith "--trials=")).bind (·.drop 9 |>.toNat?) |>.getD 4000
  let only := args.filter (!·.startsWith "--")
  IO.setRandSeed 385
  let mut stats := (0, 0, 0)
  for rs in files do
    for (o, rules) in rs.values do
      for (r, k) in rules.zipIdx do
        let key := s!"{r.loc.file}:{r.loc.line} {o.name}#{k}"
        if !only.isEmpty && !only.contains s!"{r.loc.file}:{r.loc.line}" then continue
        match r.result with
        | .setOp _ => IO.println s!"{key} SKIP setOp"; continue
        | _ => pure ()
        match ← search r trials with
        | some (s, _) =>
          IO.println s!"{key} {s}"
          if s == "SAT" then stats := (stats.1 + 1, stats.2.1, stats.2.2)
          else stats := (stats.1, stats.2.1 + 1, stats.2.2)
        | none =>
          IO.println s!"{key} NONE"
          stats := (stats.1, stats.2.1, stats.2.2 + 1)
        (← IO.getStdout).flush
  IO.eprintln s!"SAT {stats.1}, CEX/ORACLE {stats.2.1}, NONE {stats.2.2}"
  return 0

end GoFVTest.ArmSat

def main (args : List String) : IO UInt32 := GoFVTest.ArmSat.main args

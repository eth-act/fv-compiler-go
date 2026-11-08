import GoFV.Rules.Generated.ARM64
import GoFV.Rules.Generated.ARM64latelower
import GoFV.Proof.Low.RuleL
import GoFV.Rules.Derive
import GoFV.SSA.OpARM64

/-!
# Random counterexample search for `ARM64.rules` / `ARM64latelower.rules` (`lake exe arm-sat`)

`RuleSat` for the lowering obligations of `GoFV/Proof/Low/RuleL.lean` (docs/proofs/rules.md,
"Non-vacuity"): random instances of each rule, every hypothesis checked as a `Bool`, and the
result compared with `Refines` (memories with `Mem.Refines`).

* Value rules: `ArmRule.Sound1` (each commutation choice at random). The denotation (`opValX`)
  is `opValL` plus the memory ops `runL` evaluates with the activation (`arm64Op`: loads,
  stores, pair and indexed stores, without symbols) and Phase 1's `Zero`/`Move`; for a pattern
  with a memory op the register-width and top-shape premises (made for register results) are
  waived.
* Ellipsis rules `(o ...) => (o' ...)`: `SetOpSoundT` on random arguments at `o`'s natural
  shape.
* Block rules on one control: `BlockRuleL.Sound` (a bound block auxint gets a bit number).

Leaves by their consumer (`leafRole`): integers, booleans, flags, float bit patterns, pointers
into a random two-block heap memory (as their address words), memories. The arm64 helpers
`evalE` leaves to the oracle (`armBFAuxInt`, the bit-field accessors, the `flagConstant`
methods, …) are evaluated as `GoFV.Rules.Eval` does; a helper panic in a result auxint is a
`CEX`. Lines: `<file>:<line> <op>#k [SETOP|BLOCK] SAT|CEX <instance>|ORACLE <instance>|NONE`
(`ORACLE`: the verdict depends on an unmodelled atom). `--debug` prints the failing hypotheses
of the first trials of each value rule; `ARMSAT_RELAX=1` waives the register-width premise
`argsOKLr` (more instances, and `CEX`es where an op reads bits a narrow register leaves undefined).
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
  | .f64 a, .f64 b => a == b
  | .f32 a, .f32 b => a == b
  | .int a, .f64 b => a == b.toInt
  | .f64 a, .int b => a.toInt == b
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

/-- `Mem.Refines` as a `Bool`: the same allocations, bytewise (`poison` refines any byte). -/
def memRefinesB (m n : Mem) : Bool :=
  m.blocks.size == n.blocks.size &&
    (m.blocks.zip n.blocks).all fun ((b, a), (c, d)) =>
      b == c && a.writable == d.writable && a.data.size == d.data.size &&
        (a.data.zip d.data).all fun (x, y) => x == .poison || x == y

partial def refinesB : Val → Val → Bool
  | .poison, _ => true
  | .tuple as, .tuple bs | .agg as, .agg bs =>
    as.length == bs.length && (as.zip bs).all fun (a, b) => refinesB a b
  | .mem m, .mem n => memRefinesB m n
  | .blob as, .blob bs => as.length == bs.length && (as.zip bs).all fun (x, y) => x == .poison || x == y
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
  | .glob "types.TypeFlags" _ => .ty Ty.flags
  | .method (.field y "Type" _) "Size" [] _ =>
    match ev y with
    | .val _ (some p) => match shapeSize (e.ty p) with
      | some k => .int k
      | none => base.dv x
    | _ => base.dv x
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
  | "Mem" => .mem
  | "Float32" => .int .w32
  | "Float64" => .int .w64
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

def hasSub (s t : String) : Bool := (s.splitOn t).length > 1

/-- An arm64 op that reads or writes memory (its non-register argument is the memory). -/
def armMemOp (o : Op) : Bool :=
  let n := o.name
  ["load", "store", "LDP", "STP", "LDAR", "STLR", "Zero", "Move", "PRFM", "DMB", "CALL",
   "PanicBounds", "NilCheck", "MemEq", "Atomic", "LoweredWB", "LDAXR", "STLXR"].any (hasSub n)

inductive Role where
  | mem | ptr | flags | int | float | bool | idx
  deriving BEq, Inhabited

/-- What kind of value argument `i` of `o` holds. -/
def leafRole (o : Op) (i : Nat) : Role :=
  if o.generic then
    match o.name, i with
    | "Load", 0 | "Store", 0 | "Zero", 0 | "Move", 0 | "Move", 1 | "NilCheck", 0
    | "OffPtr", 0 | "AddPtr", 0 | "PtrIndex", 0 | "IsNonNil", 0 | "EqPtr", _ | "NeqPtr", _
    | "LocalAddr", 0 | "Addr", 0 => .ptr
    | "Load", 1 | "Store", 2 | "Zero", 1 | "Move", 2 | "NilCheck", 1 | "LocalAddr", 1 => .mem
    | n, _ =>
      if isBoolOp o || (n == "CondSelect" && i == 2) then .bool
      else if hasSub n "PanicBounds" && i + 1 == o.argLen.toNat then .mem
      else if hasSub n "32F" || hasSub n "64F" then .float
      else .int
  else
    match armArg o i with
    | none => if armMemOp o then .mem else .flags
    | some true => .float
    | some false =>
      if armMemOp o && (i == 0 || (hasSub o.name "Move" && i == 1)) then .ptr
      else if armMemOp o && hasSub o.name "idx" && i == 1 then .idx else .int

def randBytes (n : Nat) : IO (Array Byte) := do
  let mut d := #[]
  for _ in [0:n] do d := d.push (.b (BitVec.ofNat 8 (← IO.rand 0 255)))
  return d

/-- A memory of two 64-byte heap blocks of random bytes. -/
def randMem : IO Mem := do
  return { blocks := #[(.heap 0, { data := ← randBytes 320 }), (.heap 1, { data := ← randBytes 320 })],
           nextHeap := 2 }

/-- A pointer into one of `randMem`'s blocks, as a register holds it (`Ptr.word`: a convertible
pointer is its address word, `Val.hasTy`). -/
def randPtr : IO Val := do
  return Ptr.word ⟨.heap (← IO.rand 0 1), BitVec.ofNat 64 (← pick #[0, 0, 0, 8, 16, 24, 32, 3, 5, 12])⟩

/-- Float bit patterns: zeros, infinities, quiet and signalling NaNs of both signs, normals. -/
def randFloat (w : Width) : IO Val := do
  let pats64 : Array Nat := #[0, 0x8000000000000000, 0x7ff0000000000000, 0xfff0000000000000,
    0x7ff8000000000001, 0xfff8000000000002, 0x7ff0000000000003, 0xfff0000000000004,
    0x3ff0000000000000, 0xbff0000000000000, 0x0000000000000001, 0x4000000000000000]
  let pats32 : Array Nat := #[0, 0x80000000, 0x7f800000, 0xff800000, 0x7fc00001, 0xffc00002,
    0x7f800003, 0xff800004, 0x3f800000, 0xbf800000, 0x00000001, 0x40000000]
  let w ← if (← IO.rand 0 3) == 0 then pure (if w == .w64 then .w32 else .w64) else pure w
  if (← IO.rand 0 2) == 0 then return .int w (BitVec.ofInt w.bits (← randInt))
  let x ← pick (if w == .w64 then pats64 else pats32)
  return .int w (BitVec.ofNat w.bits x)

def randRole (o : Op) (r : Role) : IO Val := do
  match r with
  | .mem => return .mem (← randMem)
  | .ptr => if (← IO.rand 0 7) == 0 then return .int .w64 (BitVec.ofInt 64 (← randInt)) else randPtr
  | .flags => randFlags
  | .bool => return .bool ((← IO.rand 0 1) == 1)
  | .idx =>
    if (← IO.rand 0 3) == 0 then return .int .w64 (BitVec.ofInt 64 (← randInt))
    return .int (← pick #[.w64, .w64, .w32]) (BitVec.ofNat _ (← IO.rand 0 12))
  | .float => randFloat (if hasSub o.name "32F" || hasSub o.name "S" then .w32 else .w64)
  | .int =>
    let w ← match (if o.generic then argHint o 0 else none) with
      | some w => if (← IO.rand 0 4) == 0 then randWidth else pure w
      | none => randWidth
    return .int w (BitVec.ofInt w.bits (← randInt))

def randLeaf (o : Option Op) (i : Nat) : IO Val := do
  match o with
  | some o =>
    if o.generic && leafRole o i == .int then
      let w ← match argHint o i with
        | some w => if (← IO.rand 0 4) == 0 then randWidth else pure w
        | none => randWidth
      return .int w (BitVec.ofInt w.bits (← randInt))
    randRole o (leafRole o i)
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

/-- The name of the rule variable bound at `p`. -/
def varAt (r : Rule) (p : Path) : Option String :=
  match (patPos [] r.pat).lookup p with
  | some (.bind x) => r.vars[x]?.map (·.name)
  | _ => none

/-- A leaf: by its consumer, or a pointer when the rule names it as one (`ptr`, `dst`, …). -/
def leafFor (r : Rule) (p : Path) (o : Option Op) (k : Nat) : IO Val := do
  let ptrName := match varAt r p with
    | some n => ["ptr", "p", "dst", "src", "base", "idx0", "p1", "p2", "p3", "ptr0", "ptr1"].contains n
    | none => false
  let memInt := match o with
    | some o => armMemOp o && leafRole o k == .int
    | none => false
  if (ptrName && (← IO.rand 0 4) != 0) || (memInt && (← IO.rand 0 3) == 0) then randPtr
  else randLeaf o k

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

/-- `retypeL`, keeping `Vec128` blobs (whose type shape the tables here do not know). -/
def retypeX (t : Ty) (v : Val) : Val :=
  match v with
  | .blob _ | .mem _ => v
  | .tuple _ => match t with
    | .tuple _ => v.retypeL t
    | _ => v
  | v => v.retypeL t

def addrA (ai : Int64) (a : Val) : Option Ptr := Arm64.addr a (BitVec.ofInt 64 ai.toInt)

def memOr : Option Mem → Val
  | some m => .mem m
  | none => .poison

/-- `opValL` plus the memory ops `runL` evaluates with the activation (`arm64Op`, without a
symbol: `symAddr` is `Arm64.addr`), and Phase 1's `Zero`/`Move` roots (`memRoot`). An invalid
write is `poison` (the source's is `stuck`, which carries no obligation). -/
def opValX (op : Op) (ty : Ty) (ai : Int64) (ax : Option AuxRef) (args : List Val) : Val :=
  let ld (n : Nat) (s : Bool) := match args with
    | [a, .mem m] => (addrA ai a).elim .poison (Arm64.loadN ty n s m)
    | _ => .poison
  let ldPair (n : Nat) (s : Bool) := match args with
    | [a, .mem m] => match addrA ai a, addrA (ai + Int64.ofNat n) a with
      | some p, some q => Arm64.loadPair ty n s m p q
      | _, _ => .poison
    | _ => .poison
  let st (n : Nat) := match args with
    | [a, x, .mem m] => match addrA ai a with
      | some p => memOr (Arm64.storeN n p x m)
      | none => .poison
    | _ => .poison
  let stPair (n : Nat) := match args with
    | [a, x, y, .mem m] => match addrA ai a, addrA (ai + Int64.ofNat n) a with
      | some p, some q => memOr (Arm64.storePair n p q x y m)
      | _, _ => .poison
    | _ => .poison
  let stIdx (n scale : Nat) := match args with
    | [a, i, x, .mem m] =>
      let s := if scale = 1 then Arm64.add .other [a, i] else
        match Arm64.reg i with
        | some k => Arm64.add .other [a, .int .w64 (k * BitVec.ofNat 64 scale)]
        | none => .poison
      match Arm64.addr s 0 with
      | some p => memOr (Arm64.storeN n p x m)
      | none => .poison
    | _ => .poison
  let big := ai.toInt < 0 || ai.toInt > 4096
  match op with
  | .Zero | .Move | .ARM64LoweredZero | .ARM64LoweredZeroLoop | .ARM64LoweredMove
  | .ARM64LoweredMoveLoop =>
    if big then .poison else match op with
    | .Zero => match args with
      | [a, .mem m] => match a.asPtrWord with
        | some p => memOr (m.write p (Array.replicate ai.toInt.toNat (.b 0)))
        | none => .poison
      | _ => .poison
    | .Move => match args with
      | [a, b, .mem m] => match a.asPtrWord, b.asPtrWord with
        | some d, some s => match m.read s ai.toInt.toNat with
          | some bs => memOr (m.write d bs)
          | none => .poison
        | _, _ => .poison
      | _ => .poison
    | op => opValL tabs op ty ai ax args
  | .ARM64FMOVSload => ld 4 false
  | .ARM64FMOVDload => ld 8 false
  | .ARM64FMOVQload => match args with
    | [a, .mem m] => (addrA ai a).elim .poison (Arm64.load16 m)
    | _ => .poison
  | .ARM64LDP => ldPair 8 false
  | .ARM64LDPW => ldPair 4 false
  | .ARM64LDPSW => ldPair 4 true
  | .ARM64FLDPD => ldPair 8 false
  | .ARM64FLDPS => ldPair 4 false
  | .ARM64FLDPQ => ldPair 16 false
  | .ARM64MOVBstore => st 1
  | .ARM64MOVHstore => st 2
  | .ARM64MOVWstore => st 4
  | .ARM64MOVDstore => st 8
  | .ARM64FMOVSstore => st 4
  | .ARM64FMOVDstore => st 8
  | .ARM64FMOVQstore => st 16
  | .ARM64STP => stPair 8
  | .ARM64STPW => stPair 4
  | .ARM64FSTPD => stPair 8
  | .ARM64FSTPS => stPair 4
  | .ARM64FSTPQ => stPair 16
  | .ARM64MOVBstoreidx => stIdx 1 1
  | .ARM64MOVHstoreidx => stIdx 2 1
  | .ARM64MOVWstoreidx => stIdx 4 1
  | .ARM64MOVDstoreidx => stIdx 8 1
  | .ARM64FMOVSstoreidx => stIdx 4 1
  | .ARM64FMOVDstoreidx => stIdx 8 1
  | .ARM64MOVHstoreidx2 => stIdx 2 2
  | .ARM64MOVWstoreidx4 => stIdx 4 4
  | .ARM64MOVDstoreidx8 => stIdx 8 8
  | .ARM64FMOVSstoreidx4 => stIdx 4 4
  | .ARM64FMOVDstoreidx8 => stIdx 8 8
  | .ARM64DMB => match args with
    | [.mem m] => .mem m
    | _ => .poison
  | .ARM64PRFM => match args with
    | [_, .mem m] => .mem m
    | _ => .poison
  | .PrefetchCache | .PrefetchCacheStreamed => match args with
    | [_, .mem m] => .mem m
    | _ => .poison
  | .Select0 | .Select1 => match args with
    | [.tuple (a :: b :: _)] => if op == .Select0 then a else b
    | _ => opValL tabs op ty ai ax args
  | .PubBarrier => match args with
    | [.mem m] => .mem m
    | _ => .poison
  | op => opValL tabs op ty ai ax args

mutual
def denX (e : PEnv) (p : Path) : Pat → Val
  | .op o _ _ _ _ _ args _ =>
    retypeX (e.ty p) (opValX o (e.ty p) (e.auxInt p) (e.aux p) (densX e p 0 args))
  | _ => e.leaf p
def densX (e : PEnv) (p : Path) (i : Nat) : List Pat → List Val
  | [] => []
  | q :: qs => denX e (i :: p) q :: densX e p (i + 1) qs
end

def rawX (e : PEnv) : Pat → Val
  | .op o _ _ _ _ _ args _ => opValX o (e.ty []) (e.auxInt []) (e.aux []) (densX e [] 0 args)
  | _ => e.leaf []

mutual
def bindsX (e : PEnv) (p : Path) : Pat → List (Nat × DV)
  | .wild | .same _ => []
  | .bind x => [(x, .val (e.leaf p) (some p))]
  | pat@(.op o name ty ai _ _ args _) =>
    (match name with | some x => [(x, .val (denX e p pat) (some p))] | none => []) ++
    (match ty with | .bind x => [(x, .ty (e.ty p))] | _ => []) ++
    (match ai with | .bind x => [(x, auxDVA o.auxType (e.auxInt p))] | _ => []) ++
    bindssX e p 0 args
def bindssX (e : PEnv) (p : Path) (i : Nat) : List Pat → List (Nat × DV)
  | [] => []
  | q :: qs => bindsX e (i :: p) q ++ bindssX e p (i + 1) qs
end

def sigmaX (e : PEnv) (pat : Pat) (x : Nat) : DV :=
  ((bindsX e [] pat).lookup x).getD .other

def nodeDenX (e : PEnv) (pat : Pat) (ev : Expr → DV) (or : Oracle) (σ : Nat → DV) (topTy : Ty)
    (nodes : List RNode) : Nat → Nat → Val
  | 0, _ => .poison
  | fuel + 1, k =>
    match nodes[k]? with
    | none => .poison
    | some n =>
      let t := nodeTyL ev or topTy n.ty
      let ai := match n.auxInt with
        | some ae => (toAuxIntL n.op.auxType (ev ae)).getD (or.auxInt ae)
        | none => 0
      let ax := nodeAuxL e pat or n.aux
      let argv := n.args.map fun
        | .var x => (σ x).valOr (or.val (.var x))
        | .node j => nodeDenX e pat ev or σ topTy nodes fuel j
        | .expr e => (ev e).valOr (or.val e)
      if n.op == .ARM64MOVDreg || n.op == .ARM64MOVDnop then
        -- `arm64Op`: the register of `x`, sign-extended if its producer sign-extends
        let sx := match n.args with
          | [.var x] => (patPos [] pat).any fun (_, q) => match q with
            | .op o (some y) .. => y == x && Arm64.signExtends o
            | _ => false
          | _ => false
        match argv with
        | [Val.int _ v] => retypeX t (Arm64.res t (if sx then v.signExtend 64 else v.setWidth 64))
        | [a] => retypeX t (Arm64.regVal t a)
        | _ => Val.poison
      else
      retypeX t (opValX n.op t ai ax argv)

def resDenX (e : PEnv) (pat : Pat) (ev : Expr → DV) (or : Oracle) (σ : Nat → DV) (topTy : Ty) :
    Result → Val
  | .copy ce => (ev ce).valOr (or.val ce)
  | .build nodes => nodeDenX e pat ev or σ topTy nodes nodes.length 0
  | .setOp o => or.val (.op o)

def solve (r : Rule) (pos : List (Path × Pat)) (or : Oracle) (i : Inst) : Inst := Id.run do
  let mut i := typeLeaves pos i
  for (p, q) in nodesOf pos do
    match q with
    | .op o _ _ _ _ _ args _ =>
      let e := i.env
      let raw := opValX o (e.ty p) (e.auxInt p) none (densX e p 0 args)
      let t := match raw, e.ty p with
        | .poison, .other => tyOfTyp o.typ
        | .poison, t => t
        | .int _ _, .int w => .int w
        | v, _ => shapeOf v
      i := { i with ty := set i.ty p t }
      -- a constant holds a value of its type (Go's constants are canonical for their type)
      if o == .ARM64MOVDconst then
        if let .int w := t then
          if w != .w64 then
            let k := Int64.ofInt (GoFV.Rules.wrapInt w.bits true (i.env.auxInt p).toInt)
            i := { i with auxInt := set i.auxInt p k }
    | _ => pure ()
  let e := i.env
  let σ := sigmaX e r.pat
  let top := denX e [] r.pat
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
        | .f64 b => i := { i with auxInt := set i.auxInt p (Int64.ofInt b.toInt) }
        | .f32 b =>
          i := { i with auxInt := set i.auxInt p (Int64.ofInt (GoFV.IEEE.convert .b32 .b64 .rne b).toInt) }
        | .op c => if o.auxType == .CCop then
            i := { i with auxInt := set i.auxInt p (Int64.ofNat c.goNum) }
        | _ => pure ()
    | .same x =>
      if let .val w _ := σ x then i := { i with leaf := set i.leaf p w }
    | _ => pure ()
  return typeLeaves pos i

/-- A store (a memory-typed top op): it writes the low bytes of its value register, so the
register-width premise of `argsOKLr` (made for register results) does not apply. -/
def memTop (pat : Pat) : Bool :=
  (patPos [] pat).any fun (_, q) => match q with
    | .op o .. => o.typ == "Mem" || o == .Load || armMemOp o
    | _ => false

/-- `Select0`/`Select1` at the top: a component of the tuple, of the component's shape. -/
def selTop : Pat → Bool
  | .op o .. => o == .Select0 || o == .Select1 || o == .SelectN
  | _ => false

/-- `ARMSAT_RELAX=1`: waive the register-width premise `argsOKLr` everywhere (an op may read more
bits of a narrow register than its shape holds; `Arm64.reg` zero-extends them). -/
initialize relaxRef : IO.Ref Bool ← IO.mkRef false

/-- `some (ok, res)` when every hypothesis holds and the matched value is defined. -/
def check (r : Rule) (or : Oracle) (i : Inst) (relax : Bool := false) : Option (Bool × Val × Val) :=
  let e := i.env
  let σ := sigmaX e r.pat
  let top := denX e [] r.pat
  let or := armOracle (r.vars.map (·.ty)) σ or e top
  let ev := evalE (r.vars.map (·.ty)) σ or e top
  let raw := (rawX e r.pat).retypeL (e.ty [])
  let ok := Pat.arityOk r.pat && wfB e [] r.pat && consB ev σ e [] r.pat && condB ev r.cond &&
    typedB e [] r.pat && Pat.argsOK e.ty [] r.pat && (memTop r.pat || selTop r.pat || Pat.topOKL (e.ty []) r.pat) &&
    (relax || memTop r.pat || argsOKLr r.loc e.ty r.pat) && copyShapeB ev e r.result &&
    resFitsL (e.ty []) r.result &&
    Pat.addrOKL e.ty e.aux e.auxInt [] r.pat &&
    !(match raw with | .poison => true | _ => false)
  if ok then
    let res := resDenX e r.pat ev or σ (e.ty []) r.result
    if resPanics ev r.result then some (false, raw, .blob []) else
    some (refinesB raw res, raw, res)
  else none

/-- Which hypotheses of `check` fail (debugging). -/
def whyNot (r : Rule) (or : Oracle) (i : Inst) : List String :=
  let e := i.env
  let σ := sigmaX e r.pat
  let top := denX e [] r.pat
  let or := armOracle (r.vars.map (·.ty)) σ or e top
  let ev := evalE (r.vars.map (·.ty)) σ or e top
  let raw := (rawX e r.pat).retypeL (e.ty [])
  [("arity", Pat.arityOk r.pat), ("wf", wfB e [] r.pat), ("cons", consB ev σ e [] r.pat),
   ("cond", condB ev r.cond), ("typed", typedB e [] r.pat), ("argsOK", Pat.argsOK e.ty [] r.pat),
   ("topOKL", memTop r.pat || selTop r.pat || Pat.topOKL (e.ty []) r.pat), ("argsOKL", memTop r.pat || argsOKLr r.loc e.ty r.pat),
   ("copyShape", copyShapeB ev e r.result), ("resFits", resFitsL (e.ty []) r.result),
   ("addrOKL", Pat.addrOKL e.ty e.aux e.auxInt [] r.pat),
   ("raw " ++ raw.render, !(match raw with | .poison => true | _ => false))].filterMap
    fun (n, b) => if b then none else some n

def renderByte : Byte → String
  | .b x => toString x.toNat
  | .frag _ k => s!"frag{k}"
  | .poison => "P"

/-- A value, with a memory shown by its bytes that differ from `other`'s. -/
def renderVs (v other : Val) : String :=
  match v, other with
  | .mem m, .mem n =>
    let ds := (m.blocks.zip n.blocks).toList.flatMap fun ((b, a), (_, d)) =>
      ((List.range a.data.size).filter fun k => a.data[k]! != d.data[k]!).map fun k =>
        s!"{Val.renderBlk b}[{k}]={renderByte a.data[k]!}"
    s!"mem({ds.take 12})"
  | v, _ => v.render

def render (i : Inst) : String :=
  let ls := i.leaf.map fun (p, v) => s!"{p.reverse}={v.render}"
  let ts := i.ty.filter (fun (p, _) => p.isEmpty) |>.map fun (_, t) => s!"top:{repr t}"
  let as := i.auxInt.filter (·.2 != 0) |>.map fun (p, a) => s!"{p.reverse}:[{a.toInt}]"
  " ".intercalate (ls ++ as ++ ts)

/-- An auxint in the range of its aux type (Go stores `int32` offsets, `int8` … sign-extended). -/
def wrapAux (o : Op) (k : Int64) : Int64 :=
  match o.auxType with
  | .Int32 | .SymOff | .CallOff => Int64.ofInt (GoFV.Rules.wrapInt 32 true k.toInt)
  | .Int16 => Int64.ofInt (GoFV.Rules.wrapInt 16 true k.toInt)
  | .Int8 => Int64.ofInt (GoFV.Rules.wrapInt 8 true k.toInt)
  | .UInt8 => Int64.ofInt (GoFV.Rules.wrapInt 8 false k.toInt)
  | _ => k

def randAux (o : Op) : IO Int64 := do
  return wrapAux o (← randAux0 o)
where randAux0 (o : Op) : IO Int64 := do
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
    -- offsets and sizes of memory ops: mostly inside the 64-byte blocks
    if (armMemOp o || o.name == "MOVDaddr" || o.name == "OffPtr" || o.name == "Zero" ||
        o.name == "Move") && (← IO.rand 0 3) != 0 then
      if (o.name == "Zero" || o.name == "Move" || hasSub o.name "Lowered") && (← IO.rand 0 1) == 0 then
        return Int64.ofNat (← IO.rand 0 260)
      return Int64.ofInt (Int.ofNat (← IO.rand 0 40) - 8)
    return Int64.ofInt (← randInt)

/-- The shape a generic op produces (`topOKL`): its Go result type, else by its name's widths
(a conversion's target, a shift's operand, a comparison's boolean). -/
def natTy (o : Op) : Ty :=
  if o.typ != "" then tyOfTyp o.typ else
  let n := o.name
  if ["Eq", "Neq", "Less", "Leq", "IsInBounds", "IsSliceInBounds", "IsNonNil"].any (fun (q : String) => n.startsWith q) then .bool
  else if ["Ctz", "BitLen", "PopCount"].any (fun (q : String) => n.startsWith q) then .int .w64
  else match opWidths o with
    | [] => .int .w64
    | [w] => .int w
    | ws => if hasSub n "to" then .int (ws.getLast!) else .int (ws.head!)

def randTy (o : Op) : IO Ty := do
  if o.typ == "Mem" then return .mem
  if o == .ARM64FMOVDgpfp || o == .ARM64FMOVDfpgp then return .int .w64
  if o == .ARM64FMOVSgpfp || o == .ARM64FMOVSfpgp then return .int .w32
  if !o.generic && o.typ == "" then
    return (← pick #[.int .w64, .int .w64, .int .w32])
  if o.generic then
    if o.typ == "" then
      if o == .Select0 || o == .Select1 then return .int .w64
      if (← IO.rand 0 3) != 0 then return natTy o
      return (← pick #[.int .w64, .int .w32, .int .w16, .int .w8, .ptr none, .bool])
    return tyOfTyp o.typ
  match ← IO.rand 0 5 with
  | 0 => return .int .w32
  | 1 => return .int (← randWidth)
  | _ => return .int .w64

def search (r0 : Rule) (trials : Nat) (dbg : Bool := false) : IO (Option (String × Inst)) := do
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
      i := { i with leaf := set i.leaf p (← leafFor r p o k) }
    for (p, q) in pos do
      if let .op o .. := q then
        i := { i with auxInt := set i.auxInt p (← randAux o), ty := set i.ty p (← randTy o) }
        -- an address or index computed for a memory op is a 64-bit register
        if let k :: parent := p then
          if let some (.op po ..) := pos.lookup parent then
            if !o.generic && !po.generic && (leafRole po k == .ptr || leafRole po k == .idx) then
              i := { i with ty := set i.ty p (.int .w64) }
            -- a constant offset or index of a memory op: mostly inside the blocks
            if o == .ARM64MOVDconst && armMemOp po && (← IO.rand 0 1) == 0 then
              i := { i with auxInt := set i.auxInt p (Int64.ofNat (← IO.rand 0 40)) }
    for _ in [0:3] do
      i := solve r pos or i
    if dbg && t < 6 then IO.eprintln s!"  {whyNot r or i} {render i}"
    let relax ← relaxRef.get
    match check r or i relax, check r or2 i relax with
    | some (true, _, _), some (true, _, _) => sat := sat <|> some i
    | some (false, raw, res), some (false, _, res2) =>
      if res == res2 then
        return some (s!"CEX {render i} src={renderVs raw res} tgt={renderVs res raw}", i)
      else return some (s!"ORACLE {render i} src={raw.render} tgt={res.render}", i)
    | some (a, raw, res), some (b, _, _) =>
      if a != b then return some (s!"ORACLE {render i} src={raw.render} tgt={res.render}", i)
    | _, _ => pure ()
  return sat.map fun i => ("SAT", i)

/-- An ellipsis rule `(o ...) => (o' ...)`: the same arguments, type and fields
(`SetOpSoundT`). Random arguments by role; `CEX` when `o'` does not refine `o`. -/
def searchSetOp (o o' : Op) (trials : Nat) : IO String := do
  if o.argLen < 0 then return "SKIP variadic"
  let n := o.argLen.toNat
  let mut sat := false
  for _ in [0:trials] do
    let mut args := #[]
    for i in [0:n] do
      args := args.push (← randLeaf (some o) i)
    let ai ← randAux o
    let ty := natTy o
    let raw := (opValX o ty ai none args.toList).retypeL ty
    if raw matches .poison then continue
    let res := (opValX o' ty ai none args.toList).retypeL ty
    if refinesB raw res then sat := true
    else
      let as := args.toList.map Val.render
      return s!"CEX args={as} [{ai.toInt}] top:{repr ty} src={raw.render} tgt={res.render}"
  return if sat then "SAT" else "NONE"

/-- A block rule on one control (`BlockRuleL.Sound`): random instances of the control pattern;
`CEX` when the old block takes an edge and the new one takes another or gets stuck. -/
def searchBlock (br : BlockRule) (trials : Nat) : IO String := do
  let [pat0] := br.controls | return "SKIP controls"
  if br.kind == .ARM64JUMPTABLE || br.newKind == .ARM64JUMPTABLE then return "SKIP jumptable"
  let sws := GoFV.Opt.RewriteCheck.choices (GoFV.Opt.RewriteCheck.Pat.commutes pat0)
  let r0 : Rule := { loc := br.loc, op := .Invalid, vars := br.vars, pat := pat0, cond := br.cond,
                     block := none, result := .copy (.var 0), pos := [] }
  let mut sat := false
  for t in [0:trials] do
    let sw ← pick sws.toArray
    let pat := (Pat.swapC pat0 sw).1
    let r := { r0 with pat }
    let pos := patPos [] pat
    let b := t % 2 == 0
    let or := oracle b (if t % 4 == 2 then false else b) (if t % 8 ≥ 4 then !b else b) 0 .poison
    let mut i : Inst := {}
    for (p, o, k) in leafHints pos do
      i := { i with leaf := set i.leaf p (← leafFor r p o k) }
    for (p, q) in pos do
      if let .op o .. := q then
        -- block controls read whole registers: arm64 nodes at the 64-bit shape
        let t ← if o.generic then randTy o else pure (.int .w64)
        i := { i with auxInt := set i.auxInt p (← randAux o), ty := set i.ty p t }
    for _ in [0:3] do
      i := solve r pos or i
    let e := i.env
    -- the block auxint: a literal the rule asks for, or a bound variable (`[t]`, a bit number)
    let ai : Int64 ← match br.auxInt with
      | .eq (.lit _ (.int k)) => pure (Int64.ofInt k)
      | _ => pure (Int64.ofNat (← IO.rand 0 63))
    let σ0 := sigmaX e pat
    let σ := match br.auxInt with
      | .bind x => fun y => if y == x then .int ai.toInt else σ0 y
      | _ => σ0
    let top := denX e [] pat
    let or := armOracle (br.vars.map (·.ty)) σ or e top
    let ev := evalE (br.vars.map (·.ty)) σ or e top
    let ok := Pat.arityOk pat && wfB e [] pat && consB ev σ e [] pat && condB ev br.cond &&
      typedB e [] pat && Pat.argsOK e.ty [] pat && Pat.topOKL (e.ty []) pat &&
      argsOKLr br.loc e.ty pat
    if !ok then continue
    let some b := brVal br.kind ai top | continue
    let some ai' := newAuxL ev br.newAuxInt | return s!"CEX newAux {render i}"
    let nb := match br.newKind, br.newControls with
      | .First, _ => some true
      | k, [(.var x, _)] => brVal k ai' ((σ x).valOr .poison)
      | k, [(.build ns, _)] => brVal k ai' (nodeDenX e pat ev or σ .other ns ns.length 0)
      | _, _ => none
    if nb == some (b != br.swapSuccs) then sat := true
    else return s!"CEX {render i} ctrl={top.render} old={b} new={nb}"
  return if sat then "SAT" else "NONE"

def files : List RuleSet :=
  [Generated.ARM64.ruleSet, Generated.ARM64latelower.ruleSet]

def main (args : List String) : IO UInt32 := do
  let trials := (args.find? (·.startsWith "--trials=")).bind (·.drop 9 |>.toNat?) |>.getD 4000
  let only := args.filter (!·.startsWith "--")
  IO.setRandSeed 385
  relaxRef.set ((← IO.getEnv "ARMSAT_RELAX") == some "1")
  let mut stats := (0, 0, 0)
  for rs in files do
    for (o, rules) in rs.values do
      for (r, k) in rules.zipIdx do
        let key := s!"{r.loc.file}:{r.loc.line} {o.name}#{k}"
        if !only.isEmpty && !only.contains s!"{r.loc.file}:{r.loc.line}" then continue
        match r.result with
        | .setOp o' =>
          IO.println s!"{key} SETOP {← searchSetOp o o' trials}"; (← IO.getStdout).flush; continue
        | _ => pure ()
        match ← search r trials (args.contains "--debug") with
        | some (s, _) =>
          IO.println s!"{key} {s}"
          if s == "SAT" then stats := (stats.1 + 1, stats.2.1, stats.2.2)
          else stats := (stats.1, stats.2.1 + 1, stats.2.2)
        | none =>
          IO.println s!"{key} NONE"
          stats := (stats.1, stats.2.1, stats.2.2 + 1)
        (← IO.getStdout).flush
    for (k, brs) in rs.blocks do
      for (br, j) in brs.zipIdx do
        let key := s!"{br.loc.file}:{br.loc.line} block {k.name}#{j}"
        if !only.isEmpty && !only.contains s!"{br.loc.file}:{br.loc.line}" then continue
        IO.println s!"{key} BLOCK {← searchBlock br trials}"
        (← IO.getStdout).flush
  IO.eprintln s!"SAT {stats.1}, CEX/ORACLE {stats.2.1}, NONE {stats.2.2}"
  return 0

end GoFVTest.ArmSat

def main (args : List String) : IO UInt32 := GoFVTest.ArmSat.main args

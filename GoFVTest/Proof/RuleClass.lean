import GoFV.Rules.Generated

/-!
# Rule classification for the rule lemmas (`docs/proofs/rules.md`)

`lake env lean --run GoFVTest/Proof/RuleClass.lean [--list]` classifies every exported rule of
the four rule files by the semantic phase its ops need (`docs/plans/semantics.md` §9):

* `P1`: every op of the pattern and the result has a phase-P1 arm in `GoFV.SSA.Sem.evalPure`
  (integers, booleans, tuples), the pattern has no `___`/`...` arity and the result is a build
  or a copy of a rule variable;
* `P2`: likewise, but some ops have only a later-phase arm in `evalPure` (pointers, composites,
  `Load` from a memory value; `p2Names`): `Rule.Sound`'s denotation covers these rules too;
* `mem`, `call`, `float`, `ptr` (pointers and composites), `phi`: the first later-phase op
  found, by that priority;
* `block`: block rules.

Prints the per-file table and the per-op-family table; `--list` also prints one line per rule
(`<file> <op>#<index> <class> <family>`), the input of the coverage table.
-/

open GoFV.SSA GoFV.Rules

namespace GoFVTest.RuleClass

/-- The ops with a phase-P1 arm in `evalPure` (`GoFV/SSA/Sem/Pure.lean`, P1 snapshot). -/
def p1Names : List String :=
  ["Add8", "Sub8", "Mul8", "And8", "Or8", "Xor8", "Neg8", "Com8", "Add16", "Sub16", "Mul16",
   "And16", "Or16", "Xor16", "Neg16", "Com16", "Add32", "Sub32", "Mul32", "And32", "Or32",
   "Xor32", "Neg32", "Com32", "Add64", "Sub64", "Mul64", "And64", "Or64", "Xor64", "Neg64",
   "Com64", "Hmul32", "Hmul32u", "Mul32uhilo", "Mul32uover", "Hmul64", "Hmul64u", "Mul64uhilo",
   "Mul64uover", "Avg64u", "Div8", "Div8u", "Mod8", "Mod8u", "Div16", "Div16u", "Mod16",
   "Mod16u", "Div32", "Div32u", "Mod32", "Mod32u", "Div64", "Div64u", "Mod64", "Mod64u",
   "Div128u", "Eq8", "Neq8", "Less8", "Less8U", "Leq8", "Leq8U", "Eq16", "Neq16", "Less16",
   "Less16U", "Leq16", "Leq16U", "Eq32", "Neq32", "Less32", "Less32U", "Leq32", "Leq32U",
   "Eq64", "Neq64", "Less64", "Less64U", "Leq64", "Leq64U", "AndB", "OrB", "EqB", "NeqB", "Not",
   "CondSelect", "IsInBounds", "IsSliceInBounds", "SpectreIndex", "SpectreSliceIndex",
   "Ctz8", "Ctz8NonZero", "BitLen8", "PopCount8", "BitRev8", "RotateLeft8", "Ctz16",
   "Ctz16NonZero", "BitLen16", "PopCount16", "BitRev16", "RotateLeft16", "Bswap16", "Ctz32",
   "Ctz32NonZero", "BitLen32", "PopCount32", "BitRev32", "RotateLeft32", "Bswap32", "Ctz64",
   "Ctz64NonZero", "BitLen64", "PopCount64", "BitRev64", "RotateLeft64", "Bswap64", "Min64",
   "Min64u", "Max64", "Max64u", "Add64carry", "Sub64borrow", "Slicemask", "SignExt8to16",
   "ZeroExt8to16", "SignExt8to32", "ZeroExt8to32", "SignExt8to64", "ZeroExt8to64",
   "SignExt16to32", "ZeroExt16to32", "SignExt16to64", "ZeroExt16to64", "SignExt32to64",
   "ZeroExt32to64", "Trunc16to8", "Trunc32to8", "Trunc32to16", "Trunc64to8", "Trunc64to16",
   "Trunc64to32", "CvtBoolToUint8", "Const8", "Const16", "Const32", "Const64", "ConstBool",
   "Select0", "Select1", "MakeTuple", "Copy", "MakeResult"] ++
  -- shifts
  (["8", "16", "32", "64"].flatMap fun a => ["8", "16", "32", "64"].flatMap fun b =>
    [s!"Lsh{a}x{b}", s!"Rsh{a}x{b}", s!"Rsh{a}Ux{b}"])

def isP1 (o : Op) : Bool := p1Names.contains o.name

/-- The ops with an `evalPure` arm added after phase P1 (pointers, composites, loads from a
memory value, tuples of calls; `GoFV/SSA/Sem/Pure.lean`, snapshot of #98/#141). A rule all of
whose ops have an `evalPure` arm is covered by `Rule.Sound`'s denotation. -/
def p2Names : List String :=
  ["AddPtr", "ArrayMake1", "ArraySelect", "AtomicLoad32", "AtomicLoad64", "AtomicLoad8",
   "AtomicLoadAcq32", "AtomicLoadAcq64", "AtomicLoadPtr", "ComplexImag", "ComplexMake",
   "ComplexReal", "ConstInterface", "ConstNil", "ConstSlice", "Convert", "Dereference",
   "Empty", "EqInter", "EqPtr", "EqSlice", "IData", "IMake", "ITab", "IsNonNil", "Load",
   "MemEq", "NeqInter", "NeqPtr", "NeqSlice", "OffPtr", "PtrIndex", "SelectN", "SelectNAddr",
   "SliceCap", "SliceLen", "SliceMake", "SlicePtr", "SlicePtrUnchecked", "StringLen",
   "StringMake", "StringPtr", "StructMake", "StructSelect", "SubPtr"]

def isP2 (o : Op) : Bool := p2Names.contains o.name

def memNames : List String :=
  ["Load", "Store", "Move", "Zero", "StoreWB", "MoveWB", "ZeroWB", "WB", "NilCheck", "VarDef",
   "VarLive", "KeepAlive", "InitMem", "MemEq", "LoadMasked8", "LoadMasked16", "LoadMasked32",
   "LoadMasked64", "StoreMasked8", "StoreMasked16", "StoreMasked32", "StoreMasked64",
   "SelectN", "SelectNAddr", "Arg", "ArgIntReg", "ArgFloatReg", "LocalAddr", "GetG",
   "GetClosurePtr", "GetCallerPC", "GetCallerSP"]

def isFloat (o : Op) : Bool :=
  let n := o.name
  (n.splitOn "32F").length > 1 || (n.splitOn "64F").length > 1 ||
  (n.startsWith "Cvt" && n != "CvtBoolToUint8") ||
  ["Sqrt", "Sqrt32", "Floor", "Ceil", "Trunc", "RoundToEven", "Round", "Abs", "Copysign",
   "FMA"].contains n

/-- Category of a non-P1 op. -/
def opClass (o : Op) : String :=
  if o.call then "call"
  else if memNames.contains o.name || o.typ == "Mem" || (o.name.startsWith "Atomic") then "mem"
  else if isFloat o then "float"
  else if o.name == "Phi" then "phi"
  else "ptr"

mutual
def patOps : Pat → List Op
  | .op o _ _ _ _ _ args _ => o :: patsOps args
  | _ => []
def patsOps : List Pat → List Op
  | [] => []
  | p :: ps => patOps p ++ patsOps ps
end

mutual
def patArityOk : Pat → Bool
  | .op _ _ _ _ _ ar args _ =>
    (match ar with | .fixed | .exact _ => true | _ => false) && patsArityOk args
  | _ => true
def patsArityOk : List Pat → Bool
  | [] => true
  | p :: ps => patArityOk p && patsArityOk ps
end

def resOps : Result → List Op
  | .build ns => ns.map (·.op)
  | .setOp o => [o]
  | .copy _ => []

def classPrio : List String := ["call", "mem", "float", "ptr", "phi"]

def classify (r : Rule) : String :=
  let ops := patOps r.pat ++ resOps r.result
  let bad := ops.filter (!isP1 ·)
  if bad.isEmpty then
    let resOk := match r.result with
      | .build _ => true
      | .copy (.var _) => true
      | _ => false
    if patArityOk r.pat && resOk then "P1" else "ptr"
  else if bad.all isP2 && patArityOk r.pat &&
      (match r.result with | .build _ | .copy (.var _) => true | _ => false) then "P2"
  else
    let cs := bad.map opClass
    (classPrio.find? cs.contains).getD "ptr"

/-- Op family of a rule's top op: the op name without its width suffix
(`Add16` → `Add`, `Rsh32Ux64` → `Rsh`, `Eq8` → `Eq`, `ZeroExt8to64` → `ZeroExt`). -/
def family (o : Op) : String :=
  let n := o.name
  let cut := n.toList.takeWhile (fun c => !c.isDigit)
  String.ofList cut

def files : List RuleSet :=
  [Generated.Generic.ruleSet, Generated.Dec.ruleSet, Generated.Divisible.ruleSet,
   Generated.Divmod.ruleSet]

def classes : List String := ["P1", "P2", "mem", "call", "float", "ptr", "phi", "block"]

def main (args : List String) : IO Unit := do
  let list := args.contains "--list"
  -- file, `<op>#<index>` (position in the op's rule list), class, family
  let mut rows : List (String × String × String × String) := []
  for rs in files do
    for (o, rules) in rs.values do
      for (r, i) in rules.zipIdx do
        rows := rows ++ [(rs.name, s!"{o.name}#{i}", classify r, family o)]
    for (k, brs) in rs.blocks do
      for (_, i) in brs.zipIdx do
        rows := rows ++ [(rs.name, s!"{k.name}#{i}", "block", "Block")]
  IO.println s!"| File | {" | ".intercalate classes} | Total |"
  IO.println s!"| --- |{String.join (classes.map fun _ => " --: |")} --: |"
  for rs in files do
    let mine := rows.filter (·.1 == rs.name)
    let cnt := classes.map fun c => toString (mine.filter (·.2.2.1 == c)).length
    IO.println s!"| `{rs.name}` | {" | ".intercalate cnt} | {mine.length} |"
  let cnt := classes.map fun c => toString (rows.filter (·.2.2.1 == c)).length
  IO.println s!"| all | {" | ".intercalate cnt} | {rows.length} |"
  if list then
    for (f, n, c, fam) in rows do
      IO.println s!"{f} {n} {c} {fam}"

end GoFVTest.RuleClass

def main (args : List String) : IO Unit := GoFVTest.RuleClass.main args

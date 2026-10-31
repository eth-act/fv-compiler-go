import GoFV.Proof.Rules.Attr
import GoFV.Proof.Rules.Den

/-!
# `Helper.ofName` at the helper names of the rules

One `rule_helper` lemma `Helper.ofName "<name>" = …` per function name called by an exported
rule, and `typShape "<name>" = …` per `typ.<name>` field they read
(`GoFVTest/Proof/RuleNames.lean` checks both lists against the rule data), proved once here,
so the rule lemmas never make the kernel compare strings.
-/

namespace GoFV.Proof.Rules

open Lean Elab Command

/-- `#helper_name_lemmas "a" "b" …`: `theorem ofName_<i> : Helper.ofName "<name>" = <value>`,
the value computed by the compiled `Helper.ofName`. -/
elab "#helper_name_lemmas " names:str* : command => do
  for (n, i) in names.toList.zipIdx do
    let s := n.getString
    let rhs := toString (repr (Helper.ofName s))
    let some rhsStx := (Parser.runParserCategory (← getEnv) `term rhs).toOption
      | throwError "cannot parse {rhs}"
    let id := mkIdent (.mkSimple s!"ofName_{i}")
    elabCommand (← `(@[rule_helper] theorem $id : Helper.ofName $n = $(⟨rhsStx⟩) := by
      decide +kernel))

/-- `#typ_shape_lemmas "a" "b" …`: `theorem typShape_<i> : typShape "<name>" = <value>`. -/
elab "#typ_shape_lemmas " names:str* : command => do
  for (n, i) in names.toList.zipIdx do
    let s := n.getString
    let rhs := toString (repr (typShape s))
    let some rhsStx := (Parser.runParserCategory (← getEnv) `term rhs).toOption
      | throwError "cannot parse {rhs}"
    let id := mkIdent (.mkSimple s!"typShape_{i}")
    elabCommand (← `(@[rule_helper] theorem $id : typShape $n = $(⟨rhsStx⟩) := by rfl))

/-- The function names called by the exported rules. -/
def helperNames : List String := [
  "CanSSA",
  "addToSub",
  "bits.Len16",
  "bits.Len32",
  "bits.Len64",
  "bits.Len8",
  "bits.OnesCount16",
  "bits.OnesCount32",
  "bits.OnesCount64",
  "bits.OnesCount8",
  "bitsAdd64",
  "bitsMulU32",
  "bitsMulU64",
  "bool2int",
  "canLoadUnaligned",
  "canRotate",
  "clobber",
  "copyCompatibleType",
  "devirtLECall",
  "disjoint",
  "hasSmallRotate",
  "imakeOfStructMake",
  "is16BitInt",
  "is32Bit",
  "is32BitFloat",
  "is32BitInt",
  "is64BitFloat",
  "is64BitInt",
  "is8BitInt",
  "isConstZero",
  "isDictArgSym",
  "isDirectAndComparableIface",
  "isDirectAndComparableType",
  "isFixedLoad",
  "isInlinableMemclr",
  "isInlinableMemmove",
  "isMalloc",
  "isNonNegative",
  "isPowerOfTwo",
  "isSameCall",
  "isSamePtr",
  "isStackPtr",
  "isVolatile",
  "log16",
  "log16u",
  "log32",
  "log32u",
  "log64",
  "log64u",
  "log8",
  "log8u",
  "math.Ceil",
  "math.Float32bits",
  "math.Float32frombits",
  "math.Float64bits",
  "math.Float64frombits",
  "math.Floor",
  "math.IsNaN",
  "math.RoundToEven",
  "math.Sqrt",
  "math.Trunc",
  "modularMultiplicativeInverse",
  "needRaceCleanup",
  "nlz16",
  "nlz32",
  "nlz64",
  "nlz8",
  "ntz16",
  "ntz32",
  "ntz64",
  "ntz8",
  "oneBit",
  "read16",
  "read32",
  "read64",
  "read8",
  "reciprocalExact32",
  "reciprocalExact64",
  "registerizable",
  "resetCopy",
  "rewriteCondSelectIntoMath",
  "rewriteFixedLoad",
  "rewriteStructLoad",
  "rewriteStructStore",
  "sdivisible16",
  "sdivisible32",
  "sdivisible64",
  "sdivisible8",
  "sdivisibleOK16",
  "sdivisibleOK32",
  "sdivisibleOK64",
  "sdivisibleOK8",
  "shiftIsBounded",
  "smagic16",
  "smagic32",
  "smagic64",
  "smagic8",
  "smagicOK16",
  "smagicOK32",
  "smagicOK64",
  "smagicOK8",
  "symIsRO",
  "symIsROZero",
  "uaddOvf",
  "udivisible16",
  "udivisible32",
  "udivisible64",
  "udivisible8",
  "udivisibleOK16",
  "udivisibleOK32",
  "udivisibleOK64",
  "udivisibleOK8",
  "umagic16",
  "umagic32",
  "umagic64",
  "umagic8",
  "umagicOK16",
  "umagicOK32",
  "umagicOK64",
  "umagicOK8",
  "warnRule"
]

#helper_name_lemmas
  "CanSSA" "addToSub" "bits.Len16" "bits.Len32" "bits.Len64" "bits.Len8" "bits.OnesCount16"
  "bits.OnesCount32" "bits.OnesCount64" "bits.OnesCount8" "bitsAdd64" "bitsMulU32" "bitsMulU64"
  "bool2int" "canLoadUnaligned" "canRotate" "clobber" "copyCompatibleType" "devirtLECall"
  "disjoint" "hasSmallRotate" "imakeOfStructMake" "is16BitInt" "is32Bit" "is32BitFloat"
  "is32BitInt" "is64BitFloat" "is64BitInt" "is8BitInt" "isConstZero" "isDictArgSym"
  "isDirectAndComparableIface" "isDirectAndComparableType" "isFixedLoad" "isInlinableMemclr"
  "isInlinableMemmove" "isMalloc" "isNonNegative" "isPowerOfTwo" "isSameCall" "isSamePtr"
  "isStackPtr" "isVolatile" "log16" "log16u" "log32" "log32u" "log64" "log64u" "log8" "log8u"
  "math.Ceil" "math.Float32bits" "math.Float32frombits" "math.Float64bits" "math.Float64frombits"
  "math.Floor" "math.IsNaN" "math.RoundToEven" "math.Sqrt" "math.Trunc"
  "modularMultiplicativeInverse" "needRaceCleanup" "nlz16" "nlz32" "nlz64" "nlz8" "ntz16" "ntz32"
  "ntz64" "ntz8" "oneBit" "read16" "read32" "read64" "read8" "reciprocalExact32"
  "reciprocalExact64" "registerizable" "resetCopy" "rewriteCondSelectIntoMath" "rewriteFixedLoad"
  "rewriteStructLoad" "rewriteStructStore" "sdivisible16" "sdivisible32" "sdivisible64"
  "sdivisible8" "sdivisibleOK16" "sdivisibleOK32" "sdivisibleOK64" "sdivisibleOK8"
  "shiftIsBounded" "smagic16" "smagic32" "smagic64" "smagic8" "smagicOK16" "smagicOK32"
  "smagicOK64" "smagicOK8" "symIsRO" "symIsROZero" "uaddOvf" "udivisible16" "udivisible32"
  "udivisible64" "udivisible8" "udivisibleOK16" "udivisibleOK32" "udivisibleOK64" "udivisibleOK8"
  "umagic16" "umagic32" "umagic64" "umagic8" "umagicOK16" "umagicOK32" "umagicOK64" "umagicOK8"
  "warnRule"

/-- The `typ.<name>` fields the exported rules read. -/
def typNames : List String :=
  ["Bool", "BytePtr", "BytePtrPtr", "Float32", "Float32Ptr", "Float64", "Float64Ptr", "Int",
   "Int16", "Int32", "Int64", "Int8", "IntPtr", "String", "UInt16", "UInt32", "UInt64", "UInt8",
   "Uintptr"]

#typ_shape_lemmas
  "Bool" "BytePtr" "BytePtrPtr" "Float32" "Float32Ptr" "Float64" "Float64Ptr" "Int" "Int16"
  "Int32" "Int64" "Int8" "IntPtr" "String" "UInt16" "UInt32" "UInt64" "UInt8" "Uintptr"

end GoFV.Proof.Rules

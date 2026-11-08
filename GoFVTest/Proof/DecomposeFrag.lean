import GoFV.Proof.Witness.Decompose

open scoped GoFV.SSA.Sem.Fixed

/-!
# The decompose witnesses and the passes' fragments

`GoFV.Proof.Witness.decomposeUser_witness`/`decomposeBuiltin_witness` show the checked stages on
`pair`/`formatBool` by kernel evaluation. Running the passes (their state uses `Std.HashMap`,
which the kernel does not evaluate):

- decompose user's output on `pair` has the witness's code (`sameCode … pairOut`), its tables
  add the split names of `pair`'s struct variable (new slots and autos), and `pair` is in
  `decUserFrag`;
- decompose builtin's output on `formatBool` adds the split names of its string variable, the
  dec rules then rewrite `formatBoolOut` further, and `formatBool` is in `decBuiltinFrag`
  (the witness takes the dec rewrite to be the identity, which `decBuiltinStagesOK` accepts
  as well).
-/

open GoFV.SSA GoFV.Opt GoFV.Opt.Decompose GoFV.Proof.Witness

/-- `fbPassEnv` with the configuration the dec rewrite reads. -/
def decEnv (pass : String) (tabs : Tables) : PassEnv :=
  { fbPassEnv pass tabs with
    config := #[("arch", #[.word "arm64"]), ("ptrsize", #[.word "8"]), ("regsize", #[.word "8"]),
      ("bigendian", #[.word "0"]), ("race", #[.word "0"]), ("archalign", #[.word "1"]),
      ("debugnil", #[.word "0"]), ("exp.simd", #[.word "0"]),
      ("zerobase", #[.str (GoStr.ofString "runtime.zerobase")]),
      ("rttype.Size_", #[.word "0:UINTPTR:8"]), ("rttype.PtrBytes", #[.word "8:UINTPTR:8"]),
      ("rttype.Hash", #[.word "16:UINT32:4"]), ("rttype.Kind_", #[.word "23:UINT8:1"]),
      ("rttype.GCData", #[.word "32:PTR:8"]), ("rttype.PtrType.Elem", #[.word "48:PTR:8"])] }

def userOK : Bool :=
  let env := decEnv "decompose user" pairTabs
  match decomposeUserPass env pair with
  | .ok out => sameCode out.func pairOut && decUserFrag env pair &&
      out.tables.slots.size > pairTabs.slots.size
  | .error _ => false

/-- `formatBool` with the line-start cache the rewrite requires (`sameCode` ignores caches). -/
def formatBoolLS : Func := { formatBool with cache := { formatBool.cache with lineStarts := some #[] } }

def builtinOK : Bool :=
  let env := decEnv "decompose builtin" formatBoolTabs
  match postExpandCallsDecomposePass env formatBoolLS with
  | .ok out => decBuiltinFrag env formatBoolLS && out.tables.slots.size > formatBoolTabs.slots.size
  | .error _ => false

#guard userOK
#guard builtinOK

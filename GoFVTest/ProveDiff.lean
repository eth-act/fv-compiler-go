import GoFV.Opt.Prove.Poset
import GoFV.Opt.Prove.Limit

/-!
`lake exe prove-difftest <cases.txt>`: replays the poset operation sequences written by
tools/provediff (run through scripts/prove-difftest.sh) on `GoFV.Opt.Prove.Poset` and compares
every result and the poset's internal state after every operation with Go's; recomputes the
limit-arithmetic cases with `GoFV.Opt.Prove.Limit`. Line formats:
tools/provediff/ssa/driver.go, tools/provediff/ssa/limits.go.
-/

namespace GoFVTest.ProveDiff

open GoFV.Opt.Prove

def joinSep (sep : String) (xs : List String) : String := sep.intercalate xs

/-- The state string of tools/provediff/ssa/driver.go `posetState`. -/
def posetState (po : Poset) : String :=
  let roots := joinSep "," (po.roots.toList.map toString)
  let nodes := joinSep "," ((po.nodes.toList.drop 1).map fun n => s!"{n.l}.{n.r}")
  let vals := (po.values.toList.toArray.qsort (fun a b => a.1 < b.1)).toList
  let vals := joinSep "," (vals.map fun (k, v) => s!"{k}={v}")
  let neq := (po.noneq.toList.toArray.qsort
    (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2))).toList
  let neq := joinSep "," (neq.map fun (h, l) => s!"{h}.{l}")
  s!"{po.lastidx};{roots};{nodes};{vals};{neq};{po.undo.size}"

def b2s (b : Bool) : String := if b then "1" else "0"

/-- Replay one op; returns the result token (without the state). -/
def step (po : Poset) (op : String) : Except String (String × Poset) := do
  if op == "c" then return ("-", po.checkpoint)
  if op == "u" then return ("-", po.undoAll)
  match op.splitOn ":" with
  | [c, a, b] =>
    let some a := a.toNat? | throw s!"bad op {op}"
    let some b := b.toNat? | throw s!"bad op {op}"
    match c with
    | "o" => let (r, po) := po.setOrderLt a b; return (b2s r, po)
    | "e" => let (r, po) := po.setOrderOrEqual a b; return (b2s r, po)
    | "q" => let (r, po) := po.setEqual a b; return (b2s r, po)
    | "n" => let (r, po) := po.setNonEqual a b; return (b2s r, po)
    | "O" => return (b2s (po.ordered a b), po)
    | "L" => return (b2s (po.orderedOrEqual a b), po)
    | "E" => return (b2s (po.equal a b), po)
    | "N" => return (b2s (po.nonEqual a b), po)
    | _ => throw s!"bad op {op}"
  | _ => throw s!"bad op {op}"

def checkPoset (toks : Array String) : Except String Unit := do
  let some nops := toks[2]!.toNat? | throw "bad nops"
  if toks.size != 3 + 2 * nops then throw "bad token count"
  let mut po : Poset := {}
  for i in [0:nops] do
    let op := toks[3 + i]!
    let (r, po') ← step po op
    po := po'
    let got := s!"{r}/{posetState po}"
    let want := toks[3 + nops + i]!
    if got != want then
      throw s!"op {i} ({op}) of {toks.extract 3 (3 + i + 1)}:\n  go:   {want}\n  lean: {got}"
  return ()

def parseLimit (s : String) : Except String Limit :=
  match s.splitOn ":" with
  | [a, b, c, d] =>
    match a.toInt?, b.toInt?, c.toNat?, d.toNat? with
    | some a, some b, some c, some d =>
      .ok ⟨Int64.ofInt a, Int64.ofInt b, UInt64.ofNat c, UInt64.ofNat d⟩
    | _, _, _, _ => .error s!"bad limit {s}"
  | _ => .error s!"bad limit {s}"

def lstr (l : Limit) : String := s!"{l.min}:{l.max}:{l.umin}:{l.umax}"

def optI (o : Option Int64) : String := match o with
  | some v => s!"{v}:true" | none => "0:false"
def optU (o : Option UInt64) : String := match o with
  | some v => s!"{v}:true" | none => "0:false"

def checkLimit (toks : Array String) : Except String Unit := do
  if toks.size != 6 then throw "bad token count"
  let op := toks[1]!
  let some b := toks[2]!.toNat? | throw "bad b"
  let l1 ← parseLimit toks[3]!
  let l2 ← parseLimit toks[4]!
  let got := match op with
    | "add" => lstr (l1.add l2 b)
    | "sub" => lstr (l1.sub l2 b)
    | "mul" => lstr (l1.mul l2 b)
    | "exp2" => lstr (l1.exp2 b)
    | "com" => lstr (l1.com b)
    | "neg" => lstr (l1.neg b)
    | "ctz" => lstr (l1.ctz b)
    | "bitlen" => lstr (l1.bitlen b)
    | "popcount" => lstr (l1.popcount b)
    | "const" => optI l1.constValue
    | "fixed" => let (f, c) := l1.unsignedFixedLeadingBits; s!"{f}:{c}"
    | "intersect" => lstr (l1.intersect l2)
    | "safe" =>
      s!"{optI (safeAdd l1.min l2.max b)}:{optI (safeSub l1.min l2.max b)}:" ++
        s!"{optU (safeAddU l1.umin l2.umax b)}:{optU (safeSubU l1.umin l2.umax b)}"
    | _ => "?"
  if got != toks[5]! then
    throw s!"{op} {b} {toks[3]!} {toks[4]!}:\n  go:   {toks[5]!}\n  lean: {got}"

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: prove-difftest <cases.txt>"; return 2
  let lines ← IO.FS.lines path
  let mut ok := 0
  let mut bad := 0
  for line in lines do
    if line.isEmpty then continue
    let toks := (line.splitOn " ").toArray
    let r := match toks[0]! with
      | "P" => checkPoset toks
      | "L" => checkLimit toks
      | k => .error s!"unknown case kind {k}"
    match r with
    | .ok () => ok := ok + 1
    | .error e =>
      bad := bad + 1
      if bad ≤ 5 then IO.eprintln s!"mismatch: {e}"
  IO.println s!"prove-difftest: {ok} cases match, {bad} mismatch"
  return if bad == 0 && ok > 0 then 0 else 1

end GoFVTest.ProveDiff

def main (args : List String) : IO UInt32 := GoFVTest.ProveDiff.main args

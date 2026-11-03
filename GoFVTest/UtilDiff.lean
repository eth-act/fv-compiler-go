import GoFV.Util.PdqSort
import GoFV.Util.PdqSortM
import GoFV.Util.SparseSet
import GoFV.Util.SparseMapPos
import Std.Data.HashMap

/-!
`lake exe util-difftest <cases.txt>`: recomputes the cases written by tools/utildiff (run
through scripts/util-difftest.sh) with the Lean ports in `GoFV.Util` and compares them with
Go's results. Line formats and trace syntax: tools/utildiff/main.go, tools/utildiff/ssa/driver.go.
-/

namespace GoFVTest.UtilDiff

open GoFV.Util

/-- `mix` of tools/utildiff/main.go. -/
def mix (x y : Nat) : UInt64 :=
  let h := (UInt64.ofNat x * 0x9E3779B97F4A7C15) ^^^ (UInt64.ofNat y * 0xC2B2AE3D27D4EB4F)
  let h := h ^^^ (h >>> 29)
  let h := h * 0xBF58476D1CE4E5B9
  h ^^^ (h >>> 32)

def compare3 (a b : Nat) : Int := if a < b then -1 else if a > b then 1 else 0

/-- `cmpFn` of tools/utildiff/main.go. -/
def cmpFn : Nat → Nat → Nat → Int
  | 0, x, y => compare3 (x >>> 12) (y >>> 12)
  | 1, x, y => compare3 x y
  | 2, x, y => ((mix x y % 3).toNat : Int) - 1
  | 3, x, y => compare3 ((x >>> 12) % 3) ((y >>> 12) % 3)
  | 4, x, y => ((x >>> 12 : Nat) : Int) - ((y >>> 12 : Nat) : Int)
  | 5, x, y => if mix x y &&& 1 == 1 then -1 else 1
  | 6, x, y => if mix x y % 16 == 0 then -1 else 1
  | _, x, y => if mix x y % 16 == 0 then 1 else -1

def parseNat (s : String) : Except String Nat :=
  match s.toNat? with
  | some n => .ok n
  | none => .error s!"bad number {s}"

def parseInt (s : String) : Except String Int :=
  match s.toInt? with
  | some n => .ok n
  | none => .error s!"bad number {s}"

/-- A sort case: `<cmp> <n> <keys> <perm>`; `less` selects `sort.Sort` over `slices.SortFunc`.
`slices.SortFunc` cases also run `PdqSortM.sortFunc` with a comparator in `StateM` that counts
its calls (the effectful port must give Go's result too). -/
def checkSort (less : Bool) (toks : Array String) : Except String Unit := do
  let id ← parseNat toks[1]!
  let n ← parseNat toks[2]!
  if toks.size != 3 + 2 * n then throw "bad token count"
  let mut data : Array Nat := Array.mkEmpty n
  for i in [0:n] do
    data := data.push ((← parseNat toks[3 + i]!) <<< 12 ||| i)
  let out :=
    if less then PdqSort.sortBy (fun x y => decide (cmpFn id x y < 0)) data
    else PdqSort.sortFunc (cmpFn id) data
  let outM := if less then out else
    ((PdqSortM.sortFunc (m := StateM Nat)
      (fun x y => do modify (· + 1); return cmpFn id x y) data).run' 0).run
  for i in [0:n] do
    let want ← parseNat toks[3 + n + i]!
    if out[i]! &&& 0xfff != want then
      throw s!"position {i}: lean {out[i]! &&& 0xfff}, go {want}"
    if outM[i]! &&& 0xfff != want then
      throw s!"position {i}: lean (PdqSortM) {outM[i]! &&& 0xfff}, go {want}"

def bracket (xs : Array String) : String := "[" ++ ",".intercalate xs.toList ++ "]"

def b01 (b : Bool) : String := if b then "1" else "0"

def runSet (cap : Nat) (ops : Array String) : Except String (Array String) := do
  let mut s := SparseSet.new cap
  let mut out : Array String := #[]
  for op in ops do
    let arg := op.drop 1 |>.toString
    match op.front with
    | 'a' => s := s.add (← parseNat arg)
    | 'A' =>
      let xs ← (if arg.isEmpty then [] else arg.splitOn ",").mapM parseNat
      s := s.addAll xs
    | 'r' => s := s.remove (← parseNat arg)
    | 'p' =>
      let (x, s') := s.pop
      s := s'
      out := out.push (toString x)
    | 'c' => s := s.clear
    | 'q' => out := out.push (b01 (s.contains (← parseNat arg)))
    | 's' => out := out.push (toString s.size)
    | 'l' => out := out.push (bracket (s.contents.map toString))
    | _ => throw s!"bad op {op}"
  return out

def runMap (cap : Nat) (ops : Array String) : Except String (Array String) := do
  let mut s : SparseMap Int := SparseMap.new cap
  let mut out : Array String := #[]
  for op in ops do
    let arg := op.drop 1 |>.toString
    match op.front with
    | 's' =>
      match arg.splitOn ":" with
      | [k, v] => s := s.set (← parseNat k) (← parseInt v)
      | _ => throw s!"bad op {op}"
    | 'g' => out := out.push (match s.get (← parseNat arg) with | some v => toString v | none => "-")
    | 'r' => s := s.remove (← parseNat arg)
    | 'c' => s := s.clear
    | 'q' => out := out.push (b01 (s.contains (← parseNat arg)))
    | 'z' => out := out.push (toString s.size)
    | 'l' => out := out.push (bracket (s.contents.map fun e => s!"{e.key}:{e.val}"))
    | _ => throw s!"bad op {op}"
  return out

def runMapPos (cap : Nat) (ops : Array String) : Except String (Array String) := do
  let mut s : SparseMapPos (Int × Nat) := SparseMapPos.new cap
  let mut out : Array String := #[]
  for op in ops do
    let arg := op.drop 1 |>.toString
    match op.front with
    | 's' =>
      match arg.splitOn ":" with
      | [k, v, i, l] => s := s.set (← parseNat k) (← parseInt v) (← parseInt i, ← parseNat l)
      | _ => throw s!"bad op {op}"
    | 'g' => out := out.push (toString (s.get (← parseNat arg)))
    | 'r' => s := s.remove (← parseNat arg)
    | 'c' => s := s.clear
    | 'q' => out := out.push (b01 (s.contains (← parseNat arg)))
    | 'z' => out := out.push (toString s.size)
    | 'l' =>
      out := out.push (bracket (s.contents.map fun e => s!"{e.key}:{e.val.1}:{e.val.2.1}:{e.val.2.2}"))
    | _ => throw s!"bad op {op}"
  return out

/-- A sparse-structure case: `<cap> <nops> <ops> <trace>`. -/
def checkSparse (run : Nat → Array String → Except String (Array String))
    (toks : Array String) : Except String Unit := do
  let cap ← parseNat toks[1]!
  let nops ← parseNat toks[2]!
  if toks.size < 3 + nops then throw "bad token count"
  let got ← run cap (toks.extract 3 (3 + nops))
  let want := toks.extract (3 + nops) toks.size
  if got != want then
    let i := (List.range (min got.size want.size)).find? (fun i => got[i]! != want[i]!)
      |>.getD (min got.size want.size)
    throw s!"result {i}: lean {got[i]?.getD "<end>"}, go {want[i]?.getD "<end>"}"

def kinds : List (String × String) :=
  [("F", "slices.SortFunc"), ("S", "sort.Sort"), ("T", "sparseSet"), ("M", "sparseMap"),
    ("P", "sparseMapPos")]

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: util-difftest <cases.txt>"; return 2
  let h ← IO.FS.Handle.mk path .read
  let mut counts : Std.HashMap String (Nat × Nat) := {}
  let mut lineNo := 0
  let mut shown := 0
  repeat
    let line ← h.getLine
    if line.isEmpty then break
    lineNo := lineNo + 1
    let toks := (line.trimAsciiEnd.toString.splitOn " ").toArray
    let kind := toks[0]!
    let res : Except String Unit :=
      match kind with
      | "F" => checkSort false toks
      | "S" => checkSort true toks
      | "T" => checkSparse runSet toks
      | "M" => checkSparse runMap toks
      | "P" => checkSparse runMapPos toks
      | _ => .error s!"unknown kind {kind}"
    let (ok, bad) := counts.getD kind (0, 0)
    match res with
    | .ok () => counts := counts.insert kind (ok + 1, bad)
    | .error e =>
      counts := counts.insert kind (ok, bad + 1)
      if shown < 20 then
        shown := shown + 1
        IO.eprintln s!"line {lineNo} ({kind}): {e}"
  let mut failed := false
  for (k, name) in kinds do
    let (ok, bad) := counts.getD k (0, 0)
    IO.println s!"{name}: {ok + bad} cases, {bad} mismatches"
    if bad > 0 || ok == 0 then failed := true
  return if failed then 1 else 0

end GoFVTest.UtilDiff

def main (args : List String) : IO UInt32 := GoFVTest.UtilDiff.main args

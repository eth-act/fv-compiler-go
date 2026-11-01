/-
Largest constants of an `.olean` (docs/PERF.md, scripts/perf-explain.py).

usage: lake env lean --run scripts/olean-top.lean M.olean [N]

For each constant stored in the module: shared Expr nodes of its type+value (DAG size) and the
bytes of string literals inside (`bv_decide` stores its LRAT certificate as one), largest first.
Tells whether a big `.olean` comes from many constants, generated equations, huge proof terms
or embedded certificates.
-/
import Lean
open Lean

structure OStat where
  seen : Std.HashSet USize := {}
  nodes : Nat := 0
  strBytes : Nat := 0

unsafe def visit (e : Expr) : StateM OStat Unit := do
  let p := ptrAddrUnsafe e
  if (← get).seen.contains p then return
  modify fun a => { a with seen := a.seen.insert p, nodes := a.nodes + 1 }
  match e with
  | .lit (.strVal s) => modify fun a => { a with strBytes := a.strBytes + s.utf8ByteSize }
  | .app f x => visit f; visit x
  | .lam _ t b _ | .forallE _ t b _ => visit t; visit b
  | .letE _ t v b _ => visit t; visit v; visit b
  | .mdata _ b | .proj _ _ b => visit b
  | _ => pure ()

unsafe def constStat (c : ConstantInfo) : Nat × Nat :=
  let go : StateM OStat Unit := do
    visit c.type
    if let some v := c.value? (allowOpaque := true) then visit v
  let a := (go.run {}).2
  (a.nodes, a.strBytes)

unsafe def main (args : List String) : IO Unit := do
  let path := args.head!
  let n := (args.getD 1 "15").toNat!
  let (md, _) ← readModuleData path
  let rows : Array (Nat × Nat × Name) := md.constants.map fun c =>
    let r := constStat c
    (r.1, r.2, c.name)
  let rows := rows.qsort fun a b => a.1 + a.2.1 / 8 > b.1 + b.2.1 / 8
  let nodes := rows.foldl (fun acc r => acc + r.1) 0
  let bytes := rows.foldl (fun acc r => acc + r.2.1) 0
  IO.println s!"{path}: {md.constants.size} constants; total {nodes} Expr nodes (per-constant DAG), {bytes} string-literal bytes"
  for (k, s, nm) in rows.toList.take n do
    IO.println s!"  {k} nodes  {s} str-bytes  {nm}"

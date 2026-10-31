import GoFV.Opt.Pass
import GoFV.SSA.Alloc
import Std.Data.HashMap.Basic

/-!
# zero arg cse (`zcse.go`)

Phase 1: the first value of each key `(op, keyFor, aux, type)` among the zero-argument values,
in `f.Blocks` × `b.Values` order, is the representative; one outside `f.Entry` is moved to the
end of `f.Entry.Values`, swap-removed from its block and the slot visited again. Phase 2: every
zero-argument argument is pointed at its representative (`SetArg`, even when unchanged).
Controls and `f.NamedValues` are not updated; nothing is freed (`docs/PASSES.md`, zero arg
cse). Aux and type equality are the export's numbers (Go `==`).
-/

namespace GoFV.Opt

open GoFV.SSA

namespace ZCSE

/-- `vkey`. -/
structure Key where
  op : Op
  ai : Int64
  ax : Option AuxRef
  t : TypeRef
  deriving BEq

instance : Hashable Key where
  hash k := mixHash (hash k.ai) (mixHash (hash k.ax) (hash k.t))

/-- `keyFor(v)`: `AuxInt` sign-normalised to the constant's width. -/
def keyFor (v : Value) : Int64 :=
  match v.op with
  | .Const32 => v.auxInt.toInt32.toInt64
  | .Const16 => v.auxInt.toInt16.toInt64
  | .Const8 | .ConstBool => v.auxInt.toInt8.toInt64
  | _ => v.auxInt

def key (v : Value) : Key := ⟨v.op, keyFor v, v.aux, v.type⟩

/-- Phase 1 on block `b`. Fuel: each step advances `i` or removes a value from `b`. -/
def scanBlock (entry b : ID) (st : Func × Std.HashMap Key ID) : Func × Std.HashMap Key ID :=
  Id.run do
  let (f, vals) := st
  let mut f := f
  let mut vals := vals
  let mut i := 0
  for _ in [0:2 * (f.getB b).values.size + 1] do
    let vs := (f.getB b).values
    if h : i < vs.size then
      let v := vs[i]
      let x := f.getV v
      if x.op.argLen == 0 then
        let k := key x
        if !vals.contains k then
          vals := vals.insert k v
          if b != entry then
            f := f.modV v fun y => { y with block := entry }
            f := f.modB entry fun y => { y with values := y.values.push v }
            f := f.modB b fun y =>
              let last := y.values.size - 1
              { y with values := (y.values.set! i y.values[last]!).pop }
            continue
      i := i + 1
    else break
  return (f, vals)

end ZCSE

/-- `zcse(f)`. -/
def zcse (f : Func) : Func := Id.run do
  let (f, vals) := f.blocks.foldl (fun st b => ZCSE.scanBlock f.entry b st) (f, {})
  let mut f := f
  for b in f.blocks do
    for v in (f.getB b).values do
      let n := (f.getV v).args.size
      for i in [0:n] do
        let a := (f.getV v).args[i]!
        let x := f.getV a
        if x.op.argLen == 0 then
          if let some rv := vals.get? (ZCSE.key x) then
            f := f.setArg v i rv
  return f

/-- The `zero arg cse` pass. -/
def zcsePass : Pass := Pass.ofFunc fun _ f => pure (zcse f)

end GoFV.Opt

import GoFV.Opt.Pass
import GoFV.SSA.Alloc
import GoFV.SSA.DomCert
import GoFV.SSA.Sem.Run
import Std.Data.TreeMap

/-!
# zero arg cse (`zcse.go`)

Phase 1: the first value of each key `(op, keyFor, aux, type)` among the zero-argument values,
in `f.Blocks` × `b.Values` order, is the representative; one outside `f.Entry` is moved to the
end of `f.Entry.Values`, swap-removed from its block and the slot visited again. Phase 2: every
zero-argument argument is pointed at its representative (`SetArg`, even when unchanged).
Controls and `f.NamedValues` are not updated; nothing is freed (`docs/PASSES.md`, zero arg
cse). Aux and type equality are the export's numbers (Go `==`). The key map is a `TreeMap`
(lookups only, so the result does not depend on the map; the kernel can evaluate it, unlike a
`HashMap`, whose `mixHash` is opaque).

The registered pass (`zcsePass`) is a translation validator: it runs `zcse` and keeps the
result only if the Bool checker `zrel` accepts it, else returns the input unchanged.
`GoFV.Proof.ZCSE.zcse_refines` proves that an accepted result refines the input. `zrel`
never rejects on the corpus (`lake exe zcse-probe`).
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

/-- A total order on keys (any order does: the map is only searched). -/
def Key.cmp (a b : Key) : Ordering :=
  (compare a.op.ctorIdx b.op.ctorIdx).then <|
    (compare a.ai.toBitVec.toNat b.ai.toBitVec.toNat).then <|
      (compare ((a.ax.map (· + 1)).getD 0) ((b.ax.map (· + 1)).getD 0)).then (compare a.t b.t)

/-- The representatives by key. -/
abbrev Vals := Std.TreeMap Key ID Key.cmp

/-- `keyFor(v)`: `AuxInt` sign-normalised to the constant's width. -/
def keyFor (v : Value) : Int64 :=
  match v.op with
  | .Const32 => v.auxInt.toInt32.toInt64
  | .Const16 => v.auxInt.toInt16.toInt64
  | .Const8 | .ConstBool => v.auxInt.toInt8.toInt64
  | _ => v.auxInt

def key (v : Value) : Key := ⟨v.op, keyFor v, v.aux, v.type⟩

/-- Phase 1 on block `b`. Fuel: each step advances `i` or removes a value from `b`. -/
def scanBlock (entry b : ID) (st : Func × Vals) : Func × Vals :=
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

namespace ZCSE

/-! ## The checker -/

open Sem in
/-- The names of the input parameters (`Sem.Ctx.make`'s `params`, without the rest of the
context). -/
def params (tabs : Tables) (f : Func) : Array (Option AuxRef) :=
  ((Sem.abiParams tabs f).filter (!·.out)).map (·.name)

/-- No arguments, not a `Phi`. -/
def argless (v : Value) : Bool := v.args.isEmpty && v.op != .Phi

/-- An argument-free value whose evaluation (`Sem.evalValue`) succeeds in every frame of a run
(the parameter names `ps`): not a root other than `InitMem`, and `Arg`/`ArgIntReg` name a
parameter. -/
def safe (tabs : Tables) (ps : Array (Option AuxRef)) (v : Value) : Bool :=
  argless v &&
  match v.op with
  | .InitMem => true
  | .Arg =>
    match v.aux with
    | some n => (ps.findIdx? (· == some n)).isSome
    | none => false
  | .ArgIntReg =>
    match v.aux.bind tabs.aux? with
    | some { kind := .nameOff n _, .. } => (ps.findIdx? (· == some n)).isSome
    | _ => false
  | .PanicBounds | .StaticLECall | .StaticCall | .Store | .StoreWB | .Move | .MoveWB | .Zero
  | .ZeroWB | .VarDef | .VarLive | .KeepAlive | .WBend | .NilCheck => false
  | op => !Sem.isRoot op

/-- `x` is an argument-free value of `g`'s entry block (where zcse's representatives live). -/
def entryArgless (g : Func) (x : ID) : Bool :=
  ((g.block? g.entry).map (·.values.contains x)).getD false && (g.value? x).any argless

/-- `fa` (of `f`) and `ga` (of `g`) are argument-free with the same op, aux, auxint and type. -/
def sameArgless (f g : Func) (fa ga : ID) : Bool :=
  match f.value? fa, g.value? ga with
  | some u, some w => argless u && argless w && u.op == w.op && u.aux == w.aux &&
      u.auxInt == w.auxInt && u.type == w.type
  | _, _ => false

/-- Value `x` of `f` and `g`: same ID, op, aux, auxint and type; each argument the same or
replaced by an argument-free value of `g`'s entry with the same key. -/
def valueOK (f g : Func) (x : ID) : Bool :=
  match f.value? x with
  | none => true
  | some fv =>
    match g.value? x with
    | none => false
    | some gv =>
      gv.id == fv.id && gv.op == fv.op && gv.aux == fv.aux && gv.auxInt == fv.auxInt &&
      gv.type == fv.type && gv.args.size == fv.args.size &&
      (List.range fv.args.size).all fun k =>
        fv.args[k]! == gv.args[k]! ||
          (entryArgless g gv.args[k]! && sameArgless f g fv.args[k]! gv.args[k]!)

/-- Block `bid` of `f` and `g`: same kind and controls; the values the same except for
argument-free values of `g`'s entry (moved there). -/
def blockOK (f g : Func) (bid : ID) : Bool :=
  match f.block? bid, g.block? bid with
  | some fb, some gb =>
    gb.kind == fb.kind && gb.controls == fb.controls &&
    fb.values.all (fun x => gb.values.contains x || entryArgless g x) &&
    gb.values.all (fun x => fb.values.contains x || entryArgless g x)
  | _, _ => false

/-- **zcse's output relation**, checked: `g` has `f`'s control-flow graph and blocks (kinds,
controls) and values (`valueOK`), except that argument-free values of `g`'s entry may come
from other blocks and replace argument-free arguments with the same key; those values
evaluate in every frame (`safe`). -/
def zrel (tabs : Tables) (f g : Func) : Bool :=
  DomCert.cfgView g == DomCert.cfgView f && g.ownAux == f.ownAux &&
  g.valueTab.size == f.valueTab.size &&
  f.blocks.all (blockOK f g) &&
  (((g.block? g.entry).map (·.values)).getD #[]).all (fun x =>
    !entryArgless g x || (g.value? x).any (safe tabs (params tabs g))) &&
  (List.range f.valueTab.size).all (valueOK f g)

end ZCSE

/-- `zcse`, validated by `ZCSE.zrel` (the input if the checker rejects the result). -/
def zcseChecked (tabs : Tables) (f : Func) : Func :=
  let g := zcse f
  if ZCSE.zrel tabs f g then g else f

/-- The `zero arg cse` pass. -/
def zcsePass : Pass := Pass.ofFunc fun env f => pure (zcseChecked env.tables f)

end GoFV.Opt

import GoFV.SSA.DomCert

/-!
# `wfDomCheck`: the slim input check of the checked CFG passes (issue #147)

The checked CFG passes (branchelim, early fuse) need of their input only well-formedness
(`GoFV.Proof.WF`) and use dominance on paths (`GoFV.Proof.Dom.UseDom`), together
`GoFV.Proof.Dom.WFDom`. `check` establishes both but also runs Go's type, aux and kind checks,
its dominator tree, loop nest, use counts and `memCheck`, and the argument-shape checks, which
these passes never use. `wfDomCheck` checks exactly what `WFDom` needs:

* `wfCheck`: the structural loops of `checkGo` — listed blocks are in the table with their ID,
  once; pred/succ edges are crosslinked; listed values are in the table with their ID, once;
  each value's per-op shape (`valueOK`: arity, `Phi` arity, `Bool` auxint range, its block);
  the entry is listed and has no predecessors; edges end at listed blocks; arguments and
  controls are listed values;
* `DomCert.check`: the dominator certificate, from which the proofs derive use dominance.

Soundness: `GoFV.Proof.wfDomCheck_wf`, `GoFV.Proof.Dom.WFDom.of_wfDomCheck`.
-/

namespace GoFV.SSA

namespace WFCheck

/-- The per-value shape facts `WF` needs: arity (`argLen`), a `Phi` has one argument per
predecessor of its block `b`, a `Bool` auxint is 0 or 1, and the value records block `b`. -/
def valueOK (b : Block) (v : Value) : Bool :=
  (v.op.argLen == -1 || (v.args.size : Int) == v.op.argLen) &&
    (v.op.auxType != .Bool || (decide (0 ≤ v.auxInt.toInt) && decide (v.auxInt.toInt ≤ 1))) &&
    v.block == b.id &&
    (v.op != .Phi || v.args.size == b.preds.size)

end WFCheck

open WFCheck in
/-- The structural checks of `checkGo` that `WF` needs (see the module doc). -/
def wfCheck (f : Func) : Except String Unit := do
  let mut blockMark : Array Bool := Array.replicate f.blockTab.size false
  let mut valueMark : Array Bool := Array.replicate f.valueTab.size false
  for bid in f.blocks do
    let some b := f.block? bid | throw s!"block b{bid} of f.Blocks is not in the block table"
    if b.id != bid then throw s!"block table entry b{bid} has ID {b.id}"
    if blockMark[bid]! then throw s!"block b{bid} appears twice"
    blockMark := blockMark.set! bid true
    for h : i in [0:b.preds.size] do
      let e := b.preds[i]
      match (f.block? e.b).bind (·.succs[e.i]?) with
      | some se =>
        if se.b != bid || se.i != i then
          throw s!"block pred/succ not crosslinked correctly {i}:b{bid} {se.i}:b{se.b}"
      | none => throw s!"block pred/succ not crosslinked correctly {i}:b{bid} (b{e.b}.Succs[{e.i}] missing)"
    for h : i in [0:b.succs.size] do
      let e := b.succs[i]
      match (f.block? e.b).bind (·.preds[e.i]?) with
      | some pe =>
        if pe.b != bid || pe.i != i then
          throw s!"block succ/pred not crosslinked correctly {i}:b{bid} {pe.i}:b{pe.b}"
      | none => throw s!"block succ/pred not crosslinked correctly {i}:b{bid} (b{e.b}.Preds[{e.i}] missing)"
    for vid in b.values do
      let some v := f.value? vid | throw s!"value v{vid} of b{bid} is not in the value table"
      if v.id != vid then throw s!"value table entry v{vid} has ID {v.id}"
      if !valueOK b v then throw s!"value v{vid} of b{bid}: bad arity, auxint or block"
      if valueMark[vid]! then throw s!"value v{vid} appears twice!"
      valueMark := valueMark.set! vid true
  if !(blockMark[f.entry]?.getD false) then throw s!"entry block b{f.entry} is missing"
  if (f.block? f.entry).any (!·.preds.isEmpty) then
    throw s!"entry block b{f.entry} has predecessor(s)"
  for bid in f.blocks do
    let some b := f.block? bid | continue
    for c in b.preds do
      if !(blockMark[c.b]?.getD false) then throw s!"predecessor block b{c.b} for b{bid} is missing"
    for c in b.succs do
      if !(blockMark[c.b]?.getD false) then throw s!"successor block b{c.b} for b{bid} is missing"
    for vid in b.values do
      let some v := f.value? vid | continue
      for a in v.args do
        if !(valueMark[a]?.getD false) then throw s!"v{a}, arg of v{vid}, is missing"
    for c in b.controls do
      if !(valueMark[c]?.getD false) then throw s!"control value for b{bid} is missing: v{c}"

/-- The input check of the checked CFG passes: `wfCheck`, then the dominator certificate. -/
def wfDomCheck (f : Func) : Except String Unit := do
  wfCheck f
  DomCert.check f

end GoFV.SSA

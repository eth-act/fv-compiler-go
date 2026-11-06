import GoFV.Opt.TabsAgreeMod
import GoFV.Proof.Pass.UnreadLRel

/-!
# Extended tables with extra frame temporaries, for a scheduled function (`tabsAgreeModL`)

`regalloc` (its `stackalloc`) gives spilled values new autos (`f.NewLocal`): the output tables
define `PAUTO` names the input's do not. The verified pipeline runs the input `f` of `regalloc`
(`runSched`) in the output tables, where `Sem.frameLocals` allocates a frame block for each of
them, so `LowerCheck.tabsAgreeL` (same frame) fails on every function that spills to a new slot.

`tabsAgreeModL tabs tabs' f` is `tabsAgreeMod` for `runSched` (and `runL`): the frame variables of
`tabs'` are those of `tabs` plus names `tabs` does not define, each non-forgeable (a `Blk.temp`
block, which no integer converts to and no value of `f` names); the values of `f` have the same
shapes in both tables, also the lowered ones (`Sem.typeShapesL`); every value is at its own ID
(`idsOK`); and every value is in the ops the proof covers (`tamOpOKL`): a memory- or tuple-shaped
argument only last, and only for the generic ops of `tamMemOps` or, on a memory-shaped last
argument, the arm64 memory ops of `UnreadL.armMemOps` (`elim unread autos`' fragment). The source
never points into the extra blocks, so its runs in `tabs'` have the same outcomes, for inputs that
hold no pointer into a frame temporary and contracts that cannot tell whether temporaries they have
no pointer to exist (`GoFV.Proof.runSched_tabsAgreeModL`).
-/

namespace GoFV.Opt

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof

/-- Value `fv` of a lowered function: a memory- or tuple-shaped argument only last, and only for
a generic op of `tamMemOps` or, on a memory-shaped last argument, an op of `UnreadL.armMemOps`
(any for a `Phi`). -/
def tamOpOKL (tabs : Tables) (f : Func) (fv : Value) : Bool :=
  fv.op == .Phi || fv.args.all (UnreadL.plainArg tabs f) ||
    (fv.args.pop.all (UnreadL.plainArg tabs f) &&
      (tamMemOps.contains fv.op ||
        (UnreadL.armMemOps.contains fv.op && UnreadL.memLast tabs f fv)))

/-- Every value of `f` is at its own ID. -/
def idsOK (f : Func) : Bool :=
  (List.range f.valueTab.size).all fun x => match f.value? x with
    | some v => v.id == x
    | none => true

/-- `tabsAgreeMod` for a scheduled (or lowered) function (see the module comment). -/
def tabsAgreeModL (tabs tabs' : Tables) (f : Func) : Bool :=
  let ps := abiParams tabs f
  let params := (ps.filter (!·.out)).map (·.name)
  let ls := frameLocals tabs params
  let ls' := frameLocals tabs' params
  let sh := typeShapes tabs
  let sh' := typeShapes tabs'
  let shL := typeShapesL tabs
  let shL' := typeShapesL tabs'
  decide ((abiParams tabs' f).toList = ps.toList) &&
  decide (deferInfo tabs' = deferInfo tabs) &&
  ps.toList.all (fun p => Ty.beq (tabs'.ty p.type) (tabs.ty p.type)) &&
  decide (ls'.toList.filter (fun l => (tabs.aux? l.1).isSome) = ls.toList) &&
  ls'.toList.all (fun l => (tabs.aux? l.1).isSome || !tabs'.forgeable l.1) &&
  ls.toList.all (fun l => tabs'.forgeable l.1 == tabs.forgeable l.1) &&
  outargsSize tabs' == outargsSize tabs &&
  f.valueTab.toList.all (fun o => Ty.beq (valueTy sh' o) (valueTy sh o) &&
    Ty.beq (valueTy shL' o) (valueTy shL o) && valueAuxAgree tabs tabs' o) &&
  idsOK f &&
  f.valueTab.toList.all fun o => match o with
    | some fv => tamOpOKL tabs f fv
    | none => true

end GoFV.Opt

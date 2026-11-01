import GoFV.Proof.Pass.CSESim
import GoFV.Proof.Pass.CopyElimSim
import GoFV.Proof.AtomSimDen
import GoFV.Proof.OrderRank
import GoFV.Proof.RunMono

/-!
# The conversion simulation: relation and obligations (issue #28)

`expand calls` keeps the control-flow graph and every value of its input (same ID, same block),
re-expresses some of them (an `Arg` as a `*Make` of its register pieces, a call result as a
`*Make` of `SelectN`s, a call on Go-typed arguments as one on register pieces, a function's
results as register pieces) and adds new values (pieces, selectors, frame values). The
simulation relates the frames at block entries by a **conversion** `cv x` per value: the
target's register of `x` refines `cv x` of the source's (`cv x = id` for most values; the
ABI encoding of the results for a call's tuple and for a `Ret` control).

`CvRel` is what the simulation needs of the pair `(f, g)`: the same CFG; per block the same
kind and controls, every source value listed in the same block of the target, new values
(`isNew`) that evaluate in any frame (pure or frame values), the same sequence of non-pure
nodes in both schedules and the `Feeds` condition of the panic transfer
(`Order.transfer_rank`), and per source value `x` the **local obligation** `Obl`: evaluating
the target's `x` (over new values that hold their own evaluations, `NewCons`, and the
converted registers of the source values `front x` it reaches) refines `cv x` of the source's
evaluation. `RR` relates the outcomes of `Ret`s (source results, target register pieces) and
`finish` turns it into refinement.
-/

namespace GoFV.Proof.EC

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Proof.AtomSim GoFV.Proof.Order

/-- A conversion of the source's register of each value into the one the target refines. -/
abbrev Cv := ID → Val → Val

/-- Refinement of results through a conversion: an evaluation that the source completes is
completed by the target with a refinement of the converted result; a panic alike. -/
inductive ResCv (c : Val → Val) : Res Val → Res Val → Prop where
  | ok {y y' : Val} : Sem.Refines (c y) y' → ResCv c (.ok y) (.ok y')
  | panic (e : Panic) {m m' : Mem} : Mem.Refines m m' → ResCv c (.panic e m) (.panic e m')
  | stuck (msg : String) (r : Res Val) : ResCv c (.stuck msg) r

/-- The target's new values `E` (closed under new arguments) each hold their own evaluation in
the frame `T`. -/
def NewCons (env : Env) (ctx : Ctx) (isNew : ID → Bool) (T : Frame) (E : ID → Prop) : Prop :=
  ∀ z, E z → isNew z = true ∧ ∃ w y, ctx.f.value? z = some w ∧
    (∀ a ∈ w.args, isNew a = true → E a) ∧ T.regs[z]? = some (some y) ∧
    evalValue env ctx T w = .ok y

/-- What a source register of value `x` holds: a value of the shape of `x`'s type, a tuple of
exactly one component per argument for a `MakeResult` (`evalValue` retypes the result of
`evalOp` at the value's shape; a tuple keeps its length), and never the result of a tail call
(`TailLECall*` is outside the semantics' phases: its evaluation is `stuck`). -/
def RegOK (ctx : Ctx) (x : ID) (y : Val) : Prop :=
  y.hasTy (ctx.tys[x]?.getD .other) = true ∧
    (∀ u vs, ctx.f.value? x = some u → u.op = .MakeResult → y = .tuple vs → vs.length = u.args.size) ∧
    ∀ u, ctx.f.value? x = some u → u.op ≠ .TailLECall ∧ u.op ≠ .TailLECallInter

/-- Every register of frame `fr` satisfies `RegOK`. -/
def RegsOK (ctx : Ctx) (fr : Frame) : Prop :=
  ∀ x y, fr.regs[x]? = some (some y) → RegOK ctx x y

/-- The source register of `z` holds the evaluation of `z`'s node in `f`. -/
def EcSrcHolds (env : Env) (tabs : Tables) (f : Func) (fr : Frame) (z : ID) : Prop :=
  ∀ u, f.value? z = some u → u.id = z ∧
    ∃ y, fr.regs[z]? = some (some y) ∧ evalValue env (Ctx.make tabs f) fr u = .ok y

/-- The target register of `z` holds the evaluation of `z`'s node in `g`. -/
def EcTgtHolds (env : Env) (tabs : Tables) (g : Func) (T : Frame) (z : ID) : Prop :=
  ∀ w, g.value? z = some w → w.id = z ∧
    ∃ y, T.regs[z]? = some (some y) ∧ evalValue env (Ctx.make tabs g) T w = .ok y

/-- The values whose source registers hold their evaluations when `x` of block `fb` is
evaluated: values of `fb` that `x` depends on in the target's block `gb`, and the non-`Phi`
values placed in strict dominators of `fb` (`Avail.DInv`). -/
def Held (f g : Func) (fb gb : Block) (x z : ID) : Prop :=
  (z ∈ fb.values ∧ Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList) z x) ∨
    ∃ v, Placed f z v ∧ v.op ≠ .Phi ∧ Anc (make f) v.block fb.id ∧ v.block ≠ fb.id

/-- `z` is a non-`Phi` value of `g` placed in a strict dominator of block `gb` (its target
register holds its evaluation in `gb`, `Avail.DInv` on the target). -/
def SDomPlaced (g : Func) (gb : Block) (z : ID) : Prop :=
  ∃ v, Placed g z v ∧ v.op ≠ .Phi ∧ Anc (make g) v.block gb.id ∧ v.block ≠ gb.id

/-- The values whose target registers hold their evaluations when `x` of block `gb` is
evaluated: nodes of `gb` that `x` depends on, and the values `SDomPlaced` in `g`. -/
def HeldT (g : Func) (gb : Block) (x z : ID) : Prop :=
  Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList) z x ∨ SDomPlaced g gb z

/-- **The local obligation of value `x`.** In frames of one activation, where the source's
arguments of `x` have registers (each `RegOK`) and the target's arguments of `x` too (its new
ones holding their evaluations), the target's registers of the source values `front` refine
their conversions, the source's registers of the values `heldS` and the target's of `heldT`
hold their evaluations, the target's evaluation of `x` refines the conversion of the source's. -/
def Obl (tabs : Tables) (f g : Func) (cv : Cv) (isNew : ID → Bool) (front : List ID)
    (heldS heldT : ID → Prop) (x : ID) : Prop :=
  ∀ u w, f.value? x = some u → g.value? x = some w →
  ∀ env : Env, env.Mono → ∀ frS T : Frame, T = { frS with regs := T.regs } →
  RegsOK (Ctx.make tabs f) frS →
  ∀ E : ID → Prop, NewCons env (Ctx.make tabs g) isNew T E →
    (∀ a ∈ w.args, isNew a = true → E a) → (∀ a ∈ w.args, Reg T a) → (∀ a ∈ u.args, Reg frS a) →
    (∀ a ∈ front, ∀ y, frS.regs[a]? = some (some y) →
      ∃ y', T.regs[a]? = some (some y') ∧ Sem.Refines (cv a y) y') →
    (∀ z, heldS z → EcSrcHolds env tabs f frS z) → (∀ z, heldT z → EcTgtHolds env tabs g T z) →
    ResCv (cv x) (evalValue env (Ctx.make tabs f) frS u) (evalValue env (Ctx.make tabs g) T w)

/-- A new value evaluates in every frame whose argument images are complete, whatever its
arguments' registers (pure values and frame values). -/
def NewEval (tabs : Tables) (g : Func) (w : Value) : Prop :=
  ∀ (env : Env) (fr : Frame) (argv : List Val), fr.images.size = (Ctx.make tabs g).params.size →
    ∃ y, evalOp env (Ctx.make tabs g) fr w argv (tabs.ty w.type) = .ok y

/-- The source has reached its value `c` in frame `G`: `c`'s evaluation completed or panicked. -/
def Reached (env : Env) (tabs : Tables) (f : Func) (G : Frame) (c : ID) : Prop :=
  ∀ u, f.value? c = some u →
    (∃ y, evalValue env (Ctx.make tabs f) G u = .ok y) ∨
      ∃ e m, evalValue env (Ctx.make tabs f) G u = .panic e m

/-- **The obligation of a new value `z` anchored at source value `c`** (a store of a stack
argument of call `c`): in frames of one activation where the source has reached `c`, `z`'s
arguments have registers (its new ones holding their evaluations), the target's registers of
the source values `front` refine their conversions and the target's of `heldT` hold their
evaluations, the target evaluates `z`. -/
def NewObl (tabs : Tables) (f g : Func) (cv : Cv) (isNew : ID → Bool) (front : List ID)
    (heldT : ID → Prop) (c z : ID) : Prop :=
  ∀ w, g.value? z = some w →
  ∀ env : Env, ∀ G T : Frame, T = { G with regs := T.regs } →
  ∀ E : ID → Prop, NewCons env (Ctx.make tabs g) isNew T E →
    (∀ a ∈ w.args, isNew a = true → E a) → (∀ a ∈ w.args, Reg T a) →
    (∀ a ∈ front, ∀ y, G.regs[a]? = some (some y) →
      ∃ y', T.regs[a]? = some (some y') ∧ Sem.Refines (cv a y) y') →
    (∀ a, heldT a → EcTgtHolds env tabs g T a) → Reached env tabs f G c →
    ∃ y, evalValue env (Ctx.make tabs g) T w = .ok y

/-- New value `z` of block `gb` is anchored at a source value `c` of `fb`: its obligation
`NewObl` (with a `front` of source values that reach it in `gb`, and the values `HeldT` in `g`),
and in `g`'s schedule no source non-pure node lies between `z` and `c` (`z` runs only when the
source reaches `c`). -/
def AnchoredAt (tabs : Tables) (f g : Func) (cv : Cv) (isNew : ID → Bool) (fb gb : Block)
    (z : ID) : Prop :=
  ∃ c ∈ fb.values, ∃ fr : List ID, NewObl tabs f g cv isNew fr (HeldT g gb z) c z ∧
    (∀ a ∈ fr, isNew a = false ∧ (a ∈ gb.values → (∃ w, g.value? a = some w ∧ w.op = .Phi) ∨
      Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList) a z)) ∧
    ∀ og, schedule g gb = some og → ∀ A B, og.toList = A ++ z :: B →
      ∃ P Q, B = P ++ c :: Q ∧ ∀ y ∈ P, npIn (schedNodes f fb).toList y = false

/-- What a `Ret` terminator reads of its control: the results and the memory. -/
def retOf : Val → Option (List Val × Mem)
  | .tuple vs =>
    match vs.getLast?, vs.dropLast with
    | some (.mem m), rs => if rs.any (fun | .poison => true | _ => false) then none else some (rs, m)
    | _, _ => none
  | _ => none

/-- The values listed in the entry block of `g`. -/
def EntryVal (g : Func) (x : ID) : Prop := ∃ eb, g.block? g.entry = some eb ∧ x ∈ eb.values

/-- Two `Phi`s that evaluate alike: the same op, arguments and type (use counts and positions
may differ). -/
def PhiSame (u w : Value) : Prop := w.op = u.op ∧ w.args = u.args ∧ w.type = u.type

section
variable (tabs : Tables) (f g : Func) (cv : Cv) (isNew : ID → Bool) (front : ID → List ID)
  (RR : List Val → Mem → List Val → Mem → Prop)

/-- One block of the conversion simulation. -/
structure CvBlock (fb gb : Block) : Prop where
  kind : gb.kind = fb.kind
  controls : gb.controls = fb.controls
  common : ∀ x ∈ fb.values, x ∈ gb.values ∧ isNew x = false
  fresh : ∀ x ∈ gb.values, x ∉ fb.values → isNew x = true
  phiT : ∀ x ∈ gb.values, ∀ w, g.value? x = some w → w.op = .Phi →
    x ∈ fb.values ∧ ∃ u, f.value? x = some u ∧ PhiSame u w
  phiS : ∀ x ∈ fb.values, ∀ u, f.value? x = some u → u.op = .Phi →
    (∃ w, g.value? x = some w ∧ PhiSame u w) ∧ (∀ y, cv x y = y) ∧ ∀ a ∈ u.args, ∀ y, cv a y = y
  sched : ∃ of og, schedule f fb = some of ∧ schedule g gb = some og ∧
    of.toList.filter (npIn (schedNodes f fb).toList) = og.toList.filter (npIn (schedNodes f fb).toList)
  feeds : ∀ a y, NodeIn (schedNodes f fb).toList a → NodeIn (schedNodes f fb).toList y →
    a ∈ argsOf (schedNodes f fb).toList y → NodeIn (schedNodes g gb).toList y →
    Feeds (NodeIn (schedNodes f fb).toList) (NodeIn (schedNodes g gb).toList)
      (argsOf (schedNodes f fb).toList) (argsOf (schedNodes g gb).toList)
      (PureIn (schedNodes f fb).toList) y a
  obl : ((make f).depthOf fb.id).isSome → ∀ x ∈ fb.values, ∀ u, f.value? x = some u →
    u.op ≠ .Phi → Obl tabs f g cv isNew (front x) (Held f g fb gb x) (HeldT g gb x) x
  front : ∀ x ∈ fb.values, ∀ u, f.value? x = some u → u.op ≠ .Phi → ∀ a ∈ front x, isNew a = false ∧
    (a ∈ gb.values → (∃ w, g.value? a = some w ∧ w.op = .Phi) ∨
      Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList) a x)
  ctrl : fb.kind = .If ∨ fb.kind = .JumpTable → ∀ c ∈ fb.controls, ∀ y, cv c y = y
  ret : fb.kind = .Ret → ∀ c, fb.controls[0]? = some c → ∀ y y', RegOK (Ctx.make tabs f) c y →
    Sem.Refines (cv c y) y' →
    ∀ rs m, retOf y = some (rs, m) → Val.anyPoison rs = false →
      ∃ rs' m', retOf y' = some (rs', m') ∧ RR rs m rs' m'
  newOK : ∀ z ∈ gb.values, isNew z = true → ∀ w, g.value? z = some w → w.op ≠ .Phi ∧
    (NewEval tabs g w ∨ AnchoredAt tabs f g cv isNew fb gb z)
  newArgs : ∀ z ∈ gb.values, ∀ w, g.value? z = some w → ∀ a ∈ w.args,
    isNew a = true → a ∈ gb.values ∨ EntryVal g a ∨ SDomPlaced g gb a

/-- **The conversion simulation's relation** between a function `f` and its rewrite `g`. -/
structure CvRel : Prop where
  cfg : cfgView g = cfgView f
  ownAux : g.ownAux = f.ownAux
  block : ∀ bid ∈ f.blocks, ∀ fb, f.block? bid = some fb → ∃ gb, g.block? bid = some gb ∧
    CvBlock tabs f g cv isNew front RR fb gb
  finish : ∀ rs m rs' m', RR rs m rs' m' →
    (finish (Ctx.make tabs f).outs 0 (.returned rs m)).Defined →
    OutcomeRefines 0 (finish (Ctx.make tabs f).outs 0 (.returned rs m))
      (finish (Ctx.make tabs f).outs 0 (.returned rs' m'))

end

end GoFV.Proof.EC

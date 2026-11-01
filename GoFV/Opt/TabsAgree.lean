import GoFV.SSA.Sem.Run
import GoFV.SSA.Sem.TyEq

/-!
# Extended tables that a function cannot tell apart (`tabsAgree`)

Passes such as `expand calls` and `decompose builtin` extend the definition tables (new types,
auxes and slots at fresh numbers). Their refinement theorems run the source function in the
input tables. `tabsAgree tabs tabs' f` checks that running `f` in `tabs'` instead of `tabs` gives
the same outcome (`GoFV.Proof.run_tabsAgree`): every lookup the semantics makes in the tables for
`f` gives the same result in both.

* The context `Sem.Ctx.make` builds: the ABI assignments of `f.OwnAux` (`abiParams`) and the
  shapes of their types, the frame variables (`frameLocals`, which reads every aux of the
  tables) and whether their blocks are forgeable, the size of the outgoing-arguments area
  (`outargsSize`, every call aux), and the shape of each value's type (`typeShapes`).
* For the aux of every value (`auxAgree`): its definition (`ArgIntReg`, `Addr`, `ConstString`,
  `LocalAddr`/`VarDef` frame blocks), the callee symbol of an `*AuxCall` (`Tables.callee?`), the
  shape a type aux names (`auxTy`) and the shapes of the types of its ABI parameters
  (`decodeArgs`, `encodeResults`, `retypeResults`).

Structural recursion over lists only (no hash maps): the check runs compiled and in the kernel.
-/

namespace GoFV.Opt

open GoFV.SSA GoFV.SSA.Sem

/-- The lookups of aux `a` agree in `tabs` and `tabs'`: its definition, callee symbol, the shape
of the type it names, and the shapes of its ABI parameters' types. -/
def auxAgree (tabs tabs' : Tables) (a : AuxRef) : Bool :=
  decide (tabs'.aux? a = tabs.aux? a) &&
  decide (tabs'.callee? a = tabs.callee? a) &&
  Ty.beq (auxTy tabs' (some a)) (auxTy tabs (some a)) &&
  match callABI? tabs (some a) with
  | some abi => abi.params.toList.all fun p => Ty.beq (tabs'.ty p.type) (tabs.ty p.type)
  | none => true

/-- `auxAgree` for the aux of a value-table entry (true for absent values and nil auxes). -/
def valueAuxAgree (tabs tabs' : Tables) : Option Value → Bool
  | some { aux := some a, .. } => auxAgree tabs tabs' a
  | _ => true

/-- Running `f` in `tabs'` gives the same outcomes as running it in `tabs`: `Ctx.make`
computes the same context (up to the tables) and every lookup through the auxes of `f`'s values
agrees (`GoFV.Proof.run_tabsAgree`). -/
def tabsAgree (tabs tabs' : Tables) (f : Func) : Bool :=
  let ps := abiParams tabs f
  let params := (ps.filter (!·.out)).map (·.name)
  let ls := frameLocals tabs params
  let sh := typeShapes tabs
  let sh' := typeShapes tabs'
  decide ((abiParams tabs' f).toList = ps.toList) &&
  ps.toList.all (fun p => Ty.beq (tabs'.ty p.type) (tabs.ty p.type)) &&
  decide ((frameLocals tabs' params).toList = ls.toList) &&
  ls.toList.all (fun l => tabs'.forgeable l.1 == tabs.forgeable l.1) &&
  outargsSize tabs' == outargsSize tabs &&
  f.valueTab.toList.all fun o => Ty.beq (valueTy sh' o) (valueTy sh o) && valueAuxAgree tabs tabs' o

end GoFV.Opt

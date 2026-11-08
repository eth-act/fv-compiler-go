import GoFV.Opt.DecPhiCheck
import GoFV.Opt.TabsAgreeMod
import GoFV.Opt.RewriteCheck
import GoFV.Rules.Proven
import GoFV.Proof.Cong

variable [GoFV.SSA.Sem.Addrs]

/-!
# decompose user, decompose builtin: the checked fragment (issue #17)

The two passes are checked in stages, every stage under the pass's output tables `T`:

- the output tables only add frame names the input cannot tell from its own (`tabsAgreeMod`
  of the input tables and `T`);
- the phi splits (`phiStage`) are related to the input by `DecPhiCheck.decPhiCheck`;
- decompose builtin's dec-rule rewrite is re-run with the proven dec rules
  (`Rules.Proven.dec`) and validated in layers (`RewriteCheck.layersOK` with
  `RewriteCheck.decLayers`: its value-rule `Load` expansions, then its `Store` splits, then
  `RewriteCheck.validate` with the other events), and must give the pass's output up to
  positions, use counts, caches and the name bookkeeping (`stripNames`), which the semantics
  never reads. A log with phi eliminations is checked in segments between them, as the rewrite
  validator does (`RewriteCheck.segsOK`): `decSegsOK`.

`decUserFrag`/`decBuiltinFrag` look only at the pass input (a pass error is in the fragment,
the pass then has no output), like `daeFrag`.
-/

namespace GoFV.Opt.Decompose

open GoFV.SSA GoFV.Proof

/-- `f` without `f.Names`, `NamedValues` and the canonical splits and slots. -/
def stripNames (f : Func) : Func := { f with names := #[], namedx := #[], splits := #[], canon := #[] }

/-- `f` and `g` have the same code: equal up to positions, use counts, caches and names. -/
def sameCode (f g : Func) : Bool := decide (eraseF (stripNames f) = eraseF (stripNames g))

/-- The proven dec rules. -/
def decProvenTable : Rules.Interp.Table := Rules.Interp.Table.ofRuleSet Rules.Proven.dec

/-- The check environment of the output tables `T`. -/
def decCheckEnv (env : PassEnv) (T : Tables) : CheckEnv := { tabs := T, typs := env.typs }

/-- decompose user's output `out` of `f` is checked: the tables only add unforgeable frame
names, and the function is `f` with its phis split. -/
def decUserOK (env : PassEnv) (f : Func) (out : PassOut) : Bool :=
  tabsAgreeMod env.tables out.tables f && DecPhiCheck.decPhiCheck out.tables f out.func

def decUserFrag (env : PassEnv) (f : Func) : Bool :=
  match decomposeUserPass env f with
  | .error _ => true
  | .ok out => decUserOK env f out

/-- `RewriteCheck.segsOK` with the decompose layers: the segments of the log `evs` between its phi
eliminations (`seg`: the events of the current one, from `f`), each accepted by `layersOK` with
`RewriteCheck.decLayers` against the function logged at the phi elimination ending it (without
`Invalid` values, `h`), which passes `check` and is related by copyelim's relation to `h` with
the `Phi` turned copy (`h'`, which passes `check`), where the next segment starts; the last
segment ends at `g2`. -/
def decSegsOK (env : PassEnv) (T : Tables) (f0 g2 : Func) :
    Func → Array Rules.RwEvent → List Rules.RwEvent → Bool
  | f, seg, [] =>
    RewriteCheck.layersOK env decProvenTable f0 { func := g2, tables := T } RewriteCheck.decLayers f seg
  | f, seg, .phielim v d pre :: evs =>
    let h := RewriteCheck.dropInvalid pre
    let h' := RewriteCheck.phiElim h v d.args[0]!
    RewriteCheck.layersOK env decProvenTable f0 { func := h, tables := T } RewriteCheck.decLayers f seg &&
      checkOK (decCheckEnv env T) h && CopyCheck.copyOK T h h' && checkOK (decCheckEnv env T) h' &&
      decSegsOK env T f0 g2 h' #[] evs
  | f, seg, ev :: evs => decSegsOK env T f0 g2 f (seg.push ev) evs

/-- The rewrite stage `g1` → `g2` (log `log`) in the output tables `T` (`decSegsOK`). -/
def decRewriteOK (env : PassEnv) (T : Tables) (g1 g2 : Func) (log : Array Rules.RwEvent) : Bool :=
  decSegsOK env T g1 g2 g1 #[] log.toList

/-- The checks of decompose builtin's stages, given the phi stage `g1` of `f`, the proven
dec rules' rewrite `g2` of `g1` with its log, and the pass output `out`: `g1` is `f` with its
phis split, `g2` is a rewrite of `g1` validated in layers (`decRewriteOK`) with `out`'s code, and
the tables only add unforgeable frame names. -/
def decBuiltinStagesOK (env : PassEnv) (f g1 g2 : Func) (log : Array Rules.RwEvent)
    (out : PassOut) : Bool :=
  let T := out.tables
  tabsAgreeMod env.tables T f && DecPhiCheck.decPhiCheck T f g1 &&
    (check (decCheckEnv env T) g1).isOk && (check (decCheckEnv env T) g2).isOk &&
    decRewriteOK env T g1 g2 log && sameCode g2 out.func

/-- decompose builtin's output `out` of `f` is checked (`decBuiltinStagesOK` of the phi stage
`phiStage` and the proven dec rules' rewrite of it). -/
def decBuiltinOK (env : PassEnv) (f : Func) (out : PassOut) : Bool :=
  match phiStage env true f with
  | .error _ => false
  | .ok (t1, g1) =>
    match Rules.rewriteRun decProvenTable false true { env with tables := t1 } g1 with
    | .error _ => false
    | .ok (o2, _, log) => decBuiltinStagesOK env f g1 o2.func log out

def decBuiltinFrag (env : PassEnv) (f : Func) : Bool :=
  match postExpandCallsDecomposePass env f with
  | .error _ => true
  | .ok out => decBuiltinOK env f out

end GoFV.Opt.Decompose

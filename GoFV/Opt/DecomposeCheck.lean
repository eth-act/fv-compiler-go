import GoFV.Opt.DecPhiCheck
import GoFV.Opt.TabsAgreeMod
import GoFV.Opt.RewriteCheck
import GoFV.Rules.Proven
import GoFV.Proof.Cong

/-!
# decompose user, decompose builtin: the checked fragment (issue #17)

The two passes are checked in stages, every stage under the pass's output tables `T`:

- the output tables only add frame names the input cannot tell from its own (`tabsAgreeMod`
  of the input tables and `T`);
- the phi splits (`phiStage`) are related to the input by `DecPhiCheck.decPhiCheck`;
- decompose builtin's dec-rule rewrite is re-run with the proven dec rules
  (`Rules.Proven.dec`) and validated (`RewriteCheck.validate`), and must give the pass's
  output up to positions, use counts, caches and the name bookkeeping (`stripNames`), which
  the semantics never reads.

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

/-- decompose builtin's output `out` of `f` is checked: the phi stage `g1` (`phiStage`) is `f`
with its phis split, the proven dec rules rewrite `g1` to a validated `g2` with `out`'s
code, and the tables only add unforgeable frame names. -/
def decBuiltinOK (env : PassEnv) (f : Func) (out : PassOut) : Bool :=
  match phiStage env true f with
  | .error _ => false
  | .ok (t1, g1) =>
    match Rules.rewriteRun decProvenTable false true { env with tables := t1 } g1 with
    | .error _ => false
    | .ok (o2, _, log) =>
      let T := out.tables
      tabsAgreeMod env.tables T f && DecPhiCheck.decPhiCheck T f g1 &&
      (check (decCheckEnv env T) g1).isOk && (check (decCheckEnv env T) o2.func).isOk &&
      tabsAgree T T g1 && RewriteCheck.validate T decProvenTable g1 o2.func log &&
      sameCode o2.func out.func

def decBuiltinFrag (env : PassEnv) (f : Func) : Bool :=
  match postExpandCallsDecomposePass env f with
  | .error _ => true
  | .ok out => decBuiltinOK env f out

end GoFV.Opt.Decompose

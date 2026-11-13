import GoFV.Proof.Rules.Den
import GoFV.Proof.Rules.OpVal

variable [GoFV.SSA.Sem.Addrs]

/-!
# The obligation of a value rule over table-evaluated nodes (issue #151)

`Rule.Sound` (`Den.lean`) denotes every op node by `evalPure`. `Addr {sym}` and
`ConstString {str}` are evaluated from the definition tables (`opVal`, `Sem.frameVal`), so a rule
over them (`generic.rules:1022` `(ConstString {str}) => (StringMake (Addr {fe.StringData(str)}
(SB)) (Const64 [len(str)]))`, nil checks of `Addr`) needs the denotation with `opVal`, for all
tables: `Pat.denT`, `nodeDenT`, `resDenT`, and `Rule.SoundT`. The frame facts a rule may use
are facts about the tables and the aux fields, which the rewrite validator checks on the
instance (`FrameOK`): `fe.StringData(str)` names a symbol whose name is the data symbol of the
string aux `str`, `len(str)` is its length, an aux `{s}` of a built node is the aux bound to `s`
(`(StringPtr (StringMake (Addr {s} base) _)) => (Addr {s} base)`), and a condition's conjunct
`str == ""` holds of the string aux bound to `str` (the aux is not a rule value, so `evalE`
leaves the comparison to the oracle).

`Rule.soundT_of_sound`: a `Rule.Sound` rule without table-evaluated nodes (`Rule.pure`) satisfies
`Rule.SoundT` (the two denotations agree). The rewrite validator's soundness uses `Rule.SoundT`
only (`RuleSet.AllSound`).
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

/-! ## Denotation -/

mutual
/-- `Pat.den` with `opVal tabs`. -/
def Pat.denT (tabs : Tables) (e : PEnv) (p : Path) : Pat → Val
  | .op o _ _ _ _ _ args _ =>
    (opVal tabs o (e.ty p) (e.auxInt p) (e.aux p) (Pat.densT tabs e p 0 args)).retype (e.ty p)
  | _ => e.leaf p
def Pat.densT (tabs : Tables) (e : PEnv) (p : Path) (i : Nat) : List Pat → List Val
  | [] => []
  | q :: qs => Pat.denT tabs e (i :: p) q :: Pat.densT tabs e p (i + 1) qs
end

/-- The value of the top node before `retype`. -/
def Pat.rawT (tabs : Tables) (e : PEnv) : Pat → Val
  | .op o _ _ _ _ _ args _ =>
    opVal tabs o (e.ty []) (e.auxInt []) (e.aux []) (Pat.densT tabs e [] 0 args)
  | _ => e.leaf []

mutual
/-- `Pat.binds` with `Pat.denT` for named op nodes. -/
def Pat.bindsT (tabs : Tables) (e : PEnv) (p : Path) : Pat → List (Nat × DV)
  | .wild | .same _ => []
  | .bind x => [(x, .val (e.leaf p) (some p))]
  | pat@(.op o name ty ai _ _ args _) =>
    (match name with | some x => [(x, .val (Pat.denT tabs e p pat) (some p))] | none => []) ++
    (match ty with | .bind x => [(x, .ty (e.ty p))] | _ => []) ++
    (match ai with | .bind x => [(x, auxIntDV o.auxType (e.auxInt p))] | _ => []) ++
    Pat.bindssT tabs e p 0 args
def Pat.bindssT (tabs : Tables) (e : PEnv) (p : Path) (i : Nat) : List Pat → List (Nat × DV)
  | [] => []
  | q :: qs => Pat.bindsT tabs e (i :: p) q ++ Pat.bindssT tabs e p (i + 1) qs
end

/-- The rule variables' values (`sigma` with `Pat.denT`). -/
def sigmaT (tabs : Tables) (e : PEnv) (pat : Pat) (x : Nat) : DV :=
  ((Pat.bindsT tabs e [] pat).lookup x).getD .other

/-- `nodeDen` with `opVal tabs`. -/
def nodeDenT (tabs : Tables) (ev : Expr → DV) (or : Oracle) (σ : Nat → DV) (topTy : Ty)
    (nodes : List RNode) : Nat → Nat → Val
  | 0, _ => .poison
  | fuel + 1, k =>
    match nodes[k]? with
    | none => .poison
    | some n =>
      let t := match n.ty with
        | some te => match ev te with
          | .ty t => t
          | _ => or.ty te
        | none => topTy
      let ai := match n.auxInt with
        | some ae => (toAuxIntD n.op.auxType (ev ae)).getD (or.auxInt ae)
        | none => 0
      let ax := match n.aux with
        | some xe => or.aux xe
        | none => none
      let argv := n.args.map fun
        | .var x => (σ x).valOr (or.val (.var x))
        | .node j => nodeDenT tabs ev or σ topTy nodes fuel j
        | .expr e => (ev e).valOr (or.val e)
      (opVal tabs n.op t ai ax argv).retype t

/-- The value `v` has after the rewrite (`resDen` with `nodeDenT`). -/
def resDenT (tabs : Tables) (ev : Expr → DV) (or : Oracle) (σ : Nat → DV) (topTy : Ty) :
    Result → Val
  | .copy ce => match ev ce with
    | .val w _ => w
    | _ => or.val ce
  | .build nodes => nodeDenT tabs ev or σ topTy nodes nodes.length 0
  | .setOp o => or.val (.op o)

/-! ## Frame helpers -/

/-- The name of the symbol aux `a`. -/
def symName? (tabs : Tables) (a : Option AuxRef) : Option GoStr :=
  match a.bind tabs.aux? with
  | some { kind := .sym name .., .. } => some name
  | _ => none

/-- The string and data symbol of the string aux `a`. -/
def strAux? (tabs : Tables) (a : Option AuxRef) : Option (GoStr × GoStr) :=
  match a.bind tabs.aux? with
  | some { kind := .str s d, .. } => some (s, d)
  | _ => none

/-- `fe.StringData(x)` of a rule variable. -/
def strDataVar? : Expr → Option Nat
  | .method (.rsv .fe) "StringData" [.var x] _ => some x
  | _ => none

/-- `int64(len(x))` of a rule variable. -/
def lenVar? : Expr → Option Nat
  | .conv .int64 (.builtin "len" [.var x] _) => some x
  | _ => none

/-- An aux `{x}` of a rule variable. -/
def auxVar? : Expr → Option Nat
  | .var x => some x
  | _ => none

/-- The amount `b` of an auxint shift `a << b` or `a >> b`. -/
def shiftAmt? : Expr → Option Expr
  | .binop .shl _ b _ | .binop .shr _ b _ => some b
  | _ => none

/-- The rule variables `x` of the condition's conjuncts `x == ""` (`&&` chains). -/
def emptyStrVars : Expr → List Nat
  | .binop .land a b _ => emptyStrVars a ++ emptyStrVars b
  | .binop .eq (.var x) (.lit _ (.str "")) _ => [x]
  | _ => []

/-- The rule variables `(x, y)` of the condition's conjuncts `isSamePtr(x, y)` (`&&` chains). -/
def samePtrVars : Expr → List (Nat × Nat)
  | .binop .land a b _ => samePtrVars a ++ samePtrVars b
  | .call "isSamePtr" [.var x, .var y] _ => [(x, y)]
  | _ => []

/-- The rule variables `x` of the condition's conjuncts `x.NumElem() == 1` (`&&` chains). -/
def numElem1Vars : Expr → List Nat
  | .binop .land a b _ => numElem1Vars a ++ numElem1Vars b
  | .binop .eq (.method (.var x) "NumElem" [] _) (.lit _ (.int 1)) _ => [x]
  | _ => []

/-- The rule variables `x` of the condition's conjuncts `x.Size() == 0` (`&&` chains). -/
def size0Vars : Expr → List Nat
  | .binop .land a b _ => size0Vars a ++ size0Vars b
  | .binop .eq (.method (.var x) "Size" [] _) (.lit _ (.int 0)) _ => [x]
  | _ => []

/-- The field binds variable `x`. -/
def _root_.GoFV.Rules.Field.bindsVar (f : GoFV.Rules.Field) (x : Nat) : Bool :=
  match f with
  | .bind y => y == x
  | _ => false

mutual
/-- The position of the first op node whose aux field binds variable `x`. -/
def Pat.auxPos (x : Nat) (p : Path) : Pat → Option Path
  | .op _ _ _ _ ax _ args _ => if ax.bindsVar x then some p else Pat.auxPoss x p 0 args
  | _ => none
def Pat.auxPoss (x : Nat) (p : Path) (i : Nat) : List Pat → Option Path
  | [] => none
  | q :: qs => (Pat.auxPos x (i :: p) q).orElse fun _ => Pat.auxPoss x p (i + 1) qs
end

/-- The nodes a result builds. -/
def _root_.GoFV.Rules.Result.nodes : Result → List RNode
  | .build ns => ns
  | _ => []

/-- The frame helpers of the result hold of the instance: an aux `fe.StringData(x)` names the
data symbol of the (non-empty) string aux bound to `x`, an auxint `int64(len(x))` is its length
(as `nodeDenT` selects it), an aux `{x}` is the aux bound to `x`, an auxint shift `a << b` or
`a >> b` shifts by a nonnegative amount (Go panics on a negative one, so the rewriter built no
such node); a conjunct `x == ""` of the condition holds of the string aux bound to `x`; a
conjunct `isSamePtr(x, y)` of leaves `x`, `y` holds of their values (the validator: the same
value); a conjunct `x.NumElem() == 1` makes the type `x` a one-element array, whose shape
(`Sem.tyOf`) is an aggregate of one field at offset 0 that fills it; a conjunct `x.Size() == 0`
makes the type `x` of size 0, whose shape (`Sem.tyOf` of a zero-size struct or array) is
`.empty`; the positions of `sameLeaves r` hold the same value; and the leaves of
`nonNegLeaves r` are nonnegative integers or `poison`. -/
def FrameOK (tabs : Tables) (e : PEnv) (ev : Expr → DV) (or : Oracle) (r : Rule) : Prop :=
  (∀ n ∈ r.result.nodes,
    (∀ xe x, n.aux = some xe → strDataVar? xe = some x →
      ∃ p s d, Pat.auxPos x [] r.pat = some p ∧ strAux? tabs (e.aux p) = some (s, d) ∧
        s.size ≠ 0 ∧ symName? tabs (or.aux xe) = some d) ∧
    (∀ ae x, n.auxInt = some ae → lenVar? ae = some x →
      ∃ p s d, Pat.auxPos x [] r.pat = some p ∧ strAux? tabs (e.aux p) = some (s, d) ∧
        (toAuxIntD n.op.auxType (ev ae)).getD (or.auxInt ae) = Int64.ofNat s.size) ∧
    (∀ xe x, n.aux = some xe → auxVar? xe = some x →
      ∃ p, Pat.auxPos x [] r.pat = some p ∧ or.aux xe = e.aux p) ∧
    (∀ ae b, n.auxInt = some ae → shiftAmt? ae = some b → ∃ i, ev b = .int i ∧ 0 ≤ i)) ∧
  (∀ x ∈ (r.cond.map emptyStrVars).getD [],
    ∃ p s d, Pat.auxPos x [] r.pat = some p ∧ strAux? tabs (e.aux p) = some (s, d) ∧ s.size = 0) ∧
  (∀ xy ∈ (r.cond.map samePtrVars).getD [],
    ∃ p q, Pat.leafPos xy.1 [] r.pat = some p ∧ Pat.leafPos xy.2 [] r.pat = some q ∧
      e.leaf p = e.leaf q) ∧
  (∀ x ∈ (r.cond.map numElem1Vars).getD [], ∃ f, ev (.var x) = .ty (.agg [(0, f)] f.size)) ∧
  (∀ x ∈ (r.cond.map size0Vars).getD [], ev (.var x) = .ty .empty) ∧
  (∀ pq ∈ sameLeaves r, e.leaf pq.1 = e.leaf pq.2) ∧
  ∀ p ∈ nonNegLeaves r, (e.leaf p).nonNeg = true

/-- **The obligation of a value rule over table-evaluated nodes**: `Rule.Sound` with the
denotation `opVal tabs`, for all tables, under the frame helpers' facts (`FrameOK`). -/
def Rule.SoundT (r : Rule) : Prop :=
  Pat.arityOk r.pat = true ∧
  ∀ (tabs : Tables) (e : PEnv) (or : Oracle), Oracle.BoolTyped or →
    let σ := sigmaT tabs e r.pat
    let ev := evalE (r.vars.map (·.ty)) σ or e (Pat.denT tabs e [] r.pat)
    FrameOK tabs e ev or r →
    Pat.wf e [] r.pat →
    Pat.cons ev σ e [] r.pat →
    condHolds ev r.cond →
    (Pat.rawT tabs e r.pat).hasTy (e.ty []) = true →
    Pat.typed e [] r.pat →
    Pat.argsOK e.ty [] r.pat = true →
    Pat.nonNegOK e r.pat r.cond = true →
    Refines (Pat.rawT tabs e r.pat) (resDenT tabs ev or σ (e.ty []) r.result)

/-! ## Rules without table-evaluated nodes -/

mutual
/-- No op node of the pattern is evaluated from the tables. -/
def Pat.pure : Pat → Bool
  | .op o _ _ _ _ _ args _ => !frameOp o && Pat.pures args
  | _ => true
def Pat.pures : List Pat → Bool
  | [] => true
  | q :: qs => Pat.pure q && Pat.pures qs
end

/-- Neither the pattern nor the built nodes have table-evaluated ops. -/
def Rule.pure (r : Rule) : Bool :=
  Pat.pure r.pat && r.result.nodes.all fun n => !frameOp n.op

mutual
theorem Pat.denT_pure (tabs : Tables) (e : PEnv) : ∀ (p : Path) (q : Pat), Pat.pure q = true →
    Pat.denT tabs e p q = Pat.den e p q
  | p, .op o _ _ _ _ _ args _, h => by
    simp only [Pat.pure, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [Pat.denT, Pat.den, opVal_pure h.1, Pat.densT_pure tabs e p 0 args h.2]
  | _, .wild, _ => rfl
  | _, .bind _, _ => rfl
  | _, .same _, _ => rfl
theorem Pat.densT_pure (tabs : Tables) (e : PEnv) : ∀ (p : Path) (i : Nat) (qs : List Pat),
    Pat.pures qs = true → Pat.densT tabs e p i qs = Pat.dens e p i qs
  | _, _, [], _ => rfl
  | p, i, q :: qs, h => by
    simp only [Pat.pures, Bool.and_eq_true] at h
    simp only [Pat.densT, Pat.dens, Pat.denT_pure tabs e (i :: p) q h.1,
      Pat.densT_pure tabs e p (i + 1) qs h.2]
end

mutual
theorem Pat.bindsT_pure (tabs : Tables) (e : PEnv) : ∀ (p : Path) (q : Pat), Pat.pure q = true →
    Pat.bindsT tabs e p q = Pat.binds e p q
  | p, .op o nm ty ai ax ar args cm, h => by
    have hd := Pat.denT_pure tabs e p (.op o nm ty ai ax ar args cm) h
    simp only [Pat.pure, Bool.and_eq_true, Bool.not_eq_true'] at h
    cases nm <;> cases ty <;> cases ai <;>
      simp only [Pat.bindsT, Pat.binds, hd, Pat.bindssT_pure tabs e p 0 args h.2]
  | _, .wild, _ => rfl
  | _, .bind _, _ => rfl
  | _, .same _, _ => rfl
theorem Pat.bindssT_pure (tabs : Tables) (e : PEnv) : ∀ (p : Path) (i : Nat) (qs : List Pat),
    Pat.pures qs = true → Pat.bindssT tabs e p i qs = Pat.bindss e p i qs
  | _, _, [], _ => rfl
  | p, i, q :: qs, h => by
    simp only [Pat.pures, Bool.and_eq_true] at h
    simp only [Pat.bindssT, Pat.bindss, Pat.bindsT_pure tabs e (i :: p) q h.1,
      Pat.bindssT_pure tabs e p (i + 1) qs h.2]
end

theorem sigmaT_pure (tabs : Tables) (e : PEnv) {pat : Pat} (h : Pat.pure pat = true) :
    sigmaT tabs e pat = sigma e pat := by
  funext x; simp only [sigmaT, sigma, Pat.bindsT_pure tabs e [] pat h]

theorem Pat.rawT_pure (tabs : Tables) (e : PEnv) : ∀ {pat : Pat}, Pat.pure pat = true →
    Pat.rawT tabs e pat = Pat.raw e pat
  | .op o _ _ _ _ _ args _, h => by
    simp only [Pat.pure, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [Pat.rawT, Pat.raw, opVal_pure h.1, Pat.densT_pure tabs e [] 0 args h.2]
  | .wild, _ => rfl
  | .bind _, _ => rfl
  | .same _, _ => rfl

theorem nodeDenT_pure (tabs : Tables) (ev : Expr → DV) (or : Oracle) (σ : Nat → DV) (topTy : Ty)
    {nodes : List RNode} (h : nodes.all (fun n => !frameOp n.op) = true) :
    ∀ fuel k, nodeDenT tabs ev or σ topTy nodes fuel k = nodeDen ev or σ topTy nodes fuel k
  | 0, _ => rfl
  | fuel + 1, k => by
    simp only [nodeDenT, nodeDen]
    cases hk : nodes[k]? with
    | none => rfl
    | some n =>
      have hn : frameOp n.op = false := by
        have := List.all_eq_true.1 h n (List.mem_of_getElem? hk)
        simpa using this
      simp only [opVal_pure hn]
      congr 2
      apply List.map_congr_left
      intro a _
      cases a with
      | var x => rfl
      | node j => exact nodeDenT_pure tabs ev or σ topTy h fuel j
      | expr _ => rfl

theorem resDenT_pure (tabs : Tables) (ev : Expr → DV) (or : Oracle) (σ : Nat → DV) (topTy : Ty)
    {res : Result} (h : res.nodes.all (fun n => !frameOp n.op) = true) :
    resDenT tabs ev or σ topTy res = resDen ev or σ topTy res := by
  cases res with
  | copy => rfl
  | setOp => rfl
  | build nodes => exact nodeDenT_pure tabs ev or σ topTy h _ _

/-- A sound rule without table-evaluated nodes satisfies the obligation over the tables. -/
theorem Rule.soundT_of_sound {r : Rule} (hs : Rule.Sound r) (hp : Rule.pure r = true) :
    Rule.SoundT r := by
  simp only [Rule.pure, Bool.and_eq_true] at hp
  refine ⟨hs.1, fun tabs e or hbt => ?_⟩
  simp only [sigmaT_pure tabs e hp.1, Pat.denT_pure tabs e [] r.pat hp.1, Pat.rawT_pure tabs e hp.1,
    resDenT_pure tabs _ or _ _ hp.2]
  intro _ hwf hcons hcond hraw htyped hargs hnn
  exact hs.2 e or hbt hwf hcons hcond hraw htyped hargs hnn

/-- `Rule.Sound` under the rule-keyed facts of `FrameOK` about the matched instance: the
leaves of `nonNegLeaves r` are nonnegative integers or `poison` (`divmod.rules:136–148`). -/
def Rule.SoundNN (r : Rule) : Prop :=
  Pat.arityOk r.pat = true ∧
  ∀ (e : PEnv) (or : Oracle), Oracle.BoolTyped or →
    let σ := sigma e r.pat
    let ev := evalE (r.vars.map (·.ty)) σ or e (Pat.den e [] r.pat)
    Pat.wf e [] r.pat →
    Pat.cons ev σ e [] r.pat →
    condHolds ev r.cond →
    (Pat.raw e r.pat).hasTy (e.ty []) = true →
    Pat.typed e [] r.pat →
    Pat.argsOK e.ty [] r.pat = true →
    Pat.nonNegOK e r.pat r.cond = true →
    (∀ p ∈ nonNegLeaves r, (e.leaf p).nonNeg = true) →
    Refines (Pat.raw e r.pat) (resDen ev or σ (e.ty []) r.result)

/-- A rule without table-evaluated nodes, sound under the leaf facts of `nonNegLeaves`,
satisfies the obligation over the tables (`FrameOK` gives the facts). -/
theorem Rule.soundT_of_soundNN {r : Rule} (hs : Rule.SoundNN r) (hp : Rule.pure r = true) :
    Rule.SoundT r := by
  simp only [Rule.pure, Bool.and_eq_true] at hp
  refine ⟨hs.1, fun tabs e or hbt => ?_⟩
  simp only [sigmaT_pure tabs e hp.1, Pat.denT_pure tabs e [] r.pat hp.1, Pat.rawT_pure tabs e hp.1,
    resDenT_pure tabs _ or _ _ hp.2]
  intro hfr hwf hcons hcond hraw htyped hargs hnn
  exact hs.2 e or hbt hwf hcons hcond hraw htyped hargs hnn hfr.2.2.2.2.2.2

end GoFV.Proof.Rules

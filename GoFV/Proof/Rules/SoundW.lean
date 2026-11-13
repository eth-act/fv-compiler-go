import GoFV.Proof.Rules.DenT
import GoFV.Proof.Retype

variable [GoFV.SSA.Sem.Addrs]

/-!
# The obligation of a rule whose matched value may be narrower than its op (issue #69)

`Rule.SoundT` assumes the matched value's raw value (`Pat.rawT`, before the top's `retype`) has
the shape of its type; the checker establishes it per instance from the top op (`topAll`,
`makeTop`). A shift built by the divmod rules at the dividend's type (`(Rsh64x16 [false] x con)`
typed `int32`, `test/ken_divconst`) does not: its raw value is a 64-bit integer, read at the
narrower type through `retype`. `Rule.SoundW` drops the shape premise and compares the retyped
value instead. The checker accepts any top type for the rules `anyTop` names (the bounded-shift
rules `generic.rules:1187–1198`, which only set the `bounded` flag of a shift whose amount is in
range), and `Rule.SoundTop` asks `Rule.SoundW` of exactly those.
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

/-- The rules whose matches the checker accepts at any top type (`RewriteCheck.ruleOK`): the
bounded-shift rules `generic.rules:1187–1198`, which only set the `bounded` flag of a shift whose
amount is in range, and the tuple rules `:193` (`Mul32uover`/`Mul64uover` by 1), `:1339`/`:1340`
(`Select0`/`Select1` of a `MakeTuple`), whose tops are tuples or selections of them. -/
def anyTop (r : Rule) : Bool :=
  (decide (1187 ≤ r.loc.line ∧ r.loc.line ≤ 1198) || r.loc.line == 193 || r.loc.line == 1339 ||
    r.loc.line == 1340) && r.loc.file == "generic"

/-- **The obligation of a value rule at any top type**: `Rule.SoundT` without the shape premise
of the raw value, for the matched value read at its type (`retype`). -/
def Rule.SoundW (r : Rule) : Prop :=
  Pat.arityOk r.pat = true ∧
  ∀ (tabs : Tables) (e : PEnv) (or : Oracle), Oracle.BoolTyped or →
    let σ := sigmaT tabs e r.pat
    let ev := evalE (r.vars.map (·.ty)) σ or e (Pat.denT tabs e [] r.pat)
    FrameOK tabs e ev or r →
    Pat.wf e [] r.pat →
    Pat.cons ev σ e [] r.pat →
    condHolds ev r.cond →
    Pat.typed e [] r.pat →
    Pat.argsOK e.ty [] r.pat = true →
    Pat.nonNegOK e r.pat r.cond = true →
    Refines ((Pat.rawT tabs e r.pat).retype (e.ty [])) (resDenT tabs ev or σ (e.ty []) r.result)

/-- `Rule.SoundW` over `evalPure` (`Rule.Sound`'s denotation), for rules without
table-evaluated nodes (`Rule.soundW_of_pure`). -/
def Rule.SoundWP (r : Rule) : Prop :=
  Pat.arityOk r.pat = true ∧
  ∀ (e : PEnv) (or : Oracle), Oracle.BoolTyped or →
    let σ := sigma e r.pat
    let ev := evalE (r.vars.map (·.ty)) σ or e (Pat.den e [] r.pat)
    Pat.wf e [] r.pat →
    Pat.cons ev σ e [] r.pat →
    condHolds ev r.cond →
    Pat.typed e [] r.pat →
    Pat.argsOK e.ty [] r.pat = true →
    Pat.nonNegOK e r.pat r.cond = true →
    Refines ((Pat.raw e r.pat).retype (e.ty [])) (resDen ev or σ (e.ty []) r.result)

theorem Rule.soundW_of_pure {r : Rule} (hp : Rule.pure r = true) (hs : Rule.SoundWP r) :
    Rule.SoundW r := by
  simp only [Rule.pure, Bool.and_eq_true] at hp
  refine ⟨hs.1, fun tabs e or hbt => ?_⟩
  simp only [sigmaT_pure tabs e hp.1, Pat.denT_pure tabs e [] r.pat hp.1, Pat.rawT_pure tabs e hp.1,
    resDenT_pure tabs _ or _ _ hp.2]
  intro _ hwf hcons hcond htyped hargs hnn
  exact hs.2 e or hbt hwf hcons hcond htyped hargs hnn

/-- A raw value of the type's shape is its own retype: `Rule.SoundW` gives `Rule.SoundT`. -/
theorem Rule.soundT_of_soundW {r : Rule} (hs : Rule.SoundW r) : Rule.SoundT r := by
  refine ⟨hs.1, fun tabs e or hbt => ?_⟩
  intro _ _ hfr hwf hcons hcond hraw htyped hargs hnn
  have h := hs.2 tabs e or hbt hfr hwf hcons hcond htyped hargs hnn
  rwa [Val.retype_of_hasTy hraw] at h

/-- What the rewrite's proof asks of a value rule the checker matches: `Rule.SoundT`, and
`Rule.SoundW` if the checker accepts it at any top type (`anyTop`). -/
def Rule.SoundTop (r : Rule) : Prop :=
  Rule.SoundT r ∧ (anyTop r = true → Rule.SoundW r)

theorem Rule.soundTop_of_soundT {r : Rule} (hs : Rule.SoundT r) (ha : anyTop r = false) :
    Rule.SoundTop r :=
  ⟨hs, fun h => absurd h (by simp [ha])⟩

theorem Rule.soundTop_of_soundW {r : Rule} (hs : Rule.SoundW r) : Rule.SoundTop r :=
  ⟨Rule.soundT_of_soundW hs, fun _ => hs⟩

end GoFV.Proof.Rules

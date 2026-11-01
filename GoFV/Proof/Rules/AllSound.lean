import GoFV.Proof.Rules.Block

/-!
# Sound rule sets

`RuleSet.AllSound s`: every value rule of `s` satisfies `Rule.SoundT` (`DenT.lean`; a
`Rule.Sound` lemma gives it for a rule without table-evaluated nodes, `Rule.soundT_of_sound`)
or is a selection of a variadic `Make` (`Rule.MakeSel`, validated per instance), every block
rule `BlockRule.Sound` (`Block.lean`). The rewrite passes' theorems (issue #113) take it as the
hypothesis on their rule set; the proven-only rule sets satisfy it
(`GoFV/Proof/Rules/Proven.lean`, generated).
-/

namespace GoFV.Proof.Rules

open GoFV.Rules

/-- `P` holds for every element of the list (one conjunct per element). -/
def ForallL {α : Type} (P : α → Prop) : List α → Prop
  | [] => True
  | a :: l => P a ∧ ForallL P l

theorem ForallL.mem {α : Type} {P : α → Prop} : ∀ {l : List α}, ForallL P l → ∀ a ∈ l, P a
  | _ :: _, ⟨h, _⟩, _, .head _ => h
  | _ :: _, ⟨_, t⟩, a, .tail _ hm => ForallL.mem t a hm

/-- The selection ops (`Comp.select`, `Comp.selectAux`): `StringPtr`, `StringLen`, `SlicePtr`,
`SlicePtrUnchecked`, `SliceLen`, `SliceCap`, `ITab`, `IData`, `ComplexReal`, `ComplexImag`,
`StructSelect`, `ArraySelect`. -/
def selOp : SSA.Op → Bool
  | .StringPtr | .StringLen | .SlicePtr | .SlicePtrUnchecked | .SliceLen | .SliceCap | .ITab
  | .IData | .ComplexReal | .ComplexImag | .StructSelect | .ArraySelect => true
  | _ => false

/-- The `Make` ops (`Comp.make`): `StringMake`, `SliceMake`, `IMake`, `ComplexMake`,
`StructMake`, `ArrayMake1`. -/
def makeOp : SSA.Op → Bool
  | .StringMake | .SliceMake | .IMake | .ComplexMake | .StructMake | .ArrayMake1 => true
  | _ => false

/-- A selection of a `Make` with a copy result: `(Sel (Make …)) => …`, e.g. `(ITab (IMake itab
_)) => itab` or the variadic `(StructSelect [i] x:(StructMake ___)) => x.Args[i]`
(`dec.rules:106`, `generic.rules:973`, issue #17). The checked rewrite first tries to validate
such an event per instance (`GoFV.Opt.RewriteCheck.makeSelOK`: `v` becomes a copy of the
selected argument). -/
def makeSelShape (r : Rule) : Bool :=
  match r.pat, r.result, r.block with
  | .op o none _ _ _ _ [.op mo _ _ _ _ _ _ _] _, .copy _, none => selOp o && makeOp mo
  | _, _, _ => false

/-- **The obligation of a selection of a variadic `Make`**: the rule has `makeSelShape` and a
`___` pattern (no `Rule.Sound` form, `Pat.arityOk`), so each of its events is validated by
`GoFV.Opt.RewriteCheck.makeSelOK`. -/
def Rule.MakeSel (r : Rule) : Prop := makeSelShape r = true ∧ Pat.arityOk r.pat = false

/-- What a value rule of a sound rule set satisfies: `Rule.SoundT`, or `Rule.MakeSel`. -/
def Rule.Checked (r : Rule) : Prop := Rule.SoundT r ∨ Rule.MakeSel r

theorem Rule.checked_of_sound {r : Rule} (h : Rule.Sound r) (hp : Rule.pure r = true) :
    Rule.Checked r :=
  .inl (Rule.soundT_of_sound h hp)

/-- Every value rule of `s` satisfies `Rule.Checked`, every block rule `BlockRule.Sound`. -/
def _root_.GoFV.Rules.RuleSet.AllSound (s : RuleSet) : Prop :=
  (∀ p ∈ s.values, ∀ r ∈ p.2, Rule.Checked r) ∧ ∀ p ∈ s.blocks, ∀ br ∈ p.2, BlockRule.Sound br

theorem RuleSet.allSound_of {s : RuleSet}
    (h : ForallL (fun p : SSA.Op × List Rule => ForallL Rule.Checked p.2) s.values)
    (hb : ForallL (fun p : SSA.BlockKind × List BlockRule => ForallL BlockRule.Sound p.2)
      s.blocks) : s.AllSound :=
  ⟨fun p hp r hr => ForallL.mem (ForallL.mem h p hp) r hr,
   fun p hp r hr => ForallL.mem (ForallL.mem hb p hp) r hr⟩

end GoFV.Proof.Rules

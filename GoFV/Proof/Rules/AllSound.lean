import GoFV.Proof.Rules.Block

variable [GoFV.SSA.Sem.Addrs]

/-!
# Sound rule sets

`RuleSet.AllSound s`: every value rule of `s` satisfies `Rule.SoundTop` (`SoundW.lean`:
`Rule.SoundT` of `DenT.lean`, which a `Rule.Sound` lemma gives for a rule without
table-evaluated nodes, `Rule.soundT_of_sound`, and `Rule.SoundW` for the `anyTop` rules),
is a selection of a variadic `Make` (`Rule.MakeSel`), an unconditional selection of a `Load`
(`Rule.LoadSel`), an `IMake` of a `StructMake` (`Rule.IMakeSM`) or a comparison of symbol
addresses (`Rule.AddrCmp`), validated per instance, a rule the checked rewrite never applies
(`Rule.Drop`), and every block
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

theorem ForallL.append_iff {α : Type} {P : α → Prop} :
    ∀ {l₁ l₂ : List α}, ForallL P (l₁ ++ l₂) ↔ ForallL P l₁ ∧ ForallL P l₂
  | [], _ => ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | _ :: _, _ => ⟨fun ⟨h, t⟩ => ⟨⟨h, (append_iff.1 t).1⟩, (append_iff.1 t).2⟩,
      fun ⟨⟨h, t⟩, t'⟩ => ⟨h, append_iff.2 ⟨t, t'⟩⟩⟩

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

/-- A selection of a `Load` without a condition whose result is built in another block:
`(StructSelect [i] x:(Load <t> ptr mem)) => @x.Block (Load <v.Type> (OffPtr … ptr) mem)`
(`dec.rules:141`, `:132`, issue #17). Its events are validated per instance only
(`GoFV.Opt.RewriteCheck.loadSelOK`). -/
def loadSelShape (r : Rule) : Bool :=
  match r.pat, r.result, r.block, r.cond with
  | .op o none _ _ _ _ [.op .Load _ _ _ _ _ _ _] _, .build _, some _, none => selOp o
  | _, _, _, _ => false

/-- **The obligation of an unconditional selection of a `Load`**: the rule has `loadSelShape`,
so each of its events is validated by `GoFV.Opt.RewriteCheck.loadSelOK` (nothing in the rule
ties the selection's type to the field's). -/
def Rule.LoadSel (r : Rule) : Prop := loadSelShape r = true

/-- A one-argument `Make` turned into its argument: `(StructMake x) && x.Type.IsPtrShaped() =>
x`, `(ArrayMake1 x) && x.Type.IsPtrShaped() => x` (`dec.rules:119`/`:120`, issue #17). False
under the semantics (a one-field pointer-shaped aggregate is `.agg [p]`, Go's is the pointer), so
the checked rewrite never applies such an event: it keeps the `Make`
(`GoFV.Opt.RewriteCheck.replay`) and accepts the output only where the value is no longer read
(`GoFV.Opt.RewriteCheck.finalOK`). -/
def dropShape (r : Rule) : Bool :=
  match r.pat, r.result, r.block with
  | .op mo none _ _ _ _ [.bind _] _, .copy _, none => makeOp mo
  | _, _, _ => false

/-- **The obligation of a dropped rule**: the rule has `dropShape`, so the checked rewrite keeps
the input's definition at each of its events. -/
def Rule.Drop (r : Rule) : Prop := dropShape r = true

/-- An `IMake` of a `StructMake` whose result is `imakeOfStructMake(v)`, an `IMake` of one of the
struct's fields (`generic.rules:981`, `dec.rules:102`: a `struct{*T}` put into a direct
interface). Its events are validated per instance only (`GoFV.Opt.RewriteCheck.imsOK`): an
interface's data word read at its pointer shape from a struct is `poison` (`Val.retype`), so the
field refines it. -/
def imsShape (r : Rule) : Bool :=
  match r.pat, r.result, r.block with
  | .op .IMake none _ _ _ _ [_, .op .StructMake _ _ _ _ _ _ _] _,
    .copy (.call "imakeOfStructMake" _ _), none => true
  | _, _, _ => false

/-- **The obligation of an `IMake` of a `StructMake`**: the rule has `imsShape`, so each of its
events is validated by `GoFV.Opt.RewriteCheck.imsOK`. -/
def Rule.IMakeSM (r : Rule) : Prop := imsShape r = true

/-- An operand of a comparison of symbol addresses: an `Addr`. -/
def addrOperand : Pat → Bool
  | .op .Addr .. => true
  | _ => false

/-- A comparison of two symbol addresses folded to a constant, `(EqPtr (Addr {x} _) (Addr {y} _))
=> (ConstBool [x == y])` (`generic.rules:1648`) and its `NeqPtr` form (`:1651`). The result
compares the symbols' auxes, which the denotation leaves to the oracle, so its events are
validated per instance only (`GoFV.Opt.RewriteCheck.addrCmpOK`: by the global blocks the `Addr`s
point to). -/
def addrCmpShape (r : Rule) : Bool :=
  match r.pat, r.result, r.block with
  | .op o none _ _ _ _ [a, b] _, .build [n], none =>
    (o == .EqPtr || o == .NeqPtr) && addrOperand a && addrOperand b && n.op == .ConstBool &&
      n.args.isEmpty
  | _, _, _ => false

/-- **The obligation of a comparison of symbol addresses**: the rule has `addrCmpShape`, so each
of its events is validated by `GoFV.Opt.RewriteCheck.addrCmpOK`. -/
def Rule.AddrCmp (r : Rule) : Prop := addrCmpShape r = true

/-- What a value rule of a sound rule set satisfies: `Rule.SoundTop` (`Rule.SoundT`, and
`Rule.SoundW` for the rules the checker accepts at any top type, `anyTop`), `Rule.MakeSel`,
`Rule.LoadSel`, `Rule.Drop`, `Rule.IMakeSM` or `Rule.AddrCmp`. -/
def Rule.Checked (r : Rule) : Prop :=
  Rule.SoundTop r ∨ Rule.MakeSel r ∨ Rule.LoadSel r ∨ Rule.Drop r ∨ Rule.IMakeSM r ∨
    Rule.AddrCmp r

theorem Rule.checked_of_soundT {r : Rule} (h : Rule.SoundT r) (ha : anyTop r = false := by rfl) :
    Rule.Checked r :=
  .inl (Rule.soundTop_of_soundT h ha)

theorem Rule.checked_of_sound {r : Rule} (h : Rule.Sound r) (hp : Rule.pure r = true)
    (ha : anyTop r = false := by rfl) : Rule.Checked r :=
  Rule.checked_of_soundT (Rule.soundT_of_sound h hp) ha

theorem Rule.checked_of_soundW {r : Rule} (h : Rule.SoundW r) : Rule.Checked r :=
  .inl (Rule.soundTop_of_soundW h)

theorem Rule.checked_of_drop {r : Rule} (h : Rule.Drop r) : Rule.Checked r :=
  .inr (.inr (.inr (.inl h)))

theorem Rule.checked_of_ims {r : Rule} (h : Rule.IMakeSM r) : Rule.Checked r :=
  .inr (.inr (.inr (.inr (.inl h))))

theorem Rule.checked_of_addrCmp {r : Rule} (h : Rule.AddrCmp r) : Rule.Checked r :=
  .inr (.inr (.inr (.inr (.inr h))))

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

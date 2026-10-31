import GoFV.SSA.Check

/-!
# Well-formedness facts (`docs/contracts/check.md`, "Facts the pass proofs need")

`WF ce f` collects, declaratively, what a passing `check ce f` guarantees and the pass proofs
use: IR integrity (listed blocks and values are in the tables with their IDs, each value is
listed once, edges are crosslinked, arguments and controls are listed values), op shapes
(arity, phi arity, `Bool` auxints) and the entry block. `GoFV.Proof.CheckFacts.check_wf`
derives it from `check`.
-/

namespace GoFV.Proof

open GoFV.SSA

/-- Block `bid` is listed in `f.Blocks` and `b` is its table entry. -/
def BlockIn (f : Func) (bid : ID) (b : Block) : Prop := bid ∈ f.blocks ∧ f.block? bid = some b

/-- Value `vid` is listed in block `bid` (`b` its table entry) and `v` is its table entry. -/
def ValueIn (f : Func) (bid : ID) (b : Block) (vid : ID) (v : Value) : Prop :=
  BlockIn f bid b ∧ vid ∈ b.values ∧ f.value? vid = some v

/-- Value `a` is listed in some block of `f`. -/
def Listed (f : Func) (a : ID) : Prop := ∃ bid b, BlockIn f bid b ∧ a ∈ b.values

structure WF (ce : CheckEnv) (f : Func) : Prop where
  /-- Listed blocks are in the table with their ID, once. -/
  blockId : ∀ bid ∈ f.blocks, ∃ b, f.block? bid = some b ∧ b.id = bid
  blocksNodup : f.blocks.toList.Nodup
  /-- Listed values are in the table with their ID and block. -/
  valueId : ∀ bid b, BlockIn f bid b → ∀ vid ∈ b.values,
    ∃ v, f.value? vid = some v ∧ v.id = vid ∧ v.block = bid
  /-- Each value is listed once. -/
  valuesNodup : ∀ bid b, BlockIn f bid b → b.values.toList.Nodup
  valueOnce : ∀ bid1 b1 bid2 b2, BlockIn f bid1 b1 → BlockIn f bid2 b2 →
    ∀ vid, vid ∈ b1.values → vid ∈ b2.values → bid1 = bid2
  /-- Edges are crosslinked and end at listed blocks. -/
  predLink : ∀ bid b, BlockIn f bid b → ∀ (i : Nat) (e : Edge), b.preds[i]? = some e →
    e.b ∈ f.blocks ∧ ∃ p, f.block? e.b = some p ∧ p.succs[e.i]? = some ⟨bid, i⟩
  succLink : ∀ bid b, BlockIn f bid b → ∀ (j : Nat) (e : Edge), b.succs[j]? = some e →
    e.b ∈ f.blocks ∧ ∃ c, f.block? e.b = some c ∧ c.preds[e.i]? = some ⟨bid, j⟩
  /-- Arity: non-variadic ops have `argLen` arguments; a `Phi` one per predecessor. -/
  arity : ∀ bid b vid v, ValueIn f bid b vid v → v.op.argLen ≠ -1 →
    (v.args.size : Int) = v.op.argLen
  phiArity : ∀ bid b vid v, ValueIn f bid b vid v → v.op = .Phi → v.args.size = b.preds.size
  /-- `Bool` auxints are 0 or 1. -/
  boolAux : ∀ bid b vid v, ValueIn f bid b vid v → v.op.auxType = .Bool →
    0 ≤ v.auxInt.toInt ∧ v.auxInt.toInt ≤ 1
  /-- Arguments and controls are listed values. -/
  argListed : ∀ bid b vid v, ValueIn f bid b vid v → ∀ a ∈ v.args, Listed f a
  ctrlListed : ∀ bid b, BlockIn f bid b → ∀ c ∈ b.controls, Listed f c
  /-- The entry block is listed and has no predecessors. -/
  entry : f.entry ∈ f.blocks
  entryPreds : ∀ b, f.block? f.entry = some b → b.preds.size = 0

end GoFV.Proof

import GoFV.Proof.Pass.ShortCircCpaRel
import GoFV.Proof.DomRel

variable [GoFV.SSA.Sem.Addrs]

/-!
# short circuit, step 1: well-formedness of the result

`Ext f h fE news`: `h` is `f` with the values `news` (new `ConstBool`s without arguments)
appended to the entry block `fE`, its values keeping ID, op, block and auxint and their argument
count, a non-`Phi` its arguments, a `Phi` taking either `f`'s argument or a value of the entry.
Both the result `g` of `constPhiArgs` and `mid f g` (the result with `f`'s arguments, the
constants only added) are such extensions (`CRel.ext_g`, `CRel.ext_mid`). An extension of a
well-formed function is well formed (`Ext.wf`) and keeps use dominance on paths (`Ext.useDom`):
paths are unchanged, and a new argument lies in the entry block, which every path starts from.
-/

namespace GoFV.Proof.ShortCirc

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.ShortCircuit GoFV.Proof Dom

/-- `g` with `f`'s arguments: the constants added to the entry, no argument replaced. -/
def mid (f g : Func) : Func :=
  { g with valueTab := g.valueTab.mapIdx fun x o =>
      match o, f.value? x with
      | some gv, some fv => some { gv with args := fv.args }
      | o, _ => o }

theorem mid_value (f g : Func) (x : ID) :
    (mid f g).value? x = match g.value? x, f.value? x with
      | some gv, some fv => some { gv with args := fv.args }
      | o, _ => o := by
  unfold mid Func.value?
  simp only [Array.getElem?_mapIdx]
  cases g.valueTab[x]? with
  | none => rfl
  | some o => cases o <;> cases f.value? x <;> rfl

theorem mid_block (f g : Func) (x : ID) : (mid f g).block? x = g.block? x := rfl

/-- The block of `h` at `y`: `f`'s, with `news` appended at the entry. -/
def adj (f : Func) (news : Array ID) (y : ID) (b : Block) : Block :=
  if y = f.entry then { b with values := b.values ++ news } else b

/-- See the module doc. -/
structure Ext (f h : Func) (fE : Block) (news : Array ID) : Prop where
  blocks : h.blocks = f.blocks
  entry : h.entry = f.entry
  block : ∀ y, h.block? y = (f.block? y).map (adj f news y)
  hfE : f.block? f.entry = some fE
  nodup : news.toList.Nodup
  newv : ∀ x ∈ news, f.value? x = none ∧ ∃ w, h.value? x = some w ∧ w.op = .ConstBool ∧
    w.args = #[] ∧ w.id = x ∧ w.block = f.entry ∧ (w.auxInt = 0 ∨ w.auxInt = 1)
  value : ∀ x fv, f.value? x = some fv → ∃ hv, h.value? x = some hv ∧ hv.id = fv.id ∧
    hv.op = fv.op ∧ hv.block = fv.block ∧ hv.auxInt = fv.auxInt ∧
    hv.args.size = fv.args.size ∧ (fv.op ≠ .Phi → hv.args = fv.args) ∧
    ∀ (k : Nat) (a : ID), hv.args[k]? = some a → fv.args[k]? = some a ∨ a ∈ fE.values ++ news

theorem adj_fields {f : Func} {news : Array ID} {y : ID} {b : Block} :
    (adj f news y b).id = b.id ∧ (adj f news y b).succs = b.succs ∧
      (adj f news y b).preds = b.preds ∧ (adj f news y b).kind = b.kind ∧
      (adj f news y b).controls = b.controls := by
  unfold adj; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem adj_values {f : Func} {news : Array ID} {y : ID} {b : Block} {x : ID}
    (h : x ∈ (adj f news y b).values) : x ∈ b.values ∨ (y = f.entry ∧ x ∈ news) := by
  unfold adj at h
  split at h
  · rename_i hy
    rcases Array.mem_append.1 h with h | h
    · exact .inl h
    · exact .inr ⟨hy, h⟩
  · exact .inl h

theorem adj_values_sup {f : Func} {news : Array ID} {y : ID} {b : Block} {x : ID}
    (h : x ∈ b.values) : x ∈ (adj f news y b).values := by
  unfold adj; split
  · exact Array.mem_append_left _ h
  · exact h

theorem reach_entry {f : Func} {b : ID} {l : List ID} (h : Reach f b l) : f.entry ∈ l := by
  induction h with
  | entry => exact List.mem_singleton_self _
  | step _ _ _ ih => exact List.mem_cons_of_mem _ ih

variable {f h : Func} {fE : Block} {news : Array ID}

namespace Ext

variable (E : Ext f h fE news)
include E

theorem block_of {y : ID} {B : Block} (hB : h.block? y = some B) :
    ∃ b, f.block? y = some b ∧ B = adj f news y b := by
  rw [E.block] at hB
  cases hf : f.block? y with
  | none => rw [hf] at hB; cases hB
  | some b => rw [hf] at hB; cases hB; exact ⟨b, rfl, rfl⟩

theorem reach_iff {b : ID} {l : List ID} : Reach h b l ↔ Reach f b l := by
  constructor
  · intro hr
    induction hr with
    | entry => rw [E.entry]; exact .entry
    | step _ hb he ih =>
      obtain ⟨b', hb', rfl⟩ := E.block_of hb
      exact .step ih hb' (by rw [adj_fields.2.1] at he; exact he)
  · intro hr
    induction hr with
    | entry => rw [← E.entry]; exact .entry
    | step _ hb he ih =>
      refine .step ih (by rw [E.block, hb]; rfl) ?_
      rw [adj_fields.2.1]; exact he

/-- A value listed in `h`: listed at the same place in `f`, or new in the entry. -/
theorem listing {ce : CheckEnv} (hwf : WF ce f) {bid : ID} {B : Block} (hb : BlockIn h bid B)
    {x : ID} (hx : x ∈ B.values) :
    ∃ b, f.block? bid = some b ∧ B = adj f news bid b ∧
      ((BlockIn f bid b ∧ x ∈ b.values) ∨ (bid = f.entry ∧ x ∈ news)) := by
  obtain ⟨b, hfb, rfl⟩ := E.block_of hb.2
  have hbm : bid ∈ f.blocks := by rw [← E.blocks]; exact hb.1
  refine ⟨b, hfb, rfl, ?_⟩
  rcases adj_values hx with h1 | h1
  · exact .inl ⟨⟨hbm, hfb⟩, h1⟩
  · exact .inr h1

theorem listed_of {a : ID} (hl : Listed f a) : Listed h a := by
  obtain ⟨bid, b, ⟨hbm, hfb⟩, ha⟩ := hl
  exact ⟨bid, adj f news bid b, ⟨by rw [E.blocks]; exact hbm, by rw [E.block, hfb]; rfl⟩,
    adj_values_sup ha⟩

theorem entryIn {ce : CheckEnv} (hwf : WF ce f) :
    BlockIn h f.entry (adj f news f.entry fE) ∧
      ∀ x, x ∈ fE.values ++ news → x ∈ (adj f news f.entry fE).values := by
  refine ⟨⟨by rw [E.blocks]; exact hwf.entry, by rw [E.block, E.hfE]; rfl⟩, fun x hx => ?_⟩
  unfold adj; simp only [ite_true]; exact hx

/-- A value of `fE` or `news` is listed in `h`. -/
theorem listed_entry {ce : CheckEnv} (hwf : WF ce f) {a : ID} (ha : a ∈ fE.values ++ news) :
    Listed h a :=
  ⟨f.entry, _, (E.entryIn hwf).1, (E.entryIn hwf).2 a ha⟩

theorem new_not_f {ce : CheckEnv} (hwf : WF ce f) {bid : ID} {b : Block} (hb : BlockIn f bid b)
    {x : ID} (hx : x ∈ b.values) (hn : x ∈ news) : False := by
  obtain ⟨v, hv, -⟩ := hwf.valueId bid b hb x hx
  rw [(E.newv x hn).1] at hv; cases hv

/-- **An extension of a well-formed function is well formed.** -/
theorem wf {ce : CheckEnv} (hwf : WF ce f) : WF ce h where
  blockId := fun bid hbm => by
    obtain ⟨b, hb, hid⟩ := hwf.blockId bid (by rw [← E.blocks]; exact hbm)
    exact ⟨adj f news bid b, by rw [E.block, hb]; rfl, by rw [adj_fields.1]; exact hid⟩
  blocksNodup := by rw [E.blocks]; exact hwf.blocksNodup
  valueId := fun bid B hB vid hv => by
    obtain ⟨b, -, rfl, hl⟩ := E.listing hwf hB hv
    rcases hl with ⟨hbf, hx⟩ | ⟨rfl, hx⟩
    · obtain ⟨fv, hfv, hid, hblk⟩ := hwf.valueId bid b hbf vid hx
      obtain ⟨hv', hhv, hid', -, hblk', -⟩ := E.value vid fv hfv
      exact ⟨hv', hhv, hid' ▸ hid, hblk' ▸ hblk⟩
    · obtain ⟨-, w, hw, -, -, hid, hblk, -⟩ := E.newv vid hx
      exact ⟨w, hw, hid, hblk⟩
  valuesNodup := fun bid B hB => by
    obtain ⟨b, hfb, rfl⟩ := E.block_of hB.2
    have hbf : BlockIn f bid b := ⟨by rw [← E.blocks]; exact hB.1, hfb⟩
    have hnd := hwf.valuesNodup bid b hbf
    unfold adj; split
    · rw [Array.toList_append, List.nodup_append]
      exact ⟨hnd, E.nodup, fun x hx y hy hxy => E.new_not_f hwf hbf (Array.mem_toList_iff.1 hx)
        (hxy ▸ Array.mem_toList_iff.1 hy)⟩
    · exact hnd
  valueOnce := fun bid1 b1 bid2 b2 hb1 hb2 vid h1 h2 => by
    obtain ⟨c1, -, rfl, l1⟩ := E.listing hwf hb1 h1
    obtain ⟨c2, -, rfl, l2⟩ := E.listing hwf hb2 h2
    rcases l1 with ⟨f1, x1⟩ | ⟨e1, n1⟩ <;> rcases l2 with ⟨f2, x2⟩ | ⟨e2, n2⟩
    · exact hwf.valueOnce bid1 c1 bid2 c2 f1 f2 vid x1 x2
    · exact (E.new_not_f hwf f1 x1 n2).elim
    · exact (E.new_not_f hwf f2 x2 n1).elim
    · rw [e1, e2]
  predLink := fun bid B hB i e he => by
    obtain ⟨b, hfb, rfl⟩ := E.block_of hB.2
    rw [adj_fields.2.2.1] at he
    obtain ⟨hm, p, hp, hs⟩ := hwf.predLink bid b ⟨by rw [← E.blocks]; exact hB.1, hfb⟩ i e he
    exact ⟨by rw [E.blocks]; exact hm, adj f news e.b p, by rw [E.block, hp]; rfl,
      by rw [adj_fields.2.1]; exact hs⟩
  succLink := fun bid B hB j e he => by
    obtain ⟨b, hfb, rfl⟩ := E.block_of hB.2
    rw [adj_fields.2.1] at he
    obtain ⟨hm, c, hc, hs⟩ := hwf.succLink bid b ⟨by rw [← E.blocks]; exact hB.1, hfb⟩ j e he
    exact ⟨by rw [E.blocks]; exact hm, adj f news e.b c, by rw [E.block, hc]; rfl,
      by rw [adj_fields.2.2.1]; exact hs⟩
  arity := fun bid B vid v ⟨hB, hx, hv⟩ hlen => by
    obtain ⟨b, -, rfl, hl⟩ := E.listing hwf hB hx
    rcases hl with ⟨hbf, hx'⟩ | ⟨-, hn⟩
    · obtain ⟨fv, hfv, -⟩ := hwf.valueId bid b hbf vid hx'
      obtain ⟨hv', hhv, -, hop, -, -, hsz, -⟩ := E.value vid fv hfv
      rw [hv] at hhv; cases hhv
      rw [hsz, hop]
      exact hwf.arity bid b vid fv ⟨hbf, hx', hfv⟩ (by rw [← hop]; exact hlen)
    · obtain ⟨-, w, hw, hop, hargs, -⟩ := E.newv vid hn
      rw [hv] at hw; cases hw
      rw [hop, hargs]; decide
  phiArity := fun bid B vid v ⟨hB, hx, hv⟩ hph => by
    obtain ⟨b, -, rfl, hl⟩ := E.listing hwf hB hx
    rcases hl with ⟨hbf, hx'⟩ | ⟨-, hn⟩
    · obtain ⟨fv, hfv, -⟩ := hwf.valueId bid b hbf vid hx'
      obtain ⟨hv', hhv, -, hop, -, -, hsz, -⟩ := E.value vid fv hfv
      rw [hv] at hhv; cases hhv
      rw [hsz, adj_fields.2.2.1]
      exact hwf.phiArity bid b vid fv ⟨hbf, hx', hfv⟩ (by rw [← hop]; exact hph)
    · obtain ⟨-, w, hw, hop, -⟩ := E.newv vid hn
      rw [hv] at hw; cases hw
      rw [hop] at hph; cases hph
  boolAux := fun bid B vid v ⟨hB, hx, hv⟩ haux => by
    obtain ⟨b, -, rfl, hl⟩ := E.listing hwf hB hx
    rcases hl with ⟨hbf, hx'⟩ | ⟨-, hn⟩
    · obtain ⟨fv, hfv, -⟩ := hwf.valueId bid b hbf vid hx'
      obtain ⟨hv', hhv, -, hop, -, hai, -⟩ := E.value vid fv hfv
      rw [hv] at hhv; cases hhv
      rw [hai]
      exact hwf.boolAux bid b vid fv ⟨hbf, hx', hfv⟩ (by rw [← hop]; exact haux)
    · obtain ⟨-, w, hw, -, -, -, -, hai⟩ := E.newv vid hn
      rw [hv] at hw; cases hw
      rcases hai with h0 | h1
      · rw [h0]; decide
      · rw [h1]; decide
  argListed := fun bid B vid v ⟨hB, hx, hv⟩ a ha => by
    obtain ⟨b, -, rfl, hl⟩ := E.listing hwf hB hx
    rcases hl with ⟨hbf, hx'⟩ | ⟨-, hn⟩
    · obtain ⟨fv, hfv, -⟩ := hwf.valueId bid b hbf vid hx'
      obtain ⟨hv', hhv, -, -, -, -, -, -, hargs⟩ := E.value vid fv hfv
      rw [hv] at hhv; cases hhv
      obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 ha
      rcases hargs k a hk with h1 | h1
      · exact E.listed_of (hwf.argListed bid b vid fv ⟨hbf, hx', hfv⟩ a
          (Array.mem_of_getElem? h1))
      · exact E.listed_entry hwf h1
    · obtain ⟨-, w, hw, -, hargs, -⟩ := E.newv vid hn
      rw [hv] at hw; cases hw
      rw [hargs] at ha; simp at ha
  ctrlListed := fun bid B hB c hc => by
    obtain ⟨b, hfb, rfl⟩ := E.block_of hB.2
    rw [adj_fields.2.2.2.2] at hc
    exact E.listed_of (hwf.ctrlListed bid b ⟨by rw [← E.blocks]; exact hB.1, hfb⟩ c hc)
  entry := by rw [E.entry, E.blocks]; exact hwf.entry
  entryPreds := fun B hB => by
    rw [E.entry] at hB
    obtain ⟨b, hfb, rfl⟩ := E.block_of hB
    rw [adj_fields.2.2.1]
    exact hwf.entryPreds b hfb

/-- The block of a value of `f` is unchanged. -/
theorem blockOf_eq {ce : CheckEnv} (hwf : WF ce f) {a : ID} (hl : Listed f a) :
    blockOf h a = blockOf f a := by
  obtain ⟨bid, b, hb, ha⟩ := hl
  obtain ⟨fv, hfv, -, -⟩ := hwf.valueId bid b hb a ha
  obtain ⟨hv, hhv, -, -, hblk, -⟩ := E.value a fv hfv
  unfold blockOf; rw [hfv, hhv]; simp [hblk]

/-- **An extension keeps use dominance on paths.** -/
theorem useDom {ce : CheckEnv} (hwf : WF ce f) (hu : UseDom f) : UseDom h := by
  have hwh := E.wf hwf
  intro bid B hbm hB
  obtain ⟨b, hfb, rfl⟩ := E.block_of hB
  have hbf : bid ∈ f.blocks := by rw [← E.blocks]; exact hbm
  obtain ⟨u1, u2, u3⟩ := hu bid b hbf hfb
  refine ⟨fun l hl vid hv v hvv hph a ha => ?_, fun l hl x hx => ?_,
    fun vid hv v hvv hph i a e l ha he hl => ?_⟩
  · rcases E.listing hwf ⟨hbm, hB⟩ hv with ⟨b', hb', hbe, hl'⟩
    rw [hfb] at hb'; cases hb'
    rcases hl' with ⟨-, hx⟩ | ⟨-, hn⟩
    · obtain ⟨fv, hfv, -⟩ := hwf.valueId bid b ⟨hbf, hfb⟩ vid hx
      obtain ⟨hv', hhv, -, hop, -, -, -, heq, -⟩ := E.value vid fv hfv
      rw [hvv] at hhv; cases hhv
      have hph' : fv.op ≠ .Phi := by rw [← hop]; exact hph
      rw [heq hph'] at ha
      rw [E.blockOf_eq hwf (hwf.argListed bid b vid fv ⟨⟨hbf, hfb⟩, hx, hfv⟩ a ha)]
      exact u1 l (E.reach_iff.1 hl) vid hx fv hfv hph' a ha
    · obtain ⟨-, w, hw, -, hargs, -⟩ := E.newv vid hn
      rw [hvv] at hw; cases hw
      rw [hargs] at ha; simp at ha
  · rw [adj_fields.2.2.2.2] at hx
    rw [E.blockOf_eq hwf (hwf.ctrlListed bid b ⟨hbf, hfb⟩ x hx)]
    exact u2 l (E.reach_iff.1 hl) x hx
  · rcases E.listing hwf ⟨hbm, hB⟩ hv with ⟨b', hb', hbe, hl'⟩
    rw [hfb] at hb'; cases hb'
    rcases hl' with ⟨-, hx⟩ | ⟨-, hn⟩
    · obtain ⟨fv, hfv, -⟩ := hwf.valueId bid b ⟨hbf, hfb⟩ vid hx
      obtain ⟨hv', hhv, -, hop, -, -, -, -, hargs⟩ := E.value vid fv hfv
      rw [hvv] at hhv; cases hhv
      rw [adj_fields.2.2.1] at he
      rcases hargs i a ha with h1 | h1
      · rw [E.blockOf_eq hwf (hwf.argListed bid b vid fv ⟨⟨hbf, hfb⟩, hx, hfv⟩ a
          (Array.mem_of_getElem? h1))]
        exact u3 vid hx fv hfv (by rw [← hop]; exact hph) i a e l h1 he (E.reach_iff.1 hl)
      · obtain ⟨w, hw, -, hblk⟩ := hwh.valueId f.entry _ (E.entryIn hwf).1 a ((E.entryIn hwf).2 a h1)
        have : blockOf h a = f.entry := by unfold blockOf; rw [hw]; simp [hblk]
        rw [this]
        exact reach_entry (E.reach_iff.1 hl)
    · obtain ⟨-, w, hw, hop, -⟩ := E.newv vid hn
      rw [hvv] at hw; cases hw
      rw [hop] at hph; cases hph

end Ext

end GoFV.Proof.ShortCirc

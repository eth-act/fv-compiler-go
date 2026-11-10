import GoFV.Proof.Gen.G7
import GoFV.Proof.Obj.Sim

variable [GoFV.SSA.Sem.Addrs]

/-!
# `runLoc` → `runMach` on slice G7 (`docs/plans/proofs3.md` §1, §6)

The first statement that goes from `runLoc` to the machine words the assembler emitted. It
composes `g7_value`/`g7_term` (`runLoc` → `runProg` on P0, `GoFV/Proof/Gen/G7.lean`) with
`obj_star` (`runProg` on P0 → `runMach` on the linked words, `Sim.lean`).

* `g7_obj_value`: a value step of a function that `checkG7` and `checkObj` both accept, from a
  `LocMatch`ed state `m` whose machine state `t` is `ObjRel`-related to it, is matched by
  machine steps of the linked code to a state related to a `LocMatch`ed `m'` after the value.
* `g7_obj_term`: the same for a terminator that goes to the next block.

P0's return address is `endP` (after the last Prog; it is not a Prog address and not a symbol,
so it is a valid `G2Env.ret`). `pcOf_inv` places every `pcOfTab` address at a Prog or at
`endP`. `hookMap_retLR` gives `HookMap` for callees that return through `X30` without other
effects.
-/

namespace GoFV.Proof.Obj

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj
open GoFV.Proof.Gen

/-- A `pcOfTab` address is a Prog's or the end. -/
theorem pcAt_inv (text : BitVec 64) (ps : List Prog) (j : Nat) :
    IsProgAddr text ps (pcAt text ps j) ∨ pcAt text ps j = endP text ps := by
  unfold pcAt
  split
  · rename_i hj
    exact Or.inl ⟨ps[j], List.getElem_mem hj, rfl⟩
  · exact Or.inr rfl

/-- An activation's `pcOf` address is a Prog's or the end. -/
theorem pcOf_inv {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog} {ret : BitVec 64}
    {tab : PcTab} {E : MatchEnv} (hE : G2Env lc g L ps ret tab E) (b : ID) (i : Nat) :
    IsProgAddr L.text ps.toList (E.pcOf b i) ∨ E.pcOf b i = endP L.text ps.toList := by
  have hpc : E.pcOf b i = pcAt L.text ps.toList (((tab.lookup b).getD []).getD i 0) := by
    rw [hE.pcOf]
    rfl
  rw [hpc]
  exact pcAt_inv _ _ _

/-- A `LocMatch`ed P0 state is at a Prog or at the end. -/
theorem locMatch_inv {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog} {ret : BitVec 64}
    {tab : PcTab} {E : MatchEnv} {s : LocState} {b : ID} {i : Nat} {m : MState}
    (hE : G2Env lc g L ps ret tab E) (hm : LocMatch E s b i m) :
    ObjInv L ps.toList m ∨ m.pc = endP L.text ps.toList := by
  have hpc : m.pc = pcAt L.text ps.toList (((tab.lookup b).getD []).getD i 0) := by
    rw [hm.pc, hE.pcOf]
    rfl
  rcases pcAt_inv L.text ps.toList (((tab.lookup b).getD []).getD i 0) with h | h
  · exact Or.inl (Or.inl (by rw [hpc]; exact h))
  · exact Or.inr (hpc.trans h)

/-- A `LocMatch`ed P0 state and a machine state with its `X27`: `X27At`. -/
theorem x27At_locMatch {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog} {ret : BitVec 64}
    {tab : PcTab} {E : MatchEnv} {s : LocState} {b : ID} {i : Nat} {m t : MState}
    {spills : Array Spill} {o : ObjIn} {otab : Tab} {base : BitVec 64} {code : Code}
    {retM : BitVec 64} (hO : ObjEnv ps spills o otab L base code retM)
    (hE : G2Env lc g L ps ret tab E) (hm : LocMatch E s b i m) (h27 : t.x 27 = m.x 27) :
    X27At otab L ps.toList m t :=
  x27At_of_eq hO h27 (by rw [hm.pc]; exact pcOf_inv hE b i)

/-- Callees that return through `X30` and change nothing else treat related states alike. -/
theorem hookMap_retLR {H : Hooks} {L : Link} {ps : List Prog} {f : BitVec 64 → BitVec 64}
    (hH : ∀ s, H.call s = some (.ret { s with pc := s.x 30 })) : HookMap H L ps f := by
  intro s t s' hR _ _ hc
  rw [hH] at hc
  cases hc
  refine ⟨{ t with pc := t.x 30 }, hH t, ?_, rfl⟩
  exact { x := hR.x, x30 := hR.x30, sp := hR.sp, v := hR.v, nzcv := hR.nzcv, mem := hR.mem,
          pc := hR.x30 }

/-- **A value step of slice G7, down to the machine words.** -/
theorem g7_obj_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    {spills : Array Spill} {o : ObjIn} {otab : Tab} {base : BitVec 64} {code : Code}
    {retM : BitVec 64} {t : MState}
    (hc : checkG7 lc ps bstart g = .ok (tab, kt))
    (hE : G6Env lc g L ps (endP L.text ps.toList) tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp3 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hpre : G7Pre lc s v)
    (hcall : CallOK H E g L lc s s' v m) (hs : stepLoc env lc s v = .ok s')
    (hO : ObjEnv ps spills o otab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hR : ObjRel (ObjEnv.map otab ps L base) m t) (hX : X27At otab L ps.toList m t)
    (hic : ∀ u, PStar H L ps.toList (endP L.text ps.toList) m u → ICallOut L ps.toList u) :
    ∃ E' m' t', E.Extends E' ∧ G6Env lc g L ps (endP L.text ps.toList) tab E' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' ∧
      MStar H code retM t t' ∧ ObjRel (ObjEnv.map otab ps L base) m' t' ∧
      X27At otab L ps.toList m' t' := by
  obtain ⟨E', m', hx, hE', hp, hlm, hinv'⟩ :=
    g7_value hc hE hbid hb hi hv hen hm hinv hpre hcall hs
  obtain ⟨t', ht, hR', -, hX'⟩ := obj_star hO hH hp hR hX (locMatch_inv hE.env hm) hic
  exact ⟨E', m', t', hx, hE', hlm, hinv', ht, hR', hX'⟩

/-- **A terminator of slice G7 that goes to a block, down to the machine words.** -/
theorem g7_obj_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    {spills : Array Spill} {o : ObjIn} {otab : Tab} {base : BitVec 64} {code : Code}
    {retM : BitVec 64} {t : MState}
    (hc : checkG7 lc ps bstart g = .ok (tab, kt))
    (hE : G6Env lc g L ps (endP L.text ps.toList) tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (ht : stepTermLoc lc s blk = .ok (.goto e, s'))
    (hO : ObjEnv ps spills o otab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hR : ObjRel (ObjEnv.map otab ps L base) m t) (hX : X27At otab L ps.toList m t)
    (hic : ∀ u, PStar H L ps.toList (endP L.text ps.toList) m u → ICallOut L ps.toList u) :
    ∃ m' t', LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList ∧
      MStar H code retM t t' ∧ ObjRel (ObjEnv.map otab ps L base) m' t' ∧
      X27At otab L ps.toList m' t' := by
  obtain ⟨m', hp, hlm, hinv', hmem⟩ := g7_term (H := H) hc hE hbid hb hm hinv hpre ht
  obtain ⟨t', htm, hR', -, hX'⟩ := obj_star hO hH hp hR hX (locMatch_inv hE.env hm) hic
  exact ⟨m', t', hlm, hinv', hmem, htm, hR', hX'⟩

end GoFV.Proof.Obj

import GoFV.Proof.Gen.G12
import GoFV.Proof.Obj.G7

/-!
# `runLoc` → `runMach` on slice G12 (`docs/plans/proofs3.md` §1, §7)

`g7_obj_value`/`g7_obj_term`'s composition for the latest merged slice: `g12_value`/`g12_term`
(`runLoc` → `runProg` on P0 under `G10Env` with P0's return address `endP`) with `obj_star`
(`runProg` on P0 → `runMach` on the linked words).

* `g12_obj_value`: a value step (not an entry value) of a function that `checkG12` and `checkObj`
  both accept, from a `LocMatch`ed state `m` whose machine state `t` is `ObjRel`-related to it, is
  matched by machine steps of the linked code to a state related to a `LocMatch`ed `m'` after the
  value.
* `g12_obj_term`: the same for a terminator that goes to the next block.

The premises are `g12_value`'s (`G7Pre`, the trusted contracts `CallOK`, `ICallOK`, `WbOK`,
`CloOK`) and `obj_star`'s (`ObjEnv`, the trusted `HookMap`).
-/

namespace GoFV.Proof.Obj

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj
open GoFV.Proof.Gen

/-- **A value step of slice G12, down to the machine words.** -/
theorem g12_obj_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    {spills : Array Spill} {o : ObjIn} {otab : Tab} {base : BitVec 64} {code : Code}
    {retM : BitVec 64} {t : MState}
    (hc : checkG12 lc ps bstart g = .ok (tab, kt))
    (hE : G10Env lc g L ps (endP L.text ps.toList) tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp3 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hpre : G7Pre lc s v)
    (hcall : CallOK H E g L lc s s' v m) (hicall : ICallOK H E L (endP L.text ps.toList) lc s s' v m)
    (hwb : WbOK H E g L lc s v m) (hclo : CloOK E s v m) (hs : stepLoc env lc s v = .ok s')
    (hO : ObjEnv ps spills o otab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hR : ObjRel (ObjEnv.map otab ps L base) m t) :
    ∃ E' m' t', E.Extends E' ∧ G10Env lc g L ps (endP L.text ps.toList) tab E' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' ∧
      MStar H code retM t t' ∧ ObjRel (ObjEnv.map otab ps L base) m' t' := by
  obtain ⟨E', m', hx, hE', hp, hlm, hinv'⟩ :=
    g12_value hc hE hbid hb hi hv hen hm hinv hpre hcall hicall hwb hclo hs
  obtain ⟨t', ht, hR', -⟩ := obj_star hO hH hp hR (locMatch_inv hE.env.env.env hm)
  exact ⟨E', m', t', hx, hE', hlm, hinv', ht, hR'⟩

/-- **A terminator of slice G12 that goes to a block, down to the machine words.** -/
theorem g12_obj_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    {spills : Array Spill} {o : ObjIn} {otab : Tab} {base : BitVec 64} {code : Code}
    {retM : BitVec 64} {t : MState}
    (hc : checkG12 lc ps bstart g = .ok (tab, kt))
    (hE : G10Env lc g L ps (endP L.text ps.toList) tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (ht : stepTermLoc lc s blk = .ok (.goto e, s'))
    (hO : ObjEnv ps spills o otab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hR : ObjRel (ObjEnv.map otab ps L base) m t) :
    ∃ m' t', LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList ∧
      MStar H code retM t t' ∧ ObjRel (ObjEnv.map otab ps L base) m' t' := by
  obtain ⟨m', hp, hlm, hinv', hmem⟩ := g12_term (H := H) hc hE hbid hb hm hinv hpre ht
  obtain ⟨t', htm, hR', -⟩ := obj_star hO hH hp hR (locMatch_inv hE.env.env.env hm)
  exact ⟨m', t', hlm, hinv', hmem, htm, hR'⟩

end GoFV.Proof.Obj

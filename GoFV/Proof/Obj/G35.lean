import GoFV.Proof.Gen.G35
import GoFV.Proof.Obj.G7

/-!
# `runLoc` → `runMach` on slice G35 (`docs/plans/proofs3.md` §1, §7, §9)

`g7_obj_value`/`g7_obj_term`'s composition for the latest merged slice: `g35_value`/`g35_term`/
`g35_nilPanic`/`g35_boundsPanic` (`runLoc` → `runProg` on P0 under `G28Env` with P0's return
address `endP`) with `obj_star` and `obj_panic` (`runProg` on P0 → `runMach` on the linked
words).

* `g35_obj_value`: a value step (not an entry value) of a function that `checkG35` and `checkObj`
  both accept, from a `LocMatch`ed state `m` (its X registers meeting G35's upper-bit table
  `uL35`, started from the block's `uIn35`, `UOKL`) whose machine state `t` is `ObjRel`-related
  to it, is matched by machine steps of the linked code to a state related to a `LocMatch`ed
  `m'` after the value.
* `g35_obj_term`: the same for a terminator that goes to the next block, whose start `uIn35` the
  state meets.
* `g35_obj_nilPanic`: a nil check that panics is matched by machine steps to a state that panics
  with `nilDeref` (`MPanics`).
* `g35_obj_boundsPanic`: a bounds check that panics is matched by machine steps to a state that
  panics with a panic `BoundsAgree`ing with it.

The premises are `g35_value`'s (`G14Pre`, `GetGOK`, the trusted contracts `CallOK`, `CallOKZ`,
`ICallOK`, `WbOK`, `CloOK`, `MemEqOK`) and `obj_star`'s (`ObjEnv`, the trusted `HookMap`); a panic
also `obj_panic`'s (the trusted `HookPanicMap`), a bounds panic the trusted `BoundsOK`.
-/

namespace GoFV.Proof.Obj

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj
open GoFV.Proof.Gen

/-- On a function with no arm64 op, G35 is `checkNL30`. -/
theorem checkNL30_of_35 {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : Except String (PcTab × KTab)} (hl : lc.ctx.f.lowered = false)
    (h : checkG35 lc ps bstart g = r) : checkNL30 lc ps bstart g = r :=
  checkG31_nl hl (checkG31_of_33 hl (checkG33_of_35 hl h))

/-- **A value step of slice G35, down to the machine words.** -/
theorem g35_obj_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    {spills : Array Spill} {o : ObjIn} {otab : Tab} {base : BitVec 64} {code : Code}
    {retM : BitVec 64} {t : MState}
    (hc : checkG35 lc ps bstart g = .ok (tab, kt))
    (hE : G28Env lc g L ps (endP L.text ps.toList) tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hu : UOKL m (uL35 lc (uIn35 lc bid) blk i))
    (hpre : G14Pre lc s v)
    (hcall : CallOK H E g L lc s s' v m) (hcallz : CallOKZ H E g L lc s s' v m)
    (hicall : ICallOK H E L (endP L.text ps.toList) lc s s' v m)
    (hwb : WbOK H E g L lc s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hmeq : MemEqOK H E g L lc s v m) (hs : stepLoc env lc s v = .ok s')
    (hO : ObjEnv ps spills o otab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hR : ObjRel (ObjEnv.map otab ps L base) m t)
    (hic : ∀ u, PStar H L ps.toList (endP L.text ps.toList) m u → ICallOut L ps.toList u) :
    ∃ E' m' t', E.Extends E' ∧ G28Env lc g L ps (endP L.text ps.toList) tab E' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' ∧
      UOKL m' (uL35 lc (uIn35 lc bid) blk (i + 1)) ∧
      MStar H code retM t t' ∧ ObjRel (ObjEnv.map otab ps L base) m' t' ∧
      (otab.leaf = true → ¬ IsProgAddr L.text ps.toList (m.x 30) →
        m.x 30 ≠ endP L.text ps.toList → m'.x 30 = m.x 30) := by
  obtain ⟨E', m', hx, hE', hp, hlm, hinv', hu'⟩ :=
    g35_value hc hE hbid hb hi hv hen hm hinv hu hpre hcall hcallz hicall hwb hclo hgetg hmeq hs
  have hI := locMatch_inv hE.env.env.env.env hm
  obtain ⟨t', ht, hR', -⟩ := obj_star hO hH hp hR hI hic
  exact ⟨E', m', t', hx, hE', hlm, hinv', hu', ht, hR',
    fun hl h1 h2 => obj_star_leaf hO hH hp hR hI hic hl ⟨h1, h2⟩⟩

/-- **A terminator of slice G35 that goes to a block, down to the machine words.** -/
theorem g35_obj_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    {spills : Array Spill} {o : ObjIn} {otab : Tab} {base : BitVec 64} {code : Code}
    {retM : BitVec 64} {t : MState}
    (hc : checkG35 lc ps bstart g = .ok (tab, kt))
    (hE : G28Env lc g L ps (endP L.text ps.toList) tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (hu : UOKL m (uL35 lc (uIn35 lc bid) blk blk.values.size))
    (ht : stepTermLoc lc s blk = .ok (.goto e, s'))
    (hO : ObjEnv ps spills o otab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hR : ObjRel (ObjEnv.map otab ps L base) m t)
    (hic : ∀ u, PStar H L ps.toList (endP L.text ps.toList) m u → ICallOut L ps.toList u) :
    ∃ m' t', LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList ∧ UOKL m' (uIn35 lc e.b) ∧
      MStar H code retM t t' ∧ ObjRel (ObjEnv.map otab ps L base) m' t' ∧
      (otab.leaf = true → ¬ IsProgAddr L.text ps.toList (m.x 30) →
        m.x 30 ≠ endP L.text ps.toList → m'.x 30 = m.x 30) := by
  obtain ⟨m', hp, hlm, hinv', hmem, hu'⟩ := g35_term (H := H) hc hE hbid hb hm hinv hpre hu ht
  have hI := locMatch_inv hE.env.env.env.env hm
  obtain ⟨t', htm, hR', -⟩ := obj_star hO hH hp hR hI hic
  exact ⟨m', t', hlm, hinv', hmem, hu', htm, hR',
    fun hl h1 h2 => obj_star_leaf hO hH hp hR hI hic hl ⟨h1, h2⟩⟩

/-- **A nil check of slice G35 that panics, down to the machine words**: machine steps of the
linked code to a state that panics with `runLoc`'s panic `nilDeref` (the `MOVB` at the nil page,
`MPanics`). -/
theorem g35_obj_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState} {m : MState}
    {e : Panic} {mm' : Mem}
    {spills : Array Spill} {o : ObjIn} {otab : Tab} {base : BitVec 64} {code : Code}
    {retM : BitVec 64} {t : MState}
    (hc : checkG35 lc ps bstart g = .ok (tab, kt))
    (hE : G28Env lc g L ps (endP L.text ps.toList) tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hs : stepLoc env lc s v = .panic e mm')
    (hO : ObjEnv ps spills o otab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hHP : HookPanicMap H L ps.toList (ObjEnv.map otab ps L base))
    (hR : ObjRel (ObjEnv.map otab ps L base) m t)
    (hic : ∀ u, PStar H L ps.toList (endP L.text ps.toList) m u → ICallOut L ps.toList u) :
    e = .nilDeref ∧ ∃ t', MStar H code retM t t' ∧ MPanics H code retM t' e := by
  obtain ⟨he, m', hp, hpp⟩ := g35_nilPanic (H := H) hc hE hbid hb hi hv hop hm hinv hs
  obtain ⟨t1, ht1, hR1, hI1⟩ := obj_star hO hH hp hR (locMatch_inv hE.env.env.env.env hm) hic
  have hI : ObjInv L ps.toList m' := hI1.resolve_right hpp.1
  obtain ⟨t2, ht2, hpan⟩ := obj_panic hO hHP hR1 hI hpp
  exact ⟨he, t2, mstar_trans ht1 ht2, hpan⟩

/-- **A bounds check of slice G35 that panics, down to the machine words**: machine steps of the
linked code to a state that panics with the runtime's bounds panic (`BoundsOK`), which
`BoundsAgree`s with `runLoc`'s. -/
theorem g35_obj_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState} {m : MState}
    {e : Panic} {mm' : Mem}
    {spills : Array Spill} {o : ObjIn} {otab : Tab} {base : BitVec 64} {code : Code}
    {retM : BitVec 64} {t : MState}
    (hc : checkG35 lc ps bstart g = .ok (tab, kt))
    (hE : G28Env lc g L ps (endP L.text ps.toList) tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hbok : BoundsOK H g L ps.toList)
    (hs : stepLoc env lc s v = .panic e mm')
    (hO : ObjEnv ps spills o otab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hHP : HookPanicMap H L ps.toList (ObjEnv.map otab ps L base))
    (hR : ObjRel (ObjEnv.map otab ps L base) m t)
    (hic : ∀ u, PStar H L ps.toList (endP L.text ps.toList) m u → ICallOut L ps.toList u) :
    ∃ e', BoundsAgree e e' ∧ ∃ t', MStar H code retM t t' ∧ MPanics H code retM t' e' := by
  obtain ⟨e', m', he, hp, hpp⟩ :=
    g35_boundsPanic (H := H) hc hE hbid hb hi hv hop hm hinv hbok hs
  obtain ⟨t1, ht1, hR1, hI1⟩ := obj_star hO hH hp hR (locMatch_inv hE.env.env.env.env hm) hic
  have hI : ObjInv L ps.toList m' := hI1.resolve_right hpp.1
  obtain ⟨t2, ht2, hpan⟩ := obj_panic hO hHP hR1 hI hpp
  exact ⟨e', he, t2, mstar_trans ht1 ht2, hpan⟩

end GoFV.Proof.Obj

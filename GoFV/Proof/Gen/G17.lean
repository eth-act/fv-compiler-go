import GoFV.Proof.Gen.G16
import GoFV.Proof.Gen.Spec17

variable [GoFV.SSA.Sem.Addrs]

/-!
# Soundness of the genssa validator's slice G17: the goroutine (`docs/plans/proofs3.md` §4)

`g17_value`, `g17_term`, `g17_nilPanic`: `g16_value`'s, `g16_term`'s and `g16_nilPanic`'s
statements over `checkG17`; `g17_value` adds the premise `GetGOK` on the injection.

`GetG mem` runs under `runLoc` as Phase 1's `evalPure`: the pointer to the start of the opaque
global `runtime.g` (`stepLoc_getG`), written to its home, the `g` register. Genssa emits no code:
the machine's `X28` holds the activation's goroutine `E.g` (`LocMatch`'s frame clause), which is
where `ι` puts `runtime.g` (`GetGOK`), so the pointer is related to `X28` and `LocMatch` holds with
only `runLoc`'s register changed (`locMatch_setReg_keep`, `g17_getG`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-- **The goroutine block** (a premise on the injection, `docs/proofs/STATUS.md` Assumptions):
at `GetG`, `ι` maps Phase 1's opaque global `runtime.g` to the activation's goroutine `E.g`, the
`g` register's content. `E.Extends` keeps it. -/
def GetGOK (E : MatchEnv) (v : Value) : Prop :=
  v.op = .GetG → E.ι (.global "runtime.g") = some E.g

/-! ## `stepLoc` of `GetG` -/

/-- `GetG` writes the pointer to `runtime.g` to its home. -/
theorem stepLoc_getG {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}
    (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none) (hop : v.op = .GetG)
    (h : stepLoc env lc s v = .ok s') :
    s' = s.write lc v.id ((Val.ptr ⟨.global "runtime.g", 0⟩).retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, -, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
  have he : evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) =
      .ok (.ptr ⟨.global "runtime.g", 0⟩) := by
    have hr : isRoot Op.GetG = false := by decide
    unfold evalOpL evalOp frameVal
    rw [hop]
    simp only [show Op.GetG.generic = true by decide, hr, ↓reduceIte, Bool.false_eq_true]
    rfl
  rw [he] at hr
  cases hr
  rfl

/-! ## `runLoc`'s register alone -/

/-- `runLoc` writing a register whose X register already holds a related word keeps `LocMatch`
with the machine unchanged, at any PC. -/
theorem locMatch_setReg_keep {E : MatchEnv} {s : LocState} {b : ID} {i : Nat} {m : MState}
    (h : LocMatch E s b i m) {r : Nat} {k : Reg} (hobj : objX? r = some k) {x : Val}
    (hx : ValRel E.ι x (m.x k)) {b' : ID} {i' : Nat} :
    LocMatch E (s.setReg r x) b' i' { m with pc := E.pcOf b' i' } := by
  refine ⟨?_, h.flags, h.slots, h.mem, h.frame, rfl⟩
  intro r' v hv
  by_cases hrr : r' = r
  · subst hrr
    simp only [LocState.setReg] at hv
    split at hv
    · rename_i hlt
      simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hlt
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hlt.1] at hv
      simp only [Option.some.injEq] at hv
      subst hv
      have h29 := (objX?_some hobj).1
      refine ⟨fun k' hk' => ?_, fun k' hk' => absurd (objV?_lt hk') (by omega)⟩
      rw [hobj] at hk'
      cases hk'
      exact hx
    · exact h.regs r' v hv
  · have hv' : s.regs[r']? = some v := by
      simp only [LocState.setReg] at hv
      split at hv
      · rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm hrr)] at hv
        exact hv
      · exact hv
    exact h.regs r' v hv'

/-! ## The value -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- `GetG` homed in `g`: no code; `X28` holds `E.g`, where `ι` puts `runtime.g` (`GetGOK`). -/
theorem g17_getG (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    (hop : v.op = .GetG) (hvh : lc.home v.id = some (.reg gReg))
    (hcv : cls (lc.ty v.id) = some 64) (hvs : j' = j) (htemp : (lc.temps[v.id]?).join = none)
    (hs : stepLoc env lc s v = .ok s') (hg : GetGOK E v) :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  rw [stepLoc_getG hl htemp hop hs, write_reg hvh hcv]
  have hrel : ValRel E.ι ((Val.ptr ⟨.global "runtime.g", 0⟩).retypeL (lc.ty v.id)) (m.x 28) :=
    valRel_retypeL hA hcv rfl ⟨E.g, hg hop, by rw [hm.frame.2.1]; simp⟩
  have hlm := locMatch_setReg_keep hm (r := gReg) (by decide) hrel (b' := b) (i' := i + 1)
  rw [hj', hvs, ← hj, ← hm.pc] at hlm
  exact ⟨m, .refl, hlm,
    (core_setReg hinv (fits_retypeL hcv _)).mono (knext_set hK (by rw [hop]; nofun) hvh hcv), hsi⟩

end Cases

/-! ## The theorems -/

/-- One value of G17's kinds (`VK17`) emitted at the Progs from `j` to `j'`: `vk16_step`'s
statement for G17's values, with the goroutine premise `GetGOK`. -/
theorem vk17_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2}
    (hE : G10Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK17 lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s osp) (hpre : G14Pre lc s v)
    (hcall : CallOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hcallz : CallOKZAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hicall : ICallOKAt osp H E (Link.byId sym text az ez ps.toList) ret lc s s' v m)
    (hwb : WbOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s v m) (hclo : CloOK E s v m)
    (hgetg : GetGOK E v) (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G10Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp := by
  cases hVK with
  | g16 hVK16 =>
    exact vk16_step hE F hhome hcf hv hVK16 hvs htemp hj hj' hreads hm hinv hpre hcall hcallz
      hicall hwb hclo hs
  | getG hop _ _ hvh hcv =>
    obtain ⟨m', h1, h2, h3, h4⟩ := g17_getG (H := H) F hm hinv.core hinv.slots
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hvh hcv hvs htemp hs hgetg
    exact ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩⟩

/-- **G17, values.** `g16_value`'s statement over `checkG17`, with the goroutine premise
`GetGOK`. -/
theorem g17_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG17 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp3 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hpre : G14Pre lc s v)
    (hcall : CallOK H E g L lc s s' v m) (hcallz : CallOKZ H E g L lc s s' v m)
    (hicall : ICallOK H E L ret lc s s' v m)
    (hwb : WbOK H E g L lc s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G10Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' := by
  have hE0 := hE
  obtain ⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, hcf, hk, hlt, hnd, hblocks⟩ := checkG17_spec hc
  obtain ⟨b, j, js, e, next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk] at hkd
  obtain ⟨htemp, hVK⟩ := vkind17_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  rw [kAt_succ hi hv]
  exact vk17_step hE0 F hhome hcf hv hVK hvs htemp hj hj' hreads hm hinv hpre hcall hcallz hicall
    hwb hclo hgetg hs

/-- A nil check of G16's kinds is G7's. -/
theorem vk16_nil {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK16 lc g v kd)
    (hop : v.op = .ARM64LoweredNilCheck) : VK7 lc g v kd := by
  cases h with
  | g15 h =>
    cases h with
    | g14 _ h =>
      cases h with
      | g13 h =>
        cases h with
        | g12 h =>
          cases h with
          | g11 h =>
            cases h with
            | g10 h =>
              cases h with
              | g9 h =>
                cases h with
                | g8 _ h =>
                  cases h with
                  | g7 h => exact h
                  | wb hop' => rw [hop] at hop'; cases hop'
                  | sel0 hop' => rw [hop] at hop'; cases hop'
                  | sel1 hop' => rw [hop] at hop'; cases hop'
                | call hop' => rw [hop] at hop'; cases hop'
              | icall hn => rw [hop] at hn; cases hn
              | selMem hop' => rw [hop] at hop'; cases hop'
              | selReg hop' => rw [hop] at hop'; cases hop'
            | clo hop' => rw [hop] at hop'; cases hop'
          | conv hop' => rw [hop] at hop'; cases hop'
        | zero hop' => rw [hop] at hop'; cases hop'
      | idx hop' => rw [hop] at hop'; cases hop'
    | call hop' => rw [hop] at hop'; cases hop'
  | addSh hop' => rw [hop] at hop'; cases hop'

/-- A nil check of G17's kinds is G7's. -/
theorem vk17_nil {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK17 lc g v kd)
    (hop : v.op = .ARM64LoweredNilCheck) : VK7 lc g v kd := by
  cases h with
  | g16 h => exact vk16_nil h hop
  | getG hop' => rw [hop] at hop'; cases hop'

/-- **G17, nil panics.** `g16_nilPanic`'s statement over `checkG17`. -/
theorem g17_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG17 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  obtain ⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks⟩ := checkG17_spec hc
  obtain ⟨b, j, js, e', next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk] at hkd
  obtain ⟨-, hVK⟩ := vkind17_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases vk17_nil hVK hop with
  | g6 hne _ => exact absurd hop hne
  | nil _ hsz2 _ _ hao hma =>
    exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma hvs hs

/-- **G17, terminators.** `g16_term`'s statement over `checkG17`. -/
theorem g17_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG17 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList := by
  obtain ⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome, -, hk, hlt, hnd, hblocks⟩ := checkG17_spec hc
  exact termK_step hpcOf ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb
    hm hinv hpre ht

end GoFV.Proof.Gen

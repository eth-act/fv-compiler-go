import GoFV.Proof.Gen.G28
import GoFV.Proof.Gen.Spec29

variable [GoFV.SSA.Sem.Addrs]

/-!
# Soundness of the genssa validator's slice G29: the upper-bit table within a block
(`docs/plans/proofs3.md` §4)

`g29_value`, `g29_term`, `g29_nilPanic`, `g29_boundsPanic`: `g28_value`'s, `g28_term`'s,
`g28_nilPanic`'s and `g28_boundsPanic`'s statements over `checkG29`. `g29_value` carries the
invariant `UOKL` of the table `uL` (every entry's `UOK`) from value `i` to value `i + 1`, in place
of G20's `UOK` of `uAt`.

The table changes only across values that write at most one X register: a narrow load writes its
own (`vk19_narrowW`), `MOVDnop` writes none (`g20_nop`), `MOVDreg` copies one register into
another (`g21_mov`). An entry of a register the value does not write stays true (`KeepsX`,
`uokl_filter`); the value's own entry is the narrow load's `UOK`, or for `MOVDreg` the entry of
the register it copies. Every other value empties the table. Such a value is G21's
(`vk28_vk21`), so `vk21_stepL` handles it; the rest go through `vk28_step`.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The table's invariant -/

/-- The upper-bit invariant of a table: every entry's `UOK`. -/
def UOKL (m : MState) (L : List (Nat × Nat × Bool)) : Prop := ∀ e ∈ L, UOK m (some e)

/-- `m'` keeps every X register of `m` but Go register `r`'s. -/
def KeepsX (m m' : MState) (r : Nat) : Prop :=
  ∀ k : Nat, k < 31 → objX? r ≠ some (BitVec.ofNat 5 k) →
    m'.x (BitVec.ofNat 5 k) = m.x (BitVec.ofNat 5 k)

/-- Writing the X register of `objOf? r` keeps every other one. -/
theorem keepsX_wX {m m' : MState} {r kd : Nat} {val : BitVec 64}
    (hor : objOf? r = some (ARM64.REG_R0 + kd)) (hx : m'.x = (m.wX (BitVec.ofNat 5 kd) val).x) :
    KeepsX m m' r := by
  intro k hk hne
  rw [hx]
  obtain ⟨k0, hk0, he, hk0'⟩ := objOf?_some hor
  have hkk : kd = k0 := by omega
  subst hkk
  refine wX_x_ne (by omega) (by omega) (fun hkd => ?_) val
  subst hkd
  rcases hk0' with ⟨-, h31⟩ | ⟨-, hobj⟩
  · omega
  · exact hne hobj

/-- The entries of registers other than `r` stay true when the machine keeps every X register
but `r`'s. -/
theorem uokl_filter {m m' : MState} {L : List (Nat × Nat × Bool)} {r : Nat} (hL : UOKL m L)
    (hk : KeepsX m m' r) : UOKL m' (L.filter (·.1 != r)) := by
  intro e he
  obtain ⟨r', c, sg⟩ := e
  rw [List.mem_filter] at he
  obtain ⟨heL, hne⟩ := he
  have hne' : r' ≠ r := by simpa using hne
  intro k hk31 hobj
  rw [hk k hk31 (fun h => hne' (objX?_inj hobj h))]
  exact hL _ heL k hk31 hobj

/-- What `find?` found in the table is an entry of the table for that register. -/
theorem find?_entry {L : List (Nat × Nat × Bool)} {rx a c : Nat} {sg : Bool}
    (h : L.find? (·.1 == rx) = some (a, c, sg)) : (a, c, sg) ∈ L ∧ a = rx := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  simpa using List.find?_some h

/-- The table before value `i` has `uAt`'s entry. -/
theorem uok_of_uokl {lc : LocCtx} {blk : Block} {m : MState} :
    ∀ {i : Nat}, UOKL m (uL lc blk i) → UOK m (uAt lc blk i)
  | 0, _ => trivial
  | i + 1, h => by
    show UOK m (((blk.values[i]?).bind lc.ctx.f.value?).bind (uEntry lc))
    cases hv : (blk.values[i]?).bind lc.ctx.f.value? with
    | none => trivial
    | some v =>
      show UOK m (uEntry lc v)
      cases hue : uEntry lc v with
      | none => trivial
      | some e =>
        apply h
        simp only [uL, hv, uStepL, hue]
        exact List.mem_cons_self

/-- The table across `MOVDreg x`, `x` in `rx` and the value in `rv`. -/
theorem uStepL_movdReg {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value} {rx rv : Nat}
    (hue : uEntry lc v = none) (hop : v.op = .ARM64MOVDreg)
    (hx : (v.args[0]?).bind (regHome? lc) = some rx) (hv : regHome? lc v.id = some rv) :
    uStepL lc L v = movdRegStep L rx rv := by
  have hn1 : (v.op == .ARM64MOVDnop) = false := by rw [hop]; rfl
  have hn2 : (v.op == .ARM64MOVDreg) = true := by rw [hop]; rfl
  simp only [uStepL, hue, hn1, hn2, Bool.false_eq_true, ↓reduceIte, hx, hv]

/-- The table's invariant across a register copy into `rv`: the entries of other registers stay
true, and `rv` gets an entry of `rx` that holds for `rv` afterwards. -/
theorem uokl_movdReg {m m' : MState} {L : List (Nat × Nat × Bool)} {rx rv : Nat}
    (hold : UOKL m L) (hkeep : KeepsX m m' rv)
    (hnew : ∀ c sg, (rx, c, sg) ∈ L → UOK m' (some (rv, c, sg))) :
    UOKL m' (movdRegStep L rx rv) := by
  unfold movdRegStep
  cases hf : L.find? (·.1 == rx) with
  | none => exact uokl_filter hold hkeep
  | some t =>
    obtain ⟨a, c, sg⟩ := t
    obtain ⟨haL, rfl⟩ := find?_entry hf
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact hnew c sg haL
    · exact uokl_filter hold hkeep _ he

/-- Across a value that is no narrow load (`uEntry`), `MOVDnop` or `MOVDreg`, the table is
empty. -/
theorem uStepL_other {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value}
    (hue : uEntry lc v = none) (h1 : v.op ≠ .ARM64MOVDnop) (h2 : v.op ≠ .ARM64MOVDreg) :
    uStepL lc L v = [] := by
  have h1' : (v.op == .ARM64MOVDnop) = false := by simpa using h1
  have h2' : (v.op == .ARM64MOVDreg) = false := by simpa using h2
  simp only [uStepL, hue, h1', h2', Bool.false_eq_true, ↓reduceIte]

/-! ## Values of G21 that write at most one register -/

/-- A narrow load, `MOVDnop` or `MOVDreg` of G28's kinds is G21's. -/
theorem vk28_vk21 {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (hVK : VK28 lc g v kd)
    (hop : NarrowOp v.op ∨ v.op = .ARM64MOVDnop ∨ v.op = .ARM64MOVDreg) : VK21 lc g v kd := by
  unfold NarrowOp at hop
  rcases hop with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) | h | h <;>
  · cases hVK with
    | memEq h' => rw [h] at h'; cases h'
    | g27 _ h27 =>
      cases h27 with
      | logSh h' => rw [h] at h'; cases h'
      | g25 _ h25 =>
        cases h25 with
        | csel h' => rw [h] at h'; cases h'
        | csel0 h' => rw [h] at h'; cases h'
        | tst h' => rw [h] at h'; cases h'
        | tstw h' => rw [h] at h'; cases h'
        | g24 _ _ h24 =>
          cases h24 with
          | sp h' => rw [h] at h'; cases h'
          | g23 _ h23 =>
            cases h23 with
            | cset h' => rw [h] at h'; simp [Cond.ofOp] at h'
            | g22 _ h22 =>
              cases h22 with
              | ldp h' => rw [h] at h'; cases h'
              | stp h' => rw [h] at h'; cases h'
              | g21 _ h21 => exact h21

/-- A narrow load (`uEntry lc v = some e`), `MOVDnop` or `MOVDreg` of G21's kinds: the step of
`vk21_step` under the same activation, carrying the table's invariant `UOKL` across the value
(`uStepL`); the table holds the entry `movdOK29` names for a `MOVDnop`/`MOVDreg` argument. -/
theorem vk21_stepL {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)}
    (hE : G10Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hVK : VK21 lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s osp) (hpre : G14Pre lc s v)
    (hs : stepLoc env lc s v = .ok s') (hL : UOKL m L)
    (hmem : ∀ x, (v.op = .ARM64MOVDnop ∨ v.op = .ARM64MOVDreg) → v.args[0]? = some x →
      ∃ r c, regHome? lc x = some r ∧ cls (lc.ty x) = some c ∧
        (r, c, lc.signOf lc.ctx.f.valueTab.size x) ∈ L)
    (hcase : (∃ e, uEntry lc v = some e) ∨ v.op = .ARM64MOVDnop ∨ v.op = .ARM64MOVDreg) :
    ∃ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E s' bid (i + 1) m' ∧ G3Inv E lc (kStep lc K v) s' osp ∧
      UOKL m' (uStepL lc L v) := by
  have hu : ∀ x, (v.op = .ARM64MOVDnop ∨ v.op = .ARM64MOVDreg) → v.args[0]? = some x →
      ∃ r c, regHome? lc x = some r ∧ cls (lc.ty x) = some c ∧
        UOK m (some (r, c, lc.signOf lc.ctx.f.valueTab.size x)) := fun x hop hx => by
    obtain ⟨r, c, hr, hc, he⟩ := hmem x hop hx
    exact ⟨r, c, hr, hc, hL _ he⟩
  cases hVK with
  | regSame hop hsz hao hro hz hca hcd =>
    have hue : uEntry lc v = none := by
      have : narrowLd? lc v = none := by unfold narrowLd?; rw [hop]; rfl
      simp only [uEntry, this]
    obtain ⟨x, r1, hx0, hxh, hor1, hcx⟩ := argObj_spec hao
    obtain ⟨r2, hvh, hd, hor2, hcv⟩ := resObj_spec hro
    obtain rfl := objOf?_inj hor1 hor2
    have hz' : r1 ≠ zeroReg := by
      rintro rfl
      simp only [objOf?, ↓reduceIte, Option.some.injEq] at hor1
      exact hz hor1.symm
    obtain ⟨r', c', hr', hc', hu0⟩ := hu x (.inr hop) hx0
    rw [regHome?_eq.2 hxh] at hr'
    cases hr'
    rw [hcx] at hc'
    cases hc'
    obtain ⟨m', h1, h2, h3, h4, rfl⟩ := g20_nop (H := H) F hm hinv.core hinv.slots
      (kread_of_reads hreads) (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' (.inr hop) hsz
      hx0 hvh hd hz' hxh hcv (by omega) hcx hca hvs htemp hs hu0
    refine ⟨_, h1, h2, ⟨h3, h4⟩, ?_⟩
    rw [uStepL_movdReg hue hop (by rw [hx0, Option.bind_some, regHome?_eq.2 hxh])
      (regHome?_eq.2 hvh)]
    exact uokl_movdReg hL (fun _ _ _ => rfl) fun c sg h => hL _ h
  | regMov hop hsz hao hro hz hca hcd hne =>
    have hue : uEntry lc v = none := by
      have : narrowLd? lc v = none := by unfold narrowLd?; rw [hop]; rfl
      simp only [uEntry, this]
    obtain ⟨x, r1, hx0, hxh, hor1, hcx⟩ := argObj_spec hao
    obtain ⟨r2, hvh, -, hor2, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4, ka, kd, rfl, rfl, hka31, hx'⟩ := g21_mov (H := H) F hm hinv.core
      hinv.slots (kread_of_reads hreads) (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj'
      hop hsz hao hro hz hca hcd hvs htemp hs (fun x hx => hu x (.inr hop) hx)
    refine ⟨m', h1, h2, ⟨h3, h4⟩, ?_⟩
    rw [uStepL_movdReg hue hop (by rw [hx0, Option.bind_some, regHome?_eq.2 hxh])
      (regHome?_eq.2 hvh)]
    refine uokl_movdReg hL (keepsX_wX hor2 hx') fun c sg haL => ?_
    -- `r2`'s new entry: `X[kd]` is `X[ka]`, which the table names
    intro k hk hobj
    obtain ⟨kd', hkd', hkk, hkd0⟩ := objOf?_some hor2
    have hkd : kd = kd' := by omega
    subst hkd
    rcases hkd0 with ⟨hzr, -⟩ | ⟨-, hobj2⟩
    · rw [hzr] at hobj; cases hobj
    · rw [hobj] at hobj2
      have hkk' := ofNat5_inj (by omega) (by omega) (Option.some.inj hobj2)
      subst hkk'
      rw [hx', wX_x_self hk]
      obtain ⟨ka', hka', hka'', hka0⟩ := objOf?_some hor1
      have hka : ka = ka' := by omega
      subst hka
      rcases hka0 with ⟨-, h31⟩ | ⟨-, hobj1⟩
      · omega
      · exact hL _ haL ka hka31 hobj1
  | g20 hnr hVK20 =>
    cases hVK20 with
    | nop hop hsz hx hvr hd hz hxr hcv hcx =>
      obtain ⟨r', c', hr', hc', hu0⟩ := hu _ (.inl hop) hx
      rw [hxr] at hr'
      cases hr'
      have hvh := regHome?_eq.1 hvr
      have hxh := regHome?_eq.1 hxr
      obtain ⟨cv, hcv', hcv8⟩ : ∃ cv, cls (lc.ty v.id) = some cv ∧ 8 ≤ cv := by
        rcases hcv with h | h | h | h <;> exact ⟨_, h, by omega⟩
      have hcc : c' = 8 ∨ c' = 16 ∨ c' = 32 := by
        rcases hcx with h | h | h <;> (rw [hc'] at h; cases h; simp)
      obtain ⟨m', h1, h2, h3, h4, rfl⟩ := g20_nop (H := H) F hm hinv.core hinv.slots
        (kread_of_reads hreads) (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' (.inl hop) hsz
        hx hvh hd hz hxh hcv' hcv8 hc' hcc hvs htemp hs hu0
      have hue : uEntry lc v = none := by
        have : narrowLd? lc v = none := by unfold narrowLd?; rw [hop]; rfl
        simp only [uEntry, this]
      refine ⟨_, h1, h2, ⟨h3, h4⟩, ?_⟩
      simp only [uStepL, hue, hop, beq_self_eq_true, ↓reduceIte]
      exact hL
    | g19 hnn hVK19 =>
      rcases hcase with ⟨⟨r, cc, sg⟩, hue⟩ | h | h
      · obtain ⟨m', h1, h2, h3, h4, kd, val, hor, hx'⟩ := vk19_narrowW hE F hVK19 hvs htemp hj hj'
          hreads hm hinv hpre hs hue
        refine ⟨m', h1, h2, h3, ?_⟩
        simp only [uStepL, hue]
        intro e he
        rcases List.mem_cons.1 he with rfl | he
        · exact h4
        · exact uokl_filter hL (keepsX_wX hor hx') _ he
      · exact absurd h hnn
      · exact absurd h hnr

/-! ## The theorems -/

/-- One value of G29's kinds (G28's): `vk28_step`'s statement, carrying the table's invariant
`UOKL` across the value (`uStepL`). -/
theorem vk29_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)}
    (hE : G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK28 lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s osp) (hL : UOKL m L)
    (hmem : ∀ x, (v.op = .ARM64MOVDnop ∨ v.op = .ARM64MOVDreg) → v.args[0]? = some x →
      ∃ r c, regHome? lc x = some r ∧ cls (lc.ty x) = some c ∧
        (r, c, lc.signOf lc.ctx.f.valueTab.size x) ∈ L)
    (hpre : G14Pre lc s v)
    (hcall : CallOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hcallz : CallOKZAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hicall : ICallOKAt osp H E (Link.byId sym text az ez ps.toList) ret lc s s' v m)
    (hwb : WbOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s v m) (hclo : CloOK E s v m)
    (hgetg : GetGOK E v) (hmeq : MemEqOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s v m)
    (hmp : MemEqPre lc s v) (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp ∧
      UOKL m' (uStepL lc L v) := by
  by_cases hcase : (∃ e, uEntry lc v = some e) ∨ v.op = .ARM64MOVDnop ∨ v.op = .ARM64MOVDreg
  · have hmo : NarrowOp v.op ∨ v.op = .ARM64MOVDnop ∨ v.op = .ARM64MOVDreg := by
      rcases hcase with ⟨⟨r, c, sg⟩, he⟩ | h | h
      · obtain ⟨n, hnl, -⟩ := uEntry_spec he
        exact .inl (narrowLd?_spec hnl).1
      · exact .inr (.inl h)
      · exact .inr (.inr h)
    obtain ⟨m', h1, h2, h3, h4⟩ := vk21_stepL hE.env F (vk28_vk21 hVK hmo) hvs htemp hj hj'
      hreads hm hinv hpre hs hL hmem hcase
    exact ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, h3, h4⟩
  · have hue : uEntry lc v = none := by
      cases h : uEntry lc v with
      | none => rfl
      | some e => exact absurd (.inl ⟨e, h⟩) hcase
    have h1 : v.op ≠ .ARM64MOVDnop := fun h => hcase (.inr (.inl h))
    have h2 : v.op ≠ .ARM64MOVDreg := fun h => hcase (.inr (.inr h))
    obtain ⟨E', m', hx, hE', hp, hlm, hinv', -⟩ := vk28_step hE F hhome hcf hv hVK hvs htemp hj hj'
      hreads hm hinv
      (fun x hop hx => by
        obtain ⟨r, c, hr, hc, he⟩ := hmem x hop hx
        exact ⟨r, c, hr, hc, hL _ he⟩)
      hpre hcall hcallz hicall hwb hclo hgetg hmeq hmp hs
    refine ⟨E', m', hx, hE', hp, hlm, hinv', ?_⟩
    rw [uStepL_other hue h1 h2]
    intro e he
    cases he

/-- **G29, values.** `g28_value`'s statement over `checkG29`, with the same premises, carrying the
upper-bit invariant `UOKL` of the table `uL` from value `i` to value `i + 1`. -/
theorem g29_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG29 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s osp) (hu : UOKL m (uL lc blk i))
    (hpre : G14Pre lc s v)
    (hcall : CallOKAt osp H E g L lc s s' v m) (hcallz : CallOKZAt osp H E g L lc s s' v m)
    (hicall : ICallOKAt osp H E L ret lc s s' v m)
    (hwb : WbOKAt osp H E g L lc s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hmeq : MemEqOKAt osp H E g L lc s v m) (hmp : MemEqPre lc s v)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' osp ∧
      UOKL m' (uL lc blk (i + 1)) := by
  rw [uL_succ hi hv]
  cases hl : lc.ctx.f.lowered with
  | false =>
    obtain ⟨E', m', hx, hE', h1, h2, h3, -⟩ := g28_value (checkG28_of_29 hl hc) hE hbid hb hi hv
      hen hm hinv (uok_of_uokl hu) hpre hcall hcallz hicall hwb hclo hgetg hmeq hmp hs
    refine ⟨E', m', hx, hE', h1, h2, h3, ?_⟩
    have hnl : checkNL lc ps bstart g = .ok (tab, kt) := by simpa [checkG29, hl] using hc
    have hops := nl_ops hnl hbid hb hi hv hen
    have hue : uEntry lc v = none := by simp only [uEntry, narrowLd?_nl hops]
    rw [uStepL_other hue (by rcases hops with h | h | h <;> rw [h] <;> nofun)
      (by rcases hops with h | h | h <;> rw [h] <;> nofun)]
    intro e he
    cases he
  | true =>
  have hE0 := hE
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, hcf, hk, hlt, hnd, hblocks, -, hmovd⟩ :=
    checkG29_spec hl hc
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
  obtain ⟨htemp, hVK⟩ := vkind28_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  rw [kAt_succ hi hv]
  exact vk29_step hE0 F hhome hcf hv hVK hvs htemp hj hj' hreads hm hinv hu
    (fun x hop hx => movdOK29_spec hmovd hbid hb hi hv hop hx)
    hpre hcall hcallz hicall hwb hclo hgetg hmeq hmp hs

/-- **G29, nil panics.** `g28_nilPanic`'s statement over `checkG29`. -/
theorem g29_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG29 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  cases hl : lc.ctx.f.lowered with
  | false => exact g28_nilPanic (checkG28_of_29 hl hc) hE hbid hb hi hv hop hm hinv hs
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, -, -⟩ :=
    checkG29_spec hl hc
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
  obtain ⟨-, hVK⟩ := vkind28_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases vk28_nil hVK hop with
  | g6 hne _ => exact absurd hop hne
  | nil _ hsz2 _ _ hao hma =>
    exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma hvs hs

/-- **G29, bounds panics.** `g28_boundsPanic`'s statement over `checkG29`. -/
theorem g29_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG29 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hbok : BoundsOK H g L ps.toList)
    (hs : stepLoc env lc s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    exact g28_boundsPanic (checkG28_of_29 hl hc) hE hbid hb hi hv hop hm hinv hbok hs
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, hsyms, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, hpb, -⟩ :=
    checkG29_spec hl hc
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
  have hen : entryOp24 v.op = false := by
    rcases pbOp_cases hop with h | h | h | h <;> rw [h] <;> rfl
  obtain ⟨-, hVK⟩ := vkind28_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  exact vk28_boundsPanic F hsyms hpb hrow hb hi hv hVK hvs hj hreads hop hm hinv hbok hs

/-- **G29, terminators.** `g28_term`'s statement over `checkG29`. -/
theorem g29_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG29 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList := by
  cases hl : lc.ctx.f.lowered with
  | false => exact g28_term (checkG28_of_29 hl hc) hE hbid hb hm hinv hpre ht
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome, -, hk, hlt, hnd, hblocks, -, -⟩ :=
    checkG29_spec hl hc
  exact termK_step hpcOf ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb
    hm hinv hpre ht

end GoFV.Proof.Gen

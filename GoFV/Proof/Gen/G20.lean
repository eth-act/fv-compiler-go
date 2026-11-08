import GoFV.Proof.Gen.G19
import GoFV.Proof.Gen.Spec20

/-!
# Soundness of the genssa validator's slice G20: `MOVDnop` after its narrow load
(`docs/plans/proofs3.md` §4, §8)

`g20_value`, `g20_term`, `g20_nilPanic`, `g20_boundsPanic`: `g19_value`'s, `g19_term`'s,
`g19_nilPanic`'s and `g19_boundsPanic`'s statements over `checkG20`; `g20_value` also carries the
upper-bit invariant `UOK` of the table `uAt` from the state before value `i` to the state before
value `i + 1`.

`UOK m (uAt lc blk i)`: when the value before `i` is a narrow load of `n` bytes homed in register
`r` at class `c ≥ 8n` (`uEntry`), the machine's `X` register of `r` is the zero or sign extension
of its low `c` bits (`ExtOK`). The load wrote it so: `g3_loadW`/`g14_idxW` give the machine's
registers after the load, the extension of the `n` loaded bytes (`extOK_load`). Every other
value leaves nothing to show.

`MOVDnop x` emits no code; `runLoc` writes `x`'s register with the 64-bit zero or sign extension
of `x` that `signOf x` names (`movdLoc`, `stepLoc_nop`). `nopOK` puts the table's entry for `x`'s
register before it, so the machine register is that extension of its low bits, which `LocMatch`
relates to `x` (`lo_movd`), and `LocMatch` holds with the machine unchanged (`g20_nop`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The upper bits -/

/-- `X` is the sign (`sg`) or zero extension of its low `c` bits. -/
def ExtOK (X : BitVec 64) (c : Nat) (sg : Bool) : Prop :=
  X = if sg then (X.setWidth c).signExtend 64 else (X.setWidth c).setWidth 64

/-- The upper-bit invariant of a table entry: the machine's `X` register of Go register `r` is the
sign or zero extension of its low `c` bits. -/
def UOK (m : MState) : Option (Nat × Nat × Bool) → Prop
  | none => True
  | some (r, c, sg) => ∀ k : Nat, k < 31 → objX? r = some (BitVec.ofNat 5 k) →
      ExtOK (m.x (BitVec.ofNat 5 k)) c sg

theorem sext_bit (w : Nat) (hw : 0 < w ∧ w ≤ 64) (y : BitVec 64) (i : Nat) (hi : i < 64) :
    (Arm64.sext w y).getLsbD i = if i < w then y.getLsbD i else y.getLsbD (w - 1) := by
  simp only [Arm64.sext, show w ≠ 0 by omega, ↓reduceIte, BitVec.getLsbD_sshiftRight,
    BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and,
    Arm64.mask, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  by_cases hiw : i < w
  · have e : 64 - w + i - (64 - w) = i := by omega
    have h1 : 64 - w + i < 64 := by omega
    have h2 : ¬ 64 - w + i < 64 - w := by omega
    have h3 : ¬ 64 ≤ i := by omega
    simp [hiw, e, h1, h2, h3, BitVec.getLsbD_eq_getElem hi]
    intro; exact hi
  · have h1 : ¬ 64 - w + i < 64 := by omega
    have h2 : ¬ 63 < 64 - w := by omega
    have h3 : ¬ 64 ≤ i := by omega
    have h4 : w - 1 < 64 := by omega
    have h5 : w - 1 < w := by omega
    have e : 63 - (64 - w) = w - 1 := by omega
    simp [hiw, e, h1, h2, h3, h4, h5]

/-- The machine's narrow load of `n` bytes `Y` (`progStep_loadN`) is the extension of its low `c`
bits, `8n ≤ c`. -/
theorem extOK_load {n c : Nat} (sg : Bool) (hn : 1 ≤ n) (hc : 8 * n ≤ c) (hc64 : c ≤ 64)
    (Y : BitVec (8 * n)) :
    ExtOK (if sg then ProgOp.sextTo64 n (Y.setWidth 64) else Y.setWidth 64) c sg := by
  unfold ExtOK
  cases sg
  · simp only [Bool.false_eq_true, ↓reduceIte]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_setWidth]
    by_cases h1 : i < c
    · simp [h1, hi]
    · simp only [h1, decide_false, Bool.false_and, Bool.and_false]
      rw [BitVec.getLsbD_of_ge Y i (by omega), Bool.and_false]
  · simp only [↓reduceIte, ProgOp.sextTo64]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_signExtend]
    simp only [BitVec.getLsbD_setWidth, BitVec.msb_eq_getLsbD_last]
    rw [sext_bit _ ⟨by omega, by omega⟩ _ _ hi]
    by_cases h1 : i < c
    · simp [h1, hi]
    · have hc1 : c - 1 < 64 := by omega
      rw [sext_bit _ ⟨by omega, by omega⟩ _ _ hc1]
      have h2 : ¬ i < 8 * n := by omega
      have h3 : ¬ c - 1 < 8 * n ∨ c - 1 = 8 * n - 1 := by omega
      simp only [h1, h2, hi, decide_true, Bool.true_and, ↓reduceIte, show c - 1 < c by omega]
      rcases h3 with h3 | h3
      · simp [h3]
      · rw [h3]; simp

/-! ## `stepLoc` of `MOVDnop` -/

section Step

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

/-- `MOVDnop x` writes `movdLoc` of `x`'s value to its home. -/
theorem stepLoc_nop (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .ARM64MOVDnop) {x : ID} (hsz : v.args.size = 1) (hx : v.args[0]? = some x)
    (h : stepLoc env lc s v = .ok s') :
    ∃ a, s.read lc x = .ok a ∧
      s' = s.write lc v.id ((movdLoc lc v [a] (lc.ty v.id)).retypeL (lc.ty v.id)) := by
  have hargs : v.args.toList = [x] := by
    apply List.ext_getElem?
    intro k
    rcases k with _ | k
    · simpa using hx
    · simp only [Array.getElem?_toList, List.getElem?_cons_succ, List.getElem?_nil]
      exact Array.getElem?_eq_none (by omega)
  unfold stepLoc at h
  simp only [show (v.op == Op.Phi) = false by rw [hop]; rfl, Bool.false_eq_true, ↓reduceIte,
    hargs] at h
  rw [show [x].mapM (s.read lc) = (s.read lc x).bind fun y => .ok [y] from rfl] at h
  cases hr : s.read lc x with
  | panic e mm => rw [hr] at h; cases h
  | stuck msg => rw [hr] at h; cases h
  | ok a =>
    rw [hr] at h
    simp only [Res.bind, bind, hop] at h
    cases h
    refine ⟨a, rfl, ?_⟩
    rw [clobber_none (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) ht (by rw [hop]; rfl),
      lmode_retype hl]

end Step

/-- `movdLoc` of a narrow integer `a` related to `X` by its low bits, when `X` is the extension of
its low bits that `signOf` names: the 64-bit result is `X`. -/
theorem lo_movd {ι : Blk → Option (BitVec 64)} {lc : LocCtx} {v : Value} {x : ID} {t : Ty}
    (hx : v.args[0]? = some x) (ht : t ≠ .bool) {c : Nat} (hc : c = 8 ∨ c = 16 ∨ c = 32)
    {a : Val} (hfa : Fits c a) {X : BitVec 64} (hxa : ValRel ι a X)
    (hX : ExtOK X c (lc.signOf lc.ctx.f.valueTab.size x)) :
    Lo ι 64 (movdLoc lc v [a] t) X := by
  unfold movdLoc
  simp only [hx, Option.map_some, Option.getD_some]
  generalize lc.signOf lc.ctx.f.valueTab.size x = sg at hX
  cases a with
  | poison => trivial
  | int w y =>
    have hres : ∀ z : BitVec 64, Arm64.res t z = .int .w64 z := by
      intro z; cases t <;> first | rfl | exact absurd rfl ht
    simp only [hres]
    show (if sg then y.signExtend 64 else y.setWidth 64).setWidth 64 = X.setWidth 64
    simp only [BitVec.setWidth_eq]
    simp only [Fits] at hfa
    cases w with
    | w64 => simp [Width.bits] at hfa; omega
    | w8 | w16 | w32 =>
      simp only [Width.bits] at hfa
      subst hfa
      simp only [ValRel] at hxa
      rw [hX, ← hxa]
  | ptr p => simp only [Fits] at hfa; omega
  | bool b => simp only [Fits] at hfa; omega
  | _ => exact hfa.elim

/-! ## The values -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

theorem objX?_dest {r : Nat} (hr : r < 26) : ∃ k, k < 31 ∧ objX? r = some (BitVec.ofNat 5 k) := by
  unfold objX?
  by_cases h18 : r < 18
  · exact ⟨r, by omega, by simp [h18]⟩
  · exact ⟨r + 1, by omega, by simp [h18, hr]⟩

/-- `MOVDnop x` homed in `x`'s register `r`: no code; `runLoc` writes the extension of `x` that
`signOf` names, which is the machine register when the upper-bit table names `r` (`UOK`). -/
theorem g20_nop (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {x r c cv : Nat} (hop : v.op = .ARM64MOVDnop) (hsz : v.args.size = 1)
    (hx : v.args[0]? = some x) (hvh : lc.home v.id = some (.reg r)) (hd : destOK r = true)
    (hz : r ≠ zeroReg) (hxh : lc.home x = some (.reg r)) (hcv : cls (lc.ty v.id) = some cv)
    (hcv8 : 8 ≤ cv) (hcx : cls (lc.ty x) = some c) (hc : c = 8 ∨ c = 16 ∨ c = 32)
    (hvs : j' = j) (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s')
    (hu : UOK m (some (r, c, lc.signOf lc.ctx.f.valueTab.size x))) :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  have hr26 : r < 26 := by
    simp only [destOK, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hd
    rcases hd with h | h
    · exact absurd h hz
    · exact h
  obtain ⟨k, hk, hobj⟩ := objX?_dest hr26
  obtain ⟨a, ha, hxa, hfa⟩ := arg_rel hA hl hm hinv hxh hcx (kread_arg hR hnp hx hxh hcx)
    (.inr ⟨hk, hobj⟩)
  obtain ⟨a', ha', rfl⟩ := stepLoc_nop hl htemp hop hsz hx hs
  rw [ha] at ha'
  cases ha'
  have hrx : m.rX (BitVec.ofNat 5 k) = m.x (BitVec.ofNat 5 k) := by
    unfold MState.rX
    rw [if_neg]
    intro h
    exact absurd (ofNat5_inj (q := 31) (by omega) (by omega) h) (by omega)
  rw [hrx] at hxa
  have hbool := cls_ne_bool hcv hcv8
  have hlo := lo_movd (t := lc.ty v.id) hx hbool hc hfa hxa (hu k hk hobj)
  rw [write_reg hvh hcv]
  have hrel := valRel_retypeL_lo hA hcv hbool (hlo.mono (cls_le hcv))
  have hlm := locMatch_setReg_keep hm hobj hrel (b' := b) (i' := i + 1)
  rw [hj', hvs, ← hj, ← hm.pc] at hlm
  exact ⟨m, .refl, hlm,
    (core_setReg hinv (fits_retypeL hcv _)).mono (knext_set hK hnp hvh hcv), hsi⟩

end Cases

/-! ## Narrow loads of G19's kinds -/

/-- The ops of the narrow loads. -/
def NarrowOp (o : Op) : Prop :=
  o = .ARM64MOVBload ∨ o = .ARM64MOVBUload ∨ o = .ARM64MOVHload ∨ o = .ARM64MOVHUload ∨
    o = .ARM64MOVWload ∨ o = .ARM64MOVWUload ∨ o = .ARM64MOVWloadidx ∨ o = .ARM64MOVWUloadidx ∨
    o = .ARM64MOVHloadidx ∨ o = .ARM64MOVHUloadidx ∨ o = .ARM64MOVBloadidx ∨
    o = .ARM64MOVBUloadidx ∨ o = .ARM64MOVHloadidx2 ∨ o = .ARM64MOVHUloadidx2 ∨
    o = .ARM64MOVWloadidx4 ∨ o = .ARM64MOVWUloadidx4

/-- What `narrowLd?` accepted. -/
theorem narrowLd?_spec {lc : LocCtx} {v : Value} {n : Nat} {sg : Bool}
    (h : narrowLd? lc v = some (n, sg)) :
    NarrowOp v.op ∧
      ((∃ as, loadOp? v.op = some (as, n, sg) ∧ as ≠ .MOVD ∧
        (v.aux = none ∨ (v.args[0]?.bind lc.ctx.f.value?).map (·.op) = some .SB)) ∨
       (∃ as sh, loadIdxOp? v.op = some (as, n, sh, sg) ∧ as ≠ .MOVD)) := by
  cases hl : loadOp? v.op with
  | some t =>
    obtain ⟨as, n', sg'⟩ := t
    simp only [narrowLd?, hl] at h
    split at h
    · cases h
    · rename_i has
      have has' : as ≠ .MOVD := by simpa using has
      have hop : NarrowOp v.op := by
        rcases loadOp?_op hl with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
        · rw [h1] at hl; cases hl; exact absurd rfl has'
        all_goals simp [NarrowOp, h1]
      cases haux : v.aux with
      | none =>
        simp only [haux, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hop, .inl ⟨as, rfl, has', .inl rfl⟩⟩
      | some y =>
        simp only [haux] at h
        split at h
        · rename_i hsb
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hop, .inl ⟨as, rfl, has', .inr (by simpa using hsb)⟩⟩
        · cases h
  | none =>
    cases hi : loadIdxOp? v.op with
    | none => simp [narrowLd?, hl, hi] at h
    | some t =>
      obtain ⟨as, n', sh, sg'⟩ := t
      simp only [narrowLd?, hl, hi] at h
      split at h
      · cases h
      · rename_i has
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have has' : as ≠ .MOVD := by simpa using has
        refine ⟨?_, .inr ⟨as, sh, rfl, has'⟩⟩
        rcases loadIdxOp?_op hi with ⟨h1, h2, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ |
          ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, h2, -⟩
        · exact absurd h2 has'
        all_goals first | exact absurd ‹as = .MOVD› has' | simp [NarrowOp, h1]

theorem narrow_cases {o : Op} {P : Op → Prop} (h : NarrowOp o)
    (h1 : P .ARM64MOVBload) (h2 : P .ARM64MOVBUload) (h3 : P .ARM64MOVHload)
    (h4 : P .ARM64MOVHUload) (h5 : P .ARM64MOVWload) (h6 : P .ARM64MOVWUload)
    (h7 : P .ARM64MOVWloadidx) (h8 : P .ARM64MOVWUloadidx) (h9 : P .ARM64MOVHloadidx)
    (h10 : P .ARM64MOVHUloadidx) (h11 : P .ARM64MOVBloadidx) (h12 : P .ARM64MOVBUloadidx)
    (h13 : P .ARM64MOVHloadidx2) (h14 : P .ARM64MOVHUloadidx2) (h15 : P .ARM64MOVWloadidx4)
    (h16 : P .ARM64MOVWUloadidx4) : P o := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> assumption

/-- A narrow load's op is no op that is neither a load nor a register-index load. -/
theorem NarrowOp.ne {o o' : Op} (h : NarrowOp o) (h1 : loadOp? o' = none)
    (h2 : loadIdxOp? o' = none) : o ≠ o' := by
  rintro rfl
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    (rw [h] at h1 h2; first | exact absurd h1 (by decide) | exact absurd h2 (by decide))

theorem NarrowOp.icall {o : Op} (h : NarrowOp o) : icallLead o = none :=
  narrow_cases (P := fun o => icallLead o = none) h rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl

theorem NarrowOp.mark {o : Op} (h : NarrowOp o) : markOp? o = none :=
  narrow_cases (P := fun o => markOp? o = none) h rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl

theorem NarrowOp.pb {o : Op} (h : NarrowOp o) : pbOp o = false :=
  narrow_cases (P := fun o => pbOp o = false) h rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl

theorem NarrowOp.stIdx {o : Op} (h : NarrowOp o) : storeIdxOp? o = none :=
  narrow_cases (P := fun o => storeIdxOp? o = none) h rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl

/-- A narrow load is in G3 (`VK3`) or is a register-index load of G14, by its kind of G13. -/
theorem vk13_narrow {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK13 lc g v kd)
    (hn : NarrowOp v.op) (hfv : ∀ x off, ¬ FrameVarOK lc g v x off) : VK3 lc g v kd := by
  have ne : ∀ o : Op, loadOp? o = none → loadIdxOp? o = none → v.op ≠ o := fun o h1 h2 =>
    hn.ne h1 h2
  cases h with
  | zero hop => exact absurd hop (ne _ rfl rfl)
  | g12 h =>
  cases h with
  | conv hop => exact absurd hop (ne _ rfl rfl)
  | g11 h =>
  cases h with
  | clo hop => exact absurd hop (ne _ rfl rfl)
  | g10 h =>
  cases h with
  | icall hop => rw [hn.icall] at hop; cases hop
  | selMem hop => exact absurd hop (ne _ rfl rfl)
  | selReg hop => exact absurd hop (ne _ rfl rfl)
  | g9 h =>
  cases h with
  | call hop => exact absurd hop (ne _ rfl rfl)
  | g8 _ h =>
  cases h with
  | wb hop => exact absurd hop (ne _ rfl rfl)
  | sel0 hop => exact absurd hop (ne _ rfl rfl)
  | sel1 hop => exact absurd hop (ne _ rfl rfl)
  | g7 h =>
  cases h with
  | nil hop => exact absurd hop (ne _ rfl rfl)
  | g6 _ h =>
  cases h with
  | var hfv' => exact absurd hfv' (hfv _ _)
  | g5 h =>
  cases h with
  | mark hop => rw [hn.mark] at hop; cases hop
  | g4 _ h =>
  cases h with
  | ldp hop => exact absurd hop (ne _ rfl rfl)
  | stp hop => exact absurd hop (ne _ rfl rfl)
  | sel hop =>
    rcases hop with ⟨hop, -⟩ | ⟨hop, -⟩ <;> exact absurd hop (ne _ rfl rfl)
  | g3 _ _ _ _ h => exact h

/-- A narrow load of G19's kinds is in G3 (`VK3`) or is a register-index load of G14. -/
theorem vk19_narrow {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK19 lc g v kd)
    (hn : NarrowOp v.op) (hfv : ∀ x off, ¬ FrameVarOK lc g v x off) :
    VK3 lc g v kd ∨ ∃ (as : As) (n sh : Nat) (sg : Bool) (c : Nat) (rn ri rd : Int),
      loadIdxOp? v.op = some (as, n, sh, sg) ∧ v.args.size = 3 ∧ argObj lc v 0 = .ok (64, rn) ∧
      argObj lc v 1 = .ok (64, ri) ∧ memArg lc v 2 = .ok () ∧ resObj lc v = .ok (c, rd) ∧
      (8 ≤ c ∨ c = 1 ∧ n = 1 ∧ sg = false) ∧
      kd = .prog ⟨plain as (· == idxA rn ri sh) (· == regA rd), as.name⟩ := by
  have ne : ∀ o : Op, loadOp? o = none → loadIdxOp? o = none → v.op ≠ o := fun o h1 h2 =>
    hn.ne h1 h2
  cases h with
  | pb hop => rw [hn.pb] at hop; cases hop
  | g18 _ h =>
  cases h with
  | stIdx hop => rw [hn.stIdx] at hop; cases hop
  | g17 h =>
  cases h with
  | getG hop => exact absurd hop (ne _ rfl rfl)
  | g16 h =>
  cases h with
  | addSh hop => exact absurd hop (ne _ rfl rfl)
  | g15 h =>
  cases h with
  | call hop => exact absurd hop (ne _ rfl rfl)
  | g14 _ h =>
  cases h with
  | idx hop hsz3 hao hio hma hro hc =>
    exact .inr ⟨_, _, _, _, _, _, _, _, hop, hsz3, hao, hio, hma, hro, hc, rfl⟩
  | g13 h => exact .inl (vk13_narrow h hn hfv)

end GoFV.Proof.Gen

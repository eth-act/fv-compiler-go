import GoFV.Proof.Gen.G49

/-!
# `VarsAt49` at `Addrs.fixed` and at an assignment with the running frame at `SP` (#553)

`G49Env` (`G28Env ∧ VarsAt49`) puts the `Blk.local` block of every accessed frame variable at its
frame operand, `E.ι (.local act x) = some (E.sp + frameOff L nc o)`, and `AddrAgree` (part of
`G2Env`) pins a `local` block with an address to that address.

* **At `Addrs.fixed`** the `local` blocks of one activation sit `2^24` apart (`Blk.fixedBase?`), so
  two of them at `SP + c` and `SP + d` need `c ≡ d (mod 2^24)` (`addrAgree_fixed_apart`): a
  function whose accessed `local` variables have two distinct frame offsets (all of them lie within
  the 10 MB stack-variable limit) has no `G49Env` there (`g49Env_fixed_apart`). The slice theorems
  `g49_value` … `g57_value` and `verified_mach` hold for every assignment; at `Addrs.fixed` their
  `G49Env` premise is unsatisfiable for such a function.
* **At `Addrs.atSP base`** (`docs/plans/proofs3.md` §8 item 4, the machine instance in the form
  of a parameter): activation 0's `local` blocks at `base` and undecoded, their fixed region
  decoded as activation `actM = 2^22`, which `Ptr.fixedOfAddr` never decodes
  (`fixedOfAddr_act_lt`); everything else as `Addrs.fixed`. With `base` the frame operands from
  the activation's `SP` (`baseSP`), every `G28Env` at `Addrs.fixed` of a function of activation 0
  gives a `G49Env` (`g49Env_atSP`): the variables' places are no longer a constraint.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

theorem notTemp_local (a k : Nat) : NotTemp (.local a k) := fun _ _ h => by cases h

/-! ## At `Addrs.fixed` -/

section Fixed

open scoped GoFV.SSA.Sem.Fixed

/-- At `Addrs.fixed`, `AddrAgree` puts a `local` block with an address at `Blk.fixedBase?`. -/
theorem addrAgree_fixed_local {ι : Blk → Option (BitVec 64)} (hA : AddrAgree ι) {a k : Nat}
    {p : BitVec 64} (h : ι (.local a k) = some p) :
    p = BitVec.ofNat 64 (2 ^ 62 + a * 2 ^ 42 + k * 2 ^ 24) :=
  hA _ _ _ rfl h (notTemp_local a k)

/-- At `Addrs.fixed`, two `local` blocks of one activation at `s + c` and `s + d` have offsets
congruent modulo `2^24`. -/
theorem addrAgree_fixed_apart {ι : Blk → Option (BitVec 64)} (hA : AddrAgree ι) {a x y : Nat}
    {s : BitVec 64} {c d : Int} (hx : ι (.local a x) = some (s + BitVec.ofInt 64 c))
    (hy : ι (.local a y) = some (s + BitVec.ofInt 64 d)) : (c - d) % 2 ^ 24 = 0 := by
  have ex := congrArg BitVec.toNat (addrAgree_fixed_local hA hx)
  have ey := congrArg BitVec.toNat (addrAgree_fixed_local hA hy)
  simp only [BitVec.toNat_add, BitVec.toNat_ofInt, BitVec.toNat_ofNat] at ex ey
  have := s.isLt
  omega

/-- **No `G49Env` at `Addrs.fixed`** for a function that accesses two `local` variables whose
frame operands are not `0 (mod 2^24)` apart (two distinct offsets of one frame). -/
theorem g49Env_fixed_apart {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {ret : BitVec 64} {tab : PcTab} {E : MatchEnv} (hE : G49Env lc g L ps ret tab E)
    {x y : AuxRef} (hx : x ∈ accessedVars lc) (hy : y ∈ accessedVars lc) {nc nc' : AddrName}
    {o o' : Int} (hox : varOp g x = some (nc, o)) (hoy : varOp g y = some (nc', o'))
    (hnc : nc = .AUTO ∨ nc = .PARAM) (hnc' : nc' = .AUTO ∨ nc' = .PARAM)
    (hfx : lc.ctx.tabs.forgeable x = true) (hfy : lc.ctx.tabs.forgeable y = true)
    (hne : (frameOff L nc o - frameOff L nc' o') % 2 ^ 24 ≠ 0) : False :=
  hne (addrAgree_fixed_apart hE.env.env.env.env.env.addr (hE.vars x hx nc o hox hnc hfx)
    (hE.vars y hy nc' o' hoy hnc' hfy))

end Fixed

/-! ## `Addrs.atSP`: activation 0's `local` blocks at given bases -/

/-- The activation `Addrs.atSP` decodes activation 0's fixed `local` region as: above every
activation `Ptr.fixedOfAddr` decodes. -/
def actM : Nat := 2 ^ 22

/-- `Ptr.fixedOfAddr` decodes no activation from `actM` up. -/
theorem fixedOfAddr_act_lt (x : BitVec 64) {a k : Nat}
    (h : (Ptr.fixedOfAddr x).blk = .local a k) : a < actM := by
  have hx := x.isLt
  unfold Ptr.fixedOfAddr at h
  simp only at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  · injection h with ha
    unfold actM
    omega

/-- Activation 0's `local` blocks moved to activation `actM`. -/
def Ptr.toM (p : Ptr) : Ptr :=
  match p.blk with
  | .local a k => if a = 0 then ⟨.local actM k, p.off⟩ else p
  | _ => p

/-- The bases of `Addrs.atSP base`: activation 0's `local` block `k` at `base k`, activation
`actM`'s at activation 0's fixed bases, every other block at `Blk.fixedBase?`. -/
def baseM (base : Nat → Nat) : Blk → Option Nat
  | .local a k =>
    if a = 0 then some (base k)
    else if a = actM then Blk.fixedBase? (.local 0 k) else Blk.fixedBase? (.local a k)
  | b => Blk.fixedBase? b

theorem Ptr.toM_off (p : Ptr) : (Ptr.toM p).off = p.off := by
  obtain ⟨b, o⟩ := p
  cases b <;> simp only [Ptr.toM] <;> split <;> rfl

theorem Ptr.toM_add (p : Ptr) (k : BitVec 64) : (Ptr.toM p).add k = Ptr.toM (p.add k) := by
  obtain ⟨b, o⟩ := p
  cases b <;> simp only [Ptr.toM, Ptr.add] <;> split <;> rfl

theorem Ptr.toM_inWindow (p : Ptr) : (Ptr.toM p).inWindow = p.inWindow := by
  obtain ⟨b, o⟩ := p
  cases b <;> simp only [Ptr.toM] <;> split <;> rfl

theorem Ptr.toM_eq (p : Ptr) (h : ∀ k, p.blk ≠ .local 0 k) : Ptr.toM p = p := by
  obtain ⟨b, o⟩ := p
  cases b <;> simp only [Ptr.toM]
  rename_i a k
  have : a ≠ 0 := fun ha => h k (by rw [ha])
  simp [this]

theorem baseM_toM (base : Nat → Nat) (x : BitVec 64) :
    baseM base (Ptr.toM (Ptr.fixedOfAddr x)).blk = Blk.fixedBase? (Ptr.fixedOfAddr x).blk := by
  have hlt : ∀ a k, (Ptr.fixedOfAddr x).blk = .local a k → a < actM :=
    fun _ _ h => fixedOfAddr_act_lt x h
  generalize Ptr.fixedOfAddr x = p at hlt ⊢
  obtain ⟨b, o⟩ := p
  cases b <;> simp only [Ptr.toM, baseM]
  rename_i a k
  have ha := hlt a k rfl
  by_cases h0 : a = 0
  · subst h0; simp [actM]
  · simp only [h0, ite_false, baseM]
    have : a ≠ actM := by omega
    simp [h0, this]

theorem baseOf_none_M (base : Nat → Nat) (b : Blk) (h : baseM base b = none) :
    (∃ s, b = .global s) ∨ b = .wbuf := by
  cases b with
  | global s => exact .inl ⟨s, rfl⟩
  | wbuf => exact .inr rfl
  | «local» a k =>
    simp only [baseM] at h
    split at h
    · cases h
    · split at h <;> simp [Blk.fixedBase?] at h
  | _ => simp [baseM, Blk.fixedBase?] at h

/-- **The assignment with activation 0's `local` blocks at `base`** (`docs/plans/proofs3.md` §8
item 4): those blocks undecoded (held pointers, as frame temporaries), their fixed region decoded
as activation `actM`'s blocks, every other block and address as `Addrs.fixed`. -/
@[reducible] def Addrs.atSP (base : Nat → Nat) : Addrs where
  baseOf := baseM base
  decode x := Ptr.toM (Ptr.fixedOfAddr x)
  callerSP act := BitVec.ofNat 64 (2 ^ 62 + (act + 1) * 2 ^ 42)
  baseOf_nil := rfl
  baseOf_heap _ := rfl
  baseOf_global _ := rfl
  baseOf_wbuf := rfl
  baseOf_none := baseOf_none_M base
  decode_low x h := by
    apply Ptr.toM_eq
    intro k hk
    unfold Ptr.fixedOfAddr at hk
    simp only [show ¬ 2 ^ 62 ≤ x.toNat by omega] at hk
    split at hk
    · cases hk
    · simp only [h, ite_true] at hk
      cases hk
  decode_high x h := by
    obtain ⟨a, hb⟩ := Ptr.fixedOfAddr_high x h
    generalize Ptr.fixedOfAddr x = p at hb ⊢
    obtain ⟨b, o⟩ := p
    rcases hb with hb | ⟨k, hb⟩ <;> simp only at hb <;> subst hb <;> simp only [Ptr.toM]
    · exact ⟨a, .inl rfl⟩
    · split
      · exact ⟨actM, .inr ⟨k, rfl⟩⟩
      · exact ⟨a, .inr ⟨k, rfl⟩⟩
  decode_addr x := by
    rw [baseM_toM, Ptr.toM_off]
    exact Ptr.fixedOfAddr_addr x
  decode_inWindow x := by
    rw [Ptr.toM_inWindow]
    exact Ptr.fixedOfAddr_inWindow x
  decode_add x k h := by
    rw [Ptr.toM_add, Ptr.toM_inWindow] at h
    rw [Ptr.fixedOfAddr_add h, Ptr.toM_add]

/-! ## `G49Env` at `Addrs.atSP` -/

/-- The bases of activation 0's `local` blocks at the frame operands from `sp`: variable `k`'s at
`sp + frameOff L nc o` for its operand `(nc, o)` (`varOp`). -/
def baseSP (g : G2In) (L : Link) (sp : BitVec 64) (k : Nat) : Nat :=
  match varOp g k with
  | some (nc, o) => (sp + BitVec.ofInt 64 (frameOff L nc o)).toNat
  | none => 0

/-- The injection with activation 0's `local` blocks at `baseSP`, activation `actM`'s at their
bases (activation 0's fixed bases, `baseM`), every other block as `ι`. Every block `ι` places,
`ιSP` places, so an activation extending `envAtSP` can still meet `AddrAgree` (a callee's
`CallSpec`). -/
def ιSP (g : G2In) (L : Link) (sp : BitVec 64) (ι : Blk → Option (BitVec 64)) : Blk →
    Option (BitVec 64)
  | .local a k =>
    if a = 0 then some (BitVec.ofNat 64 (baseSP g L sp k))
    else if a = actM then (Blk.fixedBase? (.local 0 k)).map (BitVec.ofNat 64)
    else ι (.local a k)
  | b => ι b

/-- `ιSP` puts activation 0's `local` block of a variable with an operand at that operand. -/
theorem ιSP_local0 {g : G2In} {L : Link} {sp : BitVec 64} {ι : Blk → Option (BitVec 64)}
    {x : Nat} {nc : AddrName} {o : Int} (h : varOp g x = some (nc, o)) :
    ιSP g L sp ι (.local 0 x) = some (sp + BitVec.ofInt 64 (frameOff L nc o)) := by
  simp only [ιSP, ite_true, baseSP, h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The activation `E` with activation 0's `local` blocks at their frame operands from `E.sp`
(`ιSP`): the activation `Addrs.atSP (baseSP g L E.sp)` relates. -/
def envAtSP (g : G2In) (L : Link) (E : MatchEnv) : MatchEnv := { E with ι := ιSP g L E.sp E.ι }

/-- `AddrAgree` at `Addrs.atSP` of `ιSP` from `AddrAgree` at `Addrs.fixed` of `ι`. -/
theorem addrAgree_atSP {g : G2In} {L : Link} {sp : BitVec 64} {ι : Blk → Option (BitVec 64)}
    (hA : @AddrAgree Addrs.fixed ι) : @AddrAgree (Addrs.atSP (baseSP g L sp)) (ιSP g L sp ι) := by
  intro b n a hb ha hnt
  have hb' : baseM (baseSP g L sp) b = some n := hb
  by_cases hl : ∃ a' k, b = .local a' k
  · obtain ⟨a', k, rfl⟩ := hl
    simp only [ιSP] at ha
    simp only [baseM] at hb'
    by_cases h0 : a' = 0
    · simp only [h0, ite_true, Option.some.injEq] at ha hb'
      rw [← ha, ← hb']
    · by_cases h1 : a' = actM
      · subst h1
        have h0' : (actM = 0) = False := eq_false h0
        simp only [h0', ite_false, ite_true, Option.map_eq_some_iff] at ha hb'
        obtain ⟨n', hn', rfl⟩ := ha
        rw [hn'] at hb'
        cases hb'
        rfl
      · simp only [h0, h1, ite_false] at ha hb'
        exact hA (.local a' k) n a hb' ha hnt
  · have e1 : ιSP g L sp ι b = ι b := by
      cases b <;> simp_all [ιSP]
    have e2 : baseM (baseSP g L sp) b = Blk.fixedBase? b := by
      cases b <;> simp_all [baseM]
    rw [e1] at ha
    rw [e2] at hb'
    exact hA b n a hb' ha hnt

/-- **`G49Env` at the machine-style assignment**: a function of activation 0 with a `G28Env` at
`Addrs.fixed` has a `G49Env` at `Addrs.atSP (baseSP g L E.sp)` for `envAtSP g L E`, `E` with its
`local` blocks at their frame operands (`ιSP`): `VarsAt49` constrains nothing there, whatever the
number of accessed `local` variables. -/
theorem g49Env_atSP {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog} {ret : BitVec 64}
    {tab : PcTab} {E : MatchEnv} (hE : @G28Env Addrs.fixed lc g L ps ret tab E)
    (hact : lc.ctx.act = 0) :
    @G49Env (Addrs.atSP (baseSP g L E.sp)) lc g L ps ret tab (envAtSP g L E) := by
  -- `obtain`, not projections: a projection would synthesize the instance
  obtain ⟨⟨⟨⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩, hv⟩, hw⟩, hi⟩, hm⟩ := hE
  have hA := addrAgree_atSP (g := g) (L := L) (sp := E.sp) h5
  letI : Addrs := Addrs.atSP (baseSP g L E.sp)
  exact
    { env :=
      { env :=
        { env :=
          { env :=
            { env :=
              { lcEq := h1
                link := h2
                pcOf := h3
                retOut := h4
                addr := hA
                glob := h6
                syms := h7
                calls := h8
                slot := h9
                extra := h10
                frame := ⟨h11.lo, h11.hi, h11.slot⟩ }
              vars := hv }
            wbs := hw }
          icalls := hi }
        memeqs := hm }
      vars := by
        intro x _ nc o ho _ _
        show ιSP g L E.sp E.ι (.local lc.ctx.act x) = _
        rw [hact]
        exact ιSP_local0 ho }

end GoFV.Proof.Gen

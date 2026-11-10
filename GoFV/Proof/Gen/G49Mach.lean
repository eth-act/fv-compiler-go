import GoFV.Proof.Gen.G49
import GoFV.Proof.Gen.G53S

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
* **At `Addrs.atSP base`** (`docs/plans/proofs3.md` §8 item 4, the machine instance in the form of
  a parameter): activation 0's `local` blocks at `base`, undecoded, their fixed region decoded as
  activation `actM = 2^22`'s, which `Ptr.fixedOfAddr` never decodes (`fixedOfAddr_act_lt`);
  everything else as `Addrs.fixed`. `Addrs.atSPO base osp` (§8 item 7, G48's mode) also puts
  activation 0's `outargs` block at `osp` (`fixedOfAddr_out_lt`); both are `Addrs.atSPM`. With
  `base` the frame operands from the activation's `SP` (`baseSP`), every `G28Env` at
  `Addrs.fixed` of a function of activation 0 gives a `G49Env` (`g49Env_atSP`; `g49Env_atSPO` at
  `Addrs.atSPO … E.sp.toNat`): the variables' places are no longer a constraint.
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

/-- **At `Addrs.fixed`, in G48's mode, no `G49Env` for a function that accesses a `local`
variable** at an operand other than `x·2^24` from `SP`: `SPInv` puts activation 0's `outargs` block
at `SP`, so `AddrAgree` pins `SP` to its fixed base `2^62`, and the variable's block, at
`SP + frameOff`, to `2^62 + x·2^24`. -/
theorem g49Env_fixed_outSP {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {ret : BitVec 64} {tab : PcTab} {E : MatchEnv} {s : LocState}
    (hE : G49Env lc g L ps ret tab E) (hosp : E.outSP = true) (hsp : SPInv E s)
    (hact : lc.ctx.act = 0) {x : AuxRef} (hx : x ∈ accessedVars lc) {nc : AddrName} {o : Int}
    (hox : varOp g x = some (nc, o)) (hnc : nc = .AUTO ∨ nc = .PARAM)
    (hfx : lc.ctx.tabs.forgeable x = true)
    (hne : (frameOff L nc o - x * 2 ^ 24) % 2 ^ 64 ≠ 0) : False := by
  have hA := hE.env.env.env.env.env.addr
  have hlc : E.lc = lc := hE.env.env.env.env.env.lcEq
  obtain ⟨hout, -⟩ := hsp hosp
  rw [hlc, hact] at hout
  have hsp0 : E.sp = BitVec.ofNat 64 (2 ^ 62 + 0 * 2 ^ 42) := hA _ _ _ rfl hout (by nofun)
  have hloc := hE.vars x hx nc o hox hnc hfx
  rw [hact] at hloc
  have ex := congrArg BitVec.toNat (addrAgree_fixed_local hA hloc)
  rw [hsp0] at ex
  simp only [BitVec.toNat_add, BitVec.toNat_ofInt, BitVec.toNat_ofNat] at ex
  apply hne
  omega

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

/-- `Ptr.fixedOfAddr` decodes no `outargs` block from activation `actM` up. -/
theorem fixedOfAddr_out_lt (x : BitVec 64) {a : Nat}
    (h : (Ptr.fixedOfAddr x).blk = .outargs a) : a < actM := by
  have hx := x.isLt
  unfold Ptr.fixedOfAddr at h
  simp only at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · injection h with ha
    unfold actM
    omega
  · cases h

/-- Activation 0's `local` blocks, and with `mv` its `outargs` block, moved to activation
`actM`. -/
def Ptr.toM (mv : Bool) (p : Ptr) : Ptr :=
  match p.blk with
  | .local a k => if a = 0 then ⟨.local actM k, p.off⟩ else p
  | .outargs a => if mv = true ∧ a = 0 then ⟨.outargs actM, p.off⟩ else p
  | _ => p

/-- The bases of `Addrs.atSPM base osp`: activation 0's `local` block `k` at `base k` and, with
`osp = some o`, its `outargs` block at `o`; activation `actM`'s at activation 0's fixed bases;
every other block at `Blk.fixedBase?`. -/
def baseM (base : Nat → Nat) (osp : Option Nat) : Blk → Option Nat
  | .local a k =>
    if a = 0 then some (base k)
    else if a = actM then Blk.fixedBase? (.local 0 k) else Blk.fixedBase? (.local a k)
  | .outargs a =>
    match osp with
    | some o =>
      if a = 0 then some o
      else if a = actM then Blk.fixedBase? (.outargs 0) else Blk.fixedBase? (.outargs a)
    | none => Blk.fixedBase? (.outargs a)
  | b => Blk.fixedBase? b

theorem Ptr.toM_off (mv : Bool) (p : Ptr) : (Ptr.toM mv p).off = p.off := by
  obtain ⟨b, o⟩ := p
  cases b <;> simp only [Ptr.toM] <;> split <;> rfl

theorem Ptr.toM_add (mv : Bool) (p : Ptr) (k : BitVec 64) :
    (Ptr.toM mv p).add k = Ptr.toM mv (p.add k) := by
  obtain ⟨b, o⟩ := p
  cases b <;> simp only [Ptr.toM, Ptr.add] <;> split <;> rfl

theorem Ptr.toM_inWindow (mv : Bool) (p : Ptr) : (Ptr.toM mv p).inWindow = p.inWindow := by
  obtain ⟨b, o⟩ := p
  cases b <;> simp only [Ptr.toM] <;> split <;> rfl

theorem Ptr.toM_eq (mv : Bool) (p : Ptr) (h : ∀ k, p.blk ≠ .local 0 k)
    (ho : p.blk ≠ .outargs 0) : Ptr.toM mv p = p := by
  obtain ⟨b, o⟩ := p
  cases b <;> simp only [Ptr.toM]
  · rename_i a k
    have : a ≠ 0 := fun ha => h k (by rw [ha])
    simp [this]
  · rename_i a
    have : a ≠ 0 := fun ha => ho (by rw [ha])
    simp [this]

theorem baseM_toM (base : Nat → Nat) (osp : Option Nat) (x : BitVec 64) :
    baseM base osp (Ptr.toM osp.isSome (Ptr.fixedOfAddr x)).blk =
      Blk.fixedBase? (Ptr.fixedOfAddr x).blk := by
  have hlt : ∀ a k, (Ptr.fixedOfAddr x).blk = .local a k → a < actM :=
    fun _ _ h => fixedOfAddr_act_lt x h
  have hlo : ∀ a, (Ptr.fixedOfAddr x).blk = .outargs a → a < actM :=
    fun _ h => fixedOfAddr_out_lt x h
  generalize Ptr.fixedOfAddr x = p at hlt hlo ⊢
  obtain ⟨b, o⟩ := p
  cases b <;> simp only [Ptr.toM, baseM]
  · rename_i a k
    have ha := hlt a k rfl
    by_cases h0 : a = 0
    · subst h0; simp [actM]
    · simp only [h0, ite_false, baseM]
      have : a ≠ actM := by omega
      simp [h0, this]
  · rename_i a
    have ha := hlo a rfl
    cases osp with
    | none => simp [baseM]
    | some o =>
      by_cases h0 : a = 0
      · subst h0; simp [actM, baseM]
      · have : a ≠ actM := by omega
        simp [h0, this, baseM]

theorem baseOf_none_M (base : Nat → Nat) (osp : Option Nat) (b : Blk)
    (h : baseM base osp b = none) : (∃ s, b = .global s) ∨ b = .wbuf := by
  cases b with
  | global s => exact .inl ⟨s, rfl⟩
  | wbuf => exact .inr rfl
  | «local» a k =>
    simp only [baseM] at h
    split at h
    · cases h
    · split at h <;> simp [Blk.fixedBase?] at h
  | outargs a =>
    cases osp with
    | none => simp [baseM, Blk.fixedBase?] at h
    | some o =>
      simp only [baseM] at h
      split at h
      · cases h
      · split at h <;> simp [Blk.fixedBase?] at h
  | _ => simp [baseM, Blk.fixedBase?] at h

/-- **The assignment with activation 0's `local` blocks at `base` and, with `osp = some o`, its
`outargs` block at `o`** (`docs/plans/proofs3.md` §8 items 4 and 7): those blocks undecoded (held
pointers, as frame temporaries), their fixed regions decoded as activation `actM`'s blocks, every
other block and address as `Addrs.fixed`. -/
@[reducible] def Addrs.atSPM (base : Nat → Nat) (osp : Option Nat) : Addrs where
  baseOf := baseM base osp
  decode x := Ptr.toM osp.isSome (Ptr.fixedOfAddr x)
  callerSP act := BitVec.ofNat 64 (2 ^ 62 + (act + 1) * 2 ^ 42)
  baseOf_nil := rfl
  baseOf_heap _ := rfl
  baseOf_global _ := rfl
  baseOf_wbuf := rfl
  baseOf_none := baseOf_none_M base osp
  decode_low x h := by
    have hlow : ∀ b, (Ptr.fixedOfAddr x).blk = b → b = .nil ∨ ∃ n, b = .heap n := by
      intro b hb
      unfold Ptr.fixedOfAddr at hb
      simp only [show ¬ 2 ^ 62 ≤ x.toNat by omega] at hb
      split at hb
      · exact .inl hb.symm
      · simp only [h, ite_true] at hb
        exact .inr ⟨_, hb.symm⟩
    apply Ptr.toM_eq
    · intro k hk
      rcases hlow _ hk with h' | ⟨n, h'⟩ <;> cases h'
    · intro hk
      rcases hlow _ hk with h' | ⟨n, h'⟩ <;> cases h'
  decode_high x h := by
    obtain ⟨a, hb⟩ := Ptr.fixedOfAddr_high x h
    generalize Ptr.fixedOfAddr x = p at hb ⊢
    obtain ⟨b, o⟩ := p
    rcases hb with hb | ⟨k, hb⟩ <;> simp only at hb <;> subst hb <;> simp only [Ptr.toM]
    · split
      · exact ⟨actM, .inl rfl⟩
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

/-- **The assignment with activation 0's `local` blocks at `base`** (§8 item 4; G48's mode not
taken: the `outargs` blocks at their fixed bases). -/
abbrev Addrs.atSP (base : Nat → Nat) : Addrs := Addrs.atSPM base none

/-- **`Addrs.atSP` with activation 0's `outargs` block at `osp`** (§8 item 7, G48's mode: the
outgoing area at `SP`). -/
abbrev Addrs.atSPO (base : Nat → Nat) (osp : Nat) : Addrs := Addrs.atSPM base (some osp)

/-! ## `G49Env` at `Addrs.atSP` -/

/-- The bases of activation 0's `local` blocks at the frame operands from `sp`: variable `k`'s at
`sp + frameOff L nc o` for its operand `(nc, o)` (`varOp`); a block without an operand keeps its
fixed base `2^62 + k·2^24` (as activation `actM`'s block `k`, which the run never allocates). -/
def baseSP (g : G2In) (L : Link) (sp : BitVec 64) (k : Nat) : Nat :=
  match varOp g k with
  | some (nc, o) => (sp + BitVec.ofInt 64 (frameOff L nc o)).toNat
  | none => 2 ^ 62 + k * 2 ^ 24

/-- The injection with activation 0's `local` blocks at `baseSP` and, with `mv`, its `outargs`
block at `sp`; activation `actM`'s at their bases (activation 0's fixed bases, `baseM`); every
other block as `ι`. Every block `ι` places, `ιSPM` places, so an activation extending it can still
meet `AddrAgree` (a callee's `CallSpec`). -/
def ιSPM (g : G2In) (L : Link) (sp : BitVec 64) (ι : Blk → Option (BitVec 64)) (mv : Bool) :
    Blk → Option (BitVec 64)
  | .local a k =>
    if a = 0 then some (BitVec.ofNat 64 (baseSP g L sp k))
    else if a = actM then (Blk.fixedBase? (.local 0 k)).map (BitVec.ofNat 64)
    else ι (.local a k)
  | .outargs a =>
    if mv = true ∧ a = 0 then some sp
    else if mv = true ∧ a = actM then (Blk.fixedBase? (.outargs 0)).map (BitVec.ofNat 64)
    else ι (.outargs a)
  | b => ι b

/-- The injection of `Addrs.atSP`: activation 0's `local` blocks at `baseSP`. -/
abbrev ιSP (g : G2In) (L : Link) (sp : BitVec 64) (ι : Blk → Option (BitVec 64)) :
    Blk → Option (BitVec 64) := ιSPM g L sp ι false

/-- The injection of `Addrs.atSPO`: also activation 0's `outargs` block at `sp`. -/
abbrev ιSPO (g : G2In) (L : Link) (sp : BitVec 64) (ι : Blk → Option (BitVec 64)) :
    Blk → Option (BitVec 64) := ιSPM g L sp ι true

/-- `ιSPM` puts activation 0's `local` block of a variable with an operand at that operand. -/
theorem ιSPM_local0 {g : G2In} {L : Link} {sp : BitVec 64} {ι : Blk → Option (BitVec 64)}
    {mv : Bool} {x : Nat} {nc : AddrName} {o : Int} (h : varOp g x = some (nc, o)) :
    ιSPM g L sp ι mv (.local 0 x) = some (sp + BitVec.ofInt 64 (frameOff L nc o)) := by
  simp only [ιSPM, ite_true, baseSP, h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `ιSP` puts activation 0's `local` block of a variable with an operand at that operand. -/
theorem ιSP_local0 {g : G2In} {L : Link} {sp : BitVec 64} {ι : Blk → Option (BitVec 64)}
    {x : Nat} {nc : AddrName} {o : Int} (h : varOp g x = some (nc, o)) :
    ιSP g L sp ι (.local 0 x) = some (sp + BitVec.ofInt 64 (frameOff L nc o)) :=
  ιSPM_local0 h

/-- `ιSPO` puts activation 0's `outargs` block at `sp`. -/
theorem ιSPO_out0 {g : G2In} {L : Link} {sp : BitVec 64} {ι : Blk → Option (BitVec 64)} :
    ιSPO g L sp ι (.outargs 0) = some sp := by
  simp [ιSPO, ιSPM]

/-- The activation `E` with activation 0's `local` blocks at their frame operands from `E.sp`
(`ιSP`): the activation `Addrs.atSP (baseSP g L E.sp)` relates. -/
def envAtSP (g : G2In) (L : Link) (E : MatchEnv) : MatchEnv := { E with ι := ιSP g L E.sp E.ι }

/-- `envAtSP` with activation 0's `outargs` block at `E.sp` too (`ιSPO`): the activation
`Addrs.atSPO (baseSP g L E.sp) E.sp.toNat` relates. -/
def envAtSPO (g : G2In) (L : Link) (E : MatchEnv) : MatchEnv :=
  { E with ι := ιSPO g L E.sp E.ι }

/-- `AddrAgree` at `Addrs.atSPM` of `ιSPM` (the `outargs` block moved iff `osp = some sp`) from
`AddrAgree` at `Addrs.fixed` of `ι`. -/
theorem addrAgree_atSPM {g : G2In} {L : Link} {sp : BitVec 64} {ι : Blk → Option (BitVec 64)}
    {osp : Option Nat} (hosp : osp = none ∨ osp = some sp.toNat)
    (hA : @AddrAgree Addrs.fixed ι) :
    @AddrAgree (Addrs.atSPM (baseSP g L sp) osp) (ιSPM g L sp ι osp.isSome) := by
  intro b n a hb ha hnt
  have hb' : baseM (baseSP g L sp) osp b = some n := hb
  by_cases ho : ∃ a', b = .outargs a'
  · obtain ⟨a', rfl⟩ := ho
    rcases hosp with rfl | rfl
    · simp only [ιSPM, Option.isSome_none, Bool.false_eq_true, false_and, ite_false] at ha
      simp only [baseM] at hb'
      exact hA (.outargs a') n a hb' ha hnt
    simp only [ιSPM, Option.isSome_some, true_and] at ha
    simp only [baseM] at hb'
    by_cases h0 : a' = 0
    · simp only [h0, ite_true, Option.some.injEq] at ha hb'
      rw [← ha, ← hb', BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · by_cases h1 : a' = actM
      · subst h1
        have h0' : (actM = 0) = False := eq_false h0
        simp only [h0', ite_false, ite_true, Option.map_eq_some_iff] at ha hb'
        obtain ⟨n', hn', rfl⟩ := ha
        rw [hn'] at hb'
        cases hb'
        rfl
      · simp only [h0, h1, ite_false] at ha hb'
        exact hA (.outargs a') n a hb' ha hnt
  by_cases hl : ∃ a' k, b = .local a' k
  · obtain ⟨a', k, rfl⟩ := hl
    simp only [ιSPM] at ha
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
  · have e1 : ιSPM g L sp ι osp.isSome b = ι b := by
      cases b <;> simp_all [ιSPM]
    have e2 : baseM (baseSP g L sp) osp b = Blk.fixedBase? b := by
      cases b <;> simp_all [baseM]
    rw [e1] at ha
    rw [e2] at hb'
    exact hA b n a hb' ha hnt

/-- `AddrAgree` at `Addrs.atSP` of `ιSP` from `AddrAgree` at `Addrs.fixed` of `ι`. -/
theorem addrAgree_atSP {g : G2In} {L : Link} {sp : BitVec 64} {ι : Blk → Option (BitVec 64)}
    (hA : @AddrAgree Addrs.fixed ι) : @AddrAgree (Addrs.atSP (baseSP g L sp)) (ιSP g L sp ι) :=
  addrAgree_atSPM (osp := none) (.inl rfl) hA

/-- `AddrAgree` at `Addrs.atSPO` of `ιSPO` from `AddrAgree` at `Addrs.fixed` of `ι`. -/
theorem addrAgree_atSPO {g : G2In} {L : Link} {sp : BitVec 64} {ι : Blk → Option (BitVec 64)}
    (hA : @AddrAgree Addrs.fixed ι) :
    @AddrAgree (Addrs.atSPO (baseSP g L sp) sp.toNat) (ιSPO g L sp ι) :=
  addrAgree_atSPM (osp := some sp.toNat) (.inr rfl) hA

/-- `G49Env` at `Addrs.atSPM` for the activation `E` with `ιSPM`. -/
theorem g49Env_atSPM {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog} {ret : BitVec 64}
    {tab : PcTab} {E : MatchEnv} {osp : Option Nat} (hosp : osp = none ∨ osp = some E.sp.toNat)
    (hE : @G28Env Addrs.fixed lc g L ps ret tab E) (hact : lc.ctx.act = 0) :
    @G49Env (Addrs.atSPM (baseSP g L E.sp) osp) lc g L ps ret tab
      { E with ι := ιSPM g L E.sp E.ι osp.isSome } := by
  -- `obtain`, not projections: a projection would synthesize the instance
  obtain ⟨⟨⟨⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩, hv⟩, hw⟩, hi⟩, hm⟩ := hE
  have hA := addrAgree_atSPM (g := g) (L := L) (sp := E.sp) hosp h5
  letI : Addrs := Addrs.atSPM (baseSP g L E.sp) osp
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
        show ιSPM g L E.sp E.ι osp.isSome (.local lc.ctx.act x) = _
        rw [hact]
        exact ιSPM_local0 ho }

/-- **`G49Env` at the machine-style assignment**: a function of activation 0 with a `G28Env` at
`Addrs.fixed` has a `G49Env` at `Addrs.atSP (baseSP g L E.sp)` for `envAtSP g L E`, `E` with its
`local` blocks at their frame operands (`ιSP`): `VarsAt49` constrains nothing there, whatever the
number of accessed `local` variables. -/
theorem g49Env_atSP {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog} {ret : BitVec 64}
    {tab : PcTab} {E : MatchEnv} (hE : @G28Env Addrs.fixed lc g L ps ret tab E)
    (hact : lc.ctx.act = 0) :
    @G49Env (Addrs.atSP (baseSP g L E.sp)) lc g L ps ret tab (envAtSP g L E) :=
  g49Env_atSPM (osp := none) (.inl rfl) hE hact

/-- **`G49Env` at the machine-style assignment in G48's mode**: `g49Env_atSP` with activation 0's
`outargs` block at `SP` too (`Addrs.atSPO (baseSP g L E.sp) E.sp.toNat`, `envAtSPO g L E`). -/
theorem g49Env_atSPO {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog} {ret : BitVec 64}
    {tab : PcTab} {E : MatchEnv} (hE : @G28Env Addrs.fixed lc g L ps ret tab E)
    (hact : lc.ctx.act = 0) :
    @G49Env (Addrs.atSPO (baseSP g L E.sp) E.sp.toNat) lc g L ps ret tab (envAtSPO g L E) :=
  g49Env_atSPM (osp := some E.sp.toNat) (.inr rfl) hE hact

/-- In `envAtSPO g L E` of activation 0, the `outargs` block sits at `SP` (`SPInv`'s first
part). -/
theorem envAtSPO_out {g : G2In} {L : Link} {E : MatchEnv} (hact : E.lc.ctx.act = 0) :
    (envAtSPO g L E).ι (.outargs (envAtSPO g L E).lc.ctx.act) = some (envAtSPO g L E).sp := by
  show ιSPO g L E.sp E.ι (.outargs E.lc.ctx.act) = some E.sp
  rw [hact]
  exact ιSPO_out0

end GoFV.Proof.Gen

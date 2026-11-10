import GoFV.Proof.Obj.Words
import GoFV.Proof.Obj.Prog
import GoFV.Proof.Obj.Spec
import GoFV.Proof.Gen.Basic
import GoFV.Proof.Gen.Progs7

variable [GoFV.SSA.Sem.Addrs]

/-!
# `runProg` of P0 is matched by `runMach` of the linked words (`docs/plans/proofs3.md` §6)

The relation `ObjRel f s t` between a P0 state `s` (`runProg` under `Link.byId`) and a machine
state `t` (`runMach` of `linkCode`): every general register but `X27` (the assembler's scratch)
and `X30` equal, `X30` and the PC related by the address map `f` (`objMap`: the P0 address of
the Prog at index `k` ↦ `base + Tab.offs[k]`, the P0 end address ↦ `base + Tab.endOff`, every
other address to itself), `SP`, the vector registers, the flags and the memory equal.

`obj_step`: one `PStep` of `runProg` (a Prog, or a hook that returns) from related states is
matched by `MStar` of `runMach` (`symWords_sound`, `progSym_sound`, `checkObj_spec`), keeping
`ObjInv` (the PC at a Prog, or at a symbol after a call whose return address is a Prog or the
end); the hooks must treat related states alike (`HookMap`, the trusted runtime boundary of
`docs/proofs/STATUS.md`). `obj_star` iterates it over `PStar`. P0's `RET` is the epilogue's
(`obj_exit` in `Frame.lean`): `runProg` never steps it.
-/

namespace GoFV.Proof.Obj

open GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj
open GoFV.SSA.Sem (MStep MStar)
open GoFV.Proof.Gen (PStep PStar maxId PPanics)

/-! ## Addresses -/

/-- The P0 address of Prog ID `id` (`Link.byId` at `text0`). -/
def addrP (text0 : BitVec 64) (id : Nat) : BitVec 64 := text0 + BitVec.ofNat 64 (4 * id)

/-- The P0 address after the last Prog (`runProg`'s return address in the composition). -/
def endP (text0 : BitVec 64) (ps : List Prog) : BitVec 64 := addrP text0 (maxId ps + 1)

/-- P0 address ↦ machine address. -/
def objMap (ps : List Prog) (offs : List Nat) (endOff : Nat) (text0 base : BitVec 64)
    (a : BitVec 64) : BitVec 64 :=
  match (ps.zip offs).find? (fun po => addrP text0 po.1.id == a) with
  | some (_, q) => base + BitVec.ofNat 64 q
  | none => if a = endP text0 ps then base + BitVec.ofNat 64 endOff else a

/-- A P0 state and a machine state related by the address map `f`. -/
structure ObjRel (f : BitVec 64 → BitVec 64) (s t : MState) : Prop where
  x : ∀ k : Reg, k ≠ 27 → k ≠ 30 → t.x k = s.x k
  x30 : t.x 30 = f (s.x 30)
  sp : t.sp = s.sp
  v : t.v = s.v
  nzcv : t.nzcv = s.nzcv
  mem : t.mem = s.mem
  pc : t.pc = f s.pc

/-- The address of a Prog of the list. -/
def IsProgAddr (text0 : BitVec 64) (ps : List Prog) (a : BitVec 64) : Prop :=
  ∃ p ∈ ps, addrP text0 p.id = a

/-- Where a P0 run can be: at a Prog, or at a symbol after a call (its return address a Prog
or the end). -/
def ObjInv (L : Link) (ps : List Prog) (s : MState) : Prop :=
  IsProgAddr L.text ps s.pc ∨
    ((∃ y, s.pc = L.sym y) ∧ (IsProgAddr L.text ps (s.x 30) ∨ s.x 30 = endP L.text ps))

/-- The runtime hooks treat related states alike and return to the link register: a hook that
returns from a P0 state at a symbol (after a call) returns from every related machine state, to
related states, at the P0 state's `X30` (a Prog or the end; arm64 `BL`/`RET`: the callee
returns to `LR`, `docs/proofs/STATUS.md` Assumptions). -/
def HookMap (H : Hooks) (L : Link) (ps : List Prog) (f : BitVec 64 → BitVec 64) : Prop :=
  ∀ s t s', ObjRel f s t → (∃ y, s.pc = L.sym y) →
    (IsProgAddr L.text ps (s.x 30) ∨ s.x 30 = endP L.text ps) → H.call s = some (.ret s') →
    ∃ t', H.call t = some (.ret t') ∧ ObjRel f s' t' ∧ s'.pc = s.x 30

/-- Where `checkObj` relied on `X27` (`Tab.ok27`: the Prog before it in the list left `X27` as
P0's `R27`, and no Prog branches to it), the machine's `X27` is P0's (`at27`); after a call, the
return address is no such Prog (`ret27`: a callee returns with any `X27`). -/
structure X27At (tab : Tab) (L : Link) (ps : List Prog) (s t : MState) : Prop where
  at27 : ∀ j (hj : j < ps.length), addrP L.text ps[j].id = s.pc → tab.ok27[j]? = some true →
    t.x 27 = s.x 27
  ret27 : (∃ y, s.pc = L.sym y) → ∀ j (hj : j < ps.length), addrP L.text ps[j].id = s.x 30 →
    tab.ok27[j]? ≠ some true

/-- At the Prog at index `k`, `X27` agrees if `checkObj` relied on it there. -/
theorem x27_here {tab : Tab} {L : Link} {ps : List Prog} {s t : MState}
    (hX : X27At tab L ps s t) {k : Nat} (hk : k < ps.length) (hpc : s.pc = addrP L.text ps[k].id) :
    tab.ok27[k]?.getD false = true → t.x 27 = s.x 27 := fun h =>
  hX.at27 k hk hpc.symm (by
    cases hh : tab.ok27[k]? with
    | none => rw [hh] at h; cases h
    | some v => rw [hh] at h; cases h; rfl)

/-- The runtime hooks panic alike from related states: a hook that panics from a P0 state at a
symbol (after a call) panics with the same panic from every related machine state (trusted, as
`HookMap`). -/
def HookPanicMap (H : Hooks) (L : Link) (ps : List Prog) (f : BitVec 64 → BitVec 64) : Prop :=
  ∀ s t e s', ObjRel f s t → (∃ y, s.pc = L.sym y) →
    (IsProgAddr L.text ps (s.x 30) ∨ s.x 30 = endP L.text ps) →
    H.call s = some (.panicked e s') → ∃ t', H.call t = some (.panicked e t')

/-- What the simulation of one function rests on: the validator accepted, the P0 layout is
`Link.byId` with the validated frame, the code is the linked text, the return address and the
symbols (callees) are outside the code and are not P0 addresses. -/
structure ObjEnv (ps : Array Prog) (spills : Array Spill) (o : ObjIn) (tab : Tab) (L : Link)
    (base : BitVec 64) (code : Code) (retM : BitVec 64) : Prop where
  check : checkObj ps spills o = .ok tab
  link : L = Link.byId L.sym L.text tab.autosize tab.extrasize ps.toList
  linked : linkCode base L.sym o.text o.relocs.toList = .ok code
  size : o.text.size ≤ 2 ^ 64
  ret : code retM = none
  syms : ∀ y, code (L.sym y) = none ∧ L.sym y ≠ retM ∧ ¬ IsProgAddr L.text ps.toList (L.sym y) ∧
    L.sym y ≠ endP L.text ps.toList

/-- The address map of a validated function. -/
def ObjEnv.map (tab : Tab) (ps : Array Prog) (L : Link) (base : BitVec 64) :
    BitVec 64 → BitVec 64 :=
  objMap ps.toList tab.offs.toList tab.endOff L.text base

/-- Where `X27` agrees, at a Prog or the end (e.g. a P0 state made from the machine state):
`X27At`. -/
theorem x27At_of_eq {ps : Array Prog} {spills : Array Spill} {o : ObjIn} {tab : Tab} {L : Link}
    {base : BitVec 64} {code : Code} {retM : BitVec 64}
    (hE : ObjEnv ps spills o tab L base code retM) {s t : MState} (h27 : t.x 27 = s.x 27)
    (hpc : IsProgAddr L.text ps.toList s.pc ∨ s.pc = endP L.text ps.toList) :
    X27At tab L ps.toList s t :=
  ⟨fun _ _ _ _ => h27, fun ⟨y, hy⟩ _ _ _ _ => by
    rcases hpc with h | h
    · exact (hE.syms y).2.2.1 (hy ▸ h)
    · exact (hE.syms y).2.2.2 (hy ▸ h)⟩

/-- At a `CALL (Rn)` (`isICall`), the register holds a symbol's address: the step goes to a
linked function entry (a function value's code pointer, an itab's `fun` entry; trusted per run,
`docs/plans/proofs3.md` §6, §7). -/
def ICallOut (L : Link) (ps : List Prog) (s : MState) : Prop :=
  ∀ p s', progAt? L ps s.pc = some p → isICall p = true → progStep L p s = .ok s' →
    ∃ y, s'.pc = L.sym y

/-- A list without `CALL (Rn)` meets `ICallOut` everywhere. -/
theorem iCallOut_of_none {L : Link} {ps : List Prog} (h : ∀ p ∈ ps, isICall p = false)
    (s : MState) : ICallOut L ps s := by
  intro p s' hp hi _
  unfold progAt? at hp
  have := h p (List.mem_of_find?_eq_some hp)
  rw [hi] at this
  cases this

/-! ## The address map -/

section Addr

variable {text0 base : BitVec 64} {ps : List Prog} {offs : List Nat} {e : Nat}

theorem objMap_at (hnd : (ps.map (·.id)).Nodup) (hlt : ∀ p ∈ ps, p.id < 2 ^ 32)
    (hlen : offs.length = ps.length) {k : Nat} (hk : k < ps.length) :
    objMap ps offs e text0 base (addrP text0 ps[k].id) =
      base + BitVec.ofNat 64 (offs[k]'(by omega)) := by
  unfold objMap
  have hfind : (ps.zip offs).find? (fun po => addrP text0 po.1.id == addrP text0 ps[k].id) =
      some (ps[k], offs[k]'(by omega)) := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨by simp, k, by simp [hlen, hk], by simp, fun j hj => ?_⟩
    have hjk : j < ps.length := by omega
    simp only [List.getElem_zip, Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne,
      ne_eq]
    intro h
    have hj' := hlt _ (List.getElem_mem hjk)
    have hk' := hlt _ (List.getElem_mem hk)
    exact GoFV.Proof.Gen.id_ne_of_nodup hnd hjk hk (by omega)
      (GoFV.Proof.Gen.addr_inj (by omega) (by omega) h)
  rw [hfind]

theorem objMap_none {a : BitVec 64} (ha : ¬ IsProgAddr text0 ps a) :
    (ps.zip offs).find? (fun po => addrP text0 po.1.id == a) = none := by
  rw [List.find?_eq_none]
  intro x hx h
  apply ha
  exact ⟨x.1, List.of_mem_zip hx |>.1, by simpa using h⟩

theorem not_isProgAddr_end (hlt : ∀ p ∈ ps, p.id < 2 ^ 32) :
    ¬ IsProgAddr text0 ps (endP text0 ps) := by
  rintro ⟨p, hp, h⟩
  have hm := GoFV.Proof.Gen.maxId_lt (by decide) hlt
  have hle := GoFV.Proof.Gen.le_maxId hp
  have := GoFV.Proof.Gen.addr_inj (text := text0) (i := p.id) (k := maxId ps + 1)
    (by have := hlt p hp; omega) (by omega) h
  omega

theorem objMap_end (hlt : ∀ p ∈ ps, p.id < 2 ^ 32) :
    objMap ps offs e text0 base (endP text0 ps) = base + BitVec.ofNat 64 e := by
  unfold objMap
  rw [objMap_none (not_isProgAddr_end hlt)]
  simp

theorem objMap_fix {a : BitVec 64} (ha : ¬ IsProgAddr text0 ps a) (he : a ≠ endP text0 ps) :
    objMap ps offs e text0 base a = a := by
  unfold objMap
  rw [objMap_none ha]
  simp [he]

end Addr

/-! ## Evaluation in related states -/

theorem Ex.regsOK_reads {e : Ex} (h : e.regsOK = true) {r : Nat} (hr : e.reads r = true) :
    r < 31 ∧ r ≠ 27 ∧ r ≠ 30 := by
  induction e with
  | x q => simp [Ex.regsOK, Ex.reads] at h hr; omega
  | sp | k | sym | vlo | vq | fcvtz => simp [Ex.reads] at hr
  | ld _ a ih | shift _ _ _ a ih | ext _ _ a ih | lo32 a ih | sext _ a ih | page a ih
  | dp1 _ _ a ih | inv _ a ih =>
    exact ih (by simpa [Ex.regsOK] using h) (by simpa [Ex.reads] using hr)
  | add a b iha ihb | addSub _ _ a b iha ihb | logical _ _ a b iha ihb | bfm _ _ _ _ a b iha ihb
  | csel _ _ _ _ a b iha ihb | dp2 _ _ a b iha ihb =>
    simp only [Ex.regsOK, Bool.and_eq_true] at h
    simp only [Ex.reads, Bool.or_eq_true] at hr
    rcases hr with hr | hr
    · exact iha h.1 hr
    · exact ihb h.2 hr
  | dp3 _ _ _ a b d iha ihb ihd =>
    simp only [Ex.regsOK, Bool.and_eq_true] at h
    simp only [Ex.reads, Bool.or_eq_true] at hr
    rcases hr with (hr | hr) | hr
    · exact iha h.1.1 hr
    · exact ihb h.1.2 hr
    · exact ihd h.2 hr
  | eqsel _ a b u w iha ihb ihu ihw =>
    simp only [Ex.regsOK, Bool.and_eq_true] at h
    simp only [Ex.reads, Bool.or_eq_true] at hr
    rcases hr with ((hr | hr) | hr) | hr
    · exact iha h.1.1.1 hr
    · exact ihb h.1.1.2 hr
    · exact ihu h.1.2 hr
    · exact ihw h.2 hr

theorem VEx.regsOK_reads {e : VEx} (h : e.regsOK = true) {r : Nat} (hr : e.reads r = true) :
    r < 31 ∧ r ≠ 27 ∧ r ≠ 30 := by
  induction e with
  | v | k => simp [VEx.reads] at hr
  | ofX _ a | ld _ a | cvtf _ _ _ a =>
    exact Ex.regsOK_reads (by simpa [VEx.regsOK] using h) (by simpa [VEx.reads] using hr)
  | fp1 _ _ a ih => exact ih (by simpa [VEx.regsOK] using h) (by simpa [VEx.reads] using hr)
  | fp2 _ _ a b iha ihb | fcsel _ _ a b iha ihb =>
    simp only [VEx.regsOK, Bool.and_eq_true] at h
    simp only [VEx.reads, Bool.or_eq_true] at hr
    rcases hr with hr | hr
    · exact iha h.1 hr
    · exact ihb h.2 hr
  | fp3 _ _ _ a b d iha ihb ihd =>
    simp only [VEx.regsOK, Bool.and_eq_true] at h
    simp only [VEx.reads, Bool.or_eq_true] at hr
    rcases hr with (hr | hr) | hr
    · exact iha h.1.1 hr
    · exact ihb h.1.2 hr
    · exact ihd h.2 hr

theorem Fl.regsOK_reads {fl : Fl} (h : fl.regsOK = true) {r : Nat} (hr : fl.reads r = true) :
    r < 31 ∧ r ≠ 27 ∧ r ≠ 30 := by
  cases fl with
  | init => simp [Fl.reads] at hr
  | addSub _ _ a b | ands _ a b =>
    simp only [Fl.regsOK, Bool.and_eq_true] at h
    simp only [Fl.reads, Bool.or_eq_true] at hr
    exact hr.elim (Ex.regsOK_reads h.1) (Ex.regsOK_reads h.2)
  | fcmp _ a b =>
    simp only [Fl.regsOK, Bool.and_eq_true] at h
    simp only [Fl.reads, Bool.or_eq_true] at hr
    exact hr.elim (VEx.regsOK_reads h.1) (VEx.regsOK_reads h.2)

/-- `Ex.regsOK_reads` of `regsOK30` (`X27` allowed). -/
theorem Ex.regsOK30_reads {e : Ex} (h : e.regsOK30 = true) {r : Nat} (hr : e.reads r = true) :
    r < 31 ∧ r ≠ 30 := by
  induction e with
  | x q => simp [Ex.regsOK30, Ex.reads] at h hr; omega
  | sp | k | sym | vlo | vq | fcvtz => simp [Ex.reads] at hr
  | ld _ a ih | shift _ _ _ a ih | ext _ _ a ih | lo32 a ih | sext _ a ih | page a ih
  | dp1 _ _ a ih | inv _ a ih =>
    exact ih (by simpa [Ex.regsOK30] using h) (by simpa [Ex.reads] using hr)
  | add a b iha ihb | addSub _ _ a b iha ihb | logical _ _ a b iha ihb | bfm _ _ _ _ a b iha ihb
  | csel _ _ _ _ a b iha ihb | dp2 _ _ a b iha ihb =>
    simp only [Ex.regsOK30, Bool.and_eq_true] at h
    simp only [Ex.reads, Bool.or_eq_true] at hr
    rcases hr with hr | hr
    · exact iha h.1 hr
    · exact ihb h.2 hr
  | dp3 _ _ _ a b d iha ihb ihd =>
    simp only [Ex.regsOK30, Bool.and_eq_true] at h
    simp only [Ex.reads, Bool.or_eq_true] at hr
    rcases hr with (hr | hr) | hr
    · exact iha h.1.1 hr
    · exact ihb h.1.2 hr
    · exact ihd h.2 hr
  | eqsel _ a b u w iha ihb ihu ihw =>
    simp only [Ex.regsOK30, Bool.and_eq_true] at h
    simp only [Ex.reads, Bool.or_eq_true] at hr
    rcases hr with ((hr | hr) | hr) | hr
    · exact iha h.1.1.1 hr
    · exact ihb h.1.1.2 hr
    · exact ihu h.1.2 hr
    · exact ihw h.2 hr

theorem VEx.regsOK30_reads {e : VEx} (h : e.regsOK30 = true) {r : Nat} (hr : e.reads r = true) :
    r < 31 ∧ r ≠ 30 := by
  induction e with
  | v | k => simp [VEx.reads] at hr
  | ofX _ a | ld _ a | cvtf _ _ _ a =>
    exact Ex.regsOK30_reads (by simpa [VEx.regsOK30] using h) (by simpa [VEx.reads] using hr)
  | fp1 _ _ a ih => exact ih (by simpa [VEx.regsOK30] using h) (by simpa [VEx.reads] using hr)
  | fp2 _ _ a b iha ihb | fcsel _ _ a b iha ihb =>
    simp only [VEx.regsOK30, Bool.and_eq_true] at h
    simp only [VEx.reads, Bool.or_eq_true] at hr
    rcases hr with hr | hr
    · exact iha h.1 hr
    · exact ihb h.2 hr
  | fp3 _ _ _ a b d iha ihb ihd =>
    simp only [VEx.regsOK30, Bool.and_eq_true] at h
    simp only [VEx.reads, Bool.or_eq_true] at hr
    rcases hr with (hr | hr) | hr
    · exact iha h.1.1 hr
    · exact ihb h.1.2 hr
    · exact ihd h.2 hr

theorem Fl.regsOK30_reads {fl : Fl} (h : fl.regsOK30 = true) {r : Nat} (hr : fl.reads r = true) :
    r < 31 ∧ r ≠ 30 := by
  cases fl with
  | init => simp [Fl.reads] at hr
  | addSub _ _ a b | ands _ a b =>
    simp only [Fl.regsOK30, Bool.and_eq_true] at h
    simp only [Fl.reads, Bool.or_eq_true] at hr
    exact hr.elim (Ex.regsOK30_reads h.1) (Ex.regsOK30_reads h.2)
  | fcmp _ a b =>
    simp only [Fl.regsOK30, Bool.and_eq_true] at h
    simp only [Fl.reads, Bool.or_eq_true] at hr
    exact hr.elim (VEx.regsOK30_reads h.1) (VEx.regsOK30_reads h.2)

/-- `regsOK` excludes `X27` and `X30`, `regsOK30` only `X30`. -/
private theorem readsK_of {k : Bool} {r : Nat} (h0 : k = false → r < 31 ∧ r ≠ 27 ∧ r ≠ 30)
    (h1 : k = true → r < 31 ∧ r ≠ 30) : r < 31 ∧ (k = false → r ≠ 27) ∧ r ≠ 30 := by
  cases k
  · obtain ⟨a, b, c⟩ := h0 rfl
    exact ⟨a, fun _ => b, c⟩
  · obtain ⟨a, c⟩ := h1 rfl
    exact ⟨a, (fun h => nomatch h), c⟩

theorem Ex.regsOKK_reads {k : Bool} {e : Ex} (h : e.regsOKK k = true) {r : Nat}
    (hr : e.reads r = true) : r < 31 ∧ (k = false → r ≠ 27) ∧ r ≠ 30 :=
  readsK_of (fun hk => Ex.regsOK_reads (by simpa [Ex.regsOKK, hk] using h) hr)
    (fun hk => Ex.regsOK30_reads (by simpa [Ex.regsOKK, hk] using h) hr)

theorem VEx.regsOKK_reads {k : Bool} {e : VEx} (h : e.regsOKK k = true) {r : Nat}
    (hr : e.reads r = true) : r < 31 ∧ (k = false → r ≠ 27) ∧ r ≠ 30 :=
  readsK_of (fun hk => VEx.regsOK_reads (by simpa [VEx.regsOKK, hk] using h) hr)
    (fun hk => VEx.regsOK30_reads (by simpa [VEx.regsOKK, hk] using h) hr)

theorem Fl.regsOKK_reads {k : Bool} {fl : Fl} (h : fl.regsOKK k = true) {r : Nat}
    (hr : fl.reads r = true) : r < 31 ∧ (k = false → r ≠ 27) ∧ r ≠ 30 :=
  readsK_of (fun hk => Fl.regsOK_reads (by simpa [Fl.regsOKK, hk] using h) hr)
    (fun hk => Fl.regsOK30_reads (by simpa [Fl.regsOKK, hk] using h) hr)

theorem reg_ne_of {r : Nat} (hr : r < 31) (h27 : r ≠ 27) (h30 : r ≠ 30) :
    (BitVec.ofNat 5 r : Reg) ≠ 27 ∧ (BitVec.ofNat 5 r : Reg) ≠ 30 := by
  constructor <;> intro h <;> have := congrArg BitVec.toNat h <;> simp at this <;> omega

/-- A register read over registers related before a Prog (`k`: `X27` too) is equal in related
states. -/
theorem x_rel {f : BitVec 64 → BitVec 64} {s t : MState} (hR : ObjRel f s t) {k : Bool}
    (h27 : k = true → t.x 27 = s.x 27) {r : Nat} (h : r < 31 ∧ (k = false → r ≠ 27) ∧ r ≠ 30) :
    t.x (BitVec.ofNat 5 r) = s.x (BitVec.ofNat 5 r) := by
  obtain ⟨h31, h27r, h30⟩ := h
  by_cases hr : r = 27
  · subst hr
    cases k
    · exact absurd rfl (h27r rfl)
    · exact h27 rfl
  · obtain ⟨h27', h30'⟩ := reg_ne_of h31 hr h30
    exact hR.x _ h27' h30'

theorem eval_rel {f : BitVec 64 → BitVec 64} {s t : MState} (hR : ObjRel f s t) {k : Bool}
    (h27 : k = true → t.x 27 = s.x 27) (sym : Nat → BitVec 64) {e : Ex} (he : e.regsOKK k = true) :
    e.eval ⟨t, sym⟩ = e.eval ⟨s, sym⟩ :=
  Ex.eval_congr (c := ⟨t, sym⟩) (c' := ⟨s, sym⟩) rfl hR.sp hR.mem hR.nzcv hR.v e
    fun _ hr => x_rel hR h27 (Ex.regsOKK_reads he hr)

theorem vex_eval_rel {f : BitVec 64 → BitVec 64} {s t : MState} (hR : ObjRel f s t) {k : Bool}
    (h27 : k = true → t.x 27 = s.x 27) (sym : Nat → BitVec 64) {e : VEx}
    (he : e.regsOKK k = true) : e.eval ⟨t, sym⟩ = e.eval ⟨s, sym⟩ :=
  VEx.eval_congr (c := ⟨t, sym⟩) (c' := ⟨s, sym⟩) rfl hR.sp hR.mem hR.nzcv hR.v e
    fun _ hr => x_rel hR h27 (VEx.regsOKK_reads he hr)

theorem fl_eval_rel {f : BitVec 64 → BitVec 64} {s t : MState} (hR : ObjRel f s t) {k : Bool}
    (h27 : k = true → t.x 27 = s.x 27) (sym : Nat → BitVec 64) {fl : Fl}
    (hfl : fl.regsOKK k = true) : fl.eval ⟨t, sym⟩ = fl.eval ⟨s, sym⟩ :=
  Fl.eval_congr (c := ⟨t, sym⟩) (c' := ⟨s, sym⟩) rfl hR.sp hR.mem hR.nzcv hR.v fl
    fun _ hr => x_rel hR h27 (Fl.regsOKK_reads hfl hr)

theorem storesMem_rel {f : BitVec 64 → BitVec 64} {s t : MState} (hR : ObjRel f s t) {k : Bool}
    (h27 : k = true → t.x 27 = s.x 27) (sym : Nat → BitVec 64) :
    ∀ (st : List (Ex × Nat × Ex)) (m : Memory),
      (∀ x ∈ st, x.1.regsOKK k = true ∧ x.2.2.regsOKK k = true) →
      storesMem ⟨t, sym⟩ st m = storesMem ⟨s, sym⟩ st m
  | [], _, _ => rfl
  | (a, n, v) :: st, m, h => by
    have ha := (h (a, n, v) (by simp)).1
    have hv := (h (a, n, v) (by simp)).2
    have hv' : v.eval128 ⟨t, sym⟩ = v.eval128 ⟨s, sym⟩ :=
      Ex.eval128_congr (c := ⟨t, sym⟩) (c' := ⟨s, sym⟩) rfl hR.sp hR.mem hR.nzcv hR.v v
        fun _ hr => x_rel hR h27 (Ex.regsOKK_reads hv hr)
    simp only [storesMem, eval_rel hR h27 sym ha, hv']
    exact storesMem_rel hR h27 sym st _ fun x hx => h x (by simp [hx])

theorem holds_init (c : Ctx) : Holds c {} c.s where
  x _ _ := by simp [Sym.getX, Ex.eval]
  x31 := rfl
  sp := rfl
  nzcv := rfl
  v := rfl
  mem := rfl
  x30 := by simp [Sym.getX, Ex.eval]

/-! ## One step -/

private theorem mem_cmpRegs {r : Nat} : r ∈ cmpRegs ↔ r < 31 ∧ r ≠ 27 ∧ r ≠ 30 := by
  simp only [cmpRegs, List.mem_filter, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq]

private theorem lookup_ok {α : Type} {ok : α → Bool} {l : List (Nat × α)}
    (h : ∀ x ∈ l, ok x.2 = true) {r : Nat} {v : α} (hl : l.lookup r = some v) : ok v = true := by
  induction l with
  | nil => simp at hl
  | cons a l ih =>
    obtain ⟨a1, a2⟩ := a
    by_cases hr : r = a1
    · subst hr
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hl
      subst hl
      exact h (r, a2) (by simp)
    · have hne : (r == a1) = false := by simpa using hr
      simp only [List.lookup, hne] at hl
      exact ih (fun x hx => h x (by simp [hx])) hl

/-- What `readsTmpK k = false` says about a Prog effect. -/
private theorem readsTmp_false {k : Bool} {σ : Sym} (h : σ.readsTmpK k = false) :
    (∀ r ∈ cmpRegs, (σ.getX r).regsOKK k = true) ∧ σ.sp.regsOKK k = true ∧
    σ.fl.regsOKK k = true ∧ (∀ x ∈ σ.loads, x.1.regsOKK k = true) ∧
    (∀ x ∈ σ.stores, x.1.regsOKK k = true ∧ x.2.2.regsOKK k = true) ∧
    (∀ r, (σ.getV r).regsOKK k = true) := by
  simp only [Sym.readsTmpK, Bool.or_eq_false_iff, List.any_eq_false, Bool.not_eq_true',
    Bool.not_eq_false'] at h
  obtain ⟨⟨⟨⟨⟨hx, hsp⟩, hfl⟩, hld⟩, hst⟩, hv⟩ := h
  refine ⟨fun r hr => ?_, by simpa using hsp, by simpa using hfl,
    fun x hx => by simpa using hld x hx,
    fun x hx => by simpa using hst x hx, fun r => ?_⟩
  · unfold Sym.getX
    cases hl : σ.x.lookup r with
    | none =>
      obtain ⟨h31, h27, h30⟩ := mem_cmpRegs.1 hr
      cases k <;> simp [Ex.regsOKK, Ex.regsOK, Ex.regsOK30, h31, h27, h30]
    | some v => exact lookup_ok (ok := Ex.regsOKK k) (fun x hx' => by simpa using hx x hx') hl
  · unfold Sym.getV
    cases hl : σ.v.lookup r with
    | none => cases k <;> rfl
    | some v => exact lookup_ok (ok := VEx.regsOKK k) (fun x hx' => by simpa using hv x hx') hl

/-- The machine words perform no access in the nil page if the Prog does not. -/
private theorem noNil_rel {f : BitVec 64 → BitVec 64} {sym : Nat → BitVec 64} {pσ mσ : Sym}
    {s t : MState} {k : Bool} (hR : ObjRel f s t) (h27 : k = true → t.x 27 = s.x 27)
    (hse : sameEffectK k mσ pσ = .ok ()) (hn : NoNil ⟨s, sym⟩ pσ) : NoNil ⟨t, sym⟩ mσ := by
  obtain ⟨-, -, -, -, -, hst, hld, hrt, -⟩ := sameEffect_spec hse
  obtain ⟨-, -, -, hldok, hstok, -⟩ := readsTmp_false hrt
  refine ⟨fun a n hx => ?_, fun a n v hx => ?_⟩
  · have hx' := hld _ hx
    rw [eval_rel hR h27 sym (hldok _ hx')]
    exact hn.1 a n hx'
  · rw [hst] at hx
    rw [eval_rel hR h27 sym (hstok _ hx).1]
    exact hn.2 a n v hx

/-- The registers but `X30`, `SP`, the vector registers, the flags and the memory after the
words and after the Prog agree. -/
private theorem obj_core {f : BitVec 64 → BitVec 64} {sym : Nat → BitVec 64} {pσ mσ : Sym}
    {s s' t t' : MState} {k27 : Bool} (hR : ObjRel f s t) (h27 : k27 = true → t.x 27 = s.x 27)
    (hse : sameEffectK k27 mσ pσ = .ok ())
    (hm : HoldsCore ⟨t, sym⟩ mσ t') (hp : HoldsCore ⟨s, sym⟩ pσ s') :
    (∀ k : Reg, k ≠ 27 → k ≠ 30 → t'.x k = s'.x k) ∧ t'.sp = s'.sp ∧ t'.v = s'.v ∧
      t'.nzcv = s'.nzcv ∧ t'.mem = s'.mem := by
  obtain ⟨hregs, -, -, hsp, hfl, hst, -, hrt, -, hvs⟩ := sameEffect_spec hse
  obtain ⟨hxok, hspok, hflok, -, hstok, hvok⟩ := readsTmp_false hrt
  refine ⟨fun k h27' h30 => ?_, ?_, ?_, ?_, ?_⟩
  · have hk : k = BitVec.ofNat 5 k.toNat := by simp
    have hlt := k.isLt
    by_cases h31 : k.toNat = 31
    · have : k = 31 := by rw [hk, h31]; rfl
      subst this
      rw [hm.x31, hp.x31]
      exact hR.x 31 (by decide) (by decide)
    · have h30' : k.toNat ≠ 30 := fun h => h30 (by rw [hk, h]; rfl)
      have h27'' : k.toNat ≠ 27 := fun h => h27' (by rw [hk, h]; rfl)
      have hmem : k.toNat ∈ cmpRegs := mem_cmpRegs.2 ⟨by omega, h27'', h30'⟩
      rw [hk, hm.x k.toNat (by omega), hp.x k.toNat (by omega), hregs _ hmem]
      exact eval_rel hR h27 sym (hxok _ hmem)
  · rw [hm.sp, hp.sp, hsp]
    exact eval_rel hR h27 sym hspok
  · funext k
    rw [hm.v, hp.v, Sym.evalV_getV, Sym.evalV_getV, hvs _ k.isLt]
    exact vex_eval_rel hR h27 sym (hvok _)
  · rw [hm.nzcv, hp.nzcv, hfl]
    exact fl_eval_rel hR h27 sym hflok
  · rw [hm.mem, hp.mem, hst]
    dsimp only
    rw [hR.mem]
    exact storesMem_rel hR h27 sym _ _ hstok

/-- A PC at a Prog or at the end. -/
private theorem inv_of {L : Link} {ps : List Prog} {s' : MState} {a : BitVec 64}
    (h : s'.pc = a) (hi : IsProgAddr L.text ps a ∨ a = endP L.text ps) :
    ObjInv L ps s' ∨ s'.pc = endP L.text ps := by
  subst h
  rcases hi with h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inr h

/-- A PC that goes to `tgt` or `next`. -/
private theorem obj_pc_ite {L : Link} {ps : List Prog} {f : BitVec 64 → BitVec 64}
    {s' t' : MState} {c c' : Prop} [Decidable c] [Decidable c'] {tgt next qa na : BitVec 64}
    (hs : s'.pc = if c then tgt else next) (ht : t'.pc = if c' then qa else na) (hcc : c' ↔ c)
    (htg : f tgt = qa ∧ IsProgAddr L.text ps tgt) (hfn : f next = na)
    (hinvn : IsProgAddr L.text ps next ∨ next = endP L.text ps) :
    t'.pc = f s'.pc ∧ (ObjInv L ps s' ∨ s'.pc = endP L.text ps) := by
  by_cases hc : c
  · have h1 : s'.pc = tgt := by rw [hs]; simp [hc]
    have h2 : t'.pc = qa := by rw [ht]; simp [hcc.2 hc]
    exact ⟨by rw [h2, h1, htg.1], inv_of h1 (Or.inl htg.2)⟩
  · have h1 : s'.pc = next := by rw [hs]; simp [hc]
    have h2 : t'.pc = na := by rw [ht]; simp [show ¬c' from fun h => hc (hcc.1 h)]
    exact ⟨by rw [h2, h1, hfn], inv_of h1 hinvn⟩

/-- The control after the words and after the Prog agree (`CtlMatch`). -/
private theorem obj_ctl {L : Link} {ps : List Prog} {f : BitVec 64 → BitVec 64}
    {offs : List (Nat × Nat)} {base next : BitVec 64} {p : Prog} {pσ mσ : Sym} {pc : PCtl}
    {mc : MCtl} {ol : Nat} {s s' t t' : MState} {k27 : Bool}
    (hR : ObjRel f s t) (h27 : k27 = true → t.x 27 = s.x 27) (hcm : CtlMatch k27 offs pσ mc pc)
    (hpp : PcP L p pσ s pc s')
    (hmp : CtlPc ⟨t, L.sym⟩ base ol mc t')
    (hx30 : mc.links = false → t'.x 30 = (mσ.getX 30).eval ⟨t, L.sym⟩)
    (h30m : mσ.getX 30 = .x 30) (h30p : pσ.getX 30 = .x 30)
    (hnext : L.nextAddr p.id = some next) (hfn : f next = at_ base (ol + 4))
    (hinvn : IsProgAddr L.text ps next ∨ next = endP L.text ps)
    (htgt : ∀ id q a, TgtOK offs id q → L.addr id = some a →
      f a = at_ base q ∧ IsProgAddr L.text ps a)
    (hsym : ∀ y, f (L.sym y) = L.sym y)
    (hic : isICall p = true → ∃ y, s'.pc = L.sym y) :
    t'.x 30 = f (s'.x 30) ∧ t'.pc = f s'.pc ∧ (ObjInv L ps s' ∨ s'.pc = endP L.text ps) := by
  have keep : mc.links = false → s'.x 30 = (pσ.getX 30).eval ⟨s, L.sym⟩ →
      t'.x 30 = f (s'.x 30) := by
    intro hne hs30
    rw [hx30 hne, h30m, hs30, h30p]
    exact hR.x30
  cases mc <;> cases pc <;> simp only [CtlMatch] at hcm
  case fall.fall =>
    simp only [PcP] at hpp
    simp only [CtlPc] at hmp
    obtain ⟨h1, h2⟩ := hpp
    rw [hnext, Option.some.injEq] at h1
    refine ⟨keep rfl h2, by rw [hmp, ← h1, hfn], inv_of h1.symm hinvn⟩
  case jmp.jmp q id =>
    simp only [PcP] at hpp
    simp only [CtlPc] at hmp
    obtain ⟨h1, h2⟩ := hpp
    obtain ⟨ha, hpa⟩ := htgt _ _ _ hcm h1
    exact ⟨keep rfl h2, by rw [hmp, ha], Or.inl (Or.inl hpa)⟩
  case cond.cond fl c q c' id =>
    obtain ⟨rfl, rfl, hT⟩ := hcm
    simp only [PcP] at hpp
    simp only [CtlPc, Fl.eval] at hmp
    obtain ⟨⟨next', tgt, h1, h2, h3⟩, h4⟩ := hpp
    rw [hnext, Option.some.injEq] at h1
    subst h1
    exact ⟨keep rfl h4,
      obj_pc_ite h3 hmp (Iff.of_eq (congrArg (fun z => (condOf c).holds z = true) hR.nzcv))
        (htgt _ _ _ hT h2) hfn hinvn⟩
  case cbz.cbz sf nz a q sf' nz' a' id =>
    obtain ⟨rfl, rfl, rfl, hok, hT⟩ := hcm
    simp only [PcP] at hpp
    simp only [CtlPc] at hmp
    obtain ⟨⟨next', tgt, h1, h2, h3⟩, h4⟩ := hpp
    rw [hnext, Option.some.injEq] at h1
    subst h1
    exact ⟨keep rfl h4,
      obj_pc_ite h3 hmp (by rw [eval_rel hR h27 L.sym hok]) (htgt _ _ _ hT h2) hfn hinvn⟩
  case tbz.tbz nz b a q nz' b' a' id =>
    obtain ⟨rfl, rfl, rfl, hok, hT⟩ := hcm
    simp only [PcP] at hpp
    simp only [CtlPc] at hmp
    obtain ⟨⟨next', tgt, h1, h2, h3⟩, h4⟩ := hpp
    rw [hnext, Option.some.injEq] at h1
    subst h1
    exact ⟨keep rfl h4,
      obj_pc_ite h3 hmp (by rw [eval_rel hR h27 L.sym hok]) (htgt _ _ _ hT h2) hfn hinvn⟩
  case call.call n add n' add' =>
    obtain ⟨rfl, rfl, rfl⟩ := hcm
    simp only [PcP] at hpp
    simp only [CtlPc] at hmp
    obtain ⟨h1, h2⟩ := hpp
    obtain ⟨h3, h4⟩ := hmp
    rw [hnext, Option.some.injEq] at h2
    have h0 : ∀ x : BitVec 64, x + BitVec.ofInt 64 0 = x := fun x => by simp
    rw [h0] at h1 h3
    refine ⟨by rw [h4, ← h2, hfn], by rw [h3, h1, hsym], Or.inl (Or.inr ⟨⟨n, h1⟩, ?_⟩)⟩
    rw [← h2]
    exact hinvn
  case callReg.callReg a a' =>
    obtain ⟨rfl, hok⟩ := hcm
    simp only [PcP] at hpp
    simp only [CtlPc] at hmp
    obtain ⟨h1, h2, hi⟩ := hpp
    obtain ⟨h3, h4⟩ := hmp
    obtain ⟨y, hy⟩ := hic hi
    rw [hnext, Option.some.injEq] at h2
    refine ⟨by rw [h4, ← h2, hfn], by rw [h3, eval_rel hR h27 L.sym hok, ← h1, hy, hsym],
      Or.inl (Or.inr ⟨⟨y, hy⟩, ?_⟩)⟩
    rw [← h2]
    exact hinvn

/-- A skip: no machine step. -/
private theorem obj_skip {L : Link} {ps : List Prog} {f : BitVec 64 → BitVec 64} {H : Hooks}
    {code : Code} {retM : BitVec 64} {p : Prog} {s s' t : MState} {next : BitVec 64}
    (hsk : p.isSkip = true) (hs : progStep L p s = .ok s') (hnext : L.nextAddr p.id = some next)
    (hR : ObjRel f s t) (hpc : t.pc = f next)
    (hinvn : IsProgAddr L.text ps next ∨ next = endP L.text ps) :
    ∃ t', MStar H code retM t t' ∧ ObjRel f s' t' ∧ (ObjInv L ps s' ∨ s'.pc = endP L.text ps) ∧
      s'.pc = next := by
  have : s' = { s with pc := next } := by
    simp only [progStep, hnext, hsk, ↓reduceIte, Except.ok.injEq] at hs
    exact hs.symm
  subst this
  exact ⟨t, .refl, ⟨hR.x, hR.x30, hR.sp, hR.v, hR.nzcv, hR.mem, hpc⟩, inv_of rfl hinvn, rfl⟩

/-- A Prog with words: the words run as the Prog steps; `X27` agrees after them where the
words leave it as the Prog (`est27`). -/
private theorem obj_words {L : Link} {ps : List Prog} {f : BitVec 64 → BitVec 64}
    {t0 : ByteArray} {rs : List Reloc} {offs : List (Nat × Nat)} {az ez : Int}
    {base : BitVec 64} {code : Code} {retM : BitVec 64} {H : Hooks} {p : Prog} {o e : Nat}
    {next : BitVec 64} {pσ mσ : Sym} {pc : PCtl} {mc : MCtl} {s s' t : MState} {k27 : Bool}
    (hlink : linkCode base L.sym t0 rs = .ok code) (hsz : t0.size ≤ 2 ^ 64)
    (hret : code retM = none) (haz : L.autosize = az) (hez : L.extrasize = ez)
    (hskip : p.isSkip = false) (hoe : o < e) (h4 : (e - o) % 4 = 0)
    (hps : progSym az ez p = .ok (pσ, pc)) (hms : symWords t0 rs ((e - o) / 4) o {} = .ok (mσ, mc))
    (hse : sameEffectK k27 mσ pσ = .ok ()) (hsc : sameCtl k27 offs mc pc pσ = .ok ())
    (hs : progStep L p s = .ok s') (hR : ObjRel f s t) (h27 : k27 = true → t.x 27 = s.x 27)
    (htpc : t.pc = base + BitVec.ofNat 64 o)
    (hnext : L.nextAddr p.id = some next) (hfn : f next = base + BitVec.ofNat 64 e)
    (hinvn : IsProgAddr L.text ps next ∨ next = endP L.text ps)
    (htgt : ∀ id q a, TgtOK offs id q → L.addr id = some a →
      f a = at_ base q ∧ IsProgAddr L.text ps a)
    (hsym : ∀ y, f (L.sym y) = L.sym y) (hic : isICall p = true → ∃ y, s'.pc = L.sym y) :
    ∃ t', MStar H code retM t t' ∧ ObjRel f s' t' ∧ (ObjInv L ps s' ∨ s'.pc = endP L.text ps) ∧
      PcP L p pσ s pc s' ∧ (est27 k27 mσ pσ mc = true → t'.x 27 = s'.x 27) := by
  obtain ⟨n, hn⟩ : ∃ n, (e - o) / 4 = n + 1 := ⟨(e - o) / 4 - 1, by omega⟩
  rw [hn] at hms
  obtain ⟨hnil, hcore, hpp⟩ := progSym_sound hps haz hez hskip hs
  obtain ⟨t', hst, hcore', hx30, hctl⟩ := symWords_sound (H := H) hlink hsz hret n o {} mσ mc
    ⟨t, L.sym⟩ t hms rfl (holds_init _) htpc (noNil_rel hR h27 hse hnil)
  obtain ⟨hx, hsp, hv, hfl, hmem⟩ := obj_core hR h27 hse hcore' hcore
  obtain ⟨-, h30m, h30p, -⟩ := sameEffect_spec hse
  have hfn' : f next = at_ base ((o + 4 * n : Nat) + 4) := by
    rw [hfn, at_nat]
    congr 1
    omega
  obtain ⟨h30, hpc, hinv⟩ := obj_ctl hR h27 (sameCtl_spec hsc) hpp hctl hx30 h30m h30p hnext
    hfn' hinvn htgt hsym hic
  refine ⟨t', hst, ⟨hx, h30, hsp, hv, hfl, hmem, hpc⟩, hinv, hpp, fun he => ?_⟩
  simp only [est27, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at he
  obtain ⟨⟨-, hme⟩, hok⟩ := he
  show t'.x (BitVec.ofNat 5 27) = s'.x (BitVec.ofNat 5 27)
  rw [hcore'.x 27 (by decide), hcore.x 27 (by decide), hme]
  exact eval_rel hR h27 L.sym hok

/-- A non-skip Prog whose effect has no meaning neither steps nor faults in the nil page. -/
private theorem progStep_err {L : Link} {p : Prog} {s : MState} {msg : String}
    (hsk : p.isSkip = false) (he : progEffect ⟨L, s, p⟩ = .error msg) :
    (∀ s', progStep L p s ≠ .ok s') ∧ ∀ a, progStep L p s ≠ .error (.nilPage a) := by
  refine ⟨fun s' => ?_, fun a => ?_⟩ <;> unfold progStep <;> split
  · simp
  · simp [hsk, he]
  · simp
  · simp [hsk, he]

/-- P0's `RET` has no `progEffect` (its meaning is the epilogue's). -/
private theorem ret0_effect {L : Link} {p : Prog} {s : MState} (h : isRet0 p = true) :
    p.isSkip = false ∧ progEffect ⟨L, s, p⟩ = .error "P0 RET: the epilogue's (machine level)" := by
  simp only [isRet0, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨has, hto⟩ := h
  have hname : As.name .RET = "RET" := rfl
  refine ⟨by simp [Prog.isSkip, has], ?_⟩
  unfold progEffect
  simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
    ProgOp.movMem, ProgOp.pairOp, ProgOp.rmw, ProgOp.bcond, ProgOp.startsS, hto]
  rfl

/-- An `END` placeholder has no `progEffect`. -/
private theorem end_effect {L : Link} {p : Prog} {s : MState} (has : p.as = .END) :
    p.isSkip = false ∧ progEffect ⟨L, s, p⟩ = .error "opcode not specified" := by
  have hname : As.name .END = "END" := rfl
  refine ⟨by simp [Prog.isSkip, has], ?_⟩
  unfold progEffect
  simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
    ProgOp.movMem, ProgOp.pairOp, ProgOp.rmw, ProgOp.bcond, ProgOp.startsS]
  rfl

/-- P0's `RET` does not step (its meaning is the epilogue's). -/
private theorem progStep_ret0 {L : Link} {p : Prog} {s s' : MState} (h : isRet0 p = true) :
    progStep L p s ≠ .ok s' :=
  (progStep_err (ret0_effect (L := L) (s := s) h).1 (ret0_effect h).2).1 s'

/-- An `END` placeholder does not step. -/
private theorem progStep_end {L : Link} {p : Prog} {s s' : MState} (has : p.as = .END) :
    progStep L p s ≠ .ok s' :=
  (progStep_err (end_effect (L := L) (s := s) has).1 (end_effect has).2).1 s'

private theorem progAt?_mem {sym : Nat → BitVec 64} {text : BitVec 64} {a x : Int}
    {ps : List Prog} {pc : BitVec 64} {p : Prog}
    (h : progAt? (Link.byId sym text a x ps) ps pc = some p) :
    p ∈ ps ∧ pc = addrP text p.id := by
  unfold progAt? at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  rw [GoFV.Proof.Gen.addr_byId hm] at hp
  exact ⟨hm, (Option.some.inj hp.1).symm⟩

private theorem progAt?_some {sym : Nat → BitVec 64} {text : BitVec 64} {a x : Int}
    {ps : List Prog} (hnd : (ps.map (·.id)).Nodup) (hlt : ∀ p ∈ ps, p.id < 2 ^ 32)
    {pc : BitVec 64}
    (h : IsProgAddr text ps pc) : ∃ p, progAt? (Link.byId sym text a x ps) ps pc = some p := by
  obtain ⟨p, hp, rfl⟩ := h
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
  exact ⟨_, GoFV.Proof.Gen.progAt?_byId hnd hlt hj⟩

/-- The fall-through of the Prog at index `k` and its image. -/
private theorem next_map {sym : Nat → BitVec 64} {text base : BitVec 64} {a x : Int}
    {ps : List Prog} {offs : List Nat} {e : Nat} (hnd : (ps.map (·.id)).Nodup)
    (hlt : ∀ p ∈ ps, p.id < 2 ^ 32)
    (hlen : offs.length = ps.length) {k : Nat} (hk : k < ps.length) :
    ∃ next, (Link.byId sym text a x ps).nextAddr ps[k].id = some next ∧
      objMap ps offs e text base next = base + BitVec.ofNat 64 (offs.getD (k + 1) e) ∧
      (IsProgAddr text ps next ∨ next = endP text ps) := by
  refine ⟨_, GoFV.Proof.Gen.nextAddr_byId hnd hk, ?_⟩
  split
  · rename_i h1
    refine ⟨?_, Or.inl ⟨ps[k + 1], List.getElem_mem h1, rfl⟩⟩
    rw [show text + BitVec.ofNat 64 (4 * ps[k + 1].id) = addrP text ps[k + 1].id from rfl,
      objMap_at hnd hlt hlen h1, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
  · rename_i h1
    refine ⟨?_, Or.inr rfl⟩
    rw [show text + BitVec.ofNat 64 (4 * (maxId ps + 1)) = endP text ps from rfl,
      objMap_end hlt, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega),
      Option.getD_none]

/-- The ID ↦ offset table `checkObj` checked branches against. -/
abbrev offsTab (ps : Array Prog) (tab : Tab) : List (Nat × Nat) :=
  (ps.toList.zip tab.offs.toList).map fun (p, s) => (p.id, s)

/-- `Tab.ok27`: one entry per Prog; `false` at the `TEXT` and the first body Prog; `checkBody`
checked the Prog at index `k ≥ 1` with its entry, and the next Prog's entry is what the Prog
returned (`X27` related after it) unless a Prog branches to it. -/
theorem ok27_spec {ps : Array Prog} {spills : Array Spill} {o : ObjIn} {tab : Tab}
    (h : checkObj ps spills o = .ok tab) :
    tab.ok27.size = ps.size ∧ tab.ok27[0]? = some false ∧
    tab.ok27[1]? = ps.toList[1]?.map (fun q => false && !(branchTargets ps.toList).contains q.id) ∧
    ∀ k (hk1 : 1 ≤ k) (hk : k < ps.toList.length) (hk' : k < tab.offs.toList.length), ∃ b,
      checkOne o.text o.relocs.toList (offsTab ps tab) tab.autosize tab.extrasize tab.leaf
        (tab.ok27[k]?.getD false) ps.toList[k] tab.offs.toList[k]
        (tab.offs.toList.getD (k + 1) tab.endOff) = .ok b ∧
      tab.ok27[k + 1]? = ps.toList[k + 1]?.map
        (fun q => b && !(branchTargets ps.toList).contains q.id) := by
  obtain ⟨-, -, -, -, -, -, hsz, hofs, -, -, -, -, -, ks, hbody, hok⟩ := checkObj_spec h
  have hlen : (tab.offs.toList.drop 1).length = (ps.toList.drop 1).length := by simp [hofs]
  obtain ⟨hks, h0, hall⟩ := checkBody_spec false _ _ _ ks hbody hlen
  rw [hok]
  refine ⟨by simp at hks ⊢; omega, rfl, by simpa using h0, fun k hk1 hk hk' => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨b, h1, h2⟩ := hall j (by rw [List.length_drop]; omega)
  refine ⟨b, ?_, ?_⟩
  · simpa [List.getElem_drop, Nat.add_comm, List.getD_eq_getElem?_getD] using h1
  · rw [List.getElem?_toArray, List.getElem?_cons_succ, h2, List.getElem?_drop, Nat.add_comm 1]

/-- `ok27` holds only at a Prog no Prog branches to. -/
theorem ok27_tgt {ps : Array Prog} {spills : Array Spill} {o : ObjIn} {tab : Tab}
    (h : checkObj ps spills o = .ok tab) {j : Nat} (hj : tab.ok27[j]? = some true) :
    ∃ hj' : j < ps.toList.length, ps.toList[j].id ∉ branchTargets ps.toList := by
  obtain ⟨hsz, h0, h1, hall⟩ := ok27_spec h
  obtain ⟨-, -, -, -, -, -, -, hofs, -⟩ := checkObj_spec h
  have hjl : j < ps.size := by
    rw [← hsz]
    exact (Array.getElem?_eq_some_iff.1 hj).1
  rcases j with _ | _ | k
  · rw [h0] at hj; cases hj
  · rw [h1] at hj
    simp at hj
  · obtain ⟨b, -, h2⟩ := hall (k + 1) (by omega) (by simp; omega) (by simp [hofs]; omega)
    rw [h2] at hj
    simp only [Option.map_eq_some_iff, List.getElem?_eq_some_iff, Bool.and_eq_true,
      Bool.not_eq_true'] at hj
    obtain ⟨q, ⟨hq, rfl⟩, -, hc⟩ := hj
    exact ⟨hq, by simpa using hc⟩

/-- Distinct indices of a validated list have distinct addresses. -/
private theorem addr_idx {text : BitVec 64} {ps : List Prog} (hnd : (ps.map (·.id)).Nodup)
    (hlt : ∀ p ∈ ps, p.id < 2 ^ 32) {i j : Nat} (hi : i < ps.length) (hj : j < ps.length)
    (h : addrP text ps[j].id = addrP text ps[i].id) : j = i := by
  have hi' := hlt _ (List.getElem_mem hi)
  have hj' := hlt _ (List.getElem_mem hj)
  by_cases hne : j = i
  · exact hne
  · exact absurd (GoFV.Proof.Gen.addr_inj (by omega) (by omega) h)
      (GoFV.Proof.Gen.id_ne_of_nodup hnd hj hi hne)

/-- `ok27` at the fall-through of the Prog at index `k` needs what the Prog returned. -/
private theorem ok27_next {ps : List Prog} {L : Link} {tab : Tab} {a x : Int}
    (hlink : L = Link.byId L.sym L.text a x ps) (hnd : (ps.map (·.id)).Nodup)
    (hlt : ∀ p ∈ ps, p.id < 2 ^ 32) {k : Nat} (hk : k < ps.length) {b : Bool} {tg : List Nat}
    (hok : tab.ok27[k + 1]? = ps[k + 1]?.map (fun q => b && !tg.contains q.id))
    {next : BitVec 64} (hnext : L.nextAddr ps[k].id = some next) {j : Nat} (hj : j < ps.length)
    (hpc : addrP L.text ps[j].id = next) (h27 : tab.ok27[j]? = some true) : b = true := by
  rw [hlink, GoFV.Proof.Gen.nextAddr_byId hnd hk, Option.some_inj] at hnext
  by_cases h1 : k + 1 < ps.length
  · simp only [h1, ↓reduceDIte] at hnext
    have := addr_idx (text := L.text) hnd hlt h1 hj (hpc.trans hnext.symm)
    subst this
    rw [hok, List.getElem?_eq_getElem h1] at h27
    simp only [Option.map_some, Option.some.injEq, Bool.and_eq_true] at h27
    exact h27.1
  · simp only [h1, ↓reduceDIte] at hnext
    exact absurd ⟨ps[j], List.getElem_mem hj, hpc.trans hnext.symm⟩ (not_isProgAddr_end hlt)

/-- `X27At` after the Prog at index `k`, whose step went to its fall-through, to a Prog some Prog
branches to, or (`b = false`: a call) to a symbol with the fall-through in `X30`. -/
private theorem x27_after {ps : Array Prog} {spills : Array Spill} {o : ObjIn} {tab : Tab}
    {L : Link} {base : BitVec 64} {code : Code} {retM : BitVec 64}
    (hE : ObjEnv ps spills o tab L base code retM) {k : Nat} (hk : k < ps.toList.length)
    {b : Bool} (hok : tab.ok27[k + 1]? = ps.toList[k + 1]?.map
      (fun q => b && !(branchTargets ps.toList).contains q.id))
    {next : BitVec 64} (hnext : L.nextAddr ps.toList[k].id = some next)
    (hinvn : IsProgAddr L.text ps.toList next ∨ next = endP L.text ps.toList) {s' t' : MState}
    (hd : s'.pc = next ∨
      (∃ j, ∃ hj : j < ps.toList.length, ps.toList[j].id ∈ branchTargets ps.toList ∧
        s'.pc = addrP L.text ps.toList[j].id) ∨
      (b = false ∧ (∃ y, s'.pc = L.sym y) ∧ s'.x 30 = next))
    (h27 : b = true → t'.x 27 = s'.x 27) : X27At tab L ps.toList s' t' := by
  obtain ⟨-, -, -, -, hnd, hlt, -⟩ := checkObj_spec hE.check
  have hnx : ∀ j (hj : j < ps.toList.length), addrP L.text ps.toList[j].id = next →
      tab.ok27[j]? = some true → b = true := fun j hj hpc h =>
    ok27_next hE.link hnd hlt hk hok hnext hj hpc h
  have hnsym : ∀ y, L.sym y ≠ next := fun y h => by
    rcases hinvn with hp | he
    · exact (hE.syms y).2.2.1 (h ▸ hp)
    · exact (hE.syms y).2.2.2 (h.trans he)
  refine ⟨fun j hj hpc h => ?_, fun ⟨y, hy⟩ j hj hpc h => ?_⟩
  · rcases hd with hd | ⟨i, hi, hti, hd⟩ | ⟨-, ⟨y, hy⟩, -⟩
    · exact h27 (hnx j hj (hpc.trans hd) h)
    · rw [hd] at hpc
      have := addr_idx hnd hlt hi hj hpc
      subst this
      exact absurd hti (ok27_tgt hE.check h).2
    · exact absurd ⟨ps.toList[j], List.getElem_mem hj, hpc.trans hy⟩ (hE.syms y).2.2.1
  · rcases hd with hd | ⟨i, hi, -, hd⟩ | ⟨hb, -, h30⟩
    · exact hnsym y (hy.symm.trans hd)
    · exact (hE.syms y).2.2.1 ⟨ps.toList[i], List.getElem_mem hi, (hy.symm.trans hd).symm⟩
    · rw [hnx j hj (hpc.trans h30) h] at hb
      cases hb

/-- A branch control's target is the Prog of the operand `To` (`ctlOp`). -/
private theorem ctlOp_br {p : Prog} {id : Nat} {c : PCtl} (h : ctlOp p c = .ok ())
    (hc : c = .jmp id ∨ (∃ cc, c = .cond cc id) ∨ (∃ sf nz a, c = .cbz sf nz a id) ∨
      (∃ nz b a, c = .tbz nz b a id)) : branchTo p = some id := by
  rcases hc with rfl | ⟨cc, rfl⟩ | ⟨sf, nz, a, rfl⟩ | ⟨nz, b, a, rfl⟩ <;>
  · simp only [ctlOp] at h
    split at h
    · rename_i hb
      simpa using hb
    · cases h

private theorem ite_cases {α : Type} {c : Prop} [Decidable c] {x a b : α}
    (h : x = if c then a else b) : x = a ∨ x = b := by
  split at h
  · exact .inl h
  · exact .inr h

/-- Where the words of the Prog at index `k` went (`x27_after`'s cases). -/
private theorem dest_words {ps : Array Prog} {spills : Array Spill} {o : ObjIn} {tab : Tab}
    {L : Link} {base : BitVec 64} {code : Code} {retM : BitVec 64}
    (hE : ObjEnv ps spills o tab L base code retM) {k : Nat} (hk : k < ps.toList.length)
    {pσ mσ : Sym} {pc : PCtl} {mc : MCtl} {kk : Bool} {s s' : MState} {next : BitVec 64}
    (hcm : CtlMatch kk (offsTab ps tab) pσ mc pc) (hpp : PcP L ps.toList[k] pσ s pc s')
    (hct : ctlOp ps.toList[k] pc = .ok ()) (hnext : L.nextAddr ps.toList[k].id = some next)
    (hic : isICall ps.toList[k] = true → ∃ y, s'.pc = L.sym y) :
    s'.pc = next ∨
      (∃ j, ∃ hj : j < ps.toList.length, ps.toList[j].id ∈ branchTargets ps.toList ∧
        s'.pc = addrP L.text ps.toList[j].id) ∨
      (est27 kk mσ pσ mc = false ∧ (∃ y, s'.pc = L.sym y) ∧ s'.x 30 = next) := by
  obtain ⟨-, -, -, -, -, -, -, hofs, -⟩ := checkObj_spec hE.check
  have hlen : tab.offs.toList.length = ps.toList.length := by simp [hofs]
  have hbr : ∀ id q a, TgtOK (offsTab ps tab) id q → L.addr id = some a →
      branchTo ps.toList[k] = some id →
      ∃ j, ∃ hj : j < ps.toList.length, ps.toList[j].id ∈ branchTargets ps.toList ∧
        a = addrP L.text ps.toList[j].id := by
    rintro id q a ⟨o', ho, -⟩ ha hb
    obtain ⟨j, hj, rfl, -⟩ := offOf_zip hlen ho
    rw [hE.link, GoFV.Proof.Gen.addr_byId (List.getElem_mem hj), Option.some_inj] at ha
    exact ⟨j, hj, List.mem_filterMap.2 ⟨_, List.getElem_mem hk, hb⟩, ha.symm⟩
  have hnx : ∀ {a}, L.nextAddr ps.toList[k].id = some a → a = next := fun h =>
    Option.some.inj (h.symm.trans hnext)
  cases mc <;> cases pc <;> simp only [CtlMatch] at hcm
  case fall.fall => exact .inl (hnx hpp.1)
  case jmp.jmp q id => exact .inr (.inl (hbr _ _ _ hcm hpp.1 (ctlOp_br hct (.inl rfl))))
  case cond.cond fl c q c' id =>
    obtain ⟨-, -, hT⟩ := hcm
    obtain ⟨⟨next', tgt, h1, h2, h3⟩, -⟩ := hpp
    rcases ite_cases h3 with h | h
    · obtain ⟨j, hj, hm, ha⟩ := hbr _ _ _ hT h2 (ctlOp_br hct (.inr (.inl ⟨_, rfl⟩)))
      exact .inr (.inl ⟨j, hj, hm, h.trans ha⟩)
    · exact .inl (h.trans (hnx h1))
  case cbz.cbz sf nz a q sf' nz' a' id =>
    obtain ⟨-, -, -, -, hT⟩ := hcm
    obtain ⟨⟨next', tgt, h1, h2, h3⟩, -⟩ := hpp
    rcases ite_cases h3 with h | h
    · obtain ⟨j, hj, hm, ha⟩ := hbr _ _ _ hT h2 (ctlOp_br hct (.inr (.inr (.inl ⟨_, _, _, rfl⟩))))
      exact .inr (.inl ⟨j, hj, hm, h.trans ha⟩)
    · exact .inl (h.trans (hnx h1))
  case tbz.tbz nz b a q nz' b' a' id =>
    obtain ⟨-, -, -, -, hT⟩ := hcm
    obtain ⟨⟨next', tgt, h1, h2, h3⟩, -⟩ := hpp
    rcases ite_cases h3 with h | h
    · obtain ⟨j, hj, hm, ha⟩ := hbr _ _ _ hT h2 (ctlOp_br hct (.inr (.inr (.inr ⟨_, _, _, rfl⟩))))
      exact .inr (.inl ⟨j, hj, hm, h.trans ha⟩)
    · exact .inl (h.trans (hnx h1))
  case call.call n add n' add' =>
    obtain ⟨rfl, rfl, rfl⟩ := hcm
    obtain ⟨h1, h2⟩ := hpp
    exact .inr (.inr ⟨by simp [est27, MCtl.links], ⟨n, by simpa using h1⟩, hnx h2⟩)
  case callReg.callReg a a' =>
    obtain ⟨-, h2, hi⟩ := hpp
    exact .inr (.inr ⟨by simp [est27, MCtl.links], hic hi, hnx h2⟩)

theorem obj_step {ps : Array Prog} {spills : Array Spill} {o : ObjIn} {tab : Tab} {L : Link}
    {base : BitVec 64} {code : Code} {retM : BitVec 64} {H : Hooks} {s s' t : MState}
    (hE : ObjEnv ps spills o tab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map tab ps L base))
    (hs : PStep H L ps.toList (endP L.text ps.toList) s s')
    (hR : ObjRel (ObjEnv.map tab ps L base) s t) (hX : X27At tab L ps.toList s t)
    (hI : ObjInv L ps.toList s) (hO : ICallOut L ps.toList s) :
    ∃ t', MStar H code retM t t' ∧ ObjRel (ObjEnv.map tab ps L base) s' t' ∧
      (ObjInv L ps.toList s' ∨ s'.pc = endP L.text ps.toList) ∧ X27At tab L ps.toList s' t' := by
  obtain ⟨text0, body, h0, hT, hnd, hlt, hsz2, hofs, hb0, hb1, -, -, -, -⟩ :=
    checkObj_spec hE.check
  obtain ⟨-, -, hok1, hokk⟩ := ok27_spec hE.check
  have hlink := hE.link
  have hlen : tab.offs.toList.length = ps.toList.length := by simp [hofs]
  have hsym : ∀ y, ObjEnv.map tab ps L base (L.sym y) = L.sym y := fun y =>
    objMap_fix (hE.syms y).2.2.1 (hE.syms y).2.2.2
  cases hs with
  | hook hpc hnone hcall =>
    rcases hI with hpa | ⟨⟨y, hy⟩, h30⟩
    · exfalso
      rw [hlink] at hnone
      obtain ⟨p, hp⟩ := progAt?_some hnd hlt hpa
      rw [hp] at hnone
      cases hnone
    · obtain ⟨t', hcall', hR', hpc'⟩ := hH s t s' hR ⟨y, hy⟩ h30 hcall
      have htpc : t.pc = L.sym y := by rw [hR.pc, hy, hsym]
      refine ⟨t', mstar_single (.hook ?_ ?_ hcall'), hR', inv_of hpc' h30,
        fun j hj hpa h => absurd h (hX.ret27 ⟨y, hy⟩ j hj (hpa.trans hpc')),
        fun ⟨y', hy'⟩ _ _ _ _ => ?_⟩
      · rw [htpc]; exact (hE.syms y).2.1
      · rw [htpc]; exact (hE.syms y).1
      · rw [hpc'] at hy'
        rcases h30 with h | h
        · exact (hE.syms y').2.2.1 (hy' ▸ h)
        · exact (hE.syms y').2.2.2 (hy'.symm.trans h)
  | prog hpc hp hstep =>
    rename_i p
    have hp0 := hp
    rw [hlink] at hp
    obtain ⟨hmem, hspc⟩ := progAt?_mem hp
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hmem
    have htpc : t.pc = base + BitVec.ofNat 64 (tab.offs.toList[k]'(by omega)) := by
      rw [hR.pc, hspc]
      exact objMap_at hnd hlt hlen hk
    obtain ⟨next, hnext, hfn, hinvn⟩ := next_map (sym := L.sym) (text := L.text) (base := base)
      (a := tab.autosize) (x := tab.extrasize) (e := tab.endOff) hnd hlt hlen hk
    rw [← hlink] at hnext
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · -- `TEXT`: a skip to the body's start
      have hp0 : ps.toList[0] = text0 := by
        rw [Array.getElem?_eq_some_iff] at h0
        obtain ⟨_, h0⟩ := h0
        simpa using h0
      have hsk : ps.toList[0].isSkip = true := by rw [hp0]; simp [Prog.isSkip, hT]
      have hoff0 : tab.offs.toList[0]'(by omega) = body := by
        rw [Array.getElem?_eq_some_iff] at hb0
        obtain ⟨_, hb0⟩ := hb0
        simpa using hb0
      have hoff1 : tab.offs.toList.getD 1 tab.endOff = body := by
        rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, hb1]
        rfl
      obtain ⟨t', h1, h2, h3, h4⟩ := obj_skip (ps := ps.toList) hsk hstep hnext hR
        (by rw [htpc, hoff0]; exact (hoff1 ▸ hfn).symm) hinvn
      exact ⟨t', h1, h2, h3, x27_after hE hk hok1 hnext hinvn (.inl h4) fun h => by cases h⟩
    · have h27 := x27_here hX hk hspc
      obtain ⟨b, hone, hok⟩ := hokk k hk1 hk (by omega)
      rcases checkOne_spec hone with ⟨hret0, -⟩ | ⟨-, hcp⟩
      · exact absurd hstep (progStep_ret0 hret0)
      rcases checkProg_spec hcp with ⟨hsk | hend, hoe, rfl⟩ |
          ⟨hsk, -, hoe, h4, pσ, pc, mσ, mc, hps, hms, hse, hsc, rfl⟩
      · obtain ⟨t', h1, h2, h3, h4⟩ := obj_skip (ps := ps.toList) hsk hstep hnext hR
          (by rw [htpc, hoe]; exact hfn.symm) hinvn
        exact ⟨t', h1, h2, h3, x27_after hE hk hok hnext hinvn (.inl h4) fun h => by cases h⟩
      · exact absurd hstep (progStep_end hend)
      · have hic : isICall ps.toList[k] = true → ∃ y, s'.pc = L.sym y := fun hi =>
          hO _ _ hp0 hi hstep
        obtain ⟨t', h1, h2, h3, hpp, h5⟩ := obj_words hE.linked hE.size hE.ret
          (by rw [hlink]; rfl) (by rw [hlink]; rfl) hsk hoe h4 hps hms hse hsc hstep hR h27 htpc
          hnext hfn hinvn (by
            rintro id q a ⟨o', ho, rfl⟩ ha
            obtain ⟨j, hj, rfl, rfl⟩ := offOf_zip hlen ho
            rw [hlink, GoFV.Proof.Gen.addr_byId (List.getElem_mem hj), Option.some_inj] at ha
            subst ha
            exact ⟨by rw [← at_nat]; exact objMap_at hnd hlt hlen hj, ⟨_, List.getElem_mem hj, rfl⟩⟩)
          hsym hic
        exact ⟨t', h1, h2, h3, x27_after hE hk hok hnext hinvn
          (dest_words hE hk (sameCtl_spec hsc) hpp (progSym_core hps).2 hnext hic) h5⟩

theorem obj_star {ps : Array Prog} {spills : Array Spill} {o : ObjIn} {tab : Tab} {L : Link}
    {base : BitVec 64} {code : Code} {retM : BitVec 64} {H : Hooks} {s s' t : MState}
    (hE : ObjEnv ps spills o tab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map tab ps L base))
    (hs : PStar H L ps.toList (endP L.text ps.toList) s s')
    (hR : ObjRel (ObjEnv.map tab ps L base) s t) (hX : X27At tab L ps.toList s t)
    (hI : ObjInv L ps.toList s ∨ s.pc = endP L.text ps.toList)
    (hO : ∀ u, PStar H L ps.toList (endP L.text ps.toList) s u → ICallOut L ps.toList u) :
    ∃ t', MStar H code retM t t' ∧ ObjRel (ObjEnv.map tab ps L base) s' t' ∧
      (ObjInv L ps.toList s' ∨ s'.pc = endP L.text ps.toList) ∧ X27At tab L ps.toList s' t' := by
  induction hs with
  | refl => exact ⟨t, .refl, hR, hI, hX⟩
  | tail hpre hst ih =>
    obtain ⟨t1, h1, hR1, hI1, hX1⟩ := ih
    have hpc : _ := match hst with
      | .prog h _ _ => h
      | .hook h _ _ => h
    have hI1' : ObjInv L ps.toList _ := hI1.resolve_right hpc
    obtain ⟨t2, h2, hR2, hI2, hX2⟩ := obj_step hE hH hst hR1 hX1 hI1' (hO _ hpre)
    exact ⟨t2, mstar_trans h1 h2, hR2, hI2, hX2⟩

/-! ## Leaves keep `X30` -/

/-- A Prog of a leaf (`leafOf`: no `CALL`) keeps `X30` from a state at a Prog: the `TEXT` and the
skips do not touch it, `RET` does not step on P0, and a compared Prog's effect does not write it
(`sameEffect`) and its control is no call (`progSym_ctl`; a register jump is no `CtlMatch`). -/
theorem leaf_step_x30 {ps : Array Prog} {spills : Array Spill} {o : ObjIn} {tab : Tab}
    {L : Link} {base : BitVec 64} {code : Code} {retM : BitVec 64} {H : Hooks} {s s' : MState}
    (hE : ObjEnv ps spills o tab L base code retM) (hleaf : tab.leaf = true)
    (hs : PStep H L ps.toList (endP L.text ps.toList) s s')
    (hpa : IsProgAddr L.text ps.toList s.pc) : s'.x 30 = s.x 30 := by
  obtain ⟨text0, body, h0, hT, hnd, hlt, -, hofs, -, -, hlf, -, -, -⟩ := checkObj_spec hE.check
  obtain ⟨-, -, -, hokk⟩ := ok27_spec hE.check
  have hlink := hE.link
  have hlen : tab.offs.toList.length = ps.toList.length := by simp [hofs]
  have hskip : ∀ {p : Prog}, p.isSkip = true → progStep L p s = .ok s' → s'.x 30 = s.x 30 := by
    intro p hsk hst
    unfold progStep at hst
    cases hn : L.nextAddr p.id with
    | none => rw [hn] at hst; cases hst
    | some next =>
      simp only [hn, hsk, ↓reduceIte, Except.ok.injEq] at hst
      rw [← hst]
  cases hs with
  | hook hpc hnone hcall =>
    exfalso
    rw [hlink] at hnone
    obtain ⟨p, hp⟩ := progAt?_some hnd hlt hpa
    rw [hp] at hnone
    cases hnone
  | prog hpc hp hstep =>
    rename_i p
    rw [hlink] at hp
    obtain ⟨hmem, -⟩ := progAt?_mem hp
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hmem
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · have hp0 : ps.toList[0] = text0 := by
        rw [Array.getElem?_eq_some_iff] at h0
        obtain ⟨_, h0⟩ := h0
        simpa using h0
      exact hskip (by rw [hp0]; simp [Prog.isSkip, hT]) hstep
    · obtain ⟨b, hone, -⟩ := hokk k hk1 hk (by omega)
      rcases checkOne_spec hone with ⟨hret0, -⟩ | ⟨-, hcp⟩
      · exact absurd hstep (progStep_ret0 hret0)
      rcases checkProg_spec hcp with ⟨hsk | hend, -⟩ |
          ⟨hsk, -, -, -, pσ, pc, mσ, mc, hps, -, hse, hsc, -⟩
      · exact hskip hsk hstep
      · exact absurd hstep (progStep_end hend)
      · obtain ⟨-, -, hpp⟩ := progSym_sound hps (by rw [hlink]; rfl) (by rw [hlink]; rfl) hsk
          hstep
        obtain ⟨-, -, h30p, -⟩ := sameEffect_spec hse
        have hcm := sameCtl_spec hsc
        obtain ⟨hc1, hc2, -⟩ := progSym_ctl hps
        have hnc : ps.toList[k].as ≠ .CALL := by
          have hall := hlf ▸ hleaf
          simp only [leafOf, Array.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at hall
          simpa using (hall k (by simpa using hk)).1.1
        have h30 : (pσ.getX 30).eval ⟨s, L.sym⟩ = s.x 30 := by rw [h30p]; rfl
        cases pc with
        | fall => exact hpp.2.trans h30
        | jmp id => exact hpp.2.trans h30
        | cond cc id => exact hpp.2.trans h30
        | cbz sf nz a id => exact hpp.2.trans h30
        | tbz nz b a id => exact hpp.2.trans h30
        | reg a => cases mc <;> simp only [CtlMatch] at hcm
        | call n add => exact absurd (hc1 n add rfl) hnc
        | callReg a => exact absurd (hc2 a rfl) hnc

/-- **A leaf's P0 run keeps `X30`** when it starts at a Prog (or the end) with `X30` outside the
Progs and the end: then every state of the run is at a Prog (`ObjInv`, a symbol is only reached
with a P0 return address in `X30`), and `leaf_step_x30` steps it. -/
theorem obj_star_leaf {ps : Array Prog} {spills : Array Spill} {o : ObjIn} {tab : Tab} {L : Link}
    {base : BitVec 64} {code : Code} {retM : BitVec 64} {H : Hooks} {s s' t : MState}
    (hE : ObjEnv ps spills o tab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map tab ps L base))
    (hs : PStar H L ps.toList (endP L.text ps.toList) s s')
    (hR : ObjRel (ObjEnv.map tab ps L base) s t) (hX : X27At tab L ps.toList s t)
    (hI : ObjInv L ps.toList s ∨ s.pc = endP L.text ps.toList)
    (hO : ∀ u, PStar H L ps.toList (endP L.text ps.toList) s u → ICallOut L ps.toList u)
    (hleaf : tab.leaf = true)
    (hout : ¬ IsProgAddr L.text ps.toList (s.x 30) ∧ s.x 30 ≠ endP L.text ps.toList) :
    s'.x 30 = s.x 30 := by
  induction hs with
  | refl => rfl
  | tail hpre hst ih =>
    rename_i s1 s2
    have hpc : s1.pc ≠ endP L.text ps.toList := match hst with
      | .prog h _ _ => h
      | .hook h _ _ => h
    obtain ⟨-, -, -, hI1, -⟩ := obj_star hE hH hpre hR hX hI hO
    have hpa : IsProgAddr L.text ps.toList s1.pc := by
      rcases hI1.resolve_right hpc with h | ⟨-, h30⟩
      · exact h
      · rw [ih] at h30
        rcases h30 with h | h
        · exact absurd h hout.1
        · exact absurd h hout.2
    rw [leaf_step_x30 hE hleaf hst hpa, ih]

/-! ## Panics -/

/-- The Prog performs no access in the nil page if the machine words do not (`sameEffect`'s
converse load check and equal stores). -/
private theorem noNil_back {f : BitVec 64 → BitVec 64} {sym : Nat → BitVec 64} {pσ mσ : Sym}
    {s t : MState} {k : Bool} (hR : ObjRel f s t) (h27 : k = true → t.x 27 = s.x 27)
    (hse : sameEffectK k mσ pσ = .ok ()) (hn : NoNil ⟨t, sym⟩ mσ) : NoNil ⟨s, sym⟩ pσ := by
  obtain ⟨-, -, -, -, -, hst, -, hrt, hld', -⟩ := sameEffect_spec hse
  obtain ⟨-, -, -, hldok, hstok, -⟩ := readsTmp_false hrt
  refine ⟨fun a n hx => ?_, fun a n v hx => ?_⟩
  · rw [← eval_rel hR h27 sym (hldok _ hx)]
    exact hn.1 a n (hld' _ hx)
  · rw [← eval_rel hR h27 sym (hstok _ hx).1]
    exact hn.2 a n v (by rw [hst]; exact hx)

/-- A Prog with words whose step faults in the nil page: the words run to a faulting word. -/
private theorem obj_words_fault {L : Link} {f : BitVec 64 → BitVec 64}
    {t0 : ByteArray} {rs : List Reloc} {az ez : Int}
    {base : BitVec 64} {code : Code} {retM : BitVec 64} {H : Hooks} {p : Prog} {o e : Nat}
    {pσ mσ : Sym} {pc : PCtl} {mc : MCtl} {s t : MState} {a : BitVec 64} {k : Bool}
    (hlink : linkCode base L.sym t0 rs = .ok code) (hsz : t0.size ≤ 2 ^ 64)
    (hret : code retM = none) (haz : L.autosize = az) (hez : L.extrasize = ez)
    (hoe : o < e) (h4 : (e - o) % 4 = 0)
    (hps : progSym az ez p = .ok (pσ, pc)) (hms : symWords t0 rs ((e - o) / 4) o {} = .ok (mσ, mc))
    (hse : sameEffectK k mσ pσ = .ok ()) (hs : progStep L p s = .error (.nilPage a))
    (hR : ObjRel f s t) (h27 : k = true → t.x 27 = s.x 27)
    (htpc : t.pc = base + BitVec.ofNat 64 o) :
    ∃ t', MStar H code retM t t' ∧ WordFault code retM t' := by
  obtain ⟨n, hn⟩ : ∃ n, (e - o) / 4 = n + 1 := ⟨(e - o) / 4 - 1, by omega⟩
  rw [hn] at hms
  have hbad := progSym_fault hps haz hez hs
  exact symWords_fault (H := H) hlink hsz hret n o {} mσ mc ⟨t, L.sym⟩ t hms rfl (holds_init _)
    htpc ⟨fun _ _ h => by simp at h, fun _ _ _ h => by simp at h⟩
    (fun h => hbad (noNil_back hR h27 hse h))

/-- **A P0 panic is a machine panic**: from related states, a Prog whose access is in the nil
page is matched by machine steps to a word that faults there, and a hook that panics (after a
call) panics alike from the related machine state (`HookPanicMap`). -/
theorem obj_panic {ps : Array Prog} {spills : Array Spill} {o : ObjIn} {tab : Tab} {L : Link}
    {base : BitVec 64} {code : Code} {retM : BitVec 64} {H : Hooks} {s t : MState}
    {pe : GoFV.SSA.Sem.Panic}
    (hE : ObjEnv ps spills o tab L base code retM)
    (hP : HookPanicMap H L ps.toList (ObjEnv.map tab ps L base))
    (hR : ObjRel (ObjEnv.map tab ps L base) s t) (hX : X27At tab L ps.toList s t)
    (hI : ObjInv L ps.toList s)
    (hp : PPanics H L ps.toList (endP L.text ps.toList) s pe) :
    ∃ t', MStar H code retM t t' ∧ GoFV.SSA.Sem.MPanics H code retM t' pe := by
  obtain ⟨text0, body, h0, hT, hnd, hlt, hsz2, hofs, hb0, hb1, -, -, -, -⟩ :=
    checkObj_spec hE.check
  obtain ⟨-, -, -, hokk⟩ := ok27_spec hE.check
  have hlink := hE.link
  have hlen : tab.offs.toList.length = ps.toList.length := by simp [hofs]
  have hsym : ∀ y, ObjEnv.map tab ps L base (L.sym y) = L.sym y := fun y =>
    objMap_fix (hE.syms y).2.2.1 (hE.syms y).2.2.2
  obtain ⟨-, ⟨p, a, hp', hstep, rfl⟩ | ⟨hnone, s', hcall⟩⟩ := hp
  · rw [hlink] at hp'
    obtain ⟨hmem, hspc⟩ := progAt?_mem hp'
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hmem
    have htpc : t.pc = base + BitVec.ofNat 64 (tab.offs.toList[k]'(by omega)) := by
      rw [hR.pc, hspc]
      exact objMap_at hnd hlt hlen hk
    obtain ⟨next, hnext, -, -⟩ := next_map (sym := L.sym) (text := L.text) (base := base)
      (a := tab.autosize) (x := tab.extrasize) (e := tab.endOff) hnd hlt hlen hk
    rw [← hlink] at hnext
    have hskip : ∀ {q : Prog}, q.isSkip = true → L.nextAddr q.id = some next →
        progStep L q s ≠ .error (.nilPage a) := fun hsk hq h => by
      simp [progStep, hq, hsk] at h
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · have hp0 : ps.toList[0] = text0 := by
        rw [Array.getElem?_eq_some_iff] at h0
        obtain ⟨_, h0⟩ := h0
        simpa using h0
      exact absurd hstep (hskip (by rw [hp0]; simp [Prog.isSkip, hT]) hnext)
    · obtain ⟨b, hone, -⟩ := hokk k hk1 hk (by omega)
      rcases checkOne_spec hone with ⟨hret0, -⟩ | ⟨-, hcp⟩
      · exact absurd hstep
          ((progStep_err (ret0_effect (L := L) (s := s) hret0).1 (ret0_effect hret0).2).2 a)
      rcases checkProg_spec hcp with ⟨hsk | hend, -⟩ |
          ⟨-, -, hoe, h4, pσ, pc, mσ, mc, hps, hms, hse, -⟩
      · exact absurd hstep (hskip hsk hnext)
      · exact absurd hstep
          ((progStep_err (end_effect (L := L) (s := s) hend).1 (end_effect hend).2).2 a)
      · obtain ⟨t', hrun, hpc', hc', a', hst'⟩ := obj_words_fault (H := H) hE.linked hE.size
          hE.ret (by rw [hlink]; rfl) (by rw [hlink]; rfl) hoe h4 hps hms hse hstep hR
          (x27_here hX hk hspc) htpc
        exact ⟨t', hrun, hpc', .inl ⟨hc', a', hst', rfl⟩⟩
  · rcases hI with hpa | ⟨⟨y, hy⟩, h30⟩
    · exfalso
      rw [hlink] at hnone
      obtain ⟨p, hp⟩ := progAt?_some hnd hlt hpa
      rw [hp] at hnone
      cases hnone
    · obtain ⟨t', hcall'⟩ := hP s t pe s' hR ⟨y, hy⟩ h30 hcall
      have htpc : t.pc = L.sym y := by rw [hR.pc, hy, hsym]
      exact ⟨t, .refl, by rw [htpc]; exact (hE.syms y).2.1,
        .inr ⟨by rw [htpc]; exact (hE.syms y).1, t', hcall'⟩⟩

end GoFV.Proof.Obj

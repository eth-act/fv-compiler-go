import GoFV.Proof.Obj.Words
import GoFV.Proof.Obj.Prog
import GoFV.Proof.Obj.Spec
import GoFV.Proof.Gen.Basic

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
open GoFV.Proof.Gen (PStep PStar maxId)

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

/-- The runtime hooks treat related states alike: a hook that returns from a P0 state at a
symbol (after a call) returns from every related machine state, to related states, at a Prog
or the end. -/
def HookMap (H : Hooks) (L : Link) (ps : List Prog) (f : BitVec 64 → BitVec 64) : Prop :=
  ∀ s t s', ObjRel f s t → (∃ y, s.pc = L.sym y) →
    (IsProgAddr L.text ps (s.x 30) ∨ s.x 30 = endP L.text ps) → H.call s = some (.ret s') →
    ∃ t', H.call t = some (.ret t') ∧ ObjRel f s' t' ∧
      (IsProgAddr L.text ps s'.pc ∨ s'.pc = endP L.text ps)

/-- What the simulation of one function rests on: the validator accepted, the P0 layout is
`Link.byId` with the validated frame, the code is the linked text, the return address and the
symbols (callees) are outside the code and are not P0 addresses. -/
structure ObjEnv (ps : Array Prog) (spills : Array Spill) (o : ObjIn) (tab : Tab) (L : Link)
    (base : BitVec 64) (code : Code) (retM : BitVec 64) : Prop where
  check : checkObj ps spills o = .ok tab
  link : L = Link.byId L.sym L.text tab.autosize tab.extrasize ps.toList
  code : linkCode base L.sym o.text o.relocs.toList = .ok code
  size : o.text.size ≤ 2 ^ 64
  ret : code retM = none
  syms : ∀ y, code (L.sym y) = none ∧ L.sym y ≠ retM ∧ ¬ IsProgAddr L.text ps.toList (L.sym y) ∧
    L.sym y ≠ endP L.text ps.toList

/-- The address map of a validated function. -/
def ObjEnv.map (tab : Tab) (ps : Array Prog) (L : Link) (base : BitVec 64) :
    BitVec 64 → BitVec 64 :=
  objMap ps.toList tab.offs.toList tab.endOff L.text base

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
    refine ⟨by simp, k, by simp [hlen], by simp, fun j hj => ?_⟩
    have hjk : j < ps.length := by omega
    simp only [List.getElem_zip, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not]
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
  | sp | k | sym => simp [Ex.reads] at hr
  | ld _ a ih | shift _ _ _ a ih | ext _ _ a ih | lo32 a ih | sext _ a ih | page a ih =>
    exact ih (by simpa [Ex.regsOK] using h) (by simpa [Ex.reads] using hr)
  | add a b iha ihb | addSub _ _ a b iha ihb | logical _ _ a b iha ihb | bfm _ _ _ _ a b iha ihb =>
    simp only [Ex.regsOK, Bool.and_eq_true] at h
    simp only [Ex.reads, Bool.or_eq_true] at hr
    rcases hr with hr | hr
    · exact iha h.1 hr
    · exact ihb h.2 hr

theorem reg_ne_of {r : Nat} (hr : r < 31) (h27 : r ≠ 27) (h30 : r ≠ 30) :
    (BitVec.ofNat 5 r : Reg) ≠ 27 ∧ (BitVec.ofNat 5 r : Reg) ≠ 30 := by
  constructor <;> intro h <;> have := congrArg BitVec.toNat h <;> simp at this <;> omega

theorem eval_rel {f : BitVec 64 → BitVec 64} {s t : MState} (hR : ObjRel f s t)
    (sym : Nat → BitVec 64) {e : Ex} (he : e.regsOK = true) :
    e.eval ⟨t, sym⟩ = e.eval ⟨s, sym⟩ := by
  refine Ex.eval_congr rfl hR.sp hR.mem e fun r hr => ?_
  obtain ⟨h31, h27, h30⟩ := Ex.regsOK_reads he hr
  obtain ⟨h27', h30'⟩ := reg_ne_of h31 h27 h30
  exact hR.x _ h27' h30'

theorem fl_eval_rel {f : BitVec 64 → BitVec 64} {s t : MState} (hR : ObjRel f s t)
    (sym : Nat → BitVec 64) {fl : Fl} (hfl : fl.regsOK = true) :
    fl.eval ⟨t, sym⟩ = fl.eval ⟨s, sym⟩ := by
  refine Fl.eval_congr rfl hR.sp hR.mem hR.nzcv fl fun r hr => ?_
  have hok : ∃ a b, (r ∈ [r] ∧ (a.reads r = true ∨ b.reads r = true)) ∧ a.regsOK = true ∧
      b.regsOK = true := by
    cases fl with
    | init => simp [Fl.reads] at hr
    | addSub _ _ a b =>
      simp only [Fl.reads, Bool.or_eq_true] at hr; simp only [Fl.regsOK, Bool.and_eq_true] at hfl
      exact ⟨a, b, ⟨by simp, hr⟩, hfl⟩
    | ands _ a b =>
      simp only [Fl.reads, Bool.or_eq_true] at hr; simp only [Fl.regsOK, Bool.and_eq_true] at hfl
      exact ⟨a, b, ⟨by simp, hr⟩, hfl⟩
  obtain ⟨a, b, ⟨-, hr'⟩, ha, hb⟩ := hok
  obtain ⟨h31, h27, h30⟩ := hr'.elim (Ex.regsOK_reads ha) (Ex.regsOK_reads hb)
  obtain ⟨h27', h30'⟩ := reg_ne_of h31 h27 h30
  exact hR.x _ h27' h30'

theorem storesMem_rel {f : BitVec 64 → BitVec 64} {s t : MState} (hR : ObjRel f s t)
    (sym : Nat → BitVec 64) :
    ∀ (st : List (Ex × Nat × Ex)) (m : Memory),
      (∀ x ∈ st, x.1.regsOK = true ∧ x.2.2.regsOK = true) →
      storesMem ⟨t, sym⟩ st m = storesMem ⟨s, sym⟩ st m
  | [], _, _ => rfl
  | (a, n, v) :: st, m, h => by
    have ha := (h (a, n, v) (by simp)).1
    have hv := (h (a, n, v) (by simp)).2
    simp only [storesMem, eval_rel hR sym ha, eval_rel hR sym hv]
    exact storesMem_rel hR sym st _ fun x hx => h x (by simp [hx])

theorem holds_init (c : Ctx) : Holds c {} c.s where
  x _ _ := by simp [Sym.getX, Ex.eval]
  x31 := rfl
  sp := rfl
  nzcv := rfl
  v := rfl
  mem := rfl
  x30 := by simp [Sym.getX, Ex.eval]

theorem obj_step {ps : Array Prog} {spills : Array Spill} {o : ObjIn} {tab : Tab} {L : Link}
    {base : BitVec 64} {code : Code} {retM : BitVec 64} {H : Hooks} {s s' t : MState}
    (hE : ObjEnv ps spills o tab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map tab ps L base))
    (hs : PStep H L ps.toList (endP L.text ps.toList) s s')
    (hR : ObjRel (ObjEnv.map tab ps L base) s t) (hI : ObjInv L ps.toList s) :
    ∃ t', MStar H code retM t t' ∧ ObjRel (ObjEnv.map tab ps L base) s' t' ∧
      (ObjInv L ps.toList s' ∨ s'.pc = endP L.text ps.toList) := by
  sorry

theorem obj_star {ps : Array Prog} {spills : Array Spill} {o : ObjIn} {tab : Tab} {L : Link}
    {base : BitVec 64} {code : Code} {retM : BitVec 64} {H : Hooks} {s s' t : MState}
    (hE : ObjEnv ps spills o tab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map tab ps L base))
    (hs : PStar H L ps.toList (endP L.text ps.toList) s s')
    (hR : ObjRel (ObjEnv.map tab ps L base) s t) (hI : ObjInv L ps.toList s) :
    ∃ t', MStar H code retM t t' ∧ ObjRel (ObjEnv.map tab ps L base) s' t' ∧
      (ObjInv L ps.toList s' ∨ s'.pc = endP L.text ps.toList) := by
  induction hs with
  | refl => exact ⟨t, .refl, hR, Or.inl hI⟩
  | tail _ hst ih =>
    obtain ⟨t1, h1, hR1, hI1⟩ := ih
    have hpc : _ := match hst with
      | .prog h _ _ => h
      | .hook h _ _ => h
    have hI1' : ObjInv L ps.toList _ := hI1.resolve_right hpc
    obtain ⟨t2, h2, hR2, hI2⟩ := obj_step hE hH hst hR1 hI1'
    exact ⟨t2, mstar_trans h1 h2, hR2, hI2⟩

end GoFV.Proof.Obj

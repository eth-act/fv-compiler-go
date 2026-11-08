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

/-- The runtime hooks treat related states alike: a hook that returns from a P0 state at a
symbol (after a call) returns from every related machine state, to related states, at a Prog
or the end. -/
def HookMap (H : Hooks) (L : Link) (ps : List Prog) (f : BitVec 64 → BitVec 64) : Prop :=
  ∀ s t s', ObjRel f s t → (∃ y, s.pc = L.sym y) →
    (IsProgAddr L.text ps (s.x 30) ∨ s.x 30 = endP L.text ps) → H.call s = some (.ret s') →
    ∃ t', H.call t = some (.ret t') ∧ ObjRel f s' t' ∧
      (IsProgAddr L.text ps s'.pc ∨ s'.pc = endP L.text ps)

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
  | sp | k | sym => simp [Ex.reads] at hr
  | ld _ a ih | shift _ _ _ a ih | ext _ _ a ih | lo32 a ih | sext _ a ih | page a ih
  | dp1 _ _ a ih =>
    exact ih (by simpa [Ex.regsOK] using h) (by simpa [Ex.reads] using hr)
  | add a b iha ihb | addSub _ _ a b iha ihb | logical _ _ a b iha ihb | bfm _ _ _ _ a b iha ihb
  | csel _ _ _ _ a b iha ihb =>
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

theorem reg_ne_of {r : Nat} (hr : r < 31) (h27 : r ≠ 27) (h30 : r ≠ 30) :
    (BitVec.ofNat 5 r : Reg) ≠ 27 ∧ (BitVec.ofNat 5 r : Reg) ≠ 30 := by
  constructor <;> intro h <;> have := congrArg BitVec.toNat h <;> simp at this <;> omega

theorem eval_rel {f : BitVec 64 → BitVec 64} {s t : MState} (hR : ObjRel f s t)
    (sym : Nat → BitVec 64) {e : Ex} (he : e.regsOK = true) :
    e.eval ⟨t, sym⟩ = e.eval ⟨s, sym⟩ := by
  refine Ex.eval_congr (c := ⟨t, sym⟩) (c' := ⟨s, sym⟩) rfl hR.sp hR.mem hR.nzcv e fun r hr => ?_
  obtain ⟨h31, h27, h30⟩ := Ex.regsOK_reads he hr
  obtain ⟨h27', h30'⟩ := reg_ne_of h31 h27 h30
  exact hR.x _ h27' h30'

theorem fl_eval_rel {f : BitVec 64 → BitVec 64} {s t : MState} (hR : ObjRel f s t)
    (sym : Nat → BitVec 64) {fl : Fl} (hfl : fl.regsOK = true) :
    fl.eval ⟨t, sym⟩ = fl.eval ⟨s, sym⟩ := by
  refine Fl.eval_congr (c := ⟨t, sym⟩) (c' := ⟨s, sym⟩) rfl hR.sp hR.mem hR.nzcv fl
    fun r hr => ?_
  have hok : ∃ a b : Ex, (r ∈ [r] ∧ (a.reads r = true ∨ b.reads r = true)) ∧ a.regsOK = true ∧
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

/-! ## One step -/

private theorem mem_cmpRegs {r : Nat} : r ∈ cmpRegs ↔ r < 31 ∧ r ≠ 27 ∧ r ≠ 30 := by
  simp only [cmpRegs, List.mem_filter, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq]

private theorem lookup_regsOK {l : List (Nat × Ex)} (h : ∀ x ∈ l, x.2.regsOK = true) {r : Nat}
    {v : Ex} (hl : l.lookup r = some v) : v.regsOK = true := by
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

/-- What `readsTmp = false` says about a Prog effect. -/
private theorem readsTmp_false {σ : Sym} (h : σ.readsTmp = false) :
    (∀ r ∈ cmpRegs, (σ.getX r).regsOK = true) ∧ σ.sp.regsOK = true ∧ σ.fl.regsOK = true ∧
    (∀ x ∈ σ.loads, x.1.regsOK = true) ∧
    (∀ x ∈ σ.stores, x.1.regsOK = true ∧ x.2.2.regsOK = true) := by
  simp only [Sym.readsTmp, Bool.or_eq_false_iff, List.any_eq_false, Bool.not_eq_true',
    Bool.not_eq_false'] at h
  obtain ⟨⟨⟨⟨hx, hsp⟩, hfl⟩, hld⟩, hst⟩ := h
  refine ⟨fun r hr => ?_, by simpa using hsp, by simpa using hfl,
    fun x hx => by simpa using hld x hx,
    fun x hx => by simpa using hst x hx⟩
  unfold Sym.getX
  cases hl : σ.x.lookup r with
  | none =>
    obtain ⟨h31, h27, h30⟩ := mem_cmpRegs.1 hr
    simp [Ex.regsOK, h31, h27, h30]
  | some v => exact lookup_regsOK (fun x hx' => by simpa using hx x hx') hl

/-- The machine words perform no access in the nil page if the Prog does not. -/
private theorem noNil_rel {f : BitVec 64 → BitVec 64} {sym : Nat → BitVec 64} {pσ mσ : Sym}
    {s t : MState} (hR : ObjRel f s t) (hse : sameEffect mσ pσ = .ok ())
    (hn : NoNil ⟨s, sym⟩ pσ) : NoNil ⟨t, sym⟩ mσ := by
  obtain ⟨-, -, -, -, -, hst, hld, hrt, -⟩ := sameEffect_spec hse
  obtain ⟨-, -, -, hldok, hstok⟩ := readsTmp_false hrt
  refine ⟨fun a n hx => ?_, fun a n v hx => ?_⟩
  · have hx' := hld _ hx
    rw [eval_rel hR sym (hldok _ hx')]
    exact hn.1 a n hx'
  · rw [hst] at hx
    rw [eval_rel hR sym (hstok _ hx).1]
    exact hn.2 a n v hx

/-- The registers but `X30`, `SP`, the vector registers, the flags and the memory after the
words and after the Prog agree. -/
private theorem obj_core {f : BitVec 64 → BitVec 64} {sym : Nat → BitVec 64} {pσ mσ : Sym}
    {s s' t t' : MState} (hR : ObjRel f s t) (hse : sameEffect mσ pσ = .ok ())
    (hm : HoldsCore ⟨t, sym⟩ mσ t') (hp : HoldsCore ⟨s, sym⟩ pσ s') :
    (∀ k : Reg, k ≠ 27 → k ≠ 30 → t'.x k = s'.x k) ∧ t'.sp = s'.sp ∧ t'.v = s'.v ∧
      t'.nzcv = s'.nzcv ∧ t'.mem = s'.mem := by
  obtain ⟨hregs, -, -, hsp, hfl, hst, -, hrt, -⟩ := sameEffect_spec hse
  obtain ⟨hxok, hspok, hflok, -, hstok⟩ := readsTmp_false hrt
  refine ⟨fun k h27 h30 => ?_, ?_, ?_, ?_, ?_⟩
  · have hk : k = BitVec.ofNat 5 k.toNat := by simp
    have hlt := k.isLt
    by_cases h31 : k.toNat = 31
    · have : k = 31 := by rw [hk, h31]; rfl
      subst this
      rw [hm.x31, hp.x31]
      exact hR.x 31 (by decide) (by decide)
    · have h30' : k.toNat ≠ 30 := fun h => h30 (by rw [hk, h]; rfl)
      have h27' : k.toNat ≠ 27 := fun h => h27 (by rw [hk, h]; rfl)
      have hmem : k.toNat ∈ cmpRegs := mem_cmpRegs.2 ⟨by omega, h27', h30'⟩
      rw [hk, hm.x k.toNat (by omega), hp.x k.toNat (by omega), hregs _ hmem]
      exact eval_rel hR sym (hxok _ hmem)
  · rw [hm.sp, hp.sp, hsp]
    exact eval_rel hR sym hspok
  · rw [hm.v, hp.v]
    exact hR.v
  · rw [hm.nzcv, hp.nzcv, hfl]
    exact fl_eval_rel hR sym hflok
  · rw [hm.mem, hp.mem, hst]
    dsimp only
    rw [hR.mem]
    exact storesMem_rel hR sym _ _ hstok

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
    {mc : MCtl} {ol : Nat} {s s' t t' : MState}
    (hR : ObjRel f s t) (hcm : CtlMatch offs pσ mc pc) (hpp : PcP L p pσ s pc s')
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
      obj_pc_ite h3 hmp (by rw [eval_rel hR L.sym hok]) (htgt _ _ _ hT h2) hfn hinvn⟩
  case tbz.tbz nz b a q nz' b' a' id =>
    obtain ⟨rfl, rfl, rfl, hok, hT⟩ := hcm
    simp only [PcP] at hpp
    simp only [CtlPc] at hmp
    obtain ⟨⟨next', tgt, h1, h2, h3⟩, h4⟩ := hpp
    rw [hnext, Option.some.injEq] at h1
    subst h1
    exact ⟨keep rfl h4,
      obj_pc_ite h3 hmp (by rw [eval_rel hR L.sym hok]) (htgt _ _ _ hT h2) hfn hinvn⟩
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
    refine ⟨by rw [h4, ← h2, hfn], by rw [h3, eval_rel hR L.sym hok, ← h1, hy, hsym],
      Or.inl (Or.inr ⟨⟨y, hy⟩, ?_⟩)⟩
    rw [← h2]
    exact hinvn

/-- A skip: no machine step. -/
private theorem obj_skip {L : Link} {ps : List Prog} {f : BitVec 64 → BitVec 64} {H : Hooks}
    {code : Code} {retM : BitVec 64} {p : Prog} {s s' t : MState} {next : BitVec 64}
    (hsk : p.isSkip = true) (hs : progStep L p s = .ok s') (hnext : L.nextAddr p.id = some next)
    (hR : ObjRel f s t) (hpc : t.pc = f next)
    (hinvn : IsProgAddr L.text ps next ∨ next = endP L.text ps) :
    ∃ t', MStar H code retM t t' ∧ ObjRel f s' t' ∧ (ObjInv L ps s' ∨ s'.pc = endP L.text ps) := by
  have : s' = { s with pc := next } := by
    simp only [progStep, hnext, hsk, ↓reduceIte, Except.ok.injEq] at hs
    exact hs.symm
  subst this
  exact ⟨t, .refl, ⟨hR.x, hR.x30, hR.sp, hR.v, hR.nzcv, hR.mem, hpc⟩, inv_of rfl hinvn⟩

/-- A Prog with words: the words run as the Prog steps. -/
private theorem obj_words {L : Link} {ps : List Prog} {f : BitVec 64 → BitVec 64}
    {t0 : ByteArray} {rs : List Reloc} {offs : List (Nat × Nat)} {az ez : Int}
    {base : BitVec 64} {code : Code} {retM : BitVec 64} {H : Hooks} {p : Prog} {o e : Nat}
    {next : BitVec 64} {pσ mσ : Sym} {pc : PCtl} {mc : MCtl} {s s' t : MState}
    (hlink : linkCode base L.sym t0 rs = .ok code) (hsz : t0.size ≤ 2 ^ 64)
    (hret : code retM = none) (haz : L.autosize = az) (hez : L.extrasize = ez)
    (hskip : p.isSkip = false) (hoe : o < e) (h4 : (e - o) % 4 = 0)
    (hps : progSym az ez p = .ok (pσ, pc)) (hms : symWords t0 rs ((e - o) / 4) o {} = .ok (mσ, mc))
    (hse : sameEffect mσ pσ = .ok ()) (hsc : sameCtl offs mc pc pσ = .ok ())
    (hs : progStep L p s = .ok s') (hR : ObjRel f s t) (htpc : t.pc = base + BitVec.ofNat 64 o)
    (hnext : L.nextAddr p.id = some next) (hfn : f next = base + BitVec.ofNat 64 e)
    (hinvn : IsProgAddr L.text ps next ∨ next = endP L.text ps)
    (htgt : ∀ id q a, TgtOK offs id q → L.addr id = some a →
      f a = at_ base q ∧ IsProgAddr L.text ps a)
    (hsym : ∀ y, f (L.sym y) = L.sym y) (hic : isICall p = true → ∃ y, s'.pc = L.sym y) :
    ∃ t', MStar H code retM t t' ∧ ObjRel f s' t' ∧ (ObjInv L ps s' ∨ s'.pc = endP L.text ps) := by
  obtain ⟨n, hn⟩ : ∃ n, (e - o) / 4 = n + 1 := ⟨(e - o) / 4 - 1, by omega⟩
  rw [hn] at hms
  obtain ⟨hnil, hcore, hpp⟩ := progSym_sound hps haz hez hskip hs
  obtain ⟨t', hst, hcore', hx30, hctl⟩ := symWords_sound (H := H) hlink hsz hret n o {} mσ mc
    ⟨t, L.sym⟩ t hms rfl (holds_init _) htpc (noNil_rel hR hse hnil)
  obtain ⟨hx, hsp, hv, hfl, hmem⟩ := obj_core hR hse hcore' hcore
  obtain ⟨-, h30m, h30p, -⟩ := sameEffect_spec hse
  have hfn' : f next = at_ base ((o + 4 * n : Nat) + 4) := by
    rw [hfn, at_nat]
    congr 1
    omega
  obtain ⟨h30, hpc, hinv⟩ := obj_ctl hR (sameCtl_spec hsc) hpp hctl hx30 h30m h30p hnext hfn'
    hinvn htgt hsym hic
  exact ⟨t', hst, ⟨hx, h30, hsp, hv, hfl, hmem, hpc⟩, hinv⟩

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

/-- `checkBody` checked the Prog at index `k ≥ 1`. -/
private theorem body_at {t : ByteArray} {rs : List Reloc} {offs : List (Nat × Nat)} {az ez : Int}
    {leaf : Bool} {ps : List Prog} {ss : List Nat} {lastEnd : Nat}
    (hbody : checkBody t rs offs az ez leaf (ps.drop 1) (ss.drop 1) lastEnd = .ok ())
    (hlen : ss.length = ps.length) {k : Nat} (hk1 : 1 ≤ k) (hk : k < ps.length) :
    checkOne t rs offs az ez leaf ps[k] (ss[k]'(by omega)) (ss.getD (k + 1) lastEnd) = .ok () := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := checkBody_spec _ _ _ hbody (by simp [hlen]) j (by simp; omega)
  simpa [List.getElem_drop, Nat.add_comm, List.getD_eq_getElem?_getD] using h

theorem obj_step {ps : Array Prog} {spills : Array Spill} {o : ObjIn} {tab : Tab} {L : Link}
    {base : BitVec 64} {code : Code} {retM : BitVec 64} {H : Hooks} {s s' t : MState}
    (hE : ObjEnv ps spills o tab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map tab ps L base))
    (hs : PStep H L ps.toList (endP L.text ps.toList) s s')
    (hR : ObjRel (ObjEnv.map tab ps L base) s t) (hI : ObjInv L ps.toList s)
    (hO : ICallOut L ps.toList s) :
    ∃ t', MStar H code retM t t' ∧ ObjRel (ObjEnv.map tab ps L base) s' t' ∧
      (ObjInv L ps.toList s' ∨ s'.pc = endP L.text ps.toList) := by
  obtain ⟨text0, body, h0, hT, hnd, hlt, hsz2, hofs, hb0, hb1, -, -, -, hbody⟩ :=
    checkObj_spec hE.check
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
    · obtain ⟨t', hcall', hR', hinv'⟩ := hH s t s' hR ⟨y, hy⟩ h30 hcall
      have htpc : t.pc = L.sym y := by rw [hR.pc, hy, hsym]
      refine ⟨t', mstar_single (.hook ?_ ?_ hcall'), hR', inv_of rfl hinv'⟩
      · rw [htpc]; exact (hE.syms y).2.1
      · rw [htpc]; exact (hE.syms y).1
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
      exact obj_skip hsk hstep hnext hR (by rw [htpc, hoff0]; exact (hoff1 ▸ hfn).symm) hinvn
    · have hone := body_at hbody hlen hk1 hk
      rcases checkOne_spec hone with ⟨hret0, -⟩ | ⟨-, hcp⟩
      · exact absurd hstep (progStep_ret0 hret0)
      rcases checkProg_spec hcp with ⟨hsk | hend, hoe⟩ |
          ⟨hsk, -, hoe, h4, pσ, pc, mσ, mc, hps, hms, hse, hsc⟩
      · exact obj_skip hsk hstep hnext hR (by rw [htpc, hoe]; exact hfn.symm) hinvn
      · exact absurd hstep (progStep_end hend)
      · refine obj_words hE.linked hE.size hE.ret (by rw [hlink]; rfl) (by rw [hlink]; rfl) hsk
          hoe
          h4 hps hms hse hsc hstep hR htpc hnext hfn hinvn ?_ hsym (fun hi => hO _ _ hp0 hi hstep)
        rintro id q a ⟨o', ho, rfl⟩ ha
        obtain ⟨j, hj, rfl, rfl⟩ := offOf_zip hlen ho
        rw [hlink, GoFV.Proof.Gen.addr_byId (List.getElem_mem hj), Option.some_inj] at ha
        subst ha
        exact ⟨by rw [← at_nat]; exact objMap_at hnd hlt hlen hj, ⟨_, List.getElem_mem hj, rfl⟩⟩

theorem obj_star {ps : Array Prog} {spills : Array Spill} {o : ObjIn} {tab : Tab} {L : Link}
    {base : BitVec 64} {code : Code} {retM : BitVec 64} {H : Hooks} {s s' t : MState}
    (hE : ObjEnv ps spills o tab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map tab ps L base))
    (hs : PStar H L ps.toList (endP L.text ps.toList) s s')
    (hR : ObjRel (ObjEnv.map tab ps L base) s t)
    (hI : ObjInv L ps.toList s ∨ s.pc = endP L.text ps.toList)
    (hO : ∀ u, PStar H L ps.toList (endP L.text ps.toList) s u → ICallOut L ps.toList u) :
    ∃ t', MStar H code retM t t' ∧ ObjRel (ObjEnv.map tab ps L base) s' t' ∧
      (ObjInv L ps.toList s' ∨ s'.pc = endP L.text ps.toList) := by
  induction hs with
  | refl => exact ⟨t, .refl, hR, hI⟩
  | tail hpre hst ih =>
    obtain ⟨t1, h1, hR1, hI1⟩ := ih
    have hpc : _ := match hst with
      | .prog h _ _ => h
      | .hook h _ _ => h
    have hI1' : ObjInv L ps.toList _ := hI1.resolve_right hpc
    obtain ⟨t2, h2, hR2, hI2⟩ := obj_step hE hH hst hR1 hI1' (hO _ hpre)
    exact ⟨t2, mstar_trans h1 h2, hR2, hI2⟩

/-! ## Panics -/

/-- The Prog performs no access in the nil page if the machine words do not (`sameEffect`'s
converse load check and equal stores). -/
private theorem noNil_back {f : BitVec 64 → BitVec 64} {sym : Nat → BitVec 64} {pσ mσ : Sym}
    {s t : MState} (hR : ObjRel f s t) (hse : sameEffect mσ pσ = .ok ())
    (hn : NoNil ⟨t, sym⟩ mσ) : NoNil ⟨s, sym⟩ pσ := by
  obtain ⟨-, -, -, -, -, hst, -, hrt, hld'⟩ := sameEffect_spec hse
  obtain ⟨-, -, -, hldok, hstok⟩ := readsTmp_false hrt
  refine ⟨fun a n hx => ?_, fun a n v hx => ?_⟩
  · rw [← eval_rel hR sym (hldok _ hx)]
    exact hn.1 a n (hld' _ hx)
  · rw [← eval_rel hR sym (hstok _ hx).1]
    exact hn.2 a n v (by rw [hst]; exact hx)

/-- A Prog with words whose step faults in the nil page: the words run to a faulting word. -/
private theorem obj_words_fault {L : Link} {f : BitVec 64 → BitVec 64}
    {t0 : ByteArray} {rs : List Reloc} {az ez : Int}
    {base : BitVec 64} {code : Code} {retM : BitVec 64} {H : Hooks} {p : Prog} {o e : Nat}
    {pσ mσ : Sym} {pc : PCtl} {mc : MCtl} {s t : MState} {a : BitVec 64}
    (hlink : linkCode base L.sym t0 rs = .ok code) (hsz : t0.size ≤ 2 ^ 64)
    (hret : code retM = none) (haz : L.autosize = az) (hez : L.extrasize = ez)
    (hoe : o < e) (h4 : (e - o) % 4 = 0)
    (hps : progSym az ez p = .ok (pσ, pc)) (hms : symWords t0 rs ((e - o) / 4) o {} = .ok (mσ, mc))
    (hse : sameEffect mσ pσ = .ok ()) (hs : progStep L p s = .error (.nilPage a))
    (hR : ObjRel f s t) (htpc : t.pc = base + BitVec.ofNat 64 o) :
    ∃ t', MStar H code retM t t' ∧ WordFault code retM t' := by
  obtain ⟨n, hn⟩ : ∃ n, (e - o) / 4 = n + 1 := ⟨(e - o) / 4 - 1, by omega⟩
  rw [hn] at hms
  have hbad := progSym_fault hps haz hez hs
  exact symWords_fault (H := H) hlink hsz hret n o {} mσ mc ⟨t, L.sym⟩ t hms rfl (holds_init _)
    htpc ⟨fun _ _ h => by simp at h, fun _ _ _ h => by simp at h⟩
    (fun h => hbad (noNil_back hR hse h))

/-- **A P0 panic is a machine panic**: from related states, a Prog whose access is in the nil
page is matched by machine steps to a word that faults there, and a hook that panics (after a
call) panics alike from the related machine state (`HookPanicMap`). -/
theorem obj_panic {ps : Array Prog} {spills : Array Spill} {o : ObjIn} {tab : Tab} {L : Link}
    {base : BitVec 64} {code : Code} {retM : BitVec 64} {H : Hooks} {s t : MState}
    {pe : GoFV.SSA.Sem.Panic}
    (hE : ObjEnv ps spills o tab L base code retM)
    (hP : HookPanicMap H L ps.toList (ObjEnv.map tab ps L base))
    (hR : ObjRel (ObjEnv.map tab ps L base) s t) (hI : ObjInv L ps.toList s)
    (hp : PPanics H L ps.toList (endP L.text ps.toList) s pe) :
    ∃ t', MStar H code retM t t' ∧ GoFV.SSA.Sem.MPanics H code retM t' pe := by
  obtain ⟨text0, body, h0, hT, hnd, hlt, hsz2, hofs, hb0, hb1, -, -, -, hbody⟩ :=
    checkObj_spec hE.check
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
    · have hone := body_at hbody hlen hk1 hk
      rcases checkOne_spec hone with ⟨hret0, -⟩ | ⟨-, hcp⟩
      · exact absurd hstep
          ((progStep_err (ret0_effect (L := L) (s := s) hret0).1 (ret0_effect hret0).2).2 a)
      rcases checkProg_spec hcp with ⟨hsk | hend, -⟩ |
          ⟨-, -, hoe, h4, pσ, pc, mσ, mc, hps, hms, hse, -⟩
      · exact absurd hstep (hskip hsk hnext)
      · exact absurd hstep
          ((progStep_err (end_effect (L := L) (s := s) hend).1 (end_effect hend).2).2 a)
      · obtain ⟨t', hrun, hpc', hc', a', hst'⟩ := obj_words_fault (H := H) hE.linked hE.size
          hE.ret (by rw [hlink]; rfl) (by rw [hlink]; rfl) hoe h4 hps hms hse hstep hR htpc
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

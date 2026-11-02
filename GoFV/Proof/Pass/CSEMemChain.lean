import GoFV.Proof.Pass.CSEMemBytes
import GoFV.Proof.Eval
import GoFV.Proof.PtrAddr
import GoFV.Opt.CSEMem

/-!
# cse's memory skips: where the pointers of an `OffPtr` chain point

`baseOff_rel`: the value of a pointer `p` relates to the value of its `baseOff` base `b` with
the summed offset `o` (`Rel`): if it is a pointer or a 64-bit integer, it points `o` bytes past
where `b` points (`vaddr`: a global's name and offset, or a concrete address, as `Val.retype`
converts between them), and if `b` is a pointer into block `B`, so is `p` (the chain keeps
pointers: `CSE.keepsPtr`). `allocOf_val`: an `allocOf` base is a pointer to its allocation.
-/

namespace GoFV.Proof.CSE.Mem

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt

/-- The values the memory skips use: every value of `A` is in the function and has a register,
which (outside `Phi`s) is its evaluation; `A` is closed under arguments (outside `Phi`s). -/
structure Avail (env : Env) (tabs : Tables) (f : Func) (fr : Frame) (A : ID → Prop) : Prop where
  val : ∀ x, A x → ∃ v y, f.value? x = some v ∧ fr.regs[x]? = some (some y) ∧
    (v.op ≠ .Phi → evalValue env (Ctx.make tabs f) fr v = .ok y)
  cl : ∀ x v, A x → f.value? x = some v → v.op ≠ .Phi → ∀ a ∈ v.args, A a

/-! ## Where pointer-like values point -/

/-- A position: an offset into a global, or a concrete address. -/
inductive VAddr where
  | glob (s : String) (o : BitVec 64)
  | conc (a : BitVec 64)

def VAddr.add : VAddr → BitVec 64 → VAddr
  | .glob s o, k => .glob s (o + k)
  | .conc a, k => .conc (a + k)

theorem VAddr.add_add (V : VAddr) (a b : BitVec 64) : (V.add a).add b = V.add (a + b) := by
  cases V <;> simp [VAddr.add, BitVec.add_assoc]

/-- Where a pointer points (the write-barrier buffer, which has no address either, as a global
without a name). -/
def ptrV (p : Ptr) : VAddr :=
  match p.blk with
  | .global s => .glob s p.off
  | .wbuf => .glob "" p.off
  | _ => .conc (p.addr?.getD 0)

/-- Where a pointer or a 64-bit integer (an address) points. -/
def vaddr : Val → Option VAddr
  | .ptr p => some (ptrV p)
  | .int .w64 x => some (.conc x)
  | _ => none

theorem ptrV_add (p : Ptr) (k : BitVec 64) : ptrV (p.add k) = (ptrV p).add k := by
  obtain ⟨b, o⟩ := p
  cases b <;> simp [ptrV, Ptr.add, Ptr.addr?, VAddr.add, Blk.base?, BitVec.add_assoc]

theorem ptrV_of_addr {p : Ptr} {a : BitVec 64} (h : p.addr? = some a) : ptrV p = .conc a := by
  obtain ⟨b, o⟩ := p
  cases b <;> simp_all [ptrV, Ptr.addr?, Blk.base?]

theorem ofNat_add_eq {x : BitVec 64} {base r : Nat} (h : base + r = x.toNat) :
    BitVec.ofNat 64 base + BitVec.ofNat 64 r = x := by
  rw [BitVec.ofNat_add_ofNat, h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem addr_ofAddr (x : BitVec 64) : (Ptr.ofAddr x).addr? = some x := by
  have hx : x.toNat < 18446744073709551616 := x.isLt
  unfold Ptr.ofAddr
  dsimp only
  split
  · simp [Ptr.addr?, Blk.base?]
  · split
    · simp only [Ptr.addr?, Blk.base?, Option.map_some, Option.some.injEq]
      apply ofNat_add_eq
      omega
    · split <;> simp only [Ptr.addr?, Blk.base?, Option.map_some, Option.some.injEq] <;>
        apply ofNat_add_eq <;> simp only [beq_iff_eq] at * <;> omega

theorem ofAddr_not_global (x : BitVec 64) (s : String) : (Ptr.ofAddr x).blk ≠ .global s := by
  unfold Ptr.ofAddr
  dsimp only
  split
  · nofun
  · split
    · nofun
    · split <;> nofun

theorem ptrV_ofAddr (x : BitVec 64) : ptrV (Ptr.ofAddr x) = .conc x := ptrV_of_addr (addr_ofAddr x)

/-- A pointer's word points where the pointer does. -/
theorem vaddr_word (p : Ptr) : vaddr p.word = vaddr (.ptr p) := by
  rcases Ptr.word_cases p with ⟨-, h⟩ | ⟨-, a, ha, h⟩ <;> rw [h]
  simp [vaddr, ptrV_of_addr ha]

/-- `Val.retype` keeps where a value points, or makes it point nowhere. -/
theorem vaddr_retype (t : Ty) (v : Val) : vaddr (v.retype t) = none ∨ vaddr (v.retype t) = vaddr v := by
  unfold Val.retype
  split
  · exact .inr rfl
  · rename_i w' w x
    split
    · rename_i h
      cases w' <;> cases w <;> simp_all [vaddr, Width.bits, BitVec.setWidth_eq]
    · exact .inl rfl
  · rename_i p
    exact .inr (vaddr_word p)
  · exact .inr (by simp [vaddr, ptrV_ofAddr])
  · rename_i p
    exact .inr (vaddr_word p)
  all_goals first
    | exact .inl rfl
    | exact .inr rfl
    | (split <;> first | exact .inl rfl | exact .inr rfl)
    | (simp only [Val.ofStr, Val.ofSlice]; split <;> first | exact .inl rfl | exact .inr rfl)

theorem asPtrWord_retype_keep {t : Ty} (h : CSE.keepsPtr t = true) (v : Val) :
    (v.retype t).asPtrWord = v.asPtrWord := by
  cases t <;> first | exact Val.asPtrWord_retype_ptr _ v | cases h

theorem retype_global {t : Ty} (h : CSE.keepsGlobal t = true) (s : String) (o : BitVec 64) :
    (Val.ptr ⟨.global s, o⟩).retype t = .ptr ⟨.global s, o⟩ := by
  cases t with
  | int w => cases w <;> first | rfl | cases h
  | _ => first | rfl | cases h

theorem vaddr_offPtr (k : Int64) (v : Val) :
    vaddr (PtrOps.offPtr k [v]) = none ∨
      vaddr (PtrOps.offPtr k [v]) = (vaddr v).map (·.add (BitVec.ofInt 64 k.toInt)) := by
  cases v with
  | ptr p =>
    simp only [PtrOps.offPtr, PtrOps.ptrRes]
    split
    · exact .inr (by rw [vaddr_word]; simp [vaddr, ptrV_add])
    · exact .inl rfl
  | int w x =>
    cases w
    case w64 =>
      simp only [PtrOps.offPtr, PtrOps.wordRes]
      split
      · exact .inr (by simp [vaddr, VAddr.add])
      · exact .inl rfl
    all_goals exact .inr (by simp [PtrOps.offPtr, vaddr, VAddr.add])
  | _ => exact .inl rfl

/-- `v` points `k` bytes past `bv` (or reads as no pointer: the arithmetic left the
allocation). -/
def Rel (v bv : Val) (k : Int) : Prop :=
  (vaddr v = none ∨ ∃ V, vaddr bv = some V ∧ vaddr v = some (V.add (BitVec.ofInt 64 k))) ∧
  ∀ B o, bv.asPtrWord = some ⟨B, o⟩ →
    v.asPtrWord = none ∨ v.asPtrWord = some ⟨B, o + BitVec.ofInt 64 k⟩

theorem rel_refl (v : Val) : Rel v v 0 :=
  ⟨by cases h : vaddr v with
      | none => exact .inl rfl
      | some V => exact .inr ⟨V, rfl, by cases V <;> simp [VAddr.add]⟩,
   fun B o h => .inr (by simp [h])⟩

theorem rel_step {ty : Ty} (hty : CSE.keepsPtr ty = true) {av bv : Val} {K : Int} (k : Int64)
    (h : Rel av bv K) : Rel ((PtrOps.offPtr k [av]).retype ty) bv (K + k.toInt) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun B o hb => ?_⟩
  · rcases vaddr_retype ty (PtrOps.offPtr k [av]) with h | h
    · exact .inl h
    · rw [h]
      rcases vaddr_offPtr k av with h0 | h0
      · exact .inl h0
      rw [h0]
      rcases h1 with h1 | ⟨V, hV, h1⟩
      · exact .inl (by rw [h1]; rfl)
      · refine .inr ⟨V, hV, ?_⟩
        rw [h1, Option.map_some, VAddr.add_add, BitVec.ofInt_add]
  · rw [asPtrWord_retype_keep hty, PtrOps.offPtr_asPtrWord]
    rcases h2 B o hb with h2 | h2 <;> rw [h2]
    · exact .inl rfl
    simp only [Option.bind_some, Ptr.step?, Ptr.add]
    simp only [BitVec.ofInt_add, BitVec.add_assoc]
    split
    · exact .inr rfl
    · exact .inl rfl

/-- A pointer word points where the pointer it reads as does. -/
theorem vaddr_of_asPtrWord {v : Val} {P : Ptr} (h : v.asPtrWord = some P) :
    vaddr v = some (ptrV P) := by
  rcases v with ⟨_ | _ | _ | _, x⟩ | _ | _ | _ | q | _ | _ | _ | _ <;>
    simp only [Val.asPtrWord, reduceCtorEq, Option.some.injEq] at h
  · subst h; simp [vaddr, ptrV_ofAddr]
  · subst h; rfl

/-- Two pointer words relating to one value point `kq - kp` bytes apart within a block. -/
theorem rel_same {pv qv : Val} {P Q : Ptr} {bv : Val} {kp kq : Int}
    (hpP : pv.asPtrWord = some P) (hqQ : qv.asPtrWord = some Q) (hp : Rel pv bv kp)
    (hq : Rel qv bv kq) (hb : P.blk = Q.blk) :
    Q.off = P.off + BitVec.ofInt 64 (kq - kp) := by
  obtain ⟨hp, -⟩ := hp
  obtain ⟨hq, -⟩ := hq
  rw [vaddr_of_asPtrWord hpP] at hp
  rw [vaddr_of_asPtrWord hqQ] at hq
  rcases hp with hp | ⟨V, hV, hp⟩
  · cases hp
  rcases hq with hq | ⟨V', hV', hq⟩
  · cases hq
  rw [hV] at hV'
  cases hV'
  simp only [Option.some.injEq] at hp hq
  have hs : BitVec.ofInt 64 (kq - kp) = BitVec.ofInt 64 kq - BitVec.ofInt 64 kp := by
    rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]
  rw [hs]
  obtain ⟨pb, po⟩ := P
  obtain ⟨qb, qo⟩ := Q
  simp only at hb
  subst hb
  cases V with
  | glob s o =>
    cases pb <;> simp only [ptrV, VAddr.add, reduceCtorEq, VAddr.glob.injEq] at hp hq
    all_goals
      obtain ⟨-, rfl⟩ := hp
      obtain ⟨-, rfl⟩ := hq
      simp only
      bv_omega
  | conc a =>
    cases pb <;> simp only [ptrV, VAddr.add, reduceCtorEq, VAddr.conc.injEq, Ptr.addr?,
      Blk.base?, Option.map_some, Option.getD_some] at hp hq <;> simp only <;> bv_omega

/-! ## Evaluation of the chain's values -/

theorem tys_getD (tabs : Tables) (f : Func) (v : Value) :
    (Ctx.make tabs f).tys[v.id]?.getD .other = CSE.valShape tabs f v := by
  unfold CSE.valShape
  cases h : f.value? v.id with
  | some w => rw [tys_of_value h]; rfl
  | none =>
    simp only [Ctx.make, Array.getElem?_map]
    unfold Func.value? at h
    cases hx : f.valueTab[v.id]? with
    | none => rfl
    | some o =>
      rw [hx] at h
      cases o with
      | none => rfl
      | some _ => cases h

theorem mapM_ofOption_ok {m : ID → String} {r : ID → Option Val} :
    ∀ {l : List ID} {L : List Val}, l.mapM (fun a => Res.ofOption (m a) (r a)) = .ok L →
      l.map r = L.map some
  | [], L, h => by cases h; rfl
  | a :: l, L, h => by
    rw [List.mapM_cons] at h
    cases ha : r a with
    | none => rw [ha] at h; cases h
    | some z =>
      rw [ha] at h
      change Res.bind (List.mapM (fun a => Res.ofOption (m a) (r a)) l) _ = _ at h
      cases hl : l.mapM (fun a => Res.ofOption (m a) (r a)) with
      | ok L' =>
        rw [hl] at h
        cases h
        simp only [List.map_cons, ha, mapM_ofOption_ok hl]
      | panic e m' => rw [hl] at h; cases h
      | stuck msg => rw [hl] at h; cases h

theorem map_some_inj : ∀ {L L' : List Val}, L.map some = L'.map some → L = L'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: L, b :: L', h => by
    simp only [List.map_cons, List.cons.injEq, Option.some.injEq] at h
    rw [h.1, map_some_inj h.2]

/-- An evaluated value: its arguments' registers, and the result of `evalOp` on them. -/
theorem evalValue_ok {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {y : Val}
    (h : evalValue env ctx fr v = .ok y) : ∃ argv r,
      v.args.toList.map (fun a => (fr.regs[a]?).join) = argv.map some ∧
      evalOp env ctx fr v argv (ctx.tys[v.id]?.getD .other) = .ok r ∧
      y = r.retype (ctx.tys[v.id]?.getD .other) := by
  unfold evalValue at h
  cases hm : v.args.toList.mapM (fun a =>
      Res.ofOption s!"v{v.id}: argument v{a} has no value" (fr.regs[a]?).join) with
  | panic e m => rw [hm] at h; cases h
  | stuck msg => rw [hm] at h; cases h
  | ok argv =>
    rw [hm] at h
    simp only [bind, Res.bind] at h
    cases ho : evalOp env ctx fr v argv (ctx.tys[v.id]?.getD .other) with
    | ok r => rw [ho] at h; cases h; exact ⟨argv, r, mapM_ofOption_ok hm, ho, rfl⟩
    | panic e m => rw [ho] at h; cases h
    | stuck msg => rw [ho] at h; cases h

theorem evalOp_offPtr {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val} {ty : Ty}
    (hop : v.op = .OffPtr) : evalOp env ctx fr v argv ty = .ok (PtrOps.offPtr v.auxInt argv) := by
  simp only [evalOp, frameVal, hop]
  rfl

theorem evalOp_frameVal {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val} {ty : Ty}
    {x : Val} (hop : v.op = .Addr ∨ v.op = .LocalAddr) (hx : frameVal ctx v = some x) :
    evalOp env ctx fr v argv ty = .ok x := by
  rcases hop with hop | hop <;>
  · unfold evalOp
    rw [hx]
    simp only [hop]
    rfl

/-- The value of an `OffPtr`. -/
theorem offPtr_val {env : Env} {tabs : Tables} {f : Func} {fr : Frame} {v : Value} {a : ID}
    {av y : Val} (hop : v.op = .OffPtr) (ha : v.args = #[a]) (hav : fr.regs[a]? = some (some av))
    (h : evalValue env (Ctx.make tabs f) fr v = .ok y) :
    y = (PtrOps.offPtr v.auxInt [av]).retype (CSE.valShape tabs f v) := by
  obtain ⟨argv, r, hargs, ho, rfl⟩ := evalValue_ok h
  have : argv = [av] := map_some_inj (by rw [← hargs, ha]; simp [hav])
  subst this
  rw [evalOp_offPtr hop] at ho
  cases ho
  rw [tys_getD]

/-! ## The chain -/

variable {env : Env} {tabs : Tables} {f : Func} {fr : Frame} {A : ID → Prop}

theorem Avail.eval (H : Avail env tabs f fr A) {x : ID} {v : Value} {y : Val} (hx : A x)
    (hv : f.value? x = some v) (hop : v.op ≠ .Phi) (hy : fr.regs[x]? = some (some y)) :
    evalValue env (Ctx.make tabs f) fr v = .ok y := by
  obtain ⟨v', y', hv', hy', he⟩ := H.val x hx
  rw [hv] at hv'; cases hv'
  rw [hy] at hy'; cases hy'
  exact he hop

theorem Avail.reg (H : Avail env tabs f fr A) {x : ID} (hx : A x) :
    ∃ y, fr.regs[x]? = some (some y) :=
  let ⟨_, y, _, hy, _⟩ := H.val x hx; ⟨y, hy⟩

theorem getElem!_mem {a : Array ID} {i : Nat} (h : i < a.size) : a[i]! ∈ a := by
  rw [getElem!_pos a i h]; exact Array.getElem_mem h

theorem args_one {a : Array ID} (h : a.size = 1) : a = #[a[0]!] := by
  rcases a with ⟨l⟩; rcases l with _ | ⟨x, _ | ⟨y, l⟩⟩ <;> simp_all

theorem baseOff_rel (H : Avail env tabs f fr A) : ∀ (n : Nat) (p : ID) (off : Int), A p →
    A (CSE.baseOff tabs f n p off).1 ∧ ∀ pv bv, fr.regs[p]? = some (some pv) →
      fr.regs[(CSE.baseOff tabs f n p off).1]? = some (some bv) →
      Rel pv bv ((CSE.baseOff tabs f n p off).2 - off) := by
  intro n
  induction n with
  | zero =>
    intro p off hp
    refine ⟨hp, fun pv bv h1 h2 => ?_⟩
    simp only [CSE.baseOff] at h2 ⊢
    rw [h1] at h2; cases h2; simpa using rel_refl pv
  | succ n ih =>
    intro p off hp
    have base : A p ∧ ∀ pv bv, fr.regs[p]? = some (some pv) → fr.regs[p]? = some (some bv) →
        Rel pv bv (off - off) :=
      ⟨hp, fun pv bv h1 h2 => by rw [h1] at h2; cases h2; simpa using rel_refl pv⟩
    rw [CSE.baseOff]
    cases hv : f.value? p with
    | none => exact base
    | some x =>
      simp only
      split
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨⟨hop, hsz⟩, hk⟩ := hc
        have hphi : x.op ≠ .Phi := by rw [hop]; decide
        have hA0 : A x.args[0]! := H.cl p x hp hv hphi _ (getElem!_mem (by omega))
        obtain ⟨hAb, hrel⟩ := ih x.args[0]! (off + x.auxInt.toInt) hA0
        refine ⟨hAb, fun pv bv h1 h2 => ?_⟩
        obtain ⟨av, hav⟩ := H.reg hA0
        have hy := offPtr_val hop (args_one hsz) hav (H.eval hp hv hphi h1)
        subst hy
        have := rel_step hk x.auxInt (hrel av bv hav h2)
        generalize (CSE.baseOff tabs f n x.args[0]! (off + x.auxInt.toInt)).2 = o at this ⊢
        rwa [show o - (off + x.auxInt.toInt) + x.auxInt.toInt = o - off by omega] at this
      · exact base

/-- The block an allocation lives in (activation 0: `Ctx.make`). -/
def blkOf : CSE.Alloc → Blk
  | .global s => .global s
  | .local n => .local 0 n
  | .temp n => .temp 0 n

theorem blkOf_frameAlloc (tabs : Tables) (n : AuxRef) :
    blkOf (CSE.frameAlloc tabs n) = frameBlk tabs 0 n := by
  unfold CSE.frameAlloc frameBlk; split <;> rfl

theorem blkOf_inj {a b : CSE.Alloc} (h : blkOf a = blkOf b) : a = b := by
  cases a <;> cases b <;> simp_all [blkOf]

/-- An `allocOf` base is a pointer to the start of its allocation. -/
theorem allocOf_val (H : Avail env tabs f fr A) {b : ID} {al : CSE.Alloc} (hb : A b)
    (ha : CSE.allocOf tabs f b = some al) {bv : Val} (hr : fr.regs[b]? = some (some bv)) :
    bv.asPtrWord = some ⟨blkOf al, 0⟩ := by
  unfold CSE.allocOf at ha
  cases hv : f.value? b with
  | none => rw [hv] at ha; cases ha
  | some x =>
    rw [hv] at ha
    simp only at ha
    by_cases hop : x.op = .Addr ∧ CSE.keepsGlobal (CSE.valShape tabs f x) = true
    · obtain ⟨hop, hkg⟩ := hop
      simp only [show (x.op == .Addr && CSE.keepsGlobal (CSE.valShape tabs f x)) = true by
        simp [hop, hkg], ↓reduceIte] at ha
      have he := H.eval hb hv (by rw [hop]; decide) hr
      obtain ⟨argv, r, -, ho, rfl⟩ := evalValue_ok he
      obtain ⟨s, rfl, hf⟩ : ∃ s, al = .global s ∧
          frameVal (Ctx.make tabs f) x = some (.ptr ⟨.global s, 0⟩) := by
        simp only [frameVal, hop]
        show ∃ s, al = .global s ∧ (match x.aux.bind tabs.aux? with
          | some { kind := .sym name .., .. } => some (Val.ptr ⟨.global name.toStringLossy, 0⟩)
          | _ => some .poison) = _
        revert ha
        generalize x.aux.bind tabs.aux? = o
        intro ha
        split at ha
        · cases ha; exact ⟨_, rfl, rfl⟩
        · cases ha
      rw [evalOp_frameVal (.inl hop) hf] at ho
      cases ho
      rw [tys_getD, retype_global hkg]; rfl
    · have hne : (x.op == .Addr && CSE.keepsGlobal (CSE.valShape tabs f x)) = false := by
        cases h1 : (x.op == .Addr) <;> cases h2 : CSE.keepsGlobal (CSE.valShape tabs f x) <;>
          simp_all
      simp only [hne, Bool.false_eq_true, ↓reduceIte] at ha
      split at ha
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨hop, hk⟩ := hc
        cases hx : x.aux with
        | none => rw [hx] at ha; cases ha
        | some n =>
          rw [hx] at ha; cases ha
          have he := H.eval hb hv (by rw [hop]; decide) hr
          obtain ⟨argv, r, -, ho, rfl⟩ := evalValue_ok he
          have hf : frameVal (Ctx.make tabs f) x =
              some (.ptr ⟨blkOf (CSE.frameAlloc tabs n), 0⟩) := by
            rw [blkOf_frameAlloc]; simp only [frameVal, hop, hx]; rfl
          rw [evalOp_frameVal (.inr hop) hf] at ho
          cases ho
          rw [tys_getD, asPtrWord_retype_keep hk]; rfl
      · cases ha

end GoFV.Proof.CSE.Mem

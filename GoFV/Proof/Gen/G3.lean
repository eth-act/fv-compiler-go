import GoFV.Proof.Gen.G2
import GoFV.Proof.Gen.Spec3
import GoFV.Proof.Gen.MemN
import GoFV.Proof.Gen.Progs3
import GoFV.Proof.Gen.Value3
import GoFV.Proof.Gen.Step3

variable [GoFV.SSA.Sem.Addrs]

/-!
# Soundness of the genssa validator's slice G3: widths (`docs/plans/proofs3.md` §4)

`g3_value`: when `checkG3` accepts a function with the class table `kt`, every value of a block
(other than the entry values) run by `runLoc` from a state related by `LocMatch` to a machine state,
whose registers hold values that can be read at the classes the table gives before that value
(`FitsW`; `G3Inv` at `kAt lc kt b blk i`), is matched by `runProg` steps of genssa's P0 Progs to a
state related before the next value, with the registers at the classes before the next value.
`g3_term`: a terminator that goes to a successor is matched by steps to a state related before the
successor's first value, with the registers at the classes of the successor's start (`kt.at`).

The activation is G2's (`G2Env`); the invariant (`G3Inv`) is G2's with the class map of the table
instead of one class per register (an edge may narrow a class, `kNarrow`: `termK_stepX` by
`CoreInv.monoW`); the per-value premises (`G3Pre`) are G1's, with every load (of `n` bytes,
through a register or of a global) reading valid bytes and a boolean load reading 0 or 1.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm

/-! ## The premises -/

/-- The invariant of G3's `runLoc` states at the class map `K` (from the class table): every
register holds a value of the class `K` gives it, G2's memory and slot facts, the separation of
mode `w` (`SepAt`; `false`, `SepFrom`, unless stated). -/
structure G3Inv (E : MatchEnv) (lc : LocCtx) (K : KMap) (s : LocState) (w : Bool := false) :
    Prop where
  core : CoreInv E.ι (StkAt E) K.get s w
  slots : SlotInv lc s

/-- The per-value premises of G3: G1's for compares and subtractions; a load of `n` bytes reads
valid bytes at its address (`symAddr`: the register's address plus the offset, or the global),
and a boolean load reads 0 or 1 (Go stores booleans so). -/
def G3Pre (lc : LocCtx) (s : LocState) (v : Value) : Prop :=
  ((v.op = .ARM64CMP ∨ v.op = .ARM64CMPconst) →
    ∀ a ∈ v.args.toList, ∀ x, s.read lc a = .ok x → NoBarePtr x) ∧
  (∀ as n sg, loadOp? v.op = some (as, n, sg) → ∀ a x, v.args[0]? = some a →
    s.read lc a = .ok x → ∃ p mm bs, symAddr lc.ctx v x = some p ∧ s.mem = .mem mm ∧
      mm.read p n = some bs ∧
      (lc.ty v.id = .bool → ∀ y, mm.load (.int .w8) p = .int .w8 y → y.toNat < 2)) ∧
  SubPre lc s v

/-- G3's premises give G1's for a value whose `MOVDload` has no symbol. -/
theorem G3Pre.g1 {lc : LocCtx} {s : LocState} {v : Value} (h : G3Pre lc s v)
    (haux : v.op = .ARM64MOVDload → v.aux = none) : G1Pre lc s v := by
  refine ⟨h.1, fun hop a x ha hx => ?_, h.2.2⟩
  have hl : loadOp? v.op = some (.MOVD, 8, false) := by simp [loadOp?, hop]
  obtain ⟨p, mm, bs, hp, hmm, hr, -⟩ := h.2.1 _ _ _ hl a x ha hx
  refine ⟨p, mm, bs, ?_, hmm, hr⟩
  rw [← hp]
  unfold symAddr
  rw [haux hop]

/-! ## Class maps -/

theorem KMap.get_ge {K : KMap} {r : Nat} (h : K.size ≤ r) : K.get r = none := by
  simp [KMap.get, Array.getElem?_eq_none h]

/-- The registers a value reads (`kReads`, checked by `checkK`) give `KRead`. -/
theorem kread_of_reads {lc : LocCtx} {v : Value} {K : KMap}
    (h : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2) : KRead lc v K.get := by
  intro hop a ha r c hh hr hc
  apply h (r, c)
  have hp : (v.op == Op.Phi) = false := by simpa using hop
  simp only [kReads, hp, Bool.false_eq_true, ↓reduceIte]
  apply List.mem_append_left
  refine List.mem_filterMap.2 ⟨a, ha, ?_⟩
  simp [kArg, hh, hc, hr]

/-- The result register a `SelectN` reads (`kReads`) holds the class of its component. -/
theorem ksel_of_reads {lc : LocCtx} {v : Value} {K : KMap} {c r : Nat} {ts : List Ty}
    {rs : Array (Option Nat)} (h : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hop : v.op = .SelectN) (hc0 : v.args[0]? = some c) (hts : lc.ty c = .tuple ts)
    (hhc : lc.home c = some (.results rs)) (hrs : rs[v.auxInt.toInt.toNat]? = some (some r))
    {c0 : Nat} (hcl : (ts[v.auxInt.toInt.toNat]?.bind cls) = some c0) : K.get r = some c0 := by
  apply h (r, c0)
  have hp : (v.op == Op.Phi) = false := by rw [hop]; rfl
  have hs : (v.op == Op.SelectN) = true := by rw [hop]; rfl
  simp only [kReads, hp, hs, Bool.false_eq_true, ↓reduceIte, hc0, hhc, hts, tupleTys, hrs,
    Option.join_some, hcl]
  simp

/-- The register a block's control is read from (`kControl`) holds the control's class. -/
theorem kctl_of {lc : LocCtx} {b : Block} {K : KMap}
    (h : ∀ rc ∈ kControl lc b, K.get rc.1 = some rc.2) :
    ∀ c r cc, b.controls[0]? = some c → lc.home c = some (.reg r) → r ≠ zeroReg →
      cls (lc.ty c) = some cc → K.get r = some cc := by
  intro c r cc hc hh hr hcc
  apply h (r, cc)
  simp [kControl, hc, kArg, hh, hcc, hr]

/-- The class table follows a value that writes at most its register home (`kStep`). -/
theorem knext_kStep {lc : LocCtx} {v : Value} {K : KMap}
    (hres : v.op ≠ .Phi → (∀ rs, lc.home v.id = some (.results rs) → rs = #[]) ∧
      ∀ a b, lc.home v.id ≠ some (.pair a b)) :
    KNext lc v K.get (kStep lc K v).get := by
  intro r c hr hc
  rw [kStep_get] at hc
  by_cases hop : v.op = .Phi
  · simp only [hop, ↓reduceIte] at hc
    rw [if_neg (fun h => h.1 hop)]
    exact hc
  · simp only [hop, ↓reduceIte] at hc
    cases hh : lc.home v.id with
    | none =>
      simp only [hh] at hc
      rw [if_neg (fun h => by cases h.2)]
      exact hc
    | some l =>
      cases l with
      | reg r0 =>
        simp only [hh] at hc
        by_cases hrr : r = r0
        · subst hrr
          by_cases hcond : r ≠ zeroReg ∧ r = r ∧ r < K.size
          · rw [if_pos hcond] at hc
            rw [if_pos ⟨hop, rfl⟩]
            exact hc
          · rw [if_neg hcond] at hc
            have hge : K.size ≤ r := Nat.le_of_not_lt fun hlt => hcond ⟨hr, rfl, hlt⟩
            rw [KMap.get_ge hge] at hc
            cases hc
        · rw [if_neg (fun h => hrr h.2.1)] at hc
          rw [if_neg (fun h => hrr (Location.reg.inj (Option.some.inj h.2)).symm)]
          exact hc
      | results rs =>
        simp only [hh] at hc
        rw [(hres hop).1 rs hh] at hc
        simp only [Array.toList_empty, List.zip_nil_right, kResults] at hc
        rw [if_neg (fun h => by cases h.2)]
        exact hc
      | slot k =>
        simp only [hh] at hc
        rw [if_neg (fun h => by cases h.2)]
        exact hc
      | pair a b => exact absurd hh ((hres hop).2 a b)

private theorem zip_some_filterMap : ∀ (ts : List Ty) (outs : List Nat),
    outs.length ≤ ts.length → ((ts.zip (outs.map some)).filterMap (·.2)) = outs
  | _, [], _ => by simp
  | [], _ :: _, h => by simp at h
  | t :: ts, o :: outs, h => by
    simp only [List.map_cons, List.zip_cons_cons, List.filterMap_cons]
    rw [zip_some_filterMap ts outs (by simpa using h)]

/-- The class table follows a static call with distinct result registers (`kStep`). -/
theorem kcall_kStep {lc : LocCtx} {v : Value} {K : KMap} {outs : List Nat} (hop : v.op ≠ .Phi)
    (hres : lc.home v.id = some (.results (outs.map some).toArray) ∨
      (lc.home v.id = none ∧ outs = []))
    (hnd : outs.Nodup) (hlen : outs.length ≤ (tupleTys (lc.ty v.id)).length) :
    KCall (tupleTys (lc.ty v.id)) outs K.get (kStep lc K v).get := by
  intro r c hr hc
  rw [kStep_get] at hc
  simp only [hop, ↓reduceIte] at hc
  rcases hres with hh | ⟨hh, rfl⟩
  · simp only [hh, List.toList_toArray] at hc
    refine ⟨fun j t ho ht => ?_, fun hro => ?_⟩
    · have hmem : (t, some r) ∈ (tupleTys (lc.ty v.id)).zip (outs.map some) := by
        refine List.mem_of_getElem? (List.getElem?_zip_eq_some.2 ⟨ht, ?_⟩)
        rw [List.getElem?_map, ho]; rfl
      by_cases hsz : r < K.size
      · rw [kResults_get_of_mem (by rw [zip_some_filterMap _ _ hlen]; exact hnd) hmem hsz] at hc
        exact hc
      · rw [KMap.get_ge (by rw [kResults_size]; omega)] at hc
        cases hc
    · rw [kResults_get_of_not_mem] at hc
      · exact hc
      · intro t ht
        exact hro (by
          have := List.of_mem_zip ht
          simpa using this.2)
  · simp only [hh] at hc
    exact ⟨fun j t ho => by simp at ho, fun _ => hc⟩

/-! ## One value of G3's own kinds -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {g : G2In} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- A value whose one Prog (matching a pattern) stores, outside the frame (G1's `op_mem` for a
pattern), and keeps the machine's X registers. -/
theorem op_mem2X {P : BitVec 64 → Prop} (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι P K s osp) (hkeep : Keeps E P s m)
    (hj : E.pcOf b i = pcAt text psA.toList j)
    (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j') {pat : Pat} (hone : OneAt2 psA j pat j')
    {mm' : Mem} {M : Memory} (hM : MemInj E.ι mm' M) (hkn : KeysNodup mm')
    (hsep : SepAt osp E.ι P mm') (hP : ∀ y, P y → M y = m.mem y) (hKL : KLe K' K)
    (hstep : ∀ k (hk : k < psA.toList.length), pat.ok psA.toList[k] = true →
      progStep (Link.byId sym text az ez psA.toList) psA.toList[k]
          { m with pc := pcAt text psA.toList k } =
        .ok { m with mem := M, pc := pcAt text psA.toList (k + 1) }) :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E { s with mem := .mem mm' } b (i + 1) m' ∧
      CoreInv E.ι P K' { s with mem := .mem mm' } osp ∧ m'.x = m.x := by
  obtain ⟨k, rfl, hk, hok, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hone m
  rw [pc_eta hm hj] at hstar
  obtain ⟨hsl, hfr⟩ := hkeep M hP
  have hlm := locMatch_setMem hm hsl hfr hM (b' := b) (i' := i + 1)
  rw [hj'] at hlm
  exact ⟨_, hstar.tail (pstep_at F.nodup F.lt F.ret hk rfl (hstep k hk hok)), hlm,
    (⟨hinv.regs, ⟨mm', rfl, hkn, hsep⟩⟩ : CoreInv E.ι P K { s with mem := .mem mm' } osp).mono
      hKL, rfl⟩

/-- `op_mem2X` without the X registers. -/
theorem op_mem2 {P : BitVec 64 → Prop} (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι P K s osp) (hkeep : Keeps E P s m)
    (hj : E.pcOf b i = pcAt text psA.toList j)
    (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j') {pat : Pat} (hone : OneAt2 psA j pat j')
    {mm' : Mem} {M : Memory} (hM : MemInj E.ι mm' M) (hkn : KeysNodup mm')
    (hsep : SepAt osp E.ι P mm') (hP : ∀ y, P y → M y = m.mem y) (hKL : KLe K' K)
    (hstep : ∀ k (hk : k < psA.toList.length), pat.ok psA.toList[k] = true →
      progStep (Link.byId sym text az ez psA.toList) psA.toList[k]
          { m with pc := pcAt text psA.toList k } =
        .ok { m with mem := M, pc := pcAt text psA.toList (k + 1) }) :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E { s with mem := .mem mm' } b (i + 1) m' ∧
      CoreInv E.ι P K' { s with mem := .mem mm' } osp :=
  (op_mem2X (H := H) F hm hinv hkeep hj hj' hone hM hkn hsep hP hKL hstep).imp
    fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩

theorem loadOp?_ne_phi {op : Op} {as : As} {n : Nat} {sg : Bool}
    (h : loadOp? op = some (as, n, sg)) : op ≠ .Phi := by
  rintro rfl; simp [loadOp?, narrowLoad?] at h

theorem storeOp?_ne_phi {op : Op} {as : As} {n : Nat} (h : storeOp? op = some (as, n)) :
    op ≠ .Phi := by
  rintro rfl; simp [storeOp?, narrowStore?] at h

theorem extOp?_ne_phi {op : Op} {as : As} {w : Nat} {sg : Bool}
    (h : extOp? op = some (as, w, sg)) : op ≠ .Phi := by
  rintro rfl; simp [extOp?] at h

/-- The bytes and sign extension of a load. -/
theorem loadOp?_bytes {op : Op} {as : As} {n : Nat} {sg : Bool}
    (h : loadOp? op = some (as, n, sg)) : (n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8) ∧ (n = 8 → sg = false) := by
  rcases loadOp?_op h with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ |
    ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ <;> simp

theorem storeOp?_bytes {op : Op} {as : As} {n : Nat} (h : storeOp? op = some (as, n)) :
    n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 := by
  rcases storeOp?_op h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp

theorem cls_bool {t : Ty} (h : cls t = some 1) : t = .bool := by
  cases t with
  | int w => cases w <;> simp [Gen.Check.cls, Width.bits] at h
  | ptr _ => simp [Gen.Check.cls] at h
  | bool => rfl
  | _ => simp [Gen.Check.cls] at h

/-- `g3_load` with the registers of the machine after the load: the zero or sign extension of
the `n` loaded bytes written to `X[kd]`, `rd = R0 + kd`. -/
theorem g3_loadW (F : Facts lc sym text az ez psA.toList ret E)
    (hglob : ∀ y name abi, g.syms[y]? = some (name, abi) →
      E.ι (.global name.toStringLossy) = some (sym y))
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K') (hpre : G3Pre lc s v)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {n : Nat} {sg : Bool} {c : Nat} {rd : Int} {src : Addr → Prop} {pat : Pat}
    (hop : loadOp? v.op = some (as, n, sg)) (hsz2 : v.args.size = 2) (hacc : AccessOK lc g v src)
    (hma : memArg lc v 1 = .ok ()) (hro : resObj lc v = .ok (c, rd))
    (hc : 8 ≤ c ∨ c = 1 ∧ n = 1 ∧ sg = false)
    (hpat : ∀ p, pat.ok p = true → p.as = as ∧ src p.from_ ∧ p.reg = 0 ∧ p.to = regA rd ∧
      p.scond = 0 ∧ p.rest.isEmpty = true ∧ p.regTo2 = 0)
    (hvs : OneAt2 psA j pat j') (htemp : (lc.temps[v.id]?).join = none)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      ∃ (kd : Nat) (Y : BitVec (8 * n)), rd = GoFV.Asm.ARM64.REG_R0 + kd ∧
        m'.x = (m.wX (BitVec.ofNat 5 kd)
          (if sg then ProgOp.sextTo64 n (Y.setWidth 64) else Y.setWidth 64)).x := by
  have hl := F.lowered
  have hA := F.addr
  have hnp := loadOp?_ne_phi hop
  obtain ⟨hn, hsg⟩ := loadOp?_bytes hop
  have hmov := loadOp?_movMem hop
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨a1, ha1, hamt, hah1⟩ := memArg_spec hma
  obtain ⟨a0, ha0⟩ : ∃ a0, v.args[0]? = some a0 :=
    ⟨v.args[0]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨x, hx, rfl⟩ := stepLoc_loadN hl htemp hop (arr2 hsz2 ha0 ha1)
    (read_mem hl hah1 hamt hmm) hs
  obtain ⟨p, mm2, bs, hsym, hmm2, hrd, h01⟩ := hpre.2.1 _ _ _ hop a0 x ha0 hx
  rw [hmm] at hmm2
  cases hmm2
  rw [write_reg hvh hcv, hsym]
  simp only [Option.elim]
  -- the loaded register at the access's address
  have hval : ∀ a, E.ι p.blk = some a →
      ValRel E.ι ((Arm64.loadN (lc.ty v.id) n sg mm p).retypeL (lc.ty v.id))
        (if sg then ProgOp.sextTo64 n ((readMem m.mem (a + p.off) n).setWidth 64)
         else (readMem m.mem (a + p.off) n).setWidth 64) := by
    intro a ha
    rcases hc with h8 | ⟨rfl, rfl, rfl⟩
    · have ht := cls_ne_bool hcv h8
      exact valRel_retypeL_lo hA hcv ht ((lo_loadN hA hMI hn hsg ht ha hrd).mono (cls_le hcv))
    · have ht := cls_bool hcv
      rw [ht]
      exact valRel_loadBool hA hMI ha hrd (h01 ht)
  cases hacc with
  | reg haux hao =>
    obtain ⟨a0', r0, ha0', hah0, hor0, hca0⟩ := argObj_spec hao
    rw [ha0] at ha0'
    cases ha0'
    obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
    obtain ⟨X, hX, hxv, hxf⟩ :=
      arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
    rw [hx] at hX
    cases hX
    have haddr : Arm64.addr x (BitVec.ofInt 64 v.auxInt.toInt) = some p := by
      rw [← hsym]; unfold symAddr; rw [haux]
    obtain ⟨a, hpa, haeq, hnil⟩ := addr_rel hA hMI hxv hxf haddr (by omega : 0 < n)
      (Or.inr (by rw [hrd]; rfl))
    refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor (hval a hpa) (fits_retypeL hcv _)
      (knext_set hK hnp hvh hcv) (fun k0 hk0 hok => ?_)).imp
      fun m' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, hsi, kd, _, rfl, h4⟩
    obtain ⟨has, hf, -, ht', hsc, -, -⟩ := hpat _ hok
    have haeq' : ({ m with pc := pcAt text psA.toList k0 } : MState).rX (BitVec.ofNat 5 kn) +
        BitVec.ofInt 64 v.auxInt.toInt = a + p.off := haeq
    rw [progStep_loadN hkn hkd (nextAddr_pcAt F.nodup hk0) (by rw [has]; exact hmov) hf hsc ht'
      (by rw [haeq']; exact hnil), haeq', wX_pc]
  | glob hx' ha0' hsb hsy =>
    rename_i xa a0'' name abi
    rw [ha0] at ha0'
    cases ha0'
    have hp := symAddr_global (ctx := lc.ctx) (a := x) hsy hx'
    rw [hsym] at hp
    cases hp
    obtain ⟨k0, -, hk0, hok0, -⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
    obtain ⟨-, ⟨-, -, -, -, -, y, -, hy⟩, -⟩ := hpat _ hok0
    have hpa := hglob y name abi hy
    obtain ⟨hnil, -⟩ := access_nil hMI hpa (by omega : 0 < n) (Or.inr (by rw [hrd]; rfl))
    refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor (hval _ hpa) (fits_retypeL hcv _)
      (knext_set hK hnp hvh hcv) (fun k1 hk1 hok => ?_)).imp
      fun m' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, hsi, kd, _, rfl, h4⟩
    obtain ⟨has, ⟨hf1, hf2, -, -, hf5, y', hy1, hy'⟩, -, ht', -, -, -⟩ := hpat _ hok
    have hyy : sym y' = sym y :=
      Option.some.inj ((hglob y' name abi hy').symm.trans hpa)
    have hL : (Link.byId sym text az ez psA.toList).sym y' = sym y := hyy
    rw [progStep_globLoad hkd (nextAddr_pcAt F.nodup hk1) (by rw [has]; exact hmov) hf1 hf2 hf5
      hy1 ht' (by rw [hL]; exact hnil), hL, wX_pc]

/-- A load of `n` bytes, through a 64-bit register (`off(Rn)`) or of a global (`sym+off(SB)`). -/
theorem g3_load (F : Facts lc sym text az ez psA.toList ret E)
    (hglob : ∀ y name abi, g.syms[y]? = some (name, abi) →
      E.ι (.global name.toStringLossy) = some (sym y))
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K') (hpre : G3Pre lc s v)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {n : Nat} {sg : Bool} {c : Nat} {rd : Int} {src : Addr → Prop} {pat : Pat}
    (hop : loadOp? v.op = some (as, n, sg)) (hsz2 : v.args.size = 2) (hacc : AccessOK lc g v src)
    (hma : memArg lc v 1 = .ok ()) (hro : resObj lc v = .ok (c, rd))
    (hc : 8 ≤ c ∨ c = 1 ∧ n = 1 ∧ sg = false)
    (hpat : ∀ p, pat.ok p = true → p.as = as ∧ src p.from_ ∧ p.reg = 0 ∧ p.to = regA rd ∧
      p.scond = 0 ∧ p.rest.isEmpty = true ∧ p.regTo2 = 0)
    (hvs : OneAt2 psA j pat j') (htemp : (lc.temps[v.id]?).join = none)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' :=
  (g3_loadW (H := H) F hglob hm hinv hsi hR hK hpre hj hj' hop hsz2 hacc hma hro hc hpat hvs
    htemp hs).imp fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- A store of `n` bytes, through a 64-bit register (`off(Rn)`) or to a global (`sym+off(SB)`);
it writes no X register (`XW`). -/
theorem g3_store (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size = 8)
    (hglob : ∀ y name abi, g.syms[y]? = some (name, abi) →
      E.ι (.global name.toStringLossy) = some (sym y))
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {n cs : Nat} {rs : Int} {dst : Addr → Prop} {pat : Pat}
    (hop : storeOp? v.op = some (as, n)) (hsz3 : v.args.size = 3)
    (hmt : memTy (lc.ty v.id) = true) (hhn : lc.home v.id = none) (hacc : AccessOK lc g v dst)
    (hso : argObj lc v 1 = .ok (cs, rs)) (hma : memArg lc v 2 = .ok ())
    (hc : 8 * n ≤ cs ∨ cs = 1 ∧ n = 1)
    (hpat : ∀ p, pat.ok p = true → p.as = as ∧ p.from_ = regA rs ∧ p.reg = 0 ∧ dst p.to ∧
      p.scond = 0 ∧ p.rest.isEmpty = true ∧ p.regTo2 = 0)
    (hvs : OneAt2 psA j pat j') (htemp : (lc.temps[v.id]?).join = none)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      XW lc v m m' := by
  have hl := F.lowered
  have hA := F.addr
  have hnp := storeOp?_ne_phi hop
  have hn := storeOp?_bytes hop
  obtain ⟨sg, hmov⟩ := storeOp?_movMem hop
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hso
  obtain ⟨ks, hks, rfl, hkks⟩ := objOf?_some hor1
  obtain ⟨a2, ha2, hamt, hah2⟩ := memArg_spec hma
  obtain ⟨a0, ha0⟩ : ∃ a0, v.args[0]? = some a0 :=
    ⟨v.args[0]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨y, hy, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkks
  obtain ⟨x, y', p, mm', hx, hy', hsym, hw, rfl⟩ := stepLoc_storeN hl htemp hop
    (arr3 hsz3 ha0 ha1 ha2) (read_mem hl hah2 hamt hmm) hs
  rw [hy] at hy'
  cases hy'
  obtain ⟨mm0, hmm0, hk0, hsep0⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  have hcs : 8 * n ≤ cs ∨ cs = 1 := hc.imp_right And.left
  have hbs := (storeBytes_relN hA hn hyv hyf hcs).1
  have hcan : mm.canWrite p n = true := by
    have := canWrite_of_write hw (by rw [hbs]; omega)
    rwa [hbs] at this
  rw [write_mem hhn hmt, memTy_eq hmt, retypeL_mem]
  -- the store at the injected address of its block
  suffices hfin : ∀ a, E.ι p.blk = some a →
      (∀ k (hk : k < psA.toList.length), pat.ok psA.toList[k] = true →
        progStep (Link.byId sym text az ez psA.toList) psA.toList[k]
            { m with pc := pcAt text psA.toList k } =
          .ok { m with
            mem := writeMem m.mem (a + p.off) n
              (BitVec.ofNat (8 * n) ((m.rX (BitVec.ofNat 5 ks)).toNat % 2 ^ (8 * n))),
            pc := pcAt text psA.toList (k + 1) }) →
      ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
        LocMatch E { s with mem := .mem mm' } b (i + 1) m' ∧
        CoreInv E.ι (StkAt E) K' { s with mem := .mem mm' } osp ∧
        SlotInv lc { s with mem := .mem mm' } ∧ XW lc v m m' by
    cases hacc with
    | reg haux hao =>
      obtain ⟨a0', r0, ha0', hah0, hor0, hca0⟩ := argObj_spec hao
      rw [ha0] at ha0'
      cases ha0'
      obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
      obtain ⟨X, hX, hxv, hxf⟩ :=
        arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
      rw [hx] at hX
      cases hX
      have haddr : Arm64.addr x (BitVec.ofInt 64 v.auxInt.toInt) = some p := by
        rw [← hsym]; unfold symAddr; rw [haux]
      obtain ⟨a, hpa, haeq, hnil⟩ := addr_rel hA hMI hxv hxf haddr (by omega : 0 < n) (Or.inl hcan)
      refine hfin a hpa fun k0 hk0 hok => ?_
      obtain ⟨has, hf, -, ht', hsc, -, -⟩ := hpat _ hok
      have haeq' : ({ m with pc := pcAt text psA.toList k0 } : MState).rX (BitVec.ofNat 5 kn) +
          BitVec.ofInt 64 v.auxInt.toInt = a + p.off := haeq
      rw [progStep_storeN hkn hks (nextAddr_pcAt F.nodup hk0) (by rw [has]; exact hmov) hf hsc ht'
        (by rw [haeq']; exact hnil), haeq']
        <;> rfl
    | glob hx' ha0' hsb hsy =>
      rename_i xa a0'' name abi
      rw [ha0] at ha0'
      cases ha0'
      have hp := symAddr_global (ctx := lc.ctx) (a := x) hsy hx'
      rw [hsym] at hp
      cases hp
      obtain ⟨k0, -, hk0, hok0, -⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
      obtain ⟨-, -, -, ⟨-, -, -, -, -, y0, -, hy0⟩, -⟩ := hpat _ hok0
      have hpa := hglob y0 name abi hy0
      obtain ⟨hnil, -⟩ := access_nil hMI hpa (by omega : 0 < n) (Or.inl hcan)
      refine hfin _ hpa fun k1 hk1 hok => ?_
      obtain ⟨has, hf, -, ⟨ht1, ht2, -, -, ht5, y', hy1, hy'⟩, -, -, -⟩ := hpat _ hok
      have hyy : sym y' = sym y0 := Option.some.inj ((hglob y' name abi hy').symm.trans hpa)
      have hL : (Link.byId sym text az ez psA.toList).sym y' = sym y0 := hyy
      rw [progStep_globStore hks (nextAddr_pcAt F.nodup hk1) (by rw [has]; exact hmov) hf ht1 ht2
        ht5 hy1 (by rw [hL]; exact hnil), hL]
        <;> rfl
  intro a hpa hstep
  obtain ⟨hM', hk', hback, al, hal, hoff, hout⟩ := memInj_storeN hA hMI hk0 hn hpa hyv hyf hcs hw
  have hsep' : SepAt osp E.ι (StkAt E) mm' := hsep0.write hk0 hw
  have hwf := write_wf hw (by rw [hbs]; omega)
  exact (op_mem2X (H := H) F hm hinv (stk_keeps hm hF hsz) hj hj' hvs hM' hk' hsep'
    (fun y hy => hout y fun j hj he => hsep0.not_mem hal hpa hy (by omega) (by omega))
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)) hstep).imp
    fun m' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, hsi, .inl h4⟩

/-- An extension `MOV{B,BU,H,HU,W,WU} Rn, Rd`. -/
theorem g3_ext (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {w : Nat} {sg : Bool} {ca c : Nat} {rn rd : Int}
    (he : extOp? v.op = some (as, w, sg)) (hsz1 : v.args.size = 1)
    (hao : argObj lc v 0 = .ok (ca, rn)) (hro : resObj lc v = .ok (c, rd)) (hw : w ≤ ca ∨ ca = 1)
    (h8 : 8 ≤ c) (hvs : OneAt2 psA j (.ofShape { as, from_ := regA rn, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      XW lc v m m' := by
  have hl := F.lowered
  have hA := F.addr
  have hnp := extOp?_ne_phi he
  have hmov := (extOp?_movMem he).1
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_ext hl htemp he hs
  rw [arr1 hsz1 ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  rw [write_reg hvh hcv]
  have ht := cls_ne_bool hcv h8
  refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor (valRel_ext hA hxv hxf hcv ht he hw)
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0 hok => ?_)).imp
    fun m' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, hsi, .inr ⟨r, kd, _, hvh, hor, h4⟩⟩
  obtain ⟨has, hf, -, ht', -⟩ := Shape.ok_eq hok
  rw [progStep_ext hkn hkd (nextAddr_pcAt F.nodup hk0) (by rw [has]; exact hmov) hf ht', wX_pc]
    <;> rfl

/-- `AND $k, Rn, Rd`, `LSL $k, Rn, Rd`, `LSR $k, Rn, Rd`. -/
theorem g3_aluK (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {ca c : Nat} {rn rd : Int}
    (hop : v.op = .ARM64ANDconst ∧ as = .AND ∨ v.op = .ARM64SLLconst ∧ as = .LSL ∨
      v.op = .ARM64SRLconst ∧ as = .LSR)
    (hsz1 : v.args.size = 1) (hao : argObj lc v 0 = .ok (ca, rn)) (hro : resObj lc v = .ok (c, rd))
    (h8 : 8 ≤ c) (hca : c ≤ ca) (hsr : v.op = .ARM64SRLconst → ca = 64)
    (hk : v.op ≠ .ARM64ANDconst → 0 ≤ v.auxInt.toInt ∧ v.auxInt.toInt < 64)
    (hvs : OneAt2 psA j
      (.ofShape { as, from_ := constA v.auxInt.toInt, reg := rn, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      XW lc v m m' := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rcases hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_pure3 hl htemp
    (by rcases hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]) hs
  rw [arr1 hsz1 ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  rw [write_reg hvh hcv]
  have ht := cls_ne_bool hcv h8
  have hKL := knext_set hK hnp hvh hcv
  rcases hop with ⟨hop, rfl⟩ | ⟨hop, rfl⟩ | ⟨hop, rfl⟩
  · rw [hop]
    refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor (valRel_andK hA hxv hxf hcv hca ht)
      (fits_retypeL hcv _) hKL (fun k0 hk0 hok => ?_)).imp
      fun m' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, hsi, .inr ⟨r, kd, _, hvh, hor, h4⟩⟩
    obtain ⟨has, hf, hr, ht', -⟩ := Shape.ok_eq hok
    rw [progStep_andK hkn hkd (nextAddr_pcAt F.nodup hk0) has hf hr ht', wX_pc] <;> rfl
  · have hk0 := (hk (by rw [hop]; nofun)).1
    rw [hop]
    refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor (valRel_lslK hA hxv hxf hcv hca ht)
      (fits_retypeL hcv _) hKL (fun k0 hk0' hok => ?_)).imp
      fun m' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, hsi, .inr ⟨r, kd, _, hvh, hor, h4⟩⟩
    obtain ⟨has, hf, hr, ht', -⟩ := Shape.ok_eq hok
    rw [progStep_lslK hkn hkd hk0 (nextAddr_pcAt F.nodup hk0') has hf hr ht', wX_pc] <;> rfl
  · have hk0 := (hk (by rw [hop]; nofun)).1
    have h64 := hsr hop
    subst h64
    rw [hop]
    refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor (valRel_lsrK hA hxv hxf hcv ht)
      (fits_retypeL hcv _) hKL (fun k0 hk0' hok => ?_)).imp
      fun m' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, hsi, .inr ⟨r, kd, _, hvh, hor, h4⟩⟩
    obtain ⟨has, hf, hr, ht', -⟩ := Shape.ok_eq hok
    rw [progStep_lsrK hkn hkd hk0 (nextAddr_pcAt F.nodup hk0') has hf hr ht', wX_pc] <;> rfl

/-- `UBFX $lsb, Rn, $width, Rd`. -/
theorem g3_ubfx (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {ca c : Nat} {rn rd : Int} {pat : Pat}
    (hop : v.op = .ARM64UBFX) (hsz1 : v.args.size = 1) (hk0 : 0 ≤ v.auxInt.toInt)
    (hk16 : v.auxInt.toInt < 2 ^ 16) (hao : argObj lc v 0 = .ok (ca, rn))
    (hro : resObj lc v = .ok (c, rd)) (h8 : 8 ≤ c) (hw0 : 0 < v.auxInt.toInt % 256)
    (hlw : v.auxInt.toInt / 256 + v.auxInt.toInt % 256 ≤ ca)
    (hpat : ∀ p, pat.ok p = true → p.as = .UBFX ∧ p.from_ = constA (v.auxInt.toInt / 256) ∧
      p.reg = rn ∧ p.to = regA rd ∧ p.scond = 0 ∧ p.regTo2 = 0 ∧
      ∃ x, p.rest = #[(x, constA (v.auxInt.toInt % 256))])
    (hvs : OneAt2 psA j pat j') (htemp : (lc.temps[v.id]?).join = none)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      XW lc v m m' := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_pure3 hl htemp (by simp [hop]) hs
  rw [arr1 hsz1 ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  rw [write_reg hvh hcv, hop]
  have ht := cls_ne_bool hcv h8
  refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_ubfx hA hxv hxf hk0 hlw hcv ht)
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, hsi, .inr ⟨r, kd, _, hvh, hor, h4⟩⟩
  obtain ⟨has, hf, hr, ht', hsc, h2, xr, hrest⟩ := hpat _ hok
  rw [progStep_ubfx hkn hkd (by omega) (by omega) (by omega) (nextAddr_pcAt F.nodup hk0') has hf hr
    ht' hrest, wX_pc] <;> rfl

/-- `CMPW Rm, Rn`. -/
theorem g3_cmpw (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {ca cb : Nat} {rn rm : Int}
    (hop : v.op = .ARM64CMPW) (hsz2 : v.args.size = 2) (hfl : (lc.ty v.id).isFlags = true)
    (hhn : lc.home v.id = none) (hao : argObj lc v 0 = .ok (ca, rn))
    (hbo : argObj lc v 1 = .ok (cb, rm)) (hca : 32 ≤ ca) (hcb : 32 ≤ cb)
    (hvs : OneAt2 psA j (.ofShape { as := .CMPW, from_ := regA rm, reg := rn }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      m'.x = m.x := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hbo
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨km, hkm, rfl, hkkm⟩ := objOf?_some hor1
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨y, hy, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkkm
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_pure3 hl htemp (by simp [hop]) hs
  rw [arr2 hsz2 ha0 ha1] at hargv
  obtain rfl := mapM_res_two hargv hx hy
  rw [write_flags hhn hfl, hop, isFlags_eq hfl]
  exact (op_flags F hm hinv hj hj' hvs (flagsRel_cmpw_retypeL hA hxv hyv hxf hyf hca hcb)
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)) (fun k hk hok => by
      obtain ⟨has, hf, hr, -, -⟩ := Shape.ok_eq hok
      rw [progStep_cmpwReg hkn hkm (nextAddr_pcAt F.nodup hk) has hf hr] <;> rfl)).imp
    fun m' ⟨h1, h2, h3, _, h5⟩ => ⟨h1, h2, h3, hsi, h5⟩

/-- `CMPW $k, Rn`. -/
theorem g3_cmpwK (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {ca : Nat} {rn : Int}
    (hop : v.op = .ARM64CMPWconst) (hsz1 : v.args.size = 1) (hfl : (lc.ty v.id).isFlags = true)
    (hhn : lc.home v.id = none) (hao : argObj lc v 0 = .ok (ca, rn)) (hca : 32 ≤ ca)
    (hvs : OneAt2 psA j (.ofShape { as := .CMPW, from_ := constA v.auxInt.toInt, reg := rn }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      m'.x = m.x := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_pure3 hl htemp (by simp [hop]) hs
  rw [arr1 hsz1 ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  rw [write_flags hhn hfl, hop, isFlags_eq hfl]
  exact (op_flags F hm hinv hj hj' hvs (flagsRel_cmpwK_retypeL hA hxv hxf hca)
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)) (fun k hk hok => by
      obtain ⟨has, hf, hr, -, -⟩ := Shape.ok_eq hok
      rw [progStep_cmpwConst hkn (nextAddr_pcAt F.nodup hk) has hf hr] <;> rfl)).imp
    fun m' ⟨h1, h2, h3, _, h5⟩ => ⟨h1, h2, h3, hsi, h5⟩

/-- A value of no home and a register shape writes nothing. -/
theorem write_none_cls {id : ID} {x : Val} (hh : lc.home id = none)
    (hc : (cls (lc.ty id)).isSome = true) : s.write lc id x = s := by
  unfold LocState.write
  cases hT : lc.ty id <;> rw [hT] at hc <;> simp_all [Gen.Check.cls, Ty.isFlags]

/-- Writing a Go register without machine register (`SB`) keeps `LocMatch`. -/
theorem locMatch_setReg_none (h : LocMatch E s b i m) {r : Nat} {x : Val}
    (hx : objX? r = none) (hv : objV? r = none) : LocMatch E (s.setReg r x) b i m := by
  refine { h with regs := ?_ }
  intro r' v' hv'
  simp only [LocState.setReg] at hv'
  by_cases hrr : r' = r
  · subst hrr
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rw [hx] at hk; cases hk
    · rw [hv] at hk; cases hk
  · split at hv'
    · rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm hrr)] at hv'
      exact h.regs r' v' hv'
    · exact h.regs r' v' hv'

/-- `SB`: no code; it writes no machine register. -/
theorem g3_sb (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    (hop : v.op = .SB) (hcl : (cls (lc.ty v.id)).isSome = true)
    (hh : lc.home v.id = none ∨ lc.home v.id = some (.reg sbReg)) (hvs : j' = j)
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' := by
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨c, hcv⟩ := Option.isSome_iff_exists.1 hcl
  obtain ⟨x, rfl⟩ := stepLoc_sb F.lowered htemp hop hs
  have hpc : E.pcOf b (i + 1) = m.pc := by rw [hj', hvs, ← hj, hm.pc]
  rcases hh with hh | hh
  · rw [write_none_cls hh hcl]
    exact ⟨m, .refl, locMatch_pc hm hpc,
      hinv.mono (knext_same hK (Or.inr fun _ _ => by rw [hh]; nofun)), hsi⟩
  · rw [write_reg hh hcv]
    exact ⟨m, .refl, locMatch_pc (locMatch_setReg_none hm (by decide) (by decide)) hpc,
      (core_setReg hinv (fits_retypeL hcv _)).mono (knext_set hK hnp hh hcv), hsi⟩

end Cases

/-! ## The register and bit tests -/

/-- A 32-bit register test (`ZW`/`NZW`: `CBZW`/`CBNZW`) or a bit test (`TBZ`/`TBNZ`) that goes
to a successor, from the facts `Cx.termG3` gives about its block (`TermOK3`); the machine's X
registers are kept. -/
theorem term_test {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int}
    {ret : BitVec 64} {E : MatchEnv} {cx : Cx} {P : BitVec 64 → Prop} {bid : ID} {blk : Block}
    {e : Edge} {s s' : LocState} {m : MState} {e' : Nat} {next : Option (ID × Nat)}
    {asm inv : As} (F : Facts cx.lc sym text az ez cx.ps.toList ret E) (hst : Starts cx text E)
    (hbr : testBr blk.kind = some (asm, inv)) (hterm : TermOK3 cx blk e' next asm inv)
    (hnext : ∀ n k, next = some (n, k) → cx.startIdx n = .ok k)
    (hpcT : E.pcOf bid blk.values.size = pcAt text cx.ps.toList e')
    (hm : LocMatch E s bid blk.values.size m) {K : Nat → Option Nat} (hinv : CoreInv E.ι P K s osp)
    (hK : ∀ c r cc, blk.controls[0]? = some c → cx.lc.home c = some (.reg r) → r ≠ zeroReg →
      cls (cx.lc.ty c) = some cc → K r = some cc)
    (ht : stepTermLoc cx.lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H (Link.byId sym text az ez cx.ps.toList) cx.ps.toList ret m m' ∧
      LocMatch E s' e.b 0 m' ∧ (∃ R, s' = { s with fr := { s.fr with regs := R } }) ∧
      e ∈ blk.succs.toList ∧ e.b ∈ cx.lc.ctx.f.blocks.toList ∧ m'.x = m.x := by
  have hl := F.lowered
  have hA := F.addr
  have hm0 : ({ m with pc := pcAt text cx.ps.toList e' } : MState) = m := by
    rw [← hpcT, ← hm.pc]
  have hsucc := hterm.succs
  obtain ⟨e0, e1, c, r, o, cc, hs01, hcs, hh, ho, hcl, hzw, htb⟩ := hterm.shape
  have he0 : e0 ∈ blk.succs.toList := by simp [hs01]
  have he1 : e1 ∈ blk.succs.toList := by simp [hs01]
  obtain ⟨x, R, hx, hR, hctl, hn⟩ := stepTermLoc_one hcs ht
  have harm : blk.kind.isArm64 = true ∧ blk.kind ≠ .ARM64JUMPTABLE := by
    rcases testBr_spec hbr with ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ <;> rw [hk] <;>
      exact ⟨rfl, by decide⟩
  obtain ⟨y, t, hy, htk, hsn⟩ := stepTermL_arm harm.1 harm.2 hn
  obtain rfl := (hctl y hy).symm
  have hge := succ_two hs01 hsn
  cases hge
  obtain ⟨kn, hk32, rfl, hkk⟩ := objOf?_some ho
  obtain ⟨x', hx', hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hh hcl (fun hr => hK c r cc (by simp [hcs]) hh hr hcl) hkk
  have hxx : x = x' := by
    rcases control_cases hx with h | ⟨xs, rfl⟩
    · rw [hx'] at h; exact (Res.ok.inj h).symm
    · rw [lmode_retype hl, retypeL_tuple_reg hcl] at htk
      rcases testBr_spec hbr with ⟨hz, -⟩ | ⟨hz, -⟩ | ⟨hz, -⟩ | ⟨hz, -⟩ <;>
        simp [hz, Arm64.taken, Arm64.reg32, Arm64.reg] at htk
  subst hxx
  have hmem : (if t then e0 else e1) ∈ blk.succs.toList := by cases t <;> simp [he0, he1]
  subst hR
  refine ⟨_, ?_, locMatch_jump hm, ⟨R, rfl⟩, hmem, hsucc _ hmem, rfl⟩
  rw [← hm0]
  have hrx : ∀ k', ({ m with pc := pcAt text cx.ps.toList k' } : MState).rX (BitVec.ofNat 5 kn) =
      m.rX (BitVec.ofNat 5 kn) := fun _ => rfl
  have b1 : (As.CBZW == As.CBZW) = true := by decide
  have b2 : (As.CBNZW == As.CBZW) = false := by decide
  have b3 : (As.TBNZ == As.TBNZ) = true := by decide
  have b4 : (As.TBZ == As.TBNZ) = false := by decide
  rcases testBr_spec hbr with ⟨hz, rfl, rfl⟩ | ⟨hz, rfl, rfl⟩ | ⟨hz, rfl, rfl⟩ | ⟨hz, rfl, rfl⟩
  · -- `ZW`: `CBZW`, taken when the low word is zero
    obtain ⟨hw, htwo⟩ := hzw (.inl hz)
    rw [hz] at htk
    have htv := taken_zw hA hxv hxf hw htk
    rcases htwo with h2 | h2
    · have := two_path (H := H) (d := t) F hst hnext (hsucc e0 he0) (hsucc e1 he1) h2 m
        (fun tid T k' hk _ hT hok => by
          obtain ⟨has, hf, -, hto, -⟩ := Shape.ok_eq hok
          rw [progStep_cbzw hk32 (nextAddr_pcAt F.nodup hk) (Or.inl has) hf hto hT, hrx, ← htv,
            show cx.ps.toList[k'].as = As.CBZW from has, b1]
          all_goals cases t <;> rfl)
      cases t <;> simpa using this
    · have := two_path (H := H) (d := !t) F hst hnext (hsucc e1 he1) (hsucc e0 he0) h2 m
        (fun tid T k' hk _ hT hok => by
          obtain ⟨has, hf, -, hto, -⟩ := Shape.ok_eq hok
          rw [progStep_cbzw hk32 (nextAddr_pcAt F.nodup hk) (Or.inr has) hf hto hT, hrx, ← htv,
            show cx.ps.toList[k'].as = As.CBNZW from has, b2]
          cases t <;> rfl)
      cases t <;> simpa using this
  · -- `NZW`: `CBNZW`, taken when the low word is not zero
    obtain ⟨hw, htwo⟩ := hzw (.inr hz)
    rw [hz] at htk
    have htv := taken_nzw hA hxv hxf hw htk
    have hzt : ((m.rX (BitVec.ofNat 5 kn)).setWidth 32 == 0) = !t := by rw [htv, Bool.not_not]
    rcases htwo with h2 | h2
    · have := two_path (H := H) (d := t) F hst hnext (hsucc e0 he0) (hsucc e1 he1) h2 m
        (fun tid T k' hk _ hT hok => by
          obtain ⟨has, hf, -, hto, -⟩ := Shape.ok_eq hok
          rw [progStep_cbzw hk32 (nextAddr_pcAt F.nodup hk) (Or.inr has) hf hto hT, hrx, hzt,
            show cx.ps.toList[k'].as = As.CBNZW from has, b2]
          cases t <;> rfl)
      cases t <;> simpa using this
    · have := two_path (H := H) (d := !t) F hst hnext (hsucc e1 he1) (hsucc e0 he0) h2 m
        (fun tid T k' hk _ hT hok => by
          obtain ⟨has, hf, -, hto, -⟩ := Shape.ok_eq hok
          rw [progStep_cbzw hk32 (nextAddr_pcAt F.nodup hk) (Or.inl has) hf hto hT, hrx, hzt,
            show cx.ps.toList[k'].as = As.CBZW from has, b1]
          all_goals cases t <;> rfl)
      cases t <;> simpa using this
  · -- `TBZ`: taken when the bit is clear
    obtain ⟨h0, hbit, htwo⟩ := htb (.inl hz)
    rw [hz] at htk
    have htv := taken_tbz hA hxv hxf (by omega) htk
    have hzt : (m.rX (BitVec.ofNat 5 kn)).getLsbD blk.auxInt.toInt.toNat = !t := by
      rw [htv, Bool.not_not]
    rcases htwo with h2 | h2
    · have := two_path (H := H) (d := t) F hst hnext (hsucc e0 he0) (hsucc e1 he1) h2 m
        (fun tid T k' hk _ hT hok => by
          obtain ⟨has, hf, hr, hto, -⟩ := Shape.ok_eq hok
          rw [progStep_tbz hk32 (nextAddr_pcAt F.nodup hk) (Or.inl has) hf hr hto hT, hrx, hzt,
            show cx.ps.toList[k'].as = As.TBZ from has, b4]
          cases t <;> rfl)
      cases t <;> simpa using this
    · have := two_path (H := H) (d := !t) F hst hnext (hsucc e1 he1) (hsucc e0 he0) h2 m
        (fun tid T k' hk _ hT hok => by
          obtain ⟨has, hf, hr, hto, -⟩ := Shape.ok_eq hok
          rw [progStep_tbz hk32 (nextAddr_pcAt F.nodup hk) (Or.inr has) hf hr hto hT, hrx, hzt,
            show cx.ps.toList[k'].as = As.TBNZ from has, b3]
          all_goals cases t <;> rfl)
      cases t <;> simpa using this
  · -- `TBNZ`: taken when the bit is set
    obtain ⟨h0, hbit, htwo⟩ := htb (.inr hz)
    rw [hz] at htk
    have htv := taken_tbnz hA hxv hxf (by omega) htk
    rcases htwo with h2 | h2
    · have := two_path (H := H) (d := t) F hst hnext (hsucc e0 he0) (hsucc e1 he1) h2 m
        (fun tid T k' hk _ hT hok => by
          obtain ⟨has, hf, hr, hto, -⟩ := Shape.ok_eq hok
          rw [progStep_tbz hk32 (nextAddr_pcAt F.nodup hk) (Or.inr has) hf hr hto hT, hrx, ← htv,
            show cx.ps.toList[k'].as = As.TBNZ from has, b3]
          all_goals cases t <;> rfl)
      cases t <;> simpa using this
    · have := two_path (H := H) (d := !t) F hst hnext (hsucc e1 he1) (hsucc e0 he0) h2 m
        (fun tid T k' hk _ hT hok => by
          obtain ⟨has, hf, hr, hto, -⟩ := Shape.ok_eq hok
          rw [progStep_tbz hk32 (nextAddr_pcAt F.nodup hk) (Or.inl has) hf hr hto hT, hrx, ← htv,
            show cx.ps.toList[k'].as = As.TBZ from has, b4]
          cases t <;> rfl)
      cases t <;> simpa using this

/-! ## Static facts of an accepted function -/

/-- A register home G3 handles (`homeOK3`) other than `ZERO` holds a value with a class. -/
theorem clsReg_of_home3 {lc : LocCtx} (h : ∀ i, homeOK3 lc i = true) :
    ∀ i r, lc.home i = some (.reg r) → r ≠ zeroReg → (cls (lc.ty i)).isSome = true := by
  intro i r hh hr
  have := h i
  simp only [homeOK3, hh, Bool.or_eq_true, beq_iff_eq, hr, false_or] at this
  exact this

/-- A call's home is no slot (`homeOK3`). -/
theorem call_not_slot3 {lc : LocCtx} {c : ID} {u : Value} (h : ∀ i, homeOK3 lc i = true)
    (hu : lc.ctx.f.value? c = some u) (hcop : u.op = .ARM64CALLstatic) :
    ∀ k, lc.home c ≠ some (.slot k) := by
  intro k hk
  have := h c
  simp [homeOK3, homeOK2, hk, hu, hcop] at this

theorem callTy_len {n : Nat} {t : Ty} (h : callTy n t = true) : n ≤ (tupleTys t).length := by
  cases t with
  | tuple ts =>
    simp only [callTy, Bool.and_eq_true, beq_iff_eq] at h
    simp only [tupleTys]
    omega
  | _ => simp [callTy] at h

/-- The home of value `id` is none, a register, a slot or the empty `results` home: the value
writes no register but its own (`knext_kStep`). -/
def HomeSimple (lc : LocCtx) (id : ID) : Prop :=
  ∀ l, lc.home id = some l → (∃ r, l = .reg r) ∨ (∃ k, l = .slot k) ∨ l = .results #[]

theorem HomeSimple.noRegs {lc : LocCtx} {id : ID} (h : HomeSimple lc id) :
    (∀ rs, lc.home id = some (.results rs) → rs = #[]) ∧ ∀ a b, lc.home id ≠ some (.pair a b) := by
  refine ⟨fun rs hrs => ?_, fun a b hab => ?_⟩
  · rcases h _ hrs with ⟨r, h⟩ | ⟨k, h⟩ | h <;> cases h
    rfl
  · rcases h _ hab with ⟨r, h⟩ | ⟨k, h⟩ | h <;> cases h

theorem hs_none {lc : LocCtx} {id : ID} (hh : lc.home id = none) : HomeSimple lc id :=
  fun l hl => by rw [hh] at hl; cases hl

theorem hs_reg {lc : LocCtx} {id r : ID} (hh : lc.home id = some (.reg r)) : HomeSimple lc id :=
  fun l hl => by rw [hh] at hl; cases hl; exact .inl ⟨r, rfl⟩

theorem hs_slot {lc : LocCtx} {id : ID} {k : SlotKey} (hh : lc.home id = some (.slot k)) :
    HomeSimple lc id :=
  fun l hl => by rw [hh] at hl; cases hl; exact .inr (.inl ⟨k, rfl⟩)

theorem hs_res {lc : LocCtx} {v : Value} {c : Nat} {o : Int} (hro : resObj lc v = .ok (c, o)) :
    HomeSimple lc v.id := by
  obtain ⟨r, hvh, -⟩ := resObj_spec hro
  exact hs_reg hvh

/-- A value of G1 other than a `Phi` writes no register but its own. -/
theorem vk_noRes {lc : LocCtx} {v : Value} {kd : VKind} (h : VK lc v kd) (hnp : v.op ≠ .Phi) :
    HomeSimple lc v.id := by
  cases h with
  | phi hop _ => exact absurd hop hnp
  | zero _ _ hh _ => exact hs_reg hh
  | inl _ hh _ => exact hs_none hh
  | copyMem _ _ _ _ hh => exact hs_none hh
  | copySame _ _ _ _ hro => exact hs_res hro
  | copyMov _ _ _ _ hro _ => exact hs_res hro
  | result _ hh _ _ _ =>
    rcases hh with hh | hh
    · exact hs_none hh
    · exact fun l hl => by rw [hh] at hl; cases hl; exact .inr (.inr rfl)
  | movConst _ _ hro _ => exact hs_res hro
  | alu _ _ _ _ hro _ _ _ => exact hs_res hro
  | aluK _ _ _ hro _ _ => exact hs_res hro
  | cmp _ _ _ hh _ _ => exact hs_none hh
  | cmpK _ _ _ hh _ => exact hs_none hh
  | load _ _ _ _ _ hro _ => exact hs_res hro
  | store _ _ _ _ hh _ _ _ _ => exact hs_none hh

/-- A value of G3 other than a call or a `Phi` writes no register but its own. -/
theorem vk3_noRes {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK3 lc g v kd)
    (hnc : v.op ≠ .ARM64CALLstatic) (hnp : v.op ≠ .Phi) : HomeSimple lc v.id := by
  cases h with
  | g2 _ _ h2 =>
    cases h2 with
    | g1 _ _ _ _ _ h1 => exact vk_noRes h1 hnp
    | call hop => exact absurd hop hnc
    | selMem _ _ _ _ _ _ _ _ _ hh _ => exact hs_none hh
    | selReg _ _ _ _ _ _ _ _ _ hh => exact hs_reg hh
    | addr _ _ _ _ _ _ hro _ => exact hs_res hro
    | spill _ hh => exact hs_slot hh
    | reload _ _ _ _ _ _ hro _ => exact hs_res hro
  | load _ _ _ _ _ hro => exact hs_res hro
  | store _ _ _ _ hh => exact hs_none hh
  | sb _ _ _ hh =>
    rcases hh with hh | hh
    · exact hs_none hh
    · exact hs_reg hh
  | ext _ _ _ hro => exact hs_res hro
  | aluK _ _ _ hro => exact hs_res hro
  | ubfx _ _ _ _ _ hro => exact hs_res hro
  | cmpw _ _ _ hh => exact hs_none hh
  | cmpwK _ _ _ hh => exact hs_none hh

/-! ## The theorems -/

/-- One value of G3's kinds (`VK3`) emitted at the Progs from `j` to `j'`, run from a state at the
class map `K` that gives every register the value reads its class (`kReads`): matched by `runProg`
steps to a state related before the next value, at the class map after it (`kStep`), under an
activation `E'` that extends `E`'s injection (by the callee's, at a call). `g3_value` and G4's
`g4_value` (`G4.lean`) apply it to the values of their slices. -/
theorem vk3_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2}
    (hE : G2Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E)
    (hns : ∀ c u, lc.ctx.f.value? c = some u → u.op = .ARM64CALLstatic →
      ∀ k, lc.home c ≠ some (.slot k))
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK3 lc g v kd)
    (hvs : VStep2 ps kd j j')
    (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s osp) (hpre : G3Pre lc s v)
    (hcall : CallOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G2Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp := by
  have hE0 := hE
  obtain ⟨hlcE, -, -, -, -, hglob, hsyms, hcalls, hslot, hextra, hF⟩ := hE
  have hsz := slot_sizes hlcE hcf hinv.slots
  have hR := kread_of_reads hreads
  have same : ∀ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E s' bid (i + 1) m' ∧ CoreInv E.ι (StkAt E) (kStep lc K v).get s' osp ∧
      SlotInv lc s' →
      ∃ E' m', E.Extends E' ∧ G2Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
        PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
        LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp :=
    fun m' ⟨h1, h2, h3, h4⟩ => ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE0, h1, h2, ⟨h3, h4⟩⟩
  have hK : v.op ≠ .ARM64CALLstatic → KNext lc v K.get (kStep lc K v).get :=
    fun hnc => knext_kStep fun hnp => (vk3_noRes hVK hnc hnp).noRegs
  cases hVK with
  | g2 hops hnodup hVK2 =>
    cases hVK2 with
    | g1 hnc _ _ _ _ hvk =>
      have haux : v.op = .ARM64MOVDload → v.aux = none := by
        intro hop
        rcases hops with ⟨hl0, -⟩ | ⟨-, hx⟩
        · rw [hop] at hl0; simp [loadOp?] at hl0
        · exact hx
      obtain ⟨m', h1, h2, h3, h4, -⟩ := g2_g1 (H := H) F hF hsz hm hinv.core hinv.slots hj hj'
        hvs hvk htemp (hpre.g1 haux) hR (hK hnc) hs
      exact same m' ⟨h1, h2, h3, h4⟩
    | call hop hcall' hcr _ _ _ h16 hlen hargs hres hct hrr hpat =>
      have hframed : E.framed = true := by
        cases hfr : E.framed
        · exact absurd hop (hcalls hfr id v hv)
        · rfl
      have hnp : v.op ≠ .Phi := by rw [hop]; nofun
      obtain ⟨ι', hext', hA', m', hstar, hlm, hcore', hsl'⟩ := g2_call (H := H) F hF hlcE hcf
        hframed hsyms hm hinv.core hinv.slots hR hj hj' hop hcall' hcr h16 hlen hargs hres hct
        (kcall_kStep hnp hres (hnodup hop _ _ _ _ _ hcall' hcr) (callTy_len hct)) hpat hvs htemp
        hs hcall
      exact ⟨_, m', ⟨rfl, hext'⟩, hE0.extend hext' hA', hstar, hlm, ⟨hcore', hsl'⟩⟩
    | selMem hop hsz1 hc0 hu hcop hts hct hpos hmt hnone hidx =>
      obtain ⟨m', h⟩ := g2_selMem (H := H) F hm hinv.core hinv.slots
        (hK (by rw [hop]; nofun)) hj hj' hop hsz1 hc0 hu (hns _ _ hu hcop) hts hct
        hpos hmt hnone hidx hvs htemp hs
      exact same m' h
    | selReg hop hsz1 hc0 hu hcop hts hct hpos _ hvh hr16 hlt' hcl hhc hrs =>
      obtain ⟨m', h⟩ := g2_selReg (H := H) F hm hinv.core hinv.slots
        (hK (by rw [hop]; nofun)) hj hj' hop hsz1 hc0 hu (hns _ _ hu hcop) hts hct
        hpos hvh hr16 (fun c0 hc0' => ksel_of_reads hreads hop hc0 hts hhc hrs (hcl.trans hc0'))
        hlt' hcl hhc hrs hvs htemp hs
      exact same m' h
    | addr hop hsz1 ha0 _ hx hsym hro hpat =>
      obtain ⟨m', h1, h2, h3, h4, -⟩ := g2_addr (H := H) F (fun y name abi h => hglob y name abi h)
        hm hinv.core hinv.slots (hK (by rw [hop]; nofun)) hj hj' hop hsz1 ha0 hx hsym hro hpat hvs
        htemp hs
      exact same m' ⟨h1, h2, h3, h4⟩
    | spill hop hh hso hsz1 hcv hao hpat =>
      obtain ⟨m', h1, h2, h3, h4, -⟩ := g2_spill (H := H) F hF hlcE hcf hslot hextra hm hinv.core
        hinv.slots hR (hK (by rw [hop]; nofun)) hj hj' hop hh hso hsz1 hcv hao hpat hvs htemp hs
      exact same m' ⟨h1, h2, h3, h4⟩
    | reload hop hsz1 ha0 hah hso hca hro hpat =>
      obtain ⟨m', h1, h2, h3, h4, -⟩ := g2_reload (H := H) F hF hlcE hcf hslot hm hinv.core
        hinv.slots (hK (by rw [hop]; nofun)) hj hj' hop hsz1 ha0 hah hso hca hro hpat hvs htemp hs
      exact same m' ⟨h1, h2, h3, h4⟩
  | load hop _ hsz2 hacc hma hro hcw hpat =>
    have hnc : v.op ≠ .ARM64CALLstatic := by
      intro h; rw [h] at hop; simp [loadOp?, narrowLoad?] at hop
    obtain ⟨m', h⟩ := g3_load (H := H) F (fun y name abi h => hglob y name abi h) hm hinv.core
      hinv.slots hR (hK hnc) hpre hj hj' hop hsz2 hacc hma hro hcw hpat hvs htemp hs
    exact same m' h
  | store hop _ hsz3 hmt hhn hacc hso hma hcw hpat =>
    have hnc : v.op ≠ .ARM64CALLstatic := by
      intro h; rw [h] at hop; simp [storeOp?, narrowStore?] at hop
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g3_store (H := H) F hF hsz
      (fun y name abi h => hglob y name abi h) hm hinv.core hinv.slots hR (hK hnc) hj hj' hop hsz3
      hmt hhn hacc hso hma hcw hpat hvs htemp hs
    exact same m' ⟨h1, h2, h3, h4⟩
  | sb hop _ hcl hh =>
    obtain ⟨m', h⟩ := g3_sb (H := H) F hm hinv.core hinv.slots (hK (by rw [hop]; nofun)) hj hj'
      hop hcl hh hvs htemp hs
    exact same m' h
  | ext he hsz1 hao hro hw h8 =>
    have hnc : v.op ≠ .ARM64CALLstatic := by
      intro h; rw [h] at he; simp [extOp?] at he
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g3_ext (H := H) F hm hinv.core hinv.slots hR (hK hnc) hj hj'
      he hsz1 hao hro hw h8 hvs htemp hs
    exact same m' ⟨h1, h2, h3, h4⟩
  | aluK hop hsz1 hao hro h8 hca hsr hkk =>
    have hnc : v.op ≠ .ARM64CALLstatic := by
      rcases hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g3_aluK (H := H) F hm hinv.core hinv.slots hR (hK hnc) hj
      hj' hop hsz1 hao hro h8 hca hsr hkk hvs htemp hs
    exact same m' ⟨h1, h2, h3, h4⟩
  | ubfx hop hsz1 hk0 hk16 hao hro h8 hw0 hlw hpat =>
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g3_ubfx (H := H) F hm hinv.core hinv.slots hR
      (hK (by rw [hop]; nofun)) hj hj' hop hsz1 hk0 hk16 hao hro h8 hw0 hlw hpat hvs htemp hs
    exact same m' ⟨h1, h2, h3, h4⟩
  | cmpw hop hsz2 hfl hhn hao hbo hca hcb =>
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g3_cmpw (H := H) F hm hinv.core hinv.slots hR
      (hK (by rw [hop]; nofun)) hj hj' hop hsz2 hfl hhn hao hbo hca hcb hvs htemp hs
    exact same m' ⟨h1, h2, h3, h4⟩
  | cmpwK hop hsz1 hfl hhn hao hca =>
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g3_cmpwK (H := H) F hm hinv.core hinv.slots hR
      (hK (by rw [hop]; nofun)) hj hj' hop hsz1 hfl hhn hao hca hvs htemp hs
    exact same m' ⟨h1, h2, h3, h4⟩

/-- **G3, values.** A value (not an entry value) of a function `checkG3` accepted with the class
table `kt`, run by `runLoc` from a state related by `LocMatch` to a machine state whose registers
hold values of the classes the table gives before the value (`G3Inv` at `kAt … i`), is matched by
`runProg` steps of genssa's P0 Progs to a state related before the next value, with the registers
at the classes before the next value, under an activation `E'` that extends `E`'s injection (by
the callee's, at a call) and is again a `G2Env`. At a static call the callee's behaviour is the
trusted contract `CallOK`. -/
theorem g3_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG3 lc ps bstart g = .ok (tab, kt)) (hE : G2Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp3 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hpre : G3Pre lc s v)
    (hcall : CallOK H E g L lc s s' v m) (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G2Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' := by
  have hE0 := hE
  obtain ⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome3, hcf, hk, hlt, hnd, hblocks⟩ := checkG3_spec hc
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
  obtain ⟨htemp, hVK⟩ := vkind3_spec hkd hen
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home3 hhome3, hnd, hlt, hret, hA⟩
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  rw [kAt_succ hi hv]
  exact vk3_step hE0 F (fun _ _ hu hcop => call_not_slot3 hhome3 hu hcop) hcf hv hVK hvs htemp hj
    hj' hreads hm hinv hpre hcall hs

/-- A terminator of a function whose blocks `c.blocks` accepted with G3's terminator check
(`Cx.termG3`) and whose class table `kt` passes `checkK`, from a state whose registers hold the
classes of the block's end: matched by `runProg` steps to a state related before the successor's
first value, with the registers at the successor's classes; the successor is one of the block's
and the machine's X registers are kept. `termK_step` drops the last two facts. -/
theorem termK_stepX {H : Hooks} {c : Cx2} {sym : Nat → BitVec 64} {text : BitVec 64}
    {az ez : Int} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv} {bid : ID}
    {blk : Block}
    {e : Edge} {s s' : LocState} {m : MState}
    (hpcOf : E.pcOf = pcOfTab text c.cx.ps.toList tab)
    (F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E) (htm : c.tm = c.cx.termG3)
    (hk : checkK c.cx.lc kt = .ok ()) (hblocks : c.blocks c.cx.lc.ctx.f.blocks.toList = .ok tab)
    (hbid : bid ∈ c.cx.lc.ctx.f.blocks.toList) (hb : c.cx.lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E c.cx.lc (kAt c.cx.lc kt bid blk blk.values.size) s osp)
    (hpre : G1TermPre c.cx.lc s blk) (ht : stepTermLoc c.cx.lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H (Link.byId sym text az ez c.cx.ps.toList) c.cx.ps.toList ret m m' ∧
      LocMatch E s' e.b 0 m' ∧ G3Inv E c.cx.lc (kt.at e.b) s' osp ∧
      e.b ∈ c.cx.lc.ctx.f.blocks.toList ∧ e ∈ blk.succs.toList ∧ m'.x = m.x := by
  obtain ⟨b, j, js, e', next, hb', -, hvals, hterm, hnext, hrow⟩ :=
    Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  rw [htm] at hterm
  obtain ⟨hlen, -, -⟩ := Cx2.values_spec hvals
  have hpcT : E.pcOf bid blk.values.size = pcAt text c.cx.ps.toList e' := by
    rw [hpcOf]
    simp only [pcOfTab, hrow, Option.getD_some]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [hlen])]
    simp [hlen]
  obtain ⟨-, hkb⟩ := checkK_spec hk
  obtain ⟨-, hctl, hedge⟩ := hkb bid hbid blk hb
  have hK := kctl_of hctl
  have hst := start_of_mem2 hblocks hpcOf
  have fin : ∀ m', PStar H (Link.byId sym text az ez c.cx.ps.toList) c.cx.ps.toList ret m m' ∧
      LocMatch E s' e.b 0 m' ∧ (∃ R, s' = { s with fr := { s.fr with regs := R } }) ∧
      e ∈ blk.succs.toList ∧ e.b ∈ c.cx.lc.ctx.f.blocks.toList ∧ m'.x = m.x →
      ∃ m', PStar H (Link.byId sym text az ez c.cx.ps.toList) c.cx.ps.toList ret m m' ∧
        LocMatch E s' e.b 0 m' ∧ G3Inv E c.cx.lc (kt.at e.b) s' osp ∧
        e.b ∈ c.cx.lc.ctx.f.blocks.toList ∧ e ∈ blk.succs.toList ∧ m'.x = m.x := by
    rintro m' ⟨hstar, hlm, ⟨R, rfl⟩, hmem, hin, hx⟩
    exact ⟨m', hstar, hlm,
      ⟨(core_fr hinv.core).monoW fun r cc _ h => hedge e hmem r cc h, hinv.slots⟩, hin, hmem, hx⟩
  rcases Cx.termG3_spec hterm with ⟨-, hterm⟩ | ⟨asm, inv, hbr, hterm⟩
  · rcases Cx.termG2_spec hterm with ⟨hk', -⟩ | ⟨-, hterm⟩
    · obtain ⟨R, -, hn⟩ := stepTermLoc_gen ht
      exact (stepTermL_exit hk' hn).elim
    exact fin _ (term_core (H := H) F hst hterm hnext hpcT hm hinv.core hK hpre ht).choose_spec
  · exact fin _ (term_test (H := H) F hst hbr hterm hnext hpcT hm hinv.core hK ht).choose_spec

/-- `termK_stepX` without the successor and the X registers. -/
theorem termK_step {H : Hooks} {c : Cx2} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int}
    {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv} {bid : ID} {blk : Block}
    {e : Edge} {s s' : LocState} {m : MState}
    (hpcOf : E.pcOf = pcOfTab text c.cx.ps.toList tab)
    (F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E) (htm : c.tm = c.cx.termG3)
    (hk : checkK c.cx.lc kt = .ok ()) (hblocks : c.blocks c.cx.lc.ctx.f.blocks.toList = .ok tab)
    (hbid : bid ∈ c.cx.lc.ctx.f.blocks.toList) (hb : c.cx.lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E c.cx.lc (kAt c.cx.lc kt bid blk blk.values.size) s)
    (hpre : G1TermPre c.cx.lc s blk) (ht : stepTermLoc c.cx.lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H (Link.byId sym text az ez c.cx.ps.toList) c.cx.ps.toList ret m m' ∧
      LocMatch E s' e.b 0 m' ∧ G3Inv E c.cx.lc (kt.at e.b) s' ∧
      e.b ∈ c.cx.lc.ctx.f.blocks.toList :=
  (termK_stepX hpcOf F htm hk hblocks hbid hb hm hinv hpre ht).imp
    fun _ ⟨h1, h2, h3, h4, _⟩ => ⟨h1, h2, h3, h4⟩

/-- **G3, terminators.** A terminator of a function `checkG3` accepted with the class table `kt`
that goes to a successor, from a state whose registers hold the classes of the block's end, is
matched by `runProg` steps to a state related before the successor's first value, with the
registers at the classes of the successor's start (`kt.at`); an `Exit` block never goes to one. -/
theorem g3_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG3 lc ps bstart g = .ok (tab, kt)) (hE : G2Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList := by
  obtain ⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome3, -, hk, hlt, hnd, hblocks⟩ := checkG3_spec hc
  exact termK_step hpcOf ⟨hl, clsReg_of_home3 hhome3, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb
    hm hinv hpre ht

end GoFV.Proof.Gen

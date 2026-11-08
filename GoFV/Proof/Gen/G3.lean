import GoFV.Proof.Gen.G2
import GoFV.Proof.Gen.Spec3
import GoFV.Proof.Gen.MemN
import GoFV.Proof.Gen.Progs3
import GoFV.Proof.Gen.Value3
import GoFV.Proof.Gen.Step3

/-!
# Soundness of the genssa validator's slice G3: widths (`docs/plans/proofs3.md` §4)

`g3_value`: when `checkG3` accepts a function with the class table `kt`, every value of a block
(other than the entry values) run by `runLoc` from a state related by `LocMatch` to a machine state,
whose registers hold values of the classes the table gives before that value (`G3Inv` at
`kAt lc kt b blk i`), is matched by `runProg` steps of genssa's P0 Progs to a state related before
the next value, with the registers at the classes before the next value. `g3_term`: a terminator
that goes to a successor is matched by steps to a state related before the successor's first value,
with the registers at the classes of the successor's start (`kt.at`).

The activation is G2's (`G2Env`); the invariant (`G3Inv`) is G2's with the class map of the table
instead of one class per register; the per-value premises (`G3Pre`) are G1's, with every load (of
`n` bytes, through a register or of a global) reading valid bytes and a boolean load reading 0 or 1.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm

/-! ## The premises -/

/-- The invariant of G3's `runLoc` states at the class map `K` (from the class table): every
register holds a value of the class `K` gives it, G2's memory and slot facts. -/
structure G3Inv (E : MatchEnv) (lc : LocCtx) (K : KMap) (s : LocState) : Prop where
  core : CoreInv E.ι (StkAt E) K.get s
  slots : SlotInv lc s

/-- The per-value premises of G3: G1's for compares; a load of `n` bytes reads valid bytes at its
address (`symAddr`: the register's address plus the offset, or the global), and a boolean load
reads 0 or 1 (Go stores booleans so). -/
def G3Pre (lc : LocCtx) (s : LocState) (v : Value) : Prop :=
  ((v.op = .ARM64CMP ∨ v.op = .ARM64CMPconst) →
    ∀ a ∈ v.args.toList, ∀ x, s.read lc a = .ok x → NoBarePtr x) ∧
  (∀ as n sg, loadOp? v.op = some (as, n, sg) → ∀ a x, v.args[0]? = some a →
    s.read lc a = .ok x → ∃ p mm bs, symAddr lc.ctx v x = some p ∧ s.mem = .mem mm ∧
      mm.read p n = some bs ∧
      (lc.ty v.id = .bool → ∀ y, mm.load (.int .w8) p = .int .w8 y → y.toNat < 2))

/-- G3's premises give G1's for a value whose `MOVDload` has no symbol. -/
theorem G3Pre.g1 {lc : LocCtx} {s : LocState} {v : Value} (h : G3Pre lc s v)
    (haux : v.op = .ARM64MOVDload → v.aux = none) : G1Pre lc s v := by
  refine ⟨h.1, fun hop a x ha hx => ?_⟩
  have hl : loadOp? v.op = some (.MOVD, 8, false) := by simp [loadOp?, hop]
  obtain ⟨p, mm, bs, hp, hmm, hr, -⟩ := h.2 _ _ _ hl a x ha hx
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
    (hres : ∀ rs, lc.home v.id = some (.results rs) → rs = #[]) :
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
        rw [hres rs hh] at hc
        simp only [Array.toList_empty, List.zip_nil_right, kResults] at hc
        rw [if_neg (fun h => by cases h.2)]
        exact hc
      | slot k =>
        simp only [hh] at hc
        rw [if_neg (fun h => by cases h.2)]
        exact hc
      | pair a b =>
        simp only [hh] at hc
        rw [if_neg (fun h => by cases h.2)]
        exact hc

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
pattern). -/
theorem op_mem2 {P : BitVec 64 → Prop} (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι P K s) (hkeep : Keeps E P s m)
    (hj : E.pcOf b i = pcAt text psA.toList j)
    (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j') {pat : Pat} (hone : OneAt2 psA j pat j')
    {mm' : Mem} {M : Memory} (hM : MemInj E.ι mm' M) (hkn : KeysNodup mm')
    (hsep : SepFrom E.ι P mm') (hP : ∀ y, P y → M y = m.mem y) (hKL : KLe K' K)
    (hstep : ∀ k (hk : k < psA.toList.length), pat.ok psA.toList[k] = true →
      progStep (Link.byId sym text az ez psA.toList) psA.toList[k]
          { m with pc := pcAt text psA.toList k } =
        .ok { m with mem := M, pc := pcAt text psA.toList (k + 1) }) :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E { s with mem := .mem mm' } b (i + 1) m' ∧
      CoreInv E.ι P K' { s with mem := .mem mm' } := by
  obtain ⟨k, rfl, hk, hok, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hone m
  rw [pc_eta hm hj] at hstar
  obtain ⟨hsl, hfr⟩ := hkeep M hP
  have hlm := locMatch_setMem hm hsl hfr hM (b' := b) (i' := i + 1)
  rw [hj'] at hlm
  exact ⟨_, hstar.tail (pstep_at F.nodup F.lt F.ret hk rfl (hstep k hk hok)), hlm,
    (⟨hinv.regs, ⟨mm', rfl, hkn, hsep⟩⟩ : CoreInv E.ι P K { s with mem := .mem mm' }).mono hKL⟩

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

/-- A load of `n` bytes, through a 64-bit register (`off(Rn)`) or of a global (`sym+off(SB)`). -/
theorem g3_load (F : Facts lc sym text az ez psA.toList ret E)
    (hglob : ∀ y name abi, g.syms[y]? = some (name, abi) →
      E.ι (.global name.toStringLossy) = some (sym y))
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
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
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
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
  obtain ⟨p, mm2, bs, hsym, hmm2, hrd, h01⟩ := hpre.2 _ _ _ hop a0 x ha0 hx
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
    refine (op_reg2 (H := H) F hm hinv hj hj' hvs hd hkd hor (hval a hpa) (fits_retypeL hcv _)
      (knext_set hK hnp hvh hcv) (fun k0 hk0 hok => ?_)).imp
      fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
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
    refine (op_reg2 (H := H) F hm hinv hj hj' hvs hd hkd hor (hval _ hpa) (fits_retypeL hcv _)
      (knext_set hK hnp hvh hcv) (fun k1 hk1 hok => ?_)).imp
      fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
    obtain ⟨has, ⟨hf1, hf2, -, -, hf5, y', hy1, hy'⟩, -, ht', -, -, -⟩ := hpat _ hok
    have hyy : sym y' = sym y :=
      Option.some.inj ((hglob y' name abi hy').symm.trans hpa)
    have hL : (Link.byId sym text az ez psA.toList).sym y' = sym y := hyy
    rw [progStep_globLoad hkd (nextAddr_pcAt F.nodup hk1) (by rw [has]; exact hmov) hf1 hf2 hf5
      hy1 ht' (by rw [hL]; exact hnil), hL, wX_pc]

end Cases

end GoFV.Proof.Gen

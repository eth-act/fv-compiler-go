import GoFV.Proof.Gen.G3
import GoFV.Proof.Gen.Spec4
import GoFV.Proof.Gen.Step4
import GoFV.Proof.Gen.Progs4

/-!
# Soundness of the genssa validator's slice G4: register pairs (`docs/plans/proofs3.md` §4)

`g4_value`: when `checkG4` accepts a function with the class table `kt`, every value of a block
(other than the entry values) run by `runLoc` from a state related by `LocMatch` to a machine
state, whose registers hold values of the classes the table gives before that value (`G3Inv` at
`kAt lc kt b blk i`), is matched by `runProg` steps of genssa's P0 Progs to a state related before
the next value, with the registers at the classes before the next value. `g4_term`: a terminator
that goes to a successor is matched by steps to a state related before the successor's first
value, with the registers at the classes of the successor's start (`kt.at`).

The activation and the invariant are G3's (`G2Env`, `G3Inv`). The per-value premises (`G4Pre`)
are G3's, and a pair load `LDP` reads valid bytes at both of its addresses (`pairAddr`). G3's
values go through `vk3_step`; G4's own are the pair load into a register pair (`g4_ldp`), the
pair store (`g4_stp`) and a component of a pair load in its register (`g4_sel`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm

/-! ## The premises -/

/-- The per-value premises of G4: G3's (`G3Pre`), and a pair load reads valid bytes at both of
its addresses (`pairAddr`: the register's address plus the offset, and 8 bytes above). -/
def G4Pre (lc : LocCtx) (s : LocState) (v : Value) : Prop :=
  G3Pre lc s v ∧
    (v.op = .ARM64LDP → ∀ a x, v.args[0]? = some a → s.read lc a = .ok x →
      ∃ p q mm bs bs', pairAddr lc.ctx v 8 x = some (p, q) ∧ s.mem = .mem mm ∧
        mm.read p 8 = some bs ∧ mm.read q 8 = some bs')

/-! ## Pairs -/

/-- An `Int64` offset moved by 8, as a machine word: the word moved by 8. -/
theorem ofInt_add8 (k : Int64) :
    BitVec.ofInt 64 (k + Int64.ofNat 8).toInt = BitVec.ofInt 64 k.toInt + 8 := by
  show BitVec.ofInt 64 (k + Int64.ofNat 8).toBitVec.toInt = BitVec.ofInt 64 k.toBitVec.toInt + 8
  rw [BitVec.ofInt_toInt, BitVec.ofInt_toInt, Int64.toBitVec_add]
  rfl

/-- The addresses of a pair access of 8-byte elements without a symbol: the base moved by the
offset, and by the offset plus 8. -/
theorem pairAddr_noAux {ctx : Ctx} {v : Value} {x : Val} {p q : Ptr} (hax : v.aux = none)
    (h : pairAddr ctx v 8 x = some (p, q)) :
    Arm64.addr x (BitVec.ofInt 64 v.auxInt.toInt) = some p ∧
      Arm64.addr x (BitVec.ofInt 64 v.auxInt.toInt + 8) = some q := by
  obtain ⟨h1, h2⟩ := pairAddr_eq_some h
  unfold symAddr at h1 h2
  rw [hax] at h1
  dsimp only at h2
  rw [hax, ofInt_add8] at h2
  exact ⟨h1, h2⟩

theorem retypeL_pair (y0 y1 : Val) (t0 t1 : Ty) :
    (Val.tuple [y0, y1]).retypeL (.tuple [t0, t1]) = .tuple [y0.retypeL t0, y1.retypeL t1] := by
  simp only [Val.retypeL, Val.widen, Val.widenList, Val.retype]
  rfl

/-- A pair load of 8-byte elements at a pair shape: the two 8-byte loads at the component shapes. -/
theorem loadPair_tuple {t0 t1 : Ty} {mm : Mem} {p q : Ptr} :
    Arm64.loadPair (.tuple [t0, t1]) 8 false mm p q =
      .tuple [Arm64.loadN t0 8 false mm p, Arm64.loadN t1 8 false mm q] := by
  simp [Arm64.loadPair, Arm64.loadElt, Arm64.tupleTy]

theorem writeParts_reg {s : LocState} {t : Ty} (hc : (cls t).isSome = true) (ts : List Ty)
    (x : Val) (xs : List Val) (r : Nat) (rs : List (Option Nat)) :
    s.writeParts (t :: ts) (x :: xs) (some r :: rs) = (s.setReg r x).writeParts ts xs rs := by
  have hm : memTy t = false := cls_notMem hc
  have hf : t.isFlags = false := cls_notFlags hc
  cases t <;> simp_all [LocState.writeParts, memTy]

/-- A pair written to a register pair home: the first component to the first register, then the
second to the second. -/
theorem write_pair {lc : LocCtx} {s : LocState} {id ra rb : Nat} {t0 t1 : Ty} {y0 y1 : Val}
    (hh : lc.home id = some (.pair (some ra) (some rb))) (hty : lc.ty id = .tuple [t0, t1])
    (h0 : (cls t0).isSome = true) (h1 : (cls t1).isSome = true) :
    s.write lc id (.tuple [y0, y1]) = (s.setReg ra y0).setReg rb y1 := by
  unfold LocState.write
  simp only [hh, hty, Option.map_some, Option.getD_some, Location.regList, Val.partsOf]
  rw [writeParts_reg h0, writeParts_reg h1]
  rfl

/-- A value homed in a register pair, read at a pair shape: its registers at the component shapes. -/
theorem read_pair {lc : LocCtx} {s : LocState} {c ra rb : Nat} {t0 t1 : Ty}
    (hl : lc.ctx.f.lowered = true) (hh : lc.home c = some (.pair (some ra) (some rb)))
    (hty : lc.ty c = .tuple [t0, t1]) (h0 : (cls t0).isSome = true) (h1 : (cls t1).isSome = true) :
    s.read lc c = .ok (.tuple [(s.reg t0 ra).retypeL t0, (s.reg t1 rb).retypeL t1]) := by
  have hraw : s.raw lc c = .ok (.tuple [s.reg t0 ra, s.reg t1 rb]) := by
    unfold LocState.raw
    simp only [hh, hty, Location.regList]
    rw [readParts_cons (cls_notMem h0) (cls_notFlags h0),
      readParts_cons (cls_notMem h1) (cls_notFlags h1)]
    rfl
  unfold LocState.read
  rw [hraw]; simp only [lmode_retype hl, hty, retypeL_pair]
  rfl

theorem arr4 {α : Type} {xs : Array α} {a b c d : α} (h : xs.size = 4) (h0 : xs[0]? = some a)
    (h1 : xs[1]? = some b) (h2 : xs[2]? = some c) (h3 : xs[3]? = some d) : xs = #[a, b, c, d] := by
  rcases xs with ⟨_ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, _ | ⟨u, l⟩⟩⟩⟩⟩⟩ <;> simp_all

/-! ## Class maps -/

/-- The class table follows a pair load into two distinct registers (`kStep`): each register
takes its component's class. -/
theorem kpair_kStep {lc : LocCtx} {K : KMap} {v : Value} {ra rb : Nat} {t0 t1 : Ty} {c0 c1 : Nat}
    (hop : v.op ≠ .Phi) (hh : lc.home v.id = some (.pair (some ra) (some rb)))
    (hty : lc.ty v.id = .tuple [t0, t1]) (h0 : cls t0 = some c0) (h1 : cls t1 = some c1)
    (hne : ra ≠ rb) :
    KLe (kStep lc K v).get (kSet (kSet K.get ra (some c0)) rb (some c1)) := by
  intro r c _ hc
  rw [kStep_get] at hc
  simp only [hop, ↓reduceIte, hh, hty, tupleTys, List.zip_cons_cons, List.zip_nil_right] at hc
  have hnd : ([(t0, some ra), (t1, some rb)].filterMap (·.2)).Nodup := by simp [hne]
  unfold kSet
  by_cases hrb : r = rb
  · subst hrb
    simp only [↓reduceIte]
    by_cases hsz : r < K.size
    · rw [kResults_get_of_mem (t := t1) hnd (by simp) hsz, h1] at hc; exact hc
    · rw [KMap.get_ge (by rw [kResults_size]; omega)] at hc; cases hc
  · simp only [hrb, ↓reduceIte]
    by_cases hra : r = ra
    · subst hra
      simp only [↓reduceIte]
      by_cases hsz : r < K.size
      · rw [kResults_get_of_mem (t := t0) hnd (by simp) hsz, h0] at hc; exact hc
      · rw [KMap.get_ge (by rw [kResults_size]; omega)] at hc; cases hc
    · simp only [hra, ↓reduceIte]
      rw [kResults_get_of_not_mem (by simp [hra, hrb])] at hc
      exact hc

/-- The register of a pair a `Select0`/`Select1` reads (`kReads`) holds its component's class. -/
theorem ksel4_of_reads {lc : LocCtx} {v : Value} {K : KMap} {c ra rb i r k : Nat}
    (h : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hop : v.op = .Select0 ∧ i = 0 ∧ r = ra ∨ v.op = .Select1 ∧ i = 1 ∧ r = rb)
    (hc0 : v.args[0]? = some c) (hhc : lc.home c = some (.pair (some ra) (some rb)))
    (hcl : ((tupleTys (lc.ty c))[i]?.bind cls) = some k) : K.get r = some k := by
  apply h (r, k)
  rcases hop with ⟨hop, rfl, rfl⟩ | ⟨hop, rfl, rfl⟩
  · simp [kReads, hop, hc0, hhc, hcl]
  · simp [kReads, hop, hc0, hhc, hcl]

/-! ## One value of G4's own kinds -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- `LDP off(Rn), (Ra, Rb)`: the 8 bytes at the address into `Ra`, the 8 bytes above into `Rb`. -/
theorem g4_ldp (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) {ra rb : Nat} {t0 t1 : Ty} {c0 c1 : Nat}
    (hK : KLe K' (kSet (kSet K ra (some c0)) rb (some c1))) (hpre : G4Pre lc s v)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {rn oa ob : Int} (hop : v.op = .ARM64LDP) (hsz2 : v.args.size = 2) (hax : v.aux = none)
    (hty : lc.ty v.id = .tuple [t0, t1]) (h0 : cls t0 = some c0) (h1 : cls t1 = some c1)
    (h80 : 8 ≤ c0) (h81 : 8 ≤ c1) (hao : argObj lc v 0 = .ok (64, rn))
    (hma : memArg lc v 1 = .ok ()) (hh : lc.home v.id = some (.pair (some ra) (some rb)))
    (hza : ra ≠ zeroReg) (hzb : rb ≠ zeroReg) (hda : destOK ra = true) (hdb : destOK rb = true)
    (hoa : objOf? ra = some oa) (hob : objOf? rb = some ob)
    (hvs : OneAt2 psA j
      (.ofShape { as := .LDP, from_ := memA rn v.auxInt.toInt, to := pairA oa ob }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨a1, ha1, hamt, hah1⟩ := memArg_spec hma
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨ka, hka, rfl, hkka⟩ := objOf?_some hoa
  obtain ⟨kb, hkb, rfl, hkkb⟩ := objOf?_some hob
  have hka' : ka < 31 := by
    rcases hkka with ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h hza
    · exact h
  have hkb' : kb < 31 := by
    rcases hkkb with ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h hzb
    · exact h
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨x, hx, rfl⟩ :=
    stepLoc_ldp hl htemp hop (arr2 hsz2 ha0 ha1) (read_mem hl hah1 hamt hmm) hs
  obtain ⟨X, hX, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  rw [hx] at hX
  cases hX
  obtain ⟨p, q, mm2, bs, bs', hpq, hmm2, hrp, hrq⟩ := hpre.2 hop a0 x ha0 hx
  rw [hmm] at hmm2
  cases hmm2
  obtain ⟨hap, haq⟩ := pairAddr_noAux hax hpq
  obtain ⟨a, hpa, haeq, hnil⟩ :=
    addr_rel hA hMI hxv hxf hap (by omega : 0 < 8) (Or.inr (by rw [hrp]; rfl))
  obtain ⟨a', hqa, haeq', hnil'⟩ :=
    addr_rel hA hMI hxv hxf haq (by omega : 0 < 8) (Or.inr (by rw [hrq]; rfl))
  rw [hpq]
  simp only [Option.elim]
  rw [hty, loadPair_tuple, retypeL_pair, write_pair hh hty (by rw [h0]; rfl) (by rw [h1]; rfl)]
  have ht0 := cls_ne_bool h0 h80
  have ht1 := cls_ne_bool h1 h81
  have hrel0 : ValRel E.ι ((Arm64.loadN t0 8 false mm p).retypeL t0)
      ((readMem m.mem (a + p.off) 8).setWidth 64) :=
    valRel_retypeL_lo hA h0 ht0 ((lo_loadN hA hMI (by simp) (fun _ => rfl) ht0 hpa hrp).mono
      (cls_le h0))
  have hrel1 : ValRel E.ι ((Arm64.loadN t1 8 false mm q).retypeL t1)
      ((readMem m.mem (a' + q.off) 8).setWidth 64) :=
    valRel_retypeL_lo hA h1 ht1 ((lo_loadN hA hMI (by simp) (fun _ => rfl) ht1 hqa hrq).mono
      (cls_le h1))
  obtain ⟨k, rfl, hk, hok, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
  rw [pc_eta hm hj] at hstar
  obtain ⟨hlm1, hinv1⟩ := finish_reg hm hinv hda (by omega : ka < 32) hoa hrel0
    (fits_retypeL h0 _) (b' := b) (i' := i + 1)
  obtain ⟨hlm2, hinv2⟩ := finish_reg hlm1 hinv1 hdb (by omega : kb < 32) hob hrel1
    (fits_retypeL h1 _) (b' := b) (i' := i + 1)
  rw [hj'] at hlm2
  refine ⟨_, hstar.tail (pstep_at F.nodup F.lt F.ret hk rfl ?_), hlm2, hinv2.mono hK, hsi⟩
  obtain ⟨has, hf, -, ht', hsc⟩ := Shape.ok_eq hok
  have haeq0 : ({ m with pc := pcAt text psA.toList k } : MState).rX (BitVec.ofNat 5 kn) +
      BitVec.ofInt 64 v.auxInt.toInt = a + p.off := haeq
  have haeq8 : a + p.off + 8 = a' + q.off := by rw [← haeq, BitVec.add_assoc]; exact haeq'
  rw [progStep_ldp hkn hka' hkb' (nextAddr_pcAt F.nodup hk) has hf hsc ht'
    (by rw [haeq0]; exact hnil) (by rw [haeq0, haeq8]; exact hnil'), haeq0, haeq8]
  simp only [wX_pc]

/-- `STP (Rx, Ry), off(Rn)`: the 8 bytes of `Rx` at the address, those of `Ry` 8 bytes above,
outside the frame. -/
theorem g4_stp (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size = 8)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {rn rx ry : Int} (hop : v.op = .ARM64STP) (hsz4 : v.args.size = 4) (hax : v.aux = none)
    (hmt : memTy (lc.ty v.id) = true) (hhn : lc.home v.id = none)
    (hao : argObj lc v 0 = .ok (64, rn)) (hxo : argObj lc v 1 = .ok (64, rx))
    (hyo : argObj lc v 2 = .ok (64, ry)) (hma : memArg lc v 3 = .ok ())
    (hvs : OneAt2 psA j
      (.ofShape { as := .STP, from_ := pairA rx ry, to := memA rn v.auxInt.toInt }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hxo
  obtain ⟨a2, r2, ha2, hah2, hor2, hca2⟩ := argObj_spec hyo
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨kx, hkx, rfl, hkkx⟩ := objOf?_some hor1
  obtain ⟨ky, hky, rfl, hkky⟩ := objOf?_some hor2
  obtain ⟨a3, ha3, hamt, hah3⟩ := memArg_spec hma
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨X, hX, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨Y, hY, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkkx
  obtain ⟨Z, hZ, hzv, hzf⟩ :=
    arg_rel hA hl hm hinv hah2 hca2 (kread_arg hR hnp ha2 hah2 hca2) hkky
  obtain ⟨x, y, z, p, q, mm1, mm', hx, hy, hz, hpq, hw1, hw2, rfl⟩ :=
    stepLoc_stp hl htemp hop (arr4 hsz4 ha0 ha1 ha2 ha3) (read_mem hl hah3 hamt hmm) hs
  rw [hX] at hx; cases hx
  rw [hY] at hy; cases hy
  rw [hZ] at hz; cases hz
  obtain ⟨mm0, hmm0, hk0, hsep0⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  obtain ⟨hap, haq⟩ := pairAddr_noAux hax hpq
  have hby := (storeBytes_relN hA (n := 8) (by simp) hyv hyf (Or.inl (Nat.le_refl _))).1
  have hbz := (storeBytes_relN hA (n := 8) (by simp) hzv hzf (Or.inl (Nat.le_refl _))).1
  have hcan1 : mm.canWrite p 8 = true := by
    have := canWrite_of_write hw1 (by rw [hby]; omega)
    rwa [hby] at this
  obtain ⟨a, hpa, haeq, hnil⟩ := addr_rel hA hMI hxv hxf hap (by omega : 0 < 8) (Or.inl hcan1)
  obtain ⟨hM1, hk1, hback1, al1, hal1, hoff1, hout1⟩ :=
    memInj_storeN hA hMI hk0 (by simp) hpa hyv hyf (Or.inl (Nat.le_refl _)) hw1
  have hcan2 : mm1.canWrite q 8 = true := by
    have := canWrite_of_write hw2 (by rw [hbz]; omega)
    rwa [hbz] at this
  obtain ⟨a', hqa, haeq', hnil'⟩ := addr_rel hA hM1 hxv hxf haq (by omega : 0 < 8) (Or.inl hcan2)
  obtain ⟨hM2, hk2, hback2, al2, hal2, hoff2, hout2⟩ :=
    memInj_storeN hA hM1 hk1 (by simp) hqa hzv hzf (Or.inl (Nat.le_refl _)) hw2
  have hsep1 : SepFrom E.ι (StkAt E) mm1 := by
    intro b2 al a2 hb hι w hw
    obtain ⟨al0, hb0, hs0⟩ := hback1 b2 al hb
    rw [← hs0]; exact hsep0 b2 al0 a2 hb0 hι w hw
  have hsep2 : SepFrom E.ι (StkAt E) mm' := by
    intro b2 al a2 hb hι w hw
    obtain ⟨al0, hb0, hs0⟩ := hback2 b2 al hb
    rw [← hs0]; exact hsep1 b2 al0 a2 hb0 hι w hw
  rw [write_mem hhn hmt, memTy_eq hmt, retypeL_mem]
  have haeq8 : a + p.off + 8 = a' + q.off := by rw [← haeq, BitVec.add_assoc]; exact haeq'
  refine (op_mem2 (H := H) F hm hinv (stk_keeps hm hF hsz) hj hj' hvs hM2 hk2 hsep2
    (fun w hw => (hout2 w fun j hj he => hsep1 _ _ _ hal2 hqa w hw ⟨by omega, by omega⟩).trans
      (hout1 w fun j hj he => hsep0 _ _ _ hal1 hpa w hw ⟨by omega, by omega⟩))
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)) (fun k hk hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨has, hf, -, ht', hsc⟩ := Shape.ok_eq hok
  have haeq0 : ({ m with pc := pcAt text psA.toList k } : MState).rX (BitVec.ofNat 5 kn) +
      BitVec.ofInt 64 v.auxInt.toInt = a + p.off := haeq
  rw [progStep_stp hkn hkx hky (nextAddr_pcAt F.nodup hk) has hf hsc ht'
    (by rw [haeq0]; exact hnil) (by rw [haeq0, haeq8]; exact hnil'), haeq0, haeq8]
  rfl

/-- `Select0`/`Select1` of a pair load, homed in the register of its component, changes nothing
on the machine. -/
theorem g4_sel (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {c : ID} {ra rb i0 r : Nat}
    (hop : v.op = .Select0 ∧ i0 = 0 ∧ r = ra ∨ v.op = .Select1 ∧ i0 = 1 ∧ r = rb)
    (hsz1 : v.args.size = 1) (hc0 : v.args[0]? = some c) (hpt : pairTys (lc.ty c) = true)
    (hhc : lc.home c = some (.pair (some ra) (some rb))) (hvh : lc.home v.id = some (.reg r))
    (hrz : r ≠ zeroReg) (hd : destOK r = true) (hob : (objOf? r).isSome = true)
    (hcl : ((tupleTys (lc.ty c))[i0]?.bind cls) = cls (lc.ty v.id))
    (hKr : ∀ c0, cls (lc.ty v.id) = some c0 → K r = some c0)
    (hvs : j' = j) (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rcases hop with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun
  obtain ⟨t0, t1, c0, c1, hty, h0, h1, -, -⟩ := pairTys_spec hpt
  have hread := read_pair (s := s) hl hhc hty (by rw [h0]; rfl) (by rw [h1]; rfl)
  obtain ⟨x, hx, rfl⟩ := stepLoc_select hl htemp
    (hop.imp (fun h => ⟨h.1, h.2.1⟩) (fun h => ⟨h.1, h.2.1⟩)) (arr1 hsz1 hc0) hs
  rw [hread] at hx
  cases hx
  obtain ⟨t, cv, hsel, hct, hcv⟩ : ∃ t cv, Tuple.select i0
      [.tuple [(s.reg t0 ra).retypeL t0, (s.reg t1 rb).retypeL t1]] = (s.reg t r).retypeL t ∧
      cls t = some cv ∧ cls (lc.ty v.id) = some cv := by
    rcases hop with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
    · exact ⟨t0, c0, rfl, h0, by rw [← hcl, hty]; simp [tupleTys, h0]⟩
    · exact ⟨t1, c1, rfl, h1, by rw [← hcl, hty]; simp [tupleTys, h1]⟩
  rw [hsel, write_reg hvh hcv]
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 hob
  obtain ⟨k, hk32, rfl, hkk⟩ := objOf?_some ho
  have hk31 : k < 31 ∧ objX? r = some (BitVec.ofNat 5 k) := by
    rcases hkk with ⟨h, -⟩ | h
    · exact absurd h hrz
    · exact h
  have hrel : ValRel E.ι (((s.reg t r).retypeL t).retypeL (lc.ty v.id))
      (m.rX (BitVec.ofNat 5 k)) := by
    rw [rX_lt hk31.1]
    simp only [LocState.reg, beq_iff_eq, hrz, ↓reduceIte]
    cases hv : s.regs[r]? with
    | none => simp only [Option.getD_none, retypeL_poison]; trivial
    | some raw =>
      simp only [Option.getD_some]
      have hfit := hinv.regs r raw cv hrz hv (hKr cv hcv)
      have h1' := valRel_retypeL hA hct hfit ((hm.regs r raw hv).1 _ hk31.2)
      exact valRel_retypeL hA hcv (fits_retypeL hct _) h1'
  obtain ⟨hlm, hinv'⟩ := finish_reg hm hinv hd hk32 ho hrel (fits_retypeL hcv _)
    (b' := b) (i' := i + 1)
  rw [wX_rX_self, hj', hvs, ← hj, ← hm.pc] at hlm
  exact ⟨m, .refl, hlm, hinv'.mono (knext_set hK hnp hvh hcv), hsi⟩

end Cases

/-! ## Static facts of an accepted function -/

/-- A home G4 handles (`homeOK4`) that is no register pair is one G3 handles. -/
theorem homeOK3_of_4 {lc : LocCtx} {i : Nat} (h : homeOK4 lc i = true)
    (hp : ∀ a b, lc.home i ≠ some (.pair a b)) : homeOK3 lc i = true := by
  unfold homeOK4 at h
  split at h
  next a b hh => exact absurd hh (hp a b)
  next => exact h

/-- A register home G4 handles other than `ZERO` holds a value with a class. -/
theorem clsReg_of_home4 {lc : LocCtx} (h : ∀ i, homeOK4 lc i = true) :
    ∀ i r, lc.home i = some (.reg r) → r ≠ zeroReg → (cls (lc.ty i)).isSome = true := by
  intro i r hh hr
  have := homeOK3_of_4 (h i) (fun a b hab => by rw [hh] at hab; cases hab)
  simp only [homeOK3, hh, Bool.or_eq_true, beq_iff_eq, hr, false_or] at this
  exact this

/-- A call's home is no slot (`homeOK4`). -/
theorem call_not_slot4 {lc : LocCtx} {c : ID} {u : Value} (h : ∀ i, homeOK4 lc i = true)
    (hu : lc.ctx.f.value? c = some u) (hcop : u.op = .ARM64CALLstatic) :
    ∀ k, lc.home c ≠ some (.slot k) := by
  intro k hk
  have := homeOK3_of_4 (h c) (fun a b hab => by rw [hk] at hab; cases hab)
  simp [homeOK3, homeOK2, hk, hu, hcop] at this

/-! ## The theorems -/

/-- One value of G4's kinds (`VK4`) emitted at the Progs from `j` to `j'`, run from a state at the
class map `K` that gives every register the value reads its class (`kReads`): matched by `runProg`
steps to a state related before the next value, at the class map after it (`kStep`). `g4_value`
and the later slices apply it to their values of G4's kinds. -/
theorem vk4_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2}
    (hE : G2Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome4 : ∀ i, homeOK4 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK4 lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s) (hpre : G4Pre lc s v)
    (hcall : CallOK H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G2Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' := by
  have hE0 := hE
  obtain ⟨hlcE, -, -, -, -, -, -, -, -, -, hF⟩ := hE
  have hR := kread_of_reads hreads
  have hsz := slot_sizes hlcE hcf hinv.slots
  have same : ∀ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E s' bid (i + 1) m' ∧ CoreInv E.ι (StkAt E) (kStep lc K v).get s' ∧
      SlotInv lc s' →
      ∃ E' m', E.Extends E' ∧ G2Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
        PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
        LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' :=
    fun m' ⟨h1, h2, h3, h4⟩ => ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE0, h1, h2, ⟨h3, h4⟩⟩
  cases hVK with
  | g3 _ _ _ _ hVK3 =>
    exact vk3_step hE0 F (fun _ _ hu hcop => call_not_slot4 hhome4 hu hcop) hcf hv hVK3 hvs htemp
      hj hj' hreads hm hinv hpre.1 hcall hs
  | ldp hop hsz2 hax hty h0 h1 h80 h81 hao hma hh hne hza hzb hda hdb hoa hob =>
    obtain ⟨m', h⟩ := g4_ldp (H := H) F hm hinv.core hinv.slots hR
      (kpair_kStep (by rw [hop]; nofun) hh hty h0 h1 hne) hpre hj hj' hop hsz2 hax hty h0 h1 h80
      h81 hao hma hh hza hzb hda hdb hoa hob hvs htemp hs
    exact same m' h
  | stp hop hsz4 hax hmt hhn hao hxo hyo hma =>
    obtain ⟨m', h⟩ := g4_stp (H := H) F hF hsz hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hop hsz4 hax hmt hhn hao hxo hyo hma hvs
      htemp hs
    exact same m' h
  | sel hop hsz1 hc0 _ _ hpt hhc hvh hrz hd hob hcls hcl =>
    obtain ⟨m', h⟩ := g4_sel (H := H) F hm hinv.core hinv.slots
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz1 hc0 hpt hhc hvh hrz hd hob hcl
      (fun c0 hc0' => ksel4_of_reads hreads hop hc0 hhc (hcl.trans hc0')) hvs htemp hs
    exact same m' h

/-- **G4, values.** A value (not an entry value) of a function `checkG4` accepted with the class
table `kt`, run by `runLoc` from a state related by `LocMatch` to a machine state whose registers
hold values of the classes the table gives before the value (`G3Inv` at `kAt … i`), is matched by
`runProg` steps of genssa's P0 Progs to a state related before the next value, with the registers
at the classes before the next value, under an activation `E'` that extends `E`'s injection (by
the callee's, at a call) and is again a `G2Env`. At a static call the callee's behaviour is the
trusted contract `CallOK`. -/
theorem g4_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG4 lc ps bstart g = .ok (tab, kt)) (hE : G2Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp3 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hpre : G4Pre lc s v)
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
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome4, hcf, hk, hlt, hnd, hblocks⟩ := checkG4_spec hc
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
  obtain ⟨htemp, hVK⟩ := vkind4_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  rw [kAt_succ hi hv]
  exact vk4_step hE0 ⟨hl, clsReg_of_home4 hhome4, hnd, hlt, hret, hA⟩ hhome4 hcf hv hVK hvs htemp
    hj hj' hreads hm hinv hpre hcall hs

/-- **G4, terminators.** A terminator of a function `checkG4` accepted with the class table `kt`
that goes to a successor, from a state whose registers hold the classes of the block's end, is
matched by `runProg` steps to a state related before the successor's first value, with the
registers at the classes of the successor's start (`kt.at`); an `Exit` block never goes to one. -/
theorem g4_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG4 lc ps bstart g = .ok (tab, kt)) (hE : G2Env lc g L ps ret tab E)
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
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome4, -, hk, hlt, hnd, hblocks⟩ := checkG4_spec hc
  exact termK_step hpcOf ⟨hl, clsReg_of_home4 hhome4, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb
    hm hinv hpre ht

end GoFV.Proof.Gen

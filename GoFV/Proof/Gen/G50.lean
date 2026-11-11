import GoFV.Proof.Gen.G47
import GoFV.Proof.Gen.Spec50
import GoFV.Proof.Gen.Progs50

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G50 of the genssa validator: the narrow and float pair loads (`docs/plans/proofs3.md` §4)

`checkG50 lc` (`GoFV/Gen/Check50.lean`) is G47 with the pair loads `LDPW`, `LDPSW`, `FLDPD`,
`FLDPS` (`pairOp50`) and the selects of their components. Each pair load is `arm64Op`'s
`ldPair n sg` (`stepLoc_ldPair`): two `n`-byte loads at `pairAddr`, the base moved by the offset
and by the offset plus `n` (`pairAddr_noAuxN`).

* `LDPW`/`LDPSW` into two X registers is G4's `LDP` at `n = 4` (`g50_ldpX`): each component is
  G3's 4-byte load (`lo_loadN`), zero- or sign-extended as the machine's `progStep_ldpw`;
* `FLDPD`/`FLDPS` into two V registers (`g50_ldpF`): each component is G3's `n`-byte load related
  to its V register by `fvalRel_of_valRel`, which needs the loaded value at its shape to be no
  pointer without an integer form (a pointer has no V register form);
* a select of an `LDPW`/`LDPSW` component is G4's (`g4_sel`); of an `FLDPD`/`FLDPS` component, the
  V register read at the select's float shape (`g50_selF`, as `g47_selF`).

After each of them the upper-bit table is empty (`uStep35_pair50`, `uStep35_sel50`). The run
premise `PairPre50` asks that a pair load reads valid bytes at both of its addresses and, for
`FLDPD`/`FLDPS`, that what it reads at each component shape is no pointer; `g50_value` takes
`G50Pre := G46Pre ∧ PairPre50`. `g50_initMem`, `g50_term`, `g50_nilPanic`, `g50_boundsPanic` are
G47's statements over `checkG50`.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The premise -/

/-- A pair load of G50 (`pairOp50`: `n`-byte elements) reads valid bytes at both of its addresses
(`pairAddr`); for `FLDPD`/`FLDPS` (`fp`), what it reads at each component shape is no pointer
without an integer form (a pointer has no V register form). -/
def PairPre50 (lc : LocCtx) (s : LocState) (v : Value) : Prop :=
  ∀ as n sg fp, pairOp50 v.op = some (as, n, sg, fp) → ∀ a x, v.args[0]? = some a →
    s.read lc a = .ok x → ∃ p q mm bs bs', pairAddr lc.ctx v n x = some (p, q) ∧
      s.mem = .mem mm ∧ mm.read p n = some bs ∧ mm.read q n = some bs' ∧
      (fp = true → ∀ t0 t1, lc.ty v.id = .tuple [t0, t1] →
        (∀ r, (Arm64.loadN t0 n false mm p).retypeL t0 ≠ .ptr r) ∧
        (∀ r, (Arm64.loadN t1 n false mm q).retypeL t1 ≠ .ptr r))

/-- The per-value premises of G50: G46's (`G46Pre`), and `PairPre50`. -/
def G50Pre (lc : LocCtx) (s : LocState) (v : Value) : Prop := G46Pre lc s v ∧ PairPre50 lc s v

/-! ## `stepLoc` and the addresses -/

section Step

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

private theorem mapM_two50 {a b : ID} :
    [a, b].mapM (s.read lc) =
      (s.read lc a).bind fun x => (s.read lc b).bind fun y => .ok [x, y] := rfl

/-- A pair load of G50 (`pairOp50`) `[off] a mem`: `ldPair n sg`, the two `n`-byte loads at
`pairAddr` (`poison` if there is none). -/
theorem stepLoc_ldPair (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    {as : As} {n : Nat} {sg fp : Bool} (hpo : pairOp50 v.op = some (as, n, sg, fp)) {a0 a1 : ID}
    (ha : v.args = #[a0, a1]) {mm : Mem} (hm : s.read lc a1 = .ok (.mem mm))
    (h : stepLoc env lc s v = .ok s') :
    ∃ x, s.read lc a0 = .ok x ∧
      s' = s.write lc v.id
        (((pairAddr lc.ctx v n x).elim .poison fun pq =>
          Arm64.loadPair (lc.ty v.id) n sg mm pq.1 pq.2).retypeL (lc.ty v.id)) := by
  rcases pairOp50_cases hpo with ⟨hop, -, hn4, hsg, -⟩ | ⟨hop, -, hn4, hsg, -⟩ |
    ⟨hop, -, hn4, hsg, -⟩ | ⟨hop, -, hn4, hsg, -⟩
  all_goals
    obtain ⟨argv, r, hmap, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
      (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
      (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
    rw [ha] at hmap
    change [a0, a1].mapM (s.read lc) = _ at hmap
    rw [mapM_two50] at hmap
    cases hx : s.read lc a0 with
    | panic e m => rw [hx] at hmap; cases hmap
    | stuck msg => rw [hx] at hmap; cases hmap
    | ok x =>
      rw [hx, hm] at hmap; cases hmap
      have hev : evalOpL true env lc.ctx s.fr v [x, .mem mm] (lc.ty v.id) =
          arm64Op true env lc.ctx s.fr v [x, .mem mm] (lc.ty v.id) := by
        unfold evalOpL; rw [hop]; rfl
      rw [hev] at hr
      cases hn : nilFaults true lc.ctx v [x, .mem mm] with
      | some m =>
        have he : arm64Op true env lc.ctx s.fr v [x, .mem mm] (lc.ty v.id) =
            .panic .nilDeref m := by
          unfold arm64Op; rw [hn]
        rw [he] at hr; cases hr
      | none =>
        have he : arm64Op true env lc.ctx s.fr v [x, .mem mm] (lc.ty v.id) =
            .ok ((pairAddr lc.ctx v n x).elim .poison fun pq =>
              Arm64.loadPair (lc.ty v.id) n sg mm pq.1 pq.2) := by
          subst hn4 hsg; unfold arm64Op; rw [hn, hop]
        rw [he] at hr; cases hr
        exact ⟨x, rfl, rfl⟩

end Step

/-- An `Int64` offset moved by `n`, as a machine word: the word moved by `n`. -/
theorem ofInt_addN (k : Int64) (n : Nat) :
    BitVec.ofInt 64 (k + Int64.ofNat n).toInt = BitVec.ofInt 64 k.toInt + BitVec.ofNat 64 n := by
  show BitVec.ofInt 64 (k + Int64.ofNat n).toBitVec.toInt =
    BitVec.ofInt 64 k.toBitVec.toInt + BitVec.ofNat 64 n
  rw [BitVec.ofInt_toInt, BitVec.ofInt_toInt, Int64.toBitVec_add]
  rfl

/-- The addresses of a pair access of `n`-byte elements without a symbol: the base moved by the
offset, and by the offset plus `n`. -/
theorem pairAddr_noAuxN {ctx : Ctx} {v : Value} {x : Val} {p q : Ptr} {n : Nat}
    (hax : v.aux = none) (h : pairAddr ctx v n x = some (p, q)) :
    Arm64.addr x (BitVec.ofInt 64 v.auxInt.toInt) = some p ∧
      Arm64.addr x (BitVec.ofInt 64 v.auxInt.toInt + BitVec.ofNat 64 n) = some q := by
  obtain ⟨h1, h2⟩ := pairAddr_eq_some h
  unfold symAddr at h1 h2
  rw [hax] at h1
  dsimp only at h2
  rw [hax, ofInt_addN] at h2
  exact ⟨h1, h2⟩

/-- A pair load of `n`-byte elements (`n ≠ 16`) at a pair shape: the two `n`-byte loads at the
component shapes. -/
theorem loadPair_tupleN {t0 t1 : Ty} {n : Nat} {sg : Bool} {mm : Mem} {p q : Ptr} (hn : n ≠ 16) :
    Arm64.loadPair (.tuple [t0, t1]) n sg mm p q =
      .tuple [Arm64.loadN t0 n sg mm p, Arm64.loadN t1 n sg mm q] := by
  simp [Arm64.loadPair, Arm64.loadElt, Arm64.tupleTy, hn]

/-! ## The cases -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {g : G2In} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- `LDPW`/`LDPSW off(Rn), (Ra, Rb)`: the 4 bytes at the address into `Ra`, the 4 bytes above into
`Rb`, zero- or sign-extended (`g4_ldp` at `n = 4`). -/
theorem g50_ldpX (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) {ra rb : Nat} {t0 t1 : Ty} {c0 c1 : Nat}
    (hK : KLe K' (kSet (kSet K ra (some c0)) rb (some c1))) (hpre : PairPre50 lc s v)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {n : Nat} {sg : Bool} {rn oa ob : Int}
    (hpo : pairOp50 v.op = some (as, n, sg, false)) (hsz2 : v.args.size = 2)
    (hax : v.aux = none) (hty : lc.ty v.id = .tuple [t0, t1]) (h0 : cls t0 = some c0)
    (h1 : cls t1 = some c1) (h80 : 8 ≤ c0) (h81 : 8 ≤ c1) (hao : argObj lc v 0 = .ok (64, rn))
    (hma : memArg lc v 1 = .ok ()) (hh : lc.home v.id = some (.pair (some ra) (some rb)))
    (hza : ra ≠ zeroReg) (hzb : rb ≠ zeroReg) (hda : destOK ra = true) (hdb : destOK rb = true)
    (hoa : objOf? ra = some oa) (hob : objOf? rb = some ob)
    (hvs : OneAt2 psA j
      (.ofShape { as, from_ := memA rn v.auxInt.toInt, to := pairA oa ob }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      WPairW ra rb sg m m' := by
  have hl := F.lowered
  have hA := F.addr
  have has4 : (as = .LDPW ∧ sg = false ∨ as = .LDPSW ∧ sg = true) ∧ n = 4 := by
    rcases pairOp50_cases hpo with ⟨-, rfl, rfl, rfl, -⟩ | ⟨-, rfl, rfl, rfl, -⟩ |
      ⟨-, -, -, -, h⟩ | ⟨-, -, -, -, h⟩
    · exact ⟨.inl ⟨rfl, rfl⟩, rfl⟩
    · exact ⟨.inr ⟨rfl, rfl⟩, rfl⟩
    · cases h
    · cases h
  obtain ⟨has', rfl⟩ := has4
  have hnp : v.op ≠ .Phi := by
    intro h; rw [h] at hpo; simp [pairOp50] at hpo
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
    stepLoc_ldPair hl htemp hpo (arr2 hsz2 ha0 ha1) (read_mem hl hah1 hamt hmm) hs
  obtain ⟨X, hX, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  rw [hx] at hX
  cases hX
  obtain ⟨p, q, mm2, bs, bs', hpq, hmm2, hrp, hrq, -⟩ := hpre as 4 sg false hpo a0 x ha0 hx
  rw [hmm] at hmm2
  cases hmm2
  obtain ⟨hap, haq⟩ := pairAddr_noAuxN hax hpq
  obtain ⟨a, hpa, haeq, hnil⟩ :=
    addr_rel hA hMI hxv hxf hap (by omega : 0 < 4) (Or.inr (by rw [hrp]; rfl))
  obtain ⟨a', hqa, haeq', hnil'⟩ :=
    addr_rel hA hMI hxv hxf haq (by omega : 0 < 4) (Or.inr (by rw [hrq]; rfl))
  rw [hpq]
  simp only [Option.elim]
  rw [hty, loadPair_tupleN (by decide), retypeL_pair,
    write_pair hh hty (by rw [h0]; rfl) (by rw [h1]; rfl)]
  have ht0 := cls_ne_bool h0 h80
  have ht1 := cls_ne_bool h1 h81
  have hrel0 : ValRel E.ι ((Arm64.loadN t0 4 sg mm p).retypeL t0)
      (if sg then ProgOp.sextTo64 4 ((readMem m.mem (a + p.off) 4).setWidth 64)
        else (readMem m.mem (a + p.off) 4).setWidth 64) :=
    valRel_retypeL_lo hA h0 ht0 ((lo_loadN hA hMI (by simp) (by omega) ht0 hpa hrp).mono
      (cls_le h0))
  have hrel1 : ValRel E.ι ((Arm64.loadN t1 4 sg mm q).retypeL t1)
      (if sg then ProgOp.sextTo64 4 ((readMem m.mem (a' + q.off) 4).setWidth 64)
        else (readMem m.mem (a' + q.off) 4).setWidth 64) :=
    valRel_retypeL_lo hA h1 ht1 ((lo_loadN hA hMI (by simp) (by omega) ht1 hqa hrq).mono
      (cls_le h1))
  obtain ⟨k, rfl, hk, hok, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
  rw [pc_eta hm hj] at hstar
  obtain ⟨hlm1, hinv1⟩ := finish_reg hm hinv hda (by omega : ka < 32) hoa hrel0
    (fits_retypeL h0 _) (b' := b) (i' := i + 1)
  obtain ⟨hlm2, hinv2⟩ := finish_reg hlm1 hinv1 hdb (by omega : kb < 32) hob hrel1
    (fits_retypeL h1 _) (b' := b) (i' := i + 1)
  rw [hj'] at hlm2
  refine ⟨_, hstar.tail (pstep_at F.nodup F.lt F.ret hk rfl ?_), hlm2, hinv2.mono hK, hsi,
    ka, kb, readMem m.mem (a + p.off) 4, readMem m.mem (a' + q.off) 4, hoa, hob,
    by simp only [wX_pc]⟩
  obtain ⟨has, hf, -, ht', hsc⟩ := Shape.ok_eq hok
  have has'' : psA.toList[k].as = .LDPW ∧ sg = false ∨ psA.toList[k].as = .LDPSW ∧ sg = true := by
    rw [has]; exact has'
  have haeq0 : ({ m with pc := pcAt text psA.toList k } : MState).rX (BitVec.ofNat 5 kn) +
      BitVec.ofInt 64 v.auxInt.toInt = a + p.off := haeq
  have haeq4 : a + p.off + BitVec.ofNat 64 4 = a' + q.off := by
    rw [← haeq, BitVec.add_assoc]; exact haeq'
  rw [progStep_ldpw hkn hka' hkb' (nextAddr_pcAt F.nodup hk) has'' hf hsc ht'
    (by rw [haeq0]; exact hnil) (by rw [haeq0, haeq4]; exact hnil'), haeq0, haeq4]
  simp only [wX_pc]

/-- `FLDPD`/`FLDPS off(Rn), (Fa, Fb)`: the `n` bytes at the address into `V ka`, the `n` bytes
above into `V kb`, each G3's `n`-byte load at its float shape (`fvalRel_of_valRel`). -/
theorem g50_ldpF (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) {ra rb : Nat} {t0 t1 : Ty} {as : As} {n : Nat} {sg : Bool}
    (hK : KLe K' (kSet (kSet K ra (some (8 * n))) rb (some (8 * n)))) (hpre : PairPre50 lc s v)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {rn oa ob : Int}
    (hpo : pairOp50 v.op = some (as, n, sg, true)) (hsz2 : v.args.size = 2)
    (hax : v.aux = none) (hty : lc.ty v.id = .tuple [t0, t1]) (hf0 : fTy t0 = true)
    (hf1 : fTy t1 = true) (h0 : cls t0 = some (8 * n)) (h1 : cls t1 = some (8 * n))
    (hao : argObj lc v 0 = .ok (64, rn))
    (hma : memArg lc v 1 = .ok ()) (hh : lc.home v.id = some (.pair (some ra) (some rb)))
    (hoa : fobjOf? ra = some oa) (hob : fobjOf? rb = some ob)
    (hvs : OneAt2 psA j
      (.ofShape { as, from_ := memA rn v.auxInt.toInt, to := pairA oa ob }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have hasn : (as = .FLDPD ∧ n = 8 ∨ as = .FLDPS ∧ n = 4) ∧ sg = false := by
    rcases pairOp50_cases hpo with ⟨-, -, -, -, h⟩ | ⟨-, -, -, -, h⟩ |
      ⟨-, rfl, rfl, rfl, -⟩ | ⟨-, rfl, rfl, rfl, -⟩
    · cases h
    · cases h
    · exact ⟨.inl ⟨rfl, rfl⟩, rfl⟩
    · exact ⟨.inr ⟨rfl, rfl⟩, rfl⟩
  obtain ⟨has', rfl⟩ := hasn
  have hn48 : n = 4 ∨ n = 8 := by rcases has' with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  have hnp : v.op ≠ .Phi := by
    intro h; rw [h] at hpo; simp [pairOp50] at hpo
  obtain ⟨a1, ha1, hamt, hah1⟩ := memArg_spec hma
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨ka, hka, rfl, hkka⟩ := fobjOf?_some hoa
  obtain ⟨kb, hkb, rfl, hkkb⟩ := fobjOf?_some hob
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨x, hx, rfl⟩ :=
    stepLoc_ldPair hl htemp hpo (arr2 hsz2 ha0 ha1) (read_mem hl hah1 hamt hmm) hs
  obtain ⟨X, hX, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  rw [hx] at hX
  cases hX
  obtain ⟨p, q, mm2, bs, bs', hpq, hmm2, hrp, hrq, hnpp⟩ := hpre as n false true hpo a0 x ha0 hx
  rw [hmm] at hmm2
  cases hmm2
  obtain ⟨hnp0, hnp1⟩ := hnpp rfl t0 t1 hty
  obtain ⟨hap, haq⟩ := pairAddr_noAuxN hax hpq
  obtain ⟨a, hpa, haeq, hnil⟩ :=
    addr_rel hA hMI hxv hxf hap (by omega : 0 < n) (Or.inr (by rw [hrp]; rfl))
  obtain ⟨a', hqa, haeq', hnil'⟩ :=
    addr_rel hA hMI hxv hxf haq (by omega : 0 < n) (Or.inr (by rw [hrq]; rfl))
  rw [hpq]
  simp only [Option.elim]
  rw [hty, loadPair_tupleN (by omega), retypeL_pair,
    write_pair hh hty (by rw [h0]; rfl) (by rw [h1]; rfl)]
  obtain ⟨hty0, -⟩ := fTy_eq hf0 h0
  obtain ⟨hty1, -⟩ := fTy_eq hf1 h1
  have ht0 : t0 ≠ .bool := by rw [hty0]; nofun
  have ht1 : t1 ≠ .bool := by rw [hty1]; nofun
  have hn' : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 := by omega
  have hrel0 : FValRel ((Arm64.loadN t0 n false mm p).retypeL t0)
      ((readMem m.mem (a + p.off) n).setWidth 128) := by
    have hv := valRel_retypeL_lo hA h0 ht0
      ((lo_loadN hA hMI hn' (fun _ => rfl) ht0 hpa hrp).mono (cls_le h0))
    refine fvalRel_of_valRel hA hv hnp0 (fun b' => by rw [hty0]; exact retypeL_int_ne_bool _ b') ?_
    exact BitVec.setWidth_setWidth_of_le _ (by omega)
  have hrel1 : FValRel ((Arm64.loadN t1 n false mm q).retypeL t1)
      ((readMem m.mem (a' + q.off) n).setWidth 128) := by
    have hv := valRel_retypeL_lo hA h1 ht1
      ((lo_loadN hA hMI hn' (fun _ => rfl) ht1 hqa hrq).mono (cls_le h1))
    refine fvalRel_of_valRel hA hv hnp1 (fun b' => by rw [hty1]; exact retypeL_int_ne_bool _ b') ?_
    exact BitVec.setWidth_setWidth_of_le _ (by omega)
  obtain ⟨k, rfl, hk, hok, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hvs m
  rw [pc_eta hm hj] at hstar
  have hlm1 := locMatch_setRegV hm hkka hrel0 (b' := b) (i' := i + 1)
  have hlm2 := locMatch_setRegV hlm1 hkkb hrel1 (b' := b) (i' := i + 1)
  rw [hj'] at hlm2
  have hinv2 := core_setReg (r := rb)
    (core_setReg (r := ra) hinv (fits_retypeL h0 (Arm64.loadN t0 n false mm p)))
    (fits_retypeL h1 (Arm64.loadN t1 n false mm q))
  refine ⟨_, hstar.tail (pstep_at F.nodup F.lt F.ret hk rfl ?_), hlm2, hinv2.mono hK, hsi⟩
  obtain ⟨has, hf, -, ht', hsc⟩ := Shape.ok_eq hok
  have has'' : psA.toList[k].as = .FLDPD ∧ n = 8 ∨ psA.toList[k].as = .FLDPS ∧ n = 4 := by
    rw [has]; exact has'
  have haeq0 : ({ m with pc := pcAt text psA.toList k } : MState).rX (BitVec.ofNat 5 kn) +
      BitVec.ofInt 64 v.auxInt.toInt = a + p.off := haeq
  have haeqn : a + p.off + BitVec.ofNat 64 n = a' + q.off := by
    rw [← haeq, BitVec.add_assoc]; exact haeq'
  rw [progStep_fldp hkn hka hkb (nextAddr_pcAt F.nodup hk) has'' hf hsc ht'
    (by rw [haeq0]; exact hnil) (by rw [haeq0, haeqn]; exact hnil'), haeq0, haeqn]
  rfl

/-- `Select0`/`Select1` of an `FLDPD`/`FLDPS`, homed in the V register of its component at a float
shape: no code (`g47_selF` with a pair home). -/
theorem g50_selF (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {c : ID} {n : Nat} {ra rb i0 r : Nat}
    (hop : v.op = .Select0 ∧ i0 = 0 ∧ r = ra ∨ v.op = .Select1 ∧ i0 = 1 ∧ r = rb)
    (hsz1 : v.args.size = 1) (hc0 : v.args[0]? = some c) (hpt : fpairTys (lc.ty c) n = true)
    (hhc : lc.home c = some (.pair (some ra) (some rb))) (hvh : lc.home v.id = some (.reg r))
    (hcl : ((tupleTys (lc.ty c))[i0]?.bind cls) = cls (lc.ty v.id))
    (hfo : (fobjOf? r).isSome = true) (hfv : fTy (lc.ty v.id) = true)
    (hKr : ∀ c0, cls (lc.ty v.id) = some c0 → K r = some c0)
    (hvs : j' = j) (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hnp : v.op ≠ .Phi := by rcases hop with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun
  obtain ⟨t0, t1, hty, hf0, hf1, h0, h1⟩ := fpairTys_spec hpt
  have hread := read_pair (s := s) hl hhc hty (by rw [h0]; rfl) (by rw [h1]; rfl)
  obtain ⟨x, hx, rfl⟩ := stepLoc_select hl htemp
    (hop.imp (fun h => ⟨h.1, h.2.1⟩) (fun h => ⟨h.1, h.2.1⟩)) (arr1 hsz1 hc0) hs
  rw [hread] at hx
  cases hx
  obtain ⟨t, hsel, hct, hft, hcv⟩ : ∃ t, Tuple.select i0
      [.tuple [(s.reg t0 ra).retypeL t0, (s.reg t1 rb).retypeL t1]] = (s.reg t r).retypeL t ∧
      cls t = some (8 * n) ∧ fTy t = true ∧ cls (lc.ty v.id) = some (8 * n) := by
    rcases hop with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
    · exact ⟨t0, rfl, h0, hf0, by rw [← hcl, hty]; simp [tupleTys, h0]⟩
    · exact ⟨t1, rfl, h1, hf1, by rw [← hcl, hty]; simp [tupleTys, h1]⟩
  rw [hsel, write_reg hvh hcv]
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 hfo
  obtain ⟨kd, -, rfl, hk⟩ := fobjOf?_some ho
  have hrz : r ≠ zeroReg := by have := (objV?_some hk).1; unfold zeroReg; omega
  have hrel : FValRel (((s.reg t r).retypeL t).retypeL (lc.ty v.id))
      (m.v (BitVec.ofNat 5 kd)) := by
    simp only [LocState.reg, beq_iff_eq, hrz, ↓reduceIte]
    cases hv : s.regs[r]? with
    | none => simp only [Option.getD_none, retypeL_poison]; trivial
    | some raw =>
      simp only [Option.getD_some]
      have hfit := hinv.regs r raw (8 * n) hrz hv (hKr _ hcv)
      exact fvalRel_retypeL (fvalRel_retypeLW (vrel_fvalW ((hm.regs r raw hv).2 _ hk) hfit) hfit
        hft hct)
        (fits_retypeL hct _) hfv hcv
  have hlm := locMatch_setRegV hm hk hrel (b' := b) (i' := i + 1)
  have hpc : E.pcOf b (i + 1) = m.pc := by rw [hj', hvs, ← hj, hm.pc]
  rw [hpc, wV_self_pc] at hlm
  exact ⟨m, .refl, hlm, (core_setReg hinv (fits_retypeL hcv _)).mono
    (knext_set hK hnp hvh hcv), hsi⟩

end Cases

/-! ## One value -/

/-- After a float pair load of G50 the upper-bit table is empty. -/
theorem uStep35_ldpF {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value} {as : As}
    {n : Nat} {sg : Bool} (hpo : pairOp50 v.op = some (as, n, sg, true)) : uStep35 lc L v = [] := by
  rcases pairOp50_cases hpo with ⟨-, -, -, -, h⟩ | ⟨-, -, -, -, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · cases h
  · cases h
  all_goals
    simp [uStep35, ldEntry35, loadOp?, narrowLoad?, pairOp35, uStep34, keep34, keep31, keepOp31,
      keepOp34, uStepL, uEntry, narrowLd?, loadIdxOp?, h]

/-- After a word pair load of G50 the upper-bit table holds the zero (`LDPW`) or sign (`LDPSW`)
extension of a word in each register of the pair, and the entries of the other registers. -/
theorem uStep35_ldpX {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value} {as : As}
    {n : Nat} {sg : Bool} (hpo : pairOp50 v.op = some (as, n, sg, false)) :
    uStep35 lc L v = (homeRegs lc v.id).map (fun r => (r, 32, sg)) ++
      L.filter (!(homeRegs lc v.id).contains ·.1) := by
  rcases pairOp50_cases hpo with ⟨h, -, -, rfl, -⟩ | ⟨h, -, -, rfl, -⟩ | ⟨-, -, -, -, h⟩ |
    ⟨-, -, -, -, h⟩
  · rw [uStep35_pairW (ldEntry35_none (by rw [h]; rfl) (by rw [h]; nofun))
      (by simp [pairOp35, h]) (by simp [h])]
    simp [wEntries35, h]
  · rw [uStep35_pairW (ldEntry35_none (by rw [h]; rfl) (by rw [h]; nofun))
      (by simp [pairOp35, h]) (by simp [h])]
    simp [wEntries35, h]
  · cases h
  · cases h

/-- After a select of a float pair load of G50 the upper-bit table is empty. -/
theorem uStep35_selF50 {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v u : Value} {c : ID}
    {as : As} {n : Nat} {sg : Bool} (hop : v.op = .Select0 ∨ v.op = .Select1)
    (hc0 : v.args[0]? = some c) (hu : lc.ctx.f.value? c = some u)
    (hpo : pairOp50 u.op = some (as, n, sg, true)) : uStep35 lc L v = [] := by
  rcases pairOp50_cases hpo with ⟨-, -, -, -, h⟩ | ⟨-, -, -, -, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · cases h
  · cases h
  all_goals
    rcases hop with hop | hop <;>
    simp [uStep35, ldEntry35, loadOp?, narrowLoad?, pairOp35, uStep34, keep34, keep31, keepOp31,
      keepOp34, uStepL, uEntry, narrowLd?, loadIdxOp?, h, hop, hc0, hu]

/-- A select of a word pair load of G50 emits no code: the upper-bit table stays. -/
theorem uStep35_selX50 {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v u : Value} {c : ID}
    {as : As} {n : Nat} {sg : Bool} (hop : v.op = .Select0 ∨ v.op = .Select1)
    (hc0 : v.args[0]? = some c) (hu : lc.ctx.f.value? c = some u)
    (hpo : pairOp50 u.op = some (as, n, sg, false)) : uStep35 lc L v = L := by
  have hl : loadOp? v.op = none := by rcases hop with h | h <;> rw [h] <;> rfl
  refine uStep35_sel (ldEntry35_none hl (by rcases hop with h | h <;> rw [h] <;> nofun)) ?_ hop
  rcases pairOp50_cases hpo with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, -, -, h⟩ | ⟨-, -, -, -, h⟩
  · rcases hop with hop | hop <;> simp [pairOp35, hop, hc0, hu, h]
  · rcases hop with hop | hop <;> simp [pairOp35, hop, hc0, hu, h]
  · cases h
  · cases h

/-- G50's own values are pair loads and selects. -/
theorem vk50_ops {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK50 lc g v kd) :
    VK47 lc g v kd ∨ ((pairOp50 v.op).isSome = true ∨ v.op = .Select0 ∨ v.op = .Select1) := by
  cases h with
  | g47 h => exact .inl h
  | ldpX hpo => exact .inr (.inl (by rw [hpo]; rfl))
  | ldpF hpo => exact .inr (.inl (by rw [hpo]; rfl))
  | selX hop => rcases hop with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  | selF hop => rcases hop with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]

/-- One value of G50's kinds: `vk47_step`'s statement, under `G50Pre`. -/
theorem vk50_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)}
    (hE : G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK50 lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s osp) (hL : UOKL m L)
    (hmem : ∀ x, (v.op = .ARM64MOVDnop ∨ v.op = .ARM64MOVDreg) → v.args[0]? = some x →
      ∃ r c, regHome? lc x = some r ∧ cls (lc.ty x) = some c ∧
        (r, c, lc.signOf lc.ctx.f.valueTab.size x) ∈ L)
    (hpre : G50Pre lc s v)
    (hcall : CallOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hcallz : CallOKZAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hicall : ICallOKAt osp H E (Link.byId sym text az ez ps.toList) ret lc s s' v m)
    (hwb : WbOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s v m) (hclo : CloOK E s v m)
    (hgetg : GetGOK E v) (hmeq : MemEqOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s v m)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp ∧
      UOKL m' (uStep35 lc L v) := by
  have hR := kread_of_reads hreads
  have hempty : ∀ m', UOKL m' [] := fun _ e he => by cases he
  cases hVK with
  | g47 hVK47 =>
    exact vk47_step hE F hhome hcf hv hVK47 hvs htemp hj hj' hreads hm hinv hL hmem hpre.1 hcall
      hcallz hicall hwb hclo hgetg hmeq hs
  | ldpX hpo hsz2 hax hty h0 h1 h80 h81 hao hma hh hne hza hzb hda hdb hoa hob =>
    have hnp : v.op ≠ .Phi := by intro h; rw [h] at hpo; simp [pairOp50] at hpo
    obtain ⟨m', h1', h2', h3', h4', h5'⟩ := g50_ldpX (H := H) F hm hinv.core hinv.slots hR
      (kpair_kStep hnp hh hty h0 h1 hne) hpre.2 hj hj' hpo hsz2 hax hty h0 h1 h80
      h81 hao hma hh hza hzb hda hdb hoa hob hvs htemp hs
    refine ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1', h2', ⟨h3', h4'⟩, ?_⟩
    rw [uStep35_ldpX hpo]
    simp only [homeRegs, hh]
    exact uokl_wpair hL hne h5'
  | ldpF hpo hsz2 hax hty hf0 hf1 h0 h1 hao hma hh hne hoa hob =>
    have hnp : v.op ≠ .Phi := by intro h; rw [h] at hpo; simp [pairOp50] at hpo
    obtain ⟨m', h1', h2', h3', h4'⟩ := g50_ldpF (H := H) F hm hinv.core hinv.slots hR
      (kpair_kStep hnp hh hty h0 h1 hne) hpre.2 hj hj' hpo hsz2 hax hty hf0 hf1 h0 h1
      hao hma hh hoa hob hvs htemp hs
    refine ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1', h2', ⟨h3', h4'⟩, ?_⟩
    rw [uStep35_ldpF hpo]
    exact hempty m'
  | selX hop hsz1 hc0 hu hpo hpt hhc hvh hrz hd hob hcls hcl =>
    obtain ⟨m', h1', h2', h3', h4', hx⟩ := g4_sel (H := H) F hm hinv.core hinv.slots
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz1 hc0 hpt hhc hvh hrz hd hob hcl
      (fun c0 hc0' => ksel4_of_reads hreads hop hc0 hhc (hcl.trans hc0')) hvs htemp hs
    refine ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1', h2', ⟨h3', h4'⟩, ?_⟩
    rw [uStep35_selX50 (hop.imp (·.1) (·.1)) hc0 hu hpo]
    exact fun e he => uok_of_x hx (hL e he)
  | selF hop hsz1 hc0 hu hpo hpt hhc hvh hcls hcl hfo hfv =>
    obtain ⟨m', h1', h2', h3', h4'⟩ := g50_selF (H := H) F hm hinv.core hinv.slots
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz1 hc0 hpt hhc hvh hcl hfo hfv
      (fun c0 hc0' => ksel4_of_reads hreads hop hc0 hhc (hcl.trans hc0')) hvs htemp hs
    refine ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1', h2', ⟨h3', h4'⟩, ?_⟩
    rw [uStep35_selF50 (hop.imp (·.1) (·.1)) hc0 hu hpo]
    exact hempty m'

/-- A nil check of G50's kinds is G7's. -/
theorem vk50_nil {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK50 lc g v kd)
    (hop : v.op = .ARM64LoweredNilCheck) : VK7 lc g v kd := by
  rcases vk50_ops h with h | h
  · exact vk47_nil h hop
  · rcases h with h | h | h <;> rw [hop] at h <;> simp [pairOp50] at h

/-- A bounds check of G50's kinds is G28's. -/
theorem vk50_pb {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK50 lc g v kd)
    (hop : pbOp v.op = true) : VK28 lc g v kd := by
  rcases vk50_ops h with h | h
  · exact vk47_pb h hop
  · rcases pbOp_cases hop with h' | h' | h' | h' <;> rw [h'] at h <;>
      rcases h with h | h | h <;> simp [pairOp50] at h

/-! ## The theorems on G50's check -/

/-- G47's values and G50's pair loads and selects under G50's check, under `G50Pre`. -/
theorem g50L_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG50L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hu : UOKL m (uL35 lc (uIn35 lc bid) blk i))
    (hpre : G50Pre lc s v)
    (hcall : CallOK H E g L lc s s' v m) (hcallz : CallOKZ H E g L lc s s' v m)
    (hicall : ICallOK H E L ret lc s s' v m)
    (hwb : WbOK H E g L lc s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hmeq : MemEqOK H E g L lc s v m) (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' ∧
      UOKL m' (uL35 lc (uIn35 lc bid) blk (i + 1)) := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    obtain ⟨E', m', hx, hE', h1, h2, h3, -⟩ := g33_value (checkG33_of_50L hl hc) hE hbid hb hi hv
      hen hm hinv (by rw [uL31_nl hl]; intro e he; cases he) hpre.1.1.1.1.1.1 hcall hcallz hicall
      hwb hclo hgetg hmeq hs
    refine ⟨E', m', hx, hE', h1, h2, h3, ?_⟩
    rw [uL35_nl hl]
    intro e he
    cases he
  | true =>
  rw [uL35_succ hl hi hv]
  have hE0 := hE
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, hcf, hk, hlt, hnd, hblocks, -, hmovd, -⟩ :=
    checkG50L_spec hl hc
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
  obtain ⟨htemp, hVK⟩ := vkind50_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  rw [kAt_succ hi hv]
  exact vk50_step hE0 F hhome hcf hv hVK hvs htemp hj hj' hreads hm hinv hu
    (fun x hop hx => movdOK35_spec hmovd hbid hb hi hv hop hx)
    hpre hcall hcallz hicall hwb hclo hgetg hmeq hs

/-- `InitMem` under G50's check: `g47L_initMem`'s statement. -/
theorem g50L_initMem {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG50L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hl : lc.ctx.f.lowered = true)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .InitMem) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hpre : MemInit s)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' ∧
      UOKL m' (uL35 lc (uIn35 lc bid) blk (i + 1)) := by
  have hE0 := hE
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, -, -, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, -, -, -, -, -, -, hblocks, -, -, -⟩ := checkG50L_spec hl hc
  obtain ⟨b, j, js, e, next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk, vkind50_initMem hop, vkind47_initMem hop, vkind46_initMem hop, vkind45_initMem hop,
    vkind44_initMem hop] at hkd
  obtain ⟨-, -, ht, -, hh, hmt, rfl⟩ := vkind43_initMem hkd hop
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hpc : E.pcOf bid (i + 1) = E.pcOf bid i := by rw [hj', hj, hvs]
  have hss : s' = s := by
    rw [stepLoc_initMem hl ht hop hh hmt hs]
    exact congrArg (fun x => { s with mem := x }) hpre.symm
  subst hss
  have hK : kAt c.cx.lc kt bid blk (i + 1) = kAt c.cx.lc kt bid blk i := by
    rw [kAt_succ hi hv, kStep_none (by rw [hh]; nofun) (by rw [hh]; nofun) (by rw [hh]; nofun)]
  refine ⟨E, m, ⟨rfl, fun _ _ h => h⟩, hE0, .refl, locMatch_pc hm (hpc.trans hm.pc.symm),
    hK ▸ hinv, ?_⟩
  rw [uL35_succ hl hi hv, uStep35_initMem hop]
  intro e he
  cases he

/-- G38's nil panics under G50's check. -/
theorem g50L_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG50L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  cases hl : lc.ctx.f.lowered with
  | false => exact g33_nilPanic (checkG33_of_50L hl hc) hE hbid hb hi hv hop hm hinv hs
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, -⟩ :=
    checkG50L_spec hl hc
  obtain ⟨b, j, js, e', next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk] at hkd
  obtain ⟨-, hVK⟩ := vkind50_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases vk50_nil hVK hop with
  | g6 hne _ => exact absurd hop hne
  | nil _ hsz2 _ _ hao hma =>
    exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma hvs hs

/-- G38's bounds panics under G50's check. -/
theorem g50L_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG50L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hbok : BoundsOK H g L ps.toList)
    (hs : stepLoc env lc s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    exact g33_boundsPanic (checkG33_of_50L hl hc) hE hbid hb hi hv hop hm hinv hbok hs
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, hsyms, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, hpb, -, -⟩ :=
    checkG50L_spec hl hc
  obtain ⟨b, j, js, e', next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk] at hkd
  have hen : entryOp24 v.op = false := by
    rcases pbOp_cases hop with h | h | h | h <;> rw [h] <;> rfl
  obtain ⟨-, hVK⟩ := vkind50_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  exact vk28_boundsPanic F hsyms hpb hrow hb hi hv (vk50_pb hVK hop) hvs hj hreads hop hm hinv
    hbok hs

/-- G38's terminators under G50's check. -/
theorem g50L_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG50L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (hu : UOKL m (uL35 lc (uIn35 lc bid) blk blk.values.size))
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList ∧ UOKL m' (uIn35 lc e.b) := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g33_term (checkG33_of_50L hl hc) hE hbid hb hm hinv hpre
      (by rw [uL31_nl hl]; intro e he; cases he) ht
    refine ⟨m', h1, h2, h3, h4, ?_⟩
    rw [uIn35_nl hl]
    intro e he
    cases he
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, hedges⟩ :=
    checkG50L_spec hl hc
  obtain ⟨m', h1, h2, h3, h4, he, hx⟩ := termK_stepX hpcOf
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb hm hinv hpre ht
  refine ⟨m', h1, h2, h3, h4, fun x hxin => ?_⟩
  exact uok_of_x hx (hu x (uEdgesOK35_edge hedges hbid hb he x hxin))

/-! ## The slice: the theorems on `checkG50 lc`, on `liveCtx lc` -/

/-- **G50, values.** `g47_value`'s statement over `checkG50`, under `G50Pre` (G46's premise and
`PairPre50`: a pair load reads valid bytes at both addresses, and an `FLDPD`/`FLDPS` reads no
pointer at its component shapes). -/
theorem g50_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG50 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s)
    (hu : UOKL m (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk i))
    (hpre : G50Pre (liveCtx lc) s v)
    (hcall : CallOK H E g L (liveCtx lc) s s' v m) (hcallz : CallOKZ H E g L (liveCtx lc) s s' v m)
    (hicall : ICallOK H E L ret (liveCtx lc) s s' v m)
    (hwb : WbOK H E g L (liveCtx lc) s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hmeq : MemEqOK H E g L (liveCtx lc) s v m) (hs : stepLoc env (liveCtx lc) s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env (liveCtx lc) g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' (liveCtx lc) (kAt (liveCtx lc) kt bid blk (i + 1)) s' ∧
      UOKL m' (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk (i + 1)) :=
  g50L_value (checkG50_spec hc).2 hE hbid hb hi hv hen hm hinv hu hpre hcall hcallz hicall hwb hclo
    hgetg hmeq hs

/-- **G50, `InitMem`.** `g47_initMem`'s statement over `checkG50`. -/
theorem g50_initMem {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG50 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hl : lc.ctx.f.lowered = true)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .InitMem) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s) (hpre : MemInit s)
    (hs : stepLoc env (liveCtx lc) s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env (liveCtx lc) g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' (liveCtx lc) (kAt (liveCtx lc) kt bid blk (i + 1)) s' ∧
      UOKL m' (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk (i + 1)) :=
  g50L_initMem (checkG50_spec hc).2 hE hl hbid hb hi hv hop hm hinv hpre hs

/-- **G50, nil panics.** `g47_nilPanic`'s statement over `checkG50`. -/
theorem g50_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG50 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s)
    (hs : stepLoc env (liveCtx lc) s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e :=
  g50L_nilPanic (checkG50_spec hc).2 hE hbid hb hi hv hop hm hinv hs

/-- **G50, bounds panics.** `g47_boundsPanic`'s statement over `checkG50`. -/
theorem g50_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG50 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s)
    (hbok : BoundsOK H g L ps.toList) (hs : stepLoc env (liveCtx lc) s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' :=
  g50L_boundsPanic (checkG50_spec hc).2 hE hbid hb hi hv hop hm hinv hbok hs

/-- **G50, terminators.** `g47_term`'s statement over `checkG50`. -/
theorem g50_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG50 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk blk.values.size) s)
    (hpre : G1TermPre (liveCtx lc) s blk)
    (hu : UOKL m (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk blk.values.size))
    (ht : stepTermLoc (liveCtx lc) s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧
      G3Inv E (liveCtx lc) (kt.at e.b) s' ∧ e.b ∈ lc.ctx.f.blocks.toList ∧
      UOKL m' (uIn35 (liveCtx lc) e.b) :=
  g50L_term (checkG50_spec hc).2 hE hbid hb hm hinv hpre hu ht

end GoFV.Proof.Gen

import GoFV.Proof.Gen.G61b
import GoFV.Proof.Gen.G61c
import GoFV.Proof.Gen.G61d
import GoFV.Proof.Gen.G49

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G61, group A: one value (`docs/plans/proofs3.md` §4)

`vk61a_step` is one value `VK61a` (`Spec61a.lean`) accepted, in `vk59p_step`'s form, at either
mode `osp`: each family's case lemma (`g61_xchg` in `G61a.lean`, `g61_add` and `g61_logic` in
`G61b.lean`, `g61_cas` in `G61c.lean`, `g61_lse` and `g61_casV` in `G61d.lean`), the components by
G38's `g38_sel0`/`g38_sel1` (homed as an acquire load's). The loops' branch targets are
`atomOK`'s, at the value's start `j` (`hatom`). The class table follows the value into its
register (`kldar_kStep`) and the upper-bit table is empty after it (`uStep35_atom61`,
`uStep35_selAtom61`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-- The upper-bit table is empty after an atomic of group A. -/
theorem uStep35_atom61 {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value} {f : AtomF61}
    {n : Nat} (hop : atom61? v.op = some (f, n)) : uStep35 lc L v = [] := by
  generalize ho : v.op = o at hop
  unfold atom61? at hop
  split at hop <;>
  first
    | (simp [uStep35, ldEntry35, loadOp?, narrowLoad?, pairOp35, uStep34, keep34, keep31,
        keepOp31, keepOp34, uStepL, uEntry, narrowLd?, loadIdxOp?, ho]; done)
    | cases hop

/-- The upper-bit table is empty after a component of an atomic of group A. -/
theorem uStep35_selAtom61 {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value} {c : ID}
    (hop : v.op = .Select0 ∨ v.op = .Select1) (hc : v.args[0]? = some c)
    (hu : ((lc.ctx.f.value? c).any fun u => (atom61? u.op).isSome) = true) :
    uStep35 lc L v = [] := by
  cases hcv : lc.ctx.f.value? c with
  | none => rw [hcv] at hu; cases hu
  | some u =>
    rw [hcv] at hu
    simp only [Option.any_some] at hu
    have hpu : (u.op == .ARM64LDP || u.op == .ARM64LDPW || u.op == .ARM64LDPSW ||
        u.op == .ARM64LDAR || u.op == .ARM64LDARW || u.op == .ARM64LDARB) = false := by
      have key : ∀ o : Op, (atom61? o).isSome = true → (o == .ARM64LDP || o == .ARM64LDPW ||
          o == .ARM64LDPSW || o == .ARM64LDAR || o == .ARM64LDARW || o == .ARM64LDARB) = false := by
        intro o h
        unfold atom61? at h
        split at h <;> first | decide | cases h
      exact key _ hu
    rcases hop with hop | hop <;>
      simp [uStep35, ldEntry35, loadOp?, narrowLoad?, pairOp35, uStep34, keep34, keep31,
        keepOp31, keepOp34, uStepL, uEntry, narrowLd?, loadIdxOp?, hop, hc, hcv, hpu]

/-- One value of G61's group A: it runs its Progs and keeps the activation (`G49Env`), the match
and `G3Inv` at either mode `osp`, and empties the upper-bit table; the loops' branch targets are
`atomOK`'s at the value's start (`hatom`). -/
theorem vk61a_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)} {osp : Bool}
    (hE : G49Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hcf : checkFrame lc g = .ok ())
    (hVK : VK61a lc v kd) (hvs : VStep2 ps kd j j')
    (hatom : ∀ f n, atom61? v.op = some (f, n) → atomTgt f ps j = true)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s osp)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp ∧
      UOKL m' (uStep35 lc L v) := by
  obtain ⟨hlcE, -, -, -, -, -, -, -, -, -, hF⟩ := hE.env.env.env.env.env
  have hsz := slot_sizes hlcE hcf hinv.slots
  have hR := kread_of_reads hreads
  have fin : ∀ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' →
      LocMatch E s' bid (i + 1) m' → CoreInv E.ι (StkAt E) (kStep lc K v).get s' osp →
      SlotInv lc s' → uStep35 lc L v = [] →
      ∃ E' m', E.Extends E' ∧ G49Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
        PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
        LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp ∧
        UOKL m' (uStep35 lc L v) := fun m' h1 h2 h3 h4 h5 =>
    ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩, by rw [h5]; exact fun e he => by cases he⟩
  cases hVK with
  | @rmw f n t0 rp rv rd rt r hop hf1 hf2 hsz3 _ hty hc0 hap hpr hpz hav hvr hma hh hrz hd hor
      hdp hdv htmp =>
    have hnp : v.op ≠ .Phi := (atom61?_facts hop).1
    have hKs := kldar_kStep (K := K) hnp hh hty hc0
    have hu := uStep35_atom61 (lc := lc) (L := L) hop
    have htgt := hatom f n hop
    rcases htmp with ⟨htemp, hfa, hfo, rfl⟩ | ⟨t, ht, hf, hto, htz, htd, htp, htr⟩
    · cases f with
      | xchg =>
        obtain ⟨m', h1, h2, h3, h4⟩ := g61_xchg (H := H) F hF hsz hm hinv.core hinv.slots hR hj
          hj' hop hsz3 hty hc0 hap hpz hav hma hh hrz hd hor hdp hdv htemp hvs htgt hs
        exact fin m' h1 h2 (h3.mono hKs) h4 hu
      | add =>
        obtain ⟨m', h1, h2, h3, h4⟩ := g61_add (H := H) F hF hsz hm hinv.core hinv.slots hR hj
          hj' hop hsz3 hty hc0 hap hpz hav hma hh hrz hd hor hdp hdv htemp hvs htgt hs
        exact fin m' h1 h2 (h3.mono hKs) h4 hu
      | cas => exact absurd rfl hf1
      | casV => exact absurd rfl hf2
      | andL => exact absurd rfl hfa
      | orL => exact absurd rfl hfo
      | xchgV | addV | andV | orV =>
        obtain ⟨m', h1, h2, h3, h4⟩ := g61_lse (H := H) F hF hsz hm hinv.core hinv.slots hR hj
          hj' hop (by simp) hsz3 hty hc0 hap hpr hpz hav hvr hma hh hrz hd hor hdp hdv htemp hvs
          hs
        exact fin m' h1 h2 (h3.mono hKs) h4 hu
    · obtain ⟨m', h1, h2, h3, h4⟩ := g61_logic (H := H) F hF hsz hm hinv.core hinv.slots hR hj
        hj' hop hf hsz3 hty hc0 hap hpz hav hma hh hrz hd hor hdp hdv ht hto htz htd htp htr hvs
        htgt hs
      exact fin m' h1 h2 (h3.mono hKs) h4 hu
  | @cas f n t0 rp ro rn rd r hop hf htemp hsz4 _ hty hc0 hap hpr hpz hao hor27 han hnr hma hh
      hrz hd hor =>
    have hnp : v.op ≠ .Phi := (atom61?_facts hop).1
    have hKs := kldar_kStep (K := K) hnp hh hty hc0
    have hu := uStep35_atom61 (lc := lc) (L := L) hop
    rcases hf with rfl | rfl
    · obtain ⟨m', h1, h2, h3, h4⟩ := g61_cas (H := H) F hF hsz hm hinv.core hinv.slots hR hj hj'
        hop htemp hsz4 hty hc0 hap hpr hpz hao hor27 han hnr hma hh hrz hd hor hvs
        (hatom _ _ hop) hs
      exact fin m' h1 h2 (h3.mono hKs) h4 hu
    · obtain ⟨m', h1, h2, h3, h4⟩ := g61_casV (H := H) F hF hsz hm hinv.core hinv.slots hR hj
        hj' hop htemp hsz4 hty hc0 hap hpr hpz hao hor27 han hnr hma hh hrz hd hor hvs hs
      exact fin m' h1 h2 (h3.mono hKs) h4 hu
  | @sel0 c r t0 htemp hop hsz hc0 hu htc hct hhc hvh hrz hd hob hcls hcl =>
    obtain ⟨cv, hcv⟩ := Option.isSome_iff_exists.1 hcls
    have hKr : ∀ c0, cls (lc.ty v.id) = some c0 → K.get r = some c0 := fun c0 hc0' => by
      have h0 : cls t0 = some c0 := hcl.trans hc0'
      exact ksel38_of_reads hreads hop hc0 hhc (by rw [htc]; simpa [tupleTys] using h0)
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g38_sel0 (H := H) F hm hinv.core hinv.slots
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hc0 htc hhc hvh hrz hd hob hcv hcl
      hKr hvs htemp hs
    exact fin m' h1 h2 h3 h4 (uStep35_selAtom61 (.inl hop) hc0 hu)
  | sel1 htemp hop hsz hc0 hu htc hct hhc hmt hhn =>
    have hpc : E.pcOf bid (i + 1) = E.pcOf bid i := by rw [hj', hj, hvs]
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g38_sel1 (H := H) F hm hinv.core hinv.slots
      (knext_kStep fun _ => (hs_none hhn).noRegs) hpc hop hsz hc0 htc hct hhc hmt hhn htemp hs
    exact fin m' h1 h2 h3 h4 (uStep35_selAtom61 (.inr hop) hc0 hu)

end GoFV.Proof.Gen

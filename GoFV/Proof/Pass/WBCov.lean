import GoFV.Proof.Pass.WBNpOrder

/-!
# writebarrier: the source facts of the chain's values (issue #36)

`cov_intro`: a value of the chain has its source facts (`Cov`) when the source evaluated, in the
reference frame, every value of a set `P` closed under in-block arguments that contains the value
itself (kept, role `held`) or the run its role copies (stores and dropped nil check), and the
run's memory is a memory for a `WB`. `runMem_of_ev`: a run whose first store the source evaluated
has a memory. `grOK_panic`: the reference frame of a block entry that panics after the prefix
`pre` of its schedule.
-/

namespace GoFV.Proof.WB

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Opt GoFV.Opt.WBCheck GoFV.Proof
open GoFV.Proof.MemInv (SInv ContractsOK sinv_evalAll sinv_phis)

private theorem thenRole_ne' {v : Value} {j a k : Nat} :
    thenRole v j ≠ .tgt a k ∧ thenRole v j ≠ .ncEnd a := by
  constructor <;>
  · intro h
    unfold thenRole at h
    repeat' split at h
    all_goals cases h

private theorem roleRun_tgt' {g : Func} {x : ID} :
    ∀ {rs : List Run} {k j k' : Nat}, roleRun g x rs k = .tgt j k' →
      k ≤ j ∧ ∃ r, rs[j - k]? = some r ∧ r.tgt[k']? = some x
  | [], _, _, _, h => by rw [roleRun] at h; cases h
  | r :: rs, k, j, k', h => by
    rw [roleRun] at h
    by_cases h1 : (x == r.sp.load) = true
    · rw [if_pos h1] at h; cases h
    rw [if_neg h1] at h
    by_cases h2 : (x == r.sp.flag) = true
    · rw [if_pos h2] at h; cases h
    rw [if_neg h2] at h
    by_cases h3 : (x == r.phi) = true
    · rw [if_pos h3] at h; cases h
    rw [if_neg h3] at h
    by_cases h4 : (r.ncEnd == some x) = true
    · rw [if_pos h4] at h; cases h
    rw [if_neg h4] at h
    cases hk : r.tgt.idxOf? x with
    | some k'' =>
      rw [hk] at h
      dsimp only at h
      cases h
      obtain ⟨hlt, heq, -⟩ := List.idxOf?_eq_some_iff.1 hk
      exact ⟨Nat.le_refl _, r, by simp, List.getElem?_eq_some_iff.2 ⟨hlt, heq⟩⟩
    | none =>
      rw [hk] at h
      dsimp only at h
      by_cases h5 : (vals g r.sp.t).contains x = true
      · rw [if_pos h5] at h
        cases hv : g.value? x with
        | none => rw [hv] at h; cases h
        | some v =>
          rw [hv] at h
          exact absurd h thenRole_ne'.1
      · rw [if_neg h5] at h
        obtain ⟨hk', r', hr', hx⟩ := roleRun_tgt' h
        refine ⟨by omega, r', ?_, hx⟩
        rw [show j - k = (j - (k + 1)) + 1 by omega]
        simpa using hr'

private theorem roleRun_ncEnd' {g : Func} {x : ID} :
    ∀ {rs : List Run} {k j : Nat}, roleRun g x rs k = .ncEnd j →
      k ≤ j ∧ ∃ r, rs[j - k]? = some r ∧ r.ncEnd = some x
  | [], _, _, h => by rw [roleRun] at h; cases h
  | r :: rs, k, j, h => by
    rw [roleRun] at h
    by_cases h1 : (x == r.sp.load) = true
    · rw [if_pos h1] at h; cases h
    rw [if_neg h1] at h
    by_cases h2 : (x == r.sp.flag) = true
    · rw [if_pos h2] at h; cases h
    rw [if_neg h2] at h
    by_cases h3 : (x == r.phi) = true
    · rw [if_pos h3] at h; cases h
    rw [if_neg h3] at h
    by_cases h4 : (r.ncEnd == some x) = true
    · rw [if_pos h4] at h; cases h
      exact ⟨Nat.le_refl _, r, by simp, by simpa using h4⟩
    rw [if_neg h4] at h
    cases hk : r.tgt.idxOf? x with
    | some k'' => rw [hk] at h; dsimp only at h; cases h
    | none =>
      rw [hk] at h
      dsimp only at h
      by_cases h5 : (vals g r.sp.t).contains x = true
      · rw [if_pos h5] at h
        cases hv : g.value? x with
        | none => rw [hv] at h; cases h
        | some v =>
          rw [hv] at h
          exact absurd h (thenRole_ne' (k := 0)).2
      · rw [if_neg h5] at h
        obtain ⟨hk', r', hr', hx⟩ := roleRun_ncEnd' h
        refine ⟨by omega, r', ?_, hx⟩
        rw [show j - k = (j - (k + 1)) + 1 by omega]
        simpa using hr'

private theorem roleOf_run' {c : WBCheck.Ctx} {rs : List Run} {x : ID} {ρ : Role}
    (h : c.roleOf rs x = ρ) (hρ : ρ ≠ .wbaddr ∧ ρ ≠ .const0 ∧ ρ ≠ .held ∧ ρ ≠ .lazy ∧
      ρ ≠ .invalid ∧ ρ ≠ .none) : roleRun c.g x rs 0 = ρ := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hρ
  unfold Ctx.roleOf at h
  by_cases h1 : c.isWbaddr x = true
  · rw [if_pos h1] at h; exact absurd h.symm n1
  rw [if_neg h1] at h
  by_cases h2 : c.isConst0 x = true
  · rw [if_pos h2] at h; exact absurd h.symm n2
  rw [if_neg h2] at h
  by_cases h3 : c.held x = true
  · rw [if_pos h3] at h; exact absurd h.symm n3
  rw [if_neg h3] at h
  revert h
  generalize roleRun c.g x rs 0 = R
  intro h
  cases R
  case none =>
    exfalso
    dsimp only at h
    unfold otherRole at h
    repeat' split at h
    · exact n5 h.symm
    · exact n4 h.symm
    · exact n6 h.symm
    · exact n6 h.symm
  all_goals exact h

private theorem roleOf_tgt' {c : WBCheck.Ctx} {rs : List Run} {x : ID} {j k : Nat}
    (h : c.roleOf rs x = .tgt j k) : ∃ r, rs[j]? = some r ∧ r.tgt[k]? = some x := by
  obtain ⟨-, r, hr, hx⟩ := roleRun_tgt' (roleOf_run' h (by simp))
  exact ⟨r, by simpa using hr, hx⟩

private theorem roleOf_ncEnd' {c : WBCheck.Ctx} {rs : List Run} {x : ID} {j : Nat}
    (h : c.roleOf rs x = .ncEnd j) : ∃ r, rs[j]? = some r ∧ r.ncEnd = some x := by
  obtain ⟨-, r, hr, hx⟩ := roleRun_ncEnd' (roleOf_run' h (by simp))
  exact ⟨r, by simpa using hr, hx⟩

private theorem roleOK_val' {c : WBCheck.Ctx} {b : ID} {B : Block} {segs : List ID}
    {rs : List Run} {inT : Bool} {j : Nat} {x : ID} (h : c.roleOK b B segs rs inT j x = true) :
    ∃ w, c.g.value? x = some w := by
  unfold Ctx.roleOK at h
  split at h
  · cases h
  · exact ⟨_, ‹_›⟩

namespace Setup

variable {c : WBCheck.Ctx} {b : ID} {B : Block} {rs : List Run} {l : ID}

private theorem run_ok' (S : Setup c b B rs l) {j : Nat} {r : Run} (hr : rs[j]? = some r) :
    c.runOK b B (segsOf b rs) rs j r = true :=
  (blockOK_spec S.ok S.hB S.ch).2.2.2.2.1 j r hr

private theorem run_of' (S : Setup c b B rs l) {j : Nat} {r : Run} (hr : rs[j]? = some r) :
    runOf? c.f c.g r.sp = some r :=
  ((chainRuns_spec S.ch).1 j r hr).2.2.2

/-- The dropped nil check of a run is in a closed set containing the run's stores and its
dropped nil checks. -/
private theorem nc_P (S : Setup c b B rs l) {P : ID → Prop}
    (hPcl : ∀ x a v, P x → c.f.value? x = some v → a ∈ v.args → a ∈ B.values →
      (∀ va, c.f.value? a = some va → va.op ≠ .Phi) → P a)
    {j : Nat} {r : Run} (hr : rs[j]? = some r)
    (hrun : (∀ s ∈ r.src, P s) ∧ (∀ n ∈ ncsOf c r, P n)) {n : ID} (hn : r.nc = some n) : P n := by
  by_cases hK : c.K.getD n false = true
  · obtain ⟨x0, v0, a, nv, hx0, hv0, -, ha, hnv, hnop, -, hnid⟩ :=
      (runOf_spec (run_of' S hr)).2.2.2.2.1 n hn
    obtain ⟨ce, hwf⟩ := S.wf
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hsrc, hnc⟩ := runOK_spec (run_ok' S hr)
    have hx0B := (hsrc x0 (List.mem_of_getElem? hx0)).1
    have hau : a ∈ v0.args := Array.mem_iff_getElem?.2 ⟨0, ha⟩
    obtain ⟨bid, blk, hbin, hablk⟩ := hwf.argListed b B x0 v0 ⟨⟨S.hb, S.hB⟩, hx0B, hv0⟩ a hau
    obtain ⟨va, hva, hvid, -⟩ := hwf.valueId bid blk hbin a hablk
    rw [hnv] at hva; cases hva
    have han : a = n := hvid.symm.trans hnid
    subst han
    obtain ⟨hnB, -⟩ := hnc a hn
    exact hPcl x0 a v0 (hrun.1 x0 (List.mem_of_getElem? hx0)) hv0 hau hnB
      fun va' hva' => by rw [hnv] at hva'; cases hva'; rw [hnop]; exact fun h => by cases h
  · have hK' : c.K.getD n false = false := by simpa using hK
    exact hrun.2 n (by simp [ncsOf, hn, hK'])

/-- A run whose first store the source evaluated: its memory is a memory. -/
theorem runMem_of_ev (S : Setup c b B rs l) {env : Env} {Gr : Frame} {j : Nat} {r : Run}
    (hr : rs[j]? = some r) {s0 : ID} (hs0 : r.src[0]? = some s0) (hev : Ev env c Gr s0) :
    ∃ M, RunMem Gr rs j M := by
  obtain ⟨u, y, hu, -, hev'⟩ := hev
  obtain ⟨-, -, -, hsrc, -⟩ := runOf_spec (run_of' S hr)
  obtain ⟨u', hu', hop, hlast⟩ := hsrc 0 s0 hs0
  rw [hu] at hu'; cases hu'
  obtain ⟨L, r0, hL, hop0, -⟩ := evalValue_inv hev'
  rw [DAE.evalOp_memRoot (by rcases hop with h | h | h <;> simp [h])] at hop0
  have hM : ∃ M, L.getLast? = some (.mem M) := by
    rcases hop with h | h | h
    · obtain ⟨a, q, x, M, M', rfl, -, -, -⟩ := store_inv h hop0; exact ⟨M, rfl⟩
    · obtain ⟨M, n, rfl, -⟩ := varDef_inv h hop0; exact ⟨M, rfl⟩
    · obtain ⟨M, rfl, -⟩ := varLive_inv h hop0; exact ⟨M, rfl⟩
  obtain ⟨M, hM⟩ := hM
  rw [List.getLast?_eq_getElem?] at hlast hM
  rw [regsAre_length hL] at hM
  obtain ⟨z, hz, hreg⟩ := regsAre_get hL hlast
  rw [hM] at hz; cases hz
  exact ⟨M, r, hr, hreg⟩

/-- **Source facts from a closed set of evaluated values.** -/
theorem cov_intro (S : Setup c b B rs l) {env : Env} {Gr : Frame} {P : ID → Prop}
    (hEv : ∀ x, P x → Ev env c Gr x)
    (hPcl : ∀ x a v, P x → c.f.value? x = some v → a ∈ v.args → a ∈ B.values →
      (∀ va, c.f.value? a = some va → va.op ≠ .Phi) → P a)
    {x : ID}
    (hheld : c.roleOf rs x = .held → c.K.getD x false = true →
      (∀ u, c.f.value? x = some u → u.op ≠ .Phi) → P x)
    (hrun : ∀ j, ((∃ k, c.roleOf rs x = .tgt j k) ∨ c.roleOf rs x = .ncEnd j ∨
        c.roleOf rs x = .ncThen j) →
      ∀ r, rs[j]? = some r → (∀ s ∈ r.src, P s) ∧ (∀ n ∈ ncsOf c r, P n))
    (hwb : ∀ j, c.roleOf rs x = .wb j → ∃ M, RunMem Gr rs j M) :
    Cov env c rs Gr x := by
  cases hρ : c.roleOf rs x with
  | held =>
    simp only [Cov, hρ]
    intro hK u hu hnp
    exact hEv x (hheld hρ hK fun u' hu' => by rw [hu] at hu'; cases hu'; exact hnp)
  | tgt j k =>
    simp only [Cov, hρ]
    obtain ⟨r, hr, htk⟩ := roleOf_tgt' hρ
    obtain ⟨-, -, -, -, -, hlen, -⟩ := runOK_spec (run_ok' S hr)
    have hk : k < r.src.length := by
      rw [hlen]; exact (List.getElem?_eq_some_iff.1 htk).1
    refine ⟨r, r.src[k], hr, List.getElem?_eq_getElem hk, hEv _ ?_⟩
    exact (hrun j (.inl ⟨k, hρ⟩) r hr).1 _ (List.getElem_mem hk)
  | ncEnd j =>
    simp only [Cov, hρ]
    obtain ⟨r, hr, hnE⟩ := roleOf_ncEnd' hρ
    obtain ⟨-, h2, -, -, -, -, -, -, -, hncE, -⟩ := runOK_spec (run_ok' S hr)
    have hok := (blockOK_spec S.ok S.hB S.ch).2.2.2.2.2.2.1 (j + 1) r.sp.e h2 x (hncE x hnE)
    obtain ⟨w, hw⟩ := roleOK_val' hok
    obtain ⟨-, -, r', n, hr', hn, -⟩ := roleOK_ncEnd hok hw hρ
    rw [hr] at hr'; cases hr'
    exact ⟨r, n, hr, hn, hEv n (nc_P S hPcl hr (hrun j (.inr (.inl hρ)) r hr) hn)⟩
  | ncThen j =>
    simp only [Cov, hρ]
    obtain ⟨r, hr, hxT, -⟩ := roleOf_then (o := .NilCheck) (j := j) (by rw [hρ]; rfl)
    obtain ⟨-, -, ⟨T, hT, -, -, -, -, -, hall⟩, -⟩ := runOK_spec (run_ok' S hr)
    rw [vals_of hT] at hxT
    have hok := hall x hxT
    obtain ⟨w, hw⟩ := roleOK_val' hok
    obtain ⟨-, -, r', n, hr', hn, -⟩ := roleOK_ncThen hok hw hρ
    rw [hr] at hr'; cases hr'
    exact ⟨r, n, hr, hn, hEv n (nc_P S hPcl hr (hrun j (.inr (.inr hρ)) r hr) hn)⟩
  | wb j =>
    simp only [Cov, hρ]
    exact hwb j hρ
  | _ => simp only [Cov, hρ]

/-- **The reference frame of a panicking block entry.** -/
theorem grOK_panic (S : Setup c b B rs l) (hall : ∀ b' ∈ c.f.blocks, c.blockOK b' = true)
    {ce : CheckEnv} (hwf : WF ce c.f) (hcf : CertOK c.f) {env : Env} (hE : ContractsOK MemOK env)
    {frS frT : Frame} {i : Nat} (hA : SimAt env c frS frT b i) {ps : List (ID × Val)}
    (hps : B.values.toList.filterMapM (phiStep (Ctx.make c.tabs c.f) frS i) = .ok ps)
    {o : Array ID} (ho : schedule c.f B = some o) {pre post : List ID} {r : ID}
    (hsplit : o.toList = pre ++ r :: post) {Gpre : Frame}
    (hpre : evalAll env (Ctx.make c.tabs c.f) { frS with regs := setPhis ps frS.regs } pre =
      .ok Gpre)
    (hGf : Gpre = { frS with regs := Gpre.regs })
    (hGo : ∀ z, z ∉ B.values → Gpre.regs[z]? = frS.regs[z]?)
    (hGv : ∀ x ∈ pre, ∃ v y, c.f.value? x = some v ∧ Gpre.regs[x]? = some (some y) ∧
      evalValue env (Ctx.make c.tabs c.f) Gpre v = .ok y) :
    GrOK c B rs Gpre frS := by
  have hown := valuesOwn hwf S.hb S.hB
  have hnd := hwf.valuesNodup b B ⟨S.hb, S.hB⟩
  obtain ⟨ond, otopo, omem⟩ := schedule_topo hown hnd ho
  have hpo : ∀ z ∈ pre, z ∈ o.toList := fun z hz => by rw [hsplit]; simp [hz]
  have hsinv : SInv MemOK Gpre := sinv_evalAll memOK_pred hE hwf S.memTy
    (fun x hx => ⟨b, S.hb, by rw [vals_of S.hB]; exact ((omem x).1 (hpo x hx)).1⟩)
    (sinv_phis hA.sinv hps) hpre
  refine S.grOK hall hA hGf hsinv hGo ?_ ?_
  · intro hb a haB y hy _
    by_cases hap : a ∈ pre
    · obtain ⟨v, y', hv, hy', hev⟩ := hGv a hap
      exact ⟨v, y', hv, hy', hev⟩
    · exfalso
      rw [hsplit] at ond otopo
      obtain ⟨-, -, e3, -⟩ := evalAll_spec (List.nodup_append.1 ond).1 (topoRem_prefix otopo)
        ((setPhis_size ps frS.regs).trans hA.sizeS) hpre
      rw [e3 a hap] at hy
      change (setPhis ps frS.regs)[a]? = some (some y) at hy
      obtain ⟨-, -, hkeep, hphi⟩ := phis_spec hnd hps
      obtain ⟨v, hv, -⟩ := hown a haB
      by_cases hp : v.op = .Phi
      · have hlt : a < frS.regs.size := hA.sizeS ▸ lt_of_value? hv
        obtain ⟨a', y', ha', -⟩ := hphi a haB v hv hp hlt
        have hsz := hwf.phiArity b B a v ⟨⟨S.hb, S.hB⟩, haB, hv⟩ hp
        have hB0 := hwf.entryPreds B (by rw [← hb]; exact S.hB)
        rw [Array.getElem?_eq_none (by omega)] at ha'
        cases ha'
      · rw [hkeep a (.inr ⟨v, hv, hp⟩)] at hy
        exact hA.entry hb a y hy
  · intro a hh haB ⟨y, hyB, u, hu, hnp, hau⟩
    rw [hGo a haB]
    have hd := pre_strict hcf hA.pre
    obtain ⟨-, hbT⟩ := pre_tree hwf hcf hA.pre
    have huse := hcf.domRel.uses S.hb S.hB hbT hyB hu hnp hau
    obtain ⟨bid, blk, ⟨hbid, hblk⟩, hablk⟩ := hwf.argListed b B y u ⟨⟨S.hb, S.hB⟩, hyB, hu⟩ a hau
    obtain ⟨va, hva, -, hvab⟩ := hwf.valueId bid blk ⟨hbid, hblk⟩ a hablk
    have hba : blockOf c.f a = bid := by unfold blockOf; rw [hva]; exact hvab
    rw [hba] at huse
    have hne : bid ≠ b := fun h => by
      subst h; rw [S.hB] at hblk; cases hblk; exact haB hablk
    obtain ⟨z, hz, -⟩ := hd a va ⟨hva, hvab ▸ hbid, blk, hvab ▸ hblk, hablk⟩
      (by rw [hvab]; exact ⟨huse, hne⟩)
    exact ⟨z, hz⟩

end Setup

end GoFV.Proof.WB

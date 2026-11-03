import GoFV.Proof.Pass.DeadcodePass
import GoFV.Proof.Pass.DeadSimL
import GoFV.Proof.Pass.DeadFactsL
import GoFV.Proof.Pass.CopyElimL

/-!
# deadcode refines its input under `runL` (the lowered instances)

`deadcode_refinesL`: `deadcode_refines` over `runL`, for the lowered deadcode instances
(`lowered deadcode for cse`, `lowered deadcode`, `late deadcode`; the same `deadcodePass`). With
`f1' = edgesG false f`, `f2 = copyelim (edgesG true f)` and the output `g`, as in Phase 1:

1. `f1'` refines `f`: `refinesL_of_deadRel` with `deadRel_of_ei`, `deadRelL_of_ei` and
   `lowered_ei`;
2. `f2` refines `f1'`: copyelim's `refinesL_of_rel` (its `Setup` as in Phase 1, the fragment
   `CopyLFrag` and `f2.lowered = f1'.lowered` from `DeadFragL`);
3. `g` refines `f2`: `refinesL_of_deadRel` with `deadTail_rel`, `deadTail_relL`; `g` is lowered
   iff `f` is (`hlow`), hence iff `f2` is.

`DeadFragL tabs f` (decided by `deadFragLB`, on the input: it runs copyelim on `edgesG true f`
as Phase 1's `DeadFrag.cert2` does): copyelim's output keeps `lowered` and is in copyelim's
lowered fragment `CopyLFrag` relative to `f1'`.
-/

namespace GoFV.Proof.Dead

open GoFV.SSA GoFV.Opt GoFV.Proof GoFV.Proof.CopyElim

/-- deadcode's lowered fragment (see the module doc). -/
structure DeadFragL (tabs : Tables) (f : Func) : Prop where
  copy : ∀ f2, copyelim tabs (edgesG true f) = .ok f2 →
    f2.lowered = (edgesG false f).lowered ∧ CopyLFrag tabs (edgesG false f) f2

/-- Decides `DeadFragL` (`deadFragL_of`). -/
def deadFragLB (tabs : Tables) (f : Func) : Bool :=
  match copyelim tabs (edgesG true f) with
  | .ok f2 => f2.lowered == (edgesG false f).lowered && copyLFragB tabs (edgesG false f) f2
  | .error _ => true

theorem deadFragL_of {tabs : Tables} {f : Func} (h : deadFragLB tabs f = true) :
    DeadFragL tabs f := by
  refine ⟨fun f2 hc => ?_⟩
  unfold deadFragLB at h
  rw [hc] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1, copyLFrag_of h.2⟩

/-- **deadcode refines its input under `runL`** (`lowered deadcode for cse`, `lowered deadcode`,
`late deadcode`). -/
theorem deadcode_refinesL {penv : PassEnv} {f : Func} {out : PassOut} {ce ce' : CheckEnv}
    (h : deadcodePass penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) (hfrag : DeadFrag penv.tables f)
    (hlow : out.func.lowered = f.lowered) (hfragL : DeadFragL penv.tables f) :
    RefinesL out.tables out.func penv.tables f := by
  simp only [deadcodePass, Pass.ofFunc, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i g hd
    cases h
    rw [deadcode_eq, ← edgesG_true] at hd
    cases hc : copyelim penv.tables (edgesG true f) with
    | error e => rw [hc] at hd; cases hd
    | ok f2 =>
    rw [hc] at hd
    have hwf := check_wf hf
    have hwg := check_wf hg
    have hE := ei_edgesG hwf hfrag.firstTwo
    have hwf1 := wf_of_ei hwf hE
    have hI := inv_of_j hwf hE (j_edgesG hwf hfrag.firstTwo) hfrag.copy2
    obtain ⟨hwf2, hsz, hvl⟩ := copyelim_wf_of_inv hwf1 hfrag.copy1 hI hc
    obtain ⟨hlow2, hcL⟩ := hfragL.copy f2 hc
    have hlow1 := lowered_ei hE
    have r1 : RefinesL penv.tables (edgesG false f) penv.tables f :=
      refinesL_of_deadRel ⟨⟨ce, hwf⟩, ⟨ce, hwf1⟩, deadRel_of_ei hwf hfrag.bid hE⟩
        (deadRelL_of_ei hE) hlow1
    have r2 : RefinesL penv.tables f2 penv.tables (edgesG false f) :=
      refinesL_of_rel ⟨⟨ce, hwf1⟩, ⟨ce, hwf2⟩, hfrag.cert1, hfrag.cert2 f2 hc,
        copyelim_rel_of_inv hwf1 hfrag.copy1 hI hc, hfrag.empty⟩ hlow2 hcL
    have hs2 : f2.valueTab.size ≤ f2.vidLast + 1 := by rw [hsz, hvl]; exact hfrag.copy1.size
    have r3 : RefinesL penv.tables g penv.tables f2 :=
      refinesL_of_deadRel ⟨⟨ce, hwf2⟩, ⟨ce', hwg⟩, deadTail_rel hwg hs2 hd⟩ (deadTail_relL hs2 hd)
        (by rw [hlow2, hlow1]; exact hlow)
    exact r1.trans (r2.trans r3)

end GoFV.Proof.Dead

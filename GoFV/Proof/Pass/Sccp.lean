import GoFV.Proof.Pass.SccpTerm
import GoFV.Proof.Pass.SccpDead
import GoFV.Proof.Pass.CopyRelCheck
import GoFV.Proof.Pass.CopyElim
import GoFV.Proof.Witness.Util

variable [GoFV.SSA.Sem.Addrs]

/-!
# sccp refines its input (issue #32)

`sccp_refines`: the validated pass (`GoFV.Opt.sccpChecked`) refines its input under monotone
contracts. A rejected or unchanged result is the input. An accepted one `g` goes through two
intermediate functions (`GoFV.Opt.SccpCheck`): `h` (`replaceConst` with `rewireFirst`, which
`check` accepts with `firstAny`) refines the input by the atom simulation under sccp's source
invariant (`sccpInv`: registers with a constant cell hold `poison` or the constant, on
executable blocks; premises `sc_atomArgs` and `sc_steps`, where an `If` or `JumpTable` on a
constant became a `First` towards the successor it picks); `k` (the edges removed, `Phi`s only
losing arguments) refines `h` by deadcode's simulation (`deadOK_spec`, `Dead.refines_of_deadRel`:
`k` is `h` with the other edges of those `First` blocks removed); `g` is `k` or refines it by
copyelim's simulation (`copyOK_spec`, `CopyElim.refines_of_rel`: `Phi`s that `removeEdge` turned
into copies of their one remaining argument).
-/

namespace GoFV.Proof.Sccp

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof.AtomSim

/-- **sccp refines its input.** -/
theorem sccp_refines {penv : PassEnv} {f : Func} {out : PassOut} {ce ce' : CheckEnv}
    (h : sccpChecked penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) :
    RefinesUnder Env.Mono out.tables out.func penv.tables f := by
  unfold sccpChecked at h
  cases hr : GoFV.Rules.RwEnv.ofPassEnv penv with
  | error e => simp [hr, bind, Except.bind] at h
  | ok rw =>
    cases ha : Sccp.analyze rw penv.tables f with
    | error e => simp [hr, ha, bind, Except.bind] at h
    | ok a =>
      simp only [hr, ha, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only at hg ⊢
      split
      · rename_i hok
        simp only [hok, ↓reduceIte] at hg
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hok
        obtain ⟨⟨⟨⟨-, hs⟩, hd⟩, hc⟩, hk⟩ := hok
        have K := sccpOK_spec hs
        have hwf := check_wf hf
        have hch := Witness.ok_of_toBool hc
        have h1 := atomSimInv_refines hf hch K.atoms (sccpInv hwf K) (sc_atomArgs hwf K)
          (sc_steps hwf K)
        rcases hk with hkg | ⟨hck, hco⟩
        · rw [hkg] at hd
          have h2 := Dead.refines_of_deadRel (tabs := penv.tables)
            ⟨⟨_, check_wf hch⟩, ⟨_, check_wf hg⟩, deadOK_spec hd⟩
          exact h1.trans (h2.under Env.Mono)
        · have hck' := Witness.ok_of_toBool hck
          have h2 := Dead.refines_of_deadRel (tabs := penv.tables)
            ⟨⟨_, check_wf hch⟩, ⟨_, check_wf hck'⟩, deadOK_spec hd⟩
          obtain ⟨hrel, hfr⟩ := CopyRelCheck.copyOK_spec hco
          have h3 := CopyElim.refines_of_rel (tabs := penv.tables)
            ⟨⟨_, check_wf hck'⟩, ⟨_, check_wf hg⟩, Dom.certOK_of_check (check_domCert hck'),
              Dom.certOK_of_check (check_domCert hg), hrel, hfr⟩
          exact (h1.trans (h2.under Env.Mono)).trans (h3.under Env.Mono)
      · exact RefinesUnder.refl _ _ _

end GoFV.Proof.Sccp

import GoFV.Proof.Pass.SccpTerm
import GoFV.Proof.Pass.SccpDead
import GoFV.Proof.Witness.Util

/-!
# sccp refines its input (issue #32)

`sccp_refines`: the validated pass (`GoFV.Opt.sccpChecked`) refines its input under monotone
contracts. A rejected or unchanged result is the input. An accepted one `g` goes through the
intermediate function `h` (`replaceConst` with `rewireFirst`, which `check` accepts): `h` refines
the input by the atom simulation under sccp's source invariant (`sccpInv`: registers with a
constant cell hold `poison` or the constant, on executable blocks; premises `sc_atomArgs` and
`sc_steps`, where an `If` on a constant became a `First` towards the successor it picks), and
`g` refines `h` by deadcode's simulation (`deadOK_spec`, `Dead.refines_of_deadRel`: `g` is `h`
with the second edge of those `First` blocks removed).
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
        simp only [Bool.and_eq_true] at hok
        obtain ⟨⟨⟨-, hs⟩, hd⟩, hc⟩ := hok
        have K := sccpOK_spec hs
        have hwf := check_wf hf
        have hch : check { tabs := penv.tables, typs := penv.typs } (Sccp.replace a a.keys
            Sccp.rewireFirst) = .ok () := Witness.ok_of_toBool hc
        have h1 := atomSimInv_refines hf hch K.atoms (sccpInv hwf K) (sc_atomArgs hwf K)
          (sc_steps hwf K)
        have h2 := Dead.refines_of_deadRel (tabs := penv.tables)
          ⟨⟨_, check_wf hch⟩, ⟨_, check_wf hg⟩, deadOK_spec hd⟩
        exact h1.trans (h2.under Env.Mono)
      · exact RefinesUnder.refl _ _ _

end GoFV.Proof.Sccp

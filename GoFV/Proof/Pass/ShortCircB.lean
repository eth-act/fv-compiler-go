import GoFV.Proof.Pass.ShortCircOut
import GoFV.Proof.Pass.ZCSEEval

/-!
# Checked `shortcircuitBlock`: the source's path through `b`

`bstep`: entered from `p` (along `cidx`), the source's `b` sets its `Phi`s from their arguments
along `cidx` (the control phi takes the `ConstBool` `c`), evaluates its `Copy`/`Not` chain and its
`If` takes `te`: the chain's top holds `c`'s boolean, negated `par` times (`chain_bool`; a
`retype` yields a boolean only from a boolean, `retype_bool`). It cannot panic.
-/

namespace GoFV.Proof.ShortCirc

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.ShortCircuit GoFV.Proof Dom

theorem retype_bool {t : Ty} {x : Val} {bb : Bool} (h : x.retype t = .bool bb) : x = .bool bb := by
  unfold Val.retype at h
  split at h <;> (try split at h) <;> first | (cases h; rfl) | cases h | simp_all

theorem evalOp_not {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val} {ty : Ty}
    (hop : v.op = .Not) : evalOp env ctx fr v argv ty = .ok (evalPure .Not ty v.auxInt v.aux argv) := by
  simp only [evalOp, frameVal, hop]
  rfl

theorem evalOp_constBool {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (hop : v.op = .ConstBool) :
    evalOp env ctx fr v argv ty = .ok (evalPure .ConstBool ty v.auxInt v.aux argv) := by
  simp only [evalOp, frameVal, hop]
  rfl

theorem evalValue_not {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {w : ID} {y : Val}
    (hop : v.op = .Not) (ha : v.args = #[w]) (hw : fr.regs[w]? = some (some y)) :
    evalValue env ctx fr v = .ok ((Cmp.not [y]).retype (ctx.tys[v.id]?.getD .other)) := by
  unfold evalValue
  rw [ha]
  simp only [List.mapM_cons, List.mapM_nil, hw, Option.join, bind, Res.bind, Res.ofOption, pure]
  rw [show (some (some y)).bind id = some y from rfl]
  simp only [evalOp_not hop]
  rfl

theorem evalValue_constBool {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    (hop : v.op = .ConstBool) (ha : v.args = #[]) :
    evalValue env ctx fr v = .ok ((Conv.constBool v.auxInt).retype (ctx.tys[v.id]?.getD .other)) := by
  unfold evalValue
  rw [ha]
  simp only [Array.toList_empty, List.mapM_nil, bind, Res.bind, pure]
  simp only [evalOp_constBool hop]
  rfl

theorem copy_not_no_panic {op : Op} (h : op = .Copy ∨ op = .Not) : ¬ Panicking op := by
  rcases h with rfl | rfl <;> (unfold Panicking; decide)

/-- **The chain of `b`'s control**: a boolean at `x` is the control phi's, negated `par` times. -/
theorem chain_bool {f : Func} {B : Block} {ctl : ID} {G : Frame} {env : Env} {ctx : Ctx}
    (hctx : ctx.f = f) {cb : Bool}
    (hctl : ∀ bb, G.regs[ctl]? = some (some (.bool bb)) → bb = cb)
    (hev : ∀ x ∈ B.values, ∀ v, f.value? x = some v → (v.op = .Copy ∨ v.op = .Not) →
      ∃ y, G.regs[x]? = some (some y) ∧ evalValue env ctx G v = .ok y) :
    ∀ n x l par, chainOf f B ctl n x = some (l, par) →
      ∀ bb, G.regs[x]? = some (some (.bool bb)) → bb = (cb ^^ par)
  | 0, _, _, _, h => by simp [chainOf] at h
  | n + 1, x, l, par, h => by
    unfold chainOf at h
    by_cases hx : x = ctl
    · subst hx; simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      intro bb hb; rw [← h.2]; simpa using hctl bb hb
    · simp only [show (x == ctl) = false by simpa using hx, Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · rename_i v hv
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hc
          obtain ⟨⟨hxm, hop⟩, hsz⟩ := hc
          cases hrec : chainOf f B ctl n v.args[0]! with
          | none => rw [hrec] at h; cases h
          | some lp =>
            obtain ⟨l', par'⟩ := lp
            rw [hrec] at h
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            have ih := chain_bool hctx hctl hev n _ l' par' hrec
            have hargs : v.args = #[v.args[0]!] := by
              apply Array.ext
              · simp [hsz]
              · intro i h1 h2
                have : i = 0 := by simp at h2; omega
                subst this; simp [getElem!_pos v.args 0 (by omega)]
            obtain ⟨y, hy, hevy⟩ := hev x (contains_iff.1 hxm) v hv hop
            intro bb hb
            rw [hy] at hb; cases hb
            have hdef := evalValue_args_def (by rw [hevy]; nofun) v.args[0]!
              (by rw [hargs]; simp)
            obtain ⟨ya, hya⟩ := hdef
            rcases hop with hop | hop
            · rw [evalValue_copy hop hargs hya] at hevy
              have hret := (Res.ok.inj hevy).symm
              have := retype_bool hret.symm
              subst this
              rw [← h.2, hop]
              exact ih _ hya
            · rw [evalValue_not hop hargs hya] at hevy
              have hret := (Res.ok.inj hevy).symm
              have hn := retype_bool hret.symm
              cases ya with
              | bool z =>
                have hz : bb = !z := by
                  have : Cmp.not [Val.bool z] = .bool (!z) := rfl
                  rw [this] at hn; cases hn; rfl
                rw [hz, ← h.2, hop, ih z hya]
                cases cb <;> cases par' <;> rfl
              | _ => simp [Cmp.not, bool1, Val.asBool] at hn
        · cases h
      · cases h

theorem chain_mem {f : Func} {B : Block} {ctl : ID} :
    ∀ n x l par, chainOf f B ctl n x = some (l, par) → ∀ y ∈ l,
      ∃ v, f.value? y = some v ∧ (v.op = .Copy ∨ v.op = .Not)
  | 0, _, _, _, h => by simp [chainOf] at h
  | n + 1, x, l, par, h => by
    unfold chainOf at h
    by_cases hx : x = ctl
    · subst hx; simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]; intro y hy; cases hy
    · simp only [show (x == ctl) = false by simpa using hx, Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · rename_i v hv
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hc
          cases hrec : chainOf f B ctl n v.args[0]! with
          | none => rw [hrec] at h; cases h
          | some lp =>
            obtain ⟨l', par'⟩ := lp
            rw [hrec] at h
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            rw [← h.1]
            intro y hy
            rcases List.mem_cons.1 hy with rfl | hy
            · exact ⟨v, hv, hc.1.2⟩
            · exact chain_mem n _ l' par' hrec y hy
        · cases h
      · cases h

theorem arr_one {a : Array ID} {w : ID} (hs : a.size = 1) (h : a[0]? = some w) : a = #[w] := by
  apply Array.ext
  · simp [hs]
  · intro i h1 h2
    have : i = 0 := by simp at h2; omega
    subst this
    simp only [List.getElem_toArray, List.getElem_cons_zero]
    exact (Array.getElem?_eq_some_iff.1 h).2

namespace Setup

variable {ce : CheckEnv} {tabs : Tables} {f g : Func} {s : Site} (S : Setup ce tabs f g s)
include S

set_option hygiene false in
local notation "𝓘" => infoOf tabs f g s

/-- **The source's step through `b` along `cidx`** goes to `te`. -/
theorem bstep {env : Env} {G G' : Frame} {e : Edge} (hA : ZCSE.ArglessInv env (Ctx.make tabs f) G)
    (hty : Typed (Ctx.make tabs f) G) (hs : G.regs.size = f.valueTab.size)
    (h : blockStep env (Ctx.make tabs f) G s.b s.cidx = .goto G' e) :
    e = s.te ∧ G' = { G with regs := G'.regs } ∧ G'.regs.size = G.regs.size ∧
      (∀ z, z ∉ (𝓘).bvals → G'.regs[z]? = G.regs[z]?) ∧
      (∀ v ∈ (𝓘).vs, ∃ a y, (f.getV v).args[s.cidx]? = some a ∧ G.regs[a]? = some (some y) ∧
        G'.regs[v]? = some (some (y.retype (tyOf tabs f v)))) ∧
      Typed (Ctx.make tabs f) G' ∧ ZCSE.ArglessInv env (Ctx.make tabs f) G' := by
  obtain ⟨Bb, hBb, hbm, hbid, hvals, hkind, -, -, -, -, -, -, top, cv, chain, par, c, cc, htop, hcsz,
    hcv, hcvp, hctlm, hch, hcc, hcc', hccop, hccargs, hsucc, -⟩ := S.pre
  obtain ⟨B', hB', hen, hterm⟩ := blockStep_goto h
  change f.block? s.b = some B' at hB'
  rw [hBb] at hB'; cases hB'
  have hnd := S.wf.valuesNodup s.b Bb ⟨hbm, hBb⟩
  obtain ⟨PS, o, ho, hev, hPf, hPs, -, hPk, hPp⟩ := enterBlock_spec hnd hen
  rw [hbid, sched_of_block hBb] at ho
  obtain ⟨ond, otopo, omem⟩ := schedule_topo (valuesOwn S.wf hbm hBb) hnd ho
  obtain ⟨e1, e2, e3, e4⟩ := evalAll_spec ond otopo (by rw [hPs, hs]; rfl) hev
  have hG'1 : G' = { G with regs := G'.regs } := (SameAct.of e1).trans (SameAct.of hPf) |>.eq
  have hG'P : ∀ z, z ∉ o.toList → G'.regs[z]? = PS.regs[z]? := e3
  -- the control phi holds `c`'s boolean
  have hcvl : s.ctl < G.regs.size := by rw [hs]; exact lt_of_value? hcv
  obtain ⟨c', yc, hc', hyc, hPc⟩ := hPp s.ctl hctlm cv hcv hcvp hcvl
  rw [hcc] at hc'; cases hc'
  have hcev := hA c cc yc hcc' hccargs (by rw [hccop]; decide) hyc
  rw [evalValue_constBool hccop hccargs] at hcev
  have hctlo : s.ctl ∉ o.toList := fun hm => by
    obtain ⟨-, v, hv, hne⟩ := (omem _).1 hm
    rw [hcv] at hv; cases hv; exact hne hcvp
  have hctl : ∀ bb, G'.regs[s.ctl]? = some (some (.bool bb)) → bb = (cc.auxInt != 0) := by
    intro bb hb
    rw [hG'P _ hctlo, hPc] at hb
    have h1 := retype_bool (Option.some.inj (Option.some.inj hb))
    rw [← (Res.ok.inj hcev)] at h1
    have h2 := retype_bool h1
    simp only [Conv.constBool, Val.bool.injEq] at h2
    exact h2.symm
  have hchev : ∀ x ∈ Bb.values, ∀ v, f.value? x = some v → (v.op = .Copy ∨ v.op = .Not) →
      ∃ y, G'.regs[x]? = some (some y) ∧ evalValue env (Ctx.make tabs f) G' v = .ok y := by
    intro x hx v hv hop
    have hxo : x ∈ o.toList := (omem x).2 ⟨hx, v, hv, by rcases hop with h | h <;> rw [h] <;> decide⟩
    obtain ⟨v', y, hv', hy, hevy⟩ := e4 x hxo
    change f.value? x = some v' at hv'
    rw [hv] at hv'; cases hv'
    exact ⟨y, hy, hevy⟩
  have hcb := chain_bool (ctx := Ctx.make tabs f) (B := Bb) rfl hctl hchev _ top chain par hch
  have hcs : Bb.controls = #[top] := arr_one hcsz htop
  obtain ⟨bb, e', hbb, he', hn⟩ := stepTerm_if hkind hcs hterm
  cases hn
  have := hcb bb hbb
  subst this
  rw [hsucc] at he'
  refine ⟨(Option.some.inj he').symm, hG'1, by rw [e2, hPs], fun z hz => ?_, fun v hv => ?_,
    typed_enter S.wf hbm hBb hs hty hen, ZCSE.arglessInv_enter hA hnd hen⟩
  · have hzb : z ∉ Bb.values := by rw [hvals]; exact hz
    rw [e3 z (fun hm => hzb ((omem z).1 hm).1), hPk z (.inl hzb)]
  · obtain ⟨hvb, -, hvp⟩ := S.vs_mem hv
    obtain ⟨fv, hfv, hfvp⟩ := isPhiIn_iff.1 hvp
    have hvb' : v ∈ Bb.values := by rw [hvals]; exact hvb
    obtain ⟨a, y, ha, hy, hPv⟩ := hPp v hvb' fv hfv hfvp (by rw [hs]; exact lt_of_value? hfv)
    have hvo : v ∉ o.toList := fun hm => by
      obtain ⟨-, v', hv', hne⟩ := (omem _).1 hm
      rw [hfv] at hv'; cases hv'; exact hne hfvp
    exact ⟨a, y, by rw [getV_of hfv]; exact ha, hy, by rw [e3 v hvo, hPv]; rfl⟩

/-- The source's step through `b` neither panics nor returns. -/
theorem bstep_not {env : Env} {G : Frame} (hs : G.regs.size = f.valueTab.size) :
    (∀ e m, blockStep env (Ctx.make tabs f) G s.b s.cidx ≠ .panic e m) ∧
    (∀ rs m, blockStep env (Ctx.make tabs f) G s.b s.cidx ≠ .ret rs m) := by
  obtain ⟨Bb, hBb, hbm, hbid, hvals, hkind, -, -, -, -, -, -, top, cv, chain, par, c, cc, htop, hcsz,
    hcv, hcvp, hctlm, hch, -, -, -, -, -, hall⟩ := S.pre
  have hcs : Bb.controls = #[top] := arr_one hcsz htop
  refine ⟨fun e m h => ?_, fun rs m h => ?_⟩
  · obtain ⟨B', hB', hen⟩ := blockStep_panic h
    change f.block? s.b = some B' at hB'
    rw [hBb] at hB'; cases hB'
    rw [enterBlock_eq] at hen
    cases hps : Bb.values.toList.filterMapM (phiStep (Ctx.make tabs f) G s.cidx) with
    | panic e' m' => exact filterMapM_phi_not_panic hps
    | stuck msg => rw [hps] at hen; cases hen
    | ok ps =>
    rw [hps] at hen
    change (Res.ofOption _ ((Ctx.make tabs f).sched[Bb.id]?).join).bind _ = _ at hen
    rw [hbid, sched_of_block hBb] at hen
    have hnd := S.wf.valuesNodup s.b Bb ⟨hbm, hBb⟩
    cases ho : schedule f Bb with
    | none => rw [ho] at hen; cases hen
    | some o =>
    rw [ho] at hen
    obtain ⟨-, -, omem⟩ := schedule_topo (valuesOwn S.wf hbm hBb) hnd ho
    obtain ⟨pre, r, post, g', hsplit, -, hr⟩ := evalAll_panic_split hen
    have hrm : r ∈ o.toList := by rw [hsplit]; simp
    obtain ⟨hrb, v, hv, hne⟩ := (omem r).1 hrm
    unfold stepV at hr
    rw [show (Ctx.make tabs f).f = f from rfl, hv] at hr
    have hpan := evalValue_panic_op hr
    rcases hall r hrb with hrc | hrc | hrc
    · subst hrc; rw [hcv] at hv; cases hv; exact hne hcvp
    · obtain ⟨v', hv', hop⟩ := chain_mem _ top chain par hch r hrc
      rw [hv] at hv'; cases hv'
      exact copy_not_no_panic hop hpan
    · rw [isPhiIn_true hv] at hrc; exact hne hrc
  · obtain ⟨B', G', hB', -, hterm⟩ := blockStep_ret h
    change f.block? s.b = some B' at hB'
    rw [hBb] at hB'; cases hB'
    have hx := stepTerm_if hkind hcs hterm
    obtain ⟨b0, e0, h1, h2, h3⟩ := hx
    exact Next.noConfusion h3

end Setup

end GoFV.Proof.ShortCirc

import GoFV.Proof.Pass.ShortCircKEnter
import GoFV.Proof.Agree

variable [GoFV.SSA.Sem.Addrs]

/-!
# Checked `shortcircuitBlock`: blocks outside `K`

`ostep`: a block the checker did not compare (`B ∉ K`) is the same block in both functions with
the same values (`frameOK`), reading only registers that agree (`scanOK`: outside `b`'s values,
or a moved phi whose default fact the incoming edge carries), so it runs alike
(`enterBlock_agree`, `stepTerm_agree`) and ends with the default facts.
-/

namespace GoFV.Proof.ShortCirc

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.ShortCircuit GoFV.Proof Dom

namespace Setup

variable {ce : CheckEnv} {tabs : Tables} {f g : Func} {s : Site} (S : Setup ce tabs f g s)
include S

set_option hygiene false in
local notation "𝓘" => infoOf tabs f g s

/-- **A block outside `K` runs alike** in frames agreeing outside `Delta` and on the default
facts. -/
theorem ostep {B : ID} (hBm : B ∈ f.blocks) (hBK : B ∉ (𝓘).K) {fB : Block}
    (hfB : f.block? B = some fB) {i : Nat} {E : Facts} {frS frT : Frame}
    (hrel : FactsRel (𝓘) f E frS frT)
    (hdf : ∀ v, (𝓘).look (𝓘).dflt v = some v → (𝓘).look E v = some v)
    (hfrS : frT = { frS with regs := frT.regs }) (hsz : frT.regs.size = frS.regs.size) {env : Env} :
    (∀ G, enterBlock env (Ctx.make tabs f) frS fB i = .ok G →
      ∃ GT, enterBlock env (Ctx.make tabs g) frT fB i = .ok GT ∧ GT = { G with regs := GT.regs } ∧
        GT.regs.size = G.regs.size ∧ FactsRel (𝓘) f (𝓘).dflt G GT ∧
        stepTerm GT fB = stepTerm G fB) ∧
    (∀ e m, enterBlock env (Ctx.make tabs f) frS fB i = .panic e m →
      enterBlock env (Ctx.make tabs g) frT fB i = .panic e m) := by
  have hgB : g.block? B = some fB := by rw [S.block_out hBK, hfB]
  have hBg : B ∈ g.blocks := by rw [S.gblocks]; exact hBm
  have hfid : fB.id = B := by
    obtain ⟨b', hb', hid⟩ := S.wf.blockId B hBm; rw [hfB] at hb'; cases hb'; exact hid
  let X : ID → Prop := fun a => Delta (𝓘) f a ∧ (𝓘).look E a ≠ some a
  have hag : ∀ a, ¬ X a → frT.regs[a]? = frS.regs[a]? := fun a ha => by
    by_cases hd : Delta (𝓘) f a
    · exact hrel.2 a a (Classical.byContradiction fun h => ha ⟨hd, h⟩)
    · exact hrel.1 a hd
  have hfree : ∀ a, (𝓘).freeArg a = true → Listed f a → ¬ X a := by
    intro a hf hl hX
    unfold Info.freeArg at hf
    rcases Bool.or_eq_true_iff.1 hf with h | h
    · have hb : a ∉ (𝓘).bvals := by simpa [contains_iff] using h
      exact hX.1.elim hb (· hl)
    · simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact hX.2 (hdf a h.2)
  obtain ⟨hctl, hargs⟩ := S.scan_spec hBg hBK
  rw [getB_of hgB] at hctl hargs
  have hvals := fun x (hx : x ∈ fB.values) => S.vals_out hBm hBK hfB hx
  have hsem : ∀ x ∈ fB.values, SemEq (f.value? x) (g.value? x) := fun x hx => by
    obtain ⟨fx, gx, hfx, hgx, -, h1, h2, -, h4, h5, h6⟩ := hvals x hx
    rw [hfx, hgx]; exact ⟨h1, h2, h4, h5, h6⟩
  have hca : CtxAgree (Ctx.make tabs f) (Ctx.make tabs g) fB.values.toList := by
    refine ⟨fun x hx => hsem x (Array.mem_toList_iff.1 hx), fun x hx v hv => ?_, rfl,
      params_eq' (tabs := tabs) S.gownAux, rfl⟩
    obtain ⟨fx, gx, hfx, hgx, hfid, -, -, h3, -⟩ := hvals x (Array.mem_toList_iff.1 hx)
    change f.value? x = some v at hv
    rw [hfx] at hv; cases hv
    rw [hfid, tys_of_tyOf hgx, tys_of_tyOf hfx, tyOf_eq hgx, tyOf_eq hfx, h3]
  have hargF : ∀ x ∈ fB.values, ∀ v, f.value? x = some v → ∀ a ∈ v.args, ¬ X a := by
    intro x hx v hv a ha
    obtain ⟨fx, gx, hfx, hgx, -, -, -, -, -, -, h6⟩ := hvals x hx
    rw [hfx] at hv; cases hv
    exact hfree a (hargs x hx a (by rw [getV_of hgx, h6]; exact ha))
      (argListed_of S.wf hBm hfB hx hfx ha)
  have hsch : schedule g fB = schedule f fB := by
    unfold Sem.schedule; rw [schedNodes_semEq rfl hsem]
  have hag' := enterBlock_agree (env := env) (bS := fB) (bT := fB) (i := i) (X := X)
    ⟨rfl, rfl, rfl, rfl, rfl⟩ hca
    (fun z hz v hv => by
      obtain ⟨fx, gx, hfx, -, h, -⟩ := hvals z hz
      change f.value? z = some v at hv
      rw [hfx] at hv; cases hv; exact h)
    (fun z hz v hv _ a ha => hargF z hz v hv a (args_get_mem ha))
    (by rw [hfid, sched_of_block hgB, sched_of_block hfB, hsch])
    (fun o ho => by
      have ho' : schedule f fB = some o := by
        rw [hfid, sched_of_block (tabs := tabs) hfB] at ho; exact ho
      obtain ⟨-, -, omem⟩ := schedule_topo (valuesOwn S.wf hBm hfB)
        (S.wf.valuesNodup B fB ⟨hBm, hfB⟩) ho'
      have hsub : ∀ x ∈ o.toList, x ∈ fB.values.toList := fun x hx =>
        Array.mem_toList_iff.2 ((omem x).1 hx).1
      refine ⟨hca.mono hsub, fun x hx => ⟨fun hX => ?_, fun v hv a ha =>
        hargF x (Array.mem_toList_iff.1 (hsub x hx)) v hv a ha⟩⟩
      have hxv := Array.mem_toList_iff.1 (hsub x hx)
      exact hX.1.elim (S.notb_out hBm hBK hfB hxv) (· (listed_of_mem S.wf hBm hfB hxv)))
    hfrS hsz hag
  refine ⟨fun G hG => ?_, hag'.2⟩
  obtain ⟨GT, h1, h2, h3, h4⟩ := hag'.1 G hG
  refine ⟨GT, h1, h2, h3, ⟨fun x hx => h4 x fun h => hx h.1, fun v w hvw => ?_⟩, ?_⟩
  · have hw := look_dflt hvw
    subst hw
    exact h4 w fun h => h.2 (hdf w hvw)
  · refine stepTerm_agree ⟨rfl, rfl, rfl, rfl, rfl⟩ fun c hc => h4 c ?_
    exact hfree c (hctl c hc) (S.wf.ctrlListed B fB ⟨hBm, hfB⟩ c hc)

end Setup


end GoFV.Proof.ShortCirc

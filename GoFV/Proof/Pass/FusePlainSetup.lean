import GoFV.Proof.Pass.FusePlainPres
import GoFV.Proof.Pass.DeadRel
import GoFV.Proof.Enter
import GoFV.Proof.Mixed
import GoFV.Proof.SimIH
import GoFV.Proof.Speculate

variable [GoFV.SSA.Sem.Addrs]

/-!
# fuseBlockPlain: the setting of one checked rewrite

`Setup f g run b0 c`: `f` and `g` are well formed, `f`'s uses are dominated on paths
(`Dom.UseDom`, so path dominance `SDom f` is a dominance relation: `dom`), and `g` is `f` with
the run `run` (from `b0` to `c`) fused (`PRel`). `Acc … pre G`: `G` is the source's
frame after the blocks `pre` of the run, entered from `fr` at `b0` with predecessor index `i`:
it differs from `fr` only on their values, each non-`Phi` of them re-evaluates to its register,
and `b0`'s `Phi`s hold their incoming arguments (`acc_step`).
-/

namespace GoFV.Proof.FusePlain

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.Fuse GoFV.Opt.Fuse.Plain
  GoFV.Proof Dom

/-- See the module doc. -/
structure Setup (f g : Func) (run : List ID) (b0 c : ID) : Prop where
  wf : ∃ ce, WF ce f
  wg : ∃ ce, WF ce g
  cf : UseDom f
  rel : PRel f g run b0 c

/-- See the module doc. -/
def Acc (env : Env) (tabs : Tables) (f : Func) (fr : Frame) (i : Nat) (b0 : ID) (pre : List ID)
    (G : Frame) : Prop :=
  G = { fr with regs := G.regs } ∧ G.regs.size = fr.regs.size ∧
  (∀ z, (∀ y ∈ pre, z ∉ (valsOf f y).toList) → G.regs[z]? = fr.regs[z]?) ∧
  (∀ y ∈ pre, ∀ x ∈ (valsOf f y).toList, ∀ v, f.value? x = some v → v.op ≠ .Phi →
    ∃ r, G.regs[x]? = some (some r) ∧ evalValue env (Ctx.make tabs f) G v = .ok r) ∧
  (b0 ∈ pre → ∀ x ∈ (valsOf f b0).toList, ∀ v, f.value? x = some v → v.op = .Phi →
    ∃ a r, v.args[i]? = some a ∧ fr.regs[a]? = some (some r) ∧
      G.regs[x]? = some (some (r.retype ((Ctx.make tabs f).tys[x]?.getD .other))))

theorem acc_nil {env : Env} {tabs : Tables} {f : Func} {fr : Frame} {i : Nat} {b0 : ID} :
    Acc env tabs f fr i b0 [] fr := by
  unfold Acc
  exact ⟨rfl, rfl, fun _ _ => rfl, fun _ h => by simp at h, fun h => by simp at h⟩

theorem frame_trans {a b c : Frame} (h1 : a = { b with regs := a.regs })
    (h2 : b = { c with regs := b.regs }) : a = { c with regs := a.regs } := by
  rw [h1, h2]

theorem frame_eq {a b : Frame} (h1 : a = { b with regs := a.regs })
    (h2 : ∀ z : Nat, a.regs[z]? = b.regs[z]?) : a = b := by
  rw [h1, show a.regs = b.regs from Array.ext_getElem? h2]

variable {f g : Func} {run : List ID} {b0 c : ID}

namespace Setup

variable (S : Setup f g run b0 c)
include S

theorem dom : DomRel f (Reachable f) (SDom f) := S.cf.domRel

theorem runIn {x : ID} (hx : x ∈ run) : x ∈ f.blocks := S.rel.parts.2.2.1 x hx

theorem block_of {x : ID} (hx : x ∈ run) : ∃ X, f.block? x = some X := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨X, hX, -⟩ := hwf.blockId x (S.runIn hx)
  exact ⟨X, hX⟩

theorem nodup : run.Nodup := S.rel.parts.2.1

/-- Values of distinct listed blocks are distinct. -/
theorem disj {x y : ID} (hx : x ∈ f.blocks) (hy : y ∈ f.blocks) {v : ID}
    (hvx : v ∈ (valsOf f x).toList) (hvy : v ∈ (valsOf f y).toList) : x = y := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨X, hX, hvX⟩ := valsOf_mem.1 hvx
  obtain ⟨Y, hY, hvY⟩ := valsOf_mem.1 hvy
  exact hwf.valueOnce x X y Y ⟨hx, hX⟩ ⟨hy, hY⟩ v hvX hvY

theorem gblocks : g.blocks = f.blocks := S.rel.parts.2.2.2.2.2.2.1

theorem params_eq {tabs : Tables} : (Ctx.make tabs g).params = (Ctx.make tabs f).params := by
  simp only [Ctx.make, abiParams, S.rel.parts.2.2.2.2.2.2.2.2.1]

theorem gsize : g.valueTab.size = f.valueTab.size := S.rel.parts.2.2.2.2.2.2.2.2.2.1

/-- An unchanged value, evaluated in a target frame that agrees with a source frame on its
arguments, yields the source's result. -/
theorem eval_same {tabs : Tables} {env : Env} {x : ID} {fv gv : Value} (hfv : f.value? x = some fv)
    (hgv : g.value? x = some gv) (hid : fv.id = x) {Gs g' : Frame}
    (hg' : g' = { Gs with regs := g'.regs }) (hag : ∀ a ∈ fv.args, g'.regs[a]? = Gs.regs[a]?) :
    evalValue env (Ctx.make tabs g) g' gv = evalValue env (Ctx.make tabs f) Gs fv := by
  obtain ⟨hsem, hv⟩ := S.rel.value_same x
  rw [hfv, hgv] at hsem
  obtain ⟨gv', hgv', hty, -⟩ := hv fv hfv
  rw [hgv] at hgv'; cases hgv'
  exact evalValue_ctx_congr hsem hg' hag
    (by rw [hid, tys_of_value hfv, tys_of_value hgv, hty]) rfl S.params_eq rfl

/-- The prefix and suffix of the run around one of its blocks. -/
theorem split_mem {y : ID} (hy : y ∈ run) : ∃ pre suf, run = pre ++ y :: suf :=
  List.append_of_mem hy

/-- **One more block of the run.** -/
theorem acc_step {tabs : Tables} {env : Env} {fr G G' : Frame} {i idx : Nat} {pre suf : List ID}
    {y : ID} (hr : run = pre ++ y :: suf) (hfs : fr.regs.size = f.valueTab.size)
    (hA : Acc env tabs f fr i b0 pre G) (hfirst : pre = [] → y = b0 ∧ idx = i)
    {Y : Block} (hY : f.block? y = some Y) (h : enterBlock env (Ctx.make tabs f) G Y idx = .ok G') :
    Acc env tabs f fr i b0 (pre ++ [y]) G' := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨hGf, hGs, hGo, hGv, hGp⟩ := hA
  have hyIn : y ∈ f.blocks := S.runIn (by rw [hr]; simp)
  obtain ⟨e1, e2, e3, e4, e5⟩ := enter_ok_facts hwf hyIn hY (by rw [hGs, hfs]) h
  have hnd := S.nodup
  rw [hr] at hnd
  have hyp : y ∉ pre := fun hm => by
    rw [List.nodup_append] at hnd
    exact hnd.2.2 y hm y List.mem_cons_self rfl
  have hvY : ∀ z, z ∈ (valsOf f y).toList ↔ z ∈ Y.values := fun z => by
    rw [valsOf_eq hY, Array.mem_toList_iff]
  -- a value of an earlier block is not one of `y`'s
  have hnotY : ∀ y' ∈ pre, ∀ z ∈ (valsOf f y').toList, z ∉ Y.values := fun y' hy' z hz hzY =>
    hyp (S.disj (S.runIn (by rw [hr]; simp [hy'])) hyIn hz ((hvY z).2 hzY) ▸ hy')
  refine ⟨frame_trans e1 hGf, by rw [e2, hGs], fun z hz => ?_, fun y' hy' x hx v hv hp => ?_,
    fun hb0 x hx v hv hp => ?_⟩
  · have hzY : z ∉ Y.values := fun h' => hz y (by simp) ((hvY z).2 h')
    rw [e3 z hzY, hGo z fun y'' hy'' => hz y'' (by simp [hy''])]
  · rcases List.mem_append.1 hy' with hy' | hy'
    · have hxY := hnotY y' hy' x hx
      obtain ⟨r, hr', hev⟩ := hGv y' hy' x hx v hv hp
      refine ⟨r, by rw [e3 x hxY, hr'], ?_⟩
      rw [← hev]
      refine (evalValue_congr e1 fun a ha => ?_).symm
      obtain ⟨p1, p2, hp12⟩ := List.append_of_mem hy'
      have hr2 : run = p1 ++ y' :: (p2 ++ y :: suf) := by rw [hr, hp12]; simp
      have := S.rel.reads hr2 hx hv hp ha (y := y) (by simp)
      exact (e3 a fun haY => this ((hvY a).2 haY)).symm
    · rw [List.mem_singleton] at hy'; subst hy'
      exact e4 x ((hvY x).1 hx) v hv hp
  · by_cases hpre : pre = []
    · obtain ⟨rfl, rfl⟩ := hfirst hpre
      subst hpre
      obtain ⟨a, r, ha, hra, hx'⟩ := e5 x ((hvY x).1 hx) v hv hp
      exact ⟨a, r, ha, by rw [← hra, hGo a fun _ h => nomatch h], hx'⟩
    · have hb0pre : b0 ∈ pre := by
        obtain ⟨rest, hrest⟩ := S.rel.run_cons
        rw [hr] at hrest
        cases pre with
        | nil => exact absurd rfl hpre
        | cons p pre => simp only [List.cons_append, List.cons.injEq] at hrest; simp [hrest.1]
      obtain ⟨a, r, ha, hra, hx'⟩ := hGp hb0pre x hx v hv hp
      exact ⟨a, r, ha, hra, by rw [e3 x (hnotY b0 hb0pre x hx), hx']⟩

end Setup

end GoFV.Proof.FusePlain

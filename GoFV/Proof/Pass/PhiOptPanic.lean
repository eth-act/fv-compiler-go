import GoFV.Proof.Pass.PhiOptBlock
import GoFV.Proof.Pass.ZCSERank

/-!
# phiopt: a block where the source panics

`enter_panic`: the source panics at a non-pure node `r` of its schedule after a prefix `pre`;
every source value the target evaluates before `r` is in `pre` (`schedTransfer`, from
`sched_transfer`: the target block has the source's non-pure nodes with their priorities,
`sameNP`, and the same dependencies between them, `depPres`/`depBack`, since the target's other
nodes — new values and rewritten `Phi`s — are pure and take no source node as argument,
`tnode`), the others are new values and rewritten `Phi`s, so the target reaches `r` agreeing
with the reference frame of the source's frame at the panic and panics alike.
-/

namespace GoFV.Proof.PhiOpt

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.PhiOpt Dom Order
open GoFV.Proof.CopyElim (Tree stepV_of topoRem_at prio_ne_zero_of_panic)
open GoFV.Proof.ZCSE (evalValue_panic_args npIn_sched)

variable {tabs : Tables} {f g : Func}

/-- A rewritten `Phi`'s form is pure. -/
theorem prio_rw {fv gv : Value} (h : rewriteOK tabs f g fv gv = true) : prio gv.op = 0 := by
  obtain ⟨-, -, hsz, -, hform⟩ := rewriteOK_spec h
  rcases hform with ⟨-, c, -, -, hall⟩ | ⟨w, c, neg, ⟨-, hop, -⟩, -⟩
  · obtain ⟨d, -, harm⟩ := hall 0 fv.args[0]! (by
      rw [getElem!_pos fv.args 0 (by omega)]; simp [hsz])
    rcases harm with ⟨hop, -⟩ | ⟨hop, -⟩ | ⟨n, hop, -⟩ | ⟨n, hop, -⟩ <;> rw [hop] <;> decide
  · rw [hop]; cases w <;> decide

/-- A new value is pure. -/
theorem prio_new {b x : ID} {nv : Value} (h : newOK f g b x = true) (hv : g.value? x = some nv) :
    prio nv.op = 0 := by
  obtain ⟨nv', -, hnv, -, -, hop⟩ := newOK_spec h
  rw [hv] at hnv; cases hnv
  rcases hop with ⟨hop, -⟩ | ⟨hop, -⟩ <;> rw [hop] <;> decide

section
variable (S : Setup tabs f g) {bid : ID} (hb : bid ∈ f.blocks) {fb gb : Block}
  (hfb : f.block? bid = some fb) (hgb : g.block? bid = some gb)
include S hb hfb hgb

/-- **A target node is a source node, or a pure value taking no source node as argument** (a
new value or a rewritten `Phi`). -/
theorem tnode {y : ID} (hy : NodeIn (schedNodes g gb).toList y) :
    NodeIn (schedNodes f fb).toList y ∨
      (PureIn (schedNodes g gb).toList y ∧ ¬ NodeIn (schedNodes f fb).toList y ∧
        ∀ a ∈ argsOf (schedNodes g gb).toList y, ¬ NodeIn (schedNodes f fb).toList a) := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  have hbg : bid ∈ g.blocks := by rw [S.blocks]; exact hb
  have hownG := valuesOwn hwg hbg hgb
  have hndG := hwg.valuesNodup _ _ ⟨hbg, hgb⟩
  have hownF := valuesOwn hwf hb hfb
  obtain ⟨hyg, gv, hgv, hgn⟩ := (nodeIn_schedNodes hownG).1 hy
  have hD := argsOf_schedNodes hownG hndG hyg hgv hgn
  have hpure : prio gv.op = 0 → PureIn (schedNodes g gb).toList y := fun h n hn => by
    rw [CopyElim.nodeOf_schedNodes hownG hndG hyg hgv hgn] at hn
    cases hn; exact h
  have hav : ∀ a, avail f bid a = true → ¬ NodeIn (schedNodes f fb).toList a := fun a ha hn => by
    obtain ⟨-, -, -, -, -, -, -, -, hnl⟩ := avail_spec ha
    exact not_listedIn hfb hnl ((nodeIn_schedNodes hownF).1 hn).1
  have hnone : ∀ a, f.value? a = none → ¬ NodeIn (schedNodes f fb).toList a := fun a ha hn => by
    obtain ⟨-, v, hv, -⟩ := (nodeIn_schedNodes hownF).1 hn
    rw [ha] at hv; cases hv
  obtain ⟨gv', hgv', -, hk⟩ := gval S hb hfb hgb hyg
  rw [hgv] at hgv'; cases hgv'
  rcases hk with ⟨fv, hfv, hyf, -, -, ⟨hop, -⟩ | hr⟩ | ⟨hn, -, hok⟩
  · exact .inl ((nodeIn_schedNodes hownF).2 ⟨hyf, fv, hfv, by rw [← hop]; exact hgn⟩)
  · right
    obtain ⟨hph, -, hsz2, -, hform⟩ := rewriteOK_spec hr
    refine ⟨hpure (prio_rw hr), fun h => ?_, fun a ha => ?_⟩
    · obtain ⟨-, fv', hfv', hn'⟩ := (nodeIn_schedNodes hownF).1 h
      rw [hfv] at hfv'; cases hfv'; exact hn' hph
    rw [hD] at ha
    have hfb' : fv.block = bid := by
      obtain ⟨fv', hfv', -, hblk⟩ := hwf.valueId bid fb ⟨hb, hfb⟩ y hyf
      rw [hfv] at hfv'; cases hfv'; exact hblk
    rw [hfb'] at hform
    rcases hform with ⟨-, c, hc, hcav, hall⟩ | ⟨w, c, neg, hshape, -⟩
    · obtain ⟨d, -, harm⟩ := hall 0 fv.args[0]! (by
        rw [getElem!_pos fv.args 0 (by omega)]; simp [hsz2])
      rcases harm with ⟨-, hargs, -⟩ | ⟨-, hargs, -⟩ | ⟨n, -, hargs, hn, -⟩ |
          ⟨n, -, hargs, hn, -⟩ <;>
        rw [hargs] at ha <;> simp only [Array.toList, List.mem_cons, List.not_mem_nil,
          or_false] at ha
      · subst ha; exact hav _ hcav
      · subst ha; exact hav _ hcav
      · rcases ha with rfl | rfl
        · exact hav _ hcav
        · exact hav _ hn
      · rcases ha with rfl | rfl
        · exact hav _ hcav
        · exact hav _ hn
    · obtain ⟨-, -, -, cv, cvv, x', hargs, hcvn, -⟩ := hshape
      rw [hargs] at ha
      simp only [Array.toList, List.mem_singleton] at ha
      subst ha
      exact hnone _ (isNew_spec hcvn).1
  · right
    refine ⟨hpure (prio_new hok hgv), hnone y hn, fun a ha => ?_⟩
    obtain ⟨nv, a', hnv, -, hargs, hk⟩ := newOK_spec hok
    rw [hgv] at hnv; cases hnv
    rw [hD, hargs] at ha
    simp only [Array.toList, List.mem_singleton] at ha
    subst ha
    rcases hk with ⟨-, hav'⟩ | ⟨-, hav' | ⟨hnew, -⟩⟩
    · exact hav _ hav'
    · exact hav _ hav'
    · exact hnone _ (isNew_spec hnew).1

/-- **The non-pure nodes of a block and their priorities are the same in the target.** -/
theorem sameNP : SameNP (schedNodes f fb).toList (schedNodes g gb).toList := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  have hbg : bid ∈ g.blocks := by rw [S.blocks]; exact hb
  have hownF := valuesOwn hwf hb hfb
  have hndF := hwf.valuesNodup _ _ ⟨hb, hfb⟩
  have hownG := valuesOwn hwg hbg hgb
  have hndG := hwg.valuesNodup _ _ ⟨hbg, hgb⟩
  have hST : ∀ x, npIn (schedNodes f fb).toList x = true →
      npIn (schedNodes g gb).toList x = true := by
    intro x h
    obtain ⟨hx, v, hv, hp, hpr⟩ := (npIn_sched hownF hndF).1 h
    obtain ⟨hxg, -⟩ := fnode S hb hfb hgb ((nodeIn_schedNodes hownF).2 ⟨hx, v, hv, hp⟩)
    obtain ⟨hxg, gv, hgv, hgp⟩ := (nodeIn_schedNodes hownG).1 hxg
    obtain ⟨gv', hgv', -, -, -, hr⟩ := S.rel.value x v hv
    rw [hgv] at hgv'; cases hgv'
    have hop : gv.op = v.op := by
      rcases hr with ⟨h1, -⟩ | hr
      · exact h1
      · exact absurd (rewriteOK_spec hr).1 hp
    exact (npIn_sched hownG hndG).2 ⟨hxg, gv, hgv, hgp, by rw [hop]; exact hpr⟩
  have hTS : ∀ x, npIn (schedNodes g gb).toList x = true →
      npIn (schedNodes f fb).toList x = true := by
    intro x h
    rcases tnode S hb hfb hgb (npIn_iff.1 h).1 with hS | ⟨hp, -⟩
    · obtain ⟨hx, v, hv, hn⟩ := (nodeIn_schedNodes hownF).1 hS
      obtain ⟨hxg, gv, hgv, -, hpr⟩ := (npIn_sched hownG hndG).1 h
      obtain ⟨gv', hgv', -, -, -, hr⟩ := S.rel.value x v hv
      rw [hgv] at hgv'; cases hgv'
      have hop : gv.op = v.op := by
        rcases hr with ⟨h1, -⟩ | hr
        · exact h1
        · exact absurd (rewriteOK_spec hr).1 hn
      exact (npIn_sched hownF hndF).2 ⟨hx, v, hv, hn, by rw [← hop]; exact hpr⟩
    · exact absurd hp (npIn_iff.1 h).2
  intro x
  refine ⟨Bool.eq_iff_iff.2 ⟨hTS x, hST x⟩, fun h => ?_⟩
  obtain ⟨hx, v, hv, hp, -⟩ := (npIn_sched hownF hndF).1 h
  obtain ⟨hxg, gv, hgv, -, -⟩ := (npIn_sched hownG hndG).1 (hST x h)
  obtain ⟨gv', hgv', -, -, -, hr⟩ := S.rel.value x v hv
  rw [hgv] at hgv'; cases hgv'
  have hop : gv.op = v.op := by
    rcases hr with ⟨h1, -⟩ | hr
    · exact h1
    · exact absurd (rewriteOK_spec hr).1 hp
  exact ⟨_, _, CopyElim.nodeOf_schedNodes hownF hndF hx hv hp,
    CopyElim.nodeOf_schedNodes hownG hndG hxg hgv (by rw [hop]; exact hp), by simp [hop]⟩

/-- **Target dependencies from a source node are source dependencies.** -/
theorem depBack {u v : ID}
    (hd : Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList) u v) :
    NodeIn (schedNodes f fb).toList u →
      Dep (NodeIn (schedNodes f fb).toList) (argsOf (schedNodes f fb).toList) u v ∧
        NodeIn (schedNodes f fb).toList v := by
  induction hd with
  | @arg a y ha hy hay =>
    intro haS
    rcases tnode S hb hfb hgb hy with hyS | ⟨-, -, hno⟩
    · obtain ⟨-, hargs⟩ := fnode S hb hfb hgb hyS
      rw [hargs] at hay
      exact ⟨.arg haS hyS hay, hyS⟩
    · exact absurd haS (hno a hay)
  | trans _ _ ih1 ih2 =>
    intro hu
    obtain ⟨h1, hw⟩ := ih1 hu
    obtain ⟨h2, hv⟩ := ih2 hw
    exact ⟨.trans h1 h2, hv⟩

/-- **A target prefix before a non-pure node lists only source nodes the source lists before
it** (`sched_transfer`). -/
theorem schedTransfer {oS oT : Array ID} (hso : schedule f fb = some oS)
    (hoT : schedule g gb = some oT) {r : ID} {k k' : Nat} (hk : oS.toList[k]? = some r)
    (hk' : oT.toList[k']? = some r) (hrp : npIn (schedNodes f fb).toList r = true) :
    ∀ j y, j < k' → oT.toList[j]? = some y → NodeIn (schedNodes f fb).toList y →
      ∃ i < k, oS.toList[i]? = some y :=
  sched_transfer (schedule_spec hso) (schedule_spec hoT) (sameNP S hb hfb hgb)
    (fun x y hx _ => ⟨depPres S hb hfb hgb,
      fun hd => (depBack S hb hfb hgb hd (npIn_iff.1 hx).1).1⟩) hk hk' hrp
    fun a y ha hy hay _ => ⟨(fnode S hb hfb hgb ha).1,
      .arg (fnode S hb hfb hgb ha).1 (fnode S hb hfb hgb hy).1
        (by rw [(fnode S hb hfb hgb hy).2]; exact hay)⟩

end

/-- **A block the source panics in makes the target panic alike.** -/
theorem enter_panic (S : Setup tabs f g) {env : Env} {fr frT : Frame} {bid : ID} {i : Nat}
    (hA : At env tabs f fr bid i) (hT : TR f g fr frT) {fb : Block}
    (hfb : f.block? bid = some fb) {e : Panic} {m : Mem}
    (h : enterBlock env (Ctx.make tabs f) fr fb i = .panic e m) :
    ∃ gb, g.block? bid = some gb ∧ enterBlock env (Ctx.make tabs g) frT gb i = .panic e m := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  have hbt := hA.tree S
  have hndF := hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩
  have hownF := valuesOwn hwf hbt.1 hfb
  obtain ⟨fb', hfb', hfid⟩ := hwf.blockId bid hbt.1
  rw [hfb] at hfb'; cases hfb'
  obtain ⟨psS, oS, hpsS, hso, hev⟩ := enterBlock_panic h
  rw [hfid, sched_of_block hfb] at hso
  obtain ⟨pre, r, post, Gpre, hsplit, hpre, hrp⟩ := evalAll_panic_split hev
  obtain ⟨gb, psT, oT, H, hgbb, hgid, hpsT, hoT, hH, hHsz, hHG, hagree, hframe, hsz, hrefS,
    hloc, hsame⟩ := targetRun S hA hT hfb hpsS hso hsplit hpre
  have hbg : bid ∈ g.blocks := by rw [S.blocks]; exact hbt.1
  have hownG := valuesOwn hwg hbg hgbb
  have hndG := hwg.valuesNodup _ _ ⟨hbg, hgbb⟩
  obtain ⟨-, otopoT, omemT⟩ := schedule_topo hownG hndG hoT
  obtain ⟨-, -, omem⟩ := schedule_topo hownF hndF hso
  -- the panicking root
  have hrS : r ∈ oS.toList := by rw [hsplit]; simp
  obtain ⟨hrb, fvr, hfvr, hrnph⟩ := (omem r).1 hrS
  rw [stepV_of hfvr] at hrp
  have hrop := evalValue_panic_op hrp
  obtain ⟨gvr, hgvr, -, -, -, hr⟩ := S.rel.value r fvr hfvr
  have hrsame : gvr.op = fvr.op ∧ gvr.aux = fvr.aux ∧ gvr.auxInt = fvr.auxInt ∧
      gvr.args = fvr.args := by
    rcases hr with h | h
    · exact h
    · exact absurd (rewriteOK_spec h).1 hrnph
  have hnodeR : NodeIn (schedNodes f fb).toList r :=
    (nodeIn_schedNodes hownF).2 ⟨hrb, fvr, hfvr, hrnph⟩
  have hrT : r ∈ oT.toList :=
    (omemT r).2 ((nodeIn_schedNodes hownG).1 (fnode S hbt.1 hfb hgbb hnodeR).1)
  obtain ⟨pre', post', hsplitT⟩ := List.append_of_mem hrT
  have hk : oS.toList[pre.length]? = some r := by rw [hsplit]; simp
  have hk' : oT.toList[pre'.length]? = some r := by rw [hsplitT]; simp
  have htr := schedTransfer S hbt.1 hfb hgbb hso hoT hk hk'
    ((npIn_sched hownF hndF).2 ⟨hrb, fvr, hfvr, hrnph, prio_ne_zero_of_panic hrop⟩)
  -- the target's prefix evaluates against the reference frame
  have hL := hloc pre' (fun x hx => by rw [hsplitT]; exact List.mem_append_left _ hx)
    fun x hx hN => by
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
      have hjl : j < pre'.length := (List.getElem?_eq_some_iff.1 hj).1
      have hjT : oT.toList[j]? = some x := by
        rw [hsplitT, List.getElem?_append_left hjl]; exact hj
      obtain ⟨i', hi', hix⟩ := htr j x hjl hjT hN
      rw [hsplit, List.getElem?_append_left hi'] at hix
      exact List.mem_of_getElem? hix
  have href := refOK_of_topo (Q := fun a => Listed f a) (pre := []) otopoT
    fun x hx a ha hn => hrefS x hx a ha (by simpa using hn)
  have href' := RefOK.prefix (L2 := r :: post') (by rw [← hsplitT]; exact href)
  have htopoT : TopoRem (argsF (Ctx.make tabs g).f) (pre' ++ r :: post') := by
    rw [← hsplitT]; exact otopoT
  have hargsT : argsF (Ctx.make tabs g).f r = gvr.args.toList := argsF_of (f := g) hgvr
  have hpanT := evalAll_ref_panic (post := post') (g := { frT with regs := setPhis psT frT.regs })
    hL href' (fun a ha => by
      rcases ha with ⟨hn, hl⟩ | hm
      · exact hagree a (by simpa using hn) hl
      · cases hm) hframe hsz
    (fun a ha => by
      by_cases haT : a ∈ oT.toList
      · rw [hsplitT] at haT
        rcases List.mem_append.1 haT with h' | h'
        · exact .inr h'
        · exact absurd h' (topoRem_at htopoT a ha)
      · exact .inl (.inl ⟨by simpa using haT, hrefS r hrT a ha haT⟩))
    (fun g' hg' hag => by
      rw [stepV_of (ctx := Ctx.make tabs g) hgvr, ← hrp]
      exact hsame r fvr gvr hrb hfvr hgvr hrsame (fun msg he => by rw [hrp] at he; cases he)
        g' hg' (fun a ha => hag a (by rw [hargsT]; exact Array.mem_toList_iff.2 ha)))
  refine ⟨gb, hgbb, ?_⟩
  rw [enterBlock_eq, hpsT]
  change (Res.ofOption _ ((Ctx.make tabs g).sched[gb.id]?).join).bind _ = _
  rw [hgid, sched_of_block hgbb, hoT]
  change evalAll env (Ctx.make tabs g) _ oT.toList = _
  rw [hsplitT, hpanT]

end GoFV.Proof.PhiOpt

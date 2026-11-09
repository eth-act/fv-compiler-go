import GoFV.Proof.Pass.FlagAllocLEval

variable [GoFV.SSA.Sem.Addrs]

/-!
# One block of a flagalloc rewrite under `runSched` (issue #385)

The walk `walkB` of block `b` as a simulation (`walk`): `f` evaluates its order `LF`, `g` its
order `LG`, the frames related by `RInv` (kept values have equal registers, each clone of `g`
evaluated so far in the block holds its original's register in `f`); `f`'s frame keeps
`FInv` (lemma (D) of `runL` for `runSched`, inside the block: the values `f` evaluated so far in
the block, and those placed in strict dominators, re-evaluate to their registers). So a clone
evaluates to its original's register (`cloneEval`), a kept value as in `f` (`keptEval`), a
removed value (pure) does not panic, and `g` panics where `f` does.
-/

namespace GoFV.Proof.FlagAllocL

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Proof GoFV.Proof.MoveL Dom

variable {tabs : Tables} {f g : Func} {md : LMode} {env : Env}

/-- The facts of block `b` the walk uses. -/
structure BHyp (ce : CheckEnv) (f g : Func) (b : ID) (fb gb : Block) : Prop where
  wf : WF ce f
  og : GOwn g b gb
  cf : CertOK f
  hb : b ∈ f.blocks
  hfb : f.block? b = some fb
  hgb : g.block? b = some gb
  tree : ((make f).depthOf b).isSome
  low : g.lowered = f.lowered
  own : g.ownAux = f.ownAux

/-- `f`'s side of the walk of block `b`: the rest `LF` of its order, the values `P` it has
evaluated in the block (each re-evaluates to its register, its arguments not in `LF`), and the
values placed in strict dominators (each re-evaluates to its register). -/
structure FInv (tabs : Tables) (f : Func) (md : LMode) (env : Env) (b : ID) (fb : Block)
    (LF P : List ID) (S : Frame) : Prop where
  sz : S.regs.size = f.valueTab.size
  nd : LF.Nodup
  lf : ∀ x ∈ LF, x ∈ fb.values
  pre : ∀ x ∈ P, x ∈ fb.values ∧ x ∉ LF ∧ ∃ v y, f.value? x = some v ∧
    S.regs[x]? = some (some y) ∧ evalValueL md env (Ctx.makeSched tabs f) S v = .ok y ∧
    ∀ a ∈ v.args, a ∉ LF
  anc : ∀ x v, Placed f x v → Anc (make f) v.block b → v.block ≠ b → v.op ≠ .Phi →
    ∃ y, S.regs[x]? = some (some y) ∧ evalValueL md env (Ctx.makeSched tabs f) S v = .ok y
  cover : ∀ x ∈ fb.values, isPhiIn f x = false → x ∈ P ∨ x ∈ LF

/-- The relation of the frames: kept values agree, each clone `c` of the block so far holds its
original `o`'s register (and neither is evaluated again in the block). -/
structure RInv (f g : Func) (gb : Block) (LF LG : List ID) (C : List (ID × ID)) (S T : Frame) :
    Prop where
  fr : T = { S with regs := T.regs }
  sz : T.regs.size = g.valueTab.size
  nd : LG.Nodup
  lg : ∀ x ∈ LG, x ∈ gb.values
  kept : ∀ x, keptB f g x = true → T.regs[x]? = S.regs[x]?
  clones : ∀ c o, (c, o) ∈ C →
    (∃ y, T.regs[c]? = some (some y) ∧ S.regs[o]? = some (some y)) ∧ c ∉ LG ∧ o ∉ LF

theorem fr_set {S T : Frame} (h : T = { S with regs := T.regs }) (z : ID) (y : Val) :
    T.set z y = { S with regs := (T.set z y).regs } := by
  obtain ⟨⟩ := S; obtain ⟨⟩ := T; cases h; rfl

/-! ## Steps -/

/-- `f` evaluates the next value `z` of its order. -/
theorem FInv.step {ce : CheckEnv} {b : ID} {fb gb : Block} (H : BHyp ce f g b fb gb)
    {LF' P : List ID} {z : ID} {S : Frame} (hF : FInv tabs f md env b fb (z :: LF') P S)
    {fz : Value} (hfz : f.value? z = some fz) {y : Val}
    (he : evalValueL md env (Ctx.makeSched tabs f) S fz = .ok y) (ht : ∀ a ∈ fz.args, a ∉ z :: LF') :
    FInv tabs f md env b fb LF' (z :: P) (S.set z y) := by
  have hzf : z ∈ fb.values := hF.lf z List.mem_cons_self
  obtain ⟨fz', hfz', -, hfzb⟩ := H.wf.valueId b fb ⟨H.hb, H.hfb⟩ z hzf
  rw [hfz] at hfz'; cases hfz'
  have hzlt : z < S.regs.size := hF.sz ▸ lt_of_value? hfz
  have hset : S.set z y = { S with regs := (S.set z y).regs } := rfl
  have hnd := List.nodup_cons.1 hF.nd
  refine ⟨by simp [Frame.set, hF.sz], hnd.2, fun x hx => hF.lf x (List.mem_cons_of_mem _ hx),
    fun x hx => ?_, fun x v hx hanc hne hph => ?_, fun x hx hph => ?_⟩
  · rcases List.mem_cons.1 hx with rfl | hx
    · refine ⟨hzf, hnd.1, fz, y, hfz, Frame.set_regs_self hzlt, ?_,
        fun a ha hm => ht a ha (List.mem_cons_of_mem _ hm)⟩
      rw [← he]
      refine (evalValueL_congr hset fun a ha => ?_).symm
      have hza : x ≠ a := fun h => ht a ha (h ▸ List.mem_cons_self)
      rw [Frame.set_regs_ne hza]
    · obtain ⟨hxb, hxL, v, y', hv, hy, hev, hargs⟩ := hF.pre x hx
      have hzx : z ≠ x := fun h => hxL (h ▸ List.mem_cons_self)
      refine ⟨hxb, fun hm => hxL (List.mem_cons_of_mem _ hm), v, y', hv,
        by rw [Frame.set_regs_ne hzx]; exact hy, ?_,
        fun a ha hm => hargs a ha (List.mem_cons_of_mem _ hm)⟩
      rw [← hev]
      refine (evalValueL_congr hset fun a ha => ?_).symm
      have hza : z ≠ a := fun h => hargs a ha (h ▸ List.mem_cons_self)
      rw [Frame.set_regs_ne hza]
  · obtain ⟨y', hy, hev⟩ := hF.anc x v hx hanc hne hph
    have hzx : z ≠ x := by
      rintro rfl
      have h1 := hx.1; rw [hfz] at h1; cases h1; exact hne hfzb
    refine ⟨y', by rw [Frame.set_regs_ne hzx]; exact hy, ?_⟩
    rw [← hev]
    refine (evalValueL_congr hset fun a ha => ?_).symm
    have hza : z ≠ a := by
      rintro rfl
      obtain ⟨hv, hvb, blk, hblk, hxv⟩ := hx
      have hu := H.cf.domRel.uses hvb hblk (Anc.left H.cf.parents hanc) hxv hv hph ha
      have hbo : blockOf f z = b := by unfold blockOf; rw [hfz]; exact hfzb
      rw [hbo] at hu
      exact hne (Anc.antisymm H.cf.parents hanc hu)
    rw [Frame.set_regs_ne hza]
  · rcases hF.cover x hx hph with h | h
    · exact .inl (List.mem_cons_of_mem _ h)
    · rcases List.mem_cons.1 h with rfl | h
      · exact .inl List.mem_cons_self
      · exact .inr h

/-- `f` evaluates a removed value. -/
theorem RInv.fstep {gb : Block} {LF' LG : List ID} {C : List (ID × ID)} {z : ID} {S T : Frame}
    (hR : RInv f g gb (z :: LF') LG C S T) (hk : keptB f g z = false) (y : Val) :
    RInv f g gb LF' LG C (S.set z y) T := by
  refine ⟨hR.fr, hR.sz, hR.nd, hR.lg, fun x hx => ?_, fun c o hc => ?_⟩
  · have hzx : z ≠ x := fun h => by rw [h] at hk; rw [hk] at hx; cases hx
    rw [Frame.set_regs_ne hzx]; exact hR.kept x hx
  · obtain ⟨⟨y', h1, h2⟩, h3, h4⟩ := hR.clones c o hc
    have hzo : z ≠ o := fun h => h4 (h ▸ List.mem_cons_self)
    exact ⟨⟨y', h1, by rw [Frame.set_regs_ne hzo]; exact h2⟩, h3,
      fun hm => h4 (List.mem_cons_of_mem _ hm)⟩

/-- Both evaluate the kept value `z`. -/
theorem RInv.kstep {gb : Block} {LF' LG' : List ID} {C : List (ID × ID)} {z : ID} {S T : Frame}
    (hR : RInv f g gb (z :: LF') (z :: LG') C S T) (hzS : z < S.regs.size)
    (hzT : z < T.regs.size) (y : Val) :
    RInv f g gb LF' LG' C (S.set z y) (T.set z y) := by
  refine ⟨fr_set hR.fr z y, by simp [Frame.set, hR.sz], (List.nodup_cons.1 hR.nd).2,
    fun x hx => hR.lg x (List.mem_cons_of_mem _ hx), fun x hx => ?_, fun c o hc => ?_⟩
  · by_cases hzx : z = x
    · subst hzx; rw [Frame.set_regs_self hzS, Frame.set_regs_self hzT]
    · rw [Frame.set_regs_ne hzx, Frame.set_regs_ne hzx]; exact hR.kept x hx
  · obtain ⟨⟨y', h1, h2⟩, h3, h4⟩ := hR.clones c o hc
    have hzo : z ≠ o := fun h => h4 (h ▸ List.mem_cons_self)
    have hzc : z ≠ c := fun h => h3 (h ▸ List.mem_cons_self)
    exact ⟨⟨y', by rw [Frame.set_regs_ne hzc]; exact h1, by rw [Frame.set_regs_ne hzo]; exact h2⟩,
      fun hm => h3 (List.mem_cons_of_mem _ hm), fun hm => h4 (List.mem_cons_of_mem _ hm)⟩

/-- `g` evaluates a clone `x` of `o` to `o`'s register. -/
theorem RInv.cstep {gb : Block} {LF LG' : List ID} {C : List (ID × ID)} {x o : ID} {S T : Frame}
    (hR : RInv f g gb LF (x :: LG') C S T) (hk : keptB f g x = false) {y : Val}
    (hxT : x < T.regs.size) (hSo : S.regs[o]? = some (some y)) (hoL : o ∉ LF) :
    RInv f g gb LF LG' ((x, o) :: C) S (T.set x y) := by
  refine ⟨fr_set hR.fr x y, by simp [Frame.set, hR.sz], (List.nodup_cons.1 hR.nd).2,
    fun z hz => hR.lg z (List.mem_cons_of_mem _ hz), fun z hz => ?_, fun c o' hc => ?_⟩
  · have hxz : x ≠ z := fun h => by rw [h] at hk; rw [hk] at hz; cases hz
    rw [Frame.set_regs_ne hxz]; exact hR.kept z hz
  · rcases List.mem_cons.1 hc with h | hc
    · cases h
      exact ⟨⟨y, Frame.set_regs_self hxT, hSo⟩, (List.nodup_cons.1 hR.nd).1, hoL⟩
    · obtain ⟨⟨y', h1, h2⟩, h3, h4⟩ := hR.clones c o' hc
      have hxc : x ≠ c := fun h => h3 (h ▸ List.mem_cons_self)
      exact ⟨⟨y', by rw [Frame.set_regs_ne hxc]; exact h1, h2⟩,
        fun hm => h3 (List.mem_cons_of_mem _ hm), h4⟩

/-! ## Evaluations -/

/-- Arguments related by `argRel` read equal registers, given `f`'s. -/
theorem argRel_regs {gb : Block} {LF LG : List ID} {C : List (ID × ID)} {S T : Frame}
    (hR : RInv f g gb LF LG C S T) {ga fa : ID} (h : argRel f g C ga fa = true) {y : Val}
    (hS : S.regs[fa]? = some (some y)) : T.regs[ga]? = some (some y) := by
  rcases argRel_spec h with ⟨rfl, hk⟩ | hc
  · rw [hR.kept ga hk, hS]
  · obtain ⟨⟨y', h1, h2⟩, -, -⟩ := hR.clones ga fa hc
    rw [hS] at h2; cases h2; exact h1

/-- **A kept value evaluates in `g` as in `f`** (when `f`'s does not get stuck). -/
theorem keptEval {ce : CheckEnv} {b : ID} {fb gb : Block} (H : BHyp ce f g b fb gb)
    {LF LG : List ID} {C : List (ID × ID)} {S T : Frame} (hR : RInv f g gb LF LG C S T) {z : ID}
    (hzf : z ∈ fb.values) (hzg : z ∈ gb.values) (hk : keptOK f g C z = true) {fz gz : Value}
    (hfz : f.value? z = some fz) (hgz : g.value? z = some gz)
    (hdef : ∀ a ∈ fz.args, ∃ y, S.regs[a]? = some (some y)) :
    evalValueL md env (Ctx.makeSched tabs g) T gz = evalValueL md env (Ctx.makeSched tabs f) S fz := by
  obtain ⟨fz', gz', hfz', hgz', hop, hty, haux, hai, hsx, hargs⟩ := keptOK_spec hk
  rw [hfz] at hfz'; cases hfz'
  rw [hgz] at hgz'; cases hgz'
  obtain ⟨fz2, hfz2, hfid, -⟩ := H.wf.valueId b fb ⟨H.hb, H.hfb⟩ z hzf
  rw [hfz] at hfz2; cases hfz2
  obtain ⟨gz2, hgz2, hgid, -⟩ := H.og.valueId z hzg
  rw [hgz] at hgz2; cases hgz2
  obtain ⟨hlen, hk2⟩ := args2_spec hargs
  refine evalValueL_eq_of_args hop haux hai (hgid.trans hfid.symm) (by simpa using hlen)
    (fun k a ha => ?_) hR.fr (by rw [hfid]; exact tys_eq H.low hgz hfz hty)
    (by rw [makeSched_tabs, makeSched_tabs]) (params_eq H.own) act_eq
    (by rw [makeSched_f, makeSched_f]; exact hsx)
  obtain ⟨a', ha', hr⟩ := hk2 k a (by rw [Array.getElem?_toList]; exact ha)
  obtain ⟨y, hy⟩ := hdef a (Array.mem_of_getElem? ha)
  exact ⟨a', y, by rw [← Array.getElem?_toList]; exact ha', hy, argRel_regs hR hr hy⟩

/-- **A clone evaluates to its original's register**, which `f` does not evaluate again in the
block. -/
theorem cloneEval {ce : CheckEnv} {b : ID} {fb gb : Block} (H : BHyp ce f g b fb gb)
    {LF LG P : List ID} {C : List (ID × ID)} {S T : Frame}
    (hF : FInv tabs f md env b fb LF P S) (hR : RInv f g gb LF LG C S T) {x o : ID}
    (hxg : x ∈ gb.values) (hc : cloneOK (make f) f g b P C x o = true) :
    ∃ gx y, g.value? x = some gx ∧
      evalValueL md env (Ctx.makeSched tabs g) T gx = .ok y ∧ S.regs[o]? = some (some y) ∧ o ∉ LF := by
  obtain ⟨ov, gx, hov, hgx, hcl, hop, hty, haux, hai, hargs, hav⟩ := cloneOK_spec hc
  have hph : ov.op ≠ .Phi := fun h => by rw [hop, h] at hcl; cases hcl
  obtain ⟨gx2, hgx2, hgid, -⟩ := H.og.valueId x hxg
  rw [hgx] at hgx2; cases hgx2
  -- the original is available
  obtain ⟨y, hSo, hev, hoid, hoL⟩ : ∃ y, S.regs[o]? = some (some y) ∧
      evalValueL md env (Ctx.makeSched tabs f) S ov = .ok y ∧ ov.id = o ∧ o ∉ LF := by
    rcases hav with hP | ⟨hne, hanc, hmem, hl⟩
    · obtain ⟨hob, hoL, v, y, hv, hy, hev, -⟩ := hF.pre o hP
      rw [hov] at hv; cases hv
      obtain ⟨v2, hv2, hid, -⟩ := H.wf.valueId b fb ⟨H.hb, H.hfb⟩ o hob
      rw [hov] at hv2; cases hv2
      exact ⟨y, hy, hev, hid, hoL⟩
    · obtain ⟨blk, hblk, hob⟩ := listedIn_spec hl
      obtain ⟨y, hy, hev⟩ := hF.anc o ov ⟨hov, hmem, blk, hblk, hob⟩
        ((anc_iff H.cf.parents).1 hanc) hne hph
      obtain ⟨v2, hv2, hid, -⟩ := H.wf.valueId ov.block blk ⟨hmem, hblk⟩ o hob
      rw [hov] at hv2; cases hv2
      refine ⟨y, hy, hev, hid, fun hm => ?_⟩
      obtain ⟨v3, hv3, -, hvb⟩ := H.wf.valueId b fb ⟨H.hb, H.hfb⟩ o (hF.lf o hm)
      rw [hov] at hv3; cases hv3
      exact hne hvb
  obtain ⟨hlen, hk2⟩ := args2_spec hargs
  have hdef := evalValueL_args_def (md := md) (env := env) (ctx := Ctx.makeSched tabs f)
    (fr := S) (v := ov) (by rw [hev]; nofun)
  refine ⟨gx, y, hgx, ?_, hSo, hoL⟩
  rw [← hev]
  refine evalValueL_clone hcl hop haux hai (by simpa using hlen) (fun k a ha => ?_)
    (by rw [hgid, hoid]; exact tys_eq H.low hgx hov hty)
  obtain ⟨a', ha', hr⟩ := hk2 k a (by rw [Array.getElem?_toList]; exact ha)
  obtain ⟨y', hy'⟩ := hdef a (Array.mem_of_getElem? ha)
  exact ⟨a', y', by rw [← Array.getElem?_toList]; exact ha', hy', argRel_regs hR hr hy'⟩

/-! ## The walk -/

/-- Outcomes of `f`'s and `g`'s evaluation of a block: `g` evaluates to related frames where
`f` does, panics alike. -/
def WOut (Q : Frame → Frame → Prop) : Res Frame → Res Frame → Prop
  | .ok S', rT => ∃ T', rT = .ok T' ∧ Q S' T'
  | .panic e m, rT => rT = .panic e m
  | .stuck _, _ => True

/-- The end of the walk: `f`'s side and the relation with nothing left, and the controls. -/
def WEnd (tabs : Tables) (f g : Func) (md : LMode) (env : Env) (b : ID) (fb gb : Block)
    (S T : Frame) : Prop :=
  ∃ P C, FInv tabs f md env b fb [] P S ∧ RInv f g gb [] [] C S T ∧ ctrlsOK f g fb gb C = true

/-- **The walk of block `b`**: `g`'s evaluation of its order simulates `f`'s. -/
theorem walk {ce : CheckEnv} {b : ID} {fb gb : Block} (H : BHyp ce f g b fb gb)
    {cert : Array (Option ID)} :
    ∀ (n : Nat) (LF LG P : List ID) (C : List (ID × ID)) (S T : Frame),
      LF.length + LG.length = n → walkB (make f) f g cert b fb gb LF LG P C = true →
      FInv tabs f md env b fb LF P S → RInv f g gb LF LG C S T →
      WOut (WEnd tabs f g md env b fb gb)
        (evalAllL md env (Ctx.makeSched tabs f) S LF) (evalAllL md env (Ctx.makeSched tabs g) T LG) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro LF LG P C S T hn hW hF hR
  -- a clone step of `g`
  have clone : ∀ (x : ID) (LG' : List ID), LG = x :: LG' → x ∉ fb.values → ∀ o,
      cloneOK (make f) f g b P C x o = true →
      walkB (make f) f g cert b fb gb LF LG' P ((x, o) :: C) = true →
      WOut (WEnd tabs f g md env b fb gb)
        (evalAllL md env (Ctx.makeSched tabs f) S LF) (evalAllL md env (Ctx.makeSched tabs g) T LG) := by
    intro x LG' hLG hxf o hc hW'
    subst hLG
    have hxg : x ∈ gb.values := hR.lg x List.mem_cons_self
    obtain ⟨gx, y, hgx, hev, hSo, hoL⟩ := cloneEval H hF hR hxg hc
    have hk := not_kept_g H.og H.hfb hxg hxf
    have hxT : x < T.regs.size := hR.sz ▸ lt_of_value? hgx
    rw [evalAllL_cons, stepVL_of (by rw [makeSched_f]; exact hgx), hev]
    exact ih _ (by simp at hn; omega) LF LG' P ((x, o) :: C) S (T.set x y) rfl hW' hF
      (hR.cstep hk hxT hSo hoL)
  match LF, LG with
  | [], [] =>
    simp only [walkB] at hW
    exact ⟨T, rfl, P, C, hF, hR, hW⟩
  | [], x :: LG' =>
    simp only [walkB, Bool.and_eq_true, Bool.not_eq_true'] at hW
    obtain ⟨hxf, hW⟩ := hW
    cases hcx : cert.getD x none with
    | none => rw [hcx] at hW; cases hW
    | some o =>
      rw [hcx] at hW
      simp only [Bool.and_eq_true] at hW
      exact clone x LG' rfl (by simpa using hxf) o hW.1 hW.2
  | z :: LF', LG =>
    have hzf : z ∈ fb.values := hF.lf z List.mem_cons_self
    obtain ⟨fz, hfz, -, -⟩ := H.wf.valueId b fb ⟨H.hb, H.hfb⟩ z hzf
    by_cases hzg : z ∈ gb.values
    · have hzc : gb.values.contains z = true := by simpa using hzg
      rw [walkB.eq_def] at hW
      simp only [hzc, Bool.not_true, Bool.false_eq_true, ite_false] at hW
      cases LG with
      | nil => cases hW
      | cons x LG' =>
        simp only at hW
        by_cases hxf : x ∈ fb.values
        · have hxc : fb.values.contains x = true := by simpa using hxf
          simp only [hxc, ite_true, Bool.and_eq_true, beq_iff_eq] at hW
          obtain ⟨⟨⟨hxz, hk⟩, ht⟩, hW⟩ := hW
          subst hxz
          obtain ⟨gx, hgx, -, -⟩ := H.og.valueId x hzg
          obtain ⟨fz', hfz', hta⟩ := topoOK_spec ht
          rw [hfz] at hfz'; cases hfz'
          rw [evalAllL_cons, stepVL_of (by rw [makeSched_f]; exact hfz), evalAllL_cons,
            stepVL_of (by rw [makeSched_f]; exact hgx)]
          cases he : evalValueL md env (Ctx.makeSched tabs f) S fz with
          | stuck msg => exact True.intro
          | panic e m =>
            rw [keptEval H hR hzf hzg hk hfz hgx
              (evalValueL_args_def (by rw [he]; nofun)), he]
            rfl
          | ok y =>
            rw [keptEval H hR hzf hzg hk hfz hgx (evalValueL_args_def (by rw [he]; nofun)), he]
            exact ih _ (by simp at hn; omega) LF' LG' (x :: P) C (S.set x y) (T.set x y) rfl hW
              (hF.step H hfz he hta)
              (hR.kstep (hF.sz ▸ lt_of_value? hfz) (hR.sz ▸ lt_of_value? hgx) y)
        · have hxc : fb.values.contains x = false := by simpa using hxf
          simp only [hxc, Bool.false_eq_true, ite_false] at hW
          cases hcx : cert.getD x none with
          | none => rw [hcx] at hW; cases hW
          | some o =>
            rw [hcx] at hW
            simp only [Bool.and_eq_true] at hW
            exact clone x LG' rfl hxf o hW.1 hW.2
    · have hzc : gb.values.contains z = false := by simpa using hzg
      rw [walkB.eq_def] at hW
      simp only [hzc, Bool.not_false, ite_true, Bool.and_eq_true] at hW
      obtain ⟨⟨hr, ht⟩, hW⟩ := hW
      obtain ⟨fz', hfz', hcl⟩ := remOK_spec hr
      rw [hfz] at hfz'; cases hfz'
      obtain ⟨fz', hfz', hta⟩ := topoOK_spec ht
      rw [hfz] at hfz'; cases hfz'
      have hk := not_kept_f H.wf H.hb H.hfb H.hgb hzf hzg
      rw [evalAllL_cons, stepVL_of (by rw [makeSched_f]; exact hfz)]
      cases he : evalValueL md env (Ctx.makeSched tabs f) S fz with
      | stuck msg => exact True.intro
      | panic e m => exact absurd he (evalValueL_clone_not_panic hcl)
      | ok y =>
        exact ih _ (by simp at hn; omega) LF' LG (z :: P) C (S.set z y) T rfl hW
          (hF.step H hfz he hta) (hR.fstep hk y)

end GoFV.Proof.FlagAllocL

import GoFV.Proof.Pass.PhiOptForm

variable [GoFV.SSA.Sem.Addrs]

/-!
# phiopt: the target block's schedule

`gval`: a value of a target block is a value of the source block (kept, or a rewritten `Phi`)
or new. `targetSched`: new `Not`s, then new conversions, then the rewritten `Phi`s, then the
source schedule is a dependency order of the target block, so `schedule g gb` is defined.
`depPres`: target dependency chains follow the source's (kept values keep their arguments).
-/

namespace GoFV.Proof.PhiOpt

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.PhiOpt Dom

variable {tabs : Tables} {f g : Func}

/-- What a value of a target block is. -/
theorem gval (S : Setup tabs f g) {bid : ID} (hb : bid ∈ f.blocks) {fb gb : Block}
    (hfb : f.block? bid = some fb) (hgb : g.block? bid = some gb) {x : ID} (hx : x ∈ gb.values) :
    ∃ gv, g.value? x = some gv ∧ gv.id = x ∧
      ((∃ fv, f.value? x = some fv ∧ x ∈ fb.values ∧ fv.id = x ∧ gv.type = fv.type ∧
        ((gv.op = fv.op ∧ gv.aux = fv.aux ∧ gv.auxInt = fv.auxInt ∧ gv.args = fv.args) ∨
          rewriteOK tabs f g fv gv = true)) ∨
       (f.value? x = none ∧ x ∉ fb.values ∧ newOK f g bid x = true)) := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  obtain ⟨gb', hgb', -, -, -, -, -, -, hgf⟩ := S.block hb hfb
  rw [hgb] at hgb'; cases hgb'
  have hbg : bid ∈ g.blocks := by rw [S.blocks]; exact hb
  obtain ⟨gv, hgv, hgid, -⟩ := hwg.valueId bid gb ⟨hbg, hgb⟩ x hx
  refine ⟨gv, hgv, hgid, ?_⟩
  rcases hgf x hx with hxf | ⟨hn, hok⟩
  · obtain ⟨fv, hfv, hfid, -⟩ := hwf.valueId bid fb ⟨hb, hfb⟩ x hxf
    obtain ⟨gv', hgv', -, hty, -, hrel⟩ := S.rel.value x fv hfv
    rw [hgv] at hgv'; cases hgv'
    exact .inl ⟨fv, hfv, hxf, hfid, hty, hrel⟩
  · refine .inr ⟨hn, fun hxf => ?_, hok⟩
    obtain ⟨fv, hfv, -⟩ := hwf.valueId bid fb ⟨hb, hfb⟩ x hxf
    rw [hn] at hfv; cases hfv

/-- A new value of the block, with op `op`. -/
def newOp (f g : Func) (op : Op) (x : ID) : Bool :=
  (f.value? x).isNone && (g.value? x).any (·.op == op)

/-- A rewritten `Phi`. -/
def isRw (f g : Func) (x : ID) : Bool :=
  (f.value? x).any (·.op == .Phi) && (g.value? x).any (·.op != .Phi)

/-- Segmented dependency orders. -/
theorem before_append {N : ID → Prop} {D : ID → List ID} {L1 L2 : List ID}
    (h1 : ∀ (j : Nat) x, L1[j]? = some x → ∀ a ∈ D x, N a → ∃ i < j, L1[i]? = some a)
    (h2 : ∀ (j : Nat) x, L2[j]? = some x → ∀ a ∈ D x, N a →
      a ∈ L1 ∨ ∃ i < j, L2[i]? = some a) :
    ∀ (j : Nat) x, (L1 ++ L2)[j]? = some x → ∀ a ∈ D x, N a →
      ∃ i < j, (L1 ++ L2)[i]? = some a := by
  intro j x hj a ha hN
  by_cases hjl : j < L1.length
  · rw [List.getElem?_append_left hjl] at hj
    obtain ⟨i, hi, hia⟩ := h1 j x hj a ha hN
    exact ⟨i, hi, by rw [List.getElem?_append_left (by omega)]; exact hia⟩
  · rw [List.getElem?_append_right (by omega)] at hj
    rcases h2 _ x hj a ha hN with hm | ⟨i, hi, hia⟩
    · obtain ⟨i, hi⟩ := List.getElem?_of_mem hm
      have := (List.getElem?_eq_some_iff.1 hi).1
      exact ⟨i, by omega, by rw [List.getElem?_append_left this]; exact hi⟩
    · exact ⟨L1.length + i, by omega, by
        rw [List.getElem?_append_right (by omega)]; simpa using hia⟩

/-- No argument of a segment is a node. -/
theorem before_none {N : ID → Prop} {D : ID → List ID} {L : List ID}
    (h : ∀ x ∈ L, ∀ a ∈ D x, ¬ N a) :
    ∀ (j : Nat) x, L[j]? = some x → ∀ a ∈ D x, N a → ∃ i < j, L[i]? = some a :=
  fun _ x hj a ha hN => absurd hN (h x (List.mem_of_getElem? hj) a ha)

/-- An available value is not a value of the target block. -/
theorem avail_not_mem (S : Setup tabs f g) {bid : ID} (hb : bid ∈ f.blocks) {fb gb : Block}
    (hfb : f.block? bid = some fb) (hgb : g.block? bid = some gb) {a : ID}
    (ha : avail f bid a = true) : a ∉ gb.values := by
  intro hm
  obtain ⟨-, -, -, -, -, -, -, hgf⟩ := S.block hb hfb
  obtain ⟨v, blk, hv, -, -, -, -, -, hnl⟩ := avail_spec ha
  obtain ⟨gb', hgb', -, -, -, -, -, -, hgf⟩ := S.block hb hfb
  rw [hgb] at hgb'; cases hgb'
  rcases hgf a hm with h | ⟨h, -⟩
  · exact not_listedIn hfb hnl h
  · rw [hv] at h; cases h

theorem filter_nodup {l : List ID} (h : l.Nodup) (p : ID → Bool) : (l.filter p).Nodup :=
  h.filter p

/-- **The target block has a schedule.** -/
theorem targetSched (S : Setup tabs f g) {bid : ID} (hb : bid ∈ f.blocks) {fb gb : Block}
    (hfb : f.block? bid = some fb) (hgb : g.block? bid = some gb) {oS : Array ID}
    (hsched : schedule f fb = some oS) : ∃ oT, schedule g gb = some oT := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  have hbg : bid ∈ g.blocks := by rw [S.blocks]; exact hb
  have hownG := valuesOwn hwg hbg hgb
  have hndG := hwg.valuesNodup _ _ ⟨hbg, hgb⟩
  have hownF := valuesOwn hwf hb hfb
  have hndF := hwf.valuesNodup _ _ ⟨hb, hfb⟩
  obtain ⟨gb', hgb', -, -, -, -, -, hfg, -⟩ := S.block hb hfb
  rw [hgb] at hgb'; cases hgb'
  obtain ⟨ond, -, omem⟩ := schedule_topo hownF hndF hsched
  have hspec := (schedule_spec hsched).topo
  let N := NodeIn (schedNodes g gb).toList
  let D := argsOf (schedNodes g gb).toList
  let A := gb.values.toList.filter (newOp f g .Not)
  let B := gb.values.toList.filter (newOp f g .CvtBoolToUint8)
  let C := gb.values.toList.filter (isRw f g)
  have hN : ∀ x, N x ↔ x ∈ gb.values ∧ ∃ v, g.value? x = some v ∧ v.op ≠ .Phi :=
    fun x => nodeIn_schedNodes hownG
  have hD : ∀ x gv, x ∈ gb.values → g.value? x = some gv → gv.op ≠ .Phi →
      D x = gv.args.toList := fun x gv hx hgv hn => argsOf_schedNodes hownG hndG hx hgv hn
  have hav : ∀ a, avail f bid a = true → ¬ N a := fun a ha hn =>
    avail_not_mem S hb hfb hgb ha ((hN a).1 hn).1
  -- membership of the segments
  have hA : ∀ x, x ∈ A ↔ x ∈ gb.values ∧ newOp f g .Not x = true := fun x => by
    simp [A, List.mem_filter]
  have hB : ∀ x, x ∈ B ↔ x ∈ gb.values ∧ newOp f g .CvtBoolToUint8 x = true := fun x => by
    simp [B, List.mem_filter]
  have hC : ∀ x, x ∈ C ↔ x ∈ gb.values ∧ isRw f g x = true := fun x => by
    simp [C, List.mem_filter]
  have newOp_iff : ∀ op x, newOp f g op x = true ↔ f.value? x = none ∧
      ∃ v, g.value? x = some v ∧ v.op = op := fun op x => by
    unfold newOp
    cases f.value? x <;> cases g.value? x <;> simp
  have isRw_iff : ∀ x, isRw f g x = true ↔ (∃ fv, f.value? x = some fv ∧ fv.op = .Phi) ∧
      ∃ gv, g.value? x = some gv ∧ gv.op ≠ .Phi := fun x => by
    unfold isRw
    cases f.value? x <;> cases g.value? x <;> simp
  let L := A ++ B ++ C ++ oS.toList
  have hmem : ∀ x, x ∈ L ↔ N x := by
    intro x
    simp only [L, List.mem_append, hA, hB, hC, newOp_iff, isRw_iff, hN]
    constructor
    · rintro (((⟨hx, -, v, hv, hop⟩ | ⟨hx, -, v, hv, hop⟩) | ⟨hx, -, v, hv, hop⟩) | hx)
      · exact ⟨hx, v, hv, by rw [hop]; decide⟩
      · exact ⟨hx, v, hv, by rw [hop]; decide⟩
      · exact ⟨hx, v, hv, hop⟩
      · obtain ⟨hxf, fv, hfv, hfn⟩ := (omem x).1 hx
        obtain ⟨gv, hgv, -, -, -, hr⟩ := S.rel.value x fv hfv
        refine ⟨hfg x hxf, gv, hgv, ?_⟩
        rcases hr with ⟨hop, -⟩ | hr
        · rw [hop]; exact hfn
        · exact absurd (rewriteOK_spec hr).1 hfn
    · rintro ⟨hx, gv, hgv, hgn⟩
      obtain ⟨gv', hgv', -, hk⟩ := gval S hb hfb hgb hx
      rw [hgv] at hgv'; cases hgv'
      rcases hk with ⟨fv, hfv, hxf, -, -, ⟨hop, -⟩ | hr⟩ | ⟨hn, -, hok⟩
      · exact .inr ((omem x).2 ⟨hxf, fv, hfv, by rw [← hop]; exact hgn⟩)
      · exact .inl (.inr ⟨hx, ⟨fv, hfv, (rewriteOK_spec hr).1⟩, gv, hgv, hgn⟩)
      · obtain ⟨nv, a, hnv, -, -, hop⟩ := newOK_spec hok
        rw [hgv] at hnv; cases hnv
        rcases hop with ⟨hop, -⟩ | ⟨hop, -⟩
        · exact .inl (.inl (.inl ⟨hx, hn, gv, hgv, hop⟩))
        · exact .inl (.inl (.inr ⟨hx, hn, gv, hgv, hop⟩))
  have hnd : L.Nodup := by
    have hndl := hndG
    refine List.nodup_append.2 ⟨List.nodup_append.2 ⟨List.nodup_append.2
      ⟨hndl.filter _, hndl.filter _, fun a ha b hb hab => ?_⟩, hndl.filter _,
      fun a ha b hb hab => ?_⟩, ond, fun a ha b hb hab => ?_⟩
    · subst hab
      obtain ⟨-, v, hv, h1⟩ := (newOp_iff _ _).1 ((hA a).1 ha).2
      obtain ⟨-, v', hv', h2⟩ := (newOp_iff _ _).1 ((hB a).1 hb).2
      rw [hv] at hv'; cases hv'; exact absurd (h1.symm.trans h2) (by decide)
    · subst hab
      obtain ⟨⟨fv, hfv, -⟩, -⟩ := (isRw_iff a).1 ((hC a).1 hb).2
      rcases List.mem_append.1 ha with ha | ha
      · obtain ⟨hn, -⟩ := (newOp_iff _ _).1 ((hA a).1 ha).2; rw [hn] at hfv; cases hfv
      · obtain ⟨hn, -⟩ := (newOp_iff _ _).1 ((hB a).1 ha).2; rw [hn] at hfv; cases hfv
    · subst hab
      obtain ⟨-, fv, hfv, hfn⟩ := (omem a).1 hb
      rcases List.mem_append.1 ha with ha | ha
      · rcases List.mem_append.1 ha with ha | ha
        · obtain ⟨hn, -⟩ := (newOp_iff _ _).1 ((hA a).1 ha).2; rw [hn] at hfv; cases hfv
        · obtain ⟨hn, -⟩ := (newOp_iff _ _).1 ((hB a).1 ha).2; rw [hn] at hfv; cases hfv
      · obtain ⟨⟨fv', hfv', hph⟩, -⟩ := (isRw_iff a).1 ((hC a).1 ha).2
        rw [hfv] at hfv'; cases hfv'; exact hfn hph
  -- the arguments of the segments
  have hargA : ∀ x ∈ A, ∀ a ∈ D x, ¬ N a := by
    intro x hx a ha
    obtain ⟨hxb, hnew⟩ := (hA x).1 hx
    obtain ⟨hn, v, hv, hop⟩ := (newOp_iff _ _).1 hnew
    rw [hD x v hxb hv (by rw [hop]; decide)] at ha
    have hok : newOK f g bid x = true := by
      rcases (gval S hb hfb hgb hxb) with ⟨gv, hgv, -, ⟨fv, hfv, -⟩ | ⟨-, -, hok⟩⟩
      · rw [hn] at hfv; cases hfv
      · exact hok
    obtain ⟨nv, a', hnv, -, hargs, hk⟩ := newOK_spec hok
    rw [hv] at hnv; cases hnv
    rw [hargs] at ha
    simp only [List.mem_singleton] at ha
    subst ha
    rcases hk with ⟨-, hav'⟩ | ⟨hop', -⟩
    · exact hav a hav'
    · rw [hop] at hop'; cases hop'
  have hargB : ∀ x ∈ B, ∀ a ∈ D x, N a → a ∈ A := by
    intro x hx a ha hNa
    obtain ⟨hxb, hnew⟩ := (hB x).1 hx
    obtain ⟨hn, v, hv, hop⟩ := (newOp_iff _ _).1 hnew
    rw [hD x v hxb hv (by rw [hop]; decide)] at ha
    have hok : newOK f g bid x = true := by
      rcases (gval S hb hfb hgb hxb) with ⟨gv, hgv, -, ⟨fv, hfv, -⟩ | ⟨-, -, hok⟩⟩
      · rw [hn] at hfv; cases hfv
      · exact hok
    obtain ⟨nv, a', hnv, -, hargs, hk⟩ := newOK_spec hok
    rw [hv] at hnv; cases hnv
    rw [hargs] at ha
    simp only [List.mem_singleton] at ha
    subst ha
    rcases hk with ⟨hop', -⟩ | ⟨-, hav' | ⟨hnew, u, c, hu, hup, -, -⟩⟩
    · rw [hop] at hop'; cases hop'
    · exact absurd hNa (hav a hav')
    · obtain ⟨hnn, blk, hblk, hmem⟩ := isNew_spec hnew
      rw [hgb] at hblk; cases hblk
      exact (hA a).2 ⟨hmem, (newOp_iff _ _).2 ⟨hnn, u, hu, hup⟩⟩
  have hargC : ∀ x ∈ C, ∀ a ∈ D x, N a → a ∈ B := by
    intro x hx a ha hNa
    obtain ⟨hxb, hrw⟩ := (hC x).1 hx
    obtain ⟨⟨fv, hfv, -⟩, gv, hgv, hgn⟩ := (isRw_iff x).1 hrw
    rw [hD x gv hxb hgv hgn] at ha
    obtain ⟨gv', hgv', -, -, -, hr⟩ := S.rel.value x fv hfv
    rw [hgv] at hgv'; cases hgv'
    have hfb' : fv.block = bid := by
      obtain ⟨fv', hfv', -, hblk⟩ := hwf.valueId bid fb ⟨hb, hfb⟩ x
        (by rcases (gval S hb hfb hgb hxb) with ⟨_, _, _, ⟨_, _, h, _⟩ | ⟨h, _⟩⟩
            · exact h
            · rw [hfv] at h; cases h)
      rw [hfv] at hfv'; cases hfv'; exact hblk
    rcases hr with ⟨hop, -⟩ | hr
    · exfalso
      obtain ⟨⟨fv', hfv', hph⟩, -⟩ := (isRw_iff x).1 hrw
      rw [hfv] at hfv'; cases hfv'; exact hgn (hop.trans hph)
    obtain ⟨-, -, hsz2, -, hform⟩ := rewriteOK_spec hr
    rw [hfb'] at hform
    rcases hform with ⟨-, c, hc, hcav, hall⟩ | ⟨w, c, neg, hshape, -⟩
    · -- boolean forms: the arguments are available
      exfalso
      obtain ⟨d, -, harm⟩ := hall 0 fv.args[0]! (by
        rw [getElem!_pos fv.args 0 (by omega)]; simp [hsz2])
      rcases harm with ⟨-, hargs, -⟩ | ⟨-, hargs, -⟩ | ⟨n, -, hargs, hn, -⟩ | ⟨n, -, hargs, hn, -⟩ <;>
        rw [hargs] at ha <;> simp only [List.mem_cons, List.not_mem_nil,
          or_false] at ha
      · subst ha; exact hav _ hcav hNa
      · subst ha; exact hav _ hcav hNa
      · rcases ha with rfl | rfl
        · exact hav _ hcav hNa
        · exact hav _ hn hNa
      · rcases ha with rfl | rfl
        · exact hav _ hcav hNa
        · exact hav _ hn hNa
    · obtain ⟨-, -, -, cv, cvv, x', hargs, hcvn, hcvv, hcop, -⟩ := hshape
      rw [hargs] at ha
      simp only [List.mem_singleton] at ha
      subst ha
      obtain ⟨hnn, blk, hblk, hmem⟩ := isNew_spec hcvn
      rw [hgb] at hblk; cases hblk
      exact (hB a).2 ⟨hmem, (newOp_iff _ _).2 ⟨hnn, cvv, hcvv, hcop⟩⟩
  have hargS : ∀ (j : Nat) x, oS.toList[j]? = some x → ∀ a ∈ D x, N a →
      a ∈ A ++ B ++ C ∨ ∃ i < j, oS.toList[i]? = some a := by
    intro j x hj a ha hNa
    rcases List.mem_append.1 ((hmem a).2 hNa) with h | h
    · exact .inl h
    · right
      have hxS := List.mem_of_getElem? hj
      obtain ⟨hxf, fv, hfv, hfn⟩ := (omem x).1 hxS
      obtain ⟨gv, hgv, -, -, -, hr⟩ := S.rel.value x fv hfv
      have hsame : gv.op = fv.op ∧ gv.args = fv.args := by
        rcases hr with ⟨h1, -, -, h4⟩ | hr
        · exact ⟨h1, h4⟩
        · exact absurd (rewriteOK_spec hr).1 hfn
      rw [hD x gv (hfg x hxf) hgv (by rw [hsame.1]; exact hfn), hsame.2] at ha
      obtain ⟨haf, fa, hfa, hfan⟩ := (omem a).1 h
      refine hspec.before j x hj a ?_ ((nodeIn_schedNodes hownF).2 ⟨haf, fa, hfa, hfan⟩)
      rw [argsOf_schedNodes hownF hndF hxf hfv hfn]; exact ha
  have hT : Order.Topo N D L := ⟨hnd, hmem,
    before_append (before_append (before_append (before_none hargA)
      (fun j x hj a ha hNa => .inl (hargB x (List.mem_of_getElem? hj) a ha hNa)))
      (fun j x hj a ha hNa => .inl (List.mem_append_right _ (hargC x (List.mem_of_getElem? hj) a ha hNa))))
      hargS⟩
  exact schedule_some (schedNodes_ids hownG hndG) hT

/-- A source node is a target node with the same arguments. -/
theorem fnode (S : Setup tabs f g) {bid : ID} (hb : bid ∈ f.blocks) {fb gb : Block}
    (hfb : f.block? bid = some fb) (hgb : g.block? bid = some gb) {x : ID}
    (hx : NodeIn (schedNodes f fb).toList x) :
    NodeIn (schedNodes g gb).toList x ∧
      argsOf (schedNodes g gb).toList x = argsOf (schedNodes f fb).toList x := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  have hbg : bid ∈ g.blocks := by rw [S.blocks]; exact hb
  have hownG := valuesOwn hwg hbg hgb
  have hndG := hwg.valuesNodup _ _ ⟨hbg, hgb⟩
  have hownF := valuesOwn hwf hb hfb
  have hndF := hwf.valuesNodup _ _ ⟨hb, hfb⟩
  obtain ⟨gb', hgb', -, -, -, -, -, hfg, -⟩ := S.block hb hfb
  rw [hgb] at hgb'; cases hgb'
  obtain ⟨hxf, fv, hfv, hfn⟩ := (nodeIn_schedNodes hownF).1 hx
  obtain ⟨gv, hgv, -, -, -, hr⟩ := S.rel.value x fv hfv
  have hsame : gv.op = fv.op ∧ gv.args = fv.args := by
    rcases hr with ⟨h1, -, -, h4⟩ | hr
    · exact ⟨h1, h4⟩
    · exact absurd (rewriteOK_spec hr).1 hfn
  have hgn : gv.op ≠ .Phi := by rw [hsame.1]; exact hfn
  refine ⟨(nodeIn_schedNodes hownG).2 ⟨hfg x hxf, gv, hgv, hgn⟩, ?_⟩
  rw [argsOf_schedNodes hownG hndG (hfg x hxf) hgv hgn, argsOf_schedNodes hownF hndF hxf hfv hfn,
    hsame.2]

/-- **Target dependencies follow the source's.** -/
theorem depPres (S : Setup tabs f g) {bid : ID} (hb : bid ∈ f.blocks) {fb gb : Block}
    (hfb : f.block? bid = some fb) (hgb : g.block? bid = some gb) {x y : ID}
    (h : Order.Dep (NodeIn (schedNodes f fb).toList) (argsOf (schedNodes f fb).toList) x y) :
    Order.Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList) x y := by
  induction h with
  | arg hx hy hxy =>
    obtain ⟨hx', -⟩ := fnode S hb hfb hgb hx
    obtain ⟨hy', hargs⟩ := fnode S hb hfb hgb hy
    exact .arg hx' hy' (by rw [hargs]; exact hxy)
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

end GoFV.Proof.PhiOpt

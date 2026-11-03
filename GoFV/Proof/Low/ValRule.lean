import GoFV.Proof.Low.ValMatch

/-!
# A validated lowering rule event (issue #385)

`RuleFactsL`: what `GoFV.Opt.LowerCheck.ruleOK1` establishes about a rule event `(v, r, defs)` on
the definitions `M` for one commutation choice (`r` the swapped rule `Rule.swapC`), as Phase 1's
`RuleFacts` (`GoFV/Proof/Pass/RewriteTermRule.lean`). `RuleFactsL.frame`: the event's puts change
only the IDs of `defs` (`v` and fresh IDs), each to a term (`termVL`) whose arguments are matched
values or IDs of `defs`.
-/

namespace GoFV.Proof.Low.Val

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Opt.RewriteCheck GoFV.Opt.LowerCheck GoFV.Proof.Term
open GoFV.Proof.Low
open GoFV.Proof.Pass.Rewrite (putAll get?_putAll_not get?_putAll_mem get?_put zip_all_get defIds
  Good good_of_flat evalE_good InI inst_at)
open GoFV.Proof.Rules (Path PEnv DV Oracle evalE toAuxIntD)

/-! ## The static evaluation of a rule event -/

def stVtysL (r : Rule) : List GoFV.Rules.GoTy := r.vars.map (·.ty)

def stNodesL (r : Rule) (defs : List Value) : List (RNode × Value) :=
  match r.result, defs with
  | .build ns, _ :: us => ns.zip us
  | _, _ => []

def stOrL (tabs : Tables) (r : Rule) (defs : List Value) : Oracle :=
  oracleL (stVtysL r) tabs ((r.cond.map (negAtoms false)).getD []) (stNodesL r defs)

def stσL (tabs : Tables) (M : Defs) (r : Rule) (I : Inst) : Nat → DV :=
  sigmaL tabs (envL tabs M I) r.pat

def stEvL (tabs : Tables) (M : Defs) (r : Rule) (defs : List Value) (I : Inst) :
    GoFV.Rules.Expr → DV :=
  evalE (stVtysL r) (stσL tabs M r I) (stOrL tabs r defs) (envL tabs M I)
    (Pat.denL tabs (envL tabs M I) [] r.pat)

/-- What `ruleOK1` (and the term check of `ruleOKL`) establishes. -/
structure RuleFactsL (tabs : Tables) (M : Defs) (r : Rule) (v : ID) (defs : List Value) where
  xv : Value
  I : Inst
  o : Op
  pty : GoFV.Rules.Field
  pai : GoFV.Rules.Field
  pax : GoFV.Rules.Field
  par : GoFV.Rules.Arity
  pargs : List Pat
  pcm : Bool
  hpat : r.pat = .op o none pty pai pax par pargs pcm
  hxv : M.get? v = some xv
  hterm : termVL tabs xv = true
  hid : xv.id = v
  hS : ∀ x, x ∈ GoFV.Opt.RewriteCheck.Pat.sames r.pat → x ∉ GoFV.Opt.RewriteCheck.Pat.opNames r.pat
  hmatch : MatchOKL tabs M I r.pat [] v
  hnodup : (I.map Prod.fst).Nodup
  hhead : I.head? = some ([], v)
  htail : ∀ y ∈ I.tail, y.2 ≠ v
  hcons : consOK (stEvL tabs M r defs I) (stσL tabs M r I) (envL tabs M I) I [] r.pat = true
  hwf : wfOK (envL tabs M I) [] r.pat = true
  hcond : ∀ c, r.cond = some c → stEvL tabs M r defs I c = .bool true
  hargs : GoFV.Proof.Rules.Pat.argsOK (envL tabs M I).ty [] r.pat = true
  htop : Pat.topOKL ((envL tabs M I).ty []) r.pat = true
  hargsL : Pat.argsOKL (envL tabs M I).ty [] r.pat = true
  hleaves : leavesOK M I [] r.pat = true
  hres : resultOKL tabs M (envL tabs M I) r.pat (stEvL tabs M r defs I) (stOrL tabs r defs)
    (stσL tabs M r I) I r xv defs = true
  hreach : ∀ C : ID → Prop, GoFV.Proof.Pass.Rewrite.ArgClosed M C → C v → ∀ y ∈ I, C y.2

theorem ruleFactsL {tabs : Tables} {M : Defs} {r : Rule} {v : ID} {x : Value} {defs : List Value}
    (hx : M.get? v = some x) (hterm : termVL tabs x = true) (hid : x.id = v)
    (h : ruleOK1 tabs M r v x defs = true) : Nonempty (RuleFactsL tabs M r v defs) := by
  unfold ruleOK1 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨-, hpat⟩, h⟩ := h
  split at h
  · cases h
  rename_i I hm
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨htail, hcons⟩, hwf⟩, hcond⟩, hargs⟩, htop⟩, hargsL⟩, hleaves⟩, hres⟩ := h
  obtain ⟨hmo, -, hn, hh⟩ := matchPatL_ok hm
  unfold patOK at hpat
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at hpat
  obtain ⟨htp, hS⟩ := hpat
  revert htp
  rcases hrp : r.pat with _ | _ | _ | ⟨o, nm, pty, pai, pax, par, pargs, pcm⟩ <;>
    intro htp <;> try (simp at htp)
  cases nm with
  | some _ => simp at htp
  | none =>
  have hcond' : ∀ c, r.cond = some c → stEvL tabs M r defs I c = .bool true := by
    intro c hc
    split at hcond
    · rename_i c' hc'
      rw [hc] at hc'; cases hc'
      split at hcond
      · rename_i heq; exact heq
      · cases hcond
    · rename_i hc'; rw [hc] at hc'; cases hc'
  have htail' : ∀ y ∈ I.tail, y.2 ≠ v := by
    simp only [List.all_eq_true, bne_iff_ne, ne_eq] at htail; exact htail
  exact ⟨{
    xv := x, I := I, o := o, pty := pty, pai := pai, pax := pax, par := par,
    pargs := pargs, pcm := pcm, hpat := hrp, hxv := hx, hterm := hterm, hid := hid,
    hS := hS, hmatch := hmo, hnodup := hn, hhead := hh, htail := htail',
    hcons := hcons, hwf := hwf, hcond := hcond', hargs := hargs, htop := htop, hargsL := hargsL,
    hleaves := hleaves, hres := hres,
    hreach := fun C hC hv => matchPatL_closed hC hm hv }⟩

/-! ## Facts about the matched instance -/

section Inst

variable {tabs : Tables} {M : Defs} {r : Rule} {v : ID} {defs : List Value}

theorem RuleFactsL.top_mem (F : RuleFactsL tabs M r v defs) : ([], v) ∈ F.I := by
  have hh := F.hhead
  cases h : F.I with
  | nil => rw [h] at hh; cases hh
  | cons a I =>
    rw [h] at hh; simp only [List.head?_cons, Option.some.injEq] at hh; subst hh
    exact List.mem_cons_self

theorem RuleFactsL.at_eq (F : RuleFactsL tabs M r v defs) {p : Path} {w : ID} (h : (p, w) ∈ F.I) :
    F.I.at p = w := inst_at h F.hnodup

theorem RuleFactsL.at_top (F : RuleFactsL tabs M r v defs) : F.I.at [] = v := F.at_eq F.top_mem

theorem RuleFactsL.ne_v (F : RuleFactsL tabs M r v defs) {p : Path} {w : ID} (h : (p, w) ∈ F.I)
    (hp : p ≠ []) : w ≠ v := by
  have hh := F.hhead
  have ht := F.htail
  cases hI : F.I with
  | nil => rw [hI] at h; cases h
  | cons a I =>
    rw [hI] at hh h ht
    simp only [List.head?_cons, Option.some.injEq] at hh; subst hh
    rcases List.mem_cons.1 h with h | h
    · cases h; exact absurd rfl hp
    · exact ht _ h

theorem oracleL_flat (vtys : List GoFV.Rules.GoTy) (tabs : Tables) (negs : List GoFV.Rules.Expr)
    (nodes : List (RNode × Value)) (x : GoFV.Rules.Expr) :
    ((oracleL vtys tabs negs nodes).dv x).flat = true := by
  simp only [oracleL]; split <;> rfl

theorem oracleL_boolTyped (vtys : List GoFV.Rules.GoTy) (tabs : Tables) (negs : List GoFV.Rules.Expr)
    (nodes : List (RNode × Value)) : Oracle.BoolTyped (oracleL vtys tabs negs nodes) := by
  intro x hx; exact ⟨!(negs.contains x), by simp [oracleL, hx]⟩

theorem RuleFactsL.stσ_good (F : RuleFactsL tabs M r v defs) (x : Nat) :
    Good (InI F.I) (stσL tabs M r F.I x) := by
  unfold stσL
  have hm := F.hmatch
  rw [F.hpat] at hm ⊢
  exact sigmaL_good (Q := fun _ => True) (S := GoFV.Proof.Pass.Rewrite.Pat.sz
      (.op F.o none F.pty F.pai F.pax F.par F.pargs F.pcm))
    (fun _ _ => trivial) (fun p w h _ => ⟨w, h⟩) (fun _ p w h _ _ => ⟨w, h.mem⟩) hm trivial
    (Nat.le_refl _) x

theorem RuleFactsL.stEv_good (F : RuleFactsL tabs M r v defs) (x : GoFV.Rules.Expr) :
    Good (InI F.I) (stEvL tabs M r defs F.I x) :=
  evalE_good _ _ _ F.stσ_good ⟨v, F.top_mem⟩
    (fun x => good_of_flat (oracleL_flat _ _ _ _ x)) x

theorem RuleFactsL.pos_mem (F : RuleFactsL tabs M r v defs) {d : DV} (hd : Good (InI F.I) d)
    {p : Path} (h : DV.pos? d = some p) : (p, F.I.at p) ∈ F.I := by
  cases d <;> simp only [DV.pos?, reduceCtorEq] at h
  rename_i w p'
  subst h
  obtain ⟨w', hw⟩ := hd.1 w p rfl
  rw [F.at_eq hw]; exact hw

end Inst

/-! ## The result -/

/-- The shape of a `copy` result. -/
structure CopyResL (tabs : Tables) (M : Defs) (r : Rule) (v : ID) (defs : List Value)
    (F : RuleFactsL tabs M r v defs) where
  ce : GoFV.Rules.Expr
  u : Value
  p : Path
  hres : r.result = .copy ce
  hdefs : defs = [u]
  hpos : DV.pos? (stEvL tabs M r defs F.I ce) = some p
  hid : u.id = v
  hop : u.op = .Copy
  hargs : u.args = #[F.I.at p]
  hty : (M.get? (F.I.at p)).any (fun y => y.type == u.type &&
    GoFV.Opt.CSE.tyEq (shpL tabs y.type) (shpL tabs F.xv.type)) = true
  hne : F.I.at p ≠ v

/-- The shape of a `build` result: node 0 is `v` (in place), the other nodes fresh. -/
structure BuildResL (tabs : Tables) (M : Defs) (r : Rule) (v : ID) (defs : List Value)
    (F : RuleFactsL tabs M r v defs) where
  nodes : List RNode
  u0 : Value
  us : List Value
  hres : r.result = .build nodes
  hdefs : defs = u0 :: us
  hid0 : u0.id = v
  hhead : (us.map (·.id)).head? = some v
  hlen : us.length = nodes.length
  hfresh : ∀ x ∈ (us.map (·.id)).drop 1, M.get? x = none
  hnodup : ((us.map (·.id)).drop 1).Nodup
  hnv : v ∉ (us.map (·.id)).drop 1
  hnode : ∀ k (h1 : k < nodes.length) (h2 : k < us.length),
    nodeOKL tabs (envL tabs M F.I) r.pat (stEvL tabs M r defs F.I) (stOrL tabs r defs)
      (stσL tabs M r F.I) F.I (us.map (·.id)) (shpL tabs F.xv.type) nodes[k] us[k] = true

theorem RuleFactsL.result {tabs : Tables} {M : Defs} {r : Rule} {v : ID} {defs : List Value}
    (F : RuleFactsL tabs M r v defs) : Nonempty (CopyResL tabs M r v defs F) ∨
      Nonempty (BuildResL tabs M r v defs F) := by
  have h := F.hres
  unfold resultOKL at h
  split at h
  · rename_i ce u hr hb
    simp only at h
    split at h
    · rename_i p hp
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨hid, hop⟩, hargs⟩, hty⟩, hne⟩, -⟩, -⟩ := h
      rw [F.hid] at hid hne
      exact .inl ⟨{
        ce := ce, u := u, p := p, hres := hr, hdefs := rfl, hpos := hp, hid := hid,
        hop := hop, hargs := hargs, hty := hty, hne := hne }⟩
    · cases h
  · rename_i nodes u0 us hr hb
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨hid0, hhd⟩, hlen⟩, hfresh⟩, hnd⟩, hnv⟩, hnode⟩ := h
    simp only [beq_iff_eq] at hid0 hlen hhd
    simp only [List.all_eq_true, Option.isNone_iff_eq_none] at hfresh
    simp only [decide_eq_true_eq] at hnd
    simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hnv
    rw [F.hid] at hid0 hnv hhd
    refine .inr ⟨{
      nodes := nodes, u0 := u0, us := us, hres := hr, hdefs := rfl, hid0 := hid0,
      hhead := hhd, hlen := hlen, hfresh := hfresh, hnodup := hnd, hnv := hnv,
      hnode := fun k h1 h2 => ?_ }⟩
    have := zip_all_get (f := fun x => match x with
      | (n, u) => nodeOKL tabs (envL tabs M F.I) r.pat (stEvL tabs M r (u0 :: us) F.I)
          (stOrL tabs r (u0 :: us)) (stσL tabs M r F.I) F.I (us.map (·.id)) (shpL tabs F.xv.type) n u)
      hnode (by rw [hlen]) k h1 h2
    exact this
  · simp at h

/-! ## Result nodes -/

/-- The type shape of a result node. -/
def tySelL (ev : GoFV.Rules.Expr → DV) (or : Oracle) (topTy : Ty) (n : RNode) : Ty :=
  nodeTyL ev or topTy n.ty

/-- The auxint of a result node. -/
def aiSelL (ev : GoFV.Rules.Expr → DV) (or : Oracle) (n : RNode) : Int64 :=
  match n.auxInt with
  | some ae => (toAuxIntD n.op.auxType (ev ae)).getD (or.auxInt ae)
  | none => 0

/-- The value of a result argument. -/
def argValL (tabs : Tables) (e : PEnv) (pat : Pat) (ev : GoFV.Rules.Expr → DV) (or : Oracle)
    (σ : Nat → DV) (topTy : Ty) (nodes : List RNode) (f : Nat) : RArg → Val
  | .var x => (σ x).valOr (or.val (.var x))
  | .node j => nodeDenL tabs e pat ev or σ topTy nodes f j
  | .expr e => (ev e).valOr (or.val e)

theorem nodeDenL_succ (tabs : Tables) (e : PEnv) (pat : Pat) (ev : GoFV.Rules.Expr → DV)
    (or : Oracle) (σ : Nat → DV) (topTy : Ty) (nodes : List RNode) (f k : Nat) (n : RNode)
    (hk : nodes[k]? = some n) :
    nodeDenL tabs e pat ev or σ topTy nodes (f + 1) k =
      (opValL tabs n.op (tySelL ev or topTy n) (aiSelL ev or n) (nodeAuxL e pat or n.aux)
        (n.args.map (argValL tabs e pat ev or σ topTy nodes f))).retypeL (tySelL ev or topTy n) := by
  simp only [nodeDenL, hk]
  rfl

theorem nodeOKL_facts {tabs : Tables} {e : PEnv} {pat : Pat} {ev : GoFV.Rules.Expr → DV}
    {or : Oracle} {σ : Nat → DV} {I : Inst} {ids : List ID} {topTy : Ty} {n : RNode} {u : Value}
    (h : nodeOKL tabs e pat ev or σ I ids topTy n u = true) :
    u.op = n.op ∧ termVL tabs u = true ∧ shpL tabs u.type = tySelL ev or topTy n ∧
      u.auxInt = aiSelL ev or n ∧ u.aux = nodeAuxL e pat or n.aux ∧ u.args.size = n.args.length ∧
      ∀ j (h1 : j < n.args.length) (h2 : j < u.args.size),
        argID σ I ids n.args[j] = some u.args[j] := by
  unfold nodeOKL at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hop, ht⟩, hty⟩, hai⟩, hax⟩, hsz⟩, hargs⟩ := h
  refine ⟨hop, ht, GoFV.Proof.Pass.Rewrite.tyEq_sound hty, hai, hax, hsz, fun j h1 h2 => ?_⟩
  have := zip_all_get (f := fun x => match x with | (a, w) => argID σ I ids a == some w) hargs
    (by simp [hsz]) j h1 (by simpa using h2)
  simpa using this

theorem tySelL_eq {ev ev' : GoFV.Rules.Expr → DV} (hev : ∀ x, (ev x).erase = (ev' x).erase)
    (or : Oracle) (topTy : Ty) (n : RNode) : tySelL ev or topTy n = tySelL ev' or topTy n := by
  unfold tySelL nodeTyL
  split
  · rename_i te _
    rcases DV.erase_eq_cases (hev te) with h | ⟨v, v', p, h, h'⟩
    · rw [h]
    · rw [h, h']
  · rfl

theorem aiSelL_eq {ev ev' : GoFV.Rules.Expr → DV} (hev : ∀ x, (ev x).erase = (ev' x).erase)
    (or : Oracle) (n : RNode) : aiSelL ev or n = aiSelL ev' or n := by
  unfold aiSelL
  split
  · rename_i ae _
    rcases DV.erase_eq_cases (hev ae) with h | ⟨v, v', p, h, h'⟩
    · rw [h]
    · rw [h, h']; rfl
  · rfl

/-! ## The frame of a rule event -/

section Frame

variable {tabs : Tables} {M : Defs} {r : Rule} {v : ID} {defs : List Value}

theorem termVL_of_copy {u : Value} (h : u.op = .Copy) : termVL tabs u = true := by
  have hg : Op.Copy.generic = true := by decide
  have ht : termOp .Copy = true := by decide
  unfold termVL; rw [h]; simp only [hg, ht, ite_true]

theorem CopyResL.ids {F : RuleFactsL tabs M r v defs} (R : CopyResL tabs M r v defs F) :
    defIds defs = [v] := by
  rw [show defIds defs = defIds [R.u] from congrArg _ R.hdefs]; simp [defIds, R.hid]

theorem CopyResL.put {F : RuleFactsL tabs M r v defs} (R : CopyResL tabs M r v defs F) :
    putAll M defs = M.put v R.u := by
  rw [show putAll M defs = putAll M [R.u] from congrArg _ R.hdefs]; simp [putAll, R.hid]

theorem BuildResL.usids {F : RuleFactsL tabs M r v defs} (R : BuildResL tabs M r v defs F) :
    R.us.map (·.id) = v :: (R.us.map (·.id)).drop 1 := by
  have h := R.hhead
  cases hu : R.us.map (·.id) with
  | nil => rw [hu] at h; cases h
  | cons a l => rw [hu] at h; simp only [List.head?_cons, Option.some.injEq] at h; subst h; rfl

theorem BuildResL.ids {F : RuleFactsL tabs M r v defs} (R : BuildResL tabs M r v defs F) :
    defIds defs = v :: R.us.map (·.id) := by
  rw [show defIds defs = defIds (R.u0 :: R.us) from congrArg _ R.hdefs]; simp [defIds, R.hid0]

theorem BuildResL.put {F : RuleFactsL tabs M r v defs} (R : BuildResL tabs M r v defs F) :
    putAll M defs = putAll (M.put v R.u0) R.us := by
  rw [show putAll M defs = putAll M (R.u0 :: R.us) from congrArg _ R.hdefs]
  simp [putAll, R.hid0]

theorem BuildResL.nodup {F : RuleFactsL tabs M r v defs} (R : BuildResL tabs M r v defs F) :
    (R.us.map (·.id)).Nodup := by
  rw [R.usids]; exact List.nodup_cons.2 ⟨R.hnv, R.hnodup⟩

theorem BuildResL.len {F : RuleFactsL tabs M r v defs} (R : BuildResL tabs M r v defs F) :
    0 < R.nodes.length := by
  have := R.usids; rw [← R.hlen]
  cases hu : R.us with
  | nil => rw [hu] at this; cases this
  | cons _ _ => simp

theorem BuildResL.get {F : RuleFactsL tabs M r v defs} (R : BuildResL tabs M r v defs F) (k : Nat)
    (hk : k < R.us.length) : (putAll M defs).get? R.us[k].id = some R.us[k] := by
  rw [R.put]; exact get?_putAll_mem _ _ _ R.nodup (List.getElem_mem hk)

theorem BuildResL.id0 {F : RuleFactsL tabs M r v defs} (R : BuildResL tabs M r v defs F)
    (h0 : 0 < R.us.length) : R.us[0].id = v := by
  obtain ⟨u, l, hu⟩ : ∃ u l, R.us = u :: l := by
    cases h : R.us with
    | nil => simp [h] at h0
    | cons u l => exact ⟨u, l, rfl⟩
  have h1 := R.hhead
  simp only [hu, List.map_cons, List.head?_cons, Option.some.injEq] at h1
  simp only [hu, List.getElem_cons_zero, h1]

theorem RuleFactsL.frame (F : RuleFactsL tabs M r v defs) :
    (∀ y, y ∉ defIds defs → (putAll M defs).get? y = M.get? y) ∧
    v ∈ defIds defs ∧
    (∀ y ∈ defIds defs, y = v ∨ M.get? y = none) ∧
    (∀ y ∈ defIds defs, ∃ u, (putAll M defs).get? y = some u ∧ termVL tabs u = true ∧
      ∀ a ∈ u.args, (∃ p, (p, a) ∈ F.I) ∨ a ∈ defIds defs) := by
  refine ⟨fun y hy => get?_putAll_not defs M y hy, ?_⟩
  rcases F.result with hR | hR
  · obtain ⟨R⟩ := hR
    rw [R.ids, R.put]
    refine ⟨List.mem_singleton_self _, fun y hy => .inl (List.mem_singleton.1 hy), fun y hy => ?_⟩
    rw [List.mem_singleton.1 hy]
    refine ⟨R.u, by rw [get?_put]; simp, termVL_of_copy R.hop, fun a ha => ?_⟩
    rw [R.hargs] at ha
    simp only [List.mem_toArray, List.mem_singleton] at ha
    subst ha
    exact .inl ⟨R.p, F.pos_mem (F.stEv_good R.ce) R.hpos⟩
  · obtain ⟨R⟩ := hR
    rw [R.ids]
    refine ⟨List.mem_cons_self, fun y hy => ?_, fun y hy => ?_⟩
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact .inl rfl
      · rw [R.usids] at hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact .inl rfl
        · exact .inr (R.hfresh y hy)
    · have hy' : y ∈ R.us.map (·.id) := by
        rcases List.mem_cons.1 hy with rfl | hy
        · rw [R.usids]; exact List.mem_cons_self
        · exact hy
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy'
      simp only [List.length_map] at hk
      simp only [List.getElem_map]
      refine ⟨R.us[k], R.get k hk, ?_⟩
      obtain ⟨-, ht, -, -, -, hsz, hargs⟩ := nodeOKL_facts (R.hnode k (R.hlen ▸ hk) hk)
      refine ⟨ht, fun a ha => ?_⟩
      obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem ha
      have harg := hargs j (hsz ▸ hj) hj
      cases hn : (R.nodes[k]'(R.hlen ▸ hk)).args[j]'(hsz ▸ hj) with
      | var x =>
        rw [hn] at harg
        simp only [argID, Option.map_eq_some_iff] at harg
        obtain ⟨p, hp, hpa⟩ := harg
        rw [← hpa]
        exact .inl ⟨p, F.pos_mem (F.stσ_good x) hp⟩
      | node j' =>
        rw [hn] at harg
        simp only [argID] at harg
        exact .inr (List.mem_cons_of_mem _ (List.mem_of_getElem? harg))
      | expr _ =>
        rw [hn] at harg
        simp [argID] at harg

end Frame

end GoFV.Proof.Low.Val

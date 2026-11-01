import GoFV.Proof.Pass.RewriteTermPat

/-!
# A validated rule event (issue #113)

`RuleFacts`: the facts `ruleOK` establishes about a rule event `(v, r, defs)` on the
definitions `M` (`ruleFacts`). `rule_frame`: the event's puts change only the IDs of `defs`
(`v` and fresh IDs), each to a term node whose arguments are matched values or IDs of `defs`.
-/

namespace GoFV.Proof.Pass.Rewrite

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck GoFV.Proof.Term
open GoFV.Rules (Pat Rule RNode RArg Result)
open GoFV.Proof.Rules (DV PEnv Oracle Path Pat.den sigma evalE)

/-! ## Puts -/

theorem get?_put (M : Defs) (x : ID) (u : Value) (y : ID) :
    (M.put x u).get? y = if y = x then some u else M.get? y := by
  unfold Defs.put Defs.get?
  by_cases hx : x < M.size
  · simp only [hx, ite_true, Array.set!, Array.getElem?_setIfInBounds]
    by_cases hxy : x = y
    · subst hxy; simp
    · simp [hxy, Ne.symm hxy]
  · simp only [hx, ite_false, Array.set!, Array.getElem?_setIfInBounds, Array.size_append,
      Array.size_replicate]
    by_cases hxy : x = y
    · subst hxy; simp only [ite_true]
      split
      · rfl
      · omega
    · simp only [hxy, Ne.symm hxy, ite_false, Array.getElem?_append, Array.getElem?_replicate]
      split
      · rfl
      · rw [Array.getElem?_eq_none (by omega)]; split <;> rfl

/-- The definitions after the puts of `l`. -/
def putAll (M : Defs) (l : List Value) : Defs := l.foldl (fun M u => M.put u.id u) M

theorem get?_putAll_not : ∀ (l : List Value) (M : Defs) (y : ID), y ∉ l.map (·.id) →
    (putAll M l).get? y = M.get? y
  | [], _, _, _ => rfl
  | u :: l, M, y, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [putAll, List.foldl_cons]
    rw [show l.foldl (fun M u => M.put u.id u) (M.put u.id u) = putAll (M.put u.id u) l from rfl,
      get?_putAll_not l _ y h.2, get?_put]
    simp only [h.1, ite_false]

theorem get?_putAll_mem : ∀ (l : List Value) (M : Defs) (u : Value), (l.map (·.id)).Nodup →
    u ∈ l → (putAll M l).get? u.id = some u
  | a :: l, M, u, hn, hu => by
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [putAll, List.foldl_cons]
    rw [show l.foldl (fun M u => M.put u.id u) (M.put a.id a) = putAll (M.put a.id a) l from rfl]
    rcases List.mem_cons.1 hu with rfl | hu
    · rw [get?_putAll_not l _ _ hn.1, get?_put]; simp
    · exact get?_putAll_mem l _ u hn.2 hu

/-! ## Matched values are reached from the top -/

theorem mem_swap01 {α : Type} {a : α} : ∀ {l : List α}, a ∈ swap01 l → a ∈ l
  | _ :: _ :: _, h => by
    simp only [swap01, List.mem_cons] at h ⊢
    rcases h with h | h | h
    · exact .inr (.inl h)
    · exact .inl h
    · exact .inr (.inr h)
  | [], h => h
  | [_], h => h

/-- `C` contains the arguments of its values. -/
def ArgClosed (M : Defs) (C : ID → Prop) : Prop :=
  ∀ w x, C w → M.get? w = some x → ∀ a ∈ x.args, C a

mutual
theorem matchPat_closed {M : Defs} {C : ID → Prop} (hC : ArgClosed M C) :
    ∀ {q : Pat} {p : Path} {w : ID} {sw sw' : List Bool} {I : Inst},
      matchPat M q p w sw = some (I, sw') → C w → ∀ y ∈ I, C y.2
  | .op o nm ty ai ax ar args comm, p, w, sw, sw', I, h, hw => by
    obtain ⟨x, hx, -, -, ids, sw1, J, hids, hJ, rfl⟩ := matchPat_op h
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hw
    · refine matchPats_closed hC hJ (fun a ha => hC w x hw hx a ?_) y hy
      rcases hids with rfl | ⟨-, rfl⟩
      · exact Array.mem_toList_iff.1 ha
      · exact Array.mem_toList_iff.1 (mem_swap01 ha)
  | .wild, p, w, sw, sw', I, h, hw | .bind _, p, w, sw, sw', I, h, hw
  | .same _, p, w, sw, sw', I, h, hw => by
    simp only [matchPat, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    intro y hy; simp only [List.mem_singleton] at hy; subst hy; exact hw
theorem matchPats_closed {M : Defs} {C : ID → Prop} (hC : ArgClosed M C) :
    ∀ {qs : List Pat} {p : Path} {i : Nat} {ids : List ID} {sw sw' : List Bool} {J : Inst},
      matchPats M qs p i ids sw = some (J, sw') → (∀ a ∈ ids, C a) → ∀ y ∈ J, C y.2
  | [], p, i, [], sw, sw', J, h, _ => by
    simp only [matchPats, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    intro y hy; cases hy
  | q :: qs, p, i, a :: as, sw, sw', J, h, hids => by
    simp only [matchPats] at h
    split at h
    · cases h
    · rename_i I1 sw1 h1
      split at h
      · cases h
      · rename_i J2 sw2 h2
        cases h
        intro y hy
        rcases List.mem_append.1 hy with hy | hy
        · exact matchPat_closed hC h1 (hids a List.mem_cons_self) y hy
        · exact matchPats_closed hC h2 (fun b hb => hids b (List.mem_cons_of_mem _ hb)) y hy
  | [], _, _, _ :: _, _, _, _, h, _ => by simp [matchPats] at h
  | _ :: _, _, _, [], _, _, _, h, _ => by simp [matchPats] at h
end

/-! ## The static evaluation of a rule event -/

def stVtys (r : Rule) : List GoFV.Rules.GoTy := r.vars.map (·.ty)

def stNodes (r : Rule) (defs : List Value) : List (RNode × Value) :=
  match r.result, defs with
  | .build ns, _ :: us => ns.zip us
  | _, _ => []

def stOr (tabs : Tables) (r : Rule) (defs : List Value) : Oracle :=
  oracle (stVtys r) tabs (stNodes r defs)

def stσ (tabs : Tables) (M : Defs) (r : Rule) (I : Inst) : Nat → DV :=
  GoFV.Proof.Rules.sigmaT tabs (env tabs M I) r.pat

def stEv (tabs : Tables) (M : Defs) (r : Rule) (defs : List Value) (I : Inst) :
    GoFV.Rules.Expr → DV :=
  evalE (stVtys r) (stσ tabs M r I) (stOr tabs r defs) (env tabs M I)
    (GoFV.Proof.Rules.Pat.denT tabs (env tabs M I) [] r.pat)

/-- What `ruleOK` establishes. -/
structure RuleFacts (tabs : Tables) (M : Defs) (r : Rule) (v : ID) (defs : List Value) where
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
  hterm : termOp xv.op = true
  hid : xv.id = v
  hS : ∀ x, x ∈ Pat.sames r.pat → x ∉ Pat.opNames r.pat
  hmatch : MatchOK M I r.pat [] v
  hnodup : (I.map Prod.fst).Nodup
  hhead : I.head? = some ([], v)
  htail : ∀ y ∈ I.tail, y.2 ≠ v
  hcons : consOK (stEv tabs M r defs I) (stσ tabs M r I) (env tabs M I) I [] r.pat = true
  hwf : wfOK (env tabs M I) [] r.pat = true
  hcond : ∀ c, r.cond = some c → stEv tabs M r defs I c = .bool true
  hnat : topAll o (env tabs M I) = true
  hargs : GoFV.Proof.Rules.Pat.argsOK (env tabs M I).ty [] r.pat = true
  hleaves : leavesOK M I [] r.pat = true
  hres : resultOK tabs M (stEv tabs M r defs I) (stOr tabs r defs) (stσ tabs M r I) I r xv defs = true
  hframe : ∀ nu ∈ stNodes r defs,
    frameNodeOK tabs (stEv tabs M r defs I) (env tabs M I) r.pat nu.1 nu.2 = true
  hcf : condFrameOK tabs (env tabs M I) I r.pat r.cond = true
  hreach : ∀ C : ID → Prop, ArgClosed M C → C v → ∀ y ∈ I, C y.2
  hnn : nonNegOKD tabs (putAll M defs).get? I r.pat r.cond = true

theorem ruleFacts {tabs : Tables} {M : Defs} {r : Rule} {v : ID} {defs : List Value}
    (h : ruleOK tabs M r v defs = true) : Nonempty (RuleFacts tabs M r v defs) := by
  unfold ruleOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨-, hpat⟩, h⟩ := h
  split at h
  · cases h
  rename_i xv hxv
  simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at h
  obtain ⟨⟨hterm, hid⟩, sw, -, h⟩ := h
  split at h
  · cases h
  rename_i I sw' hm
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨htail, hcons⟩, hwf⟩, hcond⟩, hnat⟩, hargs⟩, hleaves⟩, hres⟩, hframe⟩, hcf⟩, hnn⟩ := h
  have hframe' : ∀ nu ∈ stNodes r defs,
      frameNodeOK tabs (stEv tabs M r defs I) (env tabs M I) r.pat nu.1 nu.2 = true :=
    List.all_eq_true.1 hframe
  obtain ⟨hmo, -, hn, hh⟩ := matchPat_ok hm
  have hmem : ([], v) ∈ I := by
    cases I with
    | nil => cases hh
    | cons a I => simp only [List.head?_cons, Option.some.injEq] at hh; subst hh; exact List.mem_cons_self
  have hat : I.at [] = v := inst_at hmem hn
  unfold patOK at hpat
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at hpat
  obtain ⟨htop, hS⟩ := hpat
  revert hnat htop
  rcases hrp : r.pat with _ | _ | _ | ⟨o, nm, pty, pai, pax, par, pargs, pcm⟩ <;>
    intro hnat htop <;> try (simp at htop)
  cases nm with
  | some _ => simp at htop
  | none =>
  simp only at hnat
  have hcond' : ∀ c, r.cond = some c → stEv tabs M r defs I c = .bool true := by
    intro c hc
    rw [hc] at hcond
    simp only at hcond
    split at hcond
    · rename_i heq; exact heq
    · cases hcond
  have hnat' : topAll o (env tabs M I) = true := hnat
  have htail' : ∀ y ∈ I.tail, y.2 ≠ v := by
    simp only [List.all_eq_true, bne_iff_ne, ne_eq] at htail; exact htail
  exact ⟨{
    xv := xv, I := I, o := o, pty := pty, pai := pai, pax := pax, par := par,
    pargs := pargs, pcm := pcm, hpat := hrp, hxv := hxv, hterm := hterm, hid := hid,
    hS := hS, hmatch := hmo, hnodup := hn, hhead := hh, htail := htail', hcons := hcons,
    hwf := hwf, hcond := hcond', hnat := hnat', hargs := hargs, hleaves := hleaves, hres := hres,
    hframe := hframe', hcf := hcf, hreach := fun C hC hv => matchPat_closed hC hm hv, hnn := hnn }⟩

/-! ## Facts about the matched instance -/

section Inst

variable {tabs : Tables} {M : Defs} {r : Rule} {v : ID} {defs : List Value}

theorem RuleFacts.top_mem (F : RuleFacts tabs M r v defs) : ([], v) ∈ F.I := by
  have hh := F.hhead
  cases h : F.I with
  | nil => rw [h] at hh; cases hh
  | cons a I => rw [h] at hh; simp only [List.head?_cons, Option.some.injEq] at hh; subst hh;
                exact List.mem_cons_self

theorem RuleFacts.at_top (F : RuleFacts tabs M r v defs) : F.I.at [] = v :=
  inst_at F.top_mem F.hnodup

theorem RuleFacts.ne_v (F : RuleFacts tabs M r v defs) {p : Path} {w : ID} (h : (p, w) ∈ F.I)
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

theorem RuleFacts.at_eq (F : RuleFacts tabs M r v defs) {p : Path} {w : ID} (h : (p, w) ∈ F.I) :
    F.I.at p = w := inst_at h F.hnodup

/-- Matched values of the static instance: positioned values are matched positions. -/
def InI (I : Inst) : Val → Path → Prop := fun _ p => ∃ w, (p, w) ∈ I

theorem oracle_flat (vtys : List GoFV.Rules.GoTy) (tabs : Tables) (nodes : List (RNode × Value))
    (x : GoFV.Rules.Expr) : ((oracle vtys tabs nodes).dv x).flat = true := by
  simp only [oracle]; split <;> rfl

theorem RuleFacts.stσ_good (F : RuleFacts tabs M r v defs) (x : Nat) :
    Good (InI F.I) (stσ tabs M r F.I x) := by
  unfold stσ
  have hm := F.hmatch
  rw [F.hpat] at hm ⊢
  exact sigma_good (S := Pat.sz (.op F.o none F.pty F.pai F.pax F.par F.pargs F.pcm))
    (fun p w h _ => ⟨w, h⟩) (fun _ p w h _ _ => ⟨w, h.mem⟩) hm (Nat.le_refl _) x

theorem RuleFacts.stEv_good (F : RuleFacts tabs M r v defs) (x : GoFV.Rules.Expr) :
    Good (InI F.I) (stEv tabs M r defs F.I x) :=
  evalE_good _ _ _ F.stσ_good ⟨v, F.top_mem⟩
    (fun x => good_of_flat (oracle_flat _ _ _ x)) x

theorem RuleFacts.pos_mem (F : RuleFacts tabs M r v defs) {d : DV} (hd : Good (InI F.I) d)
    {p : Path} (h : DV.pos? d = some p) : (p, F.I.at p) ∈ F.I := by
  cases d <;> simp only [DV.pos?, reduceCtorEq] at h
  rename_i w p'
  subst h
  obtain ⟨w', hw⟩ := hd.1 w p rfl
  rw [F.at_eq hw]; exact hw

end Inst

/-! ## The result -/

theorem zip_all_get {α β : Type} {f : α × β → Bool} :
    ∀ {l1 : List α} {l2 : List β}, (l1.zip l2).all f = true → l1.length = l2.length →
      ∀ k (h1 : k < l1.length) (h2 : k < l2.length), f (l1[k], l2[k]) = true
  | a :: l1, b :: l2, h, hl, 0, _, _ => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h; exact h.1
  | a :: l1, b :: l2, h, hl, k + 1, h1, h2 => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h
    exact zip_all_get h.2 (by simpa using hl) k (by simpa using h1) (by simpa using h2)

/-- The shape of a `copy` result. -/
structure CopyRes (tabs : Tables) (M : Defs) (r : Rule) (v : ID) (defs : List Value)
    (F : RuleFacts tabs M r v defs) where
  ce : GoFV.Rules.Expr
  u : Value
  p : Path
  hres : r.result = .copy ce
  hdefs : defs = [u]
  hpos : DV.pos? (stEv tabs M r defs F.I ce) = some p
  hid : u.id = v
  hop : u.op = .Copy
  hargs : u.args = #[F.I.at p]
  hty : (M.get? (F.I.at p)).any (·.type == u.type) = true
  hne : F.I.at p ≠ v

/-- The shape of a `build` result. -/
structure BuildRes (tabs : Tables) (M : Defs) (r : Rule) (v : ID) (defs : List Value)
    (F : RuleFacts tabs M r v defs) where
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
    nodeOK tabs (stEv tabs M r defs F.I) (stOr tabs r defs) (stσ tabs M r F.I) F.I
      (us.map (·.id)) (tabs.ty F.xv.type) nodes[k] us[k] = true

theorem RuleFacts.result {tabs : Tables} {M : Defs} {r : Rule} {v : ID} {defs : List Value}
    (F : RuleFacts tabs M r v defs) : Nonempty (CopyRes tabs M r v defs F) ∨
      Nonempty (BuildRes tabs M r v defs F) := by
  have h := F.hres
  unfold resultOK at h
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
    simp only at h
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.all_eq_true,
      List.contains_eq_mem, decide_eq_false_iff_not, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨hid0, hhead⟩, hlen⟩, hfresh⟩, hnd⟩, hnv⟩, hnode⟩ := h
    rw [F.hid] at hid0 hhead hnv
    refine .inr ⟨{
      nodes := nodes, u0 := u0, us := us, hres := hr, hdefs := rfl, hid0 := hid0,
      hhead := hhead, hlen := hlen,
      hfresh := fun x hx => by simpa using hfresh x hx,
      hnodup := hnd, hnv := hnv,
      hnode := fun k h1 h2 => ?_ }⟩
    have := zip_all_get (f := fun x => match x with
      | (n, u) => nodeOK tabs (stEv tabs M r (u0 :: us) F.I) (stOr tabs r (u0 :: us))
          (stσ tabs M r F.I) F.I (us.map (·.id)) (tabs.ty F.xv.type) n u)
      (List.all_eq_true.2 hnode) (by rw [hlen]) k h1 h2
    exact this
  · simp at h

end GoFV.Proof.Pass.Rewrite

import GoFV.Opt.ProveCheck.Check

/-!
# The op tables of prove's validator, semantically (issue #24)

Each table entry of `GoFV.Opt.ProveCheck` (`rTab`, `cTab`, `shTab`, `opTab`) evaluates as its
family: `evalPure` at the entry's op is the family function (`rTab_eval`, `cTab_eval`,
`shTab_eval`, `opTab_mem`). Proved by enumerating the tables (each entry by `rfl` at a
concrete op), never by splitting on `Op`.
-/

namespace GoFV.Proof.ProveCheck

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.ProveCheck

theorem mem_of_lookup {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ {l : List (α × β)} {a : α} {b : β}, l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by cases h
  | (k, v) :: l, a, b, h => by
    rw [List.lookup_cons] at h
    by_cases hk : a = k
    · subst hk; simp only [beq_self_eq_true] at h; cases h; exact List.mem_cons_self
    · have : (a == k) = false := by simpa using hk
      simp only [this] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup h)

/-- The family function of an `ROp`. -/
def rOpEval : ROp → Option Width → Int64 → List Val → Val
  | .const w, _, ai, _ => Conv.const w ai
  | .zext a b, _, _, args => Conv.zeroExt a b args
  | .sext a b, _, _, args => Conv.signExt a b args
  | .and w, _, _, args => Sem.Int.and w args
  | .modu w, _, _, args => Sem.Int.modu w args
  | .add w, _, _, args => Sem.Int.add w args
  | .sub w, _, _, args => Sem.Int.sub w args
  | .bitLen w, rw, _, args => Sem.Int.bitLen w rw args
  | .popCount w, rw, _, args => Sem.Int.popCount w rw args
  | .b2u, _, _, args => Conv.boolToUint8 args

theorem rTab_eval {op : Op} {c : ROp} (h : rTab.lookup op = some c) (ty : Ty) (ai : Int64)
    (aux : Option AuxRef) (args : List Val) :
    evalPure op ty ai aux args = rOpEval c ty.width? ai args := by
  have hm := mem_of_lookup h
  simp only [rTab, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- The family function of a comparison kind. -/
def cmpEval : CmpK → List Val → Val
  | .lt w true true, args => Cmp.less w args
  | .lt w true false, args => Cmp.leq w args
  | .lt w false true, args => Cmp.lessU w args
  | .lt w false false, args => Cmp.leqU w args
  | .eq w true, args => Cmp.eq w args
  | .eq w false, args => Cmp.neq w args
  | .bounds sl, args => Cmp.inBounds sl args

theorem cTab_term {op : Op} {k : CmpK} (h : cTab.lookup op = some k) :
    GoFV.Opt.RewriteCheck.termOp op = true := by
  have hm := mem_of_lookup h
  simp only [cTab, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem rTab_term {op : Op} {c : ROp} (h : rTab.lookup op = some c) :
    GoFV.Opt.RewriteCheck.termOp op = true := by
  have hm := mem_of_lookup h
  simp only [rTab, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem cTab_eval {op : Op} {k : CmpK} (h : cTab.lookup op = some k) (ty : Ty) (ai : Int64)
    (aux : Option AuxRef) (args : List Val) : evalPure op ty ai aux args = cmpEval k args := by
  have hm := mem_of_lookup h
  simp only [cTab, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- The family function of a shift kind. -/
def shEval (w a : Width) : Nat → Bool → List Val → Val
  | 0, b => Shift.lsh w a b
  | 1, b => Shift.rsh w a b
  | _, b => Shift.rshu w a b

theorem shTab_eval {op : Op} {w a : Width} {k : Nat} (h : shTab.lookup op = some (w, a, k))
    (ty : Ty) (ai : Int64) (aux : Option AuxRef) (args : List Val) :
    evalPure op ty ai aux args = shEval w a k (ai == 1) args := by
  have hm := mem_of_lookup h
  simp only [shTab, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> rfl

/-- The entries of `opTab`, by kind: what the source and the target op evaluate to. -/
inductive OpPair : Op → Op → Width → Nat → Prop where
  | div {fo go : Op} {w : Width} {fl : Bool} :
      (∀ ty ai aux args, evalPure fo ty ai aux args = Sem.Int.divs w (fl && ai == 1) args) →
      (∀ ty ai aux args, evalPure go ty ai aux args = Sem.Int.divu w args) → OpPair fo go w 0
  | mod {fo go : Op} {w : Width} {fl : Bool} :
      (∀ ty ai aux args, evalPure fo ty ai aux args = Sem.Int.mods w (fl && ai == 1) args) →
      (∀ ty ai aux args, evalPure go ty ai aux args = Sem.Int.modu w args) → OpPair fo go w 0
  | ctz {fo go : Op} {w : Width} :
      (∀ ty ai aux args, evalPure fo ty ai aux args = Sem.Int.ctz w false ty.width? args) →
      (∀ ty ai aux args, evalPure go ty ai aux args = Sem.Int.ctz w true ty.width? args) →
      OpPair fo go w 1
  | mul {fo go : Op} {w : Width} :
      (∀ ty ai aux args, evalPure fo ty ai aux args = Sem.Int.mul w args) →
      (∀ ty ai aux args, evalPure go ty ai aux args = Sem.Int.and w args) → OpPair fo go w 2

theorem opTab_mem {fo go : Op} {w : Width} {k : Nat} (h : opTab.lookup (fo, go) = some (w, k)) :
    OpPair fo go w k := by
  have hm := mem_of_lookup h
  simp only [opTab, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨⟨rfl, rfl⟩, rfl, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl, rfl⟩
  · exact .div (fl := false) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
  all_goals first
    | exact .div (fl := true) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    | exact .mod (fl := false) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    | exact .mod (fl := true) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    | exact .ctz (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    | exact .mul (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)

end GoFV.Proof.ProveCheck

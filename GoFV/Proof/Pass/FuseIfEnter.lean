import GoFV.Proof.Pass.DeadEnter
import GoFV.Proof.Mixed
import GoFV.Proof.Speculate
import GoFV.Proof.Enter
import GoFV.Proof.Agree

variable [GoFV.SSA.Sem.Addrs]

/-!
# Entering a block of two functions that differ on a set of values

`f` and `g` differ on the values `X` (free values): a block `gb` of `g` against the block `fb`
of `f` (`BRel`) lists `fb`'s values and possibly more values of `X`; a value outside `X` is
unchanged in what the semantics reads (a `Phi` reading along the target's edge index what the
source's reads along its own), and reads nothing of `X`; a value of `X` in `gb` is
speculation-safe; a value of `X` in `fb` cannot panic. From frames agreeing outside `X`
(`Agr`), where the free values' arguments outside `gb` have registers (`FreeDef`):

* `enter_ok`: when the source enters `fb`, the target enters `gb`, the frames again agreeing
  outside `X` (reference evaluation with free values, `evalAll_mix`);
* `enter_panic`: when the source panics in `fb`, the target panics alike: the values outside
  `X` are a closed part of both blocks' nodes with the same records (`restrict_eq`), so the
  target lists before the panicking root only such values the source evaluated before it
  (`sched_transfer_sub`) and free values;
* `enter_spec`: the target alone enters a block of speculation-safe values (a speculated arm).
-/

namespace GoFV.Proof.FuseIf

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof GoFV.Proof.Order
open GoFV.Proof.CopyElim (stepV_of topoRem_append_left topoRem_at topoRem_before
  nodeOf_schedNodes)

/-- Frames agreeing outside `X`. -/
def Agr (X : ID → Bool) (frS frT : Frame) : Prop :=
  frT = { frS with regs := frT.regs } ∧ frT.regs.size = frS.regs.size ∧
    ∀ a, X a = false → frT.regs[a]? = frS.regs[a]?

/-- Block `gb` of `g` against block `fb` of `f`, entered along `iT` and `iS` (module doc). -/
structure BRel (f g : Func) (X : ID → Bool) (fb gb : Block) (iS iT : Nat) : Prop where
  id : gb.id = fb.id
  vals : ∃ ex : Array ID, gb.values = fb.values ++ ex ∧ ∀ x ∈ ex, X x = true
  same : ∀ x ∈ fb.values, X x = false → ∃ fv gv, f.value? x = some fv ∧ g.value? x = some gv ∧
    gv.id = fv.id ∧ gv.op = fv.op ∧ gv.aux = fv.aux ∧ gv.auxInt = fv.auxInt ∧
    gv.type = fv.type ∧ (∀ a ∈ gv.args, X a = false) ∧ (fv.op ≠ .Phi → gv.args = fv.args) ∧
    (fv.op = .Phi → ∀ a, fv.args[iS]? = some a → gv.args[iT]? = some a)
  free : ∀ x ∈ gb.values, X x = true → ∃ gv, g.value? x = some gv ∧ specSafeOp gv.op = true
  srcX : ∀ x ∈ fb.values, X x = true → ∀ fv, f.value? x = some fv → ¬ Panicking fv.op
  sched : ∃ o, schedule g gb = some o

/-- The arguments outside `gb` of `gb`'s free values have registers in `fr`. -/
def FreeDef (g : Func) (X : ID → Bool) (gb : Block) (fr : Frame) : Prop :=
  ∀ x ∈ gb.values, X x = true → ∀ gv, g.value? x = some gv → ∀ a ∈ gv.args, a ∉ gb.values →
    ∃ z, fr.regs[a]? = some (some z)

/-- The static setting: both functions well formed, the same parameters and value table size. -/
structure Two (f g : Func) : Prop where
  wf : ∃ ce, WF ce f
  wg : ∃ ce, WF ce g
  own : g.ownAux = f.ownAux
  vsize : g.valueTab.size = f.valueTab.size

theorem specSafe_not_phi {op : Op} (h : specSafeOp op = true) : op ≠ .Phi := by
  intro hp; subst hp; simp [specSafeOp] at h

theorem specSafe_not_panicking {op : Op} (h : specSafeOp op = true) : ¬ Panicking op := by
  intro hp
  have hr := prio_panicking hp
  unfold specSafeOp at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  exact hr (by unfold prio; simp [h.1.1.1, show op.nilCheck = false from by
    cases hn : op.nilCheck
    · rfl
    · exfalso; unfold isRoot at h; simp [hn] at h])

variable {f g : Func} {X : ID → Bool}

theorem with_regs {a b : Frame} (h : a = { b with regs := a.regs }) (R : Array (Option Val)) :
    ({ a with regs := R } : Frame) = { b with regs := R } := by
  rw [h]

/-- An unchanged non-`Phi`, in a frame agreeing with `G` on its arguments, evaluates in the
target as the source value does in `G`. -/
theorem Two.evalSame (T : Two f g) {tabs : Tables} {env : Env} {x : ID} {fv gv : Value}
    (hfv : f.value? x = some fv) (hgv : g.value? x = some gv) (hfid : fv.id = x)
    (hid : gv.id = fv.id) (hop : gv.op = fv.op) (haux : gv.aux = fv.aux)
    (hai : gv.auxInt = fv.auxInt) (hty : gv.type = fv.type) (hargs : gv.args = fv.args)
    {G g' : Frame} {r : Res Val} (hev : evalValue env (Ctx.make tabs f) G fv = r)
    (hr : ∀ msg, r ≠ .stuck msg) (hg' : g' = { G with regs := g'.regs })
    (hag : ∀ a ∈ gv.args, g'.regs[a]? = G.regs[a]?) :
    stepV env (Ctx.make tabs g) g' x = r := by
  rw [stepV_of (ctx := Ctx.make tabs g) hgv, ← hev]
  have hdef := evalValue_args_def (fun msg he => hr msg (hev ▸ he))
  refine evalValue_eq_of_args hop haux hai hid (by rw [hargs]) (fun k a hk => ?_) hg'
    (by rw [hfid, tys_of_value hgv, tys_of_value hfv, hty]) rfl (Dead.params_eq T.own) rfl
  obtain ⟨y, hy⟩ := hdef a (Array.mem_of_getElem? hk)
  refine ⟨a, y, by rw [hargs]; exact hk, hy, ?_⟩
  rw [hag a (by rw [hargs]; exact Array.mem_of_getElem? hk), hy]

/-- The static facts of a related pair of listed blocks. -/
structure Blocks (f g : Func) (bid : ID) (fb gb : Block) : Prop where
  bf : bid ∈ f.blocks
  fb : f.block? bid = some fb
  bg : bid ∈ g.blocks
  gb : g.block? bid = some gb

section
variable (T : Two f g) {bid : ID} {fb gb : Block} (B : Blocks f g bid fb gb) {iS iT : Nat}
  (hR : BRel f g X fb gb iS iT)
include hR

theorem BRel.sub {x : ID} (hx : x ∈ fb.values) : x ∈ gb.values := by
  obtain ⟨ex, hex, -⟩ := hR.vals
  rw [hex]; exact Array.mem_append_left _ hx

theorem BRel.mem_f {x : ID} (hx : x ∈ gb.values) (hX : X x = false) : x ∈ fb.values := by
  obtain ⟨ex, hex, hexX⟩ := hR.vals
  rw [hex] at hx
  rcases Array.mem_append.1 hx with h | h
  · exact h
  · rw [hexX x h] at hX; cases hX

/-- A `Phi` of `gb` is outside `X`, a `Phi` of `fb` reading along `iS` what it reads along
`iT`. -/
theorem BRel.phi {x : ID} (hx : x ∈ gb.values) {gv : Value} (hgv : g.value? x = some gv)
    (hph : gv.op = .Phi) : X x = false ∧ x ∈ fb.values ∧ ∃ fv, f.value? x = some fv ∧
      fv.op = .Phi ∧ (∀ a, fv.args[iS]? = some a → gv.args[iT]? = some a) ∧ gv.type = fv.type ∧
      ∀ a ∈ gv.args, X a = false := by
  have hX : X x = false := by
    cases hXx : X x
    · rfl
    · obtain ⟨gv', hgv', hs⟩ := hR.free x hx hXx
      rw [hgv] at hgv'; cases hgv'
      exact absurd hph (specSafe_not_phi hs)
  have hxf := hR.mem_f hx hX
  obtain ⟨fv, gv', hfv, hgv', -, hop, -, -, hty, hargs, -, hphi⟩ := hR.same x hxf hX
  rw [hgv] at hgv'; cases hgv'
  exact ⟨hX, hxf, fv, hfv, hop ▸ hph, hphi (hop ▸ hph), hty, hargs⟩

include T B

/-- **The target's `Phi`s**: they succeed, and the frames after them agree outside `X`. -/
theorem targetPhis {tabs : Tables} {frS frT : Frame} (hA : Agr X frS frT)
    (hsz : frS.regs.size = f.valueTab.size) {psS : List (ID × Val)}
    (hpsS : fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) frS iS) = .ok psS) :
    ∃ psT, gb.values.toList.filterMapM (phiStep (Ctx.make tabs g) frT iT) = .ok psT ∧
      (setPhis psT frT.regs).size = (setPhis psS frS.regs).size ∧
      (∀ a, X a = false → (setPhis psT frT.regs)[a]? = (setPhis psS frS.regs)[a]?) ∧
      (∀ a ∈ gb.values, ∀ gv, g.value? a = some gv → gv.op = .Phi →
        ∃ z, (setPhis psT frT.regs)[a]? = some (some z)) := by
  obtain ⟨ce, hwf⟩ := T.wf
  obtain ⟨ce', hwg⟩ := T.wg
  have hndF := hwf.valuesNodup _ _ ⟨B.bf, B.fb⟩
  have hndG := hwg.valuesNodup _ _ ⟨B.bg, B.gb⟩
  have hownG := valuesOwn hwg B.bg B.gb
  obtain ⟨hszS, -, hkeepS, hphiS⟩ := phis_spec hndF hpsS
  -- a `Phi` of `gb` reads the source's register
  have hphiEq : ∀ z ∈ gb.values, ∀ gv, g.value? z = some gv → gv.op = .Phi →
      ∃ fv a y, f.value? z = some fv ∧ fv.op = .Phi ∧ fv.args[iS]? = some a ∧
        frS.regs[a]? = some (some y) ∧ gv.args[iT]? = some a ∧ frT.regs[a]? = some (some y) ∧
        z ∈ fb.values ∧ gv.type = fv.type := by
    intro z hz gv hgv hph
    obtain ⟨-, hzf, fv, hfv, hfph, hidx, hty, hargs⟩ := hR.phi hz hgv hph
    obtain ⟨a, y, ha, hy, -⟩ := hphiS z hzf fv hfv hfph (by rw [hsz]; exact lt_of_value? hfv)
    have hidx' := hidx a ha
    refine ⟨fv, a, y, hfv, hfph, ha, hy, hidx', ?_, hzf, hty⟩
    rw [hA.2.2 a (hargs a (Array.mem_of_getElem? hidx')), hy]
  obtain ⟨psT, hpsT⟩ : ∃ psT, gb.values.toList.filterMapM (phiStep (Ctx.make tabs g) frT iT) =
      .ok psT := by
    refine filterMapM_phi_ok fun z hz => ?_
    rw [Array.mem_toList_iff] at hz
    obtain ⟨gv, hgv, -⟩ := hownG z hz
    by_cases hgph : gv.op = .Phi
    · obtain ⟨fv, a, y, -, -, -, -, hga, hy, -⟩ := hphiEq z hz gv hgv hgph
      refine ⟨some (z, y.retype ((Ctx.make tabs g).tys[z]?.getD .other)), ?_⟩
      unfold phiStep
      simp only [show (Ctx.make tabs g).f = g from rfl, hgv, hgph, beq_self_eq_true, ite_true,
        hga, hy, Option.join]
      rfl
    · refine ⟨none, ?_⟩
      unfold phiStep
      simp only [show (Ctx.make tabs g).f = g from rfl, hgv,
        show (gv.op == .Phi) = false by simpa using hgph]
      rfl
  obtain ⟨hszT, -, hkeepT, hphiT⟩ := phis_spec hndG hpsT
  have hltT : ∀ {z : ID} {v : Value}, f.value? z = some v → z < frT.regs.size := fun hv => by
    rw [hA.2.1, hsz]; exact lt_of_value? hv
  refine ⟨psT, hpsT, by rw [hszT, hszS, hA.2.1], fun a haX => ?_, fun a ha gv hgv hph => ?_⟩
  · by_cases ha : a ∈ gb.values
    · obtain ⟨gv, hgv, -⟩ := hownG a ha
      by_cases hgph : gv.op = .Phi
      · obtain ⟨fv, a', y, hfv, hfph, ha', hy, hga', hyT, haf, hty⟩ := hphiEq a ha gv hgv hgph
        obtain ⟨b1, y1, hb1, hy1, hT⟩ := hphiT a ha gv hgv hgph (hltT hfv)
        rw [hga'] at hb1; cases hb1
        rw [hyT] at hy1; cases hy1
        obtain ⟨b2, y2, hb2, hy2, hS⟩ :=
          hphiS a haf fv hfv hfph (by rw [hsz]; exact lt_of_value? hfv)
        rw [ha'] at hb2; cases hb2
        rw [hy] at hy2; cases hy2
        rw [hT, hS, tys_of_value hgv, tys_of_value hfv, hty]
      · have haf := hR.mem_f ha haX
        obtain ⟨fv, gv', hfv, hgv', -, hop, -⟩ := hR.same a haf haX
        rw [hgv] at hgv'; cases hgv'
        rw [hkeepT a (.inr ⟨gv, hgv, hgph⟩),
          hkeepS a (.inr ⟨fv, hfv, fun h => hgph (hop.trans h)⟩), hA.2.2 a haX]
    · have haf : a ∉ fb.values := fun h => ha (hR.sub h)
      rw [hkeepT a (.inl ha), hkeepS a (.inl haf), hA.2.2 a haX]
  · obtain ⟨fv, a', y, hfv, -, -, -, hga', hyT, -⟩ := hphiEq a ha gv hgv hph
    obtain ⟨b1, y1, hb1, hy1, hT⟩ := hphiT a ha gv hgv hph (hltT hfv)
    exact ⟨_, hT⟩

end

/-! ## The nodes outside `X` -/

theorem nodeOf_filter {q : ID → Bool} : ∀ {l : List SNode} {x : ID},
    (∀ n ∈ l, n.id = x → q n.id = true) → nodeOf (l.filter fun n => q n.id) x = nodeOf l x
  | [], _, _ => rfl
  | n :: l, x, h => by
    unfold nodeOf
    by_cases hp : q n.id = true
    · rw [List.filter_cons_of_pos (p := fun n : SNode => q n.id) hp, List.find?_cons,
        List.find?_cons]
      split
      · rfl
      · exact nodeOf_filter fun m hm => h m (List.mem_cons_of_mem _ hm)
    · rw [List.filter_cons_of_neg (p := fun n : SNode => q n.id) hp, List.find?_cons]
      have hne : (n.id == x) = false := by
        cases he : (n.id == x)
        · rfl
        · exact absurd (h n List.mem_cons_self (beq_iff_eq.1 he)) hp
      rw [hne]
      exact nodeOf_filter fun m hm => h m (List.mem_cons_of_mem _ hm)

/-- The nodes with `q`, closed under arguments, are a closed part of the nodes. -/
theorem subNodes_filter {vs : List SNode} (hd : (vs.map (·.id)).Nodup) (q : ID → Bool)
    (hcl : ∀ n ∈ vs, q n.id = true → ∀ a ∈ n.args, ∀ m ∈ vs, m.id = a → q a = true) :
    Dead.SubNodes vs (vs.filter fun n => q n.id) := by
  have hmem : ∀ {x}, NodeIn (vs.filter fun n => q n.id) x → ∃ n ∈ vs, n.id = x ∧ q x = true := by
    rintro x ⟨n, hn, rfl⟩
    obtain ⟨hn, hq⟩ := List.mem_filter.1 hn
    exact ⟨n, hn, rfl, hq⟩
  refine ⟨(List.filter_sublist.map _).nodup hd, fun x hx => ?_, fun x a hx ha hNa => ?_⟩
  · obtain ⟨n, hn, rfl, hq⟩ := hmem hx
    exact nodeOf_filter fun m _ he => by rw [he]; exact hq
  · obtain ⟨n, hn, rfl, hq⟩ := hmem hx
    rw [argsOf_of_mem hd hn] at ha
    obtain ⟨m, hm, rfl⟩ := hNa
    exact ⟨m, List.mem_filter.2 ⟨hm, hcl n hn hq m.id (Array.mem_toList_iff.1 ha) m hm rfl⟩, rfl⟩

/-- A value of `X` is no node outside `X`. -/
theorem node_filter_X {o : Option Value} {x : ID} {v : Value} (hv : o = some v) (hid : v.id = x)
    (hX : X x = true) :
    (match o with
      | some (v : Value) => if v.op == Op.Phi then none else some (⟨v.id, v.args, prio v.op⟩ : SNode)
      | none => none).filter (fun (n : SNode) => !X n.id) = none := by
  subst hv
  dsimp only
  split <;> simp [Option.filter, hid, hX]

section
variable (T : Two f g) {bid : ID} {fb gb : Block} (B : Blocks f g bid fb gb) {iS iT : Nat}
  (hR : BRel f g X fb gb iS iT)
include T B hR

/-- **The nodes outside `X`** are the same records in both blocks. -/
theorem restrict_eq : ((schedNodes f fb).toList.filter fun n => !X n.id) =
    ((schedNodes g gb).toList.filter fun n => !X n.id) := by
  obtain ⟨ce, hwf⟩ := T.wf
  obtain ⟨ce', hwg⟩ := T.wg
  have hownF := valuesOwn hwf B.bf B.fb
  have hownG := valuesOwn hwg B.bg B.gb
  obtain ⟨ex, hex, hexX⟩ := hR.vals
  unfold schedNodes
  rw [Array.toList_filterMap, Array.toList_filterMap, List.filter_filterMap,
    List.filter_filterMap, hex, Array.toList_append, List.filterMap_append]
  rw [(List.filterMap_eq_nil_iff (l := ex.toList)).2 ?nil, List.append_nil]
  case nil =>
    intro x hx
    have hxg : x ∈ gb.values := by
      rw [hex]; exact Array.mem_append_right _ (Array.mem_toList_iff.1 hx)
    obtain ⟨v, hv, hvid⟩ := hownG x hxg
    exact node_filter_X hv hvid (hexX x (Array.mem_toList_iff.1 hx))
  refine list_filterMap_congr _ fun x hx => ?_
  have hx' := Array.mem_toList_iff.1 hx
  cases hX : X x
  · obtain ⟨fv, gv, hfv, hgv, hid, hop, -, -, -, -, hargs, -⟩ := hR.same x hx' hX
    rw [hfv, hgv]
    dsimp only
    rw [hop, hid]
    by_cases hph : fv.op = .Phi
    · simp [hph]
    · simp [hph, hargs hph]
  · obtain ⟨v, hv, hvid⟩ := hownF x hx'
    obtain ⟨w, hw, hwid⟩ := hownG x (hR.sub hx')
    exact (node_filter_X hv hvid hX).trans (node_filter_X hw hwid hX).symm

/-- **The panic transfer**: the target lists before the source's panicking root `r` only values
outside `X` that the source evaluated before `r`, and values of `X`. -/
theorem transfer {oS oT : Array ID} (hoS : schedule f fb = some oS)
    (hoT : schedule g gb = some oT) {r : ID} {k k' : Nat} (hk : oS.toList[k]? = some r)
    (hk' : oT.toList[k']? = some r) (hrX : X r = false) {fv : Value}
    (hfv : f.value? r = some fv) (hph : fv.op ≠ .Phi) (hnp : prio fv.op ≠ 0) :
    ∀ j y, j < k' → oT.toList[j]? = some y → X y = false → ∃ i < k, oS.toList[i]? = some y := by
  obtain ⟨ce, hwf⟩ := T.wf
  obtain ⟨ce', hwg⟩ := T.wg
  have hownF := valuesOwn hwf B.bf B.fb
  have hownG := valuesOwn hwg B.bg B.gb
  have hndF := hwf.valuesNodup _ _ ⟨B.bf, B.fb⟩
  have hndG := hwg.valuesNodup _ _ ⟨B.bg, B.gb⟩
  have hdF := schedNodes_ids hownF hndF
  have hdG := schedNodes_ids hownG hndG
  obtain ⟨-, -, omemS⟩ := schedule_topo hownF hndF hoS
  obtain ⟨ondT, -, omemT⟩ := schedule_topo hownG hndG hoT
  have subF := subNodes_filter hdF (fun x => !X x) (by
    intro n hn hq a ha m _ _
    obtain ⟨x, hx, v, hv, hvp, rfl⟩ := mem_schedNodes.1 hn
    obtain ⟨v', hv', hvid⟩ := hownF x hx
    rw [hv] at hv'; cases hv'
    rw [hvid] at hq
    obtain ⟨fv', gv, hfv', -, -, -, -, -, -, hgX, hargs, -⟩ := hR.same x hx (by simpa using hq)
    rw [hv] at hfv'; cases hfv'
    simpa using hgX a (by rw [hargs hvp]; exact ha))
  have subG := subNodes_filter hdG (fun x => !X x) (by
    intro n hn hq a ha m _ _
    obtain ⟨x, hx, v, hv, -, rfl⟩ := mem_schedNodes.1 hn
    obtain ⟨v', hv', hvid⟩ := hownG x hx
    rw [hv] at hv'; cases hv'
    rw [hvid] at hq
    have hqx : X x = false := by simpa using hq
    obtain ⟨fv', gv, -, hgv, -, -, -, -, -, hgX, -, -⟩ := hR.same x (hR.mem_f hx hqx) hqx
    rw [hv] at hgv; cases hgv
    simpa using hgX a ha)
  have hTX := Dead.schedSpec_restrict (schedule_spec hoT) subG
  rw [← restrict_eq T B hR] at hTX
  -- the nodes outside `X`
  have hnode : ∀ y, y ∈ fb.values → X y = false → ∀ v, f.value? y = some v → v.op ≠ .Phi →
      ((schedNodes f fb).toList.filter fun n => !X n.id).any (·.id == y) = true := by
    intro y hy hyX v hv hvp
    obtain ⟨v', hv', hvid⟩ := hownF y hy
    rw [hv] at hv'; cases hv'
    refine nodeIn_any.2 ⟨⟨v.id, v.args, prio v.op⟩, List.mem_filter.2 ⟨mem_schedNodes.2
      ⟨y, hy, v, hv, hvp, rfl⟩, by simp [hvid, hyX]⟩, hvid⟩
  have hrS : r ∈ oS.toList := List.mem_of_getElem? hk
  have hrf := ((omemS r).1 hrS).1
  have hrp := hnode r hrf hrX fv hfv hph
  let P : ID → Bool := fun x =>
    ((schedNodes f fb).toList.filter fun (n : SNode) => !X n.id).any (·.id == x)
  obtain ⟨k'', hk''⟩ := List.getElem?_of_mem ((List.mem_filter (as := oT.toList) (p := P)).2
    ⟨List.mem_of_getElem? hk', hrp⟩)
  have hrnp : npIn ((schedNodes f fb).toList.filter fun n => !X n.id) r = true := by
    unfold npIn
    rw [subF.same r (nodeIn_any.1 hrp), nodeOf_schedNodes hownF hndF hrf hfv hph]
    simpa using hnp
  have htr := Dead.sched_transfer_sub (schedule_spec hoS) hTX subF hk hk'' hrnp
  intro j y hj hy hyX
  have hyT : y ∈ oT.toList := List.mem_of_getElem? hy
  obtain ⟨hyg, gv, hgv, hgp⟩ := (omemT y).1 hyT
  have hyf := hR.mem_f hyg hyX
  obtain ⟨fv', gv', hfv', hgv', -, hop, -⟩ := hR.same y hyf hyX
  rw [hgv] at hgv'; cases hgv'
  have hyp := hnode y hyf hyX fv' hfv' (fun h => hgp (hop.trans h))
  have hbef := (before_filter P hyp hrp oT.toList).2 (before_of_idx hj hy hk')
  obtain ⟨i1, i2, hi12, hi1, hi2⟩ := hbef
  have := Order.idx_unique (ondT.filter _) hi2 hk''
  subst this
  exact htr i1 y hi12 hi1

end

/-! ## Entering a related block -/

section
variable (T : Two f g) {bid : ID} {fb gb : Block} (B : Blocks f g bid fb gb) {iS iT : Nat}
  (hR : BRel f g X fb gb iS iT)
include T B hR

/-- **A block the source enters successfully is entered by the target**, to a frame agreeing
with the source's outside `X`. -/
theorem enter_ok {tabs : Tables} {env : Env} {frS frT : Frame} (hA : Agr X frS frT)
    (hsz : frS.regs.size = f.valueTab.size) (hfree : FreeDef g X gb frT) {G : Frame}
    (h : enterBlock env (Ctx.make tabs f) frS fb iS = .ok G) :
    ∃ GT, enterBlock env (Ctx.make tabs g) frT gb iT = .ok GT ∧ Agr X G GT ∧
      G.regs.size = f.valueTab.size := by
  obtain ⟨ce, hwf⟩ := T.wf
  obtain ⟨ce', hwg⟩ := T.wg
  have hownF := valuesOwn hwf B.bf B.fb
  have hownG := valuesOwn hwg B.bg B.gb
  have hndF := hwf.valuesNodup _ _ ⟨B.bf, B.fb⟩
  have hndG := hwg.valuesNodup _ _ ⟨B.bg, B.gb⟩
  obtain ⟨b', hb', hfid⟩ := hwf.blockId bid B.bf
  rw [B.fb] at hb'; cases hb'
  obtain ⟨b'', hb'', hgid⟩ := hwg.blockId bid B.bg
  rw [B.gb] at hb''; cases hb''
  rw [enterBlock_eq] at h
  cases hpsS : fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) frS iS) with
  | panic e m => rw [hpsS] at h; cases h
  | stuck msg => rw [hpsS] at h; cases h
  | ok psS =>
  rw [hpsS] at h
  change (Res.ofOption _ ((Ctx.make tabs f).sched[fb.id]?).join).bind _ = _ at h
  rw [hfid, sched_of_block B.fb] at h
  cases hso : schedule f fb with
  | none => rw [hso] at h; cases h
  | some oS =>
  rw [hso] at h
  change evalAll env (Ctx.make tabs f) _ oS.toList = .ok G at h
  obtain ⟨psT, hpsT, hszP, hagP, hdefP⟩ := targetPhis T B hR hA hsz hpsS
  obtain ⟨oT, hoT⟩ := hR.sched
  obtain ⟨ond, otopo, omemS⟩ := schedule_topo hownF hndF hso
  obtain ⟨ondT, otopoT, omemT⟩ := schedule_topo hownG hndG hoT
  obtain ⟨hszS, -, -, -⟩ := phis_spec hndF hpsS
  obtain ⟨-, -, hkeepT, -⟩ := phis_spec hndG hpsT
  obtain ⟨e1, e2, e3, e4⟩ := evalAll_spec ond (by exact otopo) (by simp [hszS, hsz]; rfl) h
  have hnotS : ∀ a, X a = false → a ∉ oT.toList → a ∉ oS.toList := by
    intro a haX ha hm
    obtain ⟨haf, fv, hfv, hfp⟩ := (omemS a).1 hm
    obtain ⟨fv', gv, hfv', hgv, -, hop, -⟩ := hR.same a haf haX
    rw [hfv] at hfv'; cases hfv'
    exact ha ((omemT a).2 ⟨hR.sub haf, gv, hgv, fun h => hfp (hop.symm.trans h)⟩)
  have hout : ∀ a, X a = false → a ∉ oT.toList →
      (setPhis psT frT.regs)[a]? = G.regs[a]? := by
    intro a haX ha
    rw [hagP a haX]
    exact (e3 a (hnotS a haX ha)).symm
  have hmix : MixOK env (Ctx.make tabs g) G (fun a => X a = true) oT.toList := by
    intro x hx
    obtain ⟨hxg, gv, hgv, hgn⟩ := (omemT x).1 hx
    refine ⟨fun hX => ?_, fun hX g' _ hdef => ?_⟩
    · have hXf : X x = false := by simpa using hX
      have hxf := hR.mem_f hxg hXf
      obtain ⟨fv, gv', hfv, hgv', hid, hop, haux, hai, hty, hgX, hargs, -⟩ := hR.same x hxf hXf
      rw [hgv] at hgv'; cases hgv'
      have hfn : fv.op ≠ .Phi := fun h => hgn (hop.trans h)
      obtain ⟨v, y, hv, hy, hev⟩ := e4 x ((omemS x).2 ⟨hxf, fv, hfv, hfn⟩)
      change f.value? x = some v at hv
      rw [hfv] at hv; cases hv
      obtain ⟨v', hv', hvid⟩ := hownF x hxf
      rw [hfv] at hv'; cases hv'
      exact ⟨y, hy, fun g' hg' hag _ => T.evalSame hfv hgv hvid hid hop haux hai hty (hargs hfn)
        hev (fun _ h => nomatch h) hg' (fun a ha => hag a (by
          rw [show (Ctx.make tabs g).f = g from rfl, argsF_of hgv]
          exact Array.mem_toList_iff.2 ha) (by simp [hgX a ha]))⟩
    · obtain ⟨gv', hgv', hs⟩ := hR.free x hxg hX
      rw [hgv] at hgv'; cases hgv'
      obtain ⟨y, hy⟩ := evalValue_specSafe (env := env) (ctx := Ctx.make tabs g) (fr := g') hs
        (fun a ha => hdef a (by
          rw [show (Ctx.make tabs g).f = g from rfl, argsF_of hgv]
          exact Array.mem_toList_iff.2 ha))
      exact ⟨y, by rw [stepV_of (ctx := Ctx.make tabs g) hgv]; exact hy⟩
  have href : RefOK (argsF (Ctx.make tabs g).f)
      (fun a => a ∉ oT.toList ∧ ∃ z, (setPhis psT frT.regs)[a]? = some (some z)) oT.toList := by
    refine Dead.refOK_of_topo otopoT fun x hx a ha hna => ⟨hna, ?_⟩
    obtain ⟨hxg, gv, hgv, hgn⟩ := (omemT x).1 hx
    rw [show (Ctx.make tabs g).f = g from rfl, argsF_of hgv] at ha
    have ha' := Array.mem_toList_iff.1 ha
    cases hXx : X x
    · have hxf := hR.mem_f hxg hXx
      obtain ⟨fv, gv', hfv, hgv', -, hop, -, -, -, hgX, hargs, -⟩ := hR.same x hxf hXx
      rw [hgv] at hgv'; cases hgv'
      have hfn : fv.op ≠ .Phi := fun h => hgn (hop.trans h)
      obtain ⟨v, y, hv, -, hev⟩ := e4 x ((omemS x).2 ⟨hxf, fv, hfv, hfn⟩)
      change f.value? x = some v at hv
      rw [hfv] at hv; cases hv
      obtain ⟨z, hz⟩ := evalValue_args_def (fun msg he => by rw [hev] at he; cases he) a
        (by rw [← hargs hfn]; exact ha')
      exact ⟨z, by rw [hout a (hgX a ha') hna, hz]⟩
    · by_cases hag : a ∈ gb.values
      · obtain ⟨av, hav, -⟩ := hownG a hag
        have hap : av.op = .Phi := Classical.byContradiction fun hne =>
          hna ((omemT a).2 ⟨hag, av, hav, hne⟩)
        exact hdefP a hag av hav hap
      · obtain ⟨z, hz⟩ := hfree x hxg hXx gv hgv a ha' hag
        exact ⟨z, by rw [hkeepT a (.inl hag), hz]⟩
  have hGs : G.regs.size = (Ctx.make tabs g).f.valueTab.size := by
    rw [e2]; show (setPhis psS frS.regs).size = g.valueTab.size
    rw [setPhis_size, hsz, T.vsize]
  obtain ⟨GT, h1, h2, h3, h4, -, h6⟩ := evalAll_mix hGs hmix href
    (fun a ha hF => hout a (by simpa using hF) ha.1) (fun a ha => ha.2)
    (g := { frT with regs := setPhis psT frT.regs })
    ((with_regs hA.1 _).trans (with_regs e1 _).symm) (by rw [e2]; simpa using hszP)
  refine ⟨GT, ?_, ⟨h2, h3, fun a haX => ?_⟩, by rw [e2]; simpa [hsz] using hszS⟩
  · rw [enterBlock_eq, hpsT]
    change (Res.ofOption _ ((Ctx.make tabs g).sched[gb.id]?).join).bind _ = _
    rw [hgid, sched_of_block B.gb, hoT]
    exact h1
  · by_cases ha : a ∈ oT.toList
    · exact h4 a (.inr ha) (by simp [haX])
    · rw [h6 a ha]; exact hout a haX ha

/-- **A block the source panics in makes the target panic alike.** -/
theorem enter_panic {tabs : Tables} {env : Env} {frS frT : Frame} (hA : Agr X frS frT)
    (hsz : frS.regs.size = f.valueTab.size) (hfree : FreeDef g X gb frT) {e : Panic} {m : Mem}
    (h : enterBlock env (Ctx.make tabs f) frS fb iS = .panic e m) :
    enterBlock env (Ctx.make tabs g) frT gb iT = .panic e m := by
  obtain ⟨ce, hwf⟩ := T.wf
  obtain ⟨ce', hwg⟩ := T.wg
  have hownF := valuesOwn hwf B.bf B.fb
  have hownG := valuesOwn hwg B.bg B.gb
  have hndF := hwf.valuesNodup _ _ ⟨B.bf, B.fb⟩
  have hndG := hwg.valuesNodup _ _ ⟨B.bg, B.gb⟩
  obtain ⟨b', hb', hfid⟩ := hwf.blockId bid B.bf
  rw [B.fb] at hb'; cases hb'
  obtain ⟨b'', hb'', hgid⟩ := hwg.blockId bid B.bg
  rw [B.gb] at hb''; cases hb''
  obtain ⟨psS, oS, hpsS, hso, hev⟩ := enterBlock_panic h
  rw [hfid, sched_of_block B.fb] at hso
  obtain ⟨pre, r, post, Gpre, hsplit, hpre, hrp⟩ := evalAll_panic_split hev
  obtain ⟨psT, hpsT, hszP, hagP, hdefP⟩ := targetPhis T B hR hA hsz hpsS
  obtain ⟨oT, hoT⟩ := hR.sched
  obtain ⟨ond, otopo, omemS⟩ := schedule_topo hownF hndF hso
  obtain ⟨ondT, otopoT, omemT⟩ := schedule_topo hownG hndG hoT
  obtain ⟨hszS, -, -, -⟩ := phis_spec hndF hpsS
  obtain ⟨-, -, hkeepT, -⟩ := phis_spec hndG hpsT
  have hsplit' := hsplit
  rw [hsplit] at ond otopo
  obtain ⟨e1, e2, e3, e4⟩ := evalAll_spec (List.nodup_append.1 ond).1
    (by exact topoRem_append_left otopo) (by simp [hszS, hsz]; rfl) hpre
  -- the panicking root, outside `X`
  have hrS : r ∈ oS.toList := by rw [hsplit']; simp
  obtain ⟨hrf, fvr, hfvr, hrnph⟩ := (omemS r).1 hrS
  rw [stepV_of hfvr] at hrp
  have hrop := evalValue_panic_op hrp
  have hrX : X r = false := by
    cases hX : X r
    · rfl
    · exact absurd hrop (hR.srcX r hrf hX fvr hfvr)
  obtain ⟨fvr', gvr, hfvr', hgvr, hidr, hopr, hauxr, hair, htyr, hgXr, hargsr, -⟩ :=
    hR.same r hrf hrX
  rw [hfvr] at hfvr'; cases hfvr'
  obtain ⟨vr, hvr, hvrid⟩ := hownF r hrf
  rw [hfvr] at hvr; cases hvr
  have hgrn : gvr.op ≠ .Phi := fun h => hrnph (hopr.symm.trans h)
  have hrT : r ∈ oT.toList := (omemT r).2 ⟨hR.sub hrf, gvr, hgvr, hgrn⟩
  obtain ⟨pre', post', hsplitT⟩ := List.append_of_mem hrT
  have hk : oS.toList[pre.length]? = some r := by rw [hsplit']; simp
  have hk' : oT.toList[pre'.length]? = some r := by rw [hsplitT]; simp
  have htr := transfer T B hR hso hoT hk hk' hrX hfvr hrnph (prio_panicking hrop)
  have hpreS : ∀ x ∈ pre', X x = false → x ∈ pre := by
    intro x hx hxX
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
    have hjl := lt_length_of_getElem? hj
    have hjT : oT.toList[j]? = some x := by rw [hsplitT, List.getElem?_append_left hjl]; exact hj
    obtain ⟨i, hi, hix⟩ := htr j x hjl hjT hxX
    rw [hsplit', List.getElem?_append_left hi] at hix
    exact List.mem_of_getElem? hix
  have hnotS : ∀ a, X a = false → a ∉ oT.toList → a ∉ oS.toList := by
    intro a haX ha hm
    obtain ⟨haf, fv, hfv, hfp⟩ := (omemS a).1 hm
    obtain ⟨fv', gv, hfv', hgv, -, hop, -⟩ := hR.same a haf haX
    rw [hfv] at hfv'; cases hfv'
    exact ha ((omemT a).2 ⟨hR.sub haf, gv, hgv, fun h => hfp (hop.symm.trans h)⟩)
  have hout : ∀ a, X a = false → a ∉ oT.toList →
      (setPhis psT frT.regs)[a]? = Gpre.regs[a]? := by
    intro a haX ha
    rw [hagP a haX]
    exact (e3 a fun hm => hnotS a haX ha (by rw [hsplit']; exact List.mem_append_left _ hm)).symm
  have htopoT : TopoRem (argsF (Ctx.make tabs g).f) (pre' ++ r :: post') := by
    rw [← hsplitT]; exact otopoT
  have hargPre : ∀ x a, (x ∈ pre' ∨ x = r) → a ∈ argsF g x → a ∈ oT.toList → a ∈ pre' := by
    intro x a hx ha haT
    rw [hsplitT] at haT
    rcases hx with hx | rfl
    · obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
      have hjl := lt_length_of_getElem? hj
      obtain ⟨i, hi, hia⟩ := topoRem_before htopoT
        (by rw [List.getElem?_append_left hjl]; exact hj) ha haT
      rw [List.getElem?_append_left (by omega)] at hia
      exact List.mem_of_getElem? hia
    · rcases List.mem_append.1 haT with h' | h'
      · exact h'
      · exact absurd h' (topoRem_at htopoT a ha)
  have hmix : MixOK env (Ctx.make tabs g) Gpre (fun a => X a = true) pre' := by
    intro x hx
    have hxT : x ∈ oT.toList := by rw [hsplitT]; exact List.mem_append_left _ hx
    obtain ⟨hxg, gv, hgv, hgn⟩ := (omemT x).1 hxT
    refine ⟨fun hX => ?_, fun hX g' _ hdef => ?_⟩
    · have hXf : X x = false := by simpa using hX
      have hxf := hR.mem_f hxg hXf
      obtain ⟨fv, gv', hfv, hgv', hid, hop, haux, hai, hty, hgX, hargs, -⟩ := hR.same x hxf hXf
      rw [hgv] at hgv'; cases hgv'
      have hfn : fv.op ≠ .Phi := fun h => hgn (hop.trans h)
      obtain ⟨v, y, hv, hy, hevx⟩ := e4 x (hpreS x hx hXf)
      change f.value? x = some v at hv
      rw [hfv] at hv; cases hv
      obtain ⟨v', hv', hvid⟩ := hownF x hxf
      rw [hfv] at hv'; cases hv'
      exact ⟨y, hy, fun g' hg' hag _ => T.evalSame hfv hgv hvid hid hop haux hai hty (hargs hfn)
        hevx (fun _ h => nomatch h) hg' (fun a ha => hag a (by
          rw [show (Ctx.make tabs g).f = g from rfl, argsF_of hgv]
          exact Array.mem_toList_iff.2 ha) (by simp [hgX a ha]))⟩
    · obtain ⟨gv', hgv', hs⟩ := hR.free x hxg hX
      rw [hgv] at hgv'; cases hgv'
      obtain ⟨y, hy⟩ := evalValue_specSafe (env := env) (ctx := Ctx.make tabs g) (fr := g') hs
        (fun a ha => hdef a (by
          rw [show (Ctx.make tabs g).f = g from rfl, argsF_of hgv]
          exact Array.mem_toList_iff.2 ha))
      exact ⟨y, by rw [stepV_of (ctx := Ctx.make tabs g) hgv]; exact hy⟩
  -- an argument outside the target's schedule has a register after the `Phi`s
  have hdefOut : ∀ x gv, g.value? x = some gv → x ∈ gb.values → ∀ a ∈ gv.args,
      a ∉ oT.toList → (X x = false → ∃ z, Gpre.regs[a]? = some (some z)) →
      ∃ z, (setPhis psT frT.regs)[a]? = some (some z) := by
    intro x gv hgv hxg a ha hna hsrc
    cases hXx : X x
    · have hxf := hR.mem_f hxg hXx
      obtain ⟨fv, gv', hfv, hgv', -, -, -, -, -, hgX, -, -⟩ := hR.same x hxf hXx
      rw [hgv] at hgv'; cases hgv'
      obtain ⟨z, hz⟩ := hsrc hXx
      exact ⟨z, by rw [hout a (hgX a ha) hna, hz]⟩
    · by_cases hag : a ∈ gb.values
      · obtain ⟨av, hav, -⟩ := hownG a hag
        have hap : av.op = .Phi := Classical.byContradiction fun hne =>
          hna ((omemT a).2 ⟨hag, av, hav, hne⟩)
        exact hdefP a hag av hav hap
      · obtain ⟨z, hz⟩ := hfree x hxg hXx gv hgv a ha hag
        exact ⟨z, by rw [hkeepT a (.inl hag), hz]⟩
  have href : RefOK (argsF (Ctx.make tabs g).f)
      (fun a => a ∉ oT.toList ∧ ∃ z, (setPhis psT frT.regs)[a]? = some (some z)) pre' := by
    refine Dead.refOK_of_topo (topoRem_append_left htopoT) fun x hx a ha hna => ?_
    have haT : a ∉ oT.toList := fun h => hna (hargPre x a (.inl hx) ha h)
    have hxT : x ∈ oT.toList := by rw [hsplitT]; exact List.mem_append_left _ hx
    obtain ⟨hxg, gv, hgv, hgn⟩ := (omemT x).1 hxT
    rw [show (Ctx.make tabs g).f = g from rfl, argsF_of hgv] at ha
    refine ⟨haT, hdefOut x gv hgv hxg a (Array.mem_toList_iff.1 ha) haT fun hXx => ?_⟩
    have hxf := hR.mem_f hxg hXx
    obtain ⟨fv, gv', hfv, hgv', -, hop, -, -, -, -, hargs, -⟩ := hR.same x hxf hXx
    rw [hgv] at hgv'; cases hgv'
    obtain ⟨v, y, hv, -, hevx⟩ := e4 x (hpreS x hx hXx)
    change f.value? x = some v at hv
    rw [hfv] at hv; cases hv
    exact evalValue_args_def (fun msg he => by rw [hevx] at he; cases he) a
      (by rw [← hargs (fun h => hgn (hop.trans h))]; exact Array.mem_toList_iff.1 ha)
  have hGs : Gpre.regs.size = (Ctx.make tabs g).f.valueTab.size := by
    rw [e2]; show (setPhis psS frS.regs).size = g.valueTab.size
    rw [setPhis_size, hsz, T.vsize]
  have hpanT := evalAll_mix_panic hGs (post := post') hmix href
    (fun a ha hF => hout a (by simpa using hF) ha.1) (fun a ha => ha.2)
    (g := { frT with regs := setPhis psT frT.regs })
    ((with_regs hA.1 _).trans (with_regs e1 _).symm) (by rw [e2]; simpa using hszP)
    (fun a ha => by
      by_cases haT : a ∈ oT.toList
      · exact .inr (hargPre r a (.inr rfl) ha haT)
      · rw [show (Ctx.make tabs g).f = g from rfl, argsF_of hgvr] at ha
        have ha' := Array.mem_toList_iff.1 ha
        refine .inl ⟨haT, hdefOut r gvr hgvr (hR.sub hrf) a ha' haT fun _ => ?_⟩
        exact evalValue_args_def (fun msg he => by rw [hrp] at he; cases he) a
          (by rw [← hargsr hrnph]; exact ha'))
    (fun g' hg' hag _ => T.evalSame hfvr hgvr hvrid hidr hopr hauxr hair htyr (hargsr hrnph) hrp
      (fun _ h => nomatch h) hg' (fun a ha => hag a (by
        rw [show (Ctx.make tabs g).f = g from rfl, argsF_of hgvr]
        exact Array.mem_toList_iff.2 ha) (by simp [hgXr a ha])))
  rw [enterBlock_eq, hpsT]
  change (Res.ofOption _ ((Ctx.make tabs g).sched[gb.id]?).join).bind _ = _
  rw [hgid, sched_of_block B.gb, hoT]
  change evalAll env (Ctx.make tabs g) _ oT.toList = _
  rw [hsplitT, hpanT]

end

/-- **The target alone enters a block of speculation-safe values** (a speculated arm): it
succeeds, changing only the block's values. -/
theorem enter_spec {ce : CheckEnv} (hwg : WF ce g) {tabs : Tables} {env : Env} {bid : ID}
    {gb : Block} (hbg : bid ∈ g.blocks) (hgb : g.block? bid = some gb)
    (hss : ∀ x ∈ gb.values, ∃ gv, g.value? x = some gv ∧ specSafeOp gv.op = true)
    (hsched : ∃ o, schedule g gb = some o) {fr : Frame} (hfs : fr.regs.size = g.valueTab.size)
    (hdef : ∀ x ∈ gb.values, ∀ gv, g.value? x = some gv → ∀ a ∈ gv.args, a ∉ gb.values →
      ∃ z, fr.regs[a]? = some (some z)) (i : Nat) :
    ∃ G, enterBlock env (Ctx.make tabs g) fr gb i = .ok G ∧ G = { fr with regs := G.regs } ∧
      G.regs.size = fr.regs.size ∧ ∀ a, a ∉ gb.values → G.regs[a]? = fr.regs[a]? := by
  have hownG := valuesOwn hwg hbg hgb
  have hndG := hwg.valuesNodup _ _ ⟨hbg, hgb⟩
  obtain ⟨b'', hb'', hgid⟩ := hwg.blockId bid hbg
  rw [hgb] at hb''; cases hb''
  obtain ⟨ps, hps⟩ : ∃ ps, gb.values.toList.filterMapM (phiStep (Ctx.make tabs g) fr i) =
      .ok ps := by
    refine filterMapM_phi_ok fun z hz => ⟨none, ?_⟩
    obtain ⟨gv, hgv, hs⟩ := hss z (Array.mem_toList_iff.1 hz)
    unfold phiStep
    simp only [show (Ctx.make tabs g).f = g from rfl, hgv,
      show (gv.op == .Phi) = false by simpa using specSafe_not_phi hs]
    rfl
  obtain ⟨-, -, hkeep, -⟩ := phis_spec hndG hps
  have hP : setPhis ps fr.regs = fr.regs := Array.ext_getElem? fun z => hkeep z (by
    by_cases hz : z ∈ gb.values
    · obtain ⟨gv, hgv, hs⟩ := hss z hz
      exact .inr ⟨gv, hgv, specSafe_not_phi hs⟩
    · exact .inl hz)
  obtain ⟨o, ho⟩ := hsched
  obtain ⟨-, otopo, omem⟩ := schedule_topo hownG hndG ho
  have hmix : MixOK env (Ctx.make tabs g) fr (fun _ => True) o.toList := by
    intro x hx
    obtain ⟨hxg, gv, hgv, -⟩ := (omem x).1 hx
    refine ⟨fun h => absurd trivial h, fun _ g' _ hd => ?_⟩
    obtain ⟨gv', hgv', hs⟩ := hss x hxg
    rw [hgv] at hgv'; cases hgv'
    obtain ⟨y, hy⟩ := evalValue_specSafe (env := env) (ctx := Ctx.make tabs g) (fr := g') hs
      (fun a ha => hd a (by
        rw [show (Ctx.make tabs g).f = g from rfl, argsF_of hgv]
        exact Array.mem_toList_iff.2 ha))
    exact ⟨y, by rw [stepV_of (ctx := Ctx.make tabs g) hgv]; exact hy⟩
  have href : RefOK (argsF (Ctx.make tabs g).f)
      (fun a => a ∉ o.toList ∧ ∃ z, fr.regs[a]? = some (some z)) o.toList := by
    refine Dead.refOK_of_topo otopo fun x hx a ha hna => ⟨hna, ?_⟩
    obtain ⟨hxg, gv, hgv, -⟩ := (omem x).1 hx
    rw [show (Ctx.make tabs g).f = g from rfl, argsF_of hgv] at ha
    refine hdef x hxg gv hgv a (Array.mem_toList_iff.1 ha) fun hag => hna ((omem a).2 ⟨hag, ?_⟩)
    obtain ⟨av, hav, hs⟩ := hss a hag
    exact ⟨av, hav, specSafe_not_phi hs⟩
  obtain ⟨G, h1, h2, h3, -, -, h6⟩ := evalAll_mix (G := fr) (F := fun _ => True) hfs hmix href
    (fun _ _ h => absurd trivial h) (fun a ha => ha.2) (g := fr) rfl rfl
  refine ⟨G, ?_, h2, h3, fun a ha => h6 a fun hm => ha ((omem a).1 hm).1⟩
  rw [enterBlock_eq, hps]
  change (Res.ofOption _ ((Ctx.make tabs g).sched[gb.id]?).join).bind _ = _
  rw [hgid, sched_of_block hgb, ho]
  change evalAll env (Ctx.make tabs g) { fr with regs := setPhis ps fr.regs } o.toList = _
  rw [hP]
  exact h1

end GoFV.Proof.FuseIf

import GoFV.Gen.Check
import GoFV.Proof.Gen.Rel

/-!
# What the genssa validator's slice G1 accepted (`docs/plans/proofs3.md` §3)

`checkG1 lc ps bstart = .ok tab` unfolded into the facts the soundness proof uses: the function
is lowered, every home is one G1 handles (`homeOK`), the Prog IDs are distinct and below `2^32`,
and for every block of the layout its row of `tab` lists the index in `ps` where each value's
Progs start (`Cx.values_spec`: each value's kind, `VK`, and the Progs between consecutive
indices, `VStep`) and where its terminator's start, whose Progs have the shapes of `TermOK`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-! ## Operands -/

theorem regHome?_eq {lc : LocCtx} {a r : Nat} : regHome? lc a = some r ↔ lc.home a = some (.reg r) := by
  sorry

theorem argObj_spec {lc : LocCtx} {v : Value} {i c : Nat} {o : Int} (h : argObj lc v i = .ok (c, o)) :
    ∃ a r, v.args[i]? = some a ∧ lc.home a = some (.reg r) ∧ objOf? r = some o ∧ cls (lc.ty a) = some c := by
  sorry

theorem resObj_spec {lc : LocCtx} {v : Value} {c : Nat} {o : Int} (h : resObj lc v = .ok (c, o)) :
    ∃ r, lc.home v.id = some (.reg r) ∧ destOK r = true ∧ objOf? r = some o ∧
      cls (lc.ty v.id) = some c := by
  sorry

theorem memArg_spec {lc : LocCtx} {v : Value} {i : Nat} (h : memArg lc v i = .ok ()) :
    ∃ a, v.args[i]? = some a ∧ memTy (lc.ty a) = true ∧ lc.home a = none := by
  sorry

/-- An obj register of a Go register: `REG_R0 + k` with `k = 31` (`ZR`) for `ZERO`, else the X
register `k < 31` of `objX?`. -/
theorem objOf?_some {r : Nat} {o : Int} (h : objOf? r = some o) :
    ∃ k : Nat, k < 32 ∧ o = ARM64.REG_R0 + k ∧
      ((r = zeroReg ∧ k = 31) ∨ (k < 31 ∧ objX? r = some (BitVec.ofNat 5 k))) := by
  sorry

/-! ## Values -/

/-- What `vkind` accepted of a value that is not an entry value, and what it emits. -/
inductive VK (lc : LocCtx) (v : Value) : VKind → Prop
  | phi : v.op = .Phi → v.args.all (lc.home · == lc.home v.id) = true → VK lc v .none
  | zero : v.op = .ARM64ZERO → v.args.size = 0 → lc.home v.id = some (.reg zeroReg) →
      (cls (lc.ty v.id)).isSome = true → VK lc v .none
  | inl : v.op = .InlMark → lc.home v.id = none → inertTy (lc.ty v.id) = true → VK lc v .none
  | copyMem : v.op = .Copy → memTy (lc.ty v.id) = true → v.args.size = 1 → memArg lc v 0 = .ok () →
      lc.home v.id = none → VK lc v .none
  | copySame {c : Nat} {r : Int} : v.op = .Copy → memTy (lc.ty v.id) = false → v.args.size = 1 →
      argObj lc v 0 = .ok (c, r) → resObj lc v = .ok (c, r) → VK lc v .none
  | copyMov {c : Nat} {ra rd : Int} : v.op = .Copy → memTy (lc.ty v.id) = false →
      v.args.size = 1 → argObj lc v 0 = .ok (c, ra) → resObj lc v = .ok (c, rd) → ra ≠ rd →
      VK lc v (.prog { as := .MOVD, from_ := regA ra, to := regA rd })
  | result : v.op = .MakeResult → (lc.home v.id = none ∨ lc.home v.id = some (.results #[])) →
      resultsTy lc v.args (lc.ty v.id) = true →
      (∀ a ∈ v.args.toList, memTy (lc.ty a) = true → lc.home a = none) →
      (∀ a ∈ v.args.toList, memTy (lc.ty a) = false →
        (regHome? lc a).isSome = true ∧ (cls (lc.ty a)).isSome = true) →
      VK lc v .none
  | movConst {c : Nat} {rd : Int} : v.op = .ARM64MOVDconst → v.args.size = 0 →
      resObj lc v = .ok (c, rd) → (c = 1 → v.auxInt = 0 ∨ v.auxInt = 1) →
      VK lc v (.prog { as := .MOVD, from_ := constA v.auxInt.toInt, to := regA rd })
  | alu {c ca cb : Nat} {rn rm rd : Int} {as : As} :
      (v.op = .ARM64ADD ∧ as = .ADD ∨ v.op = .ARM64SUB ∧ as = .SUB) → v.args.size = 2 →
      argObj lc v 0 = .ok (ca, rn) → argObj lc v 1 = .ok (cb, rm) → resObj lc v = .ok (c, rd) →
      8 ≤ c → c ≤ ca → c ≤ cb →
      VK lc v (.prog { as, from_ := regA rm, reg := rn, to := regA rd })
  | aluK {c ca : Nat} {rn rd : Int} {as : As} :
      (v.op = .ARM64ADDconst ∧ as = .ADD ∨ v.op = .ARM64SUBconst ∧ as = .SUB) → v.args.size = 1 →
      argObj lc v 0 = .ok (ca, rn) → resObj lc v = .ok (c, rd) → 8 ≤ c → c ≤ ca →
      VK lc v (.prog { as, from_ := constA v.auxInt.toInt, reg := rn, to := regA rd })
  | cmp {rn rm : Int} : v.op = .ARM64CMP → v.args.size = 2 → (lc.ty v.id).isFlags = true →
      lc.home v.id = none → argObj lc v 0 = .ok (64, rn) → argObj lc v 1 = .ok (64, rm) →
      VK lc v (.prog { as := .CMP, from_ := regA rm, reg := rn })
  | cmpK {rn : Int} : v.op = .ARM64CMPconst → v.args.size = 1 → (lc.ty v.id).isFlags = true →
      lc.home v.id = none → argObj lc v 0 = .ok (64, rn) →
      VK lc v (.prog { as := .CMP, from_ := constA v.auxInt.toInt, reg := rn })
  | load {c : Nat} {rn rd : Int} : v.op = .ARM64MOVDload → v.args.size = 2 → v.aux = none →
      argObj lc v 0 = .ok (64, rn) → memArg lc v 1 = .ok () → resObj lc v = .ok (c, rd) → 8 ≤ c →
      VK lc v (.prog { as := .MOVD, from_ := memA rn v.auxInt.toInt, to := regA rd })
  | store {cs : Nat} {rn rs : Int} : v.op = .ARM64MOVDstore → v.args.size = 3 → v.aux = none →
      memTy (lc.ty v.id) = true → lc.home v.id = none → argObj lc v 0 = .ok (64, rn) →
      argObj lc v 1 = .ok (cs, rs) → memArg lc v 2 = .ok () → (cs = 64 ∨ cs = 1) →
      VK lc v (.prog { as := .MOVD, from_ := regA rs, to := memA rn v.auxInt.toInt })

/-- What `vkind` accepted of a value that is not an entry value: no temporary, and `VK`. -/
theorem vkind_spec {lc : LocCtx} {v : Value} {kd : VKind} (h : vkind lc v = .ok kd)
    (hen : entryOp v.op = false) : (lc.temps[v.id]?).join = none ∧ VK lc v kd := by
  sorry

/-! ## Prog positions -/

/-- From index `j`, after no-ops, the Prog at index `j' - 1` has shape `sh`. -/
def OneAt (ps : Array Prog) (j : Nat) (sh : Shape) (j' : Nat) : Prop :=
  ∃ k, j ≤ k ∧ j' = k + 1 ∧ ∃ hk : k < ps.size, sh.ok ps[k] = true ∧
    ∀ l (hl : l < ps.size), j ≤ l → l < k → noop ps[l] = true

theorem Cx.one_spec {cx : Cx} {j j' : Nat} {sh : Shape} (h : cx.one j sh = .ok j') :
    OneAt cx.ps j sh j' := by
  sorry

theorem Cx.startIdx_spec {cx : Cx} {b : ID} {j : Nat} (h : cx.startIdx b = .ok j) :
    ∃ id, cx.bstart b = some id ∧ ∃ hj : j < cx.ps.size, cx.ps[j].id = id := by
  sorry

/-- The Progs between the start index of a value and the next. -/
def VStep (ps : Array Prog) : VKind → Nat → Nat → Prop
  | .entry, j, j' => j' = j
  | .none, j, j' => j' = j
  | .prog sh, j, j' => OneAt ps j sh j'

theorem Cx.values_spec {cx : Cx} {entry : Bool} :
    ∀ {ids : List ID} {j : Nat} {head : Bool} {js : List Nat} {e : Nat},
      cx.values entry ids j head = .ok (js, e) →
      js.length = ids.length ∧ (js ++ [e]).getD 0 0 = j ∧
      ∀ i (hi : i < ids.length), ∃ v kd, cx.lc.ctx.f.value? ids[i] = some v ∧
        vkind cx.lc v = .ok kd ∧ VStep cx.ps kd ((js ++ [e]).getD i 0) ((js ++ [e]).getD (i + 1) 0) := by
  sorry

/-! ## Terminators -/

/-- A branch of shape `br` to `t`, then the fall-through to `f` (laid out next, `next`) or a `JMP`
to `f`, from index `j`. -/
def TwoAt (cx : Cx) (next : Option (ID × Nat)) (j : Nat) (br : Shape) (t f : ID) : Prop :=
  ∃ tid k, cx.bstart t = some tid ∧ OneAt cx.ps j { br with to := brA tid } k ∧
    (next = some (f, k) ∨
      ∃ fid k', cx.bstart f = some fid ∧ OneAt cx.ps k { as := .JMP, to := brA fid } k')

/-- What `Cx.term` accepted of a terminator from index `j`. -/
structure TermOK (cx : Cx) (b : Block) (j : Nat) (next : Option (ID × Nat)) : Prop where
  succs : ∀ e ∈ b.succs.toList, e.b ∈ cx.lc.ctx.f.blocks.toList
  plain : b.kind = .Plain → ∃ e, b.succs = #[e] ∧
    (next = some (e.b, j) ∨ ∃ id k, cx.bstart e.b = some id ∧ OneAt cx.ps j { as := .JMP, to := brA id } k)
  branch : b.kind ≠ .Plain → b.kind ≠ .Ret → ∃ e0 e1 c, b.succs = #[e0, e1] ∧ b.controls = #[c] ∧
    ((∃ asm inv, condBr b.kind = some (asm, inv) ∧ (cx.lc.ty c).isFlags = true ∧
        cx.lc.home c = none ∧
        (TwoAt cx next j { as := asm } e0.b e1.b ∨ TwoAt cx next j { as := inv } e1.b e0.b)) ∨
     (∃ asm inv r o, condBr b.kind = none ∧ zeroBr b.kind = some (asm, inv) ∧
        cx.lc.home c = some (.reg r) ∧ objOf? r = some o ∧
        (cls (cx.lc.ty c) = some 64 ∨ cls (cx.lc.ty c) = some 1) ∧
        (TwoAt cx next j { as := asm, from_ := regA o } e0.b e1.b ∨
          TwoAt cx next j { as := inv, from_ := regA o } e1.b e0.b)))

theorem Cx.term_spec {cx : Cx} {b : Block} {j : Nat} {next : Option (ID × Nat)}
    (h : cx.term b j next = .ok ()) : TermOK cx b j next := by
  sorry

/-! ## Blocks and the whole check -/

theorem Cx.blocks_spec {cx : Cx} : ∀ {bids : List ID} {tab : PcTab}, cx.blocks bids = .ok tab →
    ∀ bid ∈ bids, ∃ b j js e next, cx.lc.ctx.f.block? bid = some b ∧ cx.startIdx bid = .ok j ∧
      cx.values (bid == cx.lc.ctx.f.entry) b.values.toList j true = .ok (js, e) ∧
      TermOK cx b e next ∧ (∀ n k, next = some (n, k) → cx.startIdx n = .ok k) ∧
      tab.lookup bid = some (js ++ [e]) := by
  sorry

theorem checkG1_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {tab : PcTab}
    (h : checkG1 lc ps bstart = .ok tab) :
    ∃ cx : Cx, cx.lc = lc ∧ cx.ps = ps ∧ cx.bstart = bstart ∧ lc.ctx.f.lowered = true ∧
      (∀ i, homeOK lc i = true) ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧
      (ps.toList.map (·.id)).Nodup ∧ cx.blocks lc.ctx.f.blocks.toList = .ok tab := by
  sorry

end GoFV.Gen.Check

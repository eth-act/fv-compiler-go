import GoFV.Proof.Obj.Basic

/-!
# What `checkObj` accepted (`GoFV/Asm/CheckObj.lean`)

The executable validator's checks as propositions: `sameEffect_spec`, `sameCtl_spec`
(`CtlMatch`), `checkProg_spec`, `checkOne_spec`, `checkBody_spec`, the templates
(`frameOK_spec`, `retOK_spec`, `checkStackCheck_spec`, `checkPrologue_spec`), the offset table
(`startsOf_*`, `offOf_zip`) and `checkObj_spec`.
-/

namespace GoFV.Proof.Obj

open GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj

theorem sameEffect_spec {m p : Sym} (h : sameEffect m p = .ok ()) :
    (∀ r ∈ cmpRegs, m.getX r = p.getX r) ∧ m.getX 30 = .x 30 ∧ p.getX 30 = .x 30 ∧
    m.sp = p.sp ∧ m.fl = p.fl ∧ m.stores = p.stores ∧ (∀ x ∈ m.loads, x ∈ p.loads) ∧
    p.readsTmp = false := by
  sorry

/-- A branch to Prog `id` reaches offset `q`. -/
def TgtOK (offs : List (Nat × Nat)) (id : Nat) (q : Int) : Prop :=
  ∃ o, offOf offs id = some o ∧ (o : Int) = q

/-- What `sameCtl` accepts. -/
def CtlMatch (offs : List (Nat × Nat)) (pr : Sym) : MCtl → PCtl → Prop
  | .fall, .fall => True
  | .jmp q, .jmp id => TgtOK offs id q
  | .cond fl c q, .cond c' id => fl = .init ∧ c = c' ∧ TgtOK offs id q
  | .cbz sf nz a q, .cbz sf' nz' a' id =>
    sf = sf' ∧ nz = nz' ∧ a = a' ∧ a'.reads 27 = false ∧ a'.reads 30 = false ∧ TgtOK offs id q
  | .tbz nz b a q, .tbz nz' b' a' id =>
    nz = nz' ∧ b = b' ∧ a = a' ∧ a'.reads 27 = false ∧ a'.reads 30 = false ∧ TgtOK offs id q
  | .reg a, .reg a' => a = .x 30 ∧ a' = .x 30 ∧ pr.getX 30 = .x 30
  | .call n add, .call n' add' => n = n' ∧ add = add' ∧ add = 0
  | _, _ => False

theorem sameCtl_spec {offs : List (Nat × Nat)} {m : MCtl} {p : PCtl} {pr : Sym}
    (h : sameCtl offs m p pr = .ok ()) : CtlMatch offs pr m p := by
  sorry

theorem checkProg_spec {t : ByteArray} {rs : List Reloc} {offs : List (Nat × Nat)} {az ez : Int}
    {p : Prog} {o e : Nat} (h : checkProg t rs offs az ez p o e = .ok ()) :
    ((p.isSkip = true ∨ p.as = .END) ∧ o = e) ∨
    (p.isSkip = false ∧ p.as ≠ .END ∧ o < e ∧ (e - o) % 4 = 0 ∧ ∃ pσ pc mσ mc,
      progSym az ez p = .ok (pσ, pc) ∧ symWords t rs ((e - o) / 4) o {} = .ok (mσ, mc) ∧
      sameEffect mσ pσ = .ok () ∧ sameCtl offs mc pc pσ = .ok ()) := by
  sorry

/-- A P0 `RET` (without operand, or of a symbol: a tail call). -/
def isRet0 (p : Prog) : Bool := p.as == .RET && (p.to.type == .NONE || p.to.sym.isSome)

/-- Where a P0 `RET`'s epilogue goes. -/
def retBack (az : Int) (leaf : Bool) (p : Prog) : MCtl :=
  match p.to.sym with
  | some y => MCtl.jmpSym y p.to.offset
  | none => .reg (if az == 0 || leaf then .x 30 else .ld 8 .sp)

theorem checkOne_spec {t : ByteArray} {rs : List Reloc} {offs : List (Nat × Nat)} {az ez : Int}
    {leaf : Bool} {p : Prog} {s e : Nat} (h : checkOne t rs offs az ez leaf p s e = .ok ()) :
    (isRet0 p = true ∧ s < e ∧ (e - s) % 4 = 0 ∧ ∃ σ c,
      symWords t rs ((e - s) / 4) s {} = .ok (σ, c) ∧ retOK az leaf σ c (retBack az leaf p) = .ok ()) ∨
    (isRet0 p = false ∧ checkProg t rs offs az ez p s e = .ok ()) := by
  sorry

theorem checkBody_spec {t : ByteArray} {rs : List Reloc} {offs : List (Nat × Nat)} {az ez : Int}
    {leaf : Bool} : ∀ (ps : List Prog) (ss : List Nat) (lastEnd : Nat),
    checkBody t rs offs az ez leaf ps ss lastEnd = .ok () → ∀ (hlen : ss.length = ps.length),
    ∀ k (hk : k < ps.length),
      checkOne t rs offs az ez leaf ps[k] (ss[k]'(by omega)) (ss.getD (k + 1) lastEnd) = .ok () := by
  sorry

theorem startsOf_length (e : Nat) (os : List (Option Nat)) : (startsOf e os).length = os.length := by
  sorry

theorem startsOf_getElem (e : Nat) (os : List (Option Nat)) (k : Nat)
    (hk : k < (startsOf e os).length) :
    (startsOf e os)[k] = (os[k]'(by rw [startsOf_length] at hk; exact hk)).getD
      ((startsOf e os).getD (k + 1) e) := by
  sorry

/-- A lookup in the ID ↦ offset table finds the offset of a Prog with that ID. -/
theorem offOf_zip {ps : List Prog} {ss : List Nat} {id q : Nat} (hlen : ss.length = ps.length)
    (h : offOf ((ps.zip ss).map fun (p, s) => (p.id, s)) id = some q) :
    ∃ k, ∃ hk : k < ps.length, ps[k].id = id ∧ ss[k]'(by omega) = q := by
  sorry

/-- The frame's prologue store pair. -/
def frameStores (az : Int) : List (Ex × Nat × Ex) :=
  [(Ex.mkAdd .sp (.k (BitVec.ofInt 64 (-az))), 8, Ex.x 30),
   (Ex.mkAdd .sp (.k (BitVec.ofInt 64 (-az - 8))), 8, Ex.x 29)]

theorem frameOK_spec {az : Int} {σ : Sym} (h : frameOK az σ = .ok ()) :
    σ.sp = Ex.mkAdd .sp (.k (BitVec.ofInt 64 (-az))) ∧
    σ.getX 29 = Ex.mkAdd .sp (.k (BitVec.ofInt 64 (-az - 8))) ∧
    (∀ r ∈ cmpRegs, r ≠ 29 → r ≠ 20 → σ.getX r = .x r) ∧ σ.getX 30 = .x 30 ∧
    (σ.stores = frameStores az ∨ σ.stores = (frameStores az).reverse) := by
  sorry

theorem retOK_spec {az : Int} {leaf : Bool} {σ : Sym} {c back : MCtl}
    (h : retOK az leaf σ c back = .ok ()) :
    (az = 0 ∧ σ = {} ∧ c = back) ∨
    (az ≠ 0 ∧ σ.sp = Ex.mkAdd .sp (.k (BitVec.ofInt 64 az)) ∧
      σ.getX 29 = (if leaf then Ex.mkAdd .sp (.k (BitVec.ofInt 64 (az - 8)))
        else .ld 8 (Ex.mkAdd .sp (.k (BitVec.ofInt 64 (-8))))) ∧
      σ.getX 30 = (if leaf then Ex.x 30 else .ld 8 .sp) ∧
      (∀ r ∈ cmpRegs, r ≠ 29 → σ.getX r = .x r) ∧ σ.fl = .init ∧ σ.stores = [] ∧ c = back) := by
  sorry

theorem checkStackCheck_spec {t : ByteArray} {rs : List Reloc} {az : Int} {o gOff ce tail : Nat}
    (h : checkStackCheck t rs az o gOff = .ok (ce, tail)) :
    az ≤ 4096 ∧ ∃ σ,
      symWords t rs (if az ≤ 128 then 3 else 4) o {} =
        .ok (σ, .cond (.addSub true true
          (if az ≤ 128 then Ex.sp else Ex.mkAdd .sp (.k (BitVec.ofInt 64 (-(az - 128)))))
          (.ld 8 (Ex.mkAdd (.x 28) (.k (BitVec.ofNat 64 gOff))))) 9 (tail : Int)) ∧
      ce = o + 4 * (if az ≤ 128 then 3 else 4) ∧ σ.stores = [] ∧
      (∀ r ∈ cmpRegs, r ≠ 16 → r ≠ 17 → σ.getX r = .x r) := by
  sorry

theorem checkPrologue_spec {t : ByteArray} {rs : List Reloc} {az : Int} {body : Nat}
    {check : Option (Nat × Nat)} (h : checkPrologue t rs az body = .ok check) :
    (az = 0 ∧ body = 0 ∧ check = none) ∨
    (az ≠ 0 ∧ ∃ fo σ,
      ((check = none ∧ fo = 0) ∨ ∃ ce tail gOff, check = some (ce, tail) ∧ fo = ce ∧
        (gOff = 16 ∨ gOff = 24) ∧ checkStackCheck t rs az 0 gOff = .ok (ce, tail)) ∧
      fo < body ∧ (body - fo) % 4 = 0 ∧ symWords t rs ((body - fo) / 4) fo {} = .ok (σ, .fall) ∧
      frameOK az σ = .ok ()) := by
  sorry

theorem checkObj_spec {ps : Array Prog} {spills : Array Spill} {o : ObjIn} {tab : Tab}
    (h : checkObj ps spills o = .ok tab) :
    ∃ text body, ps[0]? = some text ∧ text.as = .TEXT ∧ (ps.toList.map (·.id)).Nodup ∧
      (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ 2 ≤ ps.size ∧ tab.offs.size = ps.size ∧
      tab.offs[0]? = some body ∧ tab.offs[1]? = some body ∧ tab.leaf = leafOf ps ∧
      checkPrologue o.text o.relocs.toList tab.autosize body = .ok tab.check ∧
      (∀ ce tail, tab.check = some (ce, tail) → tab.endOff = tail) ∧
      checkBody o.text o.relocs.toList ((ps.toList.zip tab.offs.toList).map fun (p, s) => (p.id, s))
        tab.autosize tab.extrasize tab.leaf (ps.toList.drop 1) (tab.offs.toList.drop 1)
        tab.endOff = .ok () := by
  sorry

end GoFV.Proof.Obj

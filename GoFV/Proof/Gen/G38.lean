import GoFV.Proof.Gen.G37
import GoFV.Proof.Gen.Spec38

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G38 of the genssa validator: the acquire loads (`docs/plans/proofs3.md` §4)

`checkG38` (`GoFV/Gen/Check38.lean`) is G37 with the acquire loads `LDAR`, `LDARW`, `LDARB p mem`
(`LDAR`/`LDARW`/`LDARB (Rn), Rd`) and their components, `Select0` in the load's register and
`Select1` the memory, both without code. `g38_value`, `g38_term`, `g38_nilPanic` and
`g38_boundsPanic` are G37's statements over `checkG38`; `g38_value`'s per-value premise `G38Pre`
adds to `G14Pre` that an acquire load reads valid bytes (`LdarPre`: Phase 1's `Mem.read` of its
`n` bytes at the address in its register succeeds), as `G3Pre` does for the loads.

`runLoc` runs an acquire load as Phase 1's `atomicLoad` (`stepLoc_ldar`): the value of the
component's shape at the address, `poison` if it is not naturally aligned, and the memory
unchanged; it writes the value to the load's register and keeps the memory (`write_ldar`). At an
integer of `n` bytes or (`n = 8`) a pointer shape, that value is the `n`-byte load G3 relates to
the machine (`ldar_val`, G3's `lo_loadN`), and the machine's `LDAR*` loads the zero extension of
the `n` bytes at the address (`progStep_ldar`). A component reads the load's tuple from its home
(`read_ldar`): `Select0` is its register, which the machine already holds (`g38_sel0`), `Select1`
the memory (`g38_sel1`). The G38 values empty G35's upper-bit table (`uStep35_ldar`,
`uStep35_selLdar`). On a function with no arm64 op, `checkG38` is `checkG33`.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The premise -/

/-- An acquire load reads `n` valid bytes at the address in its register (offset 0). -/
def LdarPre (lc : LocCtx) (s : LocState) (v : Value) : Prop :=
  ∀ as n, ldar? v.op = some (as, n) → ∀ a x, v.args[0]? = some a → s.read lc a = .ok x →
    ∃ p mm bs, Arm64.addr x 0 = some p ∧ s.mem = .mem mm ∧ mm.read p n = some bs

/-- The per-value premises of G38: G14's (`G14Pre`), and an acquire load reads valid bytes
(`LdarPre`). -/
def G38Pre (lc : LocCtx) (s : LocState) (v : Value) : Prop := G14Pre lc s v ∧ LdarPre lc s v

/-! ## Ops -/

theorem ldar?_some {op : Op} {as : As} {n : Nat} (h : ldar? op = some (as, n)) :
    op = .ARM64LDAR ∧ as = .LDAR ∧ n = 8 ∨ op = .ARM64LDARW ∧ as = .LDARW ∧ n = 4 ∨
      op = .ARM64LDARB ∧ as = .LDARB ∧ n = 1 := by
  unfold ldar? at h
  split at h <;> simp_all

/-- An acquire load is no `Phi`, `MOVDnop`, `MOVDreg`, nil check, bounds panic, load of
`loadOp?` or `loadIdxOp?`, pair load. -/
theorem ldar_ne {op : Op} {as : As} {n : Nat} (h : ldar? op = some (as, n)) :
    op ≠ .Phi ∧ op ≠ .ARM64MOVDnop ∧ op ≠ .ARM64MOVDreg ∧ op ≠ .ARM64LoweredNilCheck ∧
      pbOp op = false ∧ loadOp? op = none ∧ loadIdxOp? op = none ∧ op ≠ .ARM64LDP := by
  rcases ldar?_some h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
    exact ⟨nofun, nofun, nofun, nofun, rfl, rfl, rfl, nofun⟩

/-- An acquire load writes only the register of its `(Rd;-)` home: G35's table keeps the entries
of the other registers. -/
theorem uStep35_ldar {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value} {as : As} {n : Nat}
    (hop : ldar? v.op = some (as, n)) :
    uStep35 lc L v = L.filter (!(homeRegs lc v.id).contains ·.1) := by
  obtain ⟨-, -, -, -, -, hl, -, -⟩ := ldar_ne hop
  rcases ldar?_some hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
    exact uStep35_keepOp (ldEntry35_none hl) (by simp [pairOp35, h]) (by simp [h]) (by simp [h])

/-- A component of an acquire load (of the value `c`) emits no code: G35's table stays. -/
theorem uStep35_selLdar {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value} {c : ID}
    (hop : v.op = .Select0 ∨ v.op = .Select1) (hc : v.args[0]? = some c)
    (hu : ((lc.ctx.f.value? c).any fun u => (ldar? u.op).isSome) = true) :
    uStep35 lc L v = L := by
  have hl : loadOp? v.op = none := by rcases hop with h | h <;> rw [h] <;> rfl
  refine uStep35_sel (ldEntry35_none hl) ?_ hop
  cases hv : lc.ctx.f.value? c with
  | none => rw [hv] at hu; cases hu
  | some u =>
    rw [hv] at hu
    simp only [Option.any_some, Option.isSome_iff_exists] at hu
    obtain ⟨⟨as, n⟩, hu⟩ := hu
    rcases ldar?_some hu with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rcases hop with h' | h' <;>
      simp [pairOp35, h', hc, hv, h]

/-! ## `runLoc` -/

section Steps

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

private theorem mapM_two38 {a b : ID} :
    [a, b].mapM (s.read lc) =
      (s.read lc a).bind fun x => (s.read lc b).bind fun y => .ok [x, y] := rfl

/-- An acquire load whose `arm64Op` is `atomicLoad`. -/
private theorem ldar_core (hl : lc.ctx.f.lowered = true)
    (ht : (lc.temps[v.id]?).join = none) (hne : v.op ≠ .Phi) (h1 : v.op ≠ .LoadReg)
    (h2 : v.op ≠ .StoreReg) (h3 : v.op ≠ .ARM64MOVDreg) (h4 : v.op ≠ .ARM64MOVDnop)
    (hc : v.op.regInfo.clobbers.isEmpty = true) (hc0 : v.op.regInfo.clobbersArg0 = false)
    (hc1 : v.op.regInfo.clobbersArg1 = false) (hf : v.op.clobberFlags = false)
    (hev : ∀ argv, evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) =
      arm64Op true env lc.ctx s.fr v argv (lc.ty v.id))
    (hld : ∀ x mm, nilFaults true lc.ctx v [x, .mem mm] = none →
      arm64Op true env lc.ctx s.fr v [x, .mem mm] (lc.ty v.id) =
        .ok (atomicLoad (lc.ty v.id) [x, .mem mm]))
    {a0 a1 : ID} (ha : v.args = #[a0, a1]) {mm : Mem} (hm : s.read lc a1 = .ok (.mem mm))
    (h : stepLoc env lc s v = .ok s') :
    ∃ x, s.read lc a0 = .ok x ∧
      s' = s.write lc v.id ((atomicLoad (lc.ty v.id) [x, .mem mm]).retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, hmap, hr, rfl⟩ := stepLoc_noclobber hl ht hne h1 h2 h3 h4 hc hc0 hc1 hf h
  rw [ha] at hmap
  change [a0, a1].mapM (s.read lc) = _ at hmap
  rw [mapM_two38] at hmap
  cases hx : s.read lc a0 with
  | panic e m => rw [hx] at hmap; cases hmap
  | stuck msg => rw [hx] at hmap; cases hmap
  | ok x =>
    rw [hx, hm] at hmap; cases hmap
    rw [hev] at hr
    cases hn : nilFaults true lc.ctx v [x, .mem mm] with
    | some m =>
      have he : arm64Op true env lc.ctx s.fr v [x, .mem mm] (lc.ty v.id) = .panic .nilDeref m := by
        unfold arm64Op; rw [hn]
      rw [he] at hr; cases hr
    | none =>
      rw [hld x mm hn] at hr; cases hr
      exact ⟨x, rfl, rfl⟩

/-- An acquire load (`LDAR`, `LDARW`, `LDARB p mem`): Phase 1's `atomicLoad` of the address and the
memory. -/
theorem stepLoc_ldar (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    {as : As} {n : Nat} (hop : ldar? v.op = some (as, n)) {a0 a1 : ID} (ha : v.args = #[a0, a1])
    {mm : Mem} (hm : s.read lc a1 = .ok (.mem mm)) (h : stepLoc env lc s v = .ok s') :
    ∃ x, s.read lc a0 = .ok x ∧
      s' = s.write lc v.id ((atomicLoad (lc.ty v.id) [x, .mem mm]).retypeL (lc.ty v.id)) := by
  rcases ldar?_some hop with ⟨ho, -⟩ | ⟨ho, -⟩ | ⟨ho, -⟩ <;>
  · exact ldar_core hl ht (by rw [ho]; nofun) (by rw [ho]; nofun) (by rw [ho]; nofun)
      (by rw [ho]; nofun) (by rw [ho]; nofun) (by rw [ho]; rfl) (by rw [ho]; rfl) (by rw [ho]; rfl)
      (by rw [ho]; rfl) (fun _ => by unfold evalOpL; rw [ho]; rfl)
      (fun _ _ hn => by unfold arm64Op; rw [hn, ho]; rfl) ha hm h

/-- The tuple of an acquire load written to its home `(r, -)`: the component to `r`, the memory
(unchanged) to the state's. -/
theorem write_ldar {id r : Nat} {t0 : Ty} {y : Val} {mm : Mem}
    (hh : lc.home id = some (.pair (some r) none)) (hty : lc.ty id = .tuple [t0, .mem])
    (hc : (cls t0).isSome = true) (hmem : s.mem = .mem mm) :
    s.write lc id (.tuple [y, .mem mm]) = s.setReg r y := by
  unfold LocState.write
  simp only [hh, hty, Option.map_some, Option.getD_some, Location.regList, Val.partsOf]
  rw [writeParts_reg hc]
  simp only [LocState.writeParts]
  rw [← hmem]
  rfl

/-- An acquire load's tuple read from its home `(r, -)`: the register at the component's shape,
and the memory. -/
theorem read_ldar {c r : Nat} {t0 : Ty} (hl : lc.ctx.f.lowered = true)
    (hh : lc.home c = some (.pair (some r) none)) (hty : lc.ty c = .tuple [t0, .mem])
    (hc : (cls t0).isSome = true) :
    s.read lc c = .ok (.tuple [(s.reg t0 r).retypeL t0, s.mem.retypeL .mem]) := by
  have hraw : s.raw lc c = .ok (.tuple [s.reg t0 r, s.mem]) := by
    unfold LocState.raw
    simp only [hh, hty, Location.regList]
    rw [readParts_cons (cls_notMem hc) (cls_notFlags hc)]
    rfl
  unfold LocState.read
  rw [hraw]; simp only [lmode_retype hl, hty, retypeL_pair]
  rfl

end Steps

/-! ## The loaded value -/

section Vals

/-- A base of 64 bits whose address at offset 0 is `p` is the pointer word of `p`. -/
theorem asPtrWord_of_addr {x : Val} {p : Ptr} (hf : Fits 64 x) (h : Arm64.addr x 0 = some p) :
    x.asPtrWord = some p := by
  cases x with
  | ptr q =>
    simp only [Arm64.addr, Option.some.injEq] at h
    subst h
    simp [Val.asPtrWord, Ptr.add]
  | int w a =>
    cases w <;> simp [Fits, Width.bits] at hf
    simp only [Arm64.addr, Arm64.reg, Option.map_some, Option.some.injEq] at h
    subst h
    simp [Val.asPtrWord]
  | poison => simp [Arm64.addr, Arm64.reg] at h
  | bool => simp [Fits] at hf
  | _ => exact False.elim hf

/-- Eight bytes that are a stored pointer's fragments are not concrete bytes. -/
private theorem bytesNat?_of_ptr {bs : Array Byte} {q : Ptr} (h : bytesPtr? bs = some q) :
    bytesNat? bs = none := by
  unfold bytesPtr? at h
  split at h
  · rename_i q' h0
    unfold bytesNat?
    rw [← Array.foldr_toList]
    have h0' : bs.toList[0]? = some (.frag q' 0) := by simpa using h0
    cases hl : bs.toList with
    | nil => rw [hl] at h0'; cases h0'
    | cons b rest =>
      rw [hl] at h0'
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h0'
      subst h0'
      simp only [List.foldr_cons]
  · cases h

/-- A pointer word and a 64-bit integer decode the same 8 bytes alike. -/
theorem decodePtr_eq (bs : Array Byte) : decodePtr bs = decodeInt .w64 bs := by
  unfold decodePtr decodeInt
  cases hp : bytesPtr? bs with
  | none => cases bytesNat? bs <;> rfl
  | some q => rw [bytesNat?_of_ptr hp]

/-- A load at an integer shape narrower than 64 bits is `poison` or an integer of that width. -/
private theorem load_intN {w : Width} (hw : w ≠ .w64) (mm : Mem) (p : Ptr) :
    mm.load (.int w) p = .poison ∨ ∃ y, mm.load (.int w) p = .int w y := by
  simp only [Mem.load]
  split
  · simp only [decodeLoad, Sem.decode, decodeInt]
    split
    · exact .inr ⟨_, rfl⟩
    · cases w <;> first | exact absurd rfl hw | exact .inl rfl
  · exact .inl rfl

/-- A narrow integer as the 64-bit register `Arm64.res` makes of it, at its shape: itself. -/
private theorem retypeL_res_narrow {w : Width} (hw : w ≠ .w64) (y : BitVec w.bits) :
    Val.retypeL (.int w) (Arm64.res (.int w) (y.setWidth 64)) = Val.retypeL (.int w) (.int w y) := by
  cases w with
  | w64 => exact absurd rfl hw
  | w8 =>
    show Val.int .w8 ((y.setWidth 64).setWidth 8) = Val.int .w8 (y.setWidth 8)
    rw [BitVec.setWidth_setWidth_of_le _ (by decide)]
  | w16 =>
    show Val.int .w16 ((y.setWidth 64).setWidth 16) = Val.int .w16 (y.setWidth 16)
    rw [BitVec.setWidth_setWidth_of_le _ (by decide)]
  | w32 =>
    show Val.int .w32 ((y.setWidth 64).setWidth 32) = Val.int .w32 (y.setWidth 32)
    rw [BitVec.setWidth_setWidth_of_le _ (by decide)]

/-- A narrow load at its shape is the register the `n`-byte load writes, at that shape. -/
private theorem narrow_eq {w : Width} (hw : w ≠ .w64) (mm : Mem) (p : Ptr) :
    (mm.load (.int w) p).retypeL (.int w) =
      (match mm.load (.int w) p with
        | .int _ x => Arm64.res (.int w) (x.setWidth 64)
        | _ => .poison).retypeL (.int w) := by
  rcases load_intN hw mm p with h | ⟨y, h⟩ <;> rw [h]
  exact (retypeL_res_narrow hw y).symm

/-- The value an acquire load reads at a component shape of class `8n` (an integer of `n` bytes,
or a pointer for `n = 8`) is, at that shape, G3's `n`-byte load. -/
theorem ldar_val {t0 : Ty} {n : Nat} (hc : Gen.Check.cls t0 = some (8 * n)) (mm : Mem) (p : Ptr) :
    (mm.load t0 p).retypeL t0 = (Arm64.loadN t0 n false mm p).retypeL t0 := by
  cases t0 with
  | int w =>
    simp only [Gen.Check.cls, Option.some.injEq] at hc
    cases w with
    | w64 =>
      obtain rfl : n = 8 := by simp [Width.bits] at hc; omega
      congr 1
      simp only [Arm64.loadN]
      split
      · rename_i x hx; rw [hx]; rfl
      · rfl
    | w8 =>
      obtain rfl : n = 1 := by simp [Width.bits] at hc; omega
      exact narrow_eq (by decide) mm p
    | w16 =>
      obtain rfl : n = 2 := by simp [Width.bits] at hc; omega
      exact narrow_eq (by decide) mm p
    | w32 =>
      obtain rfl : n = 4 := by simp [Width.bits] at hc; omega
      exact narrow_eq (by decide) mm p
  | ptr e =>
    simp only [Gen.Check.cls, Option.some.injEq] at hc
    obtain rfl : n = 8 := by omega
    congr 1
    have hl : mm.load (.ptr e) p = mm.load (.int .w64) p := by
      simp only [Mem.load, Ty.size, Width.bytes, Width.bits, Nat.reduceDiv]
      cases mm.read p 8 with
      | none => rfl
      | some bs => simp only [decodeLoad, Sem.decode, decodePtr_eq]; rfl
    rw [hl]
    simp only [Arm64.loadN]
    split
    · rename_i x hx; rw [hx]; rfl
    · rfl
  | bool => simp [Gen.Check.cls] at hc; omega
  | _ => simp [Gen.Check.cls] at hc

variable {ι : Blk → Option (BitVec 64)}

/-- An acquire load's component at a valid address, related to the machine's zero-extended `n`
bytes there. -/
theorem valRel_ldar (hA : AddrAgree ι) {m : Mem} {mm : Memory} (h : MemInj ι m mm) {p : Ptr}
    {a : BitVec 64} {n : Nat} {bs : Array Byte} {t0 : Ty} (hn : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8)
    (hc : Gen.Check.cls t0 = some (8 * n)) (ha : ι p.blk = some a) (hr : m.read p n = some bs) :
    ValRel ι ((if t0.size == 0 || p.off.toNat % t0.size != 0 then .poison else m.load t0 p).retypeL
      t0) ((readMem mm (a + p.off) n).setWidth 64) := by
  have h8 : 8 ≤ 8 * n := by omega
  have ht := cls_ne_bool hc h8
  split
  · rw [retypeL_poison]; trivial
  · rw [ldar_val hc]
    have hlo := lo_loadN (sg := false) hA h hn (fun _ => rfl) ht ha hr
    simp only [Bool.false_eq_true, ↓reduceIte] at hlo
    exact valRel_retypeL_lo hA hc ht (hlo.mono (cls_le hc))

end Vals

/-! ## The machine -/

section Progs

variable {L : Link} {p : Prog} {s : MState} {next : BitVec 64}

/-- An opcode name none of `progEffect`'s branches before the acquire-load one takes. -/
private def ldarPre (name : String) (n : Nat) : Prop :=
  name ∉ ["TEXT", "FUNCDATA", "PCDATA", "NOP"] ∧
  ProgOp.baseOf name ProgOp.binNames = none ∧ ProgOp.baseOf name ["CMP", "CMN", "TST"] = none ∧
  ProgOp.baseOf name ["NEG", "NEGS", "MVN", "NGC", "NGCS"] = none ∧
  ProgOp.baseOf name ["CLZ", "RBIT", "REV", "REV16", "REV32"] = none ∧
  ProgOp.baseOf name ["MADD", "MSUB"] = none ∧
  ProgOp.baseOf name ["UBFX", "SBFX", "UBFIZ", "SBFIZ", "BFI", "BFXIL"] = none ∧
  ProgOp.baseOf name ["EXTR"] = none ∧
  ProgOp.baseOf name ["CSEL", "CSINC", "CSINV", "CSNEG"] = none ∧
  ProgOp.baseOf name ["CSET", "CSETM"] = none ∧ ProgOp.movMem name = none ∧
  ProgOp.pairOp name = none ∧ ProgOp.startsS name "LDAR" = true ∧
  ProgOp.suffixBytes (ProgOp.dropS name 4) = n

private theorem ldarPre_of {op : Op} {as : As} {n : Nat} (h : ldar? op = some (as, n)) :
    ldarPre as.name n := by
  rcases ldar?_some h with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ <;>
    simp (config := { decide := true }) [ldarPre]

/-- `LDAR{,W,B} (Rn), Rd` with the address `a` outside the nil page: the zero extension of the `n`
bytes at `a` in `X kd`. -/
theorem progStep_ldar {op : Op} {as : As} {n kd : Nat} {a : BitVec 64}
    (hop : ldar? op = some (as, n)) (hkd : kd < 32) (hn : L.nextAddr p.id = some next)
    (hpa : p.as = as) (hma : (ProgCtx.mk L s p).mem p.from_ = .ok (a, none))
    (ht : p.to = regA (REG_R0 + kd)) (hnil : nilPage a = false) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd) ((readMem s.mem a n).setWidth 64) with
      pc := next } := by
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := ldarPre_of hop
  have he : progEffect ⟨L, s, p⟩ =
      .ok (effWd { loads := [(a, n)] } kd ((readMem s.mem a n).setWidth 64)) := by
    unfold progEffect
    simp only [hpa, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hma, ht, regA, Eff.ld,
      ProgCtx.load, Bool.true_or, Bool.false_eq_true, ↓reduceIte]
    rw [show p.as.name = as.name from by rw [hpa]]
    rw [h12, ite_eq_left_of_eq_true _ _ (eq_self true), h13]
    simp only [eff_wX_dest hkd]
    rfl
  have hsk : p.isSkip = false := by
    rcases ldar?_some hop with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> simp [Prog.isSkip, hpa]
  have hnil' : (effWd { loads := [(a, n)] } kd ((readMem s.mem a n).setWidth 64)).nilAccess? =
      none := by
    by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?, List.find?, hnil]
  rw [progStep_eq hn hsk he hnil']
  by_cases h : kd = 31
  · subst h; rfl
  · simp only [effWd, h, ↓reduceIte, Eff.apply, List.foldr]
    rfl

end Progs

/-! ## Class maps -/

/-- The class table follows an acquire load into its register (`kStep`): the register takes the
component's class. -/
theorem kldar_kStep {lc : LocCtx} {K : KMap} {v : Value} {r : Nat} {t0 : Ty} {c0 : Nat}
    (hop : v.op ≠ .Phi) (hh : lc.home v.id = some (.pair (some r) none))
    (hty : lc.ty v.id = .tuple [t0, .mem]) (h0 : cls t0 = some c0) :
    KLe (kStep lc K v).get (kSet K.get r (some c0)) := by
  intro r' c _ hc
  rw [kStep_get] at hc
  simp only [hop, ↓reduceIte, hh, hty, tupleTys, List.zip_cons_cons, List.zip_nil_right] at hc
  have hnd : ([(t0, some r), (Ty.mem, (none : Option Nat))].filterMap (·.2)).Nodup := by simp
  unfold kSet
  by_cases hr : r' = r
  · subst hr
    simp only [↓reduceIte]
    by_cases hsz : r' < K.size
    · rw [kResults_get_of_mem (t := t0) hnd (by simp) hsz, h0] at hc; exact hc
    · rw [KMap.get_ge (by rw [kResults_size]; omega)] at hc; cases hc
  · simp only [hr, ↓reduceIte]
    rw [kResults_get_of_not_mem (by simp [hr])] at hc
    exact hc

/-- The register of an acquire load a `Select0` reads (`kReads`) holds its component's class. -/
theorem ksel38_of_reads {lc : LocCtx} {v : Value} {K : KMap} {c r k : Nat}
    (h : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2) (hop : v.op = .Select0)
    (hc0 : v.args[0]? = some c) (hhc : lc.home c = some (.pair (some r) none))
    (hcl : ((tupleTys (lc.ty c))[0]?.bind cls) = some k) : K.get r = some k := by
  apply h (r, k)
  simp [kReads, hop, hc0, hhc, hcl]

/-! ## The cases -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- `LDAR{,W,B} (Rn), Rd`: the zero extension of the `n` bytes at the address into `Rd`, the
component of the load's tuple. -/
theorem g38_ldar (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) {as : As} {n : Nat} {t0 : Ty} {rn rd : Int} {r : Nat}
    (hK : KLe K' (kSet K r (some (8 * n)))) (hpre : LdarPre lc s v)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    (hop : ldar? v.op = some (as, n)) (hsz2 : v.args.size = 2) (hk0 : v.auxInt.toInt = 0)
    (hty : lc.ty v.id = .tuple [t0, .mem]) (hc0 : cls t0 = some (8 * n))
    (hao : argObj lc v 0 = .ok (64, rn)) (hma : memArg lc v 1 = .ok ())
    (hh : lc.home v.id = some (.pair (some r) none)) (hd : destOK r = true)
    (hor : objOf? r = some rd)
    (hvs : OneAt2 psA j ⟨plain as (· == memA rn 0) (· == regA rd), as.name⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      ∃ (kd : Nat) (val : BitVec 64), objOf? r = some (GoFV.Asm.ARM64.REG_R0 + kd) ∧
        m'.x = (m.wX (BitVec.ofNat 5 kd) val).x := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := (ldar_ne hop).1
  have hn : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 := by
    rcases ldar?_some hop with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp
  obtain ⟨a1, ha1, hamt, hah1⟩ := memArg_spec hma
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨kd, hkd, rfl, -⟩ := objOf?_some hor
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨x, hx, rfl⟩ :=
    stepLoc_ldar hl htemp hop (arr2 hsz2 ha0 ha1) (read_mem hl hah1 hamt hmm) hs
  obtain ⟨X, hX, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  rw [hx] at hX
  cases hX
  obtain ⟨p, mm2, bs, haddr, hmm2, hrd⟩ := hpre _ _ hop a0 x ha0 hx
  rw [hmm] at hmm2
  cases hmm2
  have hc0' : (cls t0).isSome = true := by rw [hc0]; rfl
  obtain ⟨a, hpa, haeq, hnil⟩ := addr_rel hA hMI hxv hxf haddr (by omega : 0 < n)
    (Or.inr (by rw [hrd]; rfl))
  rw [hty]
  simp only [atomicLoad, asPtrWord_of_addr hxf haddr]
  rw [retypeL_pair, retypeL_mem, write_ldar hh hty hc0' hmm]
  refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_ldar hA hMI hn hc0 hpa hrd) (fits_retypeL hc0 _) hK (fun k0 hk0 hok => ?_)).imp
    fun m' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, hsi, kd, _, hor, h4⟩
  obtain ⟨has, hf, -, ht', hsc, -, -⟩ := plain_spec hok
  simp only [beq_iff_eq] at hf ht'
  have hmaddr : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
      { m with pc := pcAt text psA.toList k0 } psA.toList[k0]).mem psA.toList[k0].from_ =
      .ok (a + p.off, none) := by
    rw [hf, ctx_mem_reg hkn hsc]
    have h0 : BitVec.ofInt 64 (0 : Int) = 0 := rfl
    rw [h0]
    exact congrArg (fun y => Except.ok (y, none)) haeq
  rw [progStep_ldar hop hkd (nextAddr_pcAt F.nodup hk0) has hmaddr ht' hnil, wX_pc]

/-- `Select0` of an acquire load, homed in the load's register: no code, the machine's register
already holds it. -/
theorem g38_sel0 (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {c : ID} {r : Nat} {t0 : Ty}
    (hop : v.op = .Select0) (hsz1 : v.args.size = 1) (hc0 : v.args[0]? = some c)
    (htc : lc.ty c = .tuple [t0, .mem])
    (hhc : lc.home c = some (.pair (some r) none)) (hvh : lc.home v.id = some (.reg r))
    (hrz : r ≠ zeroReg) (hd : destOK r = true) (hob : (objOf? r).isSome = true)
    {cv : Nat} (hcv : cls (lc.ty v.id) = some cv) (hcl : cls t0 = cls (lc.ty v.id))
    (hKr : ∀ c0, cls (lc.ty v.id) = some c0 → K r = some c0)
    (hvs : j' = j) (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      m'.x = m.x := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  have hct : cls t0 = some cv := hcl.trans hcv
  have hread := read_ldar (s := s) hl hhc htc (by rw [hct]; rfl)
  obtain ⟨x, hx, rfl⟩ := stepLoc_select hl htemp (.inl ⟨hop, rfl⟩) (arr1 hsz1 hc0) hs
  rw [hread] at hx
  cases hx
  have hsel : Tuple.select 0 [.tuple [(s.reg t0 r).retypeL t0, s.mem.retypeL .mem]] =
      (s.reg t0 r).retypeL t0 := rfl
  rw [hsel, write_reg hvh hcv]
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 hob
  obtain ⟨k, hk32, rfl, hkk⟩ := objOf?_some ho
  have hk31 : k < 31 ∧ objX? r = some (BitVec.ofNat 5 k) := by
    rcases hkk with ⟨h, -⟩ | h
    · exact absurd h hrz
    · exact h
  have hrel : ValRel E.ι (((s.reg t0 r).retypeL t0).retypeL (lc.ty v.id))
      (m.rX (BitVec.ofNat 5 k)) := by
    rw [rX_lt hk31.1]
    simp only [LocState.reg, beq_iff_eq, hrz, ↓reduceIte]
    cases hv : s.regs[r]? with
    | none => simp only [Option.getD_none, retypeL_poison]; trivial
    | some raw =>
      simp only [Option.getD_some]
      have hfit := hinv.regs r raw cv hrz hv (hKr cv hcv)
      have h1' := valRel_retypeL hA hct hfit ((hm.regs r raw hv).1 _ hk31.2)
      exact valRel_retypeL hA hcv (fits_retypeL hct _) h1'
  obtain ⟨hlm, hinv'⟩ := finish_reg hm hinv hd hk32 ho hrel (fits_retypeL hcv _)
    (b' := b) (i' := i + 1)
  rw [wX_rX_self, hj', hvs, ← hj, ← hm.pc] at hlm
  exact ⟨m, .refl, hlm, hinv'.mono (knext_set hK hnp hvh hcv), hsi, rfl⟩

/-- `Select1` of an acquire load: the memory, which the load kept; no code. -/
theorem g38_sel1 (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hK : KNext lc v K K') (hpc : E.pcOf b (i + 1) = E.pcOf b i)
    {c : ID} {r : Nat} {t0 : Ty}
    (hop : v.op = .Select1) (hsz1 : v.args.size = 1) (hc0 : v.args[0]? = some c)
    (htc : lc.ty c = .tuple [t0, .mem]) (hc : (cls t0).isSome = true)
    (hhc : lc.home c = some (.pair (some r) none)) (hmt : memTy (lc.ty v.id) = true)
    (hhn : lc.home v.id = none)
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      m'.x = m.x := by
  have hl := F.lowered
  obtain ⟨mm, hmm, -⟩ := hm.mem
  have hread := read_ldar (s := s) hl hhc htc hc
  obtain ⟨x, hx, rfl⟩ := stepLoc_select hl htemp (.inr ⟨hop, rfl⟩) (arr1 hsz1 hc0) hs
  rw [hread] at hx
  cases hx
  have hsel : Tuple.select 1 [.tuple [(s.reg t0 r).retypeL t0, s.mem.retypeL .mem]] =
      s.mem.retypeL .mem := rfl
  have hs' : s.write lc v.id ((Tuple.select 1
      [.tuple [(s.reg t0 r).retypeL t0, s.mem.retypeL .mem]]).retypeL (lc.ty v.id)) = s := by
    rw [hsel, write_mem hhn hmt, memTy_eq hmt, hmm, retypeL_mem, retypeL_mem, ← hmm]
  obtain ⟨m', h1, h2, h3, -, h5⟩ := op_noneX (H := H) (sym := sym) (text := text) (az := az)
    (ez := ez) (psA := psA) (ret := ret) hm hinv hs' hpc
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun))
  exact ⟨m', h1, h2, h3, by rw [hs']; exact hsi, h5⟩

end Cases

/-! ## The theorems -/

/-- One value of G38's kinds: `vk37_step`'s statement, under `G38Pre`. -/
theorem vk38_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)}
    (hE : G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK38 lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s osp) (hL : UOKL m L)
    (hmem : ∀ x, (v.op = .ARM64MOVDnop ∨ v.op = .ARM64MOVDreg) → v.args[0]? = some x →
      ∃ r c, regHome? lc x = some r ∧ cls (lc.ty x) = some c ∧
        (r, c, lc.signOf lc.ctx.f.valueTab.size x) ∈ L)
    (hpre : G38Pre lc s v)
    (hcall : CallOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hcallz : CallOKZAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hicall : ICallOKAt osp H E (Link.byId sym text az ez ps.toList) ret lc s s' v m)
    (hwb : WbOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s v m) (hclo : CloOK E s v m)
    (hgetg : GetGOK E v) (hmeq : MemEqOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s v m)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp ∧
      UOKL m' (uStep35 lc L v) := by
  have fin : ∀ m',
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' →
      LocMatch E s' bid (i + 1) m' → CoreInv E.ι (StkAt E) (kStep lc K v).get s' osp →
      SlotInv lc s' → UOKL m' (uStep35 lc L v) →
      ∃ E' m', E.Extends E' ∧ G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
        PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
        LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp ∧
        UOKL m' (uStep35 lc L v) := fun m' h1 h2 h3 h4 h5 =>
    ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩, h5⟩
  cases hVK with
  | g37 _ _ hVK37 =>
    exact vk37_step hE F hhome hcf hv hVK37 hvs htemp hj hj' hreads hm hinv hL hmem hpre.1 hcall
      hcallz hicall hwb hclo hgetg hmeq hs
  | ldar hop hsz hax hk0 hty hc0 hao hma hh hrz hd hor =>
    obtain ⟨m', h1, h2, h3, h4, kd, val, hor', hx⟩ := g38_ldar (H := H) F hm hinv.core
      hinv.slots (kread_of_reads hreads) (kldar_kStep (ldar_ne hop).1 hh hty hc0) hpre.2 hj hj'
      hop hsz hk0 hty hc0 hao hma hh hd hor hvs htemp hs
    refine fin m' h1 h2 h3 h4 ?_
    rw [uStep35_ldar hop]
    simp only [homeRegs, hh]
    exact uokl_one hL hor' hx
  | @sel0 c r t0 hop hsz hc0 hu htc hct hhc hvh hrz hd hob hcls hcl =>
    obtain ⟨cv, hcv⟩ := Option.isSome_iff_exists.1 hcls
    have hKr : ∀ c0, Gen.Check.cls (lc.ty v.id) = some c0 → K.get r = some c0 := fun c0 hc0' => by
      have h0 : Gen.Check.cls t0 = some c0 := hcl.trans hc0'
      exact ksel38_of_reads hreads hop hc0 hhc (by rw [htc]; simpa [tupleTys] using h0)
    obtain ⟨m', h1, h2, h3, h4, hx⟩ := g38_sel0 (H := H) F hm hinv.core hinv.slots
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hc0 htc hhc hvh hrz hd hob hcv hcl
      hKr hvs htemp hs
    refine fin m' h1 h2 h3 h4 ?_
    rw [uStep35_selLdar (.inl hop) hc0 hu]
    exact fun e he => uok_of_x hx (hL e he)
  | sel1 hop hsz hc0 hu htc hct hhc hmt hhn =>
    have hpc : E.pcOf bid (i + 1) = E.pcOf bid i := by rw [hj', hj, hvs]
    obtain ⟨m', h1, h2, h3, h4, hx⟩ := g38_sel1 (H := H) F hm hinv.core hinv.slots
      (knext_kStep fun _ => (hs_none hhn).noRegs) hpc hop hsz hc0 htc hct hhc hmt hhn htemp hs
    refine fin m' h1 h2 h3 h4 ?_
    rw [uStep35_selLdar (.inr hop) hc0 hu]
    exact fun e he => uok_of_x hx (hL e he)

/-- **G38, values.** `g37_value`'s statement over `checkG38`, under the per-value premise
`G38Pre` (`G14Pre`, and an acquire load reads valid bytes). -/
theorem g38_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG38 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hu : UOKL m (uL35 lc (uIn35 lc bid) blk i))
    (hpre : G38Pre lc s v)
    (hcall : CallOK H E g L lc s s' v m) (hcallz : CallOKZ H E g L lc s s' v m)
    (hicall : ICallOK H E L ret lc s s' v m)
    (hwb : WbOK H E g L lc s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hmeq : MemEqOK H E g L lc s v m) (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' ∧
      UOKL m' (uL35 lc (uIn35 lc bid) blk (i + 1)) := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    obtain ⟨E', m', hx, hE', h1, h2, h3, -⟩ := g33_value (checkG33_of_38 hl hc) hE hbid hb hi hv
      hen hm hinv (by rw [uL31_nl hl]; intro e he; cases he) hpre.1 hcall hcallz hicall hwb hclo
      hgetg hmeq hs
    refine ⟨E', m', hx, hE', h1, h2, h3, ?_⟩
    rw [uL35_nl hl]
    intro e he
    cases he
  | true =>
  rw [uL35_succ hl hi hv]
  have hE0 := hE
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, hcf, hk, hlt, hnd, hblocks, -, hmovd, -⟩ :=
    checkG38_spec hl hc
  obtain ⟨b, j, js, e, next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk] at hkd
  obtain ⟨htemp, hVK⟩ := vkind38_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  rw [kAt_succ hi hv]
  exact vk38_step hE0 F hhome hcf hv hVK hvs htemp hj hj' hreads hm hinv hu
    (fun x hop hx => movdOK35_spec hmovd hbid hb hi hv hop hx)
    hpre hcall hcallz hicall hwb hclo hgetg hmeq hs

/-- A nil check of G38's kinds is G7's. -/
theorem vk38_nil {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK38 lc g v kd)
    (hop : v.op = .ARM64LoweredNilCheck) : VK7 lc g v kd := by
  cases h with
  | g37 _ _ h => exact vk37_nil h hop
  | ldar h => exact absurd hop (ldar_ne h).2.2.2.1
  | sel0 h => rw [hop] at h; cases h
  | sel1 h => rw [hop] at h; cases h

/-- **G38, nil panics.** `g37_nilPanic`'s statement over `checkG38`. -/
theorem g38_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG38 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  cases hl : lc.ctx.f.lowered with
  | false => exact g33_nilPanic (checkG33_of_38 hl hc) hE hbid hb hi hv hop hm hinv hs
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, -⟩ :=
    checkG38_spec hl hc
  obtain ⟨b, j, js, e', next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk] at hkd
  obtain ⟨-, hVK⟩ := vkind38_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases vk38_nil hVK hop with
  | g6 hne _ => exact absurd hop hne
  | nil _ hsz2 _ _ hao hma =>
    exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma hvs hs

/-- **G38, bounds panics.** `g37_boundsPanic`'s statement over `checkG38`, under `BoundsOK`. -/
theorem g38_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG38 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hbok : BoundsOK H g L ps.toList)
    (hs : stepLoc env lc s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    exact g33_boundsPanic (checkG33_of_38 hl hc) hE hbid hb hi hv hop hm hinv hbok hs
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, hsyms, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, hpb, -, -⟩ :=
    checkG38_spec hl hc
  obtain ⟨b, j, js, e', next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk] at hkd
  have hen : entryOp24 v.op = false := by
    rcases pbOp_cases hop with h | h | h | h <;> rw [h] <;> rfl
  obtain ⟨-, hVK⟩ := vkind38_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases hVK with
  | ldar h => rw [(ldar_ne h).2.2.2.2.1] at hop; cases hop
  | sel0 h => rw [h] at hop; cases hop
  | sel1 h => rw [h] at hop; cases hop
  | g37 _ _ hVK37 =>
  cases hVK37 with
  | bin h => rw [(aluOp37_ne (aluOp37_bin h)).2.2.2.2] at hop; cases hop
  | un h => rw [(aluOp37_ne (aluOp37_un h)).2.2.2.2] at hop; cases hop
  | madd h => rw [(aluOp37_ne (aluOp37_madd h)).2.2.2.2] at hop; cases hop
  | sbfx h => rw [h] at hop; cases hop
  | g36 _ _ _ _ _ hVK36 =>
  cases hVK36 with
  | g33 _ _ _ hVK33 =>
    cases hVK33 with
    | g32 _ _ _ _ hVK32 =>
      cases hVK32 with
      | g28 _ _ _ _ _ hVK28 =>
        exact vk28_boundsPanic F hsyms hpb hrow hb hi hv hVK28 hvs hj hreads hop hm hinv hbok hs
      | bin h =>
        rw [(aluOp32_ne (aluOp32_bin h)).2.2.2.2] at hop; cases hop
      | binK h =>
        rw [(aluOp32_ne (aluOp32_binK h)).2.2.2.2] at hop; cases hop
      | un h =>
        rw [(aluOp32_ne (aluOp32_un h)).2.2.2.2] at hop; cases hop
      | csinc h => rw [h] at hop; cases hop
      | stlr h => rw [(stlr_ne (lc := c.cx.lc) h).2.2.2.2.1] at hop; cases hop
    | un h => rw [(aluOp33_ne (aluOp33_un h)).2.2.2.2] at hop; cases hop
    | ubfiz h => rw [h] at hop; cases hop
    | sra h => rw [h] at hop; cases hop
    | cmnw h => rw [h] at hop; cases hop
  | sh h => rw [(aluOp36_ne (aluOp36_sh h)).2.2.2.2] at hop; cases hop
  | shOp h => rw [(aluOp36_ne (aluOp36_shOp h)).2.2.2.2] at hop; cases hop
  | tst h => rw [h] at hop; cases hop

/-- **G38, terminators.** `g37_term`'s statement over `checkG38`. -/
theorem g38_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG38 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (hu : UOKL m (uL35 lc (uIn35 lc bid) blk blk.values.size))
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList ∧ UOKL m' (uIn35 lc e.b) := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g33_term (checkG33_of_38 hl hc) hE hbid hb hm hinv hpre
      (by rw [uL31_nl hl]; intro e he; cases he) ht
    refine ⟨m', h1, h2, h3, h4, ?_⟩
    rw [uIn35_nl hl]
    intro e he
    cases he
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, hedges⟩ :=
    checkG38_spec hl hc
  obtain ⟨m', h1, h2, h3, h4, he, hx⟩ := termK_stepX hpcOf
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb hm hinv hpre ht
  refine ⟨m', h1, h2, h3, h4, fun x hxin => ?_⟩
  exact uok_of_x hx (hu x (uEdgesOK35_edge hedges hbid hb he x hxin))

end GoFV.Proof.Gen

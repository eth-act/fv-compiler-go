import GoFV.Proof.Gen.G4
import GoFV.Proof.Gen.Spec5
import GoFV.Proof.Gen.Step5

/-!
# Soundness of the genssa validator's slice G5: memory markers (`docs/plans/proofs3.md` §4)

`g5_value`: when `checkG5` accepts a function with the class table `kt`, every value of a block
(other than the entry values) run by `runLoc` from a state related by `LocMatch` to a machine
state, whose registers hold values of the classes the table gives before that value (`G3Inv` at
`kAt lc kt b blk i`), is matched by `runProg` steps of genssa's P0 Progs to a state related before
the next value, with the registers at the classes before the next value. `g5_term`: a terminator
that goes to a successor is matched by steps to a state related before the successor's first
value, with the registers at the classes of the successor's start (`kt.at`).

The activation, the invariant and the per-value premises are G4's (`G2Env`, `G3Inv`, `G4Pre`).
G4's values go through `vk4_step`; G5's own are the memory markers (`g5_mark`), which emit no code
and change only Phase 1's memory: `VarDef` poisons a block (`memInj_poison`), `WBend` frees the
write-barrier buffer (`memInj_free`), `VarLive` and `KeepAlive` keep the memory.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm

/-! ## Memories with fewer or poisoned bytes -/

section MemSub

variable {ι : Blk → Option (BitVec 64)}

private theorem find?_mem5 {m : Mem} {b : Blk} {al : Alloc} (h : m.find? b = some al) :
    (b, al) ∈ m.blocks := by
  unfold Mem.find? at h
  cases hf : m.blocks.find? (·.1 == b) with
  | none => rw [hf] at h; cases h
  | some e =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    have h1 := Array.mem_of_find?_eq_some hf
    have h2 := Array.find?_some hf
    obtain ⟨b', al'⟩ := e
    simp only [beq_iff_eq] at h2
    subst h2
    exact h1

/-- Every block of `m'` is one of `m`'s of the same size, each byte unchanged or poison. -/
def MemSub (m m' : Mem) : Prop :=
  ∀ b al2, (b, al2) ∈ m'.blocks → ∃ al1, (b, al1) ∈ m.blocks ∧ al1.data.size = al2.data.size ∧
    ∀ i (h2 : i < al2.data.size) (h1 : i < al1.data.size),
      al2.data[i] = .poison ∨ al2.data[i] = al1.data[i]

/-- `MemInj` survives fewer blocks and poisoned bytes (under `AddrAgree`, which makes every byte
of a live block related, so the pointer words can be forgotten). -/
theorem memInj_sub (hA : AddrAgree ι) {m m' : Mem} {mm : Memory} (h : MemInj ι m mm)
    (hs : MemSub m m') : MemInj ι m' mm := by
  refine ⟨h.nil, ?_, ?_, ⟨fun _ _ => False, ?_⟩⟩
  · intro b al2 hb
    obtain ⟨al1, hb1, hsz, -⟩ := hs b al2 hb
    rw [← hsz]; exact h.mapped b al1 hb1
  · intro b al2 b' al2' a2 a2' hb hb' hne h1 h2
    obtain ⟨al1, hb1, hsz, -⟩ := hs b al2 hb
    obtain ⟨al1', hb1', hsz', -⟩ := hs b' al2' hb'
    rw [← hsz, ← hsz']; exact h.inj b al1 b' al1' a2 a2' hb1 hb1' hne h1 h2
  · intro b al2 a hb hι
    refine ⟨fun o ho => ho.elim, fun o _ ho => ho.elim, fun i hi _ => ?_⟩
    obtain ⟨al1, hb1, hsz, hby⟩ := hs b al2 hb
    have hi1 : i < al1.data.size := by rw [hsz]; exact hi
    rcases hby i hi hi1 with he | he
    · rw [he]; trivial
    · rw [he]; exact memInj_byteRel hA h hb1 hι hi1

/-- `SepFrom` survives fewer blocks of the same sizes. -/
theorem sepFrom_sub {P : BitVec 64 → Prop} {m m' : Mem} (h : SepFrom ι P m) (hs : MemSub m m') :
    SepFrom ι P m' := by
  intro b al a hb hι y hy
  obtain ⟨al1, hb1, hsz, -⟩ := hs b al hb
  rw [← hsz]; exact h b al1 a hb1 hι y hy

theorem memSub_refl (m : Mem) : MemSub m m :=
  fun _ al hb => ⟨al, hb, rfl, fun _ _ _ => .inr rfl⟩

/-- A poisoned block (`VarDef`): the same blocks and keys, one block's bytes poison. -/
theorem memSub_poison {m : Mem} (hk : KeysNodup m) (b : Blk) :
    MemSub m (m.poisonBlock b) ∧ KeysNodup (m.poisonBlock b) := by
  unfold Mem.poisonBlock
  cases hf : m.find? b with
  | none => exact ⟨memSub_refl m, hk⟩
  | some al =>
  simp only
  have hmem := find?_mem5 hf
  unfold Mem.set
  cases hi : m.blocks.findIdx? (·.1 == b) with
  | none =>
    have := Array.findIdx?_eq_none_iff.1 hi _ hmem
    simp at this
  | some idx =>
  simp only
  obtain ⟨hidx, hkey, -⟩ := Array.findIdx?_eq_some_iff_getElem.1 hi
  simp only [beq_iff_eq] at hkey
  generalize hal' : ({ al with data := Array.replicate al.data.size Byte.poison } : Alloc) = al'
  have hlist : (m.blocks.set! idx (b, al')).toList = m.blocks.toList.set idx (b, al') := by
    rw [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
  refine ⟨fun b2 al2 hb => ?_, ?_⟩
  · simp only [Array.mem_def] at hb
    rw [hlist] at hb
    rcases List.mem_or_eq_of_mem_set hb with hb | hb
    · exact ⟨al2, Array.mem_def.2 hb, rfl, fun _ _ _ => .inr rfl⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hb
      subst hal'
      refine ⟨al, hmem, by simp, fun i h2 _ => .inl ?_⟩
      simp
  · unfold KeysNodup at hk ⊢
    simp only
    rw [hlist, List.map_set]
    have hl : idx < (m.blocks.toList.map (·.1)).length := by simp [hidx]
    have := List.set_getElem_self hl
    rw [List.getElem_map, Array.getElem_toList, hkey] at this
    rw [this]; exact hk

/-- A freed block (`WBend`): the other blocks unchanged. -/
theorem memSub_free {m : Mem} (hk : KeysNodup m) (b : Blk) :
    MemSub m (m.free b) ∧ KeysNodup (m.free b) := by
  refine ⟨fun b2 al2 hb => ⟨al2, (Array.mem_filter.1 hb).1, rfl, fun _ _ _ => .inr rfl⟩, ?_⟩
  unfold KeysNodup at hk ⊢
  simp only [Mem.free, Array.toList_filter]
  exact hk.sublist (List.filter_sublist.map _)

end MemSub

/-! ## The memory markers -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- A memory marker (`VarDef`, `VarLive`, `KeepAlive`, `WBend`) emits no code: the machine state
stays, related to the state with the marker's memory. -/
theorem g5_mark (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {n : Nat} (hop : markOp? v.op = some n) (hsz : v.args.size = n)
    (hmt : memTy (lc.ty v.id) = true) (hhn : lc.home v.id = none) (hma : memArg lc v (n - 1) = .ok ())
    (hvs : j' = j) (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  obtain ⟨a, ha, hamt, hah⟩ := memArg_spec hma
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨mm0, hmm0, hk0, hsep0⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  obtain ⟨mm', rfl, hmm'⟩ := stepLoc_mark hl htemp hop hsz hmt hhn ha (read_mem hl hah hamt hmm) hs
  obtain ⟨hsub, hk'⟩ : MemSub mm mm' ∧ KeysNodup mm' := by
    rcases hmm' with rfl | ⟨b', rfl⟩ | rfl
    · exact ⟨memSub_refl _, hk0⟩
    · exact memSub_poison hk0 b'
    · exact memSub_free hk0 _
  refine ⟨m, .refl, ⟨hm.regs, hm.flags, hm.slots, ⟨mm', rfl, memInj_sub F.addr hMI hsub⟩,
    hm.frame, ?_⟩, ?_, hsi⟩
  · rw [hm.pc, hj, hj', hvs]
  · exact (⟨hinv.regs, ⟨mm', rfl, hk', sepFrom_sub hsep0 hsub⟩⟩ :
      CoreInv E.ι (StkAt E) K { s with mem := .mem mm' }).mono
      (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun))

end Cases

/-! ## The theorems -/

/-- **G5, values.** A value (not an entry value) of a function `checkG5` accepted with the class
table `kt`, run by `runLoc` from a state related by `LocMatch` to a machine state whose registers
hold values of the classes the table gives before the value (`G3Inv` at `kAt … i`), is matched by
`runProg` steps of genssa's P0 Progs to a state related before the next value, with the registers
at the classes before the next value, under an activation `E'` that extends `E`'s injection (by
the callee's, at a call) and is again a `G2Env`. At a static call the callee's behaviour is the
trusted contract `CallOK`. -/
theorem g5_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG5 lc ps bstart g = .ok (tab, kt)) (hE : G2Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp3 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hpre : G4Pre lc s v)
    (hcall : CallOK H E g L lc s s' v m) (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G2Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' := by
  have hE0 := hE
  obtain ⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome4, hcf, hk, hlt, hnd, hblocks⟩ := checkG5_spec hc
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
  obtain ⟨htemp, hVK⟩ := vkind5_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home4 hhome4, hnd, hlt, hret, hA⟩
  rw [kAt_succ hi hv]
  cases hVK with
  | g4 _ hVK4 =>
    exact vk4_step hE0 F hhome4 hcf hv hVK4 hvs htemp hj hj' hreads hm hinv hpre hcall hs
  | mark hop hsz hmt hhn hma =>
    obtain ⟨m', h1, h2, h3, h4⟩ := g5_mark (H := H) F hm hinv.core hinv.slots
      (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hop hsz hmt hhn hma hvs htemp hs
    exact ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE0, h1, h2, ⟨h3, h4⟩⟩

/-- **G5, terminators.** A terminator of a function `checkG5` accepted with the class table `kt`
that goes to a successor, from a state whose registers hold the classes of the block's end, is
matched by `runProg` steps to a state related before the successor's first value, with the
registers at the classes of the successor's start (`kt.at`); an `Exit` block never goes to one. -/
theorem g5_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG5 lc ps bstart g = .ok (tab, kt)) (hE : G2Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList := by
  obtain ⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome4, -, hk, hlt, hnd, hblocks⟩ := checkG5_spec hc
  exact termK_step hpcOf ⟨hl, clsReg_of_home4 hhome4, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb
    hm hinv hpre ht

end GoFV.Proof.Gen

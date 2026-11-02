import GoFV.Proof.Pass.MemCombineSound

/-!
# memcombine: target descriptions are complete (issue #35)

`symOf_complete`: if the bytes of a target description (`symOf … true _`) are defined and its loads
valid at the values of `den` at fuel `m`, the value of `x` at fuel `m + N` is the integer of those
bytes. The target drops an opaque value's byte only while keeping another byte of the same value,
whose definedness makes the value an integer of its shape's width (`symOf_vbw`); every memory
byte lies in one of the description's loads (`symOf_backed`). So the bytes an op drops are
defined too (`semL_dropped`) and its arguments are integers.
-/

namespace GoFV.Proof.MemCombine

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.MemCombine.Check GoFV.Opt.RewriteCheck GoFV.Proof.Term
open GoFV.Proof.AtomSim

/-! ## Memory bytes lie in loads -/

theorem isMb_zeros {s : SB} {k : Nat} (h : s ∈ zeros k) : s.isMb = false := by
  unfold zeros at h
  rw [List.eq_of_mem_replicate h]; rfl

theorem symOp_backed {tabs : Tables} {D : ID → Option Value} {tgt wide : Bool} {rec : ID → Option Desc}
    (hrec : ∀ a r, rec a = some r → Backed r.1 r.2) {v : Value} {wt : Width} {r : Desc}
    (h : symOp tabs D tgt wide rec v wt = some r) : Backed r.1 r.2 := by
  have hsub : ∀ {l l' : List SB} {sd : List LoadRec}, Backed l sd →
      (∀ s ∈ l', s.isMb = true → s ∈ l) → Backed l' sd := fun hl hs => hl.sub hs fun _ h => h
  rcases symOp_cases h with ⟨w', hw, hsz, rfl⟩ | ⟨ho, hsz, hr⟩ | ⟨ho, hl⟩ |
    ⟨w1, w2, a, hw, hsz, ha, rfl⟩ | ⟨w1, w2, a, hw, hsz, ha, hk⟩ | ⟨w1, hw, hl⟩ | ⟨w1, hw, hl⟩ |
    ⟨w1, a, hw, hsz, ha, rfl⟩ | ⟨w1, hw, ho⟩
  · intro m b i o hm
    simp [litBytes] at hm
  · exact hrec _ _ hr
  · obtain ⟨-, -, -, rfl⟩ := symLoad_spec hl
    intro m b i o hm
    simp only [List.mem_map, List.mem_range, SB.mb.injEq] at hm
    obtain ⟨k, hk, rfl, rfl, rfl, rfl⟩ := hm
    exact ⟨_, List.mem_singleton_self _, rfl, rfl, rfl, by dsimp only; omega, by dsimp only; omega⟩
  · refine hsub (l := a.1) (hrec _ _ (symArg_spec ha).1) fun s hs hm => ?_
    rcases List.mem_append.1 hs with hs | hs
    · exact hs
    · rw [isMb_zeros hs] at hm; cases hm
  · obtain ⟨rfl, -⟩ := keepB_spec hk
    exact hsub (l := a.1) (hrec _ _ (symArg_spec ha).1) fun s hs _ => List.mem_of_mem_take hs
  · obtain ⟨k, a, -, -, ha, hkp⟩ := symLsh_spec hl
    obtain ⟨rfl, -⟩ := keepB_spec hkp
    refine hsub (l := a.1) (hrec _ _ (symArg_spec ha).1) fun s hs hm => ?_
    rcases List.mem_append.1 hs with hs | hs
    · rw [isMb_zeros hs] at hm; cases hm
    · exact List.mem_of_mem_take hs
  · obtain ⟨k, a, -, -, ha, hkp⟩ := symRsh_spec hl
    obtain ⟨rfl, -⟩ := keepB_spec hkp
    refine hsub (l := a.1) (hrec _ _ (symArg_spec ha).1) fun s hs hm => ?_
    rcases List.mem_append.1 hs with hs | hs
    · exact List.mem_of_mem_drop hs
    · rw [isMb_zeros hs] at hm; cases hm
  · exact hsub (l := a.1) (hrec _ _ (symArg_spec ha).1) fun s hs _ => List.mem_reverse.1 hs
  · obtain ⟨a, b, c, -, ha, hb, hc, rfl⟩ := symOr_spec ho
    have h1 := hrec _ _ (symArg_spec ha).1
    have h2 := hrec _ _ (symArg_spec hb).1
    intro m bb i o hm
    rcases orBytes_ids hc _ hm with hs | hs | ⟨x, hx⟩
    · obtain ⟨l, hl, hl'⟩ := h1 m bb i o hs
      exact ⟨l, List.mem_append_left _ hl, hl'⟩
    · obtain ⟨l, hl, hl'⟩ := h2 m bb i o hs
      exact ⟨l, List.mem_append_right _ hl, hl'⟩
    · cases hx

/-- **Every memory byte of a description lies in one of its loads.** -/
theorem symOf_backed {tabs : Tables} {D : ID → Option Value} {tgt wide : Bool} :
    ∀ {N : Nat} {x : ID} {r : Desc}, symOf tabs D tgt wide N x = some r → Backed r.1 r.2
  | 0, _, _, h => by cases h
  | N + 1, x, r, h => by
    obtain ⟨v, wt, -, -, hc | rfl⟩ := symOf_succ_spec h
    · obtain ⟨r', ho, -, hk⟩ := hc
      obtain ⟨rfl, -⟩ := keepB_spec hk
      exact (symOp_backed (fun _ _ h => symOf_backed h) ho).sub
        (fun s hs _ => List.mem_of_mem_take hs) fun _ h => h
    · intro m b i o hm
      simp at hm

/-! ## Opaque bytes lie in their values' shapes -/

theorem VbW.sub {tabs : Tables} {D : ID → Option Value} {l l' : List SB} (h : VbW tabs D l)
    (hs : ∀ y k, SB.vb y k ∈ l' → SB.vb y k ∈ l) : VbW tabs D l' :=
  fun y k hm => h y k (hs y k hm)

theorem vb_not_mem_zeros {y : ID} {k n : Nat} : SB.vb y k ∉ zeros n := by
  unfold zeros
  simp [List.mem_replicate]

theorem symOp_vbw {tabs : Tables} {D : ID → Option Value} {tgt wide : Bool} {rec : ID → Option Desc}
    (hrec : ∀ a r, rec a = some r → VbW tabs D r.1) {v : Value} {wt : Width} {r : Desc}
    (h : symOp tabs D tgt wide rec v wt = some r) : VbW tabs D r.1 := by
  rcases symOp_cases h with ⟨w', hw, hsz, rfl⟩ | ⟨ho, hsz, hr⟩ | ⟨ho, hl⟩ |
    ⟨w1, w2, a, hw, hsz, ha, rfl⟩ | ⟨w1, w2, a, hw, hsz, ha, hk⟩ | ⟨w1, hw, hl⟩ | ⟨w1, hw, hl⟩ |
    ⟨w1, a, hw, hsz, ha, rfl⟩ | ⟨w1, hw, ho⟩
  · intro y k hm
    simp [litBytes] at hm
  · exact hrec _ _ hr
  · obtain ⟨-, -, -, rfl⟩ := symLoad_spec hl
    intro y k hm
    simp at hm
  · refine (hrec _ _ (symArg_spec ha).1).sub fun y k hs => ?_
    rcases List.mem_append.1 hs with hs | hs
    · exact hs
    · exact absurd hs vb_not_mem_zeros
  · obtain ⟨rfl, -⟩ := keepB_spec hk
    exact (hrec _ _ (symArg_spec ha).1).sub fun _ _ hs => List.mem_of_mem_take hs
  · obtain ⟨k, a, -, -, ha, hkp⟩ := symLsh_spec hl
    obtain ⟨rfl, -⟩ := keepB_spec hkp
    refine (hrec _ _ (symArg_spec ha).1).sub fun y k hs => ?_
    rcases List.mem_append.1 hs with hs | hs
    · exact absurd hs vb_not_mem_zeros
    · exact List.mem_of_mem_take hs
  · obtain ⟨k, a, -, -, ha, hkp⟩ := symRsh_spec hl
    obtain ⟨rfl, -⟩ := keepB_spec hkp
    refine (hrec _ _ (symArg_spec ha).1).sub fun y k hs => ?_
    rcases List.mem_append.1 hs with hs | hs
    · exact List.mem_of_mem_drop hs
    · exact absurd hs vb_not_mem_zeros
  · exact (hrec _ _ (symArg_spec ha).1).sub fun _ _ hs => List.mem_reverse.1 hs
  · obtain ⟨a, b, c, -, ha, hb, hc, rfl⟩ := symOr_spec ho
    intro y k hm
    rcases orBytes_ids hc _ hm with hs | hs | ⟨x, hx⟩
    · exact hrec _ _ (symArg_spec ha).1 y k hs
    · exact hrec _ _ (symArg_spec hb).1 y k hs
    · cases hx

/-- **Every opaque byte `vb y k` of a description is a byte of `y`'s integer shape.** -/
theorem symOf_vbw {tabs : Tables} {D : ID → Option Value} {tgt wide : Bool} :
    ∀ {N : Nat} {x : ID} {r : Desc}, symOf tabs D tgt wide N x = some r →
      ∀ y k, SB.vb y k ∈ r.1 → ∃ v wy, D y = some v ∧ intW (tabs.ty v.type) = some wy ∧ k < wy.bytes
  | 0, _, _, h => by cases h
  | N + 1, x, r, h => by
    obtain ⟨v, wt, hD, hty, hc | rfl⟩ := symOf_succ_spec h
    · obtain ⟨r', ho, -, hk⟩ := hc
      obtain ⟨rfl, -⟩ := keepB_spec hk
      exact (symOp_vbw (fun _ _ h => symOf_vbw h) ho).sub fun _ _ hs => List.mem_of_mem_take hs
    · intro y k hm
      simp only [List.mem_map, List.mem_range, SB.vb.injEq] at hm
      obtain ⟨k', hk, rfl, rfl⟩ := hm
      exact ⟨v, wt, hD, by rw [hty]; rfl, hk⟩

/-! ## Completeness -/

theorem concrete_list {bs : Array Byte} (hc : Concrete bs) :
    ∃ xs : List (BitVec 8), bs.toList = xs.map .b := by
  refine ⟨bs.toList.map fun x => match x with | .b b => b | _ => 0, ?_⟩
  rw [List.map_map]
  conv => lhs; rw [← List.map_id bs.toList]
  apply List.map_congr_left
  intro x hx
  obtain ⟨b, rfl⟩ := hc x hx
  rfl

/-- The memory bytes of a load read from concrete bytes are the integer's. -/
theorem mbs_sem {V : ID → Val} {mm b : ID} {i : Option ID} {o : _root_.Int} {wt : Width}
    {M : Mem} {P : Ptr} {I : BitVec 64} {bs : Array Byte} {xs : List (BitVec 8)}
    (hm : V mm = .mem M) (hp : (V b).asPtrWord = some P) (hI : idxVal V i = some I)
    (hrd : M.read (ptrAt P I o) wt.bytes = some bs) (hxs : bs.toList = xs.map .b)
    {Y : BitVec wt.bits} (hY : ∀ k (hk : k < wt.bytes), byteOf Y.toNat k = xs[k]'(by
      have := congrArg List.length hxs; have := read_size hrd
      simp only [Array.length_toList, List.length_map] at *; omega)) :
    semL V ((List.range wt.bytes).map fun (k : Nat) => SB.mb mm b i (o + (k : _root_.Int))) =
      some (bytesOf wt Y) := by
  unfold bytesOf
  refine semL_map_range _ _ fun j hj => mb_sem hm hp hI hrd (by omega) (by omega) ?_
  have hl : j < xs.length := by
    have := congrArg List.length hxs; have := read_size hrd
    simp only [Array.length_toList, List.length_map] at *; omega
  rw [show (o + (j : _root_.Int) - o).toNat = j by omega, ← Array.getElem?_toList, hxs,
    List.getElem?_map, List.getElem?_eq_getElem hl, hY j hj]
  rfl

theorem shift_int (w : Width) (b : Bool) (F : BitVec w.bits → Nat → BitVec w.bits)
    (A : BitVec w.bits) {S : BitVec 64} (hS : S.toNat < w.bits) :
    Shift.shift w .w64 b F [.int w A, .int .w64 S] = .int w (F A S.toNat) := by
  simp only [Shift.shift, Val.asInt_int]
  rw [if_neg (by simp; omega), Nat.min_eq_left (by omega)]

section
variable {E : ID → Option Value} {tabs : Tables} {ρ : ID → Val} {wide : Bool}

/-- The bytes a target description drops are defined: an opaque byte's value has a kept byte
defined, so it is an integer of its shape's width (`VbW`), and memory bytes lie in valid loads. -/
theorem semL_dropped (hT : Term.Typed E tabs ρ) {m : Nat} {kept dropped : List SB}
    {sd : List LoadRec} {B : List (BitVec 8)} (hB : semL (den E tabs ρ m) kept = some B)
    (hk : ∀ y k, SB.vb y k ∈ dropped → ∃ k', SB.vb y k' ∈ kept) (hw : VbW tabs E dropped)
    (hb : Backed dropped sd) (hl : ∀ r ∈ sd, LoadOK (den E tabs ρ m) r) :
    ∃ C, semL (den E tabs ρ m) dropped = some C := by
  refine semL_of_backed (fun y k hy => ?_) hb hl
  obtain ⟨k', hk'⟩ := hk y k hy
  obtain ⟨v, wy, hD, hwy, hlt⟩ := hw y k hy
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 hk'
  obtain ⟨c, hc, -⟩ := semL_getElem? hB n _ hn
  have hty := den_hasTy hT hD m
  rw [intW_eq hwy] at hty
  simp only [SB.sem] at hc
  unfold byte? at hc
  split at hc
  · rename_i w X hx
    rw [hx] at hty
    simp only [Val.hasTy, beq_iff_eq] at hty
    subst hty
    exact ⟨byteOf X.toNat k, by simp only [hx, byte?, hlt, ite_true]⟩
  · cases hc

theorem width_eq_of_bytesOf {w w' : Width} {X : BitVec w.bits} {l : List SB} {B : List (BitVec 8)}
    (h : bytesOf w X = B) (hl : l.length = w'.bytes) {V : ID → Val} (hs : semL V l = some B) :
    w = w' := by
  apply width_eq_of_bytes
  have := semL_length hs
  rw [← h, bytesOf_length] at this
  omega

/-- **One op**: the integer result of an op whose target description is defined. -/
theorem symOp_complete (hT : Term.Typed E tabs ρ) {m n : Nat} (hmn : m ≤ n)
    {rec : ID → Option Desc}
    (hrec : ∀ a r B, rec a = some r → semL (den E tabs ρ m) r.1 = some B →
      (∀ l ∈ r.2, LoadOK (den E tabs ρ m) l) → ∃ w X, den E tabs ρ n a = .int w X ∧ bytesOf w X = B)
    (hbk : ∀ a r, rec a = some r → Backed r.1 r.2) (hvw : ∀ a r, rec a = some r → VbW tabs E r.1)
    {v : Value} {wt : Width} {r : Desc} (h : symOp tabs E true wide rec v wt = some r)
    {B : List (BitVec 8)} (hB : semL (den E tabs ρ m) r.1 = some B)
    (hL : ∀ l ∈ r.2, LoadOK (den E tabs ρ m) l) :
    ∃ w0 Y, evalPure v.op (.int wt) v.auxInt v.aux (v.args.toList.map (den E tabs ρ n)) =
      .int w0 Y ∧ bytesOf w0 Y = B := by
  rcases symOp_cases h with ⟨w', hw, hsz, rfl⟩ | ⟨ho, hsz, hr⟩ | ⟨ho, hl⟩ |
    ⟨w1, w2, a, hw, hsz, ha, rfl⟩ | ⟨w1, w2, a, hw, hsz, ha, hk⟩ | ⟨w1, hw, hl⟩ | ⟨w1, hw, hl⟩ |
    ⟨w1, a, hw, hsz, ha, rfl⟩ | ⟨w1, hw, ho⟩
  · -- a constant
    rw [(constW_spec hw).2.2]
    rw [semL_lits] at hB
    cases hB
    exact ⟨w', _, rfl, rfl⟩
  · -- `Copy`
    rw [ho, args_one hsz]
    exact hrec _ _ _ hr hB hL
  · -- `Load`
    obtain ⟨hsz, -, -, rfl⟩ := symLoad_spec hl
    rw [ho, args_two hsz]
    generalize splitP tabs E 64 v.args[0]! none 0 = S at hB hL
    obtain ⟨b, i, o⟩ := S
    obtain ⟨M, P, I, bs, hm, hp, hI, hq, hrd, hc⟩ := hL _ (List.mem_singleton_self _)
    dsimp only at hm hp hI hq hrd hB
    have hq' := den_lift_ptr hmn hq
    obtain ⟨M', hm', hMM⟩ := refines_mem (hm ▸ den_fuel_mono E tabs ρ m n v.args[1]! hmn)
    obtain ⟨bs', hrd', hbs⟩ := Mem.Refines.read hMM hrd
    rw [concrete_mono hbs hc] at hrd'
    obtain ⟨xs, hxs⟩ := concrete_list hc
    have hlen : xs.length = wt.bytes := by
      have := congrArg List.length hxs; have := read_size hrd
      simp only [Array.length_toList, List.length_map] at *; omega
    obtain ⟨Y, hY, hYb⟩ := decodeInt_concrete hxs hlen
    refine ⟨wt, Y, ?_, ?_⟩
    · change loadOp (.int wt) [den E tabs ρ n v.args[0]!, den E tabs ρ n v.args[1]!] = _
      rw [hm']
      simp only [loadOp, hq']
      change M'.load (.int wt) (ptrAt P I o) = _
      rw [load_int, hrd']
      dsimp only
      rw [Nat.zero_add, ← read_size hrd, Array.extract_size, hY]
    · rw [mbs_sem hm hp hI hrd hxs hYb] at hB
      cases hB; rfl
  · -- `ZeroExt`
    obtain ⟨-, -, hle, hev⟩ := zextW_spec hw
    obtain ⟨hra, hla⟩ := symArg_spec ha
    rw [hev, args_one hsz]
    obtain ⟨A, Z, hA, hZ, rfl⟩ := semL_append.1 hB
    rw [semL_zeros] at hZ; cases hZ
    obtain ⟨w, X, hX, hXb⟩ := hrec _ _ _ hra hA hL
    cases width_eq_of_bytesOf hXb hla hA
    refine ⟨w2, X.setWidth w2.bits, by rw [hX]; simp [Conv.zeroExt, Sem.int1], ?_⟩
    rw [bytesOf_zext X hle, hXb]
  · -- `Trunc`
    obtain ⟨-, -, hle, hev⟩ := truncW_spec hw
    obtain ⟨hra, hla⟩ := symArg_spec ha
    obtain ⟨rfl, hnv⟩ := keepB_spec hk
    rw [hev, args_one hsz]
    obtain ⟨C, hC⟩ := semL_dropped hT hB (hnv rfl)
      ((hvw _ _ hra).sub fun _ _ hs => List.mem_of_mem_drop hs)
      ((hbk _ _ hra).sub (fun s hs _ => List.mem_of_mem_drop hs) fun _ h => h) hL
    have hA : semL (den E tabs ρ m) a.1 = some (B ++ C) := by
      rw [← List.take_append_drop w2.bytes a.1]; exact semL_append.2 ⟨_, _, hB, hC, rfl⟩
    obtain ⟨w, X, hX, hXb⟩ := hrec _ _ _ hra hA hL
    cases width_eq_of_bytesOf hXb hla hA
    refine ⟨w2, X.setWidth w2.bits, by rw [hX]; simp [Conv.trunc, Sem.int1], ?_⟩
    rw [bytesOf_trunc X hle, hXb]
    have := semL_length hB
    simp only [List.length_take] at this
    rw [List.take_left' (by omega)]
  · -- `Lsh`
    obtain ⟨-, -, hev⟩ := lshW_spec hw
    obtain ⟨k, a, hsz, hk, ha, hkp⟩ := symLsh_spec hl
    obtain ⟨hra, hla⟩ := symArg_spec ha
    obtain ⟨rfl, hnv⟩ := keepB_spec hkp
    obtain ⟨c, hc, hc0, hck, hkw⟩ := shiftBytes_spec hk
    rw [hev, args_two hsz]
    obtain ⟨Z, B1, hZ, hB1, rfl⟩ := semL_append.1 hB
    rw [semL_zeros] at hZ; cases hZ
    obtain ⟨C, hC⟩ := semL_dropped hT hB (hnv rfl)
      ((hvw _ _ hra).sub fun _ _ hs => List.mem_of_mem_drop hs)
      ((hbk _ _ hra).sub (fun s hs _ => List.mem_of_mem_drop hs) fun _ h => h) hL
    have hA : semL (den E tabs ρ m) a.1 = some (B1 ++ C) := by
      rw [← List.take_append_drop (w1.bytes - k) a.1]; exact semL_append.2 ⟨_, _, hB1, hC, rfl⟩
    obtain ⟨w, X, hX, hXb⟩ := hrec _ _ _ hra hA hL
    cases width_eq_of_bytesOf hXb hla hA
    cases n with
    | zero => cases hX
    | succ n =>
    rw [den_const64 hc]
    have hS : (BitVec.ofInt 64 c).toNat = 8 * k := by
      rw [toNat_ofInt_small hc0 (by have := bytes_le_eight w1; have := width_bits_eq w1; omega)]; omega
    rw [hX]
    refine ⟨w1, _, shift_int w1 _ (fun x n => x <<< n) X (by omega), ?_⟩
    have hkb : k ≤ w1.bytes := by have := width_bits_eq w1; omega
    rw [hS, bytesOf_shl X hkb, hXb]
    have := semL_length hB1
    simp only [List.length_take] at this
    rw [List.take_left' (by omega)]
  · -- `Rsh…U`
    obtain ⟨-, -, hev⟩ := rshuW_spec hw
    obtain ⟨k, a, hsz, hk, ha, hkp⟩ := symRsh_spec hl
    obtain ⟨hra, hla⟩ := symArg_spec ha
    obtain ⟨rfl, hnv⟩ := keepB_spec hkp
    obtain ⟨c, hc, hc0, hck, hkw⟩ := shiftBytes_spec hk
    rw [hev, args_two hsz]
    obtain ⟨B1, Z, hB1, hZ, rfl⟩ := semL_append.1 hB
    rw [semL_zeros] at hZ; cases hZ
    obtain ⟨C, hC⟩ := semL_dropped hT hB (hnv rfl)
      ((hvw _ _ hra).sub fun _ _ hs => List.mem_of_mem_take hs)
      ((hbk _ _ hra).sub (fun s hs _ => List.mem_of_mem_take hs) fun _ h => h) hL
    have hA : semL (den E tabs ρ m) a.1 = some (C ++ B1) := by
      rw [← List.take_append_drop k a.1]; exact semL_append.2 ⟨_, _, hC, hB1, rfl⟩
    obtain ⟨w, X, hX, hXb⟩ := hrec _ _ _ hra hA hL
    cases width_eq_of_bytesOf hXb hla hA
    cases n with
    | zero => cases hX
    | succ n =>
    rw [den_const64 hc]
    have hS : (BitVec.ofInt 64 c).toNat = 8 * k := by
      rw [toNat_ofInt_small hc0 (by have := bytes_le_eight w1; have := width_bits_eq w1; omega)]; omega
    rw [hX]
    refine ⟨w1, _, shift_int w1 _ (fun x n => x >>> n) X (by omega), ?_⟩
    have hkb : k ≤ w1.bytes := by have := width_bits_eq w1; omega
    rw [hS, bytesOf_ushr X hkb, hXb]
    have := semL_length hC
    simp only [List.length_take] at this
    rw [List.drop_left' (by omega)]
  · -- `Bswap`
    obtain ⟨-, -, hev⟩ := bswapW_spec hw
    obtain ⟨hra, hla⟩ := symArg_spec ha
    rw [hev, args_one hsz]
    have hA := semL_reverse hB
    rw [List.reverse_reverse] at hA
    obtain ⟨w, X, hX, hXb⟩ := hrec _ _ _ hra hA hL
    cases width_eq_of_bytesOf hXb hla hA
    refine ⟨w1, BitVec.ofNat w1.bits (Int.bswapNat (w1.bits / 8) X.toNat), by rw [hX]; simp [Sem.Int.bswap, Sem.int1], ?_⟩
    rw [bytesOf_bswap X, hXb, List.reverse_reverse]
  · -- `Or`
    obtain ⟨-, -, hev⟩ := orW_spec hw
    obtain ⟨a, b, c, hsz, ha, hb, hc, rfl⟩ := symOr_spec ho
    obtain ⟨hra, hla⟩ := symArg_spec ha
    obtain ⟨hrb, hlb⟩ := symArg_spec hb
    rw [hev, args_two hsz]
    obtain ⟨A, B', hA, hB'⟩ := orBytes_def hc hB
    obtain ⟨w, X, hX, hXb⟩ := hrec _ _ _ hra hA fun l hl => hL l (List.mem_append_left _ hl)
    obtain ⟨w', Y, hY, hYb⟩ := hrec _ _ _ hrb hB' fun l hl => hL l (List.mem_append_right _ hl)
    cases width_eq_of_bytesOf hXb hla hA
    cases width_eq_of_bytesOf hYb hlb hB'
    refine ⟨_, X ||| Y, by rw [hX, hY]; simp [Sem.Int.or, Sem.int2], ?_⟩
    have := orBytes_sem hc hA hB'
    rw [hB] at this
    cases this
    rw [bytesOf_or, hXb, hYb]

/-- **Completeness of the target's descriptions**: a description whose bytes are defined and
whose loads are valid at the values of fuel `m` describes, at fuel `m + N`, the integer of those
bytes. -/
theorem symOf_complete (hT : Term.Typed E tabs ρ) (m : Nat) : ∀ (N : Nat) (x : ID) (r : Desc)
    (B : List (BitVec 8)), symOf tabs E true wide N x = some r → semL (den E tabs ρ m) r.1 = some B →
    (∀ l ∈ r.2, LoadOK (den E tabs ρ m) l) → ∃ w X, den E tabs ρ (m + N) x = .int w X ∧ bytesOf w X = B
  | 0, _, _, _, h, _, _ => by cases h
  | N + 1, x, r, B, h, hB, hL => by
    obtain ⟨v, wt, hD, hty, hc | rfl⟩ := symOf_succ_spec h
    · obtain ⟨r', ho, hle, hk⟩ := hc
      obtain ⟨rfl, hnv⟩ := keepB_spec hk
      obtain ⟨ht, hfr⟩ := symOp_term ho
      have hbk := symOp_backed (fun _ _ h => symOf_backed h) ho
      have hvw := symOp_vbw (fun _ _ h => symOf_vbw h) ho
      obtain ⟨C, hC⟩ := semL_dropped hT hB (hnv rfl) (hvw.sub fun _ _ hs => List.mem_of_mem_drop hs)
        (hbk.sub (fun s hs _ => List.mem_of_mem_drop hs) fun _ h => h) hL
      have hA : semL (den E tabs ρ m) r'.1 = some (B ++ C) := by
        rw [← List.take_append_drop wt.bytes r'.1]; exact semL_append.2 ⟨_, _, hB, hC, rfl⟩
      obtain ⟨w0, Y, hY, hYb⟩ := symOp_complete hT (Nat.le_add_right m N)
        (fun a r B hr hB hL => symOf_complete hT m N a r B hr hB hL)
        (fun _ _ h => symOf_backed h) (fun _ _ h => symOf_vbw h) ho hA hL
      have hlen : wt.bytes ≤ w0.bytes := by
        have := semL_length hA; rw [← hYb, bytesOf_length] at this; omega
      refine ⟨wt, Y.setWidth wt.bits, ?_, ?_⟩
      · rw [← Nat.add_assoc, den_term hD ht hfr, hty, hY]
        show (if wt.bits ≤ w0.bits then Val.int wt (Y.setWidth wt.bits) else .poison) = _
        rw [if_pos (bits_le_of_bytes hlen)]
      · rw [bytesOf_trunc Y hlen, hYb]
        have := semL_length hB
        simp only [List.length_take] at this
        rw [List.take_left' (by omega)]
    · obtain ⟨c, hc, -⟩ := semL_getElem? hB 0 (.vb x 0) (by simp [bytes_pos])
      simp only [SB.sem] at hc
      unfold byte? at hc
      split at hc
      · rename_i w X hx
        have hty' := den_hasTy hT hD m
        rw [hty, hx] at hty'
        simp only [Val.hasTy, beq_iff_eq] at hty'
        subst hty'
        refine ⟨w, X, den_lift_int (by omega) hx, ?_⟩
        have : semL (den E tabs ρ m) ((List.range w.bytes).map (.vb x)) = some (bytesOf w X) := by
          unfold bytesOf
          exact semL_map_range _ _ fun k hk => by simp only [SB.sem, hx, byte?, hk, ite_true]
        rw [hB] at this
        cases this; rfl
      · cases hc

end

end GoFV.Proof.MemCombine

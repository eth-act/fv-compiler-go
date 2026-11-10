import GoFV.SSA.Sem.Pure
import GoFV.SSA.Sem.Layout

/-!
# Values without frame pointers agree under every address assignment (proofs3 §8, item 6)

The admissible address assignments (`Addrs`) agree on the blocks that are not frame blocks
(`nil` at 0, `heap n` at `(n + 1)·2^40`, globals and the write-barrier buffer without an
address: `Addrs.baseOf_*`) and on the decoding below `2^62` (`Addrs.decode_low`). So on a value
that holds no pointer into a frame block (`Val.lowB`: no `local`, `temp` or `outargs` pointer, also
not in the bytes of a memory or blob), the readers of the assignment give the same result under
any two instances `A` and `B`: `Ptr.convertible`, `Ptr.word`, `Val.retype`, `Val.hasTy`,
`Mem.load` (`*_agree`). `evalPure_agree` adds the integers an op reads as pointers
(`decodeOp`): below `2^62` (`opGuard`), where the decoding is the same.

This is what the checkers rely on (`GoFV.Proof.Rules.opValC`): they evaluate constants at
`Addrs.fixed` and accept a constant only on such values, so their verdicts hold under every
instance.
-/

namespace GoFV.SSA.Sem

/-! ## Values without frame pointers -/

/-- `p` points into no frame block (`local`, `temp`, `outargs`). -/
def Ptr.lowB (p : Ptr) : Bool :=
  match p.blk with
  | .local _ _ | .temp _ _ | .outargs _ => false
  | _ => true

/-- A byte that is no fragment of a frame pointer. -/
def Byte.lowB : Byte → Bool
  | .frag p _ => p.lowB
  | _ => true

/-- A memory none of whose bytes is a fragment of a frame pointer. -/
def Mem.lowB (m : Mem) : Bool := m.blocks.all fun e => e.2.data.all Byte.lowB

mutual
/-- `v` holds no pointer into a frame block (`Ptr.lowB`), also not in its memories' or blobs'
bytes. -/
def Val.lowB : Val → Bool
  | .ptr p => p.lowB
  | .mem m => m.lowB
  | .tuple vs => Val.lowBs vs
  | .agg vs => Val.lowBs vs
  | .blob bs => bs.all Byte.lowB
  | _ => true
/-- Every value of the list is `Val.lowB`. -/
def Val.lowBs : List Val → Bool
  | [] => true
  | v :: vs => v.lowB && Val.lowBs vs
end

/-- A 64-bit integer, which an op may read as a pointer (`Val.asPtrWord`, `PtrOps.wordRes`),
lies below `2^62`, where every instance decodes it alike (`Addrs.decode_low`). -/
def Val.wordLow : Val → Bool
  | .int .w64 x => decide (x.toNat < 2 ^ 62)
  | _ => true

/-- `Val.wordLow`, and of a composite its first component (`EqInter`/`EqSlice` compare the
first words, `PtrOps.eqFirst`). -/
def Val.firstLow : Val → Bool
  | .agg (v :: _) => v.wordLow
  | v => v.wordLow

/-- The ops whose value decodes an integer argument as a pointer (`Val.asPtrWord`,
`PtrOps.wordRes`). -/
def decodeOp : Op → Bool
  | .OffPtr | .AddPtr | .PtrIndex | .SubPtr | .EqPtr | .NeqPtr | .EqInter | .NeqInter | .EqSlice
  | .NeqSlice | .Load | .Dereference | .MemEq | .AtomicLoad8 | .AtomicLoad32 | .AtomicLoad64
  | .AtomicLoadPtr | .AtomicLoadAcq32 | .AtomicLoadAcq64 => true
  | _ => false

/-- The ops whose value reads the address assignment: `decodeOp`, `Convert` and `SelectNAddr`
(`Ptr.word`, `Ptr.convertible`). -/
def addrOp (op : Op) : Bool := decodeOp op || op == .Convert || op == .SelectNAddr

/-- The arguments of `op` are no integers from `2^62` up that it reads as pointers. -/
def opGuard (op : Op) (args : List Val) : Bool := !decodeOp op || args.all Val.firstLow

/-! ## Pointers -/

section Agree

variable {A B : Addrs}

theorem Blk.base?_agree {b : Blk} (h : (⟨b, 0⟩ : Ptr).lowB = true) :
    @Blk.base? A b = @Blk.base? B b := by
  cases b <;> simp only [Ptr.lowB, Bool.false_eq_true] at h <;>
    simp only [Blk.base?, @Addrs.baseOf_nil A, @Addrs.baseOf_nil B, @Addrs.baseOf_heap A,
      @Addrs.baseOf_heap B, @Addrs.baseOf_global A, @Addrs.baseOf_global B, @Addrs.baseOf_wbuf A,
      @Addrs.baseOf_wbuf B]

theorem Ptr.addr?_agree {p : Ptr} (h : p.lowB = true) : @Ptr.addr? A p = @Ptr.addr? B p := by
  obtain ⟨b, off⟩ := p
  have hb : (⟨b, 0⟩ : Ptr).lowB = true := h
  simp only [Ptr.addr?, Blk.base?_agree (A := A) (B := B) hb]

theorem Ptr.ofAddr_agree {x : BitVec 64} (h : x.toNat < 2 ^ 62) :
    @Ptr.ofAddr A x = @Ptr.ofAddr B x := by
  simp only [Ptr.ofAddr, @Addrs.decode_low A x h, @Addrs.decode_low B x h]

theorem Ptr.ofAddr_ne_agree {C : Addrs} {x : BitVec 64} (h : ¬ x.toNat < 2 ^ 62) {p : Ptr}
    (hp : p.lowB = true) : (@Ptr.ofAddr C x == p) = false := by
  obtain ⟨a, ha | ⟨k, ha⟩⟩ := @Addrs.decode_high C x (by omega) <;>
  · simp only [beq_eq_false_iff_ne, ne_eq]
    intro he
    rw [← he] at hp
    simp [Ptr.lowB, Ptr.ofAddr, ha] at hp

theorem Ptr.convertible_agree {p : Ptr} (h : p.lowB = true) :
    @Ptr.convertible A p = @Ptr.convertible B p := by
  unfold Ptr.convertible
  rw [Ptr.addr?_agree (A := A) (B := B) h]
  cases @Ptr.addr? B p with
  | none => rfl
  | some x =>
    simp only
    by_cases hl : x.toNat < 2 ^ 62
    · rw [Ptr.ofAddr_agree (A := A) (B := B) hl]
    · rw [Ptr.ofAddr_ne_agree hl h, Ptr.ofAddr_ne_agree hl h]

theorem Ptr.held_agree {p : Ptr} (h : p.lowB = true) : @Ptr.held A p = @Ptr.held B p := by
  simp only [Ptr.held, Ptr.convertible_agree (A := A) (B := B) h]

theorem Ptr.word_agree {p : Ptr} (h : p.lowB = true) : @Ptr.word A p = @Ptr.word B p := by
  simp only [Ptr.word, Ptr.convertible_agree (A := A) (B := B) h, Ptr.addr?_agree (A := A) (B := B) h]

theorem Ptr.lowB_add {p : Ptr} (k : BitVec 64) (h : p.lowB = true) : (p.add k).lowB = true := h

/-- The pointer a value reads as (`Val.asPtrWord`) on a value without a frame pointer and an
integer below `2^62`. -/
theorem Val.asPtrWord_agree {v : Val} (h : v.lowB = true) (hw : v.wordLow = true) :
    @Val.asPtrWord A v = @Val.asPtrWord B v := by
  unfold Val.asPtrWord
  split
  · rfl
  · rename_i x
    simp only [Val.wordLow, decide_eq_true_eq] at hw
    rw [Ptr.ofAddr_agree (A := A) (B := B) hw]
  · rfl

/-- `Val.asPtrWord` of such a value has no frame pointer. -/
theorem Val.asPtrWord_lowB {v : Val} {p : Ptr} (h : v.lowB = true) (hw : v.wordLow = true)
    (hp : @Val.asPtrWord A v = some p) : p.lowB = true := by
  unfold Val.asPtrWord at hp
  split at hp
  · cases hp; exact h
  · rename_i x
    cases hp
    simp only [Val.wordLow, decide_eq_true_eq] at hw
    simp only [Ptr.ofAddr, @Addrs.decode_low A x hw]
    unfold Ptr.fixedOfAddr
    simp only
    split
    · rfl
    · rfl
  · cases hp

/-! ## Bytes, memory, loads -/

/-- Every byte of `bs` is `Byte.lowB`. -/
def LowBytes (bs : Array Byte) : Prop := ∀ b ∈ bs, b.lowB = true

theorem LowBytes.of_all {bs : Array Byte} (h : bs.all Byte.lowB = true) : LowBytes bs :=
  fun b hb => Array.all_eq_true_iff_forall_mem.1 h b hb

theorem LowBytes.extract {bs : Array Byte} (h : LowBytes bs) (i j : Nat) :
    LowBytes (bs.extract i j) := by
  intro b hb
  obtain ⟨k, hk, rfl⟩ := Array.mem_extract_iff_getElem.1 hb
  exact h _ (Array.getElem_mem _)

theorem bytesPtr?_lowB {bs : Array Byte} (h : LowBytes bs) {p : Ptr} (hp : bytesPtr? bs = some p) :
    p.lowB = true := by
  unfold bytesPtr? at hp
  revert hp
  cases h0 : (bs[0]? : Option Byte) with
  | none => simp
  | some b =>
    cases b with
    | frag q i =>
      cases i with
      | zero =>
        simp only
        split
        · intro hp
          cases hp
          rw [Array.getElem?_eq_some_iff] at h0
          obtain ⟨hi, he⟩ := h0
          exact h _ (he ▸ Array.getElem_mem hi)
        · simp
      | succ => simp
    | _ => simp

theorem decodeInt_agree {bs : Array Byte} (h : LowBytes bs) (w : Width) :
    @decodeInt A w bs = @decodeInt B w bs := by
  unfold decodeInt
  split
  · rfl
  · split
    · rename_i p hp
      rw [Ptr.word_agree (A := A) (B := B) (bytesPtr?_lowB h hp)]
    · rfl

theorem decodePtr_agree {bs : Array Byte} (h : LowBytes bs) :
    @decodePtr A bs = @decodePtr B bs := by
  unfold decodePtr
  split
  · rename_i p hp
    rw [Ptr.word_agree (A := A) (B := B) (bytesPtr?_lowB h hp)]
  · rfl

mutual
theorem decode_agree {bs : Array Byte} (h : LowBytes bs) (off : Nat) :
    ∀ t : Ty, @decode A bs off t = @decode B bs off t
  | .int w => by simp only [decode]; exact decodeInt_agree (h.extract _ _) w
  | .bool => by simp only [decode]
  | .ptr _ => by simp only [decode]; exact decodePtr_agree (h.extract _ _)
  | .agg fs _ => by simp only [decode]; rw [decodeFields_agree h off fs]
  | .blob _ => by simp only [decode]
  | .empty => by simp only [decode]
  | .str => by
    simp only [decode, decodePtr_agree (A := A) (B := B) (h.extract _ _),
      decodeInt_agree (A := A) (B := B) (h.extract _ _)]
  | .slice _ => by
    simp only [decode, decodePtr_agree (A := A) (B := B) (h.extract _ _),
      decodeInt_agree (A := A) (B := B) (h.extract _ _)]
  | .opaque _ | .other | .mem | .tuple _ => by simp only [decode]
theorem decodeFields_agree {bs : Array Byte} (h : LowBytes bs) (off : Nat) :
    ∀ fs : List (Nat × Ty), @decodeFields A bs off fs = @decodeFields B bs off fs
  | [] => by simp only [decodeFields]
  | (o, t) :: fs => by
    simp only [decodeFields, decode_agree h (off + o) t, decodeFields_agree h off fs]
end

mutual
theorem decodeLoad_agree {bs : Array Byte} (h : LowBytes bs) (off : Nat) :
    ∀ t : Ty, @decodeLoad A bs off t = @decodeLoad B bs off t
  | .agg fs _ => by simp only [decodeLoad]; rw [decodeLoadFields_agree h off fs]
  | .int _ | .bool | .ptr _ | .blob _ | .opaque _ | .str | .slice _ => by
    simp only [decodeLoad, decode_agree (A := A) (B := B) h]
  | .empty | .other | .mem | .tuple _ => by simp only [decodeLoad]
theorem decodeLoadFields_agree {bs : Array Byte} (h : LowBytes bs) (off : Nat) :
    ∀ fs : List (Nat × Ty), @decodeLoadFields A bs off fs = @decodeLoadFields B bs off fs
  | [] => by simp only [decodeLoadFields]
  | (o, t) :: fs => by
    simp only [decodeLoadFields, decodeLoad_agree h (off + o) t, decodeLoadFields_agree h off fs]
end

theorem Mem.read_lowB {m : Mem} (hm : m.lowB = true) {p : Ptr} {n : Nat} {bs : Array Byte}
    (h : m.read p n = some bs) : LowBytes bs := by
  unfold Mem.read at h
  by_cases hn : (n == 0) = true
  · simp only [hn, ite_true, pure, Option.some.injEq] at h
    subst h; intro b hb; simp at hb
  · simp only [hn, Bool.false_eq_true, ite_false] at h
    cases ha : m.find? p.blk with
    | none => simp [ha] at h
    | some a =>
      simp only [ha, bind, Option.bind] at h
      split at h
      · cases h
        apply LowBytes.extract
        unfold Mem.find? at ha
        simp only [Option.map_eq_some_iff] at ha
        obtain ⟨e, he, rfl⟩ := ha
        exact LowBytes.of_all
          (Array.all_eq_true_iff_forall_mem.1 hm e (Array.mem_of_find?_eq_some he))
      · cases h

theorem Mem.load_agree {m : Mem} (hm : m.lowB = true) (t : Ty) (p : Ptr) :
    @Mem.load A m t p = @Mem.load B m t p := by
  unfold Mem.load
  split
  any_goals rfl
  · split
    · rename_i bs hbs
      exact decodeLoad_agree (Mem.read_lowB hm hbs) 0 _
    · rfl

/-! ## Shapes -/

theorem Val.lowBs_cons {v : Val} {vs : List Val} (h : Val.lowBs (v :: vs) = true) :
    v.lowB = true ∧ Val.lowBs vs = true := by
  simpa [Val.lowBs] using h

theorem Val.retypePtr_agree {v : Val} (h : v.lowB = true) :
    @Val.retypePtr A v = @Val.retypePtr B v := by
  cases v with
  | int w x => cases w <;> rfl
  | ptr p => exact Ptr.word_agree h
  | _ => rfl

theorem Val.retypeI64_agree {v : Val} (h : v.lowB = true) :
    @Val.retypeI64 A v = @Val.retypeI64 B v := by
  cases v with
  | ptr p => exact Ptr.word_agree h
  | _ => rfl

theorem Val.isPtrWord_agree {v : Val} (h : v.lowB = true) :
    @Val.isPtrWord A v = @Val.isPtrWord B v := by
  cases v with
  | int w x => cases w <;> rfl
  | ptr p => exact Ptr.held_agree h
  | _ => rfl

mutual
/-- `Val.retype` on a value without frame pointers agrees under any two instances. -/
theorem Val.retype_agree (t : Ty) : ∀ v : Val, v.lowB = true →
    @Val.retype A t v = @Val.retype B t v
  | .int w x, _ => by cases t <;> cases w <;> rfl
  | .bool _, _ => by cases t <;> rfl
  | .mem _, _ => by cases t <;> rfl
  | .tuple vs, h => by
    cases t with
    | tuple ts =>
      simp only [Val.retype]
      rw [Val.retypePre_agree ts vs (by simpa [Val.lowB] using h)]
    | _ => rfl
  | .ptr p, h => by
    cases t with
    | int w => cases w <;> first | rfl | exact Ptr.word_agree h
    | ptr _ => exact Ptr.word_agree h
    | _ => rfl
  | .agg vs, h => by
    have hl : Val.lowBs vs = true := by simpa [Val.lowB] using h
    cases t with
    | agg fs n =>
      simp only [Val.retype]
      rw [Val.retypeFields_agree fs vs hl]
    | str =>
      match vs, hl with
      | [p, l], hl =>
        obtain ⟨hp, hl⟩ := Val.lowBs_cons hl
        obtain ⟨hl, -⟩ := Val.lowBs_cons hl
        simp only [Val.retype, Val.retypePtr_agree (A := A) (B := B) hp,
          Val.retypeI64_agree (A := A) (B := B) hl]
      | [], _ | [_], _ | _ :: _ :: _ :: _, _ => rfl
    | slice e =>
      match vs, hl with
      | [p, l, c], hl =>
        obtain ⟨hp, hl⟩ := Val.lowBs_cons hl
        obtain ⟨hl, hc⟩ := Val.lowBs_cons hl
        obtain ⟨hc, -⟩ := Val.lowBs_cons hc
        simp only [Val.retype, Val.retypePtr_agree (A := A) (B := B) hp,
          Val.retypeI64_agree (A := A) (B := B) hl, Val.retypeI64_agree (A := A) (B := B) hc]
      | [], _ | [_], _ | [_, _], _ | _ :: _ :: _ :: _ :: _, _ => rfl
    | _ => rfl
  | .blob _, _ => by cases t <;> rfl
  | .empty, _ => by cases t <;> rfl
  | .poison, _ => by cases t <;> rfl
theorem Val.retypePre_agree : ∀ (ts : List Ty) (vs : List Val), Val.lowBs vs = true →
    @Val.retypePre A ts vs = @Val.retypePre B ts vs
  | [], _, _ => rfl
  | t :: ts, v :: vs, h => by
    obtain ⟨h1, h2⟩ := Val.lowBs_cons h
    simp only [Val.retypePre, Val.retype_agree t v h1, Val.retypePre_agree ts vs h2]
  | _ :: _, [], _ => rfl
theorem Val.retypeFields_agree : ∀ (fs : List (Nat × Ty)) (vs : List Val), Val.lowBs vs = true →
    @Val.retypeFields A fs vs = @Val.retypeFields B fs vs
  | [], [], _ => rfl
  | (_, t) :: fs, v :: vs, h => by
    obtain ⟨h1, h2⟩ := Val.lowBs_cons h
    simp only [Val.retypeFields, Val.retype_agree t v h1, Val.retypeFields_agree fs vs h2]
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
end

mutual
/-- `Val.hasTy` on a value without frame pointers agrees under any two instances. -/
theorem Val.hasTy_agree (t : Ty) : ∀ v : Val, v.lowB = true →
    @Val.hasTy A v t = @Val.hasTy B v t
  | .int w x, _ => by cases t <;> cases w <;> rfl
  | .bool _, _ => by cases t <;> rfl
  | .mem _, _ => by cases t <;> rfl
  | .tuple vs, h => by
    cases t with
    | tuple ts =>
      simp only [Val.hasTy]
      rw [Val.hasTyPre_agree vs ts (by simpa [Val.lowB] using h)]
    | _ => rfl
  | .ptr p, h => by
    cases t with
    | int w => cases w <;> first | rfl | exact Ptr.held_agree h
    | ptr _ => exact Ptr.held_agree h
    | _ => rfl
  | .agg vs, h => by
    have hl : Val.lowBs vs = true := by simpa [Val.lowB] using h
    have hh : (vs.head?.all fun v => @Val.isPtrWord A v) = vs.head?.all fun v => @Val.isPtrWord B v := by
      cases vs with
      | nil => rfl
      | cons v vs =>
        simp only [List.head?_cons, Option.all_some]
        exact Val.isPtrWord_agree (Val.lowBs_cons hl).1
    cases t with
    | agg fs n =>
      simp only [Val.hasTy]
      rw [Val.hasTyList_agree vs _ hl]
    | str => simp only [Val.hasTy, hh]
    | slice e => simp only [Val.hasTy, hh]
    | _ => rfl
  | .blob _, _ => by cases t <;> rfl
  | .empty, _ => by cases t <;> rfl
  | .poison, _ => by cases t <;> rfl
theorem Val.hasTyList_agree : ∀ (vs : List Val) (ts : List Ty), Val.lowBs vs = true →
    @Val.hasTyList A vs ts = @Val.hasTyList B vs ts
  | [], [], _ => rfl
  | v :: vs, t :: ts, h => by
    obtain ⟨h1, h2⟩ := Val.lowBs_cons h
    simp only [Val.hasTyList, Val.hasTy_agree t v h1, Val.hasTyList_agree vs ts h2]
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
theorem Val.hasTyPre_agree : ∀ (vs : List Val) (ts : List Ty), Val.lowBs vs = true →
    @Val.hasTyPre A vs ts = @Val.hasTyPre B vs ts
  | _, [], _ => by cases ‹List Val› <;> rfl
  | v :: vs, t :: ts, h => by
    obtain ⟨h1, h2⟩ := Val.lowBs_cons h
    simp only [Val.hasTyPre, Val.hasTy_agree t v h1, Val.hasTyPre_agree vs ts h2]
  | [], _ :: _, _ => rfl
end

/-! ## The pure ops -/

/-- Closes `f_A args = f_B args` for a family `f` that is `poison` on `args` once the value
`a` is cased (an integer also by its width). -/
local macro "agree_head " a:ident : tactic =>
  `(tactic| (cases $a:ident with | int w _ => cases w <;> rfl | _ => rfl))

/-- Closes `f_A args = f_B args` for a family `f` on argument lists of a shape `f` maps to
`poison`: both matches split, the impossible branches by their hypotheses. -/
local macro "agree_poison " f:ident : tactic =>
  `(tactic| (unfold $f:ident; split <;> (try split) <;> first | rfl | (exfalso; simp_all) | simp_all))

theorem Val.wordLow_int {x : BitVec 64} (h : (Val.int .w64 x).wordLow = true) :
    x.toNat < 2 ^ 62 := by
  simpa [Val.wordLow] using h

theorem Val.wordLow_of_firstLow {v : Val} (h : v.firstLow = true) : v.wordLow = true := by
  cases v with
  | agg vs => rfl
  | _ => exact h

theorem Val.lowBs_mem : ∀ {vs : List Val} {v : Val}, Val.lowBs vs = true → v ∈ vs →
    v.lowB = true
  | w :: ws, v, h, hm => by
    obtain ⟨h1, h2⟩ := Val.lowBs_cons h
    rcases List.mem_cons.1 hm with rfl | hm
    · exact h1
    · exact Val.lowBs_mem h2 hm

/-- The first value of `args`, and the second, with their guards. -/
theorem Val.all_cons₂ {p : Val → Bool} {a b : Val} {rest : List Val}
    (h : (a :: b :: rest).all p = true) : p a = true ∧ p b = true := by
  simp only [List.all_cons, Bool.and_eq_true] at h
  exact ⟨h.1, h.2.1⟩

theorem PtrOps.ptrRes_agree {p : Ptr} (h : p.lowB = true) :
    @PtrOps.ptrRes A p = @PtrOps.ptrRes B p := by
  simp only [PtrOps.ptrRes, Ptr.word_agree (A := A) (B := B) h]

theorem PtrOps.wordRes_agree {x : BitVec 64} (h : x.toNat < 2 ^ 62) (k : BitVec 64) :
    @PtrOps.wordRes A x k = @PtrOps.wordRes B x k := by
  simp only [PtrOps.wordRes, Ptr.ofAddr_agree (A := A) (B := B) h]

theorem PtrOps.offPtr_agree (ai : Int64) {args : List Val} (hl : Val.lowBs args = true)
    (hw : args.all Val.firstLow = true) : @PtrOps.offPtr A ai args = @PtrOps.offPtr B ai args := by
  match args, hl, hw with
  | [v], hl, hw =>
    have h1 := (Val.lowBs_cons hl).1
    have h2 : v.wordLow = true := Val.wordLow_of_firstLow (by simpa using hw)
    cases v with
    | ptr p => exact PtrOps.ptrRes_agree (Ptr.lowB_add _ h1)
    | int w x =>
      cases w
      case w64 => exact PtrOps.wordRes_agree (Val.wordLow_int h2) _
      all_goals rfl
    | _ => rfl
  | [], _, _ => rfl
  | a :: _ :: _, _, _ => agree_head a

theorem PtrOps.addPtr_agree {args : List Val} (hl : Val.lowBs args = true)
    (hw : args.all Val.firstLow = true) : @PtrOps.addPtr A args = @PtrOps.addPtr B args := by
  match args, hl, hw with
  | [v, i], hl, hw =>
    have h1 := (Val.lowBs_cons hl).1
    have h2 : v.wordLow = true := Val.wordLow_of_firstLow (Val.all_cons₂ hw).1
    cases v with
    | ptr p =>
      simp only [PtrOps.addPtr]
      cases asOffset i with
      | none => rfl
      | some k => exact PtrOps.ptrRes_agree (Ptr.lowB_add _ h1)
    | int w x =>
      cases w
      case w64 =>
        simp only [PtrOps.addPtr]
        cases asOffset i with
        | none => rfl
        | some k => exact PtrOps.wordRes_agree (Val.wordLow_int h2) _
      all_goals rfl
    | _ => rfl
  | [], _, _ => rfl
  | [a], _, _ => agree_head a
  | a :: _ :: _ :: _, _, _ => agree_head a

theorem PtrOps.ptrIndex_agree (elem : Option Nat) {args : List Val} (hl : Val.lowBs args = true)
    (hw : args.all Val.firstLow = true) :
    @PtrOps.ptrIndex A elem args = @PtrOps.ptrIndex B elem args := by
  match args, hl, hw with
  | [v, i], hl, hw =>
    have h1 := (Val.lowBs_cons hl).1
    have h2 : v.wordLow = true := Val.wordLow_of_firstLow (Val.all_cons₂ hw).1
    cases v with
    | ptr p =>
      simp only [PtrOps.ptrIndex]
      cases elem <;> cases asOffset i
      all_goals first | rfl | exact PtrOps.ptrRes_agree (Ptr.lowB_add _ h1)
    | int w x =>
      cases w
      case w64 =>
        simp only [PtrOps.ptrIndex]
        cases elem <;> cases asOffset i
        all_goals first | rfl | exact PtrOps.wordRes_agree (Val.wordLow_int h2) _
      all_goals rfl
    | _ => rfl
  | [], _, _ => rfl
  | [a], _, _ => agree_head a
  | a :: _ :: _ :: _, _, _ => agree_head a

theorem PtrOps.subPtr_agree {args : List Val} (hl : Val.lowBs args = true)
    (hw : args.all Val.firstLow = true) : @PtrOps.subPtr A args = @PtrOps.subPtr B args := by
  match args, hl, hw with
  | [a, b], hl, hw =>
    obtain ⟨ha, hl⟩ := Val.lowBs_cons hl
    obtain ⟨hb, -⟩ := Val.lowBs_cons hl
    have hwa := Val.wordLow_of_firstLow (Val.all_cons₂ hw).1
    have hwb := Val.wordLow_of_firstLow (Val.all_cons₂ hw).2
    simp only [PtrOps.subPtr]
    rw [Val.asPtrWord_agree (A := A) (B := B) ha hwa, Val.asPtrWord_agree (A := A) (B := B) hb hwb]
    cases hp : @Val.asPtrWord B a with
    | none => rfl
    | some p =>
      cases hq : @Val.asPtrWord B b with
      | none => rfl
      | some q =>
        simp only
        rw [Ptr.addr?_agree (A := A) (B := B) (Val.asPtrWord_lowB ha hwa hp),
          Ptr.addr?_agree (A := A) (B := B) (Val.asPtrWord_lowB hb hwb hq)]
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | _ :: _ :: _ :: _, _, _ => rfl

theorem PtrOps.eqPtr_agree (neg : Bool) {args : List Val} (hl : Val.lowBs args = true)
    (hw : args.all Val.firstLow = true) : @PtrOps.eqPtr A neg args = @PtrOps.eqPtr B neg args := by
  match args, hl, hw with
  | [a, b], hl, hw =>
    obtain ⟨ha, hl⟩ := Val.lowBs_cons hl
    obtain ⟨hb, -⟩ := Val.lowBs_cons hl
    simp only [PtrOps.eqPtr]
    rw [Val.asPtrWord_agree (A := A) (B := B) ha (Val.wordLow_of_firstLow (Val.all_cons₂ hw).1),
      Val.asPtrWord_agree (A := A) (B := B) hb (Val.wordLow_of_firstLow (Val.all_cons₂ hw).2)]
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | _ :: _ :: _ :: _, _, _ => rfl

theorem PtrOps.eqFirst_agree (neg : Bool) {args : List Val} (hl : Val.lowBs args = true)
    (hw : args.all Val.firstLow = true) :
    @PtrOps.eqFirst A neg args = @PtrOps.eqFirst B neg args := by
  match args, hl, hw with
  | [x, y], hl, hw =>
    obtain ⟨hx, hl⟩ := Val.lowBs_cons hl
    obtain ⟨hy, -⟩ := Val.lowBs_cons hl
    have hfx := (Val.all_cons₂ hw).1
    have hfy := (Val.all_cons₂ hw).2
    cases x with
    | agg as =>
      cases as with
      | nil => rfl
      | cons a as =>
        cases y with
        | agg bs =>
          cases bs with
          | nil => rfl
          | cons b bs =>
            have ha := (Val.lowBs_cons (by simpa [Val.lowB] using hx)).1
            have hb := (Val.lowBs_cons (by simpa [Val.lowB] using hy)).1
            simp only [PtrOps.eqFirst]
            rw [Val.asPtrWord_agree (A := A) (B := B) ha hfx,
              Val.asPtrWord_agree (A := A) (B := B) hb hfy]
        | _ => rfl
    | _ => rfl
  | [], _, _ => rfl
  | [_], _, _ => agree_poison PtrOps.eqFirst
  | _ :: _ :: _ :: _, _, _ => agree_poison PtrOps.eqFirst

theorem PtrOps.convert_agree (t : Ty) {args : List Val} (hl : Val.lowBs args = true) :
    @PtrOps.convert A t args = @PtrOps.convert B t args := by
  match args, hl with
  | [x, y], hl =>
    have h1 := (Val.lowBs_cons hl).1
    cases t with
    | int w =>
      cases w
      case w64 =>
        cases x with
        | ptr p =>
          simp only [PtrOps.convert, Ptr.convertible_agree (A := A) (B := B) h1,
            Ptr.addr?_agree (A := A) (B := B) h1]
        | _ => rfl
      all_goals rfl
    | _ => rfl
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: _ :: _ :: _, _ => rfl

theorem Tuple.selectNAddr_agree (ai : Int64) {args : List Val} (hl : Val.lowBs args = true) :
    @Tuple.selectNAddr A ai args = @Tuple.selectNAddr B ai args := by
  match args, hl with
  | [x], hl =>
    cases x with
    | tuple vs =>
      have hvs : Val.lowBs vs = true := by simpa [Val.lowB, Val.lowBs] using hl
      simp only [Tuple.selectNAddr]
      cases hg : vs.getLast? with
      | none => rfl
      | some v =>
        have hv := Val.lowBs_mem hvs (List.mem_of_getLast? hg)
        cases v with
        | agg addrs =>
          simp only
          split
          · rfl
          · cases ha : addrs[ai.toInt.toNat]? with
            | none => rfl
            | some a =>
              have hav := Val.lowBs_mem (by simpa [Val.lowB] using hv) (List.mem_of_getElem? ha)
              cases a with
              | ptr p => exact Ptr.word_agree hav
              | _ => rfl
        | _ => rfl
    | _ => rfl
  | [], _ => rfl
  | _ :: _ :: _, _ => agree_poison Tuple.selectNAddr

theorem loadOp_agree (t : Ty) {args : List Val} (hl : Val.lowBs args = true)
    (hw : args.all Val.firstLow = true) : @loadOp A t args = @loadOp B t args := by
  match args, hl, hw with
  | [a, b], hl, hw =>
    obtain ⟨ha, hl⟩ := Val.lowBs_cons hl
    obtain ⟨hb, -⟩ := Val.lowBs_cons hl
    cases b with
    | mem m =>
      simp only [loadOp]
      rw [Val.asPtrWord_agree (A := A) (B := B) ha (Val.wordLow_of_firstLow (Val.all_cons₂ hw).1)]
      cases @Val.asPtrWord B a with
      | none => rfl
      | some p => exact Mem.load_agree hb t p
    | _ => rfl
  | [], _, _ => rfl
  | [_], _, _ => agree_poison loadOp
  | _ :: _ :: _ :: _, _, _ => agree_poison loadOp

theorem atomicLoad_agree (t : Ty) {args : List Val} (hl : Val.lowBs args = true)
    (hw : args.all Val.firstLow = true) : @atomicLoad A t args = @atomicLoad B t args := by
  match args, hl, hw with
  | [a, b], hl, hw =>
    obtain ⟨ha, hl⟩ := Val.lowBs_cons hl
    obtain ⟨hb, -⟩ := Val.lowBs_cons hl
    cases b with
    | mem m =>
      simp only [atomicLoad]
      rw [Val.asPtrWord_agree (A := A) (B := B) ha (Val.wordLow_of_firstLow (Val.all_cons₂ hw).1)]
      split
      · simp only [Mem.load_agree (A := A) (B := B) hb]
      · rfl
    | _ => rfl
  | [], _, _ => rfl
  | [_], _, _ => agree_poison atomicLoad
  | _ :: _ :: _ :: _, _, _ => agree_poison atomicLoad

theorem memEq_agree {args : List Val} (hl : Val.lowBs args = true)
    (hw : args.all Val.firstLow = true) : @memEq A args = @memEq B args := by
  match args, hl, hw with
  | [x, y, z, w], hl, hw =>
    obtain ⟨hx, hl⟩ := Val.lowBs_cons hl
    obtain ⟨hy, -⟩ := Val.lowBs_cons hl
    cases z with
    | int _ n =>
      cases w with
      | mem m =>
        simp only [memEq]
        rw [Val.asPtrWord_agree (A := A) (B := B) hx (Val.wordLow_of_firstLow (Val.all_cons₂ hw).1),
          Val.asPtrWord_agree (A := A) (B := B) hy (Val.wordLow_of_firstLow (Val.all_cons₂ hw).2)]
      | _ => rfl
    | _ => rfl
  | [], _, _ => rfl
  | [_], _, _ => agree_poison memEq
  | [_, _], _, _ => agree_poison memEq
  | [_, _, _], _, _ => agree_poison memEq
  | _ :: _ :: _ :: _ :: _ :: _, _, _ => agree_poison memEq

theorem decodeOp_cases {op : Op} (h : decodeOp op = true) :
    op = .OffPtr ∨ op = .AddPtr ∨ op = .PtrIndex ∨ op = .SubPtr ∨ op = .EqPtr ∨ op = .NeqPtr ∨
    op = .EqInter ∨ op = .NeqInter ∨ op = .EqSlice ∨ op = .NeqSlice ∨ op = .Load ∨
    op = .Dereference ∨ op = .MemEq ∨ op = .AtomicLoad8 ∨ op = .AtomicLoad32 ∨
    op = .AtomicLoad64 ∨ op = .AtomicLoadPtr ∨ op = .AtomicLoadAcq32 ∨ op = .AtomicLoadAcq64 := by
  unfold decodeOp at h
  split at h <;> simp_all

/-- **`evalPure` agrees under any two instances** on arguments without frame pointers whose
integers that the op reads as pointers lie below `2^62` (`opGuard`). -/
theorem evalPure_agree (op : Op) (ty : Ty) (ai : Int64) (ax : Option AuxRef) {args : List Val}
    (hl : Val.lowBs args = true) (hg : opGuard op args = true) :
    @evalPure A op ty ai ax args = @evalPure B op ty ai ax args := by
  cases ha : addrOp op
  · cases op <;> first | exact absurd ha (by decide) | rfl
  · by_cases hd : decodeOp op = true
    · have hw : args.all Val.firstLow = true := by simpa [opGuard, hd] using hg
      rcases decodeOp_cases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact PtrOps.offPtr_agree ai hl hw
      · exact PtrOps.addPtr_agree hl hw
      · exact PtrOps.ptrIndex_agree _ hl hw
      · exact PtrOps.subPtr_agree hl hw
      · exact PtrOps.eqPtr_agree false hl hw
      · exact PtrOps.eqPtr_agree true hl hw
      · exact PtrOps.eqFirst_agree false hl hw
      · exact PtrOps.eqFirst_agree true hl hw
      · exact PtrOps.eqFirst_agree false hl hw
      · exact PtrOps.eqFirst_agree true hl hw
      · exact loadOp_agree ty hl hw
      · exact loadOp_agree ty hl hw
      · exact memEq_agree hl hw
      all_goals exact atomicLoad_agree ty hl hw
    · have hc : op = .Convert ∨ op = .SelectNAddr := by
        simp only [addrOp, Bool.or_eq_true, beq_iff_eq] at ha
        rcases ha with (ha | ha) | ha
        · exact absurd ha hd
        · exact .inl ha
        · exact .inr ha
      rcases hc with rfl | rfl
      · exact PtrOps.convert_agree ty hl
      · exact Tuple.selectNAddr_agree ai hl

end Agree

/-! ## The checkers' evaluation, at `Addrs.fixed`

The checkers evaluate at `Addrs.fixed` and take no instance, so their verdicts are those of every
instance; their soundness proofs move such a value to the instance at hand by `*_agree`. -/

/-- `Val.retype` as the checkers compute it: at `Addrs.fixed`. -/
def Val.retypeC (t : Ty) (v : Val) : Val := @Val.retype Addrs.fixed t v

/-- `Val.hasTy` as the checkers compute it: at `Addrs.fixed`. -/
def Val.hasTyC (v : Val) (t : Ty) : Bool := @Val.hasTy Addrs.fixed v t

/-- `Val.retypeI64` as the checkers compute it: at `Addrs.fixed`. -/
def Val.retypeI64C (v : Val) : Val := @Val.retypeI64 Addrs.fixed v

/-- `Mem.load` as the checkers compute it: at `Addrs.fixed`. -/
def Mem.loadC (m : Mem) (t : Ty) (p : Ptr) : Val := @Mem.load Addrs.fixed m t p

/-- `evalPure` as the checkers compute it: at `Addrs.fixed`, on arguments without frame pointers
whose pointer-read integers lie below `2^62` (`opGuard`), else `none`. -/
def evalPureC (op : Op) (ty : Ty) (ai : Int64) (ax : Option AuxRef) (args : List Val) :
    Option Val :=
  if Val.lowBs args && opGuard op args then some (@evalPure Addrs.fixed op ty ai ax args)
  else none

section Instance

variable [Addrs]

theorem Val.retypeC_eq {v : Val} (h : v.lowB = true) (t : Ty) : v.retypeC t = v.retype t :=
  (Val.retype_agree t v h).symm

theorem Val.hasTyC_eq {v : Val} (h : v.lowB = true) (t : Ty) : v.hasTyC t = v.hasTy t :=
  (Val.hasTy_agree t v h).symm

theorem Val.retypeI64C_eq {v : Val} (h : v.lowB = true) : v.retypeI64C = v.retypeI64 :=
  (Val.retypeI64_agree h).symm

theorem Mem.loadC_eq {m : Mem} (h : m.lowB = true) (t : Ty) (p : Ptr) : m.loadC t p = m.load t p :=
  (Mem.load_agree h t p).symm

theorem evalPureC_eq {op : Op} {ty : Ty} {ai : Int64} {ax : Option AuxRef} {args : List Val}
    {v : Val} (h : evalPureC op ty ai ax args = some v) : evalPure op ty ai ax args = v := by
  unfold evalPureC at h
  split at h
  · rename_i hg
    simp only [Bool.and_eq_true] at hg
    cases h
    exact evalPure_agree op ty ai ax hg.1 hg.2
  · cases h

/-- An evaluation with no arguments needs no guard. -/
theorem evalPureC_nil (op : Op) (ty : Ty) (ai : Int64) (ax : Option AuxRef) :
    evalPureC op ty ai ax [] = some (@evalPure Addrs.fixed op ty ai ax []) := by
  simp [evalPureC, Val.lowBs, opGuard]

end Instance

end GoFV.SSA.Sem

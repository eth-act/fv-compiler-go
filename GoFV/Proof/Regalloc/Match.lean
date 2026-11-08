import GoFV.Proof.Regalloc.Loc
import GoFV.Proof.EvalL
import GoFV.Proof.Pass.CopyFragL

variable [GoFV.SSA.Sem.Addrs]

/-!
# Regalloc checker soundness: the simulation relation (`docs/plans/regalloc-check.md` §5)

`Match cx env frA S fr s`: the source frame `fr` (`runSched` of `cx.f`) and the target state `s`
(`runLoc` of `cx.g`) of one activation `frA` agree on the facts `S`:

* a fact `(l, o)` (`FactOK`): `l` holds the source value of `o` (`srcVal`: a frame constant's
  value `kval`, any other value's register; component `o.comp`), exactly or, weakly, read at
  `o`'s shape; nothing is claimed while the source has no value for `o`;
* `(avail, v)`: `v`'s register is its evaluation on the current registers of its arguments;
* both frames are `frA` up to their registers, every source register has its value's shape, a
  frame constant's register is `none` or its value `kval`, the register file has its size.

`kval cx env frA id`: the value of frame constant `id`, its op evaluated on its arguments'
(`SP`/`SB`) values (`kvalN`).
-/

namespace GoFV.Proof.RA

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RegallocCheck

/-- The source's mode (`runSched`). -/
abbrev _root_.GoFV.Opt.RegallocCheck.Cx.md (cx : Cx) : LMode := LMode.sched cx.f

/-- The value of source value `id` evaluated on the values of its arguments, `n` levels deep
(frame constants: their arguments are `SP`/`SB`, which have none). -/
def kvalN (cx : Cx) (env : Env) (frA : Frame) : Nat → ID → Val
  | 0, _ => .poison
  | n + 1, id =>
    match cx.f.value? id with
    | some v =>
      match evalOpL true env cx.sc frA v (v.args.toList.map (kvalN cx env frA n)) (cx.fty id) with
      | .ok r => cx.md.retype (cx.fty id) r
      | _ => .poison
    | none => .poison

/-- The value of frame constant `id` in activation `frA`. -/
def kval (cx : Cx) (env : Env) (frA : Frame) (id : ID) : Val := kvalN cx env frA 2 id

/-- The source run's value of `id`: a frame constant's `kval`, any other value's register. -/
def srcVal (cx : Cx) (env : Env) (frA fr : Frame) (id : ID) : Option Val :=
  if cx.isK id then some (kval cx env frA id) else (fr.regs[id]?).join

/-- Fact `(l, o)` holds in the source frame `fr` and the target state `s`. -/
def FactOK (cx : Cx) (env : Env) (frA fr : Frame) (s : LocState) (F : Fact) : Prop :=
  match F.1 with
  | .avail =>
    ∃ v y, cx.f.value? F.2.id = some v ∧ v.id = F.2.id ∧ (fr.regs[F.2.id]?).join = some y ∧
      evalValueL cx.md env cx.sc fr v = .ok y
  | l =>
    ∀ x, srcVal cx env frA fr F.2.id = some x →
      if F.2.weak then cx.md.retype (cx.origTy F.2) (s.at l) = comp F.2.comp x
      else s.at l = comp F.2.comp x

/-- The simulation relation (module comment). -/
structure Match (cx : Cx) (env : Env) (frA : Frame) (S : Facts) (fr : Frame) (s : LocState) :
    Prop where
  facts : ∀ F ∈ S, FactOK cx env frA fr s F
  fr_eq : fr = { frA with regs := fr.regs }
  s_fr : s.fr = { frA with regs := s.fr.regs }
  shaped : ∀ id x, (fr.regs[id]?).join = some x → cx.md.retype (cx.fty id) x = x
  kinv : ∀ id x, cx.isK id = true → (fr.regs[id]?).join = some x → x = kval cx env frA id
  regs : RegsOK s
  fsize : fr.regs.size = cx.f.valueTab.size

end GoFV.Proof.RA

import GoFV.Proof.Pass.ECRel
import GoFV.Proof.Retype

/-!
# The shapes of the source's registers (issue #28)

`RegsOK` (`ECRel`): every register of the source holds a value of the shape of its value's
type, a `MakeResult`'s register a tuple of one component per argument. A block entry keeps it:
the `Phi`s store retyped values (`regsOK_phis`), every other value its `evalOp` result retyped
at its type (`regOK_evalValue`, `regsOK_evalAll`); a `MakeResult`'s result is the tuple of its
arguments, and retyping a tuple keeps its length or gives `poison`.
-/

namespace GoFV.Proof.EC

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof.AtomSim

theorem retypePre_length : ∀ {ts : List Ty} {vs ws : List Val},
    Val.retypePre ts vs = some ws → ws.length = vs.length
  | [], vs, ws, h => by simp only [Val.retypePre, Option.some.injEq] at h; rw [h]
  | _ :: _, [], _, h => by simp [Val.retypePre] at h
  | t :: ts, v :: vs, ws, h => by
    unfold Val.retypePre at h
    cases h' : Val.retypePre ts vs with
    | none => rw [h'] at h; cases h
    | some ws' => rw [h'] at h; cases h; simp [retypePre_length h']

/-- A tuple retyped to a tuple keeps its length. -/
theorem retype_tuple_length {t : Ty} {vs ws : List Val}
    (h : (Val.tuple vs).retype t = .tuple ws) : ws.length = vs.length := by
  cases t with
  | tuple ts =>
    unfold Val.retype at h
    cases hp : Val.retypePre ts vs with
    | none => rw [hp] at h; cases h
    | some ws' => rw [hp] at h; cases h; exact retypePre_length hp
  | _ => unfold Val.retype at h; cases h

theorem evalOp_makeResult {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (h : v.op = .MakeResult) : evalOp env ctx fr v argv ty = .ok (.tuple argv) := by
  simp only [evalOp, frameVal, h]; rfl

/-- The result of evaluating value `x` is `RegOK`. -/
theorem regOK_evalValue {env : Env} {ctx : Ctx} {fr : Frame} {x : ID} {v : Value} {y : Val}
    (hv : ctx.f.value? x = some v) (hid : v.id = x) (h : evalValue env ctx fr v = .ok y) :
    RegOK ctx x y := by
  rw [evalValue_of_regs (regs_of_ok h), hid] at h
  cases he : evalOp env ctx fr v (v.args.toList.map (rv fr)) (ctx.tys[x]?.getD .other) with
  | panic e m => rw [he] at h; cases h
  | stuck msg => rw [he] at h; cases h
  | ok r =>
    rw [he] at h; cases h
    refine ⟨Val.retype_hasTy _ _, fun u vs hu hop hy => ?_, fun u hu => ?_⟩
    · rw [hv] at hu; cases hu
      rw [evalOp_makeResult hop] at he; cases he
      rw [retype_tuple_length hy]; simp
    · rw [hv] at hu; cases hu
      refine ⟨fun hop => ?_, fun hop => ?_⟩ <;>
        simp only [evalOp, frameVal, hop, show isRoot .TailLECall = true from rfl,
          show isRoot .TailLECallInter = true from rfl, ite_true] at he <;> cases he

theorem RegsOK.set {ctx : Ctx} {fr : Frame} (h : RegsOK ctx fr) {x : ID} {y : Val}
    (hy : RegOK ctx x y) : RegsOK ctx (fr.set x y) := by
  intro z w hz
  by_cases hxz : x = z
  · subst hxz
    have hlt : x < fr.regs.size := by
      have := (Array.getElem?_eq_some_iff.1 hz).1
      simpa [Frame.set] using this
    rw [Frame.set_regs_self hlt] at hz; cases hz; exact hy
  · rw [Frame.set_regs_ne hxz] at hz; exact h z w hz

/-- `evalAll` keeps `RegsOK` (over values whose IDs are their keys). -/
theorem regsOK_evalAll {env : Env} {ctx : Ctx} :
    ∀ {L : List ID} {fr fr' : Frame}, (∀ x ∈ L, ∀ v, ctx.f.value? x = some v → v.id = x) →
      RegsOK ctx fr → evalAll env ctx fr L = .ok fr' → RegsOK ctx fr'
  | [], fr, fr', _, h, he => by cases he; exact h
  | x :: L, fr, fr', hid, h, he => by
    rw [evalAll_cons] at he
    cases hs : stepV env ctx fr x with
    | panic e m => rw [hs] at he; cases he
    | stuck msg => rw [hs] at he; cases he
    | ok y =>
      rw [hs] at he
      have hy : RegOK ctx x y := by
        unfold stepV at hs
        cases hv : ctx.f.value? x with
        | none => rw [hv] at hs; cases hs
        | some v => rw [hv] at hs; exact regOK_evalValue hv (hid x List.mem_cons_self v hv) hs
      exact regsOK_evalAll (fun z hz => hid z (List.mem_cons_of_mem _ hz)) (h.set hy) he

theorem regsOK_setPhis {ctx : Ctx} :
    ∀ {ps : List (ID × Val)} {fr : Frame}, (∀ p ∈ ps, RegOK ctx p.1 p.2) → RegsOK ctx fr →
      RegsOK ctx { fr with regs := setPhis ps fr.regs }
  | [], _, _, h => h
  | (id, x) :: ps, fr, hp, h =>
    regsOK_setPhis (ps := ps) (fr := fr.set id x) (fun p hm => hp p (List.mem_cons_of_mem _ hm))
      (h.set (hp (id, x) List.mem_cons_self))

/-- A `Phi`'s step stores a `RegOK` value (retyped; a `Phi` is not a `MakeResult`). -/
theorem regOK_phi {ctx : Ctx} {fr : Frame} {i : Nat} {p : ID × Val}
    (h : phiStep ctx fr i p.1 = .ok (some p)) : RegOK ctx p.1 p.2 := by
  obtain ⟨-, v, a, y, hv, hph, -, -, hp2⟩ := phiStep_some h
  refine ⟨by rw [hp2]; exact Val.retype_hasTy _ _, fun u vs hu hop _ => ?_, fun u hu => ?_⟩
  · rw [hv] at hu; cases hu; rw [hph] at hop; cases hop
  · rw [hv] at hu; cases hu
    exact ⟨fun h => by rw [hph] at h; cases h, fun h => by rw [hph] at h; cases h⟩

/-- Setting the collected `Phi`s keeps `RegsOK`. -/
theorem regsOK_phis {ctx : Ctx} {fr : Frame} {i : Nat} {l : List ID} {ps : List (ID × Val)}
    (hps : l.filterMapM (phiStep ctx fr i) = .ok ps) (h : RegsOK ctx fr) :
    RegsOK ctx { fr with regs := setPhis ps fr.regs } :=
  regsOK_setPhis (fun p hp => regOK_phi ((filterMapM_phi hps).2.1 p hp)) h

end GoFV.Proof.EC

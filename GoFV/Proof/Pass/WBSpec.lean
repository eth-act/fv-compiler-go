import GoFV.Opt.WriteBarrierCheck
import GoFV.Proof.Pass.RewriteTerm

/-!
# writebarrier: what the checker's structure establishes (issue #36)

The checker `WBCheck.wbOK` read as propositions: the context (`ctxOf_spec`, `wbOK_spec`), the
kept and last-store marks (`keptMarks_spec`, `lastMarks_spec`), the flag address and constant
(`lazyOK_spec`), and the chain of a block (`splitOf_spec`, `chainRuns_spec`, `runOf_spec`).
-/

namespace GoFV.Proof.WB

open GoFV.SSA GoFV.Opt GoFV.Opt.WBCheck

theorem ctxOf_spec {tabs : Tables} {f g : Func} {c : WBCheck.Ctx} (h : ctxOf tabs f g = some c) :
    c.tabs = tabs ∧ c.f = f ∧ c.g = g ∧ c.K = keptMarks f g ∧ c.Lst = lastMarks f g ∧
      lazyOK tabs f g c.K c.Lst = some c.lazy := by
  sorry

theorem wbOK_spec {tabs : Tables} {f g : Func} (h : wbOK tabs f g = true) :
    g.entry = f.entry ∧ g.ownAux = f.ownAux ∧ memTyOK tabs f = true ∧
      ∃ c, ctxOf tabs f g = some c ∧ ∀ b ∈ f.blocks, c.blockOK b = true := by
  sorry

/-- A kept value: listed in both functions with the same fields. -/
theorem keptMarks_spec {f g : Func} {x : ID} (h : (keptMarks f g).getD x false = true) :
    ∃ u w, f.value? x = some u ∧ g.value? x = some w ∧ sameV u w = true ∧
      (∃ b ∈ f.blocks, ∃ B, f.block? b = some B ∧ x ∈ B.values) ∧
      (∃ b ∈ g.blocks, ∃ B, g.block? b = some B ∧ x ∈ B.values) := by
  sorry

/-- A marked last store is the last store of a run of some block's chain. -/
theorem lastMarks_spec {f g : Func} {x : ID} (h : (lastMarks f g).getD x false = true) :
    ∃ b ∈ f.blocks, ∃ rs l, chainRuns? f g b = some (rs, l) ∧ ∃ r ∈ rs, r.last = x := by
  sorry

theorem lazyOK_some {tabs : Tables} {f g : Func} {K Lst : Array Bool} {wa c0 : ID}
    (h : lazyOK tabs f g K Lst = some (some (wa, c0))) :
    (∃ w, g.value? wa = some w ∧ w.op = .Addr ∧ symName? tabs w.aux = some "runtime.writeBarrier" ∧
      isPtrTy (tabs.ty w.type) = true ∧ w.args.size = 1) ∧
    (∃ w, g.value? c0 = some w ∧ w.op = .Const32 ∧ w.auxInt = (0 : Int64) ∧ w.args = #[] ∧
      tabs.ty w.type = .int .w32) ∧
    wa ∈ vals g g.entry ∧ c0 ∈ vals g g.entry ∧
    (∀ b ∈ f.blocks, ∀ rs l, chainRuns? f g b = some (rs, l) → ∀ r ∈ rs,
      r.sp.wbaddr = wa ∧ r.sp.const0 = c0) := by
  sorry

theorem lazyOK_none {tabs : Tables} {f g : Func} {K Lst : Array Bool}
    (h : lazyOK tabs f g K Lst = some none) :
    ∀ b ∈ f.blocks, ∀ rs l, chainRuns? f g b = some (rs, l) → rs = [] := by
  sorry

/-- A split block. -/
theorem splitOf_spec {f g : Func} {c : ID} {s : Split} (h : splitOf? f g c = some s) :
    s.c = c ∧ ∃ C, g.block? c = some C ∧ C.kind = .If ∧ C.controls = #[s.flag] ∧
      C.succs = #[⟨s.t, 0⟩, ⟨s.e, 0⟩] ∧ s.t ≠ s.e ∧ s.t ∉ f.blocks ∧ s.e ∉ f.blocks ∧
      (∃ fv, g.value? s.flag = some fv ∧ fv.op = .Neq32 ∧ fv.args = #[s.load, s.const0]) ∧
      (∃ lv, g.value? s.load = some lv ∧ lv.op = .Load ∧ lv.args = #[s.wbaddr, s.mem]) := by
  sorry

/-- The chain of a block: consecutive splits, each with its run, ending at the last block. -/
theorem chainRuns_spec {f g : Func} {b l : ID} {rs : List Run} (h : chainRuns? f g b = some (rs, l)) :
    (∀ j r, rs[j]? = some r → (segsOf b rs)[j]? = some r.sp.c ∧
      (segsOf b rs)[j + 1]? = some r.sp.e ∧ splitOf? f g r.sp.c = some r.sp ∧
      runOf? f g r.sp = some r) ∧
    (segsOf b rs).getLast? = some l := by
  sorry

/-- A run: its source stores form a memory chain from the split's memory, ending at `last`; the
dropped nil check is the first store's address. -/
theorem runOf_spec {f g : Func} {s : Split} {r : Run} (h : runOf? f g s = some r) :
    r.sp = s ∧ r.src.length = r.tgt.length ∧ r.src.getLast? = some r.last ∧
    (∀ (k : Nat) (x : ID), r.src[k]? = some x → ∃ u, f.value? x = some u ∧
      (u.op = .Store ∨ u.op = .VarDef ∨ u.op = .VarLive) ∧
      u.args.toList.getLast? = some (match k with
        | 0 => s.mem
        | k + 1 => r.src[k]!)) ∧
    (∀ n, r.nc = some n → ∃ x0 v0 nv, r.src[0]? = some x0 ∧ f.value? x0 = some v0 ∧
      v0.op = .Store ∧ v0.args[0]? = some n ∧ f.value? n = some nv ∧ nv.op = .NilCheck ∧
      nv.args[1]? = some s.mem ∧ nv.id = n) ∧
    (∃ pv, g.value? r.phi = some pv ∧ pv.op = .Phi ∧ pv.args = #[s.mem, r.memThen]) ∧
    (vals g s.e)[0]? = some r.phi ∧
    (∀ x w, (vals g s.t).toList.find? (fun x => (g.value? x).any (·.op == Op.WB)) = some x →
      g.value? x = some w → r.wbN = w.auxInt.toInt.toNat) := by
  sorry

end GoFV.Proof.WB

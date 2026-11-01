import GoFV.Proof.Pass.WBRole

/-!
# writebarrier: the checker's block conditions as propositions (issue #36)

`blockOK_spec`, `runOK_spec`, `npOK_spec`, `keptNP_spec`: `Ctx.blockOK`, `Ctx.runOK`,
`Ctx.npOK` and `Ctx.keptNP` read as propositions; `availIn_spec`: an available argument.
-/

namespace GoFV.Proof.WB

open GoFV.SSA GoFV.Opt GoFV.Opt.WBCheck

/-- The dropped nil check of a run, as `npOK` lists it. -/
def ncsOf (c : WBCheck.Ctx) (r : Run) : List ID :=
  match r.nc with
  | some n => if c.K.getD n false then [] else [n]
  | none => []

section
variable {c : WBCheck.Ctx}

theorem availIn_spec {B : Block} {segs : List ID} {j : Nat} {a : ID}
    (h : c.availIn B segs j a = true) :
    c.held a = true ∧ (a ∈ B.values → ∃ s ∈ segs.take (j + 1), a ∈ vals c.g s) ∧
      (a ∉ B.values → ∃ y ∈ B.values, ∃ u, c.f.value? y = some u ∧ u.op ≠ .Phi ∧ a ∈ u.args) := by
  sorry

theorem keptNP_spec {s : ID} {l : List ID} (h : c.keptNP s = some l) :
    ∃ C o, c.g.block? s = some C ∧ Sem.schedule c.g C = some o ∧
      l = (o.toList.filter (npOf c.g C)).filter (c.K.getD · false) := by
  sorry

theorem npOK_spec {B : Block} {rs : List Run} {segs : List ID} (h : c.npOK B rs segs = true) :
    ∃ src k0 ks, Ctx.npSeq c.f B = some src ∧ segs.mapM c.keptNP = some (k0 :: ks) ∧
      src = k0 ++ (rs.zip ks).flatMap (fun p => ncsOf c p.1 ++ p.1.src ++ p.2) := by
  sorry

theorem runOK_spec {b : ID} {B : Block} {segs : List ID} {rs : List Run} {j : Nat} {r : Run}
    (h : c.runOK b B segs rs j r = true) :
    segs[j]? = some r.sp.c ∧ segs[j + 1]? = some r.sp.e ∧
    (∃ T, c.g.block? r.sp.t = some T ∧ T.id = r.sp.t ∧ T.kind = .Plain ∧
      T.succs = #[⟨r.sp.e, 1⟩] ∧ (Ctx.npSeq c.g T).isSome ∧
      (∀ n, r.nc = some n → ∃ y ys, Ctx.npSeq c.g T = some (y :: ys) ∧ c.roleOf rs y = .ncThen j) ∧
      ∀ x ∈ T.values, c.roleOK b B segs rs true j x = true) ∧
    (∃ E, c.g.block? r.sp.e = some E ∧ E.id = r.sp.e ∧
      (∀ y, r.ncEnd = some y → ∃ ys, Ctx.npSeq c.g E = some (y :: ys)) ∧
      (r.ncEnd = none → r.nc = none)) ∧
    (∃ C, c.g.block? r.sp.c = some C ∧ C.id = r.sp.c) ∧
    r.src.length = r.tgt.length ∧ 0 < r.src.length ∧ r.last ∈ vals c.g r.sp.e ∧
    (∀ x ∈ r.src, x ∈ B.values ∧ c.K.getD x false = false) ∧
    (∀ n, r.nc = some n → n ∈ B.values ∧ ∃ u, c.f.value? n = some u ∧ u.op = .NilCheck) := by
  sorry

theorem blockOK_spec {b : ID} (h : c.blockOK b = true) {B : Block} (hB : c.f.block? b = some B)
    {rs : List Run} {l : ID} (hch : chainRuns? c.f c.g b = some (rs, l)) :
    (∃ L C0, c.g.block? l = some L ∧ c.g.block? b = some C0 ∧ L.id = l ∧ C0.id = b ∧
      L.kind = B.kind ∧ L.controls = B.controls ∧ L.succs = B.succs ∧
      ∀ x ∈ B.controls, c.held x = true) ∧
    (segsOf b rs).getLast? = some l ∧
    ((segsOf b rs) ++ rs.map (·.sp.t)).Nodup ∧
    (∀ j r, rs[j]? = some r → c.runOK b B (segsOf b rs) rs j r = true) ∧
    (∀ x ∈ B.values, (c.K.getD x false = true → ∃ s ∈ segsOf b rs, x ∈ vals c.g s) ∧
      (c.K.getD x false = false → (∃ r ∈ rs, x ∈ r.src) ∨ ∃ r ∈ rs, r.nc = some x)) ∧
    (∀ j s, (segsOf b rs)[j]? = some s → ∀ x ∈ vals c.g s,
      c.roleOK b B (segsOf b rs) rs false j x = true) ∧
    c.npOK B rs (segsOf b rs) = true := by
  sorry

end

end GoFV.Proof.WB

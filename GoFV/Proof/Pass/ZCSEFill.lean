import GoFV.Proof.Pass.ZCSEEval

/-!
# zcse: the target's frame

Outside the entry block, the target's frame is the source's with every `EA g` value (zcse's
representatives, evaluated once in the target's entry) set to its constant: `fill`. `argRead`:
where the source reads an argument, the target reads the related argument (kept, or a
representative with the same key) from `fill` and gets the same value.
-/

namespace GoFV.Proof.ZCSE

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.ZCSE Dom

variable {tabs : Tables} {f g : Func}

/-- The value of `g`'s value `x` in the activation of `F`, if it evaluates. -/
def cst (env : Env) (tabs : Tables) (g : Func) (F : Frame) (x : ID) : Option Val :=
  match g.value? x with
  | some v =>
    match evalValue env (Ctx.make tabs g) F v with
    | .ok y => some y
    | _ => none
  | none => none

/-- `F` with every `EA g` value set to its constant. -/
def fill (env : Env) (tabs : Tables) (g : Func) (F : Frame) : Frame :=
  { F with regs := F.regs.mapIdx fun x o => if entryArgless g x then cst env tabs g F x else o }

theorem fill_frame (env : Env) (F : Frame) :
    fill env tabs g F = { F with regs := (fill env tabs g F).regs } := rfl

theorem fill_size (env : Env) (F : Frame) : (fill env tabs g F).regs.size = F.regs.size := by
  simp [fill]

theorem fill_get (env : Env) (F : Frame) (x : ID) :
    (fill env tabs g F).regs[x]? =
      F.regs[x]?.map fun o => if entryArgless g x then cst env tabs g F x else o := by
  simp [fill, Array.getElem?_mapIdx]

theorem fill_not_ea (env : Env) (F : Frame) {x : ID} (hx : ¬ EA g x) :
    (fill env tabs g F).regs[x]? = F.regs[x]? := by
  rw [fill_get]
  cases F.regs[x]? <;> simp [hx]

theorem cst_frame {env : Env} {F F' : Frame} (hF : F' = { F with regs := F'.regs }) {x : ID}
    (hx : EA g x) : cst env tabs g F' x = cst env tabs g F x := by
  obtain ⟨-, -, -, v, hv, hva, -⟩ := ea_iff.1 hx
  unfold cst; rw [hv]; simp only
  rw [evalValue_argless_regs hva hF]

theorem fill_ea_eq {env : Env} {F F' : Frame} (hF : F' = { F with regs := F'.regs })
    (hs : F'.regs.size = F.regs.size) {x : ID} (hx : EA g x) :
    (fill env tabs g F').regs[x]? = (fill env tabs g F).regs[x]? := by
  rw [fill_get, fill_get, cst_frame hF hx]
  rcases Nat.lt_or_ge x F.regs.size with h | h
  · rw [Array.getElem?_eq_getElem h, Array.getElem?_eq_getElem (hs ▸ h)]; simp [hx]
  · rw [Array.getElem?_eq_none h, Array.getElem?_eq_none (hs ▸ h)]

/-- An `EA g` value holds its constant in `fill`. -/
theorem fill_ea {env : Env} (S : Setup tabs f g) {F : Frame} (hsz : F.regs.size = f.valueTab.size)
    (hlen : F.args.length = (Ctx.make tabs f).params.size) {x : ID} (hx : EA g x) :
    ∃ v y, g.value? x = some v ∧ evalValue env (Ctx.make tabs g) F v = .ok y ∧
      (fill env tabs g F).regs[x]? = some (some y) := by
  obtain ⟨v, hv, hsafe⟩ := S.rel.safe x hx
  obtain ⟨y, hy⟩ := safe_ok (env := env) (fr := F) hsafe (by rw [hlen, S.params])
  refine ⟨v, y, hv, hy, ?_⟩
  have hlt : x < F.regs.size := by rw [hsz, ← S.rel.vsize]; exact ZCSE.lt_of_value? hv
  rw [fill_get, Array.getElem?_eq_getElem hlt]
  simp [hx, cst, hv, hy]

/-- An argument-free value of `f` and a value of `g` with the same op, aux, auxint and type
evaluate alike in a source frame. -/
theorem eval_cross {env : Env} (S : Setup tabs f g) {F : Frame} {a b : ID} {u w : Value}
    (hu : f.value? a = some u) (hw : g.value? b = some w) (hua : u.args = #[])
    (hwa : w.args = #[]) (hop : w.op = u.op) (hax : w.aux = u.aux) (hai : w.auxInt = u.auxInt)
    (hty : w.type = u.type) (huid : u.id = a) (hwid : w.id = b) {y : Val}
    (h : evalValue env (Ctx.make tabs f) F u = .ok y) :
    evalValue env (Ctx.make tabs g) F w = .ok y :=
  evalValue_argless (ctx := Ctx.make tabs f) (ctx' := Ctx.make tabs g) hua hwa hop hax hai
    (by rw [hwid, huid, tys_of_value hu, tys_of_value hw, hty]) rfl S.params rfl h

/-- **Reading a related argument.** Where the source reads `fa` (a listed value), the target
reads `ga` (`fa` itself or a representative with the same key) from `fill` and gets the same. -/
theorem argRead {env : Env} (S : Setup tabs f g) {F : Frame}
    (hinv : ArglessInv env (Ctx.make tabs f) F) (hsz : F.regs.size = f.valueTab.size)
    {fa ga : ID} (hfl : Listed f fa) {y : Val} (hy : F.regs[fa]? = some (some y))
    (hr : ga = fa ∨ EA g ga ∧ Same f g fa ga) : (fill env tabs g F).regs[ga]? = some (some y) := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  by_cases hea : EA g ga
  · obtain ⟨gE, hgE, hgaE, w, hw, hwa, hwn⟩ := ea_iff.1 hea
    have hwid : w.id = ga := by
      obtain ⟨w', hw', hid, -⟩ := hwg.valueId g.entry gE ⟨hwg.entry, hgE⟩ ga hgaE
      rw [hw] at hw'; cases hw'; exact hid
    -- the source value read
    obtain ⟨u, hu, huid, hcore⟩ : ∃ u, f.value? fa = some u ∧ u.id = fa ∧
        u.args = #[] ∧ u.op ≠ .Phi ∧ w.op = u.op ∧ w.aux = u.aux ∧ w.auxInt = u.auxInt ∧
        w.type = u.type := by
      obtain ⟨b, fb, hbin, hx⟩ := hfl
      obtain ⟨u, hu, huid, -⟩ := hwf.valueId b fb hbin fa hx
      refine ⟨u, hu, huid, ?_⟩
      rcases hr with rfl | ⟨-, hs⟩
      · obtain ⟨w', hw', -, hop, hax, hai, hty, hsz', -⟩ := S.value hu
        rw [hw] at hw'; cases hw'
        rw [hwa] at hsz'
        exact ⟨Array.eq_empty_of_size_eq_zero (by simpa using hsz'.symm),
          by rw [← hop]; exact hwn, hop, hax, hai, hty⟩
      · obtain ⟨u', w', hu', hw', hua, hun, -, -, hop, hax, hai, hty⟩ := same_iff.1 hs
        rw [hu] at hu'; cases hu'
        rw [hw] at hw'; cases hw'
        exact ⟨hua, hun, hop.symm, hax.symm, hai.symm, hty.symm⟩
    obtain ⟨hua, hun, hop, hax, hai, hty⟩ := hcore
    have hev := eval_cross S hu hw hua hwa hop hax hai hty huid hwid (hinv fa u y hu hua hun hy)
    have hlt : ga < F.regs.size := by rw [hsz, ← S.rel.vsize]; exact ZCSE.lt_of_value? hw
    rw [fill_get, Array.getElem?_eq_getElem hlt]
    simp [hea, cst, hw, hev]
  · rcases hr with rfl | ⟨h, -⟩
    · rw [fill_not_ea env F hea]; exact hy
    · exact absurd h hea

end GoFV.Proof.ZCSE

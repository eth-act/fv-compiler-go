import GoFV.Opt.Pass

/-!
# softfloat (`softfloat.go`)

`softfloat` returns at once unless `f.Config.SoftFloat` (`softfloat.go:13`), which linux/arm64
never sets (only `-d=softfloat`; `docs/PASSES.md`, softfloat). The port is that guard, on the
exported `config softfloat`; the soft-float rewrite itself is not ported, so a function compiled
with `SoftFloat` on is reported as unsupported rather than passed through.
-/

namespace GoFV.Opt

open GoFV.SSA

/-- `softfloat(f)` for `Config.SoftFloat = softFloat`. -/
def softfloat (softFloat : Bool) (f : Func) : Except String Func :=
  if softFloat then throw "softfloat: Config.SoftFloat is set; the soft-float rewrite is not ported"
  else pure f

theorem softfloat_off (f : Func) : softfloat false f = .ok f := rfl

/-- The `softfloat` pass. -/
def softfloatPass : Pass := Pass.ofFunc fun env f => do softfloat (← env.flag "softfloat") f

end GoFV.Opt

import GoFV.Opt.Pass

/-!
# cpufeatures, rewrite tern (`cpufeatures.go`, `rewritetern.go`)

Both are `disabled: !buildcfg.Experiment.SIMD` (`compile.go:492-493`), off in the default build
(no export section). With SIMD on they still return at once unless the architecture is amd64
(`cpufeatures.go:116-120`, `rewritetern.go:38-46`; `rewriteTern` first returns when
`f.maxCPUFeatures == CPUNone`, which only an amd64 `cpufeatures` changes). The amd64 bodies are
not ported.
-/

namespace GoFV.Opt

open GoFV.SSA

/-- `arch == amd64` from `config arch`. -/
def isAMD64 (env : PassEnv) : Except String Bool :=
  match env.config? "arch" with
  | some #[.word a] => pure (a == "amd64")
  | _ => throw "config arch: missing"

/-- `cpufeatures(f)`: no-op unless amd64. -/
def cpufeaturesPass : Pass := Pass.ofFunc fun env f => do
  if ← isAMD64 env then throw "cpufeatures: amd64 is not ported" else pure f

/-- `rewriteTern(f)`: no-op unless amd64. -/
def rewriteTernPass : Pass := Pass.ofFunc fun env f => do
  if ← isAMD64 env then throw "rewrite tern: amd64 is not ported" else pure f

/-- `disabled: !buildcfg.Experiment.SIMD` (both passes). -/
def simdDisabled (env : PassEnv) : Except String Bool := return !(← env.flag "exp.simd")

end GoFV.Opt

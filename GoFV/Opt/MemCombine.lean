import GoFV.Opt.MemCombine.Loads
import GoFV.Opt.MemCombine.Stores

/-!
# memcombine (`memcombine.go:18-27`)

Combines smaller loads and stores into larger ones when the architecture allows unaligned
accesses (`docs/PASSES.md`, memcombine): `memcombineLoads`, then `memcombineStores`.
Clobbered values stay in their blocks as `Invalid` (stores retyped `bool`) for deadcode.
-/

namespace GoFV.Opt

open GoFV.SSA GoFV.Opt.MemCombine

/-- `memcombine(f)` with the configuration `c`, threading the definition tables. -/
def memcombine (c : Cfg) (unalignedOK : Bool) (tabs : Tables) (f : Func) :
    Except String (Func × Tables) := do
  if !unalignedOK then return (f, tabs)
  let ((), s) ← (do memcombineLoads; if c.stores then memcombineStores : M Unit).run c
    |>.run { f, tabs }
  return (s.f, s.tabs)

/-- memcombine's configuration from the pass environment, and `Config.unalignedOK`. -/
def memcombineCfg (env : PassEnv) : Except String (Cfg × Bool) := do
  let int (k : String) : Except String Int := do
    match env.config? k with
    | some #[.word w] =>
      match w.toInt? with
      | some n => pure n
      | none => throw s!"config {k}: not an integer"
    | _ => throw s!"config {k}: missing"
  let typ (k : String) : Except String TypeRef := do
    match env.typ? k with
    | some t => pure t
    | none => throw s!"typs: no {k}"
  let arch := match env.config? "arch" with
    | some #[.word w] => w
    | some #[.str s] => String.fromUTF8! s.bytes
    | _ => ""
  let c : Cfg := {
    regSize := Int64.ofInt (← int "regsize"), bigEndian := ← env.flag "bigendian",
    s390x := arch == "S390X",
    bswap64 := ← env.flag "havebswap64", bswap32 := ← env.flag "havebswap32",
    bswap16 := ← env.flag "havebswap16",
    bool := ← typ "Bool", u16 := ← typ "UInt16", u32 := ← typ "UInt32", u64 := ← typ "UInt64",
    sameType := env.typeOrder.eq }
  return (c, ← env.flag "unalignedok")

/-- The `memcombine` pass. -/
def memcombinePass : Pass := fun env f => do
  let (c, u) ← memcombineCfg env
  let (func, tables) ← memcombine c u env.tables f
  return { func, tables }

end GoFV.Opt

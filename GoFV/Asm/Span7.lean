import GoFV.Asm.Aclass
import GoFV.Asm.Asmout

/-!
# `span7` (`asm7.go:1142-1440`; `docs/PASSES3.md` D4)

Layout of the text symbol: the first pass assigns PCs and collects the literal pool
(`addLiteralsToPool`, `addpool`, `checkpool`, `flushpool`), the fix-up passes insert branch
veneers for conditional branches whose target is out of range (`fixUpLongBranch`; Go's
`changed = changed || c.fixUpLongBranch(p)` short circuit is kept, so a pass fixes at most one
branch), the emission pass encodes every Prog with `asmout` (`GoFV.Asm.Asmout`) into
`cursym.P` (little-endian words, `PCALIGN` padding as `NOOP`s, then zero bytes up to
`funcAlign`), and the jump tables get their words (`jt.Sym.WriteAddr`).

Not ported here: the `MarkUnsafePoints` call in the middle of `span7` (the driver
`GoFV.Asm.Flush` calls it right after `span7`; it does not read what follows it), the
`ctxt.Retpoline` diagnostic (`-spectre=ret`, not a configuration the export has) and the
`oprange` initialization check (`buildop` always ran; `ARM64.oprange` is its result).
-/

namespace GoFV.Asm

open ARM64 AsmM Aclass

/-- `addr.Target()` (`link.go:254-259`): the branch target of a `TYPE_BRANCH` operand. -/
def addrTarget (a : Addr) : Option Nat :=
  if a.type == .BRANCH then
    match a.val with
    | .target id => some id
    | _ => none
  else none

/-- `obj.AlignmentPaddingLength` (`util.go:769-793`): the padding a `PCALIGN`/`PCALIGNMAX` at
`pc` (`int32`) needs. -/
def alignmentPaddingLength (pc : Int) (p : Prog) : AsmM Int := do
  let a := p.from_.offset
  -- `a&(a-1) == 0 && 8 <= a && a <= 2048`
  if !((8 <= a && a <= 2048) && (a.toNat &&& (a.toNat - 1)) == 0) then
    fail s!"AlignmentPaddingLength: alignment value of an instruction must be a power of two \
      and in the range [8, 2048], got {a}"
  let lob := pc % a
  if p.as == .PCALIGN then
    if lob != 0 then return a - lob
    return 0
  -- emit as many as s bytes of padding to obtain alignment
  let s := p.to.offset
  if s < 0 || s >= a then
    fail s!"AlignmentPaddingLength: PCALIGNMAX 'amount' {s} must be non-negative and smaller \
      than the alignment {a}"
  if s >= a - lob then return a - lob
  return 0

/-- `obj.AlignmentPadding` (`util.go:754-758`) with `requireAlignment` (`util.go:797-802`;
`ctxt.Headtype` is never `Haix` on arm64): raises the text symbol's `Align`. -/
def alignmentPadding (pc : Int) (p : Prog) : AsmM Int := do
  let v ← alignmentPaddingLength pc p
  let a := p.from_.offset
  if (← get).textAlign < wrapI16 a then
    modify fun s => { s with textAlign := wrapI16 a }
  return v

/-- `ctxt7.asmsizeBytes` (`asm7.go:1238-1249`): the size of Prog `p` in bytes. -/
def asmsizeBytes (p : Nat) : AsmM Int := do
  let pr ← getP p
  match pr.as with
  | .PCALIGN | .PCALIGNMAX => alignmentPadding (wrapI32 pr.pc) pr
  | .NOP | .FUNCDATA | .PCDATA => return 0
  | _ =>
    let o ← oplook p
    optabSize o p

/-- `ctxt7.fixUpLongBranch` (`asm7.go:1253-1288`): inserts a veneer (`B` to the target after
the branch, retargeted, and a `B` over it) when `p` is a short conditional branch whose
target is out of range. -/
def fixUpLongBranch (p : Nat) : AsmM Bool := do
  let mut toofar := false
  let o ← oplook p
  let pr ← getP p
  let flag := o.flag.toNat
  -- very large branches
  if (flag &&& BRANCH14BITS.toNat != 0 || flag &&& BRANCH19BITS.toNat != 0) then
    if let some tgt := addrTarget pr.to then
      let otxt := (← getP tgt).pc - pr.pc
      if flag &&& BRANCH14BITS.toNat != 0 then
        -- branch instruction encodes 14 bits
        toofar := otxt <= -(1 <<< 15) + 10 || otxt >= (1 <<< 15) - 10
      else if flag &&& BRANCH19BITS.toNat != 0 then
        -- branch instruction encodes 19 bits
        toofar := otxt <= -(1 <<< 20) + 10 || otxt >= (1 <<< 20) - 10
      if toofar then
        let q ← newProg
        setLink q (← linkOf p)
        setLink p (some q)
        modP q fun x => { x with as := .JMP, to := { x.to with type := .BRANCH, val := .target tgt } }
        modP p fun x => { x with to := { x.to with val := .target q } }
        let q ← newProg
        setLink q (← linkOf p)
        setLink p (some q)
        -- q.To.SetTarget(q.Link.Link)
        let ql ← match ← linkOf q with
          | some l => pure l
          | none => fail "fixUpLongBranch: nil q.Link"
        let tgt2 : AddrVal := match ← linkOf ql with
          | some l => .target l
          | none => .nilTarget
        modP q fun x => { x with as := .JMP, to := { x.to with type := .BRANCH, val := tgt2 } }
  return toofar

/-- `roundUp` (`asm7.go:1446-1451`) on `uint32`. -/
def roundUp (x to : Nat) : AsmM Nat := do
  if to == 0 || to &&& (to - 1) != 0 then
    fail s!"roundUp: rounded up to a value that is not a power of 2: {to}"
  return ((x + to - 1) % 2 ^ 32) - ((x + to - 1) % 2 ^ 32) % to

/-- `ctxt7.flushpool` (`asm7.go:1351-1389`): links the pending literal pool after `p`, behind a
branch over it (or an `UNDEF` at the end of the function) unless `p` is an unconditional
branch. -/
def flushpool (p : Nat) : AsmM Unit := do
  let pr ← getP p
  -- Needs to insert a branch before flushing the pool.
  -- We don't need the jump if following an unconditional branch.
  if !(pr.as == .JMP || pr.as == .RET || pr.as == .ERET) then
    let q ← newProg
    match ← linkOf p with
    | none =>
      -- If p is the last instruction of the function, insert an UNDEF instruction in case
      -- the execution fall through to the pool.
      modP q fun x => { x with as := .UNDEF }
    | some l =>
      -- Else insert a branch to the next instruction of p.
      modP q fun x => { x with as := .JMP, to := { x.to with type := .BRANCH, val := .target l } }
    setLink q (← get).blitrl
    modP q fun x => { x with pos := pr.pos }
    modify fun s => { s with blitrl := some q }
  -- The line number for constant pool entries doesn't really matter.
  -- We set it to the line number of the preceding instruction so that
  -- there are no deltas to encode in the pc-line tables.
  let mut cur := (← get).blitrl
  repeat
    match cur with
    | none => break
    | some q =>
      modP q fun x => { x with pos := pr.pos }
      cur ← linkOf q
  match (← get).elitrl with
  | some e => setLink e (← linkOf p)
  | none => fail "flushpool: nil elitrl"
  setLink p (← get).blitrl
  -- BUG: should refer back to values until out-of-range
  modify fun s => { s with blitrl := none, elitrl := none, poolSize := 0, poolStart := 0 }

/-- `ctxt7.checkpool` (`asm7.go:1341-1349`): flushes the pool when it may go out of range or
`p` is the last Prog. -/
def checkpool (p : Nat) : AsmM Unit := do
  let pr ← getP p
  let s ← get
  if s.poolSize >= 0xffff0 ||
      !ispcdisp (wrapI32 (pr.pc + 4 + s.poolSize - s.poolStart + 8)) ||
      (← linkOf p).isNone then
    flushpool p

/-- `ctxt7.addpool` (`asm7.go:1398-1444`): a `WORD`/`DWORD` literal for operand `a` of `p`
(`From` if `isFrom`, else `To`) in the pending pool (an equal `To` is reused), as `p.Pool`. -/
def addpool (p : Nat) (isFrom : Bool) : AsmM Unit := do
  let pr ← getP p
  let a := if isFrom then pr.from_ else pr.to
  let (cls, a) ← aclassAddr a
  modP p fun x => if isFrom then { x with from_ := a } else { x with to := a }
  let cls : Int := cls
  let lit := (← get).instoffset
  let t ← newProg
  let mut tas : As := .WORD
  let mut sz : Nat := 4
  if a.type == .CONST then
    if lit != wrapI32 lit && lit != wrapU32 lit then
      -- out of range -0x80000000 ~ 0xffffffff, must store 64-bit.
      tas := .DWORD
      sz := 8
    -- else store 32-bit
  else if (pr.as == .MOVD && a.type != .MEM) || cls == C_ADDR || cls == C_VCON ||
      lit != wrapI32 lit || lit != wrapU32 lit then
    -- conservative: don't know if we want signed or unsigned extension.
    -- in case of ambiguity, store 64-bit
    tas := .DWORD
    sz := 8
  modP t fun x => { x with as := tas, to := { x.to with type := .CONST, offset := lit } }
  let tTo := (← getP t).to
  let mut cur := (← get).blitrl
  repeat
    match cur with
    | none => break
    | some q =>
      -- could hash on t.t0.offset
      if (← getP q).to == tTo then
        modP p fun x => { x with pool := some q }
        return
      cur ← linkOf q
  match (← get).blitrl with
  | none =>
    modify fun s => { s with blitrl := some t, poolStart := (wrapU32 pr.pc).toNat }
  | some _ =>
    match (← get).elitrl with
    | some e => setLink e (some t)
    | none => fail "addpool: nil elitrl"
  modify fun s => { s with elitrl := some t }
  if tas == .DWORD then
    -- make DWORD 8-byte aligned, this is not required by ISA,
    -- just to avoid performance penalties when loading from
    -- the constant pool across a cache line.
    let r ← roundUp (← get).poolSize 8
    modify fun s => { s with poolSize := r }
  modify fun s => { s with poolSize := (s.poolSize + sz) % 2 ^ 32 }
  modP p fun x => { x with pool := some t }

/-- `ctxt7.addLiteralsToPool` (`asm7.go:1291-1303`). -/
def addLiteralsToPool (p : Nat) : AsmM Unit := do
  let o ← oplook p
  if o.flag.toNat &&& LFROM.toNat != 0 then addpool p true
  if o.flag.toNat &&& LTO.toNat != 0 then addpool p false
  if (← get).blitrl.isSome then checkpool p

/-- `codeBuffer.emit` (`asm7.go:1220-1225`): appends little-endian words to `cursym.P`. -/
def codeBufferEmit (ops : Array UInt32) : AsmM Unit := do
  -- Take `P` out of the state so that the pushes update it in place.
  let b ← modifyGet fun s => (s.textP, { s with textP := .empty })
  let b := ops.foldl (init := b) fun b o =>
    b |>.push o.toUInt8 |>.push (o >>> 8).toUInt8 |>.push (o >>> 16).toUInt8
      |>.push (o >>> 24).toUInt8
  modify fun s => { s with textP := b }

/-- `codeBuffer.finish` (`asm7.go:1229-1233`): pads `cursym.P` with zero bytes to
`funcAlign`. -/
def codeBufferFinish : AsmM Unit :=
  modify fun s => Id.run do
    let mut b := s.textP
    while b.size % funcAlign.toNat > 0 do
      b := b.push 0
    return { s with textP := b }

/-! ## `LSym.WriteAddr` (`data.go`) -/

private def bytesHasPrefix (s pre : ByteArray) : Bool :=
  pre.size ≤ s.size && (List.range pre.size).all fun i => s[i]! == pre[i]!

private def bytesHasSuffix (s suf : ByteArray) : Bool :=
  suf.size ≤ s.size &&
    (List.range suf.size).all fun i => s[s.size - suf.size + i]! == suf[i]!

private def bytesContains (s sub : ByteArray) : Bool :=
  sub.size ≤ s.size &&
    (List.range (s.size - sub.size + 1)).any fun j =>
      (List.range sub.size).all fun i => s[j + i]! == sub[i]!

/-- `ctxt.IsFIPS()` (`fips140.go:150-158`). -/
def ctxtIsFIPS : AsmM Bool := do
  let pkg := (← read).pkgpath
  if pkg.endsWith "_test" then return false
  return pkg == "crypto/internal/fips140" || pkg.startsWith "crypto/internal/fips140/"

/-- `s.setFIPSType(ctxt)` (`fips140.go:213-292`; `obj.EnableFIPS()` is true on arm64 linux/
darwin, `bisectFIPS` nil) on data symbol `d` named `name`. -/
def setFIPSType (name : ByteArray) (d : SymData) : AsmM SymData := do
  -- External test packages are not in scope.
  if (← read).pkgpath.endsWith "_test" then return d
  if d.attr &&& Obj.AttrStatic.toNat != 0 then
    -- Static (file-scoped) symbol does not have name prefix,
    -- but must be local to package; rely on whether package is FIPS.
    if !(← ctxtIsFIPS) then return d
  else
    -- Name must begin with crypto/internal/fips140, then dot or slash.
    let pre := "crypto/internal/fips140".toUTF8
    if name.size ≤ pre.size || (name[pre.size]! != '.'.toNat.toUInt8 &&
        name[pre.size]! != '/'.toNat.toUInt8) || !bytesHasPrefix name pre then
      return d
    if d.kind != "STEXT" && d.kind != "STEXTFIPS" then
      let has (x : String) := bytesContains name x.toUTF8
      let ends (x : String) := bytesHasSuffix name x.toUTF8
      if has ".inittask" || has ".dict" || has ".typeAssert" || ends ".arginfo0" ||
          ends ".arginfo1" || ends ".argliveinfo" || ends ".args_stackmap" ||
          ends ".opendefer" || ends ".stkobj" || ends "·f" then
        return d
      if name == "crypto/internal/fips140/check.linkinfo".toUTF8 then return d
  -- This is a FIPS symbol! Convert its type to FIPS.
  let kind := match d.kind with
    | "STEXT" => "STEXTFIPS"
    | "SDATA" => "SDATAFIPS"
    | "SRODATA" => "SRODATAFIPS"
    | "SNOPTRDATA" => "SNOPTRDATAFIPS"
    | k => k
  return { d with kind }

/-- `s.WriteAddr(ctxt, off, siz, rsym, roff)` (`data.go:116-138` with `prepwrite`,
`data.go:67-85`, and `AddRel`, `data.go:206-211`; `checkFIPSReloc` only diagnoses with
`Flag_shared`, which is off) on symbol `k`. -/
def writeAddr (k : Nat) (off : Int) (siz : Nat) (rsym : Nat) (roff : Int) : AsmM Unit := do
  let (name, _) ← symName k
  -- Allow 4-byte addresses for DWARF.
  if siz != 8 && siz != 4 then
    fail s!"WriteAddr: bad address size {siz} in {name.toStringLossy}"
  let mut d ← symData k
  -- prepwrite
  if off < 0 || off >= 1 <<< 30 then
    fail s!"prepwrite: bad off={off} siz={siz} s={name.toStringLossy}"
  match d.kind with
  | "Sxxx" | "SBSS" => d := { d with kind := "SDATA" }
  | "SNOPTRBSS" => d := { d with kind := "SNOPTRDATA" }
  | "STLSBSS" => fail s!"prepwrite: cannot supply data for STLSBSS var {name.toStringLossy}"
  | _ => pure ()
  d ← setFIPSType name.bytes d
  let l := off + siz
  if d.data.size < l.toNat then
    d := { d with data := d.data ++ ByteArray.mk (Array.replicate (l.toNat - d.data.size) 0) }
  if l > d.size then d := { d with size := l }
  if wrapI32 off != off then
    fail s!"WriteAddr: off overflow {off} in {name.toStringLossy}"
  let r : Reloc := { off := off, siz := siz, type := "R_ADDR", add := roff, sym := some rsym }
  d := { d with relocs := d.relocs.push r }
  setSymData k d

/-! ## `span7` -/

/-- `span7` (`asm7.go:1142-1227`, without `MarkUnsafePoints`). -/
def span7 : AsmM Unit := do
  let text := (← get).text
  -- handle external functions and ELF section symbols
  if (← linkOf text).isNone then return
  let tp ← getP text
  let off := tp.to.offset
  -- c := ctxt7{…, autosize: int32(p.To.Offset & 0xffffffff), extrasize: int32(p.To.Offset >> 32)}
  modify fun s => { s with autosize := wrapI32 (off % 2 ^ 32), extrasize := wrapI32 (off >>> 32),
                           instoffset := 0, pc := 0, blitrl := none, elitrl := none,
                           poolStart := 0, poolSize := 0 }
  -- extrasize is no longer needed
  modP text fun x => { x with to := { x.to with offset := off % 2 ^ 32 }, pc := 0 }
  -- Process literal pool and allocate initial program counter for each Prog, before
  -- generating branch veneers.
  let mut pc : Int := 0
  let mut cur ← linkOf text
  repeat
    match cur with
    | none => break
    | some p =>
      modP p fun x => { x with pc }
      addLiteralsToPool p
      pc := pc + (← asmsizeBytes p)
      cur ← linkOf p
  -- if any procedure is large enough to generate a large SBRA branch, then generate extra
  -- passes putting branches around jmps to fix. this is rare.
  let mut changed := true
  while changed do
    changed := false
    pc := 0
    cur ← linkOf text
    repeat
      match cur with
      | none => break
      | some p =>
        modP p fun x => { x with pc }
        -- `changed = changed || c.fixUpLongBranch(p)`: no fix once one was made this pass.
        if !changed then changed ← fixUpLongBranch p
        pc := pc + (← asmsizeBytes p)
        cur ← linkOf p
  -- lay out the code, emitting code and data relocations.
  cur ← linkOf text
  repeat
    match cur with
    | none => break
    | some p =>
      let pr ← getP p
      modify fun s => { s with pc := pr.pc }
      match pr.as with
      | .PCALIGN | .PCALIGNMAX =>
        let v ← alignmentPaddingLength (wrapI32 pr.pc) pr
        -- emit ANOOP instruction by the padding size
        for _ in [0:(v / 4).toNat] do
          codeBufferEmit #[OP_NOOP.toNat.toUInt32]
      | .NOP | .FUNCDATA | .PCDATA => pure ()
      | _ =>
        let out ← asmout p
        codeBufferEmit out
      cur ← linkOf p
  codeBufferFinish
  modify fun s => { s with textSize := s.textP.size }
  -- Now that we know byte offsets, we can generate jump table entries.
  let fn := (← get).fn
  for (jt, targets) in fn.jumpTables do
    for i in [0:targets.size] do
      -- The ith jumptable entry points to the p.Pc'th byte in the function symbol s.
      let tpc := (← getP targets[i]!).pc
      writeAddr jt (i * 8) 8 fn.sym tpc

end GoFV.Asm

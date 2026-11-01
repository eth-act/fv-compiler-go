import GoFV.SSA.Sem.Env
import GoFV.SSA.Sem.Ptr

/-!
# Runtime contracts (`docs/plans/semantics.md` §5, phase P3)

Trusted behaviour of the runtime entry points the compiler calls, on Go-typed arguments, as
`Contract`s (`Env.runtime`): allocation (`newobject`, `makeslice`, `growslice` with the
runtime's capacity growth and size classes), copying and clearing (`memmove`,
`memclrNoHeapPointers`, `typedmemmove`, `typedslicecopy`), comparison (`memequal`), boxing
(`convT*`), strings (`concatstring*`, `slicebytetostring`, `stringtoslicebyte`), `print*`
(no observable effect: output is not modelled), and the panicking entry points.

Type descriptors are read from memory (`Size_` at offset 0, `PtrBytes` at 8: export
`config rttype.*`), as the global image lays them out (`Sem/Image.lean`). New objects are heap
allocations (`Mem.allocHeap`); pointer identity of the runtime's caches (`staticuint64s`,
`zerobase` for every zero-sized allocation) is modelled only for `zerobase`. An allocation
larger than `maxModelAlloc` is `stuck` (the executable model holds every byte).
-/

namespace GoFV.SSA.Sem

namespace Runtime

/-- `maxAlloc` on 64-bit Linux (`runtime/malloc.go`). -/
def maxAlloc : Nat := 2 ^ 48

/-- Largest allocation the executable model performs. -/
def maxModelAlloc : Nat := 2 ^ 24

/-- The concrete 64-bit word at `p + off`. -/
def readWord (m : Mem) (p : Ptr) (off : Nat) : Option Nat := do
  let bs ← m.read (p.add (BitVec.ofNat 64 off)) 8
  bytesNat? bs

/-- `et.Size_` and `et.PtrBytes` of a type descriptor. -/
def typeInfo (m : Mem) (et : Ptr) : Option (Nat × Nat) := do
  return (← readWord m et 0, ← readWord m et 8)

/-- The size classes of `internal/runtime/gc/sizeclasses.go`. -/
def sizeClasses : List Nat :=
  [0, 8, 16, 24, 32, 48, 64, 80, 96, 112, 128, 144, 160, 176, 192, 208, 224, 240, 256, 288, 320,
   352, 384, 416, 448, 480, 512, 576, 640, 704, 768, 896, 1024, 1152, 1280, 1408, 1536, 1792,
   2048, 2304, 2688, 3072, 3200, 3456, 4096, 4864, 5376, 6144, 6528, 6784, 6912, 8192, 9472,
   9728, 10240, 10880, 12288, 13568, 14336, 16384, 18432, 19072, 20480, 21760, 24576, 27264,
   28672, 32768]

/-- `roundupsize(size, noscan)` (`runtime/msize.go`): the size of the block `mallocgc`
allocates, minus the malloc header of a scanned object above 512 bytes. -/
def roundupsize (size : Nat) (noscan : Bool) : Nat :=
  let req := if !noscan && size > 512 then size + 8 else size
  if req ≤ 32768 - 8 then
    ((sizeClasses.find? (req ≤ ·)).getD req) - (req - size)
  else (req + 8191) / 8192 * 8192

/-- `nextslicecap(newLen, oldCap)` (`runtime/slice.go`). -/
def nextslicecap (newLen oldCap : Nat) : Nat :=
  let double := oldCap + oldCap
  if newLen > double then newLen
  else if oldCap < 256 then double
  else
    -- newcap += (newcap + 3*256) >> 2 until newcap ≥ newLen (at most ~log_{1.25} steps)
    let rec grow : Nat → Nat → Nat
      | 0, c => c
      | k + 1, c => if c ≥ newLen then c else grow k (c + (c + 768) / 4)
    grow 256 oldCap

/-- An integer argument as a signed value. -/
def asInt : Val → Option Int
  | .int _ x => some x.toInt
  | _ => none

/-- A pointer argument (nil for the integer 0). -/
def asPtr : Val → Option Ptr
  | .ptr p => some p
  | .int .w64 x => some (Ptr.ofAddr x)
  | _ => none

/-- A string argument: data pointer and length. -/
def asString : Val → Option (Ptr × Nat)
  | .agg [p, n] => do return (← asPtr p, (← asInt n).toNat)
  | _ => none

/-- A fresh zeroed allocation of `n` bytes (`zerobase` for 0). -/
def alloc (m : Mem) (n : Nat) : Option (Ptr × Mem) :=
  if n == 0 then some (⟨.global "runtime.zerobase", 0⟩, m)
  else if n > maxModelAlloc then none
  else some (m.allocHeap (Array.replicate n (.b 0)))

/-- A fresh allocation holding `bs`. -/
def allocBytes (m : Mem) (bs : Array Byte) : Option (Ptr × Mem) :=
  if bs.isEmpty then some (⟨.global "runtime.zerobase", 0⟩, m)
  else if bs.size > maxModelAlloc then none
  else some (m.allocHeap bs)

/-- A Go string value. -/
def strVal (p : Ptr) (n : Nat) : Val := .agg [.ptr p, .i64 (BitVec.ofNat 64 n)]

/-- A Go slice value. -/
def sliceVal (p : Ptr) (len cap : Nat) : Val :=
  .agg [.ptr p, .i64 (BitVec.ofNat 64 len), .i64 (BitVec.ofNat 64 cap)]

/-- Turn an `Option` result into a contract outcome (`none`: invalid arguments or access). -/
def ok? (name : String) : Option (List Val × Mem) → COutcome
  | some (rs, m) => .returned rs m
  | none => .stuck s!"{name}: invalid arguments or memory access"

/-- `runtime.newobject(typ)`. -/
def newobject : Contract := fun args _ m => ok? "newobject" do
  let [t] := args | none
  let (size, _) ← typeInfo m (← asPtr t)
  let (p, m) ← alloc m size
  return ([.ptr p], m)

/-- `runtime.makeslice(et, len, cap)`: `makeslice: len out of range` / `cap out of range`. -/
def makeslice : Contract := fun args _ m =>
  match args with
  | [et, len, cap] =>
    match asPtr et, asInt len, asInt cap with
    | some et, some len, some cap =>
      match typeInfo m et with
      | none => .stuck "makeslice: bad type"
      | some (size, _) =>
        let bad (n : Int) := n < 0 || size * n.toNat > maxAlloc
        if bad cap || len < 0 || len > cap then
          if bad len then .panicked (.error "makeslice: len out of range") m
          else .panicked (.error "makeslice: cap out of range") m
        else ok? "makeslice" do
          let (p, m) ← alloc m (size * cap.toNat)
          return ([.ptr p], m)
    | _, _, _ => .stuck "makeslice: bad arguments"
  | _ => .stuck "makeslice: bad arguments"

/-- `runtime.growslice(oldPtr, newLen, oldCap, num, et)` (`runtime/slice.go`). -/
def growslice : Contract := fun args _ m =>
  match args with
  | [old, newLen, oldCap, num, et] =>
    match asPtr old, asInt newLen, asInt oldCap, asInt num, asPtr et with
    | some old, some newLen, some oldCap, some num, some et =>
      match typeInfo m et with
      | none => .stuck "growslice: bad type"
      | some (size, ptrBytes) =>
        if newLen < 0 then .panicked (.error "growslice: len out of range") m
        else if size == 0 then
          .returned [sliceVal ⟨.global "runtime.zerobase", 0⟩ newLen.toNat newLen.toNat] m
        else
          let oldLen := (newLen - num).toNat
          let newcap := nextslicecap newLen.toNat oldCap.toNat
          let capmem := roundupsize (newcap * size) (ptrBytes == 0)
          let newcap := capmem / size
          if newcap * size > maxAlloc then .panicked (.error "growslice: len out of range") m
          else ok? "growslice" do
            let (p, m) ← alloc m (newcap * size)
            let bs ← m.read old (oldLen * size)
            let m ← m.write p bs
            return ([sliceVal p newLen.toNat newcap], m)
    | _, _, _, _, _ => .stuck "growslice: bad arguments"
  | _ => .stuck "growslice: bad arguments"

/-- `runtime.growsliceBuf(oldPtr, newLen, oldCap, num, et, bufPtr, bufLen)`: the caller's
stack buffer when the new length fits (capacity rounded up to a size class, the tail zeroed),
else `growslice`. -/
def growsliceBuf : Contract := fun args clo m =>
  match args with
  | [old, newLen, oldCap, num, et, buf, bufLen] =>
    match asPtr old, asInt newLen, asInt num, asPtr et, asPtr buf, asInt bufLen with
    | some old, some newLen, some num, some et, some buf, some bufLen =>
      if newLen > bufLen then growslice [.ptr old, .i64 (BitVec.ofInt 64 newLen), oldCap, .i64 (BitVec.ofInt 64 num), .ptr et] clo m
      else
        match typeInfo m et with
        | none => .stuck "growsliceBuf: bad type"
        | some (size, ptrBytes) =>
          if size == 0 then .stuck "growsliceBuf: zero-sized element" else
          ok? "growsliceBuf" do
            let oldLen := (newLen - num).toNat
            let m ← if old != buf && oldLen != 0 then do
                m.write buf (← m.read old (oldLen * size))
              else pure m
            let newCap := roundupsize (newLen.toNat * size) (ptrBytes == 0) / size
            let m ← if newLen.toNat < newCap then
                m.write (buf.add (BitVec.ofNat 64 (newLen.toNat * size)))
                  (Array.replicate ((newCap - newLen.toNat) * size) (.b 0))
              else pure m
            return ([sliceVal buf newLen.toNat newCap], m)
    | _, _, _, _, _, _ => .stuck "growsliceBuf: bad arguments"
  | _ => .stuck "growsliceBuf: bad arguments"

/-- `runtime.moveSlice(et, old, len, cap)` / `moveSliceNoScan(elemSize, old, len, cap)`
(`noScan`: the first argument is the element size): the slice copied to the heap. The Go
signature returns `(unsafe.Pointer, int, int)`; the compiler's call (`ssagen`) types the result
as one slice, which is what the contract returns. -/
def moveSlice (noScan : Bool) : Contract := fun args _ m => ok? "moveSlice" do
  let [e, old, len, cap] := args | none
  let size ← if noScan then (asInt e).map Int.toNat else (typeInfo m (← asPtr e)).map (·.1)
  let old ← asPtr old
  let len := (← asInt len).toNat
  let cap := (← asInt cap).toNat
  if cap == 0 then
    return ([sliceVal (if old.isNil then old else ⟨.global "runtime.zerobase", 0⟩) 0 0], m)
  let bs ← m.read old (cap * size)
  let (p, m) ← allocBytes m bs
  return ([sliceVal p len cap], m)

/-- `runtime.moveSliceNoCap(et, old, len)` / `moveSliceNoCapNoScan(elemSize, old, len)`. -/
def moveSliceNoCap (noScan : Bool) : Contract := fun args _ m => ok? "moveSliceNoCap" do
  let [e, old, len] := args | none
  let (size, ptrBytes) ← if noScan then (asInt e).map (·.toNat, 0) else typeInfo m (← asPtr e)
  let old ← asPtr old
  let len := (← asInt len).toNat
  if len == 0 then
    return ([sliceVal (if old.isNil then old else ⟨.global "runtime.zerobase", 0⟩) 0 0], m)
  let capmem := roundupsize (len * size) (noScan || ptrBytes == 0)
  let cap := capmem / size
  let (p, m) ← alloc m (cap * size)
  let m ← m.write p (← m.read old (len * size))
  return ([sliceVal p len cap], m)

/-- The size-specialized allocators `mallocgcTinySC*`, `mallocgcSmallNoScanSC*`,
`mallocgcSmallScanNoHeaderSC*` (`size, typ, needzero`): a zeroed object of `size` bytes. -/
def mallocSized : Contract := fun args _ m => ok? "mallocgc" do
  let [size, _, _] := args | none
  let (p, m) ← alloc m (← asInt size).toNat
  return ([.ptr p], m)

/-- `runtime.memmove(to, from, n)`. -/
def memmove : Contract := fun args _ m => ok? "memmove" do
  let [to, fr, n] := args | none
  let bs ← m.read (← asPtr fr) (← asInt n).toNat
  return ([], ← m.write (← asPtr to) bs)

/-- `runtime.memclrNoHeapPointers(ptr, n)`. -/
def memclr : Contract := fun args _ m => ok? "memclrNoHeapPointers" do
  let [p, n] := args | none
  return ([], ← m.write (← asPtr p) (Array.replicate (← asInt n).toNat (.b 0)))

/-- `runtime.typedmemmove(typ, dst, src)`. -/
def typedmemmove : Contract := fun args _ m => ok? "typedmemmove" do
  let [t, dst, src] := args | none
  let (size, _) ← typeInfo m (← asPtr t)
  let bs ← m.read (← asPtr src) size
  return ([], ← m.write (← asPtr dst) bs)

/-- `runtime.typedslicecopy(typ, dstPtr, dstLen, srcPtr, srcLen) int`. -/
def typedslicecopy : Contract := fun args _ m => ok? "typedslicecopy" do
  let [t, dst, dl, src, sl] := args | none
  let (size, _) ← typeInfo m (← asPtr t)
  let n := min (← asInt dl).toNat (← asInt sl).toNat
  let bs ← m.read (← asPtr src) (n * size)
  return ([.i64 (BitVec.ofNat 64 n)], ← m.write (← asPtr dst) bs)

/-- `runtime.memequal(a, b, size) bool`. -/
def memequal : Contract := fun args _ m => ok? "memequal" do
  let [a, b, n] := args | none
  let n := (← asInt n).toNat
  let x ← m.read (← asPtr a) n
  let y ← m.read (← asPtr b) n
  if x.any (· == .poison) || y.any (· == .poison) then none
  return ([.bool (x == y)], m)

/-- `runtime.convT16/32/64(v)`, `convTstring(s)`, `convTslice(s)`: a new object holding `v`
(`n` bytes, shape `t`). -/
def convT (t : Ty) : Contract := fun args _ m => ok? "convT" do
  let [v] := args | none
  let (p, m) ← allocBytes m (encode t v)
  return ([.ptr p], m)

/-- `runtime.convT(typ, v unsafe.Pointer)`, `convTnoptr`: a new copy of `*v`. -/
def convTtyp : Contract := fun args _ m => ok? "convT" do
  let [t, v] := args | none
  let (size, _) ← typeInfo m (← asPtr t)
  let bs ← m.read (← asPtr v) size
  let (p, m) ← allocBytes m bs
  return ([.ptr p], m)

/-- The bytes of string `s`. -/
def strBytes (m : Mem) (s : Val) : Option (Array Byte) := do
  let (p, n) ← asString s
  m.read p n

/-- A new string with bytes `bs` (the empty string has a nil data pointer). -/
def newString (m : Mem) (bs : Array Byte) : Option (Val × Mem) :=
  if bs.isEmpty then some (strVal Ptr.null 0, m)
  else do
    let (p, m) ← allocBytes m bs
    return (strVal p bs.size, m)

/-- `runtime.concatstring{2..5}(buf, a, b, …)`. -/
def concatstringN : Contract := fun args _ m => ok? "concatstring" do
  let _ :: ss := args | none
  let bs ← ss.foldlM (fun acc s => do return acc ++ (← strBytes m s)) #[]
  let (s, m) ← newString m bs
  return ([s], m)

/-- `runtime.concatstrings(buf, a []string)`. -/
def concatstrings : Contract := fun args _ m => ok? "concatstrings" do
  let [_, .agg [ap, an, _]] := args | none
  let ap ← asPtr ap
  let n := (← asInt an).toNat
  let bs ← (List.range n).foldlM (fun acc i => do
    let w ← m.read (ap.add (BitVec.ofNat 64 (16 * i))) 8
    let p ← asPtr (decodePtr w)
    let len ← readWord m ap (16 * i + 8)
    return acc ++ (← m.read p len)) #[]
  let (s, m) ← newString m bs
  return ([s], m)

/-- `runtime.slicebytetostring(buf, ptr, n)`. -/
def slicebytetostring : Contract := fun args _ m => ok? "slicebytetostring" do
  let [_, p, n] := args | none
  let bs ← m.read (← asPtr p) (← asInt n).toNat
  let (s, m) ← newString m bs
  return ([s], m)

/-- `runtime.stringtoslicebyte(buf *tmpBuf, s)`: into `buf` (capacity 32) when given and large
enough, else a new array with capacity `roundupsize(len)`. -/
def stringtoslicebyte : Contract := fun args _ m => ok? "stringtoslicebyte" do
  let [buf, s] := args | none
  let bs ← strBytes m s
  let buf ← asPtr buf
  if !buf.isNil && bs.size ≤ 32 then
    return ([sliceVal buf bs.size 32], ← m.write buf bs)
  else
    let cap := roundupsize bs.size true
    let (p, m) ← alloc m cap
    return ([sliceVal p bs.size cap], ← m.write p bs)

/-- Entry points with no effect the semantics models (`print*`: output is not modelled). -/
def noEffect : Contract := fun _ _ m => .returned [] m

/-- A panicking entry point. -/
def panics (e : Panic) : Contract := fun _ _ m => .panicked e m

end Runtime

open Runtime in
/-- The runtime contracts (P1's panicking entry points and the ones above). -/
def Env.runtime : Env where
  extern
    | "runtime.panicdivide" => some (panics .divide)
    | "runtime.panicshift" => some (panics .shift)
    | "runtime.panicoverflow" => some (panics .overflow)
    | "runtime.newobject" => some newobject
    | "runtime.makeslice" => some makeslice
    | "runtime.growslice" | "runtime.growsliceNoAlias" => some growslice
    | "runtime.growsliceBuf" | "runtime.growsliceBufNoAlias" => some growsliceBuf
    | "runtime.moveSlice" => some (moveSlice false)
    | "runtime.moveSliceNoScan" => some (moveSlice true)
    | "runtime.moveSliceNoCap" => some (moveSliceNoCap false)
    | "runtime.moveSliceNoCapNoScan" => some (moveSliceNoCap true)
    | "runtime.panicmakeslicelen" => some (panics (.error "makeslice: len out of range"))
    | "runtime.panicmakeslicecap" => some (panics (.error "makeslice: cap out of range"))
    | "runtime.memmove" => some memmove
    | "runtime.memclrNoHeapPointers" => some memclr
    | "runtime.typedmemmove" => some typedmemmove
    | "runtime.typedslicecopy" => some typedslicecopy
    | "runtime.memequal" => some memequal
    | "runtime.convT16" => some (convT (.int .w16))
    | "runtime.convT32" => some (convT (.int .w32))
    | "runtime.convT64" => some (convT (.int .w64))
    | "runtime.convTstring" => some (convT (.agg [(0, .ptr (some 1)), (8, .int .w64)] 16))
    | "runtime.convTslice" =>
      some (convT (.agg [(0, .ptr none), (8, .int .w64), (16, .int .w64)] 24))
    | "runtime.convT" | "runtime.convTnoptr" => some convTtyp
    | "runtime.concatstring2" | "runtime.concatstring3" | "runtime.concatstring4"
    | "runtime.concatstring5" => some concatstringN
    | "runtime.concatstrings" => some concatstrings
    | "runtime.slicebytetostring" => some slicebytetostring
    | "runtime.stringtoslicebyte" => some stringtoslicebyte
    | "runtime.printlock" | "runtime.printunlock" | "runtime.printnl" | "runtime.printsp"
    | "runtime.printint" | "runtime.printuint" | "runtime.printbool" | "runtime.printstring"
    | "runtime.printpointer" | "runtime.printhex" | "runtime.printslice"
    | "runtime.printfloat" | "runtime.printcomplex" => some noEffect
    | name =>
      if name.startsWith "runtime.mallocgcTinySC" || name.startsWith "runtime.mallocgcSmallNoScanSC" ||
          name.startsWith "runtime.mallocgcSmallScanNoHeaderSC" then some mallocSized
      else if name == "runtime.gopanic" || name == "runtime.throw" || name == "runtime.panicwrap" ||
          name == "runtime.panicnildottype" || name == "runtime.panicdottypeE" ||
          name == "runtime.panicdottypeI" || name == "runtime.fatal" then
        some (panics (.runtime name))
      else none

end GoFV.SSA.Sem

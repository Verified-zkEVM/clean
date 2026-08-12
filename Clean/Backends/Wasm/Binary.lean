/-
WASM binary emitter. Encodes the AST to binary WASM format using ByteArray.
-/
import Clean.Backends.Wasm.Ast

namespace Backends.Wasm.Binary

open Ast (ValType Instr Func Module BinOp UnOp RelOp)

/-! ## Named WASM opcodes and constants -/

-- Magic number and version
private def wasmMagic : List UInt8 := [0x00, 0x61, 0x73, 0x6D]
private def wasmVersion : List UInt8 := [0x01, 0x00, 0x00, 0x00]

-- Section IDs
private def sectionIdType     : ℕ := 1
private def sectionIdFunction : ℕ := 3
private def sectionIdMemory   : ℕ := 5
private def sectionIdExport   : ℕ := 7
private def sectionIdCode     : ℕ := 10
private def sectionIdData     : ℕ := 11

-- Block type encodings
private def blockTypeEmpty : UInt8 := 0x40

-- Value types (also encoded in vtOpc)
private def valtypeI32 : UInt8 := 0x7F
private def valtypeI64 : UInt8 := 0x7E

-- Control flow opcodes
private def opUnreachable : UInt8 := 0x00
private def opNop         : UInt8 := 0x01
private def opBlock       : UInt8 := 0x02
private def opLoop        : UInt8 := 0x03
private def opIf          : UInt8 := 0x04
private def opElse        : UInt8 := 0x05
private def opEnd         : UInt8 := 0x0B
private def opBr          : UInt8 := 0x0C
private def opBrIf        : UInt8 := 0x0D
private def opReturn      : UInt8 := 0x0F

-- Call opcodes
private def opCall        : UInt8 := 0x10

-- Local access opcodes
private def opLocalGet    : UInt8 := 0x20
private def opLocalSet    : UInt8 := 0x21
private def opLocalTee    : UInt8 := 0x22

-- Memory opcodes
private def opI32Load     : UInt8 := 0x28
private def opI64Load     : UInt8 := 0x29
private def opI32Store    : UInt8 := 0x36
private def opI64Store    : UInt8 := 0x37

-- Numeric opcodes
private def opI32Const    : UInt8 := 0x41
private def opI64Const    : UInt8 := 0x42
private def opI32Eq       : UInt8 := 0x46
private def opI32LtU      : UInt8 := 0x49
private def opI64Eq       : UInt8 := 0x51
private def opI32Eqz      : UInt8 := 0x45
private def opI64Eqz      : UInt8 := 0x50
private def opI64LtS      : UInt8 := 0x53
private def opI64LtU      : UInt8 := 0x54
private def opI64Ne       : UInt8 := 0x52
private def opI64GtS      : UInt8 := 0x55
private def opI64GtU      : UInt8 := 0x56
private def opI64LeS      : UInt8 := 0x57
private def opI64LeU      : UInt8 := 0x58
private def opI64GeS      : UInt8 := 0x59
private def opI64GeU      : UInt8 := 0x5A
private def opI32Ne       : UInt8 := 0x47
private def opI32WrapI64  : UInt8 := 0xA7
private def opI64ExtI32U  : UInt8 := 0xAD
private def opDrop        : UInt8 := 0x1A
private def opSelect      : UInt8 := 0x1B

-- Stack opcodes
private def opI32BinopBase : UInt8 := 0x6A
private def opI64BinopBase : UInt8 := 0x7C

-- Type section
private def functypeOpcode  : UInt8 := 0x60

-- Memory section
private def memflagsNoMax   : UInt8 := 0x00
private def memoryCount     : UInt8 := 0x01

-- Export section
private def exportKindFunc   : UInt8 := 0x00
private def exportKindMem    : UInt8 := 0x02
private def memoryExportIndex : UInt8 := 0x00

-- Name section (custom section)
private def customSectionName : ℕ := 0
private def nameSubsectionFunctionNames : ℕ := 1

-- LEB128 encoding
private def leb128ContBit    : ℕ := 0x80   -- continuation bit (bit 7 set = more bytes)
private def leb128Limit      : ℕ := 128    -- 7-bit group size
private def leb128SignBit    : ℕ := 64     -- bit 6 of a 7-bit group
private def leb128PayloadMask : ℕ := 0x7F  -- low 7 bits

-- Signed-const two's-complement bounds for i32.const / i64.const
private def i32ConstSignBase  : ℕ := 2^31
private def i32ConstModulus   : ℕ := 2^32
private def i64ConstSignBase  : ℕ := 2^63
private def i64ConstModulus   : ℕ := 2^64

/-! ## LEB128 encoding with ByteArray -/

partial def putULEB128 (arr : ByteArray) (n : ℕ) : ByteArray :=
  if n < leb128Limit then arr.push (UInt8.ofNat n)
  else
    let b := n % leb128Limit
    putULEB128 (arr.push (UInt8.ofNat (b ||| leb128ContBit))) (n / leb128Limit)

/-- Signed LEB128 encoding. Handles both positive and negative values.
    Encodes in two's complement: for negative n, each 7-bit group is
    sign-extended in the final byte. -/
partial def putSLEB128 (arr : ByteArray) (n : ℤ) : ByteArray :=
  let b := n % leb128Limit
  let rest := n / leb128Limit
  -- A byte is final if the remaining value is 0 AND the sign bit (bit 6) is clear,
  -- OR if the remaining value is -1 AND the sign bit is set (sign extension complete).
  if (rest = 0 && b < leb128SignBit) || (rest = -1 && b ≥ leb128SignBit) then
    arr.push (UInt8.ofNat (b.toNat &&& leb128PayloadMask))
  else
    putSLEB128 (arr.push (UInt8.ofNat ((b.toNat &&& leb128PayloadMask) ||| leb128ContBit))) rest

/-! ## WASM value type opcodes -/

def vtOpc : ValType → UInt8
  | .i32 => valtypeI32
  | .i64 => valtypeI64

/-! ## Instruction encoding -/

def binopOffset : BinOp → ℕ
  | .add => 0  | .sub => 1  | .mul => 2
  | .div_u => 4 | .rem_u => 6
  | .and => 7  | .or => 8   | .xor => 9
  | .shl => 10 | .shr_s => 11 | .shr_u => 12
  | .rotl => 13 | .rotr => 14

/-- Label stack entry: (label name, nesting depth from current position). -/
abbrev LabelStack := List (String × ℕ)

/-- Look up a label in the stack and return its relative depth (0-indexed from innermost).
    Unknown labels are an error (never silently branch to depth 0). -/
def resolveLabel (stack : LabelStack) (label : String) : Except String ℕ :=
  match stack.findIdx? fun (l, _) => l = label with
  | some idx => pure idx
  | none => .error s!"encodeInstr: unknown label '${label}'"

/-- Encode a block type (empty or single value). -/
def encodeBlockType (arr : ByteArray) : Option ValType → ByteArray
  | none => arr.push blockTypeEmpty
  | some .i32 => arr.push valtypeI32
  | some .i64 => arr.push valtypeI64

/-- Encode memory alignment immediate. The align field is a power-of-2 exponent. -/
def encodeMemArg (arr : ByteArray) (offset align : ℕ) : ByteArray :=
  putULEB128 (putULEB128 arr align) offset

mutual
/-- Encode a single instruction. Unsupported instructions and unknown labels
    are errors, so a broken module fails at compile time rather than emitting
    silently-wrong WASM. -/
partial def encodeInstr (arr : ByteArray) (resolveCall : String → Except String ℕ) (labels : LabelStack) :
    Instr → Except String ByteArray
  | .const .i32 n => pure (putSLEB128 (arr.push opI32Const) (if n < i32ConstSignBase then (n : ℤ) else ((n : ℤ) - (i32ConstModulus : ℤ))))
  | .const .i64 n => pure (putSLEB128 (arr.push opI64Const) (if n < i64ConstSignBase then (n : ℤ) else ((n : ℤ) - (i64ConstModulus : ℤ))))
  | .binop .i32 op => pure (arr.push (UInt8.ofNat (opI32BinopBase.toNat + binopOffset op)))
  | .binop .i64 op => pure (arr.push (UInt8.ofNat (opI64BinopBase.toNat + binopOffset op)))
  | .unop .i32 .wrap_i64 => pure (arr.push opI32WrapI64)
  | .unop .i64 .extend_i32_u => pure (arr.push opI64ExtI32U)
  | .unop t op => .error s!"encodeInstr: unsupported unop {repr op} on {repr t}"
  | .relop .i32 .eq => pure (arr.push opI32Eq)
  | .relop .i64 .eq => pure (arr.push opI64Eq)
  | .relop .i32 .lt_u => pure (arr.push opI32LtU)
  | .relop .i64 .lt_u => pure (arr.push opI64LtU)
  | .relop .i32 .eqz => pure (arr.push opI32Eqz)
  | .relop .i64 .eqz => pure (arr.push opI64Eqz)
  | .relop .i64 .lt_s => pure (arr.push opI64LtS)
  | .relop .i64 .ne => pure (arr.push opI64Ne)
  | .relop .i64 .le_u => pure (arr.push opI64LeU)
  | .relop .i64 .ge_u => pure (arr.push opI64GeU)
  | .relop .i64 .gt_u => pure (arr.push opI64GtU)
  | .relop .i32 .ne => pure (arr.push opI32Ne)
  | .relop t op => .error s!"encodeInstr: unsupported relop {repr op} on {repr t}"
  | .localGet idx => pure (putULEB128 (arr.push opLocalGet) idx)
  | .localSet idx => pure (putULEB128 (arr.push opLocalSet) idx)
  | .localTee idx => pure (putULEB128 (arr.push opLocalTee) idx)
  | .call name => do
    let idx ← resolveCall name
    pure (putULEB128 (arr.push opCall) idx)
  | .br label => do
    let d ← resolveLabel labels label
    pure (putULEB128 (arr.push opBr) d)
  | .brIf label => do
    let d ← resolveLabel labels label
    pure (putULEB128 (arr.push opBrIf) d)
  | .block label result body => encodeBlock arr resolveCall labels opBlock label result body
  | .loop label result body => encodeBlock arr resolveCall labels opLoop label result body
  | .ifElse label result thenBody elseBody => do
    let arr := arr.push opIf
    let arr := encodeBlockType arr result
    let innerLabels := (label, 0) :: labels
    let arr ← thenBody.foldlM (fun a i => encodeInstr a resolveCall innerLabels i) arr
    if elseBody.isEmpty then pure (arr.push opEnd)
    else do
      let arr ← elseBody.foldlM (fun a i => encodeInstr a resolveCall innerLabels i) (arr.push opElse)
      pure (arr.push opEnd)
  | .memLoad .i32 off align => pure (encodeMemArg (arr.push opI32Load) off align)
  | .memLoad .i64 off align => pure (encodeMemArg (arr.push opI64Load) off align)
  | .memStore .i32 off align => pure (encodeMemArg (arr.push opI32Store) off align)
  | .memStore .i64 off align => pure (encodeMemArg (arr.push opI64Store) off align)
  | .drop => pure (arr.push opDrop)
  | .select => pure (arr.push opSelect)
  | .unreachable => pure (arr.push opUnreachable)
  | .nop => pure (arr.push opNop)
  | .return => pure (arr.push opReturn)

/-- Encode a block/loop body with correct result type and label tracking. -/
partial def encodeBlock (arr : ByteArray) (resolveCall : String → Except String ℕ) (labels : LabelStack)
    (opcode : UInt8) (label : String) (result : Option ValType) (body : List Instr) : Except String ByteArray := do
  let arr := arr.push opcode
  let arr := encodeBlockType arr result
  let innerLabels := (label, 0) :: labels.map fun (l, d) => (l, d + 1)
  let arr ← body.foldlM (fun a i => encodeInstr a resolveCall innerLabels i) arr
  pure (arr.push opEnd)
end

/-! ## Module encoding -/

def putSection (arr : ByteArray) (id : ℕ) (content : ByteArray) : ByteArray :=
  let arr := arr.push (UInt8.ofNat id)
  let arr := putULEB128 arr content.size
  arr ++ content

def encodeString (arr : ByteArray) (s : String) : ByteArray :=
  let utf8 := s.toUTF8
  let arr := putULEB128 arr utf8.size
  utf8.foldl (fun a b => a.push b) arr

/-- Encode a WASM module to binary. Unknown function names are errors, so a
    broken call cannot silently target function 0. -/
def Module.toBinary (m : Module) : Except String ByteArray := do
  let funcs := m.funcs
  let nameToIdx (name : String) : Except String ℕ :=
    match funcs.findIdx? (fun f => f.name == name) with
    | some idx => pure idx
    | none => .error s!"toBinary: unknown function '{name}'"

  -- Collect unique type signatures
  let sigs := funcs.map (fun f => (f.params.map Prod.snd, f.results))
  let uniqueSigs := List.reverse <| sigs.foldl (fun acc s => if acc.elem s then acc else s :: acc) []
  let sigIdx (sig : List ValType × List ValType) : Except String ℕ :=
    match uniqueSigs.findIdx? (fun s => s == sig) with
    | some idx => pure idx
    | none => .error "toBinary: signature not found"

  -- Type section
  let typeSec := uniqueSigs.foldl (fun (arr : ByteArray) (params, results) =>
    let arr := arr.push functypeOpcode
    let arr := putULEB128 arr params.length
    let arr := params.foldl (fun a t => a.push (vtOpc t)) arr
    putULEB128 arr results.length
    |> fun a => results.foldl (fun a' t => a'.push (vtOpc t)) a
  ) (putULEB128 ByteArray.empty uniqueSigs.length)

  -- Function section
  let funcSec ← funcs.foldlM (fun (arr : ByteArray) f => do
    let s ← sigIdx (f.params.map Prod.snd, f.results)
    pure (putULEB128 arr s)
  ) (putULEB128 ByteArray.empty funcs.length)

  -- Memory section: 1 memory, min pages only
  let memSec := ByteArray.empty.push memoryCount |>.push memflagsNoMax |> fun a => putULEB128 a m.memoryPages

  -- Export section
  let exportCount := 1 + (funcs.filter fun f => f.exportName.isSome).length
  let exportSec := putULEB128 ByteArray.empty exportCount
  -- Memory export
  let exportSec := encodeString exportSec "memory"
  let exportSec := exportSec.push exportKindMem |>.push memoryExportIndex
  -- Function exports
  let exportSec ← funcs.foldlM (fun (arr : ByteArray) f =>
    match f.exportName with
    | none => pure arr
    | some ename => do
      let arr := encodeString arr ename
      let arr := arr.push exportKindFunc
      let idx ← nameToIdx f.name
      pure (putULEB128 arr idx)
  ) exportSec

  -- Code section
  let codeCount := funcs.length
  let codeSec ← funcs.foldlM (fun (arr : ByteArray) f => do
    let locals := f.locals.map Prod.snd
    let localSec := putULEB128 ByteArray.empty locals.length
    let localSec := locals.foldl (fun a t =>
      (putULEB128 a 1).push (vtOpc t)
    ) localSec
    let bodyArr ← f.body.foldlM (fun a i => encodeInstr a nameToIdx [] i) localSec
    let funcBytes := bodyArr.push opEnd
    pure (putULEB128 arr funcBytes.size |> fun a => a ++ funcBytes)
  ) (putULEB128 ByteArray.empty codeCount)

  -- Name section (custom section id 0): maps function indices to names for debugging.
  -- Format: "name" string, subsection_id=1, subsection_size, count, entries.
  let nameSec ← do
    let nameMap ← funcs.foldlM (fun (arr : ByteArray) f => do
      let idx ← nameToIdx f.name
      pure (putULEB128 arr idx |> fun a => encodeString a f.name)
    ) (putULEB128 ByteArray.empty funcs.length)
    let subsec := putULEB128 ByteArray.empty nameSubsectionFunctionNames |> fun a => putULEB128 a nameMap.size |> fun a => a ++ nameMap
    pure (encodeString ByteArray.empty "name" ++ subsec)
  -- Data section (id 11): active segments initializing signal memory, e.g. the
  -- constant signal 0 = 1 (matching the Circom convention of static init).
  -- Per segment: memidx u32 (0), offset expr (i32.const + end), size, bytes.
  let dataSec := m.dataSegments.foldl (fun arr seg =>
    let (offset, bytes) := seg
    let arr := putULEB128 arr 0  -- memidx 0 (the single memory)
    let arr := arr.push opI32Const |> fun a => putSLEB128 a (offset : ℤ)
    let arr := arr.push opEnd
    let arr := putULEB128 arr bytes.length
    bytes.foldl (fun a b => a.push (UInt8.ofNat b)) arr
  ) (putULEB128 ByteArray.empty m.dataSegments.length)
  -- Assemble: magic + version + sections
  let arr := wasmMagic.foldl (fun a b => a.push b) ByteArray.empty
  let arr := wasmVersion.foldl (fun a b => a.push b) arr
  let arr := putSection arr sectionIdType typeSec
  let arr := putSection arr sectionIdFunction funcSec
  let arr := putSection arr sectionIdMemory memSec
  let arr := putSection arr sectionIdExport exportSec
  let arr := putSection arr sectionIdCode codeSec
  let arr := putSection arr sectionIdData dataSec
  let arr := putSection arr customSectionName nameSec  -- custom section = name section
  pure arr

end Backends.Wasm.Binary

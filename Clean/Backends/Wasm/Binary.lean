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
private def opI64LtU      : UInt8 := 0x65
private def opI32Eqz      : UInt8 := 0x45
private def opI64Eqz      : UInt8 := 0x50
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

-- Export kinds
private def exportKindFunc   : UInt8 := 0x00
private def exportKindMem    : UInt8 := 0x02

-- Code section
private def codeLocalGroup   : UInt8 := 1

-- LEB128 encoding
private def leb128ContBit    : ℕ := 0x80
private def leb128Limit      : ℕ := 128

/-! ## LEB128 encoding with ByteArray -/

partial def putULEB128 (arr : ByteArray) (n : ℕ) : ByteArray :=
  if n < leb128Limit then arr.push (UInt8.ofNat n)
  else
    let b := n % leb128Limit
    putULEB128 (arr.push (UInt8.ofNat (b ||| leb128ContBit))) (n / leb128Limit)

/-- Signed LEB128 encoding. Not yet implemented for negative values;
    the backend never emits negative immediates, so this is a safe no-op. -/
def putSLEB128 (arr : ByteArray) (n : ℤ) : ByteArray :=
  if n ≥ 0 then putULEB128 arr n.toNat
  else arr -- Not reached: the AST never produces negative immediates

/-! ## WASM value type opcodes -/

def vtOpc : ValType → UInt8
  | .i32 => valtypeI32
  | .i64 => valtypeI64

/-! ## Instruction encoding -/

def binopOffset : BinOp → ℕ
  | .add => 0  | .sub => 1  | .mul => 2
  | .div_u => 4 | .rem_u => 6
  | .and => 7  | .or => 8   | .xor => 9
  | .shl => 10 | .shr_u => 11 | .shr_s => 12
  | .rotl => 13 | .rotr => 14

/-- Label stack entry: (label name, nesting depth from current position). -/
abbrev LabelStack := List (String × ℕ)

/-- Look up a label in the stack and return its relative depth (0-indexed from innermost). -/
def resolveLabel (stack : LabelStack) (label : String) : ℕ :=
  match stack.findIdx? fun (l, _) => l = label with
  | some idx => idx
  | none => 0

/-- Encode a block type (empty or single value). -/
def encodeBlockType (arr : ByteArray) : Option ValType → ByteArray
  | none => arr.push blockTypeEmpty
  | some .i32 => arr.push valtypeI32
  | some .i64 => arr.push valtypeI64

/-- Encode memory alignment immediate. The align field is a power-of-2 exponent. -/
def encodeMemArg (arr : ByteArray) (offset align : ℕ) : ByteArray :=
  putULEB128 (putULEB128 arr align) offset

mutual
partial def encodeInstr (arr : ByteArray) (resolveCall : String → ℕ) (labels : LabelStack) : Instr → ByteArray
  | .const .i32 n => putULEB128 (arr.push opI32Const) n
  | .const .i64 n => putULEB128 (arr.push opI64Const) n
  | .binop .i32 op => arr.push (UInt8.ofNat (opI32BinopBase.toNat + binopOffset op))
  | .binop .i64 op => arr.push (UInt8.ofNat (opI64BinopBase.toNat + binopOffset op))
  | .unop .i32 .wrap_i64 => arr.push opI32WrapI64
  | .unop .i64 .extend_i32_u => arr.push opI64ExtI32U
  | .unop _ _ => arr
  | .relop .i32 .eq => arr.push opI32Eq
  | .relop .i64 .eq => arr.push opI64Eq
  | .relop .i32 .lt_u => arr.push opI32LtU
  | .relop .i64 .lt_u => arr.push opI64LtU
  | .relop .i32 .eqz => arr.push opI32Eqz
  | .relop .i64 .eqz => arr.push opI64Eqz
  | .relop _ _ => arr
  | .localGet idx => putULEB128 (arr.push opLocalGet) idx
  | .localSet idx => putULEB128 (arr.push opLocalSet) idx
  | .localTee idx => putULEB128 (arr.push opLocalTee) idx
  | .call name => putULEB128 (arr.push opCall) (resolveCall name)
  | .br label => putULEB128 (arr.push opBr) (resolveLabel labels label)
  | .brIf label => putULEB128 (arr.push opBrIf) (resolveLabel labels label)
  | .block label result body => encodeBlock arr resolveCall labels opBlock label result body
  | .loop label result body => encodeBlock arr resolveCall labels opLoop label result body
  | .ifElse result thenBody elseBody =>
    let arr := arr.push opIf
    let arr := encodeBlockType arr result
    let innerLabels := ("", 0) :: labels
    let arr := thenBody.foldl (fun a i => encodeInstr a resolveCall innerLabels i) arr
    let arr := if elseBody.isEmpty then arr else
      (arr.push opElse) |> fun a => elseBody.foldl (fun a' i => encodeInstr a' resolveCall innerLabels i) a
    arr.push opEnd
  | .memLoad .i32 off align => encodeMemArg (arr.push opI32Load) off align
  | .memLoad .i64 off align => encodeMemArg (arr.push opI64Load) off align
  | .memStore .i32 off align => encodeMemArg (arr.push opI32Store) off align
  | .memStore .i64 off align => encodeMemArg (arr.push opI64Store) off align
  | .drop => arr.push opDrop
  | .select => arr.push opSelect
  | .unreachable => arr.push opUnreachable
  | .nop => arr.push opNop
  | .return => arr.push opReturn

/-- Encode a block/loop body with correct result type and label tracking. -/
partial def encodeBlock (arr : ByteArray) (resolveCall : String → ℕ) (labels : LabelStack)
    (opcode : UInt8) (label : String) (result : Option ValType) (body : List Instr) : ByteArray :=
  let arr := arr.push opcode
  let arr := encodeBlockType arr result
  let innerLabels := (label, 0) :: labels.map fun (l, d) => (l, d + 1)
  let arr := body.foldl (fun a i => encodeInstr a resolveCall innerLabels i) arr
  arr.push opEnd
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

def Module.toBinary (m : Module) : ByteArray :=
  let funcs := m.funcs
  let nameToIdx (name : String) : ℕ :=
    funcs.findIdx? (fun f => f.name == name) |>.getD 0

  -- Collect unique type signatures
  let sigs := funcs.map (fun f => (f.params.map Prod.snd, f.results))
  let uniqueSigs := List.reverse <| sigs.foldl (fun acc s => if acc.elem s then acc else s :: acc) []
  let sigIdx (sig : List ValType × List ValType) : ℕ :=
    uniqueSigs.findIdx? (fun s => s == sig) |>.getD 0

  -- Type section
  let typeSec := uniqueSigs.foldl (fun (arr : ByteArray) (params, results) =>
    let arr := arr.push functypeOpcode
    let arr := putULEB128 arr params.length
    let arr := params.foldl (fun a t => a.push (vtOpc t)) arr
    putULEB128 arr results.length
    |> fun a => results.foldl (fun a' t => a'.push (vtOpc t)) a
  ) (putULEB128 ByteArray.empty 0 |> fun a => putULEB128 a uniqueSigs.length)

  -- Function section
  let funcSec := funcs.foldl (fun (arr : ByteArray) f =>
    putULEB128 arr (sigIdx (f.params.map Prod.snd, f.results))
  ) (putULEB128 ByteArray.empty 0 |> fun a => putULEB128 a funcs.length)

  -- Memory section: 1 memory, min pages only
  let memSec := ByteArray.empty.push 0x01 |>.push memflagsNoMax |> fun a => putULEB128 a m.memoryPages

  -- Export section
  let exportCount := 1 + (funcs.filter fun f => f.exportName.isSome).length
  let exportSec := putULEB128 ByteArray.empty 0 |> fun a => putULEB128 a exportCount
  -- Memory export
  let exportSec := encodeString exportSec "memory"
  let exportSec := exportSec.push exportKindMem |>.push 0x00
  -- Function exports
  let exportSec := funcs.foldl (fun (arr : ByteArray) f =>
    match f.exportName with
    | none => arr
    | some ename =>
      let arr := encodeString arr ename
      let arr := arr.push exportKindFunc
      putULEB128 arr (nameToIdx f.name)
  ) exportSec

  -- Code section
  let codeCount := funcs.length
  let codeSec := funcs.foldl (fun (arr : ByteArray) f =>
    let locals := f.locals.map Prod.snd
    let localSec := putULEB128 ByteArray.empty 0 |> fun a => putULEB128 a locals.length
    let localSec := locals.foldl (fun a t =>
      putULEB128 (a.push codeLocalGroup) 0 |> fun a' => a'.push (vtOpc t)
    ) localSec
    let bodyArr := f.body.foldl (fun a i => encodeInstr a nameToIdx [] i) localSec
    let funcBytes := bodyArr.push opEnd
    putULEB128 (putULEB128 arr 0) funcBytes.size |> fun a => a ++ funcBytes
  ) (putULEB128 ByteArray.empty 0 |> fun a => putULEB128 a codeCount)

  -- Assemble: magic + version + sections
  let arr := wasmMagic.foldl (fun a b => a.push b) ByteArray.empty
  let arr := wasmVersion.foldl (fun a b => a.push b) arr
  let arr := putSection arr sectionIdType typeSec
  let arr := putSection arr sectionIdFunction funcSec
  let arr := putSection arr sectionIdMemory memSec
  let arr := putSection arr sectionIdExport exportSec
  let arr := putSection arr sectionIdCode codeSec
  arr

end Backends.Wasm.Binary

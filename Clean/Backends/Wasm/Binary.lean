/-
WASM binary emitter. Encodes the AST to binary WASM format using ByteArray.
-/
import Clean.Backends.Wasm.Ast

namespace Backends.Wasm.Binary

open Ast (ValType Instr Func Module BinOp UnOp RelOp)

/-! ## LEB128 encoding with ByteArray -/

partial def putULEB128 (arr : ByteArray) (n : ℕ) : ByteArray :=
  if n < 128 then arr.push (UInt8.ofNat n)
  else
    let b := n % 128
    putULEB128 (arr.push (UInt8.ofNat (b ||| 0x80))) (n / 128)

def putSLEB128 (arr : ByteArray) (n : ℤ) : ByteArray :=
  if n ≥ 0 then putULEB128 arr n.toNat else arr  -- simplified

/-! ## WASM value type opcodes -/

def vtOpc : ValType → UInt8
  | .i32 => 0x7F
  | .i64 => 0x7E

/-! ## Instruction encoding -/

def binopOffset : BinOp → ℕ
  | .add => 0  | .sub => 1  | .mul => 2
  | .div_u => 4 | .rem_u => 6
  | .and => 7  | .or => 8   | .xor => 9
  | .shl => 10 | .shr_u => 11 | .shr_s => 12
  | .rotl => 13 | .rotr => 14

partial def encodeInstr (arr : ByteArray) (resolveCall : String → ℕ) : Instr → ByteArray
  | .const .i32 n => putULEB128 (arr.push 0x41) n
  | .const .i64 n => putULEB128 (arr.push 0x42) n
  | .binop .i32 op => arr.push (UInt8.ofNat (0x6A + binopOffset op))
  | .binop .i64 op => arr.push (UInt8.ofNat (0x7C + binopOffset op))
  | .unop .i32 .wrap_i64 => arr.push 0xA7
  | .unop .i64 .extend_i32_u => arr.push 0xAD
  | .unop _ _ => arr
  | .relop .i32 .eq => arr.push 0x46
  | .relop .i64 .eq => arr.push 0x51
  | .relop .i32 .lt_u => arr.push 0x49
  | .relop .i64 .lt_u => arr.push 0x65
  | .relop .i64 .eqz => arr.push 0x50
  | .relop _ _ => arr
  | .localGet idx => putULEB128 (arr.push 0x20) idx
  | .localSet idx => putULEB128 (arr.push 0x21) idx
  | .localTee idx => putULEB128 (arr.push 0x22) idx
  | .call name => putULEB128 (arr.push 0x10) (resolveCall name)
  | .br _ => putULEB128 (arr.push 0x0C) 0
  | .brIf _ => putULEB128 (arr.push 0x0D) 0
  | .block _ _ body => encodeBlock arr resolveCall 0x02 body
  | .loop _ _ body => encodeBlock arr resolveCall 0x03 body
  | .ifElse result thenBody elseBody =>
    let arr := arr.push 0x04
    let arr := match result with
      | [] => arr.push 0x40  -- empty block type
      | [t] => arr.push (vtOpc t)  -- single result type
      | _ => arr.push 0x40  -- multi-value: placeholder (needs type section ref)
    let arr := thenBody.foldl (fun a i => encodeInstr a resolveCall i) arr
    let arr := if elseBody.isEmpty then arr else
      (arr.push 0x05) |> fun a => elseBody.foldl (fun a' i => encodeInstr a' resolveCall i) a
    arr.push 0x0B
  | .memLoad .i32 off _ => putULEB128 (putULEB128 (arr.push 0x28) 2) off
  | .memLoad .i64 off _ => putULEB128 (putULEB128 (arr.push 0x29) 3) off
  | .memStore .i32 off _ => putULEB128 (putULEB128 (arr.push 0x36) 2) off
  | .memStore .i64 off _ => putULEB128 (putULEB128 (arr.push 0x37) 3) off
  | .drop => arr.push 0x1A
  | .select => arr.push 0x1B
  | .unreachable => arr.push 0x00
  | .nop => arr.push 0x01
  | .return => arr.push 0x0F

/-- Encode a block/loop body. -/
partial def encodeBlock (arr : ByteArray) (resolveCall : String → ℕ) (opcode : UInt8) (body : List Instr) : ByteArray :=
  let arr := arr.push opcode
  let arr := arr.push 0x40  -- empty result type
  let arr := body.foldl (fun a i => encodeInstr a resolveCall i) arr
  arr.push 0x0B

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
  let uniqueSigs := sigs.dedup
  let sigIdx (sig : List ValType × List ValType) : ℕ :=
    uniqueSigs.findIdx? (fun s => s == sig) |>.getD 0

  -- Type section
  let typeSec := uniqueSigs.foldl (fun (arr : ByteArray) (params, results) =>
    let arr := arr.push 0x60  -- functype
    let arr := putULEB128 arr params.length
    let arr := params.foldl (fun a t => a.push (vtOpc t)) arr
    putULEB128 arr results.length
    |> fun a => results.foldl (fun a' t => a'.push (vtOpc t)) a
  ) (putULEB128 ByteArray.empty 0 |> fun a => putULEB128 a uniqueSigs.length)

  -- Function section: map each function to type index
  let funcSec := funcs.foldl (fun (arr : ByteArray) f =>
    putULEB128 arr (sigIdx (f.params.map Prod.snd, f.results))
  ) (putULEB128 ByteArray.empty 0 |> fun a => putULEB128 a funcs.length)

  -- Memory section: 1 memory, min pages only
  let memSec := ByteArray.empty.push 0x01 |>.push 0x00 |> fun a => putULEB128 a m.memoryPages

  -- Export section
  let exportCount := 1 + (funcs.filter fun f => f.exportName.isSome).length
  let exportSec := putULEB128 ByteArray.empty 0 exportCount
  -- Memory export
  let exportSec := encodeString exportSec "memory"
  let exportSec := exportSec.push 0x02 |>.push 0x00  -- mem idx 0
  -- Function exports
  let exportSec := funcs.foldl (fun (arr : ByteArray) f =>
    match f.exportName with
    | none => arr
    | some ename =>
      let arr := encodeString arr ename
      let arr := arr.push 0x00  -- func export
      putULEB128 arr (nameToIdx f.name)
  ) exportSec

  -- Code section: function bodies
  let codeCount := funcs.length
  let codeSec := funcs.foldl (fun (arr : ByteArray) f =>
    -- Locals
    let locals := f.locals.map Prod.snd
    let localSec := putULEB128 ByteArray.empty 0 locals.length
    let localSec := locals.foldl (fun a t =>
      putULEB128 (a.push (UInt8.ofNat 1)) 0 |> fun a' => a'.push (vtOpc t)
    ) localSec
    -- Body
    let bodyArr := f.body.foldl (fun a i => encodeInstr a nameToIdx i) localSec
    let funcBytes := bodyArr.push 0x0B  -- end
    putULEB128 arr 0 funcBytes.size |> fun a => a ++ funcBytes
  ) (putULEB128 ByteArray.empty 0 codeCount)

  -- Assemble: magic + version + sections
  let arr := ByteArray.empty.push 0x00 |>.push 0x61 |>.push 0x73 |>.push 0x6D  -- magic
  let arr := arr.push 0x01 |>.push 0x00 |>.push 0x00 |>.push 0x00  -- version 1
  let arr := putSection arr 1 typeSec
  let arr := putSection arr 3 funcSec
  let arr := putSection arr 5 memSec
  let arr := putSection arr 7 exportSec
  let arr := putSection arr 10 codeSec
  arr

end Backends.Wasm.Binary

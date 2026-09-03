/-
Minimal typed WASM AST for the Clean backend. Covers only the subset of WASM we use:
i64/i32 arithmetic, locals, function calls, control flow, memory operations.
-/
import Mathlib.Data.Nat.Basic

namespace Backends.Wasm.Ast

/-! ## Types -/

inductive ValType | i32 | i64
deriving Repr, DecidableEq

/-! ## Operations -/

inductive BinOp
  | add | sub | mul | div_u | rem_u
  | and | or | xor | shl | shr_u | shr_s | rotl | rotr
deriving Repr, DecidableEq

inductive UnOp
  | clz | ctz | popcnt | extend_i32_u | wrap_i64
deriving Repr, DecidableEq

inductive RelOp
  | eq | ne | lt_u | lt_s | gt_u | gt_s | le_u | le_s | ge_u | ge_s
  | eqz
deriving Repr, DecidableEq

/-! ## Instructions -/

inductive Instr
  | const (t : ValType) (n : ℕ)
  | binop (t : ValType) (op : BinOp)
  | unop (t : ValType) (op : UnOp)
  | relop (t : ValType) (op : RelOp)
  | localGet (idx : ℕ)
  | localSet (idx : ℕ)
  | localTee (idx : ℕ)
  | call (name : String)
  | block (label : String) (result : Option ValType) (body : List Instr)
  | loop (label : String) (result : Option ValType) (body : List Instr)
  | br (label : String)
  | brIf (label : String)
  | ifElse (label : String) (result : Option ValType) (thenBody : List Instr) (elseBody : List Instr)
  | memLoad (t : ValType) (offset : ℕ) (align : ℕ)
  | memStore (t : ValType) (offset : ℕ) (align : ℕ)
  | drop | select | unreachable | nop | return
deriving Repr, Inhabited

/-! ## Functions and Modules -/

structure Func where
  name : String
  exportName : Option String := none
  params : List (String × ValType) := []
  results : List ValType := []
  locals : List (String × ValType) := []
  body : List Instr := []
deriving Repr, Inhabited

structure Module where
  memoryPages : ℕ := 1
  dataSegments : List (ℕ × List ℕ) := []
  funcs : List Func := []
deriving Repr, Inhabited

end Backends.Wasm.Ast

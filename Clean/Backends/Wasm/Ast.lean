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

/-! ## Text emitter (WAT format) -/

def ValType.toString : ValType → String
  | .i32 => "i32"
  | .i64 => "i64"

def BinOp.toString : BinOp → String
  | .add => "add"    | .sub => "sub"    | .mul => "mul"
  | .div_u => "div_u" | .rem_u => "rem_u"
  | .and => "and"    | .or => "or"      | .xor => "xor"
  | .shl => "shl"    | .shr_u => "shr_u" | .shr_s => "shr_s"
  | .rotl => "rotl"  | .rotr => "rotr"

def UnOp.toString : UnOp → String
  | .clz => "clz" | .ctz => "ctz" | .popcnt => "popcnt"
  | .extend_i32_u => "extend_i32_u"
  | .wrap_i64 => "wrap_i64"

def RelOp.toString : RelOp → String
  | .eq => "eq" | .ne => "ne" | .lt_u => "lt_u" | .lt_s => "lt_s"
  | .gt_u => "gt_u" | .gt_s => "gt_s" | .le_u => "le_u" | .le_s => "le_s"
  | .ge_u => "ge_u" | .ge_s => "ge_s" | .eqz => "eqz"

def escapeStr (s : String) : String :=
  s.map fun c => if c == '"' then '\\' else c

def Instr.toString (i : Instr) (indent : ℕ := 0) : String :=
  let pad := String.join (List.replicate indent "  ")
  match i with
  | .const t n => s!"{pad}{ValType.toString t}.const {n}"
  | .binop t op => s!"{pad}{ValType.toString t}.{BinOp.toString op}"
  | .unop t op => s!"{pad}{ValType.toString t}.{UnOp.toString op}"
  | .relop t op => s!"{pad}{ValType.toString t}.{RelOp.toString op}"
  | .localGet idx => s!"{pad}local.get {idx}"
  | .localSet idx => s!"{pad}local.set {idx}"
  | .localTee idx => s!"{pad}local.tee {idx}"
  | .call name => pad ++ "call " ++ name
  | .block label result body =>
    let resultStr := match result with | some t => s!" (result {ValType.toString t})" | none => ""
    let labelStr := if label.isEmpty then "" else s!" ${label}"
    pad ++ "block" ++ labelStr ++ resultStr ++ "\n" ++ bodyListToString body (indent+1) ++ "\n" ++ pad ++ "end"
  | .loop label result body =>
    let resultStr := match result with | some t => s!" (result {ValType.toString t})" | none => ""
    let labelStr := if label.isEmpty then "" else s!" ${label}"
    pad ++ "loop" ++ labelStr ++ resultStr ++ "\n" ++ bodyListToString body (indent+1) ++ "\n" ++ pad ++ "end"
  | .br label => pad ++ "br $" ++ label
  | .brIf label => pad ++ "br_if $" ++ label
  | .ifElse label result thenBody elseBody =>
    let resultStr := match result with
      | none => ""
      | some t => s!" (result {ValType.toString t})"
    let labelStr := if label.isEmpty then "" else s!" ${label}"
    let thenStr := bodyListToString thenBody (indent+1)
    let elseStr := if elseBody.isEmpty then "" else
      s!"\n{pad}else\n{bodyListToString elseBody (indent+1)}"
    s!"{pad}if" ++ labelStr ++ resultStr ++ "\n" ++ thenStr ++ elseStr ++ "\n" ++ pad ++ "end"
  | .memLoad t offset _ => s!"{pad}{ValType.toString t}.load offset={offset}"
  | .memStore t offset _ => s!"{pad}{ValType.toString t}.store offset={offset}"
  | .drop => s!"{pad}drop"
  | .select => s!"{pad}select"
  | .unreachable => s!"{pad}unreachable"
  | .nop => s!"{pad}nop"
  | .return => s!"{pad}return"
where
  bodyListToString (body : List Instr) (indent : ℕ) : String :=
    String.intercalate "\n" (body.map fun instr => instr.toString indent)

def Func.toString (f : Func) : String :=
  let paramItem (n : String) (t : ValType) : String :=
    if n.isEmpty then s!"(param {ValType.toString t})"
    else ("(param " ++ n ++ " " ++ ValType.toString t ++ ")")
  let paramsStr := String.intercalate " " (f.params.map fun (n, t) => paramItem n t)
  let resultStr := match f.results with
    | [] => ""
    | [t] => s!" (result {ValType.toString t})"
    | ts => s!" (result {String.intercalate " " (ts.map ValType.toString)})"
  let localItem (n : String) (t : ValType) : String :=
    if n.isEmpty then s!"(local {ValType.toString t})"
    else ("(local " ++ n ++ " " ++ ValType.toString t ++ ")")
  let localsStr := String.intercalate " " (f.locals.map fun (n, t) => localItem n t)
  let exportStr := match f.exportName with
    | some n => s!" (export \"{escapeStr n}\")" | none => ""
  let bodyStr := String.intercalate "\n" (f.body.map fun i => i.toString 2)
  ("  (func " ++ f.name) ++ exportStr ++ " " ++ paramsStr ++ resultStr ++ "\n    " ++ localsStr ++ "\n" ++ bodyStr ++ "\n  )"

def Module.toString (m : Module) : String :=
  let memoryStr := s!"  (memory (export \"memory\") {m.memoryPages})"
  let byteToEscape (b : ℕ) : String :=
    let hi := b / 16
    let lo := b % 16
    let d (n : ℕ) : Char := Nat.digitChar n
    s!"\\{d hi}{d lo}"
  let dataSegmentStr (off : ℕ) (bytes : List ℕ) : String :=
    s!"  (data (i32.const {off}) \"{String.join (bytes.map byteToEscape)}\")"
  let dataStrs := m.dataSegments.map fun (off, bytes) => dataSegmentStr off bytes
  let funcsStr := String.intercalate "\n\n" (m.funcs.map Func.toString)
  String.intercalate "\n" ([
    "(module",
    memoryStr
  ] ++ dataStrs ++ [
    funcsStr,
    ")"
  ])

end Backends.Wasm.Ast

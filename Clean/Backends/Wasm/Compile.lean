/-
WASM WAT Compiler: WitgenIR → WAT text
-/
import Clean.Circuit.WitnessIR
import Clean.Circuit.Expression
import Clean.Circuit.Operations

namespace Backends.Wasm

open Witgen (FExpr NExpr BExpr VExpr Step WitgenIR)

variable {F : Type} [FiniteField F]

/-! ## Builder -/

structure Builder where
  lines : List String := []
  indent : ℕ := 0

def Builder.push (line : String) (b : Builder) : Builder :=
  let pad := String.join (List.replicate b.indent "    ")
  { b with lines := (pad ++ line) :: b.lines }

def Builder.indented (n : ℕ) (f : Builder → Builder) (b : Builder) : Builder :=
  let inner := f { b with indent := b.indent + n }
  { inner with indent := b.indent }

def Builder.build (b : Builder) : String :=
  String.intercalate "\n" b.lines.reverse

/-! ## Field helpers -/

def fieldHelpers (p : ℕ) : String :=
  let ps := toString p
  let pm2 := toString (p - 2)
  String.intercalate "\n" [
    s!"  ;; Field arithmetic modulo {ps}",
    s!"  (func $fadd (param i64) (param i64) (result i64)",
    s!"    local.get 0 local.get 1 i64.add",
    s!"    i64.const {ps} i64.rem_u)",
    "",
    s!"  (func $fmul (param i64) (param i64) (result i64)",
    s!"    local.get 0 local.get 1 i64.mul",
    s!"    i64.const {ps} i64.rem_u)",
    "",
    s!"  (func $fsub (param i64) (param i64) (result i64)",
    s!"    (local $d i64)",
    s!"    local.get 0 local.get 1 i64.sub local.tee $d",
    s!"    i64.const 0 i64.lt_s",
    s!"    (if (result i64) (then local.get $d i64.const {ps} i64.add)",
    s!"    (else local.get $d))",
    s!"    i64.const {ps} i64.rem_u)",
    "",
    s!"  (func $fpow (param i64) (param i64) (result i64)",
    s!"    (local $r i64) (local $b i64) (local $e i64)",
    s!"    i64.const 1 local.set $r",
    s!"    local.get 0 local.set $b",
    s!"    local.get 1 local.set $e",
    s!"    (block $done (loop $loop",
    s!"      local.get $e i64.eqz br_if $done",
    s!"      local.get $e i64.const 1 i64.and i64.eqz",
    s!"      (if (then) (else local.get $r local.get $b call $fmul local.set $r))",
    s!"      local.get $b local.get $b call $fmul local.set $b",
    s!"      local.get $e i64.const 1 i64.shr_u local.set $e",
    s!"      br $loop))",
    s!"    local.get $r)",
    "",
    s!"  (func $finv (param i64) (result i64)",
    s!"    local.get 0 i64.const {pm2} call $fpow)"
  ]

/-! ## Variable mapping -/

structure VarMap where
  env : List (ℕ × ℕ) := []
  nextLocal : ℕ := 0

def VarMap.init (numInputs : ℕ) : VarMap :=
  { env := List.range numInputs |>.map fun i => (i, i), nextLocal := numInputs }

def VarMap.lookup (vm : VarMap) (idx : ℕ) : ℕ :=
  match vm.env.find? fun (i, _) => i = idx with
  | some (_, w) => w
  | none => idx

def VarMap.alloc (vm : VarMap) (m : ℕ) (baseVarIdx : ℕ) : VarMap × List ℕ :=
  let wasmLocals := List.range m |>.map fun i => vm.nextLocal + i
  let newEnv := (List.range m |>.map fun i => (baseVarIdx + i, vm.nextLocal + i)) ++ vm.env
  ({ env := newEnv, nextLocal := vm.nextLocal + m }, wasmLocals)

/-! ## Expression compilers -/

mutual

partial def compileFExpr (vm : VarMap) : FExpr F → Builder → Builder
  | .const c, b => b.push s!"i64.const {FiniteField.val c}"
  | .add a e, b => let b := compileFExpr vm a b; let b := compileFExpr vm e b; b.push "call $fadd"
  | .mul a e, b => let b := compileFExpr vm a b; let b := compileFExpr vm e b; b.push "call $fmul"
  | .inv a, b => let b := compileFExpr vm a b; b.push "call $finv"
  | .expr (.var i), b => b.push s!"local.get {vm.lookup i.index}"
  | .expr (.const c), b => b.push s!"i64.const {FiniteField.val c}"
  | .expr (.add a e), b => let b := compileFExpr vm (.expr a) b; let b := compileFExpr vm (.expr e) b; b.push "call $fadd"
  | .expr (.mul a e), b => let b := compileFExpr vm (.expr a) b; let b := compileFExpr vm (.expr e) b; b.push "call $fmul"
  | .ite c t e, b =>
    let b := compileBExpr vm c b
    let b := b.push "(if (result i64) (then"
    let b := Builder.indented 1 (compileFExpr vm t) b
    let b := b.push ") (else"
    let b := Builder.indented 1 (compileFExpr vm e) b
    b.push "))"
  | .ofNat n, b => compileNExpr vm n b
  | .localVar _, b => b.push "i64.const 0  ;; localVar"
  | .envGet _, b => b.push "i64.const 0  ;; envGet"
  | .listGet _ _, b => b.push "i64.const 0  ;; listGet"
  | .dataGet _ _ _ _, b => b.push "i64.const 0  ;; dataGet"
  | .hintGet _ _ _ _, b => b.push "i64.const 0  ;; hintGet"

partial def compileNExpr (vm : VarMap) : NExpr F → Builder → Builder
  | .const n, b => b.push s!"i64.const {n}"
  | .val x, b => compileFExpr vm x b
  | .idx, b => b.push "i64.const 0"
  | .localVar _, b => b.push "i64.const 0"
  | .add a e, b => let b := compileNExpr vm a b; let b := compileNExpr vm e b; b.push "i64.add"
  | .mul a e, b => let b := compileNExpr vm a b; let b := compileNExpr vm e b; b.push "i64.mul"
  | .div a e, b => let b := compileNExpr vm a b; let b := compileNExpr vm e b; b.push "i64.div_u"
  | .mod a e, b => let b := compileNExpr vm a b; let b := compileNExpr vm e b; b.push "i64.rem_u"
  | .land a e, b => let b := compileNExpr vm a b; let b := compileNExpr vm e b; b.push "i64.and"
  | .lor a e, b => let b := compileNExpr vm a b; let b := compileNExpr vm e b; b.push "i64.or"
  | .lxor a e, b => let b := compileNExpr vm a b; let b := compileNExpr vm e b; b.push "i64.xor"
  | .shiftL a e, b => let b := compileNExpr vm a b; let b := compileNExpr vm e b; b.push "i64.shl"
  | .shiftR a e, b => let b := compileNExpr vm a b; let b := compileNExpr vm e b; b.push "i64.shr_u"
  | .ite c t e, b =>
    let b := compileBExpr vm c b
    let b := b.push "(if (result i64) (then"
    let b := Builder.indented 1 (compileNExpr vm t) b
    let b := b.push ") (else"
    let b := Builder.indented 1 (compileNExpr vm e) b
    b.push "))"

partial def compileBExpr (vm : VarMap) : BExpr F → Builder → Builder
  | .true, b => b.push "i64.const 1"
  | .false, b => b.push "i64.const 0"
  | .feq a e, b => let b := compileFExpr vm a b; let b := compileFExpr vm e b; b.push "i64.eq"
  | .lt a e, b => let b := compileNExpr vm a b; let b := compileNExpr vm e b; b.push "i64.lt_u"
  | .neq a e, b => let b := compileNExpr vm a b; let b := compileNExpr vm e b; b.push "i64.eq  i64.eqz"
  | .not x, b => let b := compileBExpr vm x b; b.push "i64.eqz"
  | .and a e, b => let b := compileBExpr vm a b; let b := compileBExpr vm e b; b.push "i64.and"

end

/-! ## Module compilation -/

def processOps (numInputs : ℕ) : List (Operation F) → VarMap → ℕ → List String → VarMap × ℕ × List String
  | [], vm, _, lines => (vm, numInputs, lines.reverse)
  | .witness m code :: rest, vm, vi, acc =>
    match code with
    | .ir [] (.lit es) =>
      let (newAcc, newVm, newVi) := es.toList.foldl (fun ((ls, vm, vi) : List String × VarMap × ℕ) (e : FExpr F) =>
        let eb : Builder := {}
        let eb := compileFExpr vm e eb
        let (vm', wasmLocals) := vm.alloc 1 vi
        let wasmLocal := wasmLocals.head?.getD 0
        let newLs := s!"    local.set {wasmLocal}" :: eb.build :: ls
        (newLs, vm', vi + 1)
      ) (acc, vm, vi)
      processOps numInputs rest newVm newVi newAcc
    | .ir [] (.mapRange n _body) =>
      -- witnessAny: input variables, already mapped to function params. Just allocate slots.
      let newVm := { vm with nextLocal := vm.nextLocal + n }
      processOps numInputs rest newVm (vi + n) acc
    | _ => processOps numInputs rest vm vi acc
  | _ :: rest, vm, vi, acc => processOps numInputs rest vm vi acc

def compileModule (fieldPrime numInputs : ℕ) (ops : List (Operation F)) : String :=
  let vm := VarMap.init numInputs
  let (finalVm, _, bodyLines) := processOps numInputs ops vm numInputs []

  let totalWitness := finalVm.nextLocal - numInputs
  let returnLines := List.range totalWitness |>.map fun i =>
    s!"    local.get {numInputs + i}"

  let allBody := String.intercalate "\n" (bodyLines ++ returnLines)
  let inputParams := String.intercalate " "
    (List.range numInputs |>.map fun i => s!"(param $in_{i} i64)")
  let localDecls := String.intercalate " "
    (List.range totalWitness |>.map fun _ => "(local i64)")
  let resultTypes := String.intercalate " "
    (List.replicate totalWitness "i64")

  String.intercalate "\n" [
    s!"(module",
    s!"  (memory (export \"memory\") 1)",
    fieldHelpers fieldPrime,
    s!"  (func (export \"witness\") {inputParams} (result {resultTypes})",
    s!"    {localDecls}",
    allBody,
    s!"  )",
    s!")"
  ]

end Backends.Wasm

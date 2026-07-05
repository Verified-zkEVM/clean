/-
WASM WAT Compiler: WitgenIR → WAT text
-/
import Clean.Circuit.WitnessIR
import Clean.Circuit.Expression
import Clean.Circuit.Operations

namespace Backends.Wasm

open Witgen (FExpr NExpr BExpr VExpr Step WitgenIR)

variable {F : Type} [FiniteField F]

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

def fieldHelpers (p : ℕ) : String :=
  let ps := toString p
  let pm2 := toString (p - 2)
  String.intercalate "\n" [
    s!"  ;; Field arithmetic modulo {ps}",
    s!"  (func $fadd (param i64) (param i64) (result i64)",
    s!"    local.get 0 local.get 1 i64.add i64.const {ps} i64.rem_u)",
    s!"  (func $fmul (param i64) (param i64) (result i64)",
    s!"    local.get 0 local.get 1 i64.mul i64.const {ps} i64.rem_u)",
    s!"  (func $fsub (param i64) (param i64) (result i64)",
    s!"    (local $d i64) local.get 0 local.get 1 i64.sub local.tee $d",
    s!"    i64.const 0 i64.lt_s",
    s!"    (if (result i64) (then local.get $d i64.const {ps} i64.add) (else local.get $d))",
    s!"    i64.const {ps} i64.rem_u)",
    s!"  (func $fpow (param i64) (param i64) (result i64)",
    s!"    (local $r i64) (local $b i64) (local $e i64)",
    s!"    i64.const 1 local.set $r  local.get 0 local.set $b  local.get 1 local.set $e",
    s!"    (block $done (loop $loop",
    s!"      local.get $e i64.eqz br_if $done",
    s!"      local.get $e i64.const 1 i64.and i64.eqz",
    s!"      (if (then) (else local.get $r local.get $b call $fmul local.set $r))",
    s!"      local.get $b local.get $b call $fmul local.set $b",
    s!"      local.get $e i64.const 1 i64.shr_u local.set $e br $loop))",
    s!"    local.get $r)",
    s!"  (func $finv (param i64) (result i64)",
    s!"    local.get 0 i64.const {pm2} call $fpow)" ]

structure VarMap where
  env : List (ℕ × ℕ) := []
  nextLocal : ℕ := 0
  loopIdx : Option ℕ := none
  letBase : ℕ := 0

def VarMap.init (numInputs : ℕ) : VarMap :=
  { env := List.range numInputs |>.map fun i => (i, i), nextLocal := numInputs }

def VarMap.lookup (vm : VarMap) (idx : ℕ) : ℕ :=
  match vm.env.find? fun (i, _) => i = idx with | some (_, w) => w | none => idx

def VarMap.alloc (vm : VarMap) (m : ℕ) (baseVarIdx : ℕ) : VarMap × List ℕ :=
  let wasmLocals := List.range m |>.map fun i => vm.nextLocal + i
  let newEnv := (List.range m |>.map fun i => (baseVarIdx + i, vm.nextLocal + i)) ++ vm.env
  ({ env := newEnv, nextLocal := vm.nextLocal + m, loopIdx := vm.loopIdx, letBase := vm.letBase }, wasmLocals)

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
    let b := Builder.indented 1 (compileFExpr vm e) b; b.push "))"
  | .ofNat n, b => compileNExpr vm n b
  | .localVar i, b => b.push s!"local.get {vm.lookup (vm.letBase + i)}"
  | .envGet _, b => b.push "i64.const 0  ;; envGet stub"
  | .listGet _ _, b => b.push "i64.const 0  ;; listGet stub"
  | .dataGet _ _ _ _, b => b.push "i64.const 0  ;; dataGet stub"
  | .hintGet _ _ _ _, b => b.push "i64.const 0  ;; hintGet stub"

partial def compileNExpr (vm : VarMap) : NExpr F → Builder → Builder
  | .const n, b => b.push s!"i64.const {n}"
  | .val x, b => compileFExpr vm x b
  | .idx, b => match vm.loopIdx with | some _ => b.push "local.get $idx" | none => b.push "i64.const 0"
  | .localVar i, b => b.push s!"local.get {vm.lookup (vm.letBase + i)}"
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
    let b := Builder.indented 1 (compileNExpr vm e) b; b.push "))"

partial def compileBExpr (vm : VarMap) : BExpr F → Builder → Builder
  | .true, b => b.push "i64.const 1"
  | .false, b => b.push "i64.const 0"
  | .feq a e, b => let b := compileFExpr vm a b; let b := compileFExpr vm e b; b.push "i64.eq"
  | .lt a e, b => let b := compileNExpr vm a b; let b := compileNExpr vm e b; b.push "i64.lt_u"
  | .neq a e, b => let b := compileNExpr vm a b; let b := compileNExpr vm e b; b.push "i64.eq"
  | .not x, b => let b := compileBExpr vm x b; b.push "i64.eqz"
  | .and a e, b => let b := compileBExpr vm a b; let b := compileBExpr vm e b; b.push "i64.and"
end

/-! ## Module compilation -/

def compileSteps (vm : VarMap) (vi : ℕ) (steps : List (Step F)) : VarMap × ℕ × List String :=
  steps.foldl (fun ((vm, vi, ls) : VarMap × ℕ × List String) step =>
    match step with
    | .letF e =>
      let eb : Builder := {}
      let eb := compileFExpr vm e eb
      let (vm', locs) := vm.alloc 1 vi
      (vm', vi + 1, ls ++ [eb.build, s!"    local.set {locs.head?.getD 0}"])
    | .letN e =>
      let eb : Builder := {}
      let eb := compileNExpr vm e eb
      let (vm', locs) := vm.alloc 1 vi
      (vm', vi + 1, ls ++ [eb.build, s!"    local.set {locs.head?.getD 0}"])
  ) (vm, vi, [])

def compileLit (vm : VarMap) (vi : ℕ) (acc : List String) (es : List (FExpr F)) : VarMap × ℕ × List String :=
  es.foldl (fun ((vm, vi, ls) : VarMap × ℕ × List String) (e : FExpr F) =>
    let eb : Builder := {}
    let eb := compileFExpr vm e eb
    let (vm', locs) := vm.alloc 1 vi
    (vm', vi + 1, ls ++ [eb.build, s!"    local.set {locs.head?.getD 0}"])
  ) (vm, vi, acc)

def compileVExpr (vm : VarMap) (vi : ℕ) (acc : List String) : {m : ℕ} → VExpr F m → VarMap × ℕ × List String
  | _, .lit es => compileLit vm vi acc es.toList
  | _, .mapRange n body =>
    match body with
    | .envGet _ => (vm, vi, acc)
    | _ =>
      let (vmOut, _) := vm.alloc n vi
      let outBase := vmOut.nextLocal - n
      let ls := (List.range n).foldl (fun (ls : List String) (i : ℕ) =>
        let vmB := { vmOut with loopIdx := some 0 }
        let eb : Builder := {}
        let eb := compileFExpr vmB body eb
        ls ++ [s!"    i64.const {i}", "    local.set $idx", eb.build, s!"    local.set {outBase + i}"]
      ) acc
      ({ vmOut with loopIdx := none }, vi + n, ls)
  | _, .append _ _ => (vm, vi, "    ;; append NYI" :: acc)

def flattenOp : Operation F → List (FlatOperation F)
  | .witness m code => [.witness m code]
  | .assert e => [.assert e]
  | .lookup l => [.lookup l]
  | .interact i => [.interact i]
  | .subcircuit s => s.ops.toFlat

def flattenOps (ops : List (Operation F)) : List (FlatOperation F) :=
  match ops with
  | [] => []
  | op :: rest => flattenOp op ++ flattenOps rest

def processFlatOps (numInputs : ℕ) : List (FlatOperation F) → VarMap → ℕ → List String → VarMap × ℕ × List String
  | [], vm, _, lines => (vm, numInputs, lines)
  | .witness _ (.ir steps vexpr) :: rest, vm, vi, acc =>
    let vmStep := { vm with letBase := vi }
    let (vmS, viS, stepLines) := compileSteps vmStep vi steps
    let (vmOut, viOut, outLines) := compileVExpr vmS viS stepLines vexpr
    processFlatOps numInputs rest vmOut viOut (acc ++ outLines)
  | _ :: rest, vm, vi, acc => processFlatOps numInputs rest vm vi acc

def compileModule (fieldPrime numInputs : ℕ) (ops : List (Operation F)) : String :=
  let vm := VarMap.init numInputs
  let flatOps := flattenOps ops
  let (finalVm, _, bodyLines) := processFlatOps numInputs flatOps vm numInputs []
  let tw := finalVm.nextLocal - numInputs
  let totalSignals := 1 + numInputs + tw
  let ps := toString fieldPrime
  -- Memory layout: 0=computed_flag, 4=SRWM(word0), 8=signal_array(totalSignals*4 bytes)
  let srwmBase := 4
  let signalBase := 8
  let inputParams := String.intercalate " " (List.range numInputs |>.map fun i => s!"(param $in_{i} i64)")
  let locals := String.intercalate " "
    ((List.replicate tw "(local i64)") ++ ["(local $idx i64)"])
  let rets := List.range tw |>.map fun i => s!"    local.get {numInputs + i}"
  let computeBody := String.intercalate "\n" (bodyLines ++ rets)
  let results := if tw > 0 then
    s!"(result {String.intercalate " " (List.replicate tw "i64")})" else ""
  -- Input load lines: read each input from memory as i32, extend to i64 for computation
  let inputLoads := String.intercalate "\n" (List.range numInputs |>.map fun i =>
    s!"    i32.const {signalBase + (1 + i) * 4} i32.load  i64.extend_i32_u  local.set $in_{i}")
  -- Push inputs onto stack for calling $compute
  let inputPush := String.intercalate "\n" (List.range numInputs |>.map fun i =>
    s!"    local.get $in_{i}")
  -- Output store for getWitness: wrap i64 to i32, store to signal array
  let outputStoresW := String.intercalate "\n" (List.range tw |>.map fun i =>
    s!"    i32.const {signalBase + (1 + numInputs + i) * 4}  local.get $w_{i}  i32.wrap_i64  i32.store")
  -- snarkjs ABI exports
  let snarkjsExports := String.intercalate "\n\n" [
    s!"  (func (export \"getFieldNumLen32\") (result i32) i32.const 1)",
    s!"  (func (export \"getRawPrime\")  i32.const {srwmBase}  i32.const {fieldPrime}  i32.store)",
    s!"  (func (export \"readSharedRWMemory\") (param i32) (result i32)",
    s!"    i32.const {srwmBase}  local.get 0  i32.const 4  i32.mul  i32.add  i32.load)",
    s!"  (func (export \"writeSharedRWMemory\") (param $j i32) (param $v i32)",
    s!"    i32.const {srwmBase}  local.get $j  i32.const 4  i32.mul  i32.add  local.get $v  i32.store)",
    s!"  (func (export \"getInputSignalSize\") (param i32) (param i32) (result i32) i32.const {numInputs})",
    s!"  (func (export \"getInputSize\") (result i32) i32.const {numInputs})",
    s!"  (func (export \"getWitnessSize\") (result i32) i32.const {totalSignals})",
    s!"  (func (export \"setInputSignal\") (param $hMSB i32) (param $hLSB i32) (param $idx i32)",
    s!"    i32.const {signalBase + 4}  local.get $idx  i32.const 4  i32.mul  i32.add",
    s!"    i32.const {srwmBase}  i32.load",
    s!"    i32.store)",
    s!"  (func (export \"getWitness\") (param $i i32)",
    s!"    (local $tmp i32) {String.intercalate " " (List.range numInputs |>.map fun i => s!"(local $in_{i} i64)")} {String.intercalate " " (List.range tw |>.map fun i => s!"(local $w_{i} i64)")} (local $idx i64)",
    s!"    i32.const 0  i32.load  i32.eqz",
    s!"    (if (then",
    s!"{inputLoads}",
    s!"{inputPush}",
    s!"      call $compute",
    s!"{String.intercalate "\n" (List.range tw |>.reverse.map fun i => s!"      local.set $w_{i}")}",
    s!"{outputStoresW}",
    s!"      i32.const {signalBase}  i32.const 1  i32.store",
    s!"      i32.const 0  i32.const 1  i32.store",
    s!"    ))",
    s!"    i32.const 0",
    s!"    i32.const {signalBase}  local.get $i  i32.const 4  i32.mul  i32.add  i32.load",
    s!"    i32.store offset={srwmBase})",
    s!"  (func (export \"getMessageChar\") (result i32) i32.const 0)",
    s!"  (func (export \"getVersion\") (result i32) i32.const 2)",
    s!"  (func (export \"getMinorVersion\") (result i32) i32.const 0)",
    s!"  (func (export \"getPatchVersion\") (result i32) i32.const 0)",
    s!"  (func (export \"init\") (param i32) i32.const 0 i32.const 0 i32.store  i32.const {signalBase} i32.const 1 i32.store)"
  ]
  String.intercalate "\n" [
    s!"(module",
    s!"  (memory (export \"memory\") 1)",
    s!"  ;; Pre-initialize signal[0] = 1 (constant)",
    s!"  (data (i32.const {signalBase}) \"\\01\\00\\00\\00\")",
    fieldHelpers fieldPrime,
    s!"  ;; Internal compute function (our existing witness logic)",
    s!"  (func $compute {inputParams} {results}",
    s!"    {locals}",
    computeBody,
    s!"  )",
    s!"  ;; Direct witness export (for testing)",
    s!"  (func (export \"witness\") {inputParams} {results}",
    s!"    {locals}",
    computeBody,
    s!"  )",
    snarkjsExports,
    s!")"
  ]

end Backends.Wasm

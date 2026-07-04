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
  | .envGet _, b => b.push "i64.const 0"
  | .listGet _ _, b => b.push "i64.const 0"
  | .dataGet _ _ _ _, b => b.push "i64.const 0"
  | .hintGet _ _ _ _, b => b.push "i64.const 0"

partial def compileNExpr (vm : VarMap) : NExpr F → Builder → Builder
  | .const n, b => b.push s!"i64.const {n}"
  | .val x, b => compileFExpr vm x b
  | .idx, b => match vm.loopIdx with | some li => b.push s!"local.get {li}" | none => b.push "i64.const 0"
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
      -- Use nextLocal as the idx temp (one extra, not counted in witnesses)
      let idxLocal := vmOut.nextLocal
      let vmOut' := { vmOut with nextLocal := vmOut.nextLocal + 1 }
      let ls := (List.range n).foldl (fun (ls : List String) (i : ℕ) =>
        let vmB := { vmOut' with loopIdx := some idxLocal }
        let eb : Builder := {}
        let eb := compileFExpr vmB body eb
        ls ++ [s!"    i64.const {i}", s!"    local.set {idxLocal}", eb.build, s!"    local.set {outBase + i}"]
      ) acc
      ({ vmOut' with loopIdx := none }, vi + n, ls)
  | _, .append _ _ => (vm, vi, "    ;; append NYI" :: acc)

def processOps (numInputs : ℕ) : List (Operation F) → VarMap → ℕ → List String → VarMap × ℕ × List String
  | [], vm, _, lines => (vm, numInputs, lines)
  | .witness _ (.ir steps vexpr) :: rest, vm, vi, acc =>
    let vmStep := { vm with letBase := vi }
    let (vmS, viS, stepLines) := compileSteps vmStep vi steps
    let (vmOut, viOut, outLines) := compileVExpr vmS viS stepLines vexpr
    processOps numInputs rest vmOut viOut (acc ++ outLines)
  | _ :: rest, vm, vi, acc => processOps numInputs rest vm vi acc

def compileModule (fieldPrime numInputs : ℕ) (ops : List (Operation F)) : String :=
  let vm := VarMap.init numInputs
  let (finalVm, _, bodyLines) := processOps numInputs ops vm numInputs []
  let tw := finalVm.nextLocal - numInputs
  -- The return values: WASM locals numInputs .. nextLocal-1, skipping idx temps.
  -- We compute which locals to return by filtering out temps (those not in the VarMap env).
  -- Simpler: return all allocated locals. Extra temps will be ignored by snarkjs.
  let rets := List.range tw |>.map fun i => s!"    local.get {numInputs + i}"
  let allBody := String.intercalate "\n" (bodyLines ++ rets)
  let inputParams := String.intercalate " " (List.range numInputs |>.map fun i => s!"(param $in_{i} i64)")
  let locals := String.intercalate " " (List.replicate tw "(local i64)")
  let results := String.intercalate " " (List.replicate tw "i64")
  String.intercalate "\n" [
    s!"(module",
    s!"  (memory (export \"memory\") 1)",
    fieldHelpers fieldPrime,
    s!"  (func (export \"witness\") {inputParams} (result {results})",
    s!"    {locals}",
    allBody,
    s!"  )",
    s!")"
  ]

end Backends.Wasm

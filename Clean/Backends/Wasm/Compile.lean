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

/-! ## Single-word field arithmetic (numWords=1) -/

def genSingleWordArith (p : ℕ) : String :=
  let ps := toString p
  let pm2 := toString (p - 2)
  String.intercalate "\n" [
    s!"  ;; Field arithmetic modulo {ps} (single-word)",
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

/-! ## Multi-word field arithmetic (numWords > 1) -/

/-- Split a Nat into numWords 64-bit limbs (little-endian). -/
def toLimbs (n numWords : ℕ) : List ℕ :=
  List.range numWords |>.map fun i => (n >>> (i * 64)) % (2^64)

/-- Generate WAT for 64×64→128 multiplication helper. -/
def genMul64x64 : String :=
  String.intercalate "\n" [
    "  ;; 64×64 → 128-bit multiplication helper",
    "  (func $mul64x64 (param $a i64) (param $b i64) (result i64 i64)",
    "    (local $a_lo i64) (local $a_hi i64) (local $b_lo i64) (local $b_hi i64)",
    "    (local $p00 i64) (local $p01 i64) (local $p10 i64) (local $p11 i64)",
    "    (local $lo i64) (local $hi i64)",
    "    ;; Split a",
    "    local.get $a  i64.const 0xFFFFFFFF  i64.and  local.set $a_lo",
    "    local.get $a  i64.const 32  i64.shr_u  local.set $a_hi",
    "    ;; Split b",
    "    local.get $b  i64.const 0xFFFFFFFF  i64.and  local.set $b_lo",
    "    local.get $b  i64.const 32  i64.shr_u  local.set $b_hi",
    "    ;; p00 = a_lo * b_lo",
    "    local.get $a_lo  local.get $b_lo  i64.mul  local.set $p00",
    "    ;; p01 = a_lo * b_hi",
    "    local.get $a_lo  local.get $b_hi  i64.mul  local.set $p01",
    "    ;; p10 = a_hi * b_lo",
    "    local.get $a_hi  local.get $b_lo  i64.mul  local.set $p10",
    "    ;; p11 = a_hi * b_hi",
    "    local.get $a_hi  local.get $b_hi  i64.mul  local.set $p11",
    "    ;; lo = p00 + (p01<<32) + (p10<<32)",
    "    local.get $p00",
    "    local.get $p01  i64.const 0xFFFFFFFF  i64.and  i64.const 32  i64.shl  i64.add",
    "    local.get $p10  i64.const 0xFFFFFFFF  i64.and  i64.const 32  i64.shl  i64.add",
    "    local.set $lo",
    "    ;; hi = p11 + (p01>>32) + (p10>>32) + carry",
    "    local.get $p11",
    "    local.get $p01  i64.const 32  i64.shr_u  i64.add",
    "    local.get $p10  i64.const 32  i64.shr_u  i64.add",
    "    local.get $lo  local.get $p00  i64.lt_u  i64.extend_i32_u  i64.add",
    "    local.set $hi",
    "    local.get $lo  local.get $hi",
    "  )" ]

/-- Generate WAT for one limb multiplication + accumulation: c[k] += a[i]*b[j] with full carry propagation.
    Returns list of WAT lines. -/
def genLimbMulAccum (N i j : ℕ) : List String :=
  let k := i + j
  let body := [
    s!"    ;; c[{k}] += a[{i}] * b[{j}]",
    s!"    local.get $a{i}  local.get $b{j}  call $mul64x64",
    s!"    local.set $hi  local.set $lo",
    s!"    ;; c[{k}] += lo",
    s!"    local.get $c{k}  local.get $lo  i64.add  local.tee $c{k}",
    s!"    local.get $lo  i64.lt_u  i64.extend_i32_u  local.set $carry",
    s!"    ;; c[{k+1}] += hi + carry",
    s!"    local.get $hi  local.get $carry  i64.add  local.set $sum",
    s!"    local.get $c{k+1}  local.get $sum  i64.add  local.tee $c{k+1}",
    s!"    local.get $sum  i64.lt_u  i64.extend_i32_u  local.set $carry"
  ]
  -- Propagate carry through remaining limbs
  let propagate : List String :=
    (List.range ((2*N) - (k+2))) >>= fun d =>
      let idx := k + 2 + d
      [
        s!"    ;; propagate carry to c[{idx}]",
        s!"    local.get $c{idx}  local.get $carry  i64.add  local.tee $c{idx}",
        s!"    local.get $carry  i64.lt_u  i64.extend_i32_u  local.set $carry"
      ]
  body ++ propagate

/-- Generate WAT for multi-word modular multiplication with Barrett reduction.
    Schoolbook N×N→2N, then one-pass reduction: c_lo + c_hi * (2^(N*64) mod p),
    carry handling loop, and conditional subtraction of p. -/
def genFmul (p numWords : ℕ) : String :=
  let N := numWords
  let limbs2N := 2 * N
  let rModP := (2^(N*64)) % p
  let rLimbs := toLimbs rModP N
  let pLimbs := toLimbs p N
  -- Main schoolbook: a[0..N-1] × b[0..N-1] → c[0..2N-1]
  let schoolbook : List String :=
    (List.range N) >>= fun i =>
      (List.range N) >>= fun j =>
        genLimbMulAccum N i j
  -- Reduction schoolbook: c[N..2N-1] × r[0..N-1] → t[0..2N-1]
  let redMul : List String :=
    (List.range N) >>= fun i =>
      (List.range N) >>= fun j =>
        let k := i + j
        [
          s!"    ;; t[{k}] += c[{N+i}] * r[{j}]",
          s!"    local.get $c{N+i}  local.get $r{j}  call $mul64x64",
          s!"    local.set $hi  local.set $lo",
          s!"    local.get $t{k}  local.get $lo  i64.add  local.tee $t{k}",
          s!"    local.get $lo  i64.lt_u  i64.extend_i32_u  local.set $carry",
          s!"    local.get $hi  local.get $carry  i64.add  local.set $sum",
          s!"    local.get $t{k+1}  local.get $sum  i64.add  local.tee $t{k+1}",
          s!"    local.get $sum  i64.lt_u  i64.extend_i32_u  local.set $carry"
        ] ++ (List.range (limbs2N - (k+2))).map fun d =>
          let idx := k + 2 + d
          s!"    local.get $t{idx}  local.get $carry  i64.add  local.tee $t{idx}\n    local.get $carry  i64.lt_u  i64.extend_i32_u  local.set $carry"
  -- Add t[0..N-1] to c[0..N-1] (with carry)
  let addRedHeader : List String := [
    s!"    ;; c_lo += t_lo",
    s!"    local.get $c0  local.get $t0  i64.add  local.set $c0",
    s!"    local.get $c0  local.get $t0  i64.lt_u  i64.extend_i32_u  local.set $carry"
  ]
  let addRedBody : List String := (List.range (N-1)) >>= fun i =>
    let idx := i + 1
    [
      s!"    local.get $c{idx}  local.get $t{idx}  i64.add  local.get $carry  i64.add  local.set $c{idx}",
      s!"    local.get $c{idx}  local.get $t{idx}  i64.lt_u  i64.extend_i32_u",
      s!"    local.get $c{idx}  local.get $carry  i64.lt_u  i64.extend_i32_u  i64.or  local.set $carry"
    ]
  let addRed : List String := addRedHeader ++ addRedBody
  -- Carry elimination loop: while carry, add R_mod_p to c
  let carryLoopHeader : List String := [
    s!"    ;; While carry, add R_mod_p to c",
    s!"    (block $carry_done",
    s!"    (loop $carry_loop",
    s!"      local.get $carry  i64.eqz  br_if $carry_done",
    s!"      i64.const 0  local.set $carry",
    s!"      local.get $c0  local.get $r0  i64.add  local.tee $c0",
    s!"      local.get $c0  local.get $r0  i64.lt_u  i64.extend_i32_u  local.set $carry"
  ]
  let carryLoopBody : List String := (List.range (N-1)) >>= fun i =>
    let idx := i + 1
    [
      s!"      local.get $c{idx}  local.get $r{idx}  i64.add  local.get $carry  i64.add  local.tee $c{idx}",
      s!"      local.get $c{idx}  local.get $r{idx}  i64.lt_u  i64.extend_i32_u",
      s!"      local.get $c{idx}  local.get $carry  i64.lt_u  i64.extend_i32_u  i64.or  local.set $carry"
    ]
  let carryLoopFooter : List String := [
    s!"      br $carry_loop",
    s!"    ))"
  ]
  let carryLoop : List String := carryLoopHeader ++ carryLoopBody ++ carryLoopFooter
  -- Conditional subtraction of p: compute c - p → t, use t if c >= p (no borrow)
  let condSubHeader : List String := [
    s!"    ;; Compute c - p into t[0..{N-1}]",
    s!"    local.get $c0  local.get $p0  i64.sub  local.set $t0",
    s!"    local.get $c0  local.get $p0  i64.lt_u  i64.extend_i32_u  local.set $carry"
  ]
  let condSubBody : List String := (List.range (N-1)) >>= fun i =>
    let idx := i + 1
    [
      s!"    local.get $c{idx}  local.get $p{idx}  i64.sub  local.get $carry  i64.sub  local.set $t{idx}",
      s!"    local.get $c{idx}  local.get $p{idx}  i64.lt_u  i64.extend_i32_u",
      s!"    local.get $c{idx}  local.get $p{idx}  i64.eq  i64.extend_i32_u",
      s!"    local.get $carry  i64.and  i64.or  local.set $carry"
    ]
  let condSubIfHeader : List String := [
    s!"    ;; If no borrow (carry=0), c >= p, use t",
    s!"    (if (i64.eqz (local.get $carry))",
    s!"      (then"
  ]
  let condSubIfBody : List String := (List.range N) >>= fun i =>
    [s!"        local.get $t{i}  local.set $c{i}"]
  let condSubIfFooter : List String := [
    s!"      )",
    s!"    )"
  ]
  let condSub : List String := condSubHeader ++ condSubBody ++ condSubIfHeader ++ condSubIfBody ++ condSubIfFooter
  -- Locals: working + product c[0..2N-1] + temp t[0..2N-1] + constants r[0..N-1] + p[0..N-1]
  let locList : List String :=
    ["(local $lo i64) (local $hi i64) (local $carry i64) (local $sum i64)"] ++
    ((List.range limbs2N).map fun i => s!"(local $c{i} i64)") ++
    ((List.range limbs2N).map fun i => s!"(local $t{i} i64)") ++
    ((List.range N).map fun i => s!"(local $r{i} i64)") ++
    ((List.range N).map fun i => s!"(local $p{i} i64)")
  let locals := String.intercalate " " locList
  let aParams := String.intercalate " " ((List.range N).map fun i => s!"(param $a{i} i64)")
  let bParams := String.intercalate " " ((List.range N).map fun i => s!"(param $b{i} i64)")
  let params := s!"{aParams} {bParams}"
  let results := String.intercalate " " (List.replicate N "i64")
  -- Init product c and temp t
  let initC := (List.range limbs2N).map fun i => s!"    i64.const 0  local.set $c{i}"
  let initT := (List.range limbs2N).map fun i => s!"    i64.const 0  local.set $t{i}"
  let loadR := (rLimbs.zip (List.range N)).map fun (val, i) =>
    s!"    i64.const {val}  local.set $r{i}"
  let loadP := (pLimbs.zip (List.range N)).map fun (val, i) =>
    s!"    i64.const {val}  local.set $p{i}"
  String.intercalate "\n" ([
    s!"  ;; Modular multiplication ({N}x{N} schoolbook + Barrett reduction)",
    s!"  (func $fmul {params} (result {results})",
    s!"    {locals}"
  ] ++ initC ++ initT ++ loadR ++ loadP ++ [
    s!"    ;; ── Schoolbook multiplication ──"
  ] ++ schoolbook ++ [
    s!"    ;; ── Reduction: t = c_hi * R_mod_p ──"
  ] ++ redMul ++ addRed ++ carryLoop ++ [
    s!"    ;; ── Conditional subtraction of p ──"
  ] ++ condSub ++ [
    s!"    {String.intercalate " " (List.range N |>.map fun i => s!"local.get $c{i}")}",
    s!"  )"
  ])

def genFadd (numWords : ℕ) : String :=
  let N := numWords
  let aParams := String.intercalate " " ((List.range N).map fun i => s!"(param $a{i} i64)")
  let bParams := String.intercalate " " ((List.range N).map fun i => s!"(param $b{i} i64)")
  let params := s!"{aParams} {bParams}"
  let results := String.intercalate " " (List.replicate N "i64")
  let locals := String.intercalate " " ((List.range N).map fun i => s!"(local $r{i} i64)") ++ " (local $c i64)"
  -- Add limb 0
  let add0 := [
    s!"    local.get $a0  local.get $b0  i64.add  local.set $r0",
    s!"    local.get $r0  local.get $a0  i64.lt_u  i64.extend_i32_u  local.set $c"
  ]
  -- Add limbs 1..N-1 with carry
  let addRest := (List.range (N-1)) >>= fun i =>
    let idx := i + 1
    [
      s!"    local.get $a{idx}  local.get $b{idx}  i64.add  local.get $c  i64.add  local.set $r{idx}",
      s!"    local.get $r{idx}  local.get $a{idx}  i64.lt_u  i64.extend_i32_u",
      s!"    local.get $r{idx}  local.get $b{idx}  i64.lt_u  i64.extend_i32_u  i64.or  local.set $c"
    ]
  let rets := String.intercalate " " (List.range N |>.map fun i => s!"local.get $r{i}")
  String.intercalate "\n" ([
    s!"  ;; Modular addition ({N}×64-bit, unreduced)",
    s!"  (func $fadd {params} (result {results})",
    s!"    {locals}"
  ] ++ add0 ++ addRest ++ [
    s!"    {rets}",
    s!"  )"
  ])

/-- Generate WAT for multi-word modular subtraction. -/
def genFsub (numWords : ℕ) : String :=
  let N := numWords
  let aParams := String.intercalate " " ((List.range N).map fun i => s!"(param $a{i} i64)")
  let bParams := String.intercalate " " ((List.range N).map fun i => s!"(param $b{i} i64)")
  let params := s!"{aParams} {bParams}"
  let results := String.intercalate " " (List.replicate N "i64")
  let locals := String.intercalate " " ((List.range N).map fun i => s!"(local $r{i} i64)") ++ " (local $br i64)"
  -- Sub limb 0
  let sub0 := [
    s!"    local.get $a0  local.get $b0  i64.sub  local.set $r0",
    s!"    local.get $a0  local.get $b0  i64.lt_u  i64.extend_i32_u  local.set $br"
  ]
  -- Sub limbs 1..N-1 with borrow
  let subRest := (List.range (N-1)) >>= fun i =>
    let idx := i + 1
    [
      s!"    local.get $a{idx}  local.get $b{idx}  i64.sub  local.get $br  i64.sub  local.set $r{idx}",
      s!"    local.get $a{idx}  local.get $b{idx}  i64.lt_u  i64.extend_i32_u",
      s!"    local.get $a{idx}  local.get $b{idx}  i64.eq  i64.extend_i32_u",
      s!"    local.get $br  i64.and  i64.or  local.set $br"
    ]
  let rets := String.intercalate " " (List.range N |>.map fun i => s!"local.get $r{i}")
  String.intercalate "\n" ([
    s!"  ;; Modular subtraction ({N}×64-bit, unreduced)",
    s!"  (func $fsub {params} (result {results})",
    s!"    {locals}"
  ] ++ sub0 ++ subRest ++ [
    s!"    {rets}",
    s!"  )"
  ])

/-- Generate WAT for modular inverse via Fermat's little theorem: a^(p-2) mod p.
    Uses square-and-multiply, calling $fmul for each step (~254 squarings + ~127 muls). -/
def genFinv (p numWords : ℕ) : String :=
  let N := numWords
  let exp := p - 2  -- exponent for Fermat
  -- Find MSB position by scanning from high bit down
  let bitPositions := List.range (N*64) |>.reverse
  let msb := (bitPositions.find? fun b => (exp >>> b) % 2 = 1).getD (N*64 - 1)
  let params := String.intercalate " " ((List.range N).map fun i => s!"(param $a{i} i64)")
  let results := String.intercalate " " (List.replicate N "i64")
  let rLocals := String.intercalate " " ((List.range N).map fun i => s!"(local $r{i} i64)")
  -- Push r limbs and constant 1 (for initialization)
  let pushR := String.intercalate " " ((List.range N).map fun i => s!"local.get $r{i}")
  let pushA := String.intercalate " " ((List.range N).map fun i => s!"local.get $a{i}")
  let push1 := String.intercalate " " ("i64.const 1" :: (List.replicate (N-1) "i64.const 0"))
  -- Capture fmul result into r (stack: r0..rN-1, with rN-1 on top)
  let captureR := String.intercalate "\n    " ((List.range N).reverse.map fun i => s!"local.set $r{i}")
  -- Generate square: r = fmul(r, r)
  let square := s!"    {pushR}  {pushR}\n    call $fmul\n    {captureR}"
  -- Generate multiply: r = fmul(r, a)
  let multiply := s!"    {pushR}  {pushA}\n    call $fmul\n    {captureR}"
  -- Standard square-and-multiply: r=1, then for each bit MSB→0: square, conditionally multiply
  let init := [
    s!"    ;; r = 1",
    s!"    {push1}",
    s!"    {captureR}"
  ]
  -- Process ALL bits from MSB down to 0: square, then multiply if bit is set
  let steps : List String := (List.range (msb+1) |>.reverse) >>= fun b =>
    if (exp >>> b) % 2 = 1 then
      [square, multiply]
    else
      [square]
  String.intercalate "\n" ([
    s!"  ;; Modular inverse via Fermat: a^(p-2) mod p ({msb+1} bits)",
    s!"  (func $finv {params} (result {results})",
    s!"    {rLocals}"
  ] ++ init ++ steps ++ [
    s!"    ;; Return r",
    s!"    {pushR}",
    s!"  )"
  ])

def genMultiWordArith (p numWords : ℕ) : String :=
  let ps := toString p
  let N := numWords
  let nBits := N * 64
  String.intercalate "\n" [
    s!"  ;; Multi-word field arithmetic for prime {ps} ({N} words, {nBits} bits)",
    genMul64x64,
    genFmul p N,
    genFadd N,
    genFsub N,
    genFinv p N
  ]

def fieldHelpers (p : ℕ) (numWords : ℕ) : String :=
  if numWords = 1 then
    genSingleWordArith p
  else
    genMultiWordArith p numWords

structure VarMap where
  env : List (ℕ × ℕ) := []
  nextLocal : ℕ := 0
  loopIdx : Option ℕ := none
  letBase : ℕ := 0
  numWords : ℕ := 1

def VarMap.init (numInputs : ℕ) (numWords : ℕ := 1) : VarMap :=
  { env := List.range numInputs |>.map fun i => (i, i * numWords)
    nextLocal := numInputs * numWords
    numWords }

def VarMap.lookup (vm : VarMap) (idx : ℕ) : ℕ :=
  match vm.env.find? fun (i, _) => i = idx with | some (_, w) => w | none => idx * vm.numWords

def VarMap.alloc (vm : VarMap) (m : ℕ) (baseVarIdx : ℕ) : VarMap × List ℕ :=
  let nw := vm.numWords
  let wasmLocals := List.range (m * nw) |>.map fun i => vm.nextLocal + i
  let newEnv := (List.range m |>.map fun i => (baseVarIdx + i, vm.nextLocal + i * nw)) ++ vm.env
  ({ env := newEnv, nextLocal := vm.nextLocal + m * nw, loopIdx := vm.loopIdx,
     letBase := vm.letBase, numWords := nw }, wasmLocals)

def pushConst (c : F) (vm : VarMap) (b : Builder) : Builder :=
  let nw := vm.numWords
  let val := FiniteField.val c
  if nw = 1 then
    b.push s!"i64.const {val}"
  else
    List.range nw |>.foldl (fun (b' : Builder) (w : ℕ) =>
      let limb := (val >>> (w * 64)) % (2^64)
      b'.push s!"i64.const {limb}") b

def pushVar (idx : ℕ) (vm : VarMap) (b : Builder) : Builder :=
  let nw := vm.numWords
  let base := vm.lookup idx
  if nw = 1 then
    b.push s!"local.get {base}"
  else
    List.range nw |>.foldl (fun (b' : Builder) (w : ℕ) =>
      b'.push s!"local.get {base + w}") b

mutual
partial def compileFExpr (vm : VarMap) : FExpr F → Builder → Builder
  | .const c, b => pushConst c vm b
  | .add a e, b => let b := compileFExpr vm a b; let b := compileFExpr vm e b; b.push "call $fadd"
  | .mul a e, b => let b := compileFExpr vm a b; let b := compileFExpr vm e b; b.push "call $fmul"
  | .inv a, b => let b := compileFExpr vm a b; b.push "call $finv"
  | .expr (.var i), b => pushVar i.index vm b
  | .expr (.const c), b => pushConst c vm b
  | .expr (.add a e), b => let b := compileFExpr vm (.expr a) b; let b := compileFExpr vm (.expr e) b; b.push "call $fadd"
  | .expr (.mul a e), b => let b := compileFExpr vm (.expr a) b; let b := compileFExpr vm (.expr e) b; b.push "call $fmul"
  | .ite c t e, b =>
    let nw := vm.numWords
    if nw = 1 then
      let b := compileBExpr vm c b
      let b := b.push "(if (result i64) (then"
      let b := Builder.indented 1 (compileFExpr vm t) b
      let b := b.push ") (else"
      let b := Builder.indented 1 (compileFExpr vm e) b; b.push "))"
    else
      -- Multi-word ite not yet supported; push nw zeros
      List.range nw |>.foldl (fun (b' : Builder) _ => b'.push "i64.const 0  ;; ite MW stub") b
  | .ofNat n, b => compileNExpr vm n b
  | .localVar i, b => pushVar (vm.letBase + i) vm b
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

/-! ## Expression flattening (shared by WASM and R1CS compilers) -/

abbrev LinComb := List (ℕ × ℕ)  -- sparse (signalIndex × coefficient) pairs
abbrev Constraint := LinComb × LinComb × LinComb  -- (A, B, C)

structure FlattenState where
  nextSignal : ℕ := 1
  constraints : List Constraint := []

def isConstant (lc : LinComb) : Bool :=
  match lc with | [(0, _)] => true | _ => false

def scaleLinComb (c : ℕ) (lc : LinComb) (p : ℕ) : LinComb :=
  lc.map fun (i, coeff) => (i, (c * coeff) % p)

def addLinCombs (a b : LinComb) (p : ℕ) : LinComb :=
  match a, b with
  | [], _ => b
  | _, [] => a
  | (i1, c1) :: xs, (i2, c2) :: ys =>
    if i1 < i2 then (i1, c1) :: addLinCombs xs ((i2, c2) :: ys) p
    else if i1 = i2 then (i1, (c1 + c2) % p) :: addLinCombs xs ys p
    else (i2, c2) :: addLinCombs ((i1, c1) :: xs) ys p

open Expression (var const add mul) in
partial def flattenExpr (p : ℕ) (vm : VarMap) : Expression F → FlattenState → (LinComb × FlattenState)
  | .var i, st => ([(1 + vm.lookup i.index, 1)], st)  -- R1CS signal = 1 + WASM local
  | .const c, st =>
    let val := FiniteField.val c % p
    ([(0, val)], st)
  | .add a b, st =>
    let (la, st1) := flattenExpr p vm a st
    let (lb, st2) := flattenExpr p vm b st1
    (addLinCombs la lb p, st2)
  | .mul a b, st =>
    let (la, st1) := flattenExpr p vm a st
    let (lb, st2) := flattenExpr p vm b st1
    if isConstant la then
      (scaleLinComb ((la.head?.getD (0,0)).2) lb p, st2)
    else if isConstant lb then
      (scaleLinComb ((lb.head?.getD (0,0)).2) la p, st2)
    else
      let k := st2.nextSignal
      let st3 : FlattenState := { nextSignal := k + 1, constraints := (la, lb, [(k, 1)]) :: st2.constraints }
      ([(k, 1)], st3)

/-! ## WASM code generation for intermediate signals -/

/-- Generate WAT to load signal i from memory as i64. Signal 0 is the constant 1. -/
def loadSignal (i signalBase signalBytes : ℕ) : String :=
  if i = 0 then "i64.const 1"
  else s!"i32.const {signalBase + i * signalBytes}  i32.load  i64.extend_i32_u"

/-- Generate WAT to evaluate a linear combination, leaving the result as i64 on the stack. -/
def compileLinCombWAT (lc : LinComb) (signalBase signalBytes : ℕ) : String :=
  match lc with
  | [] => "i64.const 0"
  | [(0, c)] => s!"i64.const {c}"
  | [(i, c)] =>
    s!"{loadSignal i signalBase signalBytes}\n    i64.const {c}\n    call $fmul"
  | (i1, c1) :: rest =>
    -- Start with first term, then accumulate
    let first := if i1 = 0 then s!"i64.const {c1}"
      else s!"{loadSignal i1 signalBase signalBytes}\n    i64.const {c1}\n    call $fmul"
    let restWAT := rest.map fun (p : ℕ × ℕ) =>
      let i := p.1; let c := p.2
      if i = 0 then s!"    i64.const {c}\n    call $fadd"
      else s!"{loadSignal i signalBase signalBytes}\n    i64.const {c}\n    call $fmul\n    call $fadd"
    String.intercalate "\n" (first :: restWAT)

/--
Discover intermediate signals from assert expressions. Returns:
- numIntermediates: count of extra signals
- intLocals: WAT local declarations for each intermediate
- intComputation: WAT code to compute each intermediate and store to memory
- total extra signals (to add to totalSignals)
-/
def discoverAndCompileIntermediates (p : ℕ) (vm : VarMap) (flatOps : List (FlatOperation F))
    (startSignal signalBase signalBytes : ℕ) : ℕ × List String × List String :=
  -- Walk assert expressions, run flattenExpr to discover intermediates
  let (st, _) := flatOps.foldl (fun (acc : FlattenState × Unit) (op : FlatOperation F) =>
    match op with
    | .assert e =>
      let (_, st') := flattenExpr p vm e acc.1
      (st', ())
    | _ => acc
  ) ({ nextSignal := startSignal }, ())
  let numInt := st.nextSignal - startSignal
  -- Generate WAT for each intermediate constraint (la, lb, [{k, 1}])
  -- Process reversed for oldest-first dependency order
  let intConstraintsRev := List.reverse st.constraints
  -- Recursively build locals and computation lines
  let rec buildWAT (idx : ℕ) (lines : List String) (locals : List String)
      (remaining : List Constraint) : ℕ × List String × List String :=
    match remaining with
    | [] => (idx, lines, locals)
    | (la, lb, [(k, _)]) :: rest =>
      let localName := s!"$int_{idx}"
      let laWAT := compileLinCombWAT la signalBase signalBytes
      let lbWAT := compileLinCombWAT lb signalBase signalBytes
      let computeLine := String.intercalate "\n" [
        s!"{laWAT}",
        s!"{lbWAT}",
        s!"    call $fmul",
        s!"    local.set {localName}",
        s!"    i32.const {signalBase + k * signalBytes}  local.get {localName}  i32.wrap_i64  i32.store"
      ]
      buildWAT (idx + 1) (computeLine :: lines) (s!"(local {localName} i64)" :: locals) rest
    | _ :: rest => buildWAT idx lines locals rest
  let (_, lines, locals) := buildWAT 0 [] [] intConstraintsRev
  (numInt, List.reverse locals, List.reverse lines)

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

def compileModule (fieldPrime numInputs : ℕ) (ops : List (Operation F)) (numWords : ℕ := 1) : String :=
  let nw := numWords
  let vm := VarMap.init numInputs nw
  let flatOps := flattenOps ops
  let (finalVm, _, bodyLines) := processFlatOps numInputs flatOps vm (numInputs * nw) []
  let witnessWords := finalVm.nextLocal - numInputs * nw
  let witnessCount := witnessWords / nw
  let n32 := nw * 2  -- i32 words per field element
  -- Memory layout: 0=computed_flag, 4=SRWM(n32*4 bytes), 4+n32*4=signal_array(N*n32*4 bytes)
  let srwmBase := 4
  let signalBase := 4 + n32 * 4
  let signalBytes := n32 * 4  -- bytes per signal
  -- Discover R1CS intermediates from assert expressions
  let startSignal := 1 + finalVm.nextLocal / nw  -- next signal index after WASM locals + constant
  let (numInt, intLocals, intCode) :=
    discoverAndCompileIntermediates fieldPrime vm flatOps startSignal signalBase signalBytes
  let totalSignals := startSignal + numInt
  -- $compute params: each input = nw i64 values, no results (stores to memory)
  let inputParams := String.intercalate " " (List.range numInputs  >>= fun i =>
    (List.range nw).map fun w => s!"(param $in_{i}_{w} i64)")
  -- $compute locals: witnesses + idx
  let locals := String.intercalate " "
    ((List.replicate witnessWords "(local i64)") ++ ["(local $idx i64)"])
  -- After witness computation, store each witness word to signal memory
  let outputStoresInCompute := String.intercalate "\n" (List.range witnessCount  >>= fun i =>
    (List.range nw).map fun w =>
      s!"    i32.const {signalBase + (1 + numInputs + i) * signalBytes + w * 4}  local.get {numInputs * nw + i * nw + w}  i32.wrap_i64  i32.store")
  let computeBody := String.intercalate "\n" (bodyLines ++ [outputStoresInCompute])
  let results := "" -- no multi-value returns; results stored to memory
  -- Input loads: read nw i32 values per input, extend to i64, set input word locals
  let inputLoads := String.intercalate "\n" (List.range numInputs  >>= fun i =>
    (List.range nw).map fun w =>
      s!"    i32.const {signalBase + (1 + i) * signalBytes + w * 4} i32.load  i64.extend_i32_u  local.set $in_{i}_{w}")
  -- Push inputs for $compute call
  let inputPush := String.intercalate "\n" (List.range numInputs  >>= fun i =>
    (List.range nw).map fun w => s!"    local.get $in_{i}_{w}")
  -- getWitness: no need for witness locals (results stored to memory by $compute)
  let gwInputLocals := String.intercalate " " (List.range numInputs  >>= fun i =>
    (List.range nw).map fun w => s!"(local $in_{i}_{w} i64)")
  -- snarkjs ABI exports
  let snarkjsExports := String.intercalate "\n\n" [
    s!"  (func (export \"getFieldNumLen32\") (result i32) i32.const {n32})",
    s!"  (func (export \"getRawPrime\")" ++
    (String.intercalate "\n" ((List.range n32).map fun w =>
      s!"    i32.const {srwmBase + w * 4}  i32.const {(fieldPrime >>> (w * 32)) % (2^32)}  i32.store")) ++ ")",
    s!"  (func (export \"readSharedRWMemory\") (param i32) (result i32)",
    s!"    i32.const {srwmBase}  local.get 0  i32.const 4  i32.mul  i32.add  i32.load)",
    s!"  (func (export \"writeSharedRWMemory\") (param $j i32) (param $v i32)",
    s!"    i32.const {srwmBase}  local.get $j  i32.const 4  i32.mul  i32.add  local.get $v  i32.store)",
    s!"  (func (export \"getInputSignalSize\") (param i32) (param i32) (result i32) i32.const {numInputs})",
    s!"  (func (export \"getInputSize\") (result i32) i32.const {numInputs})",
    s!"  (func (export \"getWitnessSize\") (result i32) i32.const {totalSignals})",
    s!"  (func (export \"setInputSignal\") (param $hMSB i32) (param $hLSB i32) (param $idx i32)",
    s!"    i32.const {signalBase + signalBytes}  local.get $idx  i32.const {signalBytes}  i32.mul  i32.add",
    s!"    i32.const {srwmBase}  i32.load",
    s!"    i32.store)",
    s!"  (func (export \"getWitness\") (param $i i32)",
    s!"    (local $tmp i32) {gwInputLocals} {String.intercalate " " intLocals} (local $idx i64)",
    s!"    i32.const 0  i32.load  i32.eqz",
    s!"    (if (then",
    s!"{inputLoads}",
    s!"{inputPush}",
    s!"      call $compute",
    -- Compute and store intermediates (after witnesses are in memory)
    s!"{String.intercalate "\n" intCode}",
    s!"      i32.const {signalBase}  i32.const 1  i32.store",
    s!"      i32.const 0  i32.const 1  i32.store",
    s!"    ))",
    s!"    i32.const 0",
    s!"    i32.const {signalBase}  local.get $i  i32.const {signalBytes}  i32.mul  i32.add  i32.load",
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
    s!"  (data (i32.const {signalBase}) \"\\01{String.join (List.replicate (signalBytes - 1) "\\00")}\")",
    fieldHelpers fieldPrime nw,
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

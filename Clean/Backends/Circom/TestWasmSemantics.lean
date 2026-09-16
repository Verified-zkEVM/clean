import Clean.Backends.Circom.TestWasmCompile

/-!
Positive conformance checks for the WASM backend. These check the intended
semantics of the corrected implementation; they do not run an old compiler or
construct proofs against a different constraint relation.
-/

open Backends.Circom
open TestWasmCompile

namespace TestWasmSemantics

/-- Appending a computation block preserves both the existing instruction
order and the instruction order inside that block. -/
example (cb : CodeBuilder) (instructions : List Ast.Instr) :
    (cb.pushList instructions).build = cb.build ++ instructions := by
  simp [CodeBuilder.pushList, CodeBuilder.build]

/- Field-vector constructors agree with the IR evaluator in the standard
BN254 layout. Include empty tables as an ordinary default case. -/
#eval! withTools ["snarkjs"] do
  let p := Specs.Poseidon.BN254_PRIME
  let nw := 4
  let input := 42
  let ops : List (Operation Specs.Poseidon.F) :=
    [.witness 8 (.ir [] (.bitsOf (.expr (.var ⟨0⟩)))),
     .witness 1 (.ir [] (.lit #v[.listGet [] (.const 0)]))]
  let wit ← compileAndWitness p 1 ["in"] [] ops nw
    "/tmp/wasm_semantics_vectors.wasm" (Lean.Json.mkObj [("in", Lean.Json.str (toString input))]).compress
  let expected := [1, input] ++
    ((List.range 8).map fun i => (input >>> i) % 2) ++ [0]
  unless wit = expected do
    throw <| IO.userError "field-vector conformance mismatch"
  IO.println "OK: field-vector constructors preserve canonical field values"

/- UInt64 arithmetic agrees with the source evaluator, including its total
zero-divisor convention and compositions of arithmetic operations. -/
#eval! withTools ["snarkjs"] do
  for nw in [1, 2] do
    for (x, y) in [(17, 3), (17, 0)] do
      let a : Witgen.U64Expr (F p1009) := .const (UInt64.ofNat x)
      let b : Witgen.U64Expr (F p1009) := .const (UInt64.ofNat y)
      let ops : List (Operation (F p1009)) :=
        [.witness 3 (.ir [] (.lit #v[
          .ofU64 (.div a b), .ofU64 (.mod a b),
          .ofU64 (.add (.div a b) (.mod a b))]))]
      let wit ← compileAndWitness p1009 0 [] [] ops nw
        "/tmp/wasm_semantics_u64.wasm" "{}"
      let q := ((UInt64.ofNat x) / (UInt64.ofNat y)).toNat
      let r := ((UInt64.ofNat x) % (UInt64.ofNat y)).toNat
      unless wit = [1, q, r, q + r] do
        throw <| IO.userError "UInt64 arithmetic conformance mismatch"
  IO.println "OK: UInt64 arithmetic agrees with Lean evaluation"

/- Test field arithmetic independently of circuit encoding, against integer
modular arithmetic. Use a full-width modulus and canonical boundary residues to check
the final reduction carry. -/
#eval! withTools ["node", "wasm-validate"] do
  let p := 2^128 - 159
  let nw := 2
  let funcs := (genMultiWordArith p nw).map fun f =>
    if f.name = "$fadd" then { f with exportName := some "add" }
    else if f.name = "$fmul" then { f with exportName := some "mul" }
    else f
  let wasm ← match Binary.Module.toBinary { funcs } with
    | .ok b => pure b
    | .error e => throw <| IO.userError e
  let path := "/tmp/wasm_semantics_arithmetic.wasm"
  IO.FS.writeBinFile path wasm
  let validation ← IO.Process.output { cmd := "wasm-validate", args := #[path] }
  unless validation.exitCode = 0 do
    throw <| IO.userError validation.stderr
  let js := "
const fs = require('node:fs');
const [path, prime, width] = process.argv.slice(1);
const p = BigInt(prime), n = Number(width);
const R = (1n << BigInt(64*n)) % p;
const mask = (1n << 64n) - 1n;
const limbs = x => Array.from({length:n}, (_,i) => (x >> BigInt(64*i)) & mask);
const value = xs => xs.reduce((a,x,i) => a + (BigInt.asUintN(64,x) << BigInt(64*i)), 0n);
const wasm = new WebAssembly.Instance(new WebAssembly.Module(fs.readFileSync(path))).exports;
const samples = [0n, 1n, p-1n];
for (const x of samples) for (const y of samples) {
const a = limbs(x*R % p), b = limbs(y*R % p);
if (value(wasm.add(...a,...b)) !== ((x+y)%p)*R%p) throw Error('field addition conformance');
if (value(wasm.mul(...a,...b)) !== ((x*y)%p)*R%p) throw Error('field multiplication conformance');
}
"
  let result ← IO.Process.output {
    cmd := "node", args := #["-e", js, path, toString p, toString nw] }
  unless result.exitCode = 0 do
    throw <| IO.userError result.stderr
  IO.println "OK: multi-word arithmetic agrees with modular arithmetic"

end TestWasmSemantics

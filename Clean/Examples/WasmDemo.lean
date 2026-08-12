import Clean.Backends.Wasm.Compile
import Clean.Backends.Wasm.R1CS
import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Primes
import Clean.Specs.Poseidon
import Clean.Circomlib.Poseidon
import Clean.Specs.PoseidonOptimized

/-!
# WASM backend demo: `mulAdd`

A tiny circuit with two public inputs `a, b` and one witness `w = a·b + 5`,
compiled end-to-end to the snarkjs toolchain:

1. `mulAdd` is the circuit: `witness` creates the witness variable and `===`
   adds the constraint `w = a·b + 5`.
2. `.operations 2` extracts the flat operation list (offset = 2 public inputs).
3. `compileModule` produces the binary WASM module (Circom 2 witness-calculator ABI),
   with the input names `["a", "b"]` (strict snarkjs key checking) and the
   output witness `[2]` (outputs-first signal layout).
4. `compileR1CS` produces the R1CS constraint system as JSON.
5. The `#eval!` below writes both artifacts to `/tmp`. Then, from the shell:

   ```bash
   wasm-validate /tmp/wasm_demo_circuit.wasm
   snarkjs wtns calculate /tmp/wasm_demo_circuit.wasm \
       /tmp/wasm_demo_input.json /tmp/wasm_demo_witness.wtns
   snarkjs wtns export json /tmp/wasm_demo_witness.wtns /tmp/wasm_demo_witness.json
   ```

   with the standard circom input format — one key per input (unknown keys are
   rejected by the module):

   ```json
   {"a": "3", "b": "4"}
   ```

   For `a = 3, b = 4` the witness is `[1, 17, 3, 4, 12]`: signal 0 is the
   constant signal, signal 1 is the output `w = 3·4 + 5 = 17` (outputs-first
   layout), then the two inputs, then an intermediate (signal 4 = `a·b` = 12)
   induced by the `===` assert: the compiler witnesses the product as its own
   signal so the constraints stay quadratic — `a·b = v4` and `w = v4 + 5`
   (visible in the R1CS JSON).
-/

open Backends.Wasm

namespace Examples.WasmDemo

/-- Two inputs `a, b`; witness `w = a·b + 5`, constrained to equal `a·b + 5`. -/
def mulAdd (a b : Expression (F p1009)) : Circuit (F p1009) (Expression (F p1009)) := do
  let w ← witness (.expr (a * b + 5))
  w === a * b + 5
  return w

/-- Circuit operations with the two public inputs at variables 0 and 1;
    the witness `w` is circuit variable 2 (the output). -/
def ops : List (Operation (F p1009)) :=
  (mulAdd (varFromOffset field 0) (varFromOffset field 1)).operations 2

/-- Compile to binary WASM (single-word: `p1009 ≤ 2^32`), with strict input
    names `["a", "b"]` and the output witness `[2]` (outputs-first layout). -/
def wasm : Except String ByteArray := compileModule p1009 2 ["a", "b"] [2] ops 1

/-- Compile the R1CS constraints to JSON. -/
def r1csJson : Except String String := compileR1CS p1009 2 ["a", "b"] [2] ops 1

/-- Compile the R1CS constraints to the binary `.r1cs` format (for
    `snarkjs r1cs info`, `groth16 setup`, ...). -/
def r1csBin : Except String ByteArray := compileR1CSBin p1009 2 ["a", "b"] [2] ops 1

#eval! do
  let binary ← match wasm with
    | .ok b => pure b
    | .error e => throw <| IO.userError s!"compileModule: {e}"
  IO.FS.writeBinFile (System.FilePath.mk "/tmp/wasm_demo_circuit.wasm") binary
  let r1cs ← match r1csJson with
    | .ok s => pure s
    | .error e => throw <| IO.userError s!"compileR1CS: {e}"
  IO.FS.writeFile (System.FilePath.mk "/tmp/wasm_demo_circuit.r1cs.json") r1cs
  let bin ← match r1csBin with
    | .ok b => pure b
    | .error e => throw <| IO.userError s!"compileR1CSBin: {e}"
  IO.FS.writeBinFile (System.FilePath.mk "/tmp/wasm_demo_circuit.r1cs") bin
  IO.println s!"wrote /tmp/wasm_demo_circuit.wasm ({binary.size} bytes), .r1cs.json and .r1cs ({bin.size} bytes)"

end Examples.WasmDemo

/-!
# The real user flow: a packaged `FormalCircuit`

`mulAdd` above was deliberately small. A production circuit — like the
`Poseidon1` hash gadget bundled in `Clean.Circomlib.Poseidon` — is packaged as
a `FormalCircuit` with proofs. Compiling it is still just glue:

1. Get its operations: `(Poseidon1.circuit.main (varFromOffset field 0)).operations 1`
   — the circuit's `main` takes its own input variable (1 public input); no
   hand-written witness IR anywhere.
2. Compile: `compileModule BN254_PRIME 1 ["in"] [401] ops 4` — one call
   produces the whole witness-generation module (Montgomery multi-word
   arithmetic, all ABI functions, ~200 KB of WASM), with strict input-name
   checking and the output witness (circuit variable 401, signal 402 in the default layout) moved to signal 1
   (outputs-first layout).
3. Run snarkjs — exactly as with `circom`'s output:
   `snarkjs wtns calculate /tmp/poseidon_demo.wasm input.json witness.wtns`,
   with `input.json` = `{"in": "0"}`.

The `#eval!` below writes the module and prints the Lean ground truth
(`Specs.PoseidonOptimized.poseidon1Opt`) so the snarkjs witness can be checked
against it. Because the output is declared via `outputVarIdx`, the Poseidon1
output is signal 1, and the groth16 `public.json` correctly contains
`[output, input]`.

With the binary `.r1cs` the circuit can run through the full proving flow:

```bash
snarkjs r1cs info /tmp/poseidon_demo.r1cs
snarkjs powersoftau new bn128 12 pot12_0000.ptau
snarkjs powersoftau contribute pot12_0000.ptau pot12_0001.ptau --name=clean -e=demo
snarkjs powersoftau prepare phase2 pot12_0001.ptau pot12_final.ptau
snarkjs groth16 setup /tmp/poseidon_demo.r1cs pot12_final.ptau poseidon.zkey
snarkjs zkey export verificationkey poseidon.zkey vkey.json
snarkjs groth16 prove poseidon.zkey /tmp/poseidon_demo_witness.wtns proof.json public.json
snarkjs groth16 verify vkey.json public.json proof.json
```
-/

namespace Examples.WasmDemo.Poseidon

/-- Operations of the full `Poseidon1` hash gadget (BN254, 1 public input). -/
def poseidonOps : List (Operation Specs.Poseidon.F) :=
  (Circomlib.Poseidon.Poseidon1.circuit.main (varFromOffset field 0)).operations 1

/-- Compile the whole gadget: 4 limbs of Montgomery arithmetic, all ABI
    functions; input name `"in"`, output witness at variable 401. -/
def poseidonWasm : Except String ByteArray := compileModule Specs.Poseidon.BN254_PRIME 1 ["in"] [401] poseidonOps 4

/-- The gadget's constraints as a binary `.r1cs` (for `groth16 setup`). -/
def poseidonR1CSBin : Except String ByteArray := compileR1CSBin Specs.Poseidon.BN254_PRIME 1 ["in"] [401] poseidonOps 4

#eval! do
  let binary ← match poseidonWasm with
    | .ok b => pure b
    | .error e => throw <| IO.userError s!"compileModule: {e}"
  IO.FS.writeBinFile (System.FilePath.mk "/tmp/poseidon_demo.wasm") binary
  let r1cs ← match poseidonR1CSBin with
    | .ok b => pure b
    | .error e => throw <| IO.userError s!"compileR1CSBin: {e}"
  IO.FS.writeBinFile (System.FilePath.mk "/tmp/poseidon_demo.r1cs") r1cs
  let expected := Specs.PoseidonOptimized.poseidon1Opt (0 : Specs.Poseidon.F)
  IO.println s!"wrote /tmp/poseidon_demo.wasm ({binary.size} bytes) and /tmp/poseidon_demo.r1cs ({r1cs.size} bytes)"
  IO.println s!"Lean ground truth: poseidon1(0) = {ZMod.val expected}"

end Examples.WasmDemo.Poseidon

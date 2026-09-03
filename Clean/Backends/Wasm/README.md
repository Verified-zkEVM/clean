# Clean WASM Backend

A compiler written in Lean that turns [Clean](https://github.com/VanshSahay/clean) circuits into standalone artifacts the [snarkjs](https://github.com/iden3/snarkjs) toolchain can consume directly:

- **Binary WASM witness-generation modules** implementing the [Circom 2 witness-calculator ABI](https://github.com/iden3/circom_runtime/blob/master/js/witness_calculator.js) , `snarkjs wtns calculate circuit.wasm input.json witness.wtns` works out of the box.
- **R1CS constraint files** in two formats: a pretty-printed JSON object, and the binary `.r1cs` format consumed directly by `snarkjs r1cs info`, `groth16 setup`, and the other `r1cs` subcommands.

Because the compiler itself is written in Lean, every output is built from the same formal definitions the rest of Clean's verification machinery uses, and the end-to-end test harness checks generated witnesses against Lean ground truth.

## What it has to offer

- **Circom 2 ABI compatibility** : the emitted module exports the full witness-calculator interface (`init`, `witness`, `getWitness`, `setInputSignal`, ...), so it drops into the standard snarkjs flow without wrappers.
- **Multiprecision field arithmetic** : Montgomery multiplication for BN254 and other primes up to 254 bits, written in Lean and checked end-to-end against Lean ground truth; single-word fast paths for primes ≤ 2³².
- **Never silently wrong** : the compiler is total: every unsupported instruction or unknown label fails at *compile time* with a descriptive `Except String` error instead of emitting a broken or incorrect module (see [Error handling](#error-handling)).
- **No runtime dependencies** : the output is a self-contained binary `.wasm` file plus `.r1cs`/`.json` constraint files; no Lean runtime or WASI needed.
- **Multi-word arithmetic** : fields larger than one 64-bit limb (e.g. BN254, 4 limbs) are fully supported, including Montgomery-form representation and conversion at boundaries.



## Architecture

Both backends share a single flattening pass over the circuit's operations:

```
Clean circuit (Circuit F α)
        │  .operations offset
        ▼
List (Operation F)
        │  Operations.toFlat
        ▼
List (FlatOperation F)
        ├──► Compile.lean ──► Ast.lean (typed WASM AST) ──► Binary.lean (binary encoder) ──► .wasm
        └──► R1CS.lean ──► R1CS JSON + binary .r1cs (constraints + prime metadata)
```


| File           | Role                                                                                |
| -------------- | ----------------------------------------------------------------------------------- |
| `Compile.lean` | Flattening pass, witness-generation code generation, all ABI functions              |
| `Ast.lean`     | Typed WASM AST (instructions, functions, modules, binary opcodes)                   |
| `Binary.lean`  | LEB128/binary encoding of the AST into a `.wasm` byte array, with validation errors |
| `R1CS.lean`    | Quadratic-constraint extraction, JSON serialization, binary `.r1cs` encoding       |




## Quick start

```lean
import Clean.Backends.Wasm.Compile
import Clean.Backends.Wasm.R1CS
import Clean.Utils.Field          -- the field type `F p`
import Clean.Utils.Primes         -- small test primes, e.g. `p1009`
import Clean.Specs.Poseidon       -- `BN254_PRIME`
import Clean.Circomlib.Poseidon   -- `Poseidon1`, a full gadget to compile
open Backends.Wasm

-- Witness IR: one input `x`, one witness `w = x + 5`.
def addOps : List (Operation (F p1009)) :=
  [.witness 1 (.ir [] (.lit #v[.add (.expr (.var ⟨0⟩)) (.const 5)]))]

-- Single-word: primes ≤ 2^32 (small test fields); input name "x", output = witness 1.
def wasm : Except String ByteArray := compileModule p1009 1 ["x"] [1] addOps 1

-- The operations of a larger circuit, offset by its public inputs (here: 1).
def ops : List (Operation Specs.Poseidon.F) :=
  (Circomlib.Poseidon.Poseidon1.circuit.main (varFromOffset field 0)).operations 1

-- Multi-word: BN254 needs 4 64-bit limbs; input "in", output witness 402.
def wasmBN254 : Except String ByteArray := compileModule BN254_PRIME 1 ["in"] [402] ops 4

-- R1CS constraints for the same circuit, as JSON and as binary .r1cs
def r1csJson : Except String String := compileR1CS BN254_PRIME 1 ["in"] [402] ops 4
def r1csBin : Except String ByteArray := compileR1CSBin BN254_PRIME 1 ["in"] [402] ops 4
```

To use the output, write the bytes to a file and hand them to snarkjs:

```bash
snarkjs wtns calculate circuit.wasm input.json witness.wtns
```

A complete end-to-end example (including `wasm-validate` and a ground-truth comparison) lives in `[Clean/Utils/Test/TestWasmCompile.lean](../../Utils/Test/TestWasmCompile.lean)`.

## API



### `compileModule`

```lean
def compileModule (fieldPrime numInputs : ℕ) (inputNames : List String := [])
    (outputVarIdx : List ℕ := []) (ops : List (Operation F)) (numWords : ℕ) :
    Except String ByteArray
```


| Parameter       | Meaning                                                                        |
| --------------- | ------------------------------------------------------------------------------ |
| `fieldPrime`    | The field prime (e.g. `1009` for small test fields, `BN254_PRIME` for BN254)   |
| `numInputs`     | Number of public input signals                                                 |
| `inputNames`    | Optional input names (one per input). When given, the module validates input.json keys by FNV-1a hash, like circom: unknown keys are rejected. When empty, any key is accepted and the value array must hold all `numInputs` elements (see [Inputs](#inputs)). |
| `outputVarIdx`  | Optional circuit-variable indices of the output witnesses. When given, the signal layout is outputs-first (see [Signal layout](#signal-layout)) and `groth16 public.json` contains the real outputs. |
| `ops`           | The circuit's operations (`Operations F`), e.g. `circuit.operations numInputs` |
| `numWords`      | Number of 64-bit limbs per field element (see below)                           |


Returns the binary WASM module, or an error describing the problem.

### `compileR1CS`

```lean
def compileR1CS (fieldPrime numInputs : ℕ) (inputNames : List String := [])
    (outputVarIdx : List ℕ := []) (ops : List (Operation F)) (numWords : ℕ) :
    Except String String
```

Same inputs as `compileModule` and returns the R1CS constraint system as a pretty-printed JSON string.

### `compileR1CSBin`

```lean
def compileR1CSBin (fieldPrime numInputs : ℕ) (inputNames : List String := [])
    (outputVarIdx : List ℕ := []) (ops : List (Operation F)) (numWords : ℕ) :
    Except String ByteArray
```

Same inputs and constraint pipeline as `compileR1CS`, returned as a binary `.r1cs` file (the r1csfile format read by snarkjs). This is what `groth16 setup` consumes:

```bash
snarkjs r1cs info circuit.r1cs
snarkjs groth16 setup circuit.r1cs pot_final.ptau circuit.zkey
```

For field elements smaller than 64 bits the coefficient byte width is padded up to the field's word size (`8·⌈bitLength/64⌉`), which is what snarkjs's reader expects; the encoded values are unchanged.

### Choosing `numWords`

- `numWords` must satisfy `numWords * 64 ≥ bitLength(fieldPrime)`; a smaller value is rejected with an error naming the minimum.
- Use `1` only for primes ≤ 2³², so that the product of two field elements fits in an i64 before modular reduction (enforced with an error otherwise).
- Use `2` for primes between 2³² and 2⁶⁴, and `4` for BN254 (254-bit prime).



## Supported operations


| Operation                               | Status                                                       |
| --------------------------------------- | ------------------------------------------------------------ |
| `const`, `add`, `mul`, `inv`            | ✅ Supported                                                  |
| `var`, `localVar`                       | ✅ Supported                                                  |
| `ofU64`                                 | ✅ Supported (zero-extends to `numWords` limbs, reduces)      |
| `val`                                   | ✅ Supported (keeps lowest 64 bits of integer representation) |
| `ite` (if-else)                         | ✅ Supported (multi-value for multi-word)                     |
| `lt`, `neq`, `not`, `and` (booleans)    | ✅ Supported                                                  |
| `flt` (field-sorted `<`)                | ✅ Supported (limb-wise compare for multi-word)               |
| `bit` (bit test)                        | ✅ Supported                                                  |
| `feq`                                   | ✅ Supported (pairwise limb compare for multi-word)           |
| `lit`, `mapRange`, `envRange`, `bitsOf` | ✅ Supported                                                  |
| `append`                                | ✅ Supported                                                  |
| `listGet`                               | ✅ Supported (select-sum chain)                               |
| `dataGet`, `hintGet`                    | ❌ Not representable in a standalone module (`.error`)        |
| `native` witnesses (Lean closures)      | ❌ Not compilable (`.error`)                                  |
| `idx` (outside `mapRange`)              | ❌ Invalid (`.error`)                                         |
| lookups                                 | Ignored by witness generation; `.error` in R1CS export       |
| interactions                            | Ignored by witness generation; `.error` in R1CS export       |


Lookups and interactions constrain existing values and allocate no witnesses, so witness generation skips them; they cannot be expressed as quadratic constraints, so the R1CS exporter rejects them.

All u64-sorted (`U64Expr`) arithmetic is performed on single 64-bit words with WASM's native wrap-around semantics, exactly matching the IR's `UInt64` evaluation.

## Error handling

All entry points return `Except String`. Anything the compiler cannot represent — an unsupported instruction, an unknown label or function name, a `native` witness, insufficient `numWords`, a lookup in R1CS — fails at compile time with a descriptive message. There are no silent fallbacks: the encoder emits `.error` for unknown instructions instead of an opcode that would fail deep inside snarkjs, and label resolution never falls back to depth 0.

## Output format



### Snarkjs ABI

The generated WASM module exports:


| Export                                               | Description                                                     |
| ---------------------------------------------------- | --------------------------------------------------------------- |
| `getFieldNumLen32`                                   | Number of 32-bit words per field element                        |
| `getRawPrime`                                        | Field prime split into 32-bit words                             |
| `readSharedRWMemory`                                 | Read a 32-bit word from shared memory                           |
| `writeSharedRWMemory`                                | Write a 32-bit word to shared memory                            |
| `getInputSignalSize`                                 | Size of each input signal in 32-bit words                       |
| `getInputSize`                                       | Number of public inputs                                         |
| `getWitnessSize`                                     | Total number of signals                                         |
| `setInputSignal`                                     | Set an input signal value from shared memory                    |
| `getWitness`                                         | Compute and return the witness for a signal                     |
| `getMessageChar`                                     | Error message characters (always 0: no runtime messages needed) |
| `getVersion` / `getMinorVersion` / `getPatchVersion` | snarkjs version info                                            |
| `init`                                               | Initialize signal memory                                        |
| `witness`                                            | Compute all witness values                                      |




### Inputs

snarkjs dispatches on the FNV-1a hash of each `input.json` key (circom's convention). Two modes:

- **With `inputNames`**: one key per input, each holding exactly one field element — the standard circom format, `{"a": "3", "b": "4"}`. Unknown or misspelled keys are rejected ("Signal not found"), like circom.
- **Without names (lenient)**: any single key whose value array holds all `numInputs` elements, e.g. `{"in": ["3", "4"]}`. The key name is ignored.

### Signal layout

Signal `0` is the constant signal (`1`). Without `outputVarIdx`, signals `1..numInputs` are the public inputs, followed by the circuit's witnesses in variable order and the intermediate signals induced by asserts. With `outputVarIdx`, the layout is **outputs-first** (the circom convention): signal `0` = constant, signals `1..numOutputs` = the declared output witnesses (in `outputVarIdx` order), then the inputs, then the remaining witnesses — so snarkjs's `groth16 public.json` contains the circuit's real outputs and inputs. Witness values are produced in Montgomery form internally and converted back to normal form before being stored to shared memory.

### Using with snarkjs

```bash
# Generate witness directly from the compiled binary WASM
snarkjs wtns calculate circuit.wasm input.json witness.wtns
```



## Field arithmetic



### Single-word (primes ≤ 2³²)

Uses WASM `i64` operations. Multiplication is `i64.mul` followed by `i64.rem_u`, which is safe exactly when `(p-1)² < 2⁶⁴` — i.e. `p ≤ 2³²`; larger primes with `numWords = 1` are rejected with an error.

### Multi-word (e.g. BN254)

Full multi-precision arithmetic:

- `$mul64x64`: 64×64 → 128 multiplication with carry detection
- `$fmul`: N×N schoolbook multiplication + CIOS Montgomery reduction (HAC Algorithm 14.36) with 64-bit limbs
- `$fadd`: limb-wise addition with carry + conditional mod `p`
- `$finv`: Fermat's little theorem square-and-multiply via `$fmul` (operates in Montgomery form)

Values are kept in Montgomery form (`x·R mod p`, `R = 2^(N·64)`) throughout the computation and converted only at boundaries: constants are emitted as `c·R mod p`, inputs are converted via `montMul(x, R²)`, and outputs are converted back via `montMul(x, 1)`. The reduction uses `n' = -p⁻¹ mod 2⁶⁴` and a single conditional subtraction (result < 2p).

## Verification & testing

`lake build CleanTests` runs `[TestWasmCompile.lean](../../Utils/Test/TestWasmCompile.lean)`, which:

- compiles representative circuits (empty, addition, let-steps, `flt`, `bit`, `bitsOf`, `envRange`, `append`, `listGet`, multi-word `val`) and validates the emitted binaries with `wasm-validate`;
- compiles full **Poseidon1** to WASM, runs `snarkjs wtns calculate` on three inputs, and checks each witness against the Lean ground truth computed by `Specs.PoseidonOptimized.poseidon1Opt`;
- checks negative cases: `native` witnesses, unsupported operations, and `numWords = 1` on BN254 all fail with the expected error.

For writing circuit witnesses, see `[doc/witgen-authoring.md](../../../doc/witgen-authoring.md)`.

## Performance

- **Linear lowering**: the export path (flattening → WASM instructions → binary,
  and R1CS extraction) is linear in program size. It previously accumulated
  instructions as `acc ++ chunk`, re-copying the whole prefix per witness op —
  quadratic in the number of witness cells (a reviewer's 3,596-cell circuit
  took 2.6 s; a 31K-witness Keccak-shaped circuit was dominated by the same
  term). All accumulation now conses in O(1) (`CodeBuilder`), and the
  `VarMap` layout lookup is a direct `i * numWords` formula. Regression tests
  cover 2000-witness lists and a 3000-element `mapRange`; each completes in
  milliseconds.
- **Run the compiler natively for large circuits**: `#eval!` blocks and
  `lake env lean --run` execute through Lean's bytecode interpreter, which is
  orders of magnitude slower than native code (a reviewer measured >20 minutes
  interpreted vs 2.6 s native on the same export). For big circuits, either
  `set_option eval.useNative true` in a script, or drive the compiler from a
  native executable — e.g. a `lean_exe` in your own project that calls
  `compileModule`/`compileR1CS` directly. (This ships no `lean_exe`.)
- **Expression shape matters**: never build `e + e` over a shared subtree —
  for example an `e2 := e2 + e2` loop accumulator. `flattenExpr` and
  `compileExpr` are structural recursions with no sharing, so doubling a
  shared `Expression` tree visits 2^N nodes (a 254-bit bit-decomposition
  circuit hung for over 6 minutes). Write `e2 * 2` instead: the power-of-two
  becomes a chain of N multiplications and stays linear. The bundled
  `Num2Bits`/`Bits2Num`/`BinSub` gadgets follow this; a 128-bit `Num2Bits`
  circuit compiles in milliseconds (regression-tested).
- New perf-regression tests live in
  `[TestWasmCompile.lean](../../Utils/Test/TestWasmCompile.lean)`
  ("Performance regression tests" section) and run on every `lake build
  CleanTests`.

## Known limitations

- **WASM local limit**: each witness output occupies `numWords` locals in the compute function, plus a shared scratch region of `2·numWords` and `numWords` per let-step. Circuits with tens of thousands of multi-word witnesses can approach WASM's 50,000-locals-per-function limit (e.g. SHA256Compress's 80K two-limb witnesses exceed it). Single-word circuits use no scratch and stay well under the limit.
- `dataGet`**/**`hintGet`: these read committed/uncommitted prover data from the Lean environment, which is not representable in a standalone WASM module; they are rejected with `.error`.
- **R1CS export**: lookups and interactions cannot be expressed as quadratic constraints and are rejected (see [Supported operations](#supported-operations)). Note that snarkjs's `r1cs export json` only works for primes of known curves (e.g. BN254); `r1cs info` and `groth16 setup` work for any prime.
- **`init(sanityCheck)`**: the Circom 2 `init` flag that enables constraint checking during witness generation is accepted but ignored — the module does not verify its own constraints at runtime. Use `snarkjs wtns check` on a supported curve instead.

## References

- [snarkjs](https://github.com/iden3/snarkjs)
- [Circom 2 witness-calculator ABI](https://github.com/iden3/circom_runtime/blob/master/js/witness_calculator.js)
- [WASM binary format](https://webassembly.github.io/spec/core/binary/)
- [Montgomery multiplication](https://en.wikipedia.org/wiki/Montgomery_modular_multiplication)


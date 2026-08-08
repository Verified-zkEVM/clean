# WASM Backend

Compiles Clean witness-generation IR to WASM modules with full snarkjs Circom 2 ABI compatibility. Also exports R1CS constraints in JSON format

## Overview

Two compilers sharing a common flattening pass:

- **WASM compiler** (`Compile.lean`): Compiles witness-generation IR to a typed WASM AST, emitted as a binary WASM module. Generates all snarkjs-compatible ABI functions
- **R1CS exporter** (`R1CS.lean`): Converts circuit operations to R1CS JSON format, compatible with `snarkjs`

`compileModule` returns `Except String ByteArray` (a binary WASM module); `compileR1CS` returns `Except String String` (JSON). Inputs the compiler does not support produce `.error` with a reason, never silently wrong output.

## Quick Start

```lean
import Clean.Backends.Wasm.Compile
import Clean.Backends.Wasm.R1CS

-- Compile to binary WASM (single-word, p ≤ 2^32)
def wasm : Except String ByteArray := compileModule 1009 2 myCircuitOps 1

-- Compile to binary WASM (multi-word, BN254 needs 4 words)
def wasmBN254 : Except String ByteArray := compileModule BN254_PRIME 1 myPoseidonOps 4

-- Export R1CS constraints as JSON
def r1csJson : Except String String := compileR1CS BN254_PRIME 1 1 myPoseidonOps 4
```



## Parameters

- `fieldPrime`: The field prime (e.g. 1009 for small primes, `BN254_PRIME` for BN254)
- `numInputs`: Number of public input signals
- `ops`: List of circuit operations (`Operations F`)
- `numWords`: Number of 64-bit limbs per field element. Must satisfy `numWords * 64 >= bitLength(fieldPrime)`
  - Use `1` only for primes ≤ 2^32 (so products fit in an i64 before modular reduction; enforced with an error otherwise)
  - Use `2` for primes between 2^32 and 2^64
  - Use `4` for BN254 (254-bit prime)



## Supported Operations


| Operation                                   | Status                                              |
| ------------------------------------------- | --------------------------------------------------- |
| `const`, `add`, `mul`, `inv`                | ✅ Supported                                         |
| `var`, `localVar`                           | ✅ Supported                                         |
| `ofU64`                                     | ✅ Supported (zero-extends to nw limbs, reduces)      |
| `val`                                       | ✅ Supported (keeps lowest 64 bits of integer rep)   |
| `ite` (if-else)                             | ✅ Supported (multi-value for multi-word)            |
| `lt`, `neq`, `not`, `and` (booleans)        | ✅ Supported                                         |
| `flt` (field-sorted `<`)                    | ✅ Supported (limb-wise compare for multi-word)      |
| `bit` (bit test)                            | ✅ Supported                                         |
| `feq`                                       | ✅ Supported (pairwise limb compare for multi-word)  |
| `lit`, `mapRange`, `envRange`, `bitsOf`     | ✅ Supported                                         |
| `append`                                    | ✅ Supported                                         |
| `listGet`                                    | ✅ Supported (select-sum chain)                       |
| `dataGet`, `hintGet`                          | ❌ Not yet supported (`.error`)                      |
| `native` witnesses (Lean closures)          | ❌ Not compilable (`.error`)                         |
| `idx` (outside `mapRange`)                  | ❌ Invalid (`.error`)                                |
| lookups                                     | Ignored by witness gen; `.error` in R1CS export     |
| interactions                                | ✅ Ignored by witness gen; `.error` in R1CS export |


Unsupported operations make the compiler return `.error` with a descriptive message. All u64-sorted (`U64Expr`) arithmetic is performed on single 64-bit words with WASM's native wrap-around semantics, exactly matching the IR's `UInt64` evaluation.

## Output Format

### Snarkjs ABI

The generated WASM module exports these functions:


| Export                                               | Description                                  |
| ---------------------------------------------------- | -------------------------------------------- |
| `getFieldNumLen32`                                   | Number of 32-bit words per field element     |
| `getRawPrime`                                        | Field prime split into 32-bit words          |
| `readSharedRWMemory`                                 | Read a 32-bit word from shared memory        |
| `writeSharedRWMemory`                                | Write a 32-bit word to shared memory         |
| `getInputSignalSize`                                 | Size of each input signal in 32-bit words    |
| `getInputSize`                                       | Number of public inputs                      |
| `getWitnessSize`                                     | Total number of signals                      |
| `setInputSignal`                                     | Set an input signal value from shared memory |
| `getWitness`                                         | Compute and return witness for a signal      |
| `getMessageChar`                                     | Error message chars (always 0: no messages)  |
| `getVersion` / `getMinorVersion` / `getPatchVersion` | snarkjs version info                         |
| `init`                                               | Initialize signal memory                     |
| `witness`                                            | Compute all witness values                   |


### Using with snarkjs

```bash
# Generate witness directly from the compiled binary WASM
snarkjs wtns calculate circuit.wasm input.json witness.wtns
```

The module implements the [Circom 2 witness-calculator ABI](https://github.com/iden3/circom_runtime/blob/master/js/witness_calculator.js) consumed by snarkjs.

## Field Arithmetic

### Single-word (primes ≤ 2^32)

Uses WASM `i64` operations. Multiplication uses `i64.mul` followed by `i64.rem_u`. Safe for primes where `(p-1)^2 < 2^64` (i.e., `p ≤ 2^32`); larger primes with `numWords = 1` are rejected with an error.

### Multi-word (e.g., BN254)

Full multi-precision arithmetic:

- `$mul64x64`: 64×64 → 128 multiplication with carry detection
- `$fmul`: N×N schoolbook multiplication + CIOS Montgomery reduction (HAC Algorithm 14.36) with 64-bit limbs
- `$fadd`: Limb-wise addition with carry + conditional mod p
- `$finv`: Fermat's little theorem square-and-multiply via `$fmul` (operates in Montgomery form)

Values are kept in Montgomery form (`x·R mod p`, `R = 2^(N*64)`) throughout the computation and converted only at boundaries: constants are emitted as `c·R mod p`, inputs are converted via `montMul(x, R²)`, and outputs are converted back via `montMul(x, 1)`. The reduction uses `n' = -p⁻¹ mod 2^64` and a single conditional subtraction (result < 2p).

## Known Limitations

- **WASM local limit**: each witness output occupies `numWords` locals in the compute function, plus a shared scratch region of `2*numWords` and `numWords` per let-step. Circuits with tens of thousands of multi-word witnesses can approach WASM's 50,000-local-per-function limit (e.g. SHA256Compress's 80K two-limb witnesses exceed it). Single-word circuits use no scratch and stay well under the limit.
- **`dataGet`/`hintGet`**: these read committed/uncommitted prover data from the Lean environment, which is not representable in a standalone WASM module; they are rejected with `.error`.

## References

- [snarkjs Circom 2 ABI](https://github.com/iden3/snarkjs)
- [WASM binary format](https://webassembly.github.io/spec/core/binary/)
- [Montgomery multiplication](https://en.wikipedia.org/wiki/Montgomery_modular_multiplication)


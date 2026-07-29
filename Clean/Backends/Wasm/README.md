# WASM Backend

Compiles Clean witness-generation IR to WASM modules with full snarkjs Circom 2 ABI compatibility. Also exports R1CS constraints in JSON format

## Overview

Two compilers sharing a common flattening pass:

- **WASM compiler** (`Compile.lean`): Compiles witness-generation IR to a typed WASM AST, emitted as WAT text. Generates all snarkjs-compatible ABI functions
- **R1CS exporter** (`R1CS.lean`): Converts circuit operations to R1CS JSON format, compatible with `snarkjs`

Both entry points return `Except String String`: inputs the compiler does not support produce `.error` with a reason, never silently wrong output.

## Quick Start

```lean
import Clean.Backends.Wasm.Compile
import Clean.Backends.Wasm.R1CS

-- Compile to WAT text (single-word, p ≤ 2^32)
def wat : Except String String := compileModule 1009 2 myCircuitOps 1

-- Compile to WAT text (multi-word, BN254 needs 4 words)
def watBN254 : Except String String := compileModule BN254_PRIME 1 myPoseidonOps 4

-- Export R1CS constraints as JSON
def r1csJson : Except String String := compileR1CS BN254_PRIME 1 myPoseidonOps
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
| `ofNat`                                     | ✅ Supported (zero-extends to nw limbs, reduces)      |
| `val`                                       | ✅ Supported (keeps lowest 64 bits of integer rep)   |
| `ite` (if-else)                             | ✅ Supported (multi-value for multi-word)            |
| `lt`, `neq`, `not`, `and` (booleans)        | ✅ Supported                                         |
| `feq`                                       | ✅ Supported (pairwise limb compare for multi-word)  |
| `lit`, `mapRange`                           | ✅ Supported                                         |
| `append`                                    | ✅ Supported                                         |
| `envGet`, `listGet`, `dataGet`, `hintGet`   | ❌ Not yet supported (`.error`)                      |
| `native` witnesses (Lean closures)          | ❌ Not compilable (`.error`)                         |
| `idx` (outside `mapRange`)                  | ❌ Invalid (`.error`)                                |
| lookups                                     | Ignored by witness gen; `.error` in R1CS export     |
| interactions                                | ✅ Ignored by witness gen; `.error` in R1CS export |


Unsupported operations make the compiler return `.error` with a descriptive message. Note that Nat-sorted (`NExpr`) arithmetic is performed on single 64-bit words; operations whose intermediate values exceed 2^64 wrap around.

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
# The WAT text must first be converted to binary WASM using wat2wasm (from wabt):
wat2wasm circuit.wat -o circuit.wasm

# Generate witness
snarkjs wtns calculate circuit.wasm input.json witness.wtns
```

The module implements the [Circom 2 witness-calculator ABI](https://github.com/iden3/circom_runtime/blob/master/js/witness_calculator.js) consumed by snarkjs.

## Field Arithmetic

### Single-word (primes ≤ 2^32)

Uses WASM `i64` operations. Multiplication uses `i64.mul` followed by `i64.rem_u`. Safe for primes where `(p-1)^2 < 2^64` (i.e., `p ≤ 2^32`); larger primes with `numWords = 1` are rejected with an error.

### Multi-word (e.g., BN254)

Full multi-precision arithmetic:

- `$mul64x64`: 64×64 → 128 multiplication with carry detection
- `$fmul`: N×N schoolbook multiplication + Barrett reduction (HAC Algorithm 14.42)
- `$fadd`/`$fsub`: Limb-wise addition/subtraction with carry/borrow + conditional mod p
- `$finv`: Fermat's little theorem square-and-multiply via `$fmul`

Barrett reduction uses the precomputed constant `μ = floor(2^(2*N*64) / p)` with `N+1` limbs.

## References

- [snarkjs Circom 2 ABI](https://github.com/iden3/snarkjs)
- [WASM binary format](https://webassembly.github.io/spec/core/binary/)
- [Barrett reduction](https://en.wikipedia.org/wiki/Barrett_reduction)


# WASM Backend

Compiles Clean witness-generation IR to WASM modules with full snarkjs Circom 2 ABI compatibility. Also exports R1CS constraints in JSON format

## Overview

Two compilers sharing a common flattening pass:

- **WASM compiler** (`Compile.lean`): Compiles witness-generation IR to a typed WASM AST, emitted as WAT text or binary WASM. Generates all snarkjs-compatible ABI functions
- **R1CS exporter** (`R1CS.lean`): Converts circuit operations to R1CS JSON format, compatible with `snarkjs`

## Quick Start

```lean
import Clean.Backends.Wasm.Compile
import Clean.Backends.Wasm.R1CS

-- Compile to WAT text (single-word, p < 2^32)
def wat : String := compileModule 1009 2 myCircuitOps 1

-- Compile to WAT text (multi-word, BN254 needs 4 words)
def watBN254 : String := compileModule BN254_PRIME 1 myPoseidonOps 4

-- Export R1CS constraints as JSON
def r1csJson : String := compileR1CS BN254_PRIME 1 myPoseidonOps
```



## Parameters

- `fieldPrime`: The field prime (e.g. 1009 for small primes, `BN254_PRIME` for BN254)
- `numInputs`: Number of public input signals
- `ops`: List of circuit operations (`Operations F`)
- `numWords`: Number of 64-bit limbs per field element. Must satisfy `numWords * 64 >= bitLength(fieldPrime)`
  - Use `1` for primes < 2^32 (safe) or < 2^64 (requires `$mul64x64` for multiplication)
  - Use `4` for BN254 (254-bit prime)



## Supported Operations


| Operation                                   | Status                                              |
| ------------------------------------------- | --------------------------------------------------- |
| `const`, `add`, `mul`, `inv`                | ✅ Supported                                         |
| `var`, `localVar`                           | ✅ Supported                                         |
| `ofNat`                                     | ✅ Supported (single-word; multi-word via field ops) |
| `ite` (if-else)                             | ✅ Supported (multi-value for multi-word)            |
| `feq`, `lt`, `neq`, `not`, `and` (booleans) | ✅ Supported                                         |
| `envGet`                                    | ❌ Not yet supported                                 |
| `listGet`                                   | ❌ Not yet supported                                 |
| `dataGet`                                   | ❌ Not yet supported                                 |
| `hintGet`                                   | ❌ Not yet supported                                 |
| `idx` (outside `mapRange`)                  | ❌ Not yet supported                                 |


Unsupported operations cause a compile-time panic with a descriptive error message.

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
| `getVersion` / `getMinorVersion` / `getPatchVersion` | snarkjs version info                         |
| `init`                                               | Initialize signal memory                     |
| `witness`                                            | Compute all witness values                   |


### Using with snarkjs

```bash
# Generate witness
snarkjs wtns calculate circuit.wasm input.json witness.wtns

# The WAT text can be converted to binary WASM using wat2wasm:
wat2wasm circuit.wat -o circuit.wasm

# Or use Binary.lean to emit binary directly
```

## Field Arithmetic

### Single-word (primes < 2^32 safe, or < 2^64 with care)

Uses WASM `i64` operations. Multiplication uses `i64.mul` followed by `i64.rem_u`. Safe for primes where `(p-1)^2 < 2^64` (i.e., `p < 2^32`).

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


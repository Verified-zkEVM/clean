# Witgen IR — feature requirements from existing gadgets

Survey of every witness-generation pattern in the gadgets we want the witness IR to
cover: Keccak, SHA256, FemtoCairo, FibonacciWithChannels, Bits, IsZero(Field), and
Circomlib/Poseidon. "Witness callback" = a `ProverEnvironment F → …` closure passed to
`witness` / `witnessField` / `witnessVector` / `ProvableType.witness` / `<==`.

Context: witgen execution is a left fold building the witness array incrementally; each
callback sees only earlier witnesses (`FlatOperation.dynamicWitnesses`,
`Clean/Circuit/Basic.lean:283`; `ComputableWitnesses`, `:305`). Circuit-level loop
combinators (`Clean/Circuit/Loops.lean`: `forEach`, `map`, `mapFinRange`, `foldl`,
`foldlRange`) all require `ConstantLength` bodies.

## A. Per-gadget summary

### Bits (`Clean/Gadgets/Bits.lean`)
- One `witnessVector n` callback: `fieldToBits n (x.eval env)` (`Bits.lean:11`), where
  `fieldToBits` = `.val` → `Nat.testBit i` per index → cast to F → vector build
  (`Utils/Bits.lean:14,136`).
- Circuit-level `forEach bits assertBool` + recomposition constraint (`Bits.lean:14-18`).

### IsZeroField / IsZero
- The only field-inversion callback in the survey:
  `if env x ≠ 0 then (env x)⁻¹ else 0` (`IsZeroField.lean:15`); `<==` for `1 - x*z` (`:18`).
- `IsZero` composes it via `foldlRange (size M)` over a generic `ProvableType M`, threading
  a product accumulator (`IsZero.lean:22-25`).

### SHA256
- `Add32`: `witnessVector 32` computing `(evalBitsNat a + evalBitsNat b) % 2^32` then per-bit
  `/2^i % 2` cast back (`Add32.lean:31`); `witnessField` carry `/2^32 % 2` (`:35`).
  `evalBitsNat` = `Σ (env a[i]).val · 2^i` (`:24`).
- `Xor32`: per-bit Nat XOR on `.val`, cast back (`Xor32.lean:19`). `And32`: per-bit field
  mult (`And32.lean:18`). `Ch32`: pure field arith `g + e*(f-g)` (`Ch32.lean:22`).
- `Maj32`: two sequential `witnessVector 32`, the second reading the first
  (`Maj32.lean:27,30`) — intra-circuit witness reads.
- Sigma gadgets: no witnesses, pure `rotr32`/`shr32` expression reshuffles + `xor32`
  subcircuits (`LowerSigma0.lean:21-24` etc.). `BitwiseOps.lean:42-62` defines `not32`,
  `rotr32` (`Vector.rotate`), `shr32` (`Vector.ofFn` with `if i+k<32`), `constWord32`.
- Round/Schedule/Compress: pure composition. Schedule = `foldlRange 48` with
  accumulator-dependent step reading `w[j-2..j-16]` and `Vector.set`
  (`SHA256Schedule.lean:27-52`); Rounds = `foldlRange 64` with spec constants
  `constWord32 K[i].toNat` (`SHA256Compress.lean:38-39`); Davies-Meyer via
  `mapFinRange 8` of Add32 (`:365-369`).

### Keccak
- All witness work lives in leaf gadgets:
  - `Xor64`: one structured `witness` producing `U64`, each byte
    `(env x.xN).val ^^^ (env y.xN).val`, packed `U64.mk z0…z7`, + 8 `ByteXorTable`
    lookups (`Xor/Xor64.lean:20-39`).
  - `And8`: `(eval x).val &&& (eval y).val` + lookup (`And/And8.lean:24-29`); `And64`
    chains 8× And8 (`And/And64.lean:16-24`).
  - `Rotation64Bits`: field arith `high + low * ((2^(8-offset.val):ℕ):F)`
    (`Rotation64/Rotation64Bits.lean:21-27`); `Rotation64Bytes` is a witness-free
    `if offset = k` byte permutation.
  - `U64.decomposeNat` = base-256 limb split `/256^i % 256` (`Types/U64.lean:114`);
    Horner recomposition (`:103`).
- Theta-family/Chi/RhoPi/Round/Permutation/AbsorbBlock: **no direct witnesses**; pure
  composition via `mapFinRange 5/25`, index arithmetic (`5*i+k`, `i+5`, `i+10`), literal
  constant tables (`RhoPi.lean:10-20`), `Circuit.foldl` over 24 round constants
  (`Permutation.lean:9-11`), `const (U64.fromUInt64 rc)` (`KeccakRound.lean:11-19`).

### FemtoCairo (`Examples/FemtoCairo/FemtoCairo.lean`)
- `fetchInstruction`: 4 `witness` callbacks
  `if (eval pc).val + k < programSize then program ⟨(eval pc).val + k, h⟩ else 0` — reads
  an external Lean table `program : Fin n → F`, Nat bound check with dependent proof,
  conditional fallback; + program-table lookups (`:149-161`).
- `readFromMemory`: `witness fun env => memoryValue env addr` where `memoryValue` reads
  `env.data.getTable MemoryTable` — **hint/prover-data-driven nondeterministic read**
  (`:215-219,260,264`); `<==` one-hot selector combos (`:255,269`); memory lookups.
- `nextState`: witnesses a whole `State` struct, every field a field-equality conditional
  `if eval isLoadState = 1 then eval v1 else eval state.pc + 4` (`:419-423`).
- Step = sequential subcircuit chain (`:570-584`), wrapped in `InductiveTable` (`:793`).

### FibonacciWithChannels (`Examples/FibonacciWithChannels.lean`)
- `add8`: `witness fun env => floorDiv (env (x+y)) 256` (`.val/256`, cast back) (`:74`);
  `fib8`: `mod256 (eval (x+y))` (`:135`).
- Channels (`emit`/`pull`/`push`) carry field messages but **do not feed witness
  callbacks** — constraint/interaction-side only (`:44-46,131-139`).

### Poseidon (`Circomlib/Poseidon.lean`)
- All witnesses are `<==` with pure field arithmetic: powers (Sigma `:41-43`), matrix rows
  `M[0][0]*a0 + M[1][0]*a1` (`:233`), sparse-matrix partial rounds (`:317-319`), ark add
  (`:209`). Constants from Lean `Vector ℕ` tables `C_t2/M_t2/S_t2/P_t2` indexed by
  round/offset (`:189-202`).
- Composition: `Circuit.foldl` over round-index vectors
  (`ApplyFullRounds:279`, `ApplyPartialRoundsOpt:382`). No Nat ops, no hints.

## B. Required IR features (core)

1. **Environment reads** of earlier witnesses / input expressions (`env x`, `env a[i]`) —
   universal.
2. **Field arithmetic** (`+ - *`, constants, Nat→F cast) — Poseidon, Ch32, And32, Maj32,
   Rotation64Bits, FemtoCairo selectors.
3. **Field inversion** — only IsZeroField (`:15`). First-class op or intrinsic.
4. **`ZMod.val` (F→Nat) / Nat→F cast round-trip** — pervasive: all bitwise/byte gadgets,
   Add32, Bits, Fibonacci, FemtoCairo.
5. **Nat-domain arithmetic**: `+ * / % &&& ^^^ 2^k testBit` — the single largest demand
   (Add32, Bits, Xor/And leaves, U64 decomposition, Fibonacci, Rotation64Bits). The IR
   must model a Nat (or bounded-int) domain alongside the field domain with explicit
   `val`/`cast` boundaries.
6. **Fixed-size vector construction**: `ofFn`, `mapRange`, `mapFinRange`, `map`, `#v[...]`
   literals, `replicate`, `append`, `set`, `rotate`, indexing.
7. **Conditionals in callbacks**, branching on (a) field equality (FemtoCairo `:420`,
   IsZeroField `:15`) and (b) Nat bound checks (FemtoCairo `:149`, `shr32`).
8. **Let-bindings** (Xor64 `:21`, Add32 `:32`).
9. **Struct packing to field elements** matching `ProvableType.witness` serialization —
   `U64.mk`, FemtoCairo `State`/`DecodedInstruction`.
10. **Reads from constant tables** by runtime-computed index — FemtoCairo `program`,
    SHA `K`, Poseidon `C/M/S/P` tables, Keccak round constants. Model as IR-level
    constant arrays.

## C. Intrinsic / escape-hatch candidates

1. **Field inverse** (IsZeroField) — natural primitive.
2. **Spec-function shapes**: `fieldToBits`/`testBit` decomposition, `U64.decomposeNat` /
   Horner recomposition, Nat bitwise/rotates — either inline to feature 5 or become named
   bitwise/rotate/decompose intrinsics. Round-constant tables are constant data, not
   computation.
3. **Hint/external-data reads** — FemtoCairo `memoryValue` via `env.data.getTable`, and
   `program` table reads. Genuinely nondeterministic prover input; needs an opaque
   "hint lookup" primitive keyed like `ProverData : String → (n:ℕ) → Array (Vector F n)`.
   Clearest escape hatch: the value comes from outside the computation.

## D. Composition requirements (circuit-level witgen pipeline)

1. **Sequential subcircuit splicing** with witness-offset threading — every composite
   gadget.
2. **Statically-bounded loops** (`mapFinRange`, `foldl`, `foldlRange`, `forEach`) with
   `ConstantLength` bodies; including **accumulator-dependent witnessing** (SHA Schedule
   reads `w[j-k]` from the evolving accumulator; Permutation/Rounds fold state forward).
3. **Lookups** co-occurring with witnesses (ByteTable/ByteXorTable; FemtoCairo program &
   memory tables, where the looked-up value is also witnessed from the same table).
4. **Channels/interactions** — must be emitted, but do not feed witness computation in
   surveyed code.
5. **Constant folding** of circuit-level constants (`constWord32`, `U64.fromUInt64`,
   `.const` tables).
6. **InductiveTable multi-row recurrence** — each row's input is the previous row's
   output (FemtoCairo `:793`).

## E. Risks / things that resist a naive first-order field-expression IR

1. **Dual Nat/field domain is mandatory** — a field-only IR cannot express SHA/Keccak
   byte logic.
2. **Data-dependent control flow** — branch conditions computed from runtime values
   (field equality, Nat bounds with dependent index proofs).
3. **Hint-driven nondeterminism** — FemtoCairo memory/program reads must be opaque
   primitives.
4. **Lean-closure content** — callbacks close over Lean tables/functions
   (`program : Fin n → F`, constant vectors); the IR must reference these as constant
   arrays.
5. **Evaluation-order sensitivity** — intra-circuit witness reads (Maj32) and
   accumulator recurrences mean IR evaluation order must match the offset-fold semantics
   (`Basic.lean:283,305`).
6. **Length polymorphism** — `IsZero` over generic `size M`, `witnessVector m`; lengths
   are static per instantiation but generic in source; IR must be length-polymorphic or
   monomorphized per use.
7. **Conditionals returning structs** — FemtoCairo `nextState` witnesses a struct whose
   every field is a conditional; conditionals must compose with struct packing.

**Favorable finding:** no recursion and no runtime-unbounded witness lengths anywhere in
the surveyed gadgets — all loops are statically bounded with `ConstantLength` bodies. The
hard parts are the Nat domain, data-dependent branching, and the hint escape hatch.

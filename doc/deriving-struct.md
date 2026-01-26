# ProvableStruct Deriving Macro Implementation

## What Was Built

A `deriving` handler for the `ProvableStruct` type class, located at `Clean/Utils/Tactics/ProvableStructDeriving.lean`. It's exported via `Clean/Circuit.lean`.

## How It Works

The macro generates `ProvableStruct` instances for structures of the form:
```lean
structure Foo (F : Type) where
  field1 : F
  field2 : SomeType F
  field3 : AnotherType F
deriving ProvableStruct
```

**Generated code equivalent:**
```lean
instance : ProvableStruct Foo where
  components := [field, SomeType, AnotherType]
  toComponents := fun ⟨field1, field2, field3⟩ => .cons field1 (.cons field2 (.cons field3 .nil))
  fromComponents := fun (.cons field1 (.cons field2 (.cons field3 .nil))) => Foo.mk field1 field2 field3
```

## What It Supports

1. **Simple field type `F`** → mapped to `field`
2. **Applied type map `M F`** where `M` is a constant → mapped to `M`
3. **Type aliases** like `BLAKE3State F` (which is `ProvableVector U32 16 F`) work because they reduce to the `M F` pattern

## Current Limitations (Opportunities for Enhancement)

1. **Extra type parameters**: Structures like `structure Inputs (n : ℕ) (F : Type)` don't work - macro only handles exactly one type parameter
   - Files affected: `Conditional.lean`, `Mux1.lean`, `Mux2.lean`, `Mux3.lean`

2. **Non-standard field syntax**: `Vector (U32 F) n` doesn't match the `M F` pattern (the `F` is nested inside)
   - Files affected: `BLAKE3/Round.lean`, `FinalStateUpdate.lean`, `ApplyRounds.lean`, `FinalizeChunk.lean`
   - Note: These manually write `ProvableVector U32 n` as the component type

3. **Definitional size equality**: When code uses `Fin (size MyStruct)` with literal indices, the size must be definitionally equal to a number. The derived instance computes size but doesn't reduce definitionally.
   - Files affected: `Fibonacci32.lean` (has explicit `combinedSize := 8`)

4. **Ordering requirement**: Component types must have `ProvableType` instances defined *before* the structure that uses them. Solution: move `ProvableType` instances right after their structure definitions (done in `FemtoCairo/Types.lean`).

## Key Implementation Details

Location: `Clean/Utils/Tactics/ProvableStructDeriving.lean`

**Core functions:**
- `analyzeFieldType`: Determines if field is `F` (→ `field`) or `M F` (→ `M`)
- `getProjectionInfo`: Extracts field type from projection function
- `mkProvableStructInstance`: Generates the full instance using syntax quotations
- `provableStructDerivingHandler`: Registered handler that Lean calls

**Pattern matching approach:**
- Uses `⟨f1, f2, f3⟩` syntax for `toComponents` input pattern
- Uses `.cons f1 (.cons f2 (.cons f3 .nil))` for both `toComponents` output and `fromComponents` input pattern
- Uses `StructName.mk f1 f2 f3` for `fromComponents` output

## Files Modified

**Commit 1** - Created macro:
- `Clean/Utils/Tactics/ProvableStructDeriving.lean` (new)
- `Clean/Circuit.lean` (added import)

**Commit 2** - Replaced 20+ instances across 17 files:
- Test files, Gadgets (Addition, And, Or, Xor, ByteDecomposition, BLAKE3G), Comparators, FemtoCairo

**Commit 3** - Replaced 6 more instances:
- `FemtoCairo/Types.lean` (reorganized + 3 instances)
- `Keccak/AbsorbBlock.lean`, `ThetaXor.lean` (2 instances)
- `Fibonacci32Inductive.lean` (1 instance)

## Remaining Manual Instances

```
Clean/Tables/Fibonacci32.lean                    # needs combinedSize := 8
Clean/Tables/BLAKE3/ProcessBlocksInductive.lean  # ProvableVector in field
Clean/Gadgets/BLAKE3/Round.lean                  # Vector (U32 F) n syntax
Clean/Gadgets/BLAKE3/FinalStateUpdate.lean       # Vector (U32 F) n syntax
Clean/Gadgets/BLAKE3/ApplyRounds.lean            # Vector (U32 F) n syntax
Clean/Gadgets/BLAKE3/FinalizeChunk.lean          # Vector (U32 F) n syntax
Clean/Gadgets/Conditional.lean                   # extra type param M
Clean/Circomlib/Mux1.lean                        # extra type param n
Clean/Circomlib/Mux2.lean                        # extra type param n  
Clean/Circomlib/Mux3.lean                        # extra type param n
```

## Potential Enhancements

1. **Support `Vector (M F) n` syntax**: Recognize this pattern and map to `ProvableVector M n`

2. **Support extra type parameters**: Handle `structure Foo (n : ℕ) (F : Type)` by generating `instance {n : ℕ} : ProvableStruct (Foo n)`

3. **Support `fields n` syntax**: Recognize `Vector F n` and map to `fields n`

4. **Explicit size**: Add syntax like `deriving ProvableStruct with combinedSize := 8` for cases needing definitional equality

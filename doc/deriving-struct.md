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
4. **Extra type parameters**: Structures like `structure Inputs (n : ℕ) (F : Type)` or `structure Inputs (M : TypeMap) (F : Type)` are supported
5. **`Vector (M F) n` syntax**: Fields like `message : Vector (U32 F) 16` are recognized and mapped to `ProvableVector U32 16`
6. **`Vector F n` syntax**: Fields like `data : Vector F n` are recognized and mapped to `fields n`

### Extra Type Parameters

For structures with extra type parameters before `F`:

```lean
structure Inputs (n : ℕ) (F : Type) where
  data : Vector F n
deriving ProvableStruct
```

Generates:
```lean
instance {n : ℕ} : ProvableStruct (Inputs n) where
  components := [fields n]
  ...
```

For `TypeMap` parameters, it automatically adds `ProvableType` constraints:

```lean
structure Inputs (M : TypeMap) (F : Type) where
  selector : F
  ifTrue : M F
  ifFalse : M F
deriving ProvableStruct
```

Generates:
```lean
instance {M : TypeMap} [ProvableType M] : ProvableStruct (Inputs M) where
  components := [field, M, M]
  ...
```

### Vector Field Types

The macro recognizes both `Vector F n` and `Vector (M F) n` patterns:

```lean
structure State (F : Type) where
  message : Vector (U32 F) 16  -- maps to ProvableVector U32 16
  buffer : Vector F 64          -- maps to fields 64
deriving ProvableStruct
```

**Note:** For `Vector (M F) n` to work, `M` must have a `NonEmptyProvableType` instance, not just `ProvableType`. This is because `ProvableVector.instance` requires `NonEmptyProvableType`.

## Current Limitations

1. **Definitional size equality**: When code uses `Fin (size MyStruct)` with literal indices, the size must be definitionally equal to a number. The derived instance computes size but doesn't reduce definitionally.
   - Files affected: `Fibonacci32.lean` (has explicit `combinedSize := 8`)

2. **Ordering requirement**: Component types must have `ProvableType` instances defined *before* the structure that uses them. Solution: move `ProvableType` instances right after their structure definitions.

3. **Complex nested types**: Some complex nested types in `FinalizeChunk.lean` require manual instances due to proof compatibility issues.

## Key Implementation Details

Location: `Clean/Utils/Tactics/ProvableStructDeriving.lean`

**Core functions:**
- `analyzeFieldType`: Determines if field is `F` (→ `field`), `M F` (→ `M`), `Vector F n` (→ `fields n`), or `Vector (M F) n` (→ `ProvableVector M n`)
- `analyzeParam`: Determines parameter kind (natural number, TypeMap, or other) for generating instance binders
- `extractNatLit?`: Extracts natural number literals from elaborated `OfNat.ofNat` expressions
- `mkProvableStructInstance`: Generates the full instance using syntax quotations
- `provableStructDerivingHandler`: Registered handler that Lean calls

**Pattern matching approach:**
- Uses `⟨f1, f2, f3⟩` syntax for `toComponents` input pattern
- Uses `.cons f1 (.cons f2 (.cons f3 .nil))` for both `toComponents` output and `fromComponents` input pattern
- Uses `StructName.mk f1 f2 f3` for `fromComponents` output

## Files Using `deriving ProvableStruct`

The following files now use `deriving ProvableStruct` instead of manual instances:

### Basic structures (single type parameter)
- Test files, Gadgets (Addition, And, Or, Xor, ByteDecomposition, BLAKE3G), Comparators, FemtoCairo
- `Fibonacci32Inductive.lean`
- `Keccak/AbsorbBlock.lean`, `ThetaXor.lean`

### Structures with extra ℕ parameter
- `Clean/Circomlib/Mux1.lean` (MultiMux1.Inputs)
- `Clean/Circomlib/Mux2.lean` (MultiMux2.Inputs, Mux2.Inputs)
- `Clean/Circomlib/Mux3.lean` (MultiMux3.Inputs, Mux3.Inputs)

### Structures with extra TypeMap parameter
- `Clean/Gadgets/Conditional.lean` (Inputs)

### Structures with `Vector (M F) n` fields
- `Clean/Gadgets/BLAKE3/Round.lean`
- `Clean/Gadgets/BLAKE3/FinalStateUpdate.lean`
- `Clean/Gadgets/BLAKE3/ApplyRounds.lean`

## Remaining Manual Instances

```
Clean/Tables/Fibonacci32.lean                    # needs combinedSize := 8
Clean/Tables/BLAKE3/ProcessBlocksInductive.lean  # complex structure
Clean/Gadgets/BLAKE3/FinalizeChunk.lean          # proof compatibility issues
```

## Usage

Simply add `deriving ProvableStruct` after your structure definition:

```lean
import Clean.Circuit  -- or import Clean.Utils.Tactics.ProvableStructDeriving

structure MyInputs (F : Type) where
  x : F
  y : SomeType F
deriving ProvableStruct
```

For files that don't import `Clean.Circuit`, add:
```lean
import Clean.Utils.Tactics.ProvableStructDeriving
```

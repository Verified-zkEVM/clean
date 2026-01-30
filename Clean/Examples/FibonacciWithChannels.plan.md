# FibonacciWithChannels Soundness Proof Plan

## Current Status: `add8_interactions_satisfy_requirements` structured using `add8.soundness` abstractly

## Completed Steps

### Step 1: Verifier interaction analysis ✓
- Proved verifier emits pull `(-1, (n, x, y))` and push `(1, (0, 0, 1))`

### Step 2: Channel balance extraction ✓
- Extracted `h_fib_balanced` from `h_balanced`
- Proved `h_fib_mults`: all multiplicities in FibonacciChannel are ±1

### Step 3: h_bytes_guarantees ✓
- Proved BytesChannel pulls have `z.val < 256`
- Uses contradiction: if `z.val ≥ 256`, then all entries for `#v[z]` have `mult = -1`, so sum < 0

### Step 4: h_add8_guarantees ✓
- Proved Add8Channel pull guarantees hold
- Structure:
  - Case split: entry from tables or verifier
  - Verifier: `verifier_add8_interactions_empty`
  - Tables at i=0 (pushBytes): `pushBytes_add8_interactions_empty`
  - Tables at i=1 (add8): `add8_interactions_satisfy_requirements`
  - Tables at i=2 (fib8): `fib8_add8_interactions_mult_neg`

### Step 5: h_fib8_soundness ✓
- Structure complete for validity transfer
- Case split: entry from tables or verifier
  - Verifier case: push is `(0, 0, 1)` ✓
  - Tables case: use `fib8_fib_push_has_matching_pull`

## `add8_interactions_satisfy_requirements` Proof Structure

Successfully wired up to use `add8.soundness` abstractly:

1. **Extract constraints**: From `table.Constraints`, we get `h_row_constraints : ConstraintsHoldFlat env ops.toFlat`
   - `table.abstract.operations` unfolds to `[witness inputs, subcircuit add8]`
   - `ConstraintsHold` skips witnesses and extracts `ConstraintsHoldFlat` from subcircuits
   - `toSubcircuit.ops.toFlat = ops.toFlat` by `Operations.toNested_toFlat`

2. **Build Guarantees**: `h_guarantees : ops.forAllWithInteractions env 0 [] { interact := i.Guarantees }`
   - BytesChannel.pull needs `z.val < 256` (**sorry** - needs extraction from `h_bytes_guarantees`)
   - Add8Channel.emit has `Guarantees = True`

3. **Bridge lemma**: `constraintsHoldFlat_to_soundness` converts `ConstraintsHoldFlat + Guarantees → ConstraintsHoldWithInteractions.Soundness`
   (**sorry** - lemma needs proof)

4. **Apply add8.soundness**: Gets `Spec ∧ Requirements`

5. **Extract Requirements**: Simplify to get the concrete implication about `z.val = (x.val + y.val) % 256`

6. **Finish**: Apply with `h_mult`, `h_x_range`, `h_y_range`

## Remaining Sorries

### Bridge infrastructure
| Line | Lemma | Description |
|------|-------|-------------|
| 957 | `constraintsHoldFlat_to_soundness` | Bridge: ConstraintsHoldFlat + Guarantees → Soundness |

### In `add8_interactions_satisfy_requirements`
| Line | Description |
|------|-------------|
| 1049 | `h_guarantees` - need `z.val < 256` from `h_bytes_guarantees` |
| 1059 | `h_eval_eq` - definitional equality, needs ProvableStruct simp |

### Other infrastructure (peripheral)
| Line | Description |
|------|-------------|
| 203 | `pushBytes` ElaboratedCircuit instance (4 sorries) |
| 790 | something else |
| 1130 | something else |

## Architecture Notes

The structural lemmas characterize which circuits emit what to each channel:

```
Circuit      | BytesChannel | Add8Channel | FibonacciChannel
-------------|--------------|-------------|------------------
pushBytes    | push (many)  | empty       | empty
add8         | pull (1x)    | push (1x)   | empty
fib8         | empty        | pull (1x)   | push+pull
verifier     | empty        | empty       | push+pull
```

## Key Insight

The proof uses `add8.soundness` abstractly rather than manually unfolding circuit constraints:
- `add8.soundness` proves `ConstraintsHoldWithInteractions.Soundness → Spec ∧ Requirements`
- `Requirements` for Add8Channel says: if push, then `z.val = (x.val + y.val) % 256`
- We provide the `Soundness` via the bridge lemma from `ConstraintsHoldFlat + Guarantees`

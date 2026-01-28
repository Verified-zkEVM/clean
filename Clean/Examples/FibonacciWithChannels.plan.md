# FibonacciWithChannels Soundness Proof Plan

## Current Status: Proof structure complete, sorries for structural lemmas

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

## Remaining Sorries

### Infrastructure (peripheral)
| Line | Description |
|------|-------------|
| 221-223 | `pushBytes` ElaboratedCircuit instance |

### User has in other branch
| Line | Description |
|------|-------------|
| 693 | `bytes_push_val_lt_256` |
| 708 | `fib_table_interaction_mult_pm_one` |

### Add8Channel structural lemmas
| Line | Lemma | Description |
|------|-------|-------------|
| 713 | `verifier_add8_interactions_empty` | Verifier only uses FibonacciChannel |
| 720 | `pushBytes_add8_interactions_empty` | pushBytes only uses BytesChannel |
| 729 | `fib8_add8_interactions_mult_neg` | fib8 only pulls from Add8Channel |
| 741 | `add8_interactions_satisfy_requirements` | add8 pushes satisfy Requirements |

### FibonacciChannel structural lemmas
| Line | Lemma | Description |
|------|-------|-------------|
| 752 | `pushBytes_fib_interactions_empty` | pushBytes doesn't use FibonacciChannel |
| 759 | `add8_fib_interactions_empty` | add8 doesn't use FibonacciChannel |
| 774 | `fib8_fib_push_has_matching_pull` | fib8 pushes have matching pulls |

### Main proof
| Line | Description |
|------|-------------|
| 1153 | `h_is_fib8`: table is fib8 (same pattern as h_push_req) |
| 1169 | `n_i.val + 1 < p`: overflow check |
| 1172 | Validity transfer: `IsValidFibState n_i → IsValidFibState (n_i+1)` |

## Architecture Notes

The structural lemmas characterize which circuits emit what to each channel:

```
Circuit      | BytesChannel | Add8Channel | FibonacciChannel
-------------|--------------|-------------|------------------
pushBytes    | push (many)  | empty       | empty
add8         | pull (3x)    | push (1x)   | empty
fib8         | empty        | pull (1x)   | push+pull
verifier     | empty        | empty       | push+pull
```

## Proof Flow

1. Balance guarantees every pull has matching push
2. BytesChannel: all pushes have `val < 256` (pushBytes table contains 0..255)
3. Add8Channel: pulls satisfy `z = (x + y) % 256`
4. FibonacciChannel:
   - Every push either is `(0, 0, 1)` (initial) or has a matching pull predecessor
   - Validity transfers through the chain
   - Public input `(n, x, y)` is valid

## Next Steps

1. Prove the structural lemmas (mainly about circuit structure)
2. The overflow check `n_i.val + 1 < p` needs either:
   - An assumption in the circuit constraints
   - Derivation from the fibonacci sequence length being bounded
3. The validity transfer needs to use `h_add8_guarantees` to get `z_i = (x_i + y_i) % 256`

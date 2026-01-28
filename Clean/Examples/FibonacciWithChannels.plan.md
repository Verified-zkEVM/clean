# FibonacciWithChannels soundness proof plan

This note captures learnings and a concrete plan for completing
`fibonacciEnsemble_soundness` in `Clean/Examples/FibonacciWithChannels.lean`.

## General guidelines

This is a large proof, so try to make incremental progress. Prove intermediate statements (with `have`) or work backwards from the goal with `suffices`.

Report back to the user when either:

- You have finished the proof. In this case, start your message with "SUCCESS!"
- You feel entirely stuck. You have tried to make progress from a lot of different angles, but you're at a point where no further progress seems to be possible. In this case, start your message with "I am entirely stuck, because".

## Current Status (Updated 2026-01-28)

### Sorries remaining in main theorem

```
grep -n "sorry" Clean/Examples/FibonacciWithChannels.lean
```

| Line | Location | Type | Status |
|------|----------|------|--------|
| 212-214 | `pushBytes` | Infrastructure | Peripheral - not blocking main proof |
| 681 | `bytes_interaction_large_val_is_pull` | Structural helper | **NEW** - cleanly stated |
| 696 | `fib_table_interaction_mult_pm_one` | Structural helper | **NEW** - cleanly stated |
| 894 | `h_add8_guarantees` | Semantic | Needs layered derivation |
| 922 | `h_fib8_soundness` (fib8 case) | Semantic | Needs structural extraction |

### What's proven

- ✅ `h_bytes_guarantees` - Complete! Uses `bytes_interaction_large_val_is_pull`
- ✅ `h_fib_mults` - Complete! Uses `fib_table_interaction_mult_pm_one`
- ✅ `h_fib8_soundness` (verifier case) - Push is (0, 0, 1)
- ✅ Full proof chain: `all_fib_pushes_valid → h_matching → h_valid → spec`

### Proof architecture (in the code)

```
bytes_interaction_large_val_is_pull  ───┐
       (sorry - line 681)              │
                                       ▼
h_bytes_guarantees  ◄──────────────── uses helper
       (DONE!)                         
                                       
h_add8_guarantees   ◄──────────────── similar pattern to h_bytes_guarantees
       (sorry - line 894)              
                                       ▼
h_fib8_soundness (fib8 case) ◄──────── uses add8 guarantees
       (sorry - line 922)              
                                       ▼
fib_table_interaction_mult_pm_one  ───┐
       (sorry - line 696)              │
                                       ▼
h_fib_mults  ◄─────────────────────── uses helper
       (DONE!)                         
                                       ▼
all_fib_pushes_valid  ◄──────────────  
       (DONE!)                         
                                       ▼
h_valid = spec  ◄──────────────────── DONE!
```

## Next steps for the next agent

### Priority 1: Structural helper lemmas (lines 681, 696)

These are cleanly stated and can be proven mechanically:

**`bytes_interaction_large_val_is_pull` (line 681)**:
- Statement: For BytesChannel interactions where `entry.2[0].val ≥ 256`, we have `entry.1 = -1`
- Proof approach:
  1. BytesChannel interactions come from: pushBytes, add8, fib8, verifier
  2. fib8 and verifier don't emit to BytesChannel (their `localAdds` filtered gives `[]`)
  3. pushBytes only pushes values 0..255 (so no entry with val ≥ 256)
  4. add8 only pulls from BytesChannel (mult = -1)
  5. Therefore any entry with val ≥ 256 must be from add8, hence mult = -1

**`fib_table_interaction_mult_pm_one` (line 696)**:
- Statement: For FibonacciChannel table interactions, `entry.1 = 1 ∨ entry.1 = -1`
- Proof approach:
  1. FibonacciChannel table interactions come from: pushBytes, add8, fib8
  2. pushBytes doesn't emit to FibonacciChannel (different channel name)
  3. add8 doesn't emit to FibonacciChannel (different channel name)
  4. fib8 only pulls (mult=-1) and pushes (mult=1) to FibonacciChannel

Both require unfolding `localAdds` definitions and using `Channel.filter_self_add`, `Channel.filter_self_single`, and showing filtering for wrong channel gives `[]`.

### Priority 2: `h_add8_guarantees` (line 894)

Similar structure to `h_bytes_guarantees`:
- For each add8 pull, show the guarantee holds (x < 256 → y < 256 → z = (x+y) % 256)
- Use balance to find matching push
- Pushes come from add8 rows, which satisfy the requirement by add8.soundness

### Priority 3: `h_fib8_soundness` fib8 case (line 922)

For each fib8 push entry:
1. Extract the corresponding row's input (n_i, x_i, y_i) and output z_i
2. Show the pull `(-1, #v[n_i, x_i, y_i])` is in fibInteractions
3. Show validity transfer: `IsValidFibState n_i x_i y_i → IsValidFibState (n_i + 1) y_i z_i`
   - Use add8 guarantees to get `z_i = (x_i + y_i) % 256`
   - Use fibonacci_bytes to get `x_i, y_i < 256` from input validity
   - Conclude output is next fibonacci state

## Key lemmas available

- `sum_neg_ones`: sum of -1s = -(length)
- `exists_push_of_pull`: balance + mults ±1 → pull has matching push
- `all_fib_pushes_valid`: strong induction proving all fib pushes are valid
- `lift_constraints_with_guarantees`: bridges raw constraints to per-circuit soundness
- `Channel.filter_self_add`, `Channel.filter_self_single`: for filtering channel interactions

## Tools

**Inspect proof state at a line:**
```bash
mcporter call lean-lsp.lean_goal file_path:Clean/Examples/FibonacciWithChannels.lean line:XXX
```

**Build and check errors:**
```bash
lake build Clean.Examples.FibonacciWithChannels 2>&1 | grep "error:"
```

**Find sorries:**
```bash
grep -n "sorry" Clean/Examples/FibonacciWithChannels.lean
```

## Historical notes

- The proof uses a contradiction argument for `h_bytes_guarantees`: if z.val ≥ 256, then all interactions for #v[z] are pulls (sum of -1s), but balance says sum = 0, so the list is empty, contradicting that we have a pull.
- The channel filtering infrastructure (`Channel.filter_self`, `Channel.filter_other`) has some sorries in `Clean/Circuit/Channel.lean` but the key lemmas `filter_self_add` and `filter_self_single` are proven.
- `ZMod.natCast_eq_zero_iff` is useful for finite field arithmetic: `(n : F p) = 0 ↔ p ∣ n`.

# FibonacciWithChannels soundness proof plan

This note captures learnings and a concrete plan for completing
`fibonacciEnsemble_soundness` in `Clean/Examples/FibonacciWithChannels.lean`.

## General guidelines

This is a large proof, so try to make incremental progress. Prove intermediate statements (with `have`) or work backwards from the goal with `suffices`.

Report back to the user when either:

- You have finished the proof. In this case, start your message with "SUCCESS!"
- You feel entirely stuck. You have tried to make progress from a lot of different angles, but you're at a point where no further progress seems to be possible. In this case, start your message with "I am entirely stuck, because".

## What we learned so far

- The soundness proof must **derive the ensemble spec from the given hypotheses**
  (`Constraints`, `BalancedChannels`, `VerifierAccepts`), without modifying their intent.
- It is **invalid** to finish by deriving `False` from the hypotheses (e.g. by
  changing `ConstraintsHold` or collapsing `VerifierAccepts` into a contradiction).
- The local soundness theorems for `FormalCircuitWithInteractions` are the key:
  each circuit proves
  ```
  (constraints ∧ channel guarantees) ⇒ (spec ∧ channel requirements).
  ```
  If we can establish **channel guarantees globally**, we can upgrade these to
  ```
  constraints ⇒ spec.
  ```
- The **channel balance** hypothesis is intended to derive global guarantees
  from requirements: a pulled element (multiplicity -1) should be matched by a
  push (positive multiplicity), and the push side is where requirements are proved.
- **Do NOT re-derive circuit-specific facts at the ensemble level.** All concrete
  constraint reasoning (e.g., what the assert equations mean, how carry bits work)
  is already done inside each circuit's soundness proof. The ensemble proof should
  ONLY use the abstract `Spec` and `Requirements` outputs of per-circuit soundness.
  For example, `fib8.soundness` already proves that IF the fibonacci channel
  guarantees hold for the pull AND the add8 channel guarantees hold for the pull,
  THEN the push satisfies fibonacci requirements. We should use this directly,
  not re-derive it from raw constraints.

## Key type-level structure

### Per-circuit soundness (`FormalCircuitWithInteractions.Soundness`)

```
∀ offset env interactions input_var input,
  eval env input_var = input →
  ConstraintsHoldWithInteractions.Soundness env interactions ops →
  Spec input output env ∧
  ConstraintsHoldWithInteractions.Requirements env interactions ops
```

Where:
- `ConstraintsHoldWithInteractions.Soundness` = raw constraints (asserts, lookups) 
  **PLUS channel guarantees** for each interaction
- `ConstraintsHoldWithInteractions.Requirements` = channel **requirements** output
  by each interaction

So the per-circuit soundness says:
**constraints + guarantees ⇒ spec + requirements**

### Ensemble-level `ConstraintsHold` (in the ensemble file)

```
ops.forAll 0 { assert _ e := env e = 0, lookup _ l := l.Contains env, ... }
```

This checks raw constraints only — NO channel guarantees. Interactions default to `True`.

### The lifting problem

The core challenge: go from raw `ConstraintsHold` (ensemble level) to
`ConstraintsHoldWithInteractions.Soundness` (needed for per-circuit soundness).
This requires establishing that **channel guarantees hold globally**.

## High-level plan

### Step 0: Lifting lemma ✅ DONE

Prove a general lemma:
```
ConstraintsHold env ops ∧ (all channel guarantees hold for these interactions) →
ConstraintsHoldWithInteractions.Soundness env interactions ops
```

This lemma bridges the ensemble-level constraint representation to the per-circuit
soundness input. **This is implemented as `lift_constraints_with_guarantees`.**

### Step 1: Derive channel guarantees layer by layer

The channel dependency graph for this ensemble is **acyclic except for fibonacci**:

```
pushBytes ──pushes──→ BytesChannel ──guarantees──→ add8 (pulls bytes)
add8      ──pushes──→ Add8Channel  ──guarantees──→ fib8 (pulls add8)
fib8      ──pushes──→ FibChannel   ──guarantees──→ fib8 (pulls fib — CYCLIC)
verifier  ──pushes──→ FibChannel   ──guarantees──→ verifier (pulls fib)
```

**Acyclic channels (bytes, add8):**
1. Apply `pushBytes.soundness` (needs no guarantees, since pushBytes has no pulls)
   → get `pushBytes.Requirements` for all emitted bytes
2. From per-message balance on BytesChannel + pushBytes requirements
   → derive BytesChannel **guarantees** for all pulls
3. Apply `add8.soundness` with BytesChannel guarantees
   → get `add8.Spec` + `add8.Requirements` for add8 emissions
4. From per-message balance on Add8Channel + add8 requirements
   → derive Add8Channel **guarantees** for all pulls

**Cyclic channel (fibonacci):**
5. Apply `fib8.soundness` with FibChannel + Add8Channel guarantees
   → get `fib8.Requirements` for fibonacci pushes (the next valid state)
   → BUT this requires FibChannel guarantees for the pull, creating a cycle

6. Break the cycle with **strong induction on the step counter** (as in
   `all_fib_pushes_valid`). The verifier's push of `(0, 0, 1)` provides the
   base case. Each fib8 row's push at step k+1 depends on a pull at step k,
   which by per-message balance must have a matching push at step k.
   By the IH, that push satisfies FibChannel requirements/guarantees.

### Step 2: Conclude the spec

Once all FibChannel guarantees are established:
- The verifier pulls `(n, x, y)` with guaranteed `IsValidFibState n x y`
- Apply `fibonacciVerifier.soundness` → get the ensemble spec

## Current Status (Updated 2026-01-28)

### Sorries remaining

```bash
grep -n "sorry" Clean/Examples/FibonacciWithChannels.lean
```

| Line | Location | Type | Description |
|------|----------|------|-------------|
| 220-222 | `pushBytes` | Infrastructure | Peripheral - not blocking main proof |
| 684 | `bytes_push_val_lt_256` | Structural helper | BytesChannel non-pulls have val < 256 |
| 699 | `fib_table_interaction_mult_pm_one` | Structural helper | FibChannel table mults are ±1 |
| 896 | `h_add8_guarantees` | Semantic | Needs layered derivation |
| 924 | `h_fib8_soundness` (fib8 case) | Semantic | Needs structural extraction |

### What's proven in main theorem

- ✅ `h_bytes_guarantees` - Uses contradiction: if val ≥ 256, all entries are pulls, sum < 0
- ✅ `h_fib_mults` - Uses `fib_table_interaction_mult_pm_one` helper  
- ✅ `h_fib8_soundness` (verifier case) - Push is (0, 0, 1)
- ✅ Final chain: `all_fib_pushes_valid → h_matching → h_valid → spec`

### Key insight about multiplicities

**BytesChannel multiplicities are NOT ±1!** The `pushBytes` circuit pushes each byte value
with an arbitrary multiplicity (whatever balances the pulls from add8). For example, if
byte 42 is pulled 5 times across different add8 rows (each with mult -1), then pushBytes
pushes byte 42 with multiplicity 5.

This means we can't use `exists_push_of_pull` for BytesChannel. Instead, `h_bytes_guarantees`
uses a different argument: if `z.val ≥ 256`, then there are no pushes for `#v[z]` (since
pushBytes only pushes 0..255), so all entries for `#v[z]` are pulls (mult = -1), making
the sum negative, which contradicts balance.

### Proof architecture in the code

```
bytes_push_val_lt_256  ────────────────┐
       (sorry - line 684)              │
                                       ▼
h_bytes_guarantees  ◄───────────────── DONE (contradiction: val ≥ 256 → sum < 0)
                                        
h_add8_guarantees   ◄───────────────── sorry (line 896)
       (similar pattern)                │
                                        ▼
h_fib8_soundness (fib8 case) ◄──────── sorry (line 924)
                                        │
fib_table_interaction_mult_pm_one  ────┤
       (sorry - line 699)               │
                                        ▼
h_fib_mults  ◄──────────────────────── DONE (uses helper)
                                        │
                                        ▼
all_fib_pushes_valid  ◄──────────────── DONE (proven earlier)
                                        │
                                        ▼
h_valid = spec  ◄───────────────────── DONE!
```

## Next steps for continuation

### Priority 1: Break down structural helpers into simpler building blocks

The helpers `bytes_push_val_lt_256` and `fib_table_interaction_mult_pm_one` should be
reduced to simpler per-circuit statements like:
- "add8's BytesChannel interactions have mult = -1"
- "fib8's BytesChannel interactions are `[]`"
- "verifier's BytesChannel interactions are `[]`"
- "pushBytes's BytesChannel interactions have values in 0..255"

The ensemble-level helpers then follow by combining these per-circuit facts.

**Per-circuit BytesChannel interaction characterizations:**
- `add8_bytes_localAdds`: add8 emits `[(-1, #v[z])]` to BytesChannel (z is witness)
- `fib8_bytes_localAdds_empty`: fib8 emits `[]` to BytesChannel
- `verifier_bytes_localAdds_empty`: verifier emits `[]` to BytesChannel  
- `pushBytes_bytes_localAdds`: pushBytes emits `[(m[i], #v[i]) for i in 0..255]`

**Per-circuit FibonacciChannel interaction characterizations:**
- `pushBytes_fib_localAdds_empty`: pushBytes emits `[]` to FibonacciChannel
- `add8_fib_localAdds_empty`: add8 emits `[]` to FibonacciChannel
- `fib8_fib_localAdds`: fib8 emits `[(-1, pull), (1, push)]` to FibonacciChannel

### Priority 2: `h_add8_guarantees` (line 888)

Similar structure to `h_bytes_guarantees`:
- For each add8 pull, show the guarantee holds (x < 256 → y < 256 → z = (x+y) % 256)
- Use balance to find matching push
- Pushes come from add8 rows, which satisfy the requirement by add8.soundness

### Priority 3: `h_fib8_soundness` fib8 case (line 916)

For each fib8 push entry:
1. Extract the corresponding row's input (n_i, x_i, y_i) and output z_i
2. Show the pull `(-1, #v[n_i, x_i, y_i])` is in fibInteractions
3. Show validity transfer: `IsValidFibState n_i x_i y_i → IsValidFibState (n_i + 1) y_i z_i`
   - Use add8 guarantees to get `z_i = (x_i + y_i) % 256`
   - Use fibonacci_bytes to get `x_i, y_i < 256` from input validity
   - Conclude output is next fibonacci state

## Key infrastructure already proven

- `sum_neg_ones`: sum of -1s = -(length)
- `exists_push_of_pull`: balance + mults ±1 → pull has matching push
- `all_fib_pushes_valid`: strong induction proving all fib pushes are valid
- `lift_constraints_with_guarantees`: bridges raw constraints to per-circuit soundness
- `Channel.filter_self_add`, `Channel.filter_self_single`: for filtering channel interactions
- `verifier_push_valid`: (0, 0, 1) is valid fibonacci state 0
- `fib8_step_valid`: valid input + constraints → valid output

## Likely challenges / notes

- **Balance strength**: `BalancedChannels` uses per-message balance (sum of multiplicities per message = 0)
- **Characteristic bound**: `interactions.length < p` is included in `BalancedChannels`
- **Finite field arithmetic**: Use `ZMod.natCast_eq_zero_iff` for `(n : F p) = 0 ↔ p ∣ n`
- **h_bytes_guarantees proof pattern**: Uses contradiction - if z.val ≥ 256, all interactions for #v[z] are pulls (sum of -1s), but balance says sum = 0, so list is empty, contradicting that we have a pull

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

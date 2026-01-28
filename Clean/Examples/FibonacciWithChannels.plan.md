# FibonacciWithChannels soundness proof plan

This note captures learnings and a concrete plan for completing
`fibonacciEnsemble_soundness` in `Clean/Examples/FibonacciWithChannels.lean`.

## General guidelines

This is a large proof, so try to make incremental progress. Prove intermediate statements (with `have`) or work backwards from the  
goal with `suffices`.

Report back to the user when either:

- You have finished the proof. In this case, start you message with "SUCCESS!"
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

## High-level plan (revised)

### Step 0: Lifting lemma

Prove a general lemma:
```
ConstraintsHold env ops ∧ (all channel guarantees hold for these interactions) →
ConstraintsHoldWithInteractions.Soundness env interactions ops
```

This lemma bridges the ensemble-level constraint representation to the per-circuit
soundness input. It should be a general theorem, not specific to fibonacci.

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

This part should be **automatable** for any acyclic channel dependency graph.

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

### What should be general vs. ensemble-specific

**General theorem about ensembles** (future work):
- The lifting lemma (Step 0)
- Deriving guarantees from balance + requirements for acyclic channels (Steps 1-4)
- The `exists_push_of_pull` matching lemma
- The framework for layered guarantee derivation

**Ensemble-specific** (what the user proves manually):
- The channel dependency ordering (which channels are acyclic)
- For cyclic channels: the well-founded order and inductive argument (Step 6)
- Connecting the verifier spec to the ensemble spec (Step 2)

## Likely challenges / extra hypotheses

- **Balance strength** (RESOLVED):
  We strengthened `BalancedChannels` to per-message balance (sum of multiplicities
  per message = 0), which is what real ZK systems check via random evaluation.

- **Characteristic bound** (RESOLVED for `exists_push_of_pull`):
  The `exists_push_of_pull` lemma needs `interactions.length < p`. This is a
  reasonable assumption — the total number of interactions must be smaller than
  the field characteristic.

- **Step counter wraparound** (addressed):
  `all_fib_pushes_valid` requires `n_i.val + 1 < p` for each fib8 row to ensure
  the step counter doesn't wrap around. This bounds the maximum fibonacci chain
  length to < p, which is fine for practical use.

- **Acyclic dependency** (key insight):
  For bytes/add8, the channel dependency graph is monotone:
  `pushBytes` → bytes guarantees → `add8` → add8 guarantees → `fib8`.
  This means guarantees can be derived layer by layer without induction.
  For Fibonacci, the dependency is cyclic; this is where strong induction is needed.

- **Missing proofs**:
  `pushBytes.soundness` is currently `sorry`, but its guarantees are trivial and
  should be easy to fill in (emits constants 0..255).

## Progress so far

### ✅ Completed (no sorry):

**Infrastructure:**
- `sum_neg_ones`: sum of all -1s = -(length)
- `exists_push_of_pull`: per-message balance + all mults ±1 → pull has matching push
- `verifier_push_valid`: (0, 0, 1) is valid fibonacci state 0
- `fib8_step_valid`: valid input + constraints → valid output
- `all_fib_pushes_valid`: all fibonacci pushes are valid (by strong induction)
- **`lift_constraints_with_guarantees` (Step 0)**: ✅ COMPLETE
  - Bridges ensemble-level `ConstraintsHold` to per-circuit `ConstraintsHoldWithInteractions.Soundness`
  - Key lemma for applying per-circuit soundness theorems

**BalancedChannels Enhancement:**
- Added `interactions.length < ringChar F` bound to `BalancedChannels` definition
- This provides the characteristic bound needed for `exists_push_of_pull`

**Ensemble Soundness Progress:**
Inside `fibonacciEnsemble_soundness`:
- `const_triple`: const (n,x,y) decomposes to (Expression.const n, ..., ...)
- `verifier_localAdds`: characterizes verifier's channel emissions
- `h_verifier_pull`, `h_verifier_push`: verifier interaction membership proofs (using `Channel.filter_self_add/single`)
- `h_fib_bound`: extracted from `BalancedChannels` ✅
- `h_fib_balanced`: per-message balance for fibonacci channel ✅
- `h_fib_mults` (verifier case): verifier multiplicities are ±1 ✅

**Channel Infrastructure:**
- `Channel.filter_self_single`: filtering a single emission gives a singleton list
- `Channel.filter_self_add`: filtering `emitted + is` prepends the emission to filtered `is`

### 🔄 Remaining Work:

**Line 776 - `h_fib_mults` (table case):** ⚠️ BLOCKED
- Goal: prove table fibonacci interactions have mult ±1
- **Why blocked**: Needs channel filtering lemmas to show:
  - `pushBytes.localAdds` filtered for FibonacciChannel gives `[]` (wrong channel name)
  - `add8.localAdds` filtered for FibonacciChannel gives `[]` (wrong channel name)
  - `fib8.localAdds` filtered for FibonacciChannel gives entries with mult ±1
- **Requires**: General `Channel.filter_other` lemma (filtering one channel's emissions through a different channel's filter)
- **Strategy**: See detailed roadmap in code comments at line 761-776

**Line 809 - `h_fib8_soundness`:** 🎯 MAIN WORK (Steps 1-6)
- This is the core hypothesis encapsulating layered guarantee derivation
- For each non-verifier fibonacci push, need to show:
  - IF pulled state is valid (fibonacci guarantee holds)
  - AND add8 guarantees hold
  - THEN pushed state is valid
- **Requires**:
  1. Derive BytesChannel guarantees from `pushBytes.soundness` + balance
  2. Derive Add8Channel guarantees from `add8.soundness` + BytesChannel guarantees + balance
  3. Apply `fib8.soundness` with both guarantee sets
  4. Extract the implication: valid input state → valid output state
  5. Connect to `all_fib_pushes_valid` via the extracted implications
- **Uses**: The completed lifting lemma to apply per-circuit soundness theorems

**Final Steps:**
- Apply `fibonacciVerifier.soundness` with derived FibChannel guarantees
- Show `IsValidFibState n x y` (the ensemble spec)

### Notes for next agent:

1. **Start with `h_fib8_soundness`** (line 809) - this is unblocked and the conceptually important work
2. `h_fib_mults` (table case) can be skipped or left as an assumption if channel filtering infrastructure is missing
3. The lifting lemma is complete and working - use it to connect ensemble constraints to per-circuit soundness
4. `all_fib_pushes_valid` is proven and ready to use once `h_fib8_soundness` establishes the per-row implications
5. **Tool available**: `mcporter call lean-lsp.lean_goal file_path:... line:...` to inspect proof states
   - See `skills/lean-mcp/SKILL.md` for usage
6. The ensemble proof structure is in place - just need to fill in the channel guarantee derivations

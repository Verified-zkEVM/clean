# Loop composition via state-threaded round bundles

Design for restructuring `MulIncomplete` (and later `HashPiece`/`Chain`/`MulComplete`) so that
loops decompose through formal circuit bundles — the one blessed way to split proof work — and
the six hand-written `loop_*` lemmas disappear. Agreed with Gregor 2026-07-16.

## The ownership principle

From the perspective of what is *constrained*, a double-and-add round's natural inputs are
`z[-1]`, `P[0]`, `Acc[0]` (previous running sum; base and accumulator at the current row,
treating the accumulator's y as a virtual column), and its natural outputs are `z[0]`, `P[1]`,
`Acc[1]`. The round therefore *assigns its outputs*: `z` at its own row, and the row+1 state
cells (`x_A, λ₁, λ₂, x_P, y_P`) — because `Acc[1]`'s virtual y **is** the four row+1 cells,
materializing the output accumulator means witnessing the next row's slope cells.

Consequences:
- **Zero forward references.** Every cell a round's gate reads is assigned by the round itself
  or its predecessor/init. The sequential premised-spec flow of `subcircuit_rw` completeness
  works as-is; no contract factoring, no enable shifting.
- **Assignment placement is layout-free.** Cells land at the same (column, row) as the Rust
  iteration structure; selectors don't move; copy pairs are unchanged. Keep the copies in
  Rust's execution order (z, y_a, x_a, then the base anchors) for the eventual permutation
  phase of VK matching.
- The `if r = 0` anchor branch leaves the loop (it is the *init* materializing round 0's
  input), the witnessed final y moves *into* the last round (it is that round's output
  accumulator's real y), and interior rounds become fully uniform — no branches in the loop
  body at all.

## Structure (Gregor's requirement: reviewable as two bundles + edges)

One `round` formal circuit, one `loop` formal circuit, both with clean Assumptions/Spec
contracts; `double_and_add` handles the edges (init, `q_mul_1`, last `q_mul_3` round).

### State type

```lean
/-- Loop state entering the round at row R: the previous running sum (row R−1) and the
row-R accumulator/base cells. The accumulator's y has no cell: it is virtually represented
by (λ₁, λ₂, x_A, x_P). -/
structure State (F : Type) where
  z : F               -- running sum, one row up
  xA : F              -- accumulator x
  lambda1 : F         -- slope cells whose combination represents the accumulator's y
  lambda2 : F
  base : Point F      -- x_P, y_P
deriving ProvableStruct
```

Value-level derived accessors (for specs only, never cells): `x_R = λ₁² − x_A − x_P`,
`State.accY = (λ₁ + λ₂)(x_A − x_R) / 2`, `State.acc : Point F = (xA, accY)`.

### `round (i : ℕ)` — interior round, global bit index `i`

- Shared-chip pattern: `ConfigInput = Config`, `configure := pure` (the parent owns
  configuration; bundle soundness quantifies over arbitrary config, so this is sound).
- Input `{alpha : F, s : State F}` (alpha cell needed by witgen for bit `i`).
- `synthesize cfg offset` at its own row `offset`: enable `q_mul_2 @ offset`; assign
  `z @ offset` and `x_A, λ₁, λ₂, x_P, y_P @ offset+1`; return the row+1 `State`.
- Witgen is **local**: honest values computed from the input state cells and bits `i`, `i+1`
  of the alpha cell (mirrors Rust's iteration-local computation) — not recomputed from the
  phase's start cells.
- Spec (algebraic, assumption-free — the EC upgrade happens in `loop` where the
  nondegeneracy assumptions live): ∃ k with `IsBool k`,
  `s'.z = 2·s.z + k`, `s'.base = s.base`, and the gradient/secant identities relating
  `s.acc`-cells, `s'.acc`-cells, `k`, and the base — the per-round payload the donor
  `soundness_aux` consumes.
- ProverAssumptions/ProverSpec: honest-chain shape — input state values honest-reachable ⟹
  output state values are the step values (`ProverSpec` = the value step, which the next
  round's ProverAssumptions consumes; strictly backward, so the engine chains it).

### `loop (n w : ℕ)` — rounds 0..n−1, `q_mul_2` rows

- Same shared-chip pattern.
- Input `{alpha, s0 : State}`, Output `{sFinal : State, zs : Vector F n}`.
- `synthesize`: `foldRange offset 1 n (fun r row s => (round (w+r)).call cfg row {alpha, s})`,
  then `zs ← cellVec cfg.z (fun r => offset + r) n` (same cell references as the threaded
  states' z's, by rfl) — no ops emitted; return both. `foldRange` suffices: the accumulator
  var at round k is the closed form (cells at round-determined rows), the documented
  maintainer rule; `foldRangeDynOutput` is NOT needed.
- Spec ≈ the current `RoundInvariant` content, stated on `zs`/`sFinal` values: ∃ bits, the
  z-chain over `zs`, and ∀ m, `s0.acc = m • base → 2 ≤ m → range → sFinal.acc = accScalar m
  bits n • base`. The round-to-chain induction lives HERE and nowhere else, routed into the
  imported donor algebra (`soundness_aux`, `accVal_eq_nsmul`).
- Assumptions: `base.OnCurve` (chain-level; nondegeneracy comes from the m•P range premises
  inside the Spec implication, donor-style).

### `double_and_add (n w)` — edges only

- Inputs/Output move to whole Points (resolves the ofCoords TODO):
  `Inputs {alpha, base : Point, acc : Point, z}`, `Output {acc : Point, zs : Vector (n+1)}`.
- `synthesize`: start copies `z@offset`, `y_a@offset (λ₁ col)`, `x_a@(offset+1)`; anchor
  copies `base → x_P/y_P@(offset+1)`; assign `λ₁ λ₂ @(offset+1)` (init materializes round
  0's input state — its λ's are round 0's slopes); enable `q_mul_1@offset`; call
  `loop n w` at `offset+1`; last round inline at row `offset+1+n`: assign `z`, then
  `x_A@(offset+n+2)` and the witnessed final y in `λ₁@(offset+n+2)`, enable `q_mul_3`;
  assemble Output (acc = final cells as a Point, zs = loop.zs ++ last z).
- Proofs: `circuit_proof_start` peel; `subcircuit_rw` consumes the folded `loop` chunk
  (Spec in, single-goal strengthening out); `q_mul_1`/`q_mul_3` gate facts handled at
  parent level (leaf ops, like `q_mul_1` today); donor algebra at the endpoints
  (`honest_step` row 0, final-y cancellation). **Deleted**: `loop_gate_facts`,
  `loop_anchor`, `loop_acc_sound`, `loop_zchain_sound`, `loop_row_values`,
  `loop_constraints_complete`, the `adv`/`XAr`/`YADr` reader section, `cellAt` plumbing
  where obsolete.

### Row/selector layout (unchanged from today, n+1 total rounds)

- `offset`: z and y_a start copies; `q_mul_1`.
- `offset+1 .. offset+n`: `q_mul_2` rows = `loop`'s rounds 0..n−1.
- `offset+1+n`: `q_mul_3` row = the parent's last round.
- `offset+n+2`: final `x_A` and witnessed y (λ₁ col).

### Known quirk (comment it in the code)

Round r witnesses row r+1's λ cells — *round r+1's slopes* — because the virtual-y
representation makes them part of round r's output accumulator. Completeness-wise fine:
computable from the input state values and bits i, i+1.

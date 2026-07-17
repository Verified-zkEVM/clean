# Sinsemilla stack: loop-bundle restructure + Merkle/CommitDomain completion

Applies the `loop-composition-design.md` principles (agreed 2026-07-16, executed for
`MulIncomplete`) to the Sinsemilla slice, and finishes the stack: `HashPiece`/`Chain`
as round+loop bundles over the native loop combinators, Merkle (`HashLayer`/`Layer`/
`CalculateRoot`, CondSwap ported), `CommitDomain` proven, VK fixtures matched.

## Rust-faithfulness corrections (VK-relevant, from re-reading the source)

Three deviations in the current port are *permutation/VK bugs* and are fixed by this
restructure (all cited from `halo2_gadgets-0.5.0/src/sinsemilla/chip/hash_to_point.rs`):

1. **The piece does not copy its entering `x_a`** (`hash_piece`, comment at :295: "the
   accumulator x-coordinate provided by the caller is not copied … x_a MUST have been
   already assigned within this region at the correct offset"). The current
   `HashPiece.synthesize`'s `copyAdvice input.xA` adds a copy constraint Rust doesn't
   have → permutation data mismatch. Fix: the entering row is **positional**
   (`Witness`/reads slot, the MulIncomplete ownership pattern); `Inputs` carries only
   the piece cell.
2. **`y_a` is a pure `Value` thread** (`X<F>`/`Y<F>` in `hash_all_pieces`; the only
   materialization is the trailing row's `λ₁` assignment, :258-284). The current
   Chain's per-boundary *scratch cells* (`assignAdvice cfg.lambda1 scratch …`) assign
   cells Rust doesn't, extending the region. Fix: the entering `y` becomes a
   **prover-derivation program parameter** (`Placed ProverEnvironment Fp → Fp`), used
   only inside witgen closures and surfaced through the bundle's `Witness`/`extract`
   slot so `ProverAssumptions`/`ProverSpec` can speak about its value. Interior
   boundaries derive it positionally from the previous piece's cells (`nextYA`
   formula); the first piece gets the caller's program (constant `Q.y` for public
   init). Doctrine: this is a *derived* value (UnconstrainedNative.lean's hard rule),
   not an external hint.
3. **Hash entry is `public_q_initialization`** (:122-174, the
   `¬allow_init_from_private_point` branch the action circuit uses): enable
   `q_sinsemilla4 @ offset`, `assign_fixed(fixed_y_q, offset, Q.y)`,
   `assign_advice_from_constant(x_a, offset, Q.x)`. The current `CommitDomain` seeds
   `Q` via two constrained-constant *advice* cells (`seedX`/`seedY`) — wrong columns,
   wrong copies, `initialYQGate` never enabled. Fix: port the real init (the
   `initialYQGate` finally gets its consumer); `CommitDomain`'s `Spec` pins `A = Q`
   through the constant copy (x) and the init gate (y).

## HashPiece: round + loop + edges (mirrors `MulIncompleteRound`/`MulIncomplete`)

Row layout unchanged (piece of `w + 1` words at rows `offset .. offset + w`; cells at
identical (column, row) as Rust — only assignment *attribution* moves across rounds,
which is VK-neutral).

- **State** (entering row `r`): `{ z : F, row : DoubleAndAddRow F }` — the `bits` cell
  and the four double-and-add cells at row `r`. The accumulator is virtual:
  `acc = (row.xA, yA row / 2)` (donor `yA`/`xR` reused).
- **`round G r`** (interior word `r`, `FormalRegionCircuit`, shared-chip
  `configure := pure`, `Input = field` (the piece cell), `Witness = State` positional):
  at its own row `o`: assign `q_s2 @ o := 1`; assign `z @ o+1` (`zWit`, non-native IR
  off the piece cell), `xP/λ₁/λ₂ @ o+1` (next word's slopes — the same "round r
  witnesses round r+1's slopes" quirk as MulIncomplete) and `xA @ o+1`; enable the
  generator lookup and the Sinsemilla gate at `o`. Zero forward references.
  - `Spec` (assumption-free): `∃ m < 2^K`, `w.z = ↑m + 2^K·out.z`,
    `w.row.xP = (G.S m).x`, the `y_p` derivation lands on `(G.S m).y`, and the lifted
    step: `∀ A` on-curve matching `(w.row.xA, yA w.row)`, `∀ B`,
    `step G.S m A = some B → out.row.xA = B.x ∧ 2·B.y = yA out.row`.
  - `ProverAssumptions`: entering state honest for some on-curve `A` at word `r` with
    the chain defined through word `r+1` (the gate's next-row `Y_A` invariant needs
    it). `ProverSpec`: `out = w.step …` (deterministic value step off the cell
    readings — chains backward).
  - `EnvAssumptions = GeneratorTableLoaded` (the round owns the lookup).
- **`loop G n`**: `forRange' offset 1 n (round-calls)`; output = exit `State` + the
  `n` interstitial `z` cells. `Spec`: `∃ ms`, word chain over the `z`s + the
  `hashToPoint` fold over `(List.range n).map ms` from the entering row to the exit
  row. The induction lives here and nowhere else.
- **`circuit G w final yaIn`** (edges): copy piece → `bits @ offset` (`z_0`, the one
  real copy); assign `xP/λ₁/λ₂ @ offset` (word 0's slopes; init materializes round 0's
  input; witgen reads the positional `xA @ offset` + the `yaIn` program); `loop G w`;
  the last-word edge at row `offset + w`: `q_s2 := qS2Boundary final`, exit
  `xA @ offset+w+1`, lookup enable (no gate — the linking gate at the last row belongs
  to the composing circuit, as today). `Inputs = {piece}`; `Output` as today
  (`first`/`last`/`xANext`/`zs`, all positional); `Spec` as today minus the
  `input.xA` conjunct (the chain contract anchors on `output.first` directly).
- The six hand-written loop lemmas (`loop_operations_succ`, `loop_lookup_facts`,
  `loop_gate_facts`, `loop_row_values`, `loop_constraints_complete`, plus the `loop`
  recursion itself) are deleted.

## Chain: `forRangeVar'` over the piece list

`hash_all_pieces` becomes a plain variable-stride loop (the combinator's documented
target — `rows i` = partial sums of `nᵢ + 1`), one body per piece:

- body `i`: `(HashPiece.circuit G nᵢ (i = last) (chainYA i)).call cfg (rows i)
  {piece := pieces[i]}`; re-pin `q_s2 @ rows i + nᵢ` (parent handle for the gate
  reduction, idempotent); enable the linking `sinsemillaGate @ rows i + nᵢ` (rotation
  +1 crosses into the next piece's first row / the trailing row).
- `chainYA 0 = yaIn` (the bundle's own program parameter); `chainYA (i+1)` derives the
  boundary `y` positionally from piece `i`'s last row + the next row's `x_a` (the
  `nextYA` formula over cells assigned strictly earlier).
- trailing edge after the loop (Rust :258-284): `λ₁ @ exit := final y_a` (witgen =
  `chainYA len`), dummy `λ₂/x_p := 0`.
- `Output.zs` = positional heterogeneous cell family (`zsCells ns offset :
  HVec (zLengths ns) (AssignedCell Fp)`, no ops), `point = (xA @ exit, λ₁ @ exit)`.
- Soundness/completeness: the `forRangeVar'` split gives `∀ i : Fin len` chunks;
  `subcircuit_rw` weakens each piece chunk to its Spec; a **pure value-level list
  induction** (the donor `Chain` algebra: `soundness_aux` glue per boundary,
  `PieceChunks`/`ZsFacts` assembly) replaces `chainBody_sound`/`chainBody_complete`
  and all the literal-eval bridges.
- `Inputs = {pieces}`; contract otherwise as today (Spec `G ns`, EnvAssumptions the
  loaded table — identity-threaded to every child).

## hash_message / public Q init

A small layouter-adjacent bundle (region-level, rows `offset`, then chain at the same
`offset` — Rust's init shares row 0 with the first piece): `q_s4` enable + `fixed_y_q`
assign + `x_a` from constant, then `Chain G ns (fun _ => Q.y)`. Soundness: the
constant copy pins `A.x = Q.x`; the init gate (`2·y_Q − Y_A(0) = 0`) pins
`2·A.y = enterYA`, so the chain Spec instantiates at `A = Q`. This is the entry both
`CommitDomain.commit` and Merkle's `hash_layer` use (`SinsemillaChip::hash_to_point`'s
region), packaged once.

## Merkle

- **`Gate` (Decomposition check)**: `l` is `assign_advice_from_constant` at
  `advices[4]` row `g+1` (chip.rs:355-361) — a *constant*, not an input copy; the
  current ten-copies body is corrected to nine copies + the `l` constant, and the two
  sorries closed (leaf proofs, `circuit_proof_start` + `spec_of_polysZero`/
  `polysZero_of_spec`).
- **CondSwap** ported (`utilities/cond_swap.rs:85-134` swap region + :256-283 gate;
  donor proofs from `Orchard.Utilities.CondSwap`): one-row region, copy `a`, witness
  `b`/`swap` (genuine `Unconstrained` hints — the sibling value and the position bit
  enter as `Value`s), assign `a_swapped`/`b_swapped`, `q_swap` gate.
- **`HashLayer`**: layouter-level composition mirroring `merkle/chip.rs:229-398`
  region-for-region: witness-piece regions (`witness_pieces` column — added to the
  Sinsemilla `Config`, it exists in Rust's `SinsemillaConfig` but was dropped in the
  port), `witness_short` regions for `b₁`/`b₂` (ported `shortRangeCheck`), the
  `hash_to_point` region (hash_message above), the decomposition-check region
  (`Gate`), reading `z1_a = zs[0][1]`, `z1_b = zs[1][1]` off the chain's `zs`. Value
  glue: the already-lifted `assemble`/`honest_*`.
- **`Layer`** = CondSwap.swap + HashLayer; **`CalculateRoot`** = 32-layer fold
  (`merkleRoot_of_steps` + `honestNode` already lifted).

## CommitDomain

`commit = hash_to_point(Q, msg) + [r]R` (`sinsemilla.rs:488-509`): replace the
`seedX`/`seedY` wrapper with the faithful Q init above; children = hash_message,
`blind` (the `[r]R` **stated boundary** — abstract `MulFixed.FullWidth` interface via
`BlindSpecPinned`/`BlindEnvPinned` hypotheses, unchanged), `Ecc.Add.add`. The four
stated sorries are closed against those hypotheses (no sorry remains; the boundary is
a hypothesis, not a hole).

## VK fixtures

`SinsemillaPre/Post` (+ sel-map) fixtures arrive from the sibling-machine `dump_lean`
run; `TestVkMatchSinsemilla` extends the Add/Mul pattern — the first lookup-bearing
target, exercising `lookupInputExprs`/`lookupTableExprs` projection and the
`witness_pieces`/`fixed_y_q` columns this restructure adds back.

---

## Working state (updated as the restructure lands)

**Done (pushed through c728175a):**
- `HashPieceRound.lean` — Config (+`witnessPieces` restored)/gates/lookup/configure moved
  here; `State` (`{z, row : DoubleAndAddRow}`), `State.step` via standalone defs
  (`stepXA/stepYA/stepL1/stepL2` — NEVER lets: zeta explosion), round bundle proven.
  Kernel lessons (all encoded in comments there): raw-polynomial spellings produced via
  the `rowValue` route (`step_gates`), never `simp only [...] at` a step-term hypothesis
  (deep congruence trees), goal-shaped `complete_gates` applied once syntactically.
- `HashPiece.lean` — rebuilt: `State.iter`/`iter_of_steps`/`iter_honest` (via public
  `step_exit`), `loop_fold`, `wordChain`, `LoopOut`, `rowFam` (top-level def), `loop`
  bundle (forRange' of round.call) proven; `circuit G w final yaIn` (edges) proven.
  I/O: Input = piece cell (`field`); Witness = `fieldPair` (positional x_a read, `yaIn`
  value); Output = {first, last, xANext, zs}; Spec anchored on `output.first`.

**Next (in order, per maintainer resequencing):**
1. `Chain.lean` rework: `forRangeVar'` over `rows i` = offset + partial sums of
   `(nsᵢ+1)`; body i = `(HashPiece.circuit G nᵢ (i = last) (chainYA i)).call cfg (rows i)
   {pieces[i]}` + `q_s2` re-pin at `rows i + nᵢ` + linking `sinsemillaGate` enable there;
   trailing dummy row (λ₁ := final y via chainYA len, dummy λ₂/x_p := 0); `Output.zs`
   positional (`zsCells ns offset : HVec (zLengths ns) (AssignedCell Fp)`, no ops);
   `chainYA 0 = yaIn`, `chainYA (i+1)` = positional `nextYA` over piece i's last row +
   `x_a @ rows (i+1)`. Inputs = {pieces} only. Value-level list induction replaces
   `chainBody_sound`/`chainBody_complete`; `soundness_aux` glue per boundary stays.
2. **VK matching immediately after** (before Merkle/CommitDomain proofs — layout pinned
   first): composite `configure`s mirroring the incoming Rust-exact fixture call
   sequences (Sinsemilla chain; Merkle chain incl. CondSwap `configure`), wire
   `TestVkMatchSinsemilla`/`Merkle` on the replacement fixtures (ignore 793d84f5's).
   Note other agent's fb5d88ee/2631644a: Phase-2 layout machinery (permutation σ dumps).
3. `hash_message` public-Q init (q_s4 + fixed_y_q + x_a from constant), CondSwap gadget
   port (donor `Orchard.Utilities.CondSwap`), Merkle Gate body fix (`l` is a CONSTANT at
   advices[4] row g+1, not a copy; 9 copies not 10) + HashLayer/Layer/CalculateRoot,
   CommitDomain rework on the faithful init. No sorries anywhere.
